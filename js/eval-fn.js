import { tupleKey, applyBindings } from './util.js';

const toNum = t => t.tag === 'num' ? t.value : Number(t.name);
const fromNum = n => ({ tag: 'num', value: n });

const BUILTINS = {
  '#lt': ([a, b], bindings) => {
    if (a.tag !== 'sym' && a.tag !== 'num') throw new Error('Unbound variable in #lt');
    if (b.tag !== 'sym' && b.tag !== 'num') throw new Error('Unbound variable in #lt');
    return toNum(a) < toNum(b) ? bindings : false;
  },
  '#add': ([a, b, c], bindings) => {
    const isGround = t => t.tag !== 'var' && t.tag !== 'hole';
    const [aG, bG, cG] = [isGround(a), isGround(b), isGround(c)];
    if ([aG, bG, cG].filter(Boolean).length < 2)
      throw new Error('#add requires at least 2 ground arguments');
    if (aG && bG) return unify(c, fromNum(toNum(a) + toNum(b)), bindings) ?? false;
    if (aG && cG) return unify(b, fromNum(toNum(c) - toNum(a)), bindings) ?? false;
    /* bG && cG */ return unify(a, fromNum(toNum(c) - toNum(b)), bindings) ?? false;
  },
};

function unify(pattern, value, bindings = {}) {
  if (pattern.tag === 'hole') return bindings;
  if (pattern.tag === 'var') {
    if (pattern.name in bindings) return unify(bindings[pattern.name], value, bindings);
    return { ...bindings, [pattern.name]: value };
  }
  if (pattern.tag === 'sym') {
    return (value.tag === 'sym' && value.name === pattern.name) ? bindings : null;
  }
  if (pattern.tag === 'num') {
    return (value.tag === 'num' && value.value === pattern.value) ? bindings : null;
  }
  if (value.tag !== pattern.tag || value.name !== pattern.name || value.args.length !== pattern.args.length) return null;
  let b = bindings;
  for (let i = 0; i < pattern.args.length; i++) {
    b = unify(pattern.args[i], value.args[i], b);
    if (b === null) return null;
  }
  return b;
}

// Find all binding extensions satisfying `literals` against D.
// Positive literals use posVisible(D, key); negative use negVisible(D, key).
function solve(literals, bindings, D) {
  if (literals.length === 0) return [bindings];
  const [lit, ...rest] = literals;
  const pattern = applyBindings(lit.atom, bindings);

  const containsVar = t => t.tag === 'var' || t.tag === 'hole' || (t.args?.some(containsVar) ?? false);

  if (lit.atom.tag === 'builtin') {
    const ground = applyBindings(lit.atom, bindings);
    const handler = BUILTINS[ground.name];
    if (!handler) throw new Error(`Unknown builtin: ${ground.name}`);
    const newBindings = handler(ground.args, bindings) ?? false;
    if (lit.neg) return newBindings === false ? solve(rest, bindings, D) : [];
    return newBindings !== false ? solve(rest, newBindings, D) : [];
  }

  if (lit.neg) {
    if (pattern.args?.some(containsVar)) throw new Error(`Unbound variable in negative literal: ${JSON.stringify(pattern)}`);
    return D.negVisible(pattern) ? solve(rest, bindings, D) : [];
  } else {
    const results = [];
    for (const [tuple] of D) {
      if (!D.posVisible(tuple)) continue;
      if (tuple.name !== pattern.name) continue;
      const newBindings = unify(pattern, tuple, bindings);
      if (newBindings === null) continue;
      results.push(...solve(rest, newBindings, D));
    }
    return results;
  }
}

// ── compiled derivatives ───────────────────────────────────────────────────────

function deepEqual(a, b) {
  if (a === b) return true;
  if (a.tag !== b.tag || a.name !== b.name) return false;
  if (!a.args && !b.args) return true;
  if (!a.args || !b.args || a.args.length !== b.args.length) return false;
  return a.args.every((ai, i) => deepEqual(ai, b.args[i]));
}

function nonEmptySubsets(arr) {
  const result = [];
  for (let mask = 1; mask < (1 << arr.length); mask++)
    result.push(arr.filter((_, i) => mask & (1 << i)));
  return result;
}

function compileDerivatives(rules) {
  const compiled = [];
  for (const rule of rules) {
    const matchable = rule.body.filter(lit => !lit.neg && lit.atom.tag === 'atom');

    const byName = new Map();
    for (const lit of matchable) {
      if (!byName.has(lit.atom.name)) byName.set(lit.atom.name, []);
      byName.get(lit.atom.name).push(lit);
    }

    for (const [triggerName, lits] of byName) {
      const triggerArity = lits[0].atom.args.length;

      for (const subset of nonEmptySubsets(lits)) {
        compiled.push({
          triggerName,
          triggerArity,
          subsetPatterns: subset.map(lit => lit.atom.args),
          remainingBody: rule.body.filter(lit => !subset.includes(lit)),
          head: rule.head,
        });
      }
    }
  }
  return compiled;
}

// Build { unifyNeg, unifyPos } helpers for solveWithLog.
//
// unifyNeg(t) → [{bindings, remainingBody, head}]  — neg-triggered rule matches
// unifyPos(t) → [{bindings, remainingBody, head}]  — pos-triggered (compiled) matches
function makeHelpers(derivatives, rules) {
  function unifyNeg(t) {
    const matches = [];
    for (const rule of rules) {
      for (const bodyLit of rule.body) {
        if (bodyLit.atom.tag === 'builtin' || !bodyLit.neg) continue;
        const bindings = unify(bodyLit.atom, t);
        if (bindings === null) continue;
        matches.push({
          bindings,
          remainingBody: rule.body.filter(l => l !== bodyLit),
          head: rule.head,
        });
      }
    }
    return matches;
  }

  function unifyPos(t) {
    const matches = [];
    for (const cd of derivatives) {
      if (cd.triggerName !== t.name || cd.triggerArity !== t.args.length) continue;
      let bindings = {};
      let ok = true;
      for (const patternArgs of cd.subsetPatterns) {
        for (let i = 0; i < patternArgs.length; i++) {
          bindings = unify(patternArgs[i], t.args[i], bindings);
          if (bindings === null) { ok = false; break; }
        }
        if (!ok) break;
      }
      if (!ok) continue;
      matches.push({ bindings, remainingBody: cd.remainingBody, head: cd.head });
    }
    return matches;
  }

  return { unifyNeg, unifyPos };
}

// ── reference interpreter helpers ─────────────────────────────────────────────

function solveRef(literals, bindings, D_now, D_old) {
  if (literals.length === 0) return [bindings];
  const [lit, ...rest] = literals;
  const pattern = applyBindings(lit.atom, bindings);

  const containsVar = t => t.tag === 'var' || t.tag === 'hole' || (t.args?.some(containsVar) ?? false);

  if (lit.atom.tag === 'builtin') {
    const ground = applyBindings(lit.atom, bindings);
    const handler = BUILTINS[ground.name];
    if (!handler) throw new Error(`Unknown builtin: ${ground.name}`);
    const newBindings = handler(ground.args, bindings) ?? false;
    if (lit.neg) return newBindings === false ? solveRef(rest, bindings, D_now, D_old) : [];
    return newBindings !== false ? solveRef(rest, newBindings, D_now, D_old) : [];
  }

  if (lit.neg) {
    if (pattern.args?.some(containsVar)) throw new Error(`Unbound variable in negative literal: ${JSON.stringify(pattern)}`);
    const e = D_old.get(tupleKey(pattern));
    return !(e?.count > 0) ? solveRef(rest, bindings, D_now, D_old) : [];
  } else {
    const results = [];
    for (const [key, e] of D_now) {
      if (!(e.count > 0)) continue;
      const tuple = JSON.parse(key);
      if (tuple.name !== pattern.name) continue;
      const newBindings = unify(pattern, tuple, bindings);
      if (newBindings === null) continue;
      results.push(...solveRef(rest, newBindings, D_now, D_old));
    }
    return results;
  }
}

function makeCompiledRefEvalFn(derivatives) {
  return function evalFnRef(t, D_now, D_old) {
    const results = [];
    for (const cd of derivatives) {
      if (cd.triggerName !== t.name || cd.triggerArity !== t.args.length) continue;
      if (!cd.eqConstraints.every(([i, j]) => deepEqual(t.args[i], t.args[j]))) continue;
      if (!cd.valConstraints.every(([i, sym]) => deepEqual(t.args[i], sym))) continue;
      const bindings = Object.fromEntries(
        Object.entries(cd.triggerBindings).map(([v, i]) => [v, t.args[i]])
      );
      for (const sol of solveRef(cd.remainingBody, bindings, D_now, D_old)) {
        for (const h of cd.head) results.push(applyBindings(h, sol));
      }
    }
    return results;
  };
}

function makeNegOnlyFn(rules) {
  const containsVar = t => t.tag === 'var' || t.tag === 'hole' || (t.args?.some(containsVar) ?? false);
  return function negOnlyFn(D_old) {
    const results = [];
    for (const rule of rules) {
      if (rule.body.length === 0 || rule.body.some(l => !l.neg)) continue;
      for (const sol of solveRef(rule.body, {}, new Map(), D_old)) {
        for (const h of rule.head) {
          const head = applyBindings(h, sol);
          if (!containsVar(head)) results.push(head);
        }
      }
    }
    return results;
  };
}

export { compileDerivatives, makeHelpers, solve, solveRef, makeCompiledRefEvalFn, makeNegOnlyFn };
