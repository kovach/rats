import { tupleKey, negVisible, posVisible } from './eval.js';

const BUILTINS = {
  '#lt': ([a, b]) => Number(a.name) < Number(b.name),
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
  if (value.tag !== pattern.tag || value.name !== pattern.name || value.args.length !== pattern.args.length) return null;
  let b = bindings;
  for (let i = 0; i < pattern.args.length; i++) {
    b = unify(pattern.args[i], value.args[i], b);
    if (b === null) return null;
  }
  return b;
}

function applyBindings(term, bindings) {
  if (term.tag === 'hole') return term;
  if (term.tag === 'var') return (term.name in bindings) ? bindings[term.name] : term;
  if (term.tag === 'sym') return term;
  return { ...term, args: term.args.map(a => applyBindings(a, bindings)) };
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
    if (ground.args.some(containsVar)) throw new Error(`Unbound variable in builtin: ${ground.name}`);
    const handler = BUILTINS[ground.name];
    if (!handler) throw new Error(`Unknown builtin: ${ground.name}`);
    const result = handler(ground.args);
    return (result !== lit.neg) ? solve(rest, bindings, D) : [];
  }

  if (lit.neg) {
    if (pattern.args?.some(containsVar)) throw new Error(`Unbound variable in negative literal: ${JSON.stringify(pattern)}`);
    return negVisible(D, tupleKey(pattern)) ? solve(rest, bindings, D) : [];
  } else {
    const results = [];
    for (const [key] of D) {
      if (!posVisible(D, key)) continue;
      const tuple = JSON.parse(key);
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
        const triggerBindings = {};
        const eqConstraints  = [];
        const valConstraints = [];
        let consistent = true;

        for (const lit of subset) {
          for (let i = 0; i < lit.atom.args.length; i++) {
            const term = lit.atom.args[i];
            if (term.tag === 'hole') continue;
            if (term.tag === 'var') {
              if (term.name in triggerBindings) {
                const j = triggerBindings[term.name];
                if (i !== j) eqConstraints.push([i, j]);
              } else {
                triggerBindings[term.name] = i;
              }
            } else if (term.tag === 'sym') {
              const existing = valConstraints.find(([pi]) => pi === i);
              if (existing) {
                if (existing[1].name !== term.name) { consistent = false; break; }
              } else {
                valConstraints.push([i, term]);
              }
            } else {
              consistent = false; break;
            }
          }
          if (!consistent) break;
        }

        if (!consistent) continue;

        compiled.push({
          triggerName,
          triggerArity,
          eqConstraints,
          valConstraints,
          triggerBindings,
          remainingBody: rule.body.filter(lit => !subset.includes(lit)),
          head: rule.head,
        });
      }
    }
  }
  return compiled;
}

// Build { unifyNeg, unifyPos, solve } helpers for solveWithLog.
//
// unifyNeg(t) → [{bindings, remainingBody, head}]  — neg-triggered rule matches
// unifyPos(t) → [{bindings, remainingBody, head}]  — pos-triggered (compiled) matches
// solve       — the solve function above (shared)
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
      if (!cd.eqConstraints.every(([i, j]) => deepEqual(t.args[i], t.args[j]))) continue;
      if (!cd.valConstraints.every(([i, sym]) => deepEqual(t.args[i], sym))) continue;
      const bindings = Object.fromEntries(
        Object.entries(cd.triggerBindings).map(([v, i]) => [v, t.args[i]])
      );
      matches.push({ bindings, remainingBody: cd.remainingBody, head: cd.head });
    }
    return matches;
  }

  return { unifyNeg, unifyPos, solve };
}

// ── reference interpreter helpers ─────────────────────────────────────────────

function solveRef(literals, bindings, D_now, D_old) {
  if (literals.length === 0) return [bindings];
  const [lit, ...rest] = literals;
  const pattern = applyBindings(lit.atom, bindings);

  const containsVar = t => t.tag === 'var' || t.tag === 'hole' || (t.args?.some(containsVar) ?? false);

  if (lit.atom.tag === 'builtin') {
    const ground = applyBindings(lit.atom, bindings);
    if (ground.args.some(containsVar)) throw new Error(`Unbound variable in builtin: ${ground.name}`);
    const handler = BUILTINS[ground.name];
    if (!handler) throw new Error(`Unknown builtin: ${ground.name}`);
    const result = handler(ground.args);
    return (result !== lit.neg) ? solveRef(rest, bindings, D_now, D_old) : [];
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

function makeCompiledRefEvalFn(derivatives, rules) {
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

export { compileDerivatives, makeHelpers, solveRef, makeCompiledRefEvalFn, makeNegOnlyFn };
