import { tupleKey } from './eval.js';

const BUILTINS = {
  '#lt': ([a, b]) => Number(a.name) < Number(b.name),
};

function isVar(t) { return t.tag === 'var'; }

// Unify two tagged terms given existing bindings.
// Returns extended bindings or null on failure.
function unify(pattern, value, bindings = {}) {
  if (pattern.tag === 'hole') return bindings;
  if (pattern.tag === 'var') {
    if (pattern.name in bindings) return unify(bindings[pattern.name], value, bindings);
    return { ...bindings, [pattern.name]: value };
  }
  if (pattern.tag === 'sym') {
    return (value.tag === 'sym' && value.name === pattern.name) ? bindings : null;
  }
  // compound or atom: match name and recurse into args
  if (value.tag !== pattern.tag || value.name !== pattern.name || value.args.length !== pattern.args.length) return null;
  let b = bindings;
  for (let i = 0; i < pattern.args.length; i++) {
    b = unify(pattern.args[i], value.args[i], b);
    if (b === null) return null;
  }
  return b;
}

// Apply bindings to a tagged term, recursing into args.
function applyBindings(term, bindings) {
  if (term.tag === 'hole') return term;
  if (term.tag === 'var') return (term.name in bindings) ? bindings[term.name] : term;
  if (term.tag === 'sym') return term;
  return { ...term, args: term.args.map(a => applyBindings(a, bindings)) };
}

// Find all binding extensions that satisfy `literals` against D_now (positive) / D_last (negative).
// Negative literals must be fully ground once bindings are applied.
function solve(literals, bindings, D_now, D_last) {
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
    return (result !== lit.neg) ? solve(rest, bindings, D_now, D_last) : [];
  }

  if (lit.neg) {
    if (pattern.args.some(containsVar)) throw new Error(`Unbound variable in negative literal: ${JSON.stringify(pattern)}`);
    const count = D_last.get(tupleKey(pattern)) ?? 0;
    return count > 0 ? [] : solve(rest, bindings, D_now, D_last);
  } else {
    const results = [];
    for (const [key, count] of D_now) {
      if (count <= 0) continue;
      const tuple = JSON.parse(key);
      if (tuple.name !== pattern.name) continue;
      const newBindings = unify(pattern, tuple, bindings);
      if (newBindings === null) continue;
      results.push(...solve(rest, newBindings, D_now, D_last));
    }
    return results;
  }
}

// Build an evalFn from a set of parsed rules (as returned by parseRule).
// evalFn(t, sign, D_now, D_last) -> Array<[tuple, number]>
function makeEvalFn(rules) {
  return function evalFn(t, sign, D_now, D_last) {
    const delta = [];
    for (const rule of rules) {
      for (const bodyLit of rule.body) {
        // For sign=true, match positive literals; for sign=false, match negative ones.
        if (bodyLit.atom.tag === 'builtin') continue;
        if (bodyLit.neg !== !sign) continue;
        const bindings = unify(bodyLit.atom, t);
        if (bindings === null) continue;
        const otherLits = rule.body.filter(l => l !== bodyLit);
        for (const sol of solve(otherLits, bindings, D_now, D_last)) {
          for (const headPattern of rule.head) {
            const headTuple = applyBindings(headPattern, sol);
            delta.push([headTuple, 1]);
          }
        }
      }
    }
    return delta;
  };
}

// ── compiled derivatives ───────────────────────────────────────────────────────
//
// compileDerivatives(rules) pre-computes, for every rule and every triggering
// relation name, all valid "subset unifications" of positive body literals
// against an incoming tuple.  Each CompiledDerivative fires at runtime when a
// tuple with triggerName crosses zero in D.
//
// Shape:
//   triggerName     : string            — which relation fires this query
//   triggerArity    : number            — expected arity of the trigger tuple
//   eqConstraints   : [i,j][]          — t.args[i] must deepEqual t.args[j]
//   valConstraints  : [i,SymTerm][]    — t.args[i] must deepEqual this sym
//   triggerBindings : {varName:number} — rule var → arg index in t
//   remainingBody   : Literal[]        — body lits not consumed by the trigger
//   head            : Atom[]

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

    // Group by relation name.
    const byName = new Map();
    for (const lit of matchable) {
      if (!byName.has(lit.atom.name)) byName.set(lit.atom.name, []);
      byName.get(lit.atom.name).push(lit);
    }

    for (const [triggerName, lits] of byName) {
      const triggerArity = lits[0].atom.args.length;

      for (const subset of nonEmptySubsets(lits)) {
        const triggerBindings = {};  // varName → arg index
        const eqConstraints  = [];  // [i, j]
        const valConstraints = [];  // [i, sym]
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
              // compound term in trigger position — skip this subset
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

// Build an evalFn from pre-compiled derivatives.
// - sign=true  (Phase 2, positive triggers): use compiled derivatives with subset matching.
// - sign=false (Phase 1, negative triggers): use single-literal matching (d[atom](!..)=[]).
function makeCompiledEvalFn(derivatives, rules) {
  return function evalFn(t, sign, D_now, D_last) {
    const delta = [];

    if (sign) {
      for (const cd of derivatives) {
        if (cd.triggerName !== t.name || cd.triggerArity !== t.args.length) continue;
        if (!cd.eqConstraints.every(([i, j]) => deepEqual(t.args[i], t.args[j]))) continue;
        if (!cd.valConstraints.every(([i, sym]) => deepEqual(t.args[i], sym))) continue;
        const bindings = Object.fromEntries(
          Object.entries(cd.triggerBindings).map(([v, i]) => [v, t.args[i]])
        );
        for (const sol of solve(cd.remainingBody, bindings, D_now, D_last)) {
          for (const h of cd.head) delta.push([applyBindings(h, sol), 1]);
        }
      }
    } else {
      for (const rule of rules) {
        for (const bodyLit of rule.body) {
          if (bodyLit.atom.tag === 'builtin' || !bodyLit.neg) continue;
          const bindings = unify(bodyLit.atom, t);
          if (bindings === null) continue;
          const otherLits = rule.body.filter(l => l !== bodyLit);
          for (const sol of solve(otherLits, bindings, D_now, D_last)) {
            for (const h of rule.head) delta.push([applyBindings(h, sol), 1]);
          }
        }
      }
    }

    return delta;
  };
}

export { makeEvalFn, compileDerivatives, makeCompiledEvalFn };
