import { tupleKey } from './eval.js';

// Variables are uppercase-initial strings; everything else is a constant.
function isVar(s) {
  return typeof s === 'string' && s[0] >= 'A' && s[0] <= 'Z';
}

// Unify two terms (strings or nested arrays) given existing bindings.
// Returns extended bindings or null on failure.
function unify(pattern, value, bindings = {}) {
  if (Array.isArray(pattern)) {
    if (!Array.isArray(value) || pattern.length !== value.length) return null;
    let b = bindings;
    for (let i = 0; i < pattern.length; i++) {
      b = unify(pattern[i], value[i], b);
      if (b === null) return null;
    }
    return b;
  }
  if (isVar(pattern)) {
    if (pattern in bindings) return unify(bindings[pattern], value, bindings);
    return { ...bindings, [pattern]: value };
  }
  return pattern === value ? bindings : null;
}

// Apply bindings to a term, recursing into nested arrays.
function applyBindings(term, bindings) {
  if (Array.isArray(term)) return term.map(t => applyBindings(t, bindings));
  return (isVar(term) && term in bindings) ? bindings[term] : term;
}

// Find all binding extensions that satisfy `literals` against D_now (positive) / D_last (negative).
// Negative literals must be fully ground once bindings are applied.
function solve(literals, bindings, D_now, D_last) {
  if (literals.length === 0) return [bindings];
  const [lit, ...rest] = literals;
  const pattern = applyBindings(lit.atom, bindings);

  if (lit.neg) {
    const containsVar = t => Array.isArray(t) ? t.some(containsVar) : isVar(t);
    if (pattern.some(containsVar)) throw new Error(`Unbound variable in negative literal: ${pattern}`);
    const count = D_last.get(tupleKey(pattern)) ?? 0;
    return count > 0 ? [] : solve(rest, bindings, D_now, D_last);
  } else {
    const results = [];
    for (const [key, count] of D_now) {
      if (count <= 0) continue;
      const tuple = JSON.parse(key);
      if (tuple[0] !== pattern[0]) continue;
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
        if (bodyLit.neg !== !sign) continue;
        const bindings = unify(bodyLit.atom, t);
        if (bindings === null) continue;
        const otherLits = rule.body.filter(l => l !== bodyLit);
        for (const sol of solve(otherLits, bindings, D_now, D_last)) {
          for (const headPattern of rule.head) {
            const headTuple = applyBindings(headPattern, sol);
            delta.push([headTuple, sign ? 1 : -1]);
          }
        }
      }
    }
    return delta;
  };
}

export { makeEvalFn, solve, unify, applyBindings, isVar };
