// Incremental query evaluation — alternating fixpoint algorithm
//
// D: Map<string, number>  — serialized tuple -> count
// delta: Array<[tuple, number]>  — list of (tuple, multiplicity) pairs
// evalFn(t, sign, D_now, D_last): Array<[tuple, number]>  — user-supplied match function
// trajectory: [Array<tuple>, 'up' | 'down']

function tupleKey(t) {
  return JSON.stringify(t);
}

// Apply delta to D. Returns tuples whose count crossed zero (became active or inactive).
function updateStore(D, delta) {
  const crossed = [];
  for (const [t, n] of delta) {
    const key = tupleKey(t);
    const old = D.get(key) ?? 0;
    const next = old + n;
    D.set(key, next);
    if (old === 0 && next !== 0) crossed.push(t);
    if (old !== 0 && next === 0) crossed.push(t);
  }
  return crossed;
}

// One step of the alternating fixpoint.
//
// Phase 1: for each t in the input trajectory, find rules where t unifies with a
//   *negative* body literal and apply the resulting delta to D.
//   dir='up' (t newly present in over-approx): those matches become invalid → subtract.
//   dir='down' (t newly absent): those matches become valid → add.
//   Tuples that cross zero are collected into `fresh`.
//
// Phase 2: walk `fresh` (which grows as we go), finding rules where each t unifies
//   with a *positive* body literal. Apply the same sign as phase 1. Append new
//   zero-crossings to `fresh` until the list is exhausted (fixpoint).
//
// Returns: [fresh, opposite dir]
function step(trajectory, D, evalFn, maxInner) {
  const [ts, dir] = trajectory;
  const D_last = new Map(D);
  const fresh = [];

  // Phase 1: negative matches for input tuples
  for (const t of ts) {
    // evalFn(t, false, ...) finds negative body literal matches.
    // dir='up': flip to -1 (subtract).
    let delta = evalFn(t, false, D, D_last);
    if (dir === 'up') delta = delta.map(([u, n]) => [u, -n]);
    if (delta.length > 0)
      console.log('delta: ', JSON.stringify(t), dir, JSON.stringify(delta));
    fresh.push(...updateStore(D, delta));
  }

  // Phase 2: positive matches for fresh tuples (growing-list fixpoint)
  let innerCutoff = false;
  for (let i = 0; i < fresh.length; i++) {
    if (i >= maxInner) { innerCutoff = true; break; }
    // evalFn(t, true, ...) finds positive body literal matches.
    // dir='up': flip to -1 (subtract).
    let delta = evalFn(fresh[i], true, D, D_last);
    if (dir === 'up') delta = delta.map(([u, n]) => [u, -n]);
    fresh.push(...updateStore(D, delta));
  }

  return { next: [fresh, dir === 'up' ? 'down' : 'up'], cutoff: innerCutoff };
}

function setsEqual(a, b) {
  if (a.size !== b.size) return false;
  for (const x of a) if (!b.has(x)) return false;
  return true;
}

function negOnlyDelta(rules) {
  const isVar = s => typeof s === 'string' && s[0] >= 'A' && s[0] <= 'Z';
  const containsVar = t => Array.isArray(t) ? t.some(containsVar) : isVar(t);
  const delta = [];
  for (const rule of rules) {
    if (rule.body.length === 0) continue;
    if (rule.body.some(lit => !lit.neg)) continue;
    if (rule.body.some(lit => lit.atom.some(containsVar))) continue;
    for (const head of rule.head) {
      if (head.some(containsVar)) continue;
      delta.push([head, 1]);
    }
  }
  return delta;
}

// Compute the well-founded semantics of a program.
// program: { facts: Array<tuple>, rules: (passed to makeEvalFn externally) }
// evalFn: built from the rule set
// Returns: D (the last under-approximation = result of last DOWN-output step)
// Returns the delta from rules whose body consists entirely of negative ground atoms.
// With an empty D_last, all such negative literals trivially succeed.
function solveWithLog(facts, rules, evalFn, { maxInner = 10000, maxOuter = 1000 } = {}) {
  const D = new Map();
  const log = [];

  const D_last_empty = new Map();
  const seeds = [...facts, ...negOnlyDelta(rules)];
  const fresh = [...seeds];
  let initCutoff = false;
  for (let i = 0; i < fresh.length; i++) {
    if (i >= maxInner) { initCutoff = true; break; }
    fresh.push(...updateStore(D, evalFn(fresh[i], true, D, D_last_empty)));
    // Only add the tuple itself to D if it's a seed (fact/negOnly). Derived tuples
    // are already in D via the updateStore above; adding them again would overcount.
    if (i < seeds.length) updateStore(D, [[fresh[i], 1]]);
  }
  log.push({ type: 'init', fresh: [...fresh], D: new Map(D), cutoff: initCutoff });
  if (initCutoff) return { log, result: new Map(D), cutoff: true };

  let trajectory = [fresh, 'up'];
  let lastDownD = new Map(D);
  let prevOutputTuples = null;
  let stepNum = 0;

  while (trajectory[0].length > 0) {
    const outerCutoff = stepNum >= maxOuter;
    const inputDir = trajectory[1];
    const { next, cutoff: innerCutoff } = step(trajectory, D, evalFn, maxInner);
    trajectory = next;
    stepNum++;
    if (trajectory[1] === 'down') lastDownD = new Map(D);
    log.push({ type: 'step', stepNum, inputDir, outputDir: trajectory[1],
               fresh: [...trajectory[0]], D: new Map(D), cutoff: innerCutoff || outerCutoff });
    if (innerCutoff || outerCutoff) return { log, result: lastDownD, cutoff: true };
    const outputTuples = new Set(trajectory[0].map(tupleKey));
    if (prevOutputTuples !== null && setsEqual(prevOutputTuples, outputTuples)) break;
    prevOutputTuples = outputTuples;
  }

  return { log, result: lastDownD, cutoff: false };
}

export { solveWithLog, tupleKey };
