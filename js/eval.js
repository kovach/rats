// Incremental query evaluation — alternating fixpoint algorithm (afpa3)
//
// D: Map<string, {old: number, current: number}>
//   old:     count used for negative literal visibility (old === 0 → neg succeeds)
//   current: count used for positive literal visibility (current > 0 → pos succeeds)

function tupleKey(t) {
  return JSON.stringify(t);
}

function negVisible(D, key) {
  const e = D.get(key);
  return !e || e.old === 0;
}

function posVisible(D, key) {
  const e = D.get(key);
  return !!e && e.current > 0;
}

function wouldChange(D, tuple, direction) {
  const e = D.get(tupleKey(tuple));
  const c = e ? e.current : 0;
  return (c === 0) !== (c + direction === 0);
}

function updateOld(D, tuple) {
  const key = tupleKey(tuple);
  const e = D.get(key) ?? { old: 0, current: 0 };
  D.set(key, { old: e.current, current: e.current });
}

function updateCurrent(D, tuple, direction) {
  const key = tupleKey(tuple);
  const e = D.get(key) ?? { old: 0, current: 0 };
  D.set(key, { old: e.old, current: e.current + direction });
}

function setsEqual(a, b) {
  if (a.size !== b.size) return false;
  for (const x of a) if (!b.has(x)) return false;
  return true;
}

// Seeds from rules whose body is all-negative ground literals.
// With an empty D (all old=0), every negative literal trivially succeeds.
function negOnlySeeds(rules) {
  const containsVar = t => t.tag === 'var' || t.tag === 'hole' || (t.args?.some(containsVar) ?? false);
  const seeds = [];
  for (const rule of rules) {
    if (rule.body.length === 0 || rule.body.some(l => !l.neg)) continue;
    if (rule.body.some(l => containsVar(l.atom))) continue;
    for (const h of rule.head) { if (!containsVar(h)) seeds.push(h); }
  }
  return seeds;
}

// One step of the alternating fixpoint (afpa3 algorithm).
//
// direction: +1 (up) or -1 (down)
// changes:   tuples that form the trajectory entering this step
// unifyNeg(t): returns [{bindings, remainingBody, head}] for neg-triggered rules
// unifyPos(t): returns [{bindings, remainingBody, head}] for pos-triggered rules
// solve(body, bindings, D): returns array of binding maps
//
// Returns { result, cutoff }
//   result: new trajectory (tuples produced this step)
function step(direction, changes, unifyNeg, unifyPos, solve, D, maxInner, trace = null) {
  // seen: key -> { neg: number, pos: number } — accumulated counts per tuple.
  // worklist: unique tuples in first-seen order.
  const seen = new Map();
  const worklist = [];
  for (const t of changes) {
    const key = tupleKey(t);
    if (!seen.has(key)) { seen.set(key, { neg: 0, pos: 0 }); worklist.push(t); }
    seen.get(key).neg++;
  }
  const result = [];

  for (let i = 0; i < worklist.length; i++) {
    if (i >= maxInner) return { result, cutoff: true };
    const tuple = worklist[i];
    const counts = seen.get(tupleKey(tuple));
    const produced = [];

    // Fire each unify function at most once per tuple, regardless of count.
    // it is possible for both to fire (e.g. it was asserted previous round, but has become false this round)
    const negMatches = counts.neg > 0 ? unifyNeg(tuple) : [];
    const posMatches = counts.pos > 0 ? unifyPos(tuple) : [];
    for (const { bindings, remainingBody, head } of [...negMatches, ...posMatches]) {
      for (const sol of solve(remainingBody, bindings, D)) {
        for (const h of head) {
          const derived = applyBindingsExport(h, sol);
          const dkey = tupleKey(derived);
          if (wouldChange(D, derived, direction)) {
            if (!seen.has(dkey)) { seen.set(dkey, { neg: 0, pos: 0 }); worklist.push(derived); }
            seen.get(dkey).pos++;
            result.push(derived);
            produced.push(derived);
          } else {
            updateCurrent(D, derived, direction);
          }
        }
      }
    }

    if (trace) trace.push({ counts: { ...counts }, tuple, produced });

    // updateOld is idempotent — call once if any neg triggers.
    if (counts.neg > 0) updateOld(D, tuple);
    // updateCurrent once per pos derivation.
    for (let c = 0; c < counts.pos; c++) updateCurrent(D, tuple, direction);
  }

  return { result, cutoff: false };
}

// applyBindings is defined in eval-fn.js; we need it here too for step().
// Import it via a shared export from eval-fn, or duplicate the trivial version.
// We receive it injected via the solve closure — but head patterns need it too.
// Solution: eval-fn.js exports applyBindings and we import it.
// For now, define a local copy (identical logic).
function applyBindingsExport(term, bindings) {
  if (term.tag === 'hole') return term;
  if (term.tag === 'var') return (term.name in bindings) ? bindings[term.name] : term;
  if (term.tag === 'sym') return term;
  return { ...term, args: term.args.map(a => applyBindingsExport(a, bindings)) };
}

// Compute the well-founded semantics of a program.
// Returns: { log, result, cutoff }
// result: Map<key, {old, current}> — the last stable snapshot
function solveWithLog(facts, rules, derivatives, { maxInner = 10000, maxOuter = 1000, tracing = false } = {}) {
  // These are imported from eval-fn.js via the caller passing them in,
  // but for architectural simplicity we import them at the top of this module.
  // See bottom of file — unifyNeg/unifyPos/solve are passed in via `derivatives`.
  // Actually: we receive pre-built helper functions via the `derivatives` parameter
  // which is now { unifyNeg, unifyPos, solve } rather than compiled derivative array.
  const { unifyNeg, unifyPos, solve: solveBody } = derivatives;

  const D = new Map();
  const log = [];

  // Init: compute positive closure of seeds with old=0 everywhere (all neg literals succeed).
  // Process each new tuple through unifyPos to derive further tuples.
  const seeds = [...facts, ...negOnlySeeds(rules)];
  const initWorklist = [...seeds];
  let initCutoff = false;
  for (let i = 0; i < initWorklist.length; i++) {
    if (i >= maxInner) { initCutoff = true; break; }
    const t = initWorklist[i];
    if (!wouldChange(D, t, +1)) {
      updateCurrent(D, t, +1);
      continue;
    }
    updateCurrent(D, t, +1);
    for (const { bindings, remainingBody, head } of unifyPos(t)) {
      for (const sol of solveBody(remainingBody, bindings, D)) {
        for (const h of head) {
          const derived = applyBindingsExport(h, sol);
          if (wouldChange(D, derived, +1)) initWorklist.push(derived);
        }
      }
    }
  }
  const initChanges = [...D.keys()].map(k => JSON.parse(k));
  log.push({ type: 'init', seeds: initChanges, D: new Map(D), cutoff: initCutoff });
  if (initCutoff) return { log, result: new Map(D), cutoff: true };

  let changes = initChanges;
  let direction = -1;
  let lastStableD = new Map(D);
  let prevChangeKeys = null;
  let stepNum = 0;

  while (changes.length > 0) {
    if (stepNum >= maxOuter) return { log, result: lastStableD, cutoff: true };

    const trace = tracing ? [] : null;
    const { result, cutoff } = step(direction, changes, unifyNeg, unifyPos, solveBody, D, maxInner, trace);
    stepNum++;

    log.push({ type: 'step', stepNum, direction, changes: result, D: new Map(D), cutoff, trace });
    if (cutoff) return { log, result: lastStableD, cutoff: true };

    if (direction === +1) lastStableD = new Map(D);

    const changeKeys = new Set(result.map(tupleKey));
    if (prevChangeKeys && setsEqual(prevChangeKeys, changeKeys)) break;
    prevChangeKeys = changeKeys;

    direction = -direction;
    changes = result;
  }

  return { log, result: lastStableD, cutoff: false };
}

// ── reference interpreter ──────────────────────────────────────────────────────

function stepRef(seeds, evalFnRef, D_old, maxInner) {
  const D_new = new Map();
  const worklist = [...seeds];
  for (let i = 0; i < worklist.length; i++) {
    if (i >= maxInner) return { D: D_new, cutoff: true };
    const t = worklist[i];
    const key = tupleKey(t);
    if (D_new.has(key)) continue;
    D_new.set(key, { count: 1, state: 1 });
    for (const u of evalFnRef(t, D_new, D_old)) {
      if (!D_new.has(tupleKey(u))) worklist.push(u);
    }
  }
  return { D: D_new, cutoff: false };
}

function solveRefWithLog(facts, negOnlyFn, evalFnRef, { maxInner = 10000, maxOuter = 1000 } = {}) {
  const log = [];
  let D = new Map();
  let prevKeys = null, prevPrevKeys = null;

  for (let stepNum = 1; stepNum <= maxOuter; stepNum++) {
    const D_old = D;
    const seeds = [...facts, ...negOnlyFn(D_old)];
    const { D: D_new, cutoff } = stepRef(seeds, evalFnRef, D_old, maxInner);
    D = D_new;
    log.push({ type: 'step', stepNum, D: new Map(D), cutoff });
    if (cutoff) return { log, result: D, cutoff: true };

    const keys = new Set([...D.keys()]);
    if (prevKeys && setsEqual(prevKeys, keys)) break;
    if (prevPrevKeys && setsEqual(prevPrevKeys, keys)) break;
    prevPrevKeys = prevKeys;
    prevKeys = keys;
  }
  return { log, result: D, cutoff: false };
}

export { solveWithLog, stepRef, solveRefWithLog, tupleKey, negVisible, posVisible };
