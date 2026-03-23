// Incremental query evaluation — alternating fixpoint algorithm (afpa3)

import { tupleKey, applyBindings } from './util.js';
import { Store, TupleSet } from './store.js';
import { solve } from './eval-fn.js';

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

// todo: why negOnlyFn
function solveRefWithLog(facts, negOnlyFn, evalFnRef, { maxInner = 10000, maxOuter = 1000 } = {}) {
  const log = [];
  let D = new Map();
  let prevKeys = null, prevPrevKeys = null;
  let direction = +1;

  for (let stepNum = 1; stepNum <= maxOuter; stepNum++) {
    const D_old = D;
    const seeds = [...facts, ...negOnlyFn(D_old)];
    const { D: D_new, cutoff } = stepRef(seeds, evalFnRef, D_old, maxInner);
    D = D_new;
    log.push({ type: 'step', stepNum, D: new Map(D), cutoff });
    if (cutoff) return { log, result: D, cutoff: true };

    const keys = new Set([...D.keys()]);
    if (direction == -1 && prevKeys && setsEqual(prevKeys, keys)) break;
    if (direction == -1 && prevPrevKeys && setsEqual(prevPrevKeys, keys)) break;
    prevPrevKeys = prevKeys;
    prevKeys = keys;
    direction = -direction;
  }
  return { log, result: D, cutoff: false };
}

function setsEqual(a, b) {
  if (a.size !== b.size) return false;
  for (const x of a) if (!b.has(x)) return false;
  return true;
}

// Seeds from rules whose body is all-negative ground literals.
// With an empty Store (all old=0), every negative literal trivially succeeds.
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

class WL {
  #l = [];
  push({tuple,ty}) {
    const node = this.#l.find(({tuple:tuple_,ty:ty_}) => Store.key(tuple_) === Store.key(tuple) && ty_ === ty);
    if (node) { node.w += 1 }
    else this.#l.push({tuple,ty,w:1});
  }
  get length() {
    return this.#l.length;
  }
  get(i) {
    return this.#l[i];
  }
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
  const worklist = new WL();
  for (const t of changes) {
    worklist.push({tuple: t, ty: 'neg'});
  }
  const result = new TupleSet();

  for (let i = 0; i < worklist.length; i++) {
    if (i >= maxInner) return { result: [...result], cutoff: true };
    const {tuple, ty: dir, w: count} = worklist.get(i);
    const produced = new TupleSet();

    let matches = dir == 'neg' ? unifyNeg(tuple) : unifyPos(tuple);

    const derivations = matches.flatMap(({ bindings, remainingBody, head }) =>
      solve(remainingBody,bindings, D).flatMap((sol) =>
        head.map((h) => applyBindings(h, sol))));

    // Both of these lines have the same effect: solve may now see the current value of tuple
    // (solve uses old count for negative atoms; current count for positive ones).
    if (dir === 'neg')
      D.updateOld(tuple);
    else // 'pos'
      D.updateCurrent(tuple, direction * count);

    // A few subtle things:
    //   - Worklist collapses duplicates, so if `x` is derived several times in the following loop it is queued once
    //   - This comes after the above block, so that
    //     if (z was missing at the start of the loop, tuple=z, and derived=z) we don't re-enqueue z
    //   - It is not possible to have (wouldChange = True) and worklist already contains {derived, 'pos'} bc:
    //     1) tuples only change in one direction per call to step (all +1 or all -1)
    //     2) handling it earlier would have done updateCurrent
    for (const derived of derivations) {
      if (D.wouldChange(derived, direction)) {
        worklist.push({tuple: derived, ty: 'pos'});
        result.insert(derived);
        produced.insert(derived);
      } else {
        D.updateCurrent(derived, direction);
      }
    }

    if (trace) {
      let counts = dir == 'neg' ? {neg:count,pos:0} : {neg:0, pos:count};
      trace.push({ counts, tuple, produced: [...produced] });
    }
  }
  return { result: [...result], cutoff: false };
}

// Compute the well-founded semantics of a program.
// Returns: { log, result, cutoff }
// result: Store — the last stable snapshot
function solveWithLog(facts, rules, derivatives, { maxInner = 10000, maxOuter = 1000, tracing = false } = {}) {
  const { unifyNeg, unifyPos } = derivatives;

  const D = new Store();
  const log = [];

  // Init: compute positive closure of seeds with old=0 everywhere (all neg literals succeed).
  const seeds = [...facts, ...negOnlySeeds(rules)];
  const initWorklist = [...seeds];
  let initCutoff = false;
  for (let i = 0; i < initWorklist.length; i++) {
    if (i >= maxInner) { initCutoff = true; break; }
    const t = initWorklist[i];
    const crosses = D.wouldChange(t, +1);
    D.updateCurrent(t, +1);
    if (crosses) {
      for (const { bindings, remainingBody, head } of unifyPos(t)) {
        for (const sol of solve(remainingBody, bindings, D)) {
          for (const h of head) {
            const derived = applyBindings(h, sol);
            if (D.wouldChange(derived, +1)) initWorklist.push(derived);
            else D.updateCurrent(derived, +1);
          }
        }
      }
    }
  }
  const initChanges = [...D].map(([t]) => t);
  log.push({ type: 'init', seeds: initChanges, D: D.snapshot(), cutoff: initCutoff });
  if (initCutoff) return { log, result: D.snapshot(), cutoff: true };

  let changes = initChanges;
  let direction = -1;
  let lastStableD = D.snapshot();
  let prevChangeKeys = null;
  let stepNum = 0;

  while (changes.length > 0) {
    if (stepNum >= maxOuter) return { log, result: lastStableD, cutoff: true };

    const trace = tracing ? [] : null;
    const D_before = D.snapshot();
    const { result, cutoff } = step(direction, changes, unifyNeg, unifyPos, solve, D, maxInner, trace);
    stepNum++;

    log.push({ type: 'step', stepNum, direction, changes: result, D_before, D: D.snapshot(), cutoff, trace });
    if (cutoff) return { log, result: lastStableD, cutoff: true };

    if (direction === -1) lastStableD = D.snapshot();

    if (result.length === 0) {
      lastStableD.updateAllOld();
      break;
    }
    const changeKeys = new Set(result.map(Store.key));
    if (prevChangeKeys && setsEqual(prevChangeKeys, changeKeys)) { break; }
    prevChangeKeys = changeKeys;

    direction = -direction;
    changes = result;
  }

  return { log, result: lastStableD, cutoff: false };
}

export { solveWithLog, stepRef, solveRefWithLog };
