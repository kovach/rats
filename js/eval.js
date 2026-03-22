// Incremental query evaluation — alternating fixpoint algorithm (afpa3)

import { tupleKey, applyBindings } from './util.js';
import { Store } from './store.js';

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
  push({tuple,ty,w}) {
    const node = this.#l.find(({k,t}) => Store.key(k) === Store.key(tuple) && t === ty);
    if (node) { node.w += w }
    else this.#l.push({tuple,ty,w});
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
    worklist.push({tuple: t, ty: 'neg', w: 1});
  }
  const result = [];

  for (let i = 0; i < worklist.length; i++) {
    if (i >= maxInner) return { result, cutoff: true };
    const {tuple, ty: dir, w: count} = worklist.get(i);
    const produced = [];

    let matches = dir == 'neg' ? unifyNeg(tuple) : unifyPos(tuple);

    for (const { bindings, remainingBody, head } of matches) {
    // for (const { bindings, remainingBody, head } of [...negMatches, ...posMatches]) {
      for (const sol of solve(remainingBody, bindings, D)) {
        for (const h of head) {
          const derived = applyBindings(h, sol);
          const dkey = Store.key(derived);
          if (D.wouldChange(derived, direction)) {
            worklist.push({tuple: derived, ty: 'pos', w: 1});
            result.push(derived);
            produced.push(derived);
          } else {
            D.updateCurrent(derived, direction);
            D.updateOld(derived);
          }
        }
      }
    }

    let counts = dir == 'neg' ? {neg:count,pos:0} : {neg:0, pos:count};
    if (trace) trace.push({ counts: { ...counts }, tuple, produced });

    // updateOld is idempotent — call once if any neg triggers.
    if (counts.neg > 0) D.updateOld(tuple);
    // updateCurrent once per pos derivation.
    for (let c = 0; c < counts.pos; c++) D.updateCurrent(tuple, direction);
  }

  return { result, cutoff: false };
}

// Compute the well-founded semantics of a program.
// Returns: { log, result, cutoff }
// result: Store — the last stable snapshot
function solveWithLog(facts, rules, derivatives, { maxInner = 10000, maxOuter = 1000, tracing = false } = {}) {
  const { unifyNeg, unifyPos, solve: solveBody } = derivatives;

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
        for (const sol of solveBody(remainingBody, bindings, D)) {
          for (const h of head) {
            const derived = applyBindings(h, sol);
            if (D.wouldChange(derived, +1)) initWorklist.push(derived);
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
    const { result, cutoff } = step(direction, changes, unifyNeg, unifyPos, solveBody, D, maxInner, trace);
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

export { solveWithLog, stepRef, solveRefWithLog };
