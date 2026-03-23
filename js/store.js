import { prettyAtom } from './parse-rule.js';

class TupleSet {
  #it = new Set();
  insert(tuple) {
    const key = Store.key(tuple);
    this.#it.add(key);
  }
  [Symbol.iterator]() {
    return (function*(map) {
      for (const key of map) yield JSON.parse(key);
    })(this.#it);
  }

}

// Store wraps the incremental evaluator's database.
// D: { old: number, current: number } per tuple
//   old:     used for negative literal visibility (old === 0 → neg succeeds)
//   current: used for positive literal visibility (current > 0 → pos succeeds)

class Store {
  #map = new Map();

  static key(tuple) { return JSON.stringify(tuple); }

  negVisible(tuple) {
    const e = this.#map.get(Store.key(tuple));
    return !e || e.old === 0;
  }

  posVisible(tuple) {
    const e = this.#map.get(Store.key(tuple));
    return !!e && e.current > 0;
  }

  wouldChange(tuple, direction) {
    const e = this.#map.get(Store.key(tuple));
    const c = e ? e.current : 0;
    return (c === 0) !== (c + direction === 0);
  }

  updateOld(tuple) {
    const key = Store.key(tuple);
    const e = this.#map.get(key) ?? { old: 0, current: 0 };
    this.#map.set(key, { old: e.current, current: e.current });
  }

  prune() {
    const toDelete = [];
    for (const [key, e] of this.#map) {
      if (e.old === 0 && e.current === 0)
        toDelete.push(key);
    }
    for (const k of toDelete) this.#map.delete(k);
  }

  updateAllOld() {
    for (const [_key, e] of this.#map) {
      e.old = e.current;
    }
  }

  updateCurrent(tuple, direction) {
    const key = Store.key(tuple);
    const e = this.#map.get(key) ?? { old: 0, current: 0 };
    if (e.current + direction < 0) throw 'no';
    this.#map.set(key, { old: e.old, current: e.current + direction });
  }

  snapshot() {
    const s = new Store();
    s.#map = new Map(this.#map);
    return s;
  }

  get size() { return this.#map.size; }

  equals(other) {
    // if (this.#map.size !== other.#map.size) return false;
    for (const [key, e] of this.#map) {
      const o = other.#map.get(key);
      if (!o || o.old !== e.old || o.current !== e.current) {
        console.log('!!!!!!!!!!!!!!\n', key, e, o);
        return false;
      }
    }
    return true;
  }

  checkStable() {
    for (const [key, e] of this.#map) {
      if (e.old !== e.current)
        return key;
    }
    return null;
  }

  // Iterate all entries as [tuple, {old, current}]
  [Symbol.iterator]() {
    return (function*(map) {
      for (const [key, e] of map) yield [JSON.parse(key), e];
    })(this.#map);
  }

  pretty() {
    const ts = this.activeTuples().map(([t]) => prettyAtom(t));
    if (ts.length === 0) return '';
    return '-- ' + ts.join(', ') + '.';
  }

  pretty2() {
    const ts = [];
    for (const [key, e] of this.#map)
      if (e.current > 0) ts.push([prettyAtom(JSON.parse(key)), e.old, e.current]);
    ts.sort(([a], [b]) => Store.key(a).localeCompare(Store.key(b)));
    return JSON.stringify(ts);
  }

  // Sorted active tuples as [tuple, count] for rendering
  activeTuples() {
    const ts = [];
    for (const [key, e] of this.#map)
      if (e.current > 0) ts.push([JSON.parse(key), e.current]);
    ts.sort(([a], [b]) => Store.key(a).localeCompare(Store.key(b)));
    return ts;
  }
}

export { Store, TupleSet };
