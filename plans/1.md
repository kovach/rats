# Derp in Rust: Data Structure Sketch

## Context

Derp (DERiving Predicates) is a small Datalog-like fixpoint engine. The hot loop picks tuples from a worklist, applies rules via `specialize` + `eval`, and adds new derived tuples until fixpoint. The Haskell implementation uses `String` keys everywhere, linked-list tuples, assoc-list bindings, and `Set` (balanced BST) for deduplication — all of which have cheaper Rust alternatives.

## 1. String Interning — the foundation

All `Name` and `Pred` strings become a `u32` handle into an intern table. Every comparison, hash, and map key throughout the system becomes O(1).

```rust
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Sym(u32);

pub struct Interner {
    map: HashMap<String, Sym>,
    vec: Vec<String>,           // for Display
}
```

Replaces: `type Name = String`, `type Pred = String` in `Derp/Types.hs:17-18`.

## 2. Term — preserve the enum, shrink payloads

```rust
pub enum Term {
    Var(Sym),                       // was TermVar String
    Pred(Sym),                      // was TermPred String
    Num(i32),                       // was TermNum Int
    Blank,                          // was TermBlank
    App(Sym, Arc<[Term]>),          // was TermApp String [Term]
    Str(Sym),                       // was TermString String — intern these too
}
```

Each string payload drops from 24+ bytes (ptr+len+cap) to 4 bytes. `App` args use `Arc<[Term]>` for cheap cloning since Term is recursive (can't use inline SmallVec). The enum stays 1:1 with the Haskell version — same variants, same semantics.

Source: `Derp/Types.hs:21-28`.

## 3. Tuple — `SmallVec` instead of linked list

```rust
pub type Tuple = SmallVec<[Term; 6]>;
```

Haskell's `[Term]` is a singly-linked list of heap cons cells. `SmallVec<[Term; 6]>` stores up to 6 terms inline with contiguous cache-friendly layout and O(1) indexing. Most Datalog predicates have 2-5 columns.

Source: `Derp/Types.hs:30`.

## 4. Tuples (the relation store) — hash-based

```rust
pub struct Tuples {
    relations: HashMap<Sym, HashSet<Tuple>>,
}
```

Replaces `MMap Pred (Set [Term])` — a BTree of BTrees of linked lists. The #1 hot operation in `iter` (Core.hs:177) is `member` checking to filter duplicates. This goes from O(log n * tuple_cmp_cost) to O(1) amortized. Predicate lookup goes from O(log n * string_len) to O(1).

The `MMap` monoidal merge (union inner sets on key collision) becomes:
```rust
fn insert(&mut self, pred: Sym, tuple: Tuple) -> bool;  // true if new
fn contains(&self, pred: Sym, tuple: &Tuple) -> bool;
fn union_from(&mut self, other: &Tuples);
```

Source: `Derp/Types.hs:42`, `MMap.hs`.

## 5. Worklist — `VecDeque` with `HashSet` dedup

```rust
pub type Worklist = VecDeque<Tuple>;
```

Haskell uses `Set Tuple` for the worklist (for dedup via `pick`/`minView`). Dedup is done by maintaining a separate `HashSet<Tuple>` of all ever-enqueued tuples alongside the `VecDeque`, so duplicate tuples are never enqueued. `pop_front` is O(1) vs `Set.minView`'s O(log n).

Source: `Derp/Core.hs:169-180`.

## 6. Binding — sorted `SmallVec` instead of assoc list

```rust
pub struct Binding {
    entries: SmallVec<[(Sym, Term); 8]>,  // kept sorted by Sym
}
```

Haskell's `Binding { mapping :: [(k,v)] }` is an unsorted assoc list with O(n) lookup. Rules typically bind 2-6 variables, so a sorted `SmallVec` with binary search gives O(log n) lookup (though n is tiny so this is ~2-3 comparisons of `u32`).

Critical: `specialize` on `Join` forks bindings up to 3 ways per tuple. Cheap clone (inline memcpy) matters more than asymptotic lookup speed here. `SmallVec` with 8 inline slots avoids heap allocation for most rules.

Drop `bdeps` field — it's marked unused (`Derp/Types.hs:45`).

Source: `Binding.hs:15`, `Derp/Types.hs:46`.

## 7. Expression, Closure, Rule — direct translation

```rust
pub enum Expr {
    Atom(Tuple),
    NegAtom(Tuple),
    Bind(Term, Term),
    Join(Box<Expr>, Box<Expr>),  // Box for recursion
    Unit,
}

pub struct Closure { pub ctx: Binding, pub val: Expr }
pub type CE = Closure;

pub struct Rule { pub body: CE, pub head: Vec<Tuple> }
```

These are 1:1 with the Haskell. `Join` needs `Box` because Rust enums must be sized. `Thunk` can likely be eliminated (deps are unused per `Types.hs:49-50`).

## 8. `iter` — while loop instead of tail recursion

The Haskell `iter` is tail-recursive with `case pick ts`. In Rust this becomes an explicit `while let` loop — idiomatic and avoids stack depth issues.

```rust
fn iter(step: impl Fn(&Tuple, &Tuples, &Tuples) -> Vec<Vec<Tuple>>,
        worklist: &mut Worklist, db: &mut Tuples, check: &Tuples) { ... }
```

`altIter` (two forward passes for negation) translates directly.

## Summary table

| Haskell | Rust | Rationale |
|---------|------|-----------|
| `String` (Name/Pred) | `Sym` (u32) | O(1) compare/hash |
| `[Term]` (Tuple) | `SmallVec<[Term; 6]>` | Contiguous, inline |
| `[Term]` in TermApp | `Arc<[Term]>` | Cheap clone, heap-shared |
| `Map Pred (Set [Term])` | `HashMap<Sym, HashSet<Tuple>>` | O(1) lookup + member |
| `Set Tuple` (worklist) | `VecDeque` + `HashSet` dedup | O(1) push/pop |
| `[(Name, Term)]` (Binding) | Sorted `SmallVec<[(Sym, Term); 8]>` | Cheap clone, inline |

## Crate dependencies

Only `smallvec` matters for the core engine. `hashbrown` optional (std `HashMap` is fine).

## Key files to reference during implementation

- `src/Derp/Types.hs` — all type definitions (lines 17-59)
- `src/Derp/Core.hs` — eval, specialize, iter, altIter (the whole runtime)
- `src/Binding.hs` — unification and variable binding
- `src/MMap.hs` — monoidal map semantics to replicate
- `src/Derp/Parse.hs` — parser to port

## Conversation log

> Implement the following plan:
> you can install the rust LSP analyzer plugin
> try running it on test.derp
> try running it on test.derp with a timeout of 3 seconds
> try running it on out.derp, but bisect the file: first run on only the first rule, then teh first two, and so on. use a timeout of 3 seconds for each. stop as soon as you find the prefix that hits the timeout.
... want to reuse bisect feature eventually
> follow the previous instruction by writing a rust function instead of bash.
... it generated a bash file to count through out.derp to find the rule that timed out
> it's the rule that uses `#range`.
...notice that terms are always being cloned
> can you produce a profiling report for `out.derp`
> i just installed perf and `cargo flamegraph`. try those again
> make App args use Arc<[Term]>
> rerun the perf report
> print the number of tuples generated at the end of main
> write the plan you initially used to an `.md` file
> append each of the statements I made to the end of the plan verbatim
