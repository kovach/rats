# 26/02/21
## join re-ordering
probably should index predicates before this will do much

### prompt
[ ] reorder joins (prefer eq_bf, lt_bb)
  - change the optimize_with function
    - write a helper: given current bound, extract the first `lt` or `le` predicate atom whose arguments are both bound.
    - write a helper: given current bound, extract the first `eq`-predicate atom whose arguments are both bound.
    - write a helper: given current bound, extract the first `eq`-predicate atom with exactly one bound argument
    - write a helper: given current bound, extract the first atom that is not `lt`, `le`, or `eq`
    - algorithm:
      - apply the helpers in the given order, taking the first one that returns `Some`.
      - loop until done, as is currently written
  - call this function inside `prespecialize`, only in the "non-trivial body" case
    - use the `seen` value computed over `pats` to kick off the optimization process.
    - optimize should be called just before `compile_expr(remaining, ...)`.

### result
- reordering introduces a large slowdown (~10x). need to investigate later.
- guard it with a flag.
- it worked around an error in the prompt (it's missing the default case) but instead of adding a 5th case, it didn't implement the 4th case.

# 26/02/20
## hash-consing terms
### prompt
let's try to implement something like "hash cons" for our Term constructors.
we want to reduce the complexity of the terms being hashed.
To do this we will build a data structure ("term table") with the following interface:
  - store : Term -> Id
      Whenever a new Term is inserted, it will be granted a fresh id; if already present, the old id is returned.
  - get : Id -> &Term
      Return a ref to the Term that corresponds to Id

We will add a new branch `Term::TermId` to the Term type (but not the `CTerm` type) which takes an Id and represents a stored term.

In practice, for now we will only store `Term:App` values in our term table.
Whenever we build a `Term::App`, we will store it in this table and use the id returned in its place.

A few notes about functions to change:
- `sub_term_compiled`: this function will invoke the new feature in the `CTerm::App` branch.
  the other branches should stay the same
- `match_term_compiled`: if `pat` is App and val is `TermId`, lookup the id and unify the `Term`.
  - The other cases should not need to change.
- This is not a complete list of functions to change.

A new invariant we would like to check using a couple of tests:
- any member of the Tuples data structures generated during evaluation should not contain any `Term::App` constructors (they should all be id'd instead).
- any key stored in the term table should be a Term::App that is applied only to terms that are *not* App.

### result
5062bb8a60f6fa1558a7d8fed714ee931f719b8a
  [CLAUDE] ...
fc1e76d92a89123169ff902de16d6c18b578ab9c
    fix correctness error: only unfold app terms when needed to unify

# 26/02/16
## optimize binding use
  - add a compilation step that identifies where each variable is set (once per query) vs unified (every other reference).
    removes need for binding scope operations
  - claude overwrote its initial plan at some point, before I copied it over
    - the new [plan](plans/5.md) was generated when I instructed to eliminate a weird and overcomplicated indirection it introduced while compiling
      - this was easily fixed
  - created a parallel AST (CTerm, CExpr) for this representation, which seems unnecessary.
    - I asked why, and it gave a plausible justification: would have required modifying more existing code

## specialize rules once at startup
  - af752c6f74ae
  - see [plan](plans/4.md)
  - This was a more substantial change with very little prompting required.
    Its initial approach was incorrect, but it corrected it only being told a test failed.

# 26/02/14
## use serde
  - see [plan](plans/3.md)

# 26/02/12
## server
  - 9d0e7fa96
  - watch input files, compose hs/rs operations, better rendering.

## fix allocations
  - see [plan](plans/2.md)
  - also switched to mutable binding usage pattern

## automatic port derp implementation to rust:
  - 13b6110 [CLAUDE,UNREVIEWED] used claude to mostly automatically port Derp to rust. performance is still not significantly better; need to improve ownership structure
  - see [plan](plans/1.md)
  - some remaining issues:
    - [scott] review
    - parser should use combinators
    - too much copying
  - anecdotes:
    - after the first pass on the code, claude tried to generate a derp program for testing.
      its output had a minor error (wrote `foo a.` instead of `-- foo a.`, like traditional syntax),
      failed to parse, it read the parse error (from the parser it had just implemented) and fixed.

# 26/02/11
used claude code to make starter code for a webserver, generate a simple html view, and make a new module:

  - 938fb86 Move Derp modules into Derp/ subpackage, split types from core
  - 4c5a5b6 Serialize Tuples to JSON, serve HTML view over WebSocket
  - b8412a6 Add web server with warp + wai-websockets + aeson
