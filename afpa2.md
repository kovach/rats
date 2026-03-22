# Part 1
26/03/19

A *trajectory* is a finite set of tuples and a direction marker (up or down)
step :: Trajectory -> Trajectory
the AFP algorithm computes a series of alternating trajectories until reaching a fixpoint; either:
  - empty trajectory (all atoms get truth value from most recent iteration)
  - a pair of adjacent trajectories that are equal in opposite directions (they contain the atoms with no truth value)

step uses the input trajectory to update *negative matches*
  - (phase 1) for each t in the trajectory:
    - we evaluate all the rules where t unifies with a negative atom
    - for each match, we add or subtract the consequent from the database
      - if the trajectory is up, t represents a newly asserted positive tuple in the over-approx.
        therefore the matches on t were previously inserted, but are no longer valid. we subtract them from the db.
      - conversely, if down, we add them to the db
    - as we add (or subtract), we check for any tuples that transition from (or to) count=0.
      we append these tuples to a list called fresh
  - (phase 2) each of these tuples is a brand new added (or not brand new deleted) tuple
    - we need to update the fixpoint with respect to these changes to positive slots.
    - now we step through the list, and for each t:
      - evaluate all the rules where t unifies with a positive atom
      - for each match, add or subtract the consequent from the database (use the same sign as we did in the first step)
      - as we encounter fresh atoms, we append them to the fresh list that we're traversing
      - once we reach the end of fresh, we output a new trajectory: (fresh, opposite sign). we use the opposite of the input sign

# Part 2
solve :: Program -> Database
this function computes a fixpoint using step. first though, it needs to initialize things in a particular way.

the input program is a pair of (fact set, rule set)
compute an initial fixpoint starting from the facts and assuming everything is false (D and `D_last` is empty)
everything fresh (including the facts) is included in an UP trajectory.
now we repeatedly apply `step` (step depends on the rule set but not the fact set)
- if step returns an empty trajectory, halt
- if two consecutive traces ever contain the same tuple set, halt. return the value of D from the last step that yielded a DOWN trajectory (the last underapproximation)

# Part 3
see [asdf](notes-on-query-derivative.md)

# Part 4
26/03/20

We need to be more careful about the database state we use at each step of incremental evaluation.
We also need to justify the claim that *DOWN* steps can be done by simply removing tuples, computing their prior consequences using the state we have, and iteratively removing them.

define multiplicity fixpoint
  ? fixpoint for operator that maps program to *derivation (rule match, head tuple) set* as opposed to *tuple set*

## down step
> We also need to justify the claim that *DOWN* steps can be done by simply removing tuples, computing their prior consequences using the state we have, and iteratively removing them.

When we update the neg database, we just need to
- pick out the derivations that used them (standard one at a time semi-naive)
- handle any tuple that became relationally false (also to be done one at a time)
- during phase 2, we don't need to worry about the state of the neg tuples that were undone, because every derivation that used one of those rules was handled immediately in phase 1
  (any other rules with negative atoms were negative atoms that didn't change in phase 1, so their state is simple)
- I think this is a fixpoint, and the right one
  - at the end of the day we have a function thats monotone in two arguments, and we're reducing one of the arguments, then reducing the fixpoint on the other, so this should be easy to check and prove

*BACKGROUND IDEA*: we modify the *store* to store two counts for each tuple: the value prior to the last update and the updated value.
- If exactly one of these values is 0, call the tuple unstable; If these two values are equal, call it simple; otherwise modified.
  We *resolve* a tuple by setting (prior = update, update = update).
  After a fixpoint, we can immediately resolve the modified tuples.
- We need to resolve the unstable tuples one at a time.
  We use these as state for semi-naive: we process the pending tuples. when we process t, we make it stable (by setting (prior = update, update = update))

!a -> b.
!c -> d.
b,d -> e.

suppose neg set went from {a,c} to {}.
all proofs need to be removed.
remove b, then d. when removing b, d still present, so join in r3 passes, we remove e.
when removing d, b has been removed. no join on r3.

  !a -> b.
  b, !c -> d.
  b,d -> e.

  notes:


!a, !c -> b.
when undoing {a}, c still present, so we undo b once. then we undo c, but a present, so no duplicate.

*return value*
during phase 2, some tuples become false. we need to yield these to the next step (which we do by leaving them unstable)
  so we *do not* *resolve* the unstable positive tuples, we store them in an array and remove their derivations but leave them as q[n -> 0] in the store

## up step
So, some tuples have become unstable in the ->0 direction.
say q[->0]

p, !q -> r.
r, !q -> s.

during the fixpoint, we need to process r[0 -> 1] to derive s
  this is different than the down step, where the negative part is constant, so we didn't have to handle q[->0] type transitions mid iteration
  no i'm analogizing to the wrong thing: i did miss something
we also need to *return* the fact that r[0 -> n>0] to the next phase

## what state

the store maps tuples (q) to counts (0,1,2,...)
each q is in one of these states:
  1  stable
  2  unstable wrt current phase 1 or phase 1 of next step
  3  unstable wrt current fixpoint (needs to touch pos atoms during 2)
if q is not in the store (because it has count 0) we say that it is in state 1

- at the start of step, every tuple is in state 1 or 2
- after phase 1, every tuple is in state 1 or 3
- after phase 2, every tuple is in state 1 or 2

what phase 1 and 2 have in common:
  we pop pick tuples one at a time, plug them into a specialized query, and then evaluate the rest of the query
  the result is a tuple delta (if DOWN, delta is negative) which we apply to the store, and possibly get back some tuples that transitioned
  these transitioned tuples go from state 1 to state 3 (if in phase 1) or state 2 (if in phase 2)

what differs:
  in phase 1, the tuples we pick get unified with *negative* atoms, and in phase 2 positive atoms
  when evaluating "the rest of the query" we need to use specialized subsets of the store (see below)

summary:
  any modification updates the count immediately
    if q transitions during phase 1, mark it as state 3 [1 -> 3]
      as we resolve during phase 1, mark [2 -> 1] (only state-1 tuples participate in neg-atom queries)
    if q transitions during phase 2, mark it as state 3 [1 -> 3]
      as we resolve during phase 2, mark [3 -> 2]
  query liveness during phases
    phase 1:
      pick q with state 2
      q changed state on previous iteration. in this phase, unify it with negative atoms, solve query
      then q[2] -> q[1]
      DOWN:
        q is something that became *true* at previous step, so participated in matches that might be undone
        pos atoms query q[1] or q[2] or q[3]
        neg atoms query (not q[1])
        - q[3] is something becoming false, so it was true before, and participates in phase 1 removals
        output is negative
      UP:
        new neg with old pos
        pos atoms query q[1]
        neg atoms query (not q[1])
        - q[2] become false at previous step
        - q[3] is becoming true, will be handled in phase 2
        output is positive
    phase 2:
      initially all atoms in state 1 or 3; can do [1 -> 2] as you go
      pick 3; 3 -> 2
      unify 3 with pos atom
      DOWN:
        pos atoms query q[1] or q[3] (1: unchanged. 3: being removed, but not handled yet)
        neg atoms query (not q[1]) don't include the things becoming false now (3 or 2)
        atoms can transition from 1 (positive count) to 3 (0 count)
        output is negative
      UP:
        pos atoms query q[1] or q[2] (1: unchanged. 2: being added, handled earlier)
        neg atoms query (not q[1])
        atoms can transition from 1 (0 count) to 3 (positive count)
        output is positive

some changes to make:
  - the specialization code needs to also specialize by negative atoms
  - these logic changes need to be applied to makeEvalFn; we need probably several versions that step can call
  - need to update the store data structure
  - what else?

# fixing states
26/03/21

i added a bunch of temporary logging and fixed an issue: in the terminology of the reference doc, I was using UP/DOWN to refer to the direction that the *current* iteration is going, not the direction of the previous trajectory. so I flipped a couple of signs to fix that.

i've now realized that some of the instructions were wrong.
the problem is that a tuple can be in state 2, and be transitioned to state 3 during phase 1.
phase 1 tries to move tuples from 2->1, but might also move a tuple ->3
so they are not being handled properly. we need to
- modify store to hold two counts: the previous iteration count and the current one
- at the start of step, we copy the current count to the old count.
- during step, current count can change but old count stays constant
- old count is used to determine



