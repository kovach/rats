# Part 1
26/03/19

A *trajectory* is a finite set of tuples and a direction marker (up or down)
step :: Trajectory -> Trajectory
it uses the input trajectory to update *negative matches*
  - for each t in the trajectory:
    - we evaluate all the rules where t unifies with a negative atom
    - for each match, we add or subtract the consequent from the database
      - if the trajectory is up, t represents a newly asserted positive tuple in the over-approx.
        therefore the matches on t were previously inserted, but are no longer valid. we subtract them from the db.
      - conversely, if down, we add them to the db
    - as we add (or subtract), we check for any tuples that transition from (or to) count=0.
      we append these tuples to a list called fresh
  - each of these tuples is a brand new added (or not brand new deleted) tuple
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

