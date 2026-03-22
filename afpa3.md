new plan
  store (database): maps tuples to pairs of counts
    - the first count is what is used to solve negative atoms. a negative atom succeeds if this count is 0 or the tuple is missing from the store
      - also called *old count*
    - the second count is used for positive atoms. succeeds if >0
      - also called *current count*


step direction changes =
  assume:
    direction = +/- 1
    - direction indicates the direction of changes during *this* step
    changes = list tuple

  result = []
  set = changes.map (\x -> (negative, x))
  while set.length > 0
    (sign, tuple) := pop set
    for ((body, head) in unify sign tuple rules)
      for (sol in solve rest)
        if (wouldChangeIfUpdated store (sub sol head, direction))
          set.push (positive, tuple)
          result.push tuple
    if sign == negative
      updateOld store tuple
    else
      updateCurrent store tuple direction

  return result

- `unify sign tuple rules` finds all the atoms that unify with tuple from rules. if sign positive, it matches positive atoms (otherwise negative)
- solve for the rest of the literals
- wouldChangeIfUpdated checks to see if add/removing (based on direction) to current count would transition to/from zero from/to non-zero value
- updateOld copies current count to old count
- updateCurrent updates current count by adding direction (+/- 1)
- the outer loop calls step with alternating direction. (the first direction after initialization is down, -1)
