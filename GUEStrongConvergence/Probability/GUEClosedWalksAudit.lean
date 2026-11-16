/-
# Axiom audit for the one-shot GUE closed-walk expansion

All declarations in `GUEStrongConvergence.Probability.GUEClosedWalks` must depend only on the
standard logical axioms `propext`, `Classical.choice`, and `Quot.sound`.
-/
import GUEStrongConvergence.Probability.GUEClosedWalks

#print axioms GUEStrongConvergence.guePathLast
#print axioms GUEStrongConvergence.guePathEntries
#print axioms GUEStrongConvergence.guePathLast_nil
#print axioms GUEStrongConvergence.guePathLast_cons
#print axioms GUEStrongConvergence.guePathEntries_nil
#print axioms GUEStrongConvergence.guePathEntries_cons
#print axioms GUEStrongConvergence.guePathSumOneShot
#print axioms GUEStrongConvergence.sum_fin_cons
#print axioms GUEStrongConvergence.guePathSum_eq_oneShot
#print axioms GUEStrongConvergence.gueClosedWalkSum
#print axioms GUEStrongConvergence.gueWickClosedWalk
#print axioms GUEStrongConvergence.gueWord_entry_oneShot
#print axioms GUEStrongConvergence.trace_gueWord_eq_closedWalkSum
#print axioms GUEStrongConvergence.gueNormTrace_eq_closedWalkSum
#print axioms GUEStrongConvergence.integral_trace_gueWord_eq_wick_sum
#print axioms GUEStrongConvergence.integral_gueNormTrace_eq_wick_sum
#print axioms GUEStrongConvergence.gueClosedWalkSum_nil
#print axioms GUEStrongConvergence.gueWickClosedWalk_nil
#print axioms GUEStrongConvergence.integral_gueNormTrace_nil
