/-
# Axiom audit for GUE matrix words and trace words

All declarations in `GUEStrongConvergence.Probability.GUETraceWords` must depend only on the
standard logical axioms `propext`, `Classical.choice`, and `Quot.sound`.
-/
import GUEStrongConvergence.Probability.GUETraceWords

#print axioms GUEStrongConvergence.gueWord
#print axioms GUEStrongConvergence.gueNormTrace
#print axioms GUEStrongConvergence.guePathSum
#print axioms GUEStrongConvergence.guePathSum_nil
#print axioms GUEStrongConvergence.guePathSum_cons
#print axioms GUEStrongConvergence.gueEntry_mk
#print axioms GUEStrongConvergence.gueWord_entry_pathSum
#print axioms GUEStrongConvergence.trace_gueWord_eq_sum_pathSum
#print axioms GUEStrongConvergence.holder_two_mul
#print axioms GUEStrongConvergence.memLp_finset_sum
#print axioms GUEStrongConvergence.memLp_guePathSum
#print axioms GUEStrongConvergence.integrable_guePathSum
#print axioms GUEStrongConvergence.integrable_trace_gueWord
#print axioms GUEStrongConvergence.integrable_gueNormTrace
#print axioms GUEStrongConvergence.gueWick
#print axioms GUEStrongConvergence.gueWick_nil
#print axioms GUEStrongConvergence.gueWick_cons
#print axioms GUEStrongConvergence.integral_gueProd_eq_gueWick
#print axioms GUEStrongConvergence.integral_gueProd_odd_zero
#print axioms GUEStrongConvergence.gueMatrix_neg
#print axioms GUEStrongConvergence.gueWord_neg
#print axioms GUEStrongConvergence.trace_gueWord_neg
#print axioms GUEStrongConvergence.gueNormTrace_neg
#print axioms GUEStrongConvergence.gueWord_nil
#print axioms GUEStrongConvergence.trace_gueWord_nil
#print axioms GUEStrongConvergence.gueNormTrace_nil
#print axioms GUEStrongConvergence.stdGaussian_isNegInvariant
#print axioms GUEStrongConvergence.integral_trace_gueWord_eq_sum_pathSum
#print axioms GUEStrongConvergence.integral_gueNormTrace_eq_sum_pathSum
#print axioms GUEStrongConvergence.integral_trace_gueWord_odd_zero
#print axioms GUEStrongConvergence.integral_gueNormTrace_odd_zero
