/-
Axiom audit for the smooth spectral variance module (Lemma V workstream).

Every headline statement is checked to depend only on the three standard axioms of Lean/Mathlib
(`propext`, `Classical.choice`, `Quot.sound`); no `sorry`, `admit` or project axiom is used.
-/
import GUEStrongConvergence.Probability.SmoothSpectralVariance

#print axioms GUEStrongConvergence.hasDerivAt_pow_matrix
#print axioms GUEStrongConvergence.hasDerivAt_trace_pow
#print axioms GUEStrongConvergence.trace_monomialDirection
#print axioms GUEStrongConvergence.trace_polyDirection_eq
#print axioms GUEStrongConvergence.hasDerivAt_trace_polyMatrix
#print axioms GUEStrongConvergence.guePencilMatrix_update_eq
#print axioms GUEStrongConvergence.hasDerivAt_gueStatistic_update
#print axioms GUEStrongConvergence.variance_gueStatistic_le
#print axioms GUEStrongConvergence.variance_gueStatistic_le_of_contraction
