/-
# Axiom audit for the common Gaussian probability space

This file records the `#print axioms` audit for every declaration in
`GUEStrongConvergence.Probability.CommonSpace`.  Each theorem must depend only on Lean's
standard logical axioms `propext`, `Classical.choice`, and `Quot.sound`; no project-specific
axiom, `sorry`, or `admit` is permitted.
-/
import GUEStrongConvergence.Probability.CommonSpace

#print axioms GUEStrongConvergence.isProbabilityMeasure_commonGaussianMeasure
#print axioms GUEStrongConvergence.measurePreserving_eval_commonGaussian
#print axioms GUEStrongConvergence.commonGaussianMeasure_map_eval
#print axioms GUEStrongConvergence.hasLaw_eval_commonGaussian
#print axioms GUEStrongConvergence.gueMatrixOn
#print axioms GUEStrongConvergence.gueMatrixOn_isHermitian
#print axioms GUEStrongConvergence.measurable_gueMatrixOn_entry
#print axioms GUEStrongConvergence.measurable_gueMatrix
#print axioms GUEStrongConvergence.measurable_gueMatrixOn
#print axioms GUEStrongConvergence.map_gueMatrixOn
#print axioms GUEStrongConvergence.map_gueMatrixOn_entry
#print axioms GUEStrongConvergence.hasLaw_gueMatrixOn
#print axioms GUEStrongConvergence.integral_gueMatrixOn_mul
#print axioms GUEStrongConvergence.iIndepFun_commonBlocks
#print axioms GUEStrongConvergence.iIndepFun_gueMatrixOn
#print axioms GUEStrongConvergence.stdGaussian_map_toLp_symm
#print axioms GUEStrongConvergence.commonGaussianMeasure_map_coords
#print axioms GUEStrongConvergence.gaussianCoord
#print axioms GUEStrongConvergence.measurable_gaussianCoord
#print axioms GUEStrongConvergence.map_gaussianCoord
#print axioms GUEStrongConvergence.hasLaw_gaussianCoord
#print axioms GUEStrongConvergence.iIndepFun_of_map_eq
#print axioms GUEStrongConvergence.iIndepFun_gaussianCoord
