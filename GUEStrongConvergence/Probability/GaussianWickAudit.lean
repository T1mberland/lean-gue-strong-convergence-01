/-
# Axiom audit for Gaussian Wick recursion

Every declaration in `GUEStrongConvergence.Probability.GaussianWick` must depend only on
Lean's standard logical axioms `propext`, `Classical.choice`, and `Quot.sound`.
-/
import GUEStrongConvergence.Probability.GaussianWick

#print axioms GUEStrongConvergence.coordProd
#print axioms GUEStrongConvergence.coordProdDeriv
#print axioms GUEStrongConvergence.coordProdOff
#print axioms GUEStrongConvergence.coordProd_piRecon
#print axioms GUEStrongConvergence.integrable_coordProdOff_pi
#print axioms GUEStrongConvergence.integrable_density_prod_coordProdOff
#print axioms GUEStrongConvergence.integral_coord_mul_coordProd
#print axioms GUEStrongConvergence.gaussianMoment
#print axioms GUEStrongConvergence.wick
#print axioms GUEStrongConvergence.gaussianMoment_eq_wick
#print axioms GUEStrongConvergence.wick_pair
#print axioms GUEStrongConvergence.gaussianMoment_pair
#print axioms GUEStrongConvergence.integral_coordProd_pair
#print axioms GUEStrongConvergence.integral_coord_four
#print axioms GUEStrongConvergence.coordProdDeriv_eq_sum
#print axioms GUEStrongConvergence.hasDerivAt_coordProd
#print axioms GUEStrongConvergence.memLp_coord_pi
#print axioms GUEStrongConvergence.memLp_coord_stdGaussian
#print axioms GUEStrongConvergence.memLp_finProd_one
#print axioms GUEStrongConvergence.integrable_coordProd_pi
#print axioms GUEStrongConvergence.integrable_coordProd_stdGaussian
#print axioms GUEStrongConvergence.integrable_coord_sq
#print axioms GUEStrongConvergence.integrable_coord_sq_mul_coord_sq
#print axioms GUEStrongConvergence.integrable_coord_sq_pi
#print axioms GUEStrongConvergence.integrable_density_prod_const
#print axioms GUEStrongConvergence.integrable_density_prod_coord_sq
#print axioms GUEStrongConvergence.integral_coord_sq_mul_coord_sq
