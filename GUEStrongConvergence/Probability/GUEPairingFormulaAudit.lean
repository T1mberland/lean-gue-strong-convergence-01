/-
# Axiom audit for the explicit GUE pairing formula

All declarations in `GUEStrongConvergence.Probability.GUEPairingFormula` must depend only on
the standard logical axioms `propext`, `Classical.choice`, and `Quot.sound`.
-/
import GUEStrongConvergence.Probability.GUEPairingFormula

#print axioms GUEStrongConvergence.GUEPairing
#print axioms GUEStrongConvergence.GUEPairing.weight
#print axioms GUEStrongConvergence.GUEPairing.weight_nil
#print axioms GUEStrongConvergence.GUEPairing.weight_cons
#print axioms GUEStrongConvergence.GUEPairing.consEquiv
#print axioms GUEStrongConvergence.GUEPairing.fintype
#print axioms GUEStrongConvergence.sum_sigma_univ
#print axioms GUEStrongConvergence.gueWick_eq_sum_pairing
#print axioms GUEStrongConvergence.integral_gueProd_eq_sum_pairing
