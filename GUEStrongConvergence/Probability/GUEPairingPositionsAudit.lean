/-
# Axiom audit for the positional GUE partner permutation

All declarations in `GUEStrongConvergence.Probability.GUEPairingPositions` must depend only on
the standard logical axioms `propext`, `Classical.choice`, and `Quot.sound`.
-/
import GUEStrongConvergence.Probability.GUEPairingPositions

#print axioms GUEStrongConvergence.eraseIndex
#print axioms GUEStrongConvergence.succAbove_eraseIndex
#print axioms GUEStrongConvergence.eraseIndex_succAbove
#print axioms GUEStrongConvergence.partner
#print axioms GUEStrongConvergence.partner_cons_zero
#print axioms GUEStrongConvergence.partner_cons_head
#print axioms GUEStrongConvergence.partner_cons_other
#print axioms GUEStrongConvergence.pred_ne_of_ne_succ
#print axioms GUEStrongConvergence.partner_ne_self
#print axioms GUEStrongConvergence.partner_involutive
#print axioms GUEStrongConvergence.partnerPerm
#print axioms GUEStrongConvergence.partnerPerm_apply
#print axioms GUEStrongConvergence.partnerPerm_involutive
#print axioms GUEStrongConvergence.partnerPerm_ne_self
#print axioms GUEStrongConvergence.partnerPerm_bijective
