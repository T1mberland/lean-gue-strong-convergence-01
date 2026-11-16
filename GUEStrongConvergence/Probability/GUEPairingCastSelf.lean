/-
# Bridges between `Eq.rec`-transports and `GUEPairing.castLength`

`GUEPairing.castLength` transports pairings between entry lists of equal length. The two lemmas
below identify its identity-instance and its relation to `Eq.rec`, which is what the
`partner`-recursion (stated with dependent list equality) needs.
-/
import GUEStrongConvergence.Probability.GUEPairingCast

namespace GUEStrongConvergence.GUEPairing

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {N : ℕ}

/-- `castLength` along the identity length equality is the identity. -/
theorem castLength_self : (l : List (GUEEntry ι N)) → (p : GUEPairing l) →
    castLength l l rfl p = p
  | _, .nil => rfl
  | _, .cons e l k p => by
    rw [castLength_cons]
    congr 1
    · exact castLength_self (l.eraseIdx k) p

/-- The `Eq.rec` transport of a pairing is the `castLength` transport. -/
theorem eqRec_eq_castLength {l₁ l₂ : List (GUEEntry ι N)} (h : l₁ = l₂)
    (p : GUEPairing l₁) :
    (h ▸ p) = castLength l₁ l₂ (congrArg List.length h) p := by
  cases h
  exact (castLength_self l₁ p).symm

end GUEStrongConvergence.GUEPairing
