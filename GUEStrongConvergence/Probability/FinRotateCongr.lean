/-
# Naturality of `finRotate` under `finCongr`, and `pairOrbitCount` transport invariance

`finRotate` is the cyclic shift on `Fin n`. The value-preserving relabelling `finCongr h`
intertwines the cyclic shifts on the two types (in both orientations), hence conjugation by it
preserves orbit counts. Consequently the number of faces of a pairing is invariant under the
length-preserving transport `GUEPairing.castLength`.
-/
import GUEStrongConvergence.Probability.GUEPairingOrbits
import GUEStrongConvergence.Probability.GUEPairingCast
import GUEStrongConvergence.Probability.GUEPairingGenusSplit
import GUEStrongConvergence.Probability.GUEPairingEar

namespace GUEStrongConvergence

/-- `finRotate` is natural under the value-preserving equivalence `finCongr` (one orientation). -/
lemma finCongr_symm_trans_finRotate_trans_finCongr {m n : ℕ} (h : m = n) :
    (finCongr h).symm.trans ((finRotate m).trans (finCongr h)) = finRotate n := by
  subst h
  ext i
  simp [finRotate]

/-- `finRotate` is natural under `finCongr` (the other orientation, function form). -/
lemma finCongr_finRotate_apply {m n : ℕ} (h : m = n) (i : Fin m) :
    finCongr h (finRotate m i) = finRotate n (finCongr h i) := by
  subst h
  simp [finRotate]

/-- Conjugation by `finCongr` fixes the cyclic shift. -/
lemma conjBy_finCongr_finRotate {m n : ℕ} (h : m = n) :
    conjBy (finCongr h) (finRotate m) = finRotate n := by
  ext i
  rw [conjBy_apply, finCongr_finRotate_apply h]
  simp

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {N : ℕ}

/-- **The face count is invariant under the length-preserving pairing transport.** -/
theorem pairOrbitCount_castLength {l₁ l₂ : List (GUEEntry ι N)} (h : l₁.length = l₂.length)
    (p : GUEPairing l₁) :
    pairOrbitCount (GUEPairing.castLength l₁ l₂ h p) = pairOrbitCount p := by
  have hpartner : partnerPerm (GUEPairing.castLength l₁ l₂ h p)
      = conjBy (finCongr h) (partnerPerm p) := by
    rw [GUEPairing.partnerPerm_castLength]
    rfl
  have hperm : pairOrbitPerm (GUEPairing.castLength l₁ l₂ h p)
      = conjBy (finCongr h) (pairOrbitPerm p) := by
    rw [pairOrbitPerm, hpartner, pairOrbitPerm, conjBy_mul,
      conjBy_finCongr_finRotate h]
  rw [pairOrbitCount, hperm, pairOrbitCount, permOrbitCount_conjBy]

end GUEStrongConvergence
