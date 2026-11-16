/-
# Block-diagonal factorization of the two-walk slot sum: the unconditional `hblock`

This file finishes the block-diagonal factorization `hblock` of the variance chain, using the
critical-path partner lemma `GUEPairing.partner_append_aux` (in `GUEPairingAppendPartner`).

## What is proved here

* `partnerPerm_append`: the partner permutation of a juxtaposition `append l₁ l₂ p₁ p₂` is the
  conjugate by `finSumFinEquiv` of the direct sum `partnerPerm p₁ ⊞ partnerPerm p₂`
  (up to the length equality `(l₁ ++ l₂).length = l₁.length + l₂.length`).
* the loop-count split for juxtaposed slot pairings, via `twoWalkLoopCount_sumCongr`.
* `slotCross_iff_not_blockDiag`: a slot pairing crosses the two blocks iff it is not
  block-diagonal.
* `hblock`: the non-crossing part of the slot pairing sum is the square of the one-walk genus sum.

No `sorry`/axiom is used.
-/
import GUEStrongConvergence.Probability.GUEPairingAppendPartner
import GUEStrongConvergence.Probability.GUEPairingGenusSplit

open MeasureTheory ProbabilityTheory Filter
open scoped RealInnerProductSpace Matrix ENNReal Topology

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false
set_option linter.unusedVariables false
set_option linter.deprecated false
set_option linter.unusedSimpArgs false

namespace GUEStrongConvergence

attribute [local instance] Classical.propDecidable

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {N : ℕ}

namespace GUEPairing

variable {l₁ l₂ : List (GUEEntry ι N)}

/-- **The partner permutation of a juxtaposition** is the conjugation by `finSumFinEquiv` of the
direct sum of the two partner permutations. -/
theorem partnerPerm_append (p₁ : GUEPairing l₁) (p₂ : GUEPairing l₂) :
    (finCongr (by rw [List.length_append])).permCongr
        (partnerPerm (append l₁ l₂ p₁ p₂)) =
      finSumFinEquiv.permCongr ((partnerPerm p₁).sumCongr (partnerPerm p₂)) := by
  apply Equiv.ext
  intro b
  rw [Equiv.permCongr_apply, Equiv.permCongr_apply]
  cases b using Fin.addCases with
  | left i =>
    have hidx : (Fin.cast (by rw [List.length_append] : (l₁ ++ l₂).length =
          l₁.length + l₂.length).symm (Fin.castAdd l₂.length i) : Fin (l₁ ++ l₂).length) =
        (⟨i.val, by rw [List.length_append]; exact Nat.lt_add_right _ i.isLt⟩ :
          Fin (l₁ ++ l₂).length) := Fin.ext rfl
    simp only [finSumFinEquiv_symm_apply_castAdd, Equiv.Perm.sumCongr_apply, Sum.map_inl,
      finSumFinEquiv_apply_left, finCongr_symm_apply, finCongr_apply_coe, partnerPerm_apply,
      Fin.val_castAdd, hidx]
    apply Fin.ext
    simpa using (partner_append_aux l₁.length l₁ rfl l₂ p₁ p₂).1 i
  | right j =>
    have hidx : (Fin.cast (by rw [List.length_append] : (l₁ ++ l₂).length =
          l₁.length + l₂.length).symm (Fin.natAdd l₁.length j) : Fin (l₁ ++ l₂).length) =
        (⟨l₁.length + j.val, by rw [List.length_append]; omega⟩ :
          Fin (l₁ ++ l₂).length) := Fin.ext rfl
    simp only [finSumFinEquiv_symm_apply_natAdd, Equiv.Perm.sumCongr_apply, Sum.map_inr,
      finSumFinEquiv_apply_right, finCongr_symm_apply, finCongr_apply_coe, partnerPerm_apply,
      Fin.val_natAdd, hidx]
    apply Fin.ext
    simpa using (partner_append_aux l₁.length l₁ rfl l₂ p₁ p₂).2 j

/-! ### Conjugation calculus -/

section ConjBy

variable {α β γ : Type*}

/-- `conjBy` is the transport of a permutation along a bijection, written as a composition. -/
theorem conjBy_eq_trans (e : α ≃ β) (σ : Equiv.Perm α) :
    conjBy e σ = e.symm.trans (σ.trans e) := by
  apply Equiv.ext
  intro b
  rfl

/-- Composition of two conjugations. -/
theorem conjBy_trans' (e : α ≃ β) (e' : β ≃ γ) (σ : Equiv.Perm α) :
    conjBy e' (conjBy e σ) = conjBy (e.trans e') σ := by
  apply Equiv.ext
  intro b
  rfl

/-- `conjBy` is `Equiv.permCongr`. -/
theorem conjBy_eq_permCongr (e : α ≃ β) (σ : Equiv.Perm α) :
    conjBy e σ = e.permCongr σ := by
  apply Equiv.ext
  intro b
  rfl

/-- Conjugating the cyclic shift by a length identification gives the cyclic shift. -/
theorem permCongr_finRotate {m k : ℕ} (h : m = k) :
    (finCongr h).permCongr (finRotate m) = finRotate k := by
  subst h
  rfl

/-- Two successive conjugations compose into one. -/
theorem permCongr_permCongr {α β γ : Type*} (e : α ≃ β) (e' : β ≃ γ)
    (σ : Equiv.Perm α) :
    e'.permCongr (e.permCongr σ) = (e.trans e').permCongr σ := by
  apply Equiv.ext
  intro b
  rfl

end ConjBy

/-- **The conjugated partner permutation of a juxtaposition.**  For a pairing of `l₁ ++ l₂`
transported to the index type `Fin (k₁ + k₂)` along the length equalities, the partner
permutation is the `finSumFinEquiv`-conjugate of the direct sum of the two transported block
partner permutations. -/
theorem conjBy_partnerPerm_append {k₁ k₂ : ℕ} {l₁ l₂ : List (GUEEntry ι N)}
    (h₁ : l₁.length = k₁) (h₂ : l₂.length = k₂)
    (p₁ : GUEPairing l₁) (p₂ : GUEPairing l₂) :
    conjBy (finCongr (by rw [List.length_append, h₁, h₂]))
        (partnerPerm (GUEPairing.append l₁ l₂ p₁ p₂)) =
      finSumFinEquiv.permCongr
        (((finCongr h₁).permCongr (partnerPerm p₁)).sumCongr
          ((finCongr h₂).permCongr (partnerPerm p₂))) := by
  apply Equiv.ext
  intro b
  rw [conjBy_apply, Equiv.permCongr_apply]
  cases b using Fin.addCases with
  | left i =>
    have hidx : ((finCongr (by rw [List.length_append, h₁, h₂] :
          (l₁ ++ l₂).length = k₁ + k₂)).symm
          (Fin.castAdd k₂ i) : Fin (l₁ ++ l₂).length) =
        (⟨(Fin.cast h₁.symm i).val, by
          rw [List.length_append]; exact Nat.lt_add_right _ (Fin.cast h₁.symm i).isLt⟩ :
          Fin (l₁ ++ l₂).length) := Fin.ext (by simp)
    have hb : (finSumFinEquiv.symm (Fin.castAdd k₂ i) : Fin k₁ ⊕ Fin k₂) = Sum.inl i := by
      rw [finSumFinEquiv_symm_apply_castAdd]
    simp only [hidx, hb, Equiv.Perm.sumCongr_apply, Sum.map_inl, Equiv.permCongr_apply,
      finSumFinEquiv_apply_left, partnerPerm_apply, finCongr_apply_coe, Fin.val_castAdd]
    apply Fin.ext
    simpa using (GUEPairing.partner_append_aux l₁.length l₁ rfl l₂ p₁ p₂).1
      (Fin.cast h₁.symm i)
  | right j =>
    have hidx : ((finCongr (by rw [List.length_append, h₁, h₂] :
          (l₁ ++ l₂).length = k₁ + k₂)).symm
          (Fin.natAdd k₁ j) : Fin (l₁ ++ l₂).length) =
        (⟨l₁.length + j.val, by
          rw [List.length_append]; have := j.isLt; omega⟩ : Fin (l₁ ++ l₂).length) :=
        Fin.ext (by simp only [finCongr_symm_apply_coe, Fin.val_natAdd]; omega)
    have hb : (finSumFinEquiv.symm (Fin.natAdd k₁ j) : Fin k₁ ⊕ Fin k₂) = Sum.inr j := by
      rw [finSumFinEquiv_symm_apply_natAdd]
    simp only [hidx, hb, Equiv.Perm.sumCongr_apply, Sum.map_inr, Equiv.permCongr_apply,
      finSumFinEquiv_apply_right, partnerPerm_apply, finCongr_apply_coe, Fin.val_natAdd]
    apply Fin.ext
    simpa [h₁] using (GUEPairing.partner_append_aux l₁.length l₁ rfl l₂ p₁ p₂).2
      (Fin.cast h₂.symm j)

/-- **The slot permutation of a juxtaposed slot pairing**, written in block form. -/
theorem slotPerm_append_eq {w : List ι}
    (V : Fin (w.length + w.reverse.length) → Fin N)
    (p : GUEPairing (slotBlock₁ w V ++ slotBlock₂ w V)) :
    slotPerm ((slotList_eq_append w V).symm ▸ p) =
      conjBy (finCongr (by rw [List.length_append, length_slotBlock₁, length_slotBlock₂] :
          (slotBlock₁ w V ++ slotBlock₂ w V).length = w.length + w.reverse.length))
        (partnerPerm p) := by
  have hAB : (slotBlock₁ w V ++ slotBlock₂ w V).length = (slotList w V).length :=
    congrArg List.length (slotList_eq_append w V).symm
  have hcast : ((slotList_eq_append w V).symm ▸ p) =
      GUEPairing.castLength (slotBlock₁ w V ++ slotBlock₂ w V) (slotList w V) hAB p :=
    eqRec_eq_castLength (slotList_eq_append w V).symm p
  rw [hcast, slotPerm, partnerPerm_castLength]
  rw [show ((finCongr hAB).symm.trans
        ((partnerPerm p).trans (finCongr hAB))) =
      (finCongr hAB).permCongr (partnerPerm p) from
    (Equiv.permCongr_def (finCongr hAB) (partnerPerm p)).symm]
  rw [conjBy_eq_permCongr, conjBy_eq_permCongr, permCongr_permCongr]
  congr 1

/-- **The loop-count split for a juxtaposed slot pairing**: the two-walk loop count of the
juxtaposition of the two slot blocks is the sum of the two single-walk face counts. -/
theorem twoWalkLoopCount_slotPerm_append {w : List ι}
    (V : Fin (w.length + w.reverse.length) → Fin N)
    (p₁ : GUEPairing (slotBlock₁ w V)) (p₂ : GUEPairing (slotBlock₂ w V)) :
    twoWalkLoopCount w.length w.reverse.length
        (slotPerm ((slotList_eq_append w V).symm ▸
          GUEPairing.append (slotBlock₁ w V) (slotBlock₂ w V) p₁ p₂)) =
      pairOrbitCount p₁ + pairOrbitCount p₂ := by
  rw [slotPerm_append_eq]
  rw [conjBy_partnerPerm_append (length_slotBlock₁ w V) (length_slotBlock₂ w V)
    p₁ p₂]
  rw [twoWalkLoopCount_sumCongr]
  congr 1
  · rw [← permCongr_finRotate (length_slotBlock₁ w V), ← Equiv.permCongr_mul,
      permOrbitCount_permCongr]
    rfl
  · rw [← permCongr_finRotate (length_slotBlock₂ w V), ← Equiv.permCongr_mul,
      permOrbitCount_permCongr]
    rfl

/-! ### No-crossing pairings are block diagonal -/

/-- The "no pair crosses the block boundary" condition: the partner of every position of the
first block stays in the first block. -/
def NoCrossList (l₁ l₂ : List (GUEEntry ι N)) (q : GUEPairing (l₁ ++ l₂)) : Prop :=
  ∀ i : Fin l₁.length,
    (partner (l₁ ++ l₂) q
      ⟨i.val, by rw [List.length_append]; exact Nat.lt_add_right _ i.isLt⟩).val < l₁.length

/-- Arithmetic: if the insertion of `y` at `k` lands below `m + 1` and `k ≤ m`, then `y` lands
below `m`. -/
theorem val_lt_of_succAbove_val_lt {n m : ℕ} (k : Fin (n + 1)) (y : Fin n)
    (hk : k.val ≤ m) (h : (k.succAbove y).val < m + 1) : y.val < m := by
  rw [val_succAbove] at h
  split_ifs at h with hy <;> omega

/-- **A pairing with no crossing pair is block diagonal** (induction on the length of the first
block). -/
theorem blockDiag_of_noCross_aux : ∀ (n : ℕ) (l₁ : List (GUEEntry ι N)), l₁.length = n →
    ∀ (l₂ : List (GUEEntry ι N)) (q : GUEPairing (l₁ ++ l₂)), NoCrossList l₁ l₂ q →
      BlockDiag l₁ l₂ q := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro l₁ hl l₂ q hq
    cases l₁ with
    | nil =>
      exact ⟨GUEPairing.nil, q, rfl⟩
    | cons e l =>
      cases l with
      | nil =>
        cases q with
        | cons e' T k p =>
          cases l₂ with
          | nil => exact Fin.elim0 k
          | cons y l₂' =>
            have h0 : (partner (e :: (y :: l₂')) (GUEPairing.cons e (y :: l₂') k p)
                (0 : Fin (e :: (y :: l₂')).length)).val < (e :: ([] : List (GUEEntry ι N))).length := by
              simpa using hq ⟨0, by simp⟩
            rw [partner_cons_zero e y l₂' k p] at h0
            simp only [Fin.val_succ, List.length_cons, List.length_nil] at h0
            omega
      | cons x l' =>
        cases q with
        | cons e' T k p =>
          have h0 : (partner (e :: (x :: (l' ++ l₂)))
              (GUEPairing.cons e (x :: (l' ++ l₂)) k p) (0 : Fin (e :: (x :: (l' ++ l₂))).length)).val
              < (e :: x :: l').length := by
            simpa using hq ⟨0, by simp⟩
          rw [partner_cons_zero e x (l' ++ l₂) k p] at h0
          simp only [Fin.val_succ, List.length_cons] at h0
          have hklt : k.val < l'.length + 1 := by omega
          -- the partner index inside the first block
          let k' : Fin (x :: l').length := ⟨k.val, by simpa using hklt⟩
          let E : List (GUEEntry ι N) := (x :: l').eraseIdx k'
          have hElen : E.length = l'.length := by
            show ((x :: l').eraseIdx k').length = l'.length
            rw [List.length_eraseIdx, ite_eq_left k'.isLt]
            simp
          have hEA : (x :: (l' ++ l₂)).eraseIdx k = E ++ l₂ := by
            show (x :: (l' ++ l₂)).eraseIdx k'.val = ((x :: l').eraseIdx k'.val) ++ l₂
            exact eraseIdx_append_left (x :: l') l₂ k'
          have hlen : ((x :: (l' ++ l₂)).eraseIdx k).length = (E ++ l₂).length :=
            congrArg List.length hEA
          have hlenP : ((x :: (l' ++ l₂)).eraseIdx k).length = (l' ++ l₂).length := by
            have h1 := List.length_eraseIdx_add_one (l := x :: (l' ++ l₂)) (i := k.val) k.isLt
            simp only [List.length_cons] at h1
            omega
          let p' : GUEPairing (E ++ l₂) :=
            GUEPairing.castLength ((x :: (l' ++ l₂)).eraseIdx k) (E ++ l₂) hlen p
          have hplen : ((x :: (l' ++ l₂)).eraseIdx k).length = l'.length + l₂.length := by
            rw [hlenP, List.length_append]
          have hnc : NoCrossList E l₂ p' := by
            intro j
            have hjlt : j.val < l'.length := by
              have := j.isLt
              omega
            let j0 : Fin ((x :: (l' ++ l₂)).eraseIdx k).length :=
              ⟨j.val, by rw [hplen]; omega⟩
            -- the index of `p'` corresponding to `j0`
            have hidx1 : (⟨j.val, by
                  rw [List.length_append]
                  exact Nat.lt_add_right _ j.isLt⟩ : Fin (E ++ l₂).length) =
                Fin.cast hlen j0 := by
              apply Fin.ext
              simp only [Fin.val_cast]
              rfl
            rw [hidx1]
            have hpc : partner (E ++ l₂) p' (Fin.cast hlen j0) =
                Fin.cast hlen (partner ((x :: (l' ++ l₂)).eraseIdx k) p j0) :=
              GUEPairing.partner_castLength p (E ++ l₂) hlen j0
            rw [hpc, Fin.val_cast]
            -- read the partner of `q` at the insertion of `j0`
            have hj0val : (Fin.cast hlenP j0).val = j.val := by simp [j0]
            have hposlt : (k.succAbove (Fin.cast hlenP j0)).succ.val <
                (e :: x :: l').length := by
              rw [Fin.val_succ, val_succAbove]
              split_ifs with hy <;> simp only [List.length_cons] <;> omega
            have hfull := hq ⟨(k.succAbove (Fin.cast hlenP j0)).succ.val, hposlt⟩
            have hidx2 : (⟨(k.succAbove (Fin.cast hlenP j0)).succ.val, by
                  rw [List.length_append]
                  exact Nat.lt_add_right _ hposlt⟩ : Fin ((e :: x :: l') ++ l₂).length) =
                (k.succAbove (Fin.cast hlenP j0)).succ := Fin.ext rfl
            have hpc2 : partner (e :: x :: (l' ++ l₂))
                (GUEPairing.cons e (x :: (l' ++ l₂)) k p)
                ((k.succAbove (Fin.cast hlenP j0)).succ) =
                (k.succAbove (Fin.cast hlenP
                  (partner ((x :: (l' ++ l₂)).eraseIdx k) p j0))).succ :=
              partner_cons_succAbove k p hlenP j0
            rw [hidx2] at hfull
            have hfull' : (partner (e :: x :: (l' ++ l₂))
                (GUEPairing.cons e (x :: (l' ++ l₂)) k p)
                ((k.succAbove (Fin.cast hlenP j0)).succ)).val < (e :: x :: l').length := hfull
            have hfull2 : (k.succAbove (Fin.cast hlenP
                (partner ((x :: (l'++l₂)).eraseIdx k) p j0))).succ.val <
                (e :: x :: l').length := by
              simpa only [hpc2] using hfull'
            simp only [Fin.val_succ, List.length_cons] at hfull2
            have hylt : (Fin.cast hlenP (partner ((x :: (l' ++ l₂)).eraseIdx k) p j0)).val <
                l'.length := by
              refine val_lt_of_succAbove_val_lt k (Fin.cast hlenP (partner _ p j0))
                (by omega) (by omega)
            rw [Fin.val_cast] at hylt
            rw [hElen]
            exact hylt
          have hElt : E.length < n := by
            have : (e :: x :: l').length = n := hl
            simp only [List.length_cons] at this
            omega
          obtain ⟨p₁, p₂, hp'⟩ := ih E.length hElt E rfl l₂ p' hnc
          refine ⟨GUEPairing.cons e (x :: l') k' p₁, p₂, ?_⟩
          rw [GUEPairing.append_cons]
          -- keep the index `k` on both sides: it is definitionally the index produced by
          -- `append_cons`, so no dependent rewrite of the index is needed
          show GUEPairing.cons e ((x :: l') ++ l₂) k p =
            GUEPairing.cons e ((x :: l') ++ l₂) k
              ((eraseIdx_append_left (x :: l') l₂ k').symm ▸
                GUEPairing.append ((x :: l').eraseIdx k') l₂ p₁ p₂)
          have hp : p = GUEPairing.castLength (E ++ l₂) ((x :: (l' ++ l₂)).eraseIdx k)
              hlen.symm p' := by
            show p = GUEPairing.castLength (E ++ l₂) ((x :: (l' ++ l₂)).eraseIdx k) hlen.symm
              (GUEPairing.castLength ((x :: (l' ++ l₂)).eraseIdx k) (E ++ l₂) hlen p)
            exact (GUEPairing.castLength_castLength p (E ++ l₂) hlen).symm
          rw [hp, hp']
          rw [(eqRec_eq_castLength hEA.symm (GUEPairing.append E l₂ p₁ p₂)).symm]

/-- **A pairing with no crossing pair is block diagonal.** -/
theorem blockDiag_of_noCross {l₁ l₂ : List (GUEEntry ι N)} (q : GUEPairing (l₁ ++ l₂))
    (h : NoCrossList l₁ l₂ q) : BlockDiag l₁ l₂ q :=
  blockDiag_of_noCross_aux l₁.length l₁ rfl l₂ q h

/-- `NoCrossList` is exactly the negation of `SlotCross` for the conjugated partner permutation. -/
theorem noCross_iff_not_slotCross {k₁ k₂ : ℕ} {l₁ l₂ : List (GUEEntry ι N)}
    (h₁ : l₁.length = k₁) (h₂ : l₂.length = k₂)
    (h : (l₁ ++ l₂).length = k₁ + k₂) (q : GUEPairing (l₁ ++ l₂)) :
    NoCrossList l₁ l₂ q ↔ ¬ SlotCross k₁ k₂ (conjBy (finCongr h) (partnerPerm q)) := by
  constructor
  · intro hnc hcross
    obtain ⟨i, j, hij⟩ := hcross
    have hval := congrArg Fin.val hij
    rw [conjBy_apply] at hval
    simp only [finCongr_apply_coe, finCongr_symm_apply_coe, Fin.val_castAdd, Fin.val_natAdd]
      at hval
    have hidx : ((finCongr h).symm (Fin.castAdd k₂ i) : Fin (l₁ ++ l₂).length) =
        (⟨(Fin.cast h₁.symm i).val, by
          rw [List.length_append]
          exact Nat.lt_add_right _ (Fin.cast h₁.symm i).isLt⟩ : Fin (l₁ ++ l₂).length) :=
      Fin.ext rfl
    rw [hidx] at hval
    have hlt := hnc (Fin.cast h₁.symm i)
    have hlt' : ((partnerPerm q) ⟨(Fin.cast h₁.symm i).val, by
        rw [List.length_append]
        exact Nat.lt_add_right _ (Fin.cast h₁.symm i).isLt⟩ :
        Fin (l₁ ++ l₂).length).val < l₁.length := hlt
    rw [hval] at hlt'
    omega
  · intro hnc i
    by_contra hle
    push_neg at hle
    have hilt : i.val < l₁.length := i.isLt
    have hk1 : l₁.length = k₁ := h₁
    have hge : k₁ ≤ (partner (l₁ ++ l₂) q
        ⟨i.val, by rw [List.length_append]; exact Nat.lt_add_right _ i.isLt⟩).val := by
      rw [← h₁]
      exact hle
    have hlt : (partner (l₁ ++ l₂) q
        ⟨i.val, by rw [List.length_append]; exact Nat.lt_add_right _ i.isLt⟩).val < k₁ + k₂ := by
      rw [← h]
      exact (partner (l₁ ++ l₂) q _).isLt
    let j : Fin k₂ := ⟨(partner (l₁ ++ l₂) q
        ⟨i.val, by rw [List.length_append]; exact Nat.lt_add_right _ i.isLt⟩).val - k₁,
      by omega⟩
    refine hnc ⟨Fin.cast h₁ i, j, ?_⟩
    apply Fin.ext
    rw [conjBy_apply]
    simp only [finCongr_apply_coe, finCongr_symm_apply_coe, Fin.val_castAdd, Fin.val_natAdd]
    have hidx : ((finCongr h).symm (Fin.castAdd k₂ (Fin.cast h₁ i)) : Fin (l₁ ++ l₂).length) =
        (⟨i.val, by rw [List.length_append]; exact Nat.lt_add_right _ i.isLt⟩ :
          Fin (l₁ ++ l₂).length) := Fin.ext rfl
    rw [hidx]
    have hj : j.val = (partner (l₁ ++ l₂) q
        ⟨i.val, by rw [List.length_append]; exact Nat.lt_add_right _ i.isLt⟩).val - k₁ := rfl
    show (Fin.val ((partnerPerm q) (⟨i.val, by
      rw [List.length_append]
      exact Nat.lt_add_right _ i.isLt⟩ : Fin (l₁ ++ l₂).length))) = k₁ + j.val
    rw [partnerPerm_apply, hj]
    omega

/-! ### Parity of pairings -/

/-- A pairing can only exist on a list of even length (each pair removes two entries). -/
theorem even_length_of_guePairing {l : List (GUEEntry ι N)} (p : GUEPairing l) :
    Even l.length := by
  induction p with
  | nil => exact ⟨0, rfl⟩
  | cons e l k p ih =>
    obtain ⟨m, hm⟩ := ih
    have hk := k.isLt
    rw [List.length_eraseIdx_of_lt hk] at hm
    exact ⟨m + 1, by simp only [List.length_cons]; omega⟩

/-- There is no pairing of an odd-length list. -/
theorem isEmpty_guePairing_of_odd {l : List (GUEEntry ι N)} (h : Odd l.length) :
    IsEmpty (GUEPairing l) :=
  ⟨fun p => Nat.not_even_iff_odd.mpr h (even_length_of_guePairing p)⟩

/-- `Eq.rec` transport along an equality of the index is `cast` along the induced equality of
types. -/
theorem eqRec_eq_cast {α : Sort*} {F : α → Sort*} {a b : α} (h : a = b) (x : F a) :
    (h ▸ x) = cast (congrArg F h) x := by
  cases h
  rfl

/-- `2 * (n / 2) = n` holds exactly for even `n`, transported across an equality of lengths. -/
theorem even_split_iff {n m : ℕ} (h : n = m) : (n = 2 * (n / 2)) ↔ (m = 2 * (m / 2)) := by
  subst h
  rfl

/-- **A pairing with no crossing pair is block diagonal**, converse direction: a juxtaposed
pairing never crosses the block boundary. -/
theorem noCross_of_blockDiag {l₁ l₂ : List (GUEEntry ι N)} (q : GUEPairing (l₁ ++ l₂))
    (h : BlockDiag l₁ l₂ q) : NoCrossList l₁ l₂ q := by
  obtain ⟨p₁, p₂, rfl⟩ := h
  intro i
  rw [(GUEPairing.partner_append_aux l₁.length l₁ rfl l₂ p₁ p₂).1 i]
  exact (partner l₁ p₁ i).isLt

/-! ### The label sequences of the two slot blocks -/

/-- The label at a position of the first slot block is the label of the word. -/
theorem slotBlock₁_get_label' (w : List ι) (V : Fin (w.length + w.reverse.length) → Fin N)
    (i : Fin (slotBlock₁ w V).length) :
    ((slotBlock₁ w V).get i).1 = w.get (Fin.cast (length_slotBlock₁ w V) i) := by
  unfold slotBlock₁ at *
  rw [List.get_ofFn]
  simp only [slotEntry]
  rw [twoWalkLabel_castAdd]

/-- The label at a position of the second slot block is the label of the reversed word. -/
theorem slotBlock₂_get_label' (w : List ι) (V : Fin (w.length + w.reverse.length) → Fin N)
    (i : Fin (slotBlock₂ w V).length) :
    ((slotBlock₂ w V).get i).1 = w.reverse.get (Fin.cast (length_slotBlock₂ w V) i) := by
  unfold slotBlock₂ at *
  rw [List.get_ofFn]
  simp only [slotEntry]
  rw [twoWalkLabel_natAdd]

/-- **The pairing sum over the first slot block is the one-walk genus sum of `w`.** -/
theorem sum_slotBlock₁_eq_genusSum (w : List ι) (N : ℕ) (hN : 1 ≤ N)
    (V : Fin (w.length + w.reverse.length) → Fin N) :
    (∑ p : GUEPairing (slotBlock₁ w V),
        gueLabelWeight (slotBlock₁ w V) p * (N : ℂ) ^ pairOrbitCount p) = genusSum w N := by
  classical
  by_cases heven : w.length = 2 * (w.length / 2)
  · rw [genusSum, dite_eq_left heven]
    have hlen : (gueCanonicalEntries w (w.length / 2) heven hN).length
        = (slotBlock₁ w V).length := by
      rw [length_gueCanonicalEntries, length_slotBlock₁]
      exact heven.symm
    rw [sum_pairOrbitCount_eq_of_label_eq (l₁ := gueCanonicalEntries w (w.length / 2) heven hN)
      (l₂ := slotBlock₁ w V) hlen]
    · exact GUEPairing.sum_gueCanonicalEntries_crossdim w (w.length / 2) heven hN (N : ℂ)
    · intro i
      rw [gueCanonicalEntries_get_label, slotBlock₁_get_label']
      exact congrArg (fun j => w.get j) (Fin.ext rfl)
  · rw [genusSum, dite_eq_right heven]
    have hodd : Odd (slotBlock₁ w V).length := by
      rw [length_slotBlock₁]
      exact Nat.not_even_iff_odd.mp (fun hev => heven
        (Nat.two_mul_div_two_of_even hev).symm)
    haveI : IsEmpty (GUEPairing (slotBlock₁ w V)) := isEmpty_guePairing_of_odd hodd
    exact Finset.sum_eq_zero (fun p _ => (isEmpty_guePairing_of_odd hodd).false p |>.elim)

/-- **The pairing sum over the second slot block is the one-walk genus sum of `w.reverse`.** -/
theorem sum_slotBlock₂_eq_genusSum (w : List ι) (N : ℕ) (hN : 1 ≤ N)
    (V : Fin (w.length + w.reverse.length) → Fin N) :
    (∑ p : GUEPairing (slotBlock₂ w V),
        gueLabelWeight (slotBlock₂ w V) p * (N : ℂ) ^ pairOrbitCount p) = genusSum w.reverse N := by
  classical
  have hrev : w.reverse.length = w.length := by simp
  have hsplit := even_split_iff hrev
  by_cases heven : w.reverse.length = 2 * (w.reverse.length / 2)
  · rw [genusSum, dite_eq_left heven]
    have hlen : (gueCanonicalEntries w.reverse (w.reverse.length / 2) heven hN).length
        = (slotBlock₂ w V).length := by
      rw [length_gueCanonicalEntries, length_slotBlock₂]
      exact heven.symm
    rw [sum_pairOrbitCount_eq_of_label_eq
      (l₁ := gueCanonicalEntries w.reverse (w.reverse.length / 2) heven hN)
      (l₂ := slotBlock₂ w V) hlen]
    · exact GUEPairing.sum_gueCanonicalEntries_crossdim w.reverse
        (w.reverse.length / 2) heven hN (N : ℂ)
    · intro i
      rw [gueCanonicalEntries_get_label, slotBlock₂_get_label']
      exact congrArg (fun j => w.reverse.get j) (Fin.ext rfl)
  · rw [genusSum, dite_eq_right heven]
    have hodd : Odd (slotBlock₂ w V).length := by
      rw [length_slotBlock₂]
      exact Nat.not_even_iff_odd.mp (fun hev => heven
        (Nat.two_mul_div_two_of_even hev).symm)
    exact Finset.sum_eq_zero (fun p _ => (isEmpty_guePairing_of_odd hodd).false p |>.elim)

/-! ### The slot permutation and slot weight of a two-block pairing -/

/-- The slot permutation of a pairing of the two-block slot list. -/
def blockSlotPerm {w : List ι} {V : Fin (w.length + w.reverse.length) → Fin N}
    (q : GUEPairing (slotBlock₁ w V ++ slotBlock₂ w V)) :
    Equiv.Perm (Fin (w.length + w.reverse.length)) :=
  conjBy (finCongr (by rw [List.length_append, length_slotBlock₁, length_slotBlock₂] :
      (slotBlock₁ w V ++ slotBlock₂ w V).length = w.length + w.reverse.length)) (partnerPerm q)

/-- The slot weight of a pairing of the two-block slot list. -/
def blockSlotWeight (N : ℕ) {w : List ι} {V : Fin (w.length + w.reverse.length) → Fin N}
    (q : GUEPairing (slotBlock₁ w V ++ slotBlock₂ w V)) : ℂ :=
  gueLabelWeight (slotBlock₁ w V ++ slotBlock₂ w V) q *
    (N : ℂ) ^ (twoWalkLoopCount w.length w.reverse.length (blockSlotPerm q))

/-- The loop count of a juxtaposed two-block slot pairing is the sum of the block face counts. -/
theorem twoWalkLoopCount_blockSlotPerm_append (w : List ι)
    (V : Fin (w.length + w.reverse.length) → Fin N)
    (p₁ : GUEPairing (slotBlock₁ w V)) (p₂ : GUEPairing (slotBlock₂ w V)) :
    twoWalkLoopCount w.length w.reverse.length
        (blockSlotPerm (GUEPairing.append (slotBlock₁ w V) (slotBlock₂ w V) p₁ p₂)) =
      pairOrbitCount p₁ + pairOrbitCount p₂ := by
  unfold blockSlotPerm
  rw [← slotPerm_append_eq V (GUEPairing.append (slotBlock₁ w V) (slotBlock₂ w V) p₁ p₂)]
  exact twoWalkLoopCount_slotPerm_append V p₁ p₂

/-- The two-block slot weight factors over the two blocks. -/
theorem sum_pair_blockSlotWeight (w : List ι) (N : ℕ)
    (V : Fin (w.length + w.reverse.length) → Fin N) :
    (∑ p : GUEPairing (slotBlock₁ w V) × GUEPairing (slotBlock₂ w V),
        blockSlotWeight N (GUEPairing.append (slotBlock₁ w V) (slotBlock₂ w V) p.1 p.2)) =
      (∑ p₁ : GUEPairing (slotBlock₁ w V),
          gueLabelWeight (slotBlock₁ w V) p₁ * (N : ℂ) ^ pairOrbitCount p₁) *
        (∑ p₂ : GUEPairing (slotBlock₂ w V),
          gueLabelWeight (slotBlock₂ w V) p₂ * (N : ℂ) ^ pairOrbitCount p₂) := by
  classical
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun p₁ _ => Finset.sum_congr rfl fun p₂ _ => ?_
  rw [blockSlotWeight, twoWalkLoopCount_blockSlotPerm_append, gueLabelWeight_append, pow_add]
  ring

/-- **The non-crossing two-block slot sum is the square of the one-walk genus sum.** -/
theorem hblock_block (w : List ι) (N : ℕ) (hN : 1 ≤ N)
    (V : Fin (w.length + w.reverse.length) → Fin N) :
    (∑ q : GUEPairing (slotBlock₁ w V ++ slotBlock₂ w V),
        (if ¬ SlotCross w.length w.reverse.length (blockSlotPerm q) then
          blockSlotWeight N q else 0)) = (genusSum w N) ^ 2 := by
  classical
  have hcross : ∀ q : GUEPairing (slotBlock₁ w V ++ slotBlock₂ w V),
      (¬ SlotCross w.length w.reverse.length (blockSlotPerm q)) ↔
        BlockDiag (slotBlock₁ w V) (slotBlock₂ w V) q := by
    intro q
    unfold blockSlotPerm
    rw [← noCross_iff_not_slotCross (length_slotBlock₁ w V) (length_slotBlock₂ w V)
      (by rw [List.length_append, length_slotBlock₁, length_slotBlock₂])]
    exact ⟨fun h => blockDiag_of_noCross q h, fun h => noCross_of_blockDiag q h⟩
  rw [← Finset.sum_filter]
  have hpred : (Finset.univ.filter fun q : GUEPairing (slotBlock₁ w V ++ slotBlock₂ w V) =>
        ¬ SlotCross w.length w.reverse.length (blockSlotPerm q))
      = Finset.univ.filter fun q : GUEPairing (slotBlock₁ w V ++ slotBlock₂ w V) =>
          BlockDiag (slotBlock₁ w V) (slotBlock₂ w V) q := by
    apply Finset.filter_congr
    intro q _
    exact hcross q
  rw [hpred]
  rw [Finset.sum_subtype
    (p := fun q : GUEPairing (slotBlock₁ w V ++ slotBlock₂ w V) =>
      BlockDiag (slotBlock₁ w V) (slotBlock₂ w V) q)
    (s := Finset.univ.filter fun q : GUEPairing (slotBlock₁ w V ++ slotBlock₂ w V) =>
      BlockDiag (slotBlock₁ w V) (slotBlock₂ w V) q) (h := by intro x; simp)
    (f := fun q => blockSlotWeight N q)]
  rw [GUEPairing.sum_blockDiag (fun q => blockSlotWeight N q)]
  rw [sum_pair_blockSlotWeight, sum_slotBlock₁_eq_genusSum w N hN V,
    sum_slotBlock₂_eq_genusSum w N hN V]
  rw [genusSum_reverse' w N hN, pow_two]

/-! ### From the two-block list back to the canonical slot list -/

/-- **Reindexing the slot sum along the block decomposition of the canonical slot list.** -/
theorem sum_slotList_eq_sum_blockSlot (w : List ι) (N : ℕ)
    (V : Fin (w.length + w.reverse.length) → Fin N) :
    (∑ q : GUEPairing (slotList w V),
        (if ¬ SlotCross w.length w.reverse.length (slotPerm q) then slotWeight N q else 0)) =
      ∑ q : GUEPairing (slotBlock₁ w V ++ slotBlock₂ w V),
        (if ¬ SlotCross w.length w.reverse.length (blockSlotPerm q) then
          blockSlotWeight N q else 0) := by
  classical
  have h := slotList_eq_append w V
  refine (Fintype.sum_equiv (Equiv.cast (congrArg GUEPairing h)).symm
    (fun q : GUEPairing (slotBlock₁ w V ++ slotBlock₂ w V) =>
      (if ¬ SlotCross w.length w.reverse.length (blockSlotPerm q) then
        blockSlotWeight N q else 0))
    (fun q : GUEPairing (slotList w V) =>
      (if ¬ SlotCross w.length w.reverse.length (slotPerm q) then slotWeight N q else 0))
    ?_).symm
  intro q
  have hq : (Equiv.cast (congrArg GUEPairing h)).symm q = h.symm ▸ q := by
    rw [← Equiv.cast_symm, Equiv.cast_apply]
    exact (eqRec_eq_cast h.symm q).symm
  rw [hq]
  have hperm : slotPerm (h.symm ▸ q) = blockSlotPerm q := slotPerm_append_eq V q
  have hweight : slotWeight N (h.symm ▸ q) = blockSlotWeight N q := by
    simp only [slotWeight, blockSlotWeight]
    rw [hperm, gueLabelWeight_eqRec h.symm q]
  rw [hperm, hweight]

/-! ### The unconditional block-diagonal factorization `hblock` -/

/-- **Block-diagonal factorization of the two-walk slot sum**: the non-crossing part of the slot
pairing sum is the square of the one-walk genus sum. -/
theorem hblock (w : List ι) (hk : 1 ≤ w.length) (N : ℕ) (hN : 1 ≤ N)
    (V₀ : Fin (w.length + w.reverse.length) → Fin N) :
    (∑ q ∈ (Finset.univ.filter fun q : GUEPairing (slotList w V₀) =>
        ¬ SlotCross w.length w.reverse.length (slotPerm q)), slotWeight N q) =
      (genusSum w N) ^ 2 := by
  classical
  rw [Finset.sum_filter]
  rw [sum_slotList_eq_sum_blockSlot w N V₀]
  exact hblock_block w N hN V₀

end GUEPairing

/-- **The block-diagonal factorization at the top level** (restatement of `GUEPairing.hblock`). -/
theorem hblock (w : List ι) (hk : 1 ≤ w.length) (N : ℕ) (hN : 1 ≤ N)
    (V₀ : Fin (w.length + w.reverse.length) → Fin N) :
    (∑ q ∈ (Finset.univ.filter fun q : GUEPairing (slotList w V₀) =>
        ¬ SlotCross w.length w.reverse.length (slotPerm q)), slotWeight N q) =
      (genusSum w N) ^ 2 :=
  GUEPairing.hblock w hk N hN V₀

/-- **Unconditional simultaneous almost-sure convergence for all trace words**, with the one-walk
genus sum as the mean-square input: the block-diagonal factorization `hblock` is no longer a
hypothesis but the theorem `hblock` above. -/
theorem ae_all_words_gueNormTrace_genusSum_unconditional :
    ∀ᵐ x ∂(commonGaussianMeasure ι), ∀ w : List ι,
      Tendsto (fun N : ℕ => gueNormTrace w (x N)) atTop (𝓝 (wordLimit w)) :=
  ae_all_words_gueNormTrace_genusSum (fun w hk N hN V₀ => hblock w hk N hN V₀)

end

end GUEStrongConvergence



