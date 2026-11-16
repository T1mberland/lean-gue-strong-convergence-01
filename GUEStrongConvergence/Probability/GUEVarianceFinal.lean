/-
# Final assembly of the GUE trace-word variance bound

This file closes the variance chain by combining the two-walk slot expansion
(`GUETwoWalkSlot`) with the conditional variance bound and almost-sure step
(`GUEVarianceAssembly`).

Main results of this file:

* `gueTwoTraceDelta_eq_slot_sum`: the two-trace delta moment in the canonical slot form
  `∑_q labelW(q) * N ^ L(q)`, where `q` runs over the pairings of a fixed canonical slot list
  and `L(q)` is the two-walk loop count of the transported pairing;
* `gueTwoTraceWick_eq_slot_sum`: the same in the normalized Wick form `N^{-k} ∑_q ...`;
* `norm_gueLabelWeight_le_one`, `slotPerm_mul_self`, `slotPerm_ne_self`,
  `twoWalkLoopCount_slot_le_of_cross` and `norm_slotCross_sum_le`: the crossing part of the pairing
  sum is bounded by the number of pairings times `N ^ k` — these are unconditional;
* `variance_bound_gueNormTrace`: the `O(N^{-2})` variance bound
  `∫ ‖tr_N W − E tr_N W‖² ≤ #(Equiv.Perm (Fin 2k)) / N²`, conditional only on the mean formula
  `hmean` and on the **block-diagonal factorization** `hblock`;
* `ae_tendsto_gueNormTrace_of_slot` and `ae_tendsto_gueNormTrace_of_slot_genus`: the almost-sure
  step, the latter with the explicit limit `∑_{non-crossing} labelW`.

## The remaining input `hblock`

`hblock` states that the pairings of the two-walk slot list that are *not* crossing contribute
exactly `(S N) ^ 2`, where `S` is the single-walk (label-weighted) genus sum.  It is the only
missing combinatorial brick of the variance chain.  Note that `twoWalkLoopCount_sumCongr` is
necessary but *not* sufficient: it is a statement about permutations, while `hblock` needs a
pairing-level split

`{q : GUEPairing (l₁ ++ l₂) // q block-diagonal} ≃ GUEPairing l₁ × GUEPairing l₂`

with label-weight multiplicativity (`gueLabelWeight_eq_prod_partner`) and the identification of the
transported partner permutation with `finSumFinEquiv.permCongr (σ₁.sumCongr σ₂)`, plus the reversal
invariance `S(w.reverse) = S(w)` for the second block.

No `sorry`/axiom is used.
-/
import GUEStrongConvergence.Probability.GUETwoWalkSlot
import GUEStrongConvergence.Probability.GUEVarianceExpansion
import GUEStrongConvergence.Probability.GUEVarianceAssembly
import GUEStrongConvergence.Probability.GUEPartnerInjective
import GUEStrongConvergence.Probability.GUEWordGenusLimit

open MeasureTheory ProbabilityTheory Filter
open scoped RealInnerProductSpace Matrix ENNReal Topology

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false
set_option linter.unusedVariables false

namespace GUEStrongConvergence

attribute [local instance] Classical.propDecidable

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {N : ℕ}

/-! ### All-pairing slot expansion of the two-trace delta moment -/

/-- **All-pairing slot expansion**: the two-trace delta moment is the label-weighted sum over the
pairings `q` of the canonical slot list, each weighted by `N` to the two-walk loop count of the
transported pairing. -/
theorem gueTwoTraceDelta_eq_slot_sum (w : List ι) (hk : 1 ≤ w.length)
    (V₀ : Fin (w.length + w.reverse.length) → Fin N) :
    gueTwoTraceDelta N w w.reverse =
      ∑ q : GUEPairing (twoWalkSlotList w.length w.reverse.length
          (twoWalkLabel w w.reverse) V₀),
        gueLabelWeight (twoWalkSlotList w.length w.reverse.length
            (twoWalkLabel w w.reverse) V₀) q *
          (N : ℂ) ^ (twoWalkLoopCount w.length w.reverse.length
            (conjBy (finCongr (by simp : (twoWalkSlotList w.length w.reverse.length
              (twoWalkLabel w w.reverse) V₀).length = w.length + w.reverse.length))
              (partnerPerm q))) := by
  classical
  have h₂ : 1 ≤ w.reverse.length := by simpa using hk
  -- the two-walk vertex sum
  rw [gueTwoTraceDelta_eq_sum_vertex w w.reverse hk h₂]
  -- the entries of the two closed walks are the canonical slot entries
  have hcongr : ∀ (u₁ : Fin w.length → Fin N) (u₂ : Fin w.reverse.length → Fin N),
      (∑ p : GUEPairing (guePairEntries w w.reverse (u₁ (cyclicLastIdx hk))
          (u₂ (cyclicLastIdx h₂)) u₁ u₂), gueDeltaWeight _ p) =
        ∑ p : GUEPairing (twoWalkSlotList w.length w.reverse.length
            (twoWalkLabel w w.reverse)
            (Fin.append (slotVertex hk u₁) (slotVertex h₂ u₂))), gueDeltaWeight _ p := by
    intro u₁ u₂
    rw [guePairEntries_cyclicVertex_slot w w.reverse hk h₂ u₁ u₂]
  simp_rw [hcongr]
  -- reindex `(u₁, u₂)` as one slot vertex function
  rw [sum_twoWalk_slotVertex w.length w.reverse.length hk h₂
    (fun V => ∑ p : GUEPairing (twoWalkSlotList w.length w.reverse.length
      (twoWalkLabel w w.reverse) V), gueDeltaWeight _ p)]
  -- transport every pairing to the canonical list
  have hstep : ∀ V : Fin (w.length + w.reverse.length) → Fin N,
      (∑ p : GUEPairing (twoWalkSlotList w.length w.reverse.length
          (twoWalkLabel w w.reverse) V), gueDeltaWeight _ p) =
        ∑ q : GUEPairing (twoWalkSlotList w.length w.reverse.length
            (twoWalkLabel w w.reverse) V₀),
          gueDeltaWeight (twoWalkSlotList w.length w.reverse.length
            (twoWalkLabel w w.reverse) V)
            (GUEPairing.castLength (twoWalkSlotList w.length w.reverse.length
              (twoWalkLabel w w.reverse) V₀)
              (twoWalkSlotList w.length w.reverse.length (twoWalkLabel w w.reverse) V)
              (by simp) q) := by
    intro V
    exact (GUEPairing.sum_castLength (M := ℂ)
      (by simp : (twoWalkSlotList w.length w.reverse.length
        (twoWalkLabel w w.reverse) V₀).length =
          (twoWalkSlotList w.length w.reverse.length (twoWalkLabel w w.reverse) V).length)
      (fun p => gueDeltaWeight (twoWalkSlotList w.length w.reverse.length
        (twoWalkLabel w w.reverse) V) p)).symm
  simp_rw [hstep]
  -- swap the vertex sum and the pairing sum
  rw [Finset.sum_comm]
  -- evaluate the vertex sum for each fixed pairing
  refine Finset.sum_congr rfl fun q _ => ?_
  -- the label weight is independent of the vertex function
  have hlab : ∀ V : Fin (w.length + w.reverse.length) → Fin N,
      gueLabelWeight (twoWalkSlotList w.length w.reverse.length
          (twoWalkLabel w w.reverse) V₀) q =
        gueLabelWeight (twoWalkSlotList w.length w.reverse.length
          (twoWalkLabel w w.reverse) V)
          (GUEPairing.castLength (twoWalkSlotList w.length w.reverse.length
            (twoWalkLabel w w.reverse) V₀)
            (twoWalkSlotList w.length w.reverse.length (twoWalkLabel w w.reverse) V)
            (by simp) q) := by
    intro V
    refine GUEPairing.gueLabelWeight_castLength q _ (by simp) ?_
    intro i
    rw [get_twoWalkSlotList_apply, get_twoWalkSlotList_apply]
    simp only [slotEntry]
    congr 1
  have hconst : ∀ V : Fin (w.length + w.reverse.length) → Fin N,
      gueDeltaWeight (twoWalkSlotList w.length w.reverse.length
          (twoWalkLabel w w.reverse) V)
          (GUEPairing.castLength (twoWalkSlotList w.length w.reverse.length
            (twoWalkLabel w w.reverse) V₀)
            (twoWalkSlotList w.length w.reverse.length (twoWalkLabel w w.reverse) V)
            (by simp) q) =
        gueLabelWeight (twoWalkSlotList w.length w.reverse.length
            (twoWalkLabel w w.reverse) V₀) q *
          gueIndexWeight (twoWalkSlotList w.length w.reverse.length
            (twoWalkLabel w w.reverse) V)
            (GUEPairing.castLength (twoWalkSlotList w.length w.reverse.length
              (twoWalkLabel w w.reverse) V₀)
              (twoWalkSlotList w.length w.reverse.length (twoWalkLabel w w.reverse) V)
              (by simp) q) := by
    intro V
    rw [gueDeltaWeight_eq_label_mul_index, ← hlab V]
  calc (∑ V : Fin (w.length + w.reverse.length) → Fin N,
      gueDeltaWeight (twoWalkSlotList w.length w.reverse.length
        (twoWalkLabel w w.reverse) V)
        (GUEPairing.castLength (twoWalkSlotList w.length w.reverse.length
          (twoWalkLabel w w.reverse) V₀)
          (twoWalkSlotList w.length w.reverse.length (twoWalkLabel w w.reverse) V)
          (by simp) q))
      = ∑ V : Fin (w.length + w.reverse.length) → Fin N,
          gueLabelWeight (twoWalkSlotList w.length w.reverse.length
              (twoWalkLabel w w.reverse) V₀) q *
            gueIndexWeight (twoWalkSlotList w.length w.reverse.length
              (twoWalkLabel w w.reverse) V)
              (GUEPairing.castLength (twoWalkSlotList w.length w.reverse.length
                (twoWalkLabel w w.reverse) V₀)
                (twoWalkSlotList w.length w.reverse.length (twoWalkLabel w w.reverse) V)
                (by simp) q) := Finset.sum_congr rfl fun V _ => hconst V
    _ = gueLabelWeight (twoWalkSlotList w.length w.reverse.length
            (twoWalkLabel w w.reverse) V₀) q *
          ∑ V : Fin (w.length + w.reverse.length) → Fin N,
            gueIndexWeight (twoWalkSlotList w.length w.reverse.length
              (twoWalkLabel w w.reverse) V)
              (GUEPairing.castLength (twoWalkSlotList w.length w.reverse.length
                (twoWalkLabel w w.reverse) V₀)
                (twoWalkSlotList w.length w.reverse.length (twoWalkLabel w w.reverse) V)
                (by simp) q) := (Finset.mul_sum _ _ _).symm
    _ = gueLabelWeight (twoWalkSlotList w.length w.reverse.length
            (twoWalkLabel w w.reverse) V₀) q *
          (N : ℂ) ^ (twoWalkLoopCount w.length w.reverse.length
            (conjBy (finCongr (by simp : (twoWalkSlotList w.length w.reverse.length
              (twoWalkLabel w w.reverse) V₀).length = w.length + w.reverse.length))
              (partnerPerm q))) := by
        rw [sum_slotIndexWeight]

/-! ### The canonical slot list, its pairings and the slot weight -/

/-- The canonical slot list of `w` and `w.reverse`. -/
abbrev slotList (w : List ι) (V : Fin (w.length + w.reverse.length) → Fin N) :
    List (GUEEntry ι N) :=
  twoWalkSlotList w.length w.reverse.length (twoWalkLabel w w.reverse) V

/-- The pairing permutation of a pairing of the canonical slot list, transported to the canonical
list. -/
def slotPerm {w : List ι} {V : Fin (w.length + w.reverse.length) → Fin N}
    (q : GUEPairing (slotList w V)) : Equiv.Perm (Fin (w.length + w.reverse.length)) :=
  conjBy (finCongr (by simp : (slotList w V).length = w.length + w.reverse.length))
    (partnerPerm q)

/-- The slot weight of a pairing: its label weight times `N` to its loop count. -/
def slotWeight (N : ℕ) {w : List ι} {V : Fin (w.length + w.reverse.length) → Fin N}
    (q : GUEPairing (slotList w V)) : ℂ :=
  gueLabelWeight (slotList w V) q *
    (N : ℂ) ^ (twoWalkLoopCount w.length w.reverse.length (slotPerm q))

/-- **Wick expansion in slot form**: the two-trace Wick sum is `N^{-k}` times the label-weighted
pairing sum over the canonical slot list. -/
theorem gueTwoTraceWick_eq_slot_sum (w : List ι) (hk : 1 ≤ w.length)
    (V₀ : Fin (w.length + w.reverse.length) → Fin N) :
    gueTwoTraceWick N w w.reverse =
      ((N : ℂ)⁻¹) ^ w.length * ∑ q : GUEPairing (slotList w V₀), slotWeight N q := by
  rw [gueTwoTraceWick_eq_delta_sum, gueTwoTraceDelta_eq_slot_sum w hk V₀]
  have hhalf : (w.length + w.reverse.length) / 2 = w.length := by
    have h : w.reverse.length = w.length := by simp
    omega
  rw [hhalf]
  rfl

/-- The transported pairing permutation is an involution. -/
theorem slotPerm_mul_self {w : List ι} {V : Fin (w.length + w.reverse.length) → Fin N}
    (q : GUEPairing (slotList w V)) : slotPerm q * slotPerm q = 1 := by
  rw [slotPerm, ← conjBy_mul]
  have h : partnerPerm q * partnerPerm q = 1 := by
    refine Equiv.ext fun i => ?_
    rw [Equiv.Perm.mul_apply, Equiv.Perm.one_apply]
    exact partnerPerm_involutive q i
  rw [h, conjBy_one]

/-- The transported pairing permutation is fixed-point-free. -/
theorem slotPerm_ne_self {w : List ι} {V : Fin (w.length + w.reverse.length) → Fin N}
    (q : GUEPairing (slotList w V)) (i : Fin (w.length + w.reverse.length)) :
    slotPerm q i ≠ i :=
  conjBy_ne_self _ (partnerPerm_ne_self q) i

/-! ### The label weight is bounded by one -/

/-- The label weight of a pairing is a product of `0`/`1` indicators, hence has norm at most one. -/
theorem norm_gueLabelWeight_le_one (l : List (GUEEntry ι N)) (p : GUEPairing l) :
    ‖gueLabelWeight l p‖ ≤ 1 := by
  induction p with
  | nil => simp
  | cons e l k p ih =>
    rw [gueLabelWeight_cons, norm_mul]
    have h1 : ‖gueLabelCov e (l.get k)‖ ≤ 1 := by
      unfold gueLabelCov
      split_ifs <;> simp
    calc ‖gueLabelCov e (l.get k)‖ * ‖gueLabelWeight (l.eraseIdx k) p‖ ≤ 1 * 1 := by
          refine mul_le_mul h1 ih (norm_nonneg _) ?_
          norm_num
      _ = 1 := by norm_num

/-! ### The cross pairings -/

/-- A pairing permutation is *crossing* if some pair joins the first block to the second. -/
def SlotCross (k₁ k₂ : ℕ) (σ : Equiv.Perm (Fin (k₁ + k₂))) : Prop :=
  ∃ (i : Fin k₁) (j : Fin k₂), σ (Fin.castAdd k₂ i) = Fin.natAdd k₁ j

/-- **Cross-pairing loop bound for the slot pairings**: a crossing slot pairing has at most
`w.length` loops. -/
theorem twoWalkLoopCount_slot_le_of_cross (w : List ι) (hk : 1 ≤ w.length)
    {V : Fin (w.length + w.reverse.length) → Fin N} (q : GUEPairing (slotList w V))
    (hcross : SlotCross w.length w.reverse.length (slotPerm q)) :
    twoWalkLoopCount w.length w.reverse.length (slotPerm q) ≤ w.length := by
  have h₂ : 1 ≤ w.reverse.length := by simpa using hk
  have h := twoWalkLoopCount_cross_le w.length w.reverse.length hk h₂ (slotPerm q)
    (slotPerm_mul_self q) (slotPerm_ne_self q) hcross
  have hhalf : (w.length + w.reverse.length) / 2 = w.length := by
    have hr : w.reverse.length = w.length := by simp
    omega
  omega

/-- The number of pairings of the canonical slot list is bounded by the number of permutations of
the same index type (the partner permutation is injective). -/
theorem card_guePairing_le_perm (l : List (GUEEntry ι N)) :
    Fintype.card (GUEPairing l) ≤ Fintype.card (Equiv.Perm (Fin l.length)) :=
  Fintype.card_le_of_injective (fun q => partnerPerm q) partnerPerm_injective

/-! ### The cross contribution is bounded by the number of permutations -/

/-- **Cross-contribution bound in slot form**: the crossing part of the slot pairing sum is bounded
by the number of pairings (at most the number of permutations) times `N ^ w.length`. -/
theorem norm_slotCross_sum_le (w : List ι) (hk : 1 ≤ w.length)
    (N : ℕ) (hN : 1 ≤ N) (V₀ : Fin (w.length + w.reverse.length) → Fin N) :
    ‖∑ q ∈ (Finset.univ.filter fun q : GUEPairing (slotList w V₀) =>
        SlotCross w.length w.reverse.length (slotPerm q)), slotWeight N q‖ ≤
      (Fintype.card (Equiv.Perm (Fin (w.length + w.reverse.length))) : ℝ) *
        (N : ℝ) ^ w.length := by
  classical
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  set s : Finset (GUEPairing (slotList w V₀)) :=
    Finset.univ.filter (fun q => SlotCross w.length w.reverse.length (slotPerm q)) with hs
  have hterm : ∀ q ∈ s, ‖slotWeight N q‖ ≤ (N : ℝ) ^ w.length := by
    intro q hq
    rw [hs, Finset.mem_filter] at hq
    obtain ⟨-, hcross⟩ := hq
    have hL := twoWalkLoopCount_slot_le_of_cross w hk q hcross
    rw [slotWeight, norm_mul, norm_pow, Complex.norm_natCast]
    have h1 := norm_gueLabelWeight_le_one (slotList w V₀) q
    have h2 : (N : ℝ) ^ (twoWalkLoopCount w.length w.reverse.length (slotPerm q)) ≤
        (N : ℝ) ^ w.length := pow_le_pow_right₀ hN1 hL
    calc ‖gueLabelWeight (slotList w V₀) q‖ *
          (N : ℝ) ^ (twoWalkLoopCount w.length w.reverse.length (slotPerm q))
        ≤ 1 * (N : ℝ) ^ w.length := mul_le_mul h1 h2 (by positivity) (by norm_num)
      _ = (N : ℝ) ^ w.length := one_mul _
  have hcard : s.card ≤ Fintype.card (Equiv.Perm (Fin (w.length + w.reverse.length))) := by
    refine (Finset.card_filter_le _ _).trans ?_
    rw [Finset.card_univ]
    have := card_guePairing_le_perm (slotList w V₀)
    simpa using this
  calc ‖∑ q ∈ s, slotWeight N q‖
      ≤ ∑ q ∈ s, ‖slotWeight N q‖ := norm_sum_le _ _
    _ ≤ ∑ _q ∈ s, (N : ℝ) ^ w.length := Finset.sum_le_sum hterm
    _ = (s.card : ℝ) * (N : ℝ) ^ w.length := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (Fintype.card (Equiv.Perm (Fin (w.length + w.reverse.length))) : ℝ) *
          (N : ℝ) ^ w.length := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        exact_mod_cast hcard

/-! ### The unconditional variance bound -/

/-- **Unconditional `O(N^{-2})` variance bound** from the slot expansion and the block-diagonal
factorization `D N = (S N)^2` of the pairing sum. -/
theorem variance_bound_gueNormTrace (w : List ι) (hk : 1 ≤ w.length) (S : ℕ → ℂ)
    (hblock : ∀ (N : ℕ) (_ : 1 ≤ N) (V₀ : Fin (w.length + w.reverse.length) → Fin N),
      (∑ q ∈ (Finset.univ.filter fun q : GUEPairing (slotList w V₀) =>
          ¬ SlotCross w.length w.reverse.length (slotPerm q)), slotWeight N q) = (S N) ^ 2)
    (hmean : ∀ N : ℕ, Complex.normSq (∫ y, gueNormTrace w y
        ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))) =
      ((((N : ℂ)⁻¹) ^ (w.length + 2) * (S N) ^ 2)).re) :
    ∀ N : ℕ, 1 ≤ N →
      ∫ x : EuclideanSpace ℝ (GUECoord ι N),
          ‖gueNormTrace w x - ∫ y, gueNormTrace w y
            ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))‖ ^ 2
        ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) ≤
          (Fintype.card (Equiv.Perm (Fin (w.length + w.reverse.length))) : ℝ) /
            (N : ℝ) ^ 2 := by
  classical
  -- the crossing contribution, extended by `0` at `N = 0`
  let A : ℕ → ℂ := fun M =>
    if hM : M = 0 then 0
    else ∑ q ∈ (Finset.univ.filter fun q : GUEPairing
          (slotList w (fun _ => (⟨0, Nat.pos_of_ne_zero hM⟩ : Fin M))) =>
        SlotCross w.length w.reverse.length (slotPerm q)), slotWeight M q
  have hWick : ∀ M : ℕ, gueTwoTraceWick M w w.reverse =
      ((M : ℂ)⁻¹) ^ w.length * ((S M) ^ 2 + A M) := by
    intro M
    by_cases hM : M = 0
    · subst hM
      have hw : w.length ≠ 0 := by omega
      have hzero : gueTwoTraceWick 0 w w.reverse = 0 := by simp [gueTwoTraceWick]
      rw [hzero]
      simp only [A, dite_eq_left rfl]
      rw [show ((0 : ℕ) : ℂ)⁻¹ = 0 by simp, zero_pow hw]
      simp
    · have hMpos : 1 ≤ M := Nat.pos_of_ne_zero hM
      rw [gueTwoTraceWick_eq_slot_sum w hk
        (fun _ => (⟨0, Nat.pos_of_ne_zero hM⟩ : Fin M))]
      simp only [A, dite_eq_right hM]
      rw [← Finset.sum_filter_add_sum_filter_not (s := Finset.univ)
        (p := fun q : GUEPairing (slotList w (fun _ => (⟨0, Nat.pos_of_ne_zero hM⟩ : Fin M))) =>
          SlotCross w.length w.reverse.length (slotPerm q)) (f := fun q => slotWeight M q)]
      rw [hblock M hMpos]
      ring
  have hA : ∀ M : ℕ, 1 ≤ M →
      ‖A M‖ ≤ (Fintype.card (Equiv.Perm (Fin (w.length + w.reverse.length))) : ℝ) *
        (M : ℝ) ^ w.length := by
    intro M hM
    have hMne : M ≠ 0 := by omega
    simp only [A, dite_eq_right hMne]
    exact norm_slotCross_sum_le w hk M hM _
  intro M hM
  exact variance_bound_of_wick_expansion w w.length S A
    (Fintype.card (Equiv.Perm (Fin (w.length + w.reverse.length))) : ℝ) hWick hmean hA M hM

/-! ### Almost-sure convergence -/

/-- **Almost-sure convergence from the slot expansion**: the variance bound together with the
convergence of the means gives almost-sure convergence of the trace word on the common Gaussian
space. -/
theorem ae_tendsto_gueNormTrace_of_slot (w : List ι) (hk : 1 ≤ w.length) (S : ℕ → ℂ) (L : ℂ)
    (hblock : ∀ (N : ℕ) (_ : 1 ≤ N) (V₀ : Fin (w.length + w.reverse.length) → Fin N),
      (∑ q ∈ (Finset.univ.filter fun q : GUEPairing (slotList w V₀) =>
          ¬ SlotCross w.length w.reverse.length (slotPerm q)), slotWeight N q) = (S N) ^ 2)
    (hmean : ∀ N : ℕ, Complex.normSq (∫ y, gueNormTrace w y
        ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))) =
      ((((N : ℂ)⁻¹) ^ (w.length + 2) * (S N) ^ 2)).re)
    (hmeanLimit : Tendsto (fun N : ℕ => ∫ y, gueNormTrace w y
      ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))) atTop (𝓝 L)) :
    ∀ᵐ x ∂(commonGaussianMeasure ι),
      Tendsto (fun N : ℕ => gueNormTrace w (x N)) atTop (𝓝 L) :=
  ae_tendsto_gueNormTrace w L
    (Fintype.card (Equiv.Perm (Fin (w.length + w.reverse.length))) : ℝ)
    (variance_bound_gueNormTrace w hk S hblock hmean) hmeanLimit

/-- **Almost-sure convergence with the explicit word limit**: if the mean has the one-walk genus
expansion over a list `l` of length `2m`, the almost-sure limit is the sum of the labels of the
non-crossing pairings. -/
theorem ae_tendsto_gueNormTrace_of_slot_genus (w : List ι) (hk : 1 ≤ w.length) (S : ℕ → ℂ)
    (hblock : ∀ (N : ℕ) (_ : 1 ≤ N) (V₀ : Fin (w.length + w.reverse.length) → Fin N),
      (∑ q ∈ (Finset.univ.filter fun q : GUEPairing (slotList w V₀) =>
          ¬ SlotCross w.length w.reverse.length (slotPerm q)), slotWeight N q) = (S N) ^ 2)
    (hmean : ∀ N : ℕ, Complex.normSq (∫ y, gueNormTrace w y
        ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))) =
      ((((N : ℂ)⁻¹) ^ (w.length + 2) * (S N) ^ 2)).re)
    (m : ℕ) (hm : 1 ≤ m) (l : List (GUEEntry ι N)) (hl : l.length = 2 * m)
    (label : GUEPairing l → ℂ)
    (hgenus : ∀ M : ℕ, (∫ y, gueNormTrace w y
        ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι M)))) =
      ((M : ℂ) ^ (m + 1))⁻¹ * ∑ p : GUEPairing l, label p * (M : ℂ) ^ (pairOrbitCount p)) :
    ∀ᵐ x ∂(commonGaussianMeasure ι),
      Tendsto (fun N : ℕ => gueNormTrace w (x N)) atTop
        (𝓝 (∑ p ∈ (Finset.univ.filter IsNonCrossing), label p)) := by
  classical
  refine ae_tendsto_gueNormTrace_of_slot w hk S _ hblock hmean ?_
  exact genus_limit_isNonCrossing l hl label
    (fun p hp => pairOrbitCount_eq_of_isNonCrossing p m hm hl hp) _ hgenus

/-- **Almost-sure convergence from the exact genus expansion in `zpow` form** — the shape produced
by `integral_gueNormTrace_eq_genus_canonical`. -/
theorem ae_tendsto_gueNormTrace_of_slot_zpow (w : List ι) (hk : 1 ≤ w.length) (S : ℕ → ℂ)
    (hblock : ∀ (N : ℕ) (_ : 1 ≤ N) (V₀ : Fin (w.length + w.reverse.length) → Fin N),
      (∑ q ∈ (Finset.univ.filter fun q : GUEPairing (slotList w V₀) =>
          ¬ SlotCross w.length w.reverse.length (slotPerm q)), slotWeight N q) = (S N) ^ 2)
    (hmean : ∀ N : ℕ, Complex.normSq (∫ y, gueNormTrace w y
        ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))) =
      ((((N : ℂ)⁻¹) ^ (w.length + 2) * (S N) ^ 2)).re)
    (m : ℕ) (hm : 1 ≤ m) (K : List (GUEEntry ι N)) (hK : K.length = 2 * m)
    (label : GUEPairing K → ℂ)
    (hgenus : ∀ M : ℕ, (∫ y, gueNormTrace w y
        ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι M)))) =
      (M : ℂ) ^ (-(m + 1) : ℤ) * ∑ p : GUEPairing K, label p * (M : ℂ) ^ (pairOrbitCount p)) :
    ∀ᵐ x ∂(commonGaussianMeasure ι),
      Tendsto (fun N : ℕ => gueNormTrace w (x N)) atTop
        (𝓝 (∑ p ∈ (Finset.univ.filter IsNonCrossing), label p)) := by
  refine ae_tendsto_gueNormTrace_of_slot_genus w hk S hblock hmean m hm K hK label ?_
  intro M
  rw [hgenus M, show (M : ℂ) ^ (-(m + 1) : ℤ) = ((M : ℂ) ^ (m + 1))⁻¹ by
    rw [zpow_neg, show ((m : ℤ) + 1) = ((m + 1 : ℕ) : ℤ) by omega, zpow_natCast]]

end

end GUEStrongConvergence
