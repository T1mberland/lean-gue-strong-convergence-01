/-
# HT05 harness: assembling `HT05Inputs` from the invertibility inputs

`StrongConvergence/HT05Final.lean` reduces the project target to the per-pencil inputs
`HT05Inputs N A₀ A η₀ Cst`.  This file supplies those inputs from the analytic input that is
proved independently (`StrongConvergence/HT05Invertibility.lean`, not imported here):

* `IsUnit (gueResolventMean A₀ A z)` and `frob (gueResolventMean A₀ A z)⁻¹ ≤ C_inv (im z)⁻¹`
  for `0 < im z` (taken below as explicit hypotheses, so that substitution is mechanical);
* the Dyson left-inverse `m⁻¹ * m = 1` at every `0 < im z`.

## Contents

1. `analyticOnNhd_selfEnergy_sub`, `analyticOnNhd_selfEnergy` — **analyticity of the
   self-energy branch** `z ↦ selfEnergy A₀ A z - A₀ = ∑ i, A i * m(z) * A i + m(z)⁻¹` on any
   subset of the upper half-plane on which `m` is invertible.
2. `ht05EselfEnergyConst`, `frob_selfEnergy_sub_smul_one_le_const`,
   `isUnit_operatorMatrixDifference_selfEnergy` — the explicit self-energy constant and
   invertibility of the operator-valued difference from the Frobenius closeness bound.
3. `norm_operatorMatrixArgumentResolvent_selfEnergy_le` — `‖res(Λ - A₀)‖ ≤ 2 / im z` via the
   Neumann factorization around the self-adjoint pencil.
4. `gueResolventMean_eq_operatorMatrixArgumentCauchy_of_small_point`, `exists_small_point`,
   `ht05E_threshold_small`, `ht05E_lt_threshold_of_small` — the physical-branch identification
   on a half-plane from the *small-point* form of the Dyson uniqueness theorem (so no
   normalization-at-infinity lemmas are needed).
5. `HT05Inputs_of_invertible`, `HT05InvertibilityInput`, `HT05Inputs_of_invertibilityInput`,
   `GUEStrongConvergenceStatement_of_invertible` — the harness for a constant inverse bound
   `frob (m⁻¹) ≤ C_inv (im z)⁻¹`; `GUEStrongConvergenceStatement_of_HT05Inputs` then gives the
   project target.
6. **Weighted interface** (§7-8): the unconditional self-energy bound
   (`HT05Invertibility.frob_selfEnergy_sub_smul_one_le`) carries a genuine `‖z‖²` factor
   (`selfEnergy - z • 1 = -(meanCentredDefect) * m⁻¹` with `frob (meanCentredDefect) =
   O(N⁻² (im z)⁻⁴)` and `frob (m⁻¹) ≳ ‖z‖`), so the unweighted `HT05Inputs` is false for large
   `|Re z|`.  `HT05Inputs'` therefore carries `(1 + ‖z‖)²` in both conjuncts, and
   `weightedStripBoundProven_of_HT05Inputs'` turns it into the honest weighted strip bound
   `WeightedStripBoundProven A₀ A η₀ 1 (4 (card d)² Cst)`.  **Soundness of the `∀ᶠ N, ∀ z`
   order:** the good branch is only invoked where the *weighted* good-region inequality holds;
   every point with large `|Re z|` satisfies its complement and is absorbed by the trivial
   bound `2 (card d) / im z` in the bad branch, so no large-`|Re z|` case is left over.
   The weighted endgame wiring is `weightedStripDataAtRepair_of_HT05Inputs'`,
   `weightedStripInputsRepair_of_HT05Inputs'`, `GUEStrongConvergenceStatement_of_HT05Inputs'`.

No `sorry`, no new axioms.
-/
import GUEStrongConvergence.StrongConvergence.HT05Final
import GUEStrongConvergence.StrongConvergence.HT05ArgumentAnalytic
import GUEStrongConvergence.Probability.DysonLimit

open MeasureTheory ProbabilityTheory Matrix Filter
open FreeProbability FreeProbability.Fock
open scoped Matrix.Norms.Operator ComplexOrder ENNReal NNReal Topology BigOperators

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

namespace GUEStrongConvergence

noncomputable section

variable {ι d : Type*} [Fintype ι] [Fintype d] [DecidableEq d] [DecidableEq ι]

noncomputable local instance ht05EPartialOrder :
    PartialOrder (WordSpace ι →L[ℂ] WordSpace ι) :=
  CStarAlgebra.spectralOrder _
noncomputable local instance ht05EStarOrderedRing :
    StarOrderedRing (WordSpace ι →L[ℂ] WordSpace ι) :=
  CStarAlgebra.spectralOrderedRing _

/-! ## 1. Analyticity of the self-energy branch -/

/-- **Analyticity of the finite-`N` self-energy shifted by `A₀`.**

`selfEnergy A₀ A z - A₀ = ∑ i, A i * m(z) * A i + m(z)⁻¹`; the finite sum of products of the
analytic averaged resolvent is analytic, and `m(z)⁻¹ = Ring.inverse (m z)` is the composition of
the analytic averaged resolvent with the inverse map, which is analytic at every unit. -/
theorem analyticOnNhd_selfEnergy_sub {N : ℕ} (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    (hA₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian) (hN : 0 < N)
    {U : Set ℂ} (hU : ∀ z ∈ U, 0 < z.im)
    (hUnit : ∀ z ∈ U, IsUnit (gueResolventMean (N := N) A₀ A z)) :
    AnalyticOnNhd ℂ (fun z => selfEnergy (N := N) A₀ A z - A₀) U := by
  have hAnM : AnalyticOnNhd ℂ (fun z => gueResolventMean (N := N) A₀ A z) {z : ℂ | 0 < z.im} :=
    analytic_gueResolventMean A₀ A hA₀ hA hN
  intro z hz
  have hzM : AnalyticAt ℂ (fun w => gueResolventMean (N := N) A₀ A w) z := hAnM z (hU z hz)
  -- the quadratic term
  have hsum : AnalyticAt ℂ
      (fun w => ∑ i, A i * gueResolventMean (N := N) A₀ A w * A i) z := by
    have h := Finset.analyticAt_sum
      (f := fun i (w : ℂ) => A i * gueResolventMean (N := N) A₀ A w * A i) Finset.univ
      (fun i _ => (analyticAt_const.mul hzM).mul analyticAt_const)
    have hfun : (∑ n, fun w : ℂ => A n * gueResolventMean (N := N) A₀ A w * A n) =
        fun w => ∑ i, A i * gueResolventMean (N := N) A₀ A w * A i := by
      funext w
      rw [Finset.sum_apply]
    rwa [hfun] at h
  -- the inverse term
  have hinv : AnalyticAt ℂ (fun w => (gueResolventMean (N := N) A₀ A w)⁻¹) z := by
    have h1 : AnalyticAt ℂ (fun w => Ring.inverse (gueResolventMean (N := N) A₀ A w)) z := by
      obtain ⟨u, hu⟩ := hUnit z hz
      have h2 : AnalyticAt ℂ Ring.inverse (gueResolventMean (N := N) A₀ A z) := by
        rw [← hu]
        exact analyticAt_inverse u
      exact h2.comp hzM
    refine h1.congr ?_
    filter_upwards with w
    exact (Matrix.nonsing_inv_eq_ringInverse (gueResolventMean (N := N) A₀ A w)).symm
  have hfun : (fun w => selfEnergy (N := N) A₀ A w - A₀) =
      fun w => (∑ i, A i * gueResolventMean (N := N) A₀ A w * A i) +
        (gueResolventMean (N := N) A₀ A w)⁻¹ := by
    funext w
    simp only [selfEnergy]
    abel
  rw [hfun]
  exact hsum.add hinv

/-- Analyticity of the finite-`N` self-energy branch itself. -/
theorem analyticOnNhd_selfEnergy {N : ℕ} (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    (hA₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian) (hN : 0 < N)
    {U : Set ℂ} (hU : ∀ z ∈ U, 0 < z.im)
    (hUnit : ∀ z ∈ U, IsUnit (gueResolventMean (N := N) A₀ A z)) :
    AnalyticOnNhd ℂ (fun z => selfEnergy (N := N) A₀ A z) U := by
  have h := analyticOnNhd_selfEnergy_sub A₀ A hA₀ hA hN hU hUnit
  have hfun : (fun z => selfEnergy (N := N) A₀ A z) =
      fun z => (selfEnergy (N := N) A₀ A z - A₀) + A₀ := by
    funext z
    abel
  rw [hfun]
  exact h.add analyticOnNhd_const

/-! ## 2. The explicit self-energy constant and invertibility of the difference -/

/-- The explicit self-energy constant `C_A = 4 (card d)² (∑_i frob(A i)²)² C_inv` produced by
`frob_selfEnergy_sub_smul_one_le`. -/
def ht05EselfEnergyConst (Cinv : ℝ) (A : ι → Matrix d d ℂ) : ℝ :=
  4 * (Fintype.card d : ℝ) ^ 2 * (∑ i, (frob (A i)) ^ 2) ^ 2 * Cinv

/-- The self-energy constant is nonnegative for `C_inv ≥ 0`. -/
lemma ht05EselfEnergyConst_nonneg {Cinv : ℝ} (hCinv : 0 ≤ Cinv) (A : ι → Matrix d d ℂ) :
    0 ≤ ht05EselfEnergyConst (ι := ι) (d := d) Cinv A := by
  rw [ht05EselfEnergyConst]
  have h1 : (0 : ℝ) ≤ (Fintype.card d : ℝ) ^ 2 := by positivity
  have h2 : (0 : ℝ) ≤ (∑ i, (frob (A i)) ^ 2) ^ 2 := sq_nonneg _
  exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) h1) h2) hCinv

/-- `y^(-5) * y⁻¹ = y^(-6)` for `y > 0`. -/
lemma ht05E_rpow_neg_five_mul_inv {y : ℝ} (hy : 0 < y) :
    y ^ (-(5 : ℝ)) * y⁻¹ = y ^ (-(6 : ℝ)) := by
  rw [Real.rpow_neg hy.le, Real.rpow_neg hy.le, Real.rpow_ofNat, Real.rpow_ofNat]
  field_simp

/-- **The explicit self-energy bound** `frob (selfEnergy - z • 1) ≤ C_A (im z)^(-5) / N²`. -/
theorem frob_selfEnergy_sub_smul_one_le_const {N : ℕ} (A₀ : Matrix d d ℂ)
    (A : ι → Matrix d d ℂ) (hA₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian)
    {Cinv : ℝ} (hCinv : 0 ≤ Cinv)
    (hminv : ∀ z : ℂ, 0 < z.im →
      frob ((gueResolventMean (N := N) A₀ A z)⁻¹) ≤ Cinv * (z.im)⁻¹)
    (hm : ∀ z : ℂ, 0 < z.im →
      gueResolventMean (N := N) A₀ A z * (gueResolventMean (N := N) A₀ A z)⁻¹ = 1)
    (hmL : ∀ z : ℂ, 0 < z.im →
      (gueResolventMean (N := N) A₀ A z)⁻¹ * gueResolventMean (N := N) A₀ A z = 1)
    (hN : 0 < N) :
    ∀ z : ℂ, 0 < z.im →
      frob (selfEnergy (N := N) A₀ A z - z • (1 : Matrix d d ℂ)) ≤
        ht05EselfEnergyConst (ι := ι) (d := d) Cinv A * z.im ^ (-(5 : ℝ)) / (N : ℝ) ^ 2 := by
  intro z hz
  have h := frob_selfEnergy_sub_smul_one_le_of_inv (N := N) A₀ A hA₀ hA hz hCinv
    (hminv z hz) (hm z hz) (hmL z hz) hN
  simpa only [ht05EselfEnergyConst] using h

/-- **Invertibility of the operator-valued difference at the self-energy argument.**

On the region where `Cst (im z)^(-6) / N² < 1/2` and `Cst ≥ card d * C_A`, the Frobenius
distance from the genuine pencil point is small enough for
`isUnit_operatorMatrixDifference_of_frob_close`. -/
theorem isUnit_operatorMatrixDifference_selfEnergy {N : ℕ} (A₀ : Matrix d d ℂ)
    (A : ι → Matrix d d ℂ) (hA₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian)
    {Cinv Cst : ℝ} (hCinv : 0 ≤ Cinv) (hCst0 : 0 ≤ Cst)
    (hCst : (Fintype.card d : ℝ) * ht05EselfEnergyConst (ι := ι) (d := d) Cinv A ≤ Cst)
    (hminv : ∀ z : ℂ, 0 < z.im →
      frob ((gueResolventMean (N := N) A₀ A z)⁻¹) ≤ Cinv * (z.im)⁻¹)
    (hm : ∀ z : ℂ, 0 < z.im →
      gueResolventMean (N := N) A₀ A z * (gueResolventMean (N := N) A₀ A z)⁻¹ = 1)
    (hmL : ∀ z : ℂ, 0 < z.im →
      (gueResolventMean (N := N) A₀ A z)⁻¹ * gueResolventMean (N := N) A₀ A z = 1)
    (hN : 0 < N) {z : ℂ} (hz : 0 < z.im)
    (hsmall : Cst * z.im ^ (-(6 : ℝ)) / (N : ℝ) ^ 2 < 1 / 2) :
    IsUnit (operatorMatrixDifference A (selfEnergy (N := N) A₀ A z - A₀)) := by
  have hfr := frob_selfEnergy_sub_smul_one_le_const (N := N) A₀ A hA₀ hA hCinv hminv hm hmL hN z hz
  refine isUnit_operatorMatrixDifference_of_frob_close A₀ A hA₀ hA _ z hz ?_
  have hcard0 : (0 : ℝ) ≤ (Fintype.card d : ℝ) := by positivity
  have hN2 : (0 : ℝ) < (N : ℝ) ^ 2 := by positivity
  have him5 : (0 : ℝ) ≤ z.im ^ (-(5 : ℝ)) := (Real.rpow_pos_of_pos hz _).le
  have hinv0 : (0 : ℝ) ≤ (z.im)⁻¹ := by positivity
  -- bound the product by `Cst (im z)^(-6) / N²`
  have hstep : (Fintype.card d : ℝ) * frob (selfEnergy (N := N) A₀ A z - z • (1 : Matrix d d ℂ)) *
      (z.im)⁻¹ ≤ Cst * z.im ^ (-(6 : ℝ)) / (N : ℝ) ^ 2 := by
    have h1 : (Fintype.card d : ℝ) *
        frob (selfEnergy (N := N) A₀ A z - z • (1 : Matrix d d ℂ)) * (z.im)⁻¹ ≤
        (Fintype.card d : ℝ) *
          (ht05EselfEnergyConst (ι := ι) (d := d) Cinv A * z.im ^ (-(5 : ℝ)) / (N : ℝ) ^ 2) *
          (z.im)⁻¹ := by
      refine mul_le_mul_of_nonneg_right ?_ hinv0
      exact mul_le_mul_of_nonneg_left hfr hcard0
    refine h1.trans ?_
    have heq1 : (Fintype.card d : ℝ) *
          (ht05EselfEnergyConst (ι := ι) (d := d) Cinv A * z.im ^ (-(5 : ℝ)) / (N : ℝ) ^ 2) *
          (z.im)⁻¹ =
        ((Fintype.card d : ℝ) * ht05EselfEnergyConst (ι := ι) (d := d) Cinv A) *
          (z.im ^ (-(5 : ℝ)) * (z.im)⁻¹) / (N : ℝ) ^ 2 := by ring
    rw [heq1, ht05E_rpow_neg_five_mul_inv hz]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hCst
      (Real.rpow_pos_of_pos hz _).le) hN2.le
  exact lt_of_le_of_lt hstep (lt_trans hsmall (by norm_num))


/-! ## 3. The operator resolvent norm bound `‖res(Λ - A₀)‖ ≤ 2 / im z` -/

/-- `y^(-6) * y = y^(-5)` for `y > 0`. -/
lemma ht05E_rpow_neg_six_mul {y : ℝ} (hy : 0 < y) :
    y ^ (-(6 : ℝ)) * y = y ^ (-(5 : ℝ)) := by
  rw [Real.rpow_neg hy.le, Real.rpow_neg hy.le, Real.rpow_ofNat, Real.rpow_ofNat]
  field_simp

/-- **The operator-valued resolvent at the self-energy argument is `O((im z)⁻¹)`.**

Writing `X = (z • 1 - P) + δ` with `P` the self-adjoint operator pencil and
`δ = (Λ - z • 1) ⊗ 1` the embedded self-energy defect, the Neumann factorization
`X = (z • 1 - P) * (1 + (z • 1 - P)⁻¹ δ)` and `‖(z • 1 - P)⁻¹‖ ≤ (im z)⁻¹` give
`‖X⁻¹‖ ≤ 2 (im z)⁻¹` as soon as the good-region smallness condition holds. -/
theorem norm_operatorMatrixArgumentResolvent_selfEnergy_le {N : ℕ}
    (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ) (hA₀ : A₀.IsHermitian)
    (hA : ∀ i, (A i).IsHermitian) {CA Cst : ℝ}
    (hfr : ∀ z : ℂ, 0 < z.im →
      frob (selfEnergy (N := N) A₀ A z - z • (1 : Matrix d d ℂ)) ≤
        CA * z.im ^ (-(5 : ℝ)) / (N : ℝ) ^ 2)
    (hCst : (Fintype.card d : ℝ) * CA ≤ Cst)
    {z : ℂ} (hz : 0 < z.im)
    (hsmall : Cst * z.im ^ (-(6 : ℝ)) / (N : ℝ) ^ 2 < 1 / 2) :
    ‖CStarMatrix.ofMatrix
      (operatorMatrixArgumentResolvent A (selfEnergy (N := N) A₀ A z - A₀))‖ ≤ 2 / z.im := by
  set Λ : Matrix d d ℂ := selfEnergy (N := N) A₀ A z with hΛ
  set P : CStarMatrix d d (WordSpace ι →L[ℂ] WordSpace ι) :=
    operatorMatrixDifference A (z • (1 : Matrix d d ℂ) - A₀) with hPdef
  set δ : CStarMatrix d d (WordSpace ι →L[ℂ] WordSpace ι) :=
    CStarMatrix.ofMatrix (scalarMatrixEmbedding
      (A := WordSpace ι →L[ℂ] WordSpace ι) (Λ - z • (1 : Matrix d d ℂ))) with hδdef
  have hPunit : IsUnit P := by
    rw [hPdef, operatorMatrixDifference_pencil]
    exact StarProbabilitySpace.selfAdjoint_mem_resolventSet_of_im_ne_zero
      (operatorMatrixPencil A₀ A) (operatorMatrixPencil_isSelfAdjoint A₀ A hA₀ hA) z hz.ne'
  have hPinv : ‖Ring.inverse P‖ ≤ (z.im)⁻¹ := by
    rw [hPdef, operatorMatrixDifference_pencil]
    have h := norm_resolvent_le_inv_im
      (operatorMatrixPencil_isSelfAdjoint A₀ A hA₀ hA) (z := z) hz
    simpa [resolvent] using h
  have hX : operatorMatrixDifference A (Λ - A₀) = P + δ := by
    have hE : (Λ - A₀) - (z • (1 : Matrix d d ℂ) - A₀) = Λ - z • (1 : Matrix d d ℂ) := by
      abel
    have hsub := operatorMatrixDifference_sub (C := A) (B₁ := Λ - A₀)
      (B₂ := z • (1 : Matrix d d ℂ) - A₀)
    rw [hE] at hsub
    have hδ' : δ = scalarMatrixEmbedding (Λ - z • (1 : Matrix d d ℂ)) := by
      rw [hδdef]
      rfl
    rw [hPdef, hδ', ← hsub]
    abel
  -- the perturbation is at most `im z / 2` in norm
  have hδnorm : ‖δ‖ ≤ z.im / 2 := by
    have h1 : ‖δ‖ ≤ (Fintype.card d : ℝ) * frob (Λ - z • (1 : Matrix d d ℂ)) := by
      rw [hδdef]
      exact norm_scalarMatrixEmbedding_le_card_mul_frob_local _
    have hcard0 : (0 : ℝ) ≤ (Fintype.card d : ℝ) := by positivity
    have h2 : (Fintype.card d : ℝ) * frob (Λ - z • (1 : Matrix d d ℂ)) ≤
        (Fintype.card d : ℝ) * (CA * z.im ^ (-(5 : ℝ)) / (N : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_left (by rw [hΛ]; exact hfr z hz) hcard0
    refine h1.trans (h2.trans ?_)
    have heq : (Fintype.card d : ℝ) * (CA * z.im ^ (-(5 : ℝ)) / (N : ℝ) ^ 2) =
        ((Fintype.card d : ℝ) * CA) * z.im ^ (-(5 : ℝ)) / (N : ℝ) ^ 2 := by ring
    rw [heq]
    have hle : ((Fintype.card d : ℝ) * CA) * z.im ^ (-(5 : ℝ)) / (N : ℝ) ^ 2 ≤
        Cst * z.im ^ (-(5 : ℝ)) / (N : ℝ) ^ 2 := by
      refine div_le_div_of_nonneg_right ?_ (by positivity)
      exact mul_le_mul_of_nonneg_right hCst (Real.rpow_pos_of_pos hz _).le
    refine hle.trans ?_
    have hmul := mul_lt_mul_of_pos_right hsmall hz
    have heq2 : Cst * z.im ^ (-(6 : ℝ)) / (N : ℝ) ^ 2 * z.im =
        Cst * z.im ^ (-(5 : ℝ)) / (N : ℝ) ^ 2 := by
      rw [div_mul_eq_mul_div, mul_assoc, ht05E_rpow_neg_six_mul hz]
    rw [heq2] at hmul
    linarith [hmul]
  -- the Neumann factor
  set Y : CStarMatrix d d (WordSpace ι →L[ℂ] WordSpace ι) := Ring.inverse P * δ with hYdef
  have hY : ‖Y‖ ≤ 1 / 2 := by
    have h1 : ‖Y‖ ≤ ‖Ring.inverse P‖ * ‖δ‖ := by
      rw [hYdef]; exact norm_mul_le _ _
    have h2 : ‖Ring.inverse P‖ * ‖δ‖ ≤ (z.im)⁻¹ * (z.im / 2) := by
      refine mul_le_mul hPinv hδnorm (norm_nonneg _) (by positivity)
    have h3 : (z.im)⁻¹ * (z.im / 2) = 1 / 2 := by
      field_simp
    linarith [h1, h2, h3.symm.le]
  have hYlt : ‖Y‖ < 1 := lt_of_le_of_lt hY (by norm_num)
  have hPeq : P + δ = P * (1 + Y) := by
    rw [hYdef, mul_add, mul_one, ← mul_assoc, Ring.mul_inverse_cancel P hPunit, one_mul]
  have hfac : Ring.inverse (operatorMatrixDifference A (Λ - A₀)) =
      Ring.inverse (1 + Y) * Ring.inverse P := by
    rw [hX, hPeq, Ring.inverse_mul (Or.inl hPunit)]
  have hone : ‖(1 : CStarMatrix d d (WordSpace ι →L[ℂ] WordSpace ι))‖ ≤ 1 := by
    have h : ‖(1 : CStarMatrix d d (WordSpace ι →L[ℂ] WordSpace ι))‖ =
        ‖(1 : CStarMatrix d d (WordSpace ι →L[ℂ] WordSpace ι))‖ *
          ‖(1 : CStarMatrix d d (WordSpace ι →L[ℂ] WordSpace ι))‖ := by
      rw [← CStarRing.norm_star_mul_self
        (x := (1 : CStarMatrix d d (WordSpace ι →L[ℂ] WordSpace ι))), star_one, one_mul]
    nlinarith [norm_nonneg (1 : CStarMatrix d d (WordSpace ι →L[ℂ] WordSpace ι))]
  have hnormY : ‖Ring.inverse (1 + Y)‖ ≤ 2 := by
    have hneglt : ‖-Y‖ < 1 := by rwa [norm_neg]
    have hgeom : Ring.inverse (1 + Y) = ∑' i : ℕ, (-Y) ^ i := by
      have hstep : (1 : CStarMatrix d d (WordSpace ι →L[ℂ] WordSpace ι)) + Y = 1 - (-Y) := by
        rw [sub_neg_eq_add]
      rw [hstep, ← geom_series_eq_inverse (-Y) hneglt]
    rw [hgeom]
    have hle := tsum_geometric_le_of_norm_lt_one (-Y) hneglt
    have hnormneg : ‖-Y‖ ≤ 1 / 2 := by rw [norm_neg]; exact hY
    have hlow : (1 - ‖-Y‖)⁻¹ ≤ 2 := by
      have h0 : (0 : ℝ) < 1 - ‖-Y‖ := by linarith
      have hhalf : (1 : ℝ) / 2 ≤ 1 - ‖-Y‖ := by linarith
      calc (1 - ‖-Y‖)⁻¹ = 1 / (1 - ‖-Y‖) := by rw [one_div]
        _ ≤ 1 / ((1 : ℝ) / 2) := one_div_le_one_div_of_le (by norm_num) hhalf
        _ = 2 := by norm_num
    linarith
  have hmain : ‖Ring.inverse (operatorMatrixDifference A (Λ - A₀))‖ ≤ 2 / z.im := by
    rw [hfac]
    calc ‖Ring.inverse (1 + Y) * Ring.inverse P‖
        ≤ ‖Ring.inverse (1 + Y)‖ * ‖Ring.inverse P‖ := norm_mul_le _ _
      _ ≤ 2 * (z.im)⁻¹ := by
          refine mul_le_mul hnormY hPinv (norm_nonneg _) (by norm_num)
      _ = 2 / z.im := by ring
  simpa only [operatorMatrixArgumentResolvent, Equiv.apply_symm_apply, hΛ] using hmain


/-! ## 4. Norm comparisons and the physical-branch identification -/

/-- The operator (row) norm of a square complex matrix is at most `card d` times the Frobenius
norm. -/
lemma norm_le_card_mul_frob (M : Matrix d d ℂ) :
    ‖M‖ ≤ (Fintype.card d : ℝ) * frob M := by
  refine (ht05_linfty_opNorm_le_sum_entries M).trans ?_
  rw [Finset.sum_comm]
  exact sum_norm_entries_le_card_mul_frob M

/-- Entrywise bound for the matrix-argument Cauchy transform, from a bound on the operator
resolvent. -/
lemma norm_operatorMatrixArgumentCauchy_entry_le (A : ι → Matrix d d ℂ) (B : Matrix d d ℂ)
    {η : ℝ} (hη : ‖CStarMatrix.ofMatrix (operatorMatrixArgumentResolvent A B)‖ ≤ η) (i j : d) :
    ‖operatorMatrixArgumentCauchy A B i j‖ ≤ η := by
  rw [operatorMatrixArgumentCauchy, matrixExpectation_apply, operatorMatrixArgumentResolvent,
    CStarMatrix.ofMatrix_symm_apply]
  exact (norm_vacuumExpectation_le (Ring.inverse (operatorMatrixDifference A B) i j)).trans
    ((CStarMatrix.norm_entry_le_norm (M := Ring.inverse (operatorMatrixDifference A B))).trans hη)

/-- Frobenius bound for the matrix-argument Cauchy transform from an operator-resolvent bound. -/
lemma frob_operatorMatrixArgumentCauchy_le_of_resolvent
    (A : ι → Matrix d d ℂ) (B : Matrix d d ℂ) {η : ℝ} (hη0 : 0 ≤ η)
    (hη : ‖CStarMatrix.ofMatrix (operatorMatrixArgumentResolvent A B)‖ ≤ η) :
    frob (operatorMatrixArgumentCauchy A B) ≤ (Fintype.card d : ℝ) * η :=
  frob_le_card_mul_of_entry_le _
    (fun i j => norm_operatorMatrixArgumentCauchy_entry_le A B hη i j) hη0

/-- **The self-energy minus `A₀` minus the covariance is `m⁻¹`.** -/
lemma selfEnergy_sub_A₀_sub_covariance {N : ℕ} (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    (z : ℂ) :
    selfEnergy (N := N) A₀ A z - A₀ -
        matrixCovariance A (gueResolventMean (N := N) A₀ A z) =
      (gueResolventMean (N := N) A₀ A z)⁻¹ := by
  rw [selfEnergy, matrixCovariance_apply]
  abel

/-- **The physical-branch identification on the half-plane `{r < im z}`.**

All inputs are explicit: the invertibility data for the finite-`N` mean (Worker D's output), the
good-region smallness condition `Cst (im z)^(-6)/N² < 1/2` (supplied through `r`), and one point
`z₀` in the half-plane where the two branches are small.  The uniqueness theorem
`matrixDyson_analytic_unique_of_small_point` then identifies the mean with the matrix-argument
Cauchy transform throughout the half-plane. -/
theorem gueResolventMean_eq_operatorMatrixArgumentCauchy_of_small_point {N : ℕ}
    (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ) (hA₀ : A₀.IsHermitian)
    (hA : ∀ i, (A i).IsHermitian) (hN : 0 < N) {Cinv Cst r : ℝ}
    (hCinv : 0 ≤ Cinv)
    (hminv : ∀ z : ℂ, 0 < z.im →
      frob ((gueResolventMean (N := N) A₀ A z)⁻¹) ≤ Cinv * (z.im)⁻¹)
    (hm : ∀ z : ℂ, 0 < z.im →
      gueResolventMean (N := N) A₀ A z * (gueResolventMean (N := N) A₀ A z)⁻¹ = 1)
    (hmL : ∀ z : ℂ, 0 < z.im →
      (gueResolventMean (N := N) A₀ A z)⁻¹ * gueResolventMean (N := N) A₀ A z = 1)
    (hmunit : ∀ z : ℂ, 0 < z.im → IsUnit (gueResolventMean (N := N) A₀ A z))
    (hCst : (Fintype.card d : ℝ) *
      ht05EselfEnergyConst (ι := ι) (d := d) Cinv A ≤ Cst) (hrpos : 0 < r)
    (hr : ∀ z : ℂ, r < z.im → Cst * z.im ^ (-(6 : ℝ)) / (N : ℝ) ^ 2 < 1 / 2)
    (z₀ : ℂ) (hz₀ : r < z₀.im)
    (hsmall : ‖gueResolventMean (N := N) A₀ A z₀‖ * (∑ i, ‖A i‖ ^ 2) *
      ‖operatorMatrixArgumentCauchy A (selfEnergy (N := N) A₀ A z₀ - A₀)‖ < 1) :
    Set.EqOn (gueResolventMean (N := N) A₀ A)
      (fun z => operatorMatrixArgumentCauchy A (selfEnergy (N := N) A₀ A z - A₀))
      {z : ℂ | r < z.im} := by
  set U : Set ℂ := {z : ℂ | r < z.im} with hUdef
  have hUopen : IsOpen U := isOpen_lt continuous_const Complex.continuous_im
  have hUconv : Convex ℝ U := by
    intro x hx y hy a b ha hb hab
    simp only [U, Set.mem_ofPred_eq, Complex.add_im, Complex.smul_im, smul_eq_mul] at hx hy ⊢
    rcases lt_or_eq_of_le ha with hapos | hazero
    · have h1 : a * r < a * x.im := mul_lt_mul_of_pos_left hx hapos
      have h2 : b * r ≤ b * y.im := mul_le_mul_of_nonneg_left hy.le hb
      have h3 : a * r + b * r = r := by rw [← add_mul, hab, one_mul]
      linarith
    · subst hazero
      have hb1 : b = 1 := by linarith
      subst hb1
      simpa using hy
  have hUconn : IsPreconnected U := hUconv.isPreconnected
  have hpos : ∀ z ∈ U, 0 < z.im := fun z hz => lt_trans hrpos hz
  have hUnit : ∀ z ∈ U,
      IsUnit (operatorMatrixDifference A (selfEnergy (N := N) A₀ A z - A₀)) :=
    fun z hz => isUnit_operatorMatrixDifference_selfEnergy A₀ A hA₀ hA hCinv
      (le_trans (mul_nonneg (by positivity) (ht05EselfEnergyConst_nonneg hCinv A)) hCst) hCst
      hminv hm hmL hN (hpos z hz) (hr z hz)
  refine matrixDyson_analytic_unique_of_small_point A
    (fun z => selfEnergy (N := N) A₀ A z - A₀) (gueResolventMean (N := N) A₀ A)
    (fun z => operatorMatrixArgumentCauchy A (selfEnergy (N := N) A₀ A z - A₀)) U
    hUopen hUconn
    ((analytic_gueResolventMean A₀ A hA₀ hA hN).mono (fun z hz => hpos z hz))
    (analyticOnNhd_operatorMatrixArgumentCauchy_comp A
      (fun z => selfEnergy (N := N) A₀ A z) A₀ U
      (analyticOnNhd_selfEnergy A₀ A hA₀ hA hN hpos
        (fun z hz => hmunit z (hpos z hz)))
      hUnit)
    (fun z hz => by
      rw [selfEnergy_sub_A₀_sub_covariance]
      exact hmL z (hpos z hz))
    (fun z hz => operatorMatrixArgumentCauchy_dyson A
      (selfEnergy (N := N) A₀ A z - A₀) (hUnit z hz))
    z₀ hz₀ hsmall


/-! ## 5. The explicit threshold `(2 Cst / N²)^(1/6)` -/

/-- **The smallness condition from the explicit half-plane threshold.** -/
lemma ht05E_threshold_small {N : ℕ} (hN : 0 < N) {Cst : ℝ} (hCst : 0 < Cst) {z : ℂ}
    (hz : (2 * Cst / (N : ℝ) ^ 2) ^ ((1 : ℝ) / 6) < z.im) :
    Cst * z.im ^ (-(6 : ℝ)) / (N : ℝ) ^ 2 < 1 / 2 := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hD : 0 < 2 * Cst / (N : ℝ) ^ 2 := by positivity
  set r : ℝ := (2 * Cst / (N : ℝ) ^ 2) ^ ((1 : ℝ) / 6) with hrdef
  have hy : 0 < z.im := lt_trans (Real.rpow_pos_of_pos hD _) hz
  have hr6 : r ^ (6 : ℝ) = 2 * Cst / (N : ℝ) ^ 2 := by
    have h2 : (2 * Cst / (N : ℝ) ^ 2) ^ ((1 : ℝ) / 6 * 6) = 2 * Cst / (N : ℝ) ^ 2 := by
      rw [show ((1 : ℝ) / 6 * 6) = 1 by norm_num, Real.rpow_one]
    calc r ^ (6 : ℝ) = ((2 * Cst / (N : ℝ) ^ 2) ^ ((1 : ℝ) / 6)) ^ (6 : ℝ) := by rw [hrdef]
      _ = (2 * Cst / (N : ℝ) ^ 2) ^ ((1 : ℝ) / 6 * 6) := (Real.rpow_mul hD.le _ _).symm
      _ = 2 * Cst / (N : ℝ) ^ 2 := h2
  have hlt : r ^ (6 : ℝ) < z.im ^ (6 : ℝ) :=
    Real.rpow_lt_rpow (Real.rpow_nonneg hD.le _) hz (by norm_num)
  rw [hr6] at hlt
  have hlt' : 2 * Cst / (N : ℝ) ^ 2 < z.im ^ 6 := by simpa using hlt
  have hy6 : 0 < z.im ^ 6 := by positivity
  have h3 : (2 * Cst / (N : ℝ) ^ 2) / 2 < z.im ^ 6 / 2 :=
    div_lt_div_of_pos_right hlt' (by norm_num)
  have h2 : Cst / (N : ℝ) ^ 2 < z.im ^ 6 / 2 := by
    calc Cst / (N : ℝ) ^ 2 = (2 * Cst / (N : ℝ) ^ 2) / 2 := by ring
      _ < z.im ^ 6 / 2 := h3
  have hy6inv : z.im ^ (-(6 : ℝ)) = (z.im ^ 6)⁻¹ := by
    rw [Real.rpow_neg hy.le, Real.rpow_ofNat]
  calc Cst * z.im ^ (-(6 : ℝ)) / (N : ℝ) ^ 2 = (Cst / (N : ℝ) ^ 2) * z.im ^ (-(6 : ℝ)) := by
        ring
    _ = (Cst / (N : ℝ) ^ 2) * (z.im ^ 6)⁻¹ := by rw [hy6inv]
    _ < (z.im ^ 6 / 2) * (z.im ^ 6)⁻¹ := mul_lt_mul_of_pos_right h2 (by positivity)
    _ = 1 / 2 := by field_simp

/-- **The half-plane threshold is implied by the smallness condition.** -/
lemma ht05E_lt_threshold_of_small {N : ℕ} (hN : 0 < N) {Cst : ℝ} (hCst : 0 < Cst) {z : ℂ}
    (hz : 0 < z.im) (hsmall : Cst * z.im ^ (-(6 : ℝ)) / (N : ℝ) ^ 2 < 1 / 2) :
    (2 * Cst / (N : ℝ) ^ 2) ^ ((1 : ℝ) / 6) < z.im := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hD : 0 < 2 * Cst / (N : ℝ) ^ 2 := by positivity
  have hy6 : 0 < z.im ^ 6 := by positivity
  have hy6inv : z.im ^ (-(6 : ℝ)) = (z.im ^ 6)⁻¹ := by
    rw [Real.rpow_neg hz.le, Real.rpow_ofNat]
  rw [hy6inv] at hsmall
  have hstep := mul_lt_mul_of_pos_right hsmall hy6
  rw [show Cst * (z.im ^ 6)⁻¹ / (N : ℝ) ^ 2 * z.im ^ 6 =
      Cst / (N : ℝ) ^ 2 by field_simp] at hstep
  have heq : (2 : ℝ) * (Cst / (N : ℝ) ^ 2) = 2 * Cst / (N : ℝ) ^ 2 := by ring
  have hDlt : 2 * Cst / (N : ℝ) ^ 2 < z.im ^ 6 := by linarith
  have hy6rpow : (z.im ^ 6 : ℝ) ^ ((1 : ℝ) / 6) = z.im := by
    have h1 : (z.im ^ 6 : ℝ) = z.im ^ (6 : ℝ) := (Real.rpow_natCast z.im 6).symm
    rw [h1, ← Real.rpow_mul hz.le]
    norm_num
  have hiff := Real.rpow_lt_rpow_iff (x := 2 * Cst / (N : ℝ) ^ 2) (y := z.im ^ 6)
    (z := ((1 : ℝ) / 6)) hD.le (by positivity)
    (by norm_num : (0 : ℝ) < 1 / 6)
  have hlt : (2 * Cst / (N : ℝ) ^ 2) ^ ((1 : ℝ) / 6) < (z.im ^ 6 : ℝ) ^ ((1 : ℝ) / 6) :=
    hiff.mpr hDlt
  rwa [hy6rpow] at hlt


/-- **A point of the half-plane at which both Dyson branches are small.**

At `z₀ = i Y` with `Y` large we have `‖m‖ ≤ (card d)²/Y` and `‖g‖ ≤ 2 (card d)²/Y`, so the
small-point hypothesis of `matrixDyson_analytic_unique_of_small_point` holds. -/
theorem exists_small_point {N : ℕ} (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    (hA₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian) (hN : 0 < N)
    {Cinv Cst r : ℝ} (hCinv : 0 ≤ Cinv)
    (hCst : (Fintype.card d : ℝ) *
      ht05EselfEnergyConst (ι := ι) (d := d) Cinv A ≤ Cst) (hrpos : 0 < r)
    (hr : ∀ z : ℂ, r < z.im → Cst * z.im ^ (-(6 : ℝ)) / (N : ℝ) ^ 2 < 1 / 2)
    (hminv : ∀ z : ℂ, 0 < z.im →
      frob ((gueResolventMean (N := N) A₀ A z)⁻¹) ≤ Cinv * (z.im)⁻¹)
    (hm : ∀ z : ℂ, 0 < z.im →
      gueResolventMean (N := N) A₀ A z * (gueResolventMean (N := N) A₀ A z)⁻¹ = 1)
    (hmL : ∀ z : ℂ, 0 < z.im →
      (gueResolventMean (N := N) A₀ A z)⁻¹ * gueResolventMean (N := N) A₀ A z = 1) :
    ∃ z₀ : ℂ, r < z₀.im ∧
      ‖gueResolventMean (N := N) A₀ A z₀‖ * (∑ i, ‖A i‖ ^ 2) *
        ‖operatorMatrixArgumentCauchy A (selfEnergy (N := N) A₀ A z₀ - A₀)‖ < 1 := by
  set S : ℝ := ∑ i, ‖A i‖ ^ 2 with hSdef
  have hS : 0 ≤ S := by
    rw [hSdef]
    exact Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hcard : (0 : ℝ) ≤ (Fintype.card d : ℝ) := by positivity
  have hcard2 : (0 : ℝ) ≤ (Fintype.card d : ℝ) ^ 2 := by positivity
  set K : ℝ := 2 * (Fintype.card d : ℝ) ^ 4 * S with hKdef
  have hK : 0 ≤ K := by
    rw [hKdef]
    have h1 : (0 : ℝ) ≤ (Fintype.card d : ℝ) ^ 4 := by positivity
    exact mul_nonneg (mul_nonneg (by norm_num) h1) hS
  set Y : ℝ := max r 0 + Real.sqrt K + 1 with hYdef
  have hYr : r < Y := by
    have h1 : r ≤ max r 0 := le_max_left _ _
    have h2 : 0 ≤ Real.sqrt K := Real.sqrt_nonneg _
    rw [hYdef]
    linarith
  have hYpos : 0 < Y := lt_trans hrpos hYr
  have hY2 : K < Y ^ 2 := by
    have hs : Real.sqrt K < Y := by
      have h1 : 0 ≤ max r 0 := le_max_right r 0
      have h2 : 0 ≤ Real.sqrt K := Real.sqrt_nonneg _
      rw [hYdef]
      linarith
    have hsq : (Real.sqrt K) ^ 2 = K := Real.sq_sqrt hK
    nlinarith [hs, hsq, Real.sqrt_nonneg K]
  refine ⟨(Y : ℂ) * Complex.I, ?_, ?_⟩
  · simpa using hYr
  have hz0im : ((Y : ℂ) * Complex.I).im = Y := by simp
  have hz0pos : 0 < ((Y : ℂ) * Complex.I).im := by rw [hz0im]; exact hYpos
  have hr0 : r < ((Y : ℂ) * Complex.I).im := by rw [hz0im]; exact hYr
  set M : ℝ := ‖gueResolventMean (N := N) A₀ A ((Y : ℂ) * Complex.I)‖ with hMdef
  set G : ℝ := ‖operatorMatrixArgumentCauchy A
    (selfEnergy (N := N) A₀ A ((Y : ℂ) * Complex.I) - A₀)‖ with hGdef
  have hM0 : 0 ≤ M := by rw [hMdef]; exact norm_nonneg _
  have hG0 : 0 ≤ G := by rw [hGdef]; exact norm_nonneg _
  have hm_bound : M ≤ (Fintype.card d : ℝ) ^ 2 * Y⁻¹ := by
    rw [hMdef]
    refine (norm_le_card_mul_frob _).trans ?_
    have h := frob_gueResolventMean_le A₀ A hA₀ hA ((Y : ℂ) * Complex.I) hz0pos hN
    rw [hz0im] at h
    calc (Fintype.card d : ℝ) * frob (gueResolventMean (N := N) A₀ A ((Y : ℂ) * Complex.I))
        ≤ (Fintype.card d : ℝ) * ((Fintype.card d : ℝ) * Y⁻¹) := by gcongr
      _ = (Fintype.card d : ℝ) ^ 2 * Y⁻¹ := by ring
  have hg_bound : G ≤ 2 * (Fintype.card d : ℝ) ^ 2 * Y⁻¹ := by
    rw [hGdef]
    have hfr := frob_selfEnergy_sub_smul_one_le_const (N := N) A₀ A hA₀ hA hCinv hminv hm hmL hN
    have hres : ‖CStarMatrix.ofMatrix (operatorMatrixArgumentResolvent A
        (selfEnergy (N := N) A₀ A ((Y : ℂ) * Complex.I) - A₀))‖ ≤
        2 / ((Y : ℂ) * Complex.I).im :=
      norm_operatorMatrixArgumentResolvent_selfEnergy_le A₀ A hA₀ hA (CA := ht05EselfEnergyConst
        (ι := ι) (d := d) Cinv A) (Cst := Cst) hfr hCst hz0pos (hr _ hr0)
    have hη0 : (0 : ℝ) ≤ 2 / ((Y : ℂ) * Complex.I).im := div_nonneg (by norm_num) hz0pos.le
    have hf := frob_operatorMatrixArgumentCauchy_le_of_resolvent A
      (selfEnergy (N := N) A₀ A ((Y : ℂ) * Complex.I) - A₀) hη0 hres
    refine (norm_le_card_mul_frob _).trans ?_
    calc (Fintype.card d : ℝ) * frob (operatorMatrixArgumentCauchy A
          (selfEnergy (N := N) A₀ A ((Y : ℂ) * Complex.I) - A₀))
        ≤ (Fintype.card d : ℝ) * ((Fintype.card d : ℝ) * (2 / ((Y : ℂ) * Complex.I).im)) := by
          gcongr
      _ = 2 * (Fintype.card d : ℝ) ^ 2 * Y⁻¹ := by rw [hz0im]; ring
  have hMSS : M * S ≤ ((Fintype.card d : ℝ) ^ 2 * Y⁻¹) * S :=
    mul_le_mul_of_nonneg_right hm_bound hS
  have hprod : M * S * G ≤ ((Fintype.card d : ℝ) ^ 2 * Y⁻¹) * S *
      (2 * (Fintype.card d : ℝ) ^ 2 * Y⁻¹) := by
    refine mul_le_mul hMSS hg_bound hG0 ?_
    exact mul_nonneg (mul_nonneg hcard2 (inv_nonneg.mpr hYpos.le)) hS
  have heq : ((Fintype.card d : ℝ) ^ 2 * Y⁻¹) * S * (2 * (Fintype.card d : ℝ) ^ 2 * Y⁻¹) =
      K / Y ^ 2 := by
    rw [hKdef, div_eq_mul_inv]
    have h1 : Y⁻¹ * Y⁻¹ = (Y ^ 2)⁻¹ := by rw [← mul_inv, pow_two]
    calc ((Fintype.card d : ℝ) ^ 2 * Y⁻¹) * S * (2 * (Fintype.card d : ℝ) ^ 2 * Y⁻¹)
        = 2 * (Fintype.card d : ℝ) ^ 4 * S * (Y⁻¹ * Y⁻¹) := by ring
      _ = 2 * (Fintype.card d : ℝ) ^ 4 * S * (Y ^ 2)⁻¹ := by rw [h1]
  have hfinal : M * S * G ≤ K / Y ^ 2 := hprod.trans (le_of_eq heq)
  have hYsq : (0 : ℝ) < Y ^ 2 := pow_pos hYpos 2
  have hKY : K / Y ^ 2 < 1 := by
    rw [div_lt_one hYsq]
    exact hY2
  exact lt_of_le_of_lt hfinal hKY

/-! ## 6. The payoff: `HT05Inputs` from the invertibility of the averaged resolvent -/

/-- **`HT05Inputs` from the invertibility inputs.**

The self-energy bound, the operator resolvent norm bound and the physical-branch identification are
combined into the two conjuncts of `HT05Inputs`, with the explicit constants
`Cst = max 1 (max C_A (card d * C_A))`, `C_A = 4 (card d)² (∑ frob(A i)²)² C_inv`.

The invertibility hypotheses are uniform in `N` because the two conjuncts of `HT05Inputs` are
`∀ᶠ N in atTop` statements. -/
theorem HT05Inputs_of_invertible (N : ℕ) (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    (hA₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian) {Cinv : ℝ} (hCinv : 0 ≤ Cinv)
    (hminv : ∀ (n : ℕ), 0 < n → ∀ z : ℂ, 0 < z.im →
      frob ((gueResolventMean (N := n) A₀ A z)⁻¹) ≤ Cinv * (z.im)⁻¹)
    (hm : ∀ (n : ℕ), 0 < n → ∀ z : ℂ, 0 < z.im →
      gueResolventMean (N := n) A₀ A z * (gueResolventMean (N := n) A₀ A z)⁻¹ = 1)
    (hmL : ∀ (n : ℕ), 0 < n → ∀ z : ℂ, 0 < z.im →
      (gueResolventMean (N := n) A₀ A z)⁻¹ * gueResolventMean (N := n) A₀ A z = 1)
    (hmunit : ∀ (n : ℕ), 0 < n → ∀ z : ℂ, 0 < z.im →
      IsUnit (gueResolventMean (N := n) A₀ A z))
    {η₀ : ℝ} (hη₀ : 2 < η₀) :
    HT05Inputs N A₀ A η₀
      (max 1 (max (ht05EselfEnergyConst (ι := ι) (d := d) Cinv A)
        ((Fintype.card d : ℝ) * ht05EselfEnergyConst (ι := ι) (d := d) Cinv A))) := by
  set CA : ℝ := ht05EselfEnergyConst (ι := ι) (d := d) Cinv A with hCAdef
  set Cst : ℝ := max 1 (max CA ((Fintype.card d : ℝ) * CA)) with hCstdef
  have hCstpos : 0 < Cst := lt_of_lt_of_le one_pos (le_max_left _ _)
  have hcardCA : (Fintype.card d : ℝ) * CA ≤ Cst :=
    le_trans (le_max_right CA _) (le_max_right 1 _)
  have hDpos : ∀ (n : ℕ), 0 < n → 0 < 2 * Cst / (n : ℝ) ^ 2 := by
    intro n hn
    have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    positivity
  refine ⟨Filter.eventually_atTop.mpr ⟨1, fun n hn z hz _hlt => ?_⟩,
    Filter.eventually_atTop.mpr ⟨1, fun n hn z hz _hlt hsmall => ?_⟩⟩
  · have hn0 : 0 < n := hn
    have hfr := frob_selfEnergy_sub_smul_one_le_const (N := n) A₀ A hA₀ hA hCinv
      (fun w hw => hminv n hn0 w hw) (fun w hw => hm n hn0 w hw)
      (fun w hw => hmL n hn0 w hw) hn0 z hz
    refine hfr.trans ?_
    refine div_le_div_of_nonneg_right ?_ (by positivity)
    refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_pos_of_pos hz _).le
    refine le_trans ?_ (le_max_right (1 : ℝ) (max CA ((Fintype.card d : ℝ) * CA)))
    simpa only [hCAdef] using le_max_left CA ((Fintype.card d : ℝ) * CA)
  · have hn0 : 0 < n := hn
    have hr : ∀ w : ℂ, (2 * Cst / (n : ℝ) ^ 2) ^ ((1 : ℝ) / 6) < w.im →
        Cst * w.im ^ (-(6 : ℝ)) / (n : ℝ) ^ 2 < 1 / 2 :=
      fun w hw => ht05E_threshold_small hn0 hCstpos hw
    have hrpos : 0 < (2 * Cst / (n : ℝ) ^ 2) ^ ((1 : ℝ) / 6) :=
      Real.rpow_pos_of_pos (hDpos n hn0) _
    have hzr : (2 * Cst / (n : ℝ) ^ 2) ^ ((1 : ℝ) / 6) < z.im :=
      ht05E_lt_threshold_of_small hn0 hCstpos hz hsmall
    obtain ⟨z₀, hz₀, hsmall₀⟩ := exists_small_point A₀ A hA₀ hA hn0 hCinv
      (by simpa only [hCAdef, hCstdef] using hcardCA)
      hrpos hr (fun w hw => hminv n hn0 w hw) (fun w hw => hm n hn0 w hw)
      (fun w hw => hmL n hn0 w hw)
    have heq := gueResolventMean_eq_operatorMatrixArgumentCauchy_of_small_point A₀ A hA₀ hA hn0
      hCinv (fun w hw => hminv n hn0 w hw) (fun w hw => hm n hn0 w hw)
      (fun w hw => hmL n hn0 w hw) (fun w hw => hmunit n hn0 w hw)
      (by simpa only [hCAdef, hCstdef] using hcardCA) hrpos hr z₀ hz₀ hsmall₀
    refine ⟨heq (x := z) (by simpa using hzr), ?_, ?_⟩
    · exact isUnit_operatorMatrixDifference_selfEnergy A₀ A hA₀ hA hCinv hCstpos.le
        (by simpa only [hCAdef, hCstdef] using hcardCA)
        (fun w hw => hminv n hn0 w hw) (fun w hw => hm n hn0 w hw)
        (fun w hw => hmL n hn0 w hw) hn0 hz hsmall
    · refine norm_operatorMatrixArgumentResolvent_selfEnergy_le A₀ A hA₀ hA
        (CA := CA) (Cst := Cst) ?_ (by simpa only [hCAdef, hCstdef] using hcardCA) hz hsmall
      intro w hw
      have hfr := frob_selfEnergy_sub_smul_one_le_const (N := n) A₀ A hA₀ hA hCinv
        (fun v hv => hminv n hn0 v hv) (fun v hv => hm n hn0 v hv)
        (fun v hv => hmL n hn0 v hv) hn0 w hw
      refine hfr.trans ?_
      refine div_le_div_of_nonneg_right ?_ (by positivity)
      exact mul_le_mul_of_nonneg_right (le_of_eq hCAdef.symm)
        (Real.rpow_pos_of_pos hw _).le


/-- **The invertibility input for a fixed Hermitian pencil**, uniformly in `N`.

This is the exact input produced by `StrongConvergence/HT05Invertibility.lean`: invertibility of the
finite-`N` averaged resolvent, an explicit inverse bound `frob m⁻¹ ≤ C_inv (im z)⁻¹`, and the two
Dyson identities (the `m⁻¹ * m = 1` direction is the one used by the harness). -/
def HT05InvertibilityInput (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ) (Cinv : ℝ) : Prop :=
  (∀ (n : ℕ), 0 < n → ∀ z : ℂ, 0 < z.im →
    frob ((gueResolventMean (N := n) A₀ A z)⁻¹) ≤ Cinv * (z.im)⁻¹)
  ∧ (∀ (n : ℕ), 0 < n → ∀ z : ℂ, 0 < z.im →
    gueResolventMean (N := n) A₀ A z * (gueResolventMean (N := n) A₀ A z)⁻¹ = 1)
  ∧ (∀ (n : ℕ), 0 < n → ∀ z : ℂ, 0 < z.im →
    (gueResolventMean (N := n) A₀ A z)⁻¹ * gueResolventMean (N := n) A₀ A z = 1)
  ∧ (∀ (n : ℕ), 0 < n → ∀ z : ℂ, 0 < z.im → IsUnit (gueResolventMean (N := n) A₀ A z))

/-- **`HT05Inputs` from the bundled invertibility input.** -/
theorem HT05Inputs_of_invertibilityInput (N : ℕ) (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    (hA₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian) {Cinv : ℝ} (hCinv : 0 ≤ Cinv)
    (hinv : HT05InvertibilityInput A₀ A Cinv) {η₀ : ℝ} (hη₀ : 2 < η₀) :
    HT05Inputs N A₀ A η₀
      (max 1 (max (ht05EselfEnergyConst (ι := ι) (d := d) Cinv A)
        ((Fintype.card d : ℝ) * ht05EselfEnergyConst (ι := ι) (d := d) Cinv A))) :=
  HT05Inputs_of_invertible N A₀ A hA₀ hA hCinv hinv.1 hinv.2.1 hinv.2.2.1 hinv.2.2.2 hη₀

/-- **FINAL WIRING — the project target from the invertibility of the averaged resolvent.**

For every matrix pencil, the invertibility input (`IsUnit m`, `frob m⁻¹ ≤ C_inv / im z`, the Dyson
identities) gives `HT05Inputs`, and `GUEStrongConvergenceStatement_of_HT05Inputs` converts the
per-pencil inputs into the project target. -/
theorem GUEStrongConvergenceStatement_of_invertible (r : ℕ)
    (h : ∀ (k : ℕ) (F : RatPolyIdx r (k + 1)) (z : ℝ), ∃ Cinv : ℝ,
      0 ≤ Cinv ∧ HT05InvertibilityInput (pencilConstCoeff k F z) (pencilDirCoeff k F) Cinv) :
    GUEStrongConvergenceStatement r := by
  refine GUEStrongConvergenceStatement_of_HT05Inputs r (fun k F z => ?_)
  obtain ⟨Cinv, hCinv, hinv⟩ := h k F z
  refine ⟨3, max 1 (max (ht05EselfEnergyConst (ι := Fin r) (d := Fin (pencilCoeffDim k F)) Cinv
      (pencilDirCoeff k F))
      ((Fintype.card (Fin (pencilCoeffDim k F)) : ℝ) *
        ht05EselfEnergyConst (ι := Fin r) (d := Fin (pencilCoeffDim k F)) Cinv
          (pencilDirCoeff k F))), by norm_num, ?_, ?_⟩
  · exact le_trans (by norm_num) (le_max_left (1 : ℝ) _)
  · exact HT05Inputs_of_invertibilityInput (pencilCoeffDim k F) (pencilConstCoeff k F z)
      (pencilDirCoeff k F) (pencilConstCoeff_isHermitian k F z) (pencilDirCoeff_isHermitian k F)
      hCinv hinv (by norm_num)


/-! ## 7. The weighted interface `HT05Inputs'`

Worker D's unconditional bounds carry a `‖z‖²` factor, and this factor is genuine:
`selfEnergy − z • 1 = −(meanCentredDefect) * m⁻¹` with `frob (meanCentredDefect) = O(N⁻² (im z)⁻⁴)`
and `frob (m⁻¹) ≳ ‖z‖`, so the unweighted `HT05Final.HT05Inputs` is false for large `|Re z|`.
The correct statement carries the weight `(1 + ‖z‖)²` in both conjuncts.  The endgame
(`WeightedStripBoundProven A₀ A η₀ K C_s`) already allows a polynomial weight `(K + ‖z‖)²`, so the
weighted inputs still give the honest weighted strip bound with `K := 1`.

Quantifier order: both conjuncts are `∀ᶠ N, ∀ z`.  Under the weighted split this is sound: the good
branch is only invoked at points where the *weighted* good-region inequality holds, and every point
with large `|Re z|` satisfies the complement `1/2 ≤ Cst (1+‖z‖)² (im z)⁻⁶ / N²` and is handled by the
trivial bound in the bad branch (this is where the large-`|Re z|` region is absorbed). -/

/-- **The weighted HT05 inputs.**  Same two conjuncts as `HT05Final.HT05Inputs`, with the weight
`(1 + ‖z‖)²` on both the self-energy bound and the good-region smallness condition. -/
def HT05Inputs' (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ) (η₀ Cst : ℝ) : Prop :=
  (∀ᶠ N : ℕ in Filter.atTop, ∀ z : ℂ, 0 < z.im → |z.im| < η₀ →
      frob (selfEnergy (N := N) A₀ A z - z • (1 : Matrix d d ℂ)) ≤
        Cst * (1 + ‖z‖) ^ 2 * z.im ^ (-(5 : ℝ)) / (N : ℝ) ^ 2)
  ∧ (∀ᶠ N : ℕ in Filter.atTop, ∀ z : ℂ, 0 < z.im → |z.im| < η₀ →
      Cst * (1 + ‖z‖) ^ 2 * z.im ^ (-(6 : ℝ)) / (N : ℝ) ^ 2 < 1 / 2 →
      gueResolventMean (N := N) A₀ A z =
          operatorMatrixArgumentCauchy A (selfEnergy (N := N) A₀ A z - A₀) ∧
        IsUnit (operatorMatrixDifference A (selfEnergy (N := N) A₀ A z - A₀)) ∧
        ‖CStarMatrix.ofMatrix
          (operatorMatrixArgumentResolvent A (selfEnergy (N := N) A₀ A z - A₀))‖ ≤ 2 / z.im)

/-- **Weighted good-region comparison**: the unweighted comparison at the frozen constant
`Cst (1 + ‖z‖)²`. -/
theorem frob_mean_sub_limit_le_good_weighted (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    (hA₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian) {N : ℕ} {Λ : Matrix d d ℂ}
    {Cst : ℝ} (hCst : 0 ≤ Cst) {z : ℂ} (hz : 0 < z.im) (hN : 0 < N)
    (hΛ : frob (Λ - z • (1 : Matrix d d ℂ)) ≤
      Cst * (1 + ‖z‖) ^ 2 * z.im ^ (-(5 : ℝ)) / (N : ℝ) ^ 2)
    (hunit : IsUnit (operatorMatrixDifference A (Λ - A₀)))
    (hn : ‖CStarMatrix.ofMatrix (operatorMatrixArgumentResolvent A (Λ - A₀))‖ ≤ 2 / z.im)
    (hident : gueResolventMean (N := N) A₀ A z = operatorMatrixArgumentCauchy A (Λ - A₀)) :
    frob (gueResolventMean (N := N) A₀ A z - operatorMatrixPencilCauchy A₀ A z) ≤
      4 * (Fintype.card d : ℝ) ^ 2 * Cst * (1 + ‖z‖) ^ 2 * z.im ^ (-(7 : ℝ)) /
        (N : ℝ) ^ 2 := by
  have hCstz : 0 ≤ Cst * (1 + ‖z‖) ^ 2 := mul_nonneg hCst (sq_nonneg _)
  have h := frob_mean_sub_limit_le_good A₀ A hA₀ hA (Cst := Cst * (1 + ‖z‖) ^ 2) hCstz hz hN
    hΛ hunit hn hident
  refine h.trans (le_of_eq ?_)
  ring

/-- **Weighted bad-region comparison**: off the weighted good region the trivial deterministic
bound gives the same weighted rate. -/
theorem frob_mean_sub_limit_le_bad_weighted [Nonempty d] (A₀ : Matrix d d ℂ)
    (A : ι → Matrix d d ℂ) (hA₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian) {N : ℕ}
    {Cst : ℝ} (hCst : 0 ≤ Cst) {z : ℂ} (hz : 0 < z.im) (hN : 0 < N)
    (hbad : 1 / 2 ≤ Cst * (1 + ‖z‖) ^ 2 * z.im ^ (-(6 : ℝ)) / (N : ℝ) ^ 2) :
    frob (gueResolventMean (N := N) A₀ A z - operatorMatrixPencilCauchy A₀ A z) ≤
      4 * (Fintype.card d : ℝ) ^ 2 * Cst * (1 + ‖z‖) ^ 2 * z.im ^ (-(7 : ℝ)) /
        (N : ℝ) ^ 2 := by
  refine (frob_mean_sub_limit_trivial_le A₀ A hA₀ hA hz hN).trans ?_
  have hcard1 : (1 : ℝ) ≤ (Fintype.card d : ℝ) := by
    exact_mod_cast Fintype.card_pos_iff.mpr ‹Nonempty d›
  have hkey : 1 ≤ 2 * (Fintype.card d : ℝ) * Cst * (1 + ‖z‖) ^ 2 *
      z.im ^ (-(6 : ℝ)) / (N : ℝ) ^ 2 := by
    have heq : 2 * (Fintype.card d : ℝ) *
          (Cst * (1 + ‖z‖) ^ 2 * z.im ^ (-(6 : ℝ)) / (N : ℝ) ^ 2) =
        2 * (Fintype.card d : ℝ) * Cst * (1 + ‖z‖) ^ 2 * z.im ^ (-(6 : ℝ)) /
          (N : ℝ) ^ 2 := by ring
    rw [← heq]
    nlinarith [hbad, hcard1]
  calc 2 * (Fintype.card d : ℝ) * (z.im)⁻¹
      = (2 * (Fintype.card d : ℝ) * (z.im)⁻¹) * 1 := by ring
    _ ≤ (2 * (Fintype.card d : ℝ) * (z.im)⁻¹) *
          (2 * (Fintype.card d : ℝ) * Cst * (1 + ‖z‖) ^ 2 * z.im ^ (-(6 : ℝ)) /
            (N : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_left hkey (by positivity)
    _ = 4 * (Fintype.card d : ℝ) ^ 2 * Cst * (1 + ‖z‖) ^ 2 * z.im ^ (-(7 : ℝ)) /
          (N : ℝ) ^ 2 := by
        rw [rpow_neg_seven_eq_six_mul_inv hz]
        ring

/-- **Weighted uniform comparison** on the strip `{0 < im z, |im z| < η₀}`. -/
theorem frob_mean_sub_limit_le_uniform_weighted [Nonempty d] (A₀ : Matrix d d ℂ)
    (A : ι → Matrix d d ℂ) (hA₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian) {N : ℕ}
    (hN : 0 < N) {η₀ Cst : ℝ} (hCst : 0 ≤ Cst) (Λ : ℂ → Matrix d d ℂ)
    (hΛ : ∀ z : ℂ, 0 < z.im → |z.im| < η₀ →
      frob (Λ z - z • (1 : Matrix d d ℂ)) ≤
        Cst * (1 + ‖z‖) ^ 2 * z.im ^ (-(5 : ℝ)) / (N : ℝ) ^ 2)
    (hgood : ∀ z : ℂ, 0 < z.im → |z.im| < η₀ →
      Cst * (1 + ‖z‖) ^ 2 * z.im ^ (-(6 : ℝ)) / (N : ℝ) ^ 2 < 1 / 2 →
      gueResolventMean (N := N) A₀ A z = operatorMatrixArgumentCauchy A (Λ z - A₀) ∧
        IsUnit (operatorMatrixDifference A (Λ z - A₀)) ∧
        ‖CStarMatrix.ofMatrix (operatorMatrixArgumentResolvent A (Λ z - A₀))‖ ≤ 2 / z.im)
    {z : ℂ} (hz : 0 < z.im) (hlt : |z.im| < η₀) :
    frob (gueResolventMean (N := N) A₀ A z - operatorMatrixPencilCauchy A₀ A z) ≤
      4 * (Fintype.card d : ℝ) ^ 2 * Cst * (1 + ‖z‖) ^ 2 * z.im ^ (-(7 : ℝ)) /
        (N : ℝ) ^ 2 := by
  by_cases hgc : Cst * (1 + ‖z‖) ^ 2 * z.im ^ (-(6 : ℝ)) / (N : ℝ) ^ 2 < 1 / 2
  · obtain ⟨hident, hunit, hn⟩ := hgood z hz hlt hgc
    exact frob_mean_sub_limit_le_good_weighted A₀ A hA₀ hA hCst hz hN (hΛ z hz hlt)
      hunit hn hident
  · exact frob_mean_sub_limit_le_bad_weighted A₀ A hA₀ hA hCst hz hN (le_of_not_gt hgc)

/-- **The honest weighted strip bound from the weighted inputs** (both half-planes; the lower
half-plane uses the unconditional conjugation symmetry of the limit branch). -/
theorem weightedStripBoundProven_of_HT05Inputs' [Nonempty d] (A₀ : Matrix d d ℂ)
    (A : ι → Matrix d d ℂ) (hA₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian)
    {η₀ Cst : ℝ} (hCst : 0 ≤ Cst) (hη₀ : 0 < η₀) (h : HT05Inputs' A₀ A η₀ Cst) :
    WeightedStripBoundProven A₀ A η₀ 1 (4 * (Fintype.card d : ℝ) ^ 2 * Cst) := by
  have hupper : ∀ᶠ N : ℕ in Filter.atTop, ∀ z : ℂ, 0 < z.im → |z.im| < η₀ →
      frob (gueResolventMean (N := N) A₀ A z - operatorMatrixPencilCauchy A₀ A z) ≤
        4 * (Fintype.card d : ℝ) ^ 2 * Cst * (1 + ‖z‖) ^ 2 * |z.im| ^ (-(7 : ℝ)) /
          (N : ℝ) ^ 2 := by
    filter_upwards [h.1, h.2, eventually_gt_atTop (0 : ℕ)] with N hΛN hgoodN hN z hz hlt
    have hb := frob_mean_sub_limit_le_uniform_weighted A₀ A hA₀ hA hN hCst
      (fun w => selfEnergy (N := N) A₀ A w) hΛN hgoodN hz hlt
    simpa only [abs_of_pos hz] using hb
  have hlower : ∀ᶠ N : ℕ in Filter.atTop, ∀ z : ℂ, z.im < 0 → |z.im| < η₀ →
      frob (gueResolventMean (N := N) A₀ A z - operatorMatrixPencilCauchy A₀ A z) ≤
        4 * (Fintype.card d : ℝ) ^ 2 * Cst * (1 + ‖z‖) ^ 2 * |z.im| ^ (-(7 : ℝ)) /
          (N : ℝ) ^ 2 := by
    filter_upwards [hupper] with N hN z hzneg hlt
    have hzpos : 0 < (star z).im := by simpa [Complex.star_def] using hzneg
    have hlt' : |(star z).im| < η₀ := by simpa [Complex.star_def] using hlt
    have hb := hN (star z) hzpos hlt'
    rw [frob_gueResolventMean_sub_limit_star_of_limit A₀ A hA₀ hA
      (operatorMatrixPencilCauchy_star_unconditional A₀ A hA₀ hA) z] at hb
    simpa [Complex.star_def] using hb
  filter_upwards [hupper, hlower] with N hn hl
  intro z hz hlt
  rcases lt_trichotomy z.im 0 with h | h | h
  · exact hl z h hlt
  · exact absurd h hz
  · exact hn z h hlt


/-! ## 8. The weighted endgame wiring -/

/-- **The pencil strip field from the weighted inputs.** -/
theorem weightedStripDataAtRepair_of_HT05Inputs' (r k : ℕ) (F : RatPolyIdx r (k + 1))
    {z ε : ℝ} (hε : 0 < ε) {η₀ Cst : ℝ} (hη₀ : 2 < η₀) (hCst : 0 ≤ Cst)
    (h : HT05Inputs' (pencilConstCoeff k F z) (pencilDirCoeff k F) η₀ Cst) :
    WeightedStripDataAtRepair r k F z ε := by
  haveI : Nonempty (Fin (pencilCoeffDim k F)) := ⟨⟨0, pencilCoeffDim_pos r k F⟩⟩
  exact weightedStripDataAtRepair_of_stripBound (r := r) (k := k) (F := F) (z := z) (ε := ε)
    hε hη₀ (mul_nonneg (by norm_num) hCst)
    (weightedStripBoundProven_of_HT05Inputs' (pencilConstCoeff k F z) (pencilDirCoeff k F)
      (pencilConstCoeff_isHermitian k F z) (pencilDirCoeff_isHermitian k F)
      hCst (by linarith) h)

/-- **The corrected two-field bundle from the per-pencil weighted inputs.** -/
theorem weightedStripInputsRepair_of_HT05Inputs' (r : ℕ)
    (h : ∀ (k : ℕ) (F : RatPolyIdx r (k + 1)) (z : ℝ), ∃ η₀ Cst : ℝ,
      2 < η₀ ∧ 0 ≤ Cst ∧
        HT05Inputs' (pencilConstCoeff k F z) (pencilDirCoeff k F) η₀ Cst) :
    WeightedStripInputsRepair r := by
  refine weightedStripInputsRepair_of_pencilField r ?_
  intro k F z ε hε
  obtain ⟨η₀, Cst, hη₀, hCst, hin⟩ := h k F z
  exact weightedStripDataAtRepair_of_HT05Inputs' r k F hε hη₀ hCst hin

/-- **The project target from the per-pencil weighted inputs.** -/
theorem GUEStrongConvergenceStatement_of_HT05Inputs' (r : ℕ)
    (h : ∀ (k : ℕ) (F : RatPolyIdx r (k + 1)) (z : ℝ), ∃ η₀ Cst : ℝ,
      2 < η₀ ∧ 0 ≤ Cst ∧
        HT05Inputs' (pencilConstCoeff k F z) (pencilDirCoeff k F) η₀ Cst) :
    GUEStrongConvergenceStatement r :=
  GUEStrongConvergenceStatement_of_weightedStripInputsRepair
    (weightedStripInputsRepair_of_HT05Inputs' r h)

end

end GUEStrongConvergence
