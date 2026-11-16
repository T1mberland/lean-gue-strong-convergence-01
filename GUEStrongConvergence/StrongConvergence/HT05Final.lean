/-
# HT05 final assembly: from the finite-`N` comparison inputs to the project target

This file wires the good/bad-region comparison (`StrongConvergence/HT05Comparison.lean`, with the
lower half-plane supplied unconditionally by `StrongConvergence/HT05LimitConjugation.lean`)
into the already verified endgame of `Probability/ScalarPencilStrip.lean` and
`StrongConvergence/CorrectedEndgame.lean`.

## Contents

1. `frob_selfEnergy_sub_smul_one_le_of_inv` — **the self-energy bound**, derived from the exact
   factorization `selfEnergy − z • 1 = −(meanCentredDefect) * m⁻¹`
   (`HT05FiniteMean.selfEnergy_sub_smul_one`), the sharp defect bound
   `frob_meanCentredDefect_le` (`≤ 4 (card d)² (∑ frob(A i)²)² N⁻² |Im z|⁻⁴`) and an explicit
   inverse bound `frob m⁻¹ ≤ C_inv |Im z|⁻¹`:
   `frob (selfEnergy − z • 1) ≤ 4 (card d)² (∑ frob(A i)²)² C_inv N⁻² |Im z|⁻⁵`.

2. `HT05Inputs N A₀ A η₀ Cst` — the exact remaining inputs at a fixed Hermitian pencil: the
   self-energy bound and Worker B's good-region identification together with the operator
   resolvent norm bound `‖res(Λ − A₀)‖ ≤ 2 / Im z`.

3. `weightedStripBoundProven_of_HT05Inputs` — those inputs give the honest weighted strip bound
   `frob (g_N − g) ≤ 4 (card d)² Cst (1 + ‖z‖)² |Im z|⁻⁷ / N²`.

4. `GUEStrongConvergenceStatement_of_HT05Inputs` — the final assembly: for every `r`, the project
   target follows from the per-pencil HT05 inputs.

No `sorry`, no new axioms.
-/
import GUEStrongConvergence.StrongConvergence.HT05LimitConjugation
import GUEStrongConvergence.StrongConvergence.HT05FiniteMean
import GUEStrongConvergence.Probability.ScalarPencilStrip
import GUEStrongConvergence.StrongConvergence.CorrectedEndgame

open MeasureTheory ProbabilityTheory Matrix Filter
open FreeProbability FreeProbability.Fock
open scoped ENNReal NNReal Topology BigOperators

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 8000000

namespace GUEStrongConvergence

variable {ι d : Type*} [Fintype ι] [Fintype d] [DecidableEq d] [DecidableEq ι]

noncomputable local instance ht05CFinalPartialOrder :
    PartialOrder (WordSpace ι →L[ℂ] WordSpace ι) :=
  CStarAlgebra.spectralOrder _
noncomputable local instance ht05CFinalStarOrderedRing :
    StarOrderedRing (WordSpace ι →L[ℂ] WordSpace ι) :=
  CStarAlgebra.spectralOrderedRing _

/-! ## 1. The self-energy bound -/

/-- `(y⁻¹)^4 * y⁻¹ = y^(-5)` for `y > 0`. -/
theorem inv_pow_four_mul_inv_eq_rpow_neg_five {y : ℝ} (hy : 0 < y) :
    (y⁻¹) ^ 4 * y⁻¹ = y ^ (-(5 : ℝ)) := by
  have h5 : y ^ (-(5 : ℝ)) = ((y ^ 5 : ℝ))⁻¹ := by
    rw [Real.rpow_neg hy.le, Real.rpow_ofNat]
  rw [h5, inv_pow]
  have hne : y ≠ 0 := hy.ne'
  field_simp

/-- **The self-energy is `O(N⁻² |Im z|⁻⁵)`.**  The exact factorization
`selfEnergy − z•1 = −D m⁻¹`, the sharp defect bound and an explicit inverse bound
`frob m⁻¹ ≤ C_inv |Im z|⁻¹` give
`frob (selfEnergy − z • 1) ≤ 4 (card d)² (∑ frob(A i)²)² C_inv N⁻² |Im z|⁻⁵`. -/
theorem frob_selfEnergy_sub_smul_one_le_of_inv {N : ℕ} (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    (hA₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian) {z : ℂ} (hz : 0 < z.im)
    {Cinv : ℝ} (hCinv : 0 ≤ Cinv)
    (hminv : frob ((gueResolventMean (N := N) A₀ A z)⁻¹) ≤ Cinv * (z.im)⁻¹)
    (hm : gueResolventMean (N := N) A₀ A z * (gueResolventMean (N := N) A₀ A z)⁻¹ = 1)
    (hmL : (gueResolventMean (N := N) A₀ A z)⁻¹ * gueResolventMean (N := N) A₀ A z = 1)
    (hN : 0 < N) :
    frob (selfEnergy (N := N) A₀ A z - z • (1 : Matrix d d ℂ)) ≤
      4 * (Fintype.card d : ℝ) ^ 2 * (∑ i, (frob (A i)) ^ 2) ^ 2 * Cinv *
        z.im ^ (-(5 : ℝ)) / (N : ℝ) ^ 2 := by
  classical
  have hfac := selfEnergy_sub_smul_one (N := N) A₀ A hA₀ hA z hz.ne'
    (by exact_mod_cast hN.ne') hm hmL
  rw [hfac]
  have hD := frob_meanCentredDefect_le (N := N) A₀ A hA₀ hA z hz hN
  have hminv0 : 0 ≤ frob ((gueResolventMean (N := N) A₀ A z)⁻¹) := frob_nonneg _
  have hmul : frob (-(meanCentredDefect (N := N) A₀ A z) *
        (gueResolventMean (N := N) A₀ A z)⁻¹) ≤
      frob (meanCentredDefect (N := N) A₀ A z) *
        frob ((gueResolventMean (N := N) A₀ A z)⁻¹) := by
    rw [neg_mul, frob_neg]
    exact frob_mul_le _ _
  have hS0 : (0 : ℝ) ≤ (∑ i, (frob (A i)) ^ 2) ^ 2 := sq_nonneg _
  have hcoef0 : (0 : ℝ) ≤ 4 * (Fintype.card d : ℝ) ^ 2 * (∑ i, (frob (A i)) ^ 2) ^ 2 *
      ((N : ℝ)⁻¹) ^ 2 * ((z.im)⁻¹) ^ 4 := by
    have h4 : (0 : ℝ) ≤ 4 * (Fintype.card d : ℝ) ^ 2 := by positivity
    have h3 : (0 : ℝ) ≤ ((N : ℝ)⁻¹) ^ 2 := sq_nonneg _
    have h2 : (0 : ℝ) ≤ ((z.im)⁻¹) ^ 4 := by positivity
    exact mul_nonneg (mul_nonneg (mul_nonneg h4 hS0) h3) h2
  have hstep : frob (meanCentredDefect (N := N) A₀ A z) *
        frob ((gueResolventMean (N := N) A₀ A z)⁻¹) ≤
      (4 * (Fintype.card d : ℝ) ^ 2 * (∑ i, (frob (A i)) ^ 2) ^ 2 *
          ((N : ℝ)⁻¹) ^ 2 * ((z.im)⁻¹) ^ 4) * (Cinv * (z.im)⁻¹) :=
    mul_le_mul hD hminv hminv0 hcoef0
  refine (hmul.trans hstep).trans (le_of_eq ?_)
  have hy : 0 < z.im := hz
  have hNinv : ((N : ℝ)⁻¹) ^ 2 = ((N : ℝ) ^ 2)⁻¹ := inv_pow _ 2
  rw [div_eq_mul_inv, hNinv, ← inv_pow_four_mul_inv_eq_rpow_neg_five hy]
  ring

/-! ## 2. The HT05 input bundle at a fixed Hermitian pencil -/

/-- **The two remaining HT05 inputs** at a fixed Hermitian pencil.

* the first conjunct is the quantitative self-energy estimate;
* the second conjunct is the good-region identification of the finite-`N` mean with the free
  matrix-argument Cauchy transform at the corrected argument, together with the operator
  resolvent norm bound `‖res(Λ − A₀)‖ ≤ 2 / Im z`. -/
def HT05Inputs (N : ℕ) (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ) (η₀ Cst : ℝ) : Prop :=
  (∀ᶠ N : ℕ in Filter.atTop, ∀ z : ℂ, 0 < z.im → |z.im| < η₀ →
      frob (selfEnergy (N := N) A₀ A z - z • (1 : Matrix d d ℂ)) ≤
        Cst * z.im ^ (-(5 : ℝ)) / (N : ℝ) ^ 2)
  ∧ (∀ᶠ N : ℕ in Filter.atTop, ∀ z : ℂ, 0 < z.im → |z.im| < η₀ →
      Cst * z.im ^ (-(6 : ℝ)) / (N : ℝ) ^ 2 < 1 / 2 →
      gueResolventMean (N := N) A₀ A z =
          operatorMatrixArgumentCauchy A (selfEnergy (N := N) A₀ A z - A₀) ∧
        IsUnit (operatorMatrixDifference A (selfEnergy (N := N) A₀ A z - A₀)) ∧
        ‖CStarMatrix.ofMatrix
          (operatorMatrixArgumentResolvent A (selfEnergy (N := N) A₀ A z - A₀))‖ ≤ 2 / z.im)

/-- **The honest weighted strip bound from the HT05 inputs** (both half-planes, no
limit-side conjugation hypothesis: that is `HT05LimitConjugation`). -/
theorem weightedStripBoundProven_of_HT05Inputs {N : ℕ} [Nonempty d] (A₀ : Matrix d d ℂ)
    (A : ι → Matrix d d ℂ) (hA₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian)
    {η₀ Cst : ℝ} (hCst : 0 ≤ Cst) (hη₀ : 0 < η₀)
    (h : HT05Inputs N A₀ A η₀ Cst) :
    WeightedStripBoundProven A₀ A η₀ 1 (4 * (Fintype.card d : ℝ) ^ 2 * Cst) :=
  weightedStripBoundProven_of_comparison_unconditional A₀ A hA₀ hA hCst hη₀
    (fun N z => selfEnergy (N := N) A₀ A z) h.1 h.2

/-! ## 3. The per-pencil strip data and the final assembly -/

/-- **The pencil field of the corrected bundle from the HT05 inputs.** -/
theorem weightedStripDataAtRepair_of_HT05Inputs {N : ℕ} (r k : ℕ) (F : RatPolyIdx r (k + 1))
    {z ε : ℝ} (hε : 0 < ε) {η₀ Cst : ℝ} (hη₀ : 2 < η₀) (hCst : 0 ≤ Cst)
    (h : HT05Inputs N (pencilConstCoeff k F z) (pencilDirCoeff k F) η₀ Cst) :
    WeightedStripDataAtRepair r k F z ε := by
  haveI : Nonempty (Fin (pencilCoeffDim k F)) := ⟨⟨0, pencilCoeffDim_pos r k F⟩⟩
  exact weightedStripDataAtRepair_of_stripBound (r := r) (k := k) (F := F) (z := z) (ε := ε)
    hε hη₀ (by positivity)
    (weightedStripBoundProven_of_HT05Inputs (pencilConstCoeff k F z) (pencilDirCoeff k F)
      (pencilConstCoeff_isHermitian k F z) (pencilDirCoeff_isHermitian k F)
      hCst (by linarith) h)

/-- **The corrected two-field bundle from the per-pencil HT05 inputs.**

The scalar (`d = 1`) field is already unconditional
(`scalarField_weightedStripInputsRepair`); only the matrix pencil field needs the HT05 inputs. -/
theorem weightedStripInputsRepair_of_HT05Inputs (r : ℕ)
    (h : ∀ (k : ℕ) (F : RatPolyIdx r (k + 1)) (z : ℝ), ∃ η₀ Cst : ℝ,
      2 < η₀ ∧ 0 ≤ Cst ∧
        HT05Inputs (pencilCoeffDim k F) (pencilConstCoeff k F z) (pencilDirCoeff k F) η₀ Cst) :
    WeightedStripInputsRepair r := by
  refine weightedStripInputsRepair_of_pencilField r ?_
  intro k F z ε hε
  obtain ⟨η₀, Cst, hη₀, hCst, hin⟩ := h k F z
  exact weightedStripDataAtRepair_of_HT05Inputs r k F hε hη₀ hCst hin

/-- **FINAL ASSEMBLY — the project target from the per-pencil HT05 inputs.**

The chain is `HT05Comparison` (good/bad region, with the lower half-plane from
`HT05LimitConjugation`) → `WeightedStripBoundProven` → `weightedStripDataAtRepair_of_stripBound`
→ `weightedStripInputsRepair_of_pencilField` →
`GUEStrongConvergenceStatement_of_weightedStripInputsRepair`. -/
theorem GUEStrongConvergenceStatement_of_HT05Inputs (r : ℕ)
    (h : ∀ (k : ℕ) (F : RatPolyIdx r (k + 1)) (z : ℝ), ∃ η₀ Cst : ℝ,
      2 < η₀ ∧ 0 ≤ Cst ∧
        HT05Inputs (pencilCoeffDim k F) (pencilConstCoeff k F z) (pencilDirCoeff k F) η₀ Cst) :
    GUEStrongConvergenceStatement r :=
  GUEStrongConvergenceStatement_of_weightedStripInputsRepair
    (weightedStripInputsRepair_of_HT05Inputs r h)

end GUEStrongConvergence
