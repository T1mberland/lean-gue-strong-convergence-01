/-
# The unconditional `hV` field of `PencilLemmaSResidual` for a smooth cutoff

`Probability/FlatContraction.lean` proves the flattened Lemma V with the direction contraction
*discharged*, but it still takes the six analytic inputs of `flatLemmaV` as hypotheses:

* `hF` — `MemLp 2` of the block statistic `flatStatBlk` on the Gaussian block;
* `hDmem` — `MemLp 2` of the cfc trace derivatives `flatDerivStat · p`;
* `hpoly` — polynomial growth along each Gaussian coordinate;
* `hint` — integrability of `‖f'(fl ℒ_z)‖_F²`;
* `hWint`, `hW0` — integrability and nonnegativity of the mean of `τ_N((f')²(fl ℒ_z))`.

This file discharges all six from a single smooth cutoff `IsSmoothCutoff`, as
`StrongConvergence/ScalarInclusionSmooth.lean` does for the scalar pencil, and thereby delivers
`hV` of `PencilLemmaSResidual` unconditionally.

## The estimates

With `m = pencilFlatDim r k F N` and a global bound `|f'| ≤ M` on the cutoff derivative
(`IsSmoothCutoff.exists_deriv_bound`):

* **`hF`** — `|f| ≤ 1`, so `|τ_N(f(fl ℒ_z))| ≤ 1` (`flatStatBlk_memLp`).  The block statistic
  is measurable because the flattened pencil is *continuous* in the Gaussian block
  (`continuous_flatPencilBlk`), and its cfc is measurable by `measurable_cfc_of_hermitian`.
  This is the *block* form that `flatLemmaV_hV_unconditional` consumes; its common-space
  counterpart `flatStat_memLp`/`hZ_flatStat` (on `commonGaussianMeasure`, from `|f| ≤ 1`) is
  already on main and is not needed for `hV`.
* **`hWint`** — `|(f')²| ≤ M²` (`flatStatBlk_sq_integrable`), and `hW0` is
  `integral_normTrace_cfc_nonneg`.
* **`hint`** — `‖f'(L)‖_F² ≤ card · M²` (`hsNorm_cfc_le_card_mul_sq`) together with
  measurability of `y ↦ ‖cfc (deriv f) (fl ℒ_z(y))‖_F`
  (`integrable_hsNorm_cfc_flatPencilBlk`).
* **`hDmem`** — `|τ_N(f'(L) ∂_p L)| ≤ m⁻¹ √(card · M²) √‖∂_p L‖_F` by
  `abs_inv_card_trace_mul_le` (`abs_flatDerivStat_le`), a uniform bound hence `MemLp`
  (`flatDerivStat_memLp`).
* **`hpoly`** — the same two uniform bounds, `1` for `flatStatBlk` and the constant of
  `abs_flatDerivStat_le` for `flatDerivStat`, give polynomial growth through
  `polyGrowth_of_bound'` (`polyGrowth_flatStatBlk`, `polyGrowth_flatDerivStat`).
* **`hW0`** is `hW0_flatStat` (`integral_normTrace_cfc_nonneg`), already on main.

## Main results

* `flatStatBlk_memLp`, `flatStatBlk_sq_integrable`, `integrable_hsNorm_cfc_flatPencilBlk`,
  `abs_flatDerivStat_le`, `flatDerivStat_memLp`, `polyGrowth_flatStatBlk`,
  `polyGrowth_flatDerivStat` — the six analytic inputs, unconditionally;
* **`flatLemmaV_hV_field`** — the `hV` statement with the constant
  `2 · flatContractionConst r k F / pencilVDim r k F`:
  `∀ᶠ N, Var(τ_N(f(fl ℒ_z))) ≤ 2G/pencilVDim/N² · E[τ_N((f')²(fl ℒ_z))]`;
* `PencilLemmaSResidual_of_smoothCutoff_hV` — the residual bundle `PencilLemmaSResidual` with
  its `hV` field filled in, leaving only `hM` and `hWb` explicit.

No `sorry`, no new axioms.
-/
import GUEStrongConvergence.Probability.FlatContraction
import GUEStrongConvergence.StrongConvergence.FlatSideConditions

open Filter MeasureTheory ProbabilityTheory FreeProbability FreeProbability.Fock Matrix
open scoped BigOperators ComplexOrder ENNReal NNReal Topology

namespace GUEStrongConvergence

noncomputable section

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

variable {r : ℕ}

/-! ## 1. Measurability of the flattened pencil and of the cfc statistics

The flattened pencil is *continuous* in the Gaussian block (`continuous_flatPencilBlk`), so its
entries are measurable; `measurable_cfc_of_hermitian` then gives measurability of the cfc, and
the normalized trace of a product of a measurable matrix family with the constant direction
`flatStepDir` is measurable entrywise. -/

section Measurability

/-- Entry measurability of the flattened pencil on the Gaussian block. -/
lemma measurable_flatPencilBlk_entry (k : ℕ) (F : RatPolyIdx r (k + 1)) (N : ℕ) (z : ℝ)
    (a b : Fin (pencilFlatDim r k F N)) :
    Measurable fun y : EuclideanSpace ℝ (GUECoord (Fin r) (N + 1)) =>
      flatPencilBlk r k F N z y a b :=
  ((continuous_flatPencilBlk k F N z).matrix_elem a b).measurable

/-- Measurability of the cfc of the derivative applied to the flattened pencil. -/
lemma measurable_cfc_deriv_flatPencilBlk (k : ℕ) (F : RatPolyIdx r (k + 1)) (N : ℕ) (z : ℝ)
    {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) :
    Measurable fun y : EuclideanSpace ℝ (GUECoord (Fin r) (N + 1)) =>
      cfc (deriv f) (flatPencilBlk r k F N z y) :=
  measurable_cfc_of_hermitian (fun a b => measurable_flatPencilBlk_entry k F N z a b)
    (fun y => flatPencilBlk_isHermitian k F N z y) hf.continuous_deriv_one

/-- Measurability of the Hilbert–Schmidt norm of the cfc of the derivative. -/
lemma measurable_hsNorm_cfc_flatPencilBlk (k : ℕ) (F : RatPolyIdx r (k + 1)) (N : ℕ) (z : ℝ)
    {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) :
    Measurable fun y : EuclideanSpace ℝ (GUECoord (Fin r) (N + 1)) =>
      hsNorm (cfc (deriv f) (flatPencilBlk r k F N z y)) :=
  measurable_hsNorm (fun a b =>
    measurable_pi_iff.mp
      (measurable_pi_iff.mp (measurable_cfc_deriv_flatPencilBlk k F N z hf) a) b)

/-- Measurability of the cfc trace derivative statistic `τ_N(f'(fl ℒ_z) ∂_p fl ℒ_z)`. -/
lemma measurable_flatDerivStat (k : ℕ) (F : RatPolyIdx r (k + 1)) (z : ℝ) (N : ℕ) (f : ℝ → ℝ)
    (hf : ContDiff ℝ 1 f) (p : GUECoord (Fin r) (N + 1)) :
    Measurable fun y : EuclideanSpace ℝ (GUECoord (Fin r) (N + 1)) =>
      flatDerivStat r k F z N f y p := by
  have hcfc := measurable_cfc_deriv_flatPencilBlk k F N z hf
  have hX : ∀ a b, Measurable fun y : EuclideanSpace ℝ (GUECoord (Fin r) (N + 1)) =>
      cfc (deriv f) (flatPencilBlk r k F N z y) a b :=
    fun a b => measurable_pi_iff.mp (measurable_pi_iff.mp hcfc a) b
  have hD : ∀ a b, Measurable fun _ : EuclideanSpace ℝ (GUECoord (Fin r) (N + 1)) =>
      flatStepDir r k F N z p a b := fun a b => measurable_const
  have hfun : (fun y : EuclideanSpace ℝ (GUECoord (Fin r) (N + 1)) =>
        flatDerivStat r k F z N f y p)
      = fun y => normTrace
          (cfc (deriv f) (flatPencilBlk r k F N z y) * flatStepDir r k F N z p) := rfl
  rw [hfun]
  simp only [normTrace]
  exact measurable_const.mul (measurable_trace_re (measurable_matrix_mul_entries hX hD))

end Measurability

/-! ## 2. Bounds for the cfc statistics

Both bounds use only the global derivative bound `|f'| ≤ M` of the cutoff, through
`hsNorm_cfc_le_card_mul_sq` (`‖g(L)‖_F² ≤ card · sup |g|²`) and
`abs_inv_card_trace_mul_le` (`|τ(A D)| ≤ m⁻¹ √‖A‖_F² √‖D‖_F²`). -/

section Bounds

/-- **Pointwise bound on the cfc trace derivative.**  For every Gaussian block point `y` and
coordinate `p`,

`|τ_N(f'(fl ℒ_z) ∂_p fl ℒ_z)| ≤ m⁻¹ √(card · M²) √‖∂_p fl ℒ_z‖_F`,

where `m = pencilFlatDim r k F N` and `card = m` (the card of `Fin m`). -/
lemma abs_flatDerivStat_le (k : ℕ) (F : RatPolyIdx r (k + 1)) (z : ℝ) (N : ℕ) (f : ℝ → ℝ)
    (hf : ContDiff ℝ 1 f) {M : ℝ} (hMbound : ∀ y, |deriv f y| ≤ M)
    (y : EuclideanSpace ℝ (GUECoord (Fin r) (N + 1))) (p : GUECoord (Fin r) (N + 1)) :
    |flatDerivStat r k F z N f y p|
      ≤ (pencilFlatDim r k F N : ℝ)⁻¹ *
          (Real.sqrt ((pencilFlatDim r k F N : ℝ) * M ^ 2) *
            Real.sqrt (hsNorm (flatStepDir r k F N z p))) := by
  have hL : (flatPencilBlk r k F N z y).IsHermitian := flatPencilBlk_isHermitian k F N z y
  have hh : hsNorm (cfc (deriv f) (flatPencilBlk r k F N z y))
      ≤ (pencilFlatDim r k F N : ℝ) * M ^ 2 := by
    simpa using hsNorm_cfc_le_card_mul_sq (flatPencilBlk r k F N z y) hL
      hf.continuous_deriv_one hMbound
  have h1 : flatDerivStat r k F z N f y p
      = (pencilFlatDim r k F N : ℝ)⁻¹ *
          ((cfc (deriv f) (flatPencilBlk r k F N z y) * flatStepDir r k F N z p).trace).re :=
    rfl
  rw [h1]
  have hmul := abs_inv_card_trace_mul_le (X := cfc (deriv f) (flatPencilBlk r k F N z y))
    (D := flatStepDir r k F N z p)
  simp only [Fintype.card_fin] at hmul
  refine hmul.trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg _)
  exact Real.sqrt_le_sqrt hh

/-- **Polynomial growth of the block statistic** along any Gaussian coordinate, from `|f| ≤ 1`. -/
lemma polyGrowth_flatStatBlk (k : ℕ) (F : RatPolyIdx r (k + 1)) (z : ℝ) (N : ℕ) (f : ℝ → ℝ)
    {C : ℝ} (hC : ∀ y, |f y| ≤ C) (hC0 : 0 ≤ C)
    (y : EuclideanSpace ℝ (GUECoord (Fin r) (N + 1))) (p : GUECoord (Fin r) (N + 1)) :
    PolyGrowth (fun u : ℝ => flatStatBlk r k F z N f (euclidUpdate y p u)) :=
  polyGrowth_of_bound' fun u =>
    abs_normTrace_cfc_le (flatPencilBlk_isHermitian k F N z (euclidUpdate y p u)) f hC hC0

/-- **Polynomial growth of the cfc trace derivative** along any Gaussian coordinate, from the
global derivative bound. -/
lemma polyGrowth_flatDerivStat (k : ℕ) (F : RatPolyIdx r (k + 1)) (z : ℝ) (N : ℕ) (f : ℝ → ℝ)
    (hf : ContDiff ℝ 1 f) {M : ℝ} (hMbound : ∀ y, |deriv f y| ≤ M)
    (y : EuclideanSpace ℝ (GUECoord (Fin r) (N + 1))) (p : GUECoord (Fin r) (N + 1)) :
    PolyGrowth (fun u : ℝ => flatDerivStat r k F z N f (euclidUpdate y p u) p) :=
  polyGrowth_of_bound'
    (fun u => abs_flatDerivStat_le k F z N f hf hMbound (euclidUpdate y p u) p)

end Bounds

/-! ## 3. The six analytic inputs of the unconditional flattened Lemma V -/

section Inputs

/-- **`hF`: `MemLp 2` of the block statistic** from a global bound on the cutoff. -/
lemma flatStatBlk_memLp (k : ℕ) (F : RatPolyIdx r (k + 1)) (z : ℝ) (N : ℕ)
    {f : ℝ → ℝ} (hf : Continuous f) {C : ℝ} (hC : ∀ y, |f y| ≤ C) (hC0 : 0 ≤ C) :
    MemLp (flatStatBlk r k F z N f) 2
      (stdGaussian (EuclideanSpace ℝ (GUECoord (Fin r) (N + 1)))) := by
  have hM : ∀ a b : Fin (pencilFlatDim r k F N), Measurable
      fun y : EuclideanSpace ℝ (GUECoord (Fin r) (N + 1)) => flatPencilBlk r k F N z y a b :=
    fun a b => measurable_flatPencilBlk_entry k F N z a b
  have hHerm : ∀ y : EuclideanSpace ℝ (GUECoord (Fin r) (N + 1)),
      (flatPencilBlk r k F N z y).IsHermitian := fun y => flatPencilBlk_isHermitian k F N z y
  exact memLp_normTrace_cfc (μ := stdGaussian (EuclideanSpace ℝ (GUECoord (Fin r) (N + 1))))
    (M := fun y : EuclideanSpace ℝ (GUECoord (Fin r) (N + 1)) => flatPencilBlk r k F N z y)
    hM hHerm hf hC hC0

/-- **`hWint`: integrability of the `(f')²` block statistic** from a global bound on `f'`. -/
lemma flatStatBlk_sq_integrable (k : ℕ) (F : RatPolyIdx r (k + 1)) (z : ℝ) (N : ℕ)
    {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) {M : ℝ} (hMbound : ∀ y, |deriv f y| ≤ M) :
    Integrable (flatStatBlk r k F z N (fun y => (deriv f y) ^ 2))
      (stdGaussian (EuclideanSpace ℝ (GUECoord (Fin r) (N + 1)))) := by
  have hM : ∀ a b : Fin (pencilFlatDim r k F N), Measurable
      fun y : EuclideanSpace ℝ (GUECoord (Fin r) (N + 1)) => flatPencilBlk r k F N z y a b :=
    fun a b => measurable_flatPencilBlk_entry k F N z a b
  have hHerm : ∀ y : EuclideanSpace ℝ (GUECoord (Fin r) (N + 1)),
      (flatPencilBlk r k F N z y).IsHermitian := fun y => flatPencilBlk_isHermitian k F N z y
  have hcont : Continuous fun y : ℝ => (deriv f y) ^ 2 := hf.continuous_deriv_one.pow 2
  have hbound : ∀ y : ℝ, |(deriv f y) ^ 2| ≤ M ^ 2 := fun y => by
    rw [abs_of_nonneg (sq_nonneg (deriv f y))]
    calc (deriv f y) ^ 2 = |deriv f y| ^ 2 := by rw [sq_abs]
      _ ≤ M ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (hMbound y) 2
  exact integrable_normTrace_cfc
    (μ := stdGaussian (EuclideanSpace ℝ (GUECoord (Fin r) (N + 1))))
    (M := fun y => flatPencilBlk r k F N z y)
    (hM := fun a b => measurable_flatPencilBlk_entry k F N z a b)
    (hHerm := fun y => flatPencilBlk_isHermitian k F N z y) hcont hbound (sq_nonneg M)

/-- **`hint`: integrability of `‖f'(fl ℒ_z)‖_F²`** from the global derivative bound. -/
lemma integrable_hsNorm_cfc_flatPencilBlk (k : ℕ) (F : RatPolyIdx r (k + 1)) (z : ℝ) (N : ℕ)
    {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) {M : ℝ} (hMbound : ∀ y, |deriv f y| ≤ M) :
    Integrable (fun y : EuclideanSpace ℝ (GUECoord (Fin r) (N + 1)) =>
      hsNorm (cfc (deriv f) (flatPencilBlk r k F N z y)))
      (stdGaussian (EuclideanSpace ℝ (GUECoord (Fin r) (N + 1)))) := by
  refine Integrable.of_bound (measurable_hsNorm_cfc_flatPencilBlk k F N z hf).aestronglyMeasurable
    ((pencilFlatDim r k F N : ℝ) * M ^ 2) (Filter.Eventually.of_forall fun y => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (hsNorm_nonneg _)]
  simpa using hsNorm_cfc_le_card_mul_sq (flatPencilBlk r k F N z y)
    (flatPencilBlk_isHermitian k F N z y) hf.continuous_deriv_one hMbound

/-- **`hDmem`: `MemLp 2` of the cfc trace derivatives**, from the uniform bound
`abs_flatDerivStat_le`. -/
lemma flatDerivStat_memLp (k : ℕ) (F : RatPolyIdx r (k + 1)) (z : ℝ) (N : ℕ) (f : ℝ → ℝ)
    (hf : ContDiff ℝ 1 f) {M : ℝ} (hMbound : ∀ y, |deriv f y| ≤ M)
    (p : GUECoord (Fin r) (N + 1)) :
    MemLp (fun y => flatDerivStat r k F z N f y p) 2
      (stdGaussian (EuclideanSpace ℝ (GUECoord (Fin r) (N + 1)))) := by
  refine MemLp.of_bound (measurable_flatDerivStat k F z N f hf p).aestronglyMeasurable
    ((pencilFlatDim r k F N : ℝ)⁻¹ *
      (Real.sqrt ((pencilFlatDim r k F N : ℝ) * M ^ 2) *
        Real.sqrt (hsNorm (flatStepDir r k F N z p))))
    (Filter.Eventually.of_forall fun y => ?_)
  rw [Real.norm_eq_abs]
  exact abs_flatDerivStat_le k F z N f hf hMbound y p

end Inputs

/-! ## 4. The `hV` field, unconditionally -/

section HVField

local instance : Nontrivial (closedSemicircularAlgebra (Fin r)) :=
  (closedGeneratedVacuumState (Fin r)).toProbabilitySpace.nontrivial

local instance : PartialOrder (closedSemicircularAlgebra (Fin r)) :=
  CStarAlgebra.spectralOrder _

local instance : StarOrderedRing (closedSemicircularAlgebra (Fin r)) :=
  CStarAlgebra.spectralOrderedRing _

/-- **Lemma V (`hV`) for the flattened pencil with a smooth cutoff, fully discharged.**  With
`G = flatContractionConst r k F` and `V = pencilVDim r k F`,

`Var(τ_N(f(fl ℒ_z))) ≤ 2 G / V / N² · E[τ_N((f')²(fl ℒ_z))]` eventually in `N`.

This is `flatLemmaV_hV_unconditional` with all six analytic inputs supplied from the smooth
cutoff: the local bound `|f| ≤ 1` and the global bound `|f'| ≤ M`. -/
theorem flatLemmaV_hV_field (k : ℕ) (F : RatPolyIdx r (k + 1)) (z : ℝ) {ε : ℝ} {f : ℝ → ℝ}
    (hf : IsSmoothCutoff (specC (h1PencilLimit r k F z)) ε f) (hf2 : ContDiff ℝ 1 f) :
    ∀ᶠ N : ℕ in atTop,
      variance (flatStat r k F z N f) (commonGaussianMeasure (Fin r))
        ≤ 2 * flatContractionConst r k F / pencilVDim r k F / (N : ℝ) ^ 2
            * ∫ x, flatStat r k F z N (fun t => (deriv f t) ^ 2) x
                ∂(commonGaussianMeasure (Fin r)) := by
  obtain ⟨M, -, hMbound⟩ := hf.exists_deriv_bound
  refine flatLemmaV_hV_unconditional k F z f hf2 ?_ ?_ ?_ ?_ ?_ ?_
  · -- `hF`
    intro N
    exact flatStatBlk_memLp k F z N hf2.continuous (fun y => hf.abs_le_one y) zero_le_one
  · -- `hDmem`
    intro N p
    exact flatDerivStat_memLp k F z N f hf2 hMbound p
  · -- `hpoly`
    intro N p
    filter_upwards with y
    exact ⟨polyGrowth_flatStatBlk k F z N f (fun y => hf.abs_le_one y) zero_le_one y p,
      polyGrowth_flatDerivStat k F z N f hf2 hMbound y p⟩
  · -- `hint`
    intro N
    exact integrable_hsNorm_cfc_flatPencilBlk k F z N hf2 hMbound
  · -- `hWint`
    intro N
    exact flatStatBlk_sq_integrable k F z N hf2 hMbound
  · -- `hW0`
    intro N
    exact hW0_flatStat k F z f N

/-- The `hV` field of `PencilLemmaSResidual` with the constant `C = 2 flatContractionConst /
pencilVDim`, in the residual shape `C / N² * ∫ …`.  This is syntactically the `hV` field of
`PencilLemmaSResidual` at that constant. -/
theorem hV_field_residual_shape (k : ℕ) (F : RatPolyIdx r (k + 1)) (z : ℝ) {ε : ℝ} {f : ℝ → ℝ}
    (hf : IsSmoothCutoff (specC (h1PencilLimit r k F z)) ε f) (hf2 : ContDiff ℝ 1 f) :
    ∀ᶠ N : ℕ in atTop,
      variance (flatStat r k F z N f) (commonGaussianMeasure (Fin r))
        ≤ (2 * flatContractionConst r k F / pencilVDim r k F) / (N : ℝ) ^ 2
            * ∫ x, flatStat r k F z N (fun t => (deriv f t) ^ 2) x
                ∂(commonGaussianMeasure (Fin r)) :=
  flatLemmaV_hV_field k F z hf hf2

/-- The constant of the discharged `hV` field is nonnegative. -/
lemma flatContractionConst_div_pencilVDim_nonneg (k : ℕ) (F : RatPolyIdx r (k + 1)) :
    0 ≤ 2 * flatContractionConst r k F / pencilVDim r k F := by
  have hG : 0 ≤ flatContractionConst r k F := flatContractionConst_nonneg k F
  have hV : 0 < pencilVDim r k F := pencilVDim_pos k F
  positivity

/-- **`PencilLemmaSResidual` with its `hV` field discharged.**  For a smooth cutoff, the
residual bundle holds at the constant `C = 2 flatContractionConst / pencilVDim` as soon as the
two genuine analytic inputs `hM` (Lemma M) and `hWb` (the `(W)` bound) are supplied. -/
theorem PencilLemmaSResidual_of_smoothCutoff_hV (k : ℕ) (F : RatPolyIdx r (k + 1)) (z : ℝ)
    {ε : ℝ} {f : ℝ → ℝ} (C' : ℝ)
    (hf : IsSmoothCutoff (specC (h1PencilLimit r k F z)) ε f) (hf2 : ContDiff ℝ 1 f)
    (hM : FlatLemmaM r k F z f (2 * flatContractionConst r k F / pencilVDim r k F))
    (hWb : ∀ᶠ N : ℕ in atTop,
      ∫ x, flatStat r k F z N (fun y => (deriv f y) ^ 2) x ∂(commonGaussianMeasure (Fin r))
        ≤ C' / (N : ℝ) ^ 2) :
    PencilLemmaSResidual r k F z f (2 * flatContractionConst r k F / pencilVDim r k F) C' where
  hM := hM
  hV := hV_field_residual_shape k F z hf hf2
  hWb := hWb

/-- **`PencilLemmaSData` with `hZ`, `hWint`, `hW0` and `hV` all discharged.**  For a smooth
cutoff and `C' ≥ 0`, only the mean comparison `hM` (Lemma M) and the `(W)` bound `hWb` remain
explicit; the variance constant is the explicit `2 flatContractionConst / pencilVDim`.

Note that `hf : IsSmoothCutoff …` already provides `ContDiff ℝ 1 f`, so no separate
regularity hypothesis is needed here. -/
theorem PencilLemmaSData_of_smoothCutoff_hV (k : ℕ) (F : RatPolyIdx r (k + 1)) (z ε : ℝ)
    {f : ℝ → ℝ} (C' : ℝ)
    (hf : IsSmoothCutoff (specC (h1PencilLimit r k F z)) ε f)
    (hM : FlatLemmaM r k F z f (2 * flatContractionConst r k F / pencilVDim r k F))
    (hWb : ∀ᶠ N : ℕ in atTop,
      ∫ x, flatStat r k F z N (fun y => (deriv f y) ^ 2) x ∂(commonGaussianMeasure (Fin r))
        ≤ C' / (N : ℝ) ^ 2)
    (hC' : 0 ≤ C') :
    PencilLemmaSData r k F z ε f (2 * flatContractionConst r k F / pencilVDim r k F) C' :=
  PencilLemmaSData_of_smoothCutoff k F z ε f _ C' hf
    (PencilLemmaSResidual_of_smoothCutoff_hV k F z C' hf hf.contDiff hM hWb)
    (flatContractionConst_div_pencilVDim_nonneg k F) hC'

end HVField

end

end GUEStrongConvergence
