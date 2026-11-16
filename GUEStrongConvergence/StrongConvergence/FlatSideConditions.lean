/-
# Side conditions of `PencilLemmaSData` for the flattened pencil

`StrongConvergence/FlattenPencil.lean` reduces Lemma S for the linearization pencils to the
six-input structure `PencilLemmaSData` on the *flattened* statistic

`flatStat r k F z N f x = τ_N(f(flat ℒ_z(x)))`.

For the scalar case, `StrongConvergence/ScalarInclusionSmooth.lean` proves the four side
conditions `hZ`, `hWint`, `hW0`, `hV` unconditionally (from a smooth cutoff), leaving only the
mean comparison `hM` and the `(W)` bound `hWb` explicit.  This file does the same for the
flattened pencil:

* **Measurability.**  `continuous_flatPencilBlk` and `measurable_h1PencilApproxFlat_entry`: the
  flattened pencil is continuous (hence measurable) in the Gaussian block.  The proof uses the
  affinity of the pencil in the generator tuple (`penLFlat_add_smul`) to package the pencil as
  a continuous linear map of the block tuple, composed with the explicitly continuous GUE
  block `blockGUEBlk`.
* **`hZ`, `hWint`, `hW0`.**  `flatStat_memLp`, `flatStat_sq_memLp`, `integrable_flatStat_sq`,
  `integral_flatStat_sq_nonneg` are the general estimates (`|f| ≤ C`, `|f'| ≤ M`, `(f')² ≥ 0`);
  `hZ_flatStat`, `hWint_flatStat`, `hW0_flatStat` instantiate them from an `IsSmoothCutoff`.
* **The residual shape.**  `FlatLemmaM` pins the exact shape of the `hM` field (Lemma M), and
  `PencilLemmaSResidual` bundles the three genuinely analytic estimates `hM`, `hV`, `hWb`.
  `PencilLemmaSData_of_smoothCutoff` assembles a full `PencilLemmaSData` from a smooth cutoff
  and `PencilLemmaSResidual`, so a downstream consumer only needs the cutoff and `hM`, `hV`,
  `hWb`.

## Regularity of the cutoff

All the side conditions in this file need only `C¹` regularity: `hZ` uses continuity and
`|f| ≤ 1`; `hWint`/`hW0` use continuity of `(f')²` and the global bound on `f'`, which is
supplied by the compact support of `(f')²` (`IsSmoothCutoff.exists_deriv_bound`).  The
`C²` regularity that the smooth Lemma M representation (`Probability/LemmaMSmooth.lean`) needs
is available for free from the same construction: `exists_isSmoothCutoff_two` below packages
`exists_contDiff_two_cutoff` as an `IsSmoothCutoff` together with `ContDiff ℝ 2 f`.  Since
`IsSmoothCutoff` only records `ContDiff ℝ 1 f`, the residual `hM` field should be discharged
using that strengthened choice.

No `sorry`, no new axioms.
-/
import GUEStrongConvergence.Probability.FlatLemmaV
import GUEStrongConvergence.StrongConvergence.ScalarInclusionSmooth

open Filter MeasureTheory ProbabilityTheory FreeProbability FreeProbability.Fock Matrix
open scoped BigOperators ComplexOrder ENNReal Pointwise Topology

namespace GUEStrongConvergence

noncomputable section

set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

/-! ## 1. Continuity and measurability of the flattened pencil -/

section FlatContinuity

variable {r : ℕ}

/-- The block algebra is finite-dimensional over `ℝ`. -/
instance instFiniteDimensionalBlockAlg (d N : ℕ) : FiniteDimensional ℝ (BlockAlg d N) :=
  inferInstanceAs (FiniteDimensional ℝ
    (Matrix (Fin d) (Fin d) (Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ)))

/-- The flattened pencil, made linear by subtracting its value at the zero generator tuple.
Affinity of the pencil (`penLFlat_add_smul`) is exactly the linearity of this map. -/
def penLFlatLinear (k : ℕ) (F : RatPolyIdx r (k + 1)) (N : ℕ) (z : ℝ) :
    (Fin r → BlockAlg ((k + 1) + (k + 1)) N) →ₗ[ℝ]
      Matrix (Fin (pencilFlatDim r k F N)) (Fin (pencilFlatDim r k F N)) ℂ where
  toFun X := penLFlat r k F N z X - penLFlat r k F N z 0
  map_add' X Y := by
    have h := penLFlat_add_smul (k := k) (F := F) N z X Y 1
    rw [one_smul] at h
    rw [h, one_smul]
    module
  map_smul' c X := by
    have h := penLFlat_add_smul (k := k) (F := F) N z 0 X c
    rw [zero_add] at h
    rw [h, add_sub_cancel_left]
    simp

/-- The linear part of the flattened pencil is continuous. -/
lemma continuous_penLFlatLinear (k : ℕ) (F : RatPolyIdx r (k + 1)) (N : ℕ) (z : ℝ) :
    Continuous (penLFlatLinear (r := r) k F N z) :=
  LinearMap.continuous_of_finiteDimensional _

/-- The value of the flattened pencil is the linear part plus its value at the zero tuple. -/
lemma penLFlat_eq_linear_add (k : ℕ) (F : RatPolyIdx r (k + 1)) (N : ℕ) (z : ℝ)
    (X : Fin r → BlockAlg ((k + 1) + (k + 1)) N) :
    penLFlat r k F N z X
      = penLFlatLinear (r := r) k F N z X + penLFlat r k F N z 0 := by
  simp [penLFlatLinear]

/-- The block GUE tuple depends continuously on the Gaussian block. -/
lemma continuous_blockGUEBlk (d N : ℕ) :
    Continuous fun y : EuclideanSpace ℝ (GUECoord (Fin r) (N + 1)) =>
      blockGUEBlk r d N y := by
  refine continuous_pi fun i => ?_
  refine continuous_matrix fun i' j' => ?_
  by_cases hij : i' = j'
  · subst hij
    refine continuous_matrix fun a b => ?_
    have hfun : (fun y : EuclideanSpace ℝ (GUECoord (Fin r) (N + 1)) =>
          blockGUEBlk r d N y i i' i' a b) = fun y => gueMatrix y.ofLp i a b := by
      funext y
      change (if i' = i' then gueMatrix y.ofLp i else 0) a b = gueMatrix y.ofLp i a b
      rw [ite_eq_left rfl]
    rw [hfun]
    unfold gueMatrix gueUnscaled
    fun_prop
  · have hfun : (fun y : EuclideanSpace ℝ (GUECoord (Fin r) (N + 1)) =>
          blockGUEBlk r d N y i i' j') =
          fun _ => (0 : CStarMatrix (Fin (N + 1)) (Fin (N + 1)) ℂ) := by
      funext y
      change (if i' = j' then gueMatrix y.ofLp i else 0) = 0
      rw [ite_eq_right hij]
    rw [hfun]
    exact continuous_const

/-- **Continuity of the flattened pencil in the Gaussian block.**  The flattened pencil is the
continuous linear part of the pencil composed with the continuous block GUE tuple. -/
theorem continuous_flatPencilBlk (k : ℕ) (F : RatPolyIdx r (k + 1)) (N : ℕ) (z : ℝ) :
    Continuous fun y : EuclideanSpace ℝ (GUECoord (Fin r) (N + 1)) =>
      flatPencilBlk r k F N z y := by
  have hlin : Continuous fun y : EuclideanSpace ℝ (GUECoord (Fin r) (N + 1)) =>
      penLFlatLinear (r := r) k F N z (blockGUEBlk r ((k + 1) + (k + 1)) N y) :=
    (continuous_penLFlatLinear k F N z).comp (continuous_blockGUEBlk _ N)
  have hfun : (fun y : EuclideanSpace ℝ (GUECoord (Fin r) (N + 1)) =>
        flatPencilBlk r k F N z y)
      = fun y => penLFlatLinear (r := r) k F N z
          (blockGUEBlk r ((k + 1) + (k + 1)) N y) + penLFlat r k F N z 0 := by
    funext y
    rw [flatPencilBlk, penLFlat_eq_linear_add]
  rw [hfun]
  exact hlin.add continuous_const

/-- The flattened approximating pencil on the common space is the block pencil evaluated at
the `(N+1)`-st Gaussian block. -/
lemma h1PencilApproxFlat_eq_flatPencilBlk (k : ℕ) (F : RatPolyIdx r (k + 1))
    (x : CommonSpace (Fin r)) (N : ℕ) (z : ℝ) :
    h1PencilApproxFlat r k F x N z = flatPencilBlk r k F N z (x (N + 1)) :=
  rfl

/-- Entry measurability of the flattened approximating pencil on the common space. -/
lemma measurable_h1PencilApproxFlat_entry (k : ℕ) (F : RatPolyIdx r (k + 1))
    (N : ℕ) (z : ℝ) (a b : Fin (pencilFlatDim r k F N)) :
    Measurable fun x : CommonSpace (Fin r) => h1PencilApproxFlat r k F x N z a b := by
  have hcont : Continuous fun x : CommonSpace (Fin r) =>
      flatPencilBlk r k F N z (x (N + 1)) :=
    (continuous_flatPencilBlk k F N z).comp (continuous_apply (N + 1))
  have hfun : (fun x : CommonSpace (Fin r) => h1PencilApproxFlat r k F x N z a b)
      = fun x => flatPencilBlk r k F N z (x (N + 1)) a b := by
    funext x
    rw [h1PencilApproxFlat_eq_flatPencilBlk]
  rw [hfun]
  exact (hcont.matrix_elem a b).measurable

/-- **Measurability of the flattened statistic.**  For continuous `f`, the flattened statistic
`x ↦ τ_N(f(flat ℒ_z(x)))` is measurable. -/
lemma measurable_flatStat (k : ℕ) (F : RatPolyIdx r (k + 1)) (z : ℝ) (N : ℕ)
    {f : ℝ → ℝ} (hf : Continuous f) :
    Measurable fun x : CommonSpace (Fin r) => flatStat r k F z N f x :=
  measurable_normTrace_cfc
    (M := fun x => h1PencilApproxFlat r k F x N z)
    (hM := fun a b => measurable_h1PencilApproxFlat_entry k F N z a b)
    (hHerm := fun x => h1PencilApproxFlat_isHermitian r k F x N z) hf

end FlatContinuity

/-! ## 2. The `L²` and integrability side conditions

These are the flattened analogues of §4 of `StrongConvergence/ScalarInclusionSmooth.lean`:
`|f| ≤ C` gives `MemLp` of `τ_N(f(flat ℒ_z))`, a global bound on `f'` gives integrability of
`τ_N((f')²(flat ℒ_z))`, and `(f')² ≥ 0` gives nonnegativity of its mean. -/

section FlatSideConditions

variable {r : ℕ}

local instance : Nontrivial (closedSemicircularAlgebra (Fin r)) :=
  (closedGeneratedVacuumState (Fin r)).toProbabilitySpace.nontrivial

local instance : PartialOrder (closedSemicircularAlgebra (Fin r)) :=
  CStarAlgebra.spectralOrder _

local instance : StarOrderedRing (closedSemicircularAlgebra (Fin r)) :=
  CStarAlgebra.spectralOrderedRing _

/-- **`hZ` at the general level.**  `MemLp 2` of the flattened statistic from a global bound on
the cutoff. -/
lemma flatStat_memLp (k : ℕ) (F : RatPolyIdx r (k + 1)) (z : ℝ)
    {f : ℝ → ℝ} (hf : Continuous f) {C : ℝ} (hC : ∀ y, |f y| ≤ C) (hC0 : 0 ≤ C) (N : ℕ) :
    MemLp (flatStat r k F z N f) 2 (commonGaussianMeasure (Fin r)) :=
  memLp_normTrace_cfc (μ := commonGaussianMeasure (Fin r))
    (M := fun x => h1PencilApproxFlat r k F x N z)
    (hM := fun a b => measurable_h1PencilApproxFlat_entry k F N z a b)
    (hHerm := fun x => h1PencilApproxFlat_isHermitian r k F x N z) hf hC hC0

/-- The `(f')²` statistic has `MemLp 2` from a bound on `f'`. -/
lemma flatStat_sq_memLp (k : ℕ) (F : RatPolyIdx r (k + 1)) (z : ℝ)
    {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) {M : ℝ} (hMbound : ∀ y, |deriv f y| ≤ M) (N : ℕ) :
    MemLp (flatStat r k F z N (fun y => (deriv f y) ^ 2)) 2
      (commonGaussianMeasure (Fin r)) := by
  have hcont : Continuous fun y : ℝ => (deriv f y) ^ 2 := hf.continuous_deriv_one.pow 2
  have hbound : ∀ y : ℝ, |(deriv f y) ^ 2| ≤ M ^ 2 := fun y => by
    rw [abs_of_nonneg (sq_nonneg (deriv f y))]
    calc (deriv f y) ^ 2 = |deriv f y| ^ 2 := by rw [sq_abs]
      _ ≤ M ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (hMbound y) 2
  exact flatStat_memLp k F z hcont hbound (sq_nonneg M) N

/-- **`hWint` at the general level.**  Integrability of the `(f')²` statistic from a global
bound on `f'`. -/
lemma integrable_flatStat_sq (k : ℕ) (F : RatPolyIdx r (k + 1)) (z : ℝ)
    {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) {M : ℝ} (hMbound : ∀ y, |deriv f y| ≤ M) (N : ℕ) :
    Integrable (flatStat r k F z N (fun y => (deriv f y) ^ 2))
      (commonGaussianMeasure (Fin r)) := by
  have hcont : Continuous fun y : ℝ => (deriv f y) ^ 2 := hf.continuous_deriv_one.pow 2
  have hbound : ∀ y : ℝ, |(deriv f y) ^ 2| ≤ M ^ 2 := fun y => by
    rw [abs_of_nonneg (sq_nonneg (deriv f y))]
    calc (deriv f y) ^ 2 = |deriv f y| ^ 2 := by rw [sq_abs]
      _ ≤ M ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (hMbound y) 2
  exact integrable_normTrace_cfc (μ := commonGaussianMeasure (Fin r))
    (M := fun x => h1PencilApproxFlat r k F x N z)
    (hM := fun a b => measurable_h1PencilApproxFlat_entry k F N z a b)
    (hHerm := fun x => h1PencilApproxFlat_isHermitian r k F x N z)
    hcont hbound (sq_nonneg M)

/-- **`hW0` at the general level.**  Nonnegativity of the mean of the `(f')²` statistic. -/
lemma integral_flatStat_sq_nonneg (k : ℕ) (F : RatPolyIdx r (k + 1)) (z : ℝ)
    (f : ℝ → ℝ) (N : ℕ) :
    0 ≤ ∫ x, flatStat r k F z N (fun y => (deriv f y) ^ 2) x
      ∂(commonGaussianMeasure (Fin r)) :=
  integral_normTrace_cfc_nonneg (μ := commonGaussianMeasure (Fin r))
    (M := fun x => h1PencilApproxFlat r k F x N z)
    (hM := fun a b => measurable_h1PencilApproxFlat_entry k F N z a b)
    (hHerm := fun x => h1PencilApproxFlat_isHermitian r k F x N z)
    (fun y => sq_nonneg (deriv f y))

/-- **`hZ` from a smooth cutoff.** -/
lemma hZ_flatStat (k : ℕ) (F : RatPolyIdx r (k + 1)) (z : ℝ) {S : Set ℝ} {ε : ℝ}
    {f : ℝ → ℝ} (hf : IsSmoothCutoff S ε f) (N : ℕ) :
    MemLp (flatStat r k F z N f) 2 (commonGaussianMeasure (Fin r)) :=
  flatStat_memLp k F z hf.contDiff.continuous (fun y => hf.abs_le_one y) zero_le_one N

/-- **`hWint` from a smooth cutoff.**  The compact support of `(f')²` gives a global bound on
`f'`, which bounds the `(f')²` statistic. -/
lemma hWint_flatStat (k : ℕ) (F : RatPolyIdx r (k + 1)) (z : ℝ) {S : Set ℝ} {ε : ℝ}
    {f : ℝ → ℝ} (hf : IsSmoothCutoff S ε f) (N : ℕ) :
    Integrable (flatStat r k F z N (fun y => (deriv f y) ^ 2))
      (commonGaussianMeasure (Fin r)) := by
  obtain ⟨M, -, hMbound⟩ := hf.exists_deriv_bound
  exact integrable_flatStat_sq k F z hf.contDiff hMbound N

/-- **`hW0` from a smooth cutoff** (in fact no regularity of `f` is needed). -/
lemma hW0_flatStat (k : ℕ) (F : RatPolyIdx r (k + 1)) (z : ℝ)
    (f : ℝ → ℝ) (N : ℕ) :
    0 ≤ ∫ x, flatStat r k F z N (fun y => (deriv f y) ^ 2) x
      ∂(commonGaussianMeasure (Fin r)) :=
  integral_flatStat_sq_nonneg k F z f N

/-! ## 3. The genuinely analytic residual: Lemma M, Lemma V and the `(W)` bound -/

/-- **Lemma M for the flattened pencil, in the exact shape of the `hM` field.**

`|E τ_N(f(flat ℒ_z))| = O(N⁻²)`.  This is *not* proved here; it pins the exact statement a
downstream consumer has to discharge (and it is the flattened analogue of the scalar `hM`).
The same shape appears as the `hM` field of `PencilLemmaSData` with the same cutoff `f` and
constant `C`. -/
def FlatLemmaM (r k : ℕ) (F : RatPolyIdx r (k + 1)) (z : ℝ) (f : ℝ → ℝ) (C : ℝ) : Prop :=
  ∀ᶠ N : ℕ in atTop,
    |∫ x, flatStat r k F z N f x ∂(commonGaussianMeasure (Fin r))| ≤ C / (N : ℝ) ^ 2

/-- The three analytic inputs that remain after the side conditions are discharged: Lemma M
(`hM`), Lemma V (`hV`, provided for the flattened pencil by `flatLemmaV`/`flatLemmaV_hV` under
the direction-contraction hypothesis) and the `(W)` bound (`hWb`). -/
structure PencilLemmaSResidual (r k : ℕ) (F : RatPolyIdx r (k + 1)) (z : ℝ)
    (f : ℝ → ℝ) (C C' : ℝ) : Prop where
  /-- Lemma M: the mean comparison. -/
  hM : FlatLemmaM r k F z f C
  /-- Lemma V: the variance bound controlled by the cfc trace derivative. -/
  hV : ∀ᶠ N : ℕ in atTop, variance (flatStat r k F z N f) (commonGaussianMeasure (Fin r))
    ≤ C / (N : ℝ) ^ 2 * ∫ x, flatStat r k F z N (fun y => (deriv f y) ^ 2) x
        ∂(commonGaussianMeasure (Fin r))
  /-- The `(W)` bound: the derivative statistic has mean `O(1/N²)`. -/
  hWb : ∀ᶠ N : ℕ in atTop, ∫ x, flatStat r k F z N (fun y => (deriv f y) ^ 2) x
    ∂(commonGaussianMeasure (Fin r)) ≤ C' / (N : ℝ) ^ 2

/-- **`PencilLemmaSData` from a smooth cutoff and the three analytic residuals.**  The fields
`hZ`, `hWint`, `hW0` are discharged, so a consumer only has to supply the cutoff and
`PencilLemmaSResidual`. -/
theorem PencilLemmaSData_of_smoothCutoff
    (k : ℕ) (F : RatPolyIdx r (k + 1)) (z ε : ℝ) (f : ℝ → ℝ) (C C' : ℝ)
    (hf : IsSmoothCutoff (specC (h1PencilLimit r k F z)) ε f)
    (hres : PencilLemmaSResidual r k F z f C C') (hC : 0 ≤ C) (hC' : 0 ≤ C') :
    PencilLemmaSData r k F z ε f C C' where
  hf0 := hf.nonneg
  hf1 := hf.eq_one
  hC := hC
  hC' := hC'
  hZ := fun N => hZ_flatStat k F z hf N
  hWint := fun N => hWint_flatStat k F z hf N
  hW0 := fun N => hW0_flatStat k F z f N
  hM := hres.hM
  hV := hres.hV
  hWb := hres.hWb

/-- **The residual input bundle**, in the same existential shape as `PencilLemmaSInputs`: for
every canonical dilated polynomial, pencil parameter and radius there are a smooth cutoff and
constants satisfying the three analytic residuals. -/
def PencilLemmaSResidualInputs (r : ℕ) : Prop :=
  ∀ (k : ℕ) (F : RatPolyIdx r (k + 1)) (z ε : ℝ), 0 < ε →
    ∃ (f : ℝ → ℝ) (C C' : ℝ),
      IsSmoothCutoff (specC (h1PencilLimit r k F z)) ε f ∧
        PencilLemmaSResidual r k F z f C C' ∧ 0 ≤ C ∧ 0 ≤ C'

/-- **The six-input bundle from the residual bundle.**  Combining `PencilLemmaSData_of_smoothCutoff`
with `PencilLemmaSResidualInputs` gives `PencilLemmaSInputs`, hence (by
`pencilSpectralInclusionData_of_lemmaSInputs`) the spectral inclusion for the flattened
pencils. -/
theorem PencilLemmaSInputs_of_residualInputs (h : PencilLemmaSResidualInputs r) :
    PencilLemmaSInputs r := by
  intro k F z ε hε
  obtain ⟨f, C, C', hf, hres, hC, hC'⟩ := h k F z ε hε
  exact ⟨f, C, C', PencilLemmaSData_of_smoothCutoff k F z ε f C C' hf hres hC hC'⟩

/-! ## 4. `C¹` versus `C²` cutoffs -/

/-- **A smooth cutoff with the `C²` regularity needed by Lemma M.**  The construction of
`exists_contDiff_cutoff` is actually smooth, so for Lemma M (whose smooth Cauchy--Pompeiu
representation needs `C²`) one can use this strengthened choice instead of
`exists_isSmoothCutoff`; the side conditions of this file only need the `C¹` part. -/
theorem exists_isSmoothCutoff_two {S : Set ℝ} {ε : ℝ} (hS : IsCompact S) (hε : 0 < ε) :
    ∃ f : ℝ → ℝ, IsSmoothCutoff S ε f ∧ ContDiff ℝ 2 f := by
  obtain ⟨f, hcd2, h0, -, hone, hle, -, hsupp⟩ := exists_contDiff_two_cutoff hS hε
  exact ⟨f, ⟨hcd2.of_le (by norm_num), h0, hle, hone, hsupp⟩, hcd2⟩

end FlatSideConditions

end

end GUEStrongConvergence
