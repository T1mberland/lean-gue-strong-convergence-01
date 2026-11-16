/-
# Flattening the polynomial linearization pencils

`PencilSpectralInclusionData r` (`StrongConvergence/PencilSpectralInclusion.lean`) is the
per-index spectral family inclusion for the linearization pencils
`h1PencilApprox r k F x n z`, which live in the block algebra

`h1An r k F n = CStarMatrix (PenIdx wds) (PenIdx wds) (BlockAlg d n)`

with `wds = polyW (h1Poly r k F)` and `d = (k+1) + (k+1)`.  Lemma S
(`ae_eventually_spectrum_subset_commonSpace`) is stated for matrices indexed by
`Fin (m N)`, so the pencils must first be flattened, and the spectrum must be transported
across the flattening.

## What this file does

* `compStarAlgEquiv` — the star-algebra version of `Matrix.compAlgEquiv` (which is only an
  `AlgEquiv`): `Matrix I I (Matrix J J R) ≃⋆ₐ[K] Matrix (I × J) (I × J) R`;
* `flattenPencilStarAlgEquiv` — the composite flattening
  `h1An r k F n ≃⋆ₐ[ℝ] Matrix (Fin (pencilFlatDim r k F n)) (Fin (pencilFlatDim r k F n)) ℂ`,
  obtained by chaining `CStarMatrix.ofMatrixStarAlgEquiv` (twice, through `BlockAlg`),
  `compStarAlgEquiv` (twice) and `reindexStarAlgEquiv`;
* `specC_flatten` — `specC` invariance: for every pencil the C⋆-graph real spectrum
  `specC (h1PencilApprox r k F x n z)` is *literally* the real spectrum of the flattened
  matrix;
* `PencilLemmaSInputs` — the six Lemma-S inputs (`hZ`, `hWint`, `hW0`, `hM`, `hV`, `hWb`)
  for the flattened polynomial statistic `flatStat r k F z N f`, with `hM` the smooth mean
  comparison (Lemma M) and `hV` the variance bound controlled by the cfc trace derivative
  statistic `τ_N((f')²(flat ℒ_z))`;
* `pencilSpectralInclusionData_of_lemmaSInputs` — those six inputs imply
  `PencilSpectralInclusionData r` (Lemma S applied to the flattened family);
* `H1CanonicalDilated_of_lemmaSInputs` and
  `GUEStrongConvergenceStatement_of_scalarSpectralInclusion_and_lemmaSInputs` — the
  `hH1`- and statement-level consequences.

Nothing is assumed beyond the six explicit analytic estimates; there is no `sorry` and no
new axiom.
-/
import GUEStrongConvergence.StrongConvergence.PencilSpectralInclusion

open Filter MeasureTheory ProbabilityTheory FreeProbability FreeProbability.Fock Matrix
open scoped BigOperators ComplexOrder ENNReal Pointwise Topology

namespace GUEStrongConvergence

noncomputable section

set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

/-! ## 1. Flattening the block algebra to a complex matrix algebra -/

section Flatten

/-- `Matrix.comp` as a star algebra equivalence.  `Matrix.compAlgEquiv` is only an
`AlgEquiv`; it is star-preserving because `Matrix.comp` acts entrywise. -/
def compStarAlgEquiv (I J R K : Type*) [Fintype I] [DecidableEq I] [Fintype J]
    [DecidableEq J] [CommSemiring K] [Semiring R] [StarRing R] [Algebra K R] :
    Matrix I I (Matrix J J R) ≃⋆ₐ[K] Matrix (I × J) (I × J) R :=
  StarAlgEquiv.ofAlgEquiv (Matrix.compAlgEquiv I J R K) (by
    intro M
    ext ⟨i1, j1⟩ ⟨i2, j2⟩
    simp [Matrix.comp_apply, Matrix.star_apply])

variable (r k : ℕ) (F : RatPolyIdx r (k + 1))

/-- The dimension of the flattened linearization pencils:
`card (PenIdx wds) * (d * (n+1))`. -/
def pencilFlatDim (n : ℕ) : ℕ :=
  Fintype.card (PenIdx (polyW (h1Poly r k F))) * (((k + 1) + (k + 1)) * (n + 1))

/-- The pencil index type, flattened to a single `Fin`.  This is the index equivalence used
for the final reindexing step of `flattenPencilStarAlgEquiv`. -/
def pencilFlatIdx (n : ℕ) :
    (PenIdx (polyW (h1Poly r k F)) × Fin ((k + 1) + (k + 1))) × Fin (n + 1) ≃
      Fin (pencilFlatDim r k F n) :=
  (Equiv.prodAssoc (PenIdx (polyW (h1Poly r k F))) (Fin ((k + 1) + (k + 1)))
      (Fin (n + 1))).trans
    ((Equiv.prodCongr (Equiv.refl (PenIdx (polyW (h1Poly r k F))))
      (finProdFinEquiv (m := (k + 1) + (k + 1)) (n := n + 1))).trans
      (pencilIndexEquiv (PenIdx (polyW (h1Poly r k F)))
        (((k + 1) + (k + 1)) * (n + 1))))

/-- The composite flattening of the ambient linearization algebra to a complex matrix
algebra.

We peel the two `CStarMatrix` layers of `BlockAlg` with `Matrix.comp`, and finish with the
index reindexing `pencilFlatIdx`.  Every step preserves `star`, so the composite is a star
algebra equivalence. -/
def flattenPencilStarAlgEquiv (n : ℕ) :
    h1An r k F n ≃⋆ₐ[ℝ]
      Matrix (Fin (pencilFlatDim r k F n)) (Fin (pencilFlatDim r k F n)) ℂ :=
  ((CStarMatrix.ofMatrixStarAlgEquiv).symm.restrictScalars ℝ).trans
    ((compStarAlgEquiv (PenIdx (polyW (h1Poly r k F))) (Fin ((k + 1) + (k + 1)))
        (CStarMatrix (Fin (n + 1)) (Fin (n + 1)) ℂ) ℝ).trans
      ((compStarAlgEquiv (PenIdx (polyW (h1Poly r k F)) × Fin ((k + 1) + (k + 1)))
          (Fin (n + 1)) ℂ ℝ).trans
        (by
          classical
          exact reindexStarAlgEquiv (pencilFlatIdx r k F n))))

/-- The flattened approximating linearization pencil of the `F`-th canonical dilated
polynomial, at block size `n + 1` and pencil parameter `z`. -/
def h1PencilApproxFlat (x : CommonSpace (Fin r)) (n : ℕ) (z : ℝ) :
    Matrix (Fin (pencilFlatDim r k F n)) (Fin (pencilFlatDim r k F n)) ℂ :=
  flattenPencilStarAlgEquiv r k F n (h1PencilApprox r k F x n z)

/-- The flattened approximating pencil is Hermitian. -/
lemma h1PencilApproxFlat_isHermitian (x : CommonSpace (Fin r)) (n : ℕ) (z : ℝ) :
    (h1PencilApproxFlat r k F x n z).IsHermitian :=
  (h1PencilApprox_isSelfAdjoint r k F x n z).map (flattenPencilStarAlgEquiv r k F n)

/-- **`specC` invariance under the flattening.**  The C⋆-graph real spectrum of the
approximating linearization pencil is the real spectrum of its flattened matrix. -/
theorem specC_flatten (x : CommonSpace (Fin r)) (n : ℕ) (z : ℝ) :
    specC (h1PencilApprox r k F x n z) =
      spectrum ℝ (h1PencilApproxFlat r k F x n z) := by
  rw [specC, h1PencilApproxFlat]
  exact (AlgEquiv.spectrum_eq (flattenPencilStarAlgEquiv r k F n)
    (h1PencilApprox r k F x n z)).symm

end Flatten

/-! ## 2. The Lemma-S inputs for the flattened pencil family -/

section PencilInputs

variable {r : ℕ}

local instance : Nontrivial (closedSemicircularAlgebra (Fin r)) :=
  (closedGeneratedVacuumState (Fin r)).toProbabilitySpace.nontrivial

local instance : PartialOrder (closedSemicircularAlgebra (Fin r)) :=
  CStarAlgebra.spectralOrder _

local instance : StarOrderedRing (closedSemicircularAlgebra (Fin r)) :=
  CStarAlgebra.spectralOrderedRing _

/-- The flattened polynomial statistic `τ_N(f(flat ℒ_z))` at the `N`-th block, as a function
of the common-space point: `normTrace (hermCfc (flat ℒ_z) f _)`. -/
def flatStat (r k : ℕ) (F : RatPolyIdx r (k + 1)) (z : ℝ) (N : ℕ) (f : ℝ → ℝ)
    (x : CommonSpace (Fin r)) : ℝ :=
  normTrace (hermCfc (h1PencilApproxFlat r k F x N z) f
    (h1PencilApproxFlat_isHermitian r k F x N z))

/-- The dimension growth constant `D = 2 * card (PenIdx wds) * d` of the flattened pencils;
`pencilFlatDim r k F N = card * (d * (N+1)) ≤ D * N` for `N ≥ 1`. -/
def pencilFlatConst (r k : ℕ) (F : RatPolyIdx r (k + 1)) : ℝ :=
  2 * ((Fintype.card (PenIdx (polyW (h1Poly r k F))) : ℝ) * (((k + 1) + (k + 1)) : ℝ))

/-- **The six Lemma-S inputs for the flattened polynomial pencil** at a fixed pencil
`(k, F, z)`, a fixed radius `ε` and a fixed cutoff `f`.

* `hf0`, `hf1`: `f ≥ 0` and `f = 1` off `specC (h1PencilLimit r k F z) + (-ε, ε)`;
* `hC`, `hC'`: the constants are nonnegative;
* `hZ`: `τ_N(f(flat ℒ_z)) ∈ L²(commonGaussianMeasure)`;
* `hWint`: `τ_N((f')²(flat ℒ_z))` is integrable;
* `hW0`: `∫ τ_N((f')²(flat ℒ_z)) ≥ 0`;
* `hM`: **Lemma M**, the smooth mean comparison `|∫ τ_N(f(flat ℒ_z))| ≤ C / N²`;
* `hV`: **Lemma V** (the cfc trace derivative input), the variance bound controlled by
  `τ_N((f')²(flat ℒ_z))`;
* `hWb`: the mean of `τ_N((f')²(flat ℒ_z))` is `O(1/N²)`.

All statements are for the *flattened* matrices, i.e. they are the six inputs of
`ae_eventually_spectrum_subset_commonSpace` for the family `N ↦ flat ℒ_z`. -/
structure PencilLemmaSData (r k : ℕ) (F : RatPolyIdx r (k + 1)) (z ε : ℝ)
    (f : ℝ → ℝ) (C C' : ℝ) : Prop where
  /-- `f` is nonnegative. -/
  hf0 : ∀ y, 0 ≤ f y
  /-- `f` is `1` off the `ε`-neighbourhood of the limit pencil spectrum. -/
  hf1 : ∀ y, y ∉ specC (h1PencilLimit r k F z) + Set.Ioo (-ε) ε → f y = 1
  /-- `C ≥ 0`. -/
  hC : 0 ≤ C
  /-- `C' ≥ 0`. -/
  hC' : 0 ≤ C'
  /-- `L²` bound for the flattened polynomial statistic. -/
  hZ : ∀ N : ℕ, MemLp (flatStat r k F z N f) 2 (commonGaussianMeasure (Fin r))
  /-- Integrability of the derivative statistic. -/
  hWint : ∀ N : ℕ, Integrable (flatStat r k F z N (fun y => (deriv f y) ^ 2))
    (commonGaussianMeasure (Fin r))
  /-- Nonnegativity of the mean of the derivative statistic. -/
  hW0 : ∀ N : ℕ, 0 ≤ ∫ x, flatStat r k F z N (fun y => (deriv f y) ^ 2) x
    ∂(commonGaussianMeasure (Fin r))
  /-- Lemma M: the mean comparison. -/
  hM : ∀ᶠ N : ℕ in atTop,
    |∫ x, flatStat r k F z N f x ∂(commonGaussianMeasure (Fin r))| ≤ C / (N : ℝ) ^ 2
  /-- Lemma V: the variance bound controlled by the cfc trace derivative. -/
  hV : ∀ᶠ N : ℕ in atTop, variance (flatStat r k F z N f) (commonGaussianMeasure (Fin r))
    ≤ C / (N : ℝ) ^ 2 * ∫ x, flatStat r k F z N (fun y => (deriv f y) ^ 2) x
        ∂(commonGaussianMeasure (Fin r))
  /-- The derivative statistic has mean `O(1/N²)`. -/
  hWb : ∀ᶠ N : ℕ in atTop, ∫ x, flatStat r k F z N (fun y => (deriv f y) ^ 2) x
    ∂(commonGaussianMeasure (Fin r)) ≤ C' / (N : ℝ) ^ 2

/-- **The single analytic input bundle**: for every canonical dilated polynomial (indexed by
`k` and the dense family index `F`), every real pencil parameter `z` and every radius `ε > 0`
there exist a cutoff `f` and constants `C, C'` satisfying the six Lemma-S estimates
`PencilLemmaSData`. -/
def PencilLemmaSInputs (r : ℕ) : Prop :=
  ∀ (k : ℕ) (F : RatPolyIdx r (k + 1)) (z ε : ℝ), 0 < ε →
    ∃ (f : ℝ → ℝ) (C C' : ℝ), PencilLemmaSData r k F z ε f C C'

/-- The flattened pencil dimensions are eventually positive. -/
lemma eventually_pos_pencilFlatDim (r k : ℕ) (F : RatPolyIdx r (k + 1)) :
    ∀ᶠ N : ℕ in atTop, 0 < pencilFlatDim r k F N := by
  haveI : Nonempty (PenIdx (polyW (h1Poly r k F))) := inferInstance
  filter_upwards with N
  exact Nat.mul_pos Fintype.card_pos (Nat.mul_pos (by omega) (Nat.succ_pos N))

/-- The flattened pencil dimensions grow at most linearly, with constant `pencilFlatConst`. -/
lemma eventually_pencilFlatDim_le (r k : ℕ) (F : RatPolyIdx r (k + 1)) :
    ∀ᶠ N : ℕ in atTop,
      (pencilFlatDim r k F N : ℝ) ≤ pencilFlatConst r k F * (N : ℝ) := by
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
  have hN' : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hcast : (pencilFlatDim r k F N : ℝ)
      = ((Fintype.card (PenIdx (polyW (h1Poly r k F))) : ℝ) * (((k + 1) + (k + 1)) : ℝ))
        * ((N : ℝ) + 1) := by
    rw [pencilFlatDim]
    push_cast
    ring
  have hc : (0 : ℝ) ≤
      ((Fintype.card (PenIdx (polyW (h1Poly r k F))) : ℝ) * (((k + 1) + (k + 1)) : ℝ)) := by
    positivity
  have hstep : (N : ℝ) + 1 ≤ 2 * (N : ℝ) := by linarith
  rw [hcast, pencilFlatConst]
  calc ((Fintype.card (PenIdx (polyW (h1Poly r k F))) : ℝ) * (((k + 1) + (k + 1)) : ℝ))
        * ((N : ℝ) + 1)
      ≤ ((Fintype.card (PenIdx (polyW (h1Poly r k F))) : ℝ) * (((k + 1) + (k + 1)) : ℝ))
        * (2 * (N : ℝ)) := by
        exact mul_le_mul_of_nonneg_left hstep hc
    _ = 2 * ((Fintype.card (PenIdx (polyW (h1Poly r k F))) : ℝ) * (((k + 1) + (k + 1)) : ℝ))
        * (N : ℝ) := by ring

end PencilInputs

/-! ## 3. Lemma S for the flattened pencil family, and the `hH1`-level consequences -/

section Main

variable {r : ℕ}

local instance : Nontrivial (closedSemicircularAlgebra (Fin r)) :=
  (closedGeneratedVacuumState (Fin r)).toProbabilitySpace.nontrivial

local instance : PartialOrder (closedSemicircularAlgebra (Fin r)) :=
  CStarAlgebra.spectralOrder _

local instance : StarOrderedRing (closedSemicircularAlgebra (Fin r)) :=
  CStarAlgebra.spectralOrderedRing _

/-- **Per-index Lemma S for the flattened polynomial linearization pencil.**

Fix a canonical dilated polynomial `(k, F)`, a real pencil parameter `z`, a radius `ε > 0`, a
cutoff `f` and constants `C, C'`, and assume the six Lemma-S estimates for the flattened
family `N ↦ flat ℒ_z` (the bundle `PencilLemmaSData`).  Then almost surely the C⋆-graph
spectrum of the approximating pencil is eventually contained in the `ε`-neighbourhood of the
limit spectrum.

This is `ae_eventually_spectrum_subset_commonSpace` applied to
`H N x = h1PencilApproxFlat r k F x N z` with `S = specC (h1PencilLimit r k F z)`, followed
by the spectrum transport `specC_flatten`. -/
theorem ae_eventually_specC_subset_of_pencilLemmaSData
    (k : ℕ) (F : RatPolyIdx r (k + 1)) (z ε : ℝ) (hε : 0 < ε)
    (f : ℝ → ℝ) (C C' : ℝ) (hd : PencilLemmaSData r k F z ε f C C') :
    ∀ᵐ x ∂(commonGaussianMeasure (Fin r)), ∀ᶠ n : ℕ in atTop,
      specC (h1PencilApprox r k F x n z) ⊆
        specC (h1PencilLimit r k F z) + Set.Ioo (-ε) ε := by
  have hm := eventually_pos_pencilFlatDim r k F
  have hD : 0 ≤ pencilFlatConst r k F := by
    rw [pencilFlatConst]
    positivity
  have hmD := eventually_pencilFlatDim_le r k F
  have hmain := ae_eventually_spectrum_subset_commonSpace
    (ι := Fin r) (m := fun N => pencilFlatDim r k F N)
    hm hε hd.hf0 hd.hf1
    (fun N x => h1PencilApproxFlat r k F x N z)
    (fun N x => h1PencilApproxFlat_isHermitian r k F x N z)
    hd.hC hd.hC' hD hmD hd.hZ hd.hWint hd.hW0 hd.hM hd.hV hd.hWb
  filter_upwards [hmain] with x hx
  filter_upwards [hx] with n hn
  intro lam hlam
  rw [specC_flatten] at hlam
  exact hn hlam

/-- **Per-index Lemma S for the flattened pencil, with the six inputs unbundled.**

This is the same statement as `ae_eventually_specC_subset_of_pencilLemmaSData`, but with the
six Lemma-S estimates as separate explicit hypotheses (`hZ`, `hWint`, `hW0`, `hM`, `hV`,
`hWb`), for consumers that discharge them individually. -/
theorem ae_eventually_specC_subset_of_inputs
    (k : ℕ) (F : RatPolyIdx r (k + 1)) (z ε : ℝ) (hε : 0 < ε)
    (f : ℝ → ℝ) (C C' : ℝ)
    (hf0 : ∀ y, 0 ≤ f y)
    (hf1 : ∀ y, y ∉ specC (h1PencilLimit r k F z) + Set.Ioo (-ε) ε → f y = 1)
    (hC : 0 ≤ C) (hC' : 0 ≤ C')
    (hZ : ∀ N : ℕ, MemLp (flatStat r k F z N f) 2 (commonGaussianMeasure (Fin r)))
    (hWint : ∀ N : ℕ, Integrable (flatStat r k F z N (fun y => (deriv f y) ^ 2))
      (commonGaussianMeasure (Fin r)))
    (hW0 : ∀ N : ℕ, 0 ≤ ∫ x, flatStat r k F z N (fun y => (deriv f y) ^ 2) x
      ∂(commonGaussianMeasure (Fin r)))
    (hM : ∀ᶠ N : ℕ in atTop,
      |∫ x, flatStat r k F z N f x ∂(commonGaussianMeasure (Fin r))| ≤ C / (N : ℝ) ^ 2)
    (hV : ∀ᶠ N : ℕ in atTop, variance (flatStat r k F z N f) (commonGaussianMeasure (Fin r))
      ≤ C / (N : ℝ) ^ 2 * ∫ x, flatStat r k F z N (fun y => (deriv f y) ^ 2) x
          ∂(commonGaussianMeasure (Fin r)))
    (hWb : ∀ᶠ N : ℕ in atTop, ∫ x, flatStat r k F z N (fun y => (deriv f y) ^ 2) x
      ∂(commonGaussianMeasure (Fin r)) ≤ C' / (N : ℝ) ^ 2) :
    ∀ᵐ x ∂(commonGaussianMeasure (Fin r)), ∀ᶠ n : ℕ in atTop,
      specC (h1PencilApprox r k F x n z) ⊆
        specC (h1PencilLimit r k F z) + Set.Ioo (-ε) ε :=
  ae_eventually_specC_subset_of_pencilLemmaSData k F z ε hε f C C'
    { hf0 := hf0, hf1 := hf1, hC := hC, hC' := hC', hZ := hZ, hWint := hWint,
      hW0 := hW0, hM := hM, hV := hV, hWb := hWb }

/-- **Lemma S for the flattened polynomial linearization pencils.**

Assume the single analytic bundle `PencilLemmaSInputs`: at every canonical dilated
polynomial, pencil parameter and radius there are a cutoff and constants satisfying the six
Lemma-S estimates for the flattened family.  Then
`PencilSpectralInclusionData r`, i.e. the approximating spectrum is almost surely eventually
contained in the `ε`-neighbourhood of the limit spectrum. -/
theorem pencilSpectralInclusionData_of_lemmaSInputs (h : PencilLemmaSInputs r) :
    PencilSpectralInclusionData r := by
  intro k F z ε hε
  obtain ⟨f, C, C', hd⟩ := h k F z ε hε
  exact ae_eventually_specC_subset_of_pencilLemmaSData k F z ε hε f C C' hd

/-- **`hH1` from the six Lemma-S estimates for the flattened pencils.** -/
theorem H1CanonicalDilated_of_lemmaSInputs (h : PencilLemmaSInputs r) :
    H1CanonicalDilated r :=
  H1CanonicalDilated_of_pencilInclusion (pencilSpectralInclusionData_of_lemmaSInputs h)

/-- **The project target from scalar spectral inclusion and the six Lemma-S estimates for the
flattened linearization pencils.** -/
theorem GUEStrongConvergenceStatement_of_scalarSpectralInclusion_and_lemmaSInputs
    (hScalar : ScalarSpectralInclusion r) (h : PencilLemmaSInputs r) :
    GUEStrongConvergenceStatement r :=
  GUEStrongConvergenceStatement_of_scalarSpectralInclusion hScalar
    (H1CanonicalDilated_of_lemmaSInputs h)

end Main

end

end GUEStrongConvergence
