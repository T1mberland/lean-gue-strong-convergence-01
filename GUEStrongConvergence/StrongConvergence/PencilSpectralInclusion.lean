/-
# Pencil spectral inclusion: from the analytic estimates to `hH1`

This file assembles the spectral-exclusion lemma for the GUE pencil
(`Probability/CutoffExclusionGrowing.lean`,
`ae_eventually_spectrum_subset_pencil`) into the project's hypothesis statements.

## The two structural gaps that this file closes

1. **Indexing.**  `ae_eventually_spectrum_subset_pencil` is stated for matrices indexed by
   `Fin (card d * N)`, while the GUE pencil `guePencilMatrix` is a matrix indexed by
   `d × Fin N`.  We construct the canonical equivalence
   `pencilIndexEquiv : d × Fin N ≃ Fin (card d * N)` and prove that the Hermitian property,
   the real spectrum, the trace, and the continuous functional calculus are transported by
   the induced algebra equivalence.  In particular the normalized trace `normTrace` of the
   reindexed cfc is exactly the pencil normalized trace `guePencilNormTrace`, so the
   statistics `gueStatisticCfc f` of `Probability/LemmaVSmooth.lean` are literally the
   statistics appearing in Lemma S.

2. **Sample space.**  Lemma S is stated for a *single* probability space `Ω`, while the
   `N`-th GUE block of the pencil lives on `stdGaussian (EuclideanSpace ℝ (GUECoord ι N))`,
   which depends on `N`.  The project's `CommonSpace ι` carries all blocks simultaneously,
   and `gueMatrixOn x N i` is the `N`-th block.  Since the law of `x ↦ x N` is the standard
   Gaussian measure on the block, means, variances and `MemLp` statements transfer verbatim
   between the block and the common space.

## Main results

* `pencilIndexEquiv`, `reindexStarAlgEquiv`, `isHermitian_reindex_iff`,
  `spectrum_reindex`, `trace_reindex`, `cfc_reindex`;
* `normTrace_hermCfc_reindex` and `gueStatisticCfc_eq_normTrace_guePencilMatrixFinOn`:
  the Lemma-S statistic of the reindexed pencil is *literally* `gueStatisticCfc`;
* `guePencilMatrixOn`, `guePencilMatrixFinOn` — the affine pencil `A₀ ⊗ 1 + ∑ A_i ⊗ G_i`
  on the common space, in the `d × Fin N` and `Fin (card d * N)` index shapes;
* `integral_eval_commonGaussian`, `variance_eval_commonGaussian`,
  `memLp_eval_commonGaussian`, `integrable_eval_commonGaussian` — transport of the
  Lemma-S inputs from the `N`-th Gaussian block to the common space;
* `ae_eventually_spectrum_subset_guePencil` — **the concrete pencil spectral inclusion**,
  with the six Lemma-S inputs stated in terms of `gueStatisticCfc` over the block measures;
* `ae_eventually_spectrum_subset_commonSpace` — Lemma S for an arbitrary Hermitian family on
  the common space (the interface the `hH1` linearization pencils consume);
* `PencilSpectralInclusionData`, `H1CanonicalDilated_of_pencilInclusion` — the
  `hH1`-shaped reduction: the *only* remaining input is the per-index pencil spectral
  inclusion, and the countable intersection (over the dense Gaussian-rational family and
  rational parameters/radii) plus the rational-to-real lifting are proved.

## The residual inputs

Everything is an explicit hypothesis; nothing is assumed that is not part of the paper's
analytic estimates.

* For `ae_eventually_spectrum_subset_guePencil` these are exactly the six inputs of
  `ae_eventually_spectrum_subset_pencil`, in the project's terms:
  `hZ`/`hWint`/`hW0` (the `L²` and integrability side conditions),
  `hV` (= `lemmaS_V_input`, conditional on the cfc trace derivative `hderiv`),
  `hWb` (= `LemmaS_Wb`), and `hM` (the smooth mean comparison of Lemma M).
* For `H1CanonicalDilated_of_pencilInclusion` the remaining input is
  `PencilSpectralInclusionData r`: for every `(k, F, z, ε)` the a.e. eventual containment of
  the approximating linearization spectrum in the `ε`-neighbourhood of the limit spectrum.
  Closing it requires (a) flattening the linearization pencil
  `CStarMatrix (PenIdx wds) (PenIdx wds) (BlockAlg m n)` to `Matrix (Fin (card ...)) ℂ`
  (via `CStarMatrix.ofMatrixStarAlgEquiv`, `Matrix.compAlgEquiv` and `Matrix.reindexAlgEquiv`,
  all of which preserve the spectrum), and (b) applying
  `ae_eventually_spectrum_subset_commonSpace` to the flattened family with the six inputs for
  the *polynomial* statistic `τ_N(f(flattened penLCS))` — the non-affine analogue of the six
  inputs above.  Those matrices are polynomial, not affine, in the GUE blocks, so
  `gueStatisticCfc` does not apply to them directly; the six inputs must be stated for the
  flattened elements.

Note on instance graphs: `CStarMatrix` carries both the matrix-algebra instances and the
C⋆-algebra instances, and `spectrum ℝ` depends on which `Algebra ℝ` instance is used.
`SpectralFamilyInclusion` is stated in the C⋆-algebra graph; `specC` pins that graph down so
that all statements in the `hH1` reduction use it consistently.
-/
import GUEStrongConvergence.Probability.CutoffExclusionGrowing
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Transfer
import GUEStrongConvergence.Probability.LemmaVSmooth
import GUEStrongConvergence.Probability.CommonSpace
import GUEStrongConvergence.StrongConvergence.ConcreteTransfer
import GUEStrongConvergence.StrongConvergence.FinalWiring
import GUEStrongConvergence.StrongConvergence.DenseFamily
import GUEStrongConvergence.Linearization.PolynomialBridge
import GUEStrongConvergence.StrongConvergence.FromPencils

open Filter MeasureTheory ProbabilityTheory FreeProbability FreeProbability.Fock Matrix
open scoped BigOperators ComplexOrder ENNReal Pointwise Topology

namespace GUEStrongConvergence

noncomputable section

set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

/-! ## 1. Reindexing the pencil to `Matrix (Fin (card d * N))` -/

section Reindex

variable {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

/-- The canonical identification of the pencil index type `d × Fin N` with
`Fin (card d * N)`. -/
def pencilIndexEquiv (d : Type*) [Fintype d] (N : ℕ) :
    d × Fin N ≃ Fin (Fintype.card d * N) :=
  ((Fintype.equivFin d).prodCongr (Equiv.refl (Fin N))).trans finProdFinEquiv

/-- `Matrix.reindex` commutes with `star` (conjugate transpose). -/
lemma star_reindex (e : m ≃ n) (A : Matrix m m ℂ) :
    star (Matrix.reindex e e A) = Matrix.reindex e e (star A) := by
  rw [Matrix.star_eq_conjTranspose, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_reindex]

/-- The reindexing algebra equivalence of `ℂ`-matrices along an index equivalence; it is a
star algebra equivalence because reindexing commutes with the conjugate transpose. -/
def reindexStarAlgEquiv (e : m ≃ n) : Matrix m m ℂ ≃⋆ₐ[ℝ] Matrix n n ℂ :=
  StarAlgEquiv.ofAlgEquiv (Matrix.reindexAlgEquiv ℝ ℂ e) (fun M => star_reindex e M)

@[simp]
lemma reindexStarAlgEquiv_apply (e : m ≃ n) (M : Matrix m m ℂ) :
    reindexStarAlgEquiv e M = Matrix.reindex e e M := rfl

/-- The reindexing preserves the Hermitian property. -/
lemma isHermitian_reindex_iff (e : m ≃ n) (A : Matrix m m ℂ) :
    (Matrix.reindex e e A).IsHermitian ↔ A.IsHermitian := by
  constructor
  · intro h
    have h' : Matrix.reindex e e Aᴴ = Matrix.reindex e e A := by
      rw [← Matrix.conjTranspose_reindex]; exact h
    have h2 := congrArg (Matrix.reindex e.symm e.symm) h'
    simp only [Matrix.reindex_apply, Matrix.submatrix_submatrix,
      Equiv.symm_symm, Equiv.symm_comp_self, Matrix.submatrix_id_id] at h2
    exact h2
  · intro h
    show Matrix.reindex e e Aᴴ = Matrix.reindex e e A
    rw [h]

/-- The reindexing preserves self-adjointness. -/
lemma isSelfAdjoint_reindex_iff (e : m ≃ n) (A : Matrix m m ℂ) :
    IsSelfAdjoint (Matrix.reindex e e A) ↔ IsSelfAdjoint A := by
  rw [isSelfAdjoint_iff, isSelfAdjoint_iff, star_reindex]
  exact (Matrix.reindexAlgEquiv ℝ ℂ e).injective.eq_iff

/-- The reindexing preserves the real spectrum. -/
theorem spectrum_reindex (e : m ≃ n) (A : Matrix m m ℂ) :
    spectrum ℝ (Matrix.reindex e e A) = spectrum ℝ A :=
  AlgEquiv.spectrum_eq (Matrix.reindexAlgEquiv ℝ ℂ e) A

/-- The reindexing preserves the trace. -/
lemma trace_reindex (e : m ≃ n) (A : Matrix m m ℂ) :
    (Matrix.reindex e e A).trace = A.trace := by
  simp only [Matrix.trace, Matrix.reindex_apply]
  exact Equiv.sum_comp e.symm (fun i => A i i)

/-- The continuous functional calculus commutes with reindexing. -/
lemma cfc_reindex (e : m ≃ n) (f : ℝ → ℝ) (A : Matrix m m ℂ) :
    cfc f (Matrix.reindex e e A) = Matrix.reindex e e (cfc f A) := by
  let E : Matrix m m ℂ ≃⋆ₐ[ℝ] Matrix n n ℂ := reindexStarAlgEquiv e
  have hpq : ∀ x : Matrix m m ℂ, IsSelfAdjoint x ↔ IsSelfAdjoint (E x) :=
    fun x => (isSelfAdjoint_reindex_iff e x).symm
  have hcont : Continuous E := by
    have hlin : Continuous ((Matrix.reindexAlgEquiv ℝ ℂ e).toLinearEquiv :
        Matrix m m ℂ →ₗ[ℝ] Matrix n n ℂ) :=
      LinearMap.continuous_of_finiteDimensional _
    exact hlin
  have h := cfc_eq_cfc_transfer (p := IsSelfAdjoint) (q := IsSelfAdjoint)
    E hcont hpq f (E A)
  have hsymm : E.symm (E A) = A := E.symm_apply_apply A
  rw [hsymm] at h
  change cfc f (E A) = Matrix.reindex e e (cfc f A)
  rw [h]
  change Matrix.reindex e e (cfc f A) = Matrix.reindex e e (cfc f A)
  rfl

end Reindex

/-! ## 1b. The pencil statistic is the reindexed normalized trace -/

section PencilStatistic

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {d : Type*} [Fintype d] [DecidableEq d]

/-- The reindexed normalized trace of the cfc is the pencil normalized trace. -/
lemma normTrace_hermCfc_reindex {N : ℕ}
    (e : d × Fin N ≃ Fin (Fintype.card d * N)) (f : ℝ → ℝ)
    (P : Matrix (d × Fin N) (d × Fin N) ℂ)
    (hH : (Matrix.reindex e e P).IsHermitian) :
    normTrace (hermCfc (Matrix.reindex e e P) f hH) = guePencilNormTrace (cfc f P) := by
  have h1 : hermCfc (Matrix.reindex e e P) f hH = cfc f (Matrix.reindex e e P) := rfl
  rw [h1, cfc_reindex, normTrace, trace_reindex, guePencilNormTrace, gueNormConst]

/-- The affine GUE pencil on the common space, in the `d × Fin N` index shape. -/
def guePencilMatrixOn (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ) (x : CommonSpace ι) (N : ℕ) :
    Matrix (d × Fin N) (d × Fin N) ℂ :=
  guePencilMatrix A₀ A (WithLp.ofLp (x N))

/-- The affine GUE pencil reindexed to `Fin (card d * N)`, the shape of Lemma S. -/
def guePencilMatrixFinOn (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    (x : CommonSpace ι) (N : ℕ) :
    Matrix (Fin (Fintype.card d * N)) (Fin (Fintype.card d * N)) ℂ :=
  Matrix.reindex (pencilIndexEquiv d N) (pencilIndexEquiv d N) (guePencilMatrixOn A₀ A x N)

/-- The pencil on the common space is Hermitian. -/
lemma guePencilMatrixOn_isHermitian (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    (hA₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian) (x : CommonSpace ι) (N : ℕ) :
    (guePencilMatrixOn A₀ A x N).IsHermitian :=
  guePencilMatrix_isHermitian A₀ A hA₀ hA _

/-- The reindexed pencil is Hermitian. -/
lemma guePencilMatrixFinOn_isHermitian (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    (hA₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian) (x : CommonSpace ι) (N : ℕ) :
    (guePencilMatrixFinOn A₀ A x N).IsHermitian :=
  (isHermitian_reindex_iff _ _).mpr (guePencilMatrixOn_isHermitian A₀ A hA₀ hA x N)

/-- **The Lemma-S statistic is the pencil statistic.**  The normalized trace of the cfc of
the reindexed pencil is exactly `gueStatisticCfc f` at the `N`-th block of the common space. -/
lemma gueStatisticCfc_eq_normTrace_guePencilMatrixFinOn
    (f : ℝ → ℝ) (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    (hA₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian) (x : CommonSpace ι) (N : ℕ)
    (hP : (guePencilMatrixFinOn A₀ A x N).IsHermitian) :
    normTrace (hermCfc (guePencilMatrixFinOn A₀ A x N) f hP) =
      gueStatisticCfc (N := N) f A₀ A hA₀ hA (x N) := by
  have h1 : gueStatisticCfc (N := N) f A₀ A hA₀ hA (x N)
      = guePencilNormTrace (cfc f (guePencilMatrix A₀ A (WithLp.ofLp (x N)))) := by
    rw [gueStatisticCfc, guePencilCfc_eq_cfc]
  rw [h1]
  have h2 := normTrace_hermCfc_reindex (pencilIndexEquiv d N) f
    (guePencilMatrixOn A₀ A x N) hP
  simpa only [guePencilMatrixFinOn, guePencilMatrixOn] using h2

end PencilStatistic

/-! ## 2. Transport of the Lemma-S inputs from the block to the common space -/

section CommonSpaceTransport

variable {ι : Type*} [Fintype ι] {N : ℕ}

/-- Integrals of block statistics over the common space are block integrals. -/
lemma integral_eval_commonGaussian {g : EuclideanSpace ℝ (GUECoord ι N) → ℝ}
    (hg : AEStronglyMeasurable g (stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))) :
    ∫ x : CommonSpace ι, g (x N) ∂(commonGaussianMeasure ι) =
      ∫ y, g y ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) :=
  (hasLaw_eval_commonGaussian (ι := ι) N).integral_comp hg

/-- Variances of block statistics over the common space are block variances. -/
lemma variance_eval_commonGaussian {g : EuclideanSpace ℝ (GUECoord ι N) → ℝ}
    (hg : AEMeasurable g (stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))) :
    variance (fun x : CommonSpace ι => g (x N)) (commonGaussianMeasure ι) =
      variance g (stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) := by
  have hX := hasLaw_eval_commonGaussian (ι := ι) N
  have hmae : AEMeasurable g ((commonGaussianMeasure ι).map (fun x : CommonSpace ι => x N)) := by
    rw [hX.map_eq]; exact hg
  have h := variance_map (X := g) (Y := fun x : CommonSpace ι => x N) hmae hX.aemeasurable
  rw [hX.map_eq] at h
  exact h.symm

/-- `MemLp` of a block statistic transfers to the common space. -/
lemma memLp_eval_commonGaussian {g : EuclideanSpace ℝ (GUECoord ι N) → ℝ} {p : ℝ≥0∞}
    (hg : MemLp g p (stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))) :
    MemLp (fun x : CommonSpace ι => g (x N)) p (commonGaussianMeasure ι) :=
  (hasLaw_eval_commonGaussian (ι := ι) N).memLp_comp hg

/-- Integrability of a block statistic transfers to the common space. -/
lemma integrable_eval_commonGaussian {g : EuclideanSpace ℝ (GUECoord ι N) → ℝ}
    (hg : Integrable g (stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))) :
    Integrable (fun x : CommonSpace ι => g (x N)) (commonGaussianMeasure ι) :=
  (hasLaw_eval_commonGaussian (ι := ι) N).integrable_comp hg

end CommonSpaceTransport

/-! ## 2b. The concrete pencil spectral inclusion

The six inputs of `ae_eventually_spectrum_subset_pencil` are stated below in the project's
own terms: `Z_N = gueStatisticCfc f` and `W_N = gueStatisticCfc (fun y => (deriv f y) ^ 2)`,
with the means and variances taken over the `N`-th Gaussian block (the measure on which the
analytic estimates `lemmaS_V_input`, `LemmaS_Wb` and Lemma M are proved). -/

section PencilSpectralInclusion

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {d : Type*} [Fintype d] [DecidableEq d] [Nonempty d]

/-- **Spectral inclusion for the GUE pencil.**  Let `A₀, A_i` be Hermitian coefficient
matrices, `S ⊆ ℝ`, `ε > 0`, and `f ≥ 0` a cutoff equal to `1` outside `S + (-ε, ε)`.
Assume the six Lemma-S inputs for the pencil statistics

`Z_N = tau_N(f(H_N))`, `W_N = tau_N((f')²(H_N))`,

namely the `L²`/integrability side conditions and the mean/variance bounds with constants
`C, C'`.  Then almost surely, for all sufficiently large `N`, every real spectral value of
the reindexed pencil `Fin (card d * N)` lies in `S + (-ε, ε)`.

The reindexing is `pencilIndexEquiv`, and the statistics above are *literally* the Lemma-S
statistics by `gueStatisticCfc_eq_normTrace_guePencilMatrixFinOn`. -/
theorem ae_eventually_spectrum_subset_guePencil
    (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    (hA₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian)
    {S : Set ℝ} {ε : ℝ} (hε : 0 < ε)
    {f : ℝ → ℝ} (hf0 : ∀ x, 0 ≤ f x)
    (hf1 : ∀ x, x ∉ S + Set.Ioo (-ε) ε → f x = 1)
    {C C' : ℝ} (hC : 0 ≤ C) (hC' : 0 ≤ C')
    (hZ : ∀ N : ℕ, MemLp (gueStatisticCfc (N := N) f A₀ A hA₀ hA) 2
      (stdGaussian (EuclideanSpace ℝ (GUECoord ι N))))
    (hWint : ∀ N : ℕ, Integrable
      (gueStatisticCfc (N := N) (fun y => (deriv f y) ^ 2) A₀ A hA₀ hA)
      (stdGaussian (EuclideanSpace ℝ (GUECoord ι N))))
    (hW0 : ∀ N : ℕ, 0 ≤ ∫ x,
      gueStatisticCfc (N := N) (fun y => (deriv f y) ^ 2) A₀ A hA₀ hA x
        ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N))))
    (hM : ∀ᶠ N : ℕ in atTop, |∫ x,
      gueStatisticCfc (N := N) f A₀ A hA₀ hA x
        ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))| ≤ C / (N : ℝ) ^ 2)
    (hV : ∀ N : ℕ, variance (gueStatisticCfc (N := N) f A₀ A hA₀ hA)
        (stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))
      ≤ C / (N : ℝ) ^ 2 * ∫ x,
          gueStatisticCfc (N := N) (fun y => (deriv f y) ^ 2) A₀ A hA₀ hA x
            ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N))))
    (hWb : ∀ N : ℕ, ∫ x,
      gueStatisticCfc (N := N) (fun y => (deriv f y) ^ 2) A₀ A hA₀ hA x
        ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) ≤ C' / (N : ℝ) ^ 2) :
    ∀ᵐ x ∂(commonGaussianMeasure ι), ∀ᶠ N : ℕ in atTop,
      spectrum ℝ (guePencilMatrixFinOn A₀ A x N) ⊆ S + Set.Ioo (-ε) ε := by
  classical
  set H : (N : ℕ) → CommonSpace ι →
      Matrix (Fin (Fintype.card d * N)) (Fin (Fintype.card d * N)) ℂ :=
    fun N x => guePencilMatrixFinOn A₀ A x N with hHdef
  have hH : ∀ N x, (H N x).IsHermitian :=
    fun N x => guePencilMatrixFinOn_isHermitian A₀ A hA₀ hA x N
  have hstatZ : ∀ (N : ℕ) (x : CommonSpace ι),
      normTrace (hermCfc (H N x) f (hH N x)) =
        gueStatisticCfc (N := N) f A₀ A hA₀ hA (x N) :=
    fun N x => gueStatisticCfc_eq_normTrace_guePencilMatrixFinOn f A₀ A hA₀ hA x N (hH N x)
  have hstatW : ∀ (N : ℕ) (x : CommonSpace ι),
      normTrace (hermCfc (H N x) (fun y => (deriv f y) ^ 2) (hH N x)) =
        gueStatisticCfc (N := N) (fun y => (deriv f y) ^ 2) A₀ A hA₀ hA (x N) :=
    fun N x => gueStatisticCfc_eq_normTrace_guePencilMatrixFinOn
      (fun y => (deriv f y) ^ 2) A₀ A hA₀ hA x N (hH N x)
  have hZe : ∀ N, (fun x : CommonSpace ι => normTrace (hermCfc (H N x) f (hH N x)))
      = fun x => gueStatisticCfc (N := N) f A₀ A hA₀ hA (x N) :=
    fun N => funext (hstatZ N)
  have hWe : ∀ N, (fun x : CommonSpace ι =>
        normTrace (hermCfc (H N x) (fun y => (deriv f y) ^ 2) (hH N x)))
      = fun x => gueStatisticCfc (N := N) (fun y => (deriv f y) ^ 2) A₀ A hA₀ hA (x N) :=
    fun N => funext (hstatW N)
  refine ae_eventually_spectrum_subset_pencil (d := d) (Ω := CommonSpace ι)
    (μ := commonGaussianMeasure ι) (S := S) (ε := ε) (f := f) (C := C) (C' := C')
    hε hf0 hf1 H hH hC hC' ?_ ?_ ?_ ?_ ?_ ?_
  · intro N
    rw [hZe N]
    exact memLp_eval_commonGaussian (hZ N)
  · intro N
    rw [hWe N]
    exact integrable_eval_commonGaussian (hWint N)
  · intro N
    rw [hWe N, integral_eval_commonGaussian (hWint N).aestronglyMeasurable]
    exact hW0 N
  · filter_upwards [hM] with N hN
    rw [hZe N, integral_eval_commonGaussian (hZ N).aestronglyMeasurable]
    exact hN
  · filter_upwards with N
    have hmeasZ : AEMeasurable (gueStatisticCfc (N := N) f A₀ A hA₀ hA)
        (stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) :=
      aestronglyMeasurable_iff_aemeasurable.mp (hZ N).aestronglyMeasurable
    rw [hZe N, hWe N, variance_eval_commonGaussian (N := N) hmeasZ,
      integral_eval_commonGaussian (hWint N).aestronglyMeasurable]
    exact hV N
  · filter_upwards with N
    rw [hWe N, integral_eval_commonGaussian (hWint N).aestronglyMeasurable]
    exact hWb N

end PencilSpectralInclusion

/-! ## 2c. Lemma S on the common Gaussian space (general Hermitian families)

The H1 reduction below consumes a spectral inclusion for the *linearization pencils*
`penLCS`, which are polynomial (not affine) in the GUE blocks.  The following wrapper makes
`ae_eventually_spectrum_subset_pencil` directly applicable to any Hermitian family on the
common space, so the six inputs can be supplied for those matrices without repeating the
probability argument. -/

section CommonSpaceLemmaS

variable {ι : Type*} [Fintype ι]

/-- **Lemma S on the common Gaussian space.**  Every Hermitian matrix family on the common
space satisfies the spectral exclusion as soon as the six Lemma-S inputs (with means,
variances and `MemLp`/integrability all over `commonGaussianMeasure`) hold and the
dimension grows at most linearly. -/
theorem ae_eventually_spectrum_subset_commonSpace
    {m : ℕ → ℕ} (hm : ∀ᶠ N in atTop, 0 < m N)
    {S : Set ℝ} {ε : ℝ} (hε : 0 < ε)
    {f : ℝ → ℝ} (hf0 : ∀ x, 0 ≤ f x)
    (hf1 : ∀ x, x ∉ S + Set.Ioo (-ε) ε → f x = 1)
    (H : (N : ℕ) → CommonSpace ι → Matrix (Fin (m N)) (Fin (m N)) ℂ)
    (hH : ∀ N x, (H N x).IsHermitian)
    {C C' D : ℝ} (hC : 0 ≤ C) (hC' : 0 ≤ C') (hD : 0 ≤ D)
    (hmD : ∀ᶠ N in atTop, (m N : ℝ) ≤ D * (N : ℝ))
    (hZ : ∀ N, MemLp (fun x => normTrace (hermCfc (H N x) f (hH N x))) 2
      (commonGaussianMeasure ι))
    (hWint : ∀ N, Integrable
      (fun x => normTrace (hermCfc (H N x) (fun y => (deriv f y) ^ 2) (hH N x)))
      (commonGaussianMeasure ι))
    (hW0 : ∀ N, 0 ≤ ∫ x,
      normTrace (hermCfc (H N x) (fun y => (deriv f y) ^ 2) (hH N x))
        ∂(commonGaussianMeasure ι))
    (hM : ∀ᶠ N : ℕ in atTop,
      |∫ x, normTrace (hermCfc (H N x) f (hH N x)) ∂(commonGaussianMeasure ι)|
        ≤ C / (N : ℝ) ^ 2)
    (hV : ∀ᶠ N in atTop, variance (fun x => normTrace (hermCfc (H N x) f (hH N x)))
        (commonGaussianMeasure ι)
      ≤ C / (N : ℝ) ^ 2 * ∫ x,
          normTrace (hermCfc (H N x) (fun y => (deriv f y) ^ 2) (hH N x))
            ∂(commonGaussianMeasure ι))
    (hWb : ∀ᶠ N in atTop, ∫ x,
      normTrace (hermCfc (H N x) (fun y => (deriv f y) ^ 2) (hH N x))
        ∂(commonGaussianMeasure ι) ≤ C' / (N : ℝ) ^ 2) :
    ∀ᵐ x ∂(commonGaussianMeasure ι), ∀ᶠ N : ℕ in atTop,
      spectrum ℝ (H N x) ⊆ S + Set.Ioo (-ε) ε :=
  ae_eventually_spectrum_subset_growing (μ := commonGaussianMeasure ι) hm hε hf0 hf1 H hH
    hC hC' hD hmD hZ hWint hW0 hM hV hWb

end CommonSpaceLemmaS

/-! ## 3. The `hH1`-shaped reduction

`H1CanonicalDilated r` (`StrongConvergence/FinalWiring.lean`) is the spectral family inclusion
for the linearization pencils of every canonical dilated Gaussian-rational polynomial.
We isolate the *per-index spectral inclusion* as the only remaining input and prove that it
implies `H1CanonicalDilated r`; this is the countable-intersection plus rational-to-real
parameter lifting step. -/

section H1Reduction

variable {r : ℕ}

local instance : Nontrivial (closedSemicircularAlgebra (Fin r)) :=
  (closedGeneratedVacuumState (Fin r)).toProbabilitySpace.nontrivial

local instance : PartialOrder (closedSemicircularAlgebra (Fin r)) :=
  CStarAlgebra.spectralOrder _

local instance : StarOrderedRing (closedSemicircularAlgebra (Fin r)) :=
  CStarAlgebra.spectralOrderedRing _

/-- The matrix polynomial of the `F`-th member of the countable dense family at coefficient
dimension `(k+1) + (k+1)` (the Hermitian-dilation doubling). -/
def h1Poly (r k : ℕ) (F : RatPolyIdx r (k + 1)) :
    Matrix (Fin ((k + 1) + (k + 1))) (Fin ((k + 1) + (k + 1)))
      (WordPolynomial ℂ (Fin r)) :=
  dilationPolyFin (denseFamily r (k + 1) F)

/-- The ambient algebra of the approximating linearization pencils. -/
abbrev h1An (r k : ℕ) (F : RatPolyIdx r (k + 1)) (n : ℕ) : Type _ :=
  CStarMatrix (PenIdx (polyW (h1Poly r k F))) (PenIdx (polyW (h1Poly r k F)))
    (BlockAlg ((k + 1) + (k + 1)) n)

/-- The ambient algebra of the limiting linearization pencils. -/
abbrev h1Alim (r k : ℕ) (F : RatPolyIdx r (k + 1)) : Type _ :=
  CStarMatrix (PenIdx (polyW (h1Poly r k F))) (PenIdx (polyW (h1Poly r k F)))
    (BlockLimit r ((k + 1) + (k + 1)))

/-- The approximating linearization pencil of the `F`-th canonical dilated polynomial, at
block size `n + 1` and pencil parameter `z`. -/
def h1PencilApprox (r k : ℕ) (F : RatPolyIdx r (k + 1)) (x : CommonSpace (Fin r))
    (n : ℕ) (z : ℝ) : h1An r k F n :=
  penLCS (blockGUE r ((k + 1) + (k + 1)) x n) (polyW (h1Poly r k F))
    (fun j => (1 / 2 : ℂ) • polyCoeff
      (A := CStarMatrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (h1Poly r k F) j)
    (0 : BlockAlg ((k + 1) + (k + 1)) n) z

/-- The limiting linearization pencil of the `F`-th canonical dilated polynomial. -/
def h1PencilLimit (r k : ℕ) (F : RatPolyIdx r (k + 1)) (z : ℝ) : h1Alim r k F :=
  penLCS (blockSemicircular r ((k + 1) + (k + 1))) (polyW (h1Poly r k F))
    (fun j => (1 / 2 : ℂ) • polyCoeff
      (A := closedSemicircularAlgebra (Fin r)) (h1Poly r k F) j)
    (0 : BlockLimit r ((k + 1) + (k + 1))) z

/-- The real spectrum in the C⋆-algebra instance graph.  `SpectralFamilyInclusion`
(`StrongConvergence/Transfer.lean`) is stated for the instances of the local `CStarAlgebra`
hypothesis; the type synonym `CStarMatrix` also carries the matrix-algebra instances, so we
pin down the C⋆-algebra graph explicitly to keep all statements in the same graph. -/
noncomputable def specC {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    (a : A) : Set ℝ :=
  spectrum ℝ a

/-- The approximating linearization pencil is self-adjoint. -/
lemma h1PencilApprox_isSelfAdjoint (r k : ℕ) (F : RatPolyIdx r (k + 1))
    (x : CommonSpace (Fin r)) (n : ℕ) (z : ℝ) :
    IsSelfAdjoint (h1PencilApprox r k F x n z) :=
  penLCS_isSelfAdjoint _ _ _
    (IsSelfAdjoint.zero (BlockAlg ((k + 1) + (k + 1)) n) :
      IsSelfAdjoint (0 : BlockAlg ((k + 1) + (k + 1)) n)) z

/-- The limiting linearization pencil is self-adjoint. -/
lemma h1PencilLimit_isSelfAdjoint (r k : ℕ) (F : RatPolyIdx r (k + 1)) (z : ℝ) :
    IsSelfAdjoint (h1PencilLimit r k F z) :=
  penLCS_isSelfAdjoint _ _ _
    (IsSelfAdjoint.zero (BlockLimit r ((k + 1) + (k + 1))) :
      IsSelfAdjoint (0 : BlockLimit r ((k + 1) + (k + 1)))) z

/-- The approximating pencils are `1`-Lipschitz in the parameter. -/
lemma h1PencilApprox_sub_norm_le (r k : ℕ) (F : RatPolyIdx r (k + 1))
    (x : CommonSpace (Fin r)) (n : ℕ) (z z' : ℝ) :
    ‖h1PencilApprox r k F x n z - h1PencilApprox r k F x n z'‖ ≤ |z - z'| :=
  penLCS_sub_norm_le _ _ _ _ z z'

/-- The limiting pencils are `1`-Lipschitz in the parameter. -/
lemma h1PencilLimit_sub_norm_le (r k : ℕ) (F : RatPolyIdx r (k + 1)) (z z' : ℝ) :
    ‖h1PencilLimit r k F z - h1PencilLimit r k F z'‖ ≤ |z - z'| :=
  penLCS_sub_norm_le _ _ _ _ z z'

/-- **Hausdorff--Lipschitz continuity of the real spectrum** in the `specC` instance graph:
for self-adjoint `a, b`, every real spectral value of `a` is within `‖a - b‖` of one of `b`. -/
lemma specC_spectrum_close {A : Type*} [CStarAlgebra A] [Nontrivial A] [PartialOrder A]
    [StarOrderedRing A] {a b : A} (ha : IsSelfAdjoint a) (hb : IsSelfAdjoint b)
    {lam : ℝ} (hlam : lam ∈ specC a) :
    ∃ mu ∈ specC b, |lam - mu| ≤ ‖a - b‖ := by
  rw [specC] at hlam ⊢
  exact exists_spectrum_close_of_norm_sub_le ha hb hlam

/-- The rational-parameter spectral inclusion predicate for a fixed `(k, F, x, n)`. -/
def h1PencilInclusionAt (r : ℕ) (x : CommonSpace (Fin r)) (n : ℕ)
    (k : ℕ) (F : RatPolyIdx r (k + 1)) (zq εq : ℚ) : Prop :=
  0 < (εq : ℝ) →
    specC (h1PencilApprox r k F x n (zq : ℝ)) ⊆
      specC (h1PencilLimit r k F (zq : ℝ)) + Set.Ioo (-(εq : ℝ)) (εq : ℝ)

/-- **Rational to real lifting of the pencil spectral inclusion.**  If the approximating
spectrum is eventually contained in the `εq`-neighbourhood of the limit spectrum for every
rational parameter and radius, then the same holds for every real parameter and radius. -/
lemma h1PencilInclusion_lift {r k : ℕ} {F : RatPolyIdx r (k + 1)} {x : CommonSpace (Fin r)}
    (hx : ∀ (zq εq : ℚ), 0 < (εq : ℝ) →
      ∀ᶠ n : ℕ in atTop,
        specC (h1PencilApprox r k F x n (zq : ℝ)) ⊆
          specC (h1PencilLimit r k F (zq : ℝ)) + Set.Ioo (-(εq : ℝ)) (εq : ℝ)) :
    ∀ z : ℝ, ∀ ε > 0, ∀ᶠ n : ℕ in atTop,
      ∀ a ∈ specC (h1PencilApprox r k F x n z),
        ∃ b ∈ specC (h1PencilLimit r k F z), |a - b| ≤ ε := by
  intro z ε hε
  obtain ⟨zq, hzq1, hzq2⟩ := exists_rat_btwn (show z < z + ε / 4 by linarith)
  have hclose : |z - (zq : ℝ)| < ε / 4 := by
    rw [abs_sub_comm, abs_of_pos (by linarith : (0 : ℝ) < (zq : ℝ) - z)]
    linarith
  have hquarter : (0 : ℝ) < ε / 4 := by positivity
  obtain ⟨εq, hεq0, hεq4⟩ := exists_rat_btwn hquarter
  filter_upwards [hx zq εq hεq0] with n hn
  intro a ha
  -- move the eigenvalue to the rational parameter
  obtain ⟨a', ha', haa'⟩ := specC_spectrum_close
    (h1PencilApprox_isSelfAdjoint r k F x n z)
    (h1PencilApprox_isSelfAdjoint r k F x n (zq : ℝ)) ha
  have haa'' : |a - a'| ≤ ε / 4 :=
    haa'.trans (le_trans (h1PencilApprox_sub_norm_le r k F x n z (zq : ℝ)) hclose.le)
  -- the rational-parameter inclusion, giving a limit spectral value close to `a'`
  obtain ⟨b', hb', c, hc, hbc⟩ := Set.mem_add.mp (hn ha')
  have ha'b' : |a' - b'| ≤ (εq : ℝ) := by
    rw [show a' - b' = c by rw [← hbc]; ring]
    exact abs_le.mpr ⟨le_of_lt hc.1, le_of_lt hc.2⟩
  -- move the limit spectral value back to the real parameter
  obtain ⟨b, hb, hb'b⟩ := specC_spectrum_close
    (h1PencilLimit_isSelfAdjoint r k F (zq : ℝ))
    (h1PencilLimit_isSelfAdjoint r k F z) hb'
  have hb'b' : |b' - b| ≤ ε / 4 := by
    refine hb'b.trans ?_
    have h := h1PencilLimit_sub_norm_le r k F (zq : ℝ) z
    rw [abs_sub_comm] at h
    exact h.trans hclose.le
  refine ⟨b, hb, ?_⟩
  calc |a - b| ≤ |a - a'| + |a' - b'| + |b' - b| := by
        rw [show a - b = (a - a') + (a' - b') + (b' - b) by ring]
        exact (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ ε / 4 + (εq : ℝ) + ε / 4 := by linarith
    _ ≤ ε := by linarith

/-- **The per-index spectral inclusion data for `hH1`**: at every real pencil parameter and
every `ε > 0`, almost surely the approximating spectrum is eventually contained in the
`ε`-neighbourhood of the limit spectrum. -/
def PencilSpectralInclusionData (r : ℕ) : Prop :=
  ∀ (k : ℕ) (F : RatPolyIdx r (k + 1)) (z : ℝ) (ε : ℝ), 0 < ε →
    ∀ᵐ x ∂(commonGaussianMeasure (Fin r)), ∀ᶠ n : ℕ in atTop,
      specC (h1PencilApprox r k F x n z) ⊆
        specC (h1PencilLimit r k F z) + Set.Ioo (-ε) ε

/-- **`hH1` from the per-index pencil spectral inclusion.**  The only remaining input is
`PencilSpectralInclusionData r`; the countable intersection over the dense family (with
rational parameters and radii) and the rational-to-real parameter lifting are proved here,
using `ae_all_forall_eventually` and `h1PencilInclusion_lift`. -/
theorem H1CanonicalDilated_of_pencilInclusion
    (h : PencilSpectralInclusionData r) :
    H1CanonicalDilated r := by
  classical
  have hstep : ∀ i : (Σ k : ℕ, RatPolyIdx r (k + 1) × ℚ × ℚ),
      ∀ᵐ x ∂(commonGaussianMeasure (Fin r)), ∀ᶠ n : ℕ in atTop,
        h1PencilInclusionAt r x n i.1 i.2.1 i.2.2.1 i.2.2.2 := by
    rintro ⟨k, F, zq, εq⟩
    by_cases hpos : (0 : ℝ) < (εq : ℝ)
    · filter_upwards [h k F (zq : ℝ) (εq : ℝ) hpos] with x hx
      exact hx.mono fun n hn _ => hn
    · filter_upwards with x
      filter_upwards with n hn
      exact absurd hn hpos
  have hall := ae_all_forall_eventually (μ := commonGaussianMeasure (Fin r))
    (p := fun (i : Σ k : ℕ, RatPolyIdx r (k + 1) × ℚ × ℚ) (x : CommonSpace (Fin r))
        (n : ℕ) => h1PencilInclusionAt r x n i.1 i.2.1 i.2.2.1 i.2.2.2) hstep
  filter_upwards [hall] with x hx
  intro k F
  exact h1PencilInclusion_lift (fun zq εq hq =>
    (hx ⟨k, F, zq, εq⟩).mono fun n hn => hn hq)

end H1Reduction

end

end GUEStrongConvergence

