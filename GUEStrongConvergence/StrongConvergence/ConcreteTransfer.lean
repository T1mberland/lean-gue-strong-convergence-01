/-
# Concrete assembly of the strong-convergence transfer for GUE

This file instantiates the abstract transfer of `StrongConvergence/Transfer.lean` with the
concrete GUE/semicircle data at a *fixed* matrix-coefficient dimension.

## Conventions

* `BlockAlg d n := M_d(M_{n+1}(ℂ))` is the varying approximating C⋆-algebra; we index by
  `n+1` so that the matrix dimension is always positive (the `N = 0` term of the final
  sequence is irrelevant for a limit along `atTop`).
* `BlockLimit r d := M_d(A_r)` with `A_r` the norm-closed semicircular algebra; the
  canonical spectral order is installed locally.
* `blockGUE` and `blockSemicircular` are the block-scalar generators `1_d ⊗ G_i` and
  `1_d ⊗ s_i`; the word list `wds` and the block coefficients `coeffn`, `coeffinf` are
  supplied by the caller together with the algebraic identification `hP` between the
  pencil polynomial `C + q + q^*` and the matrix-polynomial evaluation.

## Results

* `tendsto_norm_evalMatrixPoly_of_data`: the per-sample transfer.  The concrete states
  `ψ n = tr_d ⊗ tr_{n+1}` and `φ = tr_d ⊗ τ` are instantiated, and the transfer's moment
  hypothesis `hmom` is *proved* from scalar word-trace convergence `hWordsx` using
  `tendsto_matrixStarState_moment` and the concrete word identification of
  `ConcreteStates`; self-adjointness of `C + q + q^*` is derived from `IsSelfAdjoint C`.
* `ae_tendsto_norm_evalMatrixPoly`: the almost-sure capstone with explicit pencil data,
  `hP`, `hPinf`, `hH1` and `hB` (the hypotheses are the analytic inputs, not the
  conclusion).
* `ae_tendsto_norm_evalMatrixPoly_of_forall_ae`: the same with word convergence given word
  by word (`ae_all_iff` merges the countably many events).
* `wordPolyEval_blockDiag_eq_evalMatrixPoly`: the block identification, with block
  coefficients `A_w ⊗ 1` given by `polyCoeff` and block-scalar generators `1_d ⊗ g_i`.
* `wordPolyEvalC_zero_half_eq` and `ae_tendsto_norm_evalMatrixPoly_selfAdjoint`: the
  canonical pencil data `C = 0`, `q = (1/2) P(g)`, for which the identification with
  `evalMatrixPoly P g` is proved from self-adjointness of the evaluation.

## Remaining inputs

The spectral family inclusion `hH1` and the uniform bound `hB` are analytic inputs (the
deterministic spectral transfer and the probabilistic edge estimate); they are not derived
here.  For a non-self-adjoint `P` the reduction to the self-adjoint case would go through
`HermitianDilation.hermDilation`; the abstract identity `hermDilation_norm_eq` requires the
block-diagonal max-norm rule for the `CStarMatrix` norm, which is not available in the
pinned Mathlib, so that step is not taken here.
-/
import GUEStrongConvergence.StrongConvergence.Transfer
import GUEStrongConvergence.StrongConvergence.ConcreteStates
import GUEStrongConvergence.StrongConvergence.StateMomentComposition
import FreeProbability.Matrix.NormalizedTrace
import FreeProbability.Fock.ClosedGeneratedState

noncomputable section

namespace GUEStrongConvergence

set_option linter.unusedSectionVars false

open Filter MeasureTheory FreeProbability FreeProbability.Fock Matrix
open scoped ComplexOrder Topology

variable {r d : ℕ}

/-- The varying block algebra `M_d(M_{N}(ℂ))`, indexed by `n` with `N = n + 1`. -/
abbrev BlockAlg (d n : ℕ) : Type _ :=
  CStarMatrix (Fin d) (Fin d) (CStarMatrix (Fin (n + 1)) (Fin (n + 1)) ℂ)

/-- The limit block algebra `M_d(A_r)`, with `A_r` the closed semicircular algebra. -/
abbrev BlockLimit (r d : ℕ) : Type _ :=
  CStarMatrix (Fin d) (Fin d) (closedSemicircularAlgebra (Fin r))

/-- The block-diagonal (or "scalar") embedding `a ↦ 1_d ⊗ a`. -/
def blockDiag {A : Type*} [Zero A] {d : ℕ} (a : A) : CStarMatrix (Fin d) (Fin d) A :=
  CStarMatrix.ofMatrix fun i j => if i = j then a else 0

/-- The block-scalar GUE generators `1_d ⊗ G_i` in the varying algebras. -/
def blockGUE (r : ℕ) (d : ℕ) (x : CommonSpace (Fin r)) (n : ℕ) : Fin r → BlockAlg d n :=
  fun i => blockDiag (gueFamily r (n + 1) x i)

/-- The block-scalar semicircular generators `1_d ⊗ s_i` in the limit algebra. -/
def blockSemicircular (r d : ℕ) : Fin r → BlockLimit r d :=
  fun i => blockDiag (semicircularFamily r i)

/-- The limiting free joint word moment `τ(w)`. -/
def tau (r : ℕ) (w : List (Fin r)) : ℂ :=
  (closedGeneratedVacuumState (Fin r)).expectation (wordProd (semicircularFamily r) w)

section Concrete

variable [Nonempty (Fin d)]

local instance : Nontrivial (closedSemicircularAlgebra (Fin r)) :=
  (closedGeneratedVacuumState (Fin r)).toProbabilitySpace.nontrivial

local instance : PartialOrder (closedSemicircularAlgebra (Fin r)) :=
  CStarAlgebra.spectralOrder _

local instance : StarOrderedRing (closedSemicircularAlgebra (Fin r)) :=
  CStarAlgebra.spectralOrderedRing _

/-- `C + q + q^*` is self-adjoint whenever `C` is. -/
lemma isSelfAdjoint_wordPolyEvalC
    {B : Type*} [CStarAlgebra B] [Nontrivial B] [PartialOrder B] [StarOrderedRing B]
    {I κ : Type*} [Fintype κ] [DecidableEq κ]
    (C : B) (x : I → B) (wds : κ → List I) (coeff : κ → B)
    (hC : IsSelfAdjoint C) :
    IsSelfAdjoint (wordPolyEvalC C x wds coeff) := by
  unfold wordPolyEvalC IsSelfAdjoint
  rw [star_add, star_add, star_star, hC.star_eq]
  abel

/-- Block-diagonal matrices are scalar matrices. -/
lemma blockDiag_eq_scalar {A : Type*} [Semiring A] {d : ℕ} (a : A) :
    blockDiag (d := d) a = Matrix.scalar (Fin d) a := rfl

/-- Scalar-matrix word products are scalar matrices over the scalar word product. -/
lemma wordProd_blockDiag {A : Type*} [Ring A] {I : Type*} {d : ℕ}
    (g : I → A) (w : List I) :
    wordProd (fun i => blockDiag (d := d) (g i)) w
      = blockDiag (d := d) (wordProd g w) := by
  change wordProd (fun i => Matrix.scalar (Fin d) (g i)) w
    = Matrix.scalar (Fin d) (wordProd g w)
  exact wordProd_scalar g w

/-- **Block identification.** Evaluating the matrix of word polynomials with block
coefficients `A_w ⊗ 1` and block-scalar generators `1_d ⊗ g_i` gives exactly the
entrywise matrix-polynomial evaluation. -/
lemma wordPolyEval_blockDiag_eq_evalMatrixPoly
    {A : Type*} [CStarAlgebra A] [Nontrivial A] [PartialOrder A] [StarOrderedRing A]
    (P : Matrix (Fin d) (Fin d) (WordPolynomial ℂ (Fin r))) (g : Fin r → A) :
    wordPolyEval (fun i => blockDiag (d := d) (g i)) (polyW P)
        (fun k => polyCoeff (A := A) P k)
      = evalMatrixPoly P g := by
  have hmat : matWordEval g (polyW P) (fun k => polyCoeff (A := A) P k)
      = evalMatrixPoly P g := by
    rw [← matWordEval_eq_evaluate_support (A := A) P g]
    rfl
  rw [← hmat]
  unfold matWordEval wordPolyEval
  exact Finset.sum_congr rfl fun k _ => by
    rw [wordProd_blockDiag]
    rfl

/-- Scalar multiples of the coefficients are scalar multiples of the evaluation. -/
lemma wordPolyEval_smul_coeff
    {B : Type*} [CStarAlgebra B] [Nontrivial B] [PartialOrder B] [StarOrderedRing B]
    {I κ : Type*} [Fintype κ] [DecidableEq κ]
    (X : I → B) (wds : κ → List I) (coeff : κ → B) (c : ℂ) :
    wordPolyEval X wds (fun k => c • coeff k) = c • wordPolyEval X wds coeff := by
  simp only [wordPolyEval, Finset.smul_sum]
  exact Finset.sum_congr rfl fun k _ => smul_mul_assoc c (coeff k) _

/-- The star of a half multiple. -/
lemma star_half_smul {B : Type*} [CStarAlgebra B] (a : B) :
    star ((1 / 2 : ℂ) • a) = (1 / 2 : ℂ) • star a := by
  rw [star_smul]
  norm_num

/-- **Canonical pencil polynomial for a self-adjoint evaluation**: with `C = 0` and
`q = (1/2) P(g)`, the pencil polynomial `C + q + q^*` equals `P(g)`. -/
lemma wordPolyEvalC_zero_half_eq
    {A : Type*} [CStarAlgebra A] [Nontrivial A] [PartialOrder A] [StarOrderedRing A]
    (P : Matrix (Fin d) (Fin d) (WordPolynomial ℂ (Fin r))) (g : Fin r → A)
    (hsa : IsSelfAdjoint (evalMatrixPoly P g)) :
    wordPolyEvalC (0 : CStarMatrix (Fin d) (Fin d) A)
        (fun i => blockDiag (d := d) (g i)) (polyW P)
        (fun k => (1 / 2 : ℂ) • polyCoeff (A := A) P k)
      = evalMatrixPoly P g := by
  unfold wordPolyEvalC
  rw [zero_add]
  have hq1 : wordPolyEval (fun i => blockDiag (d := d) (g i)) (polyW P)
        (fun k => (1 / 2 : ℂ) • polyCoeff (A := A) P k)
      = (1 / 2 : ℂ) • wordPolyEval (fun i => blockDiag (d := d) (g i)) (polyW P)
          (fun k => polyCoeff (A := A) P k) := by
    unfold wordPolyEval
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun k _ =>
      smul_mul_assoc (1 / 2 : ℂ) (polyCoeff (A := A) P k) _
  have hq : wordPolyEval (fun i => blockDiag (d := d) (g i)) (polyW P)
        (fun k => (1 / 2 : ℂ) • polyCoeff (A := A) P k)
      = (1 / 2 : ℂ) • evalMatrixPoly P g := by
    rw [hq1, wordPolyEval_blockDiag_eq_evalMatrixPoly]
  rw [hq, star_half_smul, hsa.star_eq]
  rw [← add_smul, show (1 / 2 : ℂ) + 1 / 2 = 1 by norm_num, one_smul]

/-- **Per-sample transfer for matrix polynomials, conditional on the pencil data.**

The states `ψ n = tr_d ⊗ tr_{n+1}` and `φ = tr_d ⊗ τ` are concrete, and the moment
hypothesis `hmom` of the abstract transfer is discharged from scalar word-trace
convergence `hWordsx` by `tendsto_matrixStarState_moment`.  The pencil data
`(wds, coeffn, coeffinf, Cn, Cinf)` and the identifications `hP`, `hPinf` with the
matrix-polynomial evaluations are explicit hypotheses. -/
theorem tendsto_norm_evalMatrixPoly_of_data
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (x : CommonSpace (Fin r))
    (P : Matrix (Fin d) (Fin d) (WordPolynomial ℂ (Fin r)))
    (wds : κ → List (Fin r))
    (coeffn : ∀ n, κ → BlockAlg d n) (coeffinf : κ → BlockLimit r d)
    (Cn : ∀ n, BlockAlg d n) (Cinf : BlockLimit r d)
    (hCn : ∀ n, IsSelfAdjoint (Cn n)) (hCinf : IsSelfAdjoint Cinf)
    (hH1 : SpectralFamilyInclusion (B := fun n => BlockAlg d n) (Binf := BlockLimit r d)
      (blockSemicircular r d) (blockGUE r d x) wds coeffn coeffinf Cn Cinf)
    (hWordsx : ∀ w : List (Fin r),
      Tendsto (fun N : ℕ => gueNormTrace (N := N) w (x N)) atTop (𝓝 (tau r w)))
    (hP : ∀ n, wordPolyEvalC (Cn n) (blockGUE r d x n) wds (coeffn n)
      = evalMatrixPoly P (gueFamily r (n + 1) x))
    (hPinf : wordPolyEvalC Cinf (blockSemicircular r d) wds coeffinf
      = evalMatrixPoly P (semicircularFamily r))
    {Rb : ℝ}
    (hB : ∀ᶠ n in atTop,
      ‖wordPolyEvalC (Cn n) (blockGUE r d x n) wds (coeffn n)‖ ≤ Rb) :
    Tendsto (fun n => ‖evalMatrixPoly P (gueFamily r (n + 1) x)‖) atTop
      (𝓝 ‖evalMatrixPoly P (semicircularFamily r)‖) := by
  -- The state on the varying algebra: `tr_d ⊗ tr_{n+1}`.
  set ψ : ∀ n, StarProbabilitySpace (BlockAlg d n) :=
    fun n => matrixStarState (D := Fin d) (matrixStarProbabilitySpace (Fin (n + 1))) with hψ
  -- The limit state: `tr_d ⊗ τ`.
  set φ : StarProbabilitySpace (BlockLimit r d) :=
    matrixStarState (D := Fin d) (closedGeneratedVacuumState (Fin r)) with hφdef
  have hφ : IsFaithful φ.toProbabilitySpace :=
    matrixStarState_isFaithful (closedGeneratedVacuumState (Fin r))
      (closedGeneratedVacuumState_isFaithful (Fin r))
  -- Reduction of the moment hypothesis to scalar word-trace convergence.
  have hmom : ∀ k : ℕ, Tendsto
      (fun n => ((ψ n).expectation
        ((wordPolyEvalC (Cn n) (blockGUE r d x n) wds (coeffn n)) ^ (2 * k))).re)
      atTop
      (𝓝 ((φ.expectation
        ((wordPolyEvalC Cinf (blockSemicircular r d) wds coeffinf) ^ (2 * k))).re)) := by
    intro k
    simp only [hψ, hP, hPinf]
    have hbase := tendsto_matrixStarState_moment
      (A := fun n => CStarMatrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
      (Ainf := closedSemicircularAlgebra (Fin r))
      (φn := fun n => matrixStarProbabilitySpace (Fin (n + 1)))
      (φ := closedGeneratedVacuumState (Fin r))
      (P := P) (g := fun n => gueFamily r (n + 1) x)
      (ginf := semicircularFamily r) (m := 2 * k) ?_
    · exact Complex.continuous_re.continuousAt.tendsto.comp hbase
    · intro j
      have h := (hWordsx (polyW (P ^ (2 * k)) j)).comp (tendsto_add_atTop_nat 1)
      refine h.congr (fun n => ?_)
      exact (matrixStarProbabilitySpace_expectation_wordProd_gueFamily r (n + 1) x
        (polyW (P ^ (2 * k)) j)).symm
  -- The abstract transfer, with self-adjointness of the pencil polynomials.
  have htrans := tendsto_norm_of_spectral_family_and_moments
    (B := fun n => BlockAlg d n) (Binf := BlockLimit r d)
    (x := blockSemicircular r d) (X := blockGUE r d x) (wds := wds)
    (coeffn := coeffn) (coeffinf := coeffinf) (Cn := Cn) (Cinf := Cinf)
    hCn hCinf hH1 ψ φ hφ
    (fun n => isSelfAdjoint_wordPolyEvalC (Cn n) _ wds (coeffn n) (hCn n))
    (isSelfAdjoint_wordPolyEvalC Cinf _ wds coeffinf hCinf)
    hmom hB
  simpa only [hP, hPinf] using htrans

/-- **Almost-sure strong convergence for a fixed matrix polynomial, conditional on the
pencil data.**

`hWords` is convergence of all scalar GUE word traces to the free joint moments;
`hH1` is the one-sided spectral family inclusion for the concrete block pencil; `hB` is
the explicit uniform bound on the evaluated block polynomial.  The data
`(wds, coeffn, coeffinf, Cn, Cinf)` and the algebraic identifications `hP`, `hPinf` with
`evalMatrixPoly P` are supplied by the caller: extracting them from a self-adjoint
matrix polynomial (or, for non-self-adjoint `P`, passing to the Hermitian dilation) is the
remaining algebraic step and is *not* assumed here.

The limit is taken along all `N`, using that the transfer is proved along `n ↦ n + 1`. -/
theorem ae_tendsto_norm_evalMatrixPoly
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (P : Matrix (Fin d) (Fin d) (WordPolynomial ℂ (Fin r)))
    (wds : κ → List (Fin r))
    (coeffn : ∀ n, κ → BlockAlg d n) (coeffinf : κ → BlockLimit r d)
    (Cn : ∀ n, BlockAlg d n) (Cinf : BlockLimit r d)
    (hCn : ∀ n, IsSelfAdjoint (Cn n)) (hCinf : IsSelfAdjoint Cinf)
    (hP : ∀ (x : CommonSpace (Fin r)) (n : ℕ),
      wordPolyEvalC (Cn n) (blockGUE r d x n) wds (coeffn n)
        = evalMatrixPoly P (gueFamily r (n + 1) x))
    (hPinf : wordPolyEvalC Cinf (blockSemicircular r d) wds coeffinf
      = evalMatrixPoly P (semicircularFamily r))
    {Rb : ℝ}
    (hWords : ∀ᵐ x ∂(commonGaussianMeasure (Fin r)),
      ∀ w : List (Fin r),
        Tendsto (fun N : ℕ => gueNormTrace (N := N) w (x N)) atTop (𝓝 (tau r w)))
    (hH1 : ∀ᵐ x ∂(commonGaussianMeasure (Fin r)),
      SpectralFamilyInclusion (B := fun n => BlockAlg d n) (Binf := BlockLimit r d)
        (blockSemicircular r d) (blockGUE r d x) wds coeffn coeffinf Cn Cinf)
    (hB : ∀ᵐ x ∂(commonGaussianMeasure (Fin r)),
      ∀ᶠ n in atTop,
        ‖wordPolyEvalC (Cn n) (blockGUE r d x n) wds (coeffn n)‖ ≤ Rb) :
    ∀ᵐ x ∂(commonGaussianMeasure (Fin r)),
      Tendsto (fun N : ℕ => ‖evalMatrixPoly P (gueFamily r N x)‖) atTop
        (𝓝 ‖evalMatrixPoly P (semicircularFamily r)‖) := by
  filter_upwards [hWords, hH1, hB] with x hWx hHx hBx
  have h := tendsto_norm_evalMatrixPoly_of_data (r := r) (d := d) x P wds coeffn coeffinf
    Cn Cinf hCn hCinf hHx hWx (hP x) hPinf hBx
  -- Convert convergence along `n ↦ n + 1` to convergence along all `N`.
  exact (tendsto_add_atTop_iff_nat (f := fun N : ℕ =>
    ‖evalMatrixPoly P (gueFamily r N x)‖) 1).mp (by simpa using h)

/-- Variant of the capstone taking the word-trace convergence word by word (the form in
which it is produced by the moment computation); `ae_all_iff` combines the countably many
almost-sure events into one. -/
theorem ae_tendsto_norm_evalMatrixPoly_of_forall_ae
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (P : Matrix (Fin d) (Fin d) (WordPolynomial ℂ (Fin r)))
    (wds : κ → List (Fin r))
    (coeffn : ∀ n, κ → BlockAlg d n) (coeffinf : κ → BlockLimit r d)
    (Cn : ∀ n, BlockAlg d n) (Cinf : BlockLimit r d)
    (hCn : ∀ n, IsSelfAdjoint (Cn n)) (hCinf : IsSelfAdjoint Cinf)
    (hP : ∀ (x : CommonSpace (Fin r)) (n : ℕ),
      wordPolyEvalC (Cn n) (blockGUE r d x n) wds (coeffn n)
        = evalMatrixPoly P (gueFamily r (n + 1) x))
    (hPinf : wordPolyEvalC Cinf (blockSemicircular r d) wds coeffinf
      = evalMatrixPoly P (semicircularFamily r))
    {Rb : ℝ}
    (hWords : ∀ w : List (Fin r), ∀ᵐ x ∂(commonGaussianMeasure (Fin r)),
        Tendsto (fun N : ℕ => gueNormTrace (N := N) w (x N)) atTop (𝓝 (tau r w)))
    (hH1 : ∀ᵐ x ∂(commonGaussianMeasure (Fin r)),
      SpectralFamilyInclusion (B := fun n => BlockAlg d n) (Binf := BlockLimit r d)
        (blockSemicircular r d) (blockGUE r d x) wds coeffn coeffinf Cn Cinf)
    (hB : ∀ᵐ x ∂(commonGaussianMeasure (Fin r)),
      ∀ᶠ n in atTop,
        ‖wordPolyEvalC (Cn n) (blockGUE r d x n) wds (coeffn n)‖ ≤ Rb) :
    ∀ᵐ x ∂(commonGaussianMeasure (Fin r)),
      Tendsto (fun N : ℕ => ‖evalMatrixPoly P (gueFamily r N x)‖) atTop
        (𝓝 ‖evalMatrixPoly P (semicircularFamily r)‖) := by
  apply ae_tendsto_norm_evalMatrixPoly (r := r) (d := d) P wds coeffn coeffinf Cn Cinf
    hCn hCinf hP hPinf ?_ hH1 hB
  rwa [ae_all_iff]

section CanonicalData

variable (P : Matrix (Fin d) (Fin d) (WordPolynomial ℂ (Fin r)))

/-- **Capstone with canonical pencil data.**  For a matrix polynomial `P` whose
evaluations are self-adjoint, the pencil data are built canonically from `P`:
`C = 0` and `q = (1/2) P(g)` in the block algebra, so that `C + q + q^* = P(g)`.
The remaining hypotheses are the scalar word-trace convergence `hWords`, the one-sided
spectral family inclusion `hH1` and the explicit uniform bound `hB` for exactly this
canonical data.  No norm convergence is assumed. -/
theorem ae_tendsto_norm_evalMatrixPoly_selfAdjoint
    [DecidableEq (polyIdx P)]
    (hPsa : ∀ (x : CommonSpace (Fin r)) (n : ℕ),
      IsSelfAdjoint (evalMatrixPoly P (gueFamily r (n + 1) x)))
    (hPsaInf : IsSelfAdjoint (evalMatrixPoly P (semicircularFamily r)))
    {Rb : ℝ}
    (hWords : ∀ᵐ x ∂(commonGaussianMeasure (Fin r)),
      ∀ w : List (Fin r),
        Tendsto (fun N : ℕ => gueNormTrace (N := N) w (x N)) atTop (𝓝 (tau r w)))
    (hH1 : ∀ᵐ x ∂(commonGaussianMeasure (Fin r)),
      SpectralFamilyInclusion (B := fun n => BlockAlg d n) (Binf := BlockLimit r d)
        (blockSemicircular r d) (blockGUE r d x) (polyW P)
        (fun n k => (1 / 2 : ℂ) •
          polyCoeff (A := CStarMatrix (Fin (n + 1)) (Fin (n + 1)) ℂ) P k)
        (fun k => (1 / 2 : ℂ) •
          polyCoeff (A := closedSemicircularAlgebra (Fin r)) P k)
        (fun _ => 0) 0)
    (hB : ∀ᵐ x ∂(commonGaussianMeasure (Fin r)),
      ∀ᶠ n in atTop,
        ‖wordPolyEvalC (0 : BlockAlg d n) (blockGUE r d x n) (polyW P)
          (fun k => (1 / 2 : ℂ) •
            polyCoeff (A := CStarMatrix (Fin (n + 1)) (Fin (n + 1)) ℂ) P k)‖ ≤ Rb) :
    ∀ᵐ x ∂(commonGaussianMeasure (Fin r)),
      Tendsto (fun N : ℕ => ‖evalMatrixPoly P (gueFamily r N x)‖) atTop
        (𝓝 ‖evalMatrixPoly P (semicircularFamily r)‖) := by
  refine ae_tendsto_norm_evalMatrixPoly (r := r) (d := d) P (polyW P)
    (fun n k => (1 / 2 : ℂ) •
      polyCoeff (A := CStarMatrix (Fin (n + 1)) (Fin (n + 1)) ℂ) P k)
    (fun k => (1 / 2 : ℂ) •
      polyCoeff (A := closedSemicircularAlgebra (Fin r)) P k)
    (fun n => (0 : BlockAlg d n)) (0 : BlockLimit r d) ?_ ?_ ?_ ?_ hWords hH1 hB
  · intro n
    exact star_zero (R := BlockAlg d n)
  · exact star_zero (R := BlockLimit r d)
  · intro x n
    exact wordPolyEvalC_zero_half_eq P (gueFamily r (n + 1) x) (hPsa x n)
  · exact wordPolyEvalC_zero_half_eq P (semicircularFamily r) hPsaInf

end CanonicalData

end Concrete

end GUEStrongConvergence
