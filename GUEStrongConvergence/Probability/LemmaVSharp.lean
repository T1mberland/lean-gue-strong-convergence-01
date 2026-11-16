/-
# The sharp Lemma V: variance of spectral statistics of the GUE pencil

This module proves the **sharp** Gaussian-Poincaré variance bound (Lemma V of HT05,
Proposition 4.7) for polynomial spectral statistics of the affine GUE pencil

`H_N(x) = A₀ ⊗ I_N + ∑ i, A_i ⊗ G_i(x)`,

with the *normalized* trace `tau_N = (card d * N)⁻¹ Tr` over the full matrix algebra
`Matrix (d × Fin N) (d × Fin N) ℂ`.

## Main results

* `trace_gueDirMatrix_mul` — the exact trace pairing of a coordinate direction:
  `Tr(D_p X) = gueScale(N) · (α · S_p + β · T_p)`, with the two slice coefficients
  `S_p = dirCoeff X (A_i) n m`, `T_p = dirCoeff X (A_i) m n`.

* `sum_sq_trace_direction_le` — **the exact direction contraction**:
  `∑_p ‖Tr(D_p X)‖² ≤ 2 · gueScale(N)² · (∑_i frob(A_i)²) · ‖X‖_F²`.
  This is the trace-pairing analogue of `sum_sq_direction_pairing_le` (which handles the
  rank-one `W ⊗ Z` pairings); it is the `X`-general form needed for `f'(H)`.

* `hasDerivAt_gueStatisticNorm_update` — the coordinate derivative of the normalized
  statistic `Z_N = tau_N(P(H_N))`, obtained from the trace derivative
  `hasDerivAt_trace_polyMatrix` (never the false matrix identity).

* `variance_gueStatisticNorm_le` — Gaussian Poincaré for `Z_N` with all analytic hypotheses
  discharged (the paper's Lemma V *reduction*), and
  `variance_gueStatisticNorm_le_of_contraction` — its reduction to the integrated
  Hilbert–Schmidt norm of `P'(H_N)`.

* `hsNorm_gueDerivMatrix_eq` — for Hermitian `H_N`,
  `‖P'(H_N)‖_F² = (card d * N) · tau_N((P')²(H_N))`, which converts the HS bound into the
  normalized-trace form of Lemma V.

* `lemmaV_sharp_poly` — **the sharp Lemma V** for real polynomials:
  `Var(Z_N) ≤ (2 (∑_i frob(A_i)²) / (card d)) / N² · E[tau_N((P')²(H_N))]`.

* `lemmaV_sharp_poly_hsNorm` — the same bound in Hilbert–Schmidt form,
  `Var(Z_N) ≤ 2 (∑_i frob(A_i)²) / (card d)² / N³ · E‖P'(H_N)‖_F²`.

* `lemmaV_sharp_poly_rate` — the explicit rate form: from
  `E[tau_N((P')²(H_N))] ≤ C' / N²` conclude
  `Var(Z_N) ≤ 2 (∑_i frob(A_i)²) C' / (card d) / N⁴`.

The `N⁻²` factor is the point: since `gueScale(N)² = 1/N`, the pair (Lemma M, Lemma V)
gives `Var(Z_N) = O(N⁻⁴)` whenever `E[tau_N((f')²(H_N))] = O(N⁻²)`.
-/
import GUEStrongConvergence.Probability.LemmaVContraction
import GUEStrongConvergence.Probability.LemmaVAnalytic
import GUEStrongConvergence.Probability.ResolventSparseBound
import Mathlib.Analysis.Matrix.Normed

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped RealInnerProductSpace ENNReal NNReal Topology Polynomial
open scoped BigOperators

namespace GUEStrongConvergence

noncomputable section

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

variable {ι d : Type*} [Fintype ι] [DecidableEq ι] [Fintype d] [DecidableEq d] {N : ℕ}

/-! ### Target 2: the exact direction contraction for the trace pairing -/

/-- The `α`-slice coefficient `S_p = dirCoeff X (A_i) n m` of the trace pairing
`Tr(D_p X)` for `p = (i, (m, n))`. -/
def dirCoeffS (X : Matrix (d × Fin N) (d × Fin N) ℂ) (A : ι → Matrix d d ℂ)
    (p : GUECoord ι N) : ℂ :=
  dirCoeff X (A p.1) p.2.2 p.2.1

/-- The `β`-slice coefficient `T_p = dirCoeff X (A_i) m n` of the trace pairing
`Tr(D_p X)` for `p = (i, (m, n))`. -/
def dirCoeffT (X : Matrix (d × Fin N) (d × Fin N) ℂ) (A : ι → Matrix d d ℂ)
    (p : GUECoord ι N) : ℂ :=
  dirCoeff X (A p.1) p.2.1 p.2.2

/-- **Trace pairing against a GUE coordinate direction.**  For `p = (i, (m, n))`,
`Tr(D_p X) = gueScale(N) · (α · S_p + β · T_p)`. -/
theorem trace_gueDirMatrix_mul (X : Matrix (d × Fin N) (d × Fin N) ℂ)
    (A : ι → Matrix d d ℂ) (p : GUECoord ι N) :
    Matrix.trace (gueDirMatrix A p * X) =
      (gueScale N : ℂ) *
        (gueAlpha * dirCoeffS X A p + gueBeta * dirCoeffT X A p) := by
  obtain ⟨i, m, n⟩ := p
  rw [Matrix.trace_mul_comm, trace_mul_gueDirMatrix]
  rfl

/-- Cauchy–Schwarz for the `α`/`β` combination: `‖αu + βv‖² ≤ ‖u‖² + ‖v‖²`. -/
theorem norm_gueAlpha_mul_add_gueBeta_mul_sq_le (u v : ℂ) :
    ‖(gueAlpha : ℂ) * u + (gueBeta : ℂ) * v‖ ^ 2 ≤ ‖u‖ ^ 2 + ‖v‖ ^ 2 := by
  have h4 : ‖(gueAlpha : ℂ)‖ ^ 2 + ‖(gueBeta : ℂ)‖ ^ 2 = 1 :=
    norm_gueAlpha_sq_add_norm_gueBeta_sq
  have hCS : (‖(gueAlpha : ℂ)‖ * ‖u‖ + ‖(gueBeta : ℂ)‖ * ‖v‖) ^ 2
      ≤ (‖(gueAlpha : ℂ)‖ ^ 2 + ‖(gueBeta : ℂ)‖ ^ 2) * (‖u‖ ^ 2 + ‖v‖ ^ 2) := by
    nlinarith [sq_nonneg (‖(gueAlpha : ℂ)‖ * ‖v‖ - ‖(gueBeta : ℂ)‖ * ‖u‖)]
  rw [h4, one_mul] at hCS
  calc ‖(gueAlpha : ℂ) * u + (gueBeta : ℂ) * v‖ ^ 2
      ≤ (‖(gueAlpha : ℂ)‖ * ‖u‖ + ‖(gueBeta : ℂ)‖ * ‖v‖) ^ 2 := by
        refine pow_le_pow_left₀ (norm_nonneg _) ?_ 2
        calc ‖(gueAlpha : ℂ) * u + (gueBeta : ℂ) * v‖
            ≤ ‖(gueAlpha : ℂ) * u‖ + ‖(gueBeta : ℂ) * v‖ := norm_add_le _ _
          _ = ‖(gueAlpha : ℂ)‖ * ‖u‖ + ‖(gueBeta : ℂ)‖ * ‖v‖ := by rw [norm_mul, norm_mul]
    _ ≤ ‖u‖ ^ 2 + ‖v‖ ^ 2 := hCS

/-- **Entrywise Cauchy–Schwarz for a slice coefficient.**
`‖dirCoeff X B x y‖² ≤ frob(B)² · ∑_{a,b} ‖X (a,x) (b,y)‖²`. -/
theorem norm_dirCoeff_sq_le (X : Matrix (d × Fin N) (d × Fin N) ℂ) (B : Matrix d d ℂ)
    (x y : Fin N) :
    ‖dirCoeff X B x y‖ ^ 2 ≤
      (frob B) ^ 2 * (∑ a : d, ∑ b : d, ‖X (a, x) (b, y)‖ ^ 2) := by
  have hnorm : ‖dirCoeff X B x y‖ ≤
      ∑ q : d × d, ‖X (q.1, x) (q.2, y)‖ * ‖B q.2 q.1‖ := by
    rw [dirCoeff]
    calc ‖∑ a : d, ∑ b : d, X (a, x) (b, y) * B b a‖
        ≤ ∑ a : d, ‖∑ b : d, X (a, x) (b, y) * B b a‖ := norm_sum_le _ _
      _ ≤ ∑ a : d, ∑ b : d, ‖X (a, x) (b, y) * B b a‖ :=
          Finset.sum_le_sum fun a _ => norm_sum_le _ _
      _ = ∑ a : d, ∑ b : d, ‖X (a, x) (b, y)‖ * ‖B b a‖ := by
          simp only [norm_mul]
      _ = ∑ q : d × d, ‖X (q.1, x) (q.2, y)‖ * ‖B q.2 q.1‖ := by
          rw [Fintype.sum_prod_type]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (d × d))
    (fun q => ‖X (q.1, x) (q.2, y)‖) (fun q => ‖B q.2 q.1‖)
  have hf : (∑ q : d × d, ‖X (q.1, x) (q.2, y)‖ ^ 2)
      = ∑ a : d, ∑ b : d, ‖X (a, x) (b, y)‖ ^ 2 := by
    rw [Fintype.sum_prod_type]
  have hg : (∑ q : d × d, ‖B q.2 q.1‖ ^ 2) = (frob B) ^ 2 := by
    rw [frob_sq, Finset.sum_comm]
    rw [Fintype.sum_prod_type]
  calc ‖dirCoeff X B x y‖ ^ 2 ≤ (∑ q : d × d, ‖X (q.1, x) (q.2, y)‖ * ‖B q.2 q.1‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hnorm 2
    _ ≤ (∑ q : d × d, ‖X (q.1, x) (q.2, y)‖ ^ 2) *
          (∑ q : d × d, ‖B q.2 q.1‖ ^ 2) := hcs
    _ = (frob B) ^ 2 * (∑ a : d, ∑ b : d, ‖X (a, x) (b, y)‖ ^ 2) := by
        rw [hf, hg, mul_comm]

/-- The squared Hilbert–Schmidt norm as a sum over the `(x,y)`-slices of the `Fin N` index. -/
theorem hsNorm_eq_slice_sum (X : Matrix (d × Fin N) (d × Fin N) ℂ) :
    hsNorm X =
      ∑ x : Fin N, ∑ y : Fin N, ∑ a : d, ∑ b : d, ‖X (a, x) (b, y)‖ ^ 2 := by
  rw [hsNorm]
  simp only [Fintype.sum_prod_type]
  calc (∑ a : d, ∑ x : Fin N, ∑ b : d, ∑ y : Fin N, ‖X (a, x) (b, y)‖ ^ 2)
      = ∑ x : Fin N, ∑ a : d, ∑ b : d, ∑ y : Fin N, ‖X (a, x) (b, y)‖ ^ 2 :=
        Finset.sum_comm
    _ = ∑ x : Fin N, ∑ a : d, ∑ y : Fin N, ∑ b : d, ‖X (a, x) (b, y)‖ ^ 2 := by
        refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun a _ => ?_
        exact Finset.sum_comm
    _ = ∑ x : Fin N, ∑ y : Fin N, ∑ a : d, ∑ b : d, ‖X (a, x) (b, y)‖ ^ 2 := by
        refine Finset.sum_congr rfl fun x _ => ?_
        exact Finset.sum_comm

/-- **Slice contraction for one coefficient matrix.**
`∑_{x,y} ‖dirCoeff X B x y‖² ≤ frob(B)² · ‖X‖_F²`. -/
theorem sum_sq_dirCoeff_le (X : Matrix (d × Fin N) (d × Fin N) ℂ) (B : Matrix d d ℂ) :
    (∑ x : Fin N, ∑ y : Fin N, ‖dirCoeff X B x y‖ ^ 2)
      ≤ (frob B) ^ 2 * hsNorm X := by
  calc (∑ x : Fin N, ∑ y : Fin N, ‖dirCoeff X B x y‖ ^ 2)
      ≤ ∑ x : Fin N, ∑ y : Fin N,
          (frob B) ^ 2 * (∑ a : d, ∑ b : d, ‖X (a, x) (b, y)‖ ^ 2) :=
        Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => norm_dirCoeff_sq_le X B x y
    _ = (frob B) ^ 2 *
          (∑ x : Fin N, ∑ y : Fin N, ∑ a : d, ∑ b : d, ‖X (a, x) (b, y)‖ ^ 2) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Finset.mul_sum]
    _ = (frob B) ^ 2 * hsNorm X := by rw [← hsNorm_eq_slice_sum]

/-- **The `α`-slice sum contraction** over all Gaussian coordinates. -/
theorem sum_sq_dirCoeffS_le (X : Matrix (d × Fin N) (d × Fin N) ℂ)
    (A : ι → Matrix d d ℂ) :
    (∑ p : GUECoord ι N, ‖dirCoeffS X A p‖ ^ 2)
      ≤ (∑ i, (frob (A i)) ^ 2) * hsNorm X := by
  have hreindex : ∀ i : ι,
      (∑ m : Fin N, ∑ n : Fin N, ‖dirCoeff X (A i) n m‖ ^ 2)
        = ∑ x : Fin N, ∑ y : Fin N, ‖dirCoeff X (A i) x y‖ ^ 2 := by
    intro i
    exact Finset.sum_comm
  simp only [Fintype.sum_prod_type, dirCoeffS]
  simp_rw [hreindex]
  calc (∑ i : ι, ∑ x : Fin N, ∑ y : Fin N, ‖dirCoeff X (A i) x y‖ ^ 2)
      ≤ ∑ i : ι, (frob (A i)) ^ 2 * hsNorm X :=
        Finset.sum_le_sum fun i _ => sum_sq_dirCoeff_le X (A i)
    _ = (∑ i, (frob (A i)) ^ 2) * hsNorm X := by rw [Finset.sum_mul]

/-- **The `β`-slice sum contraction** over all Gaussian coordinates. -/
theorem sum_sq_dirCoeffT_le (X : Matrix (d × Fin N) (d × Fin N) ℂ)
    (A : ι → Matrix d d ℂ) :
    (∑ p : GUECoord ι N, ‖dirCoeffT X A p‖ ^ 2)
      ≤ (∑ i, (frob (A i)) ^ 2) * hsNorm X := by
  simp only [Fintype.sum_prod_type, dirCoeffT]
  calc (∑ i : ι, ∑ m : Fin N, ∑ n : Fin N, ‖dirCoeff X (A i) m n‖ ^ 2)
      ≤ ∑ i : ι, (frob (A i)) ^ 2 * hsNorm X :=
        Finset.sum_le_sum fun i _ => sum_sq_dirCoeff_le X (A i)
    _ = (∑ i, (frob (A i)) ^ 2) * hsNorm X := by rw [Finset.sum_mul]

/-- **Target 2 — the exact direction contraction for the trace pairing.**

For every matrix `X` and every coefficient family `A`,

`∑_p ‖Tr(guePencilDirection A p · X)‖² ≤ 2 · gueScale(N)² · (∑_i frob(A_i)²) · ‖X‖_F²`,

where `‖X‖_F² = hsNorm X`.  The constant `2` is the `α`/`β` slice split; the exact
orthonormality of `√N · B_p` gives the same bound with constant `1` in the scalar case,
so this is sharp in the powers of `N`. -/
theorem sum_sq_trace_direction_le (X : Matrix (d × Fin N) (d × Fin N) ℂ)
    (A : ι → Matrix d d ℂ) :
    (∑ p : GUECoord ι N, ‖Matrix.trace (gueDirMatrix A p * X)‖ ^ 2)
      ≤ 2 * (gueScale N) ^ 2 * (∑ i, (frob (A i)) ^ 2) * hsNorm X := by
  have hpoint : ∀ p : GUECoord ι N,
      ‖Matrix.trace (gueDirMatrix A p * X)‖ ^ 2 ≤
        (gueScale N) ^ 2 * (‖dirCoeffS X A p‖ ^ 2 + ‖dirCoeffT X A p‖ ^ 2) := by
    intro p
    rw [trace_gueDirMatrix_mul, norm_mul, mul_pow]
    have hnorm : ‖(gueScale N : ℂ)‖ ^ 2 = (gueScale N) ^ 2 := by
      rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
    rw [hnorm]
    exact mul_le_mul_of_nonneg_left
      (norm_gueAlpha_mul_add_gueBeta_mul_sq_le (dirCoeffS X A p) (dirCoeffT X A p))
      (sq_nonneg _)
  calc (∑ p : GUECoord ι N, ‖Matrix.trace (gueDirMatrix A p * X)‖ ^ 2)
      ≤ ∑ p : GUECoord ι N,
          (gueScale N) ^ 2 * (‖dirCoeffS X A p‖ ^ 2 + ‖dirCoeffT X A p‖ ^ 2) :=
        Finset.sum_le_sum fun p _ => hpoint p
    _ = (gueScale N) ^ 2 *
          ((∑ p : GUECoord ι N, ‖dirCoeffS X A p‖ ^ 2) +
            ∑ p : GUECoord ι N, ‖dirCoeffT X A p‖ ^ 2) := by
        rw [← Finset.mul_sum, Finset.sum_add_distrib]
    _ ≤ (gueScale N) ^ 2 *
          (2 * ((∑ i, (frob (A i)) ^ 2) * hsNorm X)) := by
        refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
        have hS := sum_sq_dirCoeffS_le X A
        have hT := sum_sq_dirCoeffT_le X A
        nlinarith
    _ = 2 * (gueScale N) ^ 2 * (∑ i, (frob (A i)) ^ 2) * hsNorm X := by ring

/-! ### Target 1: the trace derivative of the normalized statistic -/

/-- The normalization constant `(card d * N)⁻¹` of the full matrix algebra
`Matrix (d × Fin N) (d × Fin N) ℂ`. -/
def gueNormConst (d : Type*) [Fintype d] (N : ℕ) : ℝ :=
  ((Fintype.card d * N : ℕ) : ℝ)⁻¹

/-- The normalized trace `tau_N M = (card d * N)⁻¹ · Re Tr M`. -/
def guePencilNormTrace (M : Matrix (d × Fin N) (d × Fin N) ℂ) : ℝ :=
  gueNormConst d N * (Matrix.trace M).re

/-- The normalized spectral statistic `Z_N = tau_N(P(H_N(x)))`. -/
def gueStatisticNorm (P : ℝ[X]) (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    (x : EuclideanSpace ℝ (GUECoord ι N)) : ℝ :=
  guePencilNormTrace (polyMatrix P (guePencilMatrix A₀ A (WithLp.ofLp x)))

/-- The normalized coordinate derivative of the spectral statistic. -/
def gueStatisticNormDir (P : ℝ[X]) (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    (p : GUECoord ι N) (x : EuclideanSpace ℝ (GUECoord ι N)) : ℝ :=
  guePencilNormTrace (gueDerivMatrix P A₀ A x * gueDirMatrix A p)

/-- The normalized statistic is the normalization constant times the unnormalized one. -/
lemma gueStatisticNorm_eq (P : ℝ[X]) (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    (x : EuclideanSpace ℝ (GUECoord ι N)) :
    gueStatisticNorm P A₀ A x = gueNormConst d N * gueStatistic P A₀ A x := rfl

/-- The normalized coordinate derivative is the constant times the unnormalized one. -/
lemma gueStatisticNormDir_eq (P : ℝ[X]) (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    (p : GUECoord ι N) (x : EuclideanSpace ℝ (GUECoord ι N)) :
    gueStatisticNormDir P A₀ A p x = gueNormConst d N * gueStatisticDir P A₀ A p x := rfl


/-- **Coordinate derivative of the normalized statistic.**  The derivative is the normalized
trace pairing against the coordinate direction, obtained from the trace derivative
`hasDerivAt_trace_polyMatrix` (not from the false matrix identity). -/
theorem hasDerivAt_gueStatisticNorm_update (P : ℝ[X]) (A₀ : Matrix d d ℂ)
    (A : ι → Matrix d d ℂ) (x : EuclideanSpace ℝ (GUECoord ι N))
    (p : GUECoord ι N) (t₀ : ℝ) :
    HasDerivAt (fun u : ℝ => gueStatisticNorm P A₀ A (euclidUpdate x p u))
      (gueStatisticNormDir P A₀ A p (euclidUpdate x p t₀)) t₀ := by
  have h := (hasDerivAt_gueStatistic_update P A₀ A x p t₀).const_mul (gueNormConst d N)
  simpa only [gueStatisticNorm_eq, gueStatisticNormDir_eq] using h

/-! ### Gaussian Poincaré for the normalized statistic -/

/-- **Gaussian Poincaré for `Z_N = tau_N(P(H_N))`**, with all analytic hypotheses discharged
from `LemmaVAnalytic`. -/
theorem variance_gueStatisticNorm_le (P : ℝ[X]) (A₀ : Matrix d d ℂ)
    (A : ι → Matrix d d ℂ) :
    variance (gueStatisticNorm P A₀ A)
        (stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))
      ≤ ∑ p : GUECoord ι N,
          ∫ x, (gueStatisticNormDir P A₀ A p x) ^ 2
            ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) := by
  refine gaussian_poincare_stdGaussian (F := gueStatisticNorm P A₀ A)
    (D := gueStatisticNormDir P A₀ A) ?_ ?_ ?_ ?_
  · have h : MemLp (fun x => gueNormConst d N * gueStatistic P A₀ A x) 2
        (stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) :=
      (memLp_gueStatistic (N := N) P A₀ A).const_mul (gueNormConst d N)
    convert h using 1
    funext x
    exact gueStatisticNorm_eq P A₀ A x
  · intro p
    have h : MemLp (fun x => gueNormConst d N * gueStatisticDir P A₀ A p x) 2
        (stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) :=
      (memLp_gueStatisticDir (N := N) P A₀ A p).const_mul (gueNormConst d N)
    convert h using 1
    funext x
    exact gueStatisticNormDir_eq P A₀ A p x
  · intro p
    filter_upwards with x t
    exact hasDerivAt_gueStatisticNorm_update P A₀ A x p t
  · intro p
    filter_upwards [ae_polyGrowth_gueStatistic (N := N) P A₀ A p] with x hx
    exact ⟨polyGrowth_const_mul _ hx.1, polyGrowth_const_mul _ hx.2⟩

/-- **Lemma V, reduced form with the exact direction contraction.** -/
theorem variance_gueStatisticNorm_le_of_contraction (P : ℝ[X]) (A₀ : Matrix d d ℂ)
    (A : ι → Matrix d d ℂ)
    (hint : Integrable (fun x => hsNorm (gueDerivMatrix P A₀ A x))
      (stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))) :
    variance (gueStatisticNorm P A₀ A) (stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))
      ≤ (gueNormConst d N) ^ 2 *
          (2 * (gueScale N) ^ 2 * (∑ i, (frob (A i)) ^ 2) *
            ∫ x, hsNorm (gueDerivMatrix P A₀ A x)
              ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))) := by
  classical
  set μ := stdGaussian (EuclideanSpace ℝ (GUECoord ι N)) with hμ
  have hDsq : ∀ p : GUECoord ι N, Integrable (fun x => (gueStatisticDir P A₀ A p x) ^ 2) μ :=
    fun p => (memLp_gueStatisticDir P A₀ A p).integrable_sq
  have hsum_int : Integrable (fun x => ∑ p : GUECoord ι N,
      (gueStatisticDir P A₀ A p x) ^ 2) μ :=
    integrable_finsetSum _ fun p _ => hDsq p
  -- Step 1: pull the normalization constant out of the squares.
  have h1 : (∑ p : GUECoord ι N, ∫ x, (gueStatisticNormDir P A₀ A p x) ^ 2 ∂μ)
      = (gueNormConst d N) ^ 2 *
          (∑ p : GUECoord ι N, ∫ x, (gueStatisticDir P A₀ A p x) ^ 2 ∂μ) := by
    have hpt : ∀ (p : GUECoord ι N) (x : EuclideanSpace ℝ (GUECoord ι N)),
        (gueStatisticNormDir P A₀ A p x) ^ 2
          = (gueNormConst d N) ^ 2 * (gueStatisticDir P A₀ A p x) ^ 2 := by
      intro p x
      rw [gueStatisticNormDir_eq]
      ring
    simp_rw [hpt, integral_const_mul]
    rw [← Finset.mul_sum]
  -- Step 2: exchange the finite sum and the integral.
  have h2 : (∑ p : GUECoord ι N, ∫ x, (gueStatisticDir P A₀ A p x) ^ 2 ∂μ)
      = ∫ x, ∑ p : GUECoord ι N, (gueStatisticDir P A₀ A p x) ^ 2 ∂μ := by
    rw [integral_finsetSum]
    intro p _
    exact hDsq p
  -- Step 3: the pointwise direction contraction.
  have hcontr : ∀ x : EuclideanSpace ℝ (GUECoord ι N),
      ∑ p : GUECoord ι N, (gueStatisticDir P A₀ A p x) ^ 2
        ≤ 2 * (gueScale N) ^ 2 * (∑ i, (frob (A i)) ^ 2) *
            hsNorm (gueDerivMatrix P A₀ A x) := by
    intro x
    have hsum : (∑ p : GUECoord ι N, (gueStatisticDir P A₀ A p x) ^ 2)
        = ∑ p : GUECoord ι N,
            (Matrix.trace (gueDirMatrix A p * gueDerivMatrix P A₀ A x)).re ^ 2 := by
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [gueStatisticDir, gueDerivMatrix, Matrix.trace_mul_comm]
    rw [hsum]
    refine (Finset.sum_le_sum fun p _ => ?_).trans
      (sum_sq_trace_direction_le (gueDerivMatrix P A₀ A x) A)
    have h := Complex.abs_re_le_norm
      (Matrix.trace (gueDirMatrix A p * gueDerivMatrix P A₀ A x))
    have h2' := pow_le_pow_left₀ (abs_nonneg _) h 2
    simpa [sq_abs] using h2'
  refine (variance_gueStatisticNorm_le P A₀ A).trans ?_
  rw [h1, h2]
  calc (gueNormConst d N) ^ 2 *
        (∫ x, ∑ p : GUECoord ι N, (gueStatisticDir P A₀ A p x) ^ 2 ∂μ)
      ≤ (gueNormConst d N) ^ 2 *
          (∫ x, 2 * (gueScale N) ^ 2 * (∑ i, (frob (A i)) ^ 2) *
            hsNorm (gueDerivMatrix P A₀ A x) ∂μ) := by
        refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
        exact integral_mono hsum_int (hint.const_mul _) hcontr
    _ = (gueNormConst d N) ^ 2 *
          (2 * (gueScale N) ^ 2 * (∑ i, (frob (A i)) ^ 2) *
            ∫ x, hsNorm (gueDerivMatrix P A₀ A x) ∂μ) := by
        rw [integral_const_mul]

/-! ### Relating `‖P'(H)‖_F²` to the normalized trace of `(P')²` -/

/-- For Hermitian `F`, the Hilbert–Schmidt norm square is the real trace of `F * F`. -/
theorem hsNorm_eq_trace_mul_re_of_isHermitian {n : Type*} [Fintype n] [DecidableEq n]
    (F : Matrix n n ℂ) (hF : F.IsHermitian) :
    hsNorm F = (Matrix.trace (F * F)).re := by
  have hdiag : ∀ i : n, ((F * F) i i).re = ∑ j : n, ‖F i j‖ ^ 2 := by
    intro i
    rw [Matrix.mul_apply, Complex.re_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hji : F j i = star (F i j) := by
      have h := congrArg star (hF.apply i j)
      simpa using h
    have hmul : F i j * F j i = ((‖F i j‖ ^ 2 : ℝ) : ℂ) := by
      rw [hji]
      simpa using Complex.mul_conj' (F i j)
    rw [hmul, Complex.ofReal_re]
  rw [hsNorm, Matrix.trace, Complex.re_sum]
  exact Finset.sum_congr rfl fun i _ => by simpa [Matrix.diag] using (hdiag i).symm

/-- The polynomial functional calculus is multiplicative in the polynomial power. -/
lemma polyMatrix_pow {m : Type*} [Fintype m] [DecidableEq m] (Q : ℝ[X])
    (H : Matrix m m ℂ) (k : ℕ) :
    polyMatrix (Q ^ k) H = polyMatrix Q H ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ, polyMatrix_mul, ih, pow_succ]

/-- The polynomial functional calculus of a real polynomial at a Hermitian matrix is
Hermitian. -/
theorem polyMatrix_isHermitian {m : Type*} [Fintype m] [DecidableEq m] (Q : ℝ[X])
    (H : Matrix m m ℂ) (hH : H.IsHermitian) : (polyMatrix Q H).IsHermitian := by
  rw [polyMatrix_eq_sum]
  have hterm : ∀ k ∈ Q.support, (Q.coeff k • H ^ k).IsHermitian := fun k _ =>
    (hH.pow k).smul (IsSelfAdjoint.all (Q.coeff k))
  exact (isSelfAdjoint_sum _ fun k hk => (hterm k hk).isSelfAdjoint).isHermitian

/-- **`‖P'(H)‖_F²` as a normalized trace.**  For a Hermitian pencil `H` and `N > 0`,
`hsNorm (P'(H)) = (card d * N) · tau_N((P')²(H))`. -/
theorem hsNorm_gueDerivMatrix_eq [Nonempty d] (P : ℝ[X]) (A₀ : Matrix d d ℂ)
    (A : ι → Matrix d d ℂ) (hA₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian)
    (hN : 0 < N) (x : EuclideanSpace ℝ (GUECoord ι N)) :
    hsNorm (gueDerivMatrix P A₀ A x) =
      ((Fintype.card d * N : ℕ) : ℝ) *
        gueStatisticNorm (P.derivative ^ 2) A₀ A x := by
  have hHerm : (guePencilMatrix A₀ A (WithLp.ofLp x)).IsHermitian :=
    guePencilMatrix_isHermitian A₀ A hA₀ hA (WithLp.ofLp x)
  have hF : (gueDerivMatrix P A₀ A x).IsHermitian :=
    polyMatrix_isHermitian P.derivative _ hHerm
  have hmul : gueDerivMatrix P A₀ A x * gueDerivMatrix P A₀ A x
      = polyMatrix (P.derivative ^ 2) (guePencilMatrix A₀ A (WithLp.ofLp x)) := by
    rw [gueDerivMatrix, ← pow_two, ← polyMatrix_pow]
  rw [hsNorm_eq_trace_mul_re_of_isHermitian _ hF, hmul]
  have hdN : ((Fintype.card d * N : ℕ) : ℝ) ≠ 0 := by
    have h1 : 0 < Fintype.card d := Fintype.card_pos_iff.mpr ‹Nonempty d›
    exact_mod_cast Nat.mul_pos h1 hN |>.ne'
  simp only [gueStatisticNorm, guePencilNormTrace, gueNormConst]
  field_simp

/-! ### Target 4: the sharp Lemma V for polynomials -/

/-- **Lemma V (sharp, polynomial form).**  For Hermitian coefficients `A₀, A_i`, `N > 0` and
`d` nonempty,

`Var(tau_N(P(H_N))) ≤ 2 (∑_i frob(A_i)²) / (card d) / N² · E[tau_N((P')²(H_N))]`.

The `N⁻²` factor is the point: together with Lemma M it gives `Var(Z_N) = O(N⁻⁴)` whenever
`E[tau_N((P')²(H_N))] = O(N⁻²)`. -/
theorem lemmaV_sharp_poly [Nonempty d] (P : ℝ[X]) (A₀ : Matrix d d ℂ)
    (A : ι → Matrix d d ℂ) (hA₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian)
    (hN : 0 < N) :
    variance (gueStatisticNorm P A₀ A) (stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))
      ≤ 2 * (∑ i, (frob (A i)) ^ 2) / (Fintype.card d : ℝ) / (N : ℝ) ^ 2 *
          ∫ x, gueStatisticNorm (P.derivative ^ 2) A₀ A x
            ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) := by
  classical
  set μ := stdGaussian (EuclideanSpace ℝ (GUECoord ι N)) with hμ
  set S : ℝ := ∑ i, (frob (A i)) ^ 2 with hS
  set I : ℝ := ∫ x, gueStatisticNorm (P.derivative ^ 2) A₀ A x ∂μ with hI
  have hcard : 0 < Fintype.card d := Fintype.card_pos_iff.mpr ‹Nonempty d›
  have hcardR : (0 : ℝ) < (Fintype.card d : ℝ) := by exact_mod_cast hcard
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hdN : ((Fintype.card d * N : ℕ) : ℝ) ≠ 0 := by
    have hpos : 0 < Fintype.card d * N := Nat.mul_pos hcard hN
    exact_mod_cast hpos.ne'
  -- integrability of the Hilbert–Schmidt norm of `P'(H)`
  have hint : Integrable (fun x => hsNorm (gueDerivMatrix P A₀ A x)) μ := by
    have hmem := memLp_gueStatistic (N := N) (P.derivative ^ 2) A₀ A
    have hmem' : MemLp (gueStatisticNorm (P.derivative ^ 2) A₀ A) 2 μ := by
      have h : MemLp (fun x => gueNormConst d N *
          gueStatistic (P.derivative ^ 2) A₀ A x) 2 μ :=
        hmem.const_mul (gueNormConst d N)
      convert h using 1
      funext x
      exact gueStatisticNorm_eq (P.derivative ^ 2) A₀ A x
    have hint' : Integrable (gueStatisticNorm (P.derivative ^ 2) A₀ A) μ :=
      hmem'.integrable (by norm_num)
    have heq : (fun x : EuclideanSpace ℝ (GUECoord ι N) =>
          hsNorm (gueDerivMatrix P A₀ A x)) =
        fun x : EuclideanSpace ℝ (GUECoord ι N) =>
          ((Fintype.card d * N : ℕ) : ℝ) *
            gueStatisticNorm (P.derivative ^ 2) A₀ A x := by
      funext x
      exact hsNorm_gueDerivMatrix_eq P A₀ A hA₀ hA hN x
    rw [heq]
    exact hint'.const_mul _
  -- the integral of `hsNorm` is `card d * N` times the integral of `tau_N((P')²)`
  have hint_eq : (∫ x, hsNorm (gueDerivMatrix P A₀ A x) ∂μ) =
      ((Fintype.card d * N : ℕ) : ℝ) * I := by
    have heq : (fun x : EuclideanSpace ℝ (GUECoord ι N) =>
          hsNorm (gueDerivMatrix P A₀ A x)) =
        fun x : EuclideanSpace ℝ (GUECoord ι N) =>
          ((Fintype.card d * N : ℕ) : ℝ) *
            gueStatisticNorm (P.derivative ^ 2) A₀ A x := by
      funext x
      exact hsNorm_gueDerivMatrix_eq P A₀ A hA₀ hA hN x
    rw [heq, integral_const_mul, hI]
  refine (variance_gueStatisticNorm_le_of_contraction P A₀ A hint).trans (le_of_eq ?_)
  rw [hint_eq, hS, hI]
  have hDn : ((Fintype.card d * N : ℕ) : ℝ) = (Fintype.card d : ℝ) * (N : ℝ) := by
    push_cast
    ring
  have hgnc : gueNormConst d N = (((Fintype.card d : ℝ) * (N : ℝ)))⁻¹ := by
    rw [gueNormConst, hDn]
  rw [hgnc, gueScale_sq, hDn]
  field_simp

/-- **Lemma V in Hilbert–Schmidt form.**  With no Hermitian hypotheses on the coefficients,
but with integrability of `‖P'(H_N)‖_F²`,

`Var(Z_N) ≤ 2 (∑_i frob(A_i)²) / (card d)² / N³ · E‖P'(H_N)‖_F²`. -/
theorem lemmaV_sharp_poly_hsNorm [Nonempty d] (P : ℝ[X]) (A₀ : Matrix d d ℂ)
    (A : ι → Matrix d d ℂ) (hN : 0 < N)
    (hint : Integrable (fun x => hsNorm (gueDerivMatrix P A₀ A x))
      (stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))) :
    variance (gueStatisticNorm P A₀ A) (stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))
      ≤ 2 * (∑ i, (frob (A i)) ^ 2) / (Fintype.card d : ℝ) ^ 2 / (N : ℝ) ^ 3 *
          ∫ x, hsNorm (gueDerivMatrix P A₀ A x)
            ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) := by
  have hcard : 0 < Fintype.card d := Fintype.card_pos_iff.mpr ‹Nonempty d›
  have hcardR : (0 : ℝ) < (Fintype.card d : ℝ) := by exact_mod_cast hcard
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hDn : ((Fintype.card d * N : ℕ) : ℝ) = (Fintype.card d : ℝ) * (N : ℝ) := by
    push_cast
    ring
  refine (variance_gueStatisticNorm_le_of_contraction P A₀ A hint).trans (le_of_eq ?_)
  rw [gueNormConst, gueScale_sq, hDn]
  field_simp

/-- **The `O(N⁻⁴)` rate of Lemma V.**  If `E[tau_N((P')²(H_N))] = O(N⁻²)`, concretely
`E[tau_N((P')²(H_N))] ≤ C' / N²`, then

`Var(Z_N) ≤ 2 (∑_i frob(A_i)²) C' / (card d) / N⁴`.

This is the form consumed by the pair (Lemma M, Lemma V) in the smooth-cutoff argument. -/
theorem lemmaV_sharp_poly_rate [Nonempty d] (P : ℝ[X]) (A₀ : Matrix d d ℂ)
    (A : ι → Matrix d d ℂ) (hA₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian)
    (hN : 0 < N) (C' : ℝ)
    (hW : (∫ x, gueStatisticNorm (P.derivative ^ 2) A₀ A x
        ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))) ≤ C' / (N : ℝ) ^ 2) :
    variance (gueStatisticNorm P A₀ A) (stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))
      ≤ 2 * (∑ i, (frob (A i)) ^ 2) * C' / (Fintype.card d : ℝ) / (N : ℝ) ^ 4 := by
  have hcard : (0 : ℝ) ≤ (Fintype.card d : ℝ) := Nat.cast_nonneg _
  have hNR : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg _
  have hS : (0 : ℝ) ≤ ∑ i, (frob (A i)) ^ 2 :=
    Finset.sum_nonneg fun i _ => sq_nonneg _
  refine (lemmaV_sharp_poly P A₀ A hA₀ hA hN).trans ?_
  have hcoef : (0 : ℝ) ≤ 2 * (∑ i, (frob (A i)) ^ 2) / (Fintype.card d : ℝ) / (N : ℝ) ^ 2 := by
    positivity
  calc 2 * (∑ i, (frob (A i)) ^ 2) / (Fintype.card d : ℝ) / (N : ℝ) ^ 2 *
        ∫ x, gueStatisticNorm (P.derivative ^ 2) A₀ A x
          ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))
      ≤ 2 * (∑ i, (frob (A i)) ^ 2) / (Fintype.card d : ℝ) / (N : ℝ) ^ 2 *
          (C' / (N : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_left hW hcoef
    _ = 2 * (∑ i, (frob (A i)) ^ 2) * C' / (Fintype.card d : ℝ) / (N : ℝ) ^ 4 := by
        ring

end

end GUEStrongConvergence
