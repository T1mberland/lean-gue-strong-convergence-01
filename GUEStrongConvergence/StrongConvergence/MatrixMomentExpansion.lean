/-
# Matrix-coefficient polynomial moments as scalar word traces

The transfer theorem of `StrongConvergence/Transfer.lean` takes as input convergence of the
normalized moments `ψ_n(P_n ^ (2k)) → φ(P∞ ^ (2k))` of a matrix-coefficient polynomial.
The probabilistic side (`GUEWordMoments`, and the word-limit modules) provides convergence
of *scalar* trace words `tr_N(word)`.

This file performs the algebraic passage between the two. The evaluation map of a matrix of
noncommuting polynomials is multiplicative, so `(P(g))^m = (P^m)(g)`; and the trace of any
matrix-polynomial evaluation is a finite linear combination of scalar word products whose
coefficients are traces of fixed complex coefficient matrices. Consequently, convergence of
all scalar trace words implies convergence of all even moments of any fixed
matrix-coefficient polynomial.

Everything here is purely algebraic: no probability and no analysis.
-/
import GUEStrongConvergence.Linearization.PolynomialBridge
import GUEStrongConvergence.StrongConvergence.Target
import GUEStrongConvergence.Analysis.MatrixState
import Mathlib.LinearAlgebra.Matrix.Trace

noncomputable section

namespace GUEStrongConvergence

open Matrix FreeProbability

variable {A : Type*} [Ring A] [Algebra ℂ A]
variable {I κ : Type*} [Fintype κ] [DecidableEq κ]

/-- **Trace of a matrix-word evaluation.** The trace is the linear combination of scalar
word products with coefficients the traces of the coefficient matrices. -/
theorem trace_matWordEval {D : Type*} [Fintype D] [DecidableEq D]
    (g : I → A) (wds : κ → List I) (coeff : κ → Matrix D D A) :
    Matrix.trace (matWordEval g wds coeff)
      = ∑ k, Matrix.trace (coeff k) * wordProd g (wds k) := by
  classical
  simp only [matWordEval, Matrix.trace_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.trace, Matrix.trace]
  simp only [Matrix.diag_apply]
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.mul_apply]
  simp only [Matrix.scalar, Matrix.diagonal, Matrix.of_apply]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    simp [hj]
  · intro h
    exact absurd (Finset.mem_univ i) h

/-- Entrywise formula for the matrix-polynomial evaluation. -/
theorem evalMatrixPoly_apply {d : ℕ} {I : Type*} {A : Type*} [Ring A] [Algebra ℂ A]
    (P : Matrix (Fin d) (Fin d) (WordPolynomial ℂ I)) (g : I → A) (i j : Fin d) :
    evalMatrixPoly P g i j = evaluate g (P i j) := rfl

/-- **The matrix-polynomial evaluation is multiplicative.** -/
theorem evalMatrixPoly_mul {d : ℕ} {I : Type*} {A : Type*} [Ring A] [Algebra ℂ A]
    (P Q : Matrix (Fin d) (Fin d) (WordPolynomial ℂ I)) (g : I → A) :
    evalMatrixPoly (P * Q) g = evalMatrixPoly P g * evalMatrixPoly Q g := by
  classical
  ext i j
  rw [evalMatrixPoly_apply, Matrix.mul_apply, map_sum]
  conv_rhs => rw [CStarMatrix.mul_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_mul, evalMatrixPoly_apply, evalMatrixPoly_apply]

/-- Powers of the evaluation are evaluations of powers. -/
theorem evalMatrixPoly_pow {d : ℕ} {I : Type*} {A : Type*} [Ring A] [Algebra ℂ A]
    (P : Matrix (Fin d) (Fin d) (WordPolynomial ℂ I)) (g : I → A) (m : ℕ) :
    (evalMatrixPoly P g) ^ m = evalMatrixPoly (P ^ m) g := by
  induction m with
  | zero =>
    ext i j
    change (1 : Matrix (Fin d) (Fin d) A) i j
      = (evaluate g) ((1 : Matrix (Fin d) (Fin d) (WordPolynomial ℂ I)) i j)
    rw [Matrix.one_apply, Matrix.one_apply]
    by_cases h : i = j <;> simp [h]
  | succ m ih =>
    rw [pow_succ, ih, pow_succ, evalMatrixPoly_mul]

/-- **Trace of a matrix-polynomial evaluation as a finite sum of scalar word products.** -/
theorem trace_evalMatrixPoly {d : ℕ} {I : Type*} {A : Type*} [Ring A] [Algebra ℂ A]
    (P : Matrix (Fin d) (Fin d) (WordPolynomial ℂ I)) (g : I → A) :
    Matrix.trace (evalMatrixPoly P g)
      = ∑ k : polyIdx P, Matrix.trace (polyCoeff P k) * wordProd g (polyW P k) := by
  classical
  have h := matWordEval_eq_evaluate_support (A := A) (𝕜 := ℂ) P g
  have h2 : (evalMatrixPoly P g : Matrix (Fin d) (Fin d) A)
      = Matrix.of (fun i j => evaluate g (P i j)) := rfl
  rw [h2, h, trace_matWordEval]

/-- **Matrix-polynomial moments are finite combinations of scalar word traces.** -/
theorem trace_pow_evalMatrixPoly {d : ℕ} {I : Type*} {A : Type*} [Ring A] [Algebra ℂ A]
    (P : Matrix (Fin d) (Fin d) (WordPolynomial ℂ I)) (g : I → A) (m : ℕ) :
    Matrix.trace ((evalMatrixPoly P g) ^ m)
      = ∑ k : polyIdx (P ^ m),
          Matrix.trace (polyCoeff (P ^ m) k) * wordProd g (polyW (P ^ m) k) := by
  rw [evalMatrixPoly_pow, trace_evalMatrixPoly]

section AlgebraMapForm

variable {A : Type*} [Ring A] [Algebra ℂ A] [StarRing A]

/-- The complex coefficient matrix at a coefficient index. -/
def polyCoeffC {D : Type*} [DecidableEq D]
    (P : Matrix D D (WordPolynomial ℂ I)) (k : polyIdx P) : Matrix D D ℂ :=
  Matrix.of fun i j => polyC P k i j

lemma polyCoeff_eq_map {D : Type*} [DecidableEq D]
    (P : Matrix D D (WordPolynomial ℂ I)) (k : polyIdx P) :
    polyCoeff (A := A) P k = (polyCoeffC P k).map (algebraMap ℂ A) := by
  ext i j
  rfl

lemma trace_polyCoeff_eq_algebraMap {D : Type*} [Fintype D] [DecidableEq D]
    (P : Matrix D D (WordPolynomial ℂ I)) (k : polyIdx P) :
    Matrix.trace (polyCoeff (A := A) P k)
      = algebraMap ℂ A (Matrix.trace (polyCoeffC P k)) := by
  rw [polyCoeff_eq_map]
  rw [Matrix.trace, Matrix.trace, map_sum]
  rfl

/-- `algebraMap`-explicit form of the trace expansion. -/
theorem trace_evalMatrixPoly_algebraMap {d : ℕ}
    (P : Matrix (Fin d) (Fin d) (WordPolynomial ℂ I)) (g : I → A) :
    Matrix.trace (evalMatrixPoly P g)
      = ∑ k : polyIdx P,
          algebraMap ℂ A (Matrix.trace (polyCoeffC P k)) * wordProd g (polyW P k) := by
  rw [trace_evalMatrixPoly]
  exact Finset.sum_congr rfl fun k _ => by rw [trace_polyCoeff_eq_algebraMap]

/-- `algebraMap`-explicit form of the moment expansion. -/
theorem trace_pow_evalMatrixPoly_algebraMap {d : ℕ}
    (P : Matrix (Fin d) (Fin d) (WordPolynomial ℂ I)) (g : I → A) (m : ℕ) :
    Matrix.trace ((evalMatrixPoly P g) ^ m)
      = ∑ k : polyIdx (P ^ m),
          algebraMap ℂ A (Matrix.trace (polyCoeffC (P ^ m) k)) *
            wordProd g (polyW (P ^ m) k) := by
  rw [trace_pow_evalMatrixPoly]
  exact Finset.sum_congr rfl fun k _ => by rw [trace_polyCoeff_eq_algebraMap]

/-- A state pulls complex-algebraMap coefficients out of a product. -/
lemma expectation_algebraMap_mul (φ : StarProbabilitySpace A) (c : ℂ) (w : A) :
    φ.expectation (algebraMap ℂ A c * w) = c * φ.expectation w := by
  rw [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, map_smul, smul_eq_mul]

/-- **State-level moment expansion.** The state applied to the trace of the `m`-th power is
the finite linear combination of scalar word expectations with fixed complex coefficients. -/
theorem expectation_trace_pow_evalMatrixPoly {d : ℕ}
    (φ : StarProbabilitySpace A)
    (P : Matrix (Fin d) (Fin d) (WordPolynomial ℂ I)) (g : I → A) (m : ℕ) :
    φ.expectation (Matrix.trace ((evalMatrixPoly P g) ^ m))
      = ∑ k : polyIdx (P ^ m),
          (Matrix.trace (polyCoeffC (P ^ m) k)) * φ.expectation (wordProd g (polyW (P ^ m) k)) := by
  rw [trace_pow_evalMatrixPoly_algebraMap, map_sum]
  exact Finset.sum_congr rfl fun k _ => expectation_algebraMap_mul φ _ _

end AlgebraMapForm

end GUEStrongConvergence
