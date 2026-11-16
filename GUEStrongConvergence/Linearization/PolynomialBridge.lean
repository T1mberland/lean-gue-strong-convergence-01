import GUEStrongConvergence.Linearization.Evaluation
import FreeProbability.Algebraic.Distribution
import Mathlib.Tactic

set_option linter.unusedSectionVars false

/-!
# Bridge to the upstream noncommuting polynomial algebra

This file connects the project's evaluation layer to the pinned upstream library's
`WordPolynomial`/`evaluate` API (`FreeProbability.Algebraic.Distribution`), so that
matrix-coefficient polynomials are represented as matrices of `WordPolynomial`s
rather than through a second, project-local polynomial type.

* `evaluate_eq_sum_of_single`: a `WordPolynomial` presented as a finite sum of
  monomials evaluates to the corresponding `wordProd` combination (reusing the
  upstream `evaluate_single`).
* `matWordEval_eq_evaluate`: the project's `matWordEval` agrees with the entrywise
  upstream evaluation of a matrix of `WordPolynomial`s.
-/

namespace GUEStrongConvergence

open Matrix FreeProbability

variable {𝕜 A : Type*} [Field 𝕜] [Ring A] [Algebra 𝕜 A]
  {I κ : Type*} [Fintype κ]

/-- **Bridge to upstream `evaluate`.** A `WordPolynomial` presented as a finite sum of
monomials evaluates to the corresponding `wordProd` combination. -/
theorem evaluate_eq_sum_of_single (wds : κ → List I) (c : κ → 𝕜) (a : I → A)
    (p : WordPolynomial 𝕜 I)
    (hp : p = ∑ k, MonoidAlgebra.single (FreeMonoid.ofList (wds k)) (c k)) :
    evaluate a p = ∑ k, c k • wordProd a (wds k) := by
  rw [hp, map_sum]
  exact Finset.sum_congr rfl fun k _ => by rw [evaluate_single, wordProd]

/-- **Matrix version of the bridge.** For a matrix of `WordPolynomial`s whose entries
are the finite sums `P i j = ∑ k, single (ofList (wds k)) (C k i j)`, entrywise
upstream evaluation equals `matWordEval` with the coefficient matrices
`(algebraMap 𝕜 A) ∘ C`. -/
theorem matWordEval_eq_evaluate {D : Type*} [Fintype D] [DecidableEq D]
    (wds : κ → List I) (C : κ → D → D → 𝕜) (a : I → A)
    (P : Matrix D D (WordPolynomial 𝕜 I))
    (hP : ∀ i j, P i j = ∑ k, MonoidAlgebra.single (FreeMonoid.ofList (wds k)) (C k i j)) :
    (Matrix.of fun i j => evaluate a (P i j))
      = matWordEval a wds (fun k => Matrix.of fun i j => algebraMap 𝕜 A (C k i j)) := by
  funext i j
  rw [Matrix.of_apply, evaluate_eq_sum_of_single wds (fun k => C k i j) a (P i j) (hP i j),
    matWordEval, Matrix.sum_apply]
  apply Finset.sum_congr rfl
  intro k _
  rw [Matrix.mul_apply, Finset.sum_eq_single j]
  · rw [Matrix.of_apply, Matrix.scalar_apply, Matrix.diagonal_apply_eq, Algebra.smul_def]
  · intro l _ hlj
    rw [Matrix.of_apply, Matrix.scalar_apply, Matrix.diagonal_apply_ne _ hlj, mul_zero]
  · intro hj
    exact absurd (Finset.mem_univ j) hj

/-! ### Support expansion

The coefficient data of a matrix of `WordPolynomial`s is read off its support, so
the conditional matrix bridge above applies unconditionally.  This closes the
last packaging step between the project's evaluation layer and the upstream
`WordPolynomial` representation. -/

section Support

variable {D : Type*}

/-- Evaluation of a `WordPolynomial` as a finite sum over its support. -/
theorem evaluate_eq_support_sum (a : I → A) (p : WordPolynomial 𝕜 I) :
    evaluate a p = ∑ w ∈ p.coeff.support, p.coeff w • wordProd a (FreeMonoid.toList w) := by
  conv_lhs => rw [← MonoidAlgebra.sum_coeff_single p]
  rw [Finsupp.sum, map_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [show MonoidAlgebra.single w (p.coeff w) =
      MonoidAlgebra.single (FreeMonoid.ofList (FreeMonoid.toList w)) (p.coeff w) from by
        rw [FreeMonoid.ofList_toList]]
  rw [evaluate_single]
  rfl

/-- The coefficient index type of a matrix of `WordPolynomial`s: one point for
each `(i, j)` and each word in the support of `P i j`. -/
abbrev polyIdx (P : Matrix D D (WordPolynomial 𝕜 I)) : Type _ :=
  Σ p : D × D, {w : FreeMonoid I // w ∈ (P p.1 p.2).coeff.support}

/-- The word attached to a coefficient index. -/
def polyW (P : Matrix D D (WordPolynomial 𝕜 I)) (k : polyIdx P) : List I :=
  FreeMonoid.toList k.2.1

/-- The scalar coefficient attached to a coefficient index. -/
def polyC [DecidableEq D] (P : Matrix D D (WordPolynomial 𝕜 I)) (k : polyIdx P)
    (i j : D) : 𝕜 :=
  if (i, j) = k.1 then (P k.1.1 k.1.2).coeff k.2.1 else 0

/-- The coefficient matrix attached to a coefficient index. -/
def polyCoeff [DecidableEq D] (P : Matrix D D (WordPolynomial 𝕜 I)) (k : polyIdx P) :
    Matrix D D A :=
  Matrix.of fun i j => algebraMap 𝕜 A (polyC P k i j)

/-- **Expansion of `P` over its support.**  A matrix of `WordPolynomial`s is the
finite sum of its monomials. -/
theorem polyIdx_expansion [Fintype D] [DecidableEq D]
    (P : Matrix D D (WordPolynomial 𝕜 I)) (i j : D) :
    P i j = ∑ k : polyIdx P,
      MonoidAlgebra.single (FreeMonoid.ofList (polyW P k)) (polyC P k i j) := by
  classical
  have huniv : (Finset.univ : Finset (polyIdx P)) =
      Finset.univ.sigma (fun _ => Finset.univ) := by
    ext x; simp
  rw [huniv, Finset.sum_sigma, Finset.sum_eq_single (i, j)]
  · simp only [polyC, polyW, ↓reduceIte]
    rw [Finset.univ_eq_attach, Finset.sum_attach (P i j).coeff.support
      (fun y => MonoidAlgebra.single (FreeMonoid.ofList (FreeMonoid.toList y))
        ((P i j).coeff y))]
    rw [show (∑ w ∈ (P i j).coeff.support,
          MonoidAlgebra.single (FreeMonoid.ofList (FreeMonoid.toList w))
            ((P i j).coeff w))
        = ∑ w ∈ (P i j).coeff.support, MonoidAlgebra.single w ((P i j).coeff w) from
      Finset.sum_congr rfl fun w _ => by rw [FreeMonoid.ofList_toList]]
    exact (MonoidAlgebra.sum_coeff_single (P i j)).symm
  · intro p _ hp
    refine Finset.sum_eq_zero fun w _ => ?_
    simp only [polyC, polyW, ite_eq_right (Ne.symm hp), MonoidAlgebra.single_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- **Unconditional matrix bridge.**  A matrix of `WordPolynomial`s evaluates to
`matWordEval` with the coefficient data extracted from its support. -/
theorem matWordEval_eq_evaluate_support [Fintype D] [DecidableEq D]
    (P : Matrix D D (WordPolynomial 𝕜 I)) (a : I → A) :
    (Matrix.of fun i j => evaluate a (P i j)) = matWordEval a (polyW P) (polyCoeff P) :=
  matWordEval_eq_evaluate (polyW P) (polyC P) a P (polyIdx_expansion P)

end Support

end GUEStrongConvergence
