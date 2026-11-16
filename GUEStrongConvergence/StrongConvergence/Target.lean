/-
# Target statement of almost-sure operator-norm strong convergence

This module fixes the *specification* of the project's target theorem with its exact
quantifier order, together with the concrete evaluation maps it refers to. It does not
assert the theorem; it records the statement that a future proof must establish.

The statement is: for almost every sample point of the common Gaussian space, for every
fixed coefficient dimension `d > 0` and every fixed matrix-coefficient noncommutative
`*`-polynomial `P`, the operator norm of `P` evaluated at the normalized GUE tuple
converges to the operator norm of `P` evaluated at the free semicircular family.

No coefficient dimension, degree, or polynomial is allowed to depend on `N`.
-/
import GUEStrongConvergence.Probability.CommonSpace
import FreeProbability.Fock.CStarModel
import FreeProbability.Fock.ClosedGeneratedState
import FreeProbability.Algebraic.Distribution
import Mathlib.Analysis.CStarAlgebra.CStarMatrix

noncomputable section

namespace GUEStrongConvergence

open Filter MeasureTheory FreeProbability FreeProbability.Fock
open scoped ComplexOrder Topology

/-- The limiting free semicircular family, in the closed C\*-algebra it generates. -/
def semicircularFamily (r : ℕ) : Fin r → closedSemicircularAlgebra (Fin r) :=
  fun i => closedSemicircular i

/-- The normalized GUE tuple at dimension `N` on the common probability space, as elements
of the operator-norm C\*-algebra of matrices. -/
def gueFamily (r N : ℕ) (x : CommonSpace (Fin r)) :
    Fin r → CStarMatrix (Fin N) (Fin N) ℂ :=
  fun i => CStarMatrix.ofMatrix (gueMatrixOn x N i)

/-- Evaluation of a matrix-coefficient noncommutative polynomial: entry `(i,j)` is the
evaluation of the polynomial in that matrix entry at the tuple `g`. -/
def evalMatrixPoly {d : ℕ} {I : Type*} {A : Type*} [Ring A] [Algebra ℂ A]
    (P : Matrix (Fin d) (Fin d) (WordPolynomial ℂ I)) (g : I → A) :
    CStarMatrix (Fin d) (Fin d) A :=
  CStarMatrix.ofMatrix fun i j => evaluate g (P i j)

/-- The operator norm of the limiting evaluation. The canonical C\*-spectral order on the
closed semicircular algebra is installed locally so that the operator norm instance on
`CStarMatrix` applies. -/
noncomputable def limitNorm {r d : ℕ}
    (P : Matrix (Fin d) (Fin d) (WordPolynomial ℂ (Fin r))) : ℝ := by
  letI : PartialOrder (closedSemicircularAlgebra (Fin r)) :=
    CStarAlgebra.spectralOrder (closedSemicircularAlgebra (Fin r))
  letI : StarOrderedRing (closedSemicircularAlgebra (Fin r)) :=
    CStarAlgebra.spectralOrderedRing (closedSemicircularAlgebra (Fin r))
  exact ‖evalMatrixPoly P (semicircularFamily r)‖

/-- The operator norm of the limiting evaluation of an ordinary polynomial at the first
semicircular generator. -/
noncomputable def scalarLimitNorm {r : ℕ} (hr : 0 < r) (p : Polynomial ℂ) : ℝ := by
  letI : PartialOrder (closedSemicircularAlgebra (Fin r)) :=
    CStarAlgebra.spectralOrder (closedSemicircularAlgebra (Fin r))
  letI : StarOrderedRing (closedSemicircularAlgebra (Fin r)) :=
    CStarAlgebra.spectralOrderedRing (closedSemicircularAlgebra (Fin r))
  exact ‖Polynomial.aeval (closedSemicircular (⟨0, hr⟩ : Fin r)) p‖

/-- **Target specification (II.C).** Almost surely, for every fixed coefficient dimension
and every fixed matrix-coefficient noncommutative polynomial, the operator norm of the
evaluated polynomial converges to the operator norm of the limiting evaluation. -/
def GUEStrongConvergenceStatement (r : ℕ) : Prop :=
  ∀ᵐ x ∂(commonGaussianMeasure (Fin r)),
    ∀ (d : ℕ) (_ : 0 < d)
      (P : Matrix (Fin d) (Fin d) (WordPolynomial ℂ (Fin r))),
      Tendsto (fun N : ℕ => ‖evalMatrixPoly P (gueFamily r N x)‖) atTop (𝓝 (limitNorm P))

/-- Scalar ordinary-polynomial specialization of the target: for a single GUE matrix and an
ordinary polynomial with complex coefficients, the operator norm converges. -/
def ScalarPolynomialStatement (r : ℕ) : Prop :=
  ∀ᵐ x ∂(commonGaussianMeasure (Fin r)),
    ∀ (hr : 0 < r) (p : Polynomial ℂ),
      Tendsto (fun N : ℕ =>
          ‖Polynomial.aeval
            (CStarMatrix.ofMatrix (gueMatrixOn x N (⟨0, hr⟩ : Fin r))) p‖) atTop
        (𝓝 (scalarLimitNorm hr p))

end GUEStrongConvergence
