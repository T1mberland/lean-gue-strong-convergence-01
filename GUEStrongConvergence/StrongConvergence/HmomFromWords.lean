/-
# Amplified-state trace formula

Helper for the word-to-matrix-moment interface: the matrix-amplified state
`tr_D ⊗ φ` evaluated at `M` is `(card D)⁻¹ * φ (trace M)`.
-/
import GUEStrongConvergence.Analysis.MatrixState

noncomputable section

open Matrix FreeProbability
open scoped ComplexOrder

namespace GUEStrongConvergence

variable {D : Type*} [Fintype D] [DecidableEq D] [Nonempty D]

/-- The matrix-amplified state, evaluated at a matrix `M`, is
`(card D)⁻¹ * φ(trace M)`. -/
theorem matrixStarState_expectation_eq_trace
    {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    (φ : StarProbabilitySpace A) (M : CStarMatrix D D A) :
    (matrixStarState (D := D) φ).expectation M
      = ((Fintype.card D : ℂ))⁻¹ * φ.expectation (Matrix.trace M) := by
  change ((Fintype.card D : ℂ))⁻¹ * (∑ i : D, φ.expectation (M i i))
    = ((Fintype.card D : ℂ))⁻¹ * φ.expectation (Matrix.trace M)
  simp only [Matrix.trace, Matrix.diag, map_sum]

end GUEStrongConvergence
