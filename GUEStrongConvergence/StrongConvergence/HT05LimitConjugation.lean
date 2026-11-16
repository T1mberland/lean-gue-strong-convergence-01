/-
# Conjugation symmetry of the limit matrix Cauchy transform

`Probability/ResolventConj.lean` reduces the lower half-plane weighted strip bound to the
upper half-plane one by the *limit-side* conjugation symmetry
`star (operatorMatrixPencilCauchy A₀ A z) = operatorMatrixPencilCauchy A₀ A (star z)`.
That symmetry was recorded there as blocked on instance bookkeeping; this file proves it.

The three ingredients are:

* `star_resolvent` — `star (resolvent M z) = resolvent (star M) (star z)` in a complex
  C⋆-algebra, from `resolvent = Ring.inverse (algebraMap z - ·)` and `Ring.inverse_star`;
* `star_resolventMatrixArgument` — the same statement transported through the star-algebra
  equivalence `CStarMatrix.ofMatrixStarAlgEquiv` to the matrix-valued operator resolvent;
* `operatorMatrixPencil_star` — the affine Fock pencil is self-adjoint for Hermitian
  coefficients, so `star (operatorMatrixPencil A₀ A) = operatorMatrixPencil A₀ A`.

No `sorry`, no new axioms.
-/
import GUEStrongConvergence.Probability.ResolventConj
import GUEStrongConvergence.StrongConvergence.HT05Comparison
import FreeProbability.OperatorValued.MatrixCauchyImaginary

open MeasureTheory ProbabilityTheory Matrix Filter
open FreeProbability FreeProbability.Fock
open scoped ENNReal NNReal Topology

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

namespace GUEStrongConvergence

variable {ι d : Type*} [Fintype ι] [Fintype d] [DecidableEq d] [DecidableEq ι]

noncomputable local instance ht05CLimConjPartialOrder :
    PartialOrder (WordSpace ι →L[ℂ] WordSpace ι) :=
  CStarAlgebra.spectralOrder _
noncomputable local instance ht05CLimConjStarOrderedRing :
    StarOrderedRing (WordSpace ι →L[ℂ] WordSpace ι) :=
  CStarAlgebra.spectralOrderedRing _

/-- **Conjugation of the resolvent**: `star (resolvent M z) = resolvent M (star z)` for a
self-adjoint `M`.  This is `Probability/ResolventConj.lean`'s `star_resolvent_of_star_eq`
instantiated at the operator-valued matrix algebra `CStarMatrix d d (WordSpace ι →L[ℂ] …)`; the
explicit type annotation `A :=` is what aligns the two `Star` instance paths. -/
theorem star_resolvent (M : CStarMatrix d d (WordSpace ι →L[ℂ] WordSpace ι)) (z : ℂ)
    (hM : star M = M) :
    star (resolvent M z) = resolvent M (star z) :=
  star_resolvent_of_star_eq (A := CStarMatrix d d (WordSpace ι →L[ℂ] WordSpace ι)) (P := M) hM z

/-- **Conjugation of the matrix-valued operator resolvent**, transported through the
star-algebra equivalence `CStarMatrix.ofMatrixStarAlgEquiv`. -/
theorem star_resolvent_matrix (M : CStarMatrix d d (WordSpace ι →L[ℂ] WordSpace ι)) (z : ℂ)
    (hM : star M = M) :
    star (CStarMatrix.ofMatrix.symm (resolvent M z)) =
      CStarMatrix.ofMatrix.symm (resolvent M (star z)) := by
  have hstar : ∀ X : CStarMatrix d d (WordSpace ι →L[ℂ] WordSpace ι),
      star (CStarMatrix.ofMatrix.symm X) = CStarMatrix.ofMatrix.symm (star X) := fun X => rfl
  rw [hstar, star_resolvent M z hM]

/-- The vacuum expectation commutes with the conjugate transpose. -/
theorem star_matrixExpectation_vacuum (T : Matrix d d (WordSpace ι →L[ℂ] WordSpace ι)) :
    star (matrixExpectation (vacuumState ι).toProbabilitySpace T) =
      matrixExpectation (vacuumState ι).toProbabilitySpace (star T) :=
  (matrixExpectation_conjTranspose (vacuumState ι) T).symm

/-- **The affine Fock pencil is self-adjoint** for Hermitian coefficients. -/
theorem operatorMatrixPencil_star (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    (hA₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian) :
    star (operatorMatrixPencil A₀ A) = operatorMatrixPencil A₀ A :=
  (operatorMatrixPencil_isSelfAdjoint A₀ A hA₀ hA).star_eq

/-- **Conjugation symmetry of the limit Cauchy transform**:
`star (operatorMatrixPencilCauchy A₀ A z) = operatorMatrixPencilCauchy A₀ A (star z)`. -/
theorem operatorMatrixPencilCauchy_star (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    (hA₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian) (z : ℂ) :
    star (operatorMatrixPencilCauchy A₀ A z) =
      operatorMatrixPencilCauchy A₀ A (star z) := by
  have hM : star (operatorMatrixPencil A₀ A) = operatorMatrixPencil A₀ A :=
    operatorMatrixPencil_star A₀ A hA₀ hA
  unfold operatorMatrixPencilCauchy
  calc star (matrixExpectation (vacuumState ι).toProbabilitySpace
        (CStarMatrix.ofMatrix.symm (resolvent (operatorMatrixPencil A₀ A) z)))
      = matrixExpectation (vacuumState ι).toProbabilitySpace
          (star (CStarMatrix.ofMatrix.symm (resolvent (operatorMatrixPencil A₀ A) z))) :=
        star_matrixExpectation_vacuum _
    _ = matrixExpectation (vacuumState ι).toProbabilitySpace
          (CStarMatrix.ofMatrix.symm (resolvent (operatorMatrixPencil A₀ A) (star z))) := by
        rw [star_resolvent_matrix (operatorMatrixPencil A₀ A) z hM]

/-- **The limit-side conjugation hypothesis of `Probability/ResolventConj.lean` is a theorem.** -/
theorem operatorMatrixPencilCauchy_star_unconditional (A₀ : Matrix d d ℂ)
    (A : ι → Matrix d d ℂ) (hA₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian) :
    ∀ z : ℂ, star (operatorMatrixPencilCauchy A₀ A z) =
      operatorMatrixPencilCauchy A₀ A (star z) :=
  fun z => operatorMatrixPencilCauchy_star A₀ A hA₀ hA z

/-- **The honest weighted strip bound, with no limit-side hypothesis.**

This removes the conjugation hypothesis `hG` from
`HT05Comparison.weightedStripBoundProven_of_comparison`: the lower half-plane now follows from
the theorem `operatorMatrixPencilCauchy_star_unconditional`. -/
theorem weightedStripBoundProven_of_comparison_unconditional [Nonempty d]
    (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ) (hA₀ : A₀.IsHermitian)
    (hA : ∀ i, (A i).IsHermitian) {η₀ Cst : ℝ} (hCst : 0 ≤ Cst) (hη₀ : 0 < η₀)
    (Λ : ℕ → ℂ → Matrix d d ℂ)
    (hΛ : ∀ᶠ N : ℕ in Filter.atTop, ∀ z : ℂ, 0 < z.im → |z.im| < η₀ →
      frob (Λ N z - z • (1 : Matrix d d ℂ)) ≤
        Cst * z.im ^ (-(5 : ℝ)) / (N : ℝ) ^ 2)
    (hgood : ∀ᶠ N : ℕ in Filter.atTop, ∀ z : ℂ, 0 < z.im → |z.im| < η₀ →
      Cst * z.im ^ (-(6 : ℝ)) / (N : ℝ) ^ 2 < 1 / 2 →
      gueResolventMean (N := N) A₀ A z = operatorMatrixArgumentCauchy A (Λ N z - A₀) ∧
        IsUnit (operatorMatrixDifference A (Λ N z - A₀)) ∧
        ‖CStarMatrix.ofMatrix (operatorMatrixArgumentResolvent A (Λ N z - A₀))‖ ≤ 2 / z.im) :
    WeightedStripBoundProven A₀ A η₀ 1 (4 * (Fintype.card d : ℝ) ^ 2 * Cst) :=
  weightedStripBoundProven_of_comparison A₀ A hA₀ hA hCst hη₀ Λ hΛ hgood
    (operatorMatrixPencilCauchy_star_unconditional A₀ A hA₀ hA)

end GUEStrongConvergence
