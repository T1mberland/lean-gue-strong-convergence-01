/-
# Analyticity of the matrix-argument Cauchy transform in its argument

The HT05 physical-branch identification needs `AnalyticOnNhd ℂ (fun z =>
operatorMatrixArgumentCauchy A (Λ z - A₀)) U`.  This file proves the argument-analyticity

  `IsUnit (operatorMatrixDifference C B) → AnalyticAt ℂ (fun B => operatorMatrixArgumentCauchy C B) B`

and its consequence for an analytic self-energy branch `B` with `IsUnit (operatorMatrixDifference
A (B z - A₀))` on `U`.  The proof is the chain
`B ↦ (B⊗1 - ∑ A_i⊗s_i)` (affine) → `Ring.inverse` (analytic at units) → vacuum expectation
(a continuous linear map).  The vacuum expectation is re-packaged as a continuous linear map
`CStarMatrix →L[ℂ] Matrix d d ℂ` whose codomain carries the `Matrix.Norms.Operator` norm
(the norm used by the uniqueness theorems), with the explicit bound `(card d)^2`.

No `sorry`, no new axioms.
-/
import GUEStrongConvergence.StrongConvergence.HT05AnalyticOperator
import GUEStrongConvergence.StrongConvergence.HT05PhysicalBranch
import FreeProbability.OperatorValued.MatrixArgumentDyson
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.Topology.Algebra.Module.FiniteDimension

open MeasureTheory ProbabilityTheory Matrix Filter
open FreeProbability FreeProbability.Fock
open scoped Matrix.Norms.Operator ComplexOrder Topology NNReal ENNReal

set_option maxHeartbeats 4000000

namespace GUEStrongConvergence

noncomputable section

variable {ι d : Type*} {N : ℕ} [Fintype ι] [Fintype d] [DecidableEq d] [DecidableEq ι]

noncomputable local instance ht05ArgPartialOrder :
    PartialOrder (WordSpace ι →L[ℂ] WordSpace ι) :=
  CStarAlgebra.spectralOrder _
noncomputable local instance ht05ArgStarOrderedRing :
    StarOrderedRing (WordSpace ι →L[ℂ] WordSpace ι) :=
  CStarAlgebra.spectralOrderedRing _

theorem ht05_linfty_opNorm_le_sum_entries (N : Matrix d d ℂ) :
    ‖N‖ ≤ ∑ i, ∑ j, ‖N i j‖ := by
  have hsup : (Finset.univ.sup fun i : d => ∑ j, ‖N i j‖₊) ≤ ∑ i, ∑ j, ‖N i j‖₊ := by
    refine Finset.sup_le fun i _ => ?_
    exact Finset.single_le_sum (f := fun i : d => ∑ j, ‖N i j‖₊)
      (fun i _ => Finset.sum_nonneg fun j _ => by positivity) (Finset.mem_univ i)
  calc ‖N‖ = ((Finset.univ.sup fun i : d => ∑ j, ‖N i j‖₊ : ℝ≥0) : ℝ) :=
        Matrix.linfty_opNorm_def N
    _ ≤ ((∑ i, ∑ j, ‖N i j‖₊ : ℝ≥0) : ℝ) := by exact_mod_cast hsup
    _ = ∑ i, ∑ j, ‖N i j‖ := by push_cast; rfl

theorem ht05_norm_matrixExpectation_le (M : CStarMatrix d d (WordSpace ι →L[ℂ] WordSpace ι)) :
    ‖matrixExpectation (vacuumState ι).toProbabilitySpace (CStarMatrix.ofMatrix.symm M)‖ ≤
      (Fintype.card d : ℝ) ^ 2 * ‖M‖ := by
  refine (ht05_linfty_opNorm_le_sum_entries _).trans ?_
  have h1 : ∀ i j : d, ‖matrixExpectation (vacuumState ι).toProbabilitySpace
      (CStarMatrix.ofMatrix.symm M) i j‖ ≤ ‖M‖ := by
    intro i j
    rw [matrixExpectation_apply]
    exact (norm_vacuumExpectation_le (M i j)).trans
      (CStarMatrix.norm_entry_le_norm (M := M) (i := i) (j := j))
  calc ∑ i, ∑ j, ‖matrixExpectation (vacuumState ι).toProbabilitySpace
        (CStarMatrix.ofMatrix.symm M) i j‖
      ≤ ∑ i, ∑ j, ‖M‖ := by
        refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => h1 i j
    _ = (Fintype.card d : ℝ) ^ 2 * ‖M‖ := by
        simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
        ring

def ht05_matrixExpectationOpCLM :
    CStarMatrix d d (WordSpace ι →L[ℂ] WordSpace ι) →L[ℂ] Matrix d d ℂ :=
  (LinearMap.mkContinuous
    { toFun := fun M => matrixExpectation (vacuumState ι).toProbabilitySpace (CStarMatrix.ofMatrix.symm M)
      map_add' := by
        intro x y
        have h : CStarMatrix.ofMatrix.symm (x + y) =
            CStarMatrix.ofMatrix.symm x + CStarMatrix.ofMatrix.symm y := rfl
        rw [h, map_add]
      map_smul' := by
        intro c x
        have h : CStarMatrix.ofMatrix.symm (c • x) =
            c • CStarMatrix.ofMatrix.symm x := rfl
        rw [h, map_smul, RingHom.id_apply] }
    ((Fintype.card d : ℝ) ^ 2)
    (fun M => by
      simpa using ht05_norm_matrixExpectation_le (ι := ι) M))

example (M : CStarMatrix d d (WordSpace ι →L[ℂ] WordSpace ι)) :
    ht05_matrixExpectationOpCLM M =
      matrixExpectation (vacuumState ι).toProbabilitySpace (CStarMatrix.ofMatrix.symm M) := rfl

/-- Linear part of `B ↦ operatorMatrixDifference C B`. -/
def ht05_argLinCLM : Matrix d d ℂ →L[ℂ] CStarMatrix d d (WordSpace ι →L[ℂ] WordSpace ι) :=
  let lₗ : Matrix d d ℂ →ₗ[ℂ] CStarMatrix d d (WordSpace ι →L[ℂ] WordSpace ι) :=
    { toFun := fun B => CStarMatrix.ofMatrix
        (scalarMatrixEmbedding (A := WordSpace ι →L[ℂ] WordSpace ι) B)
      map_add' := by
        intro x y
        have h : CStarMatrix.ofMatrix
            (scalarMatrixEmbedding (A := WordSpace ι →L[ℂ] WordSpace ι) (x + y)) =
            CStarMatrix.ofMatrix
              (scalarMatrixEmbedding (A := WordSpace ι →L[ℂ] WordSpace ι) x) +
            CStarMatrix.ofMatrix
              (scalarMatrixEmbedding (A := WordSpace ι →L[ℂ] WordSpace ι) y) := by
          rw [map_add]
          rfl
        exact h
      map_smul' := by
        intro c x
        have h : CStarMatrix.ofMatrix
            (scalarMatrixEmbedding (A := WordSpace ι →L[ℂ] WordSpace ι) (c • x)) =
            c • CStarMatrix.ofMatrix
              (scalarMatrixEmbedding (A := WordSpace ι →L[ℂ] WordSpace ι) x) := by
          rw [map_smul]
          rfl
        exact h }
  ⟨lₗ, lₗ.continuous_of_finiteDimensional⟩

theorem analyticAt_operatorMatrixArgumentCauchy (C : ι → Matrix d d ℂ) (B : Matrix d d ℂ)
    (hB : IsUnit (operatorMatrixDifference C B)) :
    AnalyticAt ℂ (fun B => operatorMatrixArgumentCauchy C B) B := by
  have hlin : AnalyticAt ℂ (fun X : Matrix d d ℂ =>
      CStarMatrix.ofMatrix (scalarMatrixEmbedding (A := WordSpace ι →L[ℂ] WordSpace ι) X)) B := by
    refine (ht05_argLinCLM.analyticAt B).congr ?_
    exact Filter.EventuallyEq.of_eq rfl
  have haff : AnalyticAt ℂ (fun X : Matrix d d ℂ => operatorMatrixDifference C X) B := by
    have hsub : AnalyticAt ℂ (fun X : Matrix d d ℂ =>
        CStarMatrix.ofMatrix (scalarMatrixEmbedding (A := WordSpace ι →L[ℂ] WordSpace ι) X) -
          CStarMatrix.ofMatrix (matrixLinearCombination semicircular C)) B :=
      hlin.sub analyticAt_const
    refine hsub.congr ?_
    filter_upwards with X
    rfl
  obtain ⟨u, hu⟩ := hB
  have hinv : AnalyticAt ℂ (fun X : Matrix d d ℂ =>
      Ring.inverse (operatorMatrixDifference C X)) B := by
    have hu' : AnalyticAt ℂ Ring.inverse (operatorMatrixDifference C B) := by
      rw [← hu]
      exact analyticAt_inverse u
    refine (hu'.comp haff).congr ?_
    filter_upwards with X
    rfl
  have hfin : AnalyticAt ℂ (fun X : Matrix d d ℂ =>
      ht05_matrixExpectationOpCLM (Ring.inverse (operatorMatrixDifference C X))) B := by
    have hcomp := AnalyticAt.comp
      (f := fun X : Matrix d d ℂ => Ring.inverse (operatorMatrixDifference C X)) (x := B)
      (g := fun y => ht05_matrixExpectationOpCLM y)
      (ht05_matrixExpectationOpCLM.analyticAt (Ring.inverse (operatorMatrixDifference C B))) hinv
    refine hcomp.congr ?_
    filter_upwards with X
    rfl
  refine hfin.congr ?_
  filter_upwards with X
  rfl

/-- Analyticity of the matrix-argument Cauchy transform along an analytic self-energy branch. -/
theorem analyticOnNhd_operatorMatrixArgumentCauchy_comp
    (A : ι → Matrix d d ℂ) (B : ℂ → Matrix d d ℂ) (A₀ : Matrix d d ℂ) (U : Set ℂ)
    (hAnB : AnalyticOnNhd ℂ B U)
    (hUnit : ∀ z ∈ U, IsUnit (operatorMatrixDifference A (B z - A₀))) :
    AnalyticOnNhd ℂ (fun z => operatorMatrixArgumentCauchy A (B z - A₀)) U := by
  intro z hz
  have hinner : AnalyticAt ℂ (fun w : ℂ => B w - A₀) z :=
    (hAnB z hz).sub analyticAt_const
  have houter : AnalyticAt ℂ (fun X : Matrix d d ℂ => operatorMatrixArgumentCauchy A X)
      (B z - A₀) :=
    analyticAt_operatorMatrixArgumentCauchy A (B z - A₀) (hUnit z hz)
  exact AnalyticAt.comp (f := fun w : ℂ => B w - A₀) (x := z)
    (g := fun X : Matrix d d ℂ => operatorMatrixArgumentCauchy A X) houter hinner


/-- **Physical branch identification on the tube, with argument-analyticity discharged.**

Same as `gueResolventMean_eq_operatorMatrixArgumentCauchy_on_tube`, but the analyticity of
`z ↦ operatorMatrixArgumentCauchy A (B z - A₀)` is derived from analyticity of `B` and
invertibility of the operator-valued difference, rather than assumed. -/
theorem gueResolventMean_eq_operatorMatrixArgumentCauchy_on_tube_of_analytic
    (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    (hA₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian)
    (B : ℂ → Matrix d d ℂ) (T : ℝ)
    (hAnM : AnalyticOnNhd ℂ (gueResolventMean (N := N) A₀ A) (tubeRegion T))
    (hAnB : AnalyticOnNhd ℂ B (tubeRegion T))
    (hDyson : ∀ z ∈ tubeRegion T,
      (B z - A₀ - matrixCovariance A (gueResolventMean (N := N) A₀ A z)) *
        gueResolventMean (N := N) A₀ A z = 1)
    (hUnit : ∀ z ∈ tubeRegion T, IsUnit (operatorMatrixDifference A (B z - A₀)))
    (hMone : Filter.Tendsto (fun z => z • gueResolventMean (N := N) A₀ A z)
      (Bornology.cobounded ℂ ⊓ Filter.principal (tubeRegion T)) (𝓝 (1 : Matrix d d ℂ)))
    (hGone : Filter.Tendsto (fun z => z • operatorMatrixArgumentCauchy A (B z - A₀))
      (Bornology.cobounded ℂ ⊓ Filter.principal (tubeRegion T)) (𝓝 (1 : Matrix d d ℂ))) :
    Set.EqOn (gueResolventMean (N := N) A₀ A)
      (fun z => operatorMatrixArgumentCauchy A (B z - A₀)) (tubeRegion T) :=
  gueResolventMean_eq_operatorMatrixArgumentCauchy_on_tube A₀ A hA₀ hA B T hAnM
    (analyticOnNhd_operatorMatrixArgumentCauchy_comp A B A₀ (tubeRegion T) hAnB hUnit)
    hDyson hUnit hMone hGone

end

end GUEStrongConvergence
