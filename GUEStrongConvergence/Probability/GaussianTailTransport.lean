/-
# Gaussian tail bounds on arbitrary finite Euclidean spaces

`LogSobolev` states its dimension-free Gaussian concentration inequalities on
`EuclideanSpace ℝ (Fin n)` with the measure `standardGaussian n`.  The GUE
coordinate space is `EuclideanSpace ℝ (GUECoord ι N)` with Mathlib's
basis-independent `stdGaussian`.  This file transports the tail bounds across a
linearly isometric equivalence of index types, so that the concentration library
can be applied directly to GUE observables.
-/
import LogSobolev.Concentration.Gaussian
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Analysis.Normed.Lp.PiLp

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology

namespace GUEStrongConvergence

noncomputable section

/-- The standard Gaussian of `LogSobolev` on `EuclideanSpace ℝ (Fin n)` coincides with
Mathlib's basis-independent `stdGaussian`. -/
theorem standardGaussian_eq_stdGaussian (n : ℕ) :
    LogSobolev.standardGaussian n = stdGaussian (EuclideanSpace ℝ (Fin n)) := by
  rw [LogSobolev.standardGaussian, GaussianMeasure.stdGaussianE,
    GaussianMeasure.stdGaussianPi, ← map_pi_eq_stdGaussian (ι := Fin n)]
  congr 1

/-- Pushing `standardGaussian` forward along the isometry of Euclidean spaces induced
by an equivalence of index types gives Mathlib's `stdGaussian`. -/
theorem standardGaussian_map_piLpCongrLeft {κ : Type*} [Fintype κ] :
    (LogSobolev.standardGaussian (Fintype.card κ)).map
        (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Fintype.equivFin κ).symm) =
      stdGaussian (EuclideanSpace ℝ κ) := by
  rw [standardGaussian_eq_stdGaussian]
  exact stdGaussian_map _

/-- Dimension-free two-sided Gaussian tail for globally Lipschitz real functions on
`EuclideanSpace ℝ κ`, for an arbitrary finite index type `κ`, with respect to
Mathlib's `stdGaussian`. -/
theorem gaussian_measure_abs_ge_le_stdGaussian {κ : Type*} [Fintype κ] {K : ℝ≥0}
    {f : EuclideanSpace ℝ κ → ℝ} (hf : LipschitzWith K f) {r : ℝ} (hr : 0 ≤ r) :
    (stdGaussian (EuclideanSpace ℝ κ)).real
        {x | r ≤ |f x - ∫ y, f y ∂(stdGaussian (EuclideanSpace ℝ κ))|} ≤
      2 * Real.exp (-r ^ 2 / (2 * (K : ℝ) ^ 2)) := by
  classical
  let n := Fintype.card κ
  let e : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ κ :=
    LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Fintype.equivFin κ).symm
  have hmap : (stdGaussian (EuclideanSpace ℝ (Fin n))).map e =
      stdGaussian (EuclideanSpace ℝ κ) := stdGaussian_map e
  have hbase : LogSobolev.standardGaussian n =
      stdGaussian (EuclideanSpace ℝ (Fin n)) := standardGaussian_eq_stdGaussian n
  have hemes : MeasurableEmbedding e := e.continuous.measurableEmbedding e.injective
  have hmem : ∫ y, f y ∂(stdGaussian (EuclideanSpace ℝ κ)) =
      ∫ y, f (e y) ∂(stdGaussian (EuclideanSpace ℝ (Fin n))) := by
    rw [← hmap, hemes.integral_map f]
  have hmeas : MeasurableSet
      {x : EuclideanSpace ℝ κ | r ≤ |f x - ∫ y, f (e y) ∂(stdGaussian (EuclideanSpace ℝ (Fin n)))|} :=
    measurableSet_le measurable_const
      ((hf.continuous.sub continuous_const).abs.measurable)
  have hreal : (stdGaussian (EuclideanSpace ℝ κ)).real
        {x | r ≤ |f x - ∫ y, f (e y) ∂(stdGaussian (EuclideanSpace ℝ (Fin n)))|} =
      (stdGaussian (EuclideanSpace ℝ (Fin n))).real
        {y | r ≤ |f (e y) -
          ∫ y, f (e y) ∂(stdGaussian (EuclideanSpace ℝ (Fin n)))|} := by
    rw [← hmap, Measure.real, Measure.real, Measure.map_apply e.continuous.measurable hmeas]
    congr 1
  have hfe : LipschitzWith K (fun y => f (e y)) := by
    have h := hf.comp e.lipschitz
    convert h using 1
    · simp
    · funext y
      rfl
  have hbase2 := LogSobolev.gaussian_measure_abs_ge_le (K := K)
    (f := fun y => f (e y)) hfe hr
  rw [hbase] at hbase2
  rw [hmem, hreal]
  exact hbase2

end

end GUEStrongConvergence
