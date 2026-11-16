/-
# Borel–Cantelli on the common Gaussian space

The almost-sure strong-convergence statements of the project live on the countable
product `commonGaussianMeasure ι` of the finite GUE blocks.  This file provides the
standard reduction: if the `N`-th block events have summable Gaussian probabilities,
then almost surely only finitely many of them occur, i.e. eventually the `N`-th block
avoids the bad set.
-/
import GUEStrongConvergence.Probability.CommonSpace
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology

namespace GUEStrongConvergence

noncomputable section

variable {ι : Type*} [Fintype ι]

/-- **First Borel–Cantelli lemma on the common Gaussian space.**  If the probability of
the `N`-th block event is summable, then almost surely the event fails eventually. -/
theorem ae_eventually_not_mem_of_summable
    (P : (N : ℕ) → Set (EuclideanSpace ℝ (GUECoord ι N)))
    (hP : ∀ N, MeasurableSet (P N))
    (h : Summable fun N => (stdGaussian (EuclideanSpace ℝ (GUECoord ι N))).real (P N)) :
    ∀ᵐ x ∂(commonGaussianMeasure ι), ∀ᶠ N in atTop, x N ∉ P N := by
  classical
  -- the event in the product space
  set s : ℕ → Set (CommonSpace ι) := fun N => {x | x N ∈ P N} with hs
  have hsm : ∀ N, MeasurableSet (s N) := by
    intro N
    exact (measurable_pi_apply N) (hP N)
  -- rewrite the product measure of each event as the block probability
  have hprob : ∀ N, (commonGaussianMeasure ι) (s N) =
      (stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) (P N) := by
    intro N
    rw [hs]
    simp only
    rw [← commonGaussianMeasure_map_eval (ι := ι) N, Measure.map_apply]
    · rfl
    · exact measurable_pi_apply N
    · exact hP N
  have hsum : ∑' N, (commonGaussianMeasure ι) (s N) ≠ ∞ := by
    have hreal : ∑' N, ENNReal.ofReal
        (((stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) (P N)).toReal) ≠ ∞ := by
      rw [← ENNReal.ofReal_tsum_of_nonneg
        (fun N => ENNReal.toReal_nonneg) (by simpa only [Measure.real] using h)]
      exact ENNReal.ofReal_ne_top
    rw [show (∑' N, (commonGaussianMeasure ι) (s N)) = ∑' N, ENNReal.ofReal
        (((stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) (P N)).toReal) from by
      apply tsum_congr
      intro N
      rw [hprob N]
      exact (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm]
    exact hreal
  have hfin : ∀ᵐ x ∂(commonGaussianMeasure ι), {N | x ∈ s N}.Finite :=
    MeasureTheory.ae_finite_setOfPred_mem hsum
  filter_upwards [hfin] with x hx
  have hx' : ∀ᶠ N in cofinite, x ∉ s N := hx.eventually_cofinite_notMem
  rw [Nat.cofinite_eq_atTop] at hx'
  filter_upwards [hx'] with N hN
  exact hN

end

end GUEStrongConvergence
