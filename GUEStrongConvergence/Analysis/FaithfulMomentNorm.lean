/-
# The faithful-state moment-norm formula

If `φ` is a faithful state on a unital C*-algebra `A` (positivity and faithfulness are all
that is used — traciality is not needed) and `a` is self-adjoint, then

  `‖a‖ = lim_{k → ∞} φ(a ^ (2k)) ^ (1 / (2k))`.

This is the "faithful moment-norm formula" required by the lower-bound half of the
deterministic strong-convergence transfer: word-moment convergence gives convergence of
`ψ(P(X_n) ^ (2k))` for each fixed `k`, and this formula recovers `‖P(x)‖` from those
moments.

The proof realizes `φ` on the compact real spectrum of `a` as a probability measure, then
applies `tendsto_moment_root_eq_sSup` (the purely measure-theoretic moment-root limit).
-/
import FreeProbability.Analytic.SpectralMeasureSupport
import GUEStrongConvergence.Analysis.MomentRootLimit
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unital
import Mathlib.Analysis.CStarAlgebra.Spectrum

noncomputable section

open Filter MeasureTheory Topology FreeProbability
open scoped ComplexOrder ENNReal NNReal

namespace GUEStrongConvergence

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- The largest modulus of the real spectrum of a self-adjoint element is its norm. -/
theorem sSup_abs_spectrum_eq_norm [Nontrivial A] {a : A} (ha : IsSelfAdjoint a) :
    sSup ((fun t : ℝ => |t|) '' spectrum ℝ a) = ‖a‖ := by
  have hbound : ∀ y ∈ (fun t : ℝ => |t|) '' spectrum ℝ a, y ≤ ‖a‖ := by
    rintro y ⟨t, ht, rfl⟩
    simpa [Real.norm_eq_abs] using spectrum.norm_le_norm_of_mem ht
  have hbdd : BddAbove ((fun t : ℝ => |t|) '' spectrum ℝ a) := ⟨‖a‖, hbound⟩
  obtain hmem | hmem := CStarAlgebra.norm_or_neg_norm_mem_spectrum a ha
  · have hx : ‖a‖ ∈ (fun t : ℝ => |t|) '' spectrum ℝ a :=
      ⟨‖a‖, hmem, by simp [abs_of_nonneg (norm_nonneg a)]⟩
    exact le_antisymm (csSup_le ⟨_, hx⟩ hbound) (le_csSup hbdd hx)
  · have hx : ‖a‖ ∈ (fun t : ℝ => |t|) '' spectrum ℝ a :=
      ⟨-‖a‖, hmem, by simp⟩
    exact le_antisymm (csSup_le ⟨_, hx⟩ hbound) (le_csSup hbdd hx)

/-- **Faithful moment-norm formula.** For a faithful state `φ` and a self-adjoint `a`,
the roots of the even moments converge to the norm. -/
theorem tendsto_expectation_pow_rpow_eq_norm [Nontrivial A]
    (φ : StarProbabilitySpace A) (hfaith : IsFaithful φ.toProbabilitySpace)
    {a : A} (ha : IsSelfAdjoint a) :
    Tendsto (fun k : ℕ => (φ.expectation (a ^ (2 * k))).re ^ ((1 : ℝ) / ((2 * k : ℕ) : ℝ)))
      atTop (𝓝 ‖a‖) := by
  have hsupp : (spectralMeasure φ ha).support = spectrum ℝ a :=
    spectralMeasure_support_eq_spectrum φ ha hfaith
  have hsc : IsCompact (spectralMeasure φ ha).support := by
    rw [hsupp]
    exact ContinuousFunctionalCalculus.isCompact_spectrum a
  have hcompl : (spectralMeasure φ ha) (spectralMeasure φ ha).supportᶜ = 0 := by
    rw [hsupp]
    exact spectralMeasure_spectrum_compl φ ha
  have hlim := tendsto_moment_root_eq_sSup hsc hcompl
  rw [hsupp, sSup_abs_spectrum_eq_norm ha] at hlim
  have hint : ∀ k : ℕ,
      (φ.expectation (a ^ (2 * k))).re
        = ∫ t : ℝ, t ^ (2 * k) ∂(spectralMeasure φ ha) := by
    intro k
    have h1 : φ.expectation (a ^ (2 * k))
        = ((∫ t : ℝ, t ^ (2 * k) ∂(spectralMeasure φ ha) : ℝ) : ℂ) := by
      rw [← cfc_pow_id (R := ℝ) a (2 * k)]
      exact expectation_cfc_eq_integral φ ha (fun t : ℝ => t ^ (2 * k)) (by fun_prop)
    rw [h1, Complex.ofReal_re]
  refine hlim.congr' ?_
  filter_upwards with k
  rw [hint k]

end GUEStrongConvergence
