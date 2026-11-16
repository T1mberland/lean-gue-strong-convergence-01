/-
# Vanishing of the limit spectral statistic on the limit spectrum

The Lemma-S input `hM` of `ae_eventually_spectrum_subset_guePencil` is the *unshifted*
bound `|E[τ_N(f(H_N))]| ≤ C/N²`.  When the cutoff `f` comes from
`exists_contDiff_cutoff` / `exists_contDiff_two_cutoff` (so `f = 0` on the limit spectrum),
the limit contribution vanishes identically:

`τ_d(τ(f(h))) = 0`   whenever   `f = 0` on `spectrum ℝ h`.

This is the deterministic limit-side half of the smooth Lemma M comparison.  It reduces the
`hM` input to the *difference* bound `|E[τ_N(f(H_N))] − τ(f(h))| ≤ C/N²` together with the
limit-side representation of `τ(f(h))` (see `Probability/LemmaMSmooth.lean`, module docstring).

## Main result

* `limitTraceCfcC_eq_zero_of_eq_zero_on_spectrum`
-/
import GUEStrongConvergence.Probability.LimitSideSpectral

open MeasureTheory Matrix Filter Complex FreeProbability FreeProbability.Fock
open scoped ComplexOrder Topology BigOperators

namespace GUEStrongConvergence

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

variable {r d : ℕ} [Nonempty (Fin d)]

local instance limitZeroNontrivial : Nontrivial (closedSemicircularAlgebra (Fin r)) :=
  (closedGeneratedVacuumState (Fin r)).toProbabilitySpace.nontrivial

local instance limitZeroPartialOrder : PartialOrder (closedSemicircularAlgebra (Fin r)) :=
  CStarAlgebra.spectralOrder _

local instance limitZeroStarOrderedRing : StarOrderedRing (closedSemicircularAlgebra (Fin r)) :=
  CStarAlgebra.spectralOrderedRing _

local instance limitZeroCfcComplex : ContinuousFunctionalCalculus ℂ (BlockLimit r d) IsStarNormal :=
  IsStarNormal.instContinuousFunctionalCalculus

local instance limitZeroCfcReal : ContinuousFunctionalCalculus ℝ (BlockLimit r d) IsSelfAdjoint :=
  @IsSelfAdjoint.instContinuousFunctionalCalculus (BlockLimit r d) _ _ _ _ _

/-- **The limit statistic vanishes when the test function vanishes on the limit spectrum.**

The continuous functional calculus is determined by the values on the spectrum
(`cfc_congr`), so `f(h) = 0` and hence `τ_d(τ(f(h))) = 0`. -/
theorem limitTraceCfcC_eq_zero_of_eq_zero_on_spectrum
    {f : ℝ → ℝ} {h : BlockLimit r d} (hh : IsSelfAdjoint h)
    (hf : ContinuousOn f (spectrum ℝ h)) (hzero : ∀ x ∈ spectrum ℝ h, f x = 0) :
    limitTraceCfcC f h = 0 := by
  unfold limitTraceCfcC
  have hz : limitCfc f h = 0 := by
    unfold limitCfc
    rw [cfc_congr (g := fun _ => 0) (a := h) hzero]
    simpa using cfc_zero (R := ℝ) (a := h)
  rw [hz, map_zero]

/-- Real form of the vanishing: the real limit statistic is zero. -/
theorem limitTraceCfc_eq_zero_of_eq_zero_on_spectrum
    {f : ℝ → ℝ} {h : BlockLimit r d} (hh : IsSelfAdjoint h)
    (hf : ContinuousOn f (spectrum ℝ h)) (hzero : ∀ x ∈ spectrum ℝ h, f x = 0) :
    limitTraceCfc f h = 0 := by
  unfold limitTraceCfc
  rw [limitTraceCfcC_eq_zero_of_eq_zero_on_spectrum hh hf hzero]
  rfl

end

end GUEStrongConvergence
