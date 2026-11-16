/-
# Matrix-level analyticity of the averaged resolvent

`HT05Analytic.lean` proves analyticity of each entry of `z ↦ gueResolventMean A₀ A z` on the
upper half-plane.  The uniqueness theorems of the pinned `lean-free-prob` dependency are stated
for `AnalyticOnNhd ℂ (fun z => gueResolventMean A₀ A z) U` with the `Matrix.Norms.Operator`
normed structure on `Matrix d d ℂ`.  This file transports the entrywise statement to that
structure along the identity linear equivalence `(d → d → ℂ) ≃ Matrix d d ℂ`, which is continuous
because the source is finite dimensional.
-/
import GUEStrongConvergence.StrongConvergence.HT05Analytic
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Topology.Algebra.Module.FiniteDimension

open MeasureTheory ProbabilityTheory Matrix Filter
open FreeProbability FreeProbability.Fock
open scoped ComplexOrder ENNReal NNReal Topology

namespace GUEStrongConvergence

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {d : Type*} [Fintype d] [DecidableEq d] {N : ℕ}

section MatrixOperatorNorm

open scoped Matrix.Norms.Operator

/-- **Analyticity of the averaged resolvent matrix** for the `Matrix.Norms.Operator` instance
(the normed structure used by the dependency's uniqueness theorems).

The entrywise (Pi) statement is transported along the identity `(d → d → ℂ) →L Matrix d d ℂ`,
which is continuous because the source is finite-dimensional. -/
theorem analytic_gueResolventMean (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    (hA₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian) (hN : 0 < N) :
    AnalyticOnNhd ℂ (fun z => gueResolventMean (N := N) A₀ A z) {z : ℂ | 0 < z.im} := by
  have hpi := analytic_gueResolventMean_pi A₀ A hA₀ hA hN
  let e : (d → d → ℂ) →ₗ[ℂ] Matrix d d ℂ :=
    (Matrix.ofLinearEquiv (m := d) (n := d) (R := ℂ) (α := ℂ)).toLinearMap
  have hec : Continuous e := e.continuous_of_finiteDimensional
  let e' : (d → d → ℂ) →L[ℂ] Matrix d d ℂ := ⟨e, hec⟩
  refine AnalyticOnNhd.congr' (e'.comp_analyticOnNhd hpi) ?_
  filter_upwards with z
  rfl

end MatrixOperatorNorm

end

end GUEStrongConvergence
