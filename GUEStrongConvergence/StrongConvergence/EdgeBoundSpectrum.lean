/-
# The exact semicircular spectrum and the edge bound ⇒ spectral inclusion

`StrongConvergence/EdgeBound.lean` proves the cheap direction
`ScalarSpectralInclusion r → GUEEdgeBound r`.  This file proves the substantive direction
`GUEEdgeBound r → ScalarSpectralInclusion r`, which requires the classical exact spectrum
computation

`spectrum ℝ (semicircularFamily r i) = Set.Icc (-2) 2`.

That fact is the pinned dependency theorem
`FreeProbability.Fock.spectrum_closedSemicircular_real`, obtained from the identification of
the Fock spectral measure with the semicircle measure.  We only restate it for
`GUEStrongConvergence.semicircularFamily` (which is definitionally `closedSemicircular`).

With it, the argument is elementary: if `‖G‖ ≤ 2 + ε` then every real spectral value `a` of
the self-adjoint matrix `G` satisfies `|a| ≤ 2 + ε`, hence is within `ε` of the nearest point
of `[-2, 2] = spectrum ℝ (semicircularFamily r i)`.

No `sorry`, no new axioms.
-/
import GUEStrongConvergence.StrongConvergence.EdgeBound
import FreeProbability.Semicircular.SpectralIdentification

open Filter MeasureTheory ProbabilityTheory FreeProbability FreeProbability.Fock Matrix
open scoped BigOperators ComplexOrder ENNReal Pointwise Topology

namespace GUEStrongConvergence

noncomputable section

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000

variable {r : ℕ}

/-- **The exact spectrum of the free semicircular family.**  Each generator has spectrum the
full interval `[-2, 2]`.  This is the classical spectrum computation for the semicircular
element, restated for `semicircularFamily` from the pinned free-probability theorem
`FreeProbability.Fock.spectrum_closedSemicircular_real`. -/
theorem spectrum_semicircularFamily (i : Fin r) :
    spectrum ℝ (semicircularFamily r i) = Set.Icc (-2 : ℝ) 2 :=
  FreeProbability.Fock.spectrum_closedSemicircular_real i

/-- **The substantive direction: the edge bound implies scalar spectral inclusion.**

Almost surely, if eventually `‖G_i‖ ≤ 2 + ε`, then every real spectral value `a` of `G_i`
satisfies `|a| ≤ 2 + ε` and therefore lies within `ε` of the semicircular spectrum
`[-2, 2]`. -/
theorem scalarSpectralInclusion_of_gueEdgeBound {r : ℕ}
    (h : GUEEdgeBound r) : ScalarSpectralInclusion r := by
  letI : Nontrivial (closedSemicircularAlgebra (Fin r)) :=
    (closedGeneratedVacuumState (Fin r)).toProbabilitySpace.nontrivial
  filter_upwards [h] with x hx i ε hε
  filter_upwards [hx i ε hε, eventually_ge_atTop (1 : ℕ)] with N hN hN1
  haveI : Nonempty (Fin N) := ⟨⟨0, lt_of_lt_of_le Nat.zero_lt_one hN1⟩⟩
  intro a ha
  have ha2 : |a| ≤ 2 + ε := by
    have h1 := spectrum.norm_le_norm_of_mem ha
    rw [Real.norm_eq_abs] at h1
    exact h1.trans hN
  obtain ⟨b, hb, hab⟩ := exists_mem_Icc_abs_sub_le hε.le ha2
  refine ⟨b, ?_, hab⟩
  rw [spectrum_semicircularFamily i]
  exact hb

/-- **The equivalence** between the classical GUE edge bound and the scalar spectral
inclusion of the existing reduction. -/
theorem gueEdgeBound_iff_scalarSpectralInclusion {r : ℕ} :
    GUEEdgeBound r ↔ ScalarSpectralInclusion r :=
  ⟨scalarSpectralInclusion_of_gueEdgeBound, gueEdgeBound_of_scalarSpectralInclusion⟩

end

end GUEStrongConvergence
