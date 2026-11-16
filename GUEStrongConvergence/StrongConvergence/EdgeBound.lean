/-
# The GUE edge (no-outlier) bound

`StrongConvergence/CutoffExclusion.lean` reduces the scalar part of the analytic input to
`ScalarSpectralInclusion r`: almost surely, every real spectral value of every individual
GUE generator is eventually within `ε` of the spectrum of the corresponding semicircular
element.  That statement is *not* a classical no-outlier statement: it mentions the spectrum
of the free limit and is only used, in the existing reduction, through the resulting
operator-norm bound.

This file introduces the honest classical edge bound

`GUEEdgeBound r`: almost surely, for every `i` and every `ε > 0`, eventually
`‖gueFamily r N x i‖ ≤ 2 + ε`,

which is exactly the statement that the largest (in modulus) eigenvalue of the normalized
GUE matrix does not exceed the semicircular edge `2` in the limit.

We prove:

* `spectrum ℝ (semicircularFamily r i) ⊆ Set.Icc (-2) 2` (from `‖s‖ = 2`);
* the cheap direction `ScalarSpectralInclusion → GUEEdgeBound`;
* the operator-norm and `ℓ¹` (`tupleNorm`) consequences of `GUEEdgeBound`;
* the upgraded endgame
  `GUEStrongConvergenceStatement_of_pencilStrip_and_edgeBound`, replacing the opaque
  scalar spectral inclusion by `GUEEdgeBound`.

The substantive direction `GUEEdgeBound → ScalarSpectralInclusion` needs the *full*
spectrum computation `spectrum ℝ (semicircularFamily r i) = Set.Icc (-2) 2`; it is proved in
`StrongConvergence/EdgeBoundSpectrum.lean`, which imports the pinned free-probability
spectrum identification.

No `sorry`, no new axioms.
-/
import GUEStrongConvergence.StrongConvergence.FinalReduction
import GUEStrongConvergence.StrongConvergence.FinalWiring
import GUEStrongConvergence.StrongConvergence.FlattenPencil

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

/-- **The GUE edge (no-outlier) bound.**  Almost surely, for every fixed generator `i`,
every `ε > 0`, and all sufficiently large `N`, the operator norm of the individual
normalized GUE matrix `G_i` is at most the semicircular edge `2 + ε`.

This is a classical, clearly-true statement about GUE: the top eigenvalue converges almost
surely to `2`.  It involves no cutoff functions and no Cauchy--Pompeiu constants. -/
def GUEEdgeBound (r : ℕ) : Prop :=
  ∀ᵐ x ∂(commonGaussianMeasure (Fin r)), ∀ i : Fin r, ∀ ε > 0, ∀ᶠ N : ℕ in atTop,
    ‖gueFamily r N x i‖ ≤ (2 : ℝ) + ε

/-- **The semicircular spectrum is contained in `[-2, 2]`.**  This only uses `‖s_i‖ = 2`
and the spectral radius bound, not the exact spectrum. -/
lemma abs_le_two_of_mem_spectrum_semicircularFamily {i : Fin r} {b : ℝ}
    (hb : b ∈ spectrum ℝ (semicircularFamily r i)) : |b| ≤ 2 := by
  letI : Nontrivial (closedSemicircularAlgebra (Fin r)) :=
    (closedGeneratedVacuumState (Fin r)).toProbabilitySpace.nontrivial
  have hb' := spectrum.norm_le_norm_of_mem hb
  rw [Real.norm_eq_abs] at hb'
  have hnorm : ‖semicircularFamily r i‖ = 2 := norm_closedSemicircular i
  rw [hnorm] at hb'
  exact hb'

/-- **A real number close to `[-2, 2]` is within `ε` of a point of `[-2, 2]`.** -/
lemma exists_mem_Icc_abs_sub_le {a ε : ℝ} (hε : 0 ≤ ε) (h : |a| ≤ 2 + ε) :
    ∃ b ∈ Set.Icc (-2 : ℝ) 2, |a - b| ≤ ε := by
  have hup : a ≤ 2 + ε := (abs_le.mp h).2
  have hlo : -(2 + ε) ≤ a := (abs_le.mp h).1
  rcases le_total a 2 with ha2 | ha2
  · rcases le_total (-2 : ℝ) a with ha | ha
    · exact ⟨a, ⟨ha, ha2⟩, by simpa using hε⟩
    · refine ⟨-2, by norm_num, ?_⟩
      rw [show a - (-2 : ℝ) = a + 2 by ring, abs_of_nonpos (by linarith)]
      linarith
  · refine ⟨2, by norm_num, ?_⟩
    rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ a - 2)]
    linarith

/-- **The cheap direction: scalar spectral inclusion implies the edge bound.**

If every GUE spectral value is eventually within `ε` of the semicircular spectrum, and the
latter lies in `[-2, 2]`, then the norm of the self-adjoint GUE matrix is at most `2 + ε`. -/
theorem gueEdgeBound_of_scalarSpectralInclusion {r : ℕ}
    (h : ScalarSpectralInclusion r) : GUEEdgeBound r := by
  letI : Nontrivial (closedSemicircularAlgebra (Fin r)) :=
    (closedGeneratedVacuumState (Fin r)).toProbabilitySpace.nontrivial
  filter_upwards [h] with x hx i ε hε
  filter_upwards [hx i ε hε, eventually_ge_atTop (1 : ℕ)] with N hNle hN1
  haveI : Nonempty (Fin N) := ⟨⟨0, lt_of_lt_of_le Nat.zero_lt_one hN1⟩⟩
  refine norm_le_of_abs_spectrum_le (isSelfAdjoint_gueFamily x i) ?_
  intro a ha
  obtain ⟨b, hb, hab⟩ := hNle a ha
  have hb2 : |b| ≤ 2 := abs_le_two_of_mem_spectrum_semicircularFamily hb
  calc |a| = |b + (a - b)| := by rw [show b + (a - b) = a by ring]
    _ ≤ |b| + |a - b| := abs_add_le _ _
    _ ≤ 2 + ε := add_le_add hb2 hab

/-- **`ε = 1` form of the edge bound**: eventually every GUE generator has norm `≤ 3`. -/
theorem eventually_norm_gueFamily_le_three_of_gueEdgeBound {r : ℕ}
    (h : GUEEdgeBound r) :
    ∀ᵐ x ∂(commonGaussianMeasure (Fin r)), ∀ᶠ N : ℕ in atTop,
      ∀ i : Fin r, ‖gueFamily r N x i‖ ≤ 3 := by
  filter_upwards [h] with x hx
  have hN : ∀ i : Fin r, ∀ᶠ N : ℕ in atTop,
      ‖gueFamily r N x i‖ ≤ (2 : ℝ) + 1 := fun i => hx i 1 one_pos
  have hall : ∀ᶠ N : ℕ in atTop, ∀ i : Fin r,
      ‖gueFamily r N x i‖ ≤ (2 : ℝ) + 1 := eventually_all.2 hN
  filter_upwards [hall] with N hNle i
  exact (hNle i).trans (by norm_num)

/-- **The `ℓ¹` edge bound** (`tupleNorm`, the input of `FinalWiring`'s endgame) from the
operator-norm edge bound: eventually `tupleNorm (gueFamily r N x) ≤ 3 * r`. -/
theorem eventually_tupleNorm_gueFamily_le_of_gueEdgeBound {r : ℕ}
    (h : GUEEdgeBound r) :
    ∀ᵐ x ∂(commonGaussianMeasure (Fin r)), ∀ᶠ N : ℕ in atTop,
      tupleNorm (gueFamily r N x) ≤ 3 * r := by
  filter_upwards [eventually_norm_gueFamily_le_three_of_gueEdgeBound h] with x hx
  filter_upwards [hx] with N hN
  calc tupleNorm (gueFamily r N x) = ∑ i, ‖gueFamily r N x i‖ := rfl
    _ ≤ ∑ _i : Fin r, (3 : ℝ) := Finset.sum_le_sum fun i _ => hN i
    _ = 3 * r := by
        simp [Finset.sum_const, nsmul_eq_mul, mul_comm]

/-- **The upgraded endgame.**  The project target follows from

* the uniform pencil weighted-strip field (the same pencil hypothesis as in
  `WeightedStripInputsFinal`), and
* the classical GUE edge bound `GUEEdgeBound r`,

with *no* scalar cutoff / Cauchy--Pompeiu weighted-strip data and no
`ScalarSpectralInclusion`.

The scalar spectral inclusion is not needed: the pencil data already yields
`H1CanonicalDilated r` (`PencilLemmaSInputs → H1CanonicalDilated`), and the edge bound yields
the `ℓ¹` bound consumed by `GUEStrongConvergenceStatement_of_hEdge`. -/
theorem GUEStrongConvergenceStatement_of_pencilStrip_and_edgeBound {r : ℕ}
    (hpencil : ∀ (k : ℕ) (F : RatPolyIdx r (k + 1)) (z ε : ℝ), 0 < ε →
      WeightedStripDataAtFinal r k F z ε)
    (hedge : GUEEdgeBound r) : GUEStrongConvergenceStatement r :=
  GUEStrongConvergenceStatement_of_hEdge
    (eventually_tupleNorm_gueFamily_le_of_gueEdgeBound hedge)
    (H1CanonicalDilated_of_lemmaSInputs
      (PencilLemmaSInputs_of_weightedMeanInputs
        (WeightedMeanInputs_of_weightedStripInputs'''
          (WeightedStripInputs'''_of_weightedStripDataAtFinal hpencil))))

end

end GUEStrongConvergence
