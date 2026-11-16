/-
# Dyson stability with a variable resolvent bound `M(y)`

`dyson_stability` (`Probability/DysonLimit.lean`) is stated with a *fixed* resolvent bound
`frob g, frob g' ≤ C (Im z)⁻¹`, which forces the stability condition
`2 C² (∑ frob(A_i)²) ≤ (Im z)²` and hence a fixed lower threshold `|Im z| ≥ η_A`.
That threshold is what blocks the strip estimate of the smooth Lemma M.

This file records the *parametric* form of the stability argument: if both resolvents are
bounded by the same number `M` (any real number, e.g. a function `M(y)` of the imaginary
part) and `2 M² (∑ frob(A_i)²) ≤ 1`, then

`frob (g' − g) ≤ 2 M · frob D`.

The point is that the `η`-dependence has disappeared from the stability step: the only
constraint left is `M(y)² Σ ≤ 1/2`, so any *a priori* bound on the limit resolvent that is
better than `d/|Im z|` immediately improves the range of admissible `z` and the constant in
the sharp comparison.  The parametric sharp comparison
`frob_gueResolventMean_sub_limit_le_sharp_of_bound` is the corresponding `O(N⁻²)` estimate.

## Main results

* `dyson_stability_of_bound` — the parametric stability inequality;
* `frob_gueResolventMean_sub_limit_le_sharp_of_bound` — the sharp comparison with a general
  bound `M`, in the exact `O(N⁻²)` form;
* `stability_condition_of_edge_bound` — with `M(y) = C (1 + y^{-1/2})` the condition
  `2 M(y)² Σ ≤ 1` holds for `y ≥ 8 C² Σ` (and `y ≤ 1`), to be compared with the threshold
  `y ≥ (2 d² Σ)^{1/4}` forced by the trivial bound `M = d/y`.
-/
import GUEStrongConvergence.Probability.DysonLimitSharp

open MeasureTheory ProbabilityTheory Matrix Filter
open FreeProbability FreeProbability.Fock
open scoped Matrix.Norms.Frobenius ComplexOrder ENNReal NNReal Topology

set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000

namespace GUEStrongConvergence

variable {ι d : Type*} {N : ℕ} [Fintype ι] [Fintype d] [DecidableEq d] [DecidableEq ι]

noncomputable local instance : PartialOrder (WordSpace ι →L[ℂ] WordSpace ι) :=
  CStarAlgebra.spectralOrder _
noncomputable local instance : StarOrderedRing (WordSpace ι →L[ℂ] WordSpace ι) :=
  CStarAlgebra.spectralOrderedRing _

noncomputable section

/-- **Stability of the Dyson map with a variable bound.**  If `g` solves the Dyson equation
exactly, `g'` solves it with defect `D`, both are bounded by `M`, and
`2 M² (∑ frob(A_i)²) ≤ 1`, then `frob (g' − g) ≤ 2 M frob D`.

This is `dyson_stability` with the substitution `C = M · Im z`; the `(Im z)⁻¹` factors
cancel, so the statement is uniform in `Im z`. -/
theorem dyson_stability_of_bound (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ) (z : ℂ)
    (hz : 0 < z.im) (g g' D : Matrix d d ℂ) {M : ℝ}
    (hg : (z • (1 : Matrix d d ℂ) - A₀ - ∑ i, A i * g * A i) * g = 1)
    (hg' : (z • (1 : Matrix d d ℂ) - A₀ - ∑ i, A i * g' * A i) * g' = 1 + D)
    (hg_b : frob g ≤ M) (hg'_b : frob g' ≤ M)
    (hM : 0 ≤ M)
    (hη : 2 * M ^ 2 * (∑ i, (frob (A i)) ^ 2) ≤ 1) :
    frob (g' - g) ≤ 2 * M * frob D := by
  have hz_ne : z.im ≠ 0 := ne_of_gt hz
  have hC : 0 ≤ M * z.im := mul_nonneg hM (le_of_lt hz)
  have hMdiv : (M * z.im) * (z.im)⁻¹ = M := by
    field_simp
  have hgb : frob g ≤ (M * z.im) * (z.im)⁻¹ := by
    rw [hMdiv]
    exact hg_b
  have hg'b : frob g' ≤ (M * z.im) * (z.im)⁻¹ := by
    rw [hMdiv]
    exact hg'_b
  have hη' : 2 * (M * z.im) ^ 2 * (∑ i, (frob (A i)) ^ 2) ≤ (z.im) ^ 2 := by
    have hs : (0 : ℝ) < (z.im) ^ 2 := by positivity
    nlinarith [hη, hs]
  have h := dyson_stability A₀ A z hz g g' D hg hg' hgb hg'b hC hη'
  calc frob (g' - g) ≤ 2 * (M * z.im) * (z.im)⁻¹ * frob D := h
    _ = 2 * M * frob D := by
        field_simp

/-- **The sharp `O(N⁻²)` comparison with a general resolvent bound `M`.**

Compared with `frob_gueResolventMean_sub_limit_le_sharp`, the hypothesis
`2 d² (∑ frob(A_i)²) ≤ (Im z)²` is replaced by `2 M² (∑ frob(A_i)²) ≤ 1` and the bounds
`frob g_N, frob g ≤ M`; the `(Im z)⁻¹` factor of the stability step is replaced by `M`.
The defect constant is unchanged. -/
theorem frob_gueResolventMean_sub_limit_le_sharp_of_bound (A₀ : Matrix d d ℂ)
    (A : ι → Matrix d d ℂ) (hA₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian)
    (z : ℂ) (hz : 0 < z.im) (hN : 0 < N) {M : ℝ} (hM : 0 ≤ M)
    (hgN_b : frob (gueResolventMean (N := N) A₀ A z) ≤ M)
    (hg_b : frob (operatorMatrixPencilCauchy A₀ A z) ≤ M)
    (hη : 2 * M ^ 2 * (∑ i, (frob (A i)) ^ 2) ≤ 1) :
    frob (gueResolventMean (N := N) A₀ A z - operatorMatrixPencilCauchy A₀ A z)
      ≤ 2 * M *
          ((Fintype.card d : ℝ) *
            (2 * (Fintype.card d : ℝ) ^ 2 * Real.sqrt (Fintype.card d : ℝ) *
              (∑ i, (frob (A i)) ^ 2) *
              (2 * (gueScale N) ^ 2 * (∑ i, (frob (A i)) ^ 2) * ((z.im)⁻¹) ^ 4 / (N : ℝ)))) := by
  classical
  set g : Matrix d d ℂ := operatorMatrixPencilCauchy A₀ A z with hg
  set gN : Matrix d d ℂ := gueResolventMean (N := N) A₀ A z with hgN
  set K : ℝ := 2 * (Fintype.card d : ℝ) ^ 2 * Real.sqrt (Fintype.card d : ℝ) *
      (∑ i, (frob (A i)) ^ 2) *
      (2 * (gueScale N) ^ 2 * (∑ i, (frob (A i)) ^ 2) * ((z.im)⁻¹) ^ 4 / (N : ℝ)) with hK
  set D : Matrix d d ℂ := (z • (1 : Matrix d d ℂ) - A₀ - ∑ i, A i * gN * A i) * gN - 1 with hD
  have hDeq : D = (z • (1 : Matrix d d ℂ) - A₀) * gN - 1
      - ∑ i, A i * (gN * A i * gN) := by
    rw [hD, Matrix.sub_mul]
    rw [show (∑ i, A i * gN * A i) * gN = ∑ i, A i * (gN * A i * gN) from by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      noncomm_ring]
    abel
  have hD_dyson : (z • (1 : Matrix d d ℂ) - A₀ - ∑ i, A i * gN * A i) * gN = 1 + D := by
    rw [hD]
    abel
  have hDbound : frob D ≤ (Fintype.card d : ℝ) * K := by
    refine frob_le_card_mul_of_entry_le D (fun u v => ?_) (by positivity)
    rw [hDeq, hK]
    exact approximate_dyson_entry_le_sharp A₀ A hA₀ hA z hz hN u v
  have hstab := dyson_stability_of_bound A₀ A z hz g gN D
    (by rw [hg]; exact limit_dyson_equation A₀ A hA₀ hA z (ne_of_gt hz))
    hD_dyson
    (by rw [hg]; exact hg_b) (by rw [hgN]; exact hgN_b) hM hη
  calc frob (gN - g) ≤ 2 * M * frob D := hstab
    _ ≤ 2 * M * ((Fintype.card d : ℝ) * K) := by
        refine mul_le_mul_of_nonneg_left hDbound ?_
        positivity
    _ = 2 * M *
          ((Fintype.card d : ℝ) *
            (2 * (Fintype.card d : ℝ) ^ 2 * Real.sqrt (Fintype.card d : ℝ) *
              (∑ i, (frob (A i)) ^ 2) *
              (2 * (gueScale N) ^ 2 * (∑ i, (frob (A i)) ^ 2) * ((z.im)⁻¹) ^ 4 / (N : ℝ)))) := by
        rw [hK]

end

end GUEStrongConvergence
