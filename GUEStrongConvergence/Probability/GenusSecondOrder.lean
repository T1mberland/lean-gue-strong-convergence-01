/-
# Second-order accuracy of the genus expansion of the trace-word mean

The exact genus expansion of a GUE trace-word moment is
`E τ_N(w) = N^{-(m+1)} ∑_p label(p) N^{c(p)}` (`integral_eq_genusSum` /
`integral_gueNormTrace_eq_genus`), and the face count of a pairing of `2m` entries satisfies

* `c(p) = m + 1` for non-crossing `p` (`pairOrbitCount_eq_of_isNonCrossing`),
* `c(p) ≤ m - 1` for crossing `p` (`pairOrbitCount_le_of_not_isNonCrossing`).

Hence **no `1/N` term survives**: the crossing terms lose at least `N²` relative to the
maximal ones, and the mean has the second-order accuracy

  `‖E τ_N(w) − wordLimit w‖ ≤ (∑_p ‖label(p)‖) / N²`   for all `N ≥ 1`.

This is the model computation behind the `O(N^{-2})` mean input of Lemma S / `FlatLemmaM`:
the parity of the genus filtration (`pairOrbitCount_mod_two`) makes the mean error `N^{-2}`
rather than `N^{-1}`.

The abstract combinatorial lemma is `norm_genus_sum_sub_limit_le`; the GUE instantiation is
`abs_integral_gueNormTrace_sub_wordLimit_le_inv_sq`.  For odd-length words the mean and the
limit both vanish (`integral_gueNormTrace_eq_wordLimit_of_odd`), so the error is exactly `0`.

No `sorry`/axiom is used.
-/
import GUEStrongConvergence.Probability.GUEAllWords
import GUEStrongConvergence.Probability.GUEPairingEar
import GUEStrongConvergence.Probability.GUEPairingGenusSplit
import GUEStrongConvergence.Probability.GUEWordGenusExpansionInstance

open MeasureTheory ProbabilityTheory Filter
open scoped RealInnerProductSpace Matrix ENNReal Topology BigOperators

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace GUEStrongConvergence

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ### The abstract second-order genus lemma -/

/-- **Second-order accuracy of a genus sum.**  If every `NC` pairing has maximal face count
`m + 1` and every other pairing has face count at most `m - 1`, then the normalized genus sum
`N^{-(m+1)} ∑_p label(p) N^{c(p)}` differs from the sum of the labels of the `NC` pairings by
at most `(∑_p ‖label(p)‖) / N²`.  In particular there is no `1/N` term. -/
theorem norm_genus_sum_sub_limit_le {P : Type*} [Fintype P]
    (c : P → ℕ) (label : P → ℂ) (NC : P → Prop) [DecidablePred NC] {m : ℕ} (hm : 1 ≤ m)
    (hc_nc : ∀ p, NC p → c p = m + 1)
    (hc_notnc : ∀ p, ¬ NC p → c p ≤ m - 1) (N : ℕ) (hN : 1 ≤ N) :
    ‖((N : ℂ) ^ (m + 1))⁻¹ * (∑ p : P, label p * (N : ℂ) ^ (c p))
        - (∑ p ∈ (Finset.univ : Finset P).filter NC, label p)‖
      ≤ (∑ p : P, ‖label p‖) / (N : ℝ) ^ 2 := by
  classical
  have hN0 : (N : ℂ) ≠ 0 := by
    have h : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    exact_mod_cast h.ne'
  have hX1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hXpos : (0 : ℝ) < (N : ℝ) := by linarith
  set W : ℂ := ∑ p ∈ (Finset.univ : Finset P).filter NC, label p with hW
  set R : ℂ := ∑ p ∈ (Finset.univ : Finset P).filter (fun p => ¬ NC p),
    label p * (N : ℂ) ^ (c p) with hR
  -- split the genus sum into the maximal part and the rest
  have hsplit : (∑ p : P, label p * (N : ℂ) ^ (c p)) = (N : ℂ) ^ (m + 1) * W + R := by
    rw [hW, hR, Finset.mul_sum,
      ← Finset.sum_filter_add_sum_filter_not (s := (Finset.univ : Finset P)) (p := NC)
        (f := fun p => label p * (N : ℂ) ^ (c p))]
    congr 1
    · refine Finset.sum_congr rfl fun p hp => ?_
      have hp' : NC p := (Finset.mem_filter.mp hp).2
      rw [hc_nc p hp']
      ring
  -- the main algebraic cancellation
  have hmain : ((N : ℂ) ^ (m + 1))⁻¹ * ((N : ℂ) ^ (m + 1) * W + R) - W
      = ((N : ℂ) ^ (m + 1))⁻¹ * R := by
    rw [mul_add, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hN0), one_mul]
    ring
  -- the bound on the remainder
  have hRbound : ‖R‖ ≤ (∑ p : P, ‖label p‖) * (N : ℝ) ^ (m - 1) := by
    rw [hR]
    calc ‖∑ p ∈ (Finset.univ : Finset P).filter (fun p => ¬ NC p),
            label p * (N : ℂ) ^ (c p)‖
        ≤ ∑ p ∈ (Finset.univ : Finset P).filter (fun p => ¬ NC p),
            ‖label p * (N : ℂ) ^ (c p)‖ := norm_sum_le _ _
      _ ≤ ∑ p ∈ (Finset.univ : Finset P).filter (fun p => ¬ NC p),
            ‖label p‖ * (N : ℝ) ^ (m - 1) := by
          refine Finset.sum_le_sum fun p hp => ?_
          have hnc : ¬ NC p := (Finset.mem_filter.mp hp).2
          have hc := hc_notnc p hnc
          rw [norm_mul, norm_pow, Complex.norm_natCast]
          exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hX1 hc) (norm_nonneg _)
      _ = (∑ p ∈ (Finset.univ : Finset P).filter (fun p => ¬ NC p), ‖label p‖)
            * (N : ℝ) ^ (m - 1) := by
          rw [Finset.sum_mul]
      _ ≤ (∑ p : P, ‖label p‖) * (N : ℝ) ^ (m - 1) := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun p _ _ => norm_nonneg _)
  rw [hsplit, hmain, norm_mul, norm_inv, norm_pow, Complex.norm_natCast]
  have hstep : ((N : ℝ) ^ (m + 1))⁻¹ * ‖R‖
      ≤ ((N : ℝ) ^ (m + 1))⁻¹ * ((∑ p : P, ‖label p‖) * (N : ℝ) ^ (m - 1)) := by
    refine mul_le_mul_of_nonneg_left hRbound (by positivity)
  refine hstep.trans ?_
  have hEq : ((N : ℝ) ^ (m + 1))⁻¹ * ((∑ p : P, ‖label p‖) * (N : ℝ) ^ (m - 1))
      = (∑ p : P, ‖label p‖) / (N : ℝ) ^ 2 := by
    rw [div_eq_mul_inv]
    have hpow : (N : ℝ) ^ (m + 1) = (N : ℝ) ^ (m - 1) * (N : ℝ) ^ 2 := by
      rw [show m + 1 = (m - 1) + 2 by omega, pow_add]
    rw [hpow, mul_inv]
    have h1 : (N : ℝ) ^ (m - 1) ≠ 0 := by positivity
    have h2 : (N : ℝ) ^ 2 ≠ 0 := by positivity
    field_simp
  exact le_of_eq hEq

/-! ### The GUE trace-word case -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Second-order accuracy of the GUE trace-word mean.**  For a word of even length `2m`
(`m ≥ 1`) there is a constant `C ≥ 0`, depending only on the word, with

  `‖E τ_N(w) − wordLimit w‖ ≤ C / N²`   for every `N ≥ 1`.

No `1/N` term is present, by the genus dichotomy `c(p) = m+1` (non-crossing) or `c(p) ≤ m-1`
(crossing). -/
theorem abs_integral_gueNormTrace_sub_wordLimit_le_inv_sq
    (w : List ι) (m : ℕ) (hl : w.length = 2 * m) (hm : 1 ≤ m) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 1 ≤ N →
      ‖(∫ x : EuclideanSpace ℝ (GUECoord ι N), gueNormTrace (N := N) w x
          ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))) - wordLimit w‖
        ≤ C / (N : ℝ) ^ 2 := by
  classical
  have hpos : 1 ≤ w.length := by omega
  have hk : w.length / 2 = m := by omega
  have hcan : w.length = 2 * (w.length / 2) := by omega
  have hlen : (gueCanonicalEntries w (w.length / 2) hcan (le_refl 1)).length
      = 2 * m := by
    rw [length_gueCanonicalEntries]
    omega
  refine ⟨∑ q : GUEPairing (gueCanonicalEntries w (w.length / 2) hcan (le_refl 1)),
    ‖gueLabelWeight (gueCanonicalEntries w (w.length / 2) hcan (le_refl 1)) q‖,
    Finset.sum_nonneg fun q _ => norm_nonneg _, ?_⟩
  intro N hN
  have hE := integral_eq_genusSum (N := N) w hpos hN
  have hGS : genusSum w N =
      ∑ q : GUEPairing (gueCanonicalEntries w (w.length / 2) hcan (le_refl 1)),
        gueLabelWeight (gueCanonicalEntries w (w.length / 2) hcan (le_refl 1)) q
          * (N : ℂ) ^ (pairOrbitCount q) := by
    rw [genusSum, dite_eq_left hcan]
  have hWL : wordLimit w =
      ∑ q ∈ (Finset.univ : Finset
          (GUEPairing (gueCanonicalEntries w (w.length / 2) hcan (le_refl 1)))).filter
          IsNonCrossing,
        gueLabelWeight (gueCanonicalEntries w (w.length / 2) hcan (le_refl 1)) q := by
    rw [wordLimit_of_even (m := w.length / 2) hcan]
  rw [hE, hGS, hWL]
  -- convert the `zpow` factor into an inverse power
  have hzw : (N : ℂ) ^ (-(((w.length / 2 + 1 : ℕ)) : ℤ))
      = ((N : ℂ) ^ (m + 1))⁻¹ := by
    have h1 : w.length / 2 + 1 = m + 1 := by omega
    rw [h1, zpow_neg, zpow_natCast]
  rw [hzw]
  exact norm_genus_sum_sub_limit_le (fun q => pairOrbitCount q)
    (fun q => gueLabelWeight (gueCanonicalEntries w (w.length / 2) hcan (le_refl 1)) q)
    IsNonCrossing hm
    (fun q hq => pairOrbitCount_eq_of_isNonCrossing q m hm hlen hq)
    (fun q hq => pairOrbitCount_le_of_not_isNonCrossing
      (gueCanonicalEntries w (w.length / 2) hcan (le_refl 1)) q m hlen hq) N hN

/-- **Odd-length words are exact**: the mean and the limit both vanish for every `N ≥ 1`. -/
theorem integral_gueNormTrace_eq_wordLimit_of_odd
    (w : List ι) (hodd : Odd w.length) (N : ℕ) (hN : 1 ≤ N) :
    ∫ x : EuclideanSpace ℝ (GUECoord ι N), gueNormTrace (N := N) w x
        ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) = wordLimit w := by
  rw [wordLimit_of_odd hodd, integral_gueNormTrace_odd_zero w hodd]

/-- The `N^{-2}` bound for odd-length words, with constant `0`. -/
theorem abs_integral_gueNormTrace_sub_wordLimit_le_inv_sq_of_odd
    (w : List ι) (hodd : Odd w.length) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 1 ≤ N →
      ‖(∫ x : EuclideanSpace ℝ (GUECoord ι N), gueNormTrace (N := N) w x
          ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))) - wordLimit w‖
        ≤ C / (N : ℝ) ^ 2 :=
  ⟨0, le_refl 0, fun N hN => by
    rw [integral_gueNormTrace_eq_wordLimit_of_odd w hodd N hN, sub_self, norm_zero]
    simp⟩

end

end GUEStrongConvergence
