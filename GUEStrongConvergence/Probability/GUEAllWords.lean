/-
# Simultaneous almost-sure convergence for all trace words

This file assembles the per-word variance chain of `GUEVarianceFinal` into a single almost-sure
event on the common product Gaussian space on which **every** fixed word `w : List ι` has a
convergent normalized trace, with the explicit limit

* for even words `w.length = 2m` (`m ≥ 1`): the sum of the label weights of the non-crossing
  pairings of the canonical entry list `gueCanonicalEntries w m hl (le_refl 1)`
  (this is the limit supplied by `GUEPairingMapEntries.mean_limit`);
* for odd words: `0` (the mean is `0` for every `N`, `tendsto_integral_gueNormTrace_odd`);
* for the empty word: `1` (`gueNormTrace_nil`).

The three cases are collected in the definition `wordLimit`, and the single a.e. event is obtained
from the countability of `List ι` via `MeasureTheory.ae_all_iff`.

The per-word input is the block-diagonal factorization `hblock` of the two-walk slot pairing sum
(Worker K's `GUEBlockSplit`), stated as an explicit hypothesis in exactly the form used by
`GUEVarianceFinal.variance_bound_gueNormTrace`.

The mean-square hypothesis `hmean` of the variance chain is **discharged** here: the one-walk genus
sum `genusSum w N` (the label-weighted pairing sum over `gueCanonicalEntries w (w.length / 2) _
(le_refl 1)`, `0` for odd words) is real (`genusSum_exists_real`), the exact mean is
`N^{-(w.length/2+1)}` times it (`integral_eq_genusSum`, from `integral_gueNormTrace_eq_genus_canonical`
and the cross-dimension identity `sum_gueCanonicalEntries_crossdim`), and consequently
`normSq_integral_eq_genusSum` proves the mean-square formula.  Thus
`ae_all_words_gueNormTrace_genusSum` depends on `hblock` alone.

No `sorry`/axiom is used.
-/
import GUEStrongConvergence.Probability.GUEVarianceFinal
import GUEStrongConvergence.Probability.GUEPairingMapEntries
import GUEStrongConvergence.Probability.GUEWordMomentLimit
import GUEStrongConvergence.Probability.GUEWordGenusExpansionInstance

open MeasureTheory ProbabilityTheory Filter
open scoped RealInnerProductSpace Matrix ENNReal Topology

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false
set_option linter.unusedVariables false

namespace GUEStrongConvergence

attribute [local instance] Classical.propDecidable

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {N : ℕ}

/-! ### The word limit -/

/-- **The limit of the normalized trace of a fixed word.**  For a word of even length `2m` it is the
sum of the label weights of the non-crossing pairings of the canonical entry list
`gueCanonicalEntries w m _ (le_refl 1)`; for a word of odd length it is `0`. -/
def wordLimit (w : List ι) : ℂ :=
  if h : w.length = 2 * (w.length / 2) then
    (∑ p ∈ (Finset.univ : Finset
        (GUEPairing (gueCanonicalEntries w (w.length / 2) h (le_refl 1)))).filter IsNonCrossing,
      gueLabelWeight (gueCanonicalEntries w (w.length / 2) h (le_refl 1)) p)
  else 0

/-- The limit of an odd-length word is zero. -/
theorem wordLimit_of_odd {w : List ι} (hodd : Odd w.length) : wordLimit w = 0 := by
  obtain ⟨k, hk⟩ := hodd
  have hne : ¬ (w.length = 2 * (w.length / 2)) := by omega
  simp only [wordLimit, dite_eq_right hne]

/-- The limit of an even-length word is the non-crossing label sum. -/
theorem wordLimit_of_even {w : List ι} {m : ℕ} (hl : w.length = 2 * m) :
    wordLimit w =
      (∑ p ∈ (Finset.univ : Finset
          (GUEPairing (gueCanonicalEntries w m hl (le_refl 1)))).filter IsNonCrossing,
        gueLabelWeight (gueCanonicalEntries w m hl (le_refl 1)) p) := by
  have hm2 : m = w.length / 2 := by omega
  subst hm2
  simp only [wordLimit, dite_eq_left hl]

/-- The limit of the empty word is one. -/
theorem wordLimit_nil : wordLimit ([] : List ι) = 1 := by
  rw [wordLimit_of_even (m := 0) (by simp)]
  -- the canonical list of length `0`, whose only pairing is `nil` with label weight `1`
  have hlist : gueCanonicalEntries ([] : List ι) 0 (by simp) (le_refl 1) =
      ([] : List (GUEEntry ι 1)) := by
    simp [gueCanonicalEntries, List.ofFn]
  rw [hlist]
  have huniv : (Finset.univ : Finset (GUEPairing ([] : List (GUEEntry ι 1)))) =
      {GUEPairing.nil} := by
    ext p
    cases p
    simp
  rw [huniv]
  have hnc : IsNonCrossing (GUEPairing.nil : GUEPairing ([] : List (GUEEntry ι 1))) := by
    intro a
    exact Fin.elim0 a
  have hfilter : ({GUEPairing.nil} : Finset (GUEPairing ([] : List (GUEEntry ι 1)))).filter
      IsNonCrossing = {GUEPairing.nil} := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨h, -⟩
      exact h
    · intro h
      subst h
      exact ⟨rfl, hnc⟩
  rw [hfilter]
  simp

/-- **Convergence of the empty word's trace** (which is eventually constantly `1`). -/
theorem tendsto_gueNormTrace_nil (x : CommonSpace ι) :
    Tendsto (fun N : ℕ => gueNormTrace (N := N) ([] : List ι) (x N)) atTop (𝓝 1) := by
  have h : (fun N : ℕ => gueNormTrace (N := N) ([] : List ι) (x N)) =ᶠ[atTop]
      fun _ => (1 : ℂ) := by
    filter_upwards [eventually_gt_atTop 0] with M hM
    rw [gueNormTrace_nil]
    simp [Nat.ne_of_gt hM]
  exact tendsto_const_nhds.congr' h.symm

/-! ### Per-word almost-sure convergence -/

/-- **Almost-sure convergence of one fixed word**, conditional only on the block-diagonal
factorization `hblock` and the mean-square formula `hmean`. -/
theorem ae_tendsto_gueNormTrace_word (S : (w : List ι) → ℕ → ℂ) (w : List ι)
    (hblock : ∀ (N : ℕ) (_ : 1 ≤ N) (V₀ : Fin (w.length + w.reverse.length) → Fin N),
      (∑ q ∈ (Finset.univ.filter fun q : GUEPairing (slotList w V₀) =>
          ¬ SlotCross w.length w.reverse.length (slotPerm q)), slotWeight N q) = (S w N) ^ 2)
    (hmean : ∀ N : ℕ, Complex.normSq (∫ y, gueNormTrace w y
        ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))) =
      ((((N : ℂ)⁻¹) ^ (w.length + 2) * (S w N) ^ 2)).re) :
    ∀ᵐ x ∂(commonGaussianMeasure ι),
      Tendsto (fun N : ℕ => gueNormTrace w (x N)) atTop (𝓝 (wordLimit w)) := by
  by_cases hnil : w = []
  · subst hnil
    rw [wordLimit_nil]
    exact Filter.Eventually.of_forall tendsto_gueNormTrace_nil
  · have hk : 1 ≤ w.length := by
      cases w with
      | nil => exact absurd rfl hnil
      | cons _ _ => simp
    by_cases heven : Even w.length
    · obtain ⟨m, hm⟩ := heven
      have hl : w.length = 2 * (w.length / 2) := by omega
      have hm1 : 1 ≤ w.length / 2 := by omega
      simp only [wordLimit, dite_eq_left hl]
      refine ae_tendsto_gueNormTrace_of_slot w hk (S w) _ hblock hmean ?_
      exact GUEPairing.mean_limit w (w.length / 2) hl hk hm1
    · have hodd : Odd w.length := Nat.not_even_iff_odd.mp heven
      rw [wordLimit_of_odd hodd]
      exact ae_tendsto_gueNormTrace_of_slot w hk (S w) 0 hblock hmean
        (tendsto_integral_gueNormTrace_odd w hodd)

/-! ### Simultaneous convergence for all words -/

/-- **Simultaneous almost-sure convergence for all trace words**: on a single almost-sure event,
every fixed word `w : List ι` has `gueNormTrace w (x N) → wordLimit w`.  This is the `hWords`
input of the final strong-convergence assembly, with the explicit limit `wordLimit` (the
non-crossing label sum for even words, `0` for odd words and `1` for the empty word).

The only external input is the block-diagonal factorization `hblock` (stated for every word). -/
theorem ae_all_words_gueNormTrace (S : (w : List ι) → ℕ → ℂ)
    (hblock : ∀ (w : List ι) (_ : 1 ≤ w.length) (N : ℕ) (_ : 1 ≤ N)
        (V₀ : Fin (w.length + w.reverse.length) → Fin N),
      (∑ q ∈ (Finset.univ.filter fun q : GUEPairing (slotList w V₀) =>
          ¬ SlotCross w.length w.reverse.length (slotPerm q)), slotWeight N q) = (S w N) ^ 2)
    (hmean : ∀ (w : List ι) (_ : 1 ≤ w.length) (N : ℕ), Complex.normSq (∫ y, gueNormTrace w y
        ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))) =
      ((((N : ℂ)⁻¹) ^ (w.length + 2) * (S w N) ^ 2)).re) :
    ∀ᵐ x ∂(commonGaussianMeasure ι), ∀ w : List ι,
      Tendsto (fun N : ℕ => gueNormTrace w (x N)) atTop (𝓝 (wordLimit w)) := by
  rw [MeasureTheory.ae_all_iff]
  intro w
  by_cases hnil : w = []
  · subst hnil
    rw [wordLimit_nil]
    exact Filter.Eventually.of_forall tendsto_gueNormTrace_nil
  · have hk : 1 ≤ w.length := by
      cases w with
      | nil => exact absurd rfl hnil
      | cons _ _ => simp
    exact ae_tendsto_gueNormTrace_word S w (hblock w hk) (hmean w hk)

/-! ### The one-walk genus sum and the mean-square identity -/

/-- **The one-walk genus sum** of a word: the label-weighted pairing sum over the canonical entry
list with `N` to the face count.  It is `0` for words of odd length. -/
def genusSum (w : List ι) (N : ℕ) : ℂ :=
  if h : w.length = 2 * (w.length / 2) then
    ∑ q : GUEPairing (gueCanonicalEntries w (w.length / 2) h (le_refl 1)),
      gueLabelWeight (gueCanonicalEntries w (w.length / 2) h (le_refl 1)) q *
        (N : ℂ) ^ (pairOrbitCount q)
  else 0

/-- The label covariance is the coercion of a real number. -/
theorem gueLabelCov_exists_real (e f : GUEEntry ι N) :
    ∃ r : ℝ, gueLabelCov e f = (r : ℂ) := by
  by_cases h : e.1 = f.1
  · exact ⟨1, by simp [gueLabelCov, h]⟩
  · exact ⟨0, by simp [gueLabelCov, h]⟩

/-- Every label weight is the coercion of a real number. -/
theorem gueLabelWeight_exists_real (l : List (GUEEntry ι N)) (p : GUEPairing l) :
    ∃ r : ℝ, gueLabelWeight l p = (r : ℂ) := by
  induction p with
  | nil => exact ⟨1, by simp⟩
  | cons e l k p ih =>
    obtain ⟨s, hs⟩ := gueLabelCov_exists_real e (l.get k)
    obtain ⟨r, hr⟩ := ih
    refine ⟨s * r, ?_⟩
    rw [gueLabelWeight_cons, hs, hr, Complex.ofReal_mul]

/-- The genus sum is the coercion of a real number. -/
theorem genusSum_exists_real (w : List ι) (N : ℕ) : ∃ r : ℝ, genusSum w N = (r : ℂ) := by
  simp only [genusSum]
  split_ifs with h
  · have hq : ∀ q : GUEPairing (gueCanonicalEntries w (w.length / 2) h (le_refl 1)),
        ∃ r : ℝ, gueLabelWeight (gueCanonicalEntries w (w.length / 2) h (le_refl 1)) q = (r : ℂ) :=
      fun q => gueLabelWeight_exists_real _ q
    choose r hr using hq
    refine ⟨∑ q, r q * (N : ℝ) ^ (pairOrbitCount q), ?_⟩
    rw [Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [Complex.ofReal_mul, hr q]
    congr 1
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_pow]
  · exact ⟨0, by simp⟩

/-- **The exact mean formula** in terms of the genus sum, for nonempty words. -/
theorem integral_eq_genusSum (w : List ι) (hk : 1 ≤ w.length) (hN : 1 ≤ N) :
    ∫ y, gueNormTrace w y ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) =
      (N : ℂ) ^ (-(((w.length / 2 + 1 : ℕ)) : ℤ)) * genusSum w N := by
  by_cases heven : Even w.length
  · have hm' : w.length = 2 * (w.length / 2) := by
      obtain ⟨m, hm⟩ := heven
      omega
    rw [genusSum, dite_eq_left hm',
      integral_gueNormTrace_eq_genus_canonical (N := N) w (w.length / 2) hm' hk hN]
    rw [show (-(↑(w.length / 2) + 1) : ℤ) = -(((w.length / 2 + 1 : ℕ)) : ℤ) by
      push_cast
      ring]
    congr 1
    exact GUEPairing.sum_gueCanonicalEntries_crossdim w (w.length / 2) hm' hN (N : ℂ)
  · have hodd : Odd w.length := Nat.not_even_iff_odd.mp heven
    have hne : ¬ (w.length = 2 * (w.length / 2)) := by
      obtain ⟨k, hk'⟩ := hodd
      omega
    rw [genusSum, dite_eq_right hne, integral_gueNormTrace_odd_zero w hodd]
    simp

/-- **The mean-square identity in terms of the genus sum**: the squared modulus of the mean is the
real part of `N^{-(k+2)}` times the square of the one-walk genus sum. -/
theorem normSq_integral_eq_genusSum (w : List ι) (hk : 1 ≤ w.length) (N : ℕ) :
    Complex.normSq (∫ y, gueNormTrace w y
        ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))) =
      ((((N : ℂ)⁻¹) ^ (w.length + 2) * (genusSum w N) ^ 2)).re := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · -- degenerate dimension `0`
    subst hN
    have hz : ∀ y : EuclideanSpace ℝ (GUECoord ι 0), gueNormTrace (N := 0) w y = 0 := by
      intro y
      simp [gueNormTrace]
    have hp : (0 : ℂ) ^ (w.length + 2) = 0 := zero_pow (by omega)
    simp [hz, hp]
  · by_cases heven : Even w.length
    · -- even length: expand the integral and compare real forms
      obtain ⟨m, hm⟩ := heven
      have hhalf : w.length / 2 = m := by omega
      obtain ⟨r, hr⟩ := genusSum_exists_real w N
      rw [integral_eq_genusSum w hk hN, hr]
      have hexp : (-(((w.length / 2 + 1 : ℕ)) : ℤ)) = -(↑m + 1) := by
        have h2 : w.length / 2 = m := by omega
        rw [h2]
        push_cast
        ring
      rw [hexp]
      rw [show (N : ℂ) ^ (-(↑m + 1) : ℤ) = (((((N : ℝ)⁻¹) ^ (m + 1) : ℝ)) : ℂ) by
        rw [show (-(↑m + 1) : ℤ) = -((m + 1 : ℕ) : ℤ) by omega, zpow_neg, zpow_natCast]
        rw [← inv_pow]
        rw [← Complex.ofReal_natCast N, ← Complex.ofReal_inv, ← Complex.ofReal_pow]]
      rw [show w.length + 2 = 2 * m + 2 by omega]
      rw [show ((N : ℂ)⁻¹) ^ (2 * m + 2) = (((((N : ℝ)⁻¹) ^ (2 * m + 2) : ℝ)) : ℂ) by
        rw [← Complex.ofReal_natCast N, ← Complex.ofReal_inv, ← Complex.ofReal_pow]]
      rw [show ((r : ℂ) ^ 2) = ((r ^ 2 : ℝ) : ℂ) by rw [← Complex.ofReal_pow]]
      rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, Complex.normSq_ofReal, Complex.ofReal_re]
      have haa : (((N : ℝ)⁻¹) ^ (m + 1)) * (((N : ℝ)⁻¹) ^ (m + 1))
          = ((N : ℝ)⁻¹) ^ (2 * m + 2) := by
        rw [← pow_two, ← pow_mul, show (m + 1) * 2 = 2 * m + 2 by ring]
      rw [← haa]
      ring
    · -- odd length: both sides vanish
      have hodd : Odd w.length := Nat.not_even_iff_odd.mp heven
      have hne : ¬ (w.length = 2 * (w.length / 2)) := by
        obtain ⟨k, hk'⟩ := hodd
        omega
      rw [genusSum, dite_eq_right hne, integral_gueNormTrace_odd_zero w hodd]
      simp

/-- **Simultaneous almost-sure convergence for all trace words, conditional only on the
block-diagonal factorization**: `hblock` now refers to the concrete one-walk genus sum
`genusSum`, the mean-square identity having been discharged by `normSq_integral_eq_genusSum`. -/
theorem ae_all_words_gueNormTrace_genusSum
    (hblock : ∀ (w : List ι) (_ : 1 ≤ w.length) (N : ℕ) (_ : 1 ≤ N)
        (V₀ : Fin (w.length + w.reverse.length) → Fin N),
      (∑ q ∈ (Finset.univ.filter fun q : GUEPairing (slotList w V₀) =>
          ¬ SlotCross w.length w.reverse.length (slotPerm q)), slotWeight N q) = (genusSum w N) ^ 2) :
    ∀ᵐ x ∂(commonGaussianMeasure ι), ∀ w : List ι,
      Tendsto (fun N : ℕ => gueNormTrace w (x N)) atTop (𝓝 (wordLimit w)) :=
  ae_all_words_gueNormTrace (fun w N => genusSum w N) hblock
    (fun w hk N => normSq_integral_eq_genusSum w hk N)

/-! ### Reversal invariance of the genus sum -/

/-- **Conjugation of the mean under reversal of the word**: the mean of the reversed word is the
complex conjugate of the mean. -/
theorem integral_gueNormTrace_reverse (w : List ι) :
    ∫ x, gueNormTrace w.reverse x ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) =
      star (∫ x, gueNormTrace w x ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))) := by
  have h : (fun x : EuclideanSpace ℝ (GUECoord ι N) => gueNormTrace w.reverse x) =
      fun x => star (gueNormTrace w x) := by
    funext x
    rw [star_gueNormTrace]
    rfl
  rw [h]
  simpa only [starRingEnd_apply] using
    (integral_conj (μ := stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))
      (f := fun x => gueNormTrace w x))

/-- The scalar `N^{-(k+1)}` of the mean formula is the coercion of a real number. -/
theorem zpow_natCast_eq_ofReal (N n : ℕ) :
    (N : ℂ) ^ (-(n : ℤ)) = (((((N : ℝ)⁻¹) ^ n : ℝ)) : ℂ) := by
  rw [zpow_neg, zpow_natCast, ← inv_pow]
  rw [← Complex.ofReal_natCast N, ← Complex.ofReal_inv, ← Complex.ofReal_pow]

/-- **Reversal invariance of the genus sum**: `genusSum w.reverse = genusSum w`.  The means of `w`
and `w.reverse` are complex conjugates, and both genus sums are real. -/
theorem genusSum_reverse (w : List ι) (hk : 1 ≤ w.length) (N : ℕ) (hN : 1 ≤ N) :
    genusSum w.reverse N = genusSum w N := by
  have hk_r : 1 ≤ w.reverse.length := by simpa using hk
  have hlenr : w.reverse.length = w.length := by simp
  have hexp : (-(((w.reverse.length / 2 + 1 : ℕ)) : ℤ)) = (-(((w.length / 2 + 1 : ℕ)) : ℤ)) := by
    rw [hlenr]
  have hInt := integral_gueNormTrace_reverse (N := N) w
  have hw := integral_eq_genusSum w hk hN
  have hwr := integral_eq_genusSum w.reverse hk_r hN
  rw [hexp] at hwr
  rw [hw, hwr] at hInt
  have hsc := zpow_natCast_eq_ofReal N (w.length / 2 + 1)
  rw [hsc] at hInt
  obtain ⟨r, hr⟩ := genusSum_exists_real w N
  obtain ⟨s, hs⟩ := genusSum_exists_real w.reverse N
  rw [hr, hs] at hInt
  rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, Complex.star_def, Complex.conj_ofReal] at hInt
  have hNe : ((((N : ℝ)⁻¹) ^ (w.length / 2 + 1))) ≠ 0 :=
    pow_ne_zero _ (inv_ne_zero (by positivity))
  have hsr : s = r := mul_left_cancel₀ hNe (Complex.ofReal_inj.mp hInt)
  rw [hs, hr, hsr]

end

end GUEStrongConvergence
