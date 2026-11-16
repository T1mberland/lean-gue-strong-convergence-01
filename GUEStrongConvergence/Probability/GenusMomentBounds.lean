/-
# Honest genus-weighted bounds for GUE trace-word moments

This file extracts every bound on `E τ_N(X^{2m})` that follows *directly* from the exact genus
expansion

`E τ_N(w) = N^{-(m+1)} ∑_{p : pairings} label(p) N^{c(p)}`

(`integral_gueNormTrace_eq_genus_canonical`) together with the two structural facts

* `c(p) = m + 1` for non-crossing `p` (`pairOrbitCount_eq_of_isNonCrossing`),
* `c(p) ≤ m - 1` for crossing `p` (`pairOrbitCount_le_of_not_isNonCrossing`),

and the label bound `‖label(p)‖ ≤ 1` (`norm_gueLabelWeight_le_one`).

## What is proved here

Writing `nc(l)` for the number of non-crossing pairings of a list `l` of `2m` entries and
`cr(l) = #(all pairings) - nc(l)` for the number of crossing ones, we prove

`‖E τ_N(w)‖ ≤ nc + cr / N²`    (`norm_integral_gueNormTrace_le_dichotomy`)

and, since the total number of pairings of `2m` entries is `(2m - 1)!!`
(`pairingCount_le_doubleFactorial`),

`‖E τ_N(w)‖ ≤ nc + (2m - 1)!! / N²`
(`norm_integral_gueNormTrace_le_doubleFactorial`),

as well as the cruder `‖E τ_N(w)‖ ≤ (2m - 1)!! (1 + N⁻²)`.  The same dichotomy holds for the
unnormalized genus sum (`norm_genusSum_le_dichotomy`).  These bounds are uniform in the word `w`
(of fixed length) and hold for every dimension `N ≥ 1`.

Two consequences are recorded:

* `norm_integral_gueNormTrace_le_const`: for every *fixed* length `2m` the mean is bounded
  uniformly in `N ≥ 1` by an explicit constant depending only on `m`.

## What is NOT proved here (the missing combinatorial lemma)

The crude bound is useless for growing `m`: the second term `(2m - 1)!! / N²` diverges when
`m ≍ log N`.  The classical Bai–Yin / Harer–Zagier route needs a *genus-weighted* count of
crossing pairings.  Precisely, for a pairing `p` of `2m` entries put
`g(p) = (m + 1 - c(p)) / 2 ∈ {0, 1, …, ⌊m/2⌋}` (an integer by `pairOrbitCount_mod_two`), and
let `ε_g(m) = #{p : c(p) = m + 1 - 2g} = #{p : g(p) = g}`.  Then the exact mean is

`E τ_N(w) ≤ ∑_{g=0}^{⌊m/2⌋} ε_g(m) N^{-2g}`,

because `|label| ≤ 1` and every pairing of genus `g` contributes `N^{m+1-2g}`.

**Missing lemma (Harer–Zagier genus count).**  There exist absolute constants `K ≥ 1` and
`c > 0` such that for all `m ≥ 1` and all `g` with `3 g ≤ m`,

  `ε_g(m) ≤ 4^m · (K m^3)^g / g!`.

(Equivalently, `ε_g(m) / Catalan_m` is bounded by a polynomial of degree `3g` in `m`; this is a
consequence of the Harer–Zagier formula / the Harer–Zagier recursion for the number of
genus-`g` pairings.  For `g = 1` the exact value is
`ε_1(m) = Catalan_m · (m-1)m(m+1)/12`, consistent with the bound.)

Granted this lemma, splitting the sum at `G = ⌊m/3⌋` gives, for `N ≥ 2`,

`∑_{g=1}^{G} ε_g(m) N^{-2g} ≤ 4^m · exp(K m^3 / N^2)`

and, using only `∑_g ε_g(m) = (2m-1)!!` for the remaining genera,

`∑_{g>G} ε_g(m) N^{-2g} ≤ 2 · (2m-1)!! · N^{-2G}`.

For `m ≤ c N^{2/3}` the first factor is `≤ e^{K c^3} · 4^m` and the second is
`≤ (2m/(e N^{2/3}))^m ≤ 4^m` once `N` is large relative to `m`, so
`E τ_N(X^{2m}) ≤ B · 4^m` uniformly.  This is exactly the uniformity needed for the Markov
bound `P(‖X‖ > 2 + ε) ≤ N (4+δ)^m / (2+ε)^{2m}` with `m = C log N / ε`.

The missing ingredient is thus a *counting* theorem about `GUEPairing` (the Harer–Zagier
genus count), not an analytic statement.  The present file provides the analytic/algebraic
half of the reduction and the honest partial bounds that do not need it.

No `sorry`, no `admit`, no new axioms.
-/
import GUEStrongConvergence.Probability.GenusSecondOrder
import GUEStrongConvergence.Probability.GUEPairingFormula

open MeasureTheory ProbabilityTheory Filter
open scoped RealInnerProductSpace Matrix ENNReal Topology BigOperators

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace GUEStrongConvergence

attribute [local instance] Classical.propDecidable

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {N : ℕ}

/-! ### Counting pairings -/

/-- The total number of pairings of a list of GUE entries. -/
def pairingCount (l : List (GUEEntry ι N)) : ℕ :=
  Fintype.card (GUEPairing l)

/-- The number of non-crossing pairings of a list of GUE entries. -/
def nonCrossingPairingCount (l : List (GUEEntry ι N)) : ℕ :=
  ((Finset.univ : Finset (GUEPairing l)).filter IsNonCrossing).card

/-- The number of crossing pairings of a list of GUE entries. -/
def crossingPairingCount (l : List (GUEEntry ι N)) : ℕ :=
  pairingCount l - nonCrossingPairingCount l

/-- The unweighted genus pairing sum `∑_p N^{c(p)}`. -/
def pairingWeightSum (l : List (GUEEntry ι N)) (M : ℕ) : ℕ :=
  ∑ p : GUEPairing l, M ^ pairOrbitCount p

/-- The number of pairings depends only on the length of the list. -/
theorem pairingCount_eq_of_length_eq {l₁ l₂ : List (GUEEntry ι N)}
    (h : l₁.length = l₂.length) : pairingCount l₁ = pairingCount l₂ :=
  GUEPairing.card_castLength h

/-- The number of pairings of the empty list is `1`. -/
theorem pairingCount_nil : pairingCount ([] : List (GUEEntry ι N)) = 1 := by
  rw [pairingCount, Fintype.card_eq_one_iff]
  exact ⟨GUEPairing.nil, fun p => by cases p; rfl⟩

/-- A singleton list admits no pairing. -/
theorem pairingCount_singleton (e : GUEEntry ι N) : pairingCount [e] = 0 := by
  rw [pairingCount, Fintype.card_eq_zero_iff]
  exact ⟨fun p => by cases p with | cons _ _ k _ => exact Fin.elim0 k⟩

/-- **Partner-of-the-head recursion for the number of pairings.** -/
theorem pairingCount_cons_cons (e x : GUEEntry ι N) (l : List (GUEEntry ι N)) :
    pairingCount (e :: x :: l) = (l.length + 1) * pairingCount l := by
  classical
  have hlen : ∀ k : Fin (x :: l).length, ((x :: l).eraseIdx k).length = l.length := by
    intro k
    rw [List.length_eraseIdx]
    simp only [List.length_cons]
    split_ifs with h <;> omega
  rw [pairingCount, Fintype.card_congr (GUEPairing.consEquiv e (x :: l)),
    Fintype.card_sigma]
  have hcard : ∀ k : Fin (x :: l).length,
      Fintype.card (GUEPairing ((x :: l).eraseIdx k)) = pairingCount l := by
    intro k
    exact GUEPairing.card_castLength (hlen k)
  rw [Finset.sum_congr rfl (fun k _ => hcard k), Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, List.length_cons]
  push_cast
  ring

/-- **The total number of pairings of `n` entries is at most `(n-1)!!`** (equal for even `n`). -/
theorem pairingCount_le_doubleFactorial (l : List (GUEEntry ι N)) :
    pairingCount l ≤ Nat.doubleFactorial (l.length - 1) := by
  classical
  suffices h : ∀ n, ∀ l : List (GUEEntry ι N), l.length = n →
      pairingCount l ≤ Nat.doubleFactorial (l.length - 1) from h _ l rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro l hl
    rcases l with _ | ⟨e, _ | ⟨x, l'⟩⟩
    · rw [pairingCount_nil]
      simp [Nat.doubleFactorial]
    · rw [pairingCount_singleton]
      simp [Nat.doubleFactorial]
    · rw [pairingCount_cons_cons]
      have hlt : l'.length < n := by
        simp only [List.length_cons] at hl
        omega
      have hrec : pairingCount l' ≤ Nat.doubleFactorial (l'.length - 1) :=
        ih l'.length hlt l' rfl
      have hmul : (l'.length + 1) * pairingCount l'
          ≤ (l'.length + 1) * Nat.doubleFactorial (l'.length - 1) :=
        Nat.mul_le_mul_left _ hrec
      have hstep : (l'.length + 1) * Nat.doubleFactorial (l'.length - 1)
          = Nat.doubleFactorial (l'.length + 1) :=
        (Nat.doubleFactorial_add_one (l'.length)).symm
      have hlen : (e :: x :: l').length - 1 = l'.length + 1 := by
        rw [List.length_cons, List.length_cons]
        omega
      rw [hlen]
      exact hmul.trans_eq hstep

/-- **The exact number of pairings of `2m` entries is `(2m-1)!!`.** -/
theorem pairingCount_eq_doubleFactorial (l : List (GUEEntry ι N)) (m : ℕ)
    (hl : l.length = 2 * m) :
    pairingCount l = Nat.doubleFactorial (2 * m - 1) := by
  classical
  induction m generalizing l with
  | zero =>
      have hnil : l = [] := List.length_eq_zero_iff.mp (by simpa using hl)
      subst hnil
      rw [pairingCount_nil]
      simp [Nat.doubleFactorial]
  | succ m ih =>
      rcases l with _ | ⟨e, _ | ⟨x, l'⟩⟩
      · simp only [List.length_nil] at hl
        omega
      · simp only [List.length_cons, List.length_nil] at hl
        omega
      · rw [pairingCount_cons_cons]
        have hl' : l'.length = 2 * m := by
          simp only [List.length_cons] at hl
          omega
        rw [hl', ih l' hl']
        rw [show 2 * (m + 1) - 1 = 2 * m + 1 by omega]
        rw [Nat.doubleFactorial_add_one]

/-- The number of crossing pairings is at most the total number of pairings. -/
theorem crossingPairingCount_le_pairingCount (l : List (GUEEntry ι N)) :
    crossingPairingCount l ≤ pairingCount l :=
  Nat.sub_le _ _

/-- The number of non-crossing pairings is at most the total number of pairings. -/
theorem nonCrossingPairingCount_le_pairingCount (l : List (GUEEntry ι N)) :
    nonCrossingPairingCount l ≤ pairingCount l := by
  rw [nonCrossingPairingCount, pairingCount]
  exact Finset.card_filter_le _ _

/-! ### The label-weighted pairing sum -/

/-- **The label-weighted pairing sum is bounded by the unweighted genus sum.** -/
theorem norm_pairing_label_sum_le (l : List (GUEEntry ι N)) (label : GUEPairing l → ℂ)
    (hlabel : ∀ p, ‖label p‖ ≤ 1) (M : ℕ) (hM : 1 ≤ M) :
    ‖∑ p : GUEPairing l, label p * (M : ℂ) ^ pairOrbitCount p‖
      ≤ ∑ p : GUEPairing l, (M : ℝ) ^ pairOrbitCount p := by
  refine (norm_sum_le _ _).trans ?_
  refine Finset.sum_le_sum fun p _ => ?_
  rw [norm_mul, norm_pow, Complex.norm_natCast]
  exact mul_le_of_le_one_left (by positivity) (hlabel p)

/-- **Dichotomy bound for the genus-weighted pairing sum**: the non-crossing pairings
contribute `N^{m+1}` each and the crossing ones at most `N^{m-1}` each. -/
theorem pairingWeightSum_le_dichotomy (l : List (GUEEntry ι N)) (m : ℕ)
    (hl : l.length = 2 * m) (hm : 1 ≤ m) (M : ℕ) (hM : 1 ≤ M) :
    (pairingWeightSum l M : ℝ)
      ≤ nonCrossingPairingCount l * (M : ℝ) ^ (m + 1)
        + crossingPairingCount l * (M : ℝ) ^ (m - 1) := by
  classical
  have hcast : (pairingWeightSum l M : ℝ)
      = ∑ p : GUEPairing l, (M : ℝ) ^ pairOrbitCount p := by
    simp [pairingWeightSum]
  rw [hcast]
  rw [← Finset.sum_filter_add_sum_filter_not (s := (Finset.univ : Finset (GUEPairing l)))
    (p := IsNonCrossing) (f := fun p => (M : ℝ) ^ pairOrbitCount p)]
  have hnc : ∑ p ∈ (Finset.univ : Finset (GUEPairing l)).filter IsNonCrossing,
        (M : ℝ) ^ pairOrbitCount p
      ≤ nonCrossingPairingCount l * (M : ℝ) ^ (m + 1) := by
    have hterm : ∀ p ∈ (Finset.univ : Finset (GUEPairing l)).filter IsNonCrossing,
        (M : ℝ) ^ pairOrbitCount p = (M : ℝ) ^ (m + 1) := by
      intro p hp
      rw [pairOrbitCount_eq_of_isNonCrossing p m hm hl (Finset.mem_filter.mp hp).2]
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, nonCrossingPairingCount,
      nsmul_eq_mul]
  have hcr : ∑ p ∈ (Finset.univ : Finset (GUEPairing l)).filter (fun p => ¬ IsNonCrossing p),
        (M : ℝ) ^ pairOrbitCount p
      ≤ crossingPairingCount l * (M : ℝ) ^ (m - 1) := by
    have hterm : ∀ p ∈ (Finset.univ : Finset (GUEPairing l)).filter
          (fun p => ¬ IsNonCrossing p),
        (M : ℝ) ^ pairOrbitCount p ≤ (M : ℝ) ^ (m - 1) := by
      intro p hp
      exact pow_le_pow_right₀ (by exact_mod_cast hM)
        (pairOrbitCount_le_of_not_isNonCrossing l p m hl (Finset.mem_filter.mp hp).2)
    have hcard : ((Finset.univ : Finset (GUEPairing l)).filter
          (fun p => ¬ IsNonCrossing p)).card = crossingPairingCount l := by
      have h := Finset.card_filter_add_card_filter_not
        (s := (Finset.univ : Finset (GUEPairing l))) (p := IsNonCrossing)
      have huniv : (Finset.univ : Finset (GUEPairing l)).card = pairingCount l := rfl
      rw [crossingPairingCount, nonCrossingPairingCount]
      omega
    calc ∑ p ∈ (Finset.univ : Finset (GUEPairing l)).filter (fun p => ¬ IsNonCrossing p),
          (M : ℝ) ^ pairOrbitCount p
        ≤ ∑ _p ∈ (Finset.univ : Finset (GUEPairing l)).filter
            (fun p => ¬ IsNonCrossing p), (M : ℝ) ^ (m - 1) :=
          Finset.sum_le_sum hterm
      _ = (((Finset.univ : Finset (GUEPairing l)).filter
            (fun p => ¬ IsNonCrossing p)).card : ℝ) * (M : ℝ) ^ (m - 1) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ = crossingPairingCount l * (M : ℝ) ^ (m - 1) := by rw [hcard]
  linarith

/-! ### Bounds for the GUE trace-word mean -/

/-- **The dichotomy bound for the mean**: non-crossing pairings contribute their labels
(at most `1` each) and crossing pairings lose at least `N²`. -/
theorem norm_integral_gueNormTrace_le_dichotomy (w : List ι) (m : ℕ)
    (hl : w.length = 2 * m) (hm : 1 ≤ m) (M : ℕ) (hM : 1 ≤ M) :
    ‖∫ x : EuclideanSpace ℝ (GUECoord ι M), gueNormTrace (N := M) w x
        ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι M)))‖
      ≤ nonCrossingPairingCount (gueCanonicalEntries w m hl hM)
        + crossingPairingCount (gueCanonicalEntries w m hl hM) / (M : ℝ) ^ 2 := by
  classical
  have hpos : 1 ≤ w.length := by omega
  have hE := integral_gueNormTrace_eq_genus_canonical (N := M) w m hl hpos hM
  set l := gueCanonicalEntries w m hl hM with hl_def
  have hlen : l.length = 2 * m := length_gueCanonicalEntries w m hl hM
  have hMpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have hscalar : ‖(M : ℂ) ^ (-(m + 1) : ℤ)‖ = ((M : ℝ) ^ (m + 1))⁻¹ := by
    rw [show (-(m + 1) : ℤ) = -((m + 1 : ℕ) : ℤ) by omega, zpow_neg, zpow_natCast,
      norm_inv, norm_pow, Complex.norm_natCast]
  rw [hE, norm_mul, hscalar]
  have hsum := norm_pairing_label_sum_le l (fun p => gueLabelWeight l p)
    (fun p => norm_gueLabelWeight_le_one l p) M hM
  have hweight := pairingWeightSum_le_dichotomy l m hlen hm M hM
  have hcast : (pairingWeightSum l M : ℝ) = ∑ p : GUEPairing l, (M : ℝ) ^ pairOrbitCount p := by
    simp [pairingWeightSum]
  have hsum' : ‖∑ p : GUEPairing l, gueLabelWeight l p * (M : ℂ) ^ pairOrbitCount p‖
      ≤ (pairingWeightSum l M : ℝ) := by
    rw [hcast]
    exact hsum
  calc ((M : ℝ) ^ (m + 1))⁻¹
        * ‖∑ p : GUEPairing l, gueLabelWeight l p * (M : ℂ) ^ pairOrbitCount p‖
      ≤ ((M : ℝ) ^ (m + 1))⁻¹ * (pairingWeightSum l M : ℝ) :=
        mul_le_mul_of_nonneg_left hsum' (by positivity)
    _ ≤ ((M : ℝ) ^ (m + 1))⁻¹
          * (nonCrossingPairingCount l * (M : ℝ) ^ (m + 1)
            + crossingPairingCount l * (M : ℝ) ^ (m - 1)) := by
        refine mul_le_mul_of_nonneg_left hweight (by positivity)
    _ = nonCrossingPairingCount l + crossingPairingCount l / (M : ℝ) ^ 2 := by
        have hM0 : (M : ℝ) ≠ 0 := hMpos.ne'
        have hpow : (M : ℝ) ^ (m + 1) = (M : ℝ) ^ (m - 1) * (M : ℝ) ^ 2 := by
          rw [show m + 1 = (m - 1) + 2 by omega, pow_add]
        rw [hpow]
        field_simp

/-- **Dichotomy bound for the exact genus sum** (unnormalized). -/
theorem norm_genusSum_le_dichotomy (w : List ι) (m : ℕ) (hl : w.length = 2 * m)
    (hm : 1 ≤ m) (M : ℕ) (hM : 1 ≤ M) :
    ‖genusSum w M‖
      ≤ nonCrossingPairingCount (gueCanonicalEntries w m hl hM) * (M : ℝ) ^ (m + 1)
        + crossingPairingCount (gueCanonicalEntries w m hl hM) * (M : ℝ) ^ (m - 1) := by
  classical
  have hpos : 1 ≤ w.length := by omega
  have hcan : w.length = 2 * (w.length / 2) := by omega
  have hk : w.length / 2 = m := by omega
  have hN0 : (M : ℂ) ≠ 0 := by
    have : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
    exact_mod_cast this.ne'
  -- bound the normalized mean, then undo the normalization
  have hdich := norm_integral_gueNormTrace_le_dichotomy w m hl hm M hM
  have hint := integral_eq_genusSum (N := M) w hpos hM
  have hzw : ((M : ℂ) ^ (-(((w.length / 2 + 1 : ℕ)) : ℤ)))
      = (((M : ℂ) ^ (m + 1))⁻¹) := by
    have h1 : w.length / 2 + 1 = m + 1 := by omega
    rw [h1, zpow_neg, zpow_natCast]
  rw [hint, hzw, norm_mul, norm_inv, norm_pow, Complex.norm_natCast] at hdich
  set l := gueCanonicalEntries w m hl hM with hl_def
  have hdich' : ((M : ℝ) ^ (m + 1))⁻¹ * ‖genusSum w M‖
      ≤ nonCrossingPairingCount l + crossingPairingCount l / (M : ℝ) ^ 2 := by
    simpa [l] using hdich
  -- multiply through by `M^{m+1}`
  have hMpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have hmul := mul_le_mul_of_nonneg_left hdich'
    (show (0 : ℝ) ≤ (M : ℝ) ^ (m + 1) by positivity)
  have hleft : (M : ℝ) ^ (m + 1) * (((M : ℝ) ^ (m + 1))⁻¹ * ‖genusSum w M‖)
      = ‖genusSum w M‖ := by
    field_simp
  rw [hleft] at hmul
  refine hmul.trans (le_of_eq ?_)
  have hM0 : (M : ℝ) ≠ 0 := hMpos.ne'
  have hpow : (M : ℝ) ^ (m + 1) = (M : ℝ) ^ (m - 1) * (M : ℝ) ^ 2 := by
    rw [show m + 1 = (m - 1) + 2 by omega, pow_add]
  rw [hpow]
  field_simp

/-- **Reduction of the uniform genus moment bound to a genus-weighted count.**

This is the precise interface for the missing Harer--Zagier input.  If the weighted pairing sum
of a word of length `2m` satisfies `∑_p N^{c(p)} ≤ C^m N^{m+1}` for some `C > 0` and all
`N ≥ 1`, then the normalized mean obeys the uniform bound `‖E τ_N(w)‖ ≤ C^m`.  The whole
remaining content of the growing-order genus bound is therefore the combinatorial estimate on
`pairingWeightSum`; no analysis is missing. -/
theorem norm_integral_gueNormTrace_le_of_pairingWeightSum (w : List ι) (m : ℕ)
    (hl : w.length = 2 * m) (hm : 1 ≤ m) (M : ℕ) (hM : 1 ≤ M) (C : ℝ)
    (hC : 0 ≤ C)
    (hweight : (pairingWeightSum (gueCanonicalEntries w m hl hM) M : ℝ)
      ≤ C ^ m * (M : ℝ) ^ (m + 1)) :
    ‖∫ x : EuclideanSpace ℝ (GUECoord ι M), gueNormTrace (N := M) w x
        ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι M)))‖ ≤ C ^ m := by
  classical
  have hpos : 1 ≤ w.length := by omega
  have hE := integral_gueNormTrace_eq_genus_canonical (N := M) w m hl hpos hM
  set l := gueCanonicalEntries w m hl hM with hl_def
  have hMpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have hscalar : ‖(M : ℂ) ^ (-(m + 1) : ℤ)‖ = ((M : ℝ) ^ (m + 1))⁻¹ := by
    rw [show (-(m + 1) : ℤ) = -((m + 1 : ℕ) : ℤ) by omega, zpow_neg, zpow_natCast,
      norm_inv, norm_pow, Complex.norm_natCast]
  rw [hE, norm_mul, hscalar]
  have hb := norm_pairing_label_sum_le l (fun p => gueLabelWeight l p)
    (fun p => norm_gueLabelWeight_le_one l p) M hM
  have hsum' : ‖∑ p : GUEPairing l, gueLabelWeight l p * (M : ℂ) ^ pairOrbitCount p‖
      ≤ (pairingWeightSum l M : ℝ) := by
    have hcast : (pairingWeightSum l M : ℝ)
        = ∑ p : GUEPairing l, (M : ℝ) ^ pairOrbitCount p := by
      simp [pairingWeightSum]
    rw [hcast]
    exact hb
  refine ((mul_le_mul_of_nonneg_left hsum' (by positivity)).trans ?_)
  have hmain : ((M : ℝ) ^ (m + 1))⁻¹ * (C ^ m * (M : ℝ) ^ (m + 1)) = C ^ m := by
    field_simp
  rw [← hmain]
  exact mul_le_mul_of_nonneg_left hweight (by positivity)

/-- **The double-factorial form of the dichotomy bound**: since there are at most `(2m-1)!!`
pairings in total, the crossing contribution is at most `(2m-1)!! / N²`. -/
theorem norm_integral_gueNormTrace_le_doubleFactorial (w : List ι) (m : ℕ)
    (hl : w.length = 2 * m) (hm : 1 ≤ m) (M : ℕ) (hM : 1 ≤ M) :
    ‖∫ x : EuclideanSpace ℝ (GUECoord ι M), gueNormTrace (N := M) w x
        ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι M)))‖
      ≤ nonCrossingPairingCount (gueCanonicalEntries w m hl hM)
        + (Nat.doubleFactorial (2 * m - 1) : ℝ) / (M : ℝ) ^ 2 := by
  classical
  set l := gueCanonicalEntries w m hl hM with hl_def
  have hlen : l.length = 2 * m := length_gueCanonicalEntries w m hl hM
  have hcr : crossingPairingCount l ≤ Nat.doubleFactorial (2 * m - 1) := by
    refine (crossingPairingCount_le_pairingCount l).trans ?_
    have h := pairingCount_le_doubleFactorial l
    rwa [hlen] at h
  refine (norm_integral_gueNormTrace_le_dichotomy w m hl hm M hM).trans ?_
  have hstep : (crossingPairingCount l : ℝ) / (M : ℝ) ^ 2
      ≤ (Nat.doubleFactorial (2 * m - 1) : ℝ) / (M : ℝ) ^ 2 := by
    exact div_le_div_of_nonneg_right (by exact_mod_cast hcr) (by positivity)
  linarith

/-- **The cruder uniform bound** `‖E τ_N(w)‖ ≤ (2m-1)!! (1 + N⁻²)`. -/
theorem norm_integral_gueNormTrace_le_doubleFactorial_mul (w : List ι) (m : ℕ)
    (hl : w.length = 2 * m) (hm : 1 ≤ m) (M : ℕ) (hM : 1 ≤ M) :
    ‖∫ x : EuclideanSpace ℝ (GUECoord ι M), gueNormTrace (N := M) w x
        ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι M)))‖
      ≤ (Nat.doubleFactorial (2 * m - 1) : ℝ) * (1 + ((M : ℝ) ^ 2)⁻¹) := by
  classical
  set l := gueCanonicalEntries w m hl hM with hl_def
  have hlen : l.length = 2 * m := length_gueCanonicalEntries w m hl hM
  have hnc : (nonCrossingPairingCount l : ℝ) ≤ (Nat.doubleFactorial (2 * m - 1) : ℝ) := by
    have h1 : nonCrossingPairingCount l ≤ pairingCount l := nonCrossingPairingCount_le_pairingCount l
    have h2 := pairingCount_le_doubleFactorial l
    rw [hlen] at h2
    exact_mod_cast h1.trans h2
  refine (norm_integral_gueNormTrace_le_doubleFactorial w m hl hm M hM).trans ?_
  have hpos : (0 : ℝ) ≤ (Nat.doubleFactorial (2 * m - 1) : ℝ) := by positivity
  have hM2 : (0 : ℝ) < (M : ℝ) ^ 2 := by positivity
  have hdiv : (Nat.doubleFactorial (2 * m - 1) : ℝ) / (M : ℝ) ^ 2
      = (Nat.doubleFactorial (2 * m - 1) : ℝ) * ((M : ℝ) ^ 2)⁻¹ := by
    rw [div_eq_mul_inv]
  rw [hdiv]
  nlinarith

/-- **Uniformity in the dimension for fixed length**: for every fixed `m ≥ 1` there is an
explicit constant `C` (depending only on `m`) with `‖E τ_N(w)‖ ≤ C` for every `N ≥ 1`. -/
theorem norm_integral_gueNormTrace_le_const (w : List ι) (m : ℕ)
    (hl : w.length = 2 * m) (hm : 1 ≤ m) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ M : ℕ, 1 ≤ M →
      ‖∫ x : EuclideanSpace ℝ (GUECoord ι M), gueNormTrace (N := M) w x
          ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι M)))‖ ≤ C := by
  classical
  refine ⟨2 * (Nat.doubleFactorial (2 * m - 1) : ℝ), by positivity, ?_⟩
  intro M hM
  refine (norm_integral_gueNormTrace_le_doubleFactorial_mul w m hl hm M hM).trans ?_
  have hM1 : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hM2 : (1 : ℝ) ≤ (M : ℝ) ^ 2 := by nlinarith
  have hinv : ((M : ℝ) ^ 2)⁻¹ ≤ 1 := by
    rw [inv_le_one₀ (by positivity)]
    exact hM2
  have hnonneg : (0 : ℝ) ≤ (Nat.doubleFactorial (2 * m - 1) : ℝ) := by positivity
  nlinarith

end

end GUEStrongConvergence
