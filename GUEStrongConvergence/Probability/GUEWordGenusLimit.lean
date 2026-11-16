/-
# The limit of the genus expansion: the mean limit from the face-count bounds

Once the exact genus expansion
`∫ tr_N (G_w) = ∑_p label(p) N^{c(p) - m - 1}` is available for a word of length `2m`, the limit of the
mean is a purely finite combinatorial limit: the term of a pairing `p` tends to `label(p)` when
`c(p) = m + 1` and to `0` when `c(p) ≤ m - 1`.  This file contains that limit computation
independently of the transport of pairings along the vertex parametrization, so it can be combined
with the expansion as soon as the expansion is available.
-/
import GUEStrongConvergence.Probability.GUEPairingGenusSplit
import GUEStrongConvergence.Probability.GUEWordGenusExpansion

open MeasureTheory ProbabilityTheory Filter
open scoped RealInnerProductSpace Matrix ENNReal Topology BigOperators

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace GUEStrongConvergence

attribute [local instance] Classical.propDecidable

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {N : ℕ}

/-! ### Scalar limits -/

/-- `N^{-(m+1)} · N^{m+1} → 1`. -/
theorem tendsto_inv_pow_mul_pow_self (m : ℕ) :
    Tendsto (fun N : ℕ => ((N : ℂ) ^ (m + 1))⁻¹ * (N : ℂ) ^ (m + 1)) atTop (𝓝 1) := by
  refine Tendsto.congr' ?_ tendsto_const_nhds
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  have hn0 : (n : ℂ) ≠ 0 := by
    have h : (0 : ℝ) < (n : ℝ) := by
      have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      linarith
    exact_mod_cast h.ne'
  exact (inv_mul_cancel₀ (pow_ne_zero _ hn0)).symm

/-- `N^{-(m+1)} · N^{k} → 0` for `k < m + 1`. -/
theorem tendsto_inv_pow_mul_pow_of_lt (m k : ℕ) (hk : k < m + 1) :
    Tendsto (fun N : ℕ => ((N : ℂ) ^ (m + 1))⁻¹ * (N : ℂ) ^ k) atTop (𝓝 0) := by
  have hpow : Tendsto (fun n : ℕ => ((n : ℂ)⁻¹) ^ (m + 1 - k)) atTop (𝓝 0) := by
    have h := (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℂ)).pow (m + 1 - k)
    rwa [zero_pow (by omega : m + 1 - k ≠ 0)] at h
  refine hpow.congr' ?_
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  have hn0 : (n : ℂ) ≠ 0 := by
    have h : (0 : ℝ) < (n : ℝ) := by
      have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      linarith
    exact_mod_cast h.ne'
  have hmul : ((n : ℂ)⁻¹) ^ k * (n : ℂ) ^ k = 1 := by
    rw [← mul_pow, inv_mul_cancel₀ hn0, one_pow]
  exact (calc ((n : ℂ) ^ (m + 1))⁻¹ * (n : ℂ) ^ k
      = ((n : ℂ)⁻¹) ^ (m + 1) * (n : ℂ) ^ k := by rw [inv_pow]
    _ = ((n : ℂ)⁻¹) ^ ((m + 1 - k) + k) * (n : ℂ) ^ k := by
        rw [show m + 1 - k + k = m + 1 by omega]
    _ = ((n : ℂ)⁻¹) ^ (m + 1 - k) * (((n : ℂ)⁻¹) ^ k * (n : ℂ) ^ k) := by
        rw [pow_add]; ring
    _ = ((n : ℂ)⁻¹) ^ (m + 1 - k) := by rw [hmul, mul_one]).symm

/-! ### The limit of the genus sum -/

/-- **Limit of the genus expansion** (abstract finite combinatorial form): if the face count `c` of
every pairing with the "non-crossing" property is maximal (`m + 1`) and every other pairing has
`c ≤ m - 1`, then the genus sum tends to the sum of the labels of the non-crossing pairings. -/
theorem tendsto_genus_sum {P : Type*} [Fintype P] (c : P → ℕ) (label : P → ℂ)
    (NC : P → Prop) [DecidablePred NC] (m : ℕ)
    (hc_nc : ∀ p, NC p → c p = m + 1)
    (hc_notnc : ∀ p, ¬ NC p → c p ≤ m - 1) :
    Tendsto (fun N : ℕ => ((N : ℂ) ^ (m + 1))⁻¹ * ∑ p : P, label p * (N : ℂ) ^ (c p))
      atTop (𝓝 (∑ p : P, if NC p then label p else 0)) := by
  have hterm : ∀ p : P, Tendsto
      (fun n : ℕ => ((n : ℂ) ^ (m + 1))⁻¹ * (n : ℂ) ^ (c p)) atTop
      (𝓝 (if NC p then 1 else 0)) := by
    intro p
    by_cases h : NC p
    · have hc : c p = m + 1 := hc_nc p h
      rw [ite_eq_left h, hc]
      exact tendsto_inv_pow_mul_pow_self m
    · rw [ite_eq_right h]
      have hc := hc_notnc p h
      have hlt : c p < m + 1 := by
        rcases Nat.eq_or_lt_of_le hc with heq | hlt
        · omega
        · omega
      exact tendsto_inv_pow_mul_pow_of_lt m (c p) hlt
  have hsum : Tendsto
      (fun n : ℕ => ∑ p : P, label p * (((n : ℂ) ^ (m + 1))⁻¹ * (n : ℂ) ^ (c p)))
      atTop (𝓝 (∑ p : P, label p * (if NC p then (1 : ℂ) else 0))) :=
    tendsto_finsetSum Finset.univ (fun p _ => (hterm p).const_mul (label p))
  have hval : (∑ p : P, label p * (if NC p then (1 : ℂ) else 0)) =
      ∑ p : P, if NC p then label p else 0 :=
    Finset.sum_congr rfl fun p _ => by by_cases h : NC p <;> simp [h]
  rw [hval] at hsum
  refine hsum.congr' ?_
  filter_upwards with n
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun p _ => by ring

/-- **Mean limit in the presence of the genus expansion**: for a word of length `2m` whose exact
moment is the genus sum over pairings of a list `l` of length `2m`, the mean tends to the sum of the
labels of the pairings with maximal face count `m + 1`. -/
theorem genus_limit {m : ℕ} (l : List (GUEEntry ι N)) (hl : l.length = 2 * m)
    (label : GUEPairing l → ℂ) (NC : GUEPairing l → Prop) [DecidablePred NC]
    (hnc : ∀ p, NC p → pairOrbitCount p = m + 1)
    (hnotnc : ∀ p, ¬ NC p → pairOrbitCount p ≤ m - 1)
    (u : ℕ → ℂ)
    (hgenus : ∀ (M : ℕ) (h : l.length = 2 * m),
      u M = ((M : ℂ) ^ (m + 1))⁻¹ *
        ∑ p : GUEPairing l, label p * (M : ℂ) ^ (pairOrbitCount p)) :
    Tendsto u atTop (𝓝 (∑ p : GUEPairing l, if NC p then label p else 0)) := by
  refine (tendsto_genus_sum (P := GUEPairing l) (fun p => pairOrbitCount p) label NC m hnc
    hnotnc).congr' ?_
  filter_upwards with M
  exact (hgenus M hl).symm


/-! ### Wiring to the concrete face count and the non-crossing pairings -/

/-- **The face count takes no intermediate values**: for a pairing of `2m` entries (`m ≥ 1`), either
`c(p) = m + 1` (maximal) or `c(p) ≤ m - 1`. -/
theorem pairOrbitCount_eq_or_le_pred {m : ℕ} (hm : 1 ≤ m) (l : List (GUEEntry ι N))
    (hl : l.length = 2 * m) (p : GUEPairing l) :
    pairOrbitCount p = m + 1 ∨ pairOrbitCount p ≤ m - 1 := by
  have hle := pairOrbitCount_le l p m hl
  have hmod := pairOrbitCount_mod_two l p m hm hl
  rcases eq_or_ne (pairOrbitCount p) (m + 1) with h | h
  · exact Or.inl h
  · right
    omega

/-- **Mean limit for non-crossing pairings**: with the exact genus expansion of a word of length
`2m` as hypothesis, if every non-crossing pairing has maximal face count `m + 1`
(`hnc`, the ear induction), then the mean tends to the sum of the labels of the non-crossing
pairings.  The crossing bound is `pairOrbitCount_le_of_not_isNonCrossing`. -/
theorem genus_limit_isNonCrossing {m : ℕ} (l : List (GUEEntry ι N)) (hl : l.length = 2 * m)
    (label : GUEPairing l → ℂ)
    (hnc : ∀ p : GUEPairing l, IsNonCrossing p → pairOrbitCount p = m + 1)
    (u : ℕ → ℂ)
    (hgenus : ∀ M : ℕ, u M = ((M : ℂ) ^ (m + 1))⁻¹ *
      ∑ p : GUEPairing l, label p * (M : ℂ) ^ (pairOrbitCount p)) :
    Tendsto u atTop
      (𝓝 (∑ p ∈ ((Finset.univ : Finset (GUEPairing l)).filter IsNonCrossing), label p)) := by
  simpa only [Finset.sum_filter] using
    (genus_limit l hl label IsNonCrossing hnc
      (fun p hp => pairOrbitCount_le_of_not_isNonCrossing l p m hl hp) u
      (fun M _ => hgenus M))
end

end GUEStrongConvergence
