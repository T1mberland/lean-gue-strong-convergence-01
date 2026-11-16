/-
# Moment roots recover the spectral radius of a compactly supported measure

For a probability measure `μ` on `ℝ` whose support is compact, the `2k`-th roots of the
even moments `∫ t ^ (2k) ∂μ` converge to `sup {|t| : t ∈ support μ}`.

This is the purely measure-theoretic core of the faithful-state moment-norm formula
`‖a‖ = lim_k ψ(a ^ (2k)) ^ (1 / (2k))`, which in turn is the lower-bound input of the
deterministic strong-convergence transfer.
-/
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Order.Compact

set_option maxHeartbeats 1600000

noncomputable section

open Filter MeasureTheory Topology
open scoped ENNReal NNReal

namespace GUEStrongConvergence

/-- A nonzero `2k`-th power of a real number is nonnegative. -/
lemma sq_pow_nonneg (t : ℝ) (k : ℕ) : 0 ≤ t ^ (2 * k) := by
  rw [pow_mul]
  positivity

/-- An even power is the corresponding power of the absolute value. -/
lemma sq_pow_eq_abs_pow (t : ℝ) (k : ℕ) : t ^ (2 * k) = |t| ^ (2 * k) := by
  rw [pow_mul, pow_mul, sq_abs]

/-- The compact support of a probability measure is nonempty. -/
theorem support_nonempty_of_probability {μ : Measure ℝ} [IsProbabilityMeasure μ] :
    μ.support.Nonempty := by
  apply Measure.nonempty_support
  intro h0
  have h1 : μ Set.univ = 0 := by rw [h0]; simp
  rw [measure_univ] at h1
  exact one_ne_zero h1

/-- **Moment-root limit.** For a probability measure on `ℝ` supported on a compact set,
the roots of the even moments tend to the largest modulus in the support. -/
theorem tendsto_moment_root_eq_sSup {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hs : IsCompact μ.support) (hcompl : μ μ.supportᶜ = 0) :
    Tendsto (fun k : ℕ => (∫ t : ℝ, t ^ (2 * k) ∂μ) ^ ((1 : ℝ) / ((2 * k : ℕ) : ℝ))) atTop
      (𝓝 (sSup ((fun t : ℝ => |t|) '' μ.support))) := by
  classical
  set C : ℝ := sSup ((fun t : ℝ => |t|) '' μ.support) with hC
  have hsne : μ.support.Nonempty := support_nonempty_of_probability
  obtain ⟨t0, ht0, hmax⟩ := hs.exists_isMaxOn hsne (continuous_abs.continuousOn)
  have hbdd : BddAbove ((fun t : ℝ => |t|) '' μ.support) :=
    ⟨|t0|, by rintro _ ⟨t, ht, rfl⟩; exact hmax ht⟩
  have hmemC : |t0| ∈ (fun t : ℝ => |t|) '' μ.support := ⟨t0, ht0, rfl⟩
  have hCeq : C = |t0| := by
    rw [hC]
    refine le_antisymm (csSup_le ⟨_, hmemC⟩ ?_) (le_csSup hbdd hmemC)
    rintro y ⟨t, ht, rfl⟩
    simpa using hmax ht
  have hCnn : 0 ≤ C := by rw [hCeq]; positivity
  have hae : ∀ᵐ t ∂μ, t ∈ μ.support := by
    rw [MeasureTheory.ae_iff]
    have hset : {t : ℝ | t ∉ μ.support} = μ.supportᶜ := rfl
    rw [hset]
    exact hcompl
  have hmom_nonneg : ∀ k : ℕ, 0 ≤ ∫ t : ℝ, t ^ (2 * k) ∂μ := fun k =>
    integral_nonneg fun t => sq_pow_nonneg t k
  -- pointwise bound on the support
  have hpt : ∀ k : ℕ, ∀ᵐ t ∂μ, t ^ (2 * k) ≤ C ^ (2 * k) := by
    intro k
    filter_upwards [hae] with t ht
    have hle : |t| ≤ C := by rw [hCeq]; exact hmax ht
    rw [sq_pow_eq_abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg t) hle (2 * k)
  have hint : ∀ k : ℕ, Integrable (fun t : ℝ => t ^ (2 * k)) μ := by
    intro k
    refine (integrable_const (C ^ (2 * k))).mono' (by fun_prop) ?_
    filter_upwards [hpt k] with t ht
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_pow_nonneg t k)]
    exact ht
  -- upper bound on the moments
  have hupper_mom : ∀ k : ℕ, (∫ t : ℝ, t ^ (2 * k) ∂μ) ≤ C ^ (2 * k) := by
    intro k
    calc ∫ t : ℝ, t ^ (2 * k) ∂μ ≤ ∫ _t : ℝ, C ^ (2 * k) ∂μ :=
          integral_mono_ae (hint k) (integrable_const _) (hpt k)
      _ = C ^ (2 * k) := by simp
  -- the root of a `2k`-th power
  have hroot_pow : ∀ k : ℕ, k ≠ 0 → (C ^ (2 * k) : ℝ) ^ ((1 : ℝ) / ((2 * k : ℕ) : ℝ)) = C := by
    intro k hk
    rw [← Real.rpow_natCast_mul hCnn (2 * k) ((1 : ℝ) / ((2 * k : ℕ) : ℝ))]
    have h1 : ((2 * k : ℕ) : ℝ) * ((1 : ℝ) / ((2 * k : ℕ) : ℝ)) = 1 := by
      rw [mul_one_div]
      exact div_self (by positivity)
    rw [h1, Real.rpow_one]
  -- upper bound on the roots
  have hupper : ∀ᶠ k : ℕ in atTop, (∫ t : ℝ, t ^ (2 * k) ∂μ) ^ ((1 : ℝ) / ((2 * k : ℕ) : ℝ)) ≤ C := by
    filter_upwards [Filter.eventually_ge_atTop 1] with k hk
    calc (∫ t : ℝ, t ^ (2 * k) ∂μ) ^ ((1 : ℝ) / ((2 * k : ℕ) : ℝ))
        ≤ (C ^ (2 * k) : ℝ) ^ ((1 : ℝ) / ((2 * k : ℕ) : ℝ)) :=
          Real.rpow_le_rpow (hmom_nonneg k) (hupper_mom k) (by positivity)
      _ = C := hroot_pow k (by omega)
  -- lower bound on the roots
  have hlower : ∀ ε : ℝ, 0 < ε → ∀ᶠ k : ℕ in atTop,
      C - ε ≤ (∫ t : ℝ, t ^ (2 * k) ∂μ) ^ ((1 : ℝ) / ((2 * k : ℕ) : ℝ)) := by
    intro ε hε
    by_cases hCsmall : C ≤ ε / 2
    · filter_upwards [Filter.eventually_ge_atTop 0] with k _
      have h0 : C - ε ≤ 0 := by linarith
      exact h0.trans (Real.rpow_nonneg (hmom_nonneg k) _)
    push_neg at hCsmall
    set η : ℝ := ε / 2 with hη
    have hηpos : 0 < η := by positivity
    have hCη : 0 < C - η := by rw [hη]; linarith
    set U : Set ℝ := {t : ℝ | C - η < |t|} with hU
    have hUopen : IsOpen U := isOpen_lt continuous_const continuous_abs
    have hUm : MeasurableSet U := hUopen.measurableSet
    have ht0U : t0 ∈ U := by
      simp only [hU, Set.mem_setOf_eq, hCeq]
      linarith
    have hUpos : 0 < μ U :=
      (Measure.mem_support_iff_forall (μ := μ) (x := t0)).mp ht0 U (hUopen.mem_nhds ht0U)
    -- the moment is at least `(C - η)^{2k} * μ U`
    have hmom_lower : ∀ k : ℕ, (C - η) ^ (2 * k) * (μ U).toReal ≤ ∫ t : ℝ, t ^ (2 * k) ∂μ := by
      intro k
      have hind : Integrable
          (fun t : ℝ => (C - η) ^ (2 * k) * U.indicator (fun _ => (1 : ℝ)) t) μ := by
        have hEq : (fun t : ℝ => (C - η) ^ (2 * k) * U.indicator (fun _ => (1 : ℝ)) t)
            = U.indicator (fun _ => (C - η) ^ (2 * k)) := by
          funext t
          by_cases ht : t ∈ U <;> simp [ht]
        rw [hEq, integrable_indicator_iff hUm]
        exact (integrable_const ((C - η) ^ (2 * k))).integrableOn
      have hle : ∀ᵐ t ∂μ,
          (C - η) ^ (2 * k) * U.indicator (fun _ => (1 : ℝ)) t ≤ t ^ (2 * k) := by
        filter_upwards with t
        by_cases ht : t ∈ U
        · rw [Set.indicator_of_mem ht, mul_one]
          have hgt : C - η < |t| := ht
          rw [sq_pow_eq_abs_pow (C - η) k, sq_pow_eq_abs_pow t k, abs_of_pos hCη]
          exact pow_le_pow_left₀ hCη.le hgt.le (2 * k)
        · rw [Set.indicator_of_notMem ht, mul_zero]
          exact sq_pow_nonneg t k
      calc (C - η) ^ (2 * k) * (μ U).toReal
          = ∫ t : ℝ, (C - η) ^ (2 * k) * U.indicator (fun _ => (1 : ℝ)) t ∂μ := by
            rw [integral_const_mul, integral_indicator hUm, setIntegral_const, smul_eq_mul, mul_one]
            rfl
        _ ≤ ∫ t : ℝ, t ^ (2 * k) ∂μ := integral_mono_ae hind (hint k) hle
    -- the multiplicative factor `(μ U)^{1/(2k)}` tends to one
    have hT : Tendsto (fun k : ℕ => ((μ U).toReal) ^ ((1 : ℝ) / ((2 * k : ℕ) : ℝ))) atTop (𝓝 1) := by
      have hexp : Tendsto (fun k : ℕ => ((1 : ℝ) / ((2 * k : ℕ) : ℝ))) atTop (𝓝 0) := by
        have h2 : Tendsto (fun k : ℕ => ((2 * k : ℕ) : ℝ)) atTop atTop := by
          simpa [Nat.cast_mul, mul_comm] using
            (tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num : (0 : ℝ) < 2))
        have hinv : Tendsto (fun k : ℕ => (((2 * k : ℕ) : ℝ))⁻¹) atTop (𝓝 0) :=
          h2.inv_tendsto_atTop
        simpa [one_div] using hinv
      have hpos : 0 < (μ U).toReal :=
        ENNReal.toReal_pos (ne_of_gt hUpos) (measure_ne_top μ U)
      have hlog : Tendsto (fun k : ℕ =>
          ((1 : ℝ) / ((2 * k : ℕ) : ℝ)) * Real.log ((μ U).toReal)) atTop (𝓝 0) := by
        simpa using hexp.mul_const (Real.log ((μ U).toReal))
      have hexp2 : Tendsto (fun k : ℕ => Real.exp
          (((1 : ℝ) / ((2 * k : ℕ) : ℝ)) * Real.log ((μ U).toReal))) atTop (𝓝 1) := by
        simpa [Function.comp_def] using Real.continuous_exp.continuousAt.tendsto.comp hlog
      simpa [Real.rpow_def_of_pos hpos, mul_comm] using hexp2
    have hlt : 1 - η / C < 1 := by
      have hCpos : 0 < C := by linarith
      have hquot : 0 < η / C := div_pos hηpos hCpos
      linarith
    have hev : ∀ᶠ k : ℕ in atTop, 1 - η / C ≤ ((μ U).toReal) ^ ((1 : ℝ) / ((2 * k : ℕ) : ℝ)) := by
      filter_upwards [hT.eventually (isOpen_Ioi.mem_nhds hlt)] with k hk
      exact le_of_lt hk
    filter_upwards [hev, Filter.eventually_ge_atTop 1] with k hk hk1
    have hbase : 0 ≤ C - η := hCη.le
    have hstep : (C - η) ^ (2 * k) * (μ U).toReal ≤ ∫ t : ℝ, t ^ (2 * k) ∂μ := hmom_lower k
    have hroot : ((C - η) ^ (2 * k) * (μ U).toReal) ^ ((1 : ℝ) / ((2 * k : ℕ) : ℝ))
        = (C - η) * ((μ U).toReal) ^ ((1 : ℝ) / ((2 * k : ℕ) : ℝ)) := by
      rw [Real.mul_rpow (sq_pow_nonneg (C - η) k) ENNReal.toReal_nonneg]
      congr 1
      rw [← Real.rpow_natCast_mul hbase (2 * k) ((1 : ℝ) / ((2 * k : ℕ) : ℝ))]
      have h1 : ((2 * k : ℕ) : ℝ) * ((1 : ℝ) / ((2 * k : ℕ) : ℝ)) = 1 := by
        rw [mul_one_div]
        exact div_self (by positivity)
      rw [h1, Real.rpow_one]
    calc C - ε = C - 2 * η := by rw [hη]; ring
      _ ≤ (C - η) * (1 - η / C) := by
          have hCpos : 0 < C := by linarith
          field_simp
          nlinarith [sq_nonneg η]
      _ ≤ (C - η) * ((μ U).toReal) ^ ((1 : ℝ) / ((2 * k : ℕ) : ℝ)) :=
          mul_le_mul_of_nonneg_left hk hbase
      _ = ((C - η) ^ (2 * k) * (μ U).toReal) ^ ((1 : ℝ) / ((2 * k : ℕ) : ℝ)) := hroot.symm
      _ ≤ (∫ t : ℝ, t ^ (2 * k) ∂μ) ^ ((1 : ℝ) / ((2 * k : ℕ) : ℝ)) :=
          Real.rpow_le_rpow (mul_nonneg (sq_pow_nonneg _ _) ENNReal.toReal_nonneg) hstep
            (by positivity)
  refine tendsto_order.2 ⟨?_, ?_⟩
  · intro b hb
    set b' : ℝ := (b + C) / 2 with hbdef
    have hbb' : b < b' := by rw [hbdef]; linarith
    have hb'C : b' < C := by rw [hbdef]; linarith
    have hε : 0 < C - b' := by linarith
    filter_upwards [hlower (C - b') hε] with k hk
    have hEq : C - (C - b') = b' := by ring
    rw [hEq] at hk
    exact lt_of_lt_of_le hbb' hk
  · intro b hb
    filter_upwards [hupper] with k hk
    exact lt_of_le_of_lt hk hb

end GUEStrongConvergence
