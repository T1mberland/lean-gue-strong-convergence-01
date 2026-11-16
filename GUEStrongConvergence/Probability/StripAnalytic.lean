/-
# The analytic core of the weighted strip bound

`WeightedStripBound A₀ A k η₀ C_s β` (see `Probability/LemmaMWeighted.lean`) asks for

`frob (g_N(z) − g(z)) ≤ C_s |Im z|^(−β) / N²`  for `0 < |Im z| < η₀`,

where `g_N` is the Gaussian mean of the normalized partial trace of the resolvent of the
Hermitian pencil `A₀ ⊗ 1 + ∑ Aᵢ ⊗ Gᵢ` and `g` is the limit operator-valued Cauchy transform.

This file records the part of that estimate which is a *theorem* with the current machinery, and
isolates the residual obligation.

## Main results

* `coeffMass` — `S = ∑ᵢ ‖Aᵢ‖_F²`, the coefficient mass of the pencil;
* `stripThreshold` — the fixed threshold `η_A = max 1 √(2 d² S)` of the sharp comparison;
* `frob_gueResolventMean_sub_limit_le_trivial` — the deterministic both-half-plane bound
  `frob(g_N − g) ≤ 2 d |Im z|⁻¹`, valid for every nonreal `z`;
* `weightedStripBound_of_uniform` — a uniform (β = 0) strip estimate `C/N²` implies the weighted
  strip estimate: the content of `WeightedStripBound` is the uniform `N⁻²` comparison near the
  real axis, the `|Im z|^(−β)` slack only weakens it;
* `frob_gueResolventMean_sub_limit_le_rpow_top` — **the weighted strip bound is a theorem above
  the threshold**: for `η_A ≤ Im z < η₀` and every `β ≥ 0`,
  `frob(g_N − g) ≤ (8 d⁴ √d S² · max 1 (η₀^(β−5))) (Im z)^(−β) / N²`;
* `weightedStripBound_of_nearAxis` — reduction of `WeightedStripBound` to the near-axis annulus
  `0 < |Im z| < η_A` alone;
* `integral_trace_coeff_mul_gue_mul_coeff_mul_gue` — the exact mixed second moment
  `E tr(A X B X) = N⁻¹ tr A tr B`, i.e. `E τ_N(A X B X) = τ_N(A) τ_N(B)`: no `1/N` term.
-/
import GUEStrongConvergence.Probability.DysonLimitSharp
import GUEStrongConvergence.Probability.LemmaMWeighted
import GUEStrongConvergence.Probability.LemmaMMeanBound

open MeasureTheory ProbabilityTheory Matrix Filter
open FreeProbability FreeProbability.Fock
open scoped Matrix.Norms.Frobenius ComplexOrder ENNReal NNReal Topology BigOperators

namespace GUEStrongConvergence

noncomputable section

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

variable {ι d : Type*} [Fintype ι] [DecidableEq ι] [Fintype d] [DecidableEq d] [Nonempty d]
  {N : ℕ}

/-! ### The coefficient mass and the threshold -/

/-- The coefficient mass `S = ∑ᵢ ‖Aᵢ‖_F²` of a pencil. -/
def coeffMass (A : ι → Matrix d d ℂ) : ℝ := ∑ i, (frob (A i)) ^ 2

lemma coeffMass_nonneg (A : ι → Matrix d d ℂ) : 0 ≤ coeffMass A :=
  Finset.sum_nonneg fun i _ => sq_nonneg _

/-- The fixed threshold of the sharp comparison: `η_A = max 1 √(2 d² S)`. Above it the sharp
`O(N⁻² |Im z|⁻⁵)` averaged-resolvent comparison holds (see
`frob_gueResolventMean_sub_limit_le_rpow_top`). -/
def stripThreshold (A : ι → Matrix d d ℂ) : ℝ :=
  max 1 (Real.sqrt (2 * (Fintype.card d : ℝ) ^ 2 * coeffMass A))

lemma one_le_stripThreshold (A : ι → Matrix d d ℂ) : 1 ≤ stripThreshold A :=
  le_max_left _ _

lemma stripThreshold_pos (A : ι → Matrix d d ℂ) : 0 < stripThreshold A :=
  lt_of_lt_of_le one_pos (one_le_stripThreshold A)

lemma card_pos_real : (0 : ℝ) < (Fintype.card d : ℝ) := by
  exact_mod_cast Fintype.card_pos

/-- The sharp comparison's hypothesis holds above `stripThreshold`. -/
lemma sharp_threshold_le_stripThreshold (A : ι → Matrix d d ℂ) :
    2 * (Fintype.card d : ℝ) ^ 2 * coeffMass A ≤ (stripThreshold A) ^ 2 := by
  set c : ℝ := (Fintype.card d : ℝ) with hc
  have hc0 : 0 ≤ c := le_of_lt card_pos_real
  have hS := coeffMass_nonneg A
  have harg : 0 ≤ 2 * c ^ 2 * coeffMass A := by positivity
  have ht_le : Real.sqrt (2 * c ^ 2 * coeffMass A) ≤ stripThreshold A := le_max_right _ _
  have ht0 : 0 ≤ Real.sqrt (2 * c ^ 2 * coeffMass A) := Real.sqrt_nonneg _
  calc 2 * c ^ 2 * coeffMass A = (Real.sqrt (2 * c ^ 2 * coeffMass A)) ^ 2 :=
        (Real.sq_sqrt harg).symm
    _ ≤ (stripThreshold A) ^ 2 := by
        have h := pow_le_pow_left₀ ht0 ht_le 2
        simpa [hc] using h

/-! ### The trivial deterministic bound -/

/-- Deterministic bound for the averaged-resolvent deviation, valid in **both** half-planes:
`frob (g_N − g) ≤ 2 d |Im z|⁻¹`. This is the only information available on the near-axis strip
`0 < |Im z| < stripThreshold A`. -/
theorem frob_gueResolventMean_sub_limit_le_trivial (A₀ : Matrix d d ℂ)
    (A : ι → Matrix d d ℂ) (hA₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian)
    {z : ℂ} (hz : z.im ≠ 0) (hN : 0 < N) :
    frob (gueResolventMean (N := N) A₀ A z - operatorMatrixPencilCauchy A₀ A z)
      ≤ 2 * (Fintype.card d : ℝ) * |z.im|⁻¹ := by
  have h1 := frob_gueResolventMean_le_abs A₀ A hA₀ hA z hz hN
  have h2 := frob_operatorMatrixPencilCauchy_le A₀ A hA₀ hA z hz
  have htr := frob_sub_le (gueResolventMean (N := N) A₀ A z)
    (operatorMatrixPencilCauchy A₀ A z)
  linarith

/-! ### A uniform `N⁻²` strip estimate implies the weighted one -/

/-- **`WeightedStripBound` is weaker than a uniform `O(N⁻²)` strip estimate.**  If on the strip
`|Im z| < η₀` the deviation is `O(N⁻²)` *uniformly in z*, then the weighted bound with any
`β ≥ 0` follows (with constant `C · max 1 η₀^β`).  Thus the weighted power `|Im z|^(−β)` is not
the difficulty: the difficulty is the uniform `N⁻²` coefficient near `Im z = 0`. -/
theorem weightedStripBound_of_uniform (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ) (k : ℕ)
    {η₀ C β : ℝ} (hη₀ : 0 < η₀) (hη₀1 : 1 ≤ η₀) (hC : 0 ≤ C) (hβ : 0 ≤ β)
    (h : ∀ᶠ N : ℕ in atTop, ∀ z : ℂ, z.im ≠ 0 → |z.im| < η₀ →
      frob (gueResolventMean (N := N) A₀ A z - operatorMatrixPencilCauchy A₀ A z)
        ≤ C / (N : ℝ) ^ 2) :
    WeightedStripBound A₀ A k η₀ (C * max 1 (η₀ ^ β)) β := by
  filter_upwards [h, eventually_gt_atTop (0 : ℕ)] with N hN hNpos
  intro z hz hstrip
  have hNz : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hNpos
  have hzpos : 0 < |z.im| := abs_pos.mpr hz
  -- the weight factor dominates `1`
  have hkey : 1 ≤ max 1 (η₀ ^ β) * |z.im| ^ (-β) := by
    have hmax1 : (1 : ℝ) ≤ max 1 (η₀ ^ β) := le_max_left _ _
    by_cases hle : |z.im| ≤ 1
    · have hinv1 : (1 : ℝ) ≤ |z.im|⁻¹ := by
        rw [← one_div]; exact one_le_one_div hzpos hle
      have h : (1 : ℝ) ≤ |z.im|⁻¹ ^ β := Real.one_le_rpow hinv1 hβ
      have hrew : |z.im| ^ (-β) = |z.im|⁻¹ ^ β := Real.rpow_neg_eq_inv_rpow _ _
      rw [hrew]
      calc (1 : ℝ) ≤ |z.im|⁻¹ ^ β := h
        _ ≤ max 1 (η₀ ^ β) * |z.im|⁻¹ ^ β := by
            have h2 : 0 ≤ |z.im|⁻¹ ^ β := Real.rpow_nonneg (by positivity) _
            exact le_mul_of_one_le_left h2 hmax1
    · have hgt : 1 < |z.im| := not_le.mp hle
      have hinv_le : η₀⁻¹ ≤ |z.im|⁻¹ := by
        rw [← one_div, ← one_div]
        exact one_div_le_one_div_of_le hzpos (le_of_lt hstrip)
      have hstep : η₀ ^ (-β) ≤ |z.im| ^ (-β) := by
        rw [Real.rpow_neg_eq_inv_rpow η₀ β, Real.rpow_neg_eq_inv_rpow |z.im| β]
        exact Real.rpow_le_rpow (by positivity) hinv_le hβ
      have hprod : η₀ ^ β * η₀ ^ (-β) = 1 := by
        rw [← Real.rpow_add hη₀, add_neg_cancel, Real.rpow_zero]
      have hcomm : max 1 (η₀ ^ β) * η₀ ^ (-β) = 1 := by
        rw [max_eq_right (Real.one_le_rpow hη₀1 hβ)]
        exact hprod
      calc (1 : ℝ) = max 1 (η₀ ^ β) * η₀ ^ (-β) := hcomm.symm
        _ ≤ max 1 (η₀ ^ β) * |z.im| ^ (-β) :=
            mul_le_mul_of_nonneg_left hstep (le_trans zero_le_one (le_max_left _ _))
  have hb := hN z hz hstrip
  have hmono : C / (N : ℝ) ^ 2 ≤ (C * max 1 (η₀ ^ β)) * |z.im| ^ (-β) / (N : ℝ) ^ 2 := by
    have hsq : (0 : ℝ) < (N : ℝ) ^ 2 := by positivity
    have hCN : C ≤ (C * max 1 (η₀ ^ β)) * |z.im| ^ (-β) := by
      have hrew : (C * max 1 (η₀ ^ β)) * |z.im| ^ (-β)
          = C * (max 1 (η₀ ^ β) * |z.im| ^ (-β)) := by ring
      rw [hrew]
      exact le_mul_of_one_le_right hC hkey
    calc C / (N : ℝ) ^ 2 = C * ((N : ℝ) ^ 2)⁻¹ := by rw [div_eq_mul_inv]
      _ ≤ ((C * max 1 (η₀ ^ β)) * |z.im| ^ (-β)) * ((N : ℝ) ^ 2)⁻¹ := by
          exact mul_le_mul_of_nonneg_right hCN (by positivity)
      _ = (C * max 1 (η₀ ^ β)) * |z.im| ^ (-β) / (N : ℝ) ^ 2 := by rw [div_eq_mul_inv]
  exact hb.trans hmono


/-! ### Above the threshold: the weighted strip bound is a theorem -/

/-- The explicit constant `8 d⁴ √d S²` of the sharp `N⁻²` comparison. -/
def sharpConstant (A : ι → Matrix d d ℂ) : ℝ :=
  8 * (Fintype.card d : ℝ) ^ 4 * Real.sqrt (Fintype.card d : ℝ) * (coeffMass A) ^ 2

lemma sharpConstant_nonneg (A : ι → Matrix d d ℂ) : 0 ≤ sharpConstant A := by
  unfold sharpConstant
  positivity

/-- **The weighted strip bound holds above the threshold.**  If `η_A ≤ Im z < η₀` (with
`η_A = stripThreshold A`), then for every `β ≥ 0`

`frob (g_N − g) ≤ (8 d⁴ √d S² · max 1 (η₀^(β−5))) (Im z)^(−β) / N²`.

The `|Im z|^(−5)` weight of the sharp comparison is absorbed into the requested `|Im z|^(−β)`
weight: above `stripThreshold A ≥ 1` the extra factor `(Im z)^(β−5)` is bounded by `1` for
`β ≤ 5` and by `η₀^(β−5)` for `β ≥ 5`. -/
theorem frob_gueResolventMean_sub_limit_le_rpow_top (A₀ : Matrix d d ℂ)
    (A : ι → Matrix d d ℂ) (hA₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian)
    {η₀ β : ℝ} (hβ : 0 ≤ β) (hη₀ : stripThreshold A ≤ η₀)
    {z : ℂ} (hz : 0 < z.im) (hN : 0 < N)
    (hlow : stripThreshold A ≤ z.im) (htop : z.im < η₀) :
    frob (gueResolventMean (N := N) A₀ A z - operatorMatrixPencilCauchy A₀ A z)
      ≤ sharpConstant A * max 1 (η₀ ^ (β - 5)) * (z.im) ^ (-β) / (N : ℝ) ^ 2 := by
  have hS := coeffMass_nonneg A
  have hη : 2 * (Fintype.card d : ℝ) ^ 2 * coeffMass A ≤ (z.im) ^ 2 := by
    have h1 := sharp_threshold_le_stripThreshold A
    have h2 : (stripThreshold A) ^ 2 ≤ (z.im) ^ 2 :=
      pow_le_pow_left₀ (le_of_lt (stripThreshold_pos A)) hlow 2
    linarith
  have hsharp := frob_gueResolventMean_sub_limit_le_sharp A₀ A hA₀ hA z hz hN hη
  -- collapse the sharp constant to `sharpConstant A * (Im z)⁻⁵ / N²`
  have hK :
      2 * (Fintype.card d : ℝ) * (z.im)⁻¹ *
        ((Fintype.card d : ℝ) *
          (2 * (Fintype.card d : ℝ) ^ 2 * Real.sqrt (Fintype.card d : ℝ) *
            (∑ i, (frob (A i)) ^ 2) *
            (2 * (gueScale N) ^ 2 * (∑ i, (frob (A i)) ^ 2) * ((z.im)⁻¹) ^ 4 / (N : ℝ))))
        = sharpConstant A * ((z.im) ^ 5)⁻¹ / (N : ℝ) ^ 2 := by
    rw [gueScale_sq N]
    simp only [sharpConstant, coeffMass]
    have hNne : (N : ℝ) ≠ 0 := by positivity
    have hzne : z.im ≠ 0 := ne_of_gt hz
    field_simp
    ring
  have hstep1 : frob (gueResolventMean (N := N) A₀ A z - operatorMatrixPencilCauchy A₀ A z)
      ≤ sharpConstant A * ((z.im) ^ 5)⁻¹ / (N : ℝ) ^ 2 := hsharp.trans (le_of_eq hK)
  -- absorb the extra power into the requested weight
  have hw : ((z.im) ^ 5)⁻¹ ≤ max 1 (η₀ ^ (β - 5)) * (z.im) ^ (-β) := by
    have h5 : ((z.im) ^ 5)⁻¹ = (z.im) ^ (-β) * (z.im) ^ (β - 5) := by
      calc ((z.im) ^ 5)⁻¹ = (z.im) ^ (-5 : ℝ) := by
            have h := Real.rpow_neg (le_of_lt hz) (5 : ℝ)
            have h5 : ((z.im) ^ (5 : ℕ)) = (z.im) ^ ((5 : ℝ)) :=
              (Real.rpow_natCast (z.im) 5).symm
            rw [h5, show (-5 : ℝ) = -(5 : ℝ) by norm_num]
            exact h.symm
        _ = (z.im) ^ (-β + (β - 5)) := by
              rw [show -β + (β - 5) = (-5 : ℝ) by ring]
        _ = (z.im) ^ (-β) * (z.im) ^ (β - 5) := Real.rpow_add hz _ _
    rw [h5]
    have hpow : (z.im) ^ (β - 5) ≤ max 1 (η₀ ^ (β - 5)) := by
      by_cases hβ5 : 5 ≤ β
      · have h1 : (z.im) ^ (β - 5) ≤ η₀ ^ (β - 5) :=
          Real.rpow_le_rpow (le_of_lt hz) (le_of_lt htop) (by linarith)
        exact h1.trans (le_max_right _ _)
      · have hβ5' : β - 5 ≤ 0 := by linarith [not_le.mp hβ5]
        have h1 : (z.im) ^ (β - 5) ≤ (stripThreshold A) ^ (β - 5) :=
          Real.rpow_le_rpow_of_nonpos (stripThreshold_pos A) hlow hβ5'
        have h2 : (stripThreshold A) ^ (β - 5) ≤ 1 := by
          have h3 := Real.rpow_le_rpow_of_nonpos zero_lt_one (one_le_stripThreshold A) hβ5'
          simpa using h3
        exact (h1.trans h2).trans (le_max_left _ _)
    have hnn : 0 ≤ (z.im) ^ (-β) := Real.rpow_nonneg (le_of_lt hz) _
    nlinarith [hpow, hnn]
  refine hstep1.trans ?_
  have hNz : (0 : ℝ) < (N : ℝ) ^ 2 := by positivity
  calc sharpConstant A * ((z.im) ^ 5)⁻¹ / (N : ℝ) ^ 2
      ≤ sharpConstant A * (max 1 (η₀ ^ (β - 5)) * (z.im) ^ (-β)) / (N : ℝ) ^ 2 := by
        refine div_le_div_of_nonneg_right ?_ (le_of_lt hNz)
        exact mul_le_mul_of_nonneg_left hw (sharpConstant_nonneg A)
    _ = sharpConstant A * max 1 (η₀ ^ (β - 5)) * (z.im) ^ (-β) / (N : ℝ) ^ 2 := by ring


/-- **The top part in eventual form** (upper half-plane): for every `β ≥ 0`, above the threshold
`stripThreshold A` the weighted strip estimate holds with the sharp constant. -/
theorem eventually_weightedStripBound_top (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    (hA₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian) {η₀ β : ℝ} (hβ : 0 ≤ β)
    (hη₀ : stripThreshold A < η₀) :
    ∀ᶠ N : ℕ in atTop, ∀ z : ℂ, 0 < z.im → stripThreshold A ≤ z.im → z.im < η₀ →
      frob (gueResolventMean (N := N) A₀ A z - operatorMatrixPencilCauchy A₀ A z)
        ≤ (sharpConstant A * max 1 (η₀ ^ (β - 5))) * (z.im) ^ (-β) / (N : ℝ) ^ 2 := by
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN z hz hlow htop
  exact frob_gueResolventMean_sub_limit_le_rpow_top A₀ A hA₀ hA hβ (le_of_lt hη₀) hz hN hlow htop

/-- **Reduction of `WeightedStripBound` to the near-axis annulus.**

`WeightedStripBound` for the full strip `|Im z| < η₀` follows from
(i) the same weighted estimate on the *near-axis annulus* `0 < |Im z| < stripThreshold A` and
(ii) the same weighted estimate on the *outer* part `stripThreshold A ≤ |Im z| < η₀`.
Part (ii) is a theorem on the upper half-plane (`eventually_weightedStripBound_top`); hence all
remaining analytic content of `WeightedStripBound` sits in the annulus (i). -/
theorem weightedStripBound_of_nearAxis (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ) (k : ℕ)
    {η₀ C_s C_t β : ℝ}
    (hnear : ∀ᶠ N : ℕ in atTop, ∀ z : ℂ, z.im ≠ 0 → |z.im| < stripThreshold A →
      frob (gueResolventMean (N := N) A₀ A z - operatorMatrixPencilCauchy A₀ A z)
        ≤ C_s * |z.im| ^ (-β) / (N : ℝ) ^ 2)
    (htop : ∀ᶠ N : ℕ in atTop, ∀ z : ℂ, z.im ≠ 0 → stripThreshold A ≤ |z.im| → |z.im| < η₀ →
      frob (gueResolventMean (N := N) A₀ A z - operatorMatrixPencilCauchy A₀ A z)
        ≤ C_t * |z.im| ^ (-β) / (N : ℝ) ^ 2) :
    WeightedStripBound A₀ A k η₀ (max C_s C_t) β := by
  filter_upwards [hnear, htop] with N hn ht
  intro z hz hstrip
  have hw : 0 ≤ |z.im| ^ (-β) := Real.rpow_nonneg (abs_nonneg _) _
  rcases lt_or_ge |z.im| (stripThreshold A) with h | h
  · refine (hn z hz h).trans ?_
    gcongr
    exact le_max_left _ _
  · refine (ht z hz h hstrip).trans ?_
    gcongr
    exact le_max_right _ _

/-- **The upper half-plane strip bound from the near-axis annulus.**

Combining the reduction with the sharp comparison above the threshold: if the weighted estimate
holds on the near-axis annulus `0 < Im z < stripThreshold A` of the upper half-plane, then it
holds on the whole upper half-plane strip `0 < Im z < η₀`. This is the exact form in which the
missing analytic input is consumed: everything above `stripThreshold A` is already a theorem. -/
theorem eventually_upperHalfStrip_of_nearAxis (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    (hA₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian) {η₀ β C_s : ℝ}
    (hβ : 0 ≤ β) (hη₀ : stripThreshold A < η₀)
    (hnear : ∀ᶠ N : ℕ in atTop, ∀ z : ℂ, 0 < z.im → z.im < stripThreshold A →
      frob (gueResolventMean (N := N) A₀ A z - operatorMatrixPencilCauchy A₀ A z)
        ≤ C_s * (z.im) ^ (-β) / (N : ℝ) ^ 2) :
    ∀ᶠ N : ℕ in atTop, ∀ z : ℂ, 0 < z.im → z.im < η₀ →
      frob (gueResolventMean (N := N) A₀ A z - operatorMatrixPencilCauchy A₀ A z)
        ≤ max C_s (sharpConstant A * max 1 (η₀ ^ (β - 5))) * (z.im) ^ (-β) / (N : ℝ) ^ 2 := by
  filter_upwards [hnear, eventually_weightedStripBound_top A₀ A hA₀ hA hβ hη₀] with N hn ht
  intro z hz hstrip
  have hw : 0 ≤ (z.im) ^ (-β) := Real.rpow_nonneg (le_of_lt hz) _
  rcases lt_or_ge z.im (stripThreshold A) with h | h
  · refine (hn z hz h).trans ?_
    gcongr
    exact le_max_left _ _
  · refine (ht z hz h hstrip).trans ?_
    gcongr
    exact le_max_right _ _

/-! ### The exact mixed second moment -/

section MixedMoment

/-- Fubini for a finite four-fold sum of integrable functions (the `d`-fold version of
`integral_finsetSum`). -/
lemma integral_four_fold_sum {κ : Type*} [MeasurableSpace κ] {μ : Measure κ}
    (g : Fin N → Fin N → Fin N → Fin N → κ → ℂ)
    (hg : ∀ a j c e, Integrable (fun x => g a j c e x) μ) :
    ∫ x, ∑ a : Fin N, ∑ j : Fin N, ∑ c : Fin N, ∑ e : Fin N, g a j c e x ∂μ
      = ∑ a : Fin N, ∑ j : Fin N, ∑ c : Fin N, ∑ e : Fin N, ∫ x, g a j c e x ∂μ := by
  rw [integral_finsetSum Finset.univ (fun a _ => integrable_finsetSum Finset.univ (fun j _ =>
    integrable_finsetSum Finset.univ (fun c _ => integrable_finsetSum Finset.univ (fun e _ =>
      hg a j c e))))]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [integral_finsetSum Finset.univ (fun j _ => integrable_finsetSum Finset.univ (fun c _ =>
    integrable_finsetSum Finset.univ (fun e _ => hg a j c e)))]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_finsetSum Finset.univ (fun c _ => integrable_finsetSum Finset.univ (fun e _ =>
    hg a j c e))]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [integral_finsetSum Finset.univ (fun e _ => hg a j c e)]

/-- Integrability of the mixed degree-`4` monomial `A a e · X e c · B c j · X j a`. -/
lemma integrable_coeff_mul_gue_mul_coeff_mul_gue (A B : Matrix (Fin N) (Fin N) ℂ) (i : ι)
    (a j c e : Fin N) :
    Integrable (fun x : EuclideanSpace ℝ (GUECoord ι N) =>
      A a e * gueMatrix x i e c * B c j * gueMatrix x i j a)
      (stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) := by
  have h : Integrable (fun x : EuclideanSpace ℝ (GUECoord ι N) =>
      (A a e * B c j) * (gueMatrix x i e c * gueMatrix x i j a))
      (stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) :=
    (integrable_gueMatrix_mul (N := N) (ι := ι) i i e c j a).const_mul _
  refine h.congr (Eventually.of_forall fun x => ?_)
  ring

/-- **Exact mixed second moment.**  For fixed coefficient matrices `A B` and one normalized
complex GUE matrix `X = gueMatrix x i`:

`E tr (A X B X) = N⁻¹ tr A · tr B`.

In normalized-trace form this is `E τ_N(A X B X) = τ_N(A) τ_N(B)`: exactly the free value, with
**no** `1/N` correction. Matrix coefficients do not change the face-count exponent. -/
theorem integral_trace_coeff_mul_gue_mul_coeff_mul_gue (A B : Matrix (Fin N) (Fin N) ℂ)
    (i : ι) :
    ∫ x : EuclideanSpace ℝ (GUECoord ι N),
        Matrix.trace (A * gueMatrix x i * B * gueMatrix x i)
      ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))
      = ((N : ℂ)⁻¹) * Matrix.trace A * Matrix.trace B := by
  have hexp : ∀ x : EuclideanSpace ℝ (GUECoord ι N),
      Matrix.trace (A * gueMatrix x i * B * gueMatrix x i)
        = ∑ a : Fin N, ∑ j : Fin N, ∑ c : Fin N, ∑ e : Fin N,
            A a e * gueMatrix x i e c * B c j * gueMatrix x i j a := by
    intro x
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
  simp_rw [hexp]
  rw [integral_four_fold_sum (μ := stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))
    (g := fun a j c e x => A a e * gueMatrix x i e c * B c j * gueMatrix x i j a)
    (fun a j c e => integrable_coeff_mul_gue_mul_coeff_mul_gue A B i a j c e)]
  have hinner : ∀ a j c e : Fin N,
      (∫ x : EuclideanSpace ℝ (GUECoord ι N),
          A a e * gueMatrix x i e c * B c j * gueMatrix x i j a
        ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N))))
        = A a e * B c j * (if e = a ∧ c = j then ((N : ℂ)⁻¹) else 0) := by
    intro a j c e
    have h1 : (∫ x : EuclideanSpace ℝ (GUECoord ι N),
          A a e * gueMatrix x i e c * B c j * gueMatrix x i j a
        ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N))))
        = ∫ x : EuclideanSpace ℝ (GUECoord ι N),
            (A a e * B c j) * (gueMatrix x i e c * gueMatrix x i j a)
          ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) :=
      integral_congr_ae (Eventually.of_forall fun x => by ring)
    rw [h1, integral_const_mul, integral_gueMatrix_mul]
    simp
  simp only [hinner]
  have hcollapse : ∀ a j : Fin N,
      (∑ c : Fin N, ∑ e : Fin N,
          A a e * B c j * (if e = a ∧ c = j then ((N : ℂ)⁻¹) else 0))
        = A a a * B j j * ((N : ℂ)⁻¹) := by
    intro a j
    rw [Finset.sum_eq_single j]
    · rw [Finset.sum_eq_single a]
      · simp
      · intro e _ hne; simp [hne]
      · intro h; simp at h
    · intro c _ hne; simp [hne]
    · intro h; simp at h
  simp only [hcollapse]
  simp only [Matrix.trace, Matrix.diag]
  have h2 : (N : ℂ)⁻¹ * (∑ a : Fin N, A a a) * (∑ j : Fin N, B j j)
      = ((∑ a : Fin N, A a a) * (∑ j : Fin N, B j j)) * ((N : ℂ)⁻¹) := by ring
  rw [h2, Finset.sum_mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_mul]

/-- Normalized-trace form of the exact mixed second moment:
`E τ_N(A X B X) = τ_N(A) τ_N(B)`, where `τ_N(M) = N⁻¹ tr M`. No `1/N` correction. -/
theorem integral_gueNormTrace_mixed (A B : Matrix (Fin N) (Fin N) ℂ) (i : ι) :
    ∫ x : EuclideanSpace ℝ (GUECoord ι N),
        (N : ℂ)⁻¹ * Matrix.trace (A * gueMatrix x i * B * gueMatrix x i)
      ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))
      = ((N : ℂ)⁻¹ * Matrix.trace A) * ((N : ℂ)⁻¹ * Matrix.trace B) := by
  rw [integral_const_mul, integral_trace_coeff_mul_gue_mul_coeff_mul_gue]
  ring

end MixedMoment

end

end GUEStrongConvergence
