/-
# Status of the moment side, and the exact weighted-strip obligation

This module records, as kernel-checked Lean, the two facts about the probability/moment side
that the final reduction depends on, together with the precise shape of what is *not* proved.

## 1. The trace-word moments are unconditional

The whole moment side is finished: there is a **single** almost-sure event on which **every**
fixed word `w : List ι` has a convergent normalized trace, and the limit is the project's
non-crossing label sum `wordLimit w` (`ae_all_traceWord_moments_converge`), resp. the free
expectation `tau r w` (`ae_all_traceWord_moments_converge_tau`).  Both are restatements of
`ae_all_words_gueNormTrace_genusSum_unconditional` (`GUEBlockSplitFinal.lean`, where the
block-diagonal factorization is no longer a hypothesis) and of
`ae_all_words_gueNormTrace_tau_unconditional` (`FreeMomentBridgeProof.lean`, the free-moment
bridge).  The countable intersection over words is `MeasureTheory.ae_all_iff`, applied there.

## 2. What remains: the weighted strip bound

`GUEStrongConvergenceStatement_of_weightedStripInputsFinal` (see
`docs/handoffs/STATUS_MOMENTS.md`) is gated by `WeightedStripBound`
(`LemmaMWeighted.lean`), a *pointwise* statement about the averaged resolvent:

  `frob (g_N(z) - g(z)) ≤ C_s * |Im z| ^ (-β) / N²` for **all** `z` with `0 < |Im z| < η₀`,

with `0 ≤ β < k` (`k = max k 1 ≥ 1`, so `β < 1` in the `k = 0` / scalar cases).

The results below split this statement into regions:

* `weightedStripBound_iff_in`: the strip bound is equivalent to holding on the near-real region
  `|Im z| < c` and on the away region `c ≤ |Im z| < η₀`;
* `frob_gueResolventMean_sub_limit_le_of_ge`: **the away region with `Im z > 0` is already a
  theorem**, with the explicit constant `8 d⁴ √d (∑ frob (A i)²)² c⁻⁵ / N²` and exponent
  `β = 0`, derived from the sharp averaged-resolvent comparison
  `frob_gueResolventMean_sub_limit_le_sharp`.  Note the extra hypothesis
  `2 d² ∑ frob (A i)² ≤ (Im z)²` of the sharp theorem: it *forces* `|Im z| ≥ c` with
  `c = sqrt (2 d² ∑ frob (A i)²)`, which is exactly the boundary used here.
* `weightedStripBound_of_obligation`: consequently the full strip bound follows from the
  *near-real* region `|Im z| < c`, together with the negative-imaginary part of the away
  region (which is not in this repository; it should follow from the adjoint symmetry
  `g(z)^* = g(conj z)` of the partial trace of the resolvent, combined with the corresponding
  symmetry of `operatorMatrixPencilCauchy`).

So `WeightedStripObligation` below is the exact remaining analytic input.
No `sorry`/axiom is used.
-/
import GUEStrongConvergence.Probability.GUEBlockSplitFinal
import GUEStrongConvergence.StrongConvergence.FreeMomentBridgeProof
import GUEStrongConvergence.Probability.DysonLimitSharp
import GUEStrongConvergence.Probability.LemmaMWeighted

noncomputable section
namespace GUEStrongConvergence

open Filter MeasureTheory FreeProbability FreeProbability.Fock
open scoped Topology

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-! ### 1. The unconditional moment side -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **All trace-word moments converge simultaneously, unconditionally.**

There is a single almost-sure event on which every fixed word `w : List ι` has
`gueNormTrace w (x N) → wordLimit w`.  This is the unconditional all-words theorem of
`GUEBlockSplitFinal` (the block-diagonal factorization is a theorem there). -/
theorem ae_all_traceWord_moments_converge :
    ∀ᵐ x ∂(commonGaussianMeasure ι), ∀ w : List ι,
      Tendsto (fun N : ℕ => gueNormTrace w (x N)) atTop (𝓝 (wordLimit w)) :=
  ae_all_words_gueNormTrace_genusSum_unconditional

/-- **All trace-word moments converge to the free expectation `tau`, unconditionally**, in
the exact shape (`hWords`) consumed by the final assembly of `FinalStatement.lean`. -/
theorem ae_all_traceWord_moments_converge_tau (r : ℕ) :
    ∀ᵐ x ∂(commonGaussianMeasure (Fin r)), ∀ w : List (Fin r),
      Tendsto (fun N : ℕ => gueNormTrace (N := N) w (x N)) atTop (𝓝 (tau r w)) :=
  ae_all_words_gueNormTrace_tau_unconditional r

/-! ### 2. The weighted strip bound, region by region -/

variable {d : Type*} [Fintype d] [DecidableEq d] [Nonempty d]

/-- The weighted strip bound restricted to the imaginary-part annulus `ηlo ≤ |Im z| < ηhi`. -/
def WeightedStripBoundIn (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ) (k : ℕ)
    (ηlo ηhi C_s β : ℝ) : Prop :=
  ∀ᶠ N : ℕ in atTop, ∀ z : ℂ, z.im ≠ 0 → ηlo ≤ |z.im| → |z.im| < ηhi →
    frob (gueResolventMean (N := N) A₀ A z - operatorMatrixPencilCauchy A₀ A z)
      ≤ C_s * |z.im| ^ (-β) / (N : ℝ) ^ 2

/-- **The full strip bound splits into the near-real region and the away region.**  This is
pure logic: both regions use the same constants, so no strength is lost or gained. -/
theorem weightedStripBound_iff_in {A₀ : Matrix d d ℂ} {A : ι → Matrix d d ℂ} {k : ℕ}
    {η₀ C_s β c : ℝ} (hcη : c ≤ η₀) :
    WeightedStripBound A₀ A k η₀ C_s β ↔
      WeightedStripBoundIn A₀ A k 0 c C_s β ∧ WeightedStripBoundIn A₀ A k c η₀ C_s β := by
  simp only [WeightedStripBound, WeightedStripBoundIn]
  constructor
  · rintro h
    constructor
    · filter_upwards [h] with N hN z hz _ h2
      exact hN z hz (lt_of_lt_of_le h2 hcη)
    · filter_upwards [h] with N hN z hz _ h2
      exact hN z hz h2
  · rintro ⟨h1, h2⟩
    filter_upwards [h1, h2] with N hN1 hN2 z hz hη
    by_cases hlt : |z.im| < c
    · exact hN1 z hz (abs_nonneg _) hlt
    · exact hN2 z hz (le_of_not_gt hlt) hη

/-- **The away region (`Im z > 0`) of the weighted strip bound is a theorem**, with exponent
`β = 0` and the explicit constant `8 d⁴ √d (∑ frob (A i)²)² c⁻⁵`.

It is the sharp averaged-resolvent comparison `frob_gueResolventMean_sub_limit_le_sharp`
(whose conclusion carries `(Im z)⁻⁵ / N²`) evaluated on `Im z ≥ c`, where `c` is at least the
threshold `sqrt (2 d² ∑ frob (A i)²)` forced by its hypothesis. -/
theorem frob_gueResolventMean_sub_limit_le_of_ge
    {A₀ : Matrix d d ℂ} {A : ι → Matrix d d ℂ}
    (hA₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian) {c : ℝ}
    (hc : Real.sqrt (2 * (Fintype.card d : ℝ) ^ 2 * (∑ i, (frob (A i)) ^ 2)) ≤ c)
    (hc0 : 0 < c) :
    ∀ᶠ N : ℕ in atTop, ∀ z : ℂ, 0 < z.im → c ≤ z.im →
      frob (gueResolventMean (N := N) A₀ A z - operatorMatrixPencilCauchy A₀ A z)
        ≤ (8 * (Fintype.card d : ℝ) ^ 4 * Real.sqrt (Fintype.card d : ℝ) *
            (∑ i, (frob (A i)) ^ 2) ^ 2 * c⁻¹ ^ 5) / (N : ℝ) ^ 2 := by
  filter_upwards [eventually_gt_atTop 0] with N hN
  intro z hz hcz
  set S : ℝ := ∑ i, (frob (A i)) ^ 2 with hS
  set D : ℝ := (Fintype.card d : ℝ) with hD
  have hD0 : 0 ≤ D := by positivity
  have hS0 : 0 ≤ S := by positivity
  have hη : 2 * D ^ 2 * S ≤ z.im ^ 2 := by
    have h1 : 2 * D ^ 2 * S ≤ c ^ 2 := by
      calc 2 * D ^ 2 * S = (Real.sqrt (2 * D ^ 2 * S)) ^ 2 := by
            rw [Real.sq_sqrt (by positivity)]
        _ ≤ c ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) hc 2
    have h2 : c ^ 2 ≤ z.im ^ 2 := pow_le_pow_left₀ hc0.le hcz 2
    linarith
  have hsharp := frob_gueResolventMean_sub_limit_le_sharp (N := N) A₀ A hA₀ hA z hz hN hη
  have hgs : (gueScale N) ^ 2 = (N : ℝ)⁻¹ := by
    rw [gueScale, Real.sq_sqrt (by positivity)]
  have hrhs : 2 * D * (z.im)⁻¹ *
      (D * (2 * D ^ 2 * Real.sqrt D * S *
        (2 * (gueScale N) ^ 2 * S * ((z.im)⁻¹) ^ 4 / (N : ℝ))))
      = 8 * D ^ 4 * Real.sqrt D * S ^ 2 * (z.im)⁻¹ ^ 5 / (N : ℝ) ^ 2 := by
    rw [hgs]
    have hN0 : (N : ℝ) ≠ 0 := by positivity
    field_simp
    ring
  rw [hrhs] at hsharp
  have hinv : (z.im)⁻¹ ≤ c⁻¹ := by
    rw [← one_div, ← one_div]
    exact one_div_le_one_div_of_le hc0 hcz
  have hpow : (z.im)⁻¹ ^ 5 ≤ c⁻¹ ^ 5 := pow_le_pow_left₀ (by positivity) hinv 5
  have hcoef : 0 ≤ 8 * D ^ 4 * Real.sqrt D * S ^ 2 := by positivity
  rw [div_eq_mul_inv] at hsharp ⊢
  have hfin : 8 * D ^ 4 * Real.sqrt D * S ^ 2 * (z.im)⁻¹ ^ 5 * ((N : ℝ) ^ 2)⁻¹
      ≤ (8 * D ^ 4 * Real.sqrt D * S ^ 2 * c⁻¹ ^ 5) * ((N : ℝ) ^ 2)⁻¹ := by
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact mul_le_mul_of_nonneg_left hpow hcoef
  exact hsharp.trans hfin

/-- **The exact remaining analytic obligation.**  Two regions of the weighted strip bound are
not supplied by any theorem in this repository:

* the near-real region `0 < |Im z| < c` (both signs of `Im z`), and
* the negative-imaginary half of the away region `c ≤ |Im z| < η₀`.

(The positive-imaginary away region is the theorem
`frob_gueResolventMean_sub_limit_le_of_ge`.)

For the scalar (`d = 1`) pencil and the linearization pencils this residual is *not* known to
be true: the averaged resolvent differs from its limit by `N^{-1/3}`-type terms at the Airy
edge scale `|Im z| ~ N^{-2/3}`, while the required right-hand side is `C_s N^{2β/3 - 2}` with
`β < 1`.  See `docs/handoffs/STATUS_MOMENTS.md`. -/
def WeightedStripResidual (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ) (k : ℕ)
    (c η₀ C_s β : ℝ) : Prop :=
  (∀ᶠ N : ℕ in atTop, ∀ z : ℂ, z.im ≠ 0 → |z.im| < c →
    frob (gueResolventMean (N := N) A₀ A z - operatorMatrixPencilCauchy A₀ A z)
      ≤ C_s * |z.im| ^ (-β) / (N : ℝ) ^ 2) ∧
  (∀ᶠ N : ℕ in atTop, ∀ z : ℂ, z.im < 0 → c ≤ |z.im| → |z.im| < η₀ →
    frob (gueResolventMean (N := N) A₀ A z - operatorMatrixPencilCauchy A₀ A z)
      ≤ C_s * |z.im| ^ (-β) / (N : ℝ) ^ 2)

/-- **The full strip bound follows from the residual plus the positive-imaginary away region.**
The latter is available from `frob_gueResolventMean_sub_limit_le_of_ge` (with `β = 0` and the
explicit constant appearing there), so `WeightedStripResidual` is exactly the unproved content
of `WeightedStripBound`. -/
theorem weightedStripBound_of_residual_and_awayPos
    {A₀ : Matrix d d ℂ} {A : ι → Matrix d d ℂ} {k : ℕ} {c η₀ C_s β : ℝ} (hcη : c ≤ η₀)
    (hpos : ∀ᶠ N : ℕ in atTop, ∀ z : ℂ, 0 < z.im → c ≤ z.im → z.im < η₀ →
      frob (gueResolventMean (N := N) A₀ A z - operatorMatrixPencilCauchy A₀ A z)
        ≤ C_s * z.im ^ (-β) / (N : ℝ) ^ 2)
    (h : WeightedStripResidual (ι := ι) A₀ A k c η₀ C_s β) :
    WeightedStripBound A₀ A k η₀ C_s β := by
  simp only [WeightedStripBound, WeightedStripResidual] at h ⊢
  obtain ⟨hnear, hneg⟩ := h
  filter_upwards [hnear, hneg, hpos] with N hN1 hN2 hN3 z hz hη
  rcases lt_trichotomy z.im 0 with hnegim | hzero | hposim
  · by_cases hlt : |z.im| < c
    · exact hN1 z hz hlt
    · exact hN2 z hnegim (le_of_not_gt hlt) hη
  · exact absurd hzero hz
  · by_cases hlt : |z.im| < c
    · exact hN1 z hz hlt
    · have habs : |z.im| = z.im := abs_of_pos hposim
      have hle : c ≤ z.im := by
        rw [← habs]
        exact le_of_not_gt hlt
      have hlt2 : z.im < η₀ := by
        rw [← habs]
        exact hη
      have hfin := hN3 z hposim hle hlt2
      rwa [← habs] at hfin

end GUEStrongConvergence
