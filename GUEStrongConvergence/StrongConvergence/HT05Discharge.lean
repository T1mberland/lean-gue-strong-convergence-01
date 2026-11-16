/-
# HT05 discharge: the project target from the self-energy branch

This file discharges the weighted interface `HT05Inputs'` at the canonical pencils, with **no
hypotheses** on the pencil other than Hermitianity of the coefficients.  The result is
`GUEStrongConvergenceStatement_of_selfEnergy (r : ℕ) : GUEStrongConvergenceStatement r`.

## Strategy

The weighted good region is

`G = {z : ℂ | 0 < z.im ∧ Cst * (1 + ‖z‖)^2 * (im z)^(-6) / N^2 < 1/2}`.

It is *not* a half-plane, so the previous half-plane uniqueness argument does not apply directly.
Instead:

1. **`G` is path-connected** (hence preconnected).  The horizontal segment from `z` to `i im z`
   stays in `G` (same imaginary part, `‖·‖` decreases), and the vertical ray `i y`, `y ≥ im z`,
   stays in `G` because `y ↦ (1 + y)^2 / y^6` is decreasing for `y > 0`.
2. **A small point inside `G`**: `z₀ = i Y` with `Y = √(2 (card d)^4 S) + 8 Cst / N^2 + 2` and
   `S = ∑ i, frob (A i)^2`.  Then `Y ≥ 2` and `Y^4 ≥ Y > 8 Cst / N^2` give the weighted smallness
   at `z₀`, and `‖m(z₀)‖ · S · ‖g(z₀)‖ ≤ 2 (card d)^4 S / Y^2 < 1`.
3. **Pointwise variants** of the invertibility and resolvent-norm lemmas, taking a bound
   `frob (selfEnergy - z • 1) ≤ CA (im z)^(-5) / N^2` at a single point `z`, together with
   `card d * CA ≤ Cst` and `Cst (im z)^(-6) / N^2 < 1/2`.
4. **The identification on `G`** by `matrixDyson_analytic_unique_of_small_point` with `U := G`.
5. **`HT05Inputs'_of_unconditional`** with the explicit constants
   `C1 = 16 (card d)^3 S^2 (1 + K^2)`, `Cinv1 = 4 (card d) (1 + K^2)`,
   `Cst = max 1 (card d * C1)`, where `K = frobK A₀ A`.
6. **The canonical pencils** and `GUEStrongConvergenceStatement_of_selfEnergy`.

No `sorry`, no new axioms.
-/
import GUEStrongConvergence.StrongConvergence.HT05Harness
import GUEStrongConvergence.StrongConvergence.HT05Invertibility

open MeasureTheory ProbabilityTheory Matrix Filter
open FreeProbability FreeProbability.Fock
open scoped Matrix.Norms.Operator ComplexOrder ENNReal NNReal Topology BigOperators

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option profiler true
set_option profiler true
set_option maxHeartbeats 4000000

namespace GUEStrongConvergence

noncomputable section

variable {ι d : Type*} [Fintype ι] [Fintype d] [DecidableEq d] [DecidableEq ι]

noncomputable local instance ht05FPartialOrder :
    PartialOrder (WordSpace ι →L[ℂ] WordSpace ι) :=
  CStarAlgebra.spectralOrder _
noncomputable local instance ht05FStarOrderedRing :
    StarOrderedRing (WordSpace ι →L[ℂ] WordSpace ι) :=
  CStarAlgebra.spectralOrderedRing _

/-! ## The explicit constants -/

/-- The weighted self-energy constant `S = ∑ i, frob (A i)^2`. -/
def HT05S (A : ι → Matrix d d ℂ) : ℝ := ∑ i, (frob (A i)) ^ 2

/-- The pencil size constant `K = frobK A₀ A`. -/
def HT05K (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ) : ℝ := frobK A₀ A

/-- `C1 = 16 (card d)^3 S^2 (1 + K^2)`: the weighted self-energy constant. -/
def HT05C1 (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ) : ℝ :=
  16 * (Fintype.card d : ℝ) ^ 3 * (HT05S A) ^ 2 * (1 + (HT05K A₀ A) ^ 2)

/-- `Cinv1 = 4 (card d) (1 + K^2)`: the inverse bound constant. -/
def HT05Cinv1 (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ) : ℝ :=
  4 * (Fintype.card d : ℝ) * (1 + (HT05K A₀ A) ^ 2)

/-- `Cst = max 1 (card d * C1)`: the frozen weighted constant. -/
def HT05Cst (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ) : ℝ :=
  max 1 ((Fintype.card d : ℝ) * HT05C1 A₀ A)

lemma HT05S_nonneg (A : ι → Matrix d d ℂ) : 0 ≤ HT05S A := by
  rw [HT05S]
  exact Finset.sum_nonneg (fun i _ => sq_nonneg _)

lemma HT05K_nonneg (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ) : 0 ≤ HT05K A₀ A := by
  rw [HT05K]
  exact frobK_nonneg A₀ A

lemma HT05C1_nonneg (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ) : 0 ≤ HT05C1 A₀ A := by
  rw [HT05C1]
  have h1 : (0 : ℝ) ≤ (Fintype.card d : ℝ) ^ 3 := pow_nonneg (by positivity) 3
  have h2 : (0 : ℝ) ≤ (HT05S A) ^ 2 := sq_nonneg _
  have h3 : (0 : ℝ) ≤ 1 + (HT05K A₀ A) ^ 2 := by linarith [sq_nonneg (HT05K A₀ A)]
  exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) h1) h2) h3

lemma HT05Cinv1_nonneg (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ) : 0 ≤ HT05Cinv1 A₀ A := by
  rw [HT05Cinv1]
  have h3 : (0 : ℝ) ≤ 1 + (HT05K A₀ A) ^ 2 := by linarith [sq_nonneg (HT05K A₀ A)]
  exact mul_nonneg (mul_nonneg (by norm_num) (by positivity)) h3

lemma HT05Cst_pos (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ) : 0 < HT05Cst A₀ A := by
  rw [HT05Cst]
  exact lt_of_lt_of_le one_pos (le_max_left _ _)

lemma HT05Cst_ge_C1 (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ) :
    HT05C1 A₀ A ≤ HT05Cst A₀ A := by
  rw [HT05Cst]
  refine (le_trans ?_ (le_max_right _ _))
  by_cases hcard : (Fintype.card d : ℝ) = 0
  · have hC1 : HT05C1 A₀ A = 0 := by
      rw [HT05C1, hcard]
      ring
    rw [hC1]
    exact mul_nonneg (by positivity) (by positivity)
  · have hcard1 : 1 ≤ (Fintype.card d : ℝ) := by
      have hnat : 0 < Fintype.card d := Nat.pos_of_ne_zero (fun h => hcard (by exact_mod_cast h))
      exact_mod_cast hnat
    calc HT05C1 A₀ A = 1 * HT05C1 A₀ A := by ring
      _ ≤ (Fintype.card d : ℝ) * HT05C1 A₀ A := by
          exact mul_le_mul_of_nonneg_right hcard1 (HT05C1_nonneg A₀ A)

lemma HT05Cst_ge_card_mul_C1 (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ) :
    (Fintype.card d : ℝ) * HT05C1 A₀ A ≤ HT05Cst A₀ A := by
  rw [HT05Cst]
  exact le_max_right _ _

/-! ## The weighted good region -/

/-- The weighted good region `G` (the good region at the frozen constant `Cst`, with `K = 1`). -/
def goodRegionG (N : ℕ) (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ) : Set ℂ :=
  goodRegion N (HT05Cst A₀ A) 1

lemma goodRegionG_isOpen (N : ℕ) (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ) :
    IsOpen (goodRegionG N A₀ A) :=
  goodRegion_isOpen N (HT05Cst A₀ A) 1

/-- The region `G` is contained in the upper half-plane. -/
lemma goodRegionG_subset_upper (N : ℕ) (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ) :
    goodRegionG N A₀ A ⊆ {z : ℂ | 0 < z.im} := by
  intro z hz
  simpa only [goodRegionG, goodRegion, Set.mem_setOf_eq] using hz.1

lemma goodRegionG_pos_im (N : ℕ) (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ) :
    ∀ z ∈ goodRegionG N A₀ A, 0 < z.im :=
  fun z hz => goodRegionG_subset_upper N A₀ A hz

/-! ### The weight is decreasing on the positive imaginary axis -/

/-- The map `y ↦ (1 + y)^2 / y^6` is decreasing for `y > 0`. -/
lemma goodRegion_weight_antitone {y1 y2 : ℝ} (h1 : 0 < y1) (h2 : 0 < y2) (h : y1 ≤ y2) :
    (1 + y2) ^ 2 / y2 ^ 6 ≤ (1 + y1) ^ 2 / y1 ^ 6 := by
  have hy1 : 0 < y1 ^ 6 := pow_pos h1 6
  have hy2 : 0 < y2 ^ 6 := pow_pos h2 6
  rw [div_le_div_iff₀ hy2 hy1]
  -- goal: (1 + y2)^2 * y1^6 ≤ (1 + y1)^2 * y2^6
  set r : ℝ := y2 / y1 with hr
  have hr_ge_1 : 1 ≤ r := by
    rw [hr, le_div_iff₀ h1]
    linarith
  have hr_pos : 0 < r := lt_of_lt_of_le zero_lt_one hr_ge_1
  have hy2_eq : y2 = r * y1 := by
    rw [hr, div_mul_cancel₀ _ h1.ne']
  rw [hy2_eq, mul_pow]
  -- goal: (1 + r * y1)^2 * y1^6 ≤ (1 + y1)^2 * (r^6 * y1^6)
  have hkey : (1 + r * y1) ^ 2 ≤ (1 + y1) ^ 2 * r ^ 6 := by
    have h_lin : 1 + r * y1 ≤ r ^ 3 * (1 + y1) := by
      have h_diff : r ^ 3 * (1 + y1) - (1 + r * y1) =
          (r - 1) * (r ^ 2 + r + 1 + y1 * r * (r + 1)) := by ring
      have h_nonneg : 0 ≤ (r - 1) * (r ^ 2 + r + 1 + y1 * r * (r + 1)) := by
        apply mul_nonneg
        · linarith
        · positivity
      linarith
    have hpos2 : 0 < r ^ 3 * (1 + y1) := by positivity
    nlinarith [h_lin, hpos2, sq_nonneg (1 + r * y1), sq_nonneg (r ^ 3 * (1 + y1)),
      mul_nonneg (by positivity : (0:ℝ) ≤ 1 + r * y1) hpos2.le]
  calc (1 + r * y1) ^ 2 * y1 ^ 6 ≤ ((1 + y1) ^ 2 * r ^ 6) * y1 ^ 6 := by
        exact mul_le_mul_of_nonneg_right hkey (by positivity)
    _ = (1 + y1) ^ 2 * (r ^ 6 * y1 ^ 6) := by ring

/-- The weighted smallness condition at a large point on the imaginary axis. -/
lemma goodRegion_weighted_small {N : ℕ} {Cst Y : ℝ} (hCst : 0 < Cst) (hN : 0 < N)
    (hY2 : 2 ≤ Y) (hY8 : 8 * Cst / (N : ℝ) ^ 2 < Y) :
    Cst * (1 + Y) ^ 2 * ((N : ℝ) ^ 2)⁻¹ * ((Y) ^ 6)⁻¹ < 1 / 2 := by
  have hYpos : 0 < Y := lt_of_lt_of_le (by norm_num) hY2
  have hY4pos : 0 < Y ^ 4 := pow_pos hYpos 4
  have h2 : (1 + Y) ^ 2 ≤ 4 * Y ^ 2 := by nlinarith [hY2, sq_nonneg (Y - 1)]
  have h3 : (1 + Y) ^ 2 * ((Y) ^ 6)⁻¹ ≤ 4 * Y ^ 2 * ((Y) ^ 6)⁻¹ := by
    exact mul_le_mul_of_nonneg_right h2 (by positivity)
  have h4 : 4 * Y ^ 2 * ((Y) ^ 6)⁻¹ = 4 * ((Y) ^ 4)⁻¹ := by
    field_simp
  rw [h4] at h3
  have hY4_ge_Y : Y ≤ Y ^ 4 := by nlinarith [hY2, sq_nonneg Y]
  have hY4_gt : 8 * Cst / (N : ℝ) ^ 2 < Y ^ 4 := lt_of_lt_of_le hY8 hY4_ge_Y
  have h5 : 4 * Cst * ((N : ℝ) ^ 2)⁻¹ * ((Y) ^ 4)⁻¹ < 1 / 2 := by
    have hY4_gt' : 8 * Cst * ((N : ℝ) ^ 2)⁻¹ < Y ^ 4 := by
      simpa only [div_eq_mul_inv] using hY4_gt
    have heq : 4 * Cst * ((N : ℝ) ^ 2)⁻¹ * ((Y) ^ 4)⁻¹ =
        (4 * Cst * ((N : ℝ) ^ 2)⁻¹) / Y ^ 4 := by ring
    rw [heq, div_lt_iff₀ hY4pos]
    nlinarith [hY4_gt']
  calc Cst * (1 + Y) ^ 2 * ((N : ℝ) ^ 2)⁻¹ * ((Y) ^ 6)⁻¹
      = Cst * ((N : ℝ) ^ 2)⁻¹ * ((1 + Y) ^ 2 * ((Y) ^ 6)⁻¹) := by ring
    _ ≤ Cst * ((N : ℝ) ^ 2)⁻¹ * (4 * ((Y) ^ 4)⁻¹) := by
        exact mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = 4 * Cst * ((N : ℝ) ^ 2)⁻¹ * ((Y) ^ 4)⁻¹ := by ring
    _ < 1 / 2 := h5

/-! ### Path-connectivity of `G` -/

/-- The horizontal segment from `z` to `i im z` stays in `G`. -/
lemma goodRegionG_horizontal_segment (N : ℕ) (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    {z : ℂ} (hz : z ∈ goodRegionG N A₀ A) :
    ∀ t ∈ Set.Icc (0:ℝ) 1, (1 - t) * z + t * Complex.I * z.im ∈ goodRegionG N A₀ A := by
  simp only [goodRegionG, goodRegion, Set.mem_ofPred_eq] at hz ⊢
  rcases hz with ⟨hz_im, hz_small⟩
  intro t ht
  rcases ht with ⟨ht0, ht1⟩
  have h_im : ((1 - t) * z + t * Complex.I * z.im).im = z.im := by
    have h1 : ((1 : ℂ) - ↑t) = ↑(1 - t) := by norm_num
    rw [h1]
    simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
    ring
  have h_re : ((1 - t) * z + t * Complex.I * z.im).re = (1 - t) * z.re := by
    have h1 : ((1 : ℂ) - ↑t) = ↑(1 - t) := by norm_num
    rw [h1]
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
    ring
  constructor
  · rw [h_im]; exact hz_im
  · have h_norm_le : ‖(1 - t) * z + t * Complex.I * z.im‖ ≤ ‖z‖ := by
      have h_norm_sq : ‖(1 - t) * z + t * Complex.I * z.im‖^2 ≤ ‖z‖^2 := by
        rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply,
          h_re, h_im]
        have ht_sq : (1 - t) ^ 2 ≤ 1 := by nlinarith [ht0, ht1, sq_nonneg t]
        have hre_sq : ((1 - t) * z.re) ^ 2 ≤ z.re ^ 2 := by
          calc ((1 - t) * z.re) ^ 2 = (1 - t) ^ 2 * z.re ^ 2 := by ring
            _ ≤ 1 * z.re ^ 2 := by
                exact mul_le_mul_of_nonneg_right ht_sq (sq_nonneg z.re)
            _ = z.re ^ 2 := by ring
        nlinarith [hre_sq, sq_nonneg z.im]
      have h_nn1 : 0 ≤ ‖(1 - t) * z + t * Complex.I * z.im‖ := norm_nonneg _
      have h_nn2 : 0 ≤ ‖z‖ := norm_nonneg _
      nlinarith [h_norm_sq, h_nn1, h_nn2]
    rw [h_im]
    have hw : (1 + ‖(1 - t) * z + t * Complex.I * z.im‖) ^ 2 ≤ (1 + ‖z‖) ^ 2 := by
      have h0 : 0 ≤ ‖(1 - t) * z + t * Complex.I * z.im‖ := norm_nonneg _
      have h1 : 0 ≤ ‖z‖ := norm_nonneg _
      nlinarith
    have hC0 : 0 ≤ HT05Cst A₀ A := (HT05Cst_pos A₀ A).le
    have hN2 : 0 ≤ ((N : ℝ) ^ 2)⁻¹ := by positivity
    have hy6 : 0 ≤ ((z.im) ^ 6)⁻¹ := by positivity
    have hstep : HT05Cst A₀ A * (1 + ‖(1 - t) * z + t * Complex.I * z.im‖) ^ 2 *
        ((N : ℝ) ^ 2)⁻¹ * ((z.im) ^ 6)⁻¹ ≤
        HT05Cst A₀ A * (1 + ‖z‖) ^ 2 * ((N : ℝ) ^ 2)⁻¹ * ((z.im) ^ 6)⁻¹ := by
      gcongr
    exact lt_of_le_of_lt hstep hz_small

/-- The vertical ray `i y`, `y ≥ y₁`, stays in `G` when `i y₁ ∈ G`. -/
lemma goodRegionG_vertical_segment (N : ℕ) (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    {y1 y2 : ℝ} (hy1 : Complex.I * y1 ∈ goodRegionG N A₀ A) (h : y1 ≤ y2) :
    ∀ t ∈ Set.Icc (0:ℝ) 1, Complex.I * ((1 - t) * y1 + t * y2) ∈ goodRegionG N A₀ A := by
  simp only [goodRegionG, goodRegion, Set.mem_ofPred_eq] at hy1 ⊢
  rcases hy1 with ⟨hy1_im, hy1_small⟩
  have hy1_pos : 0 < y1 := by
    have him := hy1_im
    simp only [Complex.mul_im, Complex.I_re, Complex.I_im, zero_mul, one_mul,
      Complex.ofReal_im, Complex.ofReal_re] at him
    linarith
  intro t ht
  rcases ht with ⟨ht0, ht1⟩
  set y : ℝ := (1 - t) * y1 + t * y2 with hydef
  have hy_ge_y1 : y1 ≤ y := by
    rw [hydef]
    have h2 : 0 ≤ t := ht0
    have h3 : 0 ≤ y2 - y1 := by linarith
    nlinarith [mul_nonneg h2 h3]
  have hy_pos : 0 < y := lt_of_lt_of_le hy1_pos hy_ge_y1
  have h_im : (Complex.I * ((1 - t) * y1 + t * y2)).im = y := by
    rw [hydef]
    have h1 : ((1 : ℂ) - ↑t) = ↑(1 - t) := by norm_num
    rw [h1]
    have h2 : (↑(1 - t) * ↑y1 : ℂ) = ↑((1 - t) * y1) := by norm_num
    have h3 : (↑t * ↑y2 : ℂ) = ↑(t * y2) := by norm_num
    rw [h2, h3]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_im, Complex.I_re,
      Complex.I_im, zero_mul, one_mul]
    ring
  have h_norm : ‖Complex.I * ((1 - t) * y1 + t * y2)‖ = y := by
    have h1 : Complex.I * ((1 - t) * y1 + t * y2) = Complex.I * ↑y := by
      rw [hydef]
      norm_num
    rw [h1, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hy_pos]
  constructor
  · rw [h_im]; exact hy_pos
  · have hw : (1 + y) ^ 2 * ((y) ^ 6)⁻¹ ≤ (1 + y1) ^ 2 * ((y1) ^ 6)⁻¹ := by
      have hdiv : (1 + y) ^ 2 / y ^ 6 ≤ (1 + y1) ^ 2 / y1 ^ 6 :=
        goodRegion_weight_antitone hy1_pos hy_pos hy_ge_y1
      simpa only [div_eq_mul_inv] using hdiv
    have hC0 : 0 ≤ HT05Cst A₀ A * ((N : ℝ) ^ 2)⁻¹ := by
      have hC := (HT05Cst_pos A₀ A).le
      positivity
    have hstep : HT05Cst A₀ A * (1 + y) ^ 2 * ((N : ℝ) ^ 2)⁻¹ * ((y) ^ 6)⁻¹ ≤
        HT05Cst A₀ A * (1 + y1) ^ 2 * ((N : ℝ) ^ 2)⁻¹ * ((y1) ^ 6)⁻¹ := by
      calc HT05Cst A₀ A * (1 + y) ^ 2 * ((N : ℝ) ^ 2)⁻¹ * ((y) ^ 6)⁻¹
          = HT05Cst A₀ A * ((N : ℝ) ^ 2)⁻¹ * ((1 + y) ^ 2 * ((y) ^ 6)⁻¹) := by ring
        _ ≤ HT05Cst A₀ A * ((N : ℝ) ^ 2)⁻¹ * ((1 + y1) ^ 2 * ((y1) ^ 6)⁻¹) := by
            exact mul_le_mul_of_nonneg_left hw hC0
        _ = HT05Cst A₀ A * (1 + y1) ^ 2 * ((N : ℝ) ^ 2)⁻¹ * ((y1) ^ 6)⁻¹ := by ring
    have hy1_norm : ‖Complex.I * ↑y1‖ = y1 := by
      rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hy1_pos]
    have hy1_im' : (Complex.I * ↑y1).im = y1 := by
      simp only [Complex.mul_im, Complex.I_re, Complex.I_im, zero_mul, one_mul,
        Complex.ofReal_im, Complex.ofReal_re]
      linarith
    rw [hy1_norm, hy1_im'] at hy1_small
    rw [h_im, h_norm]
    exact lt_of_le_of_lt hstep hy1_small

/-- The horizontal segment joins `z` to `i im z` inside `G`. -/
lemma goodRegionG_joinedIn_horizontal (N : ℕ) (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    {z : ℂ} (hz : z ∈ goodRegionG N A₀ A) :
    JoinedIn (goodRegionG N A₀ A) z (Complex.I * z.im) := by
  let f : ℝ → ℂ := fun t => (1 - t) * z + t * Complex.I * z.im
  have hf : Continuous f := by continuity
  have h0 : f 0 = z := by simp [f]
  have h1 : f 1 = Complex.I * z.im := by simp [f]
  have hF : f '' Set.Icc (0:ℝ) 1 ⊆ goodRegionG N A₀ A := by
    rintro _ ⟨t, ht, rfl⟩
    exact goodRegionG_horizontal_segment N A₀ A hz t ht
  exact JoinedIn.ofLine hf.continuousOn h0 h1 hF

/-- The vertical segment along the imaginary axis joins `i y₁` to `i y₂` inside `G`. -/
lemma goodRegionG_joinedIn_vertical (N : ℕ) (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    {y1 y2 : ℝ} (hy1 : Complex.I * y1 ∈ goodRegionG N A₀ A) (h : y1 ≤ y2) :
    JoinedIn (goodRegionG N A₀ A) (Complex.I * y1) (Complex.I * y2) := by
  let f : ℝ → ℂ := fun t => Complex.I * ((1 - t) * y1 + t * y2)
  have hf : Continuous f := by continuity
  have h0 : f 0 = Complex.I * y1 := by simp [f]
  have h1 : f 1 = Complex.I * y2 := by simp [f]
  have hF : f '' Set.Icc (0:ℝ) 1 ⊆ goodRegionG N A₀ A := by
    rintro _ ⟨t, ht, rfl⟩
    exact goodRegionG_vertical_segment N A₀ A hy1 h t ht
  exact JoinedIn.ofLine hf.continuousOn h0 h1 hF

/-- `G` is path-connected, in particular preconnected. -/
theorem goodRegionG_isPreconnected (N : ℕ) (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ) :
    IsPreconnected (goodRegionG N A₀ A) := by
  have hnonempty : (goodRegionG N A₀ A).Nonempty := by
    by_cases hN : N = 0
    · subst hN
      refine ⟨Complex.I * 1, ?_⟩
      simp only [goodRegionG, goodRegion, Set.mem_ofPred_eq]
      constructor
      · simp only [Complex.mul_im, Complex.I_re, Complex.I_im, zero_mul, one_mul,
          Complex.ofReal_im]
        norm_num
      · simp only [Complex.mul_re, Complex.I_re, Complex.I_im, one_mul, zero_mul,
          Complex.ofReal_re, norm_mul, Complex.norm_I, Complex.norm_real]
        norm_num
    · have hNpos : 0 < N := Nat.pos_of_ne_zero hN
      have hNpos' : 0 < (N : ℝ) := by exact_mod_cast hNpos
      set Y : ℝ := 8 * HT05Cst A₀ A / (N : ℝ) ^ 2 + 2 with hYdef
      have hY2 : 2 ≤ Y := by
        rw [hYdef]
        have h1 : 0 ≤ 8 * HT05Cst A₀ A / (N : ℝ) ^ 2 := by
          have hC := (HT05Cst_pos A₀ A).le
          positivity
        linarith
      have hYpos : 0 < Y := lt_of_lt_of_le (by norm_num) hY2
      have hY8 : 8 * HT05Cst A₀ A / (N : ℝ) ^ 2 < Y := by rw [hYdef]; linarith
      refine ⟨Complex.I * Y, ?_⟩
      simp only [goodRegionG, goodRegion, Set.mem_ofPred_eq]
      constructor
      · simp only [Complex.mul_im, Complex.I_re, Complex.I_im, zero_mul, one_mul,
          Complex.ofReal_im, Complex.ofReal_re]
        norm_num
        exact hYpos
      · have him : (Complex.I * ↑Y).im = Y := by
          simp only [Complex.mul_im, Complex.I_re, Complex.I_im, zero_mul, one_mul,
            Complex.ofReal_im, Complex.ofReal_re]
          norm_num
        have hnorm : ‖Complex.I * ↑Y‖ = Y := by
          rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
            abs_of_pos hYpos]
        rw [him, hnorm]
        exact goodRegion_weighted_small (HT05Cst_pos A₀ A) hNpos hY2 hY8
  have hpath : IsPathConnected (goodRegionG N A₀ A) := by
    obtain ⟨x0, hx0⟩ := hnonempty
    refine ⟨x0, hx0, ?_⟩
    intro y hy
    have h1 : JoinedIn (goodRegionG N A₀ A) x0 (Complex.I * x0.im) :=
      goodRegionG_joinedIn_horizontal N A₀ A hx0
    have h2 : JoinedIn (goodRegionG N A₀ A) y (Complex.I * y.im) :=
      goodRegionG_joinedIn_horizontal N A₀ A hy
    have hx0_axis : Complex.I * x0.im ∈ goodRegionG N A₀ A := by
      have := goodRegionG_horizontal_segment N A₀ A hx0 1 (by norm_num)
      simpa using this
    have hy_axis : Complex.I * y.im ∈ goodRegionG N A₀ A := by
      have := goodRegionG_horizontal_segment N A₀ A hy 1 (by norm_num)
      simpa using this
    have h3 : JoinedIn (goodRegionG N A₀ A) (Complex.I * x0.im) (Complex.I * y.im) := by
      rcases le_total x0.im y.im with hle | hle
      · exact goodRegionG_joinedIn_vertical N A₀ A hx0_axis hle
      · exact (goodRegionG_joinedIn_vertical N A₀ A hy_axis hle).symm
    exact h1.trans (h3.trans h2.symm)
  exact (IsPathConnected.isConnected hpath).isPreconnected


/-! ## Pointwise variants of the invertibility and resolvent-norm lemmas -/

/-- **Pointwise invertibility of the operator-valued difference at the self-energy argument.**

Same as `isUnit_operatorMatrixDifference_selfEnergy`, but the self-energy bound is assumed at
the single point `z` (so it can be the weighted bound). -/
theorem isUnit_operatorMatrixDifference_selfEnergy_pt {N : ℕ} (A₀ : Matrix d d ℂ)
    (A : ι → Matrix d d ℂ) (hA₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian)
    {CA Cst : ℝ} {z : ℂ}
    (hfr : frob (selfEnergy (N := N) A₀ A z - z • (1 : Matrix d d ℂ)) ≤
        CA * z.im ^ (-(5 : ℝ)) / (N : ℝ) ^ 2)
    (hCst : (Fintype.card d : ℝ) * CA ≤ Cst)
    (hz : 0 < z.im) (hN : 0 < N)
    (hsmall : Cst * z.im ^ (-(6 : ℝ)) / (N : ℝ) ^ 2 < 1 / 2) :
    IsUnit (operatorMatrixDifference A (selfEnergy (N := N) A₀ A z - A₀)) := by
  refine isUnit_operatorMatrixDifference_of_frob_close A₀ A hA₀ hA _ z hz ?_
  have hcard0 : (0 : ℝ) ≤ (Fintype.card d : ℝ) := by positivity
  have hN2 : (0 : ℝ) < (N : ℝ) ^ 2 := by positivity
  have hinv0 : (0 : ℝ) ≤ (z.im)⁻¹ := by positivity
  have hstep : (Fintype.card d : ℝ) * frob (selfEnergy (N := N) A₀ A z - z • (1 : Matrix d d ℂ)) *
      (z.im)⁻¹ ≤ Cst * z.im ^ (-(6 : ℝ)) / (N : ℝ) ^ 2 := by
    have h1 : (Fintype.card d : ℝ) *
        frob (selfEnergy (N := N) A₀ A z - z • (1 : Matrix d d ℂ)) * (z.im)⁻¹ ≤
        (Fintype.card d : ℝ) *
          (CA * z.im ^ (-(5 : ℝ)) / (N : ℝ) ^ 2) *
          (z.im)⁻¹ := by
      refine mul_le_mul_of_nonneg_right ?_ hinv0
      exact mul_le_mul_of_nonneg_left hfr hcard0
    refine h1.trans ?_
    have heq1 : (Fintype.card d : ℝ) *
          (CA * z.im ^ (-(5 : ℝ)) / (N : ℝ) ^ 2) *
          (z.im)⁻¹ =
        ((Fintype.card d : ℝ) * CA) *
          (z.im ^ (-(5 : ℝ)) * (z.im)⁻¹) / (N : ℝ) ^ 2 := by ring
    rw [heq1, ht05E_rpow_neg_five_mul_inv hz]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hCst
      (Real.rpow_pos_of_pos hz _).le) hN2.le
  exact lt_of_le_of_lt hstep (lt_trans hsmall (by norm_num))

/-- **Pointwise operator-valued resolvent bound at the self-energy argument.**

Same as `norm_operatorMatrixArgumentResolvent_selfEnergy_le`, with the self-energy bound assumed
at the single point `z`. -/
theorem norm_operatorMatrixArgumentResolvent_selfEnergy_le_pt {N : ℕ}
    (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ) (hA₀ : A₀.IsHermitian)
    (hA : ∀ i, (A i).IsHermitian) {CA Cst : ℝ} {z : ℂ}
    (hfr : frob (selfEnergy (N := N) A₀ A z - z • (1 : Matrix d d ℂ)) ≤
        CA * z.im ^ (-(5 : ℝ)) / (N : ℝ) ^ 2)
    (hCst : (Fintype.card d : ℝ) * CA ≤ Cst)
    (hz : 0 < z.im) (hN : 0 < N)
    (hsmall : Cst * z.im ^ (-(6 : ℝ)) / (N : ℝ) ^ 2 < 1 / 2) :
    ‖CStarMatrix.ofMatrix
      (operatorMatrixArgumentResolvent A (selfEnergy (N := N) A₀ A z - A₀))‖ ≤ 2 / z.im := by
  set Λ : Matrix d d ℂ := selfEnergy (N := N) A₀ A z with hΛ
  set P : CStarMatrix d d (WordSpace ι →L[ℂ] WordSpace ι) :=
    operatorMatrixDifference A (z • (1 : Matrix d d ℂ) - A₀) with hPdef
  set δ : CStarMatrix d d (WordSpace ι →L[ℂ] WordSpace ι) :=
    CStarMatrix.ofMatrix (scalarMatrixEmbedding
      (A := WordSpace ι →L[ℂ] WordSpace ι) (Λ - z • (1 : Matrix d d ℂ))) with hδdef
  have hPunit : IsUnit P := by
    rw [hPdef, operatorMatrixDifference_pencil]
    exact StarProbabilitySpace.selfAdjoint_mem_resolventSet_of_im_ne_zero
      (operatorMatrixPencil A₀ A) (operatorMatrixPencil_isSelfAdjoint A₀ A hA₀ hA) z hz.ne'
  have hPinv : ‖Ring.inverse P‖ ≤ (z.im)⁻¹ := by
    rw [hPdef, operatorMatrixDifference_pencil]
    have h := norm_resolvent_le_inv_im
      (operatorMatrixPencil_isSelfAdjoint A₀ A hA₀ hA) (z := z) hz
    simpa [resolvent] using h
  have hX : operatorMatrixDifference A (Λ - A₀) = P + δ := by
    have hE : (Λ - A₀) - (z • (1 : Matrix d d ℂ) - A₀) = Λ - z • (1 : Matrix d d ℂ) := by
      abel
    have hsub := operatorMatrixDifference_sub (C := A) (B₁ := Λ - A₀)
      (B₂ := z • (1 : Matrix d d ℂ) - A₀)
    rw [hE] at hsub
    have hδ' : δ = scalarMatrixEmbedding (Λ - z • (1 : Matrix d d ℂ)) := by
      rw [hδdef]
      rfl
    rw [hPdef, hδ', ← hsub]
    abel
  have hδnorm : ‖δ‖ ≤ z.im / 2 := by
    have h1 : ‖δ‖ ≤ (Fintype.card d : ℝ) * frob (Λ - z • (1 : Matrix d d ℂ)) := by
      rw [hδdef]
      exact norm_scalarMatrixEmbedding_le_card_mul_frob_local _
    have hcard0 : (0 : ℝ) ≤ (Fintype.card d : ℝ) := by positivity
    have h2 : (Fintype.card d : ℝ) * frob (Λ - z • (1 : Matrix d d ℂ)) ≤
        (Fintype.card d : ℝ) * (CA * z.im ^ (-(5 : ℝ)) / (N : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_left (by rw [hΛ]; exact hfr) hcard0
    refine h1.trans (h2.trans ?_)
    have heq : (Fintype.card d : ℝ) * (CA * z.im ^ (-(5 : ℝ)) / (N : ℝ) ^ 2) =
        ((Fintype.card d : ℝ) * CA) * z.im ^ (-(5 : ℝ)) / (N : ℝ) ^ 2 := by ring
    rw [heq]
    have hle : ((Fintype.card d : ℝ) * CA) * z.im ^ (-(5 : ℝ)) / (N : ℝ) ^ 2 ≤
        Cst * z.im ^ (-(5 : ℝ)) / (N : ℝ) ^ 2 := by
      refine div_le_div_of_nonneg_right ?_ (by positivity)
      exact mul_le_mul_of_nonneg_right hCst (Real.rpow_pos_of_pos hz _).le
    refine hle.trans ?_
    have hmul := mul_lt_mul_of_pos_right hsmall hz
    have heq2 : Cst * z.im ^ (-(6 : ℝ)) / (N : ℝ) ^ 2 * z.im =
        Cst * z.im ^ (-(5 : ℝ)) / (N : ℝ) ^ 2 := by
      rw [div_mul_eq_mul_div, mul_assoc, ht05E_rpow_neg_six_mul hz]
    rw [heq2] at hmul
    linarith [hmul]
  set Y : CStarMatrix d d (WordSpace ι →L[ℂ] WordSpace ι) := Ring.inverse P * δ with hYdef
  have hY : ‖Y‖ ≤ 1 / 2 := by
    have h1 : ‖Y‖ ≤ ‖Ring.inverse P‖ * ‖δ‖ := by
      rw [hYdef]; exact norm_mul_le _ _
    have h2 : ‖Ring.inverse P‖ * ‖δ‖ ≤ (z.im)⁻¹ * (z.im / 2) := by
      refine mul_le_mul hPinv hδnorm (norm_nonneg _) (by positivity)
    have h3 : (z.im)⁻¹ * (z.im / 2) = 1 / 2 := by
      field_simp
    linarith [h1, h2, h3.symm.le]
  have hYlt : ‖Y‖ < 1 := lt_of_le_of_lt hY (by norm_num)
  have hPeq : P + δ = P * (1 + Y) := by
    rw [hYdef, mul_add, mul_one, ← mul_assoc, Ring.mul_inverse_cancel P hPunit, one_mul]
  have hfac : Ring.inverse (operatorMatrixDifference A (Λ - A₀)) =
      Ring.inverse (1 + Y) * Ring.inverse P := by
    rw [hX, hPeq, Ring.inverse_mul (Or.inl hPunit)]
  have hone : ‖(1 : CStarMatrix d d (WordSpace ι →L[ℂ] WordSpace ι))‖ ≤ 1 := by
    have h : ‖(1 : CStarMatrix d d (WordSpace ι →L[ℂ] WordSpace ι))‖ =
        ‖(1 : CStarMatrix d d (WordSpace ι →L[ℂ] WordSpace ι))‖ *
          ‖(1 : CStarMatrix d d (WordSpace ι →L[ℂ] WordSpace ι))‖ := by
      rw [← CStarRing.norm_star_mul_self
        (x := (1 : CStarMatrix d d (WordSpace ι →L[ℂ] WordSpace ι))), star_one, one_mul]
    nlinarith [norm_nonneg (1 : CStarMatrix d d (WordSpace ι →L[ℂ] WordSpace ι))]
  have hnormY : ‖Ring.inverse (1 + Y)‖ ≤ 2 := by
    have hneglt : ‖-Y‖ < 1 := by rwa [norm_neg]
    have hgeom : Ring.inverse (1 + Y) = ∑' i : ℕ, (-Y) ^ i := by
      have hstep : (1 : CStarMatrix d d (WordSpace ι →L[ℂ] WordSpace ι)) + Y = 1 - (-Y) := by
        rw [sub_neg_eq_add]
      rw [hstep, ← geom_series_eq_inverse (-Y) hneglt]
    rw [hgeom]
    have hle := tsum_geometric_le_of_norm_lt_one (-Y) hneglt
    have hnormneg : ‖-Y‖ ≤ 1 / 2 := by rw [norm_neg]; exact hY
    have hlow : (1 - ‖-Y‖)⁻¹ ≤ 2 := by
      have h0 : (0 : ℝ) < 1 - ‖-Y‖ := by linarith
      have hhalf : (1 : ℝ) / 2 ≤ 1 - ‖-Y‖ := by linarith
      calc (1 - ‖-Y‖)⁻¹ = 1 / (1 - ‖-Y‖) := by rw [one_div]
        _ ≤ 1 / ((1 : ℝ) / 2) := one_div_le_one_div_of_le (by norm_num) hhalf
        _ = 2 := by norm_num
    linarith
  have hmain : ‖Ring.inverse (operatorMatrixDifference A (Λ - A₀))‖ ≤ 2 / z.im := by
    rw [hfac]
    calc ‖Ring.inverse (1 + Y) * Ring.inverse P‖
        ≤ ‖Ring.inverse (1 + Y)‖ * ‖Ring.inverse P‖ := norm_mul_le _ _
      _ ≤ 2 * (z.im)⁻¹ := by
          refine mul_le_mul hnormY hPinv (norm_nonneg _) (by norm_num)
      _ = 2 / z.im := by ring
  simpa only [operatorMatrixArgumentResolvent, Equiv.apply_symm_apply, hΛ] using hmain


/-- **The weighted self-energy bound.**  The unconditional bound
`frob (selfEnergy - z • 1) ≤ 16 (card d)^3 S^2 (‖z‖² + K²) N⁻² (im z)⁻⁵` is bounded by
`C1 (1 + ‖z‖)² (im z)⁻⁵ / N²` using `‖z‖² + K² ≤ (1 + K²) (1 + ‖z‖)²`. -/
lemma frob_selfEnergy_weighted_le {N : ℕ} (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    (hA₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian) (hN : 0 < N)
    {z : ℂ} (hz : 0 < z.im) :
    frob (selfEnergy (N := N) A₀ A z - z • (1 : Matrix d d ℂ)) ≤
      HT05C1 A₀ A * (1 + ‖z‖) ^ 2 * z.im ^ (-(5 : ℝ)) / (N : ℝ) ^ 2 := by
  have h := frob_selfEnergy_sub_smul_one_le A₀ A hA₀ hA z hz hN
  refine h.trans ?_
  set K : ℝ := HT05K A₀ A with hKdef
  have hK : 0 ≤ K := HT05K_nonneg A₀ A
  have hz_nn : 0 ≤ ‖z‖ := norm_nonneg z
  have hY2K : ‖z‖ ^ 2 + K ^ 2 ≤ (1 + K ^ 2) * (1 + ‖z‖) ^ 2 := by
    have h1 : 0 ≤ K ^ 2 := sq_nonneg _
    nlinarith [hK, hz_nn, sq_nonneg ‖z‖, h1]
  have hconst : 16 * (Fintype.card d : ℝ) ^ 3 * (HT05S A) ^ 2 * (‖z‖ ^ 2 + K ^ 2) ≤
      16 * (Fintype.card d : ℝ) ^ 3 * (HT05S A) ^ 2 * ((1 + K ^ 2) * (1 + ‖z‖) ^ 2) := by
    refine mul_le_mul_of_nonneg_left hY2K ?_
    positivity
  have hfenc : 16 * (Fintype.card d : ℝ) ^ 3 * (HT05S A) ^ 2 * (‖z‖ ^ 2 + K ^ 2) *
      ((N : ℝ)⁻¹) ^ 2 * ((z.im)⁻¹) ^ 5 ≤
      16 * (Fintype.card d : ℝ) ^ 3 * (HT05S A) ^ 2 *
        ((1 + K ^ 2) * (1 + ‖z‖) ^ 2) * ((N : ℝ)⁻¹) ^ 2 * ((z.im)⁻¹) ^ 5 := by
    have h2 : 16 * (Fintype.card d : ℝ) ^ 3 * (HT05S A) ^ 2 * (‖z‖ ^ 2 + K ^ 2) *
        ((N : ℝ)⁻¹) ^ 2 ≤
        16 * (Fintype.card d : ℝ) ^ 3 * (HT05S A) ^ 2 *
          ((1 + K ^ 2) * (1 + ‖z‖) ^ 2) * ((N : ℝ)⁻¹) ^ 2 := by
      exact mul_le_mul_of_nonneg_right hconst (by positivity)
    exact mul_le_mul_of_nonneg_right h2 (by positivity)
  refine hfenc.trans (le_of_eq ?_)
  rw [HT05C1, hKdef, Real.rpow_neg hz.le, Real.rpow_ofNat]
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hN
  have hz0 : z.im ≠ 0 := hz.ne'
  field_simp

/-- **A small point inside the weighted good region `G`.**

At `z₀ = i Y` with `Y = √(2 (card d)^4 S_op) + 8 Cst / N^2 + 2` (where `S_op = ∑ i, ‖A i‖²`),
both Dyson branches are small: `‖m(z₀)‖ · (∑ i, ‖A i‖²) · ‖g(z₀)‖ ≤ 2 (card d)^4 S_op / Y^2 < 1`,
and `z₀ ∈ G`. -/
theorem exists_small_point_w {N : ℕ} (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    (hA₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian) (hN : 0 < N) :
    ∃ z₀ : ℂ, z₀ ∈ goodRegionG N A₀ A ∧
      ‖gueResolventMean (N := N) A₀ A z₀‖ * (∑ i, ‖A i‖ ^ 2) *
        ‖operatorMatrixArgumentCauchy A (selfEnergy (N := N) A₀ A z₀ - A₀)‖ < 1 := by
  set Sop : ℝ := ∑ i, ‖A i‖ ^ 2 with hSopdef
  have hSop0 : 0 ≤ Sop := by
    rw [hSopdef]
    exact Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hcard2 : (0 : ℝ) ≤ (Fintype.card d : ℝ) ^ 2 := by positivity
  set Y : ℝ := Real.sqrt (2 * (Fintype.card d : ℝ) ^ 4 * Sop) + 8 * HT05Cst A₀ A / (N : ℝ) ^ 2 + 2
    with hYdef
  have hY2 : 2 ≤ Y := by
    rw [hYdef]
    have h1 : 0 ≤ Real.sqrt (2 * (Fintype.card d : ℝ) ^ 4 * Sop) := Real.sqrt_nonneg _
    have h2 : 0 ≤ 8 * HT05Cst A₀ A / (N : ℝ) ^ 2 := by
      have hC := (HT05Cst_pos A₀ A).le
      positivity
    linarith
  have hYpos : 0 < Y := lt_of_lt_of_le (by norm_num) hY2
  have hY8 : 8 * HT05Cst A₀ A / (N : ℝ) ^ 2 < Y := by
    rw [hYdef]
    have h1 : 0 ≤ Real.sqrt (2 * (Fintype.card d : ℝ) ^ 4 * Sop) := Real.sqrt_nonneg _
    linarith
  have hY_sq : 2 * (Fintype.card d : ℝ) ^ 4 * Sop < Y ^ 2 := by
    have h1 : Real.sqrt (2 * (Fintype.card d : ℝ) ^ 4 * Sop) < Y := by
      rw [hYdef]
      have h2 : 0 ≤ 8 * HT05Cst A₀ A / (N : ℝ) ^ 2 := by
        have hC := (HT05Cst_pos A₀ A).le
        positivity
      linarith
    have hKnn : 0 ≤ 2 * (Fintype.card d : ℝ) ^ 4 * Sop := by positivity
    have hsq : (Real.sqrt (2 * (Fintype.card d : ℝ) ^ 4 * Sop)) ^ 2 = 2 * (Fintype.card d : ℝ) ^ 4 * Sop :=
      Real.sq_sqrt hKnn
    nlinarith [h1, hsq, Real.sqrt_nonneg (2 * (Fintype.card d : ℝ) ^ 4 * Sop), hYpos]
  have hz0pos : 0 < (Complex.I * Y).im := by
    simpa only [Complex.mul_im, Complex.I_re, Complex.I_im, zero_mul, one_mul,
      Complex.ofReal_im, Complex.ofReal_re, zero_add] using hYpos
  have him : (Complex.I * ↑Y).im = Y := by
    simp only [Complex.mul_im, Complex.I_re, Complex.I_im, zero_mul, one_mul,
      Complex.ofReal_im, Complex.ofReal_re]
    norm_num
  have hnormz0 : ‖(Complex.I * ↑Y : ℂ)‖ = Y := by
    rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hYpos]
  -- the self-energy bound at z₀
  have hfr : frob (selfEnergy (N := N) A₀ A (Complex.I * Y) -
      (Complex.I * Y) • (1 : Matrix d d ℂ)) ≤
      HT05C1 A₀ A * (1 + Y) ^ 2 * Y ^ (-(5 : ℝ)) / (N : ℝ) ^ 2 := by
    have h := frob_selfEnergy_weighted_le A₀ A hA₀ hA hN (z := Complex.I * Y) hz0pos
    rwa [hnormz0, him] at h
  -- the resolvent bound at z₀
  have hres : ‖CStarMatrix.ofMatrix (operatorMatrixArgumentResolvent A
      (selfEnergy (N := N) A₀ A (Complex.I * Y) - A₀))‖ ≤ 2 / Y := by
    have hCst_le : (Fintype.card d : ℝ) * (HT05C1 A₀ A * (1 + Y) ^ 2) ≤
        HT05Cst A₀ A * (1 + Y) ^ 2 := by
      have h1 := HT05Cst_ge_card_mul_C1 A₀ A
      have h2 : 0 ≤ (1 + Y) ^ 2 := sq_nonneg _
      calc (Fintype.card d : ℝ) * (HT05C1 A₀ A * (1 + Y) ^ 2)
          = ((Fintype.card d : ℝ) * HT05C1 A₀ A) * (1 + Y) ^ 2 := by ring
        _ ≤ HT05Cst A₀ A * (1 + Y) ^ 2 := by
            exact mul_le_mul_of_nonneg_right h1 h2
    have hsmall : HT05Cst A₀ A * (1 + Y) ^ 2 * Y ^ (-(6 : ℝ)) / (N : ℝ) ^ 2 < 1 / 2 := by
      have h := goodRegion_weighted_small (HT05Cst_pos A₀ A) hN hY2 hY8
      rw [Real.rpow_neg hYpos.le, Real.rpow_ofNat]
      calc HT05Cst A₀ A * (1 + Y) ^ 2 * ((Y) ^ 6)⁻¹ / (N : ℝ) ^ 2
          = HT05Cst A₀ A * (1 + Y) ^ 2 * ((N : ℝ) ^ 2)⁻¹ * ((Y) ^ 6)⁻¹ := by ring
        _ < 1 / 2 := h
    have hfr' : frob (selfEnergy (N := N) A₀ A (Complex.I * Y) -
        (Complex.I * Y) • (1 : Matrix d d ℂ)) ≤
        HT05C1 A₀ A * (1 + Y) ^ 2 * (Complex.I * Y).im ^ (-(5 : ℝ)) / (N : ℝ) ^ 2 := by
      simpa only [him] using hfr
    have hsmall' : HT05Cst A₀ A * (1 + Y) ^ 2 * (Complex.I * Y).im ^ (-(6 : ℝ)) /
        (N : ℝ) ^ 2 < 1 / 2 := by
      simpa only [him] using hsmall
    have := norm_operatorMatrixArgumentResolvent_selfEnergy_le_pt A₀ A hA₀ hA
      (CA := HT05C1 A₀ A * (1 + Y) ^ 2) (Cst := HT05Cst A₀ A * (1 + Y) ^ 2)
      hfr' hCst_le hz0pos hN hsmall'
    simpa only [him] using this
  refine ⟨Complex.I * Y, ?_, ?_⟩
  · -- membership in G
    simp only [goodRegionG, goodRegion, Set.mem_ofPred_eq]
    constructor
    · rw [him]; exact hYpos
    · rw [him, hnormz0]
      exact goodRegion_weighted_small (HT05Cst_pos A₀ A) hN hY2 hY8
  · -- the smallness condition
    have hm_bound : ‖gueResolventMean (N := N) A₀ A (Complex.I * Y)‖ ≤
        (Fintype.card d : ℝ) ^ 2 * Y⁻¹ := by
      have hnorm : ‖(gueResolventMean (N := N) A₀ A (Complex.I * Y) : Matrix d d ℂ)‖ ≤
          (Fintype.card d : ℝ) * frob (gueResolventMean (N := N) A₀ A (Complex.I * Y)) :=
        norm_le_card_mul_frob _
      refine hnorm.trans ?_
      have h := frob_gueResolventMean_le A₀ A hA₀ hA (Complex.I * Y) hz0pos hN
      rw [him] at h
      calc (Fintype.card d : ℝ) * frob (gueResolventMean (N := N) A₀ A (Complex.I * Y))
          ≤ (Fintype.card d : ℝ) * ((Fintype.card d : ℝ) * Y⁻¹) := by gcongr
        _ = (Fintype.card d : ℝ) ^ 2 * Y⁻¹ := by ring
    have hg_bound : ‖operatorMatrixArgumentCauchy A
        (selfEnergy (N := N) A₀ A (Complex.I * Y) - A₀)‖ ≤
        2 * (Fintype.card d : ℝ) ^ 2 * Y⁻¹ := by
      have hη0 : (0 : ℝ) ≤ 2 / (Complex.I * Y).im := by
        rw [him]; positivity
      have hres' : ‖CStarMatrix.ofMatrix (operatorMatrixArgumentResolvent A
          (selfEnergy (N := N) A₀ A (Complex.I * Y) - A₀))‖ ≤ 2 / (Complex.I * Y).im := by
        simpa only [him] using hres
      have hf := frob_operatorMatrixArgumentCauchy_le_of_resolvent A
        (selfEnergy (N := N) A₀ A (Complex.I * Y) - A₀) hη0 hres'
      have hnorm : ‖(operatorMatrixArgumentCauchy A
          (selfEnergy (N := N) A₀ A (Complex.I * Y) - A₀) : Matrix d d ℂ)‖ ≤
          (Fintype.card d : ℝ) * frob (operatorMatrixArgumentCauchy A
            (selfEnergy (N := N) A₀ A (Complex.I * Y) - A₀)) :=
        norm_le_card_mul_frob _
      refine hnorm.trans ?_
      calc (Fintype.card d : ℝ) * frob (operatorMatrixArgumentCauchy A
            (selfEnergy (N := N) A₀ A (Complex.I * Y) - A₀))
          ≤ (Fintype.card d : ℝ) * ((Fintype.card d : ℝ) * (2 / (Complex.I * Y).im)) := by
            gcongr
        _ = 2 * (Fintype.card d : ℝ) ^ 2 * Y⁻¹ := by rw [him]; ring
    have hprod : ‖gueResolventMean (N := N) A₀ A (Complex.I * Y)‖ * Sop *
        ‖operatorMatrixArgumentCauchy A (selfEnergy (N := N) A₀ A (Complex.I * Y) - A₀)‖ ≤
        ((Fintype.card d : ℝ) ^ 2 * Y⁻¹) * Sop * (2 * (Fintype.card d : ℝ) ^ 2 * Y⁻¹) := by
      refine mul_le_mul (mul_le_mul_of_nonneg_right hm_bound hSop0) hg_bound (norm_nonneg _) ?_
      positivity
    have heq : ((Fintype.card d : ℝ) ^ 2 * Y⁻¹) * Sop * (2 * (Fintype.card d : ℝ) ^ 2 * Y⁻¹) =
        2 * (Fintype.card d : ℝ) ^ 4 * Sop / Y ^ 2 := by
      have h1 : Y⁻¹ * Y⁻¹ = (Y ^ 2)⁻¹ := by rw [← mul_inv, pow_two]
      rw [div_eq_mul_inv, ← h1]
      ring
    have hYsq : (0 : ℝ) < Y ^ 2 := pow_pos hYpos 2
    have hlt : 2 * (Fintype.card d : ℝ) ^ 4 * Sop / Y ^ 2 < 1 := by
      rw [div_lt_one hYsq]
      exact hY_sq
    exact lt_of_le_of_lt hprod (lt_of_le_of_lt (le_of_eq heq) hlt)

/-- The weighted good region condition is exactly the frozen-constant smallness condition. -/
lemma goodRegionG_small {N : ℕ} (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    {z : ℂ} (hz : z ∈ goodRegionG N A₀ A) :
    HT05Cst A₀ A * (1 + ‖z‖) ^ 2 * z.im ^ (-(6 : ℝ)) / (N : ℝ) ^ 2 < 1 / 2 := by
  have hpos : 0 < z.im := goodRegionG_pos_im N A₀ A z hz
  have h := hz.2
  rw [Real.rpow_neg hpos.le, Real.rpow_ofNat]
  calc HT05Cst A₀ A * (1 + ‖z‖) ^ 2 * ((z.im) ^ 6)⁻¹ / (N : ℝ) ^ 2
      = HT05Cst A₀ A * (1 + ‖z‖) ^ 2 * ((N : ℝ) ^ 2)⁻¹ * ((z.im) ^ 6)⁻¹ := by ring
    _ < 1 / 2 := h

/-- **The frozen-constant comparison** `card d * (C1 (1 + ‖z‖)²) ≤ Cst (1 + ‖z‖)²`. -/
lemma card_mul_C1_le_Cst (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ) (z : ℂ) :
    (Fintype.card d : ℝ) * (HT05C1 A₀ A * (1 + ‖z‖) ^ 2) ≤
      HT05Cst A₀ A * (1 + ‖z‖) ^ 2 := by
  have h1 := HT05Cst_ge_card_mul_C1 A₀ A
  have h2 : 0 ≤ (1 + ‖z‖) ^ 2 := sq_nonneg _
  calc (Fintype.card d : ℝ) * (HT05C1 A₀ A * (1 + ‖z‖) ^ 2)
      = ((Fintype.card d : ℝ) * HT05C1 A₀ A) * (1 + ‖z‖) ^ 2 := by ring
    _ ≤ HT05Cst A₀ A * (1 + ‖z‖) ^ 2 := by
        exact mul_le_mul_of_nonneg_right h1 h2

/-- Invertibility of the operator-valued difference throughout `G`. -/
lemma isUnit_operatorMatrixDifference_selfEnergy_on_G {N : ℕ} (A₀ : Matrix d d ℂ)
    (A : ι → Matrix d d ℂ) (hA₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian)
    (hN : 0 < N) {z : ℂ} (hz : z ∈ goodRegionG N A₀ A) :
    IsUnit (operatorMatrixDifference A (selfEnergy (N := N) A₀ A z - A₀)) := by
  have hpos : 0 < z.im := goodRegionG_pos_im N A₀ A z hz
  have hfr := frob_selfEnergy_weighted_le A₀ A hA₀ hA hN hpos
  exact isUnit_operatorMatrixDifference_selfEnergy_pt A₀ A hA₀ hA hfr
    (card_mul_C1_le_Cst A₀ A z) hpos hN (goodRegionG_small A₀ A hz)

/-- The operator-valued resolvent bound throughout `G`. -/
lemma norm_operatorMatrixArgumentResolvent_selfEnergy_on_G {N : ℕ} (A₀ : Matrix d d ℂ)
    (A : ι → Matrix d d ℂ) (hA₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian)
    (hN : 0 < N) {z : ℂ} (hz : z ∈ goodRegionG N A₀ A) :
    ‖CStarMatrix.ofMatrix
      (operatorMatrixArgumentResolvent A (selfEnergy (N := N) A₀ A z - A₀))‖ ≤ 2 / z.im := by
  have hpos : 0 < z.im := goodRegionG_pos_im N A₀ A z hz
  have hfr := frob_selfEnergy_weighted_le A₀ A hA₀ hA hN hpos
  exact norm_operatorMatrixArgumentResolvent_selfEnergy_le_pt A₀ A hA₀ hA hfr
    (card_mul_C1_le_Cst A₀ A z) hpos hN (goodRegionG_small A₀ A hz)

/-- **The physical-branch identification on the weighted good region `G`.**

This is `matrixDyson_analytic_unique_of_small_point` run with `U := G` itself: `G` is open and
path-connected, both branches are analytic on it, the Dyson equations hold on it, and the small
point of `exists_small_point_w` lies in `G`. -/
theorem gueResolventMean_eq_operatorMatrixArgumentCauchy_on_G {N : ℕ}
    (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ) (hA₀ : A₀.IsHermitian)
    (hA : ∀ i, (A i).IsHermitian) (hN : 0 < N) :
    Set.EqOn (gueResolventMean (N := N) A₀ A)
      (fun z => operatorMatrixArgumentCauchy A (selfEnergy (N := N) A₀ A z - A₀))
      (goodRegionG N A₀ A) := by
  set U : Set ℂ := goodRegionG N A₀ A with hUdef
  have hUopen : IsOpen U := goodRegionG_isOpen N A₀ A
  have hUconn : IsPreconnected U := goodRegionG_isPreconnected N A₀ A
  have hpos : ∀ z ∈ U, 0 < z.im := goodRegionG_pos_im N A₀ A
  have hUnit : ∀ z ∈ U,
      IsUnit (operatorMatrixDifference A (selfEnergy (N := N) A₀ A z - A₀)) :=
    fun z hz => isUnit_operatorMatrixDifference_selfEnergy_on_G A₀ A hA₀ hA hN hz
  obtain ⟨z₀, hz₀, hsmall₀⟩ := exists_small_point_w A₀ A hA₀ hA hN
  refine matrixDyson_analytic_unique_of_small_point A
    (fun z => selfEnergy (N := N) A₀ A z - A₀) (gueResolventMean (N := N) A₀ A)
    (fun z => operatorMatrixArgumentCauchy A (selfEnergy (N := N) A₀ A z - A₀)) U
    hUopen hUconn
    ((analytic_gueResolventMean A₀ A hA₀ hA hN).mono (fun z hz => hpos z hz))
    (analyticOnNhd_operatorMatrixArgumentCauchy_comp A
      (fun z => selfEnergy (N := N) A₀ A z) A₀ U
      (analyticOnNhd_selfEnergy A₀ A hA₀ hA hN hpos
        (fun z hz => gueResolventMean_isUnit A₀ A hA₀ hA z (hpos z hz) hN))
      hUnit)
    (fun z hz => by
      rw [selfEnergy_sub_A₀_sub_covariance]
      exact gueResolventMean_inv_mul A₀ A hA₀ hA z (hpos z hz) hN)
    (fun z hz => operatorMatrixArgumentCauchy_dyson A
      (selfEnergy (N := N) A₀ A z - A₀) (hUnit z hz))
    z₀ hz₀ hsmall₀


/-! ## Discharging the weighted interface -/

/-- **The weighted interface `HT05Inputs'` holds unconditionally** for Hermitian pencils, with the
explicit frozen constants of this file. -/
theorem HT05Inputs'_of_unconditional (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    (hA₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian)
    {η₀ : ℝ} (hη₀ : 2 < η₀) :
    HT05Inputs' A₀ A η₀ (HT05Cst A₀ A) := by
  constructor
  · filter_upwards [Filter.eventually_gt_atTop (0 : ℕ)] with N hN z hz hlt
    refine (frob_selfEnergy_weighted_le A₀ A hA₀ hA hN hz).trans ?_
    have hC1 : HT05C1 A₀ A ≤ HT05Cst A₀ A := HT05Cst_ge_C1 A₀ A
    have h2 : 0 ≤ (1 + ‖z‖) ^ 2 * z.im ^ (-(5 : ℝ)) / (N : ℝ) ^ 2 := by positivity
    calc HT05C1 A₀ A * (1 + ‖z‖) ^ 2 * z.im ^ (-(5 : ℝ)) / (N : ℝ) ^ 2
        = HT05C1 A₀ A * ((1 + ‖z‖) ^ 2 * z.im ^ (-(5 : ℝ)) / (N : ℝ) ^ 2) := by ring
      _ ≤ HT05Cst A₀ A * ((1 + ‖z‖) ^ 2 * z.im ^ (-(5 : ℝ)) / (N : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_right hC1 h2
      _ = HT05Cst A₀ A * (1 + ‖z‖) ^ 2 * z.im ^ (-(5 : ℝ)) / (N : ℝ) ^ 2 := by ring
  · filter_upwards [Filter.eventually_gt_atTop (0 : ℕ)] with N hN z hz hlt hsmall
    have hzG : z ∈ goodRegionG N A₀ A := by
      simp only [goodRegionG, goodRegion, Set.mem_ofPred_eq]
      refine ⟨hz, ?_⟩
      rw [Real.rpow_neg hz.le, Real.rpow_ofNat] at hsmall
      calc HT05Cst A₀ A * (1 + ‖z‖) ^ 2 * ((N : ℝ) ^ 2)⁻¹ * ((z.im) ^ 6)⁻¹
          = HT05Cst A₀ A * (1 + ‖z‖) ^ 2 * ((z.im) ^ 6)⁻¹ / (N : ℝ) ^ 2 := by ring
        _ < 1 / 2 := hsmall
    exact ⟨gueResolventMean_eq_operatorMatrixArgumentCauchy_on_G A₀ A hA₀ hA hN hzG,
      isUnit_operatorMatrixDifference_selfEnergy_on_G A₀ A hA₀ hA hN hzG,
      norm_operatorMatrixArgumentResolvent_selfEnergy_on_G A₀ A hA₀ hA hN hzG⟩

/-- **THE PROJECT TARGET FROM THE SELF-ENERGY BRANCH.**

For every `r`, the almost-sure strong convergence statement holds, with no hypotheses other than
`r`: the weighted interface `HT05Inputs'` is discharged at each canonical pencil coefficient by
`HT05Inputs'_of_unconditional`. -/
theorem GUEStrongConvergenceStatement_of_selfEnergy (r : ℕ) :
    GUEStrongConvergenceStatement r := by
  refine GUEStrongConvergenceStatement_of_HT05Inputs' r (fun k F z => ?_)
  haveI : Nonempty (Fin (pencilCoeffDim k F)) := ⟨⟨0, pencilCoeffDim_pos r k F⟩⟩
  refine ⟨3, HT05Cst (pencilConstCoeff k F z) (pencilDirCoeff k F), by norm_num,
    (HT05Cst_pos _ _).le, ?_⟩
  exact HT05Inputs'_of_unconditional (pencilConstCoeff k F z) (pencilDirCoeff k F)
    (pencilConstCoeff_isHermitian k F z) (pencilDirCoeff_isHermitian k F) (by norm_num)

end

end GUEStrongConvergence
