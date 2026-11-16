/-
# The pencil strip bound above the Dyson threshold

`StrongConvergence/PencilLoop.lean` proves the exact matrix loop identity

`g_N - g = g * (∑ i, A_i * (g_N - g) * A_i) * g_N + g * Var`

and shows that the scalar closed form does not generalise: the linearized operator
`X ↦ g (∑ A_i X A_i) g_N` has to be inverted, with contraction constant
`‖g‖ (∑ frob(A_i)²) ‖g_N‖`.  Above the `dyson_stability` threshold that contraction is available,
and the exact identity acquires a *quantitative* form.

This file assembles the **above-threshold pencil strip bound** from

* the exact finite-`N` defect identity (the Dyson defect of `g_N` is exactly the fluctuation
  `Var`, `gue_dyson_master_identity`),
* `dyson_stability` (`Probability/DysonLimit.lean`) for the inversion,
* the sharp fluctuation bound `frob_fluctuation_le_sharp` (`PencilLoop.lean`),

giving `frob (g_N(z) - g(z)) ≤ 8 (card d)³ (∑ frob(A_i)²)² |Im z|⁻⁵ / N²` for every nonreal `z`
with `|Im z|` at least the Dyson threshold `dysonThreshold A`, on **both** half-planes.

The mass at the real axis (the near-axis annulus `|Im z| < dysonThreshold A`) is *not* covered:
`PencilLoop.lean` identifies the operator that would have to be inverted there, and no sign
argument suffices.  `weightedStripBoundProven_of_annulus` therefore states the honest
`WeightedStripBoundProven` with the annulus as the only remaining hypothesis.

No `sorry`, no new axioms.
-/
import GUEStrongConvergence.StrongConvergence.PencilLoop
import GUEStrongConvergence.Probability.StripAnalytic
import GUEStrongConvergence.Probability.ResolventConj
import GUEStrongConvergence.Probability.ScalarLoopSignComplete

open Filter MeasureTheory ProbabilityTheory Matrix
open FreeProbability FreeProbability.Fock
open scoped Matrix.Norms.Frobenius ComplexOrder ENNReal NNReal Topology BigOperators

namespace GUEStrongConvergence

noncomputable section

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 4000000

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {d : Type*} [Fintype d] [DecidableEq d]
  [Nonempty d] {N : ℕ}

/-- The coefficient mass `S = ∑ i, frob(A_i)²` of the pencil. -/
def pencilCoeffMass (A : ι → Matrix d d ℂ) : ℝ := ∑ i, (frob (A i)) ^ 2

lemma pencilCoeffMass_nonneg (A : ι → Matrix d d ℂ) : 0 ≤ pencilCoeffMass A :=
  Finset.sum_nonneg fun i _ => sq_nonneg _

/-- **The Dyson threshold** `max 1 √(2 (card d)² S)`: above it the `dyson_stability` contraction
`2 (card d)² S ≤ |Im z|²` holds. -/
def dysonThreshold (A : ι → Matrix d d ℂ) : ℝ :=
  max 1 (Real.sqrt (2 * (Fintype.card d : ℝ) ^ 2 * pencilCoeffMass A))

lemma one_le_dysonThreshold (A : ι → Matrix d d ℂ) : 1 ≤ dysonThreshold A :=
  le_max_left _ _

lemma dysonThreshold_pos (A : ι → Matrix d d ℂ) : 0 < dysonThreshold A :=
  lt_of_lt_of_le one_pos (one_le_dysonThreshold A)

/-- The `dyson_stability` contraction threshold holds above `dysonThreshold`. -/
lemma dysonThreshold_sq_ge (A : ι → Matrix d d ℂ) :
    2 * (Fintype.card d : ℝ) ^ 2 * pencilCoeffMass A ≤ (dysonThreshold A) ^ 2 := by
  set c : ℝ := (Fintype.card d : ℝ) with hc
  have hc0 : 0 ≤ c := le_of_lt card_pos_real
  have hS := pencilCoeffMass_nonneg A
  have harg : 0 ≤ 2 * c ^ 2 * pencilCoeffMass A := by positivity
  have hsqrt : (Real.sqrt (2 * c ^ 2 * pencilCoeffMass A)) ^ 2
      = 2 * c ^ 2 * pencilCoeffMass A := Real.sq_sqrt harg
  have hle : Real.sqrt (2 * c ^ 2 * pencilCoeffMass A) ≤ dysonThreshold A :=
    le_max_right _ _
  have hnn : 0 ≤ Real.sqrt (2 * c ^ 2 * pencilCoeffMass A) := Real.sqrt_nonneg _
  nlinarith [dysonThreshold_pos A]

/-! ## 1. The Dyson defect of `g_N` is exactly the fluctuation -/

/-- **The finite-`N` mean solves the Dyson equation up to the fluctuation.**

With `m = g_N(z)` and `Var = ∑ i, A_i * (E[T_N A_i T_N] - m A_i m)`,

`(z • 1 - A₀ - ∑ i, A_i m A_i) * m = 1 + Var`.

This is `gue_dyson_master_identity` rewritten; it is the input `hg'` of `dyson_stability`. -/
theorem gueResolventMean_dyson_defect (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    (hA₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian)
    (z : ℂ) (hz : z.im ≠ 0) (hN : 0 < N) :
    (z • (1 : Matrix d d ℂ) - A₀ - ∑ i, A i * gueResolventMean (N := N) A₀ A z * A i) *
        gueResolventMean (N := N) A₀ A z
      = 1 + ∑ i, A i * (gueSecondMoment (N := N) A₀ A (A i) z -
          gueResolventMean (N := N) A₀ A z * A i * gueResolventMean (N := N) A₀ A z) := by
  classical
  have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  set m : Matrix d d ℂ := gueResolventMean (N := N) A₀ A z with hm
  have h1 : (z • (1 : Matrix d d ℂ) - A₀) * m - 1
      = ∑ i, A i * gueSecondMoment (N := N) A₀ A (A i) z := by
    rw [hm]
    exact gue_dyson_master_identity A₀ A hA₀ hA z hz hNc
  have hBm : (z • (1 : Matrix d d ℂ) - A₀) * m
      = 1 + ∑ i, A i * gueSecondMoment (N := N) A₀ A (A i) z := by
    have hh := sub_eq_iff_eq_add.mp h1
    rwa [add_comm] at hh
  have hVar : (∑ i, A i * gueSecondMoment (N := N) A₀ A (A i) z) -
        (∑ i, A i * m * A i) * m
      = ∑ i, A i * (gueSecondMoment (N := N) A₀ A (A i) z - m * A i * m) := by
    rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by noncomm_ring
  rw [sub_mul, hBm, ← hVar]
  abel

/-! ## 2. Above the Dyson threshold: the pencil strip bound -/

/-- `a⁻⁵` as a natural power of `a⁻¹` (for `a > 0`). -/
lemma rpow_neg_five_eq_of_pos {a : ℝ} (ha : 0 < a) :
    a ^ (-(5 : ℝ)) = (a⁻¹) ^ 5 := by
  rw [Real.rpow_neg (le_of_lt ha) (5 : ℝ)]
  have h5 : a ^ (5 : ℝ) = a ^ 5 := Real.rpow_natCast a 5
  rw [h5]
  exact (inv_pow a 5).symm

/-- `(Im z)⁻⁵` as a natural power of `(Im z)⁻¹`. -/
lemma rpow_neg_five_eq {z : ℂ} (hz : 0 < z.im) :
    z.im ^ (-(5 : ℝ)) = ((z.im)⁻¹) ^ 5 :=
  rpow_neg_five_eq_of_pos hz

/-- **The pencil comparison above the `dyson_stability` threshold.**

For `z` in the upper half-plane with `2 (card d)² S ≤ (Im z)²` (the `dyson_stability`
contraction), the exact defect identity and the sharp fluctuation bound give

`frob (g_N(z) - g(z)) ≤ 8 (card d)³ S² (Im z)⁻⁵ / N²`,  `S = ∑ i, frob(A_i)²`. -/
theorem frob_sub_le_of_dyson_threshold (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    (hA₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian)
    (z : ℂ) (hz : 0 < z.im) (hN : 0 < N)
    (hη : 2 * (Fintype.card d : ℝ) ^ 2 * pencilCoeffMass A ≤ (z.im) ^ 2) :
    frob (gueResolventMean (N := N) A₀ A z - operatorMatrixPencilCauchy A₀ A z)
      ≤ 8 * (Fintype.card d : ℝ) ^ 3 * (pencilCoeffMass A) ^ 2 *
          ((z.im)⁻¹) ^ 5 / (N : ℝ) ^ 2 := by
  classical
  have hz' : z.im ≠ 0 := ne_of_gt hz
  set m : Matrix d d ℂ := gueResolventMean (N := N) A₀ A z with hm
  set g : Matrix d d ℂ := operatorMatrixPencilCauchy A₀ A z with hg
  set Var : Matrix d d ℂ := ∑ i, A i * (gueSecondMoment (N := N) A₀ A (A i) z - m * A i * m)
    with hVar
  -- the two Dyson equations
  have hg_eq : (z • (1 : Matrix d d ℂ) - A₀ - ∑ i, A i * g * A i) * g = 1 := by
    rw [hg]
    exact limit_dyson_equation A₀ A hA₀ hA z hz'
  have hm_eq : (z • (1 : Matrix d d ℂ) - A₀ - ∑ i, A i * m * A i) * m = 1 + Var := by
    rw [hVar, hm]
    exact gueResolventMean_dyson_defect A₀ A hA₀ hA z hz' hN
  -- the two Frobenius bounds with the same constant
  have hg_b : frob g ≤ (Fintype.card d : ℝ) * (z.im)⁻¹ := by
    rw [hg]
    simpa [abs_of_pos hz] using frob_operatorMatrixPencilCauchy_le A₀ A hA₀ hA z hz'
  have hm_b : frob m ≤ (Fintype.card d : ℝ) * (z.im)⁻¹ := by
    rw [hm]
    exact frob_gueResolventMean_le A₀ A hA₀ hA z hz hN
  have hstab : frob (m - g) ≤ 2 * (Fintype.card d : ℝ) * (z.im)⁻¹ * frob Var :=
    dyson_stability A₀ A z hz g m Var (C := (Fintype.card d : ℝ)) hg_eq hm_eq hg_b hm_b
      (by positivity) (by simpa [pencilCoeffMass] using hη)
  -- the sharp fluctuation bound
  have hfluct : frob Var
      ≤ 2 * (Fintype.card d : ℝ) ^ 2 *
          (2 * (gueScale N) ^ 2 * (pencilCoeffMass A) * ((z.im)⁻¹) ^ 4 / (N : ℝ)) *
          (pencilCoeffMass A) := by
    rw [hVar]
    simpa [pencilCoeffMass] using frob_fluctuation_le_sharp A₀ A hA₀ hA z hz hN
  -- assemble
  calc frob (m - g) ≤ 2 * (Fintype.card d : ℝ) * (z.im)⁻¹ * frob Var := hstab
    _ ≤ 2 * (Fintype.card d : ℝ) * (z.im)⁻¹ *
          (2 * (Fintype.card d : ℝ) ^ 2 *
            (2 * (gueScale N) ^ 2 * (pencilCoeffMass A) * ((z.im)⁻¹) ^ 4 / (N : ℝ)) *
            (pencilCoeffMass A)) := by
        gcongr
    _ = 8 * (Fintype.card d : ℝ) ^ 3 * (pencilCoeffMass A) ^ 2 *
          ((z.im)⁻¹) ^ 5 / (N : ℝ) ^ 2 := by
        rw [gueScale_sq]
        field_simp
        ring

/-- **Above the Dyson threshold**: the hypothesis `2 (card d)² S ≤ (Im z)²` is automatic. -/
theorem frob_sub_le_above_dysonThreshold (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    (hA₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian)
    (z : ℂ) (hz : 0 < z.im) (hN : 0 < N) (hthr : dysonThreshold A ≤ z.im) :
    frob (gueResolventMean (N := N) A₀ A z - operatorMatrixPencilCauchy A₀ A z)
      ≤ 8 * (Fintype.card d : ℝ) ^ 3 * (pencilCoeffMass A) ^ 2 *
          (z.im ^ (-(5 : ℝ))) / (N : ℝ) ^ 2 := by
  have h1 := frob_sub_le_of_dyson_threshold A₀ A hA₀ hA z hz hN ?_
  · rw [rpow_neg_five_eq hz]
    exact h1
  · have h2 : (dysonThreshold A) ^ 2 ≤ (z.im) ^ 2 :=
      pow_le_pow_left₀ (le_of_lt (dysonThreshold_pos A)) hthr 2
    linarith [dysonThreshold_sq_ge A]

/-- **The pencil strip bound above the Dyson threshold, upper half-plane, with the polynomial
weight.**  For every `Kc ≥ 0` and every `z` with `Im z ≥ dysonThreshold A`,

`frob (g_N(z) - g(z)) ≤ 8 (card d)³ S² (Kc + ‖z‖)² (Im z)⁻⁵ / N²`.

The factor `(Kc + ‖z‖)²` is the polynomial weight of `WeightedStripBoundProven`; it is harmless
above the threshold because `(Kc + ‖z‖)² ≥ 1`. -/
theorem pencilStripAbove_upper (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    (hA₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian) {Kc : ℝ} (hKc : 0 ≤ Kc) :
    ∀ᶠ N : ℕ in atTop, ∀ z : ℂ, 0 < z.im → dysonThreshold A ≤ z.im →
      frob (gueResolventMean (N := N) A₀ A z - operatorMatrixPencilCauchy A₀ A z)
        ≤ 8 * (Fintype.card d : ℝ) ^ 3 * (pencilCoeffMass A) ^ 2 *
            (Kc + ‖z‖) ^ 2 * (z.im ^ (-(5 : ℝ))) / (N : ℝ) ^ 2 := by
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN z hz hthr
  have hN0 : 0 < N := lt_of_lt_of_le Nat.zero_lt_one hN
  have hmain := frob_sub_le_above_dysonThreshold A₀ A hA₀ hA z hz hN0 hthr
  have hbase : (1 : ℝ) ≤ (Kc + ‖z‖) ^ 2 := by
    have hz1 : (1 : ℝ) ≤ ‖z‖ := by
      have h1 : (1 : ℝ) ≤ z.im := le_trans (one_le_dysonThreshold A) hthr
      have h2 : z.im ≤ |z.im| := le_abs_self z.im
      have h3 : |z.im| ≤ ‖z‖ := Complex.abs_im_le_norm z
      linarith
    have h0 : (1 : ℝ) ≤ Kc + ‖z‖ := by
      have := norm_nonneg z
      linarith
    calc (1 : ℝ) = 1 ^ 2 := by norm_num
      _ ≤ (Kc + ‖z‖) ^ 2 := pow_le_pow_left₀ zero_le_one h0 2
  have hA0 : (0 : ℝ) ≤ 8 * (Fintype.card d : ℝ) ^ 3 * (pencilCoeffMass A) ^ 2 *
      (z.im ^ (-(5 : ℝ))) := by positivity
  calc frob (gueResolventMean (N := N) A₀ A z - operatorMatrixPencilCauchy A₀ A z)
      ≤ 8 * (Fintype.card d : ℝ) ^ 3 * (pencilCoeffMass A) ^ 2 *
          (z.im ^ (-(5 : ℝ))) / (N : ℝ) ^ 2 := hmain
    _ ≤ 8 * (Fintype.card d : ℝ) ^ 3 * (pencilCoeffMass A) ^ 2 *
          (Kc + ‖z‖) ^ 2 * (z.im ^ (-(5 : ℝ))) / (N : ℝ) ^ 2 := by
        refine div_le_div_of_nonneg_right ?_ (by positivity)
        calc 8 * (Fintype.card d : ℝ) ^ 3 * (pencilCoeffMass A) ^ 2 * (z.im ^ (-(5 : ℝ)))
            = 8 * (Fintype.card d : ℝ) ^ 3 * (pencilCoeffMass A) ^ 2 *
                (z.im ^ (-(5 : ℝ))) * 1 := by ring
          _ ≤ 8 * (Fintype.card d : ℝ) ^ 3 * (pencilCoeffMass A) ^ 2 *
                (z.im ^ (-(5 : ℝ))) * (Kc + ‖z‖) ^ 2 :=
              mul_le_mul_of_nonneg_left hbase hA0
          _ = 8 * (Fintype.card d : ℝ) ^ 3 * (pencilCoeffMass A) ^ 2 *
                (Kc + ‖z‖) ^ 2 * (z.im ^ (-(5 : ℝ))) := by ring

/-! ## 3. The fluctuation bound for every nonreal `z`

The sharp covariance bound `covariance_partialTrace_mul_le_sharp` is stated for `0 < Im z`; the
lower half-plane is transferred here at the level of the *single* fluctuation matrices
`E[T A_i T] - m A_i m`, which are `star`-equivariant (no limit-side conjugation is needed). -/

/-- The matrix second moment of a Hermitian coefficient is `star`-equivariant in the spectral
parameter. -/
theorem gueSecondMoment_star (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    (hA₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian) (B : Matrix d d ℂ)
    (hB : B.IsHermitian) (z : ℂ) :
    gueSecondMoment (N := N) A₀ A B (star z) = star (gueSecondMoment (N := N) A₀ A B z) := by
  have hBstar : star B = B := by
    ext a b
    rw [Matrix.star_apply]
    exact hB.apply a b
  have hmat : ∀ x : GUECoord ι N → ℝ,
      guePartialTrace A₀ A (star z) x * B * guePartialTrace A₀ A (star z) x
        = star (guePartialTrace A₀ A z x * B * guePartialTrace A₀ A z x) := by
    intro x
    have hT : guePartialTrace A₀ A (star z) x = star (guePartialTrace A₀ A z x) := by
      ext u v
      rw [Matrix.star_apply]
      exact guePartialTrace_star A₀ A hA₀ hA x z u v
    rw [hT]
    calc star (guePartialTrace A₀ A z x) * B * star (guePartialTrace A₀ A z x)
        = star (guePartialTrace A₀ A z x) * star B * star (guePartialTrace A₀ A z x) := by
          rw [hBstar]
      _ = star (guePartialTrace A₀ A z x * B * guePartialTrace A₀ A z x) := by
          rw [star_mul, star_mul]
          noncomm_ring
  ext u v
  simp only [gueSecondMoment, Matrix.of_apply, Matrix.star_apply]
  simp only [hmat]
  exact integral_conj

/-- The single fluctuation matrix is `star`-equivariant. -/
theorem gueFluctuation_single_star (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    (hA₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian) (i : ι) (z : ℂ) :
    gueSecondMoment (N := N) A₀ A (A i) (star z) -
        gueResolventMean (N := N) A₀ A (star z) * A i * gueResolventMean (N := N) A₀ A (star z)
      = star (gueSecondMoment (N := N) A₀ A (A i) z -
          gueResolventMean (N := N) A₀ A z * A i * gueResolventMean (N := N) A₀ A z) := by
  have hBstar : star (A i) = A i := by
    ext a b
    rw [Matrix.star_apply]
    exact (hA i).apply a b
  have hm : gueResolventMean (N := N) A₀ A (star z)
      = star (gueResolventMean (N := N) A₀ A z) :=
    (gueResolventMean_star A₀ A hA₀ hA z).symm
  rw [gueSecondMoment_star A₀ A hA₀ hA (A i) (hA i) z, hm]
  calc star (gueSecondMoment (N := N) A₀ A (A i) z) -
        star (gueResolventMean (N := N) A₀ A z) * A i *
          star (gueResolventMean (N := N) A₀ A z)
      = star (gueSecondMoment (N := N) A₀ A (A i) z) -
          star (gueResolventMean (N := N) A₀ A z) * star (A i) *
            star (gueResolventMean (N := N) A₀ A z) := by rw [hBstar]
    _ = star (gueSecondMoment (N := N) A₀ A (A i) z -
          gueResolventMean (N := N) A₀ A z * A i * gueResolventMean (N := N) A₀ A z) := by
        rw [star_sub, star_mul, star_mul]
        noncomm_ring

/-- **The fluctuation bound for every nonreal `z`** (both half-planes). -/
theorem frob_fluctuation_le_sharp_abs (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    (hA₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian)
    (z : ℂ) (hz : z.im ≠ 0) (hN : 0 < N) :
    frob (∑ i, A i * (gueSecondMoment (N := N) A₀ A (A i) z -
        gueResolventMean (N := N) A₀ A z * A i * gueResolventMean (N := N) A₀ A z))
      ≤ 2 * (Fintype.card d : ℝ) ^ 2 *
          (2 * (gueScale N) ^ 2 * (pencilCoeffMass A) * ((z.im)⁻¹) ^ 4 / (N : ℝ)) *
          (pencilCoeffMass A) := by
  classical
  rcases lt_or_gt_of_ne hz with hneg | hpos
  · -- lower half-plane: transfer the sharp covariance bound from `star z`
    have hzpos : 0 < (star z).im := by simpa [Complex.star_def] using hneg
    have hvceq : 2 * (gueScale N) ^ 2 * (∑ i, (frob (A i)) ^ 2) * (((star z).im)⁻¹) ^ 4
          / (N : ℝ)
        = 2 * (gueScale N) ^ 2 * (∑ i, (frob (A i)) ^ 2) * ((z.im)⁻¹) ^ 4 / (N : ℝ) := by
      simp only [Complex.star_def, Complex.conj_im, inv_neg]
      rw [show (-(z.im)⁻¹) ^ 4 = ((z.im)⁻¹) ^ 4 by ring, inv_pow]
    have hterm : ∀ i : ι,
        frob (gueSecondMoment (N := N) A₀ A (A i) z -
          gueResolventMean (N := N) A₀ A z * A i * gueResolventMean (N := N) A₀ A z)
        ≤ 2 * (Fintype.card d : ℝ) ^ 2 * frob (A i) *
            (2 * (gueScale N) ^ 2 * (pencilCoeffMass A) * ((z.im)⁻¹) ^ 4 / (N : ℝ)) := by
      intro i
      have h1 := covariance_partialTrace_mul_le_sharp A₀ A hA₀ hA (star z) hzpos hN (A i) (hA i)
      rw [hvceq] at h1
      have h2 := gueFluctuation_single_star (N := N) A₀ A hA₀ hA i z
      have hfrob : frob (gueSecondMoment (N := N) A₀ A (A i) z -
            gueResolventMean (N := N) A₀ A z * A i * gueResolventMean (N := N) A₀ A z)
          = frob (gueSecondMoment (N := N) A₀ A (A i) (star z) -
              gueResolventMean (N := N) A₀ A (star z) * A i *
                gueResolventMean (N := N) A₀ A (star z)) := by
        rw [h2, frob_star]
      rw [hfrob]
      exact h1
    calc frob (∑ i, A i * (gueSecondMoment (N := N) A₀ A (A i) z -
          gueResolventMean (N := N) A₀ A z * A i * gueResolventMean (N := N) A₀ A z))
        ≤ ∑ i, frob (A i * (gueSecondMoment (N := N) A₀ A (A i) z -
            gueResolventMean (N := N) A₀ A z * A i * gueResolventMean (N := N) A₀ A z)) := by
          simpa using frob_sum_le (Finset.univ : Finset ι) (fun i =>
            A i * (gueSecondMoment (N := N) A₀ A (A i) z -
              gueResolventMean (N := N) A₀ A z * A i * gueResolventMean (N := N) A₀ A z))
      _ ≤ ∑ i, frob (A i) * frob (gueSecondMoment (N := N) A₀ A (A i) z -
            gueResolventMean (N := N) A₀ A z * A i * gueResolventMean (N := N) A₀ A z) :=
          Finset.sum_le_sum fun i _ => frob_mul_le _ _
      _ ≤ ∑ i, frob (A i) * (2 * (Fintype.card d : ℝ) ^ 2 * frob (A i) *
            (2 * (gueScale N) ^ 2 * (pencilCoeffMass A) * ((z.im)⁻¹) ^ 4 / (N : ℝ))) :=
          Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hterm i) (frob_nonneg _)
      _ = 2 * (Fintype.card d : ℝ) ^ 2 *
            (2 * (gueScale N) ^ 2 * (pencilCoeffMass A) * ((z.im)⁻¹) ^ 4 / (N : ℝ)) *
            (pencilCoeffMass A) := by
          have hstep : ∀ i : ι, frob (A i) * (2 * (Fintype.card d : ℝ) ^ 2 * frob (A i) *
              (2 * (gueScale N) ^ 2 * (pencilCoeffMass A) * ((z.im)⁻¹) ^ 4 / (N : ℝ)))
              = (2 * (Fintype.card d : ℝ) ^ 2 *
                  (2 * (gueScale N) ^ 2 * (pencilCoeffMass A) * ((z.im)⁻¹) ^ 4 / (N : ℝ))) *
                (frob (A i)) ^ 2 := fun i => by ring
          calc ∑ i, frob (A i) * (2 * (Fintype.card d : ℝ) ^ 2 * frob (A i) *
                (2 * (gueScale N) ^ 2 * (pencilCoeffMass A) * ((z.im)⁻¹) ^ 4 / (N : ℝ)))
              = ∑ i, (2 * (Fintype.card d : ℝ) ^ 2 *
                  (2 * (gueScale N) ^ 2 * (pencilCoeffMass A) * ((z.im)⁻¹) ^ 4 / (N : ℝ))) *
                  (frob (A i)) ^ 2 := Finset.sum_congr rfl fun i _ => hstep i
            _ = (2 * (Fintype.card d : ℝ) ^ 2 *
                  (2 * (gueScale N) ^ 2 * (pencilCoeffMass A) * ((z.im)⁻¹) ^ 4 / (N : ℝ))) *
                  ∑ i, (frob (A i)) ^ 2 := by rw [Finset.mul_sum]
            _ = 2 * (Fintype.card d : ℝ) ^ 2 *
                  (2 * (gueScale N) ^ 2 * (pencilCoeffMass A) * ((z.im)⁻¹) ^ 4 / (N : ℝ)) *
                  (pencilCoeffMass A) := rfl
  · simpa [pencilCoeffMass] using frob_fluctuation_le_sharp A₀ A hA₀ hA z hpos hN

/-- **Stability of the Dyson map, both half-planes.**  Same as `dyson_stability` with `(im z)⁻¹`
replaced by `|im z|⁻¹`, so it applies for every nonreal `z`. -/
theorem dyson_stability_abs (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ) (z : ℂ)
    (hz : z.im ≠ 0) (g g' D : Matrix d d ℂ) {C : ℝ}
    (hg : (z • (1 : Matrix d d ℂ) - A₀ - ∑ i, A i * g * A i) * g = 1)
    (hg' : (z • (1 : Matrix d d ℂ) - A₀ - ∑ i, A i * g' * A i) * g' = 1 + D)
    (hg_b : frob g ≤ C * |z.im|⁻¹) (hg'_b : frob g' ≤ C * |z.im|⁻¹)
    (hC : 0 ≤ C)
    (hη : 2 * C ^ 2 * (∑ i, (frob (A i)) ^ 2) ≤ |z.im| ^ 2) :
    frob (g' - g) ≤ 2 * C * |z.im|⁻¹ * frob D := by
  classical
  set M : Matrix d d ℂ := z • (1 : Matrix d d ℂ) - A₀ - ∑ i, A i * g * A i with hM
  set L : Matrix d d ℂ := z • (1 : Matrix d d ℂ) - A₀ - ∑ i, A i * g' * A i with hL
  have hgM : M * g = 1 := by rw [hM]; exact hg
  have hLg' : L * g' = 1 + D := by rw [hL]; exact hg'
  have hgM' : g * M = 1 := mul_eq_one_comm.mp hgM
  -- defect identity
  have hML : M - L = ∑ i, A i * (g' - g) * A i := by
    rw [hM, hL]
    rw [show z • (1 : Matrix d d ℂ) - A₀ - ∑ i, A i * g * A i -
          (z • (1 : Matrix d d ℂ) - A₀ - ∑ i, A i * g' * A i)
        = ∑ i, A i * g' * A i - ∑ i, A i * g * A i from by abel]
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_sub, sub_mul]
  have h1 : M * g' = 1 + D + (∑ i, A i * (g' - g) * A i) * g' := by
    rw [show M * g' = L * g' + (M - L) * g' from by
      rw [show (M - L) * g' = M * g' - L * g' from sub_mul M L g']
      abel]
    rw [hLg', hML]
  have hMX : M * (g' - g) = D + ∑ i, A i * (g' - g) * A i * g' := by
    calc M * (g' - g) = M * g' - M * g := mul_sub M g' g
      _ = (1 + D + (∑ i, A i * (g' - g) * A i) * g') - 1 := by rw [h1, hgM]
      _ = D + (∑ i, A i * (g' - g) * A i) * g' := by abel
      _ = D + ∑ i, A i * (g' - g) * A i * g' := by rw [Finset.sum_mul]
  -- the Frobenius estimates
  have hsum_le : frob (∑ i, A i * (g' - g) * A i * g')
      ≤ (∑ i, (frob (A i)) ^ 2) * frob (g' - g) * frob g' := by
    refine (frob_sum_le Finset.univ (fun i => A i * (g' - g) * A i * g')).trans ?_
    have hterm : ∀ i : ι, frob (A i * (g' - g) * A i * g')
        ≤ (frob (A i)) ^ 2 * frob (g' - g) * frob g' := by
      intro i
      calc frob (A i * (g' - g) * A i * g')
          ≤ frob (A i * (g' - g) * A i) * frob g' := frob_mul_le _ _
        _ ≤ (frob (A i) * frob (g' - g) * frob (A i)) * frob g' := by
            refine mul_le_mul_of_nonneg_right ?_ (frob_nonneg _)
            calc frob (A i * (g' - g) * A i)
                ≤ frob (A i * (g' - g)) * frob (A i) := frob_mul_le _ _
              _ ≤ (frob (A i) * frob (g' - g)) * frob (A i) := by
                  exact mul_le_mul_of_nonneg_right (frob_mul_le _ _) (frob_nonneg _)
        _ = (frob (A i)) ^ 2 * frob (g' - g) * frob g' := by ring
    calc (∑ i : ι, frob (A i * (g' - g) * A i * g'))
        ≤ ∑ i : ι, (frob (A i)) ^ 2 * frob (g' - g) * frob g' :=
          Finset.sum_le_sum fun i _ => hterm i
      _ = (∑ i, (frob (A i)) ^ 2) * frob (g' - g) * frob g' := by
          rw [Finset.sum_mul, Finset.sum_mul]
  have hbound : frob (M * (g' - g)) ≤ frob D + (∑ i, (frob (A i)) ^ 2) *
      frob (g' - g) * frob g' := by
    calc frob (M * (g' - g)) = frob (D + ∑ i, A i * (g' - g) * A i * g') := by rw [hMX]
      _ ≤ frob D + frob (∑ i, A i * (g' - g) * A i * g') := frob_add_le _ _
      _ ≤ frob D + (∑ i, (frob (A i)) ^ 2) * frob (g' - g) * frob g' := by
          linarith [hsum_le]
  -- `g' - g = g (M (g' - g))`
  have hXeq : g' - g = g * (M * (g' - g)) := by
    rw [← mul_assoc, hgM', one_mul]
  have hmain : frob (g' - g) ≤ frob g * frob (M * (g' - g)) := by
    conv_lhs => rw [hXeq]
    exact frob_mul_le g (M * (g' - g))
  have hstep : frob (g' - g) ≤ frob g * frob D
      + (frob g * ((∑ i, (frob (A i)) ^ 2) * frob g')) * frob (g' - g) := by
    calc frob (g' - g) ≤ frob g * frob (M * (g' - g)) := hmain
      _ ≤ frob g * (frob D + (∑ i, (frob (A i)) ^ 2) * frob (g' - g) * frob g') :=
          mul_le_mul_of_nonneg_left hbound (frob_nonneg g)
      _ = frob g * frob D
            + (frob g * ((∑ i, (frob (A i)) ^ 2) * frob g')) * frob (g' - g) := by ring
  -- coefficient bound
  have hCt : C ^ 2 * (∑ i, (frob (A i)) ^ 2) * (|z.im|⁻¹) ^ 2 ≤ 1 / 2 := by
    have hη2 : (0:ℝ) < |z.im| ^ 2 := by
      have hzpos : (0:ℝ) < |z.im| := abs_pos.mpr hz
      positivity
    rw [inv_pow, inv_eq_one_div, mul_one_div, div_le_iff₀ hη2]
    nlinarith [hη]
  have hcoef : frob g * ((∑ i, (frob (A i)) ^ 2) * frob g') ≤ 1 / 2 := by
    have hgg : frob g * ((∑ i, (frob (A i)) ^ 2) * frob g')
        ≤ (C * |z.im|⁻¹) * ((∑ i, (frob (A i)) ^ 2) * (C * |z.im|⁻¹)) := by
      have hprod : frob g * frob g' ≤ (C * |z.im|⁻¹) * (C * |z.im|⁻¹) :=
        mul_le_mul hg_b hg'_b (frob_nonneg g') (by positivity)
      calc frob g * ((∑ i, (frob (A i)) ^ 2) * frob g')
          = (∑ i, (frob (A i)) ^ 2) * (frob g * frob g') := by ring
        _ ≤ (∑ i, (frob (A i)) ^ 2) *
              ((C * |z.im|⁻¹) * (C * |z.im|⁻¹)) :=
            mul_le_mul_of_nonneg_left hprod (by positivity)
        _ = (C * |z.im|⁻¹) * ((∑ i, (frob (A i)) ^ 2) * (C * |z.im|⁻¹)) := by ring
    have h1 : (C * |z.im|⁻¹) * ((∑ i, (frob (A i)) ^ 2) * (C * |z.im|⁻¹))
        = C ^ 2 * (∑ i, (frob (A i)) ^ 2) * (|z.im|⁻¹) ^ 2 := by ring
    rw [h1] at hgg
    linarith
  have hlin : (1 / 2 : ℝ) * frob (g' - g) ≤ frob g * frob D := by
    nlinarith [hstep, hcoef, frob_nonneg (g' - g)]
  have hfinal : frob (g' - g) ≤ 2 * (frob g * frob D) := by linarith
  calc frob (g' - g) ≤ 2 * (frob g * frob D) := hfinal
    _ ≤ 2 * (C * |z.im|⁻¹) * frob D := by
        have h2D : 0 ≤ 2 * frob D := mul_nonneg (by norm_num) (frob_nonneg D)
        have h := mul_le_mul_of_nonneg_left hg_b h2D
        nlinarith [h]
    _ = 2 * C * |z.im|⁻¹ * frob D := by ring



/-- **The pencil comparison above the `dyson_stability` threshold, both half-planes.**

For every nonreal `z` with `2 (card d)² S ≤ |Im z|²`,

`frob (g_N(z) - g(z)) ≤ 8 (card d)³ S² |Im z|⁻⁵ / N²`,  `S = ∑ i, frob(A_i)²`. -/
theorem frob_sub_le_of_dyson_threshold_abs (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    (hA₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian)
    (z : ℂ) (hz : z.im ≠ 0) (hN : 0 < N)
    (hη : 2 * (Fintype.card d : ℝ) ^ 2 * pencilCoeffMass A ≤ |z.im| ^ 2) :
    frob (gueResolventMean (N := N) A₀ A z - operatorMatrixPencilCauchy A₀ A z)
      ≤ 8 * (Fintype.card d : ℝ) ^ 3 * (pencilCoeffMass A) ^ 2 *
          (((|z.im|)⁻¹) ^ 5) / (N : ℝ) ^ 2 := by
  classical
  set m : Matrix d d ℂ := gueResolventMean (N := N) A₀ A z with hm
  set g : Matrix d d ℂ := operatorMatrixPencilCauchy A₀ A z with hg
  set Var : Matrix d d ℂ := ∑ i, A i * (gueSecondMoment (N := N) A₀ A (A i) z - m * A i * m)
    with hVar
  have hg_eq : (z • (1 : Matrix d d ℂ) - A₀ - ∑ i, A i * g * A i) * g = 1 := by
    rw [hg]
    exact limit_dyson_equation A₀ A hA₀ hA z hz
  have hm_eq : (z • (1 : Matrix d d ℂ) - A₀ - ∑ i, A i * m * A i) * m = 1 + Var := by
    rw [hVar, hm]
    exact gueResolventMean_dyson_defect A₀ A hA₀ hA z hz hN
  have hg_b : frob g ≤ (Fintype.card d : ℝ) * |z.im|⁻¹ := by
    rw [hg]
    exact frob_operatorMatrixPencilCauchy_le A₀ A hA₀ hA z hz
  have hm_b : frob m ≤ (Fintype.card d : ℝ) * |z.im|⁻¹ := by
    rw [hm]
    exact frob_gueResolventMean_le_abs A₀ A hA₀ hA z hz hN
  have hstab : frob (m - g) ≤ 2 * (Fintype.card d : ℝ) * |z.im|⁻¹ * frob Var :=
    dyson_stability_abs A₀ A z hz g m Var (C := (Fintype.card d : ℝ)) hg_eq hm_eq hg_b hm_b
      (by positivity) (by simpa [pencilCoeffMass] using hη)
  have hfluct : frob Var
      ≤ 2 * (Fintype.card d : ℝ) ^ 2 *
          (2 * (gueScale N) ^ 2 * (pencilCoeffMass A) * ((z.im)⁻¹) ^ 4 / (N : ℝ)) *
          (pencilCoeffMass A) := by
    rw [hVar]
    exact frob_fluctuation_le_sharp_abs A₀ A hA₀ hA z hz hN
  calc frob (m - g) ≤ 2 * (Fintype.card d : ℝ) * |z.im|⁻¹ * frob Var := hstab
    _ ≤ 2 * (Fintype.card d : ℝ) * |z.im|⁻¹ *
          (2 * (Fintype.card d : ℝ) ^ 2 *
            (2 * (gueScale N) ^ 2 * (pencilCoeffMass A) * ((z.im)⁻¹) ^ 4 / (N : ℝ)) *
            (pencilCoeffMass A)) := by
        gcongr
    _ = 8 * (Fintype.card d : ℝ) ^ 3 * (pencilCoeffMass A) ^ 2 *
          (((|z.im|)⁻¹) ^ 5) / (N : ℝ) ^ 2 := by
        have h4 : ((z.im)⁻¹) ^ 4 = ((|z.im|)⁻¹) ^ 4 := by
          rcases lt_trichotomy z.im 0 with h | h | h
          · rw [abs_of_neg h, inv_neg]
            ring
          · exact absurd h hz
          · rw [abs_of_pos h]
        rw [h4, gueScale_sq]
        field_simp
        ring

/-- **Above the Dyson threshold, both half-planes** (the hypothesis `2 (card d)² S ≤ |Im z|²` is
automatic). -/
theorem frob_sub_le_above_dysonThreshold_abs (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    (hA₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian)
    (z : ℂ) (hz : z.im ≠ 0) (hN : 0 < N) (hthr : dysonThreshold A ≤ |z.im|) :
    frob (gueResolventMean (N := N) A₀ A z - operatorMatrixPencilCauchy A₀ A z)
      ≤ 8 * (Fintype.card d : ℝ) ^ 3 * (pencilCoeffMass A) ^ 2 *
          (|z.im| ^ (-(5 : ℝ))) / (N : ℝ) ^ 2 := by
  have h1 := frob_sub_le_of_dyson_threshold_abs A₀ A hA₀ hA z hz hN ?_
  · have hzpos : 0 < |z.im| := abs_pos.mpr hz
    rw [rpow_neg_five_eq_of_pos hzpos]
    exact h1
  · have h2 : (dysonThreshold A) ^ 2 ≤ |z.im| ^ 2 :=
      pow_le_pow_left₀ (le_of_lt (dysonThreshold_pos A)) hthr 2
    linarith [dysonThreshold_sq_ge A]

/-- **The pencil strip bound above the Dyson threshold, both half-planes, with the polynomial
weight.**

For every `Kc ≥ 0`, every nonreal `z` with `|Im z| ≥ dysonThreshold A`,

`frob (g_N(z) - g(z)) ≤ 8 (card d)³ S² (Kc + ‖z‖)² |Im z|⁻⁵ / N²`. -/
theorem pencilStripAbove (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    (hA₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian) {Kc : ℝ} (hKc : 0 ≤ Kc) :
    ∀ᶠ N : ℕ in atTop, ∀ z : ℂ, z.im ≠ 0 → dysonThreshold A ≤ |z.im| →
      frob (gueResolventMean (N := N) A₀ A z - operatorMatrixPencilCauchy A₀ A z)
        ≤ 8 * (Fintype.card d : ℝ) ^ 3 * (pencilCoeffMass A) ^ 2 *
            (Kc + ‖z‖) ^ 2 * (|z.im| ^ (-(5 : ℝ))) / (N : ℝ) ^ 2 := by
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN z hz hthr
  have hN0 : 0 < N := lt_of_lt_of_le Nat.zero_lt_one hN
  have hmain := frob_sub_le_above_dysonThreshold_abs A₀ A hA₀ hA z hz hN0 hthr
  have hbase : (1 : ℝ) ≤ (Kc + ‖z‖) ^ 2 := by
    have hz1 : (1 : ℝ) ≤ ‖z‖ := by
      have h1 : (1 : ℝ) ≤ |z.im| := le_trans (one_le_dysonThreshold A) hthr
      have h3 : |z.im| ≤ ‖z‖ := Complex.abs_im_le_norm z
      linarith
    have h0 : (1 : ℝ) ≤ Kc + ‖z‖ := by
      have := norm_nonneg z
      linarith
    calc (1 : ℝ) = 1 ^ 2 := by norm_num
      _ ≤ (Kc + ‖z‖) ^ 2 := pow_le_pow_left₀ zero_le_one h0 2
  have hA0 : (0 : ℝ) ≤ 8 * (Fintype.card d : ℝ) ^ 3 * (pencilCoeffMass A) ^ 2 *
      (|z.im| ^ (-(5 : ℝ))) := by positivity
  calc frob (gueResolventMean (N := N) A₀ A z - operatorMatrixPencilCauchy A₀ A z)
      ≤ 8 * (Fintype.card d : ℝ) ^ 3 * (pencilCoeffMass A) ^ 2 *
          (|z.im| ^ (-(5 : ℝ))) / (N : ℝ) ^ 2 := hmain
    _ ≤ 8 * (Fintype.card d : ℝ) ^ 3 * (pencilCoeffMass A) ^ 2 *
          (Kc + ‖z‖) ^ 2 * (|z.im| ^ (-(5 : ℝ))) / (N : ℝ) ^ 2 := by
        refine div_le_div_of_nonneg_right ?_ (by positivity)
        calc 8 * (Fintype.card d : ℝ) ^ 3 * (pencilCoeffMass A) ^ 2 * (|z.im| ^ (-(5 : ℝ)))
            = 8 * (Fintype.card d : ℝ) ^ 3 * (pencilCoeffMass A) ^ 2 *
                (|z.im| ^ (-(5 : ℝ))) * 1 := by ring
          _ ≤ 8 * (Fintype.card d : ℝ) ^ 3 * (pencilCoeffMass A) ^ 2 *
                (|z.im| ^ (-(5 : ℝ))) * (Kc + ‖z‖) ^ 2 :=
              mul_le_mul_of_nonneg_left hbase hA0
          _ = 8 * (Fintype.card d : ℝ) ^ 3 * (pencilCoeffMass A) ^ 2 *
                (Kc + ‖z‖) ^ 2 * (|z.im| ^ (-(5 : ℝ))) := by ring

/-- **Reparametrising the exponent from `5` to `7` above the threshold.**

For `|Im z| < η₀`, `|Im z|⁻⁵ = |Im z|⁻⁷ |Im z|² ≤ |Im z|⁻⁷ η₀²`.  Hence the above-threshold
`|Im z|⁻⁵` estimate is an `|Im z|⁻⁷` estimate with constant multiplied by `η₀²`, which is the
shape consumed by `WeightedStripBoundProven`. -/
theorem pencilStripAbove_seven (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    (hA₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian) {Kc η₀ : ℝ} (hKc : 0 ≤ Kc) :
    ∀ᶠ N : ℕ in atTop, ∀ z : ℂ, z.im ≠ 0 → dysonThreshold A ≤ |z.im| → |z.im| < η₀ →
      frob (gueResolventMean (N := N) A₀ A z - operatorMatrixPencilCauchy A₀ A z)
        ≤ 8 * (Fintype.card d : ℝ) ^ 3 * (pencilCoeffMass A) ^ 2 * η₀ ^ 2 *
            (Kc + ‖z‖) ^ 2 * (|z.im| ^ (-(7 : ℝ))) / (N : ℝ) ^ 2 := by
  filter_upwards [pencilStripAbove A₀ A hA₀ hA (Kc := Kc) hKc] with N hN z hz hthr hlt
  have hzpos : 0 < |z.im| := abs_pos.mpr hz
  have hmain := hN z hz hthr
  -- `|z.im|⁻⁵ ≤ |z.im|⁻⁷ η₀²`
  have hsplit : |z.im| ^ (-(5 : ℝ)) = |z.im| ^ (-(7 : ℝ)) * |z.im| ^ (2 : ℝ) := by
    rw [← Real.rpow_add hzpos]
    norm_num
  have h2 : |z.im| ^ (2 : ℝ) ≤ η₀ ^ 2 := by
    rw [Real.rpow_two]
    exact pow_le_pow_left₀ (abs_nonneg _) (le_of_lt hlt) 2
  have hnn : (0 : ℝ) ≤ |z.im| ^ (-(7 : ℝ)) := Real.rpow_nonneg (abs_nonneg _) _
  have hη0 : (0 : ℝ) ≤ η₀ ^ 2 := sq_nonneg _
  refine hmain.trans ?_
  rw [hsplit]
  have hA : (0 : ℝ) ≤ 8 * (Fintype.card d : ℝ) ^ 3 * (pencilCoeffMass A) ^ 2 *
      (Kc + ‖z‖) ^ 2 := by positivity
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  calc 8 * (Fintype.card d : ℝ) ^ 3 * (pencilCoeffMass A) ^ 2 *
        (Kc + ‖z‖) ^ 2 * (|z.im| ^ (-(7 : ℝ)) * |z.im| ^ (2 : ℝ))
      ≤ 8 * (Fintype.card d : ℝ) ^ 3 * (pencilCoeffMass A) ^ 2 *
        (Kc + ‖z‖) ^ 2 * (|z.im| ^ (-(7 : ℝ)) * η₀ ^ 2) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 hnn) hA
    _ = 8 * (Fintype.card d : ℝ) ^ 3 * (pencilCoeffMass A) ^ 2 * η₀ ^ 2 *
        (Kc + ‖z‖) ^ 2 * (|z.im| ^ (-(7 : ℝ))) := by ring

/-- **`WeightedStripBoundProven` from the near-axis annulus alone.**

This is the payoff of the above-threshold estimate: the honest weighted strip hypothesis on the
whole strip follows from the near-axis annulus `|Im z| < dysonThreshold A` (both half-planes)
together with the above-threshold theorems of this file — no lower-half-plane input is needed.

The constants are `max Cn (8 (card d)³ S² η₀²)`. -/
theorem weightedStripBoundProven_of_annulus (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    (hA₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian) {η₀ Kc Cn : ℝ} (hKc : 0 ≤ Kc)
    (hη : dysonThreshold A < η₀)
    (hnear : ∀ᶠ N : ℕ in atTop, ∀ z : ℂ, z.im ≠ 0 → |z.im| < dysonThreshold A →
      frob (gueResolventMean (N := N) A₀ A z - operatorMatrixPencilCauchy A₀ A z)
        ≤ Cn * (Kc + ‖z‖) ^ 2 * (|z.im| ^ (-(7 : ℝ))) / (N : ℝ) ^ 2) :
    WeightedStripBoundProven A₀ A η₀ Kc
      (max Cn (8 * (Fintype.card d : ℝ) ^ 3 * (pencilCoeffMass A) ^ 2 * η₀ ^ 2)) := by
  have habove := pencilStripAbove_seven A₀ A hA₀ hA (Kc := Kc) (η₀ := η₀) hKc
  filter_upwards [hnear, habove] with N hN hn
  intro z hz hlt
  rcases lt_or_ge |z.im| (dysonThreshold A) with h | h
  · refine (hN z hz h).trans ?_
    gcongr
    exact le_max_left _ _
  · refine (hn z hz h hlt).trans ?_
    gcongr
    exact le_max_right _ _

/-- **The corrected endgame bundle from the near-axis annulus alone.**

At the canonical linearization pencils, the corrected bundle `WeightedStripDataAtRepair`
(`StrongConvergence/CorrectedEndgame.lean`) is now inhabited from the annulus data only: the
above-threshold part of the strip is the theorem `pencilStripAbove_seven`.  This supersedes
`weightedStripDataAtRepair_of_nearAxis`, whose hypothesis `hlow` (lower half-plane above the
threshold) is no longer needed. -/
theorem weightedStripDataAtRepair_of_annulus {r k : ℕ} {F : RatPolyIdx r (k + 1)} {z ε : ℝ}
    (hε : 0 < ε) {Cn : ℝ} (hCn : 0 ≤ Cn)
    (hnear : ∀ᶠ N : ℕ in atTop, ∀ w : ℂ, w.im ≠ 0 →
      |w.im| < dysonThreshold (pencilDirCoeff k F) →
      frob (gueResolventMean (N := N) (pencilConstCoeff k F z) (pencilDirCoeff k F) w -
          operatorMatrixPencilCauchy (pencilConstCoeff k F z) (pencilDirCoeff k F) w)
        ≤ Cn * (0 + ‖w‖) ^ 2 * (|w.im| ^ (-(7 : ℝ))) / (N : ℝ) ^ 2) :
    WeightedStripDataAtRepair r k F z ε := by
  haveI : Nonempty (Fin (pencilCoeffDim k F)) := ⟨⟨0, pencilCoeffDim_pos r k F⟩⟩
  refine weightedStripDataAtRepair_of_stripBound (η₀ := dysonThreshold (pencilDirCoeff k F) + 3)
    (Kc := 0) (C_s := max Cn (8 * (Fintype.card (Fin (pencilCoeffDim k F)) : ℝ) ^ 3 *
      (pencilCoeffMass (pencilDirCoeff k F)) ^ 2 * (dysonThreshold (pencilDirCoeff k F) + 3) ^ 2))
    hε ?_ (le_trans hCn (le_max_left _ _)) ?_
  · have h1 := one_le_dysonThreshold (pencilDirCoeff k F)
    linarith
  · exact weightedStripBoundProven_of_annulus (pencilConstCoeff k F z) (pencilDirCoeff k F)
      (pencilConstCoeff_isHermitian k F z) (pencilDirCoeff_isHermitian k F) le_rfl
      (by linarith [one_le_dysonThreshold (pencilDirCoeff k F)]) hnear

end

end GUEStrongConvergence
