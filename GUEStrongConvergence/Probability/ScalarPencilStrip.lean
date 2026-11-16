/-
# The scalar weighted-strip bound at the canonical `d = 1` pencil, unconditionally

`Probability/ScalarLoopSignComplete.lean` proves the threshold-free strip bound for the
`Unit`/`Unit` scalar GUE pencil `(gueScalarA₀, gueScalarA)`.  The corrected endgame bundle
(`StrongConvergence/CorrectedEndgame.lean`) needs the same bound at the canonical scalar pencils
`(0 : Matrix (Fin 1) (Fin 1) ℂ)` and `scalarPencilCoeff i`, and in the *honest* exponent-`7`
weighted form `WeightedStripBoundProven A₀ A η₀ Kc C_s`.

This file provides:

1. `weightedStripBoundProven_of_weightedStripBound_five` — the conversion
   `WeightedStripBound A₀ A k η₀ C_s 5 → WeightedStripBoundProven A₀ A η₀ 1 (C_s * max 1 η₀²)`,
   using `|Im z|⁻⁵ = |Im z|² |Im z|⁻⁷`, `|Im z|² ≤ η₀²` and `(1 + ‖z‖)² ≥ 1`.

2. `norm_sub_le_of_scalar_loop` — the complex-analytic core of the loop bootstrap, abstract in
   the measure space, the partial trace `T`, its mean `m` and the limit `g`: from
   `m = ∫ T`, the exact scalar loop data `z m - 1 = ∫ T²`, `(z - g) g = 1`, the two sign facts and
   a variance bound `∫ ‖T - m‖² ≤ C`, it concludes `‖m - g‖ ≤ C / |Im z|`.  It is the shared
   engine behind both the `Unit`/`Unit` and the `Fin 1`/`Fin r` instantiations.

3. `integral_norm_sq_fluctuation_le_sharp_abs` — the sharp variance bound
   `∫ ‖T_N(z)_{uu} - E T_N(z)_{uu}‖² ≤ 4 (gueScale N)² (∑ ‖A_i‖_F²) |Im z|⁻⁴ / N` for **every**
   nonreal `z` (the lower half-plane follows from the upper one at `z̄` by conjugation symmetry).

4. The `Fin 1`/`Fin r` scalar pencil: the exact Schwinger--Dyson identity
   `scalarPencilLoopEquation`, the limit Dyson equation `scalarPencilLimitDyson`, the sharp
   variance bound `scalarPencilVarianceLe`, the full strip bound
   `weightedStripBound_scalarPencil`, its honest weighted form
   `weightedStripBoundProven_scalarPencil`, and finally

   **`scalarWeightedStripDataAtRepair_unconditional`** : for every `r`, `i : Fin r` and `ε > 0`,
   `ScalarWeightedStripDataAtRepair r i ε`.

   Hence the scalar field of the corrected endgame bundle `WeightedStripInputsRepair` is
   discharged unconditionally, leaving only the pencil (matrix-coefficient) field.
-/
import GUEStrongConvergence.Probability.ScalarLoopSignComplete
import GUEStrongConvergence.Probability.SharpTwoPoint
import GUEStrongConvergence.Probability.ResolventConj
import GUEStrongConvergence.StrongConvergence.CorrectedEndgame

open MeasureTheory ProbabilityTheory Matrix Filter
open FreeProbability FreeProbability.Fock
open scoped Matrix.Norms.Frobenius ComplexOrder ENNReal NNReal Topology

set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000

namespace GUEStrongConvergence

variable {ι d : Type*} {N : ℕ} [Fintype ι] [Fintype d] [DecidableEq d] [DecidableEq ι]
variable {r : ℕ}

noncomputable section

/-! ### 1. From the `β = 5` strip bound to the honest weighted `|Im z|⁻⁷` bound -/

/-- **Conversion to the honest weighted strip bound.**  On the strip `|Im z| < η₀`,
`|Im z|⁻⁵ = |Im z|² |Im z|⁻⁷ ≤ η₀² |Im z|⁻⁷`, and the polynomial weight satisfies
`(1 + ‖z‖)² ≥ 1`.  Hence the `β = 5` bound implies the honest `|Im z|⁻⁷` bound with
`Kc = 1` and `C_s' = C_s * max 1 η₀²`. -/
theorem weightedStripBoundProven_of_weightedStripBound_five
    (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ) (k : ℕ) {η₀ C_s : ℝ}
    (hC_s : 0 ≤ C_s) (h : WeightedStripBound A₀ A k η₀ C_s 5) :
    WeightedStripBoundProven A₀ A η₀ 1 (C_s * max 1 (η₀ ^ 2)) := by
  filter_upwards [h] with N hN z hz hlt
  have hx : 0 < |z.im| := abs_pos.mpr hz
  have hx2 : |z.im| ^ (2 : ℝ) = |z.im| ^ 2 := Real.rpow_two _
  have hsplit : |z.im| ^ (-5 : ℝ) = |z.im| ^ (-7 : ℝ) * |z.im| ^ 2 := by
    rw [show (-5 : ℝ) = -7 + 2 by norm_num, Real.rpow_add hx, hx2]
  have hle2 : |z.im| ^ 2 ≤ η₀ ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hlt.le 2
  have hηnn : (0 : ℝ) ≤ η₀ := le_trans (abs_nonneg _) hlt.le
  have hmaxnn : (0 : ℝ) ≤ max 1 (η₀ ^ 2) := le_trans zero_le_one (le_max_left _ _)
  have hX : 0 ≤ |z.im| ^ (-7 : ℝ) := Real.rpow_nonneg (abs_nonneg _) _
  have hw : (1 : ℝ) ≤ (1 + ‖z‖) ^ 2 := by
    have h1 : (1 : ℝ) ≤ 1 + ‖z‖ := le_add_of_nonneg_right (norm_nonneg _)
    nlinarith [norm_nonneg z]
  have hprod : (0 : ℝ) ≤ C_s * max 1 (η₀ ^ 2) := mul_nonneg hC_s hmaxnn
  have hcoef : C_s * η₀ ^ 2 ≤ (C_s * max 1 (η₀ ^ 2)) * (1 + ‖z‖) ^ 2 := by
    have h1 : C_s * η₀ ^ 2 ≤ C_s * max 1 (η₀ ^ 2) :=
      mul_le_mul_of_nonneg_left (le_max_right _ _) hC_s
    have h2 : C_s * max 1 (η₀ ^ 2) ≤ (C_s * max 1 (η₀ ^ 2)) * (1 + ‖z‖) ^ 2 := by
      nlinarith [hprod, hw]
    linarith
  calc frob (gueResolventMean (N := N) A₀ A z - operatorMatrixPencilCauchy A₀ A z)
      ≤ C_s * |z.im| ^ (-5 : ℝ) / (N : ℝ) ^ 2 := hN z hz hlt
    _ = C_s * (|z.im| ^ (-7 : ℝ) * |z.im| ^ 2) / (N : ℝ) ^ 2 := by rw [hsplit]
    _ ≤ C_s * (|z.im| ^ (-7 : ℝ) * η₀ ^ 2) / (N : ℝ) ^ 2 := by
        gcongr
    _ = C_s * η₀ ^ 2 * |z.im| ^ (-7 : ℝ) / (N : ℝ) ^ 2 := by ring
    _ ≤ (C_s * max 1 (η₀ ^ 2)) * (1 + ‖z‖) ^ 2 * |z.im| ^ (-7 : ℝ) / (N : ℝ) ^ 2 := by
        rw [show C_s * η₀ ^ 2 * |z.im| ^ (-7 : ℝ)
              = (C_s * η₀ ^ 2) * |z.im| ^ (-7 : ℝ) by ring,
          show (C_s * max 1 (η₀ ^ 2)) * (1 + ‖z‖) ^ 2 * |z.im| ^ (-7 : ℝ)
              = ((C_s * max 1 (η₀ ^ 2)) * (1 + ‖z‖) ^ 2) * |z.im| ^ (-7 : ℝ) by ring]
        exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hcoef hX) (sq_nonneg _)

/-! ### 2. The complex core of the loop bootstrap -/

/-- **Abstract loop bootstrap.**  Given a probability space `(α, μ)`, a complex function `T`
with mean `m`, the exact finite-`N` scalar loop data `z m - 1 = ∫ T²`, the limit Dyson equation
`(z - g) g = 1`, the two sign facts, and a variance bound `∫ ‖T - m‖² ≤ C`, one has
`‖m - g‖ ≤ C / |Im z|`.

No threshold on `|Im z|` is used: the denominator `z - m - g` has `|Im(z - m - g)| ≥ |Im z|`
because both imaginary parts have the sign opposite to `Im z`. -/
theorem norm_sub_le_of_scalar_loop {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsProbabilityMeasure μ] {T : α → ℂ} {m g z : ℂ} {C : ℝ} (hz : z.im ≠ 0)
    (hTint : Integrable T μ) (hT2int : Integrable (fun x => T x * T x) μ)
    (hmT : m = ∫ x, T x ∂μ)
    (hSD : z * m - 1 = ∫ x, T x * T x ∂μ)
    (hg : (z - g) * g = 1)
    (hmsign : z.im * m.im ≤ 0) (hgsign : z.im * g.im ≤ 0)
    (hVar : ∫ x, ‖T x - m‖ ^ 2 ∂μ ≤ C) :
    ‖m - g‖ ≤ C / |z.im| := by
  -- the variance is the integral of the squared fluctuation
  have hvar : (∫ x, T x * T x ∂μ) - m ^ 2 = ∫ x, (T x - m) ^ 2 ∂μ := by
    have hexp : ∀ x, (T x - m) ^ 2 = T x * T x - m * T x - T x * m + m * m := by
      intro x; ring
    rw [show (∫ x, (T x - m) ^ 2 ∂μ)
        = ∫ x, (T x * T x - m * T x - T x * m + m * m) ∂μ from
        integral_congr_ae (ae_of_all _ hexp)]
    have hiA : Integrable (fun x => T x * T x) μ := hT2int
    have hiB : Integrable (fun x => m * T x) μ := hTint.const_mul m
    have hiC : Integrable (fun x => T x * m) μ := hTint.mul_const m
    have hiD : Integrable (fun _ : α => m * m) μ := integrable_const (m * m)
    have hiAB : Integrable (fun x => T x * T x - m * T x) μ := hiA.sub hiB
    have hiABC : Integrable (fun x => T x * T x - m * T x - T x * m) μ := hiAB.sub hiC
    rw [integral_add hiABC hiD, integral_sub hiAB hiC, integral_sub hiA hiB,
      integral_const_mul, integral_mul_const, integral_const]
    rw [← hmT]
    simp
    ring
  have hm_eq : z * m - 1 - m ^ 2 = ∫ x, (T x - m) ^ 2 ∂μ := by
    linear_combination hSD + hvar
  have hid : (m - g) * (z - m - g) = ∫ x, (T x - m) ^ 2 ∂μ :=
    loop_identity_of_dyson hg hm_eq
  have hbs : ‖m - g‖ ≤ (‖∫ x, (T x - m) ^ 2 ∂μ‖) / |z.im| :=
    loop_bootstrap hz hid hmsign hgsign
  have hVar_le : ‖∫ x, (T x - m) ^ 2 ∂μ‖ ≤ C := by
    calc ‖∫ x, (T x - m) ^ 2 ∂μ‖ ≤ ∫ x, ‖(T x - m) ^ 2‖ ∂μ :=
          norm_integral_le_integral_norm _
      _ = ∫ x, ‖T x - m‖ ^ 2 ∂μ := by
          refine integral_congr_ae (ae_of_all _ fun x => ?_)
          exact norm_pow _ 2
      _ ≤ C := hVar
  calc ‖m - g‖ ≤ (‖∫ x, (T x - m) ^ 2 ∂μ‖) / |z.im| := hbs
    _ ≤ C / |z.im| := div_le_div_of_nonneg_right hVar_le (abs_nonneg _)

/-! ### 3. The sharp variance bound for every nonreal `z` -/

/-- **The sharp pencil variance bound on both half-planes.**  The upper half-plane statement is
`integral_norm_sq_fluctuation_le_sharp`; the lower half-plane follows by conjugation symmetry of
the integrand (`guePartialTrace_star`, `gueResolventMean_star`). -/
theorem integral_norm_sq_fluctuation_le_sharp_abs [Nonempty d]
    (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    (hA₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian)
    (z : ℂ) (hz : z.im ≠ 0) (hN : 0 < N) (u : d) :
    ∫ x, ‖guePartialTrace A₀ A z (x : GUECoord ι N → ℝ) u u -
        gueResolventMean (N := N) A₀ A z u u‖ ^ 2
        ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))
      ≤ 4 * (gueScale N) ^ 2 * (∑ i, (frob (A i)) ^ 2) * |z.im|⁻¹ ^ 4 / (N : ℝ) := by
  rcases lt_or_gt_of_ne hz with hneg | hpos
  · have hzpos : 0 < (star z).im := by simpa [Complex.star_def] using hneg
    have h := integral_norm_sq_fluctuation_le_sharp A₀ A hA₀ hA (star z) hzpos hN u u
    have hinteq : (∫ x, ‖guePartialTrace A₀ A z (x : GUECoord ι N → ℝ) u u -
          gueResolventMean (N := N) A₀ A z u u‖ ^ 2
          ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N))))
        = ∫ x, ‖guePartialTrace A₀ A (star z) (x : GUECoord ι N → ℝ) u u -
            gueResolventMean (N := N) A₀ A (star z) u u‖ ^ 2
            ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) := by
      refine integral_congr_ae (ae_of_all _ fun x => ?_)
      show ‖guePartialTrace A₀ A z (x : GUECoord ι N → ℝ) u u -
          gueResolventMean (N := N) A₀ A z u u‖ ^ 2
        = ‖guePartialTrace A₀ A (star z) (x : GUECoord ι N → ℝ) u u -
          gueResolventMean (N := N) A₀ A (star z) u u‖ ^ 2
      have h1 : guePartialTrace A₀ A (star z) (x : GUECoord ι N → ℝ) u u
          = star (guePartialTrace A₀ A z (x : GUECoord ι N → ℝ) u u) :=
        guePartialTrace_star A₀ A hA₀ hA x z u u
      have h2 : gueResolventMean (N := N) A₀ A (star z) u u
          = star (gueResolventMean (N := N) A₀ A z u u) := by
        have h := gueResolventMean_star (N := N) A₀ A hA₀ hA z
        calc gueResolventMean (N := N) A₀ A (star z) u u
            = (star (gueResolventMean (N := N) A₀ A z)) u u := by rw [← h]
          _ = star (gueResolventMean (N := N) A₀ A z u u) := Matrix.star_apply _ u u
      rw [h1, h2, ← star_sub, norm_star]
    rw [hinteq]
    refine h.trans (le_of_eq ?_)
    have hpow : ((star z).im)⁻¹ ^ 4 = |z.im|⁻¹ ^ 4 := by
      rw [Complex.star_def, Complex.conj_im, abs_of_neg hneg]
    rw [hpow]
  · have h := integral_norm_sq_fluctuation_le_sharp A₀ A hA₀ hA z hpos hN u u
    simpa [abs_of_pos hpos] using h


/-! ### 4. The canonical scalar pencil at `d = Fin 1` -/

/-- The Frobenius norm of the `1 × 1` identity is `1`. -/
lemma frob_one_fin_one : frob (1 : Matrix (Fin 1) (Fin 1) ℂ) = 1 := by
  have h2 : (frob (1 : Matrix (Fin 1) (Fin 1) ℂ)) ^ 2 = 1 := by
    rw [frob_sq]
    simp
  calc frob (1 : Matrix (Fin 1) (Fin 1) ℂ)
      = Real.sqrt ((frob (1 : Matrix (Fin 1) (Fin 1) ℂ)) ^ 2) :=
        (Real.sqrt_sq (frob_nonneg _)).symm
    _ = Real.sqrt 1 := by rw [h2]
    _ = 1 := Real.sqrt_one

/-- The Frobenius norm of a `1 × 1` matrix is the modulus of its only entry. -/
lemma frob_fin_one_eq (M : Matrix (Fin 1) (Fin 1) ℂ) : frob M = ‖M 0 0‖ := by
  have h2 : (frob M) ^ 2 = ‖M 0 0‖ ^ 2 := by
    rw [frob_sq]
    simp
  calc frob M = Real.sqrt ((frob M) ^ 2) := (Real.sqrt_sq (frob_nonneg _)).symm
    _ = Real.sqrt (‖M 0 0‖ ^ 2) := by rw [h2]
    _ = ‖M 0 0‖ := Real.sqrt_sq (norm_nonneg _)

/-- Entry form of `scalarPencilCoeff`: only the `i`-th coefficient is nonzero. -/
lemma scalarPencilCoeff_apply_zero (i j : Fin r) :
    scalarPencilCoeff i j 0 0 = if j = i then 1 else 0 := by
  by_cases h : j = i
  · simp [scalarPencilCoeff, h]
  · simp [scalarPencilCoeff, h]

/-- The coefficient sum `∑_j ‖A_j‖_F²` of the scalar pencil is `1`. -/
lemma sum_frob_sq_scalarPencilCoeff (i : Fin r) :
    ∑ j, (frob (scalarPencilCoeff i j)) ^ 2 = 1 := by
  rw [Finset.sum_eq_single i]
  · rw [scalarPencilCoeff, ite_eq_left (rfl : i = i), frob_one_fin_one]
    norm_num
  · intro j _ hji
    rw [scalarPencilCoeff, ite_eq_right hji]
    simp [frob]
  · intro h
    exact absurd (Finset.mem_univ i) h

/-- Multiplication of `1 × 1` matrices is scalar multiplication. -/
lemma fin_one_mul_apply_zero (M L : Matrix (Fin 1) (Fin 1) ℂ) :
    (M * L) 0 0 = M 0 0 * L 0 0 := by
  rw [Matrix.mul_apply, Fin.sum_univ_one]

/-- **Exact finite-`N` scalar Schwinger--Dyson equation for the canonical `d = 1` pencil.**
For `A₀ = 0` and `A = scalarPencilCoeff i`, the entry `(0,0)` of the exact finite-`N` matrix
master identity (`gue_dyson_master_identity`) reduces to `z m - 1 = E[T²]`. -/
theorem scalarPencil_loop_equation (z : ℂ) (hz : z.im ≠ 0) (hN : (N : ℂ) ≠ 0) (i : Fin r) :
    z * gueResolventMean (N := N) (0 : Matrix (Fin 1) (Fin 1) ℂ) (scalarPencilCoeff i) z 0 0 - 1
      = ∫ x, guePartialTrace (0 : Matrix (Fin 1) (Fin 1) ℂ) (scalarPencilCoeff i) z x 0 0 *
          guePartialTrace (0 : Matrix (Fin 1) (Fin 1) ℂ) (scalarPencilCoeff i) z x 0 0
        ∂(stdGaussian (EuclideanSpace ℝ (GUECoord (Fin r) N))) := by
  have h := congrArg (fun M : Matrix (Fin 1) (Fin 1) ℂ => M 0 0)
    (gue_dyson_master_identity (0 : Matrix (Fin 1) (Fin 1) ℂ) (scalarPencilCoeff i)
      isHermitian_zero (scalarPencilCoeff_isHermitian i) z hz hN)
  simp only [Matrix.sub_apply, Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply,
    Matrix.sum_apply, Fin.sum_univ_one, ite_true, smul_eq_mul, mul_one, sub_zero] at h
  simp only [scalarPencilCoeff_apply_zero] at h
  rw [Finset.sum_eq_single i] at h
  · simpa using h
  · intro c _ hci
    simp [hci]
  · intro hmem
    exact absurd (Finset.mem_univ i) hmem

/-- **Exact limit Dyson equation for the canonical `d = 1` pencil:**
`(z - g) g = 1` for `g = operatorMatrixPencilCauchy 0 (scalarPencilCoeff i) z 0 0`. -/
theorem scalarPencil_limit_dyson (z : ℂ) (hz : z.im ≠ 0) (i : Fin r) :
    (z - operatorMatrixPencilCauchy (0 : Matrix (Fin 1) (Fin 1) ℂ) (scalarPencilCoeff i) z 0 0) *
      operatorMatrixPencilCauchy (0 : Matrix (Fin 1) (Fin 1) ℂ) (scalarPencilCoeff i) z 0 0
      = 1 := by
  have h := congrArg (fun M : Matrix (Fin 1) (Fin 1) ℂ => M 0 0)
    (limit_dyson_equation (0 : Matrix (Fin 1) (Fin 1) ℂ) (scalarPencilCoeff i)
      isHermitian_zero (scalarPencilCoeff_isHermitian i) z hz)
  simp only [Matrix.sub_apply, Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply,
    Matrix.sum_apply, Fin.sum_univ_one, ite_true, smul_eq_mul, mul_one, sub_zero] at h
  simp only [scalarPencilCoeff_apply_zero] at h
  rw [Finset.sum_eq_single i] at h
  · simpa using h
  · intro c _ hci
    simp [hci]
  · intro hmem
    exact absurd (Finset.mem_univ i) hmem

/-- **Sharp scalar variance bound for the canonical `d = 1` pencil**, on both half-planes. -/
theorem scalarPencil_variance_le (z : ℂ) (hz : z.im ≠ 0) (hN : 0 < N) (i : Fin r) :
    ∫ x, ‖guePartialTrace (0 : Matrix (Fin 1) (Fin 1) ℂ) (scalarPencilCoeff i) z x 0 0 -
        gueResolventMean (N := N) (0 : Matrix (Fin 1) (Fin 1) ℂ) (scalarPencilCoeff i) z 0 0‖ ^ 2
        ∂(stdGaussian (EuclideanSpace ℝ (GUECoord (Fin r) N)))
      ≤ 4 * (N : ℝ)⁻¹ ^ 2 * |z.im|⁻¹ ^ 4 := by
  have h := integral_norm_sq_fluctuation_le_sharp_abs (A₀ := (0 : Matrix (Fin 1) (Fin 1) ℂ))
    (A := scalarPencilCoeff i) isHermitian_zero (scalarPencilCoeff_isHermitian i) z hz hN 0
  rw [sum_frob_sq_scalarPencilCoeff i, gueScale_sq] at h
  refine h.trans (le_of_eq ?_)
  rw [div_eq_mul_inv]
  ring

/-- **The threshold-free strip bound for the canonical `d = 1` scalar pencil**, with no
half-plane restriction, `C_s = 4` and `β = 5`. -/
theorem weightedStripBound_scalarPencil (i : Fin r) (η₀ : ℝ) :
    WeightedStripBound (0 : Matrix (Fin 1) (Fin 1) ℂ) (scalarPencilCoeff i) 0 η₀ 4 5 := by
  filter_upwards [Filter.eventually_ge_atTop 1] with N hN z hz _
  have hNpos : 0 < N := by omega
  have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast hNpos.ne'
  have hTint : Integrable (fun x : EuclideanSpace ℝ (GUECoord (Fin r) N) =>
      guePartialTrace (0 : Matrix (Fin 1) (Fin 1) ℂ) (scalarPencilCoeff i) z x 0 0)
      (stdGaussian (EuclideanSpace ℝ (GUECoord (Fin r) N))) :=
    integrable_guePartialTrace_entry_of_im_ne_zero _ _ isHermitian_zero
      (scalarPencilCoeff_isHermitian i) z hz 0 0
  have hcont : Continuous (fun x : EuclideanSpace ℝ (GUECoord (Fin r) N) =>
      guePartialTrace (0 : Matrix (Fin 1) (Fin 1) ℂ) (scalarPencilCoeff i) z x 0 0) :=
    continuous_guePartialTrace_entry _ _ isHermitian_zero (scalarPencilCoeff_isHermitian i)
      z hz 0 0
  have hbound : ∀ x : EuclideanSpace ℝ (GUECoord (Fin r) N),
      ‖guePartialTrace (0 : Matrix (Fin 1) (Fin 1) ℂ) (scalarPencilCoeff i) z x 0 0‖
        ≤ |z.im|⁻¹ :=
    fun x => norm_guePartialTrace_entry_le _ _ isHermitian_zero (scalarPencilCoeff_isHermitian i)
      _ z hz hNpos 0 0
  have hT2int : Integrable (fun x : EuclideanSpace ℝ (GUECoord (Fin r) N) =>
      guePartialTrace (0 : Matrix (Fin 1) (Fin 1) ℂ) (scalarPencilCoeff i) z x 0 0 *
        guePartialTrace (0 : Matrix (Fin 1) (Fin 1) ℂ) (scalarPencilCoeff i) z x 0 0)
      (stdGaussian (EuclideanSpace ℝ (GUECoord (Fin r) N))) := by
    refine Integrable.of_bound ((hcont.mul hcont).aestronglyMeasurable)
      (|z.im|⁻¹ * |z.im|⁻¹) ?_
    filter_upwards with x
    rw [norm_mul]
    exact mul_le_mul (hbound x) (hbound x) (norm_nonneg _) (by positivity)
  have hmain := norm_sub_le_of_scalar_loop
    (μ := stdGaussian (EuclideanSpace ℝ (GUECoord (Fin r) N)))
    (T := fun x : EuclideanSpace ℝ (GUECoord (Fin r) N) =>
      guePartialTrace (0 : Matrix (Fin 1) (Fin 1) ℂ) (scalarPencilCoeff i) z x 0 0)
    (m := gueResolventMean (N := N) (0 : Matrix (Fin 1) (Fin 1) ℂ) (scalarPencilCoeff i) z 0 0)
    (g := operatorMatrixPencilCauchy (0 : Matrix (Fin 1) (Fin 1) ℂ) (scalarPencilCoeff i) z 0 0)
    (C := 4 * (N : ℝ)⁻¹ ^ 2 * |z.im|⁻¹ ^ 4) hz hTint hT2int
    (gueResolventMean_apply _ _ z 0 0) (scalarPencil_loop_equation z hz hNc i)
    (scalarPencil_limit_dyson z hz i)
    (gueResolventMean_im_mul_im_nonpos _ _ isHermitian_zero (scalarPencilCoeff_isHermitian i) z hz 0)
    (operatorMatrixPencilCauchy_im_mul_im_nonpos _ _ isHermitian_zero
      (scalarPencilCoeff_isHermitian i) z hz 0)
    (scalarPencil_variance_le z hz hNpos i)
  rw [frob_fin_one_eq, Matrix.sub_apply]
  refine hmain.trans (le_of_eq ?_)
  have hzabs : (0 : ℝ) < |z.im| := abs_pos.mpr hz
  have hrpow : |z.im| ^ (-5 : ℝ) = (|z.im| ^ 5)⁻¹ := by
    rw [Real.rpow_neg (le_of_lt hzabs), Real.rpow_ofNat]
  rw [hrpow, div_eq_mul_inv, div_eq_mul_inv, inv_pow]
  ring

/-- **The honest weighted strip bound at the canonical `d = 1` pencil**
(`Kc = 1`, `C_s = 4 max 1 η₀²`, exponent `7`), for every `η₀ > 2`. -/
theorem weightedStripBoundProven_scalarPencil (i : Fin r) {η₀ : ℝ} (hη₀ : 2 < η₀) :
    WeightedStripBoundProven (0 : Matrix (Fin 1) (Fin 1) ℂ) (scalarPencilCoeff i)
      η₀ 1 (4 * max 1 (η₀ ^ 2)) :=
  weightedStripBoundProven_of_weightedStripBound_five (0 : Matrix (Fin 1) (Fin 1) ℂ)
    (scalarPencilCoeff i) 0 (by positivity) (weightedStripBound_scalarPencil i η₀)

/-! ### 5. The scalar field of the corrected endgame bundle, unconditionally -/

/-- **The canonical corrected bundle from a `β = 5` strip bound.**  The pencil field of
`WeightedStripInputsRepair` may be supplied in the unweighted `β = 5` form (the shape produced by
the loop bootstrap) instead of the honest `|Im z|⁻⁷` weighted form. -/
theorem weightedStripDataAtRepair_of_stripBound_five (r : ℕ) {k : ℕ}
    (F : RatPolyIdx r (k + 1)) {z ε : ℝ} (hε : 0 < ε) {η₀ C_s : ℝ}
    (hη₀ : 2 < η₀) (hC_s : 0 ≤ C_s)
    (h : WeightedStripBound (pencilConstCoeff k F z) (pencilDirCoeff k F) 0 η₀ C_s 5) :
    WeightedStripDataAtRepair r k F z ε :=
  weightedStripDataAtRepair_of_stripBound (r := r) hε hη₀
    (mul_nonneg hC_s (le_trans zero_le_one (le_max_left _ _)))
    (weightedStripBoundProven_of_weightedStripBound_five _ _ 0 hC_s h)

/-- **The scalar field is discharged unconditionally.**  For every `r`, every `i : Fin r` and
every `ε > 0`, the corrected scalar strip data holds: the strip bound is the theorem
`weightedStripBoundProven_scalarPencil`, and the cutoff conjuncts are Worker B's
`shiftedCutoff_nonempty` at the compact spectrum `spectrum ℝ (semicircularFamily r i)`. -/
theorem scalarWeightedStripDataAtRepair_unconditional (i : Fin r) (ε : ℝ) (hε : 0 < ε) :
    ScalarWeightedStripDataAtRepair r i ε := by
  refine scalarWeightedStripDataAtRepair_of_stripBound (r := r) (i := i) (ε := ε) hε
    (η₀ := 3) (Kc := 1) (C_s := 4 * max 1 ((3 : ℝ) ^ 2)) (by norm_num) (by positivity) ?_
  exact weightedStripBoundProven_scalarPencil i (by norm_num)

/-- **The second (scalar) field of `WeightedStripInputsRepair` holds for every `r`.** -/
theorem scalarField_weightedStripInputsRepair (r : ℕ) :
    ∀ (i : Fin r) (ε : ℝ), 0 < ε → ScalarWeightedStripDataAtRepair r i ε :=
  fun i ε hε => scalarWeightedStripDataAtRepair_unconditional i ε hε

/-- **Reduction of the corrected endgame bundle to its pencil field.**  The scalar field of
`WeightedStripInputsRepair` is now a theorem, so the whole bundle follows from the matrix
(pencil-coefficient) field alone. -/
theorem weightedStripInputsRepair_of_pencilField (r : ℕ)
    (hpencil : ∀ (k : ℕ) (F : RatPolyIdx r (k + 1)) (z ε : ℝ), 0 < ε →
      WeightedStripDataAtRepair r k F z ε) :
    WeightedStripInputsRepair r :=
  ⟨hpencil, fun i ε hε => scalarWeightedStripDataAtRepair_unconditional i ε hε⟩

end

end GUEStrongConvergence
