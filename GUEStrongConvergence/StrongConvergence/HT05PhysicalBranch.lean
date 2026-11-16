/-
# HT05 physical branch selection (Worker B)

This file develops the *physical / analytic branch selection* part of the HT05
argument, independent of the particular finite-`N` construction of the
self-energy (which lives in `StrongConvergence/HT05FiniteMean.lean`).

The deterministic finite-`N` mean `m = gueResolventMean A₀ A` is compared with
the actual operator-valued matrix-argument Cauchy transform
`operatorMatrixArgumentCauchy A B`.

Main objects:

* `goodRegion N C_A K_A` — the HT05 good region
  `{z | 0 < im z ∧ C_A (K_A + ‖z‖)^2 N^{-2} (im z)^{-6} < 1/2}`;
* `tubeRegion T` — an explicit open, convex, unbounded subset
  `{z | 0 < im z ∧ T < im z ∧ |re z| < 1}` of the good region, used for the
  analytic-branch uniqueness argument;
* `analytic_gueResolventMean` — the averaged resolvent is analytic on the
  upper half-plane (differentiation under the Gaussian integral).
-/
import GUEStrongConvergence.Probability.DysonVariance
import FreeProbability.OperatorValued.MatrixPhysicalBranchUniqueness
import FreeProbability.OperatorValued.MatrixCauchyPhysical

open MeasureTheory ProbabilityTheory Matrix Filter FreeProbability FreeProbability.Fock
open scoped Matrix.Norms.Operator ComplexOrder ENNReal NNReal Topology

set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000

namespace GUEStrongConvergence

noncomputable section

variable {ι d : Type*} {N : ℕ} [Fintype ι] [Fintype d] [DecidableEq d] [DecidableEq ι]

noncomputable local instance ht05BPartialOrder : PartialOrder (WordSpace ι →L[ℂ] WordSpace ι) :=
  CStarAlgebra.spectralOrder _
noncomputable local instance ht05BStarOrderedRing : StarOrderedRing (WordSpace ι →L[ℂ] WordSpace ι) :=
  CStarAlgebra.spectralOrderedRing _

/-! ### The HT05 good region -/

/-- The HT05 good region at fixed `N`: the upper half-plane points where the
self-energy perturbation is a strict contraction. -/
def goodRegion (N : ℕ) (C_A K_A : ℝ) : Set ℂ :=
  {z : ℂ | 0 < z.im ∧ C_A * (K_A + ‖z‖) ^ 2 * ((N : ℝ) ^ 2)⁻¹ * ((z.im) ^ 6)⁻¹ < 1 / 2}

/-- The defining function of the good region, written without denominators so
that it is continuous on all of `ℂ`. -/
def goodRegionLhs (N : ℕ) (C_A K_A : ℝ) (z : ℂ) : ℝ :=
  C_A * (K_A + ‖z‖) ^ 2 * ((N : ℝ) ^ 2)⁻¹ - (1 / 2) * (z.im) ^ 6

lemma continuous_goodRegionLhs (N : ℕ) (C_A K_A : ℝ) :
    Continuous (goodRegionLhs N C_A K_A) := by
  unfold goodRegionLhs
  fun_prop

/-- On the upper half-plane the good region is the strict sublevel set of
`goodRegionLhs`. -/
lemma goodRegion_eq_preimage (N : ℕ) (C_A K_A : ℝ) :
    goodRegion N C_A K_A = {z : ℂ | 0 < z.im} ∩ {z : ℂ | goodRegionLhs N C_A K_A z < 0} := by
  ext z
  simp only [goodRegion, goodRegionLhs, Set.mem_setOf_eq, Set.mem_inter_iff]
  constructor
  · rintro ⟨hy, h⟩
    have hy6 : 0 < (z.im) ^ 6 := by positivity
    refine ⟨hy, ?_⟩
    rw [show C_A * (K_A + ‖z‖) ^ 2 * ((N : ℝ) ^ 2)⁻¹ * ((z.im) ^ 6)⁻¹
        = (C_A * (K_A + ‖z‖) ^ 2 * ((N : ℝ) ^ 2)⁻¹) / (z.im) ^ 6 from by ring]
      at h
    rw [div_lt_iff₀ hy6] at h
    linarith
  · rintro ⟨hy, h⟩
    have hy6 : 0 < (z.im) ^ 6 := by positivity
    refine ⟨hy, ?_⟩
    rw [show C_A * (K_A + ‖z‖) ^ 2 * ((N : ℝ) ^ 2)⁻¹ * ((z.im) ^ 6)⁻¹
        = (C_A * (K_A + ‖z‖) ^ 2 * ((N : ℝ) ^ 2)⁻¹) / (z.im) ^ 6 from by ring]
    rw [div_lt_iff₀ hy6]
    linarith

/-- The good region is open. -/
theorem goodRegion_isOpen (N : ℕ) (C_A K_A : ℝ) : IsOpen (goodRegion N C_A K_A) := by
  rw [goodRegion_eq_preimage]
  exact (isOpen_lt continuous_const Complex.continuous_im).inter
    (isOpen_lt (continuous_goodRegionLhs N C_A K_A) continuous_const)

/-! ### An explicit unbounded convex subset of the good region -/

/-- A vertical half-infinite tube of half-width `1`, above height `T`. -/
def tubeRegion (T : ℝ) : Set ℂ :=
  {z : ℂ | 0 < z.im ∧ T < z.im ∧ |z.re| < 1}

/-- The tube is open. -/
theorem tubeRegion_isOpen (T : ℝ) : IsOpen (tubeRegion T) := by
  have h1 : IsOpen ({z : ℂ | 0 < z.im} : Set ℂ) :=
    isOpen_lt continuous_const Complex.continuous_im
  have h2 : IsOpen ({z : ℂ | T < z.im} : Set ℂ) :=
    isOpen_lt continuous_const Complex.continuous_im
  have h3 : IsOpen ({z : ℂ | |z.re| < 1} : Set ℂ) := by
    have heq : {z : ℂ | |z.re| < 1} = {z : ℂ | -1 < z.re} ∩ {z : ℂ | z.re < 1} := by
      ext z
      simp only [Set.mem_setOf_eq, Set.mem_inter_iff, abs_lt]
    rw [heq]
    exact (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)
  have hset : tubeRegion T =
      {z : ℂ | 0 < z.im} ∩ ({z : ℂ | T < z.im} ∩ {z : ℂ | |z.re| < 1}) := by
    ext z
    simp only [tubeRegion, Set.mem_setOf_eq, Set.mem_inter_iff]
  rw [hset]
  exact h1.inter (h2.inter h3)

/-- The tube is convex. -/
theorem tubeRegion_convex (T : ℝ) : Convex ℝ (tubeRegion T) := by
  rintro z ⟨hz0, hzT, hzR⟩ w ⟨hw0, hwT, hwR⟩ a b ha hb hab
  simp only [tubeRegion, Set.mem_setOf_eq, Complex.add_im, Complex.smul_im,
    Complex.add_re, Complex.smul_re, smul_eq_mul] at *
  refine ⟨?_, ?_, ?_⟩
  · rcases lt_or_eq_of_le ha with hapos | hazero
    · have h1 := mul_lt_mul_of_pos_left hz0 hapos
      rcases lt_or_eq_of_le hb with hbpos | hbz
      · have h2 := mul_lt_mul_of_pos_left hw0 hbpos
        nlinarith [h1, h2]
      · subst hbz
        nlinarith [h1]
    · subst hazero
      have hb1 : b = 1 := by linarith
      have h2 := mul_lt_mul_of_pos_left hw0 (by linarith : (0:ℝ) < b)
      nlinarith [h2, hb1]
  · rcases lt_or_eq_of_le ha with hapos | hazero
    · have h1 := mul_lt_mul_of_pos_left hzT hapos
      rcases lt_or_eq_of_le hb with hbpos | hbz
      · have h2 := mul_lt_mul_of_pos_left hwT hbpos
        nlinarith [h1, h2, hab]
      · subst hbz
        nlinarith [h1, hab]
    · subst hazero
      have hb1 : b = 1 := by linarith
      have h2 := mul_lt_mul_of_pos_left hwT (by linarith : (0:ℝ) < b)
      nlinarith [h2, hb1]
  · rw [abs_lt] at hzR hwR ⊢
    constructor
    · rcases lt_or_eq_of_le ha with hapos | hazero
      · have h1 := mul_lt_mul_of_pos_left hzR.1 hapos
        nlinarith [h1, hwR.1, hb, hab]
      · subst hazero
        have hb1 : b = 1 := by linarith
        nlinarith [hwR.1, hb1]
    · rcases lt_or_eq_of_le ha with hapos | hazero
      · have h1 := mul_lt_mul_of_pos_left hzR.2 hapos
        nlinarith [h1, hwR.2, hb, hab]
      · subst hazero
        have hb1 : b = 1 := by linarith
        nlinarith [hwR.2, hb1]

/-- The tube is preconnected. -/
theorem tubeRegion_isPreconnected (T : ℝ) : IsPreconnected (tubeRegion T) :=
  (tubeRegion_convex T).isPreconnected

/-- The tube is unbounded (it contains the vertical ray `i t` for `t → ∞`). -/
theorem tubeRegion_unbounded (T : ℝ) : ¬ Bornology.IsBounded (tubeRegion T) := by
  intro h
  obtain ⟨R, hR⟩ := h.exists_norm_le
  let t : ℝ := max R 0 + max T 0 + 2
  have hT0 : 0 ≤ max T 0 := le_max_right T 0
  have hR0 : 0 ≤ max R 0 := le_max_right R 0
  have htT : T < t := by
    have h1 : T ≤ max T 0 := le_max_left T 0
    dsimp [t]; linarith
  have ht0 : 0 < t := by
    dsimp [t]; linarith
  have hmem : (t : ℂ) * Complex.I ∈ tubeRegion T := by
    refine ⟨?_, ?_, ?_⟩
    · simpa [Complex.mul_im] using ht0
    · simpa [Complex.mul_im] using htT
    · simp [Complex.mul_re]
  have hnorm := hR _ hmem
  have hnt : ‖(t : ℂ) * Complex.I‖ = t := by
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg ht0.le]
  rw [hnt] at hnorm
  have hRle : R ≤ max R 0 := le_max_left R 0
  have ht' : max R 0 + 2 ≤ t := by
    dsimp [t]; linarith
  linarith

/-- The norm of a point of the tube is at most `√2 · im z`. -/
lemma norm_le_sqrt_two_mul_im {T : ℝ} (hT1 : 1 ≤ T) {z : ℂ} (hz : z ∈ tubeRegion T) :
    ‖z‖ ≤ Real.sqrt 2 * z.im := by
  have him0 : 0 < z.im := hz.1
  have him1 : 1 < z.im := lt_of_le_of_lt hT1 hz.2.1
  have hsq : ‖z‖ ^ 2 ≤ 2 * (z.im) ^ 2 := by
    have hre : z.re ^ 2 < 1 := by
      have h := hz.2.2
      rw [abs_lt] at h
      nlinarith [h.1, h.2]
    have hnormSq : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]; ring
    have himsq : 1 < (z.im) ^ 2 := by nlinarith
    nlinarith [hre, himsq]
  have h2 : 0 ≤ z.im := him0.le
  have hsqrt : Real.sqrt (‖z‖ ^ 2) ≤ Real.sqrt (2 * (z.im) ^ 2) :=
    Real.sqrt_le_sqrt hsq
  rw [Real.sqrt_sq (norm_nonneg z), Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2),
    Real.sqrt_sq h2] at hsqrt
  exact hsqrt

/-- On the tube the defining function of the good region is bounded by
`|C_A| (|K_A| + √2)^2 N^{-2} (im z)^{-4}`. -/
lemma goodRegion_lhs_le_tube (N : ℕ) (C_A K_A : ℝ) {T : ℝ}
    (hT1 : 1 ≤ T) {z : ℂ} (hz : z ∈ tubeRegion T) :
    C_A * (K_A + ‖z‖) ^ 2 * ((N : ℝ) ^ 2)⁻¹ * ((z.im) ^ 6)⁻¹ ≤
      |C_A| * (|K_A| + Real.sqrt 2) ^ 2 * ((N : ℝ) ^ 2)⁻¹ * ((z.im) ^ 4)⁻¹ := by
  have him0 : 0 < z.im := hz.1
  have hz1 : 1 < z.im := lt_of_le_of_lt hT1 hz.2.1
  have him1sq : 1 < (z.im) ^ 2 := by nlinarith
  have hsq2 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hnorm : ‖z‖ ≤ Real.sqrt 2 * z.im := norm_le_sqrt_two_mul_im hT1 hz
  have hKabs : |K_A + ‖z‖| ≤ (|K_A| + Real.sqrt 2) * z.im := by
    rw [abs_le]
    constructor
    · -- lower bound
      have h1 : K_A ≥ -|K_A| := neg_abs_le K_A
      have h2 : (0 : ℝ) ≤ ‖z‖ := norm_nonneg z
      have h3 : -|K_A| * z.im ≤ -|K_A| := by nlinarith [abs_nonneg K_A]
      have h4 : (0 : ℝ) ≤ Real.sqrt 2 * z.im := by positivity
      nlinarith [h1, h2, h3, h4]
    · -- upper bound
      have h1 : K_A ≤ |K_A| := le_abs_self K_A
      have h2 : |K_A| ≤ |K_A| * z.im := by nlinarith [abs_nonneg K_A]
      nlinarith [h1, h2, hnorm, hsq2, him0]
  have hKsq : (K_A + ‖z‖) ^ 2 ≤ ((|K_A| + Real.sqrt 2) * z.im) ^ 2 := by
    have h := mul_self_le_mul_self (abs_nonneg (K_A + ‖z‖)) hKabs
    simpa [sq_abs, pow_two] using h
  have hN2 : 0 ≤ ((N : ℝ) ^ 2)⁻¹ := by positivity
  have hy6 : 0 ≤ ((z.im) ^ 6)⁻¹ := by positivity
  have hy : 0 < z.im := him0
  have hfac : 0 ≤ |C_A| * ((N : ℝ) ^ 2)⁻¹ * ((z.im) ^ 6)⁻¹ := by positivity
  have hfac2 : 0 ≤ (K_A + ‖z‖) ^ 2 * ((N : ℝ) ^ 2)⁻¹ * ((z.im) ^ 6)⁻¹ := by positivity
  have hstep1 : C_A * (K_A + ‖z‖) ^ 2 * ((N : ℝ) ^ 2)⁻¹ * ((z.im) ^ 6)⁻¹
      ≤ |C_A| * (K_A + ‖z‖) ^ 2 * ((N : ℝ) ^ 2)⁻¹ * ((z.im) ^ 6)⁻¹ := by
    calc C_A * (K_A + ‖z‖) ^ 2 * ((N : ℝ) ^ 2)⁻¹ * ((z.im) ^ 6)⁻¹
        = ((K_A + ‖z‖) ^ 2 * ((N : ℝ) ^ 2)⁻¹ * ((z.im) ^ 6)⁻¹) * C_A := by ring
      _ ≤ ((K_A + ‖z‖) ^ 2 * ((N : ℝ) ^ 2)⁻¹ * ((z.im) ^ 6)⁻¹) * |C_A| :=
          mul_le_mul_of_nonneg_left (le_abs_self C_A) hfac2
      _ = |C_A| * (K_A + ‖z‖) ^ 2 * ((N : ℝ) ^ 2)⁻¹ * ((z.im) ^ 6)⁻¹ := by ring
  have hstep2 : |C_A| * (K_A + ‖z‖) ^ 2 * ((N : ℝ) ^ 2)⁻¹ * ((z.im) ^ 6)⁻¹
      ≤ |C_A| * ((|K_A| + Real.sqrt 2) * z.im) ^ 2 * ((N : ℝ) ^ 2)⁻¹ * ((z.im) ^ 6)⁻¹ := by
    calc |C_A| * (K_A + ‖z‖) ^ 2 * ((N : ℝ) ^ 2)⁻¹ * ((z.im) ^ 6)⁻¹
        = (|C_A| * ((N : ℝ) ^ 2)⁻¹ * ((z.im) ^ 6)⁻¹) * (K_A + ‖z‖) ^ 2 := by ring
      _ ≤ (|C_A| * ((N : ℝ) ^ 2)⁻¹ * ((z.im) ^ 6)⁻¹) *
            ((|K_A| + Real.sqrt 2) * z.im) ^ 2 :=
          mul_le_mul_of_nonneg_left hKsq hfac
      _ = |C_A| * ((|K_A| + Real.sqrt 2) * z.im) ^ 2 * ((N : ℝ) ^ 2)⁻¹ *
            ((z.im) ^ 6)⁻¹ := by ring
  have hstep3 : |C_A| * ((|K_A| + Real.sqrt 2) * z.im) ^ 2 * ((N : ℝ) ^ 2)⁻¹ *
        ((z.im) ^ 6)⁻¹
      = |C_A| * (|K_A| + Real.sqrt 2) ^ 2 * ((N : ℝ) ^ 2)⁻¹ * ((z.im) ^ 4)⁻¹ := by
    field_simp
  exact hstep1.trans (hstep2.trans (le_of_eq hstep3))

/-- The tube is contained in the good region, provided the height threshold is
large enough. -/
theorem tubeRegion_subset_goodRegion (N : ℕ) (C_A K_A T : ℝ)
    (hT1 : 1 ≤ T) (hsmall : |C_A| * (|K_A| + Real.sqrt 2) ^ 2 * ((N : ℝ) ^ 2)⁻¹ * (T ^ 4)⁻¹ < 1 / 2) :
    tubeRegion T ⊆ goodRegion N C_A K_A := by
  intro z hz
  have him0 : 0 < z.im := hz.1
  refine ⟨him0, ?_⟩
  have hle := goodRegion_lhs_le_tube N C_A K_A hT1 hz
  have hTpos : 0 < T := lt_of_lt_of_le (by norm_num : (0:ℝ) < 1) hT1
  have hyT : T ≤ z.im := le_of_lt hz.2.1
  have hy4 : ((z.im) ^ 4)⁻¹ ≤ (T ^ 4)⁻¹ := by
    have h := one_div_le_one_div_of_le (by positivity : (0:ℝ) < T ^ 4)
      (pow_le_pow_left₀ hTpos.le hyT 4)
    simpa [one_div] using h
  have hc : 0 ≤ |C_A| * (|K_A| + Real.sqrt 2) ^ 2 * ((N : ℝ) ^ 2)⁻¹ := by positivity
  have hfinal : |C_A| * (|K_A| + Real.sqrt 2) ^ 2 * ((N : ℝ) ^ 2)⁻¹ * ((z.im) ^ 4)⁻¹ ≤
      |C_A| * (|K_A| + Real.sqrt 2) ^ 2 * ((N : ℝ) ^ 2)⁻¹ * (T ^ 4)⁻¹ := by
    exact mul_le_mul_of_nonneg_left (by simpa [inv_pow] using hy4) hc
  exact lt_of_le_of_lt (hle.trans hfinal) hsmall

/-! ### Invertibility of the operator-valued difference (Neumann argument) -/

section Invertibility

open FreeProbability FreeProbability.Fock

/-- **Invertibility of `operatorMatrixDifference A B` near the pencil point.**

If `B` is close to `z • 1 - A₀` in the operator norm, then the operator-valued difference
`B ⊗ 1 - ∑ A_i ⊗ s_i` is invertible.  The proof is a Neumann series around the genuine
pencil resolvent at the nonreal scalar point `z`, whose inverse has norm at most `(im z)⁻¹`.

The hypothesis `hδ` is the (already available) transfer from the Frobenius bound on
`B - (z • 1 - A₀)` to the operator norm of the scalar-matrix embedding; the constant is
irrelevant for the HT05 argument since `d` is fixed. -/
theorem isUnit_operatorMatrixDifference_of_norm_close
    (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    (hA₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian)
    (B : Matrix d d ℂ) (z : ℂ) (hz : 0 < z.im)
    (hδ : ‖CStarMatrix.ofMatrix (scalarMatrixEmbedding
        (A := WordSpace ι →L[ℂ] WordSpace ι) (B - (z • (1 : Matrix d d ℂ) - A₀)))‖ *
        (z.im)⁻¹ < 1) :
    IsUnit (operatorMatrixDifference A B) := by
  set P : CStarMatrix d d (WordSpace ι →L[ℂ] WordSpace ι) :=
    operatorMatrixDifference A (z • (1 : Matrix d d ℂ) - A₀) with hPdef
  have hP : IsUnit P := by
    rw [hPdef, operatorMatrixDifference_pencil]
    exact StarProbabilitySpace.selfAdjoint_mem_resolventSet_of_im_ne_zero
      (operatorMatrixPencil A₀ A) (operatorMatrixPencil_isSelfAdjoint A₀ A hA₀ hA) z hz.ne'
  set δ : CStarMatrix d d (WordSpace ι →L[ℂ] WordSpace ι) :=
    CStarMatrix.ofMatrix (scalarMatrixEmbedding
      (A := WordSpace ι →L[ℂ] WordSpace ι) (B - (z • (1 : Matrix d d ℂ) - A₀))) with hδdef
  have hX : operatorMatrixDifference A B = P + δ := by
    rw [hPdef, hδdef]
    apply CStarMatrix.ofMatrix.injective.eq_iff.mpr
    change scalarMatrixEmbedding B - matrixLinearCombination semicircular A =
      (scalarMatrixEmbedding (z • (1 : Matrix d d ℂ) - A₀) -
        matrixLinearCombination semicircular A) +
        scalarMatrixEmbedding (B - (z • (1 : Matrix d d ℂ) - A₀))
    simp only [map_sub, map_add, map_smul, map_neg, map_one]
    abel
  have hPinv : ‖Ring.inverse P‖ ≤ (z.im)⁻¹ := by
    rw [hPdef, operatorMatrixDifference_pencil]
    have h := norm_resolvent_le_inv_im
      (operatorMatrixPencil_isSelfAdjoint A₀ A hA₀ hA) (z := z) hz
    simpa [resolvent] using h
  have hcontr : ‖Ring.inverse P * δ‖ < 1 := by
    calc ‖Ring.inverse P * δ‖ ≤ ‖Ring.inverse P‖ * ‖δ‖ := norm_mul_le _ _
      _ ≤ (z.im)⁻¹ * ‖δ‖ := mul_le_mul_of_nonneg_right hPinv (norm_nonneg _)
      _ = ‖δ‖ * (z.im)⁻¹ := by ring
      _ < 1 := hδ
  have hunit : IsUnit (1 + Ring.inverse P * δ) := by
    have h := IsUnit.one_sub_of_norm_lt_one (x := -(Ring.inverse P * δ)) (by simpa using hcontr)
    simpa using h
  have hPeq : P + δ = P * (1 + Ring.inverse P * δ) := by
    rw [mul_add, mul_one, ← mul_assoc, Ring.mul_inverse_cancel P hP, one_mul]
  rw [hX, hPeq]
  exact hP.mul hunit

end Invertibility

/-! ### The identification by analytic uniqueness -/

section Identification

open FreeProbability FreeProbability.Fock

/-- **Physical branch identification (abstract form).**

Let `B : ℂ → Matrix d d ℂ` be a self-energy branch on an open, preconnected, unbounded set
`U`, suppose the finite-`N` mean `m = gueResolventMean A₀ A` solves the Dyson equation at the
matrix argument `B z - A₀`, suppose both sides are analytic on `U` and normalized at infinity,
and suppose the operator-valued difference at `B z - A₀` is invertible on `U`.  Then
`m = operatorMatrixArgumentCauchy A (B z - A₀)` throughout `U`.

This is `matrixDyson_analytic_unique_of_normalized` with `B z` replaced by `B z - A₀`; it is the
formal HT05 Proposition 5.6 step.  All analytic inputs are explicit hypotheses. -/
theorem eqOn_operatorMatrixArgumentCauchy_of_dyson
    (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    (B : ℂ → Matrix d d ℂ) (U : Set ℂ)
    (hU : IsOpen U) (hconn : IsPreconnected U) (hunb : ¬ Bornology.IsBounded U)
    (hAnM : AnalyticOnNhd ℂ (gueResolventMean (N := N) A₀ A) U)
    (hAnG : AnalyticOnNhd ℂ
      (fun z => operatorMatrixArgumentCauchy A (B z - A₀)) U)
    (hDyson : ∀ z ∈ U,
      (B z - A₀ - matrixCovariance A (gueResolventMean (N := N) A₀ A z)) *
        gueResolventMean (N := N) A₀ A z = 1)
    (hUnit : ∀ z ∈ U, IsUnit (operatorMatrixDifference A (B z - A₀)))
    (hMone : Filter.Tendsto (fun z => z • gueResolventMean (N := N) A₀ A z)
      (Bornology.cobounded ℂ ⊓ Filter.principal U) (𝓝 (1 : Matrix d d ℂ)))
    (hGone : Filter.Tendsto (fun z => z • operatorMatrixArgumentCauchy A (B z - A₀))
      (Bornology.cobounded ℂ ⊓ Filter.principal U) (𝓝 (1 : Matrix d d ℂ))) :
    Set.EqOn (gueResolventMean (N := N) A₀ A)
      (fun z => operatorMatrixArgumentCauchy A (B z - A₀)) U := by
  refine matrixDyson_analytic_unique_of_normalized A (fun z => B z - A₀)
    (gueResolventMean (N := N) A₀ A)
    (fun z => operatorMatrixArgumentCauchy A (B z - A₀)) U hU hconn hunb hAnM hAnG ?_ ?_
    hMone hGone
  · intro z hz
    exact hDyson z hz
  · intro z hz
    exact operatorMatrixArgumentCauchy_dyson A (B z - A₀) (hUnit z hz)

end Identification

/-! ### Operator norm versus Frobenius norm for the embedded argument difference -/

section NormTransfer

open FreeProbability FreeProbability.Fock
open WithCStarModule
open scoped InnerProductSpace

/-- The operator norm of a `C⋆`-matrix is bounded by the sum of the norms of its entries. -/
theorem cstarMatrix_norm_le_sum_entries_local
    {M : CStarMatrix d d (WordSpace ι →L[ℂ] WordSpace ι)} :
    ‖M‖ ≤ ∑ j, ∑ i, ‖M i j‖ := by
  rw [CStarMatrix.norm_def]
  refine (CStarMatrix.toCLM M).opNorm_le_bound (by positivity) fun v => ?_
  calc ‖CStarMatrix.toCLM M v‖ ≤ ∑ x, ‖(CStarMatrix.toCLM M v) x‖ := pi_norm_le_sum_norm _
    _ = ∑ x, ‖∑ i, v i * M i x‖ := by simp [CStarMatrix.toCLM_apply_eq_sum]
    _ ≤ ∑ x, ∑ i, ‖v i‖ * ‖M i x‖ := by
        refine Finset.sum_le_sum fun x _ => ?_
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
        exact norm_mul_le _ _
    _ ≤ ∑ x, ∑ i, ‖v‖ * ‖M i x‖ := by
        refine Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun i _ => ?_
        exact mul_le_mul_of_nonneg_right (norm_apply_le_norm v i) (norm_nonneg _)
    _ = (∑ j, ∑ i, ‖M i j‖) * ‖v‖ := by
        simp only [Finset.sum_mul, Finset.mul_sum]
        exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun i _ => mul_comm _ _

/-- The sum of the absolute values of the entries of a complex matrix is bounded by
`card d` times its Frobenius norm. -/
theorem sum_norm_entries_le_card_mul_frob_local (M : Matrix d d ℂ) :
    ∑ j, ∑ i, ‖M i j‖ ≤ (Fintype.card d : ℝ) * frob M := by
  have hsum_eq : (∑ p : d × d, ‖M p.2 p.1‖) = ∑ j, ∑ i, ‖M i j‖ := by
    rw [Fintype.sum_prod_type]
  have hsq_eq : (∑ p : d × d, ‖M p.2 p.1‖ ^ 2) = (frob M) ^ 2 := by
    rw [frob_sq, Fintype.sum_prod_type, Finset.sum_comm]
  have hcard : (∑ _ : d × d, (1 : ℝ)) = (Fintype.card d : ℝ) ^ 2 := by
    simp [Finset.sum_const, Fintype.card_prod]
    ring
  suffices h : (∑ p : d × d, ‖M p.2 p.1‖) ≤ (Fintype.card d : ℝ) * frob M by
    rwa [hsum_eq] at h
  have key : (∑ p : d × d, ‖M p.2 p.1‖) ^ 2 ≤
      (Fintype.card d : ℝ) ^ 2 * (frob M) ^ 2 := by
    have hle := Finset.sum_mul_sq_le_sq_mul_sq (s := (Finset.univ : Finset (d × d)))
      (f := fun _ : d × d => (1 : ℝ)) (g := fun p : d × d => ‖M p.2 p.1‖)
    simpa only [one_mul, one_pow, hcard, hsq_eq] using hle
  have hS0 : 0 ≤ ∑ p : d × d, ‖M p.2 p.1‖ :=
    Finset.sum_nonneg fun _ _ => norm_nonneg _
  have h2 : ∑ p : d × d, ‖M p.2 p.1‖ ≤
      Real.sqrt ((Fintype.card d : ℝ) ^ 2 * (frob M) ^ 2) := by
    rw [← Real.sqrt_sq hS0]
    exact Real.sqrt_le_sqrt key
  rwa [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity),
    Real.sqrt_sq (frob_nonneg M)] at h2

/-- The unit of the coefficient algebra has norm at most one. -/
theorem cstar_norm_one_le_one_local :
    ‖(1 : WordSpace ι →L[ℂ] WordSpace ι)‖ ≤ 1 := by
  have h : ‖(1 : WordSpace ι →L[ℂ] WordSpace ι)‖ =
      ‖(1 : WordSpace ι →L[ℂ] WordSpace ι)‖ * ‖(1 : WordSpace ι →L[ℂ] WordSpace ι)‖ := by
    rw [← CStarRing.norm_star_mul_self (x := (1 : WordSpace ι →L[ℂ] WordSpace ι)),
      star_one, one_mul]
  nlinarith [norm_nonneg (1 : WordSpace ι →L[ℂ] WordSpace ι)]

/-- **The embedded difference of the matrix arguments, in the operator norm**, is bounded by
`card d` times the Frobenius norm of the difference. -/
theorem norm_scalarMatrixEmbedding_le_card_mul_frob_local (D : Matrix d d ℂ) :
    ‖CStarMatrix.ofMatrix (scalarMatrixEmbedding (A := WordSpace ι →L[ℂ] WordSpace ι) D)‖ ≤
      (Fintype.card d : ℝ) * frob D := by
  refine (cstarMatrix_norm_le_sum_entries_local (M :=
    CStarMatrix.ofMatrix (scalarMatrixEmbedding (A := WordSpace ι →L[ℂ] WordSpace ι) D))).trans ?_
  have hentry : ∀ i j : d,
      ‖(CStarMatrix.ofMatrix (scalarMatrixEmbedding (A := WordSpace ι →L[ℂ] WordSpace ι) D)) i j‖
        ≤ ‖D i j‖ := by
    intro i j
    change ‖scalarMatrixEmbedding (A := WordSpace ι →L[ℂ] WordSpace ι) D i j‖ ≤ ‖D i j‖
    rw [scalarMatrixEmbedding_apply, norm_algebraMap]
    exact mul_le_of_le_one_right (norm_nonneg _) cstar_norm_one_le_one_local
  refine (Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun i _ => hentry i j).trans ?_
  exact sum_norm_entries_le_card_mul_frob_local D

end NormTransfer

section Final

open FreeProbability FreeProbability.Fock

/-- **Invertibility from the Frobenius bound.**  If `card d * frob (B - z • 1) < im z`, then the
operator-valued difference at the corrected argument `B - A₀` is invertible.  This is the form
produced by the HT05 self-energy estimates (which bound `frob (selfEnergy - z • 1)`). -/
theorem isUnit_operatorMatrixDifference_of_frob_close
    (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    (hA₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian)
    (B : Matrix d d ℂ) (z : ℂ) (hz : 0 < z.im)
    (hδ : (Fintype.card d : ℝ) * frob (B - z • (1 : Matrix d d ℂ)) * (z.im)⁻¹ < 1) :
    IsUnit (operatorMatrixDifference A (B - A₀)) := by
  have hsub : B - A₀ - (z • (1 : Matrix d d ℂ) - A₀) = B - z • (1 : Matrix d d ℂ) := by abel
  refine isUnit_operatorMatrixDifference_of_norm_close A₀ A hA₀ hA (B - A₀) z hz ?_
  rw [hsub]
  exact lt_of_le_of_lt
    (mul_le_mul_of_nonneg_right (norm_scalarMatrixEmbedding_le_card_mul_frob_local _)
      (by positivity)) hδ

/-- **HT05 physical branch identification on the tube, with all inputs explicit.**

For `z` in the unbounded tube `tubeRegion T` (which is open, convex, hence preconnected, and
contained in the good region), the finite-`N` mean equals the matrix-argument Cauchy transform at
the corrected self-energy argument `B z - A₀`. -/
theorem gueResolventMean_eq_operatorMatrixArgumentCauchy_on_tube
    (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    (hA₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian)
    (B : ℂ → Matrix d d ℂ) (T : ℝ)
    (hAnM : AnalyticOnNhd ℂ (gueResolventMean (N := N) A₀ A) (tubeRegion T))
    (hAnG : AnalyticOnNhd ℂ
      (fun z => operatorMatrixArgumentCauchy A (B z - A₀)) (tubeRegion T))
    (hDyson : ∀ z ∈ tubeRegion T,
      (B z - A₀ - matrixCovariance A (gueResolventMean (N := N) A₀ A z)) *
        gueResolventMean (N := N) A₀ A z = 1)
    (hUnit : ∀ z ∈ tubeRegion T, IsUnit (operatorMatrixDifference A (B z - A₀)))
    (hMone : Filter.Tendsto (fun z => z • gueResolventMean (N := N) A₀ A z)
      (Bornology.cobounded ℂ ⊓ Filter.principal (tubeRegion T)) (𝓝 (1 : Matrix d d ℂ)))
    (hGone : Filter.Tendsto (fun z => z • operatorMatrixArgumentCauchy A (B z - A₀))
      (Bornology.cobounded ℂ ⊓ Filter.principal (tubeRegion T)) (𝓝 (1 : Matrix d d ℂ))) :
    Set.EqOn (gueResolventMean (N := N) A₀ A)
      (fun z => operatorMatrixArgumentCauchy A (B z - A₀)) (tubeRegion T) :=
  eqOn_operatorMatrixArgumentCauchy_of_dyson A₀ A B (tubeRegion T)
    (tubeRegion_isOpen T) (tubeRegion_isPreconnected T) (tubeRegion_unbounded T)
    hAnM hAnG hDyson hUnit hMone hGone

end Final
