/-
# Assembling the GUE trace-word variance chain

This file composes the three verified variance inputs into the final conditional chain:

1. `norm_crossContribution_le`: the cross-pairing contribution
   `A N = ∑_p labelW(p) N^{L(p)}` is bounded by `#P * N^k`, using `twoWalkLoopCount_cross_le`
   (`L(p) ≤ k` for cross pairings) and `‖labelW(p)‖ ≤ 1`.
2. `variance_bound_of_expansion_with_cross`: feeding that bound into
   `variance_bound_of_wick_expansion` gives `Var(tr_N W) ≤ #P / N²` from the explicit two-trace
   pairing expansion (the output of the `GUEPairing` transport).
3. `ae_tendsto_gueNormTrace`: on the common product Gaussian space `CommonSpace ι`, the
   `B / N²` variance bound plus the mean convergence give
   `∀ᵐ x, Tendsto (fun N => gueNormTrace w (x N)) atTop (𝓝 L)` via Borel–Cantelli.
-/
import GUEStrongConvergence.Probability.CommonSpace
import GUEStrongConvergence.Probability.GUEAlmostSure
import GUEStrongConvergence.Probability.GUEVarianceClosing
import GUEStrongConvergence.Probability.GUEWordVarianceGenus

open MeasureTheory ProbabilityTheory Filter
open scoped RealInnerProductSpace Matrix ENNReal Topology

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false
set_option linter.unusedVariables false

namespace GUEStrongConvergence

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {N : ℕ}

/-! ### The cross-pairing contribution -/

/-- **Cross-contribution bound**: a label-weighted sum of `N` to a loop count bounded by `k` is at
most the number of terms times `N^k`. -/
theorem norm_sum_label_pow_le {P : Type*} [Fintype P] {k : ℕ}
    (labelW : P → ℂ) (L : P → ℕ)
    (hlabel : ∀ p, ‖labelW p‖ ≤ 1) (hL : ∀ p, L p ≤ k) (N : ℕ) (hN : 1 ≤ N) :
    ‖∑ p, labelW p * (N : ℂ) ^ (L p)‖ ≤ (Fintype.card P : ℝ) * (N : ℝ) ^ k := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  calc ‖∑ p, labelW p * (N : ℂ) ^ (L p)‖
      ≤ ∑ p, ‖labelW p * (N : ℂ) ^ (L p)‖ := norm_sum_le _ _
    _ ≤ ∑ _p : P, (N : ℝ) ^ k := by
        refine Finset.sum_le_sum fun p _ => ?_
        rw [norm_mul, norm_pow, Complex.norm_natCast]
        have h1 : ‖labelW p‖ ≤ 1 := hlabel p
        have h2 : (N : ℝ) ^ (L p) ≤ (N : ℝ) ^ k := pow_le_pow_right₀ hN1 (hL p)
        calc ‖labelW p‖ * (N : ℝ) ^ (L p) ≤ 1 * (N : ℝ) ^ k := by
              exact mul_le_mul h1 h2 (by positivity) (by positivity)
          _ = (N : ℝ) ^ k := one_mul _
    _ = (Fintype.card P : ℝ) * (N : ℝ) ^ k := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- **Concrete cross bound**: for a family of cross pairings (fixed-point-free involutions with a
pair crossing the two blocks), the label-weighted loop-count sum is at most `#P * N^k`. -/
theorem norm_crossContribution_le {k : ℕ} (hk : 1 ≤ k) {P : Type*} [Fintype P]
    (toPerm : P → Equiv.Perm (Fin (k + k))) (labelW : P → ℂ)
    (hinv : ∀ p, toPerm p * toPerm p = 1) (hfix : ∀ p i, toPerm p i ≠ i)
    (hcross : ∀ p, ∃ (i : Fin k) (j : Fin k), toPerm p (Fin.castAdd k i) = Fin.natAdd k j)
    (hlabel : ∀ p, ‖labelW p‖ ≤ 1) (N : ℕ) (hN : 1 ≤ N) :
    ‖∑ p, labelW p * (N : ℂ) ^ (twoWalkLoopCount k k (toPerm p))‖ ≤
      (Fintype.card P : ℝ) * (N : ℝ) ^ k := by
  refine norm_sum_label_pow_le labelW (fun p => twoWalkLoopCount k k (toPerm p)) hlabel
    (fun p => ?_) N hN
  have h := twoWalkLoopCount_cross_le k k hk hk (toPerm p) (hinv p) (hfix p) (hcross p)
  have hhalf : (k + k) / 2 = k := by omega
  omega

/-! ### The variance bound with the explicit expansion -/

/-- **Conditional variance bound with the cross contribution bounded**: from the two-trace pairing
expansion `Wick = N^{-k} (S² + ∑_p labelW(p) N^{L(p)})`, the mean formula and the cross-pairing
loop bound, the variance of `tr_N W` is at most `#P / N²`. -/
theorem variance_bound_of_expansion_with_cross (w : List ι) (k : ℕ) (hk : 1 ≤ k)
    (S : ℕ → ℂ) {P : Type*} [Fintype P] (toPerm : P → Equiv.Perm (Fin (k + k)))
    (labelW : P → ℂ)
    (hWick : ∀ N : ℕ, gueTwoTraceWick N w w.reverse =
      ((N : ℂ)⁻¹) ^ k * (((S N) ^ 2) +
        ∑ p, labelW p * (N : ℂ) ^ (twoWalkLoopCount k k (toPerm p))))
    (hmean : ∀ N : ℕ,
      Complex.normSq (∫ y, gueNormTrace w y
        ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))) =
          ((((N : ℂ)⁻¹) ^ (k + 2) * (S N) ^ 2)).re)
    (hinv : ∀ p, toPerm p * toPerm p = 1) (hfix : ∀ p i, toPerm p i ≠ i)
    (hcross : ∀ p, ∃ (i : Fin k) (j : Fin k), toPerm p (Fin.castAdd k i) = Fin.natAdd k j)
    (hlabel : ∀ p, ‖labelW p‖ ≤ 1) :
    ∀ N : ℕ, 1 ≤ N →
      ∫ x : EuclideanSpace ℝ (GUECoord ι N),
          ‖gueNormTrace w x - ∫ y, gueNormTrace w y
            ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))‖ ^ 2
        ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) ≤
          (Fintype.card P : ℝ) / (N : ℝ) ^ 2 := by
  refine variance_bound_of_wick_expansion w k S
    (fun N => ∑ p, labelW p * (N : ℂ) ^ (twoWalkLoopCount k k (toPerm p)))
    (Fintype.card P) hWick hmean (fun N hN => ?_)
  exact norm_crossContribution_le hk toPerm labelW hinv hfix hcross hlabel N hN

/-! ### Almost-sure convergence on the common Gaussian space -/

/-- **Almost-sure convergence of a fixed GUE trace word on the common space**: given the `B / N²`
variance bound and the convergence of the means, `tr_N W` converges almost surely. -/
theorem ae_tendsto_gueNormTrace (w : List ι) (L : ℂ) (B : ℝ)
    (hVar : ∀ N : ℕ, 1 ≤ N →
      ∫ y : EuclideanSpace ℝ (GUECoord ι N),
          ‖gueNormTrace w y - ∫ z, gueNormTrace w z
            ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))‖ ^ 2
        ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) ≤ B / (N : ℝ) ^ 2)
    (hmean : Tendsto (fun N : ℕ => ∫ y, gueNormTrace w y
      ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))) atTop (𝓝 L)) :
    ∀ᵐ x ∂(commonGaussianMeasure ι),
      Tendsto (fun N : ℕ => gueNormTrace w (x N)) atTop (𝓝 L) := by
  classical
  let m : ℕ → ℂ := fun N => ∫ y, gueNormTrace w y
    ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))
  -- integrability of the centered square on each block
  have hIntBlock : ∀ N : ℕ, Integrable (fun y : EuclideanSpace ℝ (GUECoord ι N) =>
      ‖gueNormTrace w y - m N‖ ^ 2)
      (stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) := by
    intro N
    haveI : IsProbabilityMeasure (stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) :=
      ProbabilityTheory.isProbabilityMeasure_stdGaussian
    have hstep : ∀ y : EuclideanSpace ℝ (GUECoord ι N),
        (‖gueNormTrace w y - m N‖ : ℝ) ^ 2 =
          (Complex.normSq (gueNormTrace w y) -
            2 * (gueNormTrace w y * star (m N)).re) + Complex.normSq (m N) := by
      intro y
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_sub]
      simp only [Complex.star_def]
      ring
    simp_rw [hstep]
    have hmc : Integrable (fun y : EuclideanSpace ℝ (GUECoord ι N) =>
        gueNormTrace w y * star (m N))
        (stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) :=
      (integrable_gueNormTrace w).mul_const _
    have hmcr : Integrable (fun y : EuclideanSpace ℝ (GUECoord ι N) =>
        (gueNormTrace w y * star (m N)).re)
        (stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) :=
      Complex.reCLM.integrable_comp hmc
    exact ((integrable_normSq_gueNormTrace w).sub (hmcr.const_mul 2)).add
      (integrable_const _)
  -- the integral over the common space is the block integral
  have hIntEq : ∀ N : ℕ,
      ∫ x : CommonSpace ι, ‖gueNormTrace w (x N) - m N‖ ^ 2 ∂(commonGaussianMeasure ι) =
        ∫ y : EuclideanSpace ℝ (GUECoord ι N), ‖gueNormTrace w y - m N‖ ^ 2
          ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) := by
    intro N
    have h := (integral_map (measurable_pi_apply N).aemeasurable
      (by
        rw [commonGaussianMeasure_map_eval (ι := ι) N]
        exact (hIntBlock N).aestronglyMeasurable)).symm
    rwa [commonGaussianMeasure_map_eval (ι := ι) N] at h
  -- integrability on the common space
  have hF : ∀ N : ℕ, Integrable (fun x : CommonSpace ι =>
      ‖gueNormTrace w (x N) - m N‖ ^ 2) (commonGaussianMeasure ι) := by
    intro N
    exact (measurePreserving_eval_commonGaussian (ι := ι) N).integrable_comp_of_integrable
      (hIntBlock N)
  -- summability of the second moments
  have hs : Summable (fun N : ℕ =>
      ∫ x : CommonSpace ι, ‖gueNormTrace w (x N) - m N‖ ^ 2 ∂(commonGaussianMeasure ι)) := by
    simp_rw [hIntEq]
    have hbase : Summable (fun N : ℕ => B / (N : ℝ) ^ 2) := by
      have := (Real.summable_one_div_nat_pow (p := 2)).mpr (by norm_num : 1 < (2 : ℕ))
      simpa only [div_eq_mul_inv, one_mul] using this.mul_left B
    have hshift : Summable (fun N : ℕ => B / ((N : ℝ) + 1) ^ 2) := by
      have := (summable_nat_add_iff 1).mpr hbase
      simpa [Nat.cast_add, Nat.cast_one] using this
    rw [← summable_nat_add_iff 1]
    refine hshift.of_nonneg_of_le (fun N => ?_) (fun N => ?_)
    · exact integral_nonneg (fun x => by positivity)
    · have hN : 1 ≤ N + 1 := by omega
      have hb := hVar (N + 1) hN
      simpa [Nat.cast_add, Nat.cast_one] using hb
  have hmean' : Tendsto m atTop (𝓝 L) := hmean
  exact ae_tendsto_of_tendsto_deviation (μ := commonGaussianMeasure ι)
    (fun N x => gueNormTrace w (x N)) m L hF hs hmean'

/-- **Final composition**: the explicit two-trace pairing expansion, the mean formula and the
cross-pairing loop bound imply almost-sure convergence of `tr_N W` on the common Gaussian space,
with the known mean limit `L`. -/
theorem ae_tendsto_gueNormTrace_of_expansion (w : List ι) (k : ℕ) (hk : 1 ≤ k)
    (S : ℕ → ℂ) {P : Type*} [Fintype P] (toPerm : P → Equiv.Perm (Fin (k + k)))
    (labelW : P → ℂ) (L : ℂ)
    (hWick : ∀ N : ℕ, gueTwoTraceWick N w w.reverse =
      ((N : ℂ)⁻¹) ^ k * (((S N) ^ 2) +
        ∑ p, labelW p * (N : ℂ) ^ (twoWalkLoopCount k k (toPerm p))))
    (hmeanNorm : ∀ N : ℕ,
      Complex.normSq (∫ y, gueNormTrace w y
        ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))) =
          ((((N : ℂ)⁻¹) ^ (k + 2) * (S N) ^ 2)).re)
    (hinv : ∀ p, toPerm p * toPerm p = 1) (hfix : ∀ p i, toPerm p i ≠ i)
    (hcross : ∀ p, ∃ (i : Fin k) (j : Fin k), toPerm p (Fin.castAdd k i) = Fin.natAdd k j)
    (hlabel : ∀ p, ‖labelW p‖ ≤ 1)
    (hmeanLimit : Tendsto (fun N : ℕ => ∫ y, gueNormTrace w y
      ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))) atTop (𝓝 L)) :
    ∀ᵐ x ∂(commonGaussianMeasure ι),
      Tendsto (fun N : ℕ => gueNormTrace w (x N)) atTop (𝓝 L) :=
  ae_tendsto_gueNormTrace w L (Fintype.card P)
    (variance_bound_of_expansion_with_cross w k hk S toPerm labelW hWick hmeanNorm
      hinv hfix hcross hlabel)
    hmeanLimit

end

end GUEStrongConvergence
