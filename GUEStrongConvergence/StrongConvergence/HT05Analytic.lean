/-
# Analyticity of the finite-`N` averaged resolvent in the spectral parameter

The HT05 self-energy argument identifies the finite-`N` mean `m_N(z) = gueResolventMean A₀ A z`
with the free matrix-argument Cauchy transform at the corrected spectral parameter.  The
uniqueness theorems of the pinned `lean-free-prob` dependency require BOTH compared branches to be
`AnalyticOnNhd` in `z`; this file supplies that for `m_N`.

The mean is an integral over the Gaussian coordinates of a resolvent, so the proof differentiates
under the integral: for fixed coordinates the resolvent is analytic in `z`
(`spectrum.hasDerivAt_resolvent_const_left`) and the derivative is uniformly bounded by `|Im z|⁻²`
on a neighbourhood (because the pencil is Hermitian, `norm_guePencilResolvent_le`).
-/
import GUEStrongConvergence.Probability.DysonVariance
import GUEStrongConvergence.Probability.ResolventNetConcentration
import FreeProbability.OperatorValued.MatrixArgumentDyson
import FreeProbability.OperatorValued.MatrixPhysicalBranchUniqueness
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Topology.Algebra.Module.FiniteDimension

open MeasureTheory ProbabilityTheory Matrix Filter
open FreeProbability FreeProbability.Fock
open scoped Matrix.Norms.Elementwise ComplexOrder ENNReal NNReal Topology

namespace GUEStrongConvergence

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {d : Type*} [Fintype d] [DecidableEq d] {N : ℕ}

/-- **Derivative of a resolvent entry in the spectral parameter**:
`∂_z R(z)_{ab} = -(R(z)²)_{ab}` on the resolvent set. -/
theorem hasDerivAt_guePencilResolvent_entry_z (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    (hA₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian)
    (x : GUECoord ι N → ℝ) (z : ℂ) (hz : z.im ≠ 0) (a b : d × Fin N) :
    HasDerivAt (fun w => guePencilResolvent A₀ A x w a b)
      ((-(guePencilResolvent A₀ A x z ^ 2)) a b) z := by
  have hk : z ∈ resolventSet ℂ (guePencil A₀ A x) :=
    FreeProbability.StarProbabilitySpace.selfAdjoint_mem_resolventSet_of_im_ne_zero _
      (guePencil_isSelfAdjoint A₀ A hA₀ hA x) z hz
  have h := spectrum.hasDerivAt_resolvent_const_left (a := guePencil A₀ A x) hk
  simp only [guePencilResolvent]
  exact hasDerivAt_pi.mp (hasDerivAt_pi.mp h a) b

/-- The magnitude of a squared resolvent entry is at most `|Im z|⁻²`. -/
theorem norm_entry_sq_resolvent_le (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    (hA₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian)
    (x : GUECoord ι N → ℝ) (z : ℂ) (hz : z.im ≠ 0) (a b : d × Fin N) :
    ‖(-(guePencilResolvent A₀ A x z ^ 2)) a b‖ ≤ |z.im|⁻¹ ^ 2 := by
  have h1 : ‖(-(guePencilResolvent A₀ A x z ^ 2)) a b‖
      ≤ ‖-(guePencilResolvent A₀ A x z ^ 2)‖ := CStarMatrix.norm_entry_le_norm
  have h2 : ‖-(guePencilResolvent A₀ A x z ^ 2)‖
      ≤ ‖guePencilResolvent A₀ A x z‖ * ‖guePencilResolvent A₀ A x z‖ := by
    rw [norm_neg, pow_two]
    exact norm_mul_le _ _
  have h3 := norm_guePencilResolvent_le A₀ A hA₀ hA x z hz
  nlinarith [norm_nonneg (guePencilResolvent A₀ A x z), abs_pos.mpr hz,
    inv_nonneg.mpr (abs_pos.mpr hz).le]

/-- The derivative of an entry of the averaged partial trace in `z`. -/
theorem hasDerivAt_guePartialTrace_entry_z (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    (hA₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian)
    (x : GUECoord ι N → ℝ) (u v : d) {z : ℂ} (hz : z.im ≠ 0) :
    HasDerivAt (fun w => guePartialTrace A₀ A w x u v)
      ((N : ℂ)⁻¹ * ∑ k : Fin N, (-(guePencilResolvent A₀ A x z ^ 2)) (u, k) (v, k)) z := by
  simp only [guePartialTrace_apply]
  have hsum := HasDerivAt.sum (u := Finset.univ)
      (fun k _ => hasDerivAt_guePencilResolvent_entry_z A₀ A hA₀ hA x z hz (u, k) (v, k))
  have hsum' : HasDerivAt (fun w => ∑ k : Fin N, guePencilResolvent A₀ A x w (u, k) (v, k))
      (∑ k : Fin N, (-(guePencilResolvent A₀ A x z ^ 2)) (u, k) (v, k)) z := by
    have heq : (∑ k : Fin N, fun w => guePencilResolvent A₀ A x w (u, k) (v, k))
        = fun w => ∑ k : Fin N, guePencilResolvent A₀ A x w (u, k) (v, k) := by
      funext w
      simp only [Finset.sum_apply]
    rw [heq] at hsum
    exact hsum
  exact hsum'.const_mul _

/-- The derivative bound: away from the real axis the derivative of an entry of the averaged
partial trace is bounded by `|Im z|⁻²`. -/
theorem norm_deriv_guePartialTrace_entry_le (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    (hA₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian)
    (x : GUECoord ι N → ℝ) (u v : d) {z : ℂ} (hz : z.im ≠ 0) (hN : 0 < N) :
    ‖(N : ℂ)⁻¹ * ∑ k : Fin N, (-(guePencilResolvent A₀ A x z ^ 2)) (u, k) (v, k)‖
      ≤ |z.im|⁻¹ ^ 2 := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hterm : ∀ k : Fin N,
      ‖(-(guePencilResolvent A₀ A x z ^ 2)) (u, k) (v, k)‖ ≤ |z.im|⁻¹ ^ 2 :=
    fun k => norm_entry_sq_resolvent_le A₀ A hA₀ hA x z hz (u, k) (v, k)
  have hsum : ‖∑ k : Fin N, (-(guePencilResolvent A₀ A x z ^ 2)) (u, k) (v, k)‖
      ≤ (N : ℝ) * |z.im|⁻¹ ^ 2 := by
    calc ‖∑ k : Fin N, (-(guePencilResolvent A₀ A x z ^ 2)) (u, k) (v, k)‖
        ≤ ∑ k : Fin N, ‖(-(guePencilResolvent A₀ A x z ^ 2)) (u, k) (v, k)‖ :=
          norm_sum_le _ _
      _ ≤ ∑ _k : Fin N, |z.im|⁻¹ ^ 2 := Finset.sum_le_sum fun k _ => hterm k
      _ = (N : ℝ) * |z.im|⁻¹ ^ 2 := by
          simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  have hNne : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  calc (N : ℝ)⁻¹ * ‖∑ k : Fin N, (-(guePencilResolvent A₀ A x z ^ 2)) (u, k) (v, k)‖
      ≤ (N : ℝ)⁻¹ * ((N : ℝ) * |z.im|⁻¹ ^ 2) := by
        exact mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = |z.im|⁻¹ ^ 2 := by
        field_simp

/-- **Derivative of an entry of the averaged resolvent in the spectral parameter.**

Obtained by differentiating under the Gaussian integral: for almost every coordinate the resolvent
entry has `z`-derivative `-(R²)_{ab}`, and on the ball of radius `Im z / 2` around `z` all these
derivatives are bounded by the constant `(2 / Im z)²`. -/
theorem hasDerivAt_gueResolventMean_entry (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    (hA₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian) (hN : 0 < N) (u v : d)
    {z : ℂ} (hz : 0 < z.im) :
    HasDerivAt (fun w => gueResolventMean (N := N) A₀ A w u v)
      (∫ x : EuclideanSpace ℝ (GUECoord ι N),
        (N : ℂ)⁻¹ * ∑ k : Fin N, (-(guePencilResolvent A₀ A x z ^ 2)) (u, k) (v, k)
          ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))) z := by
  classical
  set μ : Measure (EuclideanSpace ℝ (GUECoord ι N)) :=
    stdGaussian (EuclideanSpace ℝ (GUECoord ι N)) with hμ
  haveI : IsProbabilityMeasure μ := by
    rw [hμ]; infer_instance
  set s : Set ℂ := Metric.ball z (z.im / 2) with hs
  have hz2 : 0 < z.im / 2 := by linarith
  have hs_nhds : s ∈ 𝓝 z := Metric.ball_mem_nhds z hz2
  have hmem : ∀ w ∈ s, z.im / 2 ≤ w.im := by
    intro w hw
    have h1 : ‖w - z‖ < z.im / 2 := by
      rw [← dist_eq_norm]; exact Metric.mem_ball.mp hw
    have h2 : |(w - z).im| ≤ ‖w - z‖ := Complex.abs_im_le_norm _
    have h3 : (w - z).im = w.im - z.im := Complex.sub_im w z
    rw [h3] at h2
    have h4 : z.im - w.im ≤ |w.im - z.im| := by
      rw [abs_sub_comm]; exact le_abs_self _
    linarith
  set F : ℂ → EuclideanSpace ℝ (GUECoord ι N) → ℂ :=
    fun w x => guePartialTrace A₀ A w (x : GUECoord ι N → ℝ) u v with hF
  set F' : ℂ → EuclideanSpace ℝ (GUECoord ι N) → ℂ :=
    fun w x => (N : ℂ)⁻¹ * ∑ k : Fin N,
      (-(guePencilResolvent A₀ A (x : GUECoord ι N → ℝ) w ^ 2)) (u, k) (v, k) with hF'
  have hF_meas : ∀ᶠ w in 𝓝 z, AEStronglyMeasurable (F w) μ := by
    filter_upwards [hs_nhds] with w hw
    have hwpos : 0 < w.im := lt_of_lt_of_le hz2 (hmem w hw)
    exact (continuous_guePartialTrace_entry A₀ A hA₀ hA w hwpos.ne' u v).aestronglyMeasurable
  have hF_int : Integrable (F z) μ := by
    have hb : ∀ᵐ x ∂μ, ‖F z x‖ ≤ |z.im|⁻¹ := by
      filter_upwards with x
      exact norm_guePartialTrace_entry_le A₀ A hA₀ hA _ z hz.ne' hN u v
    exact Integrable.of_bound
      (continuous_guePartialTrace_entry A₀ A hA₀ hA z hz.ne' u v).aestronglyMeasurable
      |z.im|⁻¹ hb
  have hsq_cont : ∀ k : Fin N, Continuous (fun x : EuclideanSpace ℝ (GUECoord ι N) =>
      (-(guePencilResolvent A₀ A (x : GUECoord ι N → ℝ) z ^ 2)) (u, k) (v, k)) := by
    intro k
    have hfun : (fun x : EuclideanSpace ℝ (GUECoord ι N) =>
        (-(guePencilResolvent A₀ A (x : GUECoord ι N → ℝ) z ^ 2)) (u, k) (v, k)) =
        fun x : EuclideanSpace ℝ (GUECoord ι N) => -∑ r : d × Fin N,
          guePencilResolvent A₀ A (x : GUECoord ι N → ℝ) z (u, k) r *
            guePencilResolvent A₀ A (x : GUECoord ι N → ℝ) z r (v, k) := by
      funext x
      simp only [pow_two, CStarMatrix.mul_apply, CStarMatrix.neg_apply, Finset.sum_neg_distrib]
    rw [hfun]
    exact (continuous_finset_sum _ (fun r _ =>
      (continuous_guePencilResolvent_entry A₀ A hA₀ hA z hz (u, k) r).mul
        (continuous_guePencilResolvent_entry A₀ A hA₀ hA z hz r (v, k)))).neg
  have hF'_meas : AEStronglyMeasurable (F' z) μ := by
    have hcont : Continuous (fun x : EuclideanSpace ℝ (GUECoord ι N) => F' z x) := by
      simp only [hF']
      exact continuous_const.mul (continuous_finsetSum _ (fun k _ => hsq_cont k))
    exact hcont.aestronglyMeasurable
  have h_bound : ∀ᵐ x ∂μ, ∀ w ∈ s, ‖F' w x‖ ≤ (2 / z.im) ^ 2 := by
    filter_upwards with x w hw
    have hwpos : 0 < w.im := lt_of_lt_of_le hz2 (hmem w hw)
    have hc := norm_deriv_guePartialTrace_entry_le A₀ A hA₀ hA
      (x : GUECoord ι N → ℝ) u v hwpos.ne' hN
    have hinv : |w.im|⁻¹ ^ 2 ≤ (2 / z.im) ^ 2 := by
      rw [abs_of_pos hwpos, pow_two, pow_two]
      have hle : w.im⁻¹ ≤ 2 / z.im := by
        rw [inv_le_iff_one_le_mul₀ hwpos]
        have hge : z.im / 2 ≤ w.im := hmem w hw
        have hcoef : (0:ℝ) < 2 / z.im := by positivity
        have h1 : (2 / z.im) * (z.im / 2) = 1 := by field_simp
        nlinarith [mul_le_mul_of_nonneg_left hge hcoef.le]
      have h2 : (0:ℝ) ≤ w.im⁻¹ := by positivity
      have h3 : (0:ℝ) ≤ 2 / z.im := by positivity
      exact mul_self_le_mul_self h2 hle
    exact hc.trans hinv
  have h_bound_int : Integrable (fun _ : EuclideanSpace ℝ (GUECoord ι N) => (2 / z.im) ^ 2) μ :=
    integrable_const _
  have h_diff : ∀ᵐ x ∂μ, ∀ w ∈ s, HasDerivAt (F · x) (F' w x) w := by
    filter_upwards with x w hw
    have hwpos : 0 < w.im := lt_of_lt_of_le hz2 (hmem w hw)
    have hd := hasDerivAt_guePartialTrace_entry_z A₀ A hA₀ hA
      (x : GUECoord ι N → ℝ) u v (z := w) hwpos.ne'
    simpa only [hF, hF'] using hd
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le (𝕜 := ℂ)
    (F := F) (F' := F') (x₀ := z) (s := s) (bound := fun _ => (2 / z.im) ^ 2) (μ := μ)
    hs_nhds hF_meas hF_int hF'_meas h_bound h_bound_int h_diff
  have heq : (fun w => gueResolventMean (N := N) A₀ A w u v)
      = fun w => ∫ x : EuclideanSpace ℝ (GUECoord ι N), F w x ∂μ := by
    funext w
    rw [gueResolventMean_apply]
  rw [heq]
  exact hmain.2

/-- **Analyticity of each entry of the averaged resolvent on the upper half-plane.** -/
theorem analytic_gueResolventMean_entry (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    (hA₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian) (hN : 0 < N) (u v : d) :
    AnalyticOnNhd ℂ (fun z => gueResolventMean (N := N) A₀ A z u v) {z : ℂ | 0 < z.im} := by
  have hopen : IsOpen {z : ℂ | 0 < z.im} := isOpen_lt continuous_const Complex.continuous_im
  refine DifferentiableOn.analyticOnNhd ?_ hopen
  intro z hz
  exact (hasDerivAt_gueResolventMean_entry A₀ A hA₀ hA hN u v hz).differentiableAt.differentiableWithinAt

/-- **Analyticity of the averaged resolvent, entrywise (Pi form).**

This is the matrix-level statement written for the product (entrywise) normed structure; it is
what the uniqueness theorems consume after transporting along the identity equivalence between
the several matrix norms on `Matrix d d ℂ`. -/
theorem analytic_gueResolventMean_pi (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    (hA₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian) (hN : 0 < N) :
    AnalyticOnNhd ℂ (fun z (u : d) (v : d) => gueResolventMean (N := N) A₀ A z u v)
      {z : ℂ | 0 < z.im} := by
  refine analyticOnNhd_pi_iff.mpr (fun u => analyticOnNhd_pi_iff.mpr (fun v => ?_))
  exact analytic_gueResolventMean_entry A₀ A hA₀ hA hN u v


end

end GUEStrongConvergence
