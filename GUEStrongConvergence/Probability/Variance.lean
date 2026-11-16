/-
# Two-point form of the variance

`∫∫ (f x - f y)^2 dmu dmu = 2 ∫ f^2 dmu - 2 (∫ f dmu)^2` for a probability measure: the identity
behind every variance-based concentration argument (and the starting point of the two-point and
Efron-Stein routes to the Gaussian Poincare inequality).
-/
import GUEStrongConvergence.Probability.GaussianMoments
open MeasureTheory ProbabilityTheory Filter
open scoped RealInnerProductSpace ENNReal NNReal Topology

namespace GUEStrongConvergence

noncomputable section

/-- Two-point form of the variance: `∫∫ (f x - f y)^2 = 2 ∫ f^2 - 2 (∫ f)^2`. -/
theorem integral_prod_sq_sub {γ : Type*} [MeasurableSpace γ] (μ : Measure γ) [IsProbabilityMeasure μ]
    {f : γ → ℝ} (hf : Integrable f μ) (hf2 : Integrable (fun x => f x ^ 2) μ) :
    ∫ z : γ × γ, (f z.1 - f z.2) ^ 2 ∂(μ.prod μ)
      = 2 * ∫ x, f x ^ 2 ∂μ - 2 * (∫ x, f x ∂μ) ^ 2 := by
  have hsq : ∀ z : γ × γ, (f z.1 - f z.2) ^ 2
      = f z.1 ^ 2 - 2 * (f z.1 * f z.2) + f z.2 ^ 2 := fun z => by ring
  simp_rw [hsq]
  have h1 : Integrable (fun z : γ × γ => f z.1 ^ 2) (μ.prod μ) := hf2.comp_fst μ
  have h2 : Integrable (fun z : γ × γ => f z.2 ^ 2) (μ.prod μ) := hf2.comp_snd μ
  have h3 : Integrable (fun z : γ × γ => f z.1 * f z.2) (μ.prod μ) := hf.mul_prod hf
  have h4 : Integrable (fun z : γ × γ => f z.1 ^ 2 - 2 * (f z.1 * f z.2)) (μ.prod μ) :=
    h1.sub (h3.const_mul 2)
  have hfst : ∫ z : γ × γ, f z.1 ^ 2 ∂(μ.prod μ) = ∫ x, f x ^ 2 ∂μ := by
    rw [integral_prod _ h1]
    simp
  have hsnd : ∫ z : γ × γ, f z.2 ^ 2 ∂(μ.prod μ) = ∫ x, f x ^ 2 ∂μ := by
    rw [integral_prod_symm _ h2]
    simp
  rw [integral_add h4 h2, integral_sub h1 (h3.const_mul 2), integral_const_mul,
    integral_prod_mul, hfst, hsnd]
  ring

/-- **Variance form of the Gaussian Poincaré inequality.** -/
theorem gaussian_poincare_variance {f f' : ℝ → ℝ}
    (hf : Integrable f (gaussianReal 0 1)) (hf2 : Integrable (fun x => f x ^ 2) (gaussianReal 0 1))
    (hpoin : ∫ x, (f x - ∫ y, f y ∂(gaussianReal 0 1)) ^ 2 ∂(gaussianReal 0 1)
      ≤ ∫ x, (f' x) ^ 2 ∂(gaussianReal 0 1)) :
    ∫ x, f x ^ 2 ∂(gaussianReal 0 1) - (∫ x, f x ∂(gaussianReal 0 1)) ^ 2
      ≤ ∫ x, (f' x) ^ 2 ∂(gaussianReal 0 1) := by
  set c := ∫ y, f y ∂(gaussianReal 0 1) with hc
  have hA : Integrable (fun x : ℝ => f x ^ 2) (gaussianReal 0 1) := hf2
  have hB : Integrable (fun x : ℝ => 2 * c * f x) (gaussianReal 0 1) := hf.const_mul _
  have hC : Integrable (fun _ : ℝ => c ^ 2) (gaussianReal 0 1) := integrable_const _
  have key : ∫ x, (f x - c) ^ 2 ∂(gaussianReal 0 1)
      = ∫ x, f x ^ 2 ∂(gaussianReal 0 1) - c ^ 2 := by
    calc ∫ x, (f x - c) ^ 2 ∂(gaussianReal 0 1)
        = ∫ x, (f x ^ 2 - 2 * c * f x + c ^ 2) ∂(gaussianReal 0 1) := by
          refine integral_congr_ae (ae_of_all _ fun x => ?_)
          ring
      _ = ∫ x, ((f x ^ 2 - 2 * c * f x) + c ^ 2) ∂(gaussianReal 0 1) := rfl
      _ = (∫ x, (f x ^ 2 - 2 * c * f x) ∂(gaussianReal 0 1)) + ∫ _x : ℝ, c ^ 2 ∂(gaussianReal 0 1) :=
          integral_add (hA.sub hB) hC
      _ = ((∫ x, f x ^ 2 ∂(gaussianReal 0 1)) - ∫ x, 2 * c * f x ∂(gaussianReal 0 1))
            + ∫ _x : ℝ, c ^ 2 ∂(gaussianReal 0 1) := by
          rw [integral_sub hA hB]
      _ = ((∫ x, f x ^ 2 ∂(gaussianReal 0 1)) - 2 * c * c) + c ^ 2 := by
          rw [integral_const_mul, integral_const, MeasureTheory.probReal_univ, one_smul,
            ← hc]
      _ = ∫ x, f x ^ 2 ∂(gaussianReal 0 1) - c ^ 2 := by ring
  rw [key] at hpoin
  exact hpoin

end

end GUEStrongConvergence
