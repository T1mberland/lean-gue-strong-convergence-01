/-
# Finite-product Gaussian Poincaré inequality

Specialises the finite-product Efron--Stein inequality to `γ = gaussianReal 0 1` and derives

`Var_{γ^⊗n}(F) ≤ ∑ p, ∫ x, (D_p F x)^2 dγ^⊗n(x)`

from the one-dimensional Gaussian Poincaré inequality applied to each coordinate fibre.

Hypotheses: `F ∈ L²(γ^⊗n)`, each `D p ∈ L²(γ^⊗n)`, almost every background tuple has a
differentiable `p`-th fibre with derivative `D p` evaluated at the updated tuple, and almost every
fibre (of `F` and of `D p`) has polynomial growth.  No coordinate Poincaré inequality is assumed;
the one-dimensional inequality is applied fibre-wise, and the `x`-integral of the fibre derivative
is collapsed back to `∫ (D p)^2` using the measure-preserving replacement map.
-/
import GUEStrongConvergence.Probability.FiniteTensorization
open MeasureTheory ProbabilityTheory Filter
open scoped ProbabilityTheory ENNReal NNReal Topology

namespace GUEStrongConvergence

noncomputable section

/-- The `n`-fold standard Gaussian product measure on `Fin n → ℝ`. -/
abbrev gaussianFinMeasure (n : ℕ) : Measure (Fin n → ℝ) :=
  Measure.pi (fun _ : Fin n => gaussianReal 0 1)

/-- **Finite-product Gaussian Poincaré inequality.**
For `F : (Fin n → ℝ) → ℝ` with coordinate derivatives `D p`,
`Var_{γ^⊗n}(F) ≤ ∑ p, ∫ x, (D p x)^2 dγ^⊗n(x)`. -/
theorem gaussian_poincare_fin {n : ℕ}
    {F : (Fin n → ℝ) → ℝ} {D : Fin n → (Fin n → ℝ) → ℝ}
    (hF : MemLp F 2 (gaussianFinMeasure n))
    (hDmem : ∀ p : Fin n, MemLp (D p) 2 (gaussianFinMeasure n))
    (hderiv : ∀ p : Fin n, ∀ᵐ x ∂(gaussianFinMeasure n), ∀ t : ℝ,
      HasDerivAt (fun u : ℝ => F (Function.update x p u)) (D p (Function.update x p t)) t)
    (hpoly : ∀ p : Fin n, ∀ᵐ x ∂(gaussianFinMeasure n),
      PolyGrowth (fun u : ℝ => F (Function.update x p u)) ∧
        PolyGrowth (fun u : ℝ => D p (Function.update x p u))) :
    variance F (gaussianFinMeasure n)
      ≤ ∑ p : Fin n,
          ∫ x, (D p x) ^ 2 ∂(gaussianFinMeasure n) := by
  cases n with
  | zero =>
      rw [variance_pi_fin_zero]
      simp
  | succ m =>
      have hEF := variance_pi_fin_le_sum_coordVar (μ := gaussianReal 0 1) (n := m + 1) F hF
      refine hEF.trans (Finset.sum_le_sum fun p _ => ?_)
      have hFp : MemLp (replaceSection F p) 2
          ((gaussianFinMeasure (m + 1)).prod (gaussianReal 0 1)) :=
        memLp_replaceSection (μ := gaussianReal 0 1) hF p
      have hDp : MemLp (fun z : (Fin (m + 1) → ℝ) × ℝ => D p (piReplace p z)) 2
          ((gaussianFinMeasure (m + 1)).prod (gaussianReal 0 1)) :=
        (hDmem p).comp_measurePreserving
          (measurePreserving_piReplace (α := ℝ) (μ := gaussianReal 0 1) p)
      have hpoint : ∀ᵐ x ∂(gaussianFinMeasure (m + 1)),
          variance (fun t => F (Function.update x p t)) (gaussianReal 0 1)
            ≤ ∫ t, (D p (piReplace p (x, t))) ^ 2 ∂(gaussianReal 0 1) := by
        filter_upwards [hderiv p, hpoly p, ae_memLp_sectionSnd hFp] with x hd hp hmem
        have hmem' : MemLp (fun t => F (Function.update x p t)) 2 (gaussianReal 0 1) :=
          hmem
        have hvar : variance (fun t => F (Function.update x p t)) (gaussianReal 0 1)
            = (∫ t, F (Function.update x p t) ^ 2 ∂(gaussianReal 0 1))
              - (∫ t, F (Function.update x p t) ∂(gaussianReal 0 1)) ^ 2 := by
          rw [variance_eq_sub hmem']
          simp only [Pi.pow_apply]
        have hpoin := gaussian_poincare_variance_poly
          (f := fun t => F (Function.update x p t))
          (f' := fun t => D p (Function.update x p t)) hd hp.1 hp.2
        rw [← hvar] at hpoin
        simpa [piReplace] using hpoin
      have hLHS : Integrable
          (fun x => variance (fun t => F (Function.update x p t)) (gaussianReal 0 1))
          (gaussianFinMeasure (m + 1)) := by
        have h := integrable_coordVar (α := ℝ) (μ := gaussianReal 0 1) hF p
        change Integrable
          (fun x => variance (fun t => F (Function.update x p t)) (gaussianReal 0 1))
          (gaussianFinMeasure (m + 1)) at h
        exact h
      have hRHS : Integrable
          (fun x => ∫ t, (D p (piReplace p (x, t))) ^ 2 ∂(gaussianReal 0 1))
          (gaussianFinMeasure (m + 1)) :=
        hDp.integrable_sq.integral_prod_left
      have hmono := integral_mono_ae hLHS hRHS hpoint
      have hprod : (∫ x, ∫ t, (D p (piReplace p (x, t))) ^ 2
            ∂(gaussianReal 0 1) ∂(gaussianFinMeasure (m + 1)))
          = ∫ z : (Fin (m + 1) → ℝ) × ℝ,
              (D p (piReplace p z)) ^ 2
                ∂((gaussianFinMeasure (m + 1)).prod (gaussianReal 0 1)) :=
        (integral_prod (fun z : (Fin (m + 1) → ℝ) × ℝ =>
          (D p (piReplace p z)) ^ 2) hDp.integrable_sq).symm
      have hcollapse : (∫ z : (Fin (m + 1) → ℝ) × ℝ,
            (D p (piReplace p z)) ^ 2
              ∂((gaussianFinMeasure (m + 1)).prod (gaussianReal 0 1)))
          = ∫ y, (D p y) ^ 2 ∂(gaussianFinMeasure (m + 1)) := by
        have hmp : MeasurePreserving (piReplace p)
            ((gaussianFinMeasure (m + 1)).prod (gaussianReal 0 1))
            (gaussianFinMeasure (m + 1)) :=
          measurePreserving_piReplace (α := ℝ) (μ := gaussianReal 0 1) p
        have h := integral_map
          (μ := (gaussianFinMeasure (m + 1)).prod (gaussianReal 0 1))
          (φ := piReplace p) (f := fun y : Fin (m + 1) → ℝ => (D p y) ^ 2)
          hmp.aemeasurable (by
            rw [hmp.map_eq]
            exact (hDmem p).aestronglyMeasurable.pow 2)
        rw [hmp.map_eq] at h
        exact h.symm
      calc (∫ x, coordVar (μ := gaussianReal 0 1) F p x
              ∂(gaussianFinMeasure (m + 1)))
          = ∫ x, variance (fun t => F (Function.update x p t)) (gaussianReal 0 1)
              ∂(gaussianFinMeasure (m + 1)) := by
              simp [coordVar]
        _ ≤ ∫ x, ∫ t, (D p (piReplace p (x, t))) ^ 2
              ∂(gaussianReal 0 1) ∂(gaussianFinMeasure (m + 1)) := hmono
        _ = ∫ z : (Fin (m + 1) → ℝ) × ℝ,
              (D p (piReplace p z)) ^ 2
                ∂((gaussianFinMeasure (m + 1)).prod (gaussianReal 0 1)) := hprod
        _ = ∫ y, (D p y) ^ 2 ∂(gaussianFinMeasure (m + 1)) := hcollapse

end

end GUEStrongConvergence
