/-
# Exact second moment of a matrix-coefficient mixed trace

For fixed matrices `A B : Matrix (Fin N) (Fin N) ℂ` and a normalized complex GUE matrix
`X = gueMatrix x i`, the exact finite-`N` second moment with two coefficient insertions is

  `E tr(A X B X) = tr(A) tr(B) / N`,

i.e. in normalized-trace form `E τ_N(A X B X) = τ_N(A) τ_N(B)`, **exactly, for every `N`**.

This settles the question whether matrix-coefficient insertions introduce `1/N` corrections to
the genus expansion: they do **not**.  The single GUE Wick contraction is

  `E[X_ab X_cd] = δ_ad δ_bc / N`   (`integral_gueMatrix_mul`),

so the two `X` insertions contract with each other on *both* index pairs, and each coefficient
matrix only sees the diagonal: the `1/N` from the covariance is exactly compensated by the `N`
of the free diagonal sum.  Equivalently: the coefficient insertions do not consume an `N`-factor,
consistently with `MixedTrace.integral_gueNormalizedMixedTrace : E τ_N(G_i G_j) = δ_ij` exactly.

Consequence for the pencil side: the mixed-trace mean is `N⁰`-accurate at this order, so it is
*not* a source of `1/N` errors; the `N^{-2}` mean input of `FlatLemmaM` is combinatorially
consistent with matrix coefficients.

No `sorry`/axiom is used.
-/
import GUEStrongConvergence.Probability.GUEModel

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped Matrix.Norms.Elementwise Topology

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace GUEStrongConvergence

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {N : ℕ}

/-- Integrability of a finite sum of integrable functions. -/
theorem integrable_finset_sum_univ {g : Fin N → EuclideanSpace ℝ (GUECoord ι N) → ℂ}
    (h : ∀ i, Integrable (g i) (stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))) :
    Integrable (fun x => ∑ i : Fin N, g i x)
      (stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) := by
  have hh := integrable_finsetSum' (μ := stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))
    (Finset.univ : Finset (Fin N)) (f := g) (fun i _ => h i)
  exact hh.congr (Eventually.of_forall fun x => by simp only [Finset.sum_apply])

/-- Integrability of a four-fold finite sum of integrable functions. -/
theorem integrable_sum4 {F : (Fin N) → (Fin N) → (Fin N) → (Fin N)
    → EuclideanSpace ℝ (GUECoord ι N) → ℂ}
    (hF : ∀ a m l k, Integrable (F a m l k)
      (stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))) :
    Integrable (fun x => ∑ a : Fin N, ∑ m : Fin N, ∑ l : Fin N, ∑ k : Fin N, F a m l k x)
      (stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) :=
  integrable_finset_sum_univ fun a => integrable_finset_sum_univ fun m =>
    integrable_finset_sum_univ fun l => integrable_finset_sum_univ fun k => hF a m l k

/-- The integral of a four-fold finite sum is the four-fold sum of the integrals. -/
theorem integral_sum4 {F : (Fin N) → (Fin N) → (Fin N) → (Fin N)
    → EuclideanSpace ℝ (GUECoord ι N) → ℂ}
    (hF : ∀ a m l k, Integrable (F a m l k)
      (stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))) :
    ∫ x : EuclideanSpace ℝ (GUECoord ι N),
        (∑ a : Fin N, ∑ m : Fin N, ∑ l : Fin N, ∑ k : Fin N, F a m l k x)
        ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))
      = ∑ a : Fin N, ∑ m : Fin N, ∑ l : Fin N, ∑ k : Fin N,
          ∫ x : EuclideanSpace ℝ (GUECoord ι N), F a m l k x
            ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) := by
  have h1 : ∫ x : EuclideanSpace ℝ (GUECoord ι N),
        (∑ a : Fin N, ∑ m : Fin N, ∑ l : Fin N, ∑ k : Fin N, F a m l k x)
        ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))
      = ∑ a : Fin N, ∫ x : EuclideanSpace ℝ (GUECoord ι N),
          (∑ m : Fin N, ∑ l : Fin N, ∑ k : Fin N, F a m l k x)
          ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) :=
    integral_finsetSum (s := (Finset.univ : Finset (Fin N)))
      (f := fun a x => ∑ m : Fin N, ∑ l : Fin N, ∑ k : Fin N, F a m l k x)
      (fun a _ => integrable_finset_sum_univ fun m => integrable_finset_sum_univ fun l =>
        integrable_finset_sum_univ fun k => hF a m l k)
  rw [h1]
  refine Finset.sum_congr rfl fun a _ => ?_
  have h2 : ∫ x : EuclideanSpace ℝ (GUECoord ι N),
        (∑ m : Fin N, ∑ l : Fin N, ∑ k : Fin N, F a m l k x)
        ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))
      = ∑ m : Fin N, ∫ x : EuclideanSpace ℝ (GUECoord ι N),
          (∑ l : Fin N, ∑ k : Fin N, F a m l k x)
          ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) :=
    integral_finsetSum (s := (Finset.univ : Finset (Fin N)))
      (f := fun m x => ∑ l : Fin N, ∑ k : Fin N, F a m l k x)
      (fun m _ => integrable_finset_sum_univ fun l => integrable_finset_sum_univ fun k =>
        hF a m l k)
  rw [h2]
  refine Finset.sum_congr rfl fun m _ => ?_
  have h3 : ∫ x : EuclideanSpace ℝ (GUECoord ι N),
        (∑ l : Fin N, ∑ k : Fin N, F a m l k x)
        ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))
      = ∑ l : Fin N, ∫ x : EuclideanSpace ℝ (GUECoord ι N),
          (∑ k : Fin N, F a m l k x)
          ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) :=
    integral_finsetSum (s := (Finset.univ : Finset (Fin N)))
      (f := fun l x => ∑ k : Fin N, F a m l k x)
      (fun l _ => integrable_finset_sum_univ fun k => hF a m l k)
  rw [h3]
  exact Finset.sum_congr rfl fun l _ =>
    integral_finsetSum (s := (Finset.univ : Finset (Fin N)))
      (f := fun k x => F a m l k x) (fun k _ => hF a m l k)

/-- The pointwise expansion of `tr(A X B X)` into the four index sums. -/
theorem trace_mul_gueMatrix_mul_gueMatrix_eq_sum (A B : Matrix (Fin N) (Fin N) ℂ)
    (i : ι) (x : GUECoord ι N → ℝ) :
    Matrix.trace (A * gueMatrix x i * B * gueMatrix x i)
      = ∑ a : Fin N, ∑ m : Fin N, ∑ l : Fin N, ∑ k : Fin N,
          A a k * gueMatrix x i k l * B l m * gueMatrix x i m a := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Finset.sum_mul]

/-- **Exact second moment with two matrix-coefficient insertions**:
`E tr(A X B X) = tr(A) tr(B) / N`. -/
theorem integral_trace_mul_gueMatrix_mul_gueMatrix (A B : Matrix (Fin N) (Fin N) ℂ) (i : ι) :
    ∫ x : EuclideanSpace ℝ (GUECoord ι N),
        Matrix.trace (A * gueMatrix x i * B * gueMatrix x i)
        ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))
      = (N : ℂ)⁻¹ * Matrix.trace A * Matrix.trace B := by
  classical
  -- the value of the integral of one summand
  have hval : ∀ (a m l k : Fin N),
      ∫ x : EuclideanSpace ℝ (GUECoord ι N),
          A a k * gueMatrix x i k l * B l m * gueMatrix x i m a
          ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))
        = A a k * B l m * (if k = a ∧ l = m then ((N : ℝ)⁻¹ : ℂ) else 0) := by
    intro a m l k
    have hcongr : (fun x : EuclideanSpace ℝ (GUECoord ι N) =>
        A a k * gueMatrix x i k l * B l m * gueMatrix x i m a)
        = fun x : EuclideanSpace ℝ (GUECoord ι N) =>
          (A a k * B l m) * (gueMatrix x i k l * gueMatrix x i m a) := by
      funext x
      ring
    rw [hcongr, integral_const_mul, integral_gueMatrix_mul]
    simp only [ite_and]
    split_ifs <;> ring
  -- integrability of one summand
  have hInt : ∀ (a m l k : Fin N), Integrable (fun x : EuclideanSpace ℝ (GUECoord ι N) =>
      A a k * gueMatrix x i k l * B l m * gueMatrix x i m a)
      (stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) := by
    intro a m l k
    have h1 : Integrable (fun x : EuclideanSpace ℝ (GUECoord ι N) =>
        (A a k * B l m) * (gueMatrix x i k l * gueMatrix x i m a))
        (stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) :=
      (integrable_gueMatrix_mul i i k l m a).const_mul _
    exact h1.congr (Eventually.of_forall fun x => by ring)
  -- the four-fold sum collapses
  have hcollapse : ∀ (c : ℂ), (∑ a : Fin N, ∑ m : Fin N, ∑ l : Fin N, ∑ k : Fin N,
      A a k * B l m * (if k = a ∧ l = m then c else 0))
      = c * (∑ a : Fin N, A a a) * (∑ l : Fin N, B l l) := by
    intro c
    have hsummand : ∀ (a m l k : Fin N),
        A a k * B l m * (if k = a ∧ l = m then c else 0)
          = (if k = a then A a k else 0) * (if l = m then c * B l m else 0) := by
      intro a m l k
      by_cases h1 : k = a <;> by_cases h2 : l = m <;>
        simp only [h1, h2, if_true, if_false, and_self, and_false, false_and,
          mul_zero, zero_mul] <;>
        first
          | rfl
          | ring
    simp only [hsummand]
    -- reorder the two inner sums
    have hreorder : (∑ a : Fin N, ∑ m : Fin N, ∑ l : Fin N, ∑ k : Fin N,
        (if k = a then A a k else 0) * (if l = m then c * B l m else 0))
        = ∑ a : Fin N, ∑ l : Fin N, ∑ m : Fin N, ∑ k : Fin N,
            (if k = a then A a k else 0) * (if l = m then c * B l m else 0) := by
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.sum_comm]
    rw [hreorder]
    have hfac : (∑ a : Fin N, ∑ l : Fin N, ∑ m : Fin N, ∑ k : Fin N,
        (if k = a then A a k else 0) * (if l = m then c * B l m else 0))
        = (∑ a : Fin N, ∑ k : Fin N, if k = a then A a k else 0) *
          (∑ l : Fin N, ∑ m : Fin N, if l = m then c * B l m else 0) := by
      rw [Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [Finset.sum_mul_sum]
      rw [Finset.sum_comm]
    rw [hfac]
    have hA : (∑ a : Fin N, ∑ k : Fin N, if k = a then A a k else 0)
        = ∑ a : Fin N, A a a := by
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.sum_ite_eq']
      simp
    have hB : (∑ l : Fin N, ∑ m : Fin N, if l = m then c * B l m else 0)
        = c * ∑ l : Fin N, B l l := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [Finset.sum_ite_eq]
      simp
    rw [hA, hB]
    ring
  calc ∫ x : EuclideanSpace ℝ (GUECoord ι N),
        Matrix.trace (A * gueMatrix x i * B * gueMatrix x i)
        ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))
      = ∫ x : EuclideanSpace ℝ (GUECoord ι N),
          (∑ a : Fin N, ∑ m : Fin N, ∑ l : Fin N, ∑ k : Fin N,
            A a k * gueMatrix x i k l * B l m * gueMatrix x i m a)
          ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) := by
        simp only [trace_mul_gueMatrix_mul_gueMatrix_eq_sum]
    _ = ∑ a : Fin N, ∑ m : Fin N, ∑ l : Fin N, ∑ k : Fin N,
          A a k * B l m * (if k = a ∧ l = m then ((N : ℝ)⁻¹ : ℂ) else 0) := by
        refine (integral_sum4 (fun a m l k => hInt a m l k)).trans ?_
        exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun m _ =>
          Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => hval a m l k
    _ = (N : ℂ)⁻¹ * Matrix.trace A * Matrix.trace B := by
        rw [hcollapse]
        simp only [Matrix.trace, Matrix.diag, Complex.ofReal_natCast]

/-- **Normalized form**: `E τ_N(A X B X) = τ_N(A) τ_N(B)` exactly, for every `N`; in
particular there is no `1/N` correction term. -/
theorem integral_normalizedTrace_mul_gueMatrix_mul_gueMatrix
    (A B : Matrix (Fin N) (Fin N) ℂ) (i : ι) :
    ∫ x : EuclideanSpace ℝ (GUECoord ι N),
        (N : ℂ)⁻¹ * Matrix.trace (A * gueMatrix x i * B * gueMatrix x i)
        ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))
      = ((N : ℂ)⁻¹ * Matrix.trace A) * ((N : ℂ)⁻¹ * Matrix.trace B) := by
  rw [integral_const_mul, integral_trace_mul_gueMatrix_mul_gueMatrix]
  ring

end

end GUEStrongConvergence
