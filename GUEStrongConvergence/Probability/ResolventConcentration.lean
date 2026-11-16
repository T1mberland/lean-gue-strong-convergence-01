/-
# Sharp ℓ² bounds for resolvent matrices

This file isolates the linear-algebraic heart of the Gaussian concentration of
resolvent pairings: for a matrix `R` with C⋆-norm bounded by `η`, the row
combination `w_k = ∑_a conj(u_a) R_{a k}` satisfies
`∑_k ‖w_k‖² ≤ η² ∑_k ‖u_k‖²`.

The proof goes through the positivity of the C⋆-matrix `η² • 1 - R R⋆`
(`CStarAlgebra.mul_star_le_algebraMap_norm_sq`) and the explicit quadratic form
`u ↦ ∑_{a,b} conj(u_a) M_{a b} u_b` on the positive cone.
-/
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.LinearAlgebra.Matrix.PosDef

open CStarModule WithCStarModule Matrix
open scoped WithCStarModule Matrix.Norms.Elementwise ComplexOrder

namespace GUEStrongConvergence

noncomputable section

variable {n : Type*} [Fintype n]

/-- The quadratic form of a complex matrix against a vector. -/
def quadform (M : CStarMatrix n n ℂ) (u : n → ℂ) : ℂ :=
  ∑ a, ∑ b, star (u a) * M a b * u b

/-- The quadratic form of `S⋆ S` is a sum of squared norms. -/
theorem quadform_star_mul_self (s : CStarMatrix n n ℂ) (u : n → ℂ) :
    (quadform (star s * s) u).re = ∑ c, ‖∑ b, s c b * u b‖ ^ 2 := by
  have hswap : ∀ F : n → n → n → ℂ,
      (∑ a, ∑ b, ∑ c, F a b c) = ∑ c, ∑ a, ∑ b, F a b c := by
    intro F
    rw [show (∑ a, ∑ b, ∑ c, F a b c) = ∑ a, ∑ c, ∑ b, F a b c from by
      apply Finset.sum_congr rfl
      intro a _
      exact Finset.sum_comm]
    exact Finset.sum_comm
  have key : ∀ a b, (star (u a) * (∑ c, star (s c a) * s c b)) * u b
      = ∑ c, star (u a) * star (s c a) * (s c b * u b) := by
    intro a b
    rw [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro c _
    ring
  have h : (quadform (star s * s) u)
      = ∑ c, (∑ a, star (u a) * star (s c a)) * (∑ b, s c b * u b) := by
    simp only [quadform, CStarMatrix.mul_apply, CStarMatrix.star_apply]
    rw [show (∑ a, ∑ b, (star (u a) * ∑ c, star (s c a) * s c b) * u b)
          = ∑ a, ∑ b, ∑ c, star (u a) * star (s c a) * (s c b * u b) from by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      exact key a b]
    rw [hswap]
    apply Finset.sum_congr rfl
    intro c _
    exact (Finset.sum_mul_sum Finset.univ Finset.univ
      (fun a => star (u a) * star (s c a)) (fun b => s c b * u b)).symm
  rw [h]
  have hc : ∀ c, ((∑ a, star (u a) * star (s c a)) * (∑ b, s c b * u b)).re
      = ‖∑ b, s c b * u b‖ ^ 2 := by
    intro c
    set z : ℂ := ∑ b, s c b * u b with hz
    have hza : (∑ a, star (u a) * star (s c a)) = star z := by
      rw [hz, star_sum]
      apply Finset.sum_congr rfl
      intro a _
      rw [star_mul]
    rw [hza]
    simp only [RCLike.star_def, Complex.conj_mul']
    rw [← Complex.ofReal_pow]
    exact Complex.ofReal_re _
  rw [Complex.re_sum]
  exact Finset.sum_congr rfl fun c _ => hc c

variable [DecidableEq n]

omit [DecidableEq n] in
/-- The quadratic form of a nonnegative C⋆-matrix has nonnegative real part. -/
theorem quadform_nonneg {M : CStarMatrix n n ℂ} (hM : 0 ≤ M) (u : n → ℂ) :
    0 ≤ (quadform M u).re := by
  rw [StarOrderedRing.nonneg_iff] at hM
  induction hM using AddSubmonoid.closure_induction with
  | mem x hx =>
    obtain ⟨s, rfl⟩ := hx
    rw [quadform_star_mul_self]
    exact Finset.sum_nonneg fun c _ => sq_nonneg _
  | zero => simp [quadform]
  | add x y hx hy ihx ihy =>
    have hsplit : quadform (x + y) u = quadform x u + quadform y u := by
      simp only [quadform, CStarMatrix.add_apply, mul_add, add_mul,
        Finset.sum_add_distrib]
    rw [hsplit, Complex.add_re]
    linarith

/-- The quadratic form of a real scalar matrix. -/
theorem quadform_algebraMap (c : ℝ) (u : n → ℂ) :
    quadform (algebraMap ℝ (CStarMatrix n n ℂ) c) u
      = (↑(c * ∑ k, ‖u k‖ ^ 2) : ℂ) := by
  have hone : (algebraMap ℝ (CStarMatrix n n ℂ) c) = c • (1 : CStarMatrix n n ℂ) := by
    rw [Algebra.algebraMap_eq_smul_one]
  rw [quadform, hone]
  simp only [CStarMatrix.smul_apply, CStarMatrix.one_apply]
  have hterm : ∀ a b, (star (u a) * c • (if a = b then (1:ℂ) else 0)) * u b
      = if a = b then (↑c * (star (u a) * u a)) else 0 := by
    intro a b
    by_cases h : a = b
    · subst h
      simp [Complex.real_smul]
      ring
    · simp [h]
  simp only [hterm, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  simp only [RCLike.star_def, Complex.conj_mul']
  rw [← Finset.mul_sum]
  have hsq : (∑ i, (↑‖u i‖ : ℂ) ^ 2) = ↑(∑ i, ‖u i‖ ^ 2) := by
    have hterm2 : ∀ i, (↑‖u i‖ : ℂ) ^ 2 = ↑(‖u i‖ ^ 2) := by
      intro i
      rw [← Complex.ofReal_pow]
    simp only [hterm2]
    rw [← Complex.ofReal_sum]
  rw [hsq, ← Complex.ofReal_mul]

/-- **Sharp ℓ² row bound.** For `‖R‖ ≤ η`, the row combinations of `R` against
`u` have squared ℓ² norm at most `η² ‖u‖²`. -/
theorem sum_sq_star_mul_le {R : CStarMatrix n n ℂ} {η : ℝ}
    (hR : ‖R‖ ≤ η) (hη : 0 ≤ η) (u : n → ℂ) :
    ∑ k, ‖∑ a, star (u a) * R a k‖ ^ 2 ≤ η ^ 2 * ∑ k, ‖u k‖ ^ 2 := by
  have hle : R * star R ≤ algebraMap ℝ (CStarMatrix n n ℂ) (‖R‖ ^ 2) :=
    CStarAlgebra.mul_star_le_algebraMap_norm_sq R
  have hM : 0 ≤ algebraMap ℝ (CStarMatrix n n ℂ) (‖R‖ ^ 2) - R * star R :=
    sub_nonneg.mpr hle
  have hq := quadform_nonneg hM u
  have hsub : quadform (algebraMap ℝ (CStarMatrix n n ℂ) (‖R‖ ^ 2) - R * star R) u
      = quadform (algebraMap ℝ (CStarMatrix n n ℂ) (‖R‖ ^ 2)) u -
        quadform (R * star R) u := by
    simp only [quadform, CStarMatrix.sub_apply, mul_sub, sub_mul,
      Finset.sum_sub_distrib]
  rw [hsub, quadform_algebraMap] at hq
  have hB : (quadform (R * star R) u).re ≤ ‖R‖ ^ 2 * ∑ k, ‖u k‖ ^ 2 := by
    have hcq : ((↑(‖R‖ ^ 2 * ∑ k, ‖u k‖ ^ 2) : ℂ)).re = ‖R‖ ^ 2 * ∑ k, ‖u k‖ ^ 2 :=
      Complex.ofReal_re _
    rw [Complex.sub_re, hcq] at hq
    linarith
  have hconv : ∀ c, ‖∑ b, (star R) c b * u b‖ = ‖∑ a, star (u a) * R a c‖ := by
    intro c
    have heq : (∑ b, (star R) c b * u b) = star (∑ a, star (u a) * R a c) := by
      rw [star_sum]
      apply Finset.sum_congr rfl
      intro a _
      rw [CStarMatrix.star_apply, star_mul]
      simp
    rw [heq, norm_star]
  have hsum : ∑ k, ‖∑ a, star (u a) * R a k‖ ^ 2
      = (quadform (R * star R) u).re := by
    rw [show (quadform (R * star R) u).re =
        (quadform (star (star R) * star R) u).re by rw [star_star],
      quadform_star_mul_self]
    apply Finset.sum_congr rfl
    intro k _
    rw [hconv k]
  rw [hsum]
  exact hB.trans (by
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun k _ => sq_nonneg _)
    nlinarith [norm_nonneg R])

end

end GUEStrongConvergence

namespace GUEStrongConvergence

noncomputable section

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **Sharp ℓ² column bound.** Companion of `sum_sq_star_mul_le`: for `‖R‖ ≤ η`,
the matrix-vector product against `u` has squared ℓ² norm at most `η² ‖u‖²`. -/
theorem sum_sq_mul_le {R : CStarMatrix n n ℂ} {η : ℝ}
    (hR : ‖R‖ ≤ η) (hη : 0 ≤ η) (u : n → ℂ) :
    ∑ k, ‖∑ a, R k a * u a‖ ^ 2 ≤ η ^ 2 * ∑ k, ‖u k‖ ^ 2 := by
  have hle : star R * R ≤ algebraMap ℝ (CStarMatrix n n ℂ) (‖R‖ ^ 2) :=
    CStarAlgebra.star_mul_le_algebraMap_norm_sq R
  have hM : 0 ≤ algebraMap ℝ (CStarMatrix n n ℂ) (‖R‖ ^ 2) - star R * R :=
    sub_nonneg.mpr hle
  have hq := quadform_nonneg hM u
  have hsub : quadform (algebraMap ℝ (CStarMatrix n n ℂ) (‖R‖ ^ 2) - star R * R) u
      = quadform (algebraMap ℝ (CStarMatrix n n ℂ) (‖R‖ ^ 2)) u -
        quadform (star R * R) u := by
    simp only [quadform, CStarMatrix.sub_apply, mul_sub, sub_mul,
      Finset.sum_sub_distrib]
  rw [hsub, quadform_algebraMap] at hq
  have hB : (quadform (star R * R) u).re ≤ ‖R‖ ^ 2 * ∑ k, ‖u k‖ ^ 2 := by
    have hcq : ((↑(‖R‖ ^ 2 * ∑ k, ‖u k‖ ^ 2) : ℂ)).re = ‖R‖ ^ 2 * ∑ k, ‖u k‖ ^ 2 :=
      Complex.ofReal_re _
    rw [Complex.sub_re, hcq] at hq
    linarith
  have hsum : ∑ k, ‖∑ a, R k a * u a‖ ^ 2 = (quadform (star R * R) u).re := by
    rw [quadform_star_mul_self]
  rw [hsum]
  exact hB.trans (by
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun k _ => sq_nonneg _)
    nlinarith [norm_nonneg R])

end

end GUEStrongConvergence
