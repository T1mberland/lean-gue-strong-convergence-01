/-
# Sparse direction-pairing norm bound

The direction matrices of the GUE pencil are supported on at most two slices of
the coordinate index.  This file turns `direction_pairing_eq` into the sharp
sum-of-squares bound that feeds the Gaussian concentration of resolvent
pairings.  The constant is `2 * gueScale N ^ 2 * ∑ᵢ ‖Aᵢ‖²_F`, i.e. of order
`1/N`, with no hidden dimension factor.
-/
import GUEStrongConvergence.Probability.ResolventPencilPairing
import GUEStrongConvergence.Probability.ResolventConcentration
import GUEStrongConvergence.Probability.GUEModel

open MeasureTheory Matrix Kronecker
open scoped Matrix.Norms.Elementwise ComplexOrder

namespace GUEStrongConvergence

noncomputable section

variable {ι d : Type*} {N : ℕ} [Fintype ι] [Fintype d] [DecidableEq d] [DecidableEq ι]

/-- Frobenius norm of a finite complex matrix. -/
def frob (M : Matrix d d ℂ) : ℝ := Real.sqrt (∑ c, ∑ c', ‖M c c'‖ ^ 2)

lemma frob_nonneg (M : Matrix d d ℂ) : 0 ≤ frob M := Real.sqrt_nonneg _

lemma frob_sq (M : Matrix d d ℂ) : (frob M) ^ 2 = ∑ c, ∑ c', ‖M c c'‖ ^ 2 := by
  rw [frob, Real.sq_sqrt]
  exact Finset.sum_nonneg fun c _ => Finset.sum_nonneg fun c' _ => sq_nonneg _

/-- Cauchy–Schwarz for a matrix bilinear form on the full `d × d` index set. -/
theorem abs_inner_slice_le (M : Matrix d d ℂ) (W Z : d → ℂ) :
    ‖∑ c, ∑ c', star (W c) * M c c' * Z c'‖ ≤
      frob M * Real.sqrt (∑ c, ‖W c‖ ^ 2) * Real.sqrt (∑ c, ‖Z c‖ ^ 2) := by
  have h1 : ‖∑ c, ∑ c', star (W c) * M c c' * Z c'‖ ≤
      ∑ c, ∑ c', ‖W c‖ * ‖M c c'‖ * ‖Z c'‖ := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun c _ => ?_)
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun c' _ => ?_)
    rw [norm_mul, norm_mul, norm_star]
  set P : ℝ := ∑ c, ∑ c', ‖M c c'‖ ^ 2 with hP
  set Q : ℝ := (∑ c, ‖W c‖ ^ 2) * (∑ c, ‖Z c‖ ^ 2) with hQ
  have hQ' : Q = ∑ c, ∑ c', ‖W c‖ ^ 2 * ‖Z c'‖ ^ 2 := by
    rw [hQ, Finset.sum_mul_sum]
  have h2 : (∑ c, ∑ c', ‖W c‖ * ‖M c c'‖ * ‖Z c'‖) ^ 2 ≤ P * Q := by
    rw [hP, hQ']
    rw [show (∑ c, ∑ c', ‖W c‖ * ‖M c c'‖ * ‖Z c'‖)
        = ∑ p : d × d, ‖M p.1 p.2‖ * (‖W p.1‖ * ‖Z p.2‖) from by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro c _
      apply Finset.sum_congr rfl
      intro c' _
      ring]
    rw [show (∑ c, ∑ c', ‖M c c'‖ ^ 2) = ∑ p : d × d, ‖M p.1 p.2‖ ^ 2 from by
      rw [Fintype.sum_prod_type]]
    rw [show (∑ c, ∑ c', ‖W c‖ ^ 2 * ‖Z c'‖ ^ 2)
        = ∑ p : d × d, (‖W p.1‖ * ‖Z p.2‖) ^ 2 from by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro c _
      apply Finset.sum_congr rfl
      intro c' _
      ring]
    exact Finset.sum_mul_sq_le_sq_mul_sq Finset.univ _ _
  have hS : 0 ≤ ∑ c, ∑ c', ‖W c‖ * ‖M c c'‖ * ‖Z c'‖ :=
    Finset.sum_nonneg fun c _ => Finset.sum_nonneg fun c' _ => by positivity
  have hP0 : 0 ≤ P := by
    rw [hP]
    exact Finset.sum_nonneg fun c _ => Finset.sum_nonneg fun c' _ => sq_nonneg _
  have hQ0 : 0 ≤ Q := by
    rw [hQ]
    exact mul_nonneg (Finset.sum_nonneg fun c _ => sq_nonneg _)
      (Finset.sum_nonneg fun c _ => sq_nonneg _)
  have h3 : ∑ c, ∑ c', ‖W c‖ * ‖M c c'‖ * ‖Z c'‖ ≤ Real.sqrt (P * Q) :=
    Real.le_sqrt_of_sq_le h2
  refine h1.trans (h3.trans ?_)
  rw [Real.sqrt_mul hP0, hQ, Real.sqrt_mul (Finset.sum_nonneg fun c _ => sq_nonneg _),
    mul_assoc]
  rfl

/-- The slice bilinear form is bounded by the Frobenius norm and the slice ℓ² norms. -/
theorem norm_sq_pairing_slice_le (M : Matrix d d ℂ) (W Z : d → ℂ) :
    ‖∑ c, ∑ c', W c * M c c' * Z c'‖ ^ 2 ≤
      (frob M) ^ 2 * (∑ c, ‖W c‖ ^ 2) * (∑ c, ‖Z c‖ ^ 2) := by
  have h := abs_inner_slice_le M (fun c => star (W c)) Z
  simp only [norm_star, star_star] at h
  have hA0 : 0 ≤ ∑ c, ‖W c‖ ^ 2 := Finset.sum_nonneg fun c _ => sq_nonneg _
  have hB0 : 0 ≤ ∑ c, ‖Z c‖ ^ 2 := Finset.sum_nonneg fun c _ => sq_nonneg _
  have hstep : ‖∑ c, ∑ c', W c * M c c' * Z c'‖ ^ 2 ≤
      (frob M * Real.sqrt (∑ c, ‖W c‖ ^ 2) * Real.sqrt (∑ c, ‖Z c‖ ^ 2)) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) h 2
  calc ‖∑ c, ∑ c', W c * M c c' * Z c'‖ ^ 2
      ≤ (frob M * Real.sqrt (∑ c, ‖W c‖ ^ 2) * Real.sqrt (∑ c, ‖Z c‖ ^ 2)) ^ 2 := hstep
    _ = (frob M) ^ 2 * (∑ c, ‖W c‖ ^ 2) * (∑ c, ‖Z c‖ ^ 2) := by
      rw [mul_pow, mul_pow, Real.sq_sqrt hA0, Real.sq_sqrt hB0]

/-- Summing the slice ℓ² norms over the slice index gives the full ℓ² norm. -/
theorem sum_slice_norm_sq (W : d × Fin N → ℂ) :
    (∑ a : Fin N, ∑ x : d, ‖W (x, a)‖ ^ 2) = ∑ k : d × Fin N, ‖W k‖ ^ 2 := by
  rw [Finset.sum_comm]
  exact (Fintype.sum_prod_type (f := fun k : d × Fin N => ‖W k‖ ^ 2)).symm

/-- Explicit multiplication of three finite sums. -/
theorem sum_mul_sum_three {ι ν : Type*} [Fintype ι] [Fintype ν]
    (f : ι → ℝ) (A B : ν → ℝ) :
    (∑ i, f i) * (∑ a, A a) * (∑ b, B b) = ∑ i, ∑ a, ∑ b, f i * A a * B b := by
  have h1 : (∑ i, f i) * (∑ a, A a) = ∑ i, ∑ a, f i * A a :=
    Finset.sum_mul_sum Finset.univ Finset.univ f A
  have h2 : (∑ i, ∑ a, f i * A a) * (∑ b, B b) = ∑ i, ∑ a, ∑ b, f i * A a * B b := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    exact Finset.sum_mul_sum Finset.univ Finset.univ (fun a => f i * A a) B
  rw [h1, h2]

/-- Factorization of the slice weights over the direction index. -/
theorem sum_prod_slice_weights (A : ι → Matrix d d ℂ) (W Z : d × Fin N → ℂ) :
    (∑ i : ι, ∑ a : Fin N, ∑ b : Fin N,
        (frob (A i)) ^ 2 * (∑ x : d, ‖W (x, a)‖ ^ 2) * (∑ x2 : d, ‖Z (x2, b)‖ ^ 2))
      = (∑ i, (frob (A i)) ^ 2) * (∑ k : d × Fin N, ‖W k‖ ^ 2)
          * (∑ k : d × Fin N, ‖Z k‖ ^ 2) := by
  rw [show (∑ k : d × Fin N, ‖W k‖ ^ 2)
        = ∑ a : Fin N, ∑ x : d, ‖W (x, a)‖ ^ 2 from (sum_slice_norm_sq W).symm,
    show (∑ k : d × Fin N, ‖Z k‖ ^ 2)
        = ∑ b : Fin N, ∑ x2 : d, ‖Z (x2, b)‖ ^ 2 from (sum_slice_norm_sq Z).symm]
  exact (sum_mul_sum_three (fun i => (frob (A i)) ^ 2)
    (fun a => ∑ x : d, ‖W (x, a)‖ ^ 2)
    (fun b => ∑ x2 : d, ‖Z (x2, b)‖ ^ 2)).symm

/-- Swapped variant of the slice-weight factorization (for the `β` half). -/
theorem sum_prod_slice_weights_swap (A : ι → Matrix d d ℂ) (W Z : d × Fin N → ℂ) :
    (∑ i : ι, ∑ a : Fin N, ∑ b : Fin N,
        (frob (A i)) ^ 2 * (∑ x : d, ‖W (x, b)‖ ^ 2) * (∑ x2 : d, ‖Z (x2, a)‖ ^ 2))
      = (∑ i, (frob (A i)) ^ 2) * (∑ k : d × Fin N, ‖W k‖ ^ 2)
          * (∑ k : d × Fin N, ‖Z k‖ ^ 2) := by
  rw [show (∑ i : ι, ∑ a : Fin N, ∑ b : Fin N,
        (frob (A i)) ^ 2 * (∑ x : d, ‖W (x, b)‖ ^ 2) * (∑ x2 : d, ‖Z (x2, a)‖ ^ 2))
      = ∑ i : ι, ∑ b : Fin N, ∑ a : Fin N,
        (frob (A i)) ^ 2 * (∑ x : d, ‖W (x, b)‖ ^ 2) * (∑ x2 : d, ‖Z (x2, a)‖ ^ 2) from by
    apply Finset.sum_congr rfl
    intro i _
    exact Finset.sum_comm]
  exact sum_prod_slice_weights A W Z

/-- The squares of the complex weights `α`, `β` sum to one. -/
theorem norm_gueAlpha_sq_add_norm_gueBeta_sq : ‖gueAlpha‖ ^ 2 + ‖gueBeta‖ ^ 2 = 1 := by
  have h1 : ‖gueAlpha‖ ^ 2 = (1:ℝ) / 2 := by
    rw [Complex.sq_norm]
    simp [gueAlpha, Complex.normSq]
    norm_num
  have h2 : ‖gueBeta‖ ^ 2 = (1:ℝ) / 2 := by
    rw [Complex.sq_norm]
    simp [gueBeta, Complex.normSq]
    norm_num
  rw [h1, h2]; norm_num

/-- Pointwise bound for the `α`-half at a fixed direction. -/
theorem alpha_slice_pointwise_le (A : ι → Matrix d d ℂ) (W Z : d × Fin N → ℂ)
    (p : GUECoord ι N) :
    ‖∑ x : d, ∑ x2 : d,
        (gueScale N : ℂ) * gueAlpha *
          (W (x, p.2.1) * A p.1 x x2 * Z (x2, p.2.2))‖ ^ 2
      ≤ (gueScale N) ^ 2 * ‖gueAlpha‖ ^ 2 *
          ((frob (A p.1)) ^ 2 *
            (∑ x : d, ‖W (x, p.2.1)‖ ^ 2) * (∑ x2 : d, ‖Z (x2, p.2.2)‖ ^ 2)) := by
  obtain ⟨i, q⟩ := p
  obtain ⟨a, b⟩ := q
  have hfact : (∑ x : d, ∑ x2 : d,
        (gueScale N : ℂ) * gueAlpha *
          (W (x, a) * A i x x2 * Z (x2, b)))
      = ((gueScale N : ℂ) * gueAlpha) *
          (∑ x : d, ∑ x2 : d, W (x, a) * A i x x2 * Z (x2, b)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    rw [Finset.mul_sum]
  rw [hfact, norm_mul, mul_pow]
  have hnorm : ‖((gueScale N : ℂ) * gueAlpha)‖ ^ 2 =
      (gueScale N) ^ 2 * ‖gueAlpha‖ ^ 2 := by
    rw [norm_mul, mul_pow]
    congr 1
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (gueScale_nonneg N)]
  rw [hnorm]
  have hP := norm_sq_pairing_slice_le (A i) (fun x => W (x, a)) (fun x2 => Z (x2, b))
  exact mul_le_mul_of_nonneg_left hP (by positivity)

/-- Pointwise bound for the `β`-half at a fixed direction. -/
theorem beta_slice_pointwise_le (A : ι → Matrix d d ℂ) (W Z : d × Fin N → ℂ)
    (p : GUECoord ι N) :
    ‖∑ x : d, ∑ x2 : d,
        (gueScale N : ℂ) * gueBeta *
          (W (x, p.2.2) * A p.1 x x2 * Z (x2, p.2.1))‖ ^ 2
      ≤ (gueScale N) ^ 2 * ‖gueBeta‖ ^ 2 *
          ((frob (A p.1)) ^ 2 *
            (∑ x : d, ‖W (x, p.2.2)‖ ^ 2) * (∑ x2 : d, ‖Z (x2, p.2.1)‖ ^ 2)) := by
  obtain ⟨i, q⟩ := p
  obtain ⟨a, b⟩ := q
  have hfact : (∑ x : d, ∑ x2 : d,
        (gueScale N : ℂ) * gueBeta *
          (W (x, b) * A i x x2 * Z (x2, a)))
      = ((gueScale N : ℂ) * gueBeta) *
          (∑ x : d, ∑ x2 : d, W (x, b) * A i x x2 * Z (x2, a)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    rw [Finset.mul_sum]
  rw [hfact, norm_mul, mul_pow]
  have hnorm : ‖((gueScale N : ℂ) * gueBeta)‖ ^ 2 =
      (gueScale N) ^ 2 * ‖gueBeta‖ ^ 2 := by
    rw [norm_mul, mul_pow]
    congr 1
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (gueScale_nonneg N)]
  rw [hnorm]
  have hP := norm_sq_pairing_slice_le (A i) (fun x => W (x, b)) (fun x2 => Z (x2, a))
  exact mul_le_mul_of_nonneg_left hP (by positivity)

/-- The `α`-half of the sparse direction-pairing bound. -/
theorem sum_sq_alpha_slice_le (A : ι → Matrix d d ℂ) (W Z : d × Fin N → ℂ) :
    ∑ p : GUECoord ι N,
        ‖∑ x : d, ∑ x2 : d,
          (gueScale N : ℂ) * gueAlpha *
            (W (x, p.2.1) * A p.1 x x2 * Z (x2, p.2.2))‖ ^ 2
      ≤ (gueScale N) ^ 2 * ‖gueAlpha‖ ^ 2 * (∑ i, (frob (A i)) ^ 2)
          * (∑ k : d × Fin N, ‖W k‖ ^ 2) * (∑ k : d × Fin N, ‖Z k‖ ^ 2) := by
  have hsum_eq : (∑ p : GUECoord ι N, ((frob (A p.1)) ^ 2 *
        (∑ x : d, ‖W (x, p.2.1)‖ ^ 2) * (∑ x2 : d, ‖Z (x2, p.2.2)‖ ^ 2)))
      = (∑ i, (frob (A i)) ^ 2) * (∑ k : d × Fin N, ‖W k‖ ^ 2)
          * (∑ k : d × Fin N, ‖Z k‖ ^ 2) := by
    rw [Fintype.sum_prod_type]
    rw [show (∑ i : ι, ∑ q : Fin N × Fin N, ((frob (A i)) ^ 2 *
          (∑ x : d, ‖W (x, q.1)‖ ^ 2) * (∑ x2 : d, ‖Z (x2, q.2)‖ ^ 2)))
        = ∑ i : ι, ∑ a : Fin N, ∑ b : Fin N, ((frob (A i)) ^ 2 *
          (∑ x : d, ‖W (x, a)‖ ^ 2) * (∑ x2 : d, ‖Z (x2, b)‖ ^ 2)) from by
      apply Finset.sum_congr rfl
      intro i _
      rw [Fintype.sum_prod_type]]
    exact sum_prod_slice_weights A W Z
  calc ∑ p : GUECoord ι N,
        ‖∑ x : d, ∑ x2 : d,
          (gueScale N : ℂ) * gueAlpha *
            (W (x, p.2.1) * A p.1 x x2 * Z (x2, p.2.2))‖ ^ 2
      ≤ ∑ p : GUECoord ι N, (gueScale N) ^ 2 * ‖gueAlpha‖ ^ 2 *
          ((frob (A p.1)) ^ 2 *
            (∑ x : d, ‖W (x, p.2.1)‖ ^ 2) * (∑ x2 : d, ‖Z (x2, p.2.2)‖ ^ 2)) :=
        Finset.sum_le_sum fun p _ => alpha_slice_pointwise_le A W Z p
    _ = (gueScale N) ^ 2 * ‖gueAlpha‖ ^ 2 *
          ∑ p : GUECoord ι N, ((frob (A p.1)) ^ 2 *
            (∑ x : d, ‖W (x, p.2.1)‖ ^ 2) * (∑ x2 : d, ‖Z (x2, p.2.2)‖ ^ 2)) := by
        conv_rhs => rw [Finset.mul_sum]
    _ = (gueScale N) ^ 2 * ‖gueAlpha‖ ^ 2 *
          ((∑ i, (frob (A i)) ^ 2) * (∑ k : d × Fin N, ‖W k‖ ^ 2) *
            (∑ k : d × Fin N, ‖Z k‖ ^ 2)) := by
        rw [hsum_eq]
    _ = (gueScale N) ^ 2 * ‖gueAlpha‖ ^ 2 * (∑ i, (frob (A i)) ^ 2)
          * (∑ k : d × Fin N, ‖W k‖ ^ 2) * (∑ k : d × Fin N, ‖Z k‖ ^ 2) := by
        ring

/-- The `β`-half of the sparse direction-pairing bound. -/
theorem sum_sq_beta_slice_le (A : ι → Matrix d d ℂ) (W Z : d × Fin N → ℂ) :
    ∑ p : GUECoord ι N,
        ‖∑ x : d, ∑ x2 : d,
          (gueScale N : ℂ) * gueBeta *
            (W (x, p.2.2) * A p.1 x x2 * Z (x2, p.2.1))‖ ^ 2
      ≤ (gueScale N) ^ 2 * ‖gueBeta‖ ^ 2 * (∑ i, (frob (A i)) ^ 2)
          * (∑ k : d × Fin N, ‖W k‖ ^ 2) * (∑ k : d × Fin N, ‖Z k‖ ^ 2) := by
  have hsum_eq : (∑ p : GUECoord ι N, ((frob (A p.1)) ^ 2 *
        (∑ x : d, ‖W (x, p.2.2)‖ ^ 2) * (∑ x2 : d, ‖Z (x2, p.2.1)‖ ^ 2)))
      = (∑ i, (frob (A i)) ^ 2) * (∑ k : d × Fin N, ‖W k‖ ^ 2)
          * (∑ k : d × Fin N, ‖Z k‖ ^ 2) := by
    rw [Fintype.sum_prod_type]
    rw [show (∑ i : ι, ∑ q : Fin N × Fin N, ((frob (A i)) ^ 2 *
          (∑ x : d, ‖W (x, q.2)‖ ^ 2) * (∑ x2 : d, ‖Z (x2, q.1)‖ ^ 2)))
        = ∑ i : ι, ∑ a : Fin N, ∑ b : Fin N, ((frob (A i)) ^ 2 *
          (∑ x : d, ‖W (x, b)‖ ^ 2) * (∑ x2 : d, ‖Z (x2, a)‖ ^ 2)) from by
      apply Finset.sum_congr rfl
      intro i _
      rw [Fintype.sum_prod_type]]
    exact sum_prod_slice_weights_swap A W Z
  calc ∑ p : GUECoord ι N,
        ‖∑ x : d, ∑ x2 : d,
          (gueScale N : ℂ) * gueBeta *
            (W (x, p.2.2) * A p.1 x x2 * Z (x2, p.2.1))‖ ^ 2
      ≤ ∑ p : GUECoord ι N, (gueScale N) ^ 2 * ‖gueBeta‖ ^ 2 *
          ((frob (A p.1)) ^ 2 *
            (∑ x : d, ‖W (x, p.2.2)‖ ^ 2) * (∑ x2 : d, ‖Z (x2, p.2.1)‖ ^ 2)) :=
        Finset.sum_le_sum fun p _ => beta_slice_pointwise_le A W Z p
    _ = (gueScale N) ^ 2 * ‖gueBeta‖ ^ 2 *
          ∑ p : GUECoord ι N, ((frob (A p.1)) ^ 2 *
            (∑ x : d, ‖W (x, p.2.2)‖ ^ 2) * (∑ x2 : d, ‖Z (x2, p.2.1)‖ ^ 2)) := by
        conv_rhs => rw [Finset.mul_sum]
    _ = (gueScale N) ^ 2 * ‖gueBeta‖ ^ 2 *
          ((∑ i, (frob (A i)) ^ 2) * (∑ k : d × Fin N, ‖W k‖ ^ 2) *
            (∑ k : d × Fin N, ‖Z k‖ ^ 2)) := by
        rw [hsum_eq]
    _ = (gueScale N) ^ 2 * ‖gueBeta‖ ^ 2 * (∑ i, (frob (A i)) ^ 2)
          * (∑ k : d × Fin N, ‖W k‖ ^ 2) * (∑ k : d × Fin N, ‖Z k‖ ^ 2) := by
        ring

/-- **Sparse direction-pairing bound.** -/
theorem sum_sq_direction_pairing_le (A : ι → Matrix d d ℂ) (W Z : d × Fin N → ℂ) :
    ∑ p : GUECoord ι N,
        ‖∑ k : d × Fin N, ∑ l : d × Fin N,
          W k * guePencilDirection A p k l * Z l‖ ^ 2
      ≤ 2 * (gueScale N) ^ 2 * (∑ i, (frob (A i)) ^ 2)
          * (∑ k : d × Fin N, ‖W k‖ ^ 2) * (∑ k : d × Fin N, ‖Z k‖ ^ 2) := by
  set S : GUECoord ι N → ℂ := fun p => ∑ x : d, ∑ x2 : d,
      (gueScale N : ℂ) * gueAlpha * (W (x, p.2.1) * A p.1 x x2 * Z (x2, p.2.2)) with hS
  set T : GUECoord ι N → ℂ := fun p => ∑ x : d, ∑ x2 : d,
      (gueScale N : ℂ) * gueBeta * (W (x, p.2.2) * A p.1 x x2 * Z (x2, p.2.1)) with hT
  have hg : ∀ p : GUECoord ι N,
      (∑ k : d × Fin N, ∑ l : d × Fin N, W k * guePencilDirection A p k l * Z l)
        = S p + T p := by
    intro p
    exact direction_pairing_eq A W Z p
  have hST : ∑ p : GUECoord ι N, ‖S p + T p‖ ^ 2
      ≤ 2 * ((gueScale N) ^ 2 * ‖gueAlpha‖ ^ 2 * (∑ i, (frob (A i)) ^ 2)
          * (∑ k : d × Fin N, ‖W k‖ ^ 2) * (∑ k : d × Fin N, ‖Z k‖ ^ 2))
        + 2 * ((gueScale N) ^ 2 * ‖gueBeta‖ ^ 2 * (∑ i, (frob (A i)) ^ 2)
          * (∑ k : d × Fin N, ‖W k‖ ^ 2) * (∑ k : d × Fin N, ‖Z k‖ ^ 2)) := by
    calc ∑ p : GUECoord ι N, ‖S p + T p‖ ^ 2
        ≤ ∑ p : GUECoord ι N, 2 * (‖S p‖ ^ 2 + ‖T p‖ ^ 2) :=
          Finset.sum_le_sum fun p _ =>
            (pow_le_pow_left₀ (norm_nonneg _) (norm_add_le (S p) (T p)) 2).trans add_sq_le
      _ = 2 * (∑ p : GUECoord ι N, ‖S p‖ ^ 2)
            + 2 * (∑ p : GUECoord ι N, ‖T p‖ ^ 2) := by
          rw [show (∑ p : GUECoord ι N, 2 * (‖S p‖ ^ 2 + ‖T p‖ ^ 2))
              = ∑ p : GUECoord ι N, (2 * ‖S p‖ ^ 2 + 2 * ‖T p‖ ^ 2) from by
            apply Finset.sum_congr rfl
            intro p _
            ring]
          simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
      _ ≤ 2 * ((gueScale N) ^ 2 * ‖gueAlpha‖ ^ 2 * (∑ i, (frob (A i)) ^ 2)
              * (∑ k : d × Fin N, ‖W k‖ ^ 2) * (∑ k : d × Fin N, ‖Z k‖ ^ 2))
            + 2 * ((gueScale N) ^ 2 * ‖gueBeta‖ ^ 2 * (∑ i, (frob (A i)) ^ 2)
              * (∑ k : d × Fin N, ‖W k‖ ^ 2) * (∑ k : d × Fin N, ‖Z k‖ ^ 2)) := by
          apply add_le_add
          · apply mul_le_mul_of_nonneg_left (sum_sq_alpha_slice_le A W Z) (by norm_num)
          · apply mul_le_mul_of_nonneg_left (sum_sq_beta_slice_le A W Z) (by norm_num)
  calc ∑ p : GUECoord ι N,
        ‖∑ k : d × Fin N, ∑ l : d × Fin N,
          W k * guePencilDirection A p k l * Z l‖ ^ 2
      = ∑ p : GUECoord ι N, ‖S p + T p‖ ^ 2 := by
        apply Finset.sum_congr rfl
        intro p _
        rw [hg p]
    _ ≤ _ := hST
    _ = 2 * (gueScale N) ^ 2 * (∑ i, (frob (A i)) ^ 2)
          * (∑ k : d × Fin N, ‖W k‖ ^ 2) * (∑ k : d × Fin N, ‖Z k‖ ^ 2) := by
        have hcoef : ‖gueAlpha‖ ^ 2 + ‖gueBeta‖ ^ 2 = 1 :=
          norm_gueAlpha_sq_add_norm_gueBeta_sq
        have hstep : 2 * ((gueScale N) ^ 2 * ‖gueAlpha‖ ^ 2 * (∑ i, (frob (A i)) ^ 2)
              * (∑ k : d × Fin N, ‖W k‖ ^ 2) * (∑ k : d × Fin N, ‖Z k‖ ^ 2))
            + 2 * ((gueScale N) ^ 2 * ‖gueBeta‖ ^ 2 * (∑ i, (frob (A i)) ^ 2)
              * (∑ k : d × Fin N, ‖W k‖ ^ 2) * (∑ k : d × Fin N, ‖Z k‖ ^ 2))
            = 2 * (gueScale N) ^ 2 * (∑ i, (frob (A i)) ^ 2)
              * (∑ k : d × Fin N, ‖W k‖ ^ 2) * (∑ k : d × Fin N, ‖Z k‖ ^ 2)
              * (‖gueAlpha‖ ^ 2 + ‖gueBeta‖ ^ 2) := by ring
        rw [hstep, hcoef, mul_one]

end

end GUEStrongConvergence
