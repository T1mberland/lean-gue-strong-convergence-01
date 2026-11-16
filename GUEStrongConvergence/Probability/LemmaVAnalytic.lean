/-
# Analytic hypotheses for Lemma V: polynomial growth of the GUE statistic

This module discharges the two analytic hypotheses of the Gaussian Poincaré step in Lemma V:

* **polynomial growth** of the scalar spectral statistic `Z_N = Re Tr P(H_N)` and of each
  coordinate derivative `∂_p Z_N`, uniformly in the Gaussian coordinates;
* **`L²` integrability** of `Z_N` and of the derivatives with respect to the standard Gaussian
  measure on `EuclideanSpace ℝ (GUECoord ι N)`.

Everything is finite dimensional and deterministic: the estimates are obtained from the
entrywise `ℓ¹` size `entrySum` of the affine pencil, the Kronecker structure of the GUE
matrices, and the polynomial functional calculus.  No probabilistic assumption is used.

The main deterministic input is

`entrySum (guePencilMatrix A₀ A x) ≤ guePencilConst N A₀ A * (1 + ∑ p, |x p|)`,

which combines the Kronecker submultiplicativity `entrySum (A ⊗ B) = entrySum A * entrySum B`
with the linearity of the GUE coordinates.  The polynomial calculus then gives
`entrySum (P(H)) ≤ C(P) * (max 1 (entrySum H)) ^ P.natDegree`.

-/
import GUEStrongConvergence.Probability.LemmaVContraction
import GUEStrongConvergence.Probability.GaussianPoincare
import Mathlib.Analysis.Matrix.Normed

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped RealInnerProductSpace ENNReal NNReal Topology Polynomial BigOperators

namespace GUEStrongConvergence

noncomputable section

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

variable {ι d : Type*} [Fintype ι] [DecidableEq ι] [Fintype d] [DecidableEq d] {N : ℕ}

/-! ### The entrywise `ℓ¹` size of scalar multiples and sums -/

/-- `entrySum` of a complex scalar multiple. -/
lemma entrySum_smul_complex {n : Type*} [Fintype n] (c : ℂ) (M : Matrix n n ℂ) :
    entrySum (c • M) = ‖c‖ * entrySum M := by
  have h : ∀ i j, ‖(c • M) i j‖ = ‖c‖ * ‖M i j‖ := by
    intro i j
    rw [Matrix.smul_apply, norm_smul]
  calc entrySum (c • M) = ∑ i, ∑ j, ‖c‖ * ‖M i j‖ := by
        simp only [entrySum, h]
    _ = ‖c‖ * ∑ i, ∑ j, ‖M i j‖ := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]
    _ = ‖c‖ * entrySum M := rfl

/-- `entrySum` of a real scalar multiple of a complex matrix. -/
lemma entrySum_smul_real {n : Type*} [Fintype n] (c : ℝ) (M : Matrix n n ℂ) :
    entrySum (c • M) = |c| * entrySum M := by
  have h : ∀ i j, ‖(c • M) i j‖ = |c| * ‖M i j‖ := by
    intro i j
    rw [Matrix.smul_apply, norm_smul, Real.norm_eq_abs]
  calc entrySum (c • M) = ∑ i, ∑ j, |c| * ‖M i j‖ := by
        simp only [entrySum, h]
    _ = |c| * ∑ i, ∑ j, ‖M i j‖ := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]
    _ = |c| * entrySum M := rfl

/-- `entrySum` is subadditive. -/
lemma entrySum_add_le {n : Type*} [Fintype n] (M N : Matrix n n ℂ) :
    entrySum (M + N) ≤ entrySum M + entrySum N := by
  have h : ∀ i j, ‖(M + N) i j‖ ≤ ‖M i j‖ + ‖N i j‖ := by
    intro i j
    rw [Matrix.add_apply]
    exact norm_add_le _ _
  calc entrySum (M + N) = ∑ i, ∑ j, ‖(M + N) i j‖ := rfl
    _ ≤ ∑ i, ∑ j, (‖M i j‖ + ‖N i j‖) := by
        refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => h i j
    _ = entrySum M + entrySum N := by
        simp only [entrySum, Finset.sum_add_distrib]

/-- `entrySum` is subadditive over finite sums. -/
lemma entrySum_finset_sum_le {n α : Type*} [Fintype n] (s : Finset α) (M : α → Matrix n n ℂ) :
    entrySum (∑ i ∈ s, M i) ≤ ∑ i ∈ s, entrySum (M i) := by
  classical
  induction s using Finset.induction with
  | empty => simp [entrySum]
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      exact (entrySum_add_le _ _).trans (add_le_add le_rfl ih)

/-- A constant can be pulled out of a double sum. -/
lemma sum_const_mul_double {α β : Type*} [Fintype α] [Fintype β] (c : ℝ)
    (f : α → β → ℝ) :
    (∑ a, ∑ b, c * f a b) = c * ∑ a, ∑ b, f a b := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]

/-- Triple sums commute. -/
lemma sum_triple_comm {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    (f : γ → α → β → ℝ) :
    (∑ a, ∑ b, ∑ c, f c a b) = ∑ c, ∑ a, ∑ b, f c a b := by
  calc (∑ a, ∑ b, ∑ c, f c a b) = ∑ a, ∑ c, ∑ b, f c a b := by
        refine Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ c, ∑ a, ∑ b, f c a b := Finset.sum_comm

/-! ### The Kronecker product and `entrySum` -/

/-- `entrySum` is multiplicative for Kronecker products. -/
lemma entrySum_kronecker {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m m ℂ) (B : Matrix n n ℂ) :
    entrySum (Matrix.kroneckerMap (· * ·) A B) = entrySum A * entrySum B := by
  have h : ∀ (x : m × n) (y : m × n),
      ‖Matrix.kroneckerMap (· * ·) A B x y‖ = ‖A x.1 y.1‖ * ‖B x.2 y.2‖ := by
    intro x y
    rw [Matrix.kroneckerMap_apply, norm_mul]
  calc entrySum (Matrix.kroneckerMap (· * ·) A B)
      = ∑ x : m × n, ∑ y : m × n, ‖A x.1 y.1‖ * ‖B x.2 y.2‖ := by
        simp only [entrySum, h]
    _ = ∑ a, ∑ c, ∑ b, ∑ e, ‖A a b‖ * ‖B c e‖ := by
        simp_rw [Fintype.sum_prod_type]
    _ = ∑ a, ∑ b, ∑ c, ∑ e, ‖A a b‖ * ‖B c e‖ := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.sum_comm]
    _ = ∑ a, ∑ b, ‖A a b‖ * (∑ c, ∑ e, ‖B c e‖) := by
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [Finset.mul_sum]
    _ = (∑ a, ∑ b, ‖A a b‖) * (∑ c, ∑ e, ‖B c e‖) := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.sum_mul]
    _ = entrySum A * entrySum B := rfl

/-! ### The GUE matrix and the affine pencil -/

/-- Pointwise bound on the GUE coefficient: at most one of the two coordinate `ite`s fires,
and each has norm at most one. -/
lemma norm_gueMatrixCoeff_le (p : GUECoord ι N) (i : ι) (a b : Fin N) :
    ‖gueMatrixCoeff p i a b‖ ≤ gueScale N * (‖gueAlpha‖ + ‖gueBeta‖) := by
  have h1 : ‖(if (i, (a, b)) = p then (1 : ℂ) else 0)‖ ≤ 1 := by
    by_cases h : (i, (a, b)) = p <;> simp [h]
  have h2 : ‖(if (i, (b, a)) = p then (1 : ℂ) else 0)‖ ≤ 1 := by
    by_cases h : (i, (b, a)) = p <;> simp [h]
  have hsum : ‖gueAlpha * (if (i, (a, b)) = p then (1 : ℂ) else 0) +
      gueBeta * (if (i, (b, a)) = p then (1 : ℂ) else 0)‖ ≤ ‖gueAlpha‖ + ‖gueBeta‖ := by
    calc ‖gueAlpha * (if (i, (a, b)) = p then (1 : ℂ) else 0) +
          gueBeta * (if (i, (b, a)) = p then (1 : ℂ) else 0)‖
        ≤ ‖gueAlpha * (if (i, (a, b)) = p then (1 : ℂ) else 0)‖ +
            ‖gueBeta * (if (i, (b, a)) = p then (1 : ℂ) else 0)‖ := norm_add_le _ _
      _ = ‖gueAlpha‖ * ‖(if (i, (a, b)) = p then (1 : ℂ) else 0)‖ +
            ‖gueBeta‖ * ‖(if (i, (b, a)) = p then (1 : ℂ) else 0)‖ := by
          rw [norm_mul, norm_mul]
      _ ≤ ‖gueAlpha‖ * 1 + ‖gueBeta‖ * 1 := by
          exact add_le_add
            (mul_le_mul_of_nonneg_left h1 (norm_nonneg _))
            (mul_le_mul_of_nonneg_left h2 (norm_nonneg _))
      _ = ‖gueAlpha‖ + ‖gueBeta‖ := by ring
  have hscale : (0:ℝ) ≤ gueScale N := gueScale_nonneg N
  calc ‖gueMatrixCoeff p i a b‖
      = gueScale N * ‖gueAlpha * (if (i, (a, b)) = p then (1 : ℂ) else 0) +
          gueBeta * (if (i, (b, a)) = p then (1 : ℂ) else 0)‖ := by
        rw [gueMatrixCoeff, norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (gueScale_nonneg N)]
    _ ≤ gueScale N * (‖gueAlpha‖ + ‖gueBeta‖) :=
        mul_le_mul_of_nonneg_left hsum hscale

/-- Entrywise size of the unnormalized GUE matrix, linear in the coordinates. -/
lemma entrySum_gueUnscaled_le (y : GUECoord ι N → ℝ) (i : ι) :
    entrySum (gueUnscaled y i) ≤
      (‖gueAlpha‖ + ‖gueBeta‖) * ∑ p : GUECoord ι N, |y p| := by
  have hrow : (∑ a : Fin N, ∑ b : Fin N, |y (i, (a, b))|) ≤
      ∑ p : GUECoord ι N, |y p| := by
    calc (∑ a : Fin N, ∑ b : Fin N, |y (i, (a, b))|)
        = ∑ q : Fin N × Fin N, |y (i, q)| :=
            (Fintype.sum_prod_type (f := fun q : Fin N × Fin N => |y (i, q)|)).symm
      _ ≤ ∑ i' : ι, ∑ q : Fin N × Fin N, |y (i', q)| := by
          refine Finset.single_le_sum (f := fun i' => ∑ q : Fin N × Fin N, |y (i', q)|)
            (fun i' _ => Finset.sum_nonneg fun q _ => abs_nonneg _) (Finset.mem_univ i)
      _ = ∑ p : GUECoord ι N, |y p| :=
          (Fintype.sum_prod_type (f := fun p : GUECoord ι N => |y p|)).symm
  have hswap : (∑ a : Fin N, ∑ b : Fin N, |y (i, (b, a))|) =
      ∑ a : Fin N, ∑ b : Fin N, |y (i, (a, b))| := by
    rw [Finset.sum_comm]
  have hzero : (0:ℝ) ≤ ∑ p : GUECoord ι N, |y p| :=
    Finset.sum_nonneg fun p _ => abs_nonneg _
  have hterm : ∀ a b : Fin N,
      ‖gueAlpha * ((y (i, (a, b)) : ℝ) : ℂ) + gueBeta * ((y (i, (b, a)) : ℝ) : ℂ)‖ ≤
        ‖gueAlpha‖ * |y (i, (a, b))| + ‖gueBeta‖ * |y (i, (b, a))| := by
    intro a b
    calc ‖gueAlpha * ((y (i, (a, b)) : ℝ) : ℂ) + gueBeta * ((y (i, (b, a)) : ℝ) : ℂ)‖
        ≤ ‖gueAlpha * ((y (i, (a, b)) : ℝ) : ℂ)‖ +
            ‖gueBeta * ((y (i, (b, a)) : ℝ) : ℂ)‖ := norm_add_le _ _
      _ = ‖gueAlpha‖ * |y (i, (a, b))| + ‖gueBeta‖ * |y (i, (b, a))| := by
          rw [norm_mul, norm_mul]
          simp [Complex.norm_real, Real.norm_eq_abs]
  calc entrySum (gueUnscaled y i)
      = ∑ a, ∑ b, ‖gueAlpha * ((y (i, (a, b)) : ℝ) : ℂ) +
          gueBeta * ((y (i, (b, a)) : ℝ) : ℂ)‖ := rfl
    _ ≤ ∑ a, ∑ b, (‖gueAlpha‖ * |y (i, (a, b))| + ‖gueBeta‖ * |y (i, (b, a))|) := by
        exact Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => hterm a b
    _ = (∑ a, ∑ b, ‖gueAlpha‖ * |y (i, (a, b))|) +
          (∑ a, ∑ b, ‖gueBeta‖ * |y (i, (b, a))|) := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun a _ => Finset.sum_add_distrib
    _ = ‖gueAlpha‖ * (∑ a, ∑ b, |y (i, (a, b))|) +
          ‖gueBeta‖ * (∑ a, ∑ b, |y (i, (b, a))|) := by
        rw [sum_const_mul_double, sum_const_mul_double]
    _ = (‖gueAlpha‖ + ‖gueBeta‖) * (∑ a, ∑ b, |y (i, (a, b))|) := by
        rw [hswap]; ring
    _ ≤ (‖gueAlpha‖ + ‖gueBeta‖) * (∑ p : GUECoord ι N, |y p|) := by
        exact mul_le_mul_of_nonneg_left hrow (by positivity)

/-- Entrywise size of the normalized GUE matrix. -/
lemma entrySum_gueMatrix_le (y : GUECoord ι N → ℝ) (i : ι) :
    entrySum (gueMatrix y i) ≤
      gueScale N * (‖gueAlpha‖ + ‖gueBeta‖) * (1 + ∑ p : GUECoord ι N, |y p|) := by
  have hS : (0:ℝ) ≤ ∑ p : GUECoord ι N, |y p| :=
    Finset.sum_nonneg fun p _ => abs_nonneg _
  have hc : (0:ℝ) ≤ gueScale N * (‖gueAlpha‖ + ‖gueBeta‖) :=
    mul_nonneg (gueScale_nonneg N) (by positivity)
  calc entrySum (gueMatrix y i)
      = entrySum ((gueScale N : ℂ) • gueUnscaled y i) := rfl
    _ = ‖(gueScale N : ℂ)‖ * entrySum (gueUnscaled y i) := entrySum_smul_complex _ _
    _ = gueScale N * entrySum (gueUnscaled y i) := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (gueScale_nonneg N)]
    _ ≤ gueScale N * ((‖gueAlpha‖ + ‖gueBeta‖) * ∑ p, |y p|) :=
        mul_le_mul_of_nonneg_left (entrySum_gueUnscaled_le y i) (gueScale_nonneg N)
    _ = gueScale N * (‖gueAlpha‖ + ‖gueBeta‖) * (∑ p, |y p|) := by ring
    _ ≤ gueScale N * (‖gueAlpha‖ + ‖gueBeta‖) * (1 + ∑ p, |y p|) := by
        exact mul_le_mul_of_nonneg_left (by linarith) hc

/-- The constant multiplying `(1 + ∑ |y p|)` in the pencil bound. -/
def guePencilConst (N : ℕ) (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ) : ℝ :=
  entrySum A₀ * (Fintype.card (Fin N) : ℝ) +
    ∑ i, entrySum (A i) * (gueScale N * (‖gueAlpha‖ + ‖gueBeta‖))

lemma guePencilConst_nonneg (N : ℕ) (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ) :
    0 ≤ guePencilConst N A₀ A := by
  refine add_nonneg (mul_nonneg (entrySum_nonneg _) (Nat.cast_nonneg _)) ?_
  exact Finset.sum_nonneg fun i _ =>
    mul_nonneg (entrySum_nonneg _) (mul_nonneg (gueScale_nonneg N) (by positivity))

/-- **Linear growth of the affine GUE pencil in the entrywise `ℓ¹` size.** -/
lemma entrySum_guePencilMatrix_le (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    (y : GUECoord ι N → ℝ) :
    entrySum (guePencilMatrix A₀ A y) ≤ guePencilConst N A₀ A * (1 + ∑ p, |y p|) := by
  have hS : (0:ℝ) ≤ ∑ p : GUECoord ι N, |y p| :=
    Finset.sum_nonneg fun p _ => abs_nonneg _
  have h1 : entrySum (Matrix.kroneckerMap (· * ·) A₀ (1 : Matrix (Fin N) (Fin N) ℂ)) =
      entrySum A₀ * (Fintype.card (Fin N) : ℝ) := by
    rw [entrySum_kronecker, entrySum_one]
  have h2 : ∀ i : ι, entrySum (Matrix.kroneckerMap (· * ·) (A i) (gueMatrix y i)) ≤
      entrySum (A i) * (gueScale N * (‖gueAlpha‖ + ‖gueBeta‖)) * (1 + ∑ p, |y p|) := by
    intro i
    refine (entrySum_kronecker (A i) (gueMatrix y i)).trans_le ?_
    calc entrySum (A i) * entrySum (gueMatrix y i)
        ≤ entrySum (A i) * (gueScale N * (‖gueAlpha‖ + ‖gueBeta‖) * (1 + ∑ p, |y p|)) :=
          mul_le_mul_of_nonneg_left (entrySum_gueMatrix_le y i) (entrySum_nonneg _)
      _ = entrySum (A i) * (gueScale N * (‖gueAlpha‖ + ‖gueBeta‖)) *
            (1 + ∑ p, |y p|) := by ring
  have hsplit : entrySum (guePencilMatrix A₀ A y) ≤
      entrySum (Matrix.kroneckerMap (· * ·) A₀ (1 : Matrix (Fin N) (Fin N) ℂ)) +
        ∑ i, entrySum (Matrix.kroneckerMap (· * ·) (A i) (gueMatrix y i)) := by
    rw [guePencilMatrix]
    exact (entrySum_add_le _ _).trans (add_le_add le_rfl (entrySum_finset_sum_le _ _))
  refine hsplit.trans ?_
  rw [h1]
  have hsum : (∑ i, entrySum (Matrix.kroneckerMap (· * ·) (A i) (gueMatrix y i))) ≤
      (∑ i, entrySum (A i) * (gueScale N * (‖gueAlpha‖ + ‖gueBeta‖))) * (1 + ∑ p, |y p|) := by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum fun i _ => h2 i
  refine (add_le_add le_rfl hsum).trans ?_
  have hc0 : (0:ℝ) ≤ entrySum A₀ * (Fintype.card (Fin N) : ℝ) :=
    mul_nonneg (entrySum_nonneg _) (Nat.cast_nonneg _)
  have hE0 : (0:ℝ) ≤ ∑ i, entrySum (A i) *
      (gueScale N * (‖gueAlpha‖ + ‖gueBeta‖)) :=
    Finset.sum_nonneg fun i _ =>
      mul_nonneg (entrySum_nonneg _) (mul_nonneg (gueScale_nonneg N) (by positivity))
  have hb : (1:ℝ) ≤ 1 + ∑ p, |y p| := by linarith
  calc entrySum A₀ * (Fintype.card (Fin N) : ℝ) +
        (∑ i, entrySum (A i) * (gueScale N * (‖gueAlpha‖ + ‖gueBeta‖))) *
          (1 + ∑ p, |y p|)
      ≤ (entrySum A₀ * (Fintype.card (Fin N) : ℝ)) * (1 + ∑ p, |y p|) +
          (∑ i, entrySum (A i) * (gueScale N * (‖gueAlpha‖ + ‖gueBeta‖))) *
            (1 + ∑ p, |y p|) := by
        exact add_le_add (le_mul_of_one_le_right hc0 hb) le_rfl
    _ = guePencilConst N A₀ A * (1 + ∑ p, |y p|) := by
        rw [guePencilConst]; ring

/-! ### Polynomial functional calculus: entrywise growth -/

/-- Entrywise size of `polyMatrix P H`, bounded by the support coefficients times the powers. -/
lemma entrySum_polyMatrix_le (P : ℝ[X]) (H : Matrix (d × Fin N) (d × Fin N) ℂ) :
    entrySum (polyMatrix P H) ≤
      ∑ k ∈ P.support,
        ‖P.coeff k‖ * ((Fintype.card (d × Fin N) : ℝ) * (max 1 (entrySum H)) ^ k) := by
  rw [polyMatrix_eq_sum]
  calc entrySum (∑ k ∈ P.support, P.coeff k • H ^ k)
      ≤ ∑ k ∈ P.support, entrySum (P.coeff k • H ^ k) := entrySum_finset_sum_le _ _
    _ = ∑ k ∈ P.support, ‖P.coeff k‖ * entrySum (H ^ k) := by
        exact Finset.sum_congr rfl fun k _ => entrySum_smul_real _ _
    _ ≤ ∑ k ∈ P.support,
          ‖P.coeff k‖ * ((Fintype.card (d × Fin N) : ℝ) * (max 1 (entrySum H)) ^ k) := by
        exact Finset.sum_le_sum fun k _ =>
          mul_le_mul_of_nonneg_left (entrySum_pow_le H k) (norm_nonneg _)

/-- Entrywise size of `polyMatrix P H`, with the degree isolated. -/
lemma entrySum_polyMatrix_le_natDegree (P : ℝ[X]) (H : Matrix (d × Fin N) (d × Fin N) ℂ) :
    entrySum (polyMatrix P H) ≤
      (∑ k ∈ P.support, ‖P.coeff k‖ * (Fintype.card (d × Fin N) : ℝ)) *
        (max 1 (entrySum H)) ^ P.natDegree := by
  refine (entrySum_polyMatrix_le P H).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun k hk => ?_
  have hkdeg : k ≤ P.natDegree := Polynomial.le_natDegree_of_mem_supp k hk
  have hbase : (1:ℝ) ≤ max 1 (entrySum H) := le_max_left _ _
  have hpow : (max 1 (entrySum H)) ^ k ≤ (max 1 (entrySum H)) ^ P.natDegree :=
    pow_le_pow_right₀ hbase hkdeg
  have hc : (0:ℝ) ≤ ‖P.coeff k‖ * (Fintype.card (d × Fin N) : ℝ) :=
    mul_nonneg (norm_nonneg _) (Nat.cast_nonneg _)
  calc ‖P.coeff k‖ * ((Fintype.card (d × Fin N) : ℝ) * (max 1 (entrySum H)) ^ k)
      = (‖P.coeff k‖ * (Fintype.card (d × Fin N) : ℝ)) * (max 1 (entrySum H)) ^ k := by ring
    _ ≤ (‖P.coeff k‖ * (Fintype.card (d × Fin N) : ℝ)) *
          (max 1 (entrySum H)) ^ P.natDegree :=
        mul_le_mul_of_nonneg_left hpow hc

/-! ### Polynomial growth in the Gaussian coordinates -/

/-- **Polynomial growth of the scalar spectral statistic.** -/
theorem gueStatistic_polyBound (P : ℝ[X]) (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ k : ℕ, ∀ x : EuclideanSpace ℝ (GUECoord ι N),
      |gueStatistic P A₀ A x| ≤
        C * (1 + ∑ p : GUECoord ι N, |(WithLp.ofLp x) p|) ^ k := by
  set D := guePencilConst N A₀ A with hD
  have hD0 : 0 ≤ D := guePencilConst_nonneg N A₀ A
  refine ⟨(∑ k ∈ P.support, ‖P.coeff k‖ * (Fintype.card (d × Fin N) : ℝ)) *
      (max 1 D) ^ P.natDegree,
    mul_nonneg (Finset.sum_nonneg fun k _ =>
      mul_nonneg (norm_nonneg _) (Nat.cast_nonneg _))
      (pow_nonneg (le_trans zero_le_one (le_max_left _ _)) _), P.natDegree, fun x => ?_⟩
  set y : GUECoord ι N → ℝ := WithLp.ofLp x with hy
  set S : ℝ := ∑ p : GUECoord ι N, |y p| with hS
  have hH : entrySum (guePencilMatrix A₀ A y) ≤ D * (1 + S) := by
    simpa [hD, hS, hy] using entrySum_guePencilMatrix_le A₀ A y
  have hmax : max 1 (entrySum (guePencilMatrix A₀ A y)) ≤ max 1 D * (1 + S) := by
    have hb : (1:ℝ) ≤ 1 + S := by
      have : (0:ℝ) ≤ S := Finset.sum_nonneg fun p _ => abs_nonneg _
      linarith
    have hDle : (max 1 D) ≥ 1 := le_max_left _ _
    rcases le_or_gt (entrySum (guePencilMatrix A₀ A y)) 1 with hle | hgt
    · rw [max_eq_left hle]
      calc (1:ℝ) = 1 * 1 := by ring
        _ ≤ max 1 D * (1 + S) := by
            exact mul_le_mul hDle hb (by norm_num) (le_trans zero_le_one hDle)
    · rw [max_eq_right (le_of_lt hgt)]
      exact hH.trans (mul_le_mul_of_nonneg_right (le_max_right _ _)
        (by linarith : (0:ℝ) ≤ 1 + S))
  have hconst : (0:ℝ) ≤ ∑ k ∈ P.support,
      ‖P.coeff k‖ * (Fintype.card (d × Fin N) : ℝ) :=
    Finset.sum_nonneg fun k _ => mul_nonneg (norm_nonneg _) (Nat.cast_nonneg _)
  have hbase0 : (0:ℝ) ≤ max 1 (entrySum (guePencilMatrix A₀ A y)) :=
    le_trans zero_le_one (le_max_left _ _)
  calc |gueStatistic P A₀ A x|
      = |(Matrix.trace (polyMatrix P (guePencilMatrix A₀ A y))).re| := rfl
    _ ≤ ‖Matrix.trace (polyMatrix P (guePencilMatrix A₀ A y))‖ :=
        Complex.abs_re_le_norm _
    _ ≤ entrySum (polyMatrix P (guePencilMatrix A₀ A y)) := norm_trace_le_entrySum _
    _ ≤ (∑ k ∈ P.support, ‖P.coeff k‖ * (Fintype.card (d × Fin N) : ℝ)) *
          (max 1 (entrySum (guePencilMatrix A₀ A y))) ^ P.natDegree :=
        entrySum_polyMatrix_le_natDegree P _
    _ ≤ (∑ k ∈ P.support, ‖P.coeff k‖ * (Fintype.card (d × Fin N) : ℝ)) *
          (max 1 D * (1 + S)) ^ P.natDegree := by
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ hbase0 hmax P.natDegree) hconst
    _ = (∑ k ∈ P.support, ‖P.coeff k‖ * (Fintype.card (d × Fin N) : ℝ)) *
          (max 1 D) ^ P.natDegree * (1 + S) ^ P.natDegree := by
        rw [mul_pow]; ring


/-! ### The coordinate derivative: growth against the GUE direction -/

/-- Entrywise size of a GUE coordinate direction (uniform in the coordinate). -/
lemma entrySum_gueDirMatrix_le (A : ι → Matrix d d ℂ) (p : GUECoord ι N) :
    entrySum (gueDirMatrix A p) ≤
      gueScale N * (‖gueAlpha‖ + ‖gueBeta‖) *
        ((Fintype.card (d × Fin N) : ℝ) * (Fintype.card (d × Fin N) : ℝ)) *
          ∑ i, entrySum (A i) := by
  set c : ℝ := gueScale N * (‖gueAlpha‖ + ‖gueBeta‖) with hc
  have hc0 : (0:ℝ) ≤ c := mul_nonneg (gueScale_nonneg N) (by positivity)
  have hentry : ∀ (i : ι) (x y : d × Fin N), ‖A i x.1 y.1‖ ≤ entrySum (A i) := by
    intro i x y
    calc ‖A i x.1 y.1‖ ≤ ∑ b : d, ‖A i x.1 b‖ :=
          Finset.single_le_sum (fun b _ => norm_nonneg _) (Finset.mem_univ y.1)
      _ ≤ ∑ a : d, ∑ b : d, ‖A i a b‖ :=
          Finset.single_le_sum
            (fun a _ => Finset.sum_nonneg fun b _ => norm_nonneg _) (Finset.mem_univ x.1)
  have hterm : ∀ (x y : d × Fin N),
      ‖gueDirMatrix A p x y‖ ≤ ∑ i, entrySum (A i) * c := by
    intro x y
    calc ‖gueDirMatrix A p x y‖
        = ‖∑ i, A i x.1 y.1 * gueMatrixCoeff p i x.2 y.2‖ := by rw [gueDirMatrix]
      _ ≤ ∑ i, ‖A i x.1 y.1 * gueMatrixCoeff p i x.2 y.2‖ := norm_sum_le _ _
      _ ≤ ∑ i, entrySum (A i) * c := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [norm_mul]
          calc ‖A i x.1 y.1‖ * ‖gueMatrixCoeff p i x.2 y.2‖
              ≤ entrySum (A i) * ‖gueMatrixCoeff p i x.2 y.2‖ :=
                mul_le_mul_of_nonneg_right (hentry i x y) (norm_nonneg _)
            _ ≤ entrySum (A i) * c :=
                mul_le_mul_of_nonneg_left (norm_gueMatrixCoeff_le p i x.2 y.2) (entrySum_nonneg _)
  calc entrySum (gueDirMatrix A p)
      = ∑ x, ∑ y, ‖gueDirMatrix A p x y‖ := rfl
    _ ≤ ∑ x, ∑ y, ∑ i, entrySum (A i) * c := by
        exact Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => hterm x y
    _ = (Fintype.card (d × Fin N) : ℝ) * (Fintype.card (d × Fin N) : ℝ) *
          (∑ i, entrySum (A i) * c) := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        ring
    _ = c * ((Fintype.card (d × Fin N) : ℝ) * (Fintype.card (d × Fin N) : ℝ)) *
          ∑ i, entrySum (A i) := by
        rw [← Finset.sum_mul]
        ring

/-- **Polynomial growth of the coordinate derivative of the scalar spectral statistic.** -/
theorem gueStatisticDir_polyBound (P : ℝ[X]) (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    (p : GUECoord ι N) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ k : ℕ, ∀ x : EuclideanSpace ℝ (GUECoord ι N),
      |gueStatisticDir P A₀ A p x| ≤
        C * (1 + ∑ q : GUECoord ι N, |(WithLp.ofLp x) q|) ^ k := by
  set D := guePencilConst N A₀ A with hD
  have hD0 : 0 ≤ D := guePencilConst_nonneg N A₀ A
  set cardNN : ℝ := (Fintype.card (d × Fin N) : ℝ) with hcard
  have hcard0 : 0 ≤ cardNN := Nat.cast_nonneg _
  set cDir : ℝ := gueScale N * (‖gueAlpha‖ + ‖gueBeta‖) * (cardNN * cardNN) *
      ∑ i, entrySum (A i) with hcDir
  have hcDir0 : 0 ≤ cDir := by
    rw [hcDir]
    exact mul_nonneg (mul_nonneg (mul_nonneg (gueScale_nonneg N) (by positivity))
      (mul_nonneg hcard0 hcard0))
      (Finset.sum_nonneg fun i _ => entrySum_nonneg _)
  set pc : ℝ := ∑ k ∈ P.derivative.support, ‖P.derivative.coeff k‖ * cardNN with hpc
  have hpc0 : 0 ≤ pc := Finset.sum_nonneg fun k _ =>
    mul_nonneg (norm_nonneg _) hcard0
  refine ⟨pc * (max 1 D) ^ P.derivative.natDegree * cDir,
    mul_nonneg (mul_nonneg hpc0 (pow_nonneg (le_trans zero_le_one (le_max_left _ _)) _)) hcDir0,
    P.derivative.natDegree, fun x => ?_⟩
  set y : GUECoord ι N → ℝ := WithLp.ofLp x with hy
  set S : ℝ := ∑ q : GUECoord ι N, |y q| with hS
  have hS0 : (0:ℝ) ≤ S := Finset.sum_nonneg fun q _ => abs_nonneg _
  have hH : entrySum (guePencilMatrix A₀ A y) ≤ D * (1 + S) := by
    simpa [hD, hS, hy] using entrySum_guePencilMatrix_le A₀ A y
  have hmax : max 1 (entrySum (guePencilMatrix A₀ A y)) ≤ max 1 D * (1 + S) := by
    have hb : (1:ℝ) ≤ 1 + S := by linarith
    have hDle : (max 1 D) ≥ 1 := le_max_left _ _
    rcases le_or_gt (entrySum (guePencilMatrix A₀ A y)) 1 with hle | hgt
    · rw [max_eq_left hle]
      calc (1:ℝ) = 1 * 1 := by ring
        _ ≤ max 1 D * (1 + S) :=
            mul_le_mul hDle hb (by norm_num) (le_trans zero_le_one hDle)
    · rw [max_eq_right (le_of_lt hgt)]
      exact hH.trans (mul_le_mul_of_nonneg_right (le_max_right _ _)
        (by linarith : (0:ℝ) ≤ 1 + S))
  have hFbound : entrySum (polyMatrix P.derivative (guePencilMatrix A₀ A y)) ≤
      pc * (max 1 D) ^ P.derivative.natDegree * (1 + S) ^ P.derivative.natDegree := by
    have hbase0 : (0:ℝ) ≤ max 1 (entrySum (guePencilMatrix A₀ A y)) :=
      le_trans zero_le_one (le_max_left _ _)
    calc entrySum (polyMatrix P.derivative (guePencilMatrix A₀ A y))
        ≤ (∑ k ∈ P.derivative.support, ‖P.derivative.coeff k‖ *
            (Fintype.card (d × Fin N) : ℝ)) *
              (max 1 (entrySum (guePencilMatrix A₀ A y))) ^ P.derivative.natDegree :=
          entrySum_polyMatrix_le_natDegree P.derivative _
      _ ≤ pc * (max 1 D * (1 + S)) ^ P.derivative.natDegree := by
          rw [hpc]
          exact mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ hbase0 hmax P.derivative.natDegree)
            (Finset.sum_nonneg fun k _ =>
              mul_nonneg (norm_nonneg (P.derivative.coeff k)) hcard0)
      _ = pc * (max 1 D) ^ P.derivative.natDegree * (1 + S) ^ P.derivative.natDegree := by
          rw [mul_pow]; ring
  have hDbound : entrySum (gueDirMatrix A p) ≤ cDir := by
    rw [hcDir, hcard]
    exact entrySum_gueDirMatrix_le A p
  calc |gueStatisticDir P A₀ A p x|
      = |(Matrix.trace (polyMatrix P.derivative (guePencilMatrix A₀ A y) *
          gueDirMatrix A p)).re| := rfl
    _ ≤ ‖Matrix.trace (polyMatrix P.derivative (guePencilMatrix A₀ A y) *
          gueDirMatrix A p)‖ := Complex.abs_re_le_norm _
    _ ≤ entrySum (polyMatrix P.derivative (guePencilMatrix A₀ A y) * gueDirMatrix A p) :=
        norm_trace_le_entrySum _
    _ ≤ entrySum (polyMatrix P.derivative (guePencilMatrix A₀ A y)) *
          entrySum (gueDirMatrix A p) := entrySum_mul_le _ _
    _ ≤ (pc * (max 1 D) ^ P.derivative.natDegree *
          (1 + S) ^ P.derivative.natDegree) * cDir := by
        exact mul_le_mul hFbound hDbound (entrySum_nonneg _) (by positivity)
    _ = pc * (max 1 D) ^ P.derivative.natDegree * cDir *
          (1 + S) ^ P.derivative.natDegree := by ring

/-! ### Polynomial growth along a coordinate fibre -/

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- Updating one coordinate changes `∑ |y q|` by at most the number of coordinates times
`|u|`. -/
lemma sum_abs_update_le (y : κ → ℝ) (p : κ) (u : ℝ) :
    (∑ q, |Function.update y p u q|) ≤ (∑ q, |y q|) + (Fintype.card κ : ℝ) * |u| := by
  have hpoint : ∀ q, |Function.update y p u q| ≤ |y q| + |u| := by
    intro q
    by_cases hq : q = p
    · subst hq
      simp
    · simp [hq]
  calc (∑ q, |Function.update y p u q|) ≤ ∑ q, (|y q| + |u|) :=
        Finset.sum_le_sum fun q _ => hpoint q
    _ = (∑ q, |y q|) + (Fintype.card κ : ℝ) * |u| := by
        rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, Finset.card_univ]

/-- A polynomial bound on the coordinates transfers to polynomial growth of every coordinate
fibre. -/
lemma polyGrowth_fibre_of_bound {F : EuclideanSpace ℝ κ → ℝ} {C : ℝ} (hC0 : 0 ≤ C) {k : ℕ}
    (h : ∀ x : EuclideanSpace ℝ κ,
      |F x| ≤ C * (1 + ∑ q, |(WithLp.ofLp x) q|) ^ k)
    (y : κ → ℝ) (p : κ) :
    PolyGrowth (fun u : ℝ => F (WithLp.toLp 2 (Function.update y p u))) := by
  set S : ℝ := ∑ q, |y q| with hS
  set K : ℝ := max 1 (Fintype.card κ : ℝ) with hK
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun q _ => abs_nonneg _
  have hK1 : 1 ≤ K := le_max_left _ _
  have hK0 : 0 ≤ K := le_trans zero_le_one hK1
  refine ⟨C * (1 + S) ^ k * K ^ k,
    mul_nonneg (mul_nonneg hC0 (pow_nonneg (by linarith) _)) (pow_nonneg hK0 _), k, fun u => ?_⟩
  have hupd : (∑ q, |(WithLp.ofLp (WithLp.toLp 2 (Function.update y p u))) q|) ≤
      S + (Fintype.card κ : ℝ) * |u| := by
    rw [hS]
    simpa using sum_abs_update_le y p u
  have hcard : (0:ℝ) ≤ (Fintype.card κ : ℝ) := Nat.cast_nonneg _
  have hu : (0:ℝ) ≤ |u| := abs_nonneg u
  have hbase : 1 + (∑ q, |(WithLp.ofLp (WithLp.toLp 2 (Function.update y p u))) q|) ≤
      (1 + S) * K * (1 + |u|) := by
    have h1S : (0:ℝ) ≤ 1 + S := by linarith
    have hstep1 : 1 + (∑ q, |(WithLp.ofLp (WithLp.toLp 2 (Function.update y p u))) q|) ≤
        1 + (S + (Fintype.card κ : ℝ) * |u|) := by linarith
    have hstep2 : (1 + S) + (Fintype.card κ : ℝ) * |u| ≤
        (1 + S) + (1 + S) * ((Fintype.card κ : ℝ) * |u|) := by
      have : (Fintype.card κ : ℝ) * |u| ≤ (1 + S) * ((Fintype.card κ : ℝ) * |u|) := by
        nlinarith [mul_nonneg hcard hu]
      linarith
    have hstep3 : 1 + (Fintype.card κ : ℝ) * |u| ≤ K * (1 + |u|) := by
      have hKcard : (Fintype.card κ : ℝ) ≤ K := le_max_right _ _
      nlinarith [hK1, hKcard, hu]
    calc 1 + (∑ q, |(WithLp.ofLp (WithLp.toLp 2 (Function.update y p u))) q|)
        ≤ 1 + (S + (Fintype.card κ : ℝ) * |u|) := hstep1
      _ = (1 + S) + (Fintype.card κ : ℝ) * |u| := by ring
      _ ≤ (1 + S) + (1 + S) * ((Fintype.card κ : ℝ) * |u|) := hstep2
      _ = (1 + S) * (1 + (Fintype.card κ : ℝ) * |u|) := by ring
      _ ≤ (1 + S) * (K * (1 + |u|)) := by
          exact mul_le_mul_of_nonneg_left hstep3 h1S
      _ = (1 + S) * K * (1 + |u|) := by ring
  calc |F (WithLp.toLp 2 (Function.update y p u))|
      ≤ C * (1 + (∑ q, |(WithLp.ofLp (WithLp.toLp 2 (Function.update y p u))) q|)) ^ k :=
        h _
    _ ≤ C * ((1 + S) * K * (1 + |u|)) ^ k := by
        have hb : (0:ℝ) ≤ 1 + (∑ q, |(WithLp.ofLp (WithLp.toLp 2 (Function.update y p u))) q|) :=
          by positivity
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hb hbase k) hC0
    _ = C * (1 + S) ^ k * K ^ k * (1 + |u|) ^ k := by
        rw [mul_pow, mul_pow]; ring

/-! ### The fibre growth hypotheses used by Gaussian Poincaré -/

/-- Polynomial growth of the scalar statistic along every coordinate fibre. -/
theorem polyGrowth_gueStatistic_fibre (P : ℝ[X]) (A₀ : Matrix d d ℂ)
    (A : ι → Matrix d d ℂ) (x : EuclideanSpace ℝ (GUECoord ι N)) (p : GUECoord ι N) :
    PolyGrowth (fun u : ℝ => gueStatistic P A₀ A (euclidUpdate x p u)) := by
  obtain ⟨C, hC0, k, h⟩ := gueStatistic_polyBound P A₀ A
  have := polyGrowth_fibre_of_bound (κ := GUECoord ι N) hC0 h (WithLp.ofLp x) p
  simpa [euclidUpdate] using this

/-- Polynomial growth of every coordinate derivative along the corresponding fibre. -/
theorem polyGrowth_gueStatisticDir_fibre (P : ℝ[X]) (A₀ : Matrix d d ℂ)
    (A : ι → Matrix d d ℂ) (x : EuclideanSpace ℝ (GUECoord ι N)) (p : GUECoord ι N) :
    PolyGrowth (fun u : ℝ => gueStatisticDir P A₀ A p (euclidUpdate x p u)) := by
  obtain ⟨C, hC0, k, h⟩ := gueStatisticDir_polyBound P A₀ A p
  have := polyGrowth_fibre_of_bound (κ := GUECoord ι N) hC0 h (WithLp.ofLp x) p
  simpa [euclidUpdate] using this

/-- The a.e. polynomial-growth hypothesis of `gaussian_poincare_stdGaussian`. -/
theorem ae_polyGrowth_gueStatistic (P : ℝ[X]) (A₀ : Matrix d d ℂ)
    (A : ι → Matrix d d ℂ) (p : GUECoord ι N) :
    ∀ᵐ x ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N))),
      PolyGrowth (fun u : ℝ => gueStatistic P A₀ A (euclidUpdate x p u)) ∧
        PolyGrowth (fun u : ℝ => gueStatisticDir P A₀ A p (euclidUpdate x p u)) :=
  Eventually.of_forall fun x =>
    ⟨polyGrowth_gueStatistic_fibre P A₀ A x p, polyGrowth_gueStatisticDir_fibre P A₀ A x p⟩

/-! ### `L²` integrability with respect to the standard Gaussian measure -/

/-- A continuous function with a polynomial bound in `∑ |x q|` is square integrable for the
standard Gaussian measure on `EuclideanSpace ℝ κ`. -/
theorem memLp_two_of_polyBound (F : EuclideanSpace ℝ κ → ℝ) (hF : Continuous F)
    (h : ∃ C : ℝ, 0 ≤ C ∧ ∃ k : ℕ, ∀ x : EuclideanSpace ℝ κ,
      |F x| ≤ C * (1 + ∑ q, |(WithLp.ofLp x) q|) ^ k) :
    MemLp F 2 (stdGaussian (EuclideanSpace ℝ κ)) := by
  obtain ⟨C, hC0, k, hb⟩ := h
  set K : ℝ := max 1 (Fintype.card κ : ℝ) with hK
  have hK1 : 1 ≤ K := le_max_left _ _
  have hK0 : 0 ≤ K := le_trans zero_le_one hK1
  -- The `k`-th power of the norm is square integrable.
  have hnk : MemLp (fun x : EuclideanSpace ℝ κ => ‖x‖ ^ k) 2
      (stdGaussian (EuclideanSpace ℝ κ)) := by
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · subst hk0
      simpa using (memLp_const (1:ℝ) : MemLp (fun _ : EuclideanSpace ℝ κ => (1:ℝ)) 2
        (stdGaussian (EuclideanSpace ℝ κ)))
    · have hkne : k ≠ 0 := hkpos.ne'
      have hdiv : (2 : ENNReal) * (k : ENNReal) / (k : ENNReal) = 2 := by
        have hk0' : (k : ENNReal) ≠ 0 := by exact_mod_cast hkne
        have hkt : (k : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top k
        rw [mul_div_assoc]
        rw [ENNReal.div_self hk0' hkt]
        simp
      have hid : MemLp (id : EuclideanSpace ℝ κ → EuclideanSpace ℝ κ)
          ((2 * k : ℕ) : ENNReal) (stdGaussian (EuclideanSpace ℝ κ)) :=
        IsGaussian.memLp_id _ (((2 * k : ℕ)) : ENNReal)
          (ENNReal.natCast_ne_top (2 * k))
      have h := hid.norm_rpow_div (q := (k : ENNReal))
      simpa [hdiv] using h
  have h1k : MemLp (fun x : EuclideanSpace ℝ κ => (1:ℝ) + ‖x‖ ^ k) 2
      (stdGaussian (EuclideanSpace ℝ κ)) := (memLp_const (1:ℝ)).add hnk
  -- `(1 + r)^k ≤ 2^k (1 + r^k)` for `r ≥ 0`.
  have hpowle : ∀ r : ℝ, 0 ≤ r → (1 + r) ^ k ≤ 2 ^ k * (1 + r ^ k) := by
    intro r hr
    have h2k0 : (0:ℝ) ≤ 2 ^ k := pow_nonneg (by norm_num) k
    have hrk0 : (0:ℝ) ≤ r ^ k := pow_nonneg hr k
    rcases le_or_gt r 1 with hr1 | hr1
    · have h1 : 1 + r ≤ 2 := by linarith
      calc (1 + r) ^ k ≤ 2 ^ k := pow_le_pow_left₀ (by linarith) h1 k
        _ ≤ 2 ^ k * (1 + r ^ k) := by nlinarith
    · have h1 : 1 + r ≤ 2 * r := by linarith
      calc (1 + r) ^ k ≤ (2 * r) ^ k := pow_le_pow_left₀ (by linarith) h1 k
        _ = 2 ^ k * r ^ k := by rw [mul_pow]
        _ ≤ 2 ^ k * (1 + r ^ k) := by nlinarith
  have hpow : MemLp (fun x : EuclideanSpace ℝ κ => (1 + ‖x‖) ^ k) 2
      (stdGaussian (EuclideanSpace ℝ κ)) := by
    refine MemLp.of_le_mul (c := 2 ^ k) h1k ?_ ?_
    · exact (by fun_prop : Continuous
        (fun x : EuclideanSpace ℝ κ => (1 + ‖x‖) ^ k)).aestronglyMeasurable
    · filter_upwards with x
      rw [Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
      exact hpowle ‖x‖ (norm_nonneg _)
  have hS : ∀ x : EuclideanSpace ℝ κ,
      (∑ q, |(WithLp.ofLp x) q|) ≤ (Fintype.card κ : ℝ) * ‖x‖ := by
    intro x
    calc (∑ q, |(WithLp.ofLp x) q|) ≤ ∑ _q : κ, ‖x‖ := by
          refine Finset.sum_le_sum fun q _ => ?_
          rw [← Real.norm_eq_abs]
          have h := PiLp.norm_apply_le (p := 2) (β := fun _ : κ => ℝ) x q
          simpa using h
      _ = (Fintype.card κ : ℝ) * ‖x‖ := by
          simp [Finset.sum_const, nsmul_eq_mul]
  have hcard : (0:ℝ) ≤ (Fintype.card κ : ℝ) := Nat.cast_nonneg _
  refine MemLp.mono' (g := fun x : EuclideanSpace ℝ κ =>
    C * K ^ k * 2 ^ k * (1 + ‖x‖ ^ k)) ?_ hF.aestronglyMeasurable ?_
  · exact h1k.const_mul (C * K ^ k * 2 ^ k)
  · filter_upwards with x
    have hx0 : (0:ℝ) ≤ ‖x‖ := norm_nonneg _
    have hKcard : (Fintype.card κ : ℝ) ≤ K := le_max_right _ _
    have hbase : 1 + (∑ q, |(WithLp.ofLp x) q|) ≤ K * (1 + ‖x‖) := by
      nlinarith [hK1, hKcard, hx0, hS x]
    have hmain : |F x| ≤ C * K ^ k * (1 + ‖x‖) ^ k := by
      calc |F x| ≤ C * (1 + (∑ q, |(WithLp.ofLp x) q|)) ^ k := hb x
        _ ≤ C * (K * (1 + ‖x‖)) ^ k := by
            have hb0 : (0:ℝ) ≤ 1 + (∑ q, |(WithLp.ofLp x) q|) := by positivity
            exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hb0 hbase k) hC0
        _ = C * K ^ k * (1 + ‖x‖) ^ k := by
            rw [mul_pow]; ring
    calc ‖F x‖ = |F x| := Real.norm_eq_abs _
      _ ≤ C * K ^ k * (1 + ‖x‖) ^ k := hmain
      _ ≤ C * K ^ k * (2 ^ k * (1 + ‖x‖ ^ k)) := by
          exact mul_le_mul_of_nonneg_left (hpowle ‖x‖ hx0) (by positivity)
      _ = C * K ^ k * 2 ^ k * ((1:ℝ) + ‖x‖ ^ k) := by ring

/-- **`L²` integrability of the scalar spectral statistic.** -/
theorem memLp_gueStatistic (P : ℝ[X]) (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ) :
    MemLp (gueStatistic P A₀ A) 2 (stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) := by
  refine memLp_two_of_polyBound _ ?_ (gueStatistic_polyBound P A₀ A)
  have hp : Continuous (fun M : Matrix (d × Fin N) (d × Fin N) ℂ => polyMatrix P M) := by
    have hfun : (fun M => polyMatrix P M) =
        fun M : Matrix (d × Fin N) (d × Fin N) ℂ => ∑ k ∈ P.support, P.coeff k • M ^ k := by
      funext M
      exact polyMatrix_eq_sum P M
    rw [hfun]
    fun_prop
  have hH : Continuous (fun x : EuclideanSpace ℝ (GUECoord ι N) =>
      guePencilMatrix A₀ A (WithLp.ofLp x)) := by
    simpa using continuous_guePencilMatrix A₀ A
  have htrace : Continuous (fun M : Matrix (d × Fin N) (d × Fin N) ℂ => Matrix.trace M) := by
    simp only [Matrix.trace, Matrix.diag]
    fun_prop
  exact Complex.continuous_re.comp (htrace.comp (hp.comp hH))

/-- **`L²` integrability of every coordinate derivative.** -/
theorem memLp_gueStatisticDir (P : ℝ[X]) (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    (p : GUECoord ι N) :
    MemLp (gueStatisticDir P A₀ A p) 2
      (stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) := by
  refine memLp_two_of_polyBound _ ?_ (gueStatisticDir_polyBound P A₀ A p)
  have hp : Continuous (fun M : Matrix (d × Fin N) (d × Fin N) ℂ =>
      polyMatrix P.derivative M * gueDirMatrix A p) := by
    have hfun : (fun M => polyMatrix P.derivative M) =
        fun M : Matrix (d × Fin N) (d × Fin N) ℂ =>
          ∑ k ∈ P.derivative.support, P.derivative.coeff k • M ^ k := by
      funext M
      exact polyMatrix_eq_sum P.derivative M
    have hp' : Continuous (fun M : Matrix (d × Fin N) (d × Fin N) ℂ =>
        polyMatrix P.derivative M) := by
      rw [hfun]
      fun_prop
    exact hp'.mul continuous_const
  have hH : Continuous (fun x : EuclideanSpace ℝ (GUECoord ι N) =>
      guePencilMatrix A₀ A (WithLp.ofLp x)) := by
    simpa using continuous_guePencilMatrix A₀ A
  have htrace : Continuous (fun M : Matrix (d × Fin N) (d × Fin N) ℂ => Matrix.trace M) := by
    simp only [Matrix.trace, Matrix.diag]
    fun_prop
  exact Complex.continuous_re.comp (htrace.comp (hp.comp hH))

end

end GUEStrongConvergence
