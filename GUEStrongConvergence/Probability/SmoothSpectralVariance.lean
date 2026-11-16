/-
# Smooth spectral statistics of the GUE: trace derivative and variance (Lemma V)

This module formalizes HT05 Proposition 4.7 / Lemma V, the variance inequality for smooth
spectral statistics of the GUE, using the **trace derivative**

`d/dt Tr(P(H + t K))|₀ = Tr(P'(H) K)`

for a real polynomial `P` and **arbitrary** matrices `H, K`.  The matrix-level identity
`d/dt P(H + t K)|₀ = P'(H) K` is *false* when `H` and `K` do not commute and is never used:
the derivative of the matrix-valued curve is the monomial Fréchet direction
`∑_{j<n} H^j K H^{n-1-j}`, whose trace collapses to `Tr(P'(H) K)` only after cyclicity of the
trace.

The derivative is computed entrywise: every entry of `t ↦ (H + t K)^n` is a scalar polynomial
in `t`, differentiated by the ordinary product rule, and the matrix derivative is repackaged
through `hasDerivAt_pi`.  This keeps the whole development inside `Matrix m m ℂ` with its
default (Pi) normed structure and avoids any operator-norm functional calculus.

## What is proved

* `polyMatrix`, `monomialDirection`, `polyDirection`, `polyDerivMatrix`: the functional
  calculus, its honest Fréchet direction, and the derivative polynomial;
* `hasDerivAt_pow_entry`, `hasDerivAt_pow_matrix`: the matrix-level derivative of
  `t ↦ (H + t K)^n` at an arbitrary point;
* `trace_monomialDirection`, `trace_polyDirection`, `polyDerivMatrix_eq`: the trace derivative
  `d/dt Tr(P(H + t K))|₀ = Tr(P'(H) K)`.

## Class of test functions

The task allows a polynomial class as the `cfc`-compatible replacement for smooth compactly
supported `f`.  We take `P : ℝ[X]`, which is dense in the smooth class and for which the trace
identity is an exact algebraic statement.
-/
import GUEStrongConvergence.Probability.GUEPencil
import GUEStrongConvergence.Probability.PolynomialPoincare
import GUEStrongConvergence.Probability.GaussianPoincare
import Mathlib.Analysis.Matrix.Normed

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped RealInnerProductSpace ENNReal NNReal Topology Polynomial
open scoped BigOperators

namespace GUEStrongConvergence

noncomputable section

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

variable {m : Type*} [Fintype m] [DecidableEq m]

/-- Derivatives commute with taking the real part of a complex-valued curve. -/
lemma hasDerivAt_re_of_complex {f : ℝ → ℂ} {f' : ℂ} {x : ℝ} (h : HasDerivAt f f' x) :
    HasDerivAt (fun y : ℝ => (f y).re) f'.re x := by
  have h1 : HasDerivAt (fun y : ℝ => Complex.reCLM (f y)) (Complex.reCLM f') x :=
    Complex.reCLM.hasFDerivAt.comp_hasDerivAt x h
  convert h1 using 1
  · funext y
    rfl
  · rfl

/-! ### Polynomial functional calculus on complex matrices -/

/-- Polynomial functional calculus: evaluation of a real polynomial at a complex matrix. -/
def polyMatrix (P : ℝ[X]) (H : Matrix m m ℂ) : Matrix m m ℂ := Polynomial.aeval H P

@[simp] lemma polyMatrix_zero (H : Matrix m m ℂ) : polyMatrix (0 : ℝ[X]) H = 0 := by
  simp [polyMatrix]

@[simp] lemma polyMatrix_one (H : Matrix m m ℂ) : polyMatrix (1 : ℝ[X]) H = 1 := by
  simp [polyMatrix]

lemma polyMatrix_add (P Q : ℝ[X]) (H : Matrix m m ℂ) :
    polyMatrix (P + Q) H = polyMatrix P H + polyMatrix Q H := by
  simp [polyMatrix]

lemma polyMatrix_mul (P Q : ℝ[X]) (H : Matrix m m ℂ) :
    polyMatrix (P * Q) H = polyMatrix P H * polyMatrix Q H := by
  simp [polyMatrix]

@[simp] lemma polyMatrix_C (c : ℝ) (H : Matrix m m ℂ) :
    polyMatrix (Polynomial.C c) H = c • (1 : Matrix m m ℂ) := by
  simp [polyMatrix, Algebra.algebraMap_eq_smul_one]

@[simp] lemma polyMatrix_X (H : Matrix m m ℂ) : polyMatrix Polynomial.X H = H := by
  simp [polyMatrix]

@[simp] lemma polyMatrix_X_pow (H : Matrix m m ℂ) (n : ℕ) :
    polyMatrix (Polynomial.X ^ n) H = H ^ n := by
  simp [polyMatrix]

/-- `polyMatrix` expands into the coefficient sum over the support of `P`. -/
lemma polyMatrix_eq_sum (P : ℝ[X]) (H : Matrix m m ℂ) :
    polyMatrix P H = ∑ n ∈ P.support, P.coeff n • H ^ n := by
  rw [polyMatrix, Polynomial.aeval_eq_sum_range]
  refine (Finset.sum_subset ?_ ?_).symm
  · intro n hn
    rw [Finset.mem_range]
    exact Nat.lt_succ_of_le (Polynomial.le_natDegree_of_mem_supp n hn)
  · intro n _ hn
    rw [Polynomial.notMem_support_iff] at hn
    rw [hn, zero_smul]

/-! ### The monomial Fréchet direction -/

/-- The Fréchet direction of the monomial `H ↦ H ^ n` at `H` in the direction `K`:
`∑_{j<n} H^j K H^(n-1-j)`.  This is **not** `n H^(n-1) K` when `H` and `K` fail to commute. -/
def monomialDirection (H K : Matrix m m ℂ) (n : ℕ) : Matrix m m ℂ :=
  ∑ j ∈ Finset.range n, H ^ j * K * H ^ (n - 1 - j)

lemma monomialDirection_zero (H K : Matrix m m ℂ) : monomialDirection H K 0 = 0 := by
  simp [monomialDirection]

lemma monomialDirection_succ (H K : Matrix m m ℂ) (n : ℕ) :
    monomialDirection H K (n + 1) = monomialDirection H K n * H + H ^ n * K := by
  rw [monomialDirection, Finset.sum_range_succ]
  have hterm : ∀ j ∈ Finset.range n, H ^ j * K * H ^ (n + 1 - 1 - j)
      = H ^ j * K * H ^ (n - 1 - j) * H := by
    intro j hj
    rw [Finset.mem_range] at hj
    rw [show n + 1 - 1 - j = n - j by omega]
    simp only [mul_assoc, ← pow_succ, show n - 1 - j + 1 = n - j by omega]
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul, ← monomialDirection]
  rw [Nat.add_sub_cancel, Nat.sub_self, pow_zero, mul_one]

/-! ### Entrywise derivative of the affine line -/

/-- The entry of the affine line `t ↦ H + t K` is affine in `t`, with derivative the
corresponding entry of `K`. -/
lemma hasDerivAt_entry_line (H K : Matrix m m ℂ) (i j : m) (t₀ : ℝ) :
    HasDerivAt (fun t : ℝ => (H + t • K) i j) (K i j) t₀ := by
  have hfun : (fun t : ℝ => (H + t • K) i j) = fun t : ℝ => H i j + (t : ℂ) * K i j := by
    funext t
    simp [Matrix.add_apply, Matrix.smul_apply, Complex.real_smul]
  rw [hfun]
  have h1 : HasDerivAt (fun t : ℝ => (t : ℂ)) (1 : ℂ) t₀ := Complex.ofRealCLM.hasDerivAt
  simpa using ((h1.mul_const (K i j)).const_add (H i j))

/-- **Entrywise derivative of the monomial curve** at an arbitrary point `t₀`.  The derivative
is the Fréchet direction evaluated at the base point `H + t₀ K`. -/
theorem hasDerivAt_pow_entry (H K : Matrix m m ℂ) (n : ℕ) :
    ∀ (i j : m) (t₀ : ℝ), HasDerivAt (fun t : ℝ => ((H + t • K) ^ n) i j)
      (monomialDirection (H + t₀ • K) K n i j) t₀ := by
  induction n with
  | zero =>
    intro i j t₀
    have hfun : (fun t : ℝ => ((H + t • K) ^ 0) i j)
        = fun _ : ℝ => (1 : Matrix m m ℂ) i j := by
      funext t
      rw [pow_zero]
    rw [hfun, monomialDirection_zero]
    simpa using (hasDerivAt_const (x := t₀) (c := ((1 : Matrix m m ℂ) i j)))
  | succ n ih =>
    intro i j t₀
    have hfun : (fun t : ℝ => ((H + t • K) ^ (n + 1)) i j)
        = fun t : ℝ => ∑ k : m, ((H + t • K) ^ n) i k * (H + t • K) k j := by
      funext t
      rw [pow_succ, Matrix.mul_apply]
    rw [hfun]
    have hsum : (fun t : ℝ => ∑ k : m, ((H + t • K) ^ n) i k * (H + t • K) k j)
        = ∑ k : m, fun t : ℝ => ((H + t • K) ^ n) i k * (H + t • K) k j := by
      funext t
      rw [Finset.sum_apply]
    rw [hsum]
    have hderiv : HasDerivAt
        (∑ k : m, fun t : ℝ => ((H + t • K) ^ n) i k * (H + t • K) k j)
        (∑ k : m, (monomialDirection (H + t₀ • K) K n i k * (H + t₀ • K) k j +
          ((H + t₀ • K) ^ n) i k * K k j)) t₀ := by
      refine HasDerivAt.sum (u := Finset.univ) ?_
      intro k _
      exact (ih i k t₀).mul (hasDerivAt_entry_line H K k j t₀)
    refine hderiv.congr_deriv ?_
    rw [monomialDirection_succ, Matrix.add_apply, Matrix.mul_apply, Matrix.mul_apply,
      Finset.sum_add_distrib]

/-- **Matrix-level derivative of the monomial curve** at an arbitrary point `t₀`. -/
theorem hasDerivAt_pow_matrix (H K : Matrix m m ℂ) (n : ℕ) (t₀ : ℝ) :
    HasDerivAt (fun t : ℝ => (H + t • K) ^ n) (monomialDirection (H + t₀ • K) K n) t₀ := by
  apply hasDerivAt_pi.mpr
  intro i
  apply hasDerivAt_pi.mpr
  intro j
  exact hasDerivAt_pow_entry H K n i j t₀

/-- **Derivative of the trace of a monomial curve**. -/
theorem hasDerivAt_trace_pow (H K : Matrix m m ℂ) (n : ℕ) (t₀ : ℝ) :
    HasDerivAt (fun t : ℝ => Matrix.trace ((H + t • K) ^ n))
      (Matrix.trace (monomialDirection (H + t₀ • K) K n)) t₀ := by
  have hfun : (fun t : ℝ => Matrix.trace ((H + t • K) ^ n))
      = fun t : ℝ => ∑ i : m, ((H + t • K) ^ n) i i := by
    funext t
    rw [Matrix.trace]
    simp [Matrix.diag]
  rw [hfun]
  have hsum : (fun t : ℝ => ∑ i : m, ((H + t • K) ^ n) i i)
      = ∑ i : m, fun t : ℝ => ((H + t • K) ^ n) i i := by
    funext t
    rw [Finset.sum_apply]
  rw [hsum]
  have hderiv : HasDerivAt
      (∑ i : m, fun t : ℝ => ((H + t • K) ^ n) i i)
      (∑ i : m, monomialDirection (H + t₀ • K) K n i i) t₀ := by
    refine HasDerivAt.sum (u := Finset.univ) ?_
    intro i _
    exact hasDerivAt_pow_entry H K n i i t₀
  have htr : Matrix.trace (monomialDirection (H + t₀ • K) K n)
      = ∑ i : m, monomialDirection (H + t₀ • K) K n i i := by
    rw [Matrix.trace]
    simp [Matrix.diag]
  rw [htr]
  exact hderiv

/-! ### The polynomial Fréchet direction and the derivative polynomial -/

/-- The Fréchet direction of the polynomial functional calculus. -/
def polyDirection (P : ℝ[X]) (H K : Matrix m m ℂ) : Matrix m m ℂ :=
  ∑ n ∈ P.support, P.coeff n • monomialDirection H K n

/-- The matrix `P'(H)` written in the coefficient form adapted to the trace identity. -/
def polyDerivMatrix (P : ℝ[X]) (H : Matrix m m ℂ) : Matrix m m ℂ :=
  ∑ n ∈ P.support, (P.coeff n * n : ℝ) • H ^ (n - 1)

/-- The trace of the polynomial functional calculus as a coefficient sum. -/
lemma trace_polyMatrix (P : ℝ[X]) (M : Matrix m m ℂ) :
    Matrix.trace (polyMatrix P M)
      = ∑ n ∈ P.support, P.coeff n • Matrix.trace (M ^ n) := by
  rw [polyMatrix_eq_sum, Matrix.trace_sum]
  exact Finset.sum_congr rfl fun n _ => Matrix.trace_smul (P.coeff n) (M ^ n)

/-- The trace of the polynomial Fréchet direction as a coefficient sum. -/
lemma trace_polyDirection (P : ℝ[X]) (M K : Matrix m m ℂ) :
    Matrix.trace (polyDirection P M K)
      = ∑ n ∈ P.support, P.coeff n • Matrix.trace (monomialDirection M K n) := by
  rw [polyDirection, Matrix.trace_sum]
  exact Finset.sum_congr rfl fun n _ => Matrix.trace_smul (P.coeff n) (monomialDirection M K n)

/-- **Cyclicity collapses the trace of the monomial direction** to `n Tr(H^(n-1) K)`. -/
lemma trace_monomialDirection (H K : Matrix m m ℂ) (n : ℕ) :
    Matrix.trace (monomialDirection H K n) = (n : ℂ) * Matrix.trace (H ^ (n - 1) * K) := by
  cases n with
  | zero => simp [monomialDirection]
  | succ n =>
    rw [monomialDirection, Matrix.trace_sum]
    have hterm : ∀ j ∈ Finset.range (n + 1),
        Matrix.trace (H ^ j * K * H ^ (n + 1 - 1 - j))
          = Matrix.trace (H ^ n * K) := by
      intro j hj
      rw [Finset.mem_range] at hj
      have hexp : n + 1 - 1 - j = n - j := by omega
      rw [hexp]
      rw [Matrix.trace_mul_comm (H ^ j * K) (H ^ (n - j))]
      rw [← mul_assoc, ← pow_add, show n - j + j = n by omega]
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    rw [Nat.add_sub_cancel]

/-- The trace identity `Tr(polyDirection) = Tr(P'(H) K)`, at the level of the coefficient
matrices. -/
lemma trace_polyDirection_eq (P : ℝ[X]) (H K : Matrix m m ℂ) :
    Matrix.trace (polyDirection P H K) = Matrix.trace (polyDerivMatrix P H * K) := by
  rw [trace_polyDirection, polyDerivMatrix, Finset.sum_mul, Matrix.trace_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [smul_mul_assoc, Matrix.trace_smul, trace_monomialDirection, Complex.real_smul,
    Complex.real_smul]
  push_cast
  ring

/-- The derivative polynomial matrix is the functional calculus of the formal derivative. -/
lemma polyMatrix_derivative_eq_polyDerivMatrix (P : ℝ[X]) (M : Matrix m m ℂ) :
    polyMatrix P.derivative M = polyDerivMatrix P M := by
  rw [polyMatrix, Polynomial.derivative_apply, Polynomial.sum_def, polyDerivMatrix]
  rw [map_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  simp only [Polynomial.aeval_mul, Polynomial.aeval_C, Polynomial.aeval_X, map_pow,
    Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]

/-- **Trace derivative for polynomials**: for arbitrary matrices `H, K` and every `t₀`,
`d/dt Tr(P(H + t K)) = Tr(P'(H + t₀ K) K)`.

This is the honest trace identity; the matrix-level statement would be false. -/
theorem hasDerivAt_trace_polyMatrix (P : ℝ[X]) (H K : Matrix m m ℂ) (t₀ : ℝ) :
    HasDerivAt (fun t : ℝ => Matrix.trace (polyMatrix P (H + t • K)))
      (Matrix.trace (polyMatrix P.derivative (H + t₀ • K) * K)) t₀ := by
  have hfun : (fun t : ℝ => Matrix.trace (polyMatrix P (H + t • K)))
      = fun t : ℝ => ∑ n ∈ P.support, P.coeff n • Matrix.trace ((H + t • K) ^ n) := by
    funext t
    rw [trace_polyMatrix]
  rw [hfun]
  have hsum : (fun t : ℝ => ∑ n ∈ P.support, P.coeff n • Matrix.trace ((H + t • K) ^ n))
      = ∑ n ∈ P.support, fun t : ℝ => P.coeff n • Matrix.trace ((H + t • K) ^ n) := by
    funext t
    rw [Finset.sum_apply]
  rw [hsum]
  have hderiv : HasDerivAt
      (∑ n ∈ P.support, fun t : ℝ => P.coeff n • Matrix.trace ((H + t • K) ^ n))
      (∑ n ∈ P.support, P.coeff n •
        Matrix.trace (monomialDirection (H + t₀ • K) K n)) t₀ := by
    refine HasDerivAt.sum (u := P.support) ?_
    intro n _
    exact (hasDerivAt_trace_pow H K n t₀).const_smul (P.coeff n)
  refine hderiv.congr_deriv ?_
  rw [← trace_polyDirection P (H + t₀ • K) K,
    polyMatrix_derivative_eq_polyDerivMatrix, ← trace_polyDirection_eq]

/-! ### An entrywise size functional and polynomial growth -/

/-- The sum of the absolute values of all entries (the entrywise `ℓ¹` size). -/
def entrySum {n : Type*} [Fintype n] (M : Matrix n n ℂ) : ℝ :=
  ∑ i, ∑ j, ‖M i j‖

lemma entrySum_nonneg {n : Type*} [Fintype n] (M : Matrix n n ℂ) : 0 ≤ entrySum M :=
  Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => norm_nonneg _

lemma norm_trace_le_entrySum {n : Type*} [Fintype n] (M : Matrix n n ℂ) :
    ‖Matrix.trace M‖ ≤ entrySum M := by
  calc ‖Matrix.trace M‖ ≤ ∑ i, ‖Matrix.diag M i‖ := norm_sum_le _ _
    _ = ∑ i, ‖M i i‖ := by simp
    _ ≤ ∑ i, ∑ j, ‖M i j‖ :=
        Finset.sum_le_sum fun i _ =>
          Finset.single_le_sum (fun j _ => norm_nonneg _) (Finset.mem_univ i)
    _ = entrySum M := rfl

lemma entrySum_mul_le {n : Type*} [Fintype n] (M N : Matrix n n ℂ) :
    entrySum (M * N) ≤ entrySum M * entrySum N := by
  have hrowN : ∀ k, (∑ j, ‖N k j‖) ≤ entrySum N := by
    intro k
    calc (∑ j, ‖N k j‖) ≤ ∑ i, ∑ j, ‖N i j‖ :=
          Finset.single_le_sum (fun i _ => Finset.sum_nonneg fun j _ => norm_nonneg _)
            (Finset.mem_univ k)
      _ = entrySum N := rfl
  have hExp : entrySum (M * N) ≤ ∑ i, ∑ j, ∑ k, ‖M i k‖ * ‖N k j‖ := by
    rw [entrySum]
    refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
    calc ‖(M * N) i j‖ = ‖∑ k, M i k * N k j‖ := by rw [Matrix.mul_apply]
      _ ≤ ∑ k, ‖M i k * N k j‖ := norm_sum_le _ _
      _ = ∑ k, ‖M i k‖ * ‖N k j‖ := by simp only [norm_mul]
  refine hExp.trans ?_
  calc ∑ i, ∑ j, ∑ k, ‖M i k‖ * ‖N k j‖
      = ∑ i, ∑ k, ∑ j, ‖M i k‖ * ‖N k j‖ := by
        refine Finset.sum_congr rfl fun i _ => ?_
        exact Finset.sum_comm
    _ ≤ ∑ i, ∑ k, ‖M i k‖ * entrySum N := by
        refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun k _ => ?_
        rw [← Finset.mul_sum]
        exact mul_le_mul_of_nonneg_left (hrowN k) (norm_nonneg _)
    _ = (∑ i, ∑ k, ‖M i k‖) * entrySum N := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun i _ => (Finset.sum_mul _ _ _).symm
    _ = entrySum M * entrySum N := rfl

lemma entrySum_one {n : Type*} [Fintype n] [DecidableEq n] :
    entrySum (1 : Matrix n n ℂ) = (Fintype.card n : ℝ) := by
  have hrow : ∀ i : n, (∑ j, ‖(1 : Matrix n n ℂ) i j‖) = 1 := by
    intro i
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hji
      simp [Matrix.one_apply, show i ≠ j from fun h => hji h.symm]
    · intro h
      simp at h
  rw [entrySum]
  simp [hrow]

lemma entrySum_pow_le {n : Type*} [Fintype n] [DecidableEq n] (M : Matrix n n ℂ) (k : ℕ) :
    entrySum (M ^ k) ≤ (Fintype.card n : ℝ) * (max 1 (entrySum M)) ^ k := by
  induction k with
  | zero =>
    rw [pow_zero, entrySum_one, pow_zero, mul_one]
  | succ k ih =>
    rw [pow_succ]
    calc entrySum (M ^ k * M) ≤ entrySum (M ^ k) * entrySum M := entrySum_mul_le _ _
      _ ≤ ((Fintype.card n : ℝ) * (max 1 (entrySum M)) ^ k) * entrySum M :=
          mul_le_mul_of_nonneg_right ih (entrySum_nonneg M)
      _ ≤ ((Fintype.card n : ℝ) * (max 1 (entrySum M)) ^ k) * max 1 (entrySum M) :=
          mul_le_mul_of_nonneg_left (le_max_right _ _)
            (mul_nonneg (Nat.cast_nonneg _)
              (pow_nonneg (le_trans zero_le_one (le_max_left _ _)) _))
      _ = (Fintype.card n : ℝ) * (max 1 (entrySum M)) ^ (k + 1) := by ring

/-! ### The GUE pencil: coordinate direction and affine update -/

variable {ι d : Type*} [Fintype ι] [DecidableEq ι] [Fintype d] [DecidableEq d] {N : ℕ}

/-- The coefficient of the Gaussian coordinate `p` in the `(a,b)`-entry of the `i`-th GUE
matrix. -/
def gueMatrixCoeff (p : GUECoord ι N) (i : ι) (a b : Fin N) : ℂ :=
  (gueScale N : ℂ) * (gueAlpha * (if (i, (a, b)) = p then 1 else 0) +
    gueBeta * (if (i, (b, a)) = p then 1 else 0))

/-- The direction of the `i`-th GUE matrix in the coordinate `p`. -/
def gueMatrixDir (p : GUECoord ι N) (i : ι) : Matrix (Fin N) (Fin N) ℂ :=
  fun a b => gueMatrixCoeff p i a b

/-- The direction of the matrix-coefficient pencil in the coordinate `p`. -/
def gueDirMatrix (A : ι → Matrix d d ℂ) (p : GUECoord ι N) :
    Matrix (d × Fin N) (d × Fin N) ℂ :=
  fun a b => ∑ i, A i a.1 b.1 * gueMatrixCoeff p i a.2 b.2

/-- A single GUE matrix is affine in each coordinate, with direction `gueMatrixDir`. -/
lemma gueMatrix_update_eq (x : GUECoord ι N → ℝ) (p : GUECoord ι N) (u : ℝ) (i : ι) :
    gueMatrix (Function.update x p u) i = gueMatrix x i + (u - x p) • gueMatrixDir p i := by
  have hx : ∀ q : GUECoord ι N,
      Function.update x p u q = x q + (u - x p) * (if q = p then (1 : ℝ) else 0) := by
    intro q
    by_cases h : q = p
    · subst h
      simp
    · simp [Function.update_apply, h]
  ext a b
  have h1 := hx (i, (a, b))
  have h2 := hx (i, (b, a))
  simp only [gueMatrix, gueUnscaled, gueMatrixDir, gueMatrixCoeff, Matrix.add_apply,
    Matrix.smul_apply]
  rw [h1, h2]
  push_cast
  by_cases h1' : (i, (a, b)) = p <;> by_cases h2' : (i, (b, a)) = p <;>
    simp [h1', h2'] <;> ring

/-- The matrix-coefficient pencil is affine in each coordinate, with direction
`gueDirMatrix A p`. -/
lemma guePencilMatrix_update_eq (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    (x : GUECoord ι N → ℝ) (p : GUECoord ι N) (u : ℝ) :
    guePencilMatrix A₀ A (Function.update x p u) =
      guePencilMatrix A₀ A x + (u - x p) • gueDirMatrix A p := by
  ext a b
  have hsplit : ∀ i : ι,
      A i a.1 b.1 * gueMatrix (Function.update x p u) i a.2 b.2
        = A i a.1 b.1 * gueMatrix x i a.2 b.2 +
          (u - x p) * (A i a.1 b.1 * gueMatrixDir p i a.2 b.2) := by
    intro i
    rw [gueMatrix_update_eq, Matrix.add_apply, Matrix.smul_apply, Complex.real_smul, mul_add]
    push_cast
    ring_nf
  rw [guePencilMatrix_apply]
  simp only [gueDirMatrix, gueMatrixDir, Matrix.add_apply, Matrix.smul_apply,
    guePencilMatrix_apply, hsplit, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [Complex.real_smul]
  push_cast
  ring

/-- The coordinate update on the Euclidean coordinate space used by Gaussian Poincaré. -/
def euclidUpdate (x : EuclideanSpace ℝ (GUECoord ι N)) (p : GUECoord ι N) (u : ℝ) :
    EuclideanSpace ℝ (GUECoord ι N) :=
  WithLp.toLp 2 (Function.update (WithLp.ofLp x) p u)

@[simp] lemma ofLp_euclidUpdate (x : EuclideanSpace ℝ (GUECoord ι N)) (p : GUECoord ι N)
    (u : ℝ) :
    WithLp.ofLp (euclidUpdate x p u) = Function.update (WithLp.ofLp x) p u := rfl

/-- The real-valued scalar spectral statistic `Z_N = Re Tr(P(H_N(x)))`. -/
def gueStatistic (P : ℝ[X]) (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    (x : EuclideanSpace ℝ (GUECoord ι N)) : ℝ :=
  (Matrix.trace (polyMatrix P (guePencilMatrix A₀ A (WithLp.ofLp x)))).re

/-- The coordinate derivative of the scalar spectral statistic, at the point `x`. -/
def gueStatisticDir (P : ℝ[X]) (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    (p : GUECoord ι N) (x : EuclideanSpace ℝ (GUECoord ι N)) : ℝ :=
  (Matrix.trace (polyMatrix P.derivative
    (guePencilMatrix A₀ A (WithLp.ofLp x)) * gueDirMatrix A p)).re

/-- **Coordinate derivative of the scalar spectral statistic.**  For every base point `x` and
every `t₀`, the derivative of `u ↦ Z_N(x` with coordinate `p` set to `u)` at `t₀` is the trace
derivative evaluated at the updated matrix. -/
theorem hasDerivAt_gueStatistic_update (P : ℝ[X]) (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    (x : EuclideanSpace ℝ (GUECoord ι N)) (p : GUECoord ι N) (t₀ : ℝ) :
    HasDerivAt (fun u : ℝ => gueStatistic P A₀ A (euclidUpdate x p u))
      (gueStatisticDir P A₀ A p (euclidUpdate x p t₀)) t₀ := by
  set H := guePencilMatrix A₀ A (WithLp.ofLp x) with hH
  set D := gueDirMatrix A p with hD
  set xp := (WithLp.ofLp x) p with hxp
  have hM : ∀ u : ℝ,
      guePencilMatrix A₀ A (WithLp.ofLp (euclidUpdate x p u)) = H + (u - xp) • D := by
    intro u
    rw [ofLp_euclidUpdate, guePencilMatrix_update_eq]
  have hfun : (fun u : ℝ => gueStatistic P A₀ A (euclidUpdate x p u))
      = fun u : ℝ => (Matrix.trace (polyMatrix P (H + (u - xp) • D))).re := by
    funext u
    rw [gueStatistic, hM u]
  rw [hfun]
  have hg := hasDerivAt_re_of_complex (hasDerivAt_trace_polyMatrix P H D (t₀ - xp))
  have hshift : HasDerivAt (fun u : ℝ => u - xp) (1 : ℝ) t₀ := by
    simpa using (hasDerivAt_id t₀).sub_const xp
  have hcomp := hg.scomp t₀ hshift
  have hfun2 : ((fun s : ℝ => (Matrix.trace (polyMatrix P (H + s • D))).re) ∘
      (fun u : ℝ => u - xp))
      = fun u : ℝ => (Matrix.trace (polyMatrix P (H + (u - xp) • D))).re := rfl
  rw [hfun2, one_smul] at hcomp
  refine hcomp.congr_deriv ?_
  rw [gueStatisticDir, hM t₀]

/-! ### Hilbert–Schmidt size of the derivative matrix -/

/-- The squared Hilbert–Schmidt norm (sum of squared entry norms). -/
def hsNorm {n : Type*} [Fintype n] (F : Matrix n n ℂ) : ℝ :=
  ∑ a, ∑ b, ‖F a b‖ ^ 2

lemma hsNorm_nonneg {n : Type*} [Fintype n] (F : Matrix n n ℂ) : 0 ≤ hsNorm F :=
  Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => by positivity

/-- The derivative matrix `P'(H_N(x))`, whose trace against the coordinate directions gives
the coordinate derivatives of the statistic. -/
def gueDerivMatrix (P : ℝ[X]) (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    (x : EuclideanSpace ℝ (GUECoord ι N)) : Matrix (d × Fin N) (d × Fin N) ℂ :=
  polyMatrix P.derivative (guePencilMatrix A₀ A (WithLp.ofLp x))

lemma gueStatisticDir_eq (P : ℝ[X]) (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    (p : GUECoord ι N) (x : EuclideanSpace ℝ (GUECoord ι N)) :
    gueStatisticDir P A₀ A p x = (Matrix.trace (gueDerivMatrix P A₀ A x * gueDirMatrix A p)).re :=
  rfl

/-! ### The Gaussian Poincaré inequality for the spectral statistic

Everything here is unconditional except the two analytic hypotheses of the Poincaré inequality:
`L²` of the statistic and of its coordinate derivatives, and polynomial growth of the
one-dimensional fibres.  The coordinate-derivative hypothesis of Poincaré is *proved*
(`hasDerivAt_gueStatistic_update`). -/

/-- **Gaussian Poincaré for the scalar spectral statistic.** -/
theorem variance_gueStatistic_le (P : ℝ[X]) (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    (hF : MemLp (gueStatistic P A₀ A) 2
      (stdGaussian (EuclideanSpace ℝ (GUECoord ι N))))
    (hDmem : ∀ p : GUECoord ι N, MemLp (gueStatisticDir P A₀ A p) 2
      (stdGaussian (EuclideanSpace ℝ (GUECoord ι N))))
    (hpoly : ∀ p : GUECoord ι N, ∀ᵐ x ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N))),
      PolyGrowth (fun u : ℝ => gueStatistic P A₀ A (euclidUpdate x p u)) ∧
        PolyGrowth (fun u : ℝ => gueStatisticDir P A₀ A p (euclidUpdate x p u))) :
    variance (gueStatistic P A₀ A) (stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))
      ≤ ∑ p : GUECoord ι N,
          ∫ x, (gueStatisticDir P A₀ A p x) ^ 2
            ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) := by
  refine gaussian_poincare_stdGaussian (F := gueStatistic P A₀ A)
    (D := gueStatisticDir P A₀ A) hF hDmem ?_ hpoly
  intro p
  filter_upwards with x t
  exact hasDerivAt_gueStatistic_update P A₀ A x p t

/-- **Lemma V, reduced form.**  Given the deterministic contraction bound
`∑_p (∂_p Z_N)^2 ≤ C * ‖P'(H_N)‖²_{HS}` with `C = 4 gueScale(N)^2 * ‖A‖²`, the Gaussian
Poincaré inequality yields
`Var Z_N ≤ C * E ‖P'(H_N)‖²_{HS}`.

With `gueScale(N)^2 = 1/N` this is the `O(1/N)` variance bound for the *unnormalized* trace
`Z_N = Tr P(H_N)`; dividing by `N` gives the `O(1/N³)` bound for `tr_N P(H_N)`. -/
theorem variance_gueStatistic_le_of_contraction (P : ℝ[X]) (A₀ : Matrix d d ℂ)
    (A : ι → Matrix d d ℂ) (cA : ℝ)
    (hF : MemLp (gueStatistic P A₀ A) 2
      (stdGaussian (EuclideanSpace ℝ (GUECoord ι N))))
    (hDmem : ∀ p : GUECoord ι N, MemLp (gueStatisticDir P A₀ A p) 2
      (stdGaussian (EuclideanSpace ℝ (GUECoord ι N))))
    (hpoly : ∀ p : GUECoord ι N, ∀ᵐ x ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N))),
      PolyGrowth (fun u : ℝ => gueStatistic P A₀ A (euclidUpdate x p u)) ∧
        PolyGrowth (fun u : ℝ => gueStatisticDir P A₀ A p (euclidUpdate x p u)))
    (hCint : Integrable (fun x => hsNorm (gueDerivMatrix P A₀ A x))
      (stdGaussian (EuclideanSpace ℝ (GUECoord ι N))))
    (hcontraction : ∀ x : EuclideanSpace ℝ (GUECoord ι N),
      ∑ p : GUECoord ι N, (gueStatisticDir P A₀ A p x) ^ 2
        ≤ 4 * (gueScale N) ^ 2 * cA * hsNorm (gueDerivMatrix P A₀ A x)) :
    variance (gueStatistic P A₀ A) (stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))
      ≤ 4 * (gueScale N) ^ 2 * cA *
          ∫ x, hsNorm (gueDerivMatrix P A₀ A x)
            ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) := by
  refine (variance_gueStatistic_le P A₀ A hF hDmem hpoly).trans ?_
  have hle : (∑ p : GUECoord ι N,
      ∫ x, (gueStatisticDir P A₀ A p x) ^ 2
        ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N))))
      ≤ ∫ x, (4 * (gueScale N) ^ 2 * cA * hsNorm (gueDerivMatrix P A₀ A x))
        ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) := by
    rw [← integral_finsetSum]
    · refine integral_mono ?_ (hCint.const_mul _) ?_
      · exact integrable_finsetSum Finset.univ fun p _ => (hDmem p).integrable_sq
      · intro x
        exact hcontraction x
    · intro p _
      exact (hDmem p).integrable_sq
  refine hle.trans (le_of_eq ?_)
  rw [integral_const_mul]

end
