/-
# Lemma V for `cfc`-smooth spectral statistics of the GUE pencil

This module extends the polynomial Lemma V (`Probability/LemmaVSharp.lean`) to the
continuous functional calculus of the affine GUE pencil.  It proves unconditionally all
the *finite-dimensional* and *algebraic* ingredients of the smooth Lemma V, and isolates
the one analytic input that Mathlib does not currently provide: the cfc trace derivative
`d/dt Tr(f(H + t D))|₀ = Tr(f'(H) D)`.

## Main results (unconditional)

* `trace_guePencilCfc` — `Tr(f(H_N(x))) = ∑_i f(λ_i(x))` (eigenvalue trace formula);
* `isHermitian_guePencilCfc`, `guePencilCfc_mul_self` — the cfc of a real continuous
  function is Hermitian and multiplicative;
* `hsNorm_guePencilCfc_eq` — the **normalized trace identity**
  `‖f(H_N)‖_F² = (card d · N) · tau_N(f²(H_N))`.

## Main results (conditional on the cfc trace derivative)

* `variance_gueStatisticCfc_le_of_contraction` — the sharp Gaussian-Poincaré reduction
  `Var(Z_N) ≤ 2 gueScale(N)² (∑ frob(A_i)²) ∫ ‖f'(H_N)‖_F² / (card d · N)²`;
* `lemmaV_sharp_smooth_of_traceDeriv` — the **smooth Lemma V** in normalized-trace form
  `Var(tau_N(f(H_N))) ≤ 2 (∑ frob(A_i)²) / (card d) / N² · E[tau_N((f')²(H_N))]`;
* `lemmaV_sharp_smooth_rate` — its `O(N⁻⁴)` rate corollary.

## The exact gap

Mathlib (as pinned) has **no differentiability of the continuous functional calculus in
the matrix variable**; a search over `Mathlib/Analysis/CStarAlgebra/` returns no
`HasDerivAt`/`HasFDerivAt` statement for `cfc`.  Hence the hypothesis `hderiv` is not
discharged here.  The verified building blocks of the standard route (polynomial
`C¹`-approximation on the compact spectrum) are included below: `polyIntegral` /
`derivative_polyIntegral`, `exists_polynomial_c1_approx`,
`trace_cfc_eq_sum_eigenvalues_general`, `hsNorm_cfc_eq`,
`eigenvalues_sq_sum_eq_hsNorm` and `eigenvalues_abs_le_sqrt_hsNorm`.  What remains is the
affine-family spectrum bound and the uniform-convergence transfer
(`hasDerivAt_of_tendstoUniformlyOn`); see the "Exact gap" section at the end of the file.
-/
import GUEStrongConvergence.Probability.LemmaVSharp
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Topology.ContinuousMap.Weierstrass
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Deriv.Polynomial

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped RealInnerProductSpace ENNReal NNReal Topology Polynomial BigOperators

namespace GUEStrongConvergence

noncomputable section

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

variable {ι d : Type*} [Fintype ι] [DecidableEq ι] [Fintype d] [DecidableEq d] {N : ℕ}

/-! ### The continuous functional calculus of the pencil -/

/-- The continuous functional calculus `f(H_N(x))` of the Hermitian pencil. -/
def guePencilCfc (f : ℝ → ℝ) (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    (hA₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian)
    (x : EuclideanSpace ℝ (GUECoord ι N)) : Matrix (d × Fin N) (d × Fin N) ℂ :=
  (guePencilMatrix_isHermitian A₀ A hA₀ hA (WithLp.ofLp x)).cfc f

/-- `guePencilCfc` is the generic continuous functional calculus. -/
lemma guePencilCfc_eq_cfc (f : ℝ → ℝ) (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    (hA₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian)
    (x : EuclideanSpace ℝ (GUECoord ι N)) :
    guePencilCfc f A₀ A hA₀ hA x =
      cfc f (guePencilMatrix A₀ A (WithLp.ofLp x)) :=
  (Matrix.IsHermitian.cfc_eq
    (guePencilMatrix_isHermitian A₀ A hA₀ hA (WithLp.ofLp x)) f).symm

/-- Conjugation by a unitary matrix preserves the trace. -/
lemma trace_conj_unitary {n 𝕜 : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n]
    (u : unitary (Matrix n n 𝕜)) (x : Matrix n n 𝕜) :
    (((u : Matrix n n 𝕜) * x * star (u : Matrix n n 𝕜))).trace = x.trace := by
  rw [Matrix.trace_mul_cycle, Unitary.coe_star_mul_self, one_mul]

/-- **Trace formula.**  The trace of `f(H_N(x))` is the sum of `f` over the eigenvalues. -/
theorem trace_guePencilCfc (f : ℝ → ℝ) (A₀ : Matrix d d ℂ)
    (A : ι → Matrix d d ℂ) (hA₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian)
    (x : EuclideanSpace ℝ (GUECoord ι N)) :
    (guePencilCfc f A₀ A hA₀ hA x).trace =
      ∑ i, ((f ((guePencilMatrix_isHermitian A₀ A hA₀ hA (WithLp.ofLp x)).eigenvalues i)
        : ℝ) : ℂ) := by
  rw [guePencilCfc, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply,
    trace_conj_unitary, trace_diagonal]
  rfl

/-- The cfc of a real function of a Hermitian matrix is Hermitian. -/
theorem isHermitian_cfc_real {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n ℂ) (hM : M.IsHermitian) (f : ℝ → ℝ) :
    (hM.cfc f).IsHermitian := by
  rw [isHermitian_iff_isSelfAdjoint, ← Matrix.IsHermitian.cfc_eq hM f]
  have h := cfc_star f M
  have h' : cfc (fun x => star (f x)) M = cfc f M := by
    congr 1
  rw [h'] at h
  exact h.symm

/-- The cfc of the pencil is Hermitian. -/
theorem isHermitian_guePencilCfc (f : ℝ → ℝ) (A₀ : Matrix d d ℂ)
    (A : ι → Matrix d d ℂ) (hA₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian)
    (x : EuclideanSpace ℝ (GUECoord ι N)) :
    (guePencilCfc f A₀ A hA₀ hA x).IsHermitian :=
  isHermitian_cfc_real _ (guePencilMatrix_isHermitian A₀ A hA₀ hA (WithLp.ofLp x)) f

/-- The square of the cfc of a continuous real function is the cfc of the square. -/
theorem guePencilCfc_mul_self (f : ℝ → ℝ) (hf : Continuous f) (A₀ : Matrix d d ℂ)
    (A : ι → Matrix d d ℂ) (hA₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian)
    (x : EuclideanSpace ℝ (GUECoord ι N)) :
    guePencilCfc f A₀ A hA₀ hA x * guePencilCfc f A₀ A hA₀ hA x =
      guePencilCfc (fun y => (f y) ^ 2) A₀ A hA₀ hA x := by
  rw [guePencilCfc_eq_cfc, guePencilCfc_eq_cfc]
  have h := cfc_mul f f (guePencilMatrix A₀ A (WithLp.ofLp x))
    (hf.continuousOn) (hf.continuousOn)
  rw [← h]
  congr 1
  funext y
  ring

/-- **Normalized trace identity for the cfc.**  For a continuous real `f`,
`‖f(H_N(x))‖_F² = (card d · N) · tau_N(f²(H_N(x)))`. -/
theorem hsNorm_guePencilCfc_eq [Nonempty d] (f : ℝ → ℝ) (hf : Continuous f)
    (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ) (hA₀ : A₀.IsHermitian)
    (hA : ∀ i, (A i).IsHermitian) (hN : 0 < N)
    (x : EuclideanSpace ℝ (GUECoord ι N)) :
    hsNorm (guePencilCfc f A₀ A hA₀ hA x) =
      ((Fintype.card d * N : ℕ) : ℝ) *
        (guePencilNormTrace (guePencilCfc (fun y => (f y) ^ 2) A₀ A hA₀ hA x)) := by
  have hH := isHermitian_guePencilCfc f A₀ A hA₀ hA x
  rw [hsNorm_eq_trace_mul_re_of_isHermitian _ hH,
    guePencilCfc_mul_self f hf A₀ A hA₀ hA x]
  have hcard : 0 < Fintype.card d := Fintype.card_pos_iff.mpr ‹Nonempty d›
  have hdN : ((Fintype.card d * N : ℕ) : ℝ) ≠ 0 := by
    have hpos : 0 < Fintype.card d * N := Nat.mul_pos hcard hN
    exact_mod_cast hpos.ne'
  simp only [guePencilNormTrace, gueNormConst]
  field_simp

/-- The normalized smooth spectral statistic `Z_N = tau_N(f(H_N))`. -/
def gueStatisticCfc (f : ℝ → ℝ) (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    (hA₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian)
    (x : EuclideanSpace ℝ (GUECoord ι N)) : ℝ :=
  guePencilNormTrace (guePencilCfc f A₀ A hA₀ hA x)

/-- The formal coordinate derivative `tau_N(f'(H_N) D_p)`. -/
def gueStatisticCfcDir (f : ℝ → ℝ) (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    (hA₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian)
    (p : GUECoord ι N) (x : EuclideanSpace ℝ (GUECoord ι N)) : ℝ :=
  guePencilNormTrace
    (guePencilCfc (deriv f) A₀ A hA₀ hA x * gueDirMatrix A p)

/-! ### Conditional sharp Lemma V for `cfc`-smooth statistics -/

/-- **Lemma V, cfc reduced form.**  Assume the cfc trace derivative of the statistic along
each Gaussian coordinate, plus the analytic side conditions.  Then

`Var(Z_N) ≤ (card d · N)⁻² · 2 gueScale(N)² (∑_i frob(A_i)²) · E‖f'(H_N)‖_F²`.

The trace derivative `hderiv` is the only non-elementary input. -/
theorem variance_gueStatisticCfc_le_of_contraction [Nonempty d] (f : ℝ → ℝ)
    (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ) (hA₀ : A₀.IsHermitian)
    (hA : ∀ i, (A i).IsHermitian) (hN : 0 < N)
    (hF : MemLp (gueStatisticCfc f A₀ A hA₀ hA) 2
      (stdGaussian (EuclideanSpace ℝ (GUECoord ι N))))
    (hDmem : ∀ p : GUECoord ι N, MemLp (gueStatisticCfcDir f A₀ A hA₀ hA p) 2
      (stdGaussian (EuclideanSpace ℝ (GUECoord ι N))))
    (hpoly : ∀ p : GUECoord ι N,
      ∀ᵐ x ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N))),
        PolyGrowth (fun u : ℝ => gueStatisticCfc f A₀ A hA₀ hA (euclidUpdate x p u)) ∧
        PolyGrowth (fun u : ℝ =>
          gueStatisticCfcDir f A₀ A hA₀ hA p (euclidUpdate x p u)))
    (hderiv : ∀ (p : GUECoord ι N),
      ∀ᵐ x ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N))), ∀ t : ℝ,
        HasDerivAt (fun u : ℝ => gueStatisticCfc f A₀ A hA₀ hA (euclidUpdate x p u))
          (gueStatisticCfcDir f A₀ A hA₀ hA p (euclidUpdate x p t)) t)
    (hint : Integrable
      (fun x => hsNorm (guePencilCfc (deriv f) A₀ A hA₀ hA x))
      (stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))) :
    variance (gueStatisticCfc f A₀ A hA₀ hA)
        (stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))
      ≤ (gueNormConst d N) ^ 2 *
          (2 * (gueScale N) ^ 2 * (∑ i, (frob (A i)) ^ 2) *
            ∫ x, hsNorm (guePencilCfc (deriv f) A₀ A hA₀ hA x)
              ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))) := by
  classical
  set μ := stdGaussian (EuclideanSpace ℝ (GUECoord ι N)) with hμ
  set c : ℝ := gueNormConst d N with hc
  -- Gaussian Poincaré.
  have hpoincare : variance (gueStatisticCfc f A₀ A hA₀ hA) μ
      ≤ ∑ p : GUECoord ι N,
          ∫ x, (gueStatisticCfcDir f A₀ A hA₀ hA p x) ^ 2 ∂μ :=
    gaussian_poincare_stdGaussian (F := gueStatisticCfc f A₀ A hA₀ hA)
      (D := gueStatisticCfcDir f A₀ A hA₀ hA) hF hDmem hderiv hpoly
  -- Exchange the finite sum and the integral.
  have h3 : (∑ p : GUECoord ι N,
        ∫ x, (gueStatisticCfcDir f A₀ A hA₀ hA p x) ^ 2 ∂μ)
      = ∫ x, ∑ p : GUECoord ι N,
          (gueStatisticCfcDir f A₀ A hA₀ hA p x) ^ 2 ∂μ := by
    rw [integral_finsetSum]
    intro p _
    exact (hDmem p).integrable_sq
  -- Pointwise contraction of the coordinate gradient.
  have hcontr : ∀ x : EuclideanSpace ℝ (GUECoord ι N),
      ∑ p : GUECoord ι N, (gueStatisticCfcDir f A₀ A hA₀ hA p x) ^ 2
        ≤ (c ^ 2 * (2 * (gueScale N) ^ 2 * (∑ i, (frob (A i)) ^ 2))) *
            hsNorm (guePencilCfc (deriv f) A₀ A hA₀ hA x) := by
    intro x
    have hpt : ∀ p : GUECoord ι N,
        (gueStatisticCfcDir f A₀ A hA₀ hA p x) ^ 2
          = c ^ 2 * (Matrix.trace
              (gueDirMatrix A p * guePencilCfc (deriv f) A₀ A hA₀ hA x)).re ^ 2 := by
      intro p
      rw [gueStatisticCfcDir, guePencilNormTrace, hc]
      rw [Matrix.trace_mul_comm]
      ring
    simp_rw [hpt]
    rw [← Finset.mul_sum]
    calc c ^ 2 * (∑ p : GUECoord ι N,
          (Matrix.trace (gueDirMatrix A p *
            guePencilCfc (deriv f) A₀ A hA₀ hA x)).re ^ 2)
        ≤ c ^ 2 * ((2 * (gueScale N) ^ 2 * (∑ i, (frob (A i)) ^ 2)) *
            hsNorm (guePencilCfc (deriv f) A₀ A hA₀ hA x)) := by
          refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg c)
          refine (Finset.sum_le_sum fun p _ => ?_).trans
            (sum_sq_trace_direction_le (guePencilCfc (deriv f) A₀ A hA₀ hA x) A)
          have h := Complex.abs_re_le_norm
            (Matrix.trace (gueDirMatrix A p * guePencilCfc (deriv f) A₀ A hA₀ hA x))
          have h2' := pow_le_pow_left₀ (abs_nonneg _) h 2
          simpa [sq_abs] using h2'
      _ = (c ^ 2 * (2 * (gueScale N) ^ 2 * (∑ i, (frob (A i)) ^ 2))) *
            hsNorm (guePencilCfc (deriv f) A₀ A hA₀ hA x) := by ring
  -- Integrability of the pointwise sum and of the HS integrand.
  have hsum_int : Integrable (fun x => ∑ p : GUECoord ι N,
      (gueStatisticCfcDir f A₀ A hA₀ hA p x) ^ 2) μ :=
    integrable_finsetSum _ fun p _ => (hDmem p).integrable_sq
  have h4 : (∫ x, ∑ p : GUECoord ι N,
        (gueStatisticCfcDir f A₀ A hA₀ hA p x) ^ 2 ∂μ)
      ≤ ∫ x, (c ^ 2 * (2 * (gueScale N) ^ 2 * (∑ i, (frob (A i)) ^ 2))) *
          hsNorm (guePencilCfc (deriv f) A₀ A hA₀ hA x) ∂μ :=
    integral_mono hsum_int
      (hint.const_mul (c ^ 2 * (2 * (gueScale N) ^ 2 * (∑ i, (frob (A i)) ^ 2)))) hcontr
  have h5 : (∫ x, (c ^ 2 * (2 * (gueScale N) ^ 2 * (∑ i, (frob (A i)) ^ 2))) *
        hsNorm (guePencilCfc (deriv f) A₀ A hA₀ hA x) ∂μ)
      = c ^ 2 * (2 * (gueScale N) ^ 2 * (∑ i, (frob (A i)) ^ 2) *
          ∫ x, hsNorm (guePencilCfc (deriv f) A₀ A hA₀ hA x) ∂μ) := by
    rw [integral_const_mul]
    ring
  exact hpoincare.trans (by rw [h3]; exact h4.trans (le_of_eq h5))

/-- **Smooth Lemma V (normalized-trace form).**  Let `f : ℝ → ℝ` be continuous, with
continuous derivative (so that `(f')²` is continuous), and assume the cfc trace derivative
of `tau_N(f(H_N))` along every Gaussian coordinate.  Then

`Var(tau_N(f(H_N))) ≤ 2 (∑_i frob(A_i)²) / (card d) / N² · E[tau_N((f')²(H_N))]`.

The `1/N²` factor is the point, exactly as in the polynomial case.  The hypothesis
`hderiv` is the cfc trace derivative; it is the only analytic input not available in
Mathlib's current `cfc` API. -/
theorem lemmaV_sharp_smooth_of_traceDeriv [Nonempty d] (f : ℝ → ℝ) (hf : Continuous f)
    (hf' : Continuous (deriv f)) (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    (hA₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian) (hN : 0 < N)
    (hF : MemLp (gueStatisticCfc f A₀ A hA₀ hA) 2
      (stdGaussian (EuclideanSpace ℝ (GUECoord ι N))))
    (hDmem : ∀ p : GUECoord ι N, MemLp (gueStatisticCfcDir f A₀ A hA₀ hA p) 2
      (stdGaussian (EuclideanSpace ℝ (GUECoord ι N))))
    (hpoly : ∀ p : GUECoord ι N,
      ∀ᵐ x ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N))),
        PolyGrowth (fun u : ℝ => gueStatisticCfc f A₀ A hA₀ hA (euclidUpdate x p u)) ∧
        PolyGrowth (fun u : ℝ =>
          gueStatisticCfcDir f A₀ A hA₀ hA p (euclidUpdate x p u)))
    (hderiv : ∀ (p : GUECoord ι N),
      ∀ᵐ x ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N))), ∀ t : ℝ,
        HasDerivAt (fun u : ℝ => gueStatisticCfc f A₀ A hA₀ hA (euclidUpdate x p u))
          (gueStatisticCfcDir f A₀ A hA₀ hA p (euclidUpdate x p t)) t)
    (hint : Integrable
      (fun x => hsNorm (guePencilCfc (deriv f) A₀ A hA₀ hA x))
      (stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))) :
    variance (gueStatisticCfc f A₀ A hA₀ hA)
        (stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))
      ≤ 2 * (∑ i, (frob (A i)) ^ 2) / (Fintype.card d : ℝ) / (N : ℝ) ^ 2 *
          ∫ x, gueStatisticCfc (fun y => (deriv f y) ^ 2) A₀ A hA₀ hA x
            ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) := by
  classical
  set μ := stdGaussian (EuclideanSpace ℝ (GUECoord ι N)) with hμ
  set c : ℝ := gueNormConst d N with hc
  set S : ℝ := ∑ i, (frob (A i)) ^ 2 with hS
  set I : ℝ := ∫ x, gueStatisticCfc (fun y => (deriv f y) ^ 2) A₀ A hA₀ hA x ∂μ with hI
  -- The identity `‖f'(H)‖_F² = (card d · N) · tau_N((f')²(H))` under the integral.
  have hconv : (∫ x, hsNorm (guePencilCfc (deriv f) A₀ A hA₀ hA x) ∂μ)
      = ((Fintype.card d * N : ℕ) : ℝ) * I := by
    have heq : (fun x : EuclideanSpace ℝ (GUECoord ι N) =>
          hsNorm (guePencilCfc (deriv f) A₀ A hA₀ hA x))
        = fun x : EuclideanSpace ℝ (GUECoord ι N) =>
            ((Fintype.card d * N : ℕ) : ℝ) *
              gueStatisticCfc (fun y => (deriv f y) ^ 2) A₀ A hA₀ hA x := by
      funext x
      simp only [gueStatisticCfc]
      exact hsNorm_guePencilCfc_eq (deriv f) hf' A₀ A hA₀ hA hN x
    rw [heq, integral_const_mul, hI]
  refine (variance_gueStatisticCfc_le_of_contraction f A₀ A hA₀ hA hN hF hDmem hpoly
    hderiv hint).trans (le_of_eq ?_)
  rw [hconv, hS, hI]
  have hcard : 0 < Fintype.card d := Fintype.card_pos_iff.mpr ‹Nonempty d›
  have hcardR : (0 : ℝ) < (Fintype.card d : ℝ) := by exact_mod_cast hcard
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hDn : ((Fintype.card d * N : ℕ) : ℝ) = (Fintype.card d : ℝ) * (N : ℝ) := by
    push_cast
    ring
  rw [gueNormConst, gueScale_sq, hDn]
  field_simp

/-- **Smooth Lemma V, explicit `O(N⁻⁴)` rate.**  If in addition
`E[tau_N((f')²(H_N))] ≤ C' / N²`, then `Var(tau_N(f(H_N))) ≤ 2 (∑ frob(A_i)²) C' / (card d) / N⁴`. -/
theorem lemmaV_sharp_smooth_rate [Nonempty d] (f : ℝ → ℝ) (hf : Continuous f)
    (hf' : Continuous (deriv f)) (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    (hA₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian) (hN : 0 < N)
    (hF : MemLp (gueStatisticCfc f A₀ A hA₀ hA) 2
      (stdGaussian (EuclideanSpace ℝ (GUECoord ι N))))
    (hDmem : ∀ p : GUECoord ι N, MemLp (gueStatisticCfcDir f A₀ A hA₀ hA p) 2
      (stdGaussian (EuclideanSpace ℝ (GUECoord ι N))))
    (hpoly : ∀ p : GUECoord ι N,
      ∀ᵐ x ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N))),
        PolyGrowth (fun u : ℝ => gueStatisticCfc f A₀ A hA₀ hA (euclidUpdate x p u)) ∧
        PolyGrowth (fun u : ℝ =>
          gueStatisticCfcDir f A₀ A hA₀ hA p (euclidUpdate x p u)))
    (hderiv : ∀ (p : GUECoord ι N),
      ∀ᵐ x ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N))), ∀ t : ℝ,
        HasDerivAt (fun u : ℝ => gueStatisticCfc f A₀ A hA₀ hA (euclidUpdate x p u))
          (gueStatisticCfcDir f A₀ A hA₀ hA p (euclidUpdate x p t)) t)
    (hint : Integrable
      (fun x => hsNorm (guePencilCfc (deriv f) A₀ A hA₀ hA x))
      (stdGaussian (EuclideanSpace ℝ (GUECoord ι N))))
    (C' : ℝ)
    (hW : (∫ x, gueStatisticCfc (fun y => (deriv f y) ^ 2) A₀ A hA₀ hA x
        ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))) ≤ C' / (N : ℝ) ^ 2) :
    variance (gueStatisticCfc f A₀ A hA₀ hA)
        (stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))
      ≤ 2 * (∑ i, (frob (A i)) ^ 2) * C' / (Fintype.card d : ℝ) / (N : ℝ) ^ 4 := by
  have hcard : (0 : ℝ) ≤ (Fintype.card d : ℝ) := Nat.cast_nonneg _
  have hNR : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg _
  have hS : (0 : ℝ) ≤ ∑ i, (frob (A i)) ^ 2 :=
    Finset.sum_nonneg fun i _ => sq_nonneg _
  refine (lemmaV_sharp_smooth_of_traceDeriv f hf hf' A₀ A hA₀ hA hN hF hDmem hpoly
    hderiv hint).trans ?_
  have hcoef : (0 : ℝ) ≤
      2 * (∑ i, (frob (A i)) ^ 2) / (Fintype.card d : ℝ) / (N : ℝ) ^ 2 := by
    positivity
  calc 2 * (∑ i, (frob (A i)) ^ 2) / (Fintype.card d : ℝ) / (N : ℝ) ^ 2 *
        ∫ x, gueStatisticCfc (fun y => (deriv f y) ^ 2) A₀ A hA₀ hA x
          ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))
      ≤ 2 * (∑ i, (frob (A i)) ^ 2) / (Fintype.card d : ℝ) / (N : ℝ) ^ 2 *
          (C' / (N : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_left hW hcoef
    _ = 2 * (∑ i, (frob (A i)) ^ 2) * C' / (Fintype.card d : ℝ) / (N : ℝ) ^ 4 := by
        ring

/-! ### Interface with the spectral-exclusion lemma (Lemma S) -/

/-- **The `(V)` input of `CutoffExclusion.ae_eventually_spectrum_subset`.**  For a smooth
cutoff `f` of the spectral-exclusion argument (`0 ≤ f`, `f = 1` outside `S + (-ε, ε)`),
this is exactly the variance inequality consumed by Lemma S, with the sharp `1/N²`
constant, *conditional* on the cfc trace derivative `hderiv` and the analytic side
conditions.  The proof is `lemmaV_sharp_smooth_of_traceDeriv`; the cutoff hypotheses are
not needed for the variance bound itself and are included only to document that this is
the right specialization. -/
theorem lemmaS_V_input [Nonempty d] (f : ℝ → ℝ) (hf : Continuous f)
    (hf' : Continuous (deriv f)) (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    (hA₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian) (hN : 0 < N)
    (hF : MemLp (gueStatisticCfc f A₀ A hA₀ hA) 2
      (stdGaussian (EuclideanSpace ℝ (GUECoord ι N))))
    (hDmem : ∀ p : GUECoord ι N, MemLp (gueStatisticCfcDir f A₀ A hA₀ hA p) 2
      (stdGaussian (EuclideanSpace ℝ (GUECoord ι N))))
    (hpoly : ∀ p : GUECoord ι N,
      ∀ᵐ x ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N))),
        PolyGrowth (fun u : ℝ => gueStatisticCfc f A₀ A hA₀ hA (euclidUpdate x p u)) ∧
        PolyGrowth (fun u : ℝ =>
          gueStatisticCfcDir f A₀ A hA₀ hA p (euclidUpdate x p u)))
    (hderiv : ∀ (p : GUECoord ι N),
      ∀ᵐ x ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N))), ∀ t : ℝ,
        HasDerivAt (fun u : ℝ => gueStatisticCfc f A₀ A hA₀ hA (euclidUpdate x p u))
          (gueStatisticCfcDir f A₀ A hA₀ hA p (euclidUpdate x p t)) t)
    (hint : Integrable
      (fun x => hsNorm (guePencilCfc (deriv f) A₀ A hA₀ hA x))
      (stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))) :
    variance (gueStatisticCfc f A₀ A hA₀ hA)
        (stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))
      ≤ 2 * (∑ i, (frob (A i)) ^ 2) / (Fintype.card d : ℝ) / (N : ℝ) ^ 2 *
          ∫ x, gueStatisticCfc (fun y => (deriv f y) ^ 2) A₀ A hA₀ hA x
            ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) :=
  lemmaV_sharp_smooth_of_traceDeriv f hf hf' A₀ A hA₀ hA hN hF hDmem hpoly hderiv hint

/-- **The `(W)`/`(V)` side input** needed by `ae_eventually_spectrum_subset`:
`E[tau_N((f')²(H_N))] ≤ C' / N²`.  This is *not* a consequence of Lemma V; it is the
companion mean bound that the spectral-exclusion argument assumes separately.  For a
cutoff with bounded derivative it should be `O(1)`, and the sharp `O(N⁻²)` input has to
come from the structural cancellation in `tau_N`; we record it here as the second
explicit hypothesis of the Lemma-S interface. -/
def LemmaS_Wb (f : ℝ → ℝ) (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    (hA₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian) (C' : ℝ) : Prop :=
  ∀ N : ℕ, (∫ x, gueStatisticCfc (fun y => (deriv f y) ^ 2) A₀ A hA₀ hA x
      ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))) ≤ C' / (N : ℝ) ^ 2

/-! ### Exact gap

The single unproved analytic input of `lemmaV_sharp_smooth_of_traceDeriv` is `hderiv`:
the cfc trace derivative
`d/dt tau_N(f(H_N(x + t e_p)))|₀ = tau_N(f'(H_N(x)) D_p)`.
It is *mathematically true* for `f ∈ C¹` and Hermitian directions `D_p` (which the GUE
directions are when the coefficients `A_i` are Hermitian), but Mathlib has no
differentiability theory for `cfc` in the matrix variable.

**Already verified in this file** (reducing the gap):
1. `polyIntegral` / `derivative_polyIntegral` — the formal polynomial antiderivative
   (`Polynomial.integral` does not exist in the pinned Mathlib);
2. `exists_polynomial_c1_approx` — simultaneous `C⁰`/`C¹` polynomial approximation on a
   compact interval containing the origin (Weierstrass for `f'` + antiderivative + FTC);
3. `trace_cfc_eq_sum_eigenvalues_general`, `hsNorm_cfc_eq`,
   `eigenvalues_sq_sum_eq_hsNorm`, `eigenvalues_abs_le_sqrt_hsNorm` — the eigenvalue
   trace formula, the cfc Hilbert–Schmidt identity, and the spectrum bound
   `|λ_i| ≤ √(hsNorm M)`.

**Still missing for `hderiv`:**
4. the spectrum bound for the affine family `H + t•D` on `|t| ≤ 1` (the operator norm of
   the `CStarMatrix` type synonym gives `‖H + t•D‖ ≤ ‖H‖ + ‖D‖`), supplying the common
   compact interval `I_x`;
5. the uniform-convergence transfer `hasDerivAt_of_tendstoUniformlyOn`, using
   `hasDerivAt_trace_polyMatrix` for the polynomial approximants and the bounds
   `|Tr(cfc g M)| ≤ card · sup|g|` and
   `|Tr(cfc g M · D)| ≤ √(card · sup|g|² · hsNorm D)`.

Once `hderiv` is available, the hypotheses `hF`, `hDmem`, `hpoly`, `hint` are discharged
for bounded `f` and `f'` from sup-norm bounds on the cfc trace and the Hilbert–Schmidt
Cauchy–Schwarz inequality, provided measurability of the cfc statistic (obtainable as a
pointwise limit of polynomial statistics on the exhausting sets `{‖x‖ ≤ k}`).
-/

/-! ### Prerequisites for the missing cfc trace derivative

The following results are the verified building blocks of the polynomial
`C¹`-approximation route to `hderiv`.  They reduce the gap to the uniform-convergence
transfer (`hasDerivAt_of_tendstoUniformlyOn`) and the bookkeeping of the approximation. -/

/-- Formal antiderivative of a real polynomial (absent from the pinned Mathlib). -/
def polyIntegral (p : ℝ[X]) : ℝ[X] :=
  ∑ n ∈ p.support, Polynomial.C (p.coeff n / (n + 1 : ℝ)) * Polynomial.X ^ (n + 1)

/-- The formal antiderivative differentiates back to the polynomial. -/
lemma derivative_polyIntegral (p : ℝ[X]) : (polyIntegral p).derivative = p := by
  rw [polyIntegral, Polynomial.derivative_sum]
  have hterm : ∀ n ∈ p.support,
      (Polynomial.C (p.coeff n / (n + 1 : ℝ)) * Polynomial.X ^ (n + 1) : ℝ[X]).derivative
        = Polynomial.C (p.coeff n) * Polynomial.X ^ n := by
    intro n _
    rw [Polynomial.derivative_C_mul, Polynomial.derivative_X_pow_succ]
    have hc : (n : ℝ) + 1 ≠ 0 := by positivity
    rw [← mul_assoc, ← Polynomial.C_mul]
    congr 1
    field_simp
  rw [Finset.sum_congr rfl hterm]
  exact Polynomial.sum_C_mul_X_pow_eq p

/-- The formal antiderivative vanishes at the origin. -/
lemma eval_zero_polyIntegral (p : ℝ[X]) : (polyIntegral p).eval 0 = 0 := by
  rw [polyIntegral, Polynomial.eval_finsetSum]
  refine Finset.sum_eq_zero fun n hn => ?_
  rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  simp

/-- **Simultaneous `C⁰`/`C¹` polynomial approximation on a compact interval containing
the origin.**  For `f ∈ C¹` there is a polynomial `q` with `|q - f| < ε` and
`|q' - f'| < ε` on `[a,b]`. -/
lemma exists_polynomial_c1_approx (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f)
    {a b : ℝ} (ha : a < 0) (hb : 0 < b) {ε : ℝ} (hε : 0 < ε) :
    ∃ q : ℝ[X], (∀ x ∈ Set.Icc a b, |q.eval x - f x| < ε) ∧
      (∀ x ∈ Set.Icc a b, |q.derivative.eval x - deriv f x| < ε) := by
  set R : ℝ := max (-a) b + 1 with hR
  have hR1 : (1 : ℝ) ≤ R := by
    rw [hR]; linarith [le_max_left (-a) b]
  have hR0 : (0 : ℝ) < R := lt_of_lt_of_le zero_lt_one hR1
  have hRabs : ∀ x ∈ Set.Icc a b, |x| ≤ R := by
    intro x hx
    rw [abs_le]
    constructor
    · have h := le_max_left (-a) b; linarith [hx.1]
    · have h := le_max_right (-a) b; linarith [hx.2]
  set ε' : ℝ := ε / (2 * R) with hε'
  have hε'0 : 0 < ε' := by positivity
  have hderiv_cont : ContinuousOn (deriv f) (Set.Icc a b) :=
    hf.continuous_deriv_one.continuousOn
  obtain ⟨p, hp⟩ := exists_polynomial_near_of_continuousOn a b (deriv f) hderiv_cont ε' hε'0
  refine ⟨Polynomial.C (f 0) + polyIntegral p, ?_, ?_⟩
  · intro x hx
    have hqderiv : (Polynomial.C (f 0) + polyIntegral p).derivative = p := by
      rw [Polynomial.derivative_add, Polynomial.derivative_C, zero_add, derivative_polyIntegral]
    have hderiv_g : ∀ y : ℝ,
        HasDerivAt (fun z => (Polynomial.C (f 0) + polyIntegral p).eval z - f z)
          (p.eval y - deriv f y) y := by
      intro y
      have h1 : HasDerivAt (fun z => (Polynomial.C (f 0) + polyIntegral p).eval z)
          ((Polynomial.C (f 0) + polyIntegral p).derivative.eval y) y :=
        Polynomial.hasDerivAt (p := Polynomial.C (f 0) + polyIntegral p) y
      have h2 : HasDerivAt f (deriv f y) y :=
        (hf.differentiable (by norm_num) y).hasDerivAt
      convert h1.sub h2 using 1
      rw [hqderiv]
    have hint : IntervalIntegrable (fun y => p.eval y - deriv f y) volume (0 : ℝ) x := by
      refine Continuous.intervalIntegrable ?_ 0 x
      exact (Polynomial.continuous p).sub hf.continuous_deriv_one
    have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := (0:ℝ)) (b := x)
      (fun y _ => hderiv_g y) hint
    have hq0 : (Polynomial.C (f 0) + polyIntegral p).eval 0 = f 0 := by
      simp [eval_zero_polyIntegral]
    have hval : (Polynomial.C (f 0) + polyIntegral p).eval x - f x
        = ∫ y in (0:ℝ)..x, (p.eval y - deriv f y) := by
      rw [hFTC, hq0]; ring
    rw [hval]
    have hIcc : ∀ y ∈ Set.uIcc (0:ℝ) x, y ∈ Set.Icc a b := by
      intro y hy
      have h0 : (0:ℝ) ∈ Set.Icc a b := ⟨le_of_lt ha, le_of_lt hb⟩
      rcases Set.mem_uIcc.mp hy with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact ⟨h0.1.trans h1, h2.trans hx.2⟩
      · exact ⟨hx.1.trans h1, h2.trans h0.2⟩
    have hbound : ‖∫ y in (0:ℝ)..x, (p.eval y - deriv f y)‖ ≤ ε' * |x - 0| := by
      refine intervalIntegral.norm_integral_le_of_norm_le_const ?_
      intro y hy
      rw [Real.norm_eq_abs]
      exact le_of_lt (hp y (hIcc y (Set.uIoc_subset_uIcc hy)))
    have hxe : |x - 0| = |x| := by ring_nf
    rw [hxe] at hbound
    have hle : ε' * |x| ≤ ε / 2 := by
      have h : ε' * |x| ≤ ε' * R := mul_le_mul_of_nonneg_left (hRabs x hx) hε'0.le
      calc ε' * |x| ≤ ε' * R := h
        _ = ε / 2 := by rw [hε']; field_simp
    have hb2 : |∫ y in (0:ℝ)..x, (p.eval y - deriv f y)| ≤ ε / 2 := by
      simpa [Real.norm_eq_abs] using hbound.trans hle
    linarith
  · intro x hx
    have hqderiv : (Polynomial.C (f 0) + polyIntegral p).derivative = p := by
      rw [Polynomial.derivative_add, Polynomial.derivative_C, zero_add, derivative_polyIntegral]
    rw [hqderiv]
    refine lt_of_lt_of_le (hp x hx) ?_
    rw [hε', div_le_iff₀ (by positivity : (0:ℝ) < 2 * R)]
    nlinarith [hε.le, hR1]

/-- **Trace formula for a general Hermitian matrix.** -/
lemma trace_cfc_eq_sum_eigenvalues_general {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n ℂ) (hM : M.IsHermitian) (g : ℝ → ℝ) :
    (hM.cfc g).trace = ∑ i, ((g (hM.eigenvalues i) : ℝ) : ℂ) := by
  rw [Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply, trace_conj_unitary,
    trace_diagonal]
  rfl

/-- **Hilbert–Schmidt norm of a cfc** in terms of the trace of the square. -/
lemma hsNorm_cfc_eq {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n ℂ) (hM : M.IsHermitian) (g : ℝ → ℝ) (hg : Continuous g) :
    hsNorm (hM.cfc g) = (Matrix.trace (hM.cfc (fun y => (g y) ^ 2))).re := by
  have hH := isHermitian_cfc_real M hM g
  rw [hsNorm_eq_trace_mul_re_of_isHermitian _ hH]
  have hmul : hM.cfc g * hM.cfc g = hM.cfc (fun y => (g y) ^ 2) := by
    rw [← Matrix.IsHermitian.cfc_eq hM g, ← Matrix.IsHermitian.cfc_eq hM (fun y => (g y) ^ 2)]
    have h := cfc_mul g g M (hg.continuousOn) (hg.continuousOn)
    rw [← h]
    congr 1
    funext y
    ring
  rw [hmul]

/-- **Sum of squared eigenvalues = Hilbert–Schmidt norm squared** for a Hermitian matrix. -/
lemma eigenvalues_sq_sum_eq_hsNorm {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n ℂ) (hM : M.IsHermitian) :
    (∑ i, (hM.eigenvalues i) ^ 2) = hsNorm M := by
  rw [hsNorm_eq_trace_mul_re_of_isHermitian M hM]
  have hid : cfc (fun x : ℝ => x) M = M := cfc_id' ℝ M
  have hmul : hM.cfc (fun x => x * x) = M * M := by
    rw [← Matrix.IsHermitian.cfc_eq hM (fun x => x * x)]
    have h := cfc_mul (fun x : ℝ => x) (fun x : ℝ => x) M
      (continuous_id.continuousOn) (continuous_id.continuousOn)
    rw [h, hid]
  rw [← hmul, trace_cfc_eq_sum_eigenvalues_general M hM, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.ofReal_re]
  ring

/-- **Eigenvalue bound.**  Every eigenvalue of a Hermitian matrix is bounded by the square
root of its Hilbert–Schmidt norm squared.  This is the spectrum bound used to build the
common compact approximation interval in the cfc trace-derivative proof. -/
lemma eigenvalues_abs_le_sqrt_hsNorm {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n ℂ) (hM : M.IsHermitian) (i : n) :
    |hM.eigenvalues i| ≤ Real.sqrt (hsNorm M) := by
  rw [← eigenvalues_sq_sum_eq_hsNorm M hM]
  exact Real.abs_le_sqrt (Finset.single_le_sum (fun j _ => sq_nonneg _) (Finset.mem_univ i))

end

end GUEStrongConvergence
