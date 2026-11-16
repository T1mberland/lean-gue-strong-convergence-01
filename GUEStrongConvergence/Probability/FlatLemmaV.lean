/-
# Lemma V for the flattened polynomial linearization pencil

`StrongConvergence/FlattenPencil.lean` reduces Lemma S for the linearization pencils to six
analytic inputs for the *flattened* statistic `flatStat r k F z N f`, of which `hV` (the
variance bound controlled by the cfc trace derivative statistic) is the main analytic one
besides Lemma M.

This file proves `hV` for the flattened polynomial pencil.

## The two structural facts

Although the linearization pencil `ℒ_z = penLCS …` is built from the geometric inverse
`linQinvMat`, the *pencil* `penL` itself only uses `linQMat = 1 - shiftMatrix x` — the
explicit inverse `linQinvMat` never enters the definition.  Since `shiftMatrix` is linear in
the generator family, the whole pencil is **affine** in the tuple of GUE blocks:

`penLCS (x + s • y) wds coeff C z = penLCS x wds coeff C z + s • (penLCS y wds coeff C z - penLCS 0 wds coeff C z)`

(`penLCS_add_smul`).  Consequently the coordinate path
`u ↦ flat ℒ_z(x with the (N+1)-st block coordinate p set to u)` is an **affine** matrix path,
so the classical cfc trace-derivative argument of `Probability/CfcTraceDerivative.lean` applies
verbatim, with the explicit direction matrix `h1PencilApproxFlatDir`.

## Main results

* `hasDerivAt_normTrace_cfc_smul` — the affine cfc trace derivative for the normalized trace
  `normTrace`: `d/du normTrace(f(H + u • D))|_{t₀} = normTrace(f'(H + t₀ • D) · D)`, for
  `f : ℝ → ℝ` of class `C¹` and arbitrary Hermitian `H, D`;
* `penL_add_smul`, `penLCS_add_smul`, `flatten_affine_apply` — the pencil is affine in the
  generator tuple;
* `blockGUEBlk_update_eq` — the block GUE tuple is affine in each Gaussian coordinate;
* `flatPencilBlk_update`, `flatStepDir`, `flatStepDir_isHermitian` — the flattened pencil
  along a coordinate is the affine path with constant Hermitian slope `∂_p ℒ_z`;
* **`hasDerivAt_flatStatBlk_update`** — the cfc trace derivative of the flattened statistic:
  `d/du tau_N(f(fl ℒ_z(x with p := u)))|_{t₀} = tau_N(f'(fl ℒ_z) · ∂_p fl ℒ_z)`;
* `flatStat_eq_blk` — `flatStat` is the block statistic composed with the `(N+1)`-st
  coordinate;
* `hsNorm_cfc_deriv_eq` — `‖f'(fl ℒ_z)‖_F² = pencilFlatDim · tau_N((f')²(fl ℒ_z))`;
* `variance_flatStatBlk_le`, `variance_flatStatBlk_le_of_contraction`,
  `variance_flatStat_le_of_contraction` — Gaussian Poincaré and the variance reduction, on the
  block and on the common Gaussian space;
* `pencilVDim`, `pencilFlatDim_eq` — the `N`-independent dimension constant
  `card (PenIdx wds) · d`, with `pencilFlatDim = pencilVDim · (N+1)`;
* **`flatLemmaV`** — Lemma V (`hV`) for the flattened pencil: from the direction contraction
  `∑_p (∂_p tau_N(f(fl ℒ_z)))² ≤ 2 gueScale(N+1)² G / m² ‖f'(fl ℒ_z)‖_F²`,
  `Var(tau_N(f(fl ℒ_z))) ≤ (2G / (card(PenIdx)·d)) / N² · E[tau_N((f')²(fl ℒ_z))]`;
* `flatLemmaV_hV` — the same in the `∀ᶠ N` form.

## The single remaining deterministic input

`flatLemmaV` isolates **one** estimate (its `hcontr` hypothesis): the sharp direction
contraction of the flattened pencil.  In the affine case this is
`sum_sq_trace_direction_le` (`Probability/LemmaVSharp.lean`): the GUE coordinate directions
`gueDirMatrix A p` give `∑_p ‖Tr(D_p X)‖² ≤ 2 gueScale² (∑_i frob(A_i)²) ‖X‖_F²`.  Here the
directions are `∂_p ℒ_z = gueScale·(α·L_i(E_ab) + β·L_i(E_ba))`, where `L_i(E)` is the linear
map "insert the block `E` into the block-diagonal slots of the words with letter `i`"; the
analogous sharp constant is the corresponding insertion count (the total word length of the
dense-family polynomial).  Proving this estimate needs the entry structure of the shift block
`Q = blockDiagonal'(1 - shiftMatrix x)` of `penL`; it is *not* assumed anywhere else in this
file.

Note the `N = 0` instance of the `hV` field of `PencilLemmaSData`: at `N = 0` the statistic
still reads the nondegenerate Gaussian block `x 1`, while the right-hand side `C/(0:ℝ)² · …`
vanishes, so the `∀ N` form is unsatisfiable; `flatLemmaV` and `flatLemmaV_hV` therefore
require `0 < N` / use the `∀ᶠ N` form.

No `sorry`, no new axioms.
-/
import GUEStrongConvergence.StrongConvergence.FlattenPencil
import GUEStrongConvergence.Probability.CfcTraceDerivative
import Mathlib.Analysis.Calculus.UniformLimitsDeriv

open MeasureTheory ProbabilityTheory Filter Matrix FreeProbability FreeProbability.Fock
open scoped RealInnerProductSpace ENNReal NNReal Topology Polynomial BigOperators ComplexOrder

namespace GUEStrongConvergence

noncomputable section

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false

/-! ## 1. The affine cfc trace derivative for the normalized trace -/

section NormTraceDeriv

/-- The normalization constant of the normalized trace at size `m` is at most `1`. -/
lemma inv_card_fin_mul_card_le_one (m : ℕ) :
    (m : ℝ)⁻¹ * (Fintype.card (Fin m) : ℝ) ≤ 1 := by
  rw [Fintype.card_fin]
  rcases Nat.eq_zero_or_pos m with h | h
  · subst h
    simp
  · have hpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast h
    rw [inv_mul_cancel₀ hpos.ne']

/-- The normalization constant of the normalized trace against the square root of the
dimension is at most `1`. -/
lemma inv_card_fin_mul_sqrt_card_le_one (m : ℕ) :
    (m : ℝ)⁻¹ * Real.sqrt (Fintype.card (Fin m) : ℝ) ≤ 1 := by
  rw [Fintype.card_fin]
  rcases Nat.eq_zero_or_pos m with h | h
  · subst h
    simp
  · have hpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast h
    have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast h
    have hsqrt : Real.sqrt (m : ℝ) ≤ (m : ℝ) := by
      rw [Real.sqrt_le_iff]
      refine ⟨by linarith, ?_⟩
      nlinarith [mul_nonneg (show (0 : ℝ) ≤ (m : ℝ) by linarith)
        (show (0 : ℝ) ≤ (m : ℝ) - 1 by linarith)]
    calc (m : ℝ)⁻¹ * Real.sqrt (m : ℝ) ≤ (m : ℝ)⁻¹ * (m : ℝ) :=
          mul_le_mul_of_nonneg_left hsqrt (by positivity)
      _ = 1 := inv_mul_cancel₀ hpos.ne'

/-- **The affine cfc trace derivative for the normalized trace.**

For `f : ℝ → ℝ` of class `C¹`, Hermitian matrices `H, D` and every real `t₀`,

`d/du normTrace(f(H + u • D))|_{u = t₀} = normTrace(f'(H + t₀ • D) · D)`.

The proof is the polynomial `C⁰`/`C¹`-approximation argument of
`Probability/CfcTraceDerivative.lean`: on the compact spectral interval of the affine family,
approximate `f` and `f'` simultaneously by polynomials, differentiate the polynomial statistics
exactly (`hasDerivAt_trace_polyMatrix`, which uses only cyclicity of the trace), and pass to
the limit by uniform convergence (`hasDerivAt_of_tendstoUniformlyOn`). -/
theorem hasDerivAt_normTrace_cfc_smul {m : ℕ} (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f)
    (H D : Matrix (Fin m) (Fin m) ℂ) (hH : H.IsHermitian) (hD : D.IsHermitian) (t₀ : ℝ) :
    HasDerivAt (fun u : ℝ => normTrace (cfc f (H + u • D)))
      (normTrace (cfc (deriv f) (H + t₀ • D) * D)) t₀ := by
  classical
  -- the Hermitian affine family
  have hHu : ∀ u : ℝ, (H + u • D).IsHermitian := by
    intro u
    exact hH.add (hD.smul (k := u) (by simp [IsSelfAdjoint]))
  -- the common compact spectral bound
  set c : ℝ := |t₀| + 1 with hcdef
  set R2 : ℝ := 2 * hsNorm H + 2 * c ^ 2 * hsNorm D with hR2def
  have hR2 : 0 ≤ R2 := by
    rw [hR2def]
    nlinarith [hsNorm_nonneg H, hsNorm_nonneg D, sq_nonneg c]
  set R : ℝ := Real.sqrt R2 + 1 with hRdef
  have hRpos : 0 < R := by rw [hRdef]; positivity
  have hRneg : -R < 0 := by linarith
  have hspec : ∀ u : ℝ, |u - t₀| < 1 → ∀ i : Fin m, |(hHu u).eigenvalues i| ≤ R := by
    intro u hu i
    have hs : |u| ≤ c := by
      rw [hcdef]
      calc |u| = |(u - t₀) + t₀| := by ring_nf
        _ ≤ |u - t₀| + |t₀| := abs_add_le _ _
        _ ≤ 1 + |t₀| := by linarith
        _ = |t₀| + 1 := by ring
    have hb : hsNorm (H + u • D) ≤ R2 := by
      rw [hR2def]
      have h1 := hsNorm_add_smul_le H D u
      have h2 : u ^ 2 ≤ c ^ 2 := by
        simpa [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hs 2
      nlinarith [hsNorm_nonneg H, hsNorm_nonneg D]
    have h2 : Real.sqrt (hsNorm (H + u • D)) ≤ Real.sqrt R2 := Real.sqrt_le_sqrt hb
    have h3 : Real.sqrt R2 < R := by
      rw [hRdef]; linarith [Real.sqrt_nonneg R2]
    exact (eigenvalues_abs_le_sqrt_hsNorm (H + u • D) (hHu u) i).trans (h2.trans h3.le)
  -- the approximation accuracy
  set eps : ℕ → ℝ := fun n => (1 : ℝ) / ((n : ℝ) + 1) / (1 + Real.sqrt (hsNorm D))
    with hepsdef
  have heps_pos : ∀ n : ℕ, 0 < eps n := by
    intro n
    rw [hepsdef]
    positivity
  have heps_tend : Tendsto eps atTop (𝓝 0) := by
    rw [hepsdef]
    have h : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    simpa using h.div_const (1 + Real.sqrt (hsNorm D))
  -- the polynomial approximants
  have happrox : ∀ n : ℕ, ∃ q : ℝ[X],
      (∀ y ∈ Set.Icc (-R) R, |q.eval y - f y| < eps n) ∧
        (∀ y ∈ Set.Icc (-R) R, |q.derivative.eval y - deriv f y| < eps n) :=
    fun n => exists_polynomial_c1_approx f hf hRneg hRpos (ε := eps n) (heps_pos n)
  choose q hq using happrox
  -- the value bound
  have hFbound : ∀ (n : ℕ) (u : ℝ), u ∈ Metric.ball t₀ 1 →
      |normTrace (polyMatrix (q n) (H + u • D)) - normTrace (cfc f (H + u • D))| ≤ eps n := by
    intro n u hu
    have hu' : |u - t₀| < 1 := by
      simpa [Real.dist_eq] using Metric.mem_ball.mp hu
    have hspecu := hspec u hu'
    have hM := hHu u
    have hbnd : ‖(cfc (fun y : ℝ => (q n).eval y - f y) (H + u • D)).trace‖
        ≤ (Fintype.card (Fin m) : ℝ) * eps n := by
      refine abs_trace_cfc_le (M := H + u • D) (hM := hM)
        (g := fun y : ℝ => (q n).eval y - f y) (R := R) (C := eps n) ?_ ?_
      · intro i; exact hspecu i
      · intro y hy
        exact le_of_lt ((hq n).1 y (Set.mem_Icc.mpr (abs_le.mp hy)))
    have hdiff : polyMatrix (q n) (H + u • D) - cfc f (H + u • D)
        = cfc (fun y : ℝ => (q n).eval y - f y) (H + u • D) := by
      rw [← cfc_polyMatrix_eq (q n) _ hM,
        ← cfc_sub_of_hermitian (fun y : ℝ => (q n).eval y) f (Polynomial.continuous (q n))
          hf.continuous _ hM]
    have hsub : normTrace (polyMatrix (q n) (H + u • D)) - normTrace (cfc f (H + u • D))
        = (m : ℝ)⁻¹
          * ((cfc (fun y : ℝ => (q n).eval y - f y) (H + u • D)).trace).re := by
      rw [normTrace, normTrace, ← hdiff, Matrix.trace_sub, Complex.sub_re]
      ring
    have hcoef : 0 ≤ (m : ℝ)⁻¹ := by positivity
    rw [hsub, abs_mul]
    calc |(m : ℝ)⁻¹| * |((cfc (fun y : ℝ => (q n).eval y - f y) (H + u • D)).trace).re|
        = (m : ℝ)⁻¹ * |((cfc (fun y : ℝ => (q n).eval y - f y) (H + u • D)).trace).re| := by
          rw [abs_of_nonneg hcoef]
      _ ≤ (m : ℝ)⁻¹ * ‖(cfc (fun y : ℝ => (q n).eval y - f y) (H + u • D)).trace‖ :=
          mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm _) hcoef
      _ ≤ (m : ℝ)⁻¹ * ((Fintype.card (Fin m) : ℝ) * eps n) :=
          mul_le_mul_of_nonneg_left hbnd hcoef
      _ = ((m : ℝ)⁻¹ * (Fintype.card (Fin m) : ℝ)) * eps n := by ring
      _ ≤ 1 * eps n :=
          mul_le_mul_of_nonneg_right (inv_card_fin_mul_card_le_one m) (le_of_lt (heps_pos n))
      _ = eps n := one_mul _
  -- the derivative bound
  have hGbound : ∀ (n : ℕ) (u : ℝ), u ∈ Metric.ball t₀ 1 →
      |normTrace (polyMatrix (q n).derivative (H + u • D) * D)
        - normTrace (cfc (deriv f) (H + u • D) * D)| ≤ eps n * Real.sqrt (hsNorm D) := by
    intro n u hu
    have hu' : |u - t₀| < 1 := by
      simpa [Real.dist_eq] using Metric.mem_ball.mp hu
    have hspecu := hspec u hu'
    have hM := hHu u
    have hcont : Continuous (fun y : ℝ => (q n).derivative.eval y - deriv f y) :=
      (Polynomial.continuous (q n).derivative).sub hf.continuous_deriv_one
    have hbnd : hsNorm (cfc (fun y : ℝ => (q n).derivative.eval y - deriv f y)
          (H + u • D))
        ≤ (Fintype.card (Fin m) : ℝ) * (eps n) ^ 2 := by
      refine hsNorm_cfc_le (M := H + u • D) (hM := hM)
        (g := fun y : ℝ => (q n).derivative.eval y - deriv f y) (hg := hcont)
        (R := R) (C := eps n) ?_ ?_ (le_of_lt (heps_pos n))
      · intro i; exact hspecu i
      · intro y hy
        exact le_of_lt ((hq n).2 y (Set.mem_Icc.mpr (abs_le.mp hy)))
    have hdiff : polyMatrix (q n).derivative (H + u • D) * D
        - cfc (deriv f) (H + u • D) * D
        = cfc (fun y : ℝ => (q n).derivative.eval y - deriv f y) (H + u • D) * D := by
      rw [← cfc_polyMatrix_eq (q n).derivative _ hM, ← sub_mul,
        ← cfc_sub_of_hermitian (fun y : ℝ => (q n).derivative.eval y) (deriv f)
          (Polynomial.continuous (q n).derivative) hf.continuous_deriv_one _ hM]
    have hsub : normTrace (polyMatrix (q n).derivative (H + u • D) * D)
        - normTrace (cfc (deriv f) (H + u • D) * D)
        = (m : ℝ)⁻¹
          * ((cfc (fun y : ℝ => (q n).derivative.eval y - deriv f y) (H + u • D) * D).trace).re := by
      rw [normTrace, normTrace, ← hdiff, Matrix.trace_sub, Complex.sub_re]
      ring
    have hcoef : 0 ≤ (m : ℝ)⁻¹ := by positivity
    have hK : 0 ≤ Real.sqrt (hsNorm D) := Real.sqrt_nonneg _
    rw [hsub, abs_mul]
    calc |(m : ℝ)⁻¹| * |((cfc (fun y : ℝ => (q n).derivative.eval y - deriv f y)
            (H + u • D) * D).trace).re|
        = (m : ℝ)⁻¹ * |((cfc (fun y : ℝ => (q n).derivative.eval y - deriv f y)
            (H + u • D) * D).trace).re| := by rw [abs_of_nonneg hcoef]
      _ ≤ (m : ℝ)⁻¹ * ‖(cfc (fun y : ℝ => (q n).derivative.eval y - deriv f y)
            (H + u • D) * D).trace‖ :=
          mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm _) hcoef
      _ ≤ (m : ℝ)⁻¹
            * (Real.sqrt (hsNorm (cfc (fun y : ℝ => (q n).derivative.eval y - deriv f y)
                (H + u • D))) * Real.sqrt (hsNorm D)) := by
          refine mul_le_mul_of_nonneg_left ?_ hcoef
          exact norm_trace_mul_le_sqrt_hsNorm _ _
      _ ≤ (m : ℝ)⁻¹
            * (Real.sqrt ((Fintype.card (Fin m) : ℝ) * (eps n) ^ 2)
              * Real.sqrt (hsNorm D)) := by
          refine mul_le_mul_of_nonneg_left ?_ hcoef
          exact mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hbnd) hK
      _ = ((m : ℝ)⁻¹ * Real.sqrt (Fintype.card (Fin m) : ℝ))
            * (eps n * Real.sqrt (hsNorm D)) := by
          rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (le_of_lt (heps_pos n))]
          ring
      _ ≤ 1 * (eps n * Real.sqrt (hsNorm D)) :=
          mul_le_mul_of_nonneg_right (inv_card_fin_mul_sqrt_card_le_one m)
            (mul_nonneg (le_of_lt (heps_pos n)) hK)
      _ = eps n * Real.sqrt (hsNorm D) := one_mul _
  -- uniform convergence of the values and of the derivatives
  have hU1 : TendstoUniformlyOn
      (fun n : ℕ => fun u : ℝ => normTrace (polyMatrix (q n) (H + u • D)))
      (fun u : ℝ => normTrace (cfc f (H + u • D))) atTop (Metric.ball t₀ 1) :=
    tendstoUniformlyOn_of_abs_sub_le heps_tend hFbound
  have hU2 : TendstoUniformlyOn
      (fun n : ℕ => fun u : ℝ => normTrace (polyMatrix (q n).derivative (H + u • D) * D))
      (fun u : ℝ => normTrace (cfc (deriv f) (H + u • D) * D))
      atTop (Metric.ball t₀ 1) := by
    refine tendstoUniformlyOn_of_abs_sub_le ?_ hGbound
    have h := heps_tend.mul_const (Real.sqrt (hsNorm D))
    simpa using h
  -- the polynomial approximants are differentiable with the announced derivative
  have hd : ∀ᶠ n : ℕ in atTop, ∀ u : ℝ, u ∈ Metric.ball t₀ 1 →
      HasDerivAt (fun u : ℝ => normTrace (polyMatrix (q n) (H + u • D)))
        (normTrace (polyMatrix (q n).derivative (H + u • D) * D)) u := by
    refine Eventually.of_forall fun n => ?_
    intro u _
    have h' : HasDerivAt (fun s : ℝ => (m : ℝ)⁻¹ * (polyMatrix (q n) (H + s • D)).trace.re)
        ((m : ℝ)⁻¹ * (polyMatrix (q n).derivative (H + u • D) * D).trace.re) u := by
      have hre : HasDerivAt (fun s : ℝ => (polyMatrix (q n) (H + s • D)).trace.re)
          ((polyMatrix (q n).derivative (H + u • D) * D).trace.re) u :=
        hasDerivAt_re_of_complex (hasDerivAt_trace_polyMatrix (q n) H D u)
      simpa only [mul_comm] using hre.const_mul ((m : ℝ)⁻¹)
    simpa only [normTrace] using h'
  -- pointwise convergence of the values
  have hconv : ∀ u : ℝ, u ∈ Metric.ball t₀ 1 →
      Tendsto (fun n : ℕ => normTrace (polyMatrix (q n) (H + u • D)))
        atTop (𝓝 (normTrace (cfc f (H + u • D)))) := by
    intro u hu
    have hb : ∀ n : ℕ, |normTrace (polyMatrix (q n) (H + u • D))
        - normTrace (cfc f (H + u • D))| ≤ eps n := fun n => hFbound n u hu
    have hlim : Tendsto (fun n : ℕ =>
        |normTrace (polyMatrix (q n) (H + u • D))
          - normTrace (cfc f (H + u • D))|) atTop (𝓝 0) :=
      squeeze_zero (fun n => abs_nonneg _) hb heps_tend
    rw [tendsto_iff_norm_sub_tendsto_zero]
    simpa [Real.norm_eq_abs] using hlim
  exact hasDerivAt_of_tendstoUniformlyOn Metric.isOpen_ball hU2 hd hconv
    (Metric.mem_ball_self zero_lt_one)

end NormTraceDeriv

/-! ## 2. The pencil is affine in the generator tuple

The linearization pencil `penL x wds coeff A0` is built from the block row `linU`, the block
column `linV` and the shift block `penB x wds = !![0, Qᴴ; Q, 0]` with `Q = linQMat x wds`;
the explicit inverse `linQinvMat` is only used in the *proofs* of the Schur-complement
statement, never in the definition of the pencil.  Since `Q` is affine in the generator family
(`shiftMatrix` is linear), the pencil is affine in the tuple of GUE blocks. -/

section PencilAffine

variable {M : Type*} [Ring M] [StarRing M] [Module ℝ M] [StarModule ℝ M]
  {I κ : Type*} [Fintype κ] [DecidableEq κ]

/-- Subtraction of block matrices, entrywise on the four blocks. -/
lemma fromBlocks_sub_apply {n o l m : Type*} {α : Type*} [AddGroup α]
    (A A' : Matrix n l α) (B B' : Matrix n m α) (C C' : Matrix o l α)
    (D D' : Matrix o m α) :
    fromBlocks A B C D - fromBlocks A' B' C' D'
      = fromBlocks (A - A') (B - B') (C - C') (D - D') := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    · simp only [Matrix.sub_apply, fromBlocks]
      rfl

lemma shiftMatrix_zero_apply (w : List I) :
    shiftMatrix (0 : I → M) w = 0 := by
  ext i j
  rw [shiftMatrix_apply]
  split <;> simp

/-- `shiftMatrix` is additive and real-homogeneous in the generator family. -/
lemma shiftMatrix_add_smul (x y : I → M) (s : ℝ) (w : List I) :
    shiftMatrix (x + s • y) w = shiftMatrix x w + s • shiftMatrix y w := by
  ext i j
  simp only [shiftMatrix_apply, Matrix.add_apply, Matrix.smul_apply, Pi.add_apply,
    Pi.smul_apply]
  split <;> simp

/-- `linQMat x = 1 - shiftMatrix x` is affine in the generator family. -/
lemma linQMat_add_smul (x y : I → M) (s : ℝ) (wds : κ → List I) :
    linQMat (x + s • y) wds = linQMat x wds + s • (linQMat y wds - linQMat 0 wds) := by
  have hpt : linQ (x + s • y) wds = linQ x wds + s • (linQ y wds - linQ 0 wds) := by
    funext k
    simp only [linQ, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, shiftMatrix_add_smul,
      shiftMatrix_zero_apply, sub_zero, smul_sub]
    abel
  simp only [linQMat]
  rw [hpt, blockDiagonal'_add, ← blockDiagonal'_sub, ← blockDiagonal'_smul]

/-- The shift block `penB x = !![0, Qᴴ; Q, 0]` is affine in the generator family. -/
lemma penB_add_smul (x y : I → M) (s : ℝ) (wds : κ → List I) :
    penB (x + s • y) wds = penB x wds + s • (penB y wds - penB 0 wds) := by
  simp only [penB, linQMat_add_smul, Matrix.conjTranspose_add, Matrix.conjTranspose_sub,
    Matrix.conjTranspose_smul, star_trivial]
  rw [fromBlocks_sub_apply, fromBlocks_smul, fromBlocks_add]
  simp

/-- For fixed corner blocks, `fromBlocks` is affine in its lower-right block. -/
lemma fromBlocks_affine (A0 : Matrix (Fin 1) (Fin 1) M) {J : Type*}
    (E : Matrix (Fin 1) J M) (E' : Matrix J (Fin 1) M) (P Q R : Matrix J J M) (s : ℝ) :
    fromBlocks A0 E E' (P + s • (Q - R))
      = fromBlocks A0 E E' P + s • (fromBlocks A0 E E' Q - fromBlocks A0 E E' R) := by
  rw [fromBlocks_sub_apply, fromBlocks_smul, fromBlocks_add]
  simp

/-- The block column `linV` does not depend on the generator family. -/
lemma linV_apply_eq (x : I → M) (wds : κ → List I) : linV x wds = linV 0 wds := rfl

/-- The block row `penE` does not depend on the generator family. -/
lemma penE_apply_eq (x : I → M) (wds : κ → List I) (coeff : κ → M) :
    penE x wds coeff = penE 0 wds coeff := by
  simp only [penE, linV_apply_eq]

/-- The block column `penEconj` does not depend on the generator family. -/
lemma penEconj_apply_eq (x : I → M) (wds : κ → List I) (coeff : κ → M) :
    penEconj x wds coeff = penEconj 0 wds coeff := by
  simp only [penEconj, linV_apply_eq]

/-- **The assembled pencil is affine in the generator family.** -/
lemma penL_add_smul (x y : I → M) (s : ℝ) (wds : κ → List I) (coeff : κ → M)
    (A0 : Matrix (Fin 1) (Fin 1) M) :
    penL (x + s • y) wds coeff A0
      = penL x wds coeff A0 + s • (penL y wds coeff A0 - penL 0 wds coeff A0) := by
  simp only [penL, penB_add_smul, penE_apply_eq, penEconj_apply_eq, fromBlocks_affine]

end PencilAffine

section PencilCS

variable {B : Type*} [CStarAlgebra B] [Nontrivial B] [PartialOrder B] [StarOrderedRing B]
  {I κ : Type*} [Fintype κ] [DecidableEq κ]

/-- **The linearization pencil `ℒ_z` is affine in the generator family.** -/
theorem penLCS_add_smul (x y : I → B) (s : ℝ) (wds : κ → List I) (coeff : κ → B)
    (C : B) (z : ℝ) :
    penLCS (x + s • y) wds coeff C z
      = penLCS x wds coeff C z + s • (penLCS y wds coeff C z - penLCS 0 wds coeff C z) := by
  simp only [penLCS]
  rw [penL_add_smul]
  simp only [CStarMatrix.of_add_of, CStarMatrix.of_sub_of, CStarMatrix.smul_of]

end PencilCS

/-! ### The generator dependence of the pencil

The first structural step towards the direction contraction of §5: the pencil depends on the
generator tuple only through the shift block `penB = !![0, Qᴴ; Q, 0]`, and `Q = 1 - shiftMatrix x`. -/

section PencilStructure

variable {M : Type*} [Ring M] [StarRing M] [Module ℝ M] [StarModule ℝ M]
  {I κ : Type*} [Fintype κ] [DecidableEq κ]

/-- The pencil's dependence on the generator tuple is confined to its lower-right `B`-block. -/
lemma penL_sub_penL_zero (x : I → M) (wds : κ → List I) (coeff : κ → M)
    (A0 : Matrix (Fin 1) (Fin 1) M) :
    penL x wds coeff A0 - penL 0 wds coeff A0
      = fromBlocks 0 0 0 (penB x wds - penB 0 wds) := by
  have hsub := fromBlocks_sub_apply (α := M) A0 A0 (penE x wds coeff) (penE 0 wds coeff)
    (penEconj x wds coeff) (penEconj 0 wds coeff) (penB x wds) (penB 0 wds)
  rw [penL, penL, hsub, penE_apply_eq, penEconj_apply_eq]
  simp

/-- The shift block's dependence on the generator tuple is confined to its off-diagonal blocks. -/
lemma penB_sub_penB_zero (x : I → M) (wds : κ → List I) :
    penB x wds - penB 0 wds
      = fromBlocks 0 ((linQMat x wds)ᴴ - (linQMat 0 wds)ᴴ)
          (linQMat x wds - linQMat 0 wds) 0 := by
  have hsub := fromBlocks_sub_apply (α := M)
    (0 : Matrix (BlkIdx wds) (BlkIdx wds) M) (0 : Matrix (BlkIdx wds) (BlkIdx wds) M)
    ((linQMat x wds)ᴴ) ((linQMat 0 wds)ᴴ) (linQMat x wds) (linQMat 0 wds)
    (0 : Matrix (BlkIdx wds) (BlkIdx wds) M) (0 : Matrix (BlkIdx wds) (BlkIdx wds) M)
  rw [penB, penB, hsub]
  simp

end PencilStructure

/-! ## 3. The flattened pencil along a Gaussian coordinate

To avoid the (nested) C⋆-algebra instances of the block algebra `BlockAlg`, the flattened
pencil is re-expressed through the *generic* assembly `penL`
(`Linearization/SelfAdjointPencil.lean`), which only needs `Ring` and `StarRing`.  The
result `penLFlat` is definitionally the flattening of `h1PencilApprox`, but all algebraic
manipulations are carried out at the generic level. -/

section FlatStructure

variable {r : ℕ}

local instance : Nontrivial (closedSemicircularAlgebra (Fin r)) :=
  (closedGeneratedVacuumState (Fin r)).toProbabilitySpace.nontrivial

local instance : PartialOrder (closedSemicircularAlgebra (Fin r)) :=
  CStarAlgebra.spectralOrder _

local instance : StarOrderedRing (closedSemicircularAlgebra (Fin r)) :=
  CStarAlgebra.spectralOrderedRing _

/-- The word coefficients of the canonical dilated polynomial, at block size `N`. -/
def h1Coeff (r k : ℕ) (F : RatPolyIdx r (k + 1)) (N : ℕ) :
    polyIdx (h1Poly r k F) → BlockAlg ((k + 1) + (k + 1)) N :=
  fun j => (1 / 2 : ℂ) • polyCoeff
    (A := CStarMatrix (Fin (N + 1)) (Fin (N + 1)) ℂ) (h1Poly r k F) j

/-- The flattened linearization pencil of a general generator tuple, obtained from the
generic assembly `penL` and the flattening equivalence. -/
def penLFlat (r k : ℕ) (F : RatPolyIdx r (k + 1)) (N : ℕ) (z : ℝ)
    (X : Fin r → BlockAlg ((k + 1) + (k + 1)) N) :
    Matrix (Fin (pencilFlatDim r k F N)) (Fin (pencilFlatDim r k F N)) ℂ :=
  flattenPencilStarAlgEquiv r k F N
    (penL X (polyW (h1Poly r k F)) (h1Coeff r k F N)
      (penA0 (0 : BlockAlg ((k + 1) + (k + 1)) N) z))

/-- The flattening of the pencil algebra is affine in its argument. -/
lemma flatten_affine_apply (r k : ℕ) (F : RatPolyIdx r (k + 1)) (N : ℕ)
    (A B C : h1An r k F N) (s : ℝ) :
    flattenPencilStarAlgEquiv r k F N (A + s • (B - C))
      = flattenPencilStarAlgEquiv r k F N A
        + s • (flattenPencilStarAlgEquiv r k F N B - flattenPencilStarAlgEquiv r k F N C) := by
  rw [map_add, map_smul, map_sub]

/-- The pencil assembled from `penL` is self-adjoint. -/
lemma penL_isSelfAdjoint (k : ℕ) (F : RatPolyIdx r (k + 1)) (N : ℕ) (z : ℝ)
    (X : Fin r → BlockAlg ((k + 1) + (k + 1)) N) :
    IsSelfAdjoint (penL X (polyW (h1Poly r k F)) (h1Coeff r k F N)
      (penA0 (0 : BlockAlg ((k + 1) + (k + 1)) N) z)) := by
  have h : (penL X (polyW (h1Poly r k F)) (h1Coeff r k F N)
      (penA0 (0 : BlockAlg ((k + 1) + (k + 1)) N) z))ᴴ
      = penL X (polyW (h1Poly r k F)) (h1Coeff r k F N)
        (penA0 (0 : BlockAlg ((k + 1) + (k + 1)) N) z) := by
    rw [penL_conjTranspose, penA0_conjTranspose (IsSelfAdjoint.zero _) z]
  exact h

/-- The flattened pencil of any generator tuple is Hermitian. -/
lemma penLFlat_isHermitian (k : ℕ) (F : RatPolyIdx r (k + 1)) (N : ℕ) (z : ℝ)
    (X : Fin r → BlockAlg ((k + 1) + (k + 1)) N) :
    (penLFlat r k F N z X).IsHermitian :=
  (penL_isSelfAdjoint k F N z X).map (flattenPencilStarAlgEquiv r k F N)

/-- **The flattened pencil is affine in the generator tuple.** -/
theorem penLFlat_add_smul (k : ℕ) (F : RatPolyIdx r (k + 1)) (N : ℕ) (z : ℝ)
    (X Y : Fin r → BlockAlg ((k + 1) + (k + 1)) N) (s : ℝ) :
    penLFlat r k F N z (X + s • Y)
      = penLFlat r k F N z X + s • (penLFlat r k F N z Y - penLFlat r k F N z 0) := by
  have h := penL_add_smul X Y s (polyW (h1Poly r k F)) (h1Coeff r k F N)
    (penA0 (0 : BlockAlg ((k + 1) + (k + 1)) N) z)
  simp only [penLFlat]
  rw [h]
  exact flatten_affine_apply r k F N _ _ _ s

/-- The block-diagonal embedding is additive. -/
lemma blockDiagEmb_add {A : Type*} [AddZeroClass A] {d : ℕ} (a b : A) :
    blockDiag (d := d) (a + b) = blockDiag (d := d) a + blockDiag (d := d) b := by
  ext i j
  show (if i = j then a + b else 0)
      = (if i = j then a else 0) + (if i = j then b else 0)
  by_cases h : i = j <;> simp [h]

/-- The block-diagonal embedding commutes with scalar multiplication. -/
lemma blockDiagEmb_smul {A : Type*} [AddMonoid A] {d : ℕ} {R : Type*} [SMulZeroClass R A]
    (s : R) (a : A) :
    blockDiag (d := d) (s • a) = s • blockDiag (d := d) a := by
  ext i j
  show (if i = j then s • a else 0) = s • (if i = j then a else 0)
  by_cases h : i = j <;> simp [h]

/-- The block GUE generator tuple, as a function of the `(N+1)`-st Gaussian block. -/
def blockGUEBlk (r d N : ℕ) (y : EuclideanSpace ℝ (GUECoord (Fin r) (N + 1))) :
    Fin r → BlockAlg d N :=
  fun i => blockDiag (A := Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) (gueMatrix y i)

/-- The coordinate direction of the block GUE generator tuple. -/
def blockGUEDir (r d N : ℕ) (p : GUECoord (Fin r) (N + 1)) : Fin r → BlockAlg d N :=
  fun i => blockDiag (A := Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) (gueMatrixDir p i)

/-- The block GUE tuple of the common space depends only on the `(N+1)`-st block. -/
lemma blockGUE_eq_blk (x : CommonSpace (Fin r)) (d N : ℕ) :
    blockGUE r d x N = blockGUEBlk r d N (x (N + 1)) := rfl

/-- **The block GUE tuple is affine in each Gaussian coordinate**, with the explicit
direction `blockGUEDir`. -/
lemma blockGUEBlk_update_eq {d N : ℕ} (y : EuclideanSpace ℝ (GUECoord (Fin r) (N + 1)))
    (p : GUECoord (Fin r) (N + 1)) (u : ℝ) :
    blockGUEBlk r d N (euclidUpdate y p u)
      = blockGUEBlk r d N y + (u - WithLp.ofLp y p) • blockGUEDir r d N p := by
  funext i
  have h := gueMatrix_update_eq (x := WithLp.ofLp y) p u i
  simp only [blockGUEBlk, blockGUEDir, Pi.add_apply, Pi.smul_apply, ofLp_euclidUpdate, h,
    blockDiagEmb_add, blockDiagEmb_smul]
  rfl

/-- The flattened linearization pencil as a function of the `(N+1)`-st Gaussian block. -/
def flatPencilBlk (r k : ℕ) (F : RatPolyIdx r (k + 1)) (N : ℕ) (z : ℝ)
    (y : EuclideanSpace ℝ (GUECoord (Fin r) (N + 1))) :
    Matrix (Fin (pencilFlatDim r k F N)) (Fin (pencilFlatDim r k F N)) ℂ :=
  penLFlat r k F N z (blockGUEBlk r ((k + 1) + (k + 1)) N y)

/-- The block-level flattened pencil is Hermitian. -/
lemma flatPencilBlk_isHermitian (k : ℕ) (F : RatPolyIdx r (k + 1)) (N : ℕ) (z : ℝ)
    (y : EuclideanSpace ℝ (GUECoord (Fin r) (N + 1))) :
    (flatPencilBlk r k F N z y).IsHermitian :=
  penLFlat_isHermitian k F N z _

/-- The affine slope of the flattened pencil in the `p`-th Gaussian coordinate: the
difference of the pencil at the direction tuple and at the zero tuple. -/
def flatStepDir (r k : ℕ) (F : RatPolyIdx r (k + 1)) (N : ℕ) (z : ℝ)
    (p : GUECoord (Fin r) (N + 1)) :
    Matrix (Fin (pencilFlatDim r k F N)) (Fin (pencilFlatDim r k F N)) ℂ :=
  penLFlat r k F N z (blockGUEDir r ((k + 1) + (k + 1)) N p) - penLFlat r k F N z 0

/-- The difference of two Hermitian matrices is Hermitian. -/
lemma isHermitian_sub {n : Type*} [Fintype n] [DecidableEq n] {A B : Matrix n n ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) : (A - B).IsHermitian := by
  have hA' : star A = A := hA
  have hB' : star B = B := hB
  show star (A - B) = A - B
  rw [star_sub, hA', hB']

/-- The affine slope of the flattened pencil is Hermitian. -/
lemma flatStepDir_isHermitian (k : ℕ) (F : RatPolyIdx r (k + 1)) (N : ℕ) (z : ℝ)
    (p : GUECoord (Fin r) (N + 1)) :
    (flatStepDir r k F N z p).IsHermitian :=
  isHermitian_sub (penLFlat_isHermitian k F N z _) (penLFlat_isHermitian k F N z 0)

/-- **The flattened linearization pencil is affine along a Gaussian coordinate**: the
coordinate path is the affine path with slope `flatStepDir`. -/
theorem flatPencilBlk_update (k : ℕ) (F : RatPolyIdx r (k + 1)) (N : ℕ) (z : ℝ)
    (p : GUECoord (Fin r) (N + 1))
    (y : EuclideanSpace ℝ (GUECoord (Fin r) (N + 1))) (u : ℝ) :
    flatPencilBlk r k F N z (euclidUpdate y p u)
      = flatPencilBlk r k F N z y + (u - WithLp.ofLp y p) • flatStepDir r k F N z p := by
  simp only [flatPencilBlk, flatStepDir, blockGUEBlk_update_eq, penLFlat_add_smul]

/-- The flattened statistic as a function of the `(N+1)`-st Gaussian block alone. -/
def flatStatBlk (r k : ℕ) (F : RatPolyIdx r (k + 1)) (z : ℝ) (N : ℕ) (f : ℝ → ℝ)
    (y : EuclideanSpace ℝ (GUECoord (Fin r) (N + 1))) : ℝ :=
  normTrace (hermCfc (flatPencilBlk r k F N z y) f (flatPencilBlk_isHermitian k F N z y))

/-- **The cfc trace derivative of the flattened pencil statistic in block form**: for `f` of
class `C¹`, the block statistic `flatStatBlk` is differentiable along the coordinate `p`,
with derivative `normTrace(f'(flat ∂_p ℒ_z) · ∂_p ℒ_z)`, where `∂_p ℒ_z` is the (constant)
affine slope `flatStepDir`. -/
theorem hasDerivAt_flatStatBlk_update (k : ℕ) (F : RatPolyIdx r (k + 1))
    (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f) (N : ℕ) (z : ℝ)
    (p : GUECoord (Fin r) (N + 1))
    (y : EuclideanSpace ℝ (GUECoord (Fin r) (N + 1))) (t₀ : ℝ) :
    HasDerivAt (fun u : ℝ => flatStatBlk r k F z N f (euclidUpdate y p u))
      (normTrace (cfc (deriv f) (flatPencilBlk r k F N z (euclidUpdate y p t₀))
        * flatStepDir r k F N z p)) t₀ := by
  have hfun : (fun u : ℝ => flatStatBlk r k F z N f (euclidUpdate y p u))
      = fun u : ℝ => normTrace
          (cfc f (flatPencilBlk r k F N z y
            + (u - WithLp.ofLp y p) • flatStepDir r k F N z p)) := by
    funext u
    rw [flatStatBlk, hermCfc, flatPencilBlk_update]
  rw [hfun]
  have hmain := hasDerivAt_normTrace_cfc_smul f hf (flatPencilBlk r k F N z y)
    (flatStepDir r k F N z p) (flatPencilBlk_isHermitian k F N z y)
    (flatStepDir_isHermitian k F N z p) (t₀ - WithLp.ofLp y p)
  have hshift : HasDerivAt (fun u : ℝ => u - WithLp.ofLp y p) (1 : ℝ) t₀ := by
    simpa using (hasDerivAt_id t₀).sub_const (WithLp.ofLp y p)
  have hcomp := hmain.scomp t₀ hshift
  rw [one_smul] at hcomp
  have hL : flatPencilBlk r k F N z y
      + (t₀ - WithLp.ofLp y p) • flatStepDir r k F N z p
      = flatPencilBlk r k F N z (euclidUpdate y p t₀) :=
    (flatPencilBlk_update k F N z p y t₀).symm
  rw [hL] at hcomp
  exact hcomp

/-- `flatStat` at a common-space point is the block statistic at its `(N+1)`-st block. -/
theorem flatStat_eq_blk (k : ℕ) (F : RatPolyIdx r (k + 1)) (x : CommonSpace (Fin r))
    (z : ℝ) (N : ℕ) (f : ℝ → ℝ) :
    flatStat r k F z N f x = flatStatBlk r k F z N f (x (N + 1)) := rfl

/-! ## 4. The sharp variance bound (Lemma V) -/

section VarianceBound

variable {r : ℕ}

local instance : Nontrivial (closedSemicircularAlgebra (Fin r)) :=
  (closedGeneratedVacuumState (Fin r)).toProbabilitySpace.nontrivial

local instance : PartialOrder (closedSemicircularAlgebra (Fin r)) :=
  CStarAlgebra.spectralOrder _

local instance : StarOrderedRing (closedSemicircularAlgebra (Fin r)) :=
  CStarAlgebra.spectralOrderedRing _

/-- The cfc trace derivative statistic `tau_N(f'(flat ℒ_z) · ∂_p flat ℒ_z)` of the flattened
pencil, at the Gaussian block point `y` and the coordinate `p`. -/
def flatDerivStat (r k : ℕ) (F : RatPolyIdx r (k + 1)) (z : ℝ) (N : ℕ) (f : ℝ → ℝ)
    (y : EuclideanSpace ℝ (GUECoord (Fin r) (N + 1))) (p : GUECoord (Fin r) (N + 1)) : ℝ :=
  normTrace (cfc (deriv f) (flatPencilBlk r k F N z y) * flatStepDir r k F N z p)

/-- The `(f')²` statistic of the flattened pencil is the cfc of `(f')²`. -/
lemma flatDerivStat_sq_eq (k : ℕ) (F : RatPolyIdx r (k + 1)) (z : ℝ) (N : ℕ) (f : ℝ → ℝ)
    (y : EuclideanSpace ℝ (GUECoord (Fin r) (N + 1))) (p : GUECoord (Fin r) (N + 1)) :
    flatDerivStat r k F z N f y p
      = normTrace (cfc (deriv f) (flatPencilBlk r k F N z y) * flatStepDir r k F N z p) := rfl

/-- The squared Hilbert–Schmidt norm of `f'(flat ℒ_z)` is the normalized trace of
`(f')²(flat ℒ_z)`: `‖f'(L)‖_F² = m · tau_N((f')²(L))` with `m = pencilFlatDim`. -/
theorem hsNorm_cfc_deriv_eq (k : ℕ) (F : RatPolyIdx r (k + 1)) (N : ℕ) (z : ℝ)
    (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f)
    (y : EuclideanSpace ℝ (GUECoord (Fin r) (N + 1))) :
    hsNorm (cfc (deriv f) (flatPencilBlk r k F N z y))
      = (pencilFlatDim r k F N : ℝ)
        * normTrace (cfc (fun t => (deriv f t) ^ 2) (flatPencilBlk r k F N z y)) := by
  set L := flatPencilBlk r k F N z y with hL
  have hLh : L.IsHermitian := flatPencilBlk_isHermitian k F N z y
  have hg : Continuous (deriv f) := hf.continuous_deriv_one
  have hsq : cfc (fun t => (deriv f t) ^ 2) L = cfc (deriv f) L * cfc (deriv f) L := by
    have hmul := cfc_mul (deriv f) (deriv f) L hg.continuousOn hg.continuousOn
    rw [← hmul]
    congr 1
    funext t
    ring
  have h1 : cfc (deriv f) L = hLh.cfc (deriv f) := Matrix.IsHermitian.cfc_eq hLh (deriv f)
  have h2 : cfc (fun t => (deriv f t) ^ 2) L = hLh.cfc (fun t => (deriv f t) ^ 2) :=
    Matrix.IsHermitian.cfc_eq hLh _
  rw [h1, hsNorm_cfc_eq L hLh (deriv f) hg, h2]
  have hpos : 0 < pencilFlatDim r k F N := by
    haveI : Nonempty (PenIdx (polyW (h1Poly r k F))) := inferInstance
    exact Nat.mul_pos Fintype.card_pos (Nat.mul_pos (by omega) (Nat.succ_pos N))
  have hm : ((pencilFlatDim r k F N : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hpos.ne'
  simp only [normTrace]
  field_simp

/-- **Gaussian Poincaré for the flattened pencil statistic**: the variance is controlled by
the integrated squared cfc trace derivatives along the Gaussian coordinates. -/
theorem variance_flatStatBlk_le (k : ℕ) (F : RatPolyIdx r (k + 1)) (z : ℝ) (N : ℕ)
    (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f)
    (hF : MemLp (flatStatBlk r k F z N f)
      2 (stdGaussian (EuclideanSpace ℝ (GUECoord (Fin r) (N + 1)))))
    (hDmem : ∀ p : GUECoord (Fin r) (N + 1), MemLp (fun y => flatDerivStat r k F z N f y p)
      2 (stdGaussian (EuclideanSpace ℝ (GUECoord (Fin r) (N + 1)))))
    (hpoly : ∀ p : GUECoord (Fin r) (N + 1),
      ∀ᵐ y ∂(stdGaussian (EuclideanSpace ℝ (GUECoord (Fin r) (N + 1)))),
        PolyGrowth (fun u : ℝ => flatStatBlk r k F z N f (euclidUpdate y p u)) ∧
        PolyGrowth (fun u : ℝ => flatDerivStat r k F z N f (euclidUpdate y p u) p)) :
    variance (flatStatBlk r k F z N f)
        (stdGaussian (EuclideanSpace ℝ (GUECoord (Fin r) (N + 1))))
      ≤ ∑ p : GUECoord (Fin r) (N + 1),
          ∫ y, (flatDerivStat r k F z N f y p) ^ 2
            ∂(stdGaussian (EuclideanSpace ℝ (GUECoord (Fin r) (N + 1)))) := by
  refine gaussian_poincare_stdGaussian (F := flatStatBlk r k F z N f)
    (D := fun p y => flatDerivStat r k F z N f y p) hF hDmem ?_ hpoly
  intro p
  filter_upwards with y t
  exact hasDerivAt_flatStatBlk_update k F f hf N z p y t

/-- **Lemma V for the flattened pencil, reduced form.**  Assume the deterministic direction
contraction `∑_p (∂_p τ_N(f(ℒ)))² ≤ C₀ ‖f'(ℒ)‖_F²`.  Then

`Var(τ_N(f(ℒ))) ≤ C₀ / m · E[τ_N((f')²(ℒ))]`,  `m = pencilFlatDim r k F N`.

Since `m = card(PenIdx) · d · (N+1)`, a contraction constant `C₀ = 2 gueScale(N+1)² G` gives
the sharp `2G/(card(PenIdx)·d) · (N+1)⁻²` bound, hence the `1/N²` of Lemma V. -/
theorem variance_flatStatBlk_le_of_contraction (k : ℕ) (F : RatPolyIdx r (k + 1)) (z : ℝ)
    (N : ℕ) (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f) (C₀ : ℝ)
    (hF : MemLp (flatStatBlk r k F z N f)
      2 (stdGaussian (EuclideanSpace ℝ (GUECoord (Fin r) (N + 1)))))
    (hDmem : ∀ p : GUECoord (Fin r) (N + 1), MemLp (fun y => flatDerivStat r k F z N f y p)
      2 (stdGaussian (EuclideanSpace ℝ (GUECoord (Fin r) (N + 1)))))
    (hpoly : ∀ p : GUECoord (Fin r) (N + 1),
      ∀ᵐ y ∂(stdGaussian (EuclideanSpace ℝ (GUECoord (Fin r) (N + 1)))),
        PolyGrowth (fun u : ℝ => flatStatBlk r k F z N f (euclidUpdate y p u)) ∧
        PolyGrowth (fun u : ℝ => flatDerivStat r k F z N f (euclidUpdate y p u) p))
    (hint : Integrable (fun y => hsNorm (cfc (deriv f) (flatPencilBlk r k F N z y)))
      (stdGaussian (EuclideanSpace ℝ (GUECoord (Fin r) (N + 1)))))
    (hcontr : ∀ y : EuclideanSpace ℝ (GUECoord (Fin r) (N + 1)),
      ∑ p : GUECoord (Fin r) (N + 1), (flatDerivStat r k F z N f y p) ^ 2
        ≤ C₀ * hsNorm (cfc (deriv f) (flatPencilBlk r k F N z y))) :
    variance (flatStatBlk r k F z N f)
        (stdGaussian (EuclideanSpace ℝ (GUECoord (Fin r) (N + 1))))
      ≤ C₀ * (pencilFlatDim r k F N : ℝ)
          * ∫ y, flatStatBlk r k F z N (fun t => (deriv f t) ^ 2) y
              ∂(stdGaussian (EuclideanSpace ℝ (GUECoord (Fin r) (N + 1)))) := by
  classical
  set μ := stdGaussian (EuclideanSpace ℝ (GUECoord (Fin r) (N + 1))) with hμ
  set m : ℝ := (pencilFlatDim r k F N : ℝ) with hm
  have hmpos : 0 < m := by
    rw [hm]
    haveI : Nonempty (PenIdx (polyW (h1Poly r k F))) := inferInstance
    have hpos : 0 < pencilFlatDim r k F N :=
      Nat.mul_pos Fintype.card_pos (Nat.mul_pos (by omega) (Nat.succ_pos N))
    exact_mod_cast hpos
  -- exchange the finite sum and the integral
  have hsum_eq : (∑ p : GUECoord (Fin r) (N + 1),
        ∫ y, (flatDerivStat r k F z N f y p) ^ 2 ∂μ)
      = ∫ y, ∑ p : GUECoord (Fin r) (N + 1),
          (flatDerivStat r k F z N f y p) ^ 2 ∂μ := by
    rw [integral_finsetSum]
    intro p _
    exact (hDmem p).integrable_sq
  -- the pointwise contraction
  have hstep : (∫ y, ∑ p : GUECoord (Fin r) (N + 1),
        (flatDerivStat r k F z N f y p) ^ 2 ∂μ)
      ≤ ∫ y, C₀ * hsNorm (cfc (deriv f) (flatPencilBlk r k F N z y)) ∂μ :=
    integral_mono (integrable_finsetSum _ fun p _ => (hDmem p).integrable_sq)
      (hint.const_mul C₀) hcontr
  -- the Hilbert–Schmidt identity
  have hblk : ∀ y : EuclideanSpace ℝ (GUECoord (Fin r) (N + 1)),
      normTrace (cfc (fun t => (deriv f t) ^ 2) (flatPencilBlk r k F N z y))
        = flatStatBlk r k F z N (fun t => (deriv f t) ^ 2) y := by
    intro y
    rw [flatStatBlk, hermCfc]
  have hhs : (∫ y, hsNorm (cfc (deriv f) (flatPencilBlk r k F N z y)) ∂μ)
      = m * ∫ y, flatStatBlk r k F z N (fun t => (deriv f t) ^ 2) y ∂μ := by
    have heq : (fun y : EuclideanSpace ℝ (GUECoord (Fin r) (N + 1)) =>
          hsNorm (cfc (deriv f) (flatPencilBlk r k F N z y)))
        = fun y : EuclideanSpace ℝ (GUECoord (Fin r) (N + 1)) =>
            m * normTrace (cfc (fun t => (deriv f t) ^ 2) (flatPencilBlk r k F N z y)) := by
      funext y
      rw [hsNorm_cfc_deriv_eq k F N z f hf y, hm]
    rw [heq]
    simp only [hblk]
    rw [integral_const_mul]
  have h2 : (∫ y, C₀ * hsNorm (cfc (deriv f) (flatPencilBlk r k F N z y)) ∂μ)
      = C₀ * (m * ∫ y, flatStatBlk r k F z N (fun t => (deriv f t) ^ 2) y ∂μ) := by
    rw [integral_const_mul, hhs]
  refine (variance_flatStatBlk_le k F z N f hf hF hDmem hpoly).trans ?_
  rw [hsum_eq]
  refine hstep.trans (le_of_eq ?_)
  rw [h2]
  ring

/-- The `N`-independent dimension constant `card (PenIdx wds) · d` of the flattened pencil;
`pencilFlatDim r k F N = pencilVDim r k F · (N+1)`. -/
def pencilVDim (r k : ℕ) (F : RatPolyIdx r (k + 1)) : ℝ :=
  (Fintype.card (PenIdx (polyW (h1Poly r k F))) : ℝ) * (((k + 1) + (k + 1)) : ℝ)

/-- The flattened pencil dimension is the `N`-independent `pencilVDim` times `N+1`. -/
lemma pencilFlatDim_eq (k : ℕ) (F : RatPolyIdx r (k + 1)) (N : ℕ) :
    (pencilFlatDim r k F N : ℝ) = pencilVDim r k F * ((N : ℝ) + 1) := by
  rw [pencilFlatDim, pencilVDim]
  push_cast
  ring

/-- `pencilVDim` is positive (the pencil index type and the block size are nonempty). -/
lemma pencilVDim_pos (k : ℕ) (F : RatPolyIdx r (k + 1)) : 0 < pencilVDim r k F := by
  haveI : Nonempty (PenIdx (polyW (h1Poly r k F))) := inferInstance
  rw [pencilVDim]
  have h1 : (0 : ℝ) < (Fintype.card (PenIdx (polyW (h1Poly r k F))) : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have h2 : (0 : ℝ) < (((k + 1) + (k + 1)) : ℝ) := by positivity
  exact mul_pos h1 h2

/-- The variance of the flattened pencil statistic on the common space is the variance of the
block statistic. -/
lemma variance_flatStat_eq_blk (k : ℕ) (F : RatPolyIdx r (k + 1)) (z : ℝ) (N : ℕ)
    (f : ℝ → ℝ)
    (hmeas : AEMeasurable (flatStatBlk r k F z N f)
      (stdGaussian (EuclideanSpace ℝ (GUECoord (Fin r) (N + 1))))) :
    variance (flatStat r k F z N f) (commonGaussianMeasure (Fin r))
      = variance (flatStatBlk r k F z N f)
          (stdGaussian (EuclideanSpace ℝ (GUECoord (Fin r) (N + 1)))) := by
  have hfun : flatStat r k F z N f
      = fun x : CommonSpace (Fin r) => flatStatBlk r k F z N f (x (N + 1)) := by
    funext x
    exact flatStat_eq_blk k F x z N f
  rw [hfun]
  exact variance_eval_commonGaussian (ι := Fin r) (N := N + 1) hmeas

/-- The integral of the flattened pencil statistic on the common space is the block integral. -/
lemma integral_flatStat_eq_blk (k : ℕ) (F : RatPolyIdx r (k + 1)) (z : ℝ) (N : ℕ)
    (f : ℝ → ℝ)
    (hmeas : AEStronglyMeasurable (flatStatBlk r k F z N f)
      (stdGaussian (EuclideanSpace ℝ (GUECoord (Fin r) (N + 1))))) :
    ∫ x, flatStat r k F z N f x ∂(commonGaussianMeasure (Fin r))
      = ∫ y, flatStatBlk r k F z N f y
          ∂(stdGaussian (EuclideanSpace ℝ (GUECoord (Fin r) (N + 1)))) := by
  have hfun : flatStat r k F z N f
      = fun x : CommonSpace (Fin r) => flatStatBlk r k F z N f (x (N + 1)) := by
    funext x
    exact flatStat_eq_blk k F x z N f
  rw [hfun]
  exact integral_eval_commonGaussian (ι := Fin r) (N := N + 1) hmeas

/-- **Lemma V for the flattened polynomial pencil, on the common Gaussian space.**  Under the
direction contraction with constant `C₀`,

`Var(tau_N(f(fl ℒ_z))) ≤ C₀ · m · E[tau_N((f')²(fl ℒ_z))]`,  `m = pencilFlatDim r k F N`. -/
theorem variance_flatStat_le_of_contraction (k : ℕ) (F : RatPolyIdx r (k + 1)) (z : ℝ)
    (N : ℕ) (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f) (C₀ : ℝ)
    (hF : MemLp (flatStatBlk r k F z N f)
      2 (stdGaussian (EuclideanSpace ℝ (GUECoord (Fin r) (N + 1)))))
    (hDmem : ∀ p : GUECoord (Fin r) (N + 1), MemLp (fun y => flatDerivStat r k F z N f y p)
      2 (stdGaussian (EuclideanSpace ℝ (GUECoord (Fin r) (N + 1)))))
    (hpoly : ∀ p : GUECoord (Fin r) (N + 1),
      ∀ᵐ y ∂(stdGaussian (EuclideanSpace ℝ (GUECoord (Fin r) (N + 1)))),
        PolyGrowth (fun u : ℝ => flatStatBlk r k F z N f (euclidUpdate y p u)) ∧
        PolyGrowth (fun u : ℝ => flatDerivStat r k F z N f (euclidUpdate y p u) p))
    (hint : Integrable (fun y => hsNorm (cfc (deriv f) (flatPencilBlk r k F N z y)))
      (stdGaussian (EuclideanSpace ℝ (GUECoord (Fin r) (N + 1)))))
    (hWint : Integrable (flatStatBlk r k F z N (fun t => (deriv f t) ^ 2))
      (stdGaussian (EuclideanSpace ℝ (GUECoord (Fin r) (N + 1)))))
    (hcontr : ∀ y : EuclideanSpace ℝ (GUECoord (Fin r) (N + 1)),
      ∑ p : GUECoord (Fin r) (N + 1), (flatDerivStat r k F z N f y p) ^ 2
        ≤ C₀ * hsNorm (cfc (deriv f) (flatPencilBlk r k F N z y))) :
    variance (flatStat r k F z N f) (commonGaussianMeasure (Fin r))
      ≤ C₀ * (pencilFlatDim r k F N : ℝ)
          * ∫ x, flatStat r k F z N (fun t => (deriv f t) ^ 2) x
              ∂(commonGaussianMeasure (Fin r)) := by
  have hblk := variance_flatStatBlk_le_of_contraction k F z N f hf C₀ hF hDmem hpoly
    hint hcontr
  rw [variance_flatStat_eq_blk k F z N f hF.aemeasurable,
    integral_flatStat_eq_blk k F z N (fun t => (deriv f t) ^ 2) hWint.aestronglyMeasurable]
  exact hblk

/-- **Lemma V for the flattened polynomial pencil: the sharp `1/N²` variance bound (the `hV`
input of `PencilLemmaSData`).**  Let `G ≥ 0` be the amplification constant of the flattened
direction family, i.e. assume the direction contraction

`∑_p (∂_p tau_N(f(fl ℒ_z)))² ≤ 2 gueScale(N+1)² G · (pencilFlatDim)⁻² · ‖f'(fl ℒ_z)‖_F²`.

Then, for `N ≥ 1`,

`Var(tau_N(f(fl ℒ_z)))  ≤  (2G / (card(PenIdx)·d)) / N² · E[tau_N((f')²(fl ℒ_z))]`.

Since `gueScale(N+1)² = 1/(N+1)` and `pencilFlatDim = card(PenIdx)·d·(N+1)`, the two `m`
factors cancel and the `(N+1)⁻²` produced is dominated by `N⁻²`: this is exactly the
bookkeeping of `lemmaV_sharp_smooth`, with `∑_i frob(A_i)²` replaced by the amplification
constant `G` of the pencil. -/
theorem flatLemmaV (k : ℕ) (F : RatPolyIdx r (k + 1)) (z : ℝ)
    (N : ℕ) (hN : 0 < N) (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f) (G : ℝ) (hG : 0 ≤ G)
    (hF : MemLp (flatStatBlk r k F z N f)
      2 (stdGaussian (EuclideanSpace ℝ (GUECoord (Fin r) (N + 1)))))
    (hDmem : ∀ p : GUECoord (Fin r) (N + 1), MemLp (fun y => flatDerivStat r k F z N f y p)
      2 (stdGaussian (EuclideanSpace ℝ (GUECoord (Fin r) (N + 1)))))
    (hpoly : ∀ p : GUECoord (Fin r) (N + 1),
      ∀ᵐ y ∂(stdGaussian (EuclideanSpace ℝ (GUECoord (Fin r) (N + 1)))),
        PolyGrowth (fun u : ℝ => flatStatBlk r k F z N f (euclidUpdate y p u)) ∧
        PolyGrowth (fun u : ℝ => flatDerivStat r k F z N f (euclidUpdate y p u) p))
    (hint : Integrable (fun y => hsNorm (cfc (deriv f) (flatPencilBlk r k F N z y)))
      (stdGaussian (EuclideanSpace ℝ (GUECoord (Fin r) (N + 1)))))
    (hWint : Integrable (flatStatBlk r k F z N (fun t => (deriv f t) ^ 2))
      (stdGaussian (EuclideanSpace ℝ (GUECoord (Fin r) (N + 1)))))
    (hcontr : ∀ y : EuclideanSpace ℝ (GUECoord (Fin r) (N + 1)),
      ∑ p : GUECoord (Fin r) (N + 1), (flatDerivStat r k F z N f y p) ^ 2
        ≤ 2 * (gueScale (N + 1)) ^ 2 * G / (pencilFlatDim r k F N : ℝ) ^ 2
            * hsNorm (cfc (deriv f) (flatPencilBlk r k F N z y)))
    (hW0 : 0 ≤ ∫ x, flatStat r k F z N (fun t => (deriv f t) ^ 2) x
      ∂(commonGaussianMeasure (Fin r))) :
    variance (flatStat r k F z N f) (commonGaussianMeasure (Fin r))
      ≤ 2 * G / pencilVDim r k F / (N : ℝ) ^ 2
          * ∫ x, flatStat r k F z N (fun t => (deriv f t) ^ 2) x
              ∂(commonGaussianMeasure (Fin r)) := by
  classical
  set m : ℝ := (pencilFlatDim r k F N : ℝ) with hm
  set V : ℝ := pencilVDim r k F with hV
  have hVpos : 0 < V := pencilVDim_pos k F
  have hmpos : 0 < m := by rw [hm, pencilFlatDim_eq]; positivity
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hmV : m = V * ((N : ℝ) + 1) := by rw [hm, hV, pencilFlatDim_eq]
  have hstep := variance_flatStat_le_of_contraction k F z N f hf
    (2 * (gueScale (N + 1)) ^ 2 * G / m ^ 2) hF hDmem hpoly hint hWint hcontr
  rw [hm] at hstep
  -- the coefficient `C₀ · m` is `2 G / ((N+1) · m)`
  have hcoef : 2 * (gueScale (N + 1)) ^ 2 * G / m ^ 2 * m
      = 2 * G / ((N : ℝ) + 1) / m := by
    have hsq : (gueScale (N + 1)) ^ 2 = ((N : ℝ) + 1)⁻¹ := by
      rw [gueScale_sq]
      push_cast
      ring_nf
    rw [hsq]
    have hpos : (0 : ℝ) < (N : ℝ) + 1 := by linarith
    field_simp
  rw [hcoef] at hstep
  refine hstep.trans ?_
  -- compare `2G/((N+1)·m)` with `2G/(V·N²)` using `m = V(N+1)`
  have hcmp : 2 * G / ((N : ℝ) + 1) / m ≤ 2 * G / V / (N : ℝ) ^ 2 := by
    rw [hmV, hV]
    rw [show (2 * G / ((N : ℝ) + 1) / (V * ((N : ℝ) + 1)))
        = 2 * G / (V * ((N : ℝ) + 1) ^ 2) by
      field_simp]
    rw [show (2 : ℝ) * G / V / (N : ℝ) ^ 2 = 2 * G / (V * (N : ℝ) ^ 2) by
      field_simp]
    have hpos1 : (0 : ℝ) < (N : ℝ) + 1 := by linarith
    have hnum : 0 ≤ 2 * G := by linarith
    have hd : (0 : ℝ) < V * (N : ℝ) ^ 2 := mul_pos hVpos (pow_pos hNR 2)
    have hle : V * (N : ℝ) ^ 2 ≤ V * ((N : ℝ) + 1) ^ 2 := by
      have hs : (N : ℝ) ^ 2 ≤ ((N : ℝ) + 1) ^ 2 := by nlinarith
      exact mul_le_mul_of_nonneg_left hs (le_of_lt hVpos)
    calc 2 * G / (V * ((N : ℝ) + 1) ^ 2) = 2 * G * (V * ((N : ℝ) + 1) ^ 2)⁻¹ := by
          rw [div_eq_mul_inv]
      _ ≤ 2 * G * (V * (N : ℝ) ^ 2)⁻¹ := by
          refine mul_le_mul_of_nonneg_left ?_ hnum
          exact inv_anti₀ hd hle
      _ = 2 * G / (V * (N : ℝ) ^ 2) := by rw [div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_right hcmp hW0

/-- **The `hV` estimate of `PencilLemmaSData`, for all large `N`.**  This is `flatLemmaV` with
the per-`N` hypotheses bundled, stated in the `∀ᶠ N` form.  (The `N = 0` instance is excluded:
`flatStat` at `N = 0` reads the nondegenerate Gaussian block `x 1`, so its variance is
positive while the right-hand side `C/0² · …` vanishes.) -/
theorem flatLemmaV_hV (k : ℕ) (F : RatPolyIdx r (k + 1)) (z : ℝ) (f : ℝ → ℝ)
    (hf : ContDiff ℝ 1 f) (G : ℝ) (hG : 0 ≤ G)
    (hF : ∀ N : ℕ, MemLp (flatStatBlk r k F z N f)
      2 (stdGaussian (EuclideanSpace ℝ (GUECoord (Fin r) (N + 1)))))
    (hDmem : ∀ (N : ℕ) (p : GUECoord (Fin r) (N + 1)),
      MemLp (fun y => flatDerivStat r k F z N f y p)
        2 (stdGaussian (EuclideanSpace ℝ (GUECoord (Fin r) (N + 1)))))
    (hpoly : ∀ (N : ℕ) (p : GUECoord (Fin r) (N + 1)),
      ∀ᵐ y ∂(stdGaussian (EuclideanSpace ℝ (GUECoord (Fin r) (N + 1)))),
        PolyGrowth (fun u : ℝ => flatStatBlk r k F z N f (euclidUpdate y p u)) ∧
        PolyGrowth (fun u : ℝ => flatDerivStat r k F z N f (euclidUpdate y p u) p))
    (hint : ∀ N : ℕ, Integrable (fun y => hsNorm (cfc (deriv f) (flatPencilBlk r k F N z y)))
      (stdGaussian (EuclideanSpace ℝ (GUECoord (Fin r) (N + 1)))))
    (hWint : ∀ N : ℕ, Integrable (flatStatBlk r k F z N (fun t => (deriv f t) ^ 2))
      (stdGaussian (EuclideanSpace ℝ (GUECoord (Fin r) (N + 1)))))
    (hcontr : ∀ (N : ℕ) (y : EuclideanSpace ℝ (GUECoord (Fin r) (N + 1))),
      ∑ p : GUECoord (Fin r) (N + 1), (flatDerivStat r k F z N f y p) ^ 2
        ≤ 2 * (gueScale (N + 1)) ^ 2 * G / (pencilFlatDim r k F N : ℝ) ^ 2
            * hsNorm (cfc (deriv f) (flatPencilBlk r k F N z y)))
    (hW0 : ∀ N : ℕ, 0 ≤ ∫ x, flatStat r k F z N (fun t => (deriv f t) ^ 2) x
      ∂(commonGaussianMeasure (Fin r))) :
    ∀ᶠ N : ℕ in atTop,
      variance (flatStat r k F z N f) (commonGaussianMeasure (Fin r))
        ≤ 2 * G / pencilVDim r k F / (N : ℝ) ^ 2
            * ∫ x, flatStat r k F z N (fun t => (deriv f t) ^ 2) x
                ∂(commonGaussianMeasure (Fin r)) := by
  filter_upwards [eventually_ge_atTop 1] with N hN
  exact flatLemmaV k F z N hN f hf G hG (hF N) (hDmem N) (hpoly N) (hint N) (hWint N)
    (hcontr N) (hW0 N)

end VarianceBound

end FlatStructure

end

end GUEStrongConvergence
