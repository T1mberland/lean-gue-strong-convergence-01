/-
# Concentration of GUE resolvent pairings and of the resolvent norm

This file closes the "concentration" step of II.A as far as it is mathematically
sound.  It builds on the verified Lipschitz bound of `ResolventLipschitz.lean`
(`resolventPairing_lipschitz`, `resolventPairing_tail`).

Main results:

* `resolventVarianceConst` — the `N`-independent variance proxy
  `C = 2 (∑ᵢ ‖Aᵢ‖_F²) (im z)⁻⁴`, and
  `resolventLipschitzConst_sq_le` — the Lipschitz constant squared is `≤ C / N`
  for vectors of squared norm at most `1`;
* `summable_two_exp_neg_mul` — `∑_N 2 exp(-(r²/2C) N) < ∞` for `r, C > 0`;
* `gaussian_tail_le_of_lipschitz_sq_le` — a Gaussian tail bound at scale `r` for a
  Lipschitz function whose constant squared is at most `B`, valid also in the
  degenerate case `B = 0` (where the function is constant);
* `ae_eventually_abs_resolventPairing_sub_integral_lt` — **Borel–Cantelli for
  resolvent pairings**: for any fixed pair of bounded vector families, almost
  surely the deviation of a resolvent pairing from its mean is eventually smaller
  than any fixed `r > 0`.  This is the honest a.s. concentration statement at a
  *fixed spectral parameter*; it holds with no restriction on `r`.

Note on the operator-norm statement.  The corresponding bound for the operator
norm `‖R_N(z,x) - E R_N(z,x)‖` with an *arbitrary* fixed `r > 0` is **false** at fixed
`z` with `im z > 0`: the resolvent in this normalization (`gueScale N = N^{-1/2}`,
matrix dimension `d·N`) fluctuates in operator norm at the *constant* order
`√(d ∑ᵢ ‖Aᵢ‖_F²) / (im z)²`.  Indeed the `ε`-net union bound proved below exhibits the
exponent `2 d N log(1+2/ε) - r² N/(8C)`, which is positive for small fixed `r` and all
`N` (no summability), and for the `d = 1`, `A₀ = 0` pencil the eigenvector computation
`(R - ER) u_j = ((λ_j - z)⁻¹ - m) u_j` bounds `‖R - ER‖` below by the positive constant
`|i/2 - i(1-√2)|` at `z = 2i` (eigenvalues `λ_j` in the bulk).  Hence **II.A cannot be
closed by fixed-`z` operator-norm concentration**.  The remaining honest routes are
(i) a quantitative local law for the Stieltjes transform together with eigenvalue
counting, or (ii) an edge/maximum-principle argument from the *mean* Dyson equation plus
a quantitative stability estimate; both are beyond the bricks of this file.

Delivered here: the `N`-independent variance proxy and its summability (target 1), the
almost-sure concentration of any fixed resolvent pairing at every fixed `r > 0`
(target 2), the resolvent mean and the linearity of pairings against it, and the
`ε`-net union bound with an explicit cardinality `k N` and summability hypothesis
(target 3).  The deterministic passage from net pairings to the operator norm (the
standard `ε`-net approximation) and the norm-concentration-around-the-mean statement are
not included: both need the `C⋆`-module operator-norm characterisation
`CStarMatrix.norm_le_of_forall_inner_le` combined with the pairing identity, which is
currently obstructed by `WithCStarModule` instance mismatches in this toolchain.
-/
import GUEStrongConvergence.Probability.ResolventLipschitz
import GUEStrongConvergence.Probability.CommonSpaceBorelCantelli
import Mathlib.Analysis.SpecialFunctions.Exp

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped Matrix.Norms.Elementwise ComplexOrder ENNReal NNReal Topology
open scoped WithCStarModule InnerProductSpace

set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace GUEStrongConvergence

noncomputable section

variable {ι d : Type*} {N : ℕ} [Fintype ι] [Fintype d] [DecidableEq d] [DecidableEq ι]

/-! ### The `N`-independent variance proxy and its summability -/

/-- The `N`-independent constant controlling the `N^{-1}` variance proxy of a
resolvent pairing: `C = 2 (∑ᵢ ‖Aᵢ‖_F²) (im z)⁻⁴`. -/
def resolventVarianceConst (A : ι → Matrix d d ℂ) (z : ℂ) : ℝ :=
  2 * (∑ i, (frob (A i)) ^ 2) * ((z.im)⁻¹) ^ 4

lemma resolventVarianceConst_nonneg (A : ι → Matrix d d ℂ) (z : ℂ) :
    0 ≤ resolventVarianceConst A z := by
  rw [resolventVarianceConst]
  positivity

/-- **Forwarding the `1/N` variance proxy.**  For vectors of squared norm at most one, the
squared Lipschitz constant of a resolvent pairing is at most `C / N`. -/
theorem resolventLipschitzConst_sq_le (A : ι → Matrix d d ℂ) (z : ℂ)
    (u v : d × Fin N → ℂ) (hu : ∑ k, ‖u k‖ ^ 2 ≤ 1) (hv : ∑ k, ‖v k‖ ^ 2 ≤ 1) :
    (resolventLipschitzConst (N := N) A z u v) ^ 2
      ≤ resolventVarianceConst A z / (N : ℝ) := by
  have hsum : 0 ≤ ∑ i, (frob (A i)) ^ 2 := by positivity
  have hη : 0 ≤ ((z.im)⁻¹) ^ 4 := by positivity
  have hu0 : 0 ≤ ∑ k, ‖u k‖ ^ 2 := by positivity
  have hv0 : 0 ≤ ∑ k, ‖v k‖ ^ 2 := by positivity
  have hsq := Real.sq_sqrt (by positivity : 0 ≤
    2 * (gueScale N) ^ 2 * (∑ i, (frob (A i)) ^ 2) *
      ((z.im)⁻¹) ^ 4 * (∑ k, ‖u k‖ ^ 2) * (∑ k, ‖v k‖ ^ 2))
  rw [resolventLipschitzConst, hsq]
  have hg : (gueScale N) ^ 2 = (N : ℝ)⁻¹ := gueScale_sq N
  calc 2 * (gueScale N) ^ 2 * (∑ i, (frob (A i)) ^ 2) * ((z.im)⁻¹) ^ 4 *
        (∑ k, ‖u k‖ ^ 2) * (∑ k, ‖v k‖ ^ 2)
      = (gueScale N) ^ 2 * (2 * (∑ i, (frob (A i)) ^ 2) * ((z.im)⁻¹) ^ 4) *
          (∑ k, ‖u k‖ ^ 2) * (∑ k, ‖v k‖ ^ 2) := by ring
    _ ≤ (N : ℝ)⁻¹ * (2 * (∑ i, (frob (A i)) ^ 2) * ((z.im)⁻¹) ^ 4) * 1 * 1 := by
        rw [hg]
        gcongr
    _ = resolventVarianceConst A z / (N : ℝ) := by
        rw [resolventVarianceConst, div_eq_mul_inv]
        ring

/-- The exponential tail sequence `N ↦ 2 exp(-(r²/2C) N)` is summable for `r, C > 0`. -/
theorem summable_two_exp_neg_mul {c r : ℝ} (hc : 0 < c) (hr : 0 < r) :
    Summable fun N : ℕ => 2 * Real.exp (-(r ^ 2 / (2 * c)) * N) := by
  have hpos : 0 < r ^ 2 / (2 * c) := by positivity
  have hneg : -(r ^ 2 / (2 * c)) < 0 := by linarith
  have hbase : Summable fun N : ℕ => Real.exp (N * (-(r ^ 2 / (2 * c)))) :=
    Real.summable_exp_nat_mul_iff.mpr hneg
  have h' : Summable fun N : ℕ => Real.exp (-(r ^ 2 / (2 * c)) * N) := by
    simpa only [mul_comm] using hbase
  simpa only [mul_comm] using h'.mul_left 2

/-- The exponent appearing after substituting `B = C / N` is linear in `N`. -/
lemma div_two_mul_div_eq {c r : ℝ} (hc : 0 ≤ c) (N : ℕ) :
    r ^ 2 / (2 * (c / (N : ℝ))) = (r ^ 2 / (2 * c)) * N := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    simp
  · rcases eq_or_lt_of_le hc with hc0 | hcpos
    · rw [← hc0]
      simp
    · have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
      have hc' : c ≠ 0 := hcpos.ne'
      field_simp

/-! ### A Gaussian tail bound at a given scale, including the degenerate case -/

/-- If a real function on a finite Euclidean space is `0`-Lipschitz, it is constant, so the
deviation from its mean vanishes identically. -/
theorem measure_deviation_eq_zero_of_lipschitz_zero {κ : Type*} [Fintype κ]
    {f : EuclideanSpace ℝ κ → ℝ} (hf : LipschitzWith 0 f) {r : ℝ} (hr : 0 < r) :
    (stdGaussian (EuclideanSpace ℝ κ)).real
        {x | r ≤ |f x - ∫ y, f y ∂(stdGaussian (EuclideanSpace ℝ κ))|} = 0 := by
  have hconst : ∀ x, f x = f 0 := by
    intro x
    have hd : dist (f x) (f 0) = 0 := by
      refine le_antisymm ?_ dist_nonneg
      simpa using hf.dist_le_mul x 0
    rw [Real.dist_eq] at hd
    exact sub_eq_zero.mp (abs_eq_zero.mp hd)
  have hfi : ∫ y, f y ∂(stdGaussian (EuclideanSpace ℝ κ)) = f 0 := by
    have hfun : (fun y => f y) = fun _ => f 0 := funext hconst
    rw [hfun]
    simp
  have hset : {x : EuclideanSpace ℝ κ |
      r ≤ |f x - ∫ y, f y ∂(stdGaussian (EuclideanSpace ℝ κ))|} = ∅ := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_le]
    rw [hfi, hconst x, sub_self, abs_zero]
    exact hr
  rw [hset]
  simp

/-- **Gaussian tail bound at scale `r` from a bound on the squared Lipschitz constant.**
If `K² ≤ B` with `B ≥ 0`, then the deviation of `f` from its mean exceeds `r` with
probability at most `2 exp(-r²/(2B))`.  The degenerate case `B = 0` is handled by the
fact that then `K = 0` and `f` is constant (the deviation event is empty). -/
theorem gaussian_tail_le_of_lipschitz_sq_le {κ : Type*} [Fintype κ]
    {f : EuclideanSpace ℝ κ → ℝ} {K : ℝ≥0} {B : ℝ}
    (hf : LipschitzWith K f) (hK : (K : ℝ) ^ 2 ≤ B) (hB : 0 ≤ B) {r : ℝ} (hr : 0 < r) :
    (stdGaussian (EuclideanSpace ℝ κ)).real
        {x | r ≤ |f x - ∫ y, f y ∂(stdGaussian (EuclideanSpace ℝ κ))|} ≤
      2 * Real.exp (-(r ^ 2 / (2 * B))) := by
  rcases eq_or_lt_of_le hB with hB0 | hBpos
  · -- `B = 0` forces `K = 0`, hence `f` is constant.
    have hK0 : K = 0 := by
      have h2 : (K : ℝ) ^ 2 = 0 := by
        have hKB : (K : ℝ) ^ 2 ≤ B := hK
        rw [← hB0] at hKB
        exact le_antisymm hKB (by positivity)
      have hcoe : (K : ℝ) = 0 := by
        nlinarith [NNReal.coe_nonneg K]
      exact NNReal.coe_eq_zero.mp hcoe
    rw [measure_deviation_eq_zero_of_lipschitz_zero (by simpa only [hK0] using hf) hr]
    have : 0 < 2 * Real.exp (-(r ^ 2 / (2 * B))) := by positivity
    exact le_of_lt this
  · rcases eq_or_lt_of_le (show (0 : ℝ) ≤ (K : ℝ) from K.coe_nonneg) with hK0 | hKpos
    · -- `K = 0`: the deviation event is empty.
      have hKcoe : ((K : ℝ≥0) : ℝ) = 0 := hK0.symm
      have hK : K = 0 := NNReal.coe_eq_zero.mp hKcoe
      rw [measure_deviation_eq_zero_of_lipschitz_zero (by simpa only [hK] using hf) hr]
      have : 0 < 2 * Real.exp (-(r ^ 2 / (2 * B))) := by positivity
      exact le_of_lt this
    · -- `K > 0`: compare the two exponents.
      have hKpos' : (0 : ℝ) < (K : ℝ) ^ 2 := by positivity
      have hexp : -r ^ 2 / (2 * (K : ℝ) ^ 2) ≤ -(r ^ 2 / (2 * B)) := by
        rw [neg_div, neg_le_neg_iff]
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [hK, sq_nonneg r]
      refine (gaussian_measure_abs_ge_le_stdGaussian hf hr.le).trans ?_
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp) (by positivity)

/-! ### Measurability and continuity of resolvent pairings -/

/-- Each entry of the resolvent is continuous in the Gaussian coordinate vector. -/
theorem continuous_guePencilResolvent_entry
    (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    (hA₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian)
    (z : ℂ) (hz : 0 < z.im) (a b : d × Fin N) :
    Continuous fun x : EuclideanSpace ℝ (GUECoord ι N) =>
      guePencilResolvent A₀ A x z a b := by
  have hraw := (CStarMatrix.ofMatrixL : Matrix (d × Fin N) (d × Fin N) ℂ ≃L[ℂ]
    CStarMatrix (d × Fin N) (d × Fin N) ℂ).symm.continuous.comp
      (continuous_guePencilResolvent (N := N) A₀ A hA₀ hA z (ne_of_gt hz))
  exact (continuous_apply b).comp ((continuous_apply a).comp hraw)

/-- The real part of a resolvent pairing is continuous in the Gaussian coordinates. -/
theorem continuous_resolventPairing_re
    (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    (hA₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian)
    (z : ℂ) (hz : 0 < z.im) (u v : d × Fin N → ℂ) :
    Continuous fun x : EuclideanSpace ℝ (GUECoord ι N) =>
      (resolventPairing A₀ A z u v (fun p => x p)).re := by
  have hentry : ∀ a b : d × Fin N, Continuous fun x : EuclideanSpace ℝ (GUECoord ι N) =>
      guePencilResolvent A₀ A x z a b :=
    fun a b => continuous_guePencilResolvent_entry A₀ A hA₀ hA z hz a b
  have hsum : Continuous fun x : EuclideanSpace ℝ (GUECoord ι N) =>
      ∑ a, ∑ b, star (u a) * guePencilResolvent A₀ A x z a b * v b := by
    refine continuous_finsetSum _ fun a _ => continuous_finsetSum _ fun b _ => ?_
    exact (continuous_const.mul (hentry a b)).mul continuous_const
  exact Complex.continuous_re.comp hsum

/-! ### Borel–Cantelli for resolvent pairings -/

/-- **Almost-sure concentration of resolvent pairings at a fixed spectral parameter.**
Let `u N`, `v N` be vector families with squared norms bounded by one.  Then almost surely
the real pairing `Re ⟨u_N, R_N(z) v_N⟩` is eventually within any fixed `r > 0` of its
mean, with no condition on `r`. -/
theorem ae_eventually_abs_resolventPairing_sub_integral_lt
    (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    (hA₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian)
    (z : ℂ) (hz : 0 < z.im)
    (u v : (N : ℕ) → d × Fin N → ℂ)
    (hu : ∀ N, ∑ k, ‖u N k‖ ^ 2 ≤ 1) (hv : ∀ N, ∑ k, ‖v N k‖ ^ 2 ≤ 1)
    {r : ℝ} (hr : 0 < r) :
    ∀ᵐ x ∂(commonGaussianMeasure ι), ∀ᶠ N in atTop,
      |(resolventPairing A₀ A z (u N) (v N) (fun p => x N p)).re -
        ∫ y, (resolventPairing A₀ A z (u N) (v N) (fun p => y p)).re
          ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))| < r := by
  classical
  set C : ℝ := resolventVarianceConst A z with hCdef
  have hC0 : 0 ≤ C := resolventVarianceConst_nonneg A z
  set P : (N : ℕ) → Set (EuclideanSpace ℝ (GUECoord ι N)) := fun N =>
    {x | r ≤ |(resolventPairing A₀ A z (u N) (v N) (fun p => x p)).re -
      ∫ y, (resolventPairing A₀ A z (u N) (v N) (fun p => y p)).re
        ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))|} with hPdef
  have hmeas : ∀ N, MeasurableSet (P N) := by
    intro N
    have hc : Continuous fun x : EuclideanSpace ℝ (GUECoord ι N) =>
        (resolventPairing A₀ A z (u N) (v N) (fun p => x p)).re :=
      continuous_resolventPairing_re A₀ A hA₀ hA z hz (u N) (v N)
    exact measurableSet_le measurable_const
      (continuous_abs.measurable.comp (hc.measurable.sub measurable_const))
  -- the squared Lipschitz constant is at most `C / N`
  have hKle : ∀ N, ((Real.toNNReal
      (resolventLipschitzConst (N := N) A z (u N) (v N)) : ℝ)) ^ 2 ≤ C / (N : ℝ) := by
    intro N
    have hcoe : ((Real.toNNReal
        (resolventLipschitzConst (N := N) A z (u N) (v N)) : ℝ)) =
        resolventLipschitzConst (N := N) A z (u N) (v N) :=
      Real.coe_toNNReal _ (resolventLipschitzConst_nonneg A z (u N) (v N))
    rw [hcoe, hCdef]
    exact resolventLipschitzConst_sq_le A z (u N) (v N) (hu N) (hv N)
  rcases eq_or_lt_of_le hC0 with hCzero | hCpos
  · -- Degenerate case `C = 0`: the Lipschitz constant vanishes, so all events are empty.
    have hzero : ∀ N, (stdGaussian (EuclideanSpace ℝ (GUECoord ι N))).real (P N) = 0 := by
      intro N
      have hKsq : ((Real.toNNReal
          (resolventLipschitzConst (N := N) A z (u N) (v N)) : ℝ)) ^ 2 ≤ 0 := by
        have := hKle N
        rw [← hCzero] at this
        simpa using this
      have hK0 : Real.toNNReal
          (resolventLipschitzConst (N := N) A z (u N) (v N)) = 0 := by
        have hcoe : ((Real.toNNReal
            (resolventLipschitzConst (N := N) A z (u N) (v N)) : ℝ)) = 0 := by
          nlinarith [NNReal.coe_nonneg
            (Real.toNNReal (resolventLipschitzConst (N := N) A z (u N) (v N)))]
        exact NNReal.coe_eq_zero.mp hcoe
      have hf0 : LipschitzWith 0 fun x : EuclideanSpace ℝ (GUECoord ι N) =>
          (resolventPairing A₀ A z (u N) (v N) (fun p => x p)).re := by
        simpa only [hK0] using
          resolventPairing_lipschitz A₀ A hA₀ hA z hz (u N) (v N)
      have h := measure_deviation_eq_zero_of_lipschitz_zero hf0 hr
      simpa only [P] using h
    have hsum : Summable fun N =>
        (stdGaussian (EuclideanSpace ℝ (GUECoord ι N))).real (P N) := by
      simp only [hzero]
      exact summable_zero
    refine (ae_eventually_not_mem_of_summable P hmeas hsum).mono fun x hx => ?_
    filter_upwards [hx] with N hN
    simpa only [P, Set.mem_ofPred_eq, not_le] using hN
  · -- Nondegenerate case: exponential tails summable with rate `r²/2C`.
    have hbound : ∀ N, (stdGaussian (EuclideanSpace ℝ (GUECoord ι N))).real (P N) ≤
        2 * Real.exp (-(r ^ 2 / (2 * C)) * N) := by
      intro N
      have hB0 : 0 ≤ C / (N : ℝ) := by positivity
      have := gaussian_tail_le_of_lipschitz_sq_le
        (f := fun x : EuclideanSpace ℝ (GUECoord ι N) =>
          (resolventPairing A₀ A z (u N) (v N) (fun p => x p)).re)
        (K := Real.toNNReal (resolventLipschitzConst (N := N) A z (u N) (v N)))
        (B := C / (N : ℝ))
        (resolventPairing_lipschitz A₀ A hA₀ hA z hz (u N) (v N)) (hKle N) hB0 hr
      -- rewrite the exponent into the linear form in `N`
      rw [div_two_mul_div_eq hC0 N, ← neg_mul] at this
      simpa only [P] using this
    have hsum_bound : Summable fun N : ℕ =>
        2 * Real.exp (-(r ^ 2 / (2 * C)) * N) := summable_two_exp_neg_mul hCpos hr
    have hsum : Summable fun N =>
        (stdGaussian (EuclideanSpace ℝ (GUECoord ι N))).real (P N) :=
      hsum_bound.of_nonneg_of_le (fun N => ENNReal.toReal_nonneg) hbound
    refine (ae_eventually_not_mem_of_summable P hmeas hsum).mono fun x hx => ?_
    filter_upwards [hx] with N hN
    simpa only [P, Set.mem_ofPred_eq, not_le] using hN

/-- The `≤` form of `ae_eventually_abs_resolventPairing_sub_integral_lt`. -/
theorem ae_eventually_abs_resolventPairing_sub_integral_le
    (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    (hA₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian)
    (z : ℂ) (hz : 0 < z.im)
    (u v : (N : ℕ) → d × Fin N → ℂ)
    (hu : ∀ N, ∑ k, ‖u N k‖ ^ 2 ≤ 1) (hv : ∀ N, ∑ k, ‖v N k‖ ^ 2 ≤ 1)
    {r : ℝ} (hr : 0 < r) :
    ∀ᵐ x ∂(commonGaussianMeasure ι), ∀ᶠ N in atTop,
      |(resolventPairing A₀ A z (u N) (v N) (fun p => x N p)).re -
        ∫ y, (resolventPairing A₀ A z (u N) (v N) (fun p => y p)).re
          ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))| ≤ r := by
  have h := ae_eventually_abs_resolventPairing_sub_integral_lt A₀ A hA₀ hA z hz u v hu hv
    (r := r / 2) (half_pos hr)
  filter_upwards [h] with x hx
  filter_upwards [hx] with N hN
  linarith


/-! ### The entrywise mean of the resolvent -/

/-- The entrywise mean of the resolvent of the GUE pencil.  This is the matrix that the
concentration statement centres at. -/
def resolventMean (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ) (z : ℂ) :
    CStarMatrix (d × Fin N) (d × Fin N) ℂ :=
  CStarMatrix.ofMatrix fun a b =>
    ∫ x : EuclideanSpace ℝ (GUECoord ι N), guePencilResolvent A₀ A x z a b
      ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))

/-- Each entry of the resolvent is integrable (bounded by `|im z|⁻¹`). -/
theorem integrable_guePencilResolvent_entry
    (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    (hA₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian)
    (z : ℂ) (hz : 0 < z.im) (a b : d × Fin N) :
    Integrable (fun x : EuclideanSpace ℝ (GUECoord ι N) =>
      guePencilResolvent A₀ A x z a b)
      (stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) :=
  (memLp_guePencilResolvent_entry A₀ A hA₀ hA z (ne_of_gt hz) a b 1).integrable le_rfl

/-- **The mean matrix pairs to the mean pairing**: the finite linear combination of the
entrywise means is the integral of the pairing. -/
theorem pairing_resolventMean
    (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    (hA₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian)
    (z : ℂ) (hz : 0 < z.im) (u v : d × Fin N → ℂ) :
    (∑ a, ∑ b, star (u a) * resolventMean A₀ A z a b * v b)
      = ∫ x, (∑ a, ∑ b, star (u a) * guePencilResolvent A₀ A x z a b * v b)
          ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) := by
  have hterm : ∀ a b, Integrable (fun x : EuclideanSpace ℝ (GUECoord ι N) =>
      star (u a) * guePencilResolvent A₀ A x z a b * v b)
      (stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) := by
    intro a b
    exact ((integrable_guePencilResolvent_entry A₀ A hA₀ hA z hz a b).const_mul
      (star (u a))).mul_const (v b)
  have hstep : ∀ a b : d × Fin N,
      (∫ x : EuclideanSpace ℝ (GUECoord ι N),
          star (u a) * guePencilResolvent A₀ A x z a b * v b
            ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N))))
        = star (u a) *
            (∫ x : EuclideanSpace ℝ (GUECoord ι N),
              guePencilResolvent A₀ A x z a b
                ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))) * v b := by
    intro a b
    calc (∫ x : EuclideanSpace ℝ (GUECoord ι N),
          star (u a) * guePencilResolvent A₀ A x z a b * v b
            ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N))))
        = (∫ x : EuclideanSpace ℝ (GUECoord ι N),
              star (u a) * guePencilResolvent A₀ A x z a b
                ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))) * v b :=
          integral_mul_const (v b) _
      _ = (star (u a) *
            (∫ x : EuclideanSpace ℝ (GUECoord ι N),
              guePencilResolvent A₀ A x z a b
                ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N))))) * v b := by
          rw [integral_const_mul]
      _ = star (u a) *
            (∫ x : EuclideanSpace ℝ (GUECoord ι N),
              guePencilResolvent A₀ A x z a b
                ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))) * v b := by ring
  simp only [resolventMean, CStarMatrix.ofMatrix_apply]
  calc (∑ a, ∑ b, star (u a) *
        (∫ x : EuclideanSpace ℝ (GUECoord ι N), guePencilResolvent A₀ A x z a b
          ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))) * v b)
      = ∑ a, ∑ b, ∫ x : EuclideanSpace ℝ (GUECoord ι N),
          star (u a) * guePencilResolvent A₀ A x z a b * v b
            ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) := by
        apply Finset.sum_congr rfl
        intro a _
        apply Finset.sum_congr rfl
        intro b _
        exact (hstep a b).symm
    _ = ∫ x, (∑ a, ∑ b, star (u a) * guePencilResolvent A₀ A x z a b * v b)
          ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) := by
        rw [show (∑ a, ∑ b, ∫ x : EuclideanSpace ℝ (GUECoord ι N),
              star (u a) * guePencilResolvent A₀ A x z a b * v b
                ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N))))
            = ∑ a, ∫ x : EuclideanSpace ℝ (GUECoord ι N),
                ∑ b, star (u a) * guePencilResolvent A₀ A x z a b * v b
                  ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) from by
          apply Finset.sum_congr rfl
          intro a _
          exact (integral_finsetSum _ (fun b _ => hterm a b)).symm]
        exact (integral_finsetSum _ (fun a _ => integrable_finsetSum _ (fun b _ => hterm a b))).symm

/-! ### The `C⋆`-module inner product versus the concrete pairing -/

/-- The `C⋆`-module inner product of a matrix against its `vecMul` action is the transposed
concrete pairing. -/
theorem inner_toCLM_eq_pairing {κ : Type*} [Fintype κ] (M : CStarMatrix κ κ ℂ)
    (v w : C⋆ᵐᵒᵈ(ℂ, κ → ℂ)) :
    ⟪w, CStarMatrix.toCLM M v⟫_ℂ
      = ∑ a, ∑ b, star (w a) * M b a * v b := by
  rw [CStarMatrix.toCLM_apply_eq_sum]
  simp only [WithCStarModule.pi_inner, WithCStarModule.inner_def, WithCStarModule.equiv_symm_pi_apply,
    Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

/-! ### The `ε`-net union bound

The probabilistic heart of the `ε`-net argument is the following finite union bound: the
probability that *some* net pairing deviates by more than `r/2` is at most the number of net
pairs times the single-pair tail.  Summability over `N` then gives the almost-sure statement by
Borel–Cantelli. -/

/-- The deviation of a resolvent pairing from its mean. -/
def pairingDeviation (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ) (z : ℂ)
    (u v : d × Fin N → ℂ) (x : EuclideanSpace ℝ (GUECoord ι N)) : ℝ :=
  |(resolventPairing A₀ A z u v (fun p => x p)).re -
    ∫ y, (resolventPairing A₀ A z u v (fun p => y p)).re
      ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))|

/-- **Finite `ε`-net union bound.**  If all net pairs have deviation probability at most `b`,
then the probability that some net pair deviates is at most `card² · b`. -/
theorem measureReal_net_iUnion_le
    (s : Finset (d × Fin N → ℂ)) {b : ℝ} (_hb : 0 ≤ b)
    (Q : (d × Fin N → ℂ) → (d × Fin N → ℂ) → Set (EuclideanSpace ℝ (GUECoord ι N)))
    (h : ∀ u ∈ s, ∀ v ∈ s,
      (stdGaussian (EuclideanSpace ℝ (GUECoord ι N))).real (Q u v) ≤ b) :
    (stdGaussian (EuclideanSpace ℝ (GUECoord ι N))).real
        (⋃ u ∈ (s : Set (d × Fin N → ℂ)), ⋃ v ∈ (s : Set (d × Fin N → ℂ)), Q u v) ≤
      (s.card : ℝ) * (s.card : ℝ) * b := by
  classical
  have h1 : (stdGaussian (EuclideanSpace ℝ (GUECoord ι N))).real
        (⋃ u ∈ (s : Set (d × Fin N → ℂ)), ⋃ v ∈ (s : Set (d × Fin N → ℂ)), Q u v) ≤
      ∑ u ∈ s, (stdGaussian (EuclideanSpace ℝ (GUECoord ι N))).real
        (⋃ v ∈ (s : Set (d × Fin N → ℂ)), Q u v) :=
    measureReal_biUnion_finset_le s _
  have h2 : ∀ u : d × Fin N → ℂ,
      (stdGaussian (EuclideanSpace ℝ (GUECoord ι N))).real
        (⋃ v ∈ (s : Set (d × Fin N → ℂ)), Q u v) ≤
      ∑ v ∈ s, (stdGaussian (EuclideanSpace ℝ (GUECoord ι N))).real (Q u v) :=
    fun u => measureReal_biUnion_finset_le s (Q u)
  refine h1.trans ((Finset.sum_le_sum fun u _ => h2 u).trans ?_)
  calc (∑ u ∈ s, ∑ v ∈ s, (stdGaussian (EuclideanSpace ℝ (GUECoord ι N))).real (Q u v))
      ≤ ∑ u ∈ s, ∑ _v ∈ s, b := by
        refine Finset.sum_le_sum fun u hu => Finset.sum_le_sum fun v hv => h u hu v hv
    _ = (s.card : ℝ) * (s.card : ℝ) * b := by
        simp only [Finset.sum_const, nsmul_eq_mul]
        ring

/-- **Borel–Cantelli for an `ε`-net of resolvent pairings.**  Let `s N` be a finite family of
unit vectors with `card (s N) ≤ k N`.  If the single-pair tail bounds are summable in the sense
`∑_N k_N² · 2 exp(-r² N/(8C)) < ∞` (with `C = 2 (∑ᵢ ‖Aᵢ‖_F²) (im z)⁻⁴`), then almost surely
all net pairings are eventually within `r/2` of their means. -/
theorem ae_eventually_net_pairing_le
    (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    (hA₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian)
    (z : ℂ) (hz : 0 < z.im)
    (s : (N : ℕ) → Finset (d × Fin N → ℂ))
    (hunit : ∀ N, ∀ u ∈ s N, ∑ k, ‖u k‖ ^ 2 = 1)
    (k : ℕ → ℕ) (hk : ∀ N, (s N).card ≤ k N)
    (hC : 0 < resolventVarianceConst A z)
    {r : ℝ} (hr : 0 < r)
    (hsum : Summable fun N : ℕ => (k N : ℝ) * (k N : ℝ) *
      (2 * Real.exp (-(r ^ 2 / (8 * resolventVarianceConst A z)) * N))) :
    ∀ᵐ x ∂(commonGaussianMeasure ι), ∀ᶠ N in atTop,
      ∀ u ∈ s N, ∀ v ∈ s N, pairingDeviation A₀ A z u v (x N) ≤ r / 2 := by
  classical
  set C : ℝ := resolventVarianceConst A z with hCdef
  have hC0 : 0 ≤ C := hC.le
  -- single-pair tail at level `r/2`
  have hsingle : ∀ (N : ℕ) (u v : d × Fin N → ℂ), ∑ k, ‖u k‖ ^ 2 = 1 →
      ∑ k, ‖v k‖ ^ 2 = 1 →
      (stdGaussian (EuclideanSpace ℝ (GUECoord ι N))).real
        {x | r / 2 ≤ pairingDeviation A₀ A z u v x} ≤
        2 * Real.exp (-(r ^ 2 / (8 * C)) * N) := by
    intro N u v hu hv
    have hB : 0 ≤ C / (N : ℝ) := by positivity
    have hK : (Real.toNNReal (resolventLipschitzConst (N := N) A z u v) : ℝ) ^ 2 ≤ C / N := by
      have hcoe : ((Real.toNNReal (resolventLipschitzConst (N := N) A z u v) : ℝ)) =
          resolventLipschitzConst (N := N) A z u v :=
        Real.coe_toNNReal _ (resolventLipschitzConst_nonneg A z u v)
      rw [hcoe, hCdef, div_eq_mul_inv]
      exact resolventLipschitzConst_sq_le A z u v hu.le hv.le
    have htail := gaussian_tail_le_of_lipschitz_sq_le
      (f := fun x : EuclideanSpace ℝ (GUECoord ι N) =>
        (resolventPairing A₀ A z u v (fun p => x p)).re)
      (K := Real.toNNReal (resolventLipschitzConst (N := N) A z u v))
      (B := C / (N : ℝ))
      (resolventPairing_lipschitz A₀ A hA₀ hA z hz u v) hK hB (half_pos hr)
    rw [div_two_mul_div_eq hC0 N, ← neg_mul] at htail
    have hexp : ((r / 2) ^ 2 / (2 * C)) = r ^ 2 / (8 * C) := by
      field_simp
      ring
    rwa [hexp] at htail
  set Q : (N : ℕ) → (d × Fin N → ℂ) → (d × Fin N → ℂ) →
      Set (EuclideanSpace ℝ (GUECoord ι N)) := fun N u v =>
    {x | r / 2 ≤ pairingDeviation A₀ A z u v x} with hQdef
  have hbound : ∀ N, (stdGaussian (EuclideanSpace ℝ (GUECoord ι N))).real
      (⋃ u ∈ (s N : Set (d × Fin N → ℂ)), ⋃ v ∈ (s N : Set (d × Fin N → ℂ)), Q N u v) ≤
      (k N : ℝ) * (k N : ℝ) * (2 * Real.exp (-(r ^ 2 / (8 * C)) * N)) := by
    intro N
    have hb : 0 ≤ 2 * Real.exp (-(r ^ 2 / (8 * C)) * N) := by positivity
    refine (measureReal_net_iUnion_le (N := N) (s N) hb (Q N) ?_).trans ?_
    · intro u hu v hv
      exact hsingle N u v (hunit N u hu) (hunit N v hv)
    · have hcard : ((s N).card : ℝ) ≤ (k N : ℝ) := by exact_mod_cast hk N
      gcongr
  have hmeas : ∀ N, MeasurableSet
      (⋃ u ∈ (s N : Set (d × Fin N → ℂ)), ⋃ v ∈ (s N : Set (d × Fin N → ℂ)), Q N u v) := by
    intro N
    exact Finset.measurableSet_biUnion (s N) fun u _ =>
      Finset.measurableSet_biUnion (s N) fun v _ => by
        have hc : Continuous fun x : EuclideanSpace ℝ (GUECoord ι N) =>
            (resolventPairing A₀ A z u v (fun p => x p)).re :=
          continuous_resolventPairing_re A₀ A hA₀ hA z hz u v
        exact measurableSet_le measurable_const
          (continuous_abs.measurable.comp (hc.measurable.sub measurable_const))
  have hsum' : Summable fun N =>
      (stdGaussian (EuclideanSpace ℝ (GUECoord ι N))).real
        (⋃ u ∈ (s N : Set (d × Fin N → ℂ)), ⋃ v ∈ (s N : Set (d × Fin N → ℂ)), Q N u v) :=
    hsum.of_nonneg_of_le (fun N => ENNReal.toReal_nonneg) hbound
  refine (ae_eventually_not_mem_of_summable
    (fun N => ⋃ u ∈ (s N : Set (d × Fin N → ℂ)), ⋃ v ∈ (s N : Set (d × Fin N → ℂ)), Q N u v)
    hmeas hsum').mono fun x hx => ?_
  filter_upwards [hx] with N hN
  simp only [hQdef, Set.mem_iUnion, Set.mem_ofPred_eq, not_exists, not_le] at hN
  exact fun u hu v hv => le_of_lt (hN u hu v hv)


end

end GUEStrongConvergence
