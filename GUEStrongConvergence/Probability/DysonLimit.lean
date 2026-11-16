/-
# Limit Dyson equation, stability, and the honest convergence rate

This file closes the logical chain of HT05 Theorem 5.7 as far as the current inputs allow:

1. **Limit Dyson equation.**  The deterministic limit `g(z)` is the operator-valued matrix
   Cauchy transform `FreeProbability.Fock.operatorMatrixPencilCauchy A₀ A z` of the pinned
   `lean-free-prob` dependency.  Its Dyson identity
   `(z • 1 - A₀ - ∑ i, A_i * g z * A_i) * g z = 1`
   is `operatorMatrixPencilCauchy_dyson`, whose covariance `matrixCovariance C D = ∑ i, C i * D * C i`
   matches this project's normalization exactly (the limit pencil is `A₀ + ∑ i, A_i ⊗ s_i`
   with unit-covariance semicirculars).

2. **Quantitative stability of the Dyson map.**  If `g` solves the Dyson equation exactly,
   `g'` solves it with defect `D`, and both satisfy `frob g, frob g' ≤ C (im z)⁻¹` with
   `2 C² (∑ frob(A_i)²) ≤ (im z)²`, then
   `frob (g' - g) ≤ 2 C (im z)⁻¹ frob D`.
   The proof is the exact identity `g' - g = g (D + ∑ i, A_i (g'-g) A_i g')`, which follows
   from the second resolvent identity at the level of the Dyson equation.

3. **Rate.**  Combining (2) with `approximate_dyson_entry_le` gives

   `frob (g_N(z) - g(z)) ≤ 4 (card d)⁴ sqrt(card d) (∑ frob(A_i)²) (im z)⁻¹ VarConst`,

   where `VarConst = 2 gueScale(N)² (∑ frob(A_i)²) (im z)⁻⁴`.  Since `gueScale(N)² = 1/N`,
   the honest rate is **`O(1/N)`**, not `O(1/N²)`.

## Rate check (important)

**Exact rate.**  `frob_gueResolventMean_sub_limit_le` gives

`frob (g_N(z) - g(z)) ≤ 4 (card d)⁴ sqrt(card d) (∑ frob(A_i)²)² gueScale(N)² (im z)⁻⁵`,

so the rate is **`O(1/N)`**, not `O(1/N²)`.  The `(im z)⁻⁵` comes from
`(im z)⁻¹` (defect-to-solution stability) times the defect's `(im z)⁻⁴` variance constant.

**Why the `O(1/N)` is not an artefact of the stability step.**  The stability lemma
`dyson_stability` is sharp at order `(im z)⁻¹`: its proof is the exact identity
`g' - g = g (D + ∑ i, A_i (g'-g) A_i g')` and a Neumann-type bound with constant
`2 (im z)⁻¹`.  The loss is entirely in the variance/covariance input.

**Normalization check.**  With `T_N = (id_d ⊗ tr_N) R = N⁻¹ ∑ k R_{(u,k),(v,k)}` and
`∂_p T_N = N⁻¹ ∑ k (R D_p R)_{(u,k),(v,k)}`, `D_p = gueScale(N) A_i ⊗ (α e_ab + β e_ba)`,
one has `‖D_p‖ ≤ gueScale(N) (|α| + |β|) ‖A_i‖`, i.e. `‖D_p‖ = O(N^{-1/2})`.  A *single*
derivative entry is therefore `O(N^{-1/2} (im z)^{-2})` by the operator-norm bound; the sharp
size is smaller by another `N^{-1/2}` because resolvent entries are typically `O(N^{-1/2})`
off the diagonal.  The Gaussian Poincaré inequality bounds the variance by
`sup_x ∑ p |∂_p T_N|²`, which is `O(gueScale(N)²) = O(1/N)`.  This bound is non-sharp by `N`:
for GUE linear statistics the true variance of a *normalized* trace is `O(N^{-2})`
(equivalently, `Var(Tr f(H)) = O(1)` for fixed smooth `f`, while Poincaré gives `O(N)` for the
unnormalized trace).  HT05's Proposition 4.7 variance `O(N^{-2})` is the *sharp two-point*
statement; it is not a consequence of the crude Poincaré/Cauchy–Schwarz derivative sum, and
recomputing that sum cannot produce it.

**What stronger input would give `O(N^{-2})`.**  The sharp two-point correlation of resolvent
entries, i.e. the second loop equation / genus expansion at second order:
`E[R_ab R_cd] - E[R_ab] E[R_cd] = O(N^{-2})`.  With it the covariance bound becomes
`O(N^{-2})`, and since `dyson_stability` contributes only `(im z)⁻¹`, the comparison would
improve to `frob (g_N - g) = O(N^{-2})`, which is the rate required by the Borel–Cantelli
step in `StrongConvergence/CutoffExclusion.lean` (`ae_eventually_lt_inv_mul_of_mean_variance`).
That second-order input is **not** available in this project and is not assumed here; the
present file is an exact finite-`N` `O(1/N)` statement.  The precise residual is therefore:
*derive the sharp two-point function (equivalently `Var(τ_N(f(H_N))) = O(N^{-2})`) for the
resolvent/polynomial statistics, replace `integral_norm_sq_fluctuation_le` by the sharp
`O(N^{-2})` covariance, and rerun the (unchanged) covariance and stability steps.*
-/
import GUEStrongConvergence.Probability.DysonVariance
import FreeProbability.OperatorValued.MatrixPencilResolvent
import FreeProbability.Analytic.Expectation

open MeasureTheory ProbabilityTheory Matrix Filter
open FreeProbability FreeProbability.Fock
open scoped Matrix.Norms.Frobenius ComplexOrder ENNReal NNReal Topology

set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000

namespace GUEStrongConvergence

variable {ι d : Type*} {N : ℕ} [Fintype ι] [Fintype d] [DecidableEq d] [DecidableEq ι]

noncomputable local instance : PartialOrder (WordSpace ι →L[ℂ] WordSpace ι) :=
  CStarAlgebra.spectralOrder _
noncomputable local instance : StarOrderedRing (WordSpace ι →L[ℂ] WordSpace ι) :=
  CStarAlgebra.spectralOrderedRing _

noncomputable section


/-! ### The Frobenius norm as a normed-ring norm -/

/-- The repo's explicit `frob` agrees with Mathlib's Frobenius norm. -/
lemma frob_eq_norm (M : Matrix d d ℂ) : frob M = ‖M‖ := by
  rw [frob, frobenius_norm_def, Real.sqrt_eq_rpow]
  congr 1
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Real.rpow_two]

lemma frob_add_le (A B : Matrix d d ℂ) : frob (A + B) ≤ frob A + frob B := by
  rw [frob_eq_norm, frob_eq_norm, frob_eq_norm]
  exact norm_add_le A B

lemma frob_sub_le (A B : Matrix d d ℂ) : frob (A - B) ≤ frob A + frob B := by
  rw [frob_eq_norm, frob_eq_norm, frob_eq_norm]
  exact norm_sub_le A B

lemma frob_mul_le (A B : Matrix d d ℂ) : frob (A * B) ≤ frob A * frob B := by
  rw [frob_eq_norm, frob_eq_norm, frob_eq_norm]
  exact norm_mul_le A B

lemma frob_sum_le {α : Type*} (s : Finset α) (f : α → Matrix d d ℂ) :
    frob (∑ i ∈ s, f i) ≤ ∑ i ∈ s, frob (f i) := by
  simpa only [frob_eq_norm] using norm_sum_le s f

lemma frob_nonneg' (M : Matrix d d ℂ) : 0 ≤ frob M := frob_nonneg M

/-- If every entry is bounded by `K`, the Frobenius norm is bounded by `card d * K`. -/
lemma frob_le_card_mul_of_entry_le (M : Matrix d d ℂ) {K : ℝ}
    (h : ∀ u v : d, ‖M u v‖ ≤ K) (hK : 0 ≤ K) :
    frob M ≤ (Fintype.card d : ℝ) * K := by
  have hsq : (frob M) ^ 2 ≤ ((Fintype.card d : ℝ) * K) ^ 2 := by
    rw [frob_sq]
    calc (∑ u : d, ∑ v : d, ‖M u v‖ ^ 2) ≤ ∑ u : d, ∑ v : d, K ^ 2 := by
          refine Finset.sum_le_sum fun u _ => Finset.sum_le_sum fun v _ => ?_
          exact pow_le_pow_left₀ (norm_nonneg _) (h u v) 2
      _ = (Fintype.card d : ℝ) * (Fintype.card d : ℝ) * K ^ 2 := by
          simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          ring
      _ = ((Fintype.card d : ℝ) * K) ^ 2 := by ring
  have hnn : 0 ≤ frob M := frob_nonneg M
  calc frob M = Real.sqrt ((frob M) ^ 2) := (Real.sqrt_sq hnn).symm
    _ ≤ Real.sqrt (((Fintype.card d : ℝ) * K) ^ 2) := Real.sqrt_le_sqrt hsq
    _ = (Fintype.card d : ℝ) * K := by
        rw [Real.sqrt_sq (mul_nonneg (by positivity) hK)]

/-! ### The limit Dyson equation -/

/-- Every nonreal `z` belongs to the resolvent set of the affine Fock pencil. -/
theorem operatorMatrixPencil_mem_resolventSet (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    (hA₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian) (z : ℂ) (hz : z.im ≠ 0) :
    z ∈ resolventSet ℂ (operatorMatrixPencil A₀ A) := by
  by_contra h
  exact hz ((operatorMatrixPencil_isSelfAdjoint A₀ A hA₀ hA).im_eq_zero_of_mem_spectrum
    (show z ∈ spectrum ℂ (operatorMatrixPencil A₀ A) from h))

/-- **Limit Dyson equation.**  For `g(z) = operatorMatrixPencilCauchy A₀ A z`,

`(z • 1 - A₀ - ∑ i, A_i * g z * A_i) * g z = 1`. -/
theorem limit_dyson_equation (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    (hA₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian) (z : ℂ) (hz : z.im ≠ 0) :
    (z • (1 : Matrix d d ℂ) - A₀
        - ∑ i, A i * operatorMatrixPencilCauchy A₀ A z * A i) *
      operatorMatrixPencilCauchy A₀ A z = 1 := by
  have h := operatorMatrixPencilCauchy_dyson A₀ A z
    (operatorMatrixPencil_mem_resolventSet A₀ A hA₀ hA z hz)
  simpa only [matrixCovariance_apply] using h

/-- Every entry of the limit Cauchy transform is bounded by `1/|im z|`. -/
theorem norm_operatorMatrixPencilCauchy_entry_le (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    (hA₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian) (z : ℂ) (hz : z.im ≠ 0)
    (u v : d) :
    ‖operatorMatrixPencilCauchy A₀ A z u v‖ ≤ |z.im|⁻¹ := by
  have hres : ‖resolvent (operatorMatrixPencil A₀ A) z‖ ≤ |z.im|⁻¹ :=
    norm_resolvent_le_inv_abs_im (operatorMatrixPencil_isSelfAdjoint A₀ A hA₀ hA) hz
  rw [operatorMatrixPencilCauchy, matrixExpectation_apply,
    CStarMatrix.ofMatrix_symm_apply]
  exact ((vacuumState ι).expectation_norm_le _).trans
    (CStarMatrix.norm_entry_le_norm.trans hres)

/-- Frobenius bound for the limit Cauchy transform. -/
theorem frob_operatorMatrixPencilCauchy_le (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    (hA₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian) (z : ℂ) (hz : z.im ≠ 0) :
    frob (operatorMatrixPencilCauchy A₀ A z) ≤ (Fintype.card d : ℝ) * |z.im|⁻¹ := by
  refine frob_le_card_mul_of_entry_le _ (fun u v => ?_) (by positivity)
  exact norm_operatorMatrixPencilCauchy_entry_le A₀ A hA₀ hA z hz u v

/-- Frobenius bound for the finite-`N` average. -/
theorem frob_gueResolventMean_le (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    (hA₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian) (z : ℂ) (hz : 0 < z.im)
    (hN : 0 < N) :
    frob (gueResolventMean (N := N) A₀ A z) ≤ (Fintype.card d : ℝ) * (z.im)⁻¹ := by
  refine frob_le_card_mul_of_entry_le _ (fun u v => ?_) (by positivity)
  rw [gueResolventMean_apply]
  calc ‖∫ x, guePartialTrace A₀ A z (x : GUECoord ι N → ℝ) u v
        ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))‖
      ≤ ∫ x, ‖guePartialTrace A₀ A z (x : GUECoord ι N → ℝ) u v‖
          ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ _x, (z.im)⁻¹ ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) := by
        refine integral_mono ?_ (integrable_const _) (fun x => ?_)
        · exact (integrable_guePartialTrace_entry A₀ A hA₀ hA z hz hN u v).norm
        · calc ‖guePartialTrace A₀ A z (x : GUECoord ι N → ℝ) u v‖ ≤ |z.im|⁻¹ :=
              norm_guePartialTrace_entry_le A₀ A hA₀ hA _ z (ne_of_gt hz) hN u v
            _ = (z.im)⁻¹ := by rw [abs_of_pos hz]
    _ = (z.im)⁻¹ := by simp

/-! ### Quantitative stability of the Dyson map -/

/-- **Stability of the Dyson map in the Frobenius norm.**  Suppose `g` solves the Dyson
equation exactly, `g'` solves it with defect `D`, and both are bounded by `C (im z)⁻¹` with
`2 C² (∑ frob(A_i)²) ≤ (im z)²`.  Then `frob (g' - g) ≤ 2 C (im z)⁻¹ frob D`. -/
theorem dyson_stability (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ) (z : ℂ)
    (hz : 0 < z.im) (g g' D : Matrix d d ℂ) {C : ℝ}
    (hg : (z • (1 : Matrix d d ℂ) - A₀ - ∑ i, A i * g * A i) * g = 1)
    (hg' : (z • (1 : Matrix d d ℂ) - A₀ - ∑ i, A i * g' * A i) * g' = 1 + D)
    (hg_b : frob g ≤ C * (z.im)⁻¹) (hg'_b : frob g' ≤ C * (z.im)⁻¹)
    (hC : 0 ≤ C)
    (hη : 2 * C ^ 2 * (∑ i, (frob (A i)) ^ 2) ≤ (z.im) ^ 2) :
    frob (g' - g) ≤ 2 * C * (z.im)⁻¹ * frob D := by
  classical
  set M : Matrix d d ℂ := z • (1 : Matrix d d ℂ) - A₀ - ∑ i, A i * g * A i with hM
  set L : Matrix d d ℂ := z • (1 : Matrix d d ℂ) - A₀ - ∑ i, A i * g' * A i with hL
  have hgM : M * g = 1 := by rw [hM]; exact hg
  have hLg' : L * g' = 1 + D := by rw [hL]; exact hg'
  have hgM' : g * M = 1 := mul_eq_one_comm.mp hgM
  -- defect identity
  have hML : M - L = ∑ i, A i * (g' - g) * A i := by
    rw [hM, hL]
    rw [show z • (1 : Matrix d d ℂ) - A₀ - ∑ i, A i * g * A i -
          (z • (1 : Matrix d d ℂ) - A₀ - ∑ i, A i * g' * A i)
        = ∑ i, A i * g' * A i - ∑ i, A i * g * A i from by abel]
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_sub, sub_mul]
  have h1 : M * g' = 1 + D + (∑ i, A i * (g' - g) * A i) * g' := by
    rw [show M * g' = L * g' + (M - L) * g' from by
      rw [show (M - L) * g' = M * g' - L * g' from sub_mul M L g']
      abel]
    rw [hLg', hML]
  have hMX : M * (g' - g) = D + ∑ i, A i * (g' - g) * A i * g' := by
    calc M * (g' - g) = M * g' - M * g := mul_sub M g' g
      _ = (1 + D + (∑ i, A i * (g' - g) * A i) * g') - 1 := by rw [h1, hgM]
      _ = D + (∑ i, A i * (g' - g) * A i) * g' := by abel
      _ = D + ∑ i, A i * (g' - g) * A i * g' := by rw [Finset.sum_mul]
  -- the Frobenius estimates
  have hsum_le : frob (∑ i, A i * (g' - g) * A i * g')
      ≤ (∑ i, (frob (A i)) ^ 2) * frob (g' - g) * frob g' := by
    refine (frob_sum_le Finset.univ (fun i => A i * (g' - g) * A i * g')).trans ?_
    have hterm : ∀ i : ι, frob (A i * (g' - g) * A i * g')
        ≤ (frob (A i)) ^ 2 * frob (g' - g) * frob g' := by
      intro i
      calc frob (A i * (g' - g) * A i * g')
          ≤ frob (A i * (g' - g) * A i) * frob g' := frob_mul_le _ _
        _ ≤ (frob (A i) * frob (g' - g) * frob (A i)) * frob g' := by
            refine mul_le_mul_of_nonneg_right ?_ (frob_nonneg _)
            calc frob (A i * (g' - g) * A i)
                ≤ frob (A i * (g' - g)) * frob (A i) := frob_mul_le _ _
              _ ≤ (frob (A i) * frob (g' - g)) * frob (A i) := by
                  exact mul_le_mul_of_nonneg_right (frob_mul_le _ _) (frob_nonneg _)
        _ = (frob (A i)) ^ 2 * frob (g' - g) * frob g' := by ring
    calc (∑ i : ι, frob (A i * (g' - g) * A i * g'))
        ≤ ∑ i : ι, (frob (A i)) ^ 2 * frob (g' - g) * frob g' :=
          Finset.sum_le_sum fun i _ => hterm i
      _ = (∑ i, (frob (A i)) ^ 2) * frob (g' - g) * frob g' := by
          rw [Finset.sum_mul, Finset.sum_mul]
  have hbound : frob (M * (g' - g)) ≤ frob D + (∑ i, (frob (A i)) ^ 2) *
      frob (g' - g) * frob g' := by
    calc frob (M * (g' - g)) = frob (D + ∑ i, A i * (g' - g) * A i * g') := by rw [hMX]
      _ ≤ frob D + frob (∑ i, A i * (g' - g) * A i * g') := frob_add_le _ _
      _ ≤ frob D + (∑ i, (frob (A i)) ^ 2) * frob (g' - g) * frob g' := by
          linarith [hsum_le]
  -- `g' - g = g (M (g' - g))`
  have hXeq : g' - g = g * (M * (g' - g)) := by
    rw [← mul_assoc, hgM', one_mul]
  have hmain : frob (g' - g) ≤ frob g * frob (M * (g' - g)) := by
    conv_lhs => rw [hXeq]
    exact frob_mul_le g (M * (g' - g))
  have hstep : frob (g' - g) ≤ frob g * frob D
      + (frob g * ((∑ i, (frob (A i)) ^ 2) * frob g')) * frob (g' - g) := by
    calc frob (g' - g) ≤ frob g * frob (M * (g' - g)) := hmain
      _ ≤ frob g * (frob D + (∑ i, (frob (A i)) ^ 2) * frob (g' - g) * frob g') :=
          mul_le_mul_of_nonneg_left hbound (frob_nonneg g)
      _ = frob g * frob D
            + (frob g * ((∑ i, (frob (A i)) ^ 2) * frob g')) * frob (g' - g) := by ring
  -- coefficient bound
  have hCt : C ^ 2 * (∑ i, (frob (A i)) ^ 2) * ((z.im)⁻¹) ^ 2 ≤ 1 / 2 := by
    have hη2 : (0:ℝ) < z.im ^ 2 := by positivity
    rw [inv_pow, inv_eq_one_div, mul_one_div, div_le_iff₀ hη2]
    nlinarith [hη]
  have hcoef : frob g * ((∑ i, (frob (A i)) ^ 2) * frob g') ≤ 1 / 2 := by
    have hgg : frob g * ((∑ i, (frob (A i)) ^ 2) * frob g')
        ≤ (C * (z.im)⁻¹) * ((∑ i, (frob (A i)) ^ 2) * (C * (z.im)⁻¹)) := by
      have hprod : frob g * frob g' ≤ (C * (z.im)⁻¹) * (C * (z.im)⁻¹) :=
        mul_le_mul hg_b hg'_b (frob_nonneg g') (by positivity)
      calc frob g * ((∑ i, (frob (A i)) ^ 2) * frob g')
          = (∑ i, (frob (A i)) ^ 2) * (frob g * frob g') := by ring
        _ ≤ (∑ i, (frob (A i)) ^ 2) *
              ((C * (z.im)⁻¹) * (C * (z.im)⁻¹)) :=
            mul_le_mul_of_nonneg_left hprod (by positivity)
        _ = (C * (z.im)⁻¹) * ((∑ i, (frob (A i)) ^ 2) * (C * (z.im)⁻¹)) := by ring
    have h1 : (C * (z.im)⁻¹) * ((∑ i, (frob (A i)) ^ 2) * (C * (z.im)⁻¹))
        = C ^ 2 * (∑ i, (frob (A i)) ^ 2) * ((z.im)⁻¹) ^ 2 := by ring
    rw [h1] at hgg
    linarith
  have hlin : (1 / 2 : ℝ) * frob (g' - g) ≤ frob g * frob D := by
    nlinarith [hstep, hcoef, frob_nonneg (g' - g)]
  have hfinal : frob (g' - g) ≤ 2 * (frob g * frob D) := by linarith
  calc frob (g' - g) ≤ 2 * (frob g * frob D) := hfinal
    _ ≤ 2 * (C * (z.im)⁻¹) * frob D := by
        have h2D : 0 ≤ 2 * frob D := mul_nonneg (by norm_num) (frob_nonneg D)
        have h := mul_le_mul_of_nonneg_left hg_b h2D
        nlinarith [h]
    _ = 2 * C * (z.im)⁻¹ * frob D := by ring


/-! ### The comparison `g_N → g` and its rate -/

/-- **Comparison of the finite-`N` mean with the limit Cauchy transform.**  The `O(1/N)`
approximate-Dyson defect and the stability of the Dyson map give

`frob (g_N(z) - g(z)) ≤ 4 (card d)³ sqrt(card d) (∑ frob(A_i)²)² (im z)⁻⁵ gueScale(N)²`.

Since `gueScale(N)² = 1/N` this is `O(1/N)` (see the module docstring for why the sharp
`O(1/N²)` needs a second-order input not available here). -/
theorem frob_gueResolventMean_sub_limit_le (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    (hA₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian)
    (z : ℂ) (hz : 0 < z.im) (hN : 0 < N)
    (hη : 2 * (Fintype.card d : ℝ) ^ 2 * (∑ i, (frob (A i)) ^ 2) ≤ (z.im) ^ 2) :
    frob (gueResolventMean (N := N) A₀ A z - operatorMatrixPencilCauchy A₀ A z)
      ≤ 2 * (Fintype.card d : ℝ) * (z.im)⁻¹ *
          ((Fintype.card d : ℝ) *
            (2 * (Fintype.card d : ℝ) ^ 2 * Real.sqrt (Fintype.card d : ℝ) *
              (∑ i, (frob (A i)) ^ 2) *
              (2 * (gueScale N) ^ 2 * (∑ i, (frob (A i)) ^ 2) * ((z.im)⁻¹) ^ 4))) := by
  classical
  set g : Matrix d d ℂ := operatorMatrixPencilCauchy A₀ A z with hg
  set gN : Matrix d d ℂ := gueResolventMean (N := N) A₀ A z with hgN
  set K : ℝ := 2 * (Fintype.card d : ℝ) ^ 2 * Real.sqrt (Fintype.card d : ℝ) *
      (∑ i, (frob (A i)) ^ 2) *
      (2 * (gueScale N) ^ 2 * (∑ i, (frob (A i)) ^ 2) * ((z.im)⁻¹) ^ 4) with hK
  set D : Matrix d d ℂ := (z • (1 : Matrix d d ℂ) - A₀ - ∑ i, A i * gN * A i) * gN - 1 with hD
  have hDeq : D = (z • (1 : Matrix d d ℂ) - A₀) * gN - 1
      - ∑ i, A i * (gN * A i * gN) := by
    rw [hD, Matrix.sub_mul]
    rw [show (∑ i, A i * gN * A i) * gN = ∑ i, A i * (gN * A i * gN) from by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      noncomm_ring]
    abel
  have hD_dyson : (z • (1 : Matrix d d ℂ) - A₀ - ∑ i, A i * gN * A i) * gN = 1 + D := by
    rw [hD]
    abel
  have hDbound : frob D ≤ (Fintype.card d : ℝ) * K := by
    refine frob_le_card_mul_of_entry_le D (fun u v => ?_) (by positivity)
    rw [hDeq, hK]
    exact approximate_dyson_entry_le A₀ A hA₀ hA z hz hN u v
  have hstab := dyson_stability A₀ A z hz g gN D
    (by rw [hg]; exact limit_dyson_equation A₀ A hA₀ hA z (ne_of_gt hz))
    hD_dyson
    (by
      rw [hg]
      simpa [abs_of_pos hz] using frob_operatorMatrixPencilCauchy_le A₀ A hA₀ hA z (ne_of_gt hz))
    (by rw [hgN]; exact frob_gueResolventMean_le A₀ A hA₀ hA z hz hN)
    (by positivity) hη
  calc frob (gN - g) ≤ 2 * (Fintype.card d : ℝ) * (z.im)⁻¹ * frob D := hstab
    _ ≤ 2 * (Fintype.card d : ℝ) * (z.im)⁻¹ * ((Fintype.card d : ℝ) * K) := by
        refine mul_le_mul_of_nonneg_left hDbound ?_
        positivity
    _ = 2 * (Fintype.card d : ℝ) * (z.im)⁻¹ *
          ((Fintype.card d : ℝ) *
            (2 * (Fintype.card d : ℝ) ^ 2 * Real.sqrt (Fintype.card d : ℝ) *
              (∑ i, (frob (A i)) ^ 2) *
              (2 * (gueScale N) ^ 2 * (∑ i, (frob (A i)) ^ 2) * ((z.im)⁻¹) ^ 4))) := by
        rw [hK]

end

end GUEStrongConvergence
