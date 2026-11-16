/-
# Exact finite-`N` Gaussian Schwinger--Dyson (master) identity for the GUE pencil

This file proves the first milestone of HT05 Theorem 5.7: the **exact finite-`N`**
Gaussian integration-by-parts identity satisfied by the averaged partial trace of the
GUE-pencil resolvent.

## Normalization (exactly as in the repository)

For fixed coefficient dimension `d` and matrix size `N`, the random affine pencil is

`H(x) = A₀ ⊗ I_N + ∑ i, A_i ⊗ G_i(x)`,  `G_i(x)_{ab} = (gueScale N) * (α x_{i,(a,b)} + β x_{i,(b,a)})`,

with `α = (1 - I)/2`, `β = (1 + I)/2`, `gueScale N = N^{-1/2}`, and `x` standard Gaussian
on `EuclideanSpace ℝ (GUECoord ι N)`.  The covariance is

`E[(G_i)_{ab} (G_j)_{cd}] = δ_{ij} δ_{ad} δ_{bc} / N`  (`integral_gueMatrix_mul`).

The resolvent is `R(z,x) = (z • 1 - H(x))⁻¹` (the genuine inverse in the C-star algebra of
matrices with the operator norm), the partial trace is

`T_N(z,x) = (id_d ⊗ tr_N) R(z,x)`,  `T_N(z,x)_{uv} = N⁻¹ ∑ k, R(z,x)_{(u,k),(v,k)}`,

and `g_N(z) = E[T_N(z,·)]` (`gueResolventMean`).

## What is proved here

1. The scalar single-GUE warm-up (`single_gue_schwinger_dyson`):
   for the single normalized GUE matrix `H = G` and `T = N⁻¹ tr R`,

   `z * E[T] - 1 = E[T * T]`.

2. The matrix-valued pencil identity (`gue_dyson_master_identity`):

   `(z • 1 - A₀) * g_N(z) - 1 = ∑ i, A_i * E[T_N(z) * A_i * T_N(z)]`,

   with **exact finite-`N`** quadratic term `E[T_N A_i T_N]` (not `g_N A_i g_N`).

The second identity is the exact finite-`N` form of the Dyson equation; it reduces to
`lean-free-prob`'s deterministic limit Dyson equation only after the (unproved here)
concentration/averaging comparison `E[T A_i T] → g A_i g`.

## Hypotheses of HT05 (5.7) that are **not** used

No averaging of the coefficient matrices is performed, no concentration of `T_N` around
`g_N` is assumed or proved, and **no comparison bound of order `N^{-2}` is assumed**.
The identity is an exact algebraic consequence of the Gaussian integration by parts, valid
for every `N` and every nonreal `z`.

Everything is stated for the actual finite random matrices; no formal Dyson relation and no
matrix identity `d/dt f(H + tK) = f'(H) K` is used (the coordinate derivative of the resolvent
is proved from the exact second-resolvent identity `guePencilResolvent_sub`).
-/
import GUEStrongConvergence.Probability.AveragedResolvent
import GUEStrongConvergence.Probability.ResolventPencilPairing

open MeasureTheory ProbabilityTheory Matrix Kronecker Filter
open scoped Matrix.Norms.Elementwise ComplexOrder ENNReal NNReal Topology

set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000

namespace GUEStrongConvergence

noncomputable section

variable {ι d : Type*} {N : ℕ} [Fintype ι] [Fintype d] [DecidableEq d] [DecidableEq ι]

/-! ### Analytic infrastructure: the coordinate Stein identity for bounded observables -/

/-- `piRecon p t y` is the pointwise update of `piRecon p 0 y` at `p`. -/
lemma piRecon_eq_update {κ : Type*} [DecidableEq κ] (p : κ)
    (y : {i : κ // ¬ i = p} → ℝ) (t : ℝ) :
    piRecon p t y = Function.update (piRecon p 0 y) p t := by
  funext i
  by_cases h : i = p
  · subst h
    simp [piRecon]
  · rw [Function.update_of_ne h]
    simp [piRecon, h]

/-- Continuity of a resolvent entry on the Euclidean Gaussian space. -/
lemma continuous_guePencilResolvent_entry_euclid (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    (hA₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian)
    (z : ℂ) (hz : z.im ≠ 0) (a b : d × Fin N) :
    Continuous (fun y : EuclideanSpace ℝ (GUECoord ι N) =>
      guePencilResolvent A₀ A (y : GUECoord ι N → ℝ) z a b) := by
  have hraw := (CStarMatrix.ofMatrixL : Matrix (d × Fin N) (d × Fin N) ℂ ≃L[ℂ]
      CStarMatrix (d × Fin N) (d × Fin N) ℂ).symm.continuous.comp
      (continuous_guePencilResolvent (N := N) A₀ A hA₀ hA z hz)
  exact (continuous_apply b).comp ((continuous_apply a).comp hraw)

/-- Continuity of a resolvent entry along the coordinate decomposition `piRecon p · y`. -/
lemma continuous_guePencilResolvent_entry_piRecon (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    (hA₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian)
    (z : ℂ) (hz : z.im ≠ 0) (p : GUECoord ι N) (a b : d × Fin N) :
    Continuous (fun w : ({i : GUECoord ι N // ¬ i = p} → ℝ) × ℝ =>
      guePencilResolvent A₀ A (piRecon p w.2 w.1) z a b) := by
  have hentry := continuous_guePencilResolvent_entry_euclid A₀ A hA₀ hA z hz a b
  have hpi : Continuous (fun w : ({i : GUECoord ι N // ¬ i = p} → ℝ) × ℝ =>
      (piRecon p w.2 w.1 : GUECoord ι N → ℝ)) := by
    apply continuous_pi
    intro q
    by_cases hq : q = p
    · subst hq
      simpa [piRecon] using continuous_snd
    · have hfun : (fun w : ({i : GUECoord ι N // ¬ i = p} → ℝ) × ℝ =>
          piRecon p w.2 w.1 q) = fun w => w.1 ⟨q, hq⟩ := by
        funext w
        simp [piRecon, hq]
      rw [hfun]
      exact (continuous_apply _).comp continuous_fst
  have hpath : Continuous (fun w : ({i : GUECoord ι N // ¬ i = p} → ℝ) × ℝ =>
      (WithLp.toLp 2 (piRecon p w.2 w.1) : EuclideanSpace ℝ (GUECoord ι N))) :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : GUECoord ι N => ℝ)).symm.continuous.comp hpi
  have := hentry.comp hpath
  simpa [Function.comp_def, WithLp.ofLp_toLp] using this

lemma continuous_gaussianPDFReal_zero_one : Continuous (fun t : ℝ => gaussianPDFReal 0 1 t) := by
  rw [gaussianPDFReal_def]
  fun_prop

/-- Decay of `ρ(t) • g(t)` at `-∞` for bounded `g`. -/
lemma tendsto_gaussianPDFReal_smul_bounded_atBot {g : ℝ → ℂ} {C : ℝ}
    (hg : ∀ t, ‖g t‖ ≤ C) :
    Tendsto (fun t : ℝ => gaussianPDFReal 0 1 t • g t) atBot (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hbound : ∀ t : ℝ, ‖gaussianPDFReal 0 1 t • g t‖
      ≤ C * (gaussianPDFReal 0 1 t * t ^ 0) := by
    intro t
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (gaussianPDFReal_nonneg 0 1 t),
      pow_zero, mul_one]
    calc gaussianPDFReal 0 1 t * ‖g t‖
        ≤ gaussianPDFReal 0 1 t * C :=
          mul_le_mul_of_nonneg_left (hg t) (gaussianPDFReal_nonneg 0 1 t)
      _ = C * gaussianPDFReal 0 1 t := by ring
  refine squeeze_zero (fun t => norm_nonneg _) (fun t => hbound t) ?_
  simpa using (tendsto_gaussianPDFReal_mul_pow_atBot 0).const_mul C

/-- Decay of `ρ(t) • g(t)` at `+∞` for bounded `g`. -/
lemma tendsto_gaussianPDFReal_smul_bounded_atTop {g : ℝ → ℂ} {C : ℝ}
    (hg : ∀ t, ‖g t‖ ≤ C) :
    Tendsto (fun t : ℝ => gaussianPDFReal 0 1 t • g t) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hbound : ∀ t : ℝ, ‖gaussianPDFReal 0 1 t • g t‖
      ≤ C * (gaussianPDFReal 0 1 t * t ^ 0) := by
    intro t
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (gaussianPDFReal_nonneg 0 1 t),
      pow_zero, mul_one]
    calc gaussianPDFReal 0 1 t * ‖g t‖
        ≤ gaussianPDFReal 0 1 t * C :=
          mul_le_mul_of_nonneg_left (hg t) (gaussianPDFReal_nonneg 0 1 t)
      _ = C * gaussianPDFReal 0 1 t := by ring
  refine squeeze_zero (fun t => norm_nonneg _) (fun t => hbound t) ?_
  simpa using (tendsto_gaussianPDFReal_mul_pow_atTop 0).const_mul C

/-- **Coordinate Stein identity for a bounded ℂ-valued observable.**  All analytic hypotheses
(integrability and decay) are discharged from uniform bounds. -/
theorem integral_eval_smul_stdGaussian_of_bounded {κ : Type*} [Fintype κ] [DecidableEq κ]
    (p : κ) {F F' : EuclideanSpace ℝ κ → ℂ} {C C' : ℝ}
    (hderiv : ∀ (y : {i : κ // ¬ i = p} → ℝ) (a : ℝ),
      HasDerivAt (fun t => F (WithLp.toLp 2 (piRecon p t y)))
        (F' (WithLp.toLp 2 (piRecon p a y))) a)
    (hFmeas : Continuous (fun w : ({i : κ // ¬ i = p} → ℝ) × ℝ =>
      F (WithLp.toLp 2 (piRecon p w.2 w.1))))
    (hF'meas : Continuous (fun w : ({i : κ // ¬ i = p} → ℝ) × ℝ =>
      F' (WithLp.toLp 2 (piRecon p w.2 w.1))))
    (hFbound : ∀ (w : ({i : κ // ¬ i = p} → ℝ) × ℝ),
      ‖F (WithLp.toLp 2 (piRecon p w.2 w.1))‖ ≤ C)
    (hF'bound : ∀ (w : ({i : κ // ¬ i = p} → ℝ) × ℝ),
      ‖F' (WithLp.toLp 2 (piRecon p w.2 w.1))‖ ≤ C') :
    ∫ x : EuclideanSpace ℝ κ, x p • F x ∂(stdGaussian (EuclideanSpace ℝ κ))
      = ∫ x : EuclideanSpace ℝ κ, F' x ∂(stdGaussian (EuclideanSpace ℝ κ)) := by
  have hint₁ : Integrable (fun w : ({i : κ // ¬ i = p} → ℝ) × ℝ =>
      gaussianPDFReal 0 1 w.2 • F' (WithLp.toLp 2 (piRecon p w.2 w.1)))
      ((Measure.pi (fun _ : {i : κ // ¬ i = p} => gaussianReal 0 1)).prod
        (volume : Measure ℝ)) := by
    refine Integrable.mono'
      ((Integrable.mul_prod (integrable_const (1:ℝ))
        (integrable_gaussianPDFReal_mul_pow 0)).const_mul C') ?_ ?_
    · exact ((continuous_gaussianPDFReal_zero_one.comp continuous_snd).smul hF'meas
        |>.aestronglyMeasurable)
    · filter_upwards with w
      have hρ := gaussianPDFReal_nonneg 0 1 w.2
      have h1 : ‖gaussianPDFReal 0 1 w.2 • F' (WithLp.toLp 2 (piRecon p w.2 w.1))‖
          = gaussianPDFReal 0 1 w.2 * ‖F' (WithLp.toLp 2 (piRecon p w.2 w.1))‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hρ]
      rw [h1, pow_zero, mul_one]
      calc gaussianPDFReal 0 1 w.2 * ‖F' (WithLp.toLp 2 (piRecon p w.2 w.1))‖
          ≤ gaussianPDFReal 0 1 w.2 * C' := mul_le_mul_of_nonneg_left (hF'bound w) hρ
        _ = C' * (1 * gaussianPDFReal 0 1 w.2) := by ring
  have hint₂ : Integrable (fun w : ({i : κ // ¬ i = p} → ℝ) × ℝ =>
      w.2 • (gaussianPDFReal 0 1 w.2 • F (WithLp.toLp 2 (piRecon p w.2 w.1))))
      ((Measure.pi (fun _ : {i : κ // ¬ i = p} => gaussianReal 0 1)).prod
        (volume : Measure ℝ)) := by
    refine Integrable.mono'
      ((Integrable.mul_prod (integrable_const (1:ℝ))
        ((integrable_gaussianPDFReal_mul_pow 1).abs)).const_mul C) ?_ ?_
    · exact ((by fun_prop : Continuous fun w : ({i : κ // ¬ i = p} → ℝ) × ℝ => w.2).smul
        ((continuous_gaussianPDFReal_zero_one.comp continuous_snd).smul hFmeas)
        |>.aestronglyMeasurable)
    · filter_upwards with w
      have hρ := gaussianPDFReal_nonneg 0 1 w.2
      calc ‖w.2 • (gaussianPDFReal 0 1 w.2 • F (WithLp.toLp 2 (piRecon p w.2 w.1)))‖
          = |w.2| * gaussianPDFReal 0 1 w.2 *
              ‖F (WithLp.toLp 2 (piRecon p w.2 w.1))‖ := by
            rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
              abs_of_nonneg hρ]
            ring
        _ ≤ |w.2| * gaussianPDFReal 0 1 w.2 * C := by
            refine mul_le_mul_of_nonneg_left (hFbound w) (by positivity)
        _ = C * (1 * |gaussianPDFReal 0 1 w.2 * w.2 ^ 1|) := by
            rw [pow_one, abs_mul, abs_of_nonneg hρ, one_mul]
            ring
  refine integral_eval_smul_stdGaussian p hderiv hint₁ hint₂ ?_ ?_
  · filter_upwards with y
    exact tendsto_gaussianPDFReal_smul_bounded_atBot (fun t => hFbound (y, t))
  · filter_upwards with y
    exact tendsto_gaussianPDFReal_smul_bounded_atTop (fun t => hFbound (y, t))

/-! ### Integrability of resolvent entries -/

/-- Every resolvent entry is integrable against the Gaussian measure. -/
lemma integrable_guePencilResolvent_entry_euclid (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    (hA₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian)
    (z : ℂ) (hz : z.im ≠ 0) (a b : d × Fin N) :
    Integrable (fun x : EuclideanSpace ℝ (GUECoord ι N) =>
      guePencilResolvent A₀ A (x : GUECoord ι N → ℝ) z a b)
      (stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) := by
  refine Integrable.of_bound
    (continuous_guePencilResolvent_entry_euclid A₀ A hA₀ hA z hz a b).aestronglyMeasurable
    (|z.im|⁻¹) ?_
  filter_upwards with x
  exact CStarMatrix.norm_entry_le_norm.trans (norm_guePencilResolvent_le A₀ A hA₀ hA _ z hz)


/-! ### The entrywise Gaussian integration-by-parts identity -/

/-- Continuity of a directional-derivative entry of the resolvent, `(R D_p R)_{ab}`, on the
Euclidean Gaussian space. -/
lemma continuous_guePencilResolvent_direction_entry_euclid
    (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    (hA₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian)
    (z : ℂ) (hz : z.im ≠ 0) (p : GUECoord ι N) (a b : d × Fin N) :
    Continuous (fun y : EuclideanSpace ℝ (GUECoord ι N) =>
      (guePencilResolvent A₀ A (y : GUECoord ι N → ℝ) z * guePencilDirection A p *
        guePencilResolvent A₀ A (y : GUECoord ι N → ℝ) z) a b) := by
  have hsum : Continuous (fun y : EuclideanSpace ℝ (GUECoord ι N) =>
      ∑ r : d × Fin N, ∑ s : d × Fin N,
        guePencilResolvent A₀ A (y : GUECoord ι N → ℝ) z a r *
          guePencilDirection A p r s *
          guePencilResolvent A₀ A (y : GUECoord ι N → ℝ) z s b) :=
    continuous_finsetSum _ fun r _ => continuous_finsetSum _ fun s _ =>
      ((continuous_guePencilResolvent_entry_euclid A₀ A hA₀ hA z hz a r).mul
        continuous_const).mul
        (continuous_guePencilResolvent_entry_euclid A₀ A hA₀ hA z hz s b)
  refine hsum.congr fun y => ?_
  rw [cstar_mul_mul_apply (guePencilResolvent A₀ A (y : GUECoord ι N → ℝ) z)
    (guePencilDirection A p) (guePencilResolvent A₀ A (y : GUECoord ι N → ℝ) z) a b]

/-- The sparse form of `(R D_p R)_{ab}` for a GUE coordinate direction
`p = (i,(k,m))`: only the two slices `k` and `m` occur. -/
lemma resolvent_direction_entry (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    (x : GUECoord ι N → ℝ) (z : ℂ) (i : ι) (k m : Fin N) (a b : d × Fin N) :
    (guePencilResolvent A₀ A x z * guePencilDirection A (i, (k, m)) *
        guePencilResolvent A₀ A x z) a b
      = (gueScale N : ℂ) *
        (gueAlpha * (∑ s : d, ∑ t : d,
            guePencilResolvent A₀ A x z a (s, k) * A i s t *
              guePencilResolvent A₀ A x z (t, m) b) +
          gueBeta * (∑ s : d, ∑ t : d,
            guePencilResolvent A₀ A x z a (s, m) * A i s t *
              guePencilResolvent A₀ A x z (t, k) b)) := by
  rw [cstar_mul_mul_apply]
  rw [direction_pairing_eq A (fun r => guePencilResolvent A₀ A x z a r)
    (fun r => guePencilResolvent A₀ A x z r b) (i, (k, m))]
  simp only [← Finset.mul_sum]
  ring

/-- **The Gaussian integration-by-parts identity for one GUE entry of the pencil.**

For every coordinate `(k,m)` of `G_i`,
`∫ G_i[k,m] R_{(u,m),(v,k)} = gueScale² ∑_{s,t} A_i[s,t] ∫ R_{(u,m),(s,m)} R_{(t,k),(v,k)}`.

The coefficient `gueScale² = 1/N` and the collapse of the two `α,β` contributions to
`α² + β² = 0`, `2αβ = 1` are the exact GUE normalization. -/
theorem integral_gueMatrix_mul_resolvent_entry (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    (hA₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian)
    (z : ℂ) (hz : z.im ≠ 0) (i : ι) (k m : Fin N) (u v : d) :
    ∫ x, gueMatrix (x : GUECoord ι N → ℝ) i k m *
        guePencilResolvent A₀ A (x : GUECoord ι N → ℝ) z (u, m) (v, k)
        ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))
      = (gueScale N : ℂ) ^ 2 * ∑ s : d, ∑ t : d, A i s t *
          ∫ x, guePencilResolvent A₀ A (x : GUECoord ι N → ℝ) z (u, m) (s, m) *
              guePencilResolvent A₀ A (x : GUECoord ι N → ℝ) z (t, k) (v, k)
            ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) := by
  classical
  set p1 : GUECoord ι N := (i, (k, m))
  set p2 : GUECoord ι N := (i, (m, k))
  set F : EuclideanSpace ℝ (GUECoord ι N) → ℂ := fun x =>
    guePencilResolvent A₀ A (x : GUECoord ι N → ℝ) z (u, m) (v, k) with hF
  set F1 : EuclideanSpace ℝ (GUECoord ι N) → ℂ := fun x =>
    (guePencilResolvent A₀ A (x : GUECoord ι N → ℝ) z *
      guePencilDirection A p1 * guePencilResolvent A₀ A (x : GUECoord ι N → ℝ) z)
        (u, m) (v, k) with hF1
  set F2 : EuclideanSpace ℝ (GUECoord ι N) → ℂ := fun x =>
    (guePencilResolvent A₀ A (x : GUECoord ι N → ℝ) z *
      guePencilDirection A p2 * guePencilResolvent A₀ A (x : GUECoord ι N → ℝ) z)
        (u, m) (v, k) with hF2
  have hRbound : ∀ (x : EuclideanSpace ℝ (GUECoord ι N)) (a b : d × Fin N),
      ‖guePencilResolvent A₀ A (x : GUECoord ι N → ℝ) z a b‖ ≤ |z.im|⁻¹ := by
    intro x a b
    exact CStarMatrix.norm_entry_le_norm.trans (norm_guePencilResolvent_le A₀ A hA₀ hA _ z hz)
  have hDbdd : ∀ x : EuclideanSpace ℝ (GUECoord ι N), ‖F1 x‖
      ≤ |z.im|⁻¹ ^ 2 * ‖guePencilDirection A p1‖ := by
    intro x
    have hR1 : ‖guePencilResolvent A₀ A (x : _) z‖ ≤ |z.im|⁻¹ :=
      norm_guePencilResolvent_le A₀ A hA₀ hA _ z hz
    show ‖(guePencilResolvent A₀ A (x : _) z * guePencilDirection A p1 *
          guePencilResolvent A₀ A (x : _) z) (u, m) (v, k)‖ ≤ _
    calc ‖(guePencilResolvent A₀ A (x : _) z * guePencilDirection A p1 *
          guePencilResolvent A₀ A (x : _) z) (u, m) (v, k)‖
        ≤ ‖guePencilResolvent A₀ A (x : _) z * guePencilDirection A p1 *
            guePencilResolvent A₀ A (x : _) z‖ := CStarMatrix.norm_entry_le_norm
      _ ≤ ‖guePencilResolvent A₀ A (x : _) z * guePencilDirection A p1‖ *
            ‖guePencilResolvent A₀ A (x : _) z‖ := norm_mul_le _ _
      _ ≤ (‖guePencilResolvent A₀ A (x : _) z‖ * ‖guePencilDirection A p1‖) *
            ‖guePencilResolvent A₀ A (x : _) z‖ := by
          exact mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
      _ ≤ (|z.im|⁻¹ * ‖guePencilDirection A p1‖) * |z.im|⁻¹ := by
          refine mul_le_mul ?_ hR1 (norm_nonneg _) (by positivity)
          exact mul_le_mul_of_nonneg_right hR1 (norm_nonneg _)
      _ = |z.im|⁻¹ ^ 2 * ‖guePencilDirection A p1‖ := by ring
  have hDbdd2 : ∀ x : EuclideanSpace ℝ (GUECoord ι N), ‖F2 x‖
      ≤ |z.im|⁻¹ ^ 2 * ‖guePencilDirection A p2‖ := by
    intro x
    have hR1 : ‖guePencilResolvent A₀ A (x : _) z‖ ≤ |z.im|⁻¹ :=
      norm_guePencilResolvent_le A₀ A hA₀ hA _ z hz
    show ‖(guePencilResolvent A₀ A (x : _) z * guePencilDirection A p2 *
          guePencilResolvent A₀ A (x : _) z) (u, m) (v, k)‖ ≤ _
    calc ‖(guePencilResolvent A₀ A (x : _) z * guePencilDirection A p2 *
          guePencilResolvent A₀ A (x : _) z) (u, m) (v, k)‖
        ≤ ‖guePencilResolvent A₀ A (x : _) z * guePencilDirection A p2 *
            guePencilResolvent A₀ A (x : _) z‖ := CStarMatrix.norm_entry_le_norm
      _ ≤ ‖guePencilResolvent A₀ A (x : _) z * guePencilDirection A p2‖ *
            ‖guePencilResolvent A₀ A (x : _) z‖ := norm_mul_le _ _
      _ ≤ (‖guePencilResolvent A₀ A (x : _) z‖ * ‖guePencilDirection A p2‖) *
            ‖guePencilResolvent A₀ A (x : _) z‖ := by
          exact mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
      _ ≤ (|z.im|⁻¹ * ‖guePencilDirection A p2‖) * |z.im|⁻¹ := by
          refine mul_le_mul ?_ hR1 (norm_nonneg _) (by positivity)
          exact mul_le_mul_of_nonneg_right hR1 (norm_nonneg _)
      _ = |z.im|⁻¹ ^ 2 * ‖guePencilDirection A p2‖ := by ring
  -- continuity of `F` and of the two directional derivatives along `piRecon`
  have hFcont : ∀ p : GUECoord ι N,
      Continuous (fun w : ({j : GUECoord ι N // ¬ j = p} → ℝ) × ℝ =>
        F (WithLp.toLp 2 (piRecon p w.2 w.1))) := by
    intro p
    have := continuous_guePencilResolvent_entry_piRecon A₀ A hA₀ hA z hz p (u, m) (v, k)
    simpa only [F, WithLp.ofLp_toLp] using this
  have hF1cont : ∀ p : GUECoord ι N,
      Continuous (fun w : ({j : GUECoord ι N // ¬ j = p} → ℝ) × ℝ =>
        F1 (WithLp.toLp 2 (piRecon p w.2 w.1))) := by
    intro p
    have hsum : Continuous (fun w : ({j : GUECoord ι N // ¬ j = p} → ℝ) × ℝ =>
        ∑ r : d × Fin N, ∑ s : d × Fin N,
          guePencilResolvent A₀ A (piRecon p w.2 w.1) z (u, m) r *
            guePencilDirection A p1 r s *
            guePencilResolvent A₀ A (piRecon p w.2 w.1) z s (v, k)) :=
      continuous_finsetSum _ fun r _ => continuous_finsetSum _ fun s _ =>
        ((continuous_guePencilResolvent_entry_piRecon A₀ A hA₀ hA z hz p (u, m) r).mul
          continuous_const).mul
          (continuous_guePencilResolvent_entry_piRecon A₀ A hA₀ hA z hz p s (v, k))
    refine hsum.congr fun w => ?_
    show _ = F1 (WithLp.toLp 2 (piRecon p w.2 w.1))
    rw [hF1]
    simp only [WithLp.ofLp_toLp]
    rw [cstar_mul_mul_apply (guePencilResolvent A₀ A (piRecon p w.2 w.1) z)
      (guePencilDirection A p1) (guePencilResolvent A₀ A (piRecon p w.2 w.1) z)
      (u, m) (v, k)]
  have hF2cont : ∀ p : GUECoord ι N,
      Continuous (fun w : ({j : GUECoord ι N // ¬ j = p} → ℝ) × ℝ =>
        F2 (WithLp.toLp 2 (piRecon p w.2 w.1))) := by
    intro p
    have hsum : Continuous (fun w : ({j : GUECoord ι N // ¬ j = p} → ℝ) × ℝ =>
        ∑ r : d × Fin N, ∑ s : d × Fin N,
          guePencilResolvent A₀ A (piRecon p w.2 w.1) z (u, m) r *
            guePencilDirection A p2 r s *
            guePencilResolvent A₀ A (piRecon p w.2 w.1) z s (v, k)) :=
      continuous_finsetSum _ fun r _ => continuous_finsetSum _ fun s _ =>
        ((continuous_guePencilResolvent_entry_piRecon A₀ A hA₀ hA z hz p (u, m) r).mul
          continuous_const).mul
          (continuous_guePencilResolvent_entry_piRecon A₀ A hA₀ hA z hz p s (v, k))
    refine hsum.congr fun w => ?_
    show _ = F2 (WithLp.toLp 2 (piRecon p w.2 w.1))
    rw [hF2]
    simp only [WithLp.ofLp_toLp]
    rw [cstar_mul_mul_apply (guePencilResolvent A₀ A (piRecon p w.2 w.1) z)
      (guePencilDirection A p2) (guePencilResolvent A₀ A (piRecon p w.2 w.1) z)
      (u, m) (v, k)]
  have hstein1 : ∫ x, x p1 • F x ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))
      = ∫ x, F1 x ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) := by
    refine integral_eval_smul_stdGaussian_of_bounded (C := |z.im|⁻¹)
      (C' := |z.im|⁻¹ ^ 2 * ‖guePencilDirection A p1‖) p1 ?_ ?_ ?_ ?_ ?_
    · intro y a
      have h := hasDerivAt_guePencilResolvent_entry A₀ A hA₀ hA (piRecon p1 0 y) p1 z hz a
        (u, m) (v, k)
      convert h using 1
      · funext t
        simp only [F, WithLp.ofLp_toLp]
        rw [piRecon_eq_update p1 y t]
      · rw [hF1]
        simp only [WithLp.ofLp_toLp]
        rw [piRecon_eq_update p1 y a]
    · exact hFcont p1
    · exact hF1cont p1
    · intro w
      exact hRbound (WithLp.toLp 2 (piRecon p1 w.2 w.1)) (u, m) (v, k)
    · intro w
      exact hDbdd (WithLp.toLp 2 (piRecon p1 w.2 w.1))
  have hstein2 : ∫ x, x p2 • F x ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))
      = ∫ x, F2 x ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) := by
    refine integral_eval_smul_stdGaussian_of_bounded (C := |z.im|⁻¹)
      (C' := |z.im|⁻¹ ^ 2 * ‖guePencilDirection A p2‖) p2 ?_ ?_ ?_ ?_ ?_
    · intro y a
      have h := hasDerivAt_guePencilResolvent_entry A₀ A hA₀ hA (piRecon p2 0 y) p2 z hz a
        (u, m) (v, k)
      convert h using 1
      · funext t
        simp only [F, WithLp.ofLp_toLp]
        rw [piRecon_eq_update p2 y t]
      · rw [hF2]
        simp only [WithLp.ofLp_toLp]
        rw [piRecon_eq_update p2 y a]
    · exact hFcont p2
    · exact hF2cont p2
    · intro w
      exact hRbound (WithLp.toLp 2 (piRecon p2 w.2 w.1)) (u, m) (v, k)
    · intro w
      exact hDbdd2 (WithLp.toLp 2 (piRecon p2 w.2 w.1))
  -- pointwise expansion of the observable
  have hpt : ∀ x : EuclideanSpace ℝ (GUECoord ι N),
      gueMatrix (x : GUECoord ι N → ℝ) i k m * F x
        = (gueScale N : ℂ) *
            (gueAlpha * (x p1 • F x) + gueBeta * (x p2 • F x)) := by
    intro x
    rw [hF]
    simp only [gueMatrix, gueUnscaled, RCLike.real_smul_eq_coe_mul]
    norm_num [p1, p2]
    ring
  -- pointwise collapse of the two directional derivatives
  have hcoef : ∀ (X Y c : ℂ),
      gueAlpha * (c * (gueAlpha * X + gueBeta * Y)) +
        gueBeta * (c * (gueAlpha * Y + gueBeta * X)) = c * Y := by
    intro X Y c
    calc gueAlpha * (c * (gueAlpha * X + gueBeta * Y)) +
          gueBeta * (c * (gueAlpha * Y + gueBeta * X))
        = c * ((gueAlpha * gueAlpha + gueBeta * gueBeta) * X +
            (gueAlpha * gueBeta + gueBeta * gueAlpha) * Y) := by ring
      _ = c * Y := by
          rw [gueAlpha_mul_self_add_gueBeta_mul_self, gueAlpha_mul_gueBeta_add]
          ring
  have hcollapse : ∀ x : EuclideanSpace ℝ (GUECoord ι N),
      gueAlpha * F1 x + gueBeta * F2 x = (gueScale N : ℂ) *
        (∑ s : d, ∑ t : d, A i s t *
          (guePencilResolvent A₀ A (x : GUECoord ι N → ℝ) z (u, m) (s, m) *
            guePencilResolvent A₀ A (x : GUECoord ι N → ℝ) z (t, k) (v, k))) := by
    intro x
    rw [hF1, hF2]
    dsimp only
    simp only [p1, p2]
    rw [resolvent_direction_entry A₀ A _ z i k m (u, m) (v, k)]
    rw [resolvent_direction_entry A₀ A _ z i m k (u, m) (v, k)]
    rw [hcoef]
    congr 1
    refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t _ => ?_
    ring
  -- integrability
  have hintF : Integrable F (stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) := by
    rw [hF]
    exact integrable_guePencilResolvent_entry_euclid A₀ A hA₀ hA z hz (u, m) (v, k)
  have hprod : ∀ (a b c e : d × Fin N),
      Integrable (fun x : EuclideanSpace ℝ (GUECoord ι N) =>
        guePencilResolvent A₀ A (x : GUECoord ι N → ℝ) z a b *
          guePencilResolvent A₀ A (x : GUECoord ι N → ℝ) z c e)
        (stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) := by
    intro a b c e
    exact (integrable_guePencilResolvent_entry_euclid A₀ A hA₀ hA z hz a b).mul_bdd
      ((continuous_guePencilResolvent_entry_euclid A₀ A hA₀ hA z hz c e).aestronglyMeasurable)
      (ae_of_all _ fun x => CStarMatrix.norm_entry_le_norm.trans
        (norm_guePencilResolvent_le A₀ A hA₀ hA _ z hz))
  have hFcontinuous : Continuous F := by
    rw [hF]
    exact continuous_guePencilResolvent_entry_euclid A₀ A hA₀ hA z hz (u, m) (v, k)
  have hintF1 : Integrable F1 (stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) := by
    refine Integrable.of_bound ?_ (|z.im|⁻¹ ^ 2 * ‖guePencilDirection A p1‖)
      (ae_of_all _ hDbdd)
    rw [hF1]
    exact (continuous_guePencilResolvent_direction_entry_euclid A₀ A hA₀ hA z hz p1
      (u, m) (v, k)).aestronglyMeasurable
  have hintF2 : Integrable F2 (stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) := by
    refine Integrable.of_bound ?_ (|z.im|⁻¹ ^ 2 * ‖guePencilDirection A p2‖)
      (ae_of_all _ hDbdd2)
    rw [hF2]
    exact (continuous_guePencilResolvent_direction_entry_euclid A₀ A hA₀ hA z hz p2
      (u, m) (v, k)).aestronglyMeasurable
  have hint_smul : ∀ p : GUECoord ι N,
      Integrable (fun x : EuclideanSpace ℝ (GUECoord ι N) => x p • F x)
        (stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) := by
    intro p
    have hmaj : Integrable (fun x : EuclideanSpace ℝ (GUECoord ι N) =>
        |z.im|⁻¹ * (1 + (x p) ^ 2))
        (stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) := by
      have hsq : Integrable (fun x : EuclideanSpace ℝ (GUECoord ι N) => (x p) ^ 2)
          (stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) := by
        have h := MemLp.mul (p := 2) (q := 2) (r := 1)
          (memLp_coord (κ := GUECoord ι N) p) (memLp_coord (κ := GUECoord ι N) p)
        refine (memLp_one_iff_integrable.mp h).congr (ae_of_all _ fun x => ?_)
        simp [sq]
      exact ((integrable_const (1:ℝ)).add hsq).const_mul |z.im|⁻¹
    have hcont : Continuous (fun x : EuclideanSpace ℝ (GUECoord ι N) => x p • F x) :=
      (by fun_prop : Continuous fun x : EuclideanSpace ℝ (GUECoord ι N) => x p).smul hFcontinuous
    refine Integrable.mono' hmaj hcont.aestronglyMeasurable ?_
    · filter_upwards with x
      have hnorm : ‖x p • F x‖ = |x p| * ‖F x‖ := by
        rw [norm_smul, Real.norm_eq_abs]
      have hb : ‖F x‖ ≤ |z.im|⁻¹ := by
        rw [hF]
        exact CStarMatrix.norm_entry_le_norm.trans
          (norm_guePencilResolvent_le A₀ A hA₀ hA _ z hz)
      calc ‖x p • F x‖ = |x p| * ‖F x‖ := hnorm
        _ ≤ |x p| * |z.im|⁻¹ :=
            mul_le_mul_of_nonneg_left hb (abs_nonneg _)
        _ ≤ |z.im|⁻¹ * (1 + (x p) ^ 2) := by
            have h1 : |x p| ≤ 1 + (x p) ^ 2 := by
              rw [abs_le]
              constructor
              · nlinarith [sq_nonneg (x p + 1 / 2)]
              · nlinarith [sq_nonneg (x p - 1 / 2)]
            calc |x p| * |z.im|⁻¹ ≤ (1 + (x p) ^ 2) * |z.im|⁻¹ :=
                  mul_le_mul_of_nonneg_right h1 (by positivity)
              _ = |z.im|⁻¹ * (1 + (x p) ^ 2) := by ring
  -- assemble
  have hmain : ∫ x, gueMatrix (x : GUECoord ι N → ℝ) i k m * F x
      ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))
      = (gueScale N : ℂ) ^ 2 * ∑ s : d, ∑ t : d, A i s t *
          ∫ x, guePencilResolvent A₀ A (x : GUECoord ι N → ℝ) z (u, m) (s, m) *
              guePencilResolvent A₀ A (x : GUECoord ι N → ℝ) z (t, k) (v, k)
            ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) := by
    rw [show (∫ x, gueMatrix (x : GUECoord ι N → ℝ) i k m * F x
        ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N))))
        = ∫ x, (gueScale N : ℂ) *
            (gueAlpha * (x p1 • F x) + gueBeta * (x p2 • F x))
            ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) from
      integral_congr_ae (ae_of_all _ hpt)]
    rw [integral_const_mul]
    have hsplit : ∫ x, (gueAlpha * (x p1 • F x) + gueBeta * (x p2 • F x))
        ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))
        = gueAlpha * ∫ x, (x p1 • F x) ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))
          + gueBeta * ∫ x, (x p2 • F x) ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) := by
      rw [integral_add ((hint_smul p1).const_mul _) ((hint_smul p2).const_mul _),
        integral_const_mul, integral_const_mul]
    rw [hsplit, hstein1, hstein2]
    rw [show gueAlpha * (∫ x, F1 x ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N))))
          + gueBeta * (∫ x, F2 x ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N))))
        = ∫ x, (gueAlpha * F1 x + gueBeta * F2 x)
            ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) from by
      rw [integral_add (hintF1.const_mul _) (hintF2.const_mul _),
        integral_const_mul, integral_const_mul]]
    rw [show (∫ x, (gueAlpha * F1 x + gueBeta * F2 x)
        ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N))))
        = ∫ x, (gueScale N : ℂ) *
            (∑ s : d, ∑ t : d, A i s t *
              (guePencilResolvent A₀ A (x : GUECoord ι N → ℝ) z (u, m) (s, m) *
                guePencilResolvent A₀ A (x : GUECoord ι N → ℝ) z (t, k) (v, k)))
            ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) from
      integral_congr_ae (ae_of_all _ hcollapse)]
    rw [integral_const_mul]
    have hlin : (∫ x, (∑ s : d, ∑ t : d, A i s t *
          (guePencilResolvent A₀ A (x : GUECoord ι N → ℝ) z (u, m) (s, m) *
            guePencilResolvent A₀ A (x : GUECoord ι N → ℝ) z (t, k) (v, k)))
          ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N))))
        = ∑ s : d, ∑ t : d, A i s t *
          ∫ x, guePencilResolvent A₀ A (x : GUECoord ι N → ℝ) z (u, m) (s, m) *
              guePencilResolvent A₀ A (x : GUECoord ι N → ℝ) z (t, k) (v, k)
            ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) := by
      rw [integral_finsetSum]
      · refine Finset.sum_congr rfl fun s _ => ?_
        rw [integral_finsetSum]
        · refine Finset.sum_congr rfl fun t _ => ?_
          rw [integral_const_mul]
        · intro t _
          exact (hprod (u, m) (s, m) (t, k) (v, k)).const_mul (A i s t)
      · intro s _
        exact integrable_finsetSum _ fun t _ =>
          (hprod (u, m) (s, m) (t, k) (v, k)).const_mul (A i s t)
    rw [hlin]
    ring
  calc ∫ x, gueMatrix (x : GUECoord ι N → ℝ) i k m *
        guePencilResolvent A₀ A (x : GUECoord ι N → ℝ) z (u, m) (v, k)
        ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))
      = ∫ x, gueMatrix (x : GUECoord ι N → ℝ) i k m * F x
          ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) := by
        refine integral_congr_ae (ae_of_all _ fun x => ?_)
        rw [hF]
    _ = (gueScale N : ℂ) ^ 2 * ∑ s : d, ∑ t : d, A i s t *
          ∫ x, guePencilResolvent A₀ A (x : GUECoord ι N → ℝ) z (u, m) (s, m) *
              guePencilResolvent A₀ A (x : GUECoord ι N → ℝ) z (t, k) (v, k)
            ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) := hmain


/-- Entry formula for the affine pencil. -/
lemma guePencil_apply_entry (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    (x : GUECoord ι N → ℝ) (a b : d × Fin N) :
    guePencil A₀ A x a b =
      A₀ a.1 b.1 * (if a.2 = b.2 then 1 else 0) +
        ∑ i, A i a.1 b.1 * gueMatrix x i a.2 b.2 := by
  rw [guePencil, CStarMatrix.ofMatrix_apply, guePencilMatrix_apply]
  congr 1

/-- The partial trace of `H * R` splits into the deterministic part `A₀ * T` and the
random contributions of the individual GUE blocks. -/
lemma partialTraceN_guePencil_mul_resolvent (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    (hA₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian)
    (x : GUECoord ι N → ℝ) (z : ℂ) (hz : z.im ≠ 0) :
    partialTraceN (guePencil A₀ A x * guePencilResolvent A₀ A x z)
      = A₀ * guePartialTrace A₀ A z x +
        ∑ i, (Matrix.of fun u v => (N : ℂ)⁻¹ * ∑ k : Fin N, ∑ a : d, ∑ m : Fin N,
          A i u a * gueMatrix x i k m *
            guePencilResolvent A₀ A x z (a, m) (v, k)) := by
  ext u v
  rw [partialTraceN_apply]
  -- expand `(H * R) (u,k) (v,k)`
  have hexp : (∑ k : Fin N, (guePencil A₀ A x * guePencilResolvent A₀ A x z) (u,k) (v,k))
      = ∑ k : Fin N, ∑ a : d, ∑ m : Fin N,
          (A₀ u a * (if k = m then 1 else 0) + ∑ i, A i u a * gueMatrix x i k m) *
            guePencilResolvent A₀ A x z (a, m) (v, k) := by
    apply Finset.sum_congr rfl
    intro k _
    rw [CStarMatrix.mul_apply, Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro m _
    rw [guePencil_apply_entry]
  rw [hexp]
  simp only [add_mul, Finset.sum_add_distrib]
  rw [mul_add, Matrix.add_apply, Matrix.mul_apply, Matrix.sum_apply]
  congr 1
  · -- deterministic part
    have hcollapse : ∀ (k : Fin N) (a : d),
        (∑ m : Fin N, A₀ u a * (if k = m then (1:ℂ) else 0) *
            guePencilResolvent A₀ A x z (a, m) (v, k))
          = A₀ u a * guePencilResolvent A₀ A x z (a, k) (v, k) := by
      intro k a
      rw [Finset.sum_eq_single k]
      · simp
      · intro m _ hm
        rw [if_neg (Ne.symm hm)]
        ring
      · intro h
        simp at h
    simp only [hcollapse, guePartialTrace_apply, partialTraceN_apply]
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro k _
    ring
  · -- random part
    have hcollapse : ∀ (k : Fin N) (a : d),
        (∑ m : Fin N, (∑ i, A i u a * gueMatrix x i k m) *
            guePencilResolvent A₀ A x z (a, m) (v, k))
          = ∑ i, ∑ m, A i u a * gueMatrix x i k m *
              guePencilResolvent A₀ A x z (a, m) (v, k) := by
      intro k a
      simp only [Finset.sum_mul]
      rw [Finset.sum_comm]
    simp only [hcollapse]
    simp only [Finset.mul_sum]
    conv_lhs =>
      enter [2, k]
      rw [Finset.sum_comm]
    rw [Finset.sum_comm]
    rfl


/-- Reordering of a five-fold finite sum: from `(k,a,m,s,t)` to `(a,s,t,k,m)`. -/
lemma sum_reorder_five {α β γ δ ε : Type*} [Fintype α] [Fintype β] [Fintype γ]
    [Fintype δ] [Fintype ε] (F : α → β → γ → δ → ε → ℂ) :
    (∑ k : α, ∑ a : β, ∑ m : γ, ∑ s : δ, ∑ t : ε, F k a m s t)
      = ∑ a : β, ∑ s : δ, ∑ t : ε, ∑ k : α, ∑ m : γ, F k a m s t := by
  conv_lhs =>
    enter [2, k, 2, a]
    rw [Finset.sum_comm]
  conv_lhs =>
    enter [2, k, 2, a, 2, s]
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  conv_lhs =>
    enter [2, a]
    rw [Finset.sum_comm]
  conv_lhs =>
    enter [2, a, 2, s]
    rw [Finset.sum_comm]

/-- Reordering of a three-fold finite sum: from `(k,a,s)` to `(a,s,k)`. -/
lemma sum_reorder_three {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    (F : α → β → γ → ℂ) :
    (∑ k : α, ∑ a : β, ∑ s : γ, F k a s)
      = ∑ a : β, ∑ s : γ, ∑ k : α, F k a s := by
  rw [Finset.sum_comm]
  conv_lhs =>
    enter [2, a]
    rw [Finset.sum_comm]


/-- The normalized scale squared is `1/N` in `ℂ`. -/
lemma gueScale_sq_complex (N : ℕ) : (gueScale N : ℂ) ^ 2 = (N : ℂ)⁻¹ := by
  rw [sq, gueScale_mul_self_complex]
  norm_num

/-- The partial trace is additive in the matrix argument. -/
lemma partialTraceN_sub (M L : CStarMatrix (d × Fin N) (d × Fin N) ℂ) :
    partialTraceN (M - L) = partialTraceN M - partialTraceN L := by
  ext u v
  simp only [partialTraceN_apply, CStarMatrix.sub_apply, Matrix.sub_apply, sub_mul,
    mul_sub, Finset.sum_sub_distrib]

/-- The resolvent identity for the pencil: `(z - H(x)) R(z,x) = 1`. -/
lemma resolvent_mul_guePencil (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    (hA₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian)
    (x : GUECoord ι N → ℝ) (z : ℂ) (hz : z.im ≠ 0) :
    (algebraMap ℂ (CStarMatrix (d × Fin N) (d × Fin N) ℂ) z - guePencil A₀ A x) *
      guePencilResolvent A₀ A x z = 1 := by
  have hunit : IsUnit (algebraMap ℂ (CStarMatrix (d × Fin N) (d × Fin N) ℂ) z -
      guePencil A₀ A x) := guePencil_mem_resolventSet A₀ A hA₀ hA x z hz
  simpa [guePencilResolvent, resolvent] using Ring.mul_inverse_cancel _ hunit

/-- A GUE entry is square-integrable, hence integrable. -/
lemma memLp_gueMatrix_entry (i : ι) (k m : Fin N) :
    MemLp (fun x : EuclideanSpace ℝ (GUECoord ι N) =>
      gueMatrix (x : GUECoord ι N → ℝ) i k m) 2
      (stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) := by
  have h1 : MemLp (fun x : EuclideanSpace ℝ (GUECoord ι N) =>
      ((x (i, (k, m)) : ℝ) : ℂ)) 2 (stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) :=
    memLp_coord_complex (i, (k, m))
  have h2 : MemLp (fun x : EuclideanSpace ℝ (GUECoord ι N) =>
      ((x (i, (m, k)) : ℝ) : ℂ)) 2 (stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) :=
    memLp_coord_complex (i, (m, k))
  have h := ((h1.const_mul gueAlpha).add (h2.const_mul gueBeta)).const_mul (gueScale N : ℂ)
  refine MemLp.ae_eq (ae_of_all _ fun x => ?_) h
  simp only [gueMatrix, gueUnscaled, Pi.add_apply, Pi.mul_apply]

/-- A GUE entry is integrable against the Gaussian measure. -/
lemma integrable_gueMatrix_entry (i : ι) (k m : Fin N) :
    Integrable (fun x : EuclideanSpace ℝ (GUECoord ι N) =>
      gueMatrix (x : GUECoord ι N → ℝ) i k m)
      (stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) :=
  MemLp.integrable (by norm_num : (1:ℝ≥0∞) ≤ 2) (memLp_gueMatrix_entry i k m)

/-- Factoring a double sum of integrals of a product of one-variable functions. -/
lemma sum_sum_integral_mul {f g : EuclideanSpace ℝ (GUECoord ι N) → Fin N → ℂ}
    (hprod : ∀ k m, Integrable (fun x => f x m * g x k)
      (stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))) :
    (∑ k : Fin N, ∑ m : Fin N,
        ∫ x, f x m * g x k ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N))))
      = ∫ x, (∑ m, f x m) * (∑ k, g x k)
          ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) := by
  have step1 : (∑ k : Fin N, ∑ m : Fin N,
        ∫ x, f x m * g x k ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N))))
      = ∑ k : Fin N, ∫ x, (∑ m, f x m) * g x k
          ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) := by
    apply Finset.sum_congr rfl
    intro k _
    rw [← integral_finsetSum]
    · refine integral_congr_ae (ae_of_all _ fun x => ?_)
      dsimp only
      rw [← Finset.sum_mul]
    · intro m _
      exact hprod k m
  rw [step1]
  rw [← integral_finsetSum]
  · refine integral_congr_ae (ae_of_all _ fun x => ?_)
    dsimp only
    rw [Finset.mul_sum]
  · intro k _
    simpa only [Finset.sum_mul] using
      integrable_finsetSum Finset.univ (fun m _ => hprod k m)


/-- **The exact second-moment computation of one GUE block.**  Integrating
`(id_d ⊗ tr_N)((A_i ⊗ G_i) R)` produces the exact finite-`N` quadratic term
`A_i * E[T_N A_i T_N]`. -/
lemma integral_partialTraceN_block (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    (hA₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian)
    (z : ℂ) (hz : z.im ≠ 0) (i : ι) (u v : d) :
    ∫ x, ((N : ℂ)⁻¹ * ∑ k : Fin N, ∑ a : d, ∑ m : Fin N,
        A i u a * gueMatrix (x : GUECoord ι N → ℝ) i k m *
          guePencilResolvent A₀ A (x : GUECoord ι N → ℝ) z (a, m) (v, k))
      ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))
    = ∑ a : d, A i u a *
        ∫ x, (guePartialTrace A₀ A z (x : GUECoord ι N → ℝ) * A i *
            guePartialTrace A₀ A z (x : GUECoord ι N → ℝ)) a v
          ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) := by
  classical
  have hRint : ∀ a b, Integrable (fun x : EuclideanSpace ℝ (GUECoord ι N) =>
      guePencilResolvent A₀ A (x : GUECoord ι N → ℝ) z a b)
      (stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) :=
    fun a b => integrable_guePencilResolvent_entry_euclid A₀ A hA₀ hA z hz a b
  have hprod : ∀ a b c e, Integrable (fun x : EuclideanSpace ℝ (GUECoord ι N) =>
      guePencilResolvent A₀ A (x : GUECoord ι N → ℝ) z a b *
        guePencilResolvent A₀ A (x : GUECoord ι N → ℝ) z c e)
      (stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) := by
    intro a b c e
    exact (hRint a b).mul_bdd
      ((continuous_guePencilResolvent_entry_euclid A₀ A hA₀ hA z hz c e).aestronglyMeasurable)
      (ae_of_all _ fun x => CStarMatrix.norm_entry_le_norm.trans
        (norm_guePencilResolvent_le A₀ A hA₀ hA _ z hz))
  have hRbdd : ∀ (x : EuclideanSpace ℝ (GUECoord ι N)) (a b : d × Fin N),
      ‖guePencilResolvent A₀ A (x : GUECoord ι N → ℝ) z a b‖ ≤ |z.im|⁻¹ := by
    intro x a b
    exact CStarMatrix.norm_entry_le_norm.trans (norm_guePencilResolvent_le A₀ A hA₀ hA _ z hz)
  have hterm : ∀ k a m, Integrable (fun x : EuclideanSpace ℝ (GUECoord ι N) =>
      A i u a * gueMatrix (x : GUECoord ι N → ℝ) i k m *
        guePencilResolvent A₀ A (x : GUECoord ι N → ℝ) z (a, m) (v, k))
      (stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) := by
    intro k a m
    have h := ((integrable_gueMatrix_entry i k m).mul_bdd
      ((continuous_guePencilResolvent_entry_euclid A₀ A hA₀ hA z hz (a, m) (v, k)).aestronglyMeasurable)
      (ae_of_all _ fun x => hRbdd x (a, m) (v, k))).const_mul (A i u a)
    refine h.congr (ae_of_all _ fun x => ?_)
    ring
  -- Step 1: push the integral through all the finite sums and constants.
  have hinner : ∫ x, (∑ k : Fin N, ∑ a : d, ∑ m : Fin N,
        A i u a * gueMatrix (x : GUECoord ι N → ℝ) i k m *
          guePencilResolvent A₀ A (x : GUECoord ι N → ℝ) z (a, m) (v, k))
        ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))
      = ∑ k : Fin N, ∑ a : d, ∑ m : Fin N,
          A i u a * ∫ x, gueMatrix (x : GUECoord ι N → ℝ) i k m *
            guePencilResolvent A₀ A (x : GUECoord ι N → ℝ) z (a, m) (v, k)
            ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) := by
    rw [integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro k _
      rw [integral_finsetSum]
      · apply Finset.sum_congr rfl
        intro a _
        rw [integral_finsetSum]
        · apply Finset.sum_congr rfl
          intro m _
          simp only [mul_assoc]
          rw [integral_const_mul]
        · intro m _
          exact hterm k a m
      · intro a _
        exact integrable_finsetSum _ fun m _ => hterm k a m
    · intro k _
      exact integrable_finsetSum _ fun a _ => integrable_finsetSum _ fun m _ => hterm k a m
  rw [integral_const_mul, hinner]
  simp_rw [integral_gueMatrix_mul_resolvent_entry A₀ A hA₀ hA z hz i]
  -- Step 2: reorder the finite sums and factor the `k,m` sums.
  have hLHS : (N : ℂ)⁻¹ * (∑ k : Fin N, ∑ a : d, ∑ m : Fin N,
        A i u a * ((gueScale N : ℂ) ^ 2 * ∑ s : d, ∑ t : d, A i s t *
          ∫ x, guePencilResolvent A₀ A (x : GUECoord ι N → ℝ) z (a, m) (s, m) *
              guePencilResolvent A₀ A (x : GUECoord ι N → ℝ) z (t, k) (v, k)
            ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))))
      = (gueScale N : ℂ) ^ 2 * (N : ℂ)⁻¹ * ∑ a : d, ∑ s : d, ∑ t : d,
          A i u a * A i s t *
            (∑ k : Fin N, ∑ m : Fin N,
              ∫ x, guePencilResolvent A₀ A (x : GUECoord ι N → ℝ) z (a, m) (s, m) *
                  guePencilResolvent A₀ A (x : GUECoord ι N → ℝ) z (t, k) (v, k)
                ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))) := by
    simp only [Finset.mul_sum]
    rw [sum_reorder_five]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro s _
    apply Finset.sum_congr rfl
    intro t _
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro m _
    ring
  rw [hLHS]
  -- Step 3: expand the quadratic term `T A_i T` and evaluate `E[T_as T_tv]`.
  have hptTA : ∀ (a : d) (x : EuclideanSpace ℝ (GUECoord ι N)),
      (guePartialTrace A₀ A z (x : GUECoord ι N → ℝ) * A i *
          guePartialTrace A₀ A z (x : GUECoord ι N → ℝ)) a v
        = ∑ s : d, ∑ t : d,
            guePartialTrace A₀ A z (x : GUECoord ι N → ℝ) a s * A i s t *
              guePartialTrace A₀ A z (x : GUECoord ι N → ℝ) t v := by
    intro a x
    simp only [Matrix.mul_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
  have hTprod : ∀ (a : d) (s : d) (t : d), Integrable (fun x : EuclideanSpace ℝ (GUECoord ι N) =>
      guePartialTrace A₀ A z (x : GUECoord ι N → ℝ) a s *
        guePartialTrace A₀ A z (x : GUECoord ι N → ℝ) t v)
      (stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) := by
    intro a s t
    have hEq : (fun x : EuclideanSpace ℝ (GUECoord ι N) =>
        guePartialTrace A₀ A z (x : GUECoord ι N → ℝ) a s *
          guePartialTrace A₀ A z (x : GUECoord ι N → ℝ) t v)
        = fun x : EuclideanSpace ℝ (GUECoord ι N) => (N : ℂ)⁻¹ * ((N : ℂ)⁻¹ *
            ((∑ m : Fin N, guePencilResolvent A₀ A (x : GUECoord ι N → ℝ) z (a, m) (s, m)) *
              (∑ k : Fin N, guePencilResolvent A₀ A (x : GUECoord ι N → ℝ) z (t, k) (v, k)))) := by
      funext x
      simp only [guePartialTrace_apply, partialTraceN_apply]
      ring
    rw [hEq]
    refine Integrable.const_mul ?_ _
    refine Integrable.const_mul ?_ _
    simp only [Finset.sum_mul_sum]
    exact integrable_finsetSum _ fun m _ => integrable_finsetSum _ fun k _ =>
      hprod (a, m) (s, m) (t, k) (v, k)
  have hprodA : ∀ (a s t : d), Integrable (fun x : EuclideanSpace ℝ (GUECoord ι N) =>
      A i s t * (guePartialTrace A₀ A z (x : GUECoord ι N → ℝ) a s *
        guePartialTrace A₀ A z (x : GUECoord ι N → ℝ) t v))
      (stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) :=
    fun a s t => (hTprod a s t).const_mul (A i s t)
  have hTA : ∀ a : d, ∫ x, (guePartialTrace A₀ A z (x : GUECoord ι N → ℝ) * A i *
        guePartialTrace A₀ A z (x : GUECoord ι N → ℝ)) a v
        ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))
      = ∑ s : d, ∑ t : d, A i s t *
          ∫ x, guePartialTrace A₀ A z (x : GUECoord ι N → ℝ) a s *
              guePartialTrace A₀ A z (x : GUECoord ι N → ℝ) t v
            ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) := by
    intro a
    rw [show (∫ x, (guePartialTrace A₀ A z (x : GUECoord ι N → ℝ) * A i *
          guePartialTrace A₀ A z (x : GUECoord ι N → ℝ)) a v
          ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N))))
        = ∫ x, ∑ s : d, ∑ t : d,
            guePartialTrace A₀ A z (x : GUECoord ι N → ℝ) a s * A i s t *
              guePartialTrace A₀ A z (x : GUECoord ι N → ℝ) t v
            ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) from
      integral_congr_ae (ae_of_all _ (hptTA a))]
    rw [integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro s _
      rw [integral_finsetSum]
      · apply Finset.sum_congr rfl
        intro t _
        rw [show (fun x : EuclideanSpace ℝ (GUECoord ι N) =>
              guePartialTrace A₀ A z (x : GUECoord ι N → ℝ) a s * A i s t *
                guePartialTrace A₀ A z (x : GUECoord ι N → ℝ) t v)
            = fun x : EuclideanSpace ℝ (GUECoord ι N) => A i s t * (guePartialTrace A₀ A z (x : GUECoord ι N → ℝ) a s *
                guePartialTrace A₀ A z (x : GUECoord ι N → ℝ) t v) from by
              funext x
              ring]
        rw [integral_const_mul]
      · intro t _
        simpa only [mul_assoc, mul_comm, mul_left_comm] using hprodA a s t
    · intro s _
      exact integrable_finsetSum _ fun t _ => by
        simpa only [mul_assoc, mul_comm, mul_left_comm] using hprodA a s t
  have hTT : ∀ (a : d) (s : d) (t : d),
      (∫ x, guePartialTrace A₀ A z (x : GUECoord ι N → ℝ) a s *
          guePartialTrace A₀ A z (x : GUECoord ι N → ℝ) t v
          ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N))))
        = (N : ℂ)⁻¹ * (N : ℂ)⁻¹ * (∑ k : Fin N, ∑ m : Fin N,
            ∫ x, guePencilResolvent A₀ A (x : GUECoord ι N → ℝ) z (a, m) (s, m) *
                guePencilResolvent A₀ A (x : GUECoord ι N → ℝ) z (t, k) (v, k)
              ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))) := by
    intro a s t
    have hpt : ∀ x : EuclideanSpace ℝ (GUECoord ι N),
        guePartialTrace A₀ A z (x : GUECoord ι N → ℝ) a s *
            guePartialTrace A₀ A z (x : GUECoord ι N → ℝ) t v
          = (N : ℂ)⁻¹ * ((N : ℂ)⁻¹ *
              ((∑ m : Fin N, guePencilResolvent A₀ A (x : GUECoord ι N → ℝ) z (a, m) (s, m)) *
                (∑ k : Fin N, guePencilResolvent A₀ A (x : GUECoord ι N → ℝ) z (t, k) (v, k)))) := by
      intro x
      simp only [guePartialTrace_apply, partialTraceN_apply]
      ring
    rw [show (∫ x, guePartialTrace A₀ A z (x : GUECoord ι N → ℝ) a s *
          guePartialTrace A₀ A z (x : GUECoord ι N → ℝ) t v
          ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N))))
        = ∫ x, (N : ℂ)⁻¹ * ((N : ℂ)⁻¹ *
            ((∑ m : Fin N, guePencilResolvent A₀ A (x : GUECoord ι N → ℝ) z (a, m) (s, m)) *
              (∑ k : Fin N, guePencilResolvent A₀ A (x : GUECoord ι N → ℝ) z (t, k) (v, k))))
          ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) from
      integral_congr_ae (ae_of_all _ hpt)]
    rw [integral_const_mul, integral_const_mul]
    rw [show (∫ x, (∑ m : Fin N, guePencilResolvent A₀ A (x : _) z (a, m) (s, m)) *
          (∑ k : Fin N, guePencilResolvent A₀ A (x : _) z (t, k) (v, k))
          ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N))))
        = ∑ k : Fin N, ∑ m : Fin N,
            ∫ x, guePencilResolvent A₀ A (x : GUECoord ι N → ℝ) z (a, m) (s, m) *
                guePencilResolvent A₀ A (x : GUECoord ι N → ℝ) z (t, k) (v, k)
              ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) from
      (sum_sum_integral_mul (f := fun x m =>
          guePencilResolvent A₀ A (x : GUECoord ι N → ℝ) z (a, m) (s, m))
        (g := fun x k =>
          guePencilResolvent A₀ A (x : GUECoord ι N → ℝ) z (t, k) (v, k))
        (fun k m => hprod (a, m) (s, m) (t, k) (v, k))).symm]
    ring
  simp only [hTA, hTT]
  rw [gueScale_sq_complex]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro t _
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro m _
  ring


/-- Pointwise partial-trace form of the resolvent identity:
`z T - A₀ T - ∑ i P_i = 1`, where `P_i` is the partial trace of `(A_i ⊗ G_i) R`. -/
lemma partialTrace_resolvent_identity (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    (hA₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian)
    (x : GUECoord ι N → ℝ) (z : ℂ) (hz : z.im ≠ 0) (hN : (N : ℂ) ≠ 0) :
    z • guePartialTrace A₀ A z x - A₀ * guePartialTrace A₀ A z x -
      ∑ i, (Matrix.of fun u v => (N : ℂ)⁻¹ * ∑ k : Fin N, ∑ a : d, ∑ m : Fin N,
        A i u a * gueMatrix x i k m *
          guePencilResolvent A₀ A x z (a, m) (v, k))
      = 1 := by
  have hres := resolvent_mul_guePencil A₀ A hA₀ hA x z hz
  have h := congrArg partialTraceN hres
  rw [partialTraceN_one hN] at h
  have hsplit : partialTraceN ((algebraMap ℂ (CStarMatrix (d × Fin N) (d × Fin N) ℂ) z -
        guePencil A₀ A x) * guePencilResolvent A₀ A x z)
      = z • guePartialTrace A₀ A z x -
        partialTraceN (guePencil A₀ A x * guePencilResolvent A₀ A x z) := by
    rw [sub_mul, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul,
      partialTraceN_sub, partialTraceN_smul]
    rfl
  rw [hsplit, partialTraceN_guePencil_mul_resolvent A₀ A hA₀ hA x z hz] at h
  rw [sub_add_eq_sub_sub] at h
  exact h

/-- Entry formula for `(z • 1 - A₀) * g_N(z)`. -/
lemma sub_smul_one_mul_mean_entry (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ) (z : ℂ)
    (u v : d) :
    ((z • (1 : Matrix d d ℂ) - A₀) * gueResolventMean (N := N) A₀ A z) u v
      = z * (∫ x, guePartialTrace A₀ A z x u v
          ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N))))
        - ∑ a : d, A₀ u a *
            (∫ x, guePartialTrace A₀ A z x a v
              ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))) := by
  rw [Matrix.sub_mul, Matrix.sub_apply]
  congr 1
  · rw [Matrix.mul_apply]
    rw [Finset.sum_eq_single u]
    · rw [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one,
        gueResolventMean_apply]
    · intro j _ hju
      rw [Matrix.smul_apply, Matrix.one_apply_ne (Ne.symm hju), smul_eq_mul, mul_zero,
        zero_mul]
    · intro h
      exact absurd (Finset.mem_univ u) h

/-- **Exact finite-`N` Gaussian Schwinger--Dyson (master) identity for the GUE pencil.**

With `T_N(z,x) = (id_d ⊗ tr_N)(z • 1 - H(x))⁻¹` and `g_N(z) = E[T_N(z,·)]`,

`(z • 1 - A₀) * g_N(z) - 1 = ∑ i, A_i * E[T_N(z) * A_i * T_N(z)]`.

All factors are exact for finite `N`: the covariance factor is `gueScale² = 1/N` and the
quadratic term is the *random* `E[T_N A_i T_N]`, not `g_N A_i g_N`.  No concentration or
comparison bound is used. -/
theorem gue_dyson_master_identity (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    (hA₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian)
    (z : ℂ) (hz : z.im ≠ 0) (hN : (N : ℂ) ≠ 0) :
    (z • (1 : Matrix d d ℂ) - A₀) * gueResolventMean (N := N) A₀ A z - 1
      = ∑ i, A i * (Matrix.of fun u v =>
          ∫ x, (guePartialTrace A₀ A z x * A i * guePartialTrace A₀ A z x) u v
            ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))) := by
  classical
  have hRint : ∀ a b, Integrable (fun x : EuclideanSpace ℝ (GUECoord ι N) =>
      guePencilResolvent A₀ A (x : GUECoord ι N → ℝ) z a b)
      (stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) :=
    fun a b => integrable_guePencilResolvent_entry_euclid A₀ A hA₀ hA z hz a b
  have hPint : ∀ (i : ι) (u v : d), Integrable (fun x : EuclideanSpace ℝ (GUECoord ι N) =>
      (N : ℂ)⁻¹ * ∑ k : Fin N, ∑ a : d, ∑ m : Fin N,
        A i u a * gueMatrix (x : GUECoord ι N → ℝ) i k m *
          guePencilResolvent A₀ A (x : GUECoord ι N → ℝ) z (a, m) (v, k))
      (stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) := by
    intro i u v
    have hterm : ∀ k a m, Integrable (fun x : EuclideanSpace ℝ (GUECoord ι N) =>
        A i u a * gueMatrix (x : GUECoord ι N → ℝ) i k m *
          guePencilResolvent A₀ A (x : GUECoord ι N → ℝ) z (a, m) (v, k))
        (stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) := by
      intro k a m
      have h := ((integrable_gueMatrix_entry i k m).mul_bdd
        ((continuous_guePencilResolvent_entry_euclid A₀ A hA₀ hA z hz (a, m) (v, k)).aestronglyMeasurable)
        (ae_of_all _ fun x => CStarMatrix.norm_entry_le_norm.trans
          (norm_guePencilResolvent_le A₀ A hA₀ hA _ z hz))).const_mul (A i u a)
      refine h.congr (ae_of_all _ fun x => ?_)
      ring
    refine Integrable.const_mul ?_ _
    exact integrable_finsetSum _ fun k _ => integrable_finsetSum _ fun a _ =>
      integrable_finsetSum _ fun m _ => hterm k a m
  have hTint : ∀ (a v : d), Integrable (fun x : EuclideanSpace ℝ (GUECoord ι N) =>
      guePartialTrace A₀ A z (x : GUECoord ι N → ℝ) a v)
      (stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) := by
    intro a v
    have hEq : (fun x : EuclideanSpace ℝ (GUECoord ι N) =>
        guePartialTrace A₀ A z (x : GUECoord ι N → ℝ) a v)
        = fun x : EuclideanSpace ℝ (GUECoord ι N) => (N : ℂ)⁻¹ * ∑ k : Fin N,
            guePencilResolvent A₀ A (x : GUECoord ι N → ℝ) z (a, k) (v, k) := by
      funext x
      simp only [guePartialTrace_apply, partialTraceN_apply]
    rw [hEq]
    exact (integrable_finsetSum _ fun k _ => hRint (a, k) (v, k)).const_mul _
  ext u v
  -- compute the left-hand side entry
  rw [Matrix.sub_apply, sub_smul_one_mul_mean_entry]
  -- integrate the pointwise identity
  have hpoint : ∀ x : EuclideanSpace ℝ (GUECoord ι N),
      z * guePartialTrace A₀ A z (x : GUECoord ι N → ℝ) u v -
          ∑ a : d, A₀ u a * guePartialTrace A₀ A z (x : GUECoord ι N → ℝ) a v -
          ∑ i, ((N : ℂ)⁻¹ * ∑ k : Fin N, ∑ a : d, ∑ m : Fin N,
            A i u a * gueMatrix (x : GUECoord ι N → ℝ) i k m *
              guePencilResolvent A₀ A (x : GUECoord ι N → ℝ) z (a, m) (v, k))
        = (1 : Matrix d d ℂ) u v := by
    intro x
    have h := congrArg (fun M : Matrix d d ℂ => M u v)
      (partialTrace_resolvent_identity A₀ A hA₀ hA (x : GUECoord ι N → ℝ) z hz hN)
    simpa only [Matrix.sub_apply, Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul,
      Matrix.sum_apply, Matrix.of_apply] using h
  -- integrate the pointwise identity
  have hInt : (∫ x, (z * guePartialTrace A₀ A z (x : GUECoord ι N → ℝ) u v -
        ∑ a : d, A₀ u a * guePartialTrace A₀ A z (x : GUECoord ι N → ℝ) a v -
        ∑ i, ((N : ℂ)⁻¹ * ∑ k : Fin N, ∑ a : d, ∑ m : Fin N,
          A i u a * gueMatrix (x : GUECoord ι N → ℝ) i k m *
            guePencilResolvent A₀ A (x : GUECoord ι N → ℝ) z (a, m) (v, k)))
        ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N))))
      = (1 : Matrix d d ℂ) u v := by
    rw [show (∫ x, (z * guePartialTrace A₀ A z (x : GUECoord ι N → ℝ) u v -
          ∑ a : d, A₀ u a * guePartialTrace A₀ A z (x : GUECoord ι N → ℝ) a v -
          ∑ i, ((N : ℂ)⁻¹ * ∑ k : Fin N, ∑ a : d, ∑ m : Fin N,
            A i u a * gueMatrix (x : GUECoord ι N → ℝ) i k m *
              guePencilResolvent A₀ A (x : GUECoord ι N → ℝ) z (a, m) (v, k)))
          ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N))))
        = ∫ x, (1 : Matrix d d ℂ) u v
            ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) from
      integral_congr_ae (ae_of_all _ hpoint)]
    simp [integral_const, measure_univ]
  -- split the integral
  have hsplit : (∫ x, (z * guePartialTrace A₀ A z (x : GUECoord ι N → ℝ) u v -
        ∑ a : d, A₀ u a * guePartialTrace A₀ A z (x : GUECoord ι N → ℝ) a v -
        ∑ i, ((N : ℂ)⁻¹ * ∑ k : Fin N, ∑ a : d, ∑ m : Fin N,
          A i u a * gueMatrix (x : GUECoord ι N → ℝ) i k m *
            guePencilResolvent A₀ A (x : GUECoord ι N → ℝ) z (a, m) (v, k)))
        ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N))))
      = z * (∫ x, guePartialTrace A₀ A z (x : GUECoord ι N → ℝ) u v
            ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N))))
        - ∑ a : d, A₀ u a *
            (∫ x, guePartialTrace A₀ A z (x : GUECoord ι N → ℝ) a v
              ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N))))
        - ∑ i, ∫ x, ((N : ℂ)⁻¹ * ∑ k : Fin N, ∑ a : d, ∑ m : Fin N,
              A i u a * gueMatrix (x : GUECoord ι N → ℝ) i k m *
                guePencilResolvent A₀ A (x : GUECoord ι N → ℝ) z (a, m) (v, k))
            ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) := by
    rw [integral_sub]
    · rw [integral_sub]
      · rw [integral_const_mul]
        rw [integral_finsetSum]
        · rw [integral_finsetSum]
          · rw [show (∑ a : d, ∫ x, A₀ u a *
                guePartialTrace A₀ A z (x : GUECoord ι N → ℝ) a v
                ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N))))
                = ∑ a : d, A₀ u a *
                  (∫ x, guePartialTrace A₀ A z (x : GUECoord ι N → ℝ) a v
                    ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))) from by
              apply Finset.sum_congr rfl
              intro a _
              rw [integral_const_mul]]
          · intro i _
            exact hPint i u v
        · intro a _
          exact (hTint a v).const_mul (A₀ u a)
      · exact (hTint u v).const_mul z
      · exact integrable_finsetSum _ fun a _ => (hTint a v).const_mul (A₀ u a)
    · exact ((hTint u v).const_mul z).sub
        (integrable_finsetSum _ fun a _ => (hTint a v).const_mul (A₀ u a))
    · exact integrable_finsetSum _ fun i _ => hPint i u v

  rw [hsplit] at hInt
  -- identify `∫ P_i` with `∑ a, A_i u a * ∫ (T A_i T) a v`
  have hPT : ∀ i : ι, (∫ x, ((N : ℂ)⁻¹ * ∑ k : Fin N, ∑ a : d, ∑ m : Fin N,
        A i u a * gueMatrix (x : GUECoord ι N → ℝ) i k m *
          guePencilResolvent A₀ A (x : GUECoord ι N → ℝ) z (a, m) (v, k))
        ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N))))
      = ∑ a : d, A i u a *
          ∫ x, (guePartialTrace A₀ A z (x : GUECoord ι N → ℝ) * A i *
              guePartialTrace A₀ A z (x : GUECoord ι N → ℝ)) a v
            ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) :=
    fun i => integral_partialTraceN_block A₀ A hA₀ hA z hz i u v
  simp only [hPT] at hInt
  -- rewrite the right-hand side entry
  simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.of_apply] at hInt ⊢
  -- conclude from `hInt`
  rw [← hInt]
  ring

/-! ### Scalar single-GUE warm-up

Taking `d = Unit`, `ι = Unit`, `A₀ = 0`, `A = 1` the pencil is the single normalized GUE
matrix `H(x) = G(x)`, `T_N = N⁻¹ tr R`, and the master identity becomes the scalar exact
finite-`N` Schwinger--Dyson equation `z E[T] - 1 = E[T²]`. -/

/-- **Exact finite-`N` Schwinger--Dyson equation for a single GUE matrix.**
With `H = G_N`, `R = (z - H)⁻¹` and `T = N⁻¹ tr R`, `z * E[T] - 1 = E[T * T]`.
The covariance normalization `E|G_ab|² = 1/N` enters through `gueScale`. -/
theorem single_gue_schwinger_dyson (z : ℂ) (hz : z.im ≠ 0) (hN : (N : ℂ) ≠ 0) :
    z * gueResolventMean (N := N) (0 : Matrix Unit Unit ℂ)
        (fun _ : Unit => (1 : Matrix Unit Unit ℂ)) z () () - 1
      = ∫ x, guePartialTrace (N := N) (0 : Matrix Unit Unit ℂ)
            (fun _ : Unit => (1 : Matrix Unit Unit ℂ)) z x () () *
          guePartialTrace (N := N) (0 : Matrix Unit Unit ℂ)
            (fun _ : Unit => (1 : Matrix Unit Unit ℂ)) z x () ()
        ∂(stdGaussian (EuclideanSpace ℝ (GUECoord Unit N))) := by
  have hm := congrArg (fun M : Matrix Unit Unit ℂ => M () ())
    (gue_dyson_master_identity (0 : Matrix Unit Unit ℂ)
      (fun _ : Unit => (1 : Matrix Unit Unit ℂ)) Matrix.isHermitian_zero
      (fun _ => Matrix.isHermitian_one) z hz hN)
  simpa [Matrix.sub_apply, Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply,
    Matrix.sum_apply, Matrix.of_apply, smul_eq_mul] using hm

end

end GUEStrongConvergence
