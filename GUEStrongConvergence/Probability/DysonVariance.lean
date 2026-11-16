/-
# Variance and covariance estimates for the GUE-pencil partial trace

This file continues HT05 Theorem 5.7 after the exact finite-`N` master identity
(`DysonMasterIdentity.lean`).  The goal is to turn

`(z • 1 - A₀) g_N(z) - 1 = ∑ i, A_i * E[T_N A_i T_N]`

into an *approximate* Dyson equation, by replacing the random quadratic term `E[T_N A_i T_N]`
with the deterministic `g_N A_i g_N`.

## Main results

* `variance_partialTrace_re_le` (milestone (a)(1)): for `0 < z.im`, every real part
  `Re T_N(z)_{uv}` has Gaussian-Poincaré variance bounded by the explicit constant

  `2 * gueScale(N)^2 * (∑ i, frob(A_i)^2) * (z.im)⁻⁴ = O(1/N)`.

  The `1/N` comes from `gueScale(N)^2 = 1/N`: the coordinate derivatives of `T_N` are
  `N⁻¹ ∑_k (R D_p R)_{(u,k),(v,k)}`, and the sparse direction-pairing bound
  (`sum_sq_direction_pairing_le`) applied to each `k`, followed by Cauchy–Schwarz over the
  `N` values of `k`, cancels the `N⁻¹`.

* `covariance_partialTrace_mul_le` (milestone (a)(2)): for Hermitian `A` with `‖A‖ ≤ 1`,

  `frob (E[T A T] - E[T] A E[T]) ≤ C(A, z, N) / N`,

  via the decomposition `T A T - ET A ET = (T-ET) A T + ET A (T-ET)` and the entrywise
  variance bound.  No concentration of `T_N` around `g_N` and no comparison with the limit
  Dyson equation is assumed.

## Normalization

Exactly as in `DysonMasterIdentity.lean`: `T_N = (id_d ⊗ tr_N) R`, `gueScale(N)^2 = 1/N`,
and the covariance of the GUE entries is `E[(G_i)_{ab}(G_j)_{cd}] = δ_ij δ_ad δ_bc / N`.

## Remaining step towards HT05 5.7

Combining the master identity with the covariance bound gives the *intermediate approximate
Dyson equation* (`approximate_dyson_entry_le`): every entry of

`(z • 1 - A₀) g_N - 1 - ∑ i, A_i g_N A_i g_N`

is bounded by `2 (card d)² sqrt(card d) (∑ frob(A_i)²) · VarConst`, with
`VarConst = 2 gueScale(N)^2 (∑ frob(A_i)^2) (im z)⁻⁴ = O(1/N)`.  Closing HT05 5.7 still needs
(i) replacement of `g_N` by the deterministic limit `g` (convergence of the mean resolvent,
not proved here) and (ii) stability of the limit Dyson equation.  Neither is assumed in this
file: all statements are exact finite-`N` inequalities.
-/
import GUEStrongConvergence.Probability.DysonMasterIdentity
import GUEStrongConvergence.Probability.ResolventLipschitz
import GUEStrongConvergence.Probability.GaussianPoincare

open MeasureTheory ProbabilityTheory Matrix Kronecker Filter
open scoped Matrix.Norms.Elementwise ComplexOrder ENNReal NNReal Topology

set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000

namespace GUEStrongConvergence

noncomputable section

variable {ι d : Type*} {N : ℕ} [Fintype ι] [Fintype d] [DecidableEq d] [DecidableEq ι]

/-! ### Polynomial growth from a uniform bound -/

/-- A uniformly bounded function has polynomial growth (degree zero). -/
lemma polyGrowth_of_bound {f : ℝ → ℝ} {C : ℝ} (h : ∀ x, |f x| ≤ C) : PolyGrowth f := by
  refine ⟨max C 0, le_max_right _ _, 0, fun x => ?_⟩
  rw [pow_zero, mul_one]
  exact (h x).trans (le_max_left _ _)

/-! ### The derivative of a partial-trace entry -/

/-- The coordinate derivative of the partial-trace entry `T_N(z)_{uv}`. -/
def guePartialTraceDir (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ) (z : ℂ)
    (u v : d) (p : GUECoord ι N) (x : GUECoord ι N → ℝ) : ℂ :=
  (N : ℂ)⁻¹ * ∑ k : Fin N,
    (guePencilResolvent A₀ A x z * guePencilDirection A p *
      guePencilResolvent A₀ A x z) (u, k) (v, k)

/-- Coordinate derivative of `T_N(z)_{uv}` along a Gaussian coordinate line. -/
lemma hasDerivAt_guePartialTrace_entry_update (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    (hA₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian)
    (x : GUECoord ι N → ℝ) (p : GUECoord ι N) (z : ℂ) (hz : z.im ≠ 0) (t₀ : ℝ)
    (u v : d) :
    HasDerivAt (fun t : ℝ => guePartialTrace A₀ A z (Function.update x p t) u v)
      (guePartialTraceDir A₀ A z u v p (Function.update x p t₀)) t₀ := by
  have hsum : HasDerivAt
      (fun t : ℝ => ∑ k : Fin N,
        guePencilResolvent A₀ A (Function.update x p t) z (u, k) (v, k))
      (∑ k : Fin N,
        (guePencilResolvent A₀ A (Function.update x p t₀) z *
          guePencilDirection A p *
          guePencilResolvent A₀ A (Function.update x p t₀) z) (u, k) (v, k)) t₀ := by
    convert (HasDerivAt.sum (u := Finset.univ) fun k _ =>
      hasDerivAt_guePencilResolvent_entry A₀ A hA₀ hA x p z hz t₀ (u, k) (v, k)) using 1
    funext t
    simp only [Finset.sum_apply]
  have h := hsum.const_mul ((N : ℂ)⁻¹)
  convert h using 1
  · funext t
    simp [guePartialTrace_apply, partialTraceN_apply]
  · simp [guePartialTraceDir]

/-! ### Continuity and boundedness -/

/-- Continuity of a partial-trace entry on the Euclidean Gaussian space. -/
lemma continuous_guePartialTrace_entry (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    (hA₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian)
    (z : ℂ) (hz : z.im ≠ 0) (u v : d) :
    Continuous (fun x : EuclideanSpace ℝ (GUECoord ι N) =>
      guePartialTrace A₀ A z (x : GUECoord ι N → ℝ) u v) := by
  have hsum : Continuous (fun x : EuclideanSpace ℝ (GUECoord ι N) =>
      ∑ k : Fin N,
        guePencilResolvent A₀ A (x : GUECoord ι N → ℝ) z (u, k) (v, k)) :=
    continuous_finsetSum _ fun k _ =>
      continuous_guePencilResolvent_entry_euclid A₀ A hA₀ hA z hz (u, k) (v, k)
  have h := (continuous_const : Continuous fun _ : EuclideanSpace ℝ (GUECoord ι N) =>
    (N : ℂ)⁻¹).mul hsum
  refine h.congr (fun x => ?_)
  simp [guePartialTrace_apply, partialTraceN_apply]

/-- Continuity of the coordinate derivative of a partial-trace entry. -/
lemma continuous_guePartialTraceDir_entry (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    (hA₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian)
    (z : ℂ) (hz : z.im ≠ 0) (u v : d) (p : GUECoord ι N) :
    Continuous (fun x : EuclideanSpace ℝ (GUECoord ι N) =>
      guePartialTraceDir A₀ A z u v p (x : GUECoord ι N → ℝ)) := by
  have hsum : Continuous (fun x : EuclideanSpace ℝ (GUECoord ι N) =>
      ∑ k : Fin N,
        (guePencilResolvent A₀ A (x : GUECoord ι N → ℝ) z * guePencilDirection A p *
          guePencilResolvent A₀ A (x : GUECoord ι N → ℝ) z) (u, k) (v, k)) :=
    continuous_finsetSum _ fun k _ =>
      continuous_guePencilResolvent_direction_entry_euclid A₀ A hA₀ hA z hz p (u, k) (v, k)
  have h := (continuous_const : Continuous fun _ : EuclideanSpace ℝ (GUECoord ι N) =>
    (N : ℂ)⁻¹).mul hsum
  refine h.congr (fun x => ?_)
  simp [guePartialTraceDir]

/-- A partial-trace entry is bounded by `1/|im z|`. -/
lemma norm_guePartialTrace_entry_le (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    (hA₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian)
    (x : GUECoord ι N → ℝ) (z : ℂ) (hz : z.im ≠ 0) (hN : 0 < N) (u v : d) :
    ‖guePartialTrace A₀ A z x u v‖ ≤ |z.im|⁻¹ := by
  have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  rw [guePartialTrace_apply]
  have hsum : ‖∑ k : Fin N,
      guePencilResolvent A₀ A x z (u, k) (v, k)‖ ≤ (N : ℝ) * |z.im|⁻¹ := by
    calc ‖∑ k : Fin N, guePencilResolvent A₀ A x z (u, k) (v, k)‖
        ≤ ∑ k : Fin N, ‖guePencilResolvent A₀ A x z (u, k) (v, k)‖ :=
          norm_sum_le _ _
      _ ≤ ∑ _k : Fin N, |z.im|⁻¹ := by
          refine Finset.sum_le_sum fun k _ => ?_
          exact CStarMatrix.norm_entry_le_norm.trans
            (norm_guePencilResolvent_le A₀ A hA₀ hA x z hz)
      _ = (N : ℝ) * |z.im|⁻¹ := by simp
  calc ‖(N : ℂ)⁻¹ * ∑ k : Fin N, guePencilResolvent A₀ A x z (u, k) (v, k)‖
      ≤ ‖(N : ℂ)⁻¹‖ * ‖∑ k : Fin N, guePencilResolvent A₀ A x z (u, k) (v, k)‖ :=
        norm_mul_le _ _
    _ ≤ ‖(N : ℂ)⁻¹‖ * ((N : ℝ) * |z.im|⁻¹) := by
        exact mul_le_mul_of_nonneg_left hsum (norm_nonneg _)
    _ = |z.im|⁻¹ := by
        rw [norm_inv, Complex.norm_natCast]
        field_simp

/-- A directional derivative entry is bounded by `‖D_p‖ / |im z|^2`. -/
lemma norm_guePartialTraceDir_le (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    (hA₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian)
    (x : GUECoord ι N → ℝ) (z : ℂ) (hz : z.im ≠ 0) (hN : 0 < N)
    (u v : d) (p : GUECoord ι N) :
    ‖guePartialTraceDir A₀ A z u v p x‖ ≤ |z.im|⁻¹ ^ 2 * ‖guePencilDirection A p‖ := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hR : ‖guePencilResolvent A₀ A x z‖ ≤ |z.im|⁻¹ :=
    norm_guePencilResolvent_le A₀ A hA₀ hA x z hz
  have hentry : ∀ k : Fin N,
      ‖(guePencilResolvent A₀ A x z * guePencilDirection A p *
        guePencilResolvent A₀ A x z) (u, k) (v, k)‖
        ≤ |z.im|⁻¹ ^ 2 * ‖guePencilDirection A p‖ := by
    intro k
    calc ‖(guePencilResolvent A₀ A x z * guePencilDirection A p *
          guePencilResolvent A₀ A x z) (u, k) (v, k)‖
        ≤ ‖guePencilResolvent A₀ A x z * guePencilDirection A p *
            guePencilResolvent A₀ A x z‖ := CStarMatrix.norm_entry_le_norm
      _ ≤ ‖guePencilResolvent A₀ A x z * guePencilDirection A p‖ *
            ‖guePencilResolvent A₀ A x z‖ := norm_mul_le _ _
      _ ≤ (‖guePencilResolvent A₀ A x z‖ * ‖guePencilDirection A p‖) *
            ‖guePencilResolvent A₀ A x z‖ := by
          exact mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
      _ ≤ (|z.im|⁻¹ * ‖guePencilDirection A p‖) * |z.im|⁻¹ := by
          refine mul_le_mul ?_ hR (norm_nonneg _) (by positivity)
          exact mul_le_mul_of_nonneg_right hR (norm_nonneg _)
      _ = |z.im|⁻¹ ^ 2 * ‖guePencilDirection A p‖ := by ring
  calc ‖guePartialTraceDir A₀ A z u v p x‖
      = ‖(N : ℂ)⁻¹ * ∑ k : Fin N,
          (guePencilResolvent A₀ A x z * guePencilDirection A p *
            guePencilResolvent A₀ A x z) (u, k) (v, k)‖ := rfl
    _ ≤ ‖(N : ℂ)⁻¹‖ * ‖∑ k : Fin N,
          (guePencilResolvent A₀ A x z * guePencilDirection A p *
            guePencilResolvent A₀ A x z) (u, k) (v, k)‖ := norm_mul_le _ _
    _ ≤ ‖(N : ℂ)⁻¹‖ * ∑ k : Fin N,
          ‖(guePencilResolvent A₀ A x z * guePencilDirection A p *
            guePencilResolvent A₀ A x z) (u, k) (v, k)‖ := by
        exact mul_le_mul_of_nonneg_left (norm_sum_le _ _) (norm_nonneg _)
    _ ≤ ‖(N : ℂ)⁻¹‖ * ∑ _k : Fin N, |z.im|⁻¹ ^ 2 * ‖guePencilDirection A p‖ := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun k _ => hentry k)
          (norm_nonneg _)
    _ = |z.im|⁻¹ ^ 2 * ‖guePencilDirection A p‖ := by
        rw [norm_inv, Complex.norm_natCast, Finset.sum_const, Finset.card_univ,
          Fintype.card_fin, nsmul_eq_mul]
        field_simp


/-! ### The unit vector at a coordinate and the sparse contraction bound -/

/-- The standard unit vector at a coordinate `(d × Fin N)`. -/
def unitVec (a : d × Fin N) : d × Fin N → ℂ := fun b => if b = a then 1 else 0

lemma sum_unitVec_norm_sq (a : d × Fin N) : ∑ b : d × Fin N, ‖unitVec a b‖ ^ 2 = 1 := by
  rw [Finset.sum_eq_single a]
  · simp [unitVec]
  · intro b _ hb
    simp [unitVec, hb]
  · intro h
    simp at h

lemma sum_unitVec_mul (X : CStarMatrix (d × Fin N) (d × Fin N) ℂ) (a b : d × Fin N) :
    (∑ x : d × Fin N, ∑ y : d × Fin N,
      star (unitVec a x) * X x y * unitVec b y) = X a b := by
  simp only [unitVec]
  rw [Finset.sum_eq_single a]
  · rw [Finset.sum_eq_single b]
    · simp
    · intro y _ hy
      simp [hy]
    · intro h
      simp at h
  · intro x _ hx
    simp [hx]
  · intro h
    simp at h

/-- The entry of `R D_p R` is the sparse pairing against the `k`-th row and column of `R`. -/
lemma partialTrace_dir_entry_eq_pairing (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    (x : GUECoord ι N → ℝ) (z : ℂ) (u v : d) (k : Fin N) (p : GUECoord ι N) :
    (guePencilResolvent A₀ A x z * guePencilDirection A p *
        guePencilResolvent A₀ A x z) (u, k) (v, k)
      = ∑ l : d × Fin N, ∑ m : d × Fin N,
          rowComb (guePencilResolvent A₀ A x z) (unitVec (u, k)) l *
            guePencilDirection A p l m *
            matVec (guePencilResolvent A₀ A x z) (unitVec (v, k)) m := by
  rw [Finset.sum_comm, ← pairing_mul_eq]
  exact (sum_unitVec_mul _ (u, k) (v, k)).symm

/-- **Sparse contraction bound for the partial-trace derivative.**  For every `x`,
the sum over all Gaussian coordinates of the squared complex coordinate derivatives of
`T_N(z)_{uv}` is at most `2 gueScale² ∑ frob(A_i)² (im z)⁻⁴`. -/
lemma sum_sq_guePartialTraceDir_le (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    (hA₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian)
    (x : GUECoord ι N → ℝ) (z : ℂ) (hz : 0 < z.im) (hN : 0 < N) (u v : d) :
    ∑ p : GUECoord ι N, ‖guePartialTraceDir A₀ A z u v p x‖ ^ 2
      ≤ 2 * (gueScale N) ^ 2 * (∑ i, (frob (A i)) ^ 2) * ((z.im)⁻¹) ^ 4 := by
  classical
  set R := guePencilResolvent A₀ A x z with hR
  set η : ℝ := (z.im)⁻¹ with hη
  have hη0 : 0 < η := by
    rw [hη]
    positivity
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hNne : (N : ℝ) ≠ 0 := hNpos.ne'
  -- per-`k` sparse bound
  have hWbound : ∀ k : Fin N,
      ∑ l : d × Fin N, ‖rowComb R (unitVec (u, k)) l‖ ^ 2 ≤ η ^ 2 := by
    intro k
    have h := sum_sq_rowComb_le A₀ A hA₀ hA z hz (unitVec (u, k)) x
    have h1 : ∑ l : d × Fin N, ‖unitVec (u, k) l‖ ^ 2 = 1 := sum_unitVec_norm_sq (u, k)
    simpa [hR, hη, h1] using h
  have hZbound : ∀ k : Fin N,
      ∑ l : d × Fin N, ‖matVec R (unitVec (v, k)) l‖ ^ 2 ≤ η ^ 2 := by
    intro k
    have h := sum_sq_matVec_le A₀ A hA₀ hA z hz (unitVec (v, k)) x
    have h1 : ∑ l : d × Fin N, ‖unitVec (v, k) l‖ ^ 2 = 1 := sum_unitVec_norm_sq (v, k)
    simpa [hR, hη, h1] using h
  have hk : ∀ k : Fin N,
      ∑ p : GUECoord ι N, ‖(R * guePencilDirection A p * R) (u, k) (v, k)‖ ^ 2
        ≤ 2 * (gueScale N) ^ 2 * (∑ i, (frob (A i)) ^ 2) * η ^ 4 := by
    intro k
    have h := sum_sq_direction_pairing_le A
      (rowComb R (unitVec (u, k))) (matVec R (unitVec (v, k)))
    have hsummand : ∀ p : GUECoord ι N,
        (R * guePencilDirection A p * R) (u, k) (v, k)
          = ∑ l : d × Fin N, ∑ m : d × Fin N,
              rowComb R (unitVec (u, k)) l * guePencilDirection A p l m *
                matVec R (unitVec (v, k)) m :=
      fun p => partialTrace_dir_entry_eq_pairing A₀ A x z u v k p
    rw [show (∑ p : GUECoord ι N,
        ‖(R * guePencilDirection A p * R) (u, k) (v, k)‖ ^ 2)
        = ∑ p : GUECoord ι N,
            ‖∑ l : d × Fin N, ∑ m : d × Fin N,
              rowComb R (unitVec (u, k)) l * guePencilDirection A p l m *
                matVec R (unitVec (v, k)) m‖ ^ 2 from by
      exact Finset.sum_congr rfl fun p _ => by rw [hsummand p]]
    refine h.trans ?_
    have hW := hWbound k
    have hZ := hZbound k
    have hW0 : 0 ≤ ∑ l : d × Fin N, ‖rowComb R (unitVec (u, k)) l‖ ^ 2 :=
      Finset.sum_nonneg fun l _ => sq_nonneg _
    have hZ0 : 0 ≤ ∑ l : d × Fin N, ‖matVec R (unitVec (v, k)) l‖ ^ 2 :=
      Finset.sum_nonneg fun l _ => sq_nonneg _
    have hfac : 2 * (gueScale N) ^ 2 * (∑ i, (frob (A i)) ^ 2) *
        (∑ l : d × Fin N, ‖rowComb R (unitVec (u, k)) l‖ ^ 2) *
        (∑ l : d × Fin N, ‖matVec R (unitVec (v, k)) l‖ ^ 2)
        ≤ 2 * (gueScale N) ^ 2 * (∑ i, (frob (A i)) ^ 2) * η ^ 2 * η ^ 2 := by
      have h1 : 2 * (gueScale N) ^ 2 * (∑ i, (frob (A i)) ^ 2) *
          (∑ l : d × Fin N, ‖rowComb R (unitVec (u, k)) l‖ ^ 2) *
          (∑ l : d × Fin N, ‖matVec R (unitVec (v, k)) l‖ ^ 2)
          ≤ 2 * (gueScale N) ^ 2 * (∑ i, (frob (A i)) ^ 2) *
            (∑ l : d × Fin N, ‖rowComb R (unitVec (u, k)) l‖ ^ 2) * η ^ 2 :=
        mul_le_mul_of_nonneg_left hZ (by positivity)
      have h2 : 2 * (gueScale N) ^ 2 * (∑ i, (frob (A i)) ^ 2) *
          (∑ l : d × Fin N, ‖rowComb R (unitVec (u, k)) l‖ ^ 2) * η ^ 2
          ≤ 2 * (gueScale N) ^ 2 * (∑ i, (frob (A i)) ^ 2) * η ^ 2 * η ^ 2 := by
        calc 2 * (gueScale N) ^ 2 * (∑ i, (frob (A i)) ^ 2) *
              (∑ l : d × Fin N, ‖rowComb R (unitVec (u, k)) l‖ ^ 2) * η ^ 2
            = (2 * (gueScale N) ^ 2 * (∑ i, (frob (A i)) ^ 2)) *
                ((∑ l : d × Fin N, ‖rowComb R (unitVec (u, k)) l‖ ^ 2) * η ^ 2) := by
                ring
          _ ≤ (2 * (gueScale N) ^ 2 * (∑ i, (frob (A i)) ^ 2)) * (η ^ 2 * η ^ 2) :=
              mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_right hW (by positivity)) (by positivity)
          _ = 2 * (gueScale N) ^ 2 * (∑ i, (frob (A i)) ^ 2) * η ^ 2 * η ^ 2 := by
              ring
      exact h1.trans h2
    calc 2 * (gueScale N) ^ 2 * (∑ i, (frob (A i)) ^ 2) *
          (∑ l : d × Fin N, ‖rowComb R (unitVec (u, k)) l‖ ^ 2) *
          (∑ l : d × Fin N, ‖matVec R (unitVec (v, k)) l‖ ^ 2)
        ≤ 2 * (gueScale N) ^ 2 * (∑ i, (frob (A i)) ^ 2) * η ^ 2 * η ^ 2 := hfac
      _ = 2 * (gueScale N) ^ 2 * (∑ i, (frob (A i)) ^ 2) * η ^ 4 := by ring
  -- Cauchy–Schwarz over `k` and exchange of the two sums
  have hterm : ∀ p : GUECoord ι N,
      ‖guePartialTraceDir A₀ A z u v p x‖ ^ 2
        ≤ ((N : ℝ)⁻¹ * ∑ k : Fin N,
            ‖(R * guePencilDirection A p * R) (u, k) (v, k)‖) ^ 2 := by
    intro p
    have hnorm : ‖guePartialTraceDir A₀ A z u v p x‖
        ≤ (N : ℝ)⁻¹ * ∑ k : Fin N,
            ‖(R * guePencilDirection A p * R) (u, k) (v, k)‖ := by
      calc ‖guePartialTraceDir A₀ A z u v p x‖
          = ‖(N : ℂ)⁻¹ * ∑ k : Fin N,
              (R * guePencilDirection A p * R) (u, k) (v, k)‖ := by rw [guePartialTraceDir, hR]
        _ ≤ ‖(N : ℂ)⁻¹‖ * ‖∑ k : Fin N,
              (R * guePencilDirection A p * R) (u, k) (v, k)‖ := norm_mul_le _ _
        _ = (N : ℝ)⁻¹ * ‖∑ k : Fin N,
              (R * guePencilDirection A p * R) (u, k) (v, k)‖ := by
              rw [norm_inv, Complex.norm_natCast]
        _ ≤ (N : ℝ)⁻¹ * ∑ k : Fin N,
              ‖(R * guePencilDirection A p * R) (u, k) (v, k)‖ := by
              exact mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
    exact pow_le_pow_left₀ (norm_nonneg _) hnorm 2
  calc ∑ p : GUECoord ι N, ‖guePartialTraceDir A₀ A z u v p x‖ ^ 2
      ≤ ∑ p : GUECoord ι N, ((N : ℝ)⁻¹ * ∑ k : Fin N,
          ‖(R * guePencilDirection A p * R) (u, k) (v, k)‖) ^ 2 :=
        Finset.sum_le_sum fun p _ => hterm p
    _ = ((N : ℝ)⁻¹) ^ 2 * ∑ p : GUECoord ι N,
          (∑ k : Fin N, ‖(R * guePencilDirection A p * R) (u, k) (v, k)‖) ^ 2 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro p _
        ring
    _ ≤ ((N : ℝ)⁻¹) ^ 2 * ∑ p : GUECoord ι N,
          ((N : ℝ) * ∑ k : Fin N,
            ‖(R * guePencilDirection A p * R) (u, k) (v, k)‖ ^ 2) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        apply Finset.sum_le_sum
        intro p _
        have := Finset.sum_mul_sq_le_sq_mul_sq (s := Finset.univ)
          (f := fun _ : Fin N => (1 : ℝ))
          (g := fun k : Fin N => ‖(R * guePencilDirection A p * R) (u, k) (v, k)‖)
        simpa [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using this
    _ = ((N : ℝ)⁻¹) ^ 2 * (N : ℝ) * ∑ p : GUECoord ι N,
          ∑ k : Fin N, ‖(R * guePencilDirection A p * R) (u, k) (v, k)‖ ^ 2 := by
        have hN : ∀ (g : GUECoord ι N → ℝ),
            (∑ p : GUECoord ι N, (N : ℝ) * g p) = (N : ℝ) * ∑ p, g p := by
          intro g
          rw [Finset.mul_sum]
        rw [hN]
        ring
    _ = ((N : ℝ)⁻¹) ^ 2 * (N : ℝ) * ∑ k : Fin N,
          ∑ p : GUECoord ι N, ‖(R * guePencilDirection A p * R) (u, k) (v, k)‖ ^ 2 := by
        rw [Finset.sum_comm]
    _ ≤ ((N : ℝ)⁻¹) ^ 2 * (N : ℝ) * ∑ _k : Fin N,
          (2 * (gueScale N) ^ 2 * (∑ i, (frob (A i)) ^ 2) * η ^ 4) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact Finset.sum_le_sum fun k _ => hk k
    _ = 2 * (gueScale N) ^ 2 * (∑ i, (frob (A i)) ^ 2) * η ^ 4 := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        have hNin : ((N : ℝ)⁻¹) ^ 2 * (N : ℝ) * (N : ℝ) = 1 := by
          field_simp
        calc ((N : ℝ)⁻¹) ^ 2 * (N : ℝ) * ((N : ℝ) * (2 * (gueScale N) ^ 2 *
              (∑ i, (frob (A i)) ^ 2) * η ^ 4))
            = (((N : ℝ)⁻¹) ^ 2 * (N : ℝ) * (N : ℝ)) *
                (2 * (gueScale N) ^ 2 * (∑ i, (frob (A i)) ^ 2) * η ^ 4) := by ring
          _ = 2 * (gueScale N) ^ 2 * (∑ i, (frob (A i)) ^ 2) * η ^ 4 := by
              rw [hNin, one_mul]


/-- Real-part form of the contraction bound. -/
lemma sum_sq_guePartialTraceDir_re_le (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    (hA₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian)
    (x : GUECoord ι N → ℝ) (z : ℂ) (hz : 0 < z.im) (hN : 0 < N) (u v : d) :
    ∑ p : GUECoord ι N, (guePartialTraceDir A₀ A z u v p x).re ^ 2
      ≤ 2 * (gueScale N) ^ 2 * (∑ i, (frob (A i)) ^ 2) * ((z.im)⁻¹) ^ 4 := by
  refine (Finset.sum_le_sum fun p _ => ?_).trans
    (sum_sq_guePartialTraceDir_le A₀ A hA₀ hA x z hz hN u v)
  have h := Complex.abs_re_le_norm (guePartialTraceDir A₀ A z u v p x)
  have h2 := pow_le_pow_left₀ (abs_nonneg _) h 2
  simpa [sq_abs] using h2

/-- Imaginary-part form of the contraction bound. -/
lemma sum_sq_guePartialTraceDir_im_le (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    (hA₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian)
    (x : GUECoord ι N → ℝ) (z : ℂ) (hz : 0 < z.im) (hN : 0 < N) (u v : d) :
    ∑ p : GUECoord ι N, (guePartialTraceDir A₀ A z u v p x).im ^ 2
      ≤ 2 * (gueScale N) ^ 2 * (∑ i, (frob (A i)) ^ 2) * ((z.im)⁻¹) ^ 4 := by
  refine (Finset.sum_le_sum fun p _ => ?_).trans
    (sum_sq_guePartialTraceDir_le A₀ A hA₀ hA x z hz hN u v)
  have h := Complex.abs_im_le_norm (guePartialTraceDir A₀ A z u v p x)
  have h2 := pow_le_pow_left₀ (abs_nonneg _) h 2
  simpa [sq_abs] using h2

/-! ### Milestone (a)(1): the Poincaré variance bound -/

/-- **Variance bound for the real part of a partial-trace entry.**  For `0 < im z`,

`Var(Re T_N(z)_{uv}) ≤ 2 * gueScale(N)^2 * (∑ i, frob(A_i)^2) * (im z)⁻⁴`.

Since `gueScale(N)^2 = 1/N`, the right-hand side is `O(1/N)`; no concentration or comparison
with the limit Dyson equation is assumed. -/
theorem variance_partialTrace_re_le (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    (hA₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian)
    (z : ℂ) (hz : 0 < z.im) (hN : 0 < N) (u v : d) :
    variance (fun x : EuclideanSpace ℝ (GUECoord ι N) =>
        (guePartialTrace A₀ A z (x : GUECoord ι N → ℝ) u v).re)
      (stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))
      ≤ 2 * (gueScale N) ^ 2 * (∑ i, (frob (A i)) ^ 2) * ((z.im)⁻¹) ^ 4 := by
  classical
  set μ := stdGaussian (EuclideanSpace ℝ (GUECoord ι N))
  set C : ℝ := 2 * (gueScale N) ^ 2 * (∑ i, (frob (A i)) ^ 2) * ((z.im)⁻¹) ^ 4 with hC
  set F : EuclideanSpace ℝ (GUECoord ι N) → ℝ := fun x =>
    (guePartialTrace A₀ A z (x : GUECoord ι N → ℝ) u v).re with hFdef
  set D : GUECoord ι N → EuclideanSpace ℝ (GUECoord ι N) → ℝ := fun p x =>
    (guePartialTraceDir A₀ A z u v p (x : GUECoord ι N → ℝ)).re with hDdef
  have hz' : z.im ≠ 0 := ne_of_gt hz
  have hFcont : Continuous F := by
    rw [hFdef]
    exact Complex.continuous_re.comp (continuous_guePartialTrace_entry A₀ A hA₀ hA z hz' u v)
  have hFmem : MemLp F 2 μ := by
    refine MemLp.of_bound hFcont.aestronglyMeasurable ((z.im)⁻¹) ?_
    filter_upwards with x
    calc ‖F x‖ = |(guePartialTrace A₀ A z (x : GUECoord ι N → ℝ) u v).re| := rfl
      _ ≤ ‖guePartialTrace A₀ A z (x : GUECoord ι N → ℝ) u v‖ := Complex.abs_re_le_norm _
      _ ≤ |z.im|⁻¹ := norm_guePartialTrace_entry_le A₀ A hA₀ hA _ z hz' hN u v
      _ = (z.im)⁻¹ := by rw [abs_of_pos hz]
  have hDcont : ∀ p : GUECoord ι N, Continuous (D p) := by
    intro p
    rw [hDdef]
    exact Complex.continuous_re.comp
      (continuous_guePartialTraceDir_entry A₀ A hA₀ hA z hz' u v p)
  have hDmem : ∀ p : GUECoord ι N, MemLp (D p) 2 μ := by
    intro p
    refine MemLp.of_bound (hDcont p).aestronglyMeasurable
      ((z.im)⁻¹ ^ 2 * ‖guePencilDirection A p‖) ?_
    filter_upwards with x
    calc ‖D p x‖ = |(guePartialTraceDir A₀ A z u v p (x : GUECoord ι N → ℝ)).re| := rfl
      _ ≤ ‖guePartialTraceDir A₀ A z u v p (x : GUECoord ι N → ℝ)‖ :=
          Complex.abs_re_le_norm _
      _ ≤ |z.im|⁻¹ ^ 2 * ‖guePencilDirection A p‖ :=
          norm_guePartialTraceDir_le A₀ A hA₀ hA _ z hz' hN u v p
      _ = (z.im)⁻¹ ^ 2 * ‖guePencilDirection A p‖ := by rw [abs_of_pos hz]
  have hderiv : ∀ p : GUECoord ι N, ∀ᵐ x ∂μ, ∀ t : ℝ,
      HasDerivAt (fun u : ℝ => F (WithLp.toLp 2 (Function.update (WithLp.ofLp x) p u)))
        (D p (WithLp.toLp 2 (Function.update (WithLp.ofLp x) p t))) t := by
    intro p
    filter_upwards with x t
    have h := hasDerivAt_guePartialTrace_entry_update A₀ A hA₀ hA
      (WithLp.ofLp x) p z hz' t u v
    have hre := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t h
    have hfun : (fun s : ℝ => F (WithLp.toLp 2 (Function.update (WithLp.ofLp x) p s)))
        = fun s : ℝ =>
            (guePartialTrace A₀ A z (Function.update (WithLp.ofLp x) p s) u v).re := by
      funext s
      simp [F, hFdef]
    have hDval : D p (WithLp.toLp 2 (Function.update (WithLp.ofLp x) p t))
        = (guePartialTraceDir A₀ A z u v p (Function.update (WithLp.ofLp x) p t)).re := by
      simp [D, hDdef]
    rw [hfun, hDval]
    exact hre
  have hpoly : ∀ p : GUECoord ι N, ∀ᵐ x ∂μ,
      PolyGrowth (fun u : ℝ => F (WithLp.toLp 2 (Function.update (WithLp.ofLp x) p u))) ∧
        PolyGrowth (fun u : ℝ => D p (WithLp.toLp 2 (Function.update (WithLp.ofLp x) p u))) := by
    intro p
    filter_upwards with x
    constructor
    · apply polyGrowth_of_bound (C := (z.im)⁻¹)
      intro t
      calc |F (WithLp.toLp 2 (Function.update (WithLp.ofLp x) p t))|
          ≤ ‖guePartialTrace A₀ A z
              (Function.update (WithLp.ofLp x) p t) u v‖ := by
            simp only [F, hFdef, WithLp.ofLp_toLp]
            exact Complex.abs_re_le_norm _
        _ ≤ |z.im|⁻¹ := norm_guePartialTrace_entry_le A₀ A hA₀ hA _ z hz' hN u v
        _ = (z.im)⁻¹ := by rw [abs_of_pos hz]
    · apply polyGrowth_of_bound (C := (z.im)⁻¹ ^ 2 * ‖guePencilDirection A p‖)
      intro t
      calc |D p (WithLp.toLp 2 (Function.update (WithLp.ofLp x) p t))|
          ≤ ‖guePartialTraceDir A₀ A z u v p
              (Function.update (WithLp.ofLp x) p t)‖ := by
            simp only [D, hDdef, WithLp.ofLp_toLp]
            exact Complex.abs_re_le_norm _
        _ ≤ |z.im|⁻¹ ^ 2 * ‖guePencilDirection A p‖ :=
            norm_guePartialTraceDir_le A₀ A hA₀ hA _ z hz' hN u v p
        _ = (z.im)⁻¹ ^ 2 * ‖guePencilDirection A p‖ := by rw [abs_of_pos hz]
  have hpoincare := gaussian_poincare_stdGaussian (F := F) (D := D)
    hFmem hDmem hderiv hpoly
  refine hpoincare.trans ?_
  have hcontr : ∀ x : EuclideanSpace ℝ (GUECoord ι N), ∑ p : GUECoord ι N, (D p x) ^ 2 ≤ C := by
    intro x
    have h := sum_sq_guePartialTraceDir_re_le A₀ A hA₀ hA
      (x : GUECoord ι N → ℝ) z hz hN u v
    simpa [D, hDdef, C, hC] using h
  have hle : (∑ p : GUECoord ι N, ∫ x, (D p x) ^ 2 ∂μ) ≤ C := by
    rw [← integral_finsetSum]
    · calc ∫ x, ∑ p : GUECoord ι N, (D p x) ^ 2 ∂μ
          ≤ ∫ _x, C ∂μ :=
            integral_mono (integrable_finsetSum _ fun p _ => (hDmem p).integrable_sq)
              (integrable_const C) (fun x => hcontr x)
        _ = C := by
            rw [integral_const]
            simp [μ]
    · intro p _
      exact (hDmem p).integrable_sq
  simpa [C, hC] using hle

/-- **Variance bound for the imaginary part of a partial-trace entry.**  For `0 < im z`,

`Var(Im T_N(z)_{uv}) ≤ 2 * gueScale(N)^2 * (∑ i, frob(A_i)^2) * (im z)⁻⁴`.

Since `gueScale(N)^2 = 1/N`, the right-hand side is `O(1/N)`; no concentration or comparison
with the limit Dyson equation is assumed. -/
theorem variance_partialTrace_im_le (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    (hA₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian)
    (z : ℂ) (hz : 0 < z.im) (hN : 0 < N) (u v : d) :
    variance (fun x : EuclideanSpace ℝ (GUECoord ι N) =>
        (guePartialTrace A₀ A z (x : GUECoord ι N → ℝ) u v).im)
      (stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))
      ≤ 2 * (gueScale N) ^ 2 * (∑ i, (frob (A i)) ^ 2) * ((z.im)⁻¹) ^ 4 := by
  classical
  set μ := stdGaussian (EuclideanSpace ℝ (GUECoord ι N))
  set C : ℝ := 2 * (gueScale N) ^ 2 * (∑ i, (frob (A i)) ^ 2) * ((z.im)⁻¹) ^ 4 with hC
  set F : EuclideanSpace ℝ (GUECoord ι N) → ℝ := fun x =>
    (guePartialTrace A₀ A z (x : GUECoord ι N → ℝ) u v).im with hFdef
  set D : GUECoord ι N → EuclideanSpace ℝ (GUECoord ι N) → ℝ := fun p x =>
    (guePartialTraceDir A₀ A z u v p (x : GUECoord ι N → ℝ)).im with hDdef
  have hz' : z.im ≠ 0 := ne_of_gt hz
  have hFcont : Continuous F := by
    rw [hFdef]
    exact Complex.continuous_im.comp (continuous_guePartialTrace_entry A₀ A hA₀ hA z hz' u v)
  have hFmem : MemLp F 2 μ := by
    refine MemLp.of_bound hFcont.aestronglyMeasurable ((z.im)⁻¹) ?_
    filter_upwards with x
    calc ‖F x‖ = |(guePartialTrace A₀ A z (x : GUECoord ι N → ℝ) u v).im| := rfl
      _ ≤ ‖guePartialTrace A₀ A z (x : GUECoord ι N → ℝ) u v‖ := Complex.abs_im_le_norm _
      _ ≤ |z.im|⁻¹ := norm_guePartialTrace_entry_le A₀ A hA₀ hA _ z hz' hN u v
      _ = (z.im)⁻¹ := by rw [abs_of_pos hz]
  have hDcont : ∀ p : GUECoord ι N, Continuous (D p) := by
    intro p
    rw [hDdef]
    exact Complex.continuous_im.comp
      (continuous_guePartialTraceDir_entry A₀ A hA₀ hA z hz' u v p)
  have hDmem : ∀ p : GUECoord ι N, MemLp (D p) 2 μ := by
    intro p
    refine MemLp.of_bound (hDcont p).aestronglyMeasurable
      ((z.im)⁻¹ ^ 2 * ‖guePencilDirection A p‖) ?_
    filter_upwards with x
    calc ‖D p x‖ = |(guePartialTraceDir A₀ A z u v p (x : GUECoord ι N → ℝ)).im| := rfl
      _ ≤ ‖guePartialTraceDir A₀ A z u v p (x : GUECoord ι N → ℝ)‖ :=
          Complex.abs_im_le_norm _
      _ ≤ |z.im|⁻¹ ^ 2 * ‖guePencilDirection A p‖ :=
          norm_guePartialTraceDir_le A₀ A hA₀ hA _ z hz' hN u v p
      _ = (z.im)⁻¹ ^ 2 * ‖guePencilDirection A p‖ := by rw [abs_of_pos hz]
  have hderiv : ∀ p : GUECoord ι N, ∀ᵐ x ∂μ, ∀ t : ℝ,
      HasDerivAt (fun u : ℝ => F (WithLp.toLp 2 (Function.update (WithLp.ofLp x) p u)))
        (D p (WithLp.toLp 2 (Function.update (WithLp.ofLp x) p t))) t := by
    intro p
    filter_upwards with x t
    have h := hasDerivAt_guePartialTrace_entry_update A₀ A hA₀ hA
      (WithLp.ofLp x) p z hz' t u v
    have hre := Complex.imCLM.hasFDerivAt.comp_hasDerivAt t h
    have hfun : (fun s : ℝ => F (WithLp.toLp 2 (Function.update (WithLp.ofLp x) p s)))
        = fun s : ℝ =>
            (guePartialTrace A₀ A z (Function.update (WithLp.ofLp x) p s) u v).im := by
      funext s
      simp [F, hFdef]
    have hDval : D p (WithLp.toLp 2 (Function.update (WithLp.ofLp x) p t))
        = (guePartialTraceDir A₀ A z u v p (Function.update (WithLp.ofLp x) p t)).im := by
      simp [D, hDdef]
    rw [hfun, hDval]
    exact hre
  have hpoly : ∀ p : GUECoord ι N, ∀ᵐ x ∂μ,
      PolyGrowth (fun u : ℝ => F (WithLp.toLp 2 (Function.update (WithLp.ofLp x) p u))) ∧
        PolyGrowth (fun u : ℝ => D p (WithLp.toLp 2 (Function.update (WithLp.ofLp x) p u))) := by
    intro p
    filter_upwards with x
    constructor
    · apply polyGrowth_of_bound (C := (z.im)⁻¹)
      intro t
      calc |F (WithLp.toLp 2 (Function.update (WithLp.ofLp x) p t))|
          ≤ ‖guePartialTrace A₀ A z
              (Function.update (WithLp.ofLp x) p t) u v‖ := by
            simp only [F, hFdef, WithLp.ofLp_toLp]
            exact Complex.abs_im_le_norm _
        _ ≤ |z.im|⁻¹ := norm_guePartialTrace_entry_le A₀ A hA₀ hA _ z hz' hN u v
        _ = (z.im)⁻¹ := by rw [abs_of_pos hz]
    · apply polyGrowth_of_bound (C := (z.im)⁻¹ ^ 2 * ‖guePencilDirection A p‖)
      intro t
      calc |D p (WithLp.toLp 2 (Function.update (WithLp.ofLp x) p t))|
          ≤ ‖guePartialTraceDir A₀ A z u v p
              (Function.update (WithLp.ofLp x) p t)‖ := by
            simp only [D, hDdef, WithLp.ofLp_toLp]
            exact Complex.abs_im_le_norm _
        _ ≤ |z.im|⁻¹ ^ 2 * ‖guePencilDirection A p‖ :=
            norm_guePartialTraceDir_le A₀ A hA₀ hA _ z hz' hN u v p
        _ = (z.im)⁻¹ ^ 2 * ‖guePencilDirection A p‖ := by rw [abs_of_pos hz]
  have hpoincare := gaussian_poincare_stdGaussian (F := F) (D := D)
    hFmem hDmem hderiv hpoly
  refine hpoincare.trans ?_
  have hcontr : ∀ x : EuclideanSpace ℝ (GUECoord ι N), ∑ p : GUECoord ι N, (D p x) ^ 2 ≤ C := by
    intro x
    have h := sum_sq_guePartialTraceDir_im_le A₀ A hA₀ hA
      (x : GUECoord ι N → ℝ) z hz hN u v
    simpa [D, hDdef, C, hC] using h
  have hle : (∑ p : GUECoord ι N, ∫ x, (D p x) ^ 2 ∂μ) ≤ C := by
    rw [← integral_finsetSum]
    · calc ∫ x, ∑ p : GUECoord ι N, (D p x) ^ 2 ∂μ
          ≤ ∫ _x, C ∂μ :=
            integral_mono (integrable_finsetSum _ fun p _ => (hDmem p).integrable_sq)
              (integrable_const C) (fun x => hcontr x)
        _ = C := by
            rw [integral_const]
            simp [μ]
    · intro p _
      exact (hDmem p).integrable_sq
  simpa [C, hC] using hle


/-! ### The complex `L²` fluctuation of a partial-trace entry -/

/-- A partial-trace entry is integrable against the Gaussian measure. -/
lemma integrable_guePartialTrace_entry (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    (hA₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian)
    (z : ℂ) (hz : 0 < z.im) (hN : 0 < N) (u v : d) :
    Integrable (fun x : EuclideanSpace ℝ (GUECoord ι N) =>
      guePartialTrace A₀ A z (x : GUECoord ι N → ℝ) u v)
      (stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) := by
  refine Integrable.of_bound
    ((continuous_guePartialTrace_entry A₀ A hA₀ hA z (ne_of_gt hz) u v).aestronglyMeasurable)
    ((z.im)⁻¹) ?_
  filter_upwards with x
  calc ‖guePartialTrace A₀ A z (x : GUECoord ι N → ℝ) u v‖ ≤ |z.im|⁻¹ :=
        norm_guePartialTrace_entry_le A₀ A hA₀ hA _ z (ne_of_gt hz) hN u v
    _ = (z.im)⁻¹ := by rw [abs_of_pos hz]

/-- The real part of the mean is the integral of the real part. -/
lemma integral_re_guePartialTrace_entry (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    (hA₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian)
    (z : ℂ) (hz : 0 < z.im) (hN : 0 < N) (u v : d) :
    (gueResolventMean (N := N) A₀ A z u v).re
      = ∫ x, (guePartialTrace A₀ A z (x : GUECoord ι N → ℝ) u v).re
          ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) := by
  rw [gueResolventMean_apply]
  have h := ContinuousLinearMap.integral_comp_comm (L := Complex.reCLM)
    (φ := fun x : EuclideanSpace ℝ (GUECoord ι N) =>
      guePartialTrace A₀ A z (x : GUECoord ι N → ℝ) u v)
    (integrable_guePartialTrace_entry A₀ A hA₀ hA z hz hN u v)
  simpa [Complex.reCLM_apply] using h.symm

/-- The imaginary part of the mean is the integral of the imaginary part. -/
lemma integral_im_guePartialTrace_entry (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    (hA₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian)
    (z : ℂ) (hz : 0 < z.im) (hN : 0 < N) (u v : d) :
    (gueResolventMean (N := N) A₀ A z u v).im
      = ∫ x, (guePartialTrace A₀ A z (x : GUECoord ι N → ℝ) u v).im
          ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) := by
  rw [gueResolventMean_apply]
  have h := ContinuousLinearMap.integral_comp_comm (L := Complex.imCLM)
    (φ := fun x : EuclideanSpace ℝ (GUECoord ι N) =>
      guePartialTrace A₀ A z (x : GUECoord ι N → ℝ) u v)
    (integrable_guePartialTrace_entry A₀ A hA₀ hA z hz hN u v)
  simpa [Complex.imCLM_apply] using h.symm

/-- The mean is bounded by `1/im z`. -/
lemma norm_gueResolventMean_entry_le (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    (hA₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian)
    (z : ℂ) (hz : 0 < z.im) (hN : 0 < N) (u v : d) :
    ‖gueResolventMean (N := N) A₀ A z u v‖ ≤ (z.im)⁻¹ := by
  rw [gueResolventMean_apply]
  have hη : 0 ≤ (z.im)⁻¹ := by positivity
  calc ‖∫ x, guePartialTrace A₀ A z (x : GUECoord ι N → ℝ) u v
        ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))‖
      ≤ ∫ x, ‖guePartialTrace A₀ A z (x : GUECoord ι N → ℝ) u v‖
          ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ _x, (z.im)⁻¹ ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) := by
        refine integral_mono ?_ (integrable_const _) (fun x => ?_)
        · exact (integrable_guePartialTrace_entry A₀ A hA₀ hA z hz hN u v).norm
        · calc ‖guePartialTrace A₀ A z (x : GUECoord ι N → ℝ) u v‖
              ≤ |z.im|⁻¹ := norm_guePartialTrace_entry_le A₀ A hA₀ hA _ z (ne_of_gt hz) hN u v
            _ = (z.im)⁻¹ := by rw [abs_of_pos hz]
    _ = (z.im)⁻¹ := by simp

/-- **Complex `L²` fluctuation bound for a partial-trace entry.** -/
lemma integral_norm_sq_fluctuation_le (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    (hA₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian)
    (z : ℂ) (hz : 0 < z.im) (hN : 0 < N) (u v : d) :
    ∫ x, ‖guePartialTrace A₀ A z (x : GUECoord ι N → ℝ) u v -
        gueResolventMean (N := N) A₀ A z u v‖ ^ 2
        ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))
      ≤ 2 * (2 * (gueScale N) ^ 2 * (∑ i, (frob (A i)) ^ 2) * ((z.im)⁻¹) ^ 4) := by
  classical
  set μ := stdGaussian (EuclideanSpace ℝ (GUECoord ι N))
  set T : EuclideanSpace ℝ (GUECoord ι N) → ℂ := fun x =>
    guePartialTrace A₀ A z (x : GUECoord ι N → ℝ) u v with hT
  set m : ℂ := gueResolventMean (N := N) A₀ A z u v with hm
  have hz' : z.im ≠ 0 := ne_of_gt hz
  have hTcont : Continuous T := by
    rw [hT]
    exact continuous_guePartialTrace_entry A₀ A hA₀ hA z hz' u v
  have hTint : Integrable T μ := by
    rw [hT]
    exact integrable_guePartialTrace_entry A₀ A hA₀ hA z hz hN u v
  have hre : m.re = ∫ x, (T x).re ∂μ := by
    rw [hm, hT]
    exact integral_re_guePartialTrace_entry A₀ A hA₀ hA z hz hN u v
  have him : m.im = ∫ x, (T x).im ∂μ := by
    rw [hm, hT]
    exact integral_im_guePartialTrace_entry A₀ A hA₀ hA z hz hN u v
  have hm_bound : ‖m‖ ≤ (z.im)⁻¹ := by
    rw [hm]
    exact norm_gueResolventMean_entry_le A₀ A hA₀ hA z hz hN u v
  have hT_bound : ∀ x, ‖T x‖ ≤ (z.im)⁻¹ := by
    intro x
    rw [hT]
    calc ‖guePartialTrace A₀ A z (x : GUECoord ι N → ℝ) u v‖ ≤ |z.im|⁻¹ :=
          norm_guePartialTrace_entry_le A₀ A hA₀ hA _ z hz' hN u v
      _ = (z.im)⁻¹ := by rw [abs_of_pos hz]
  -- integrability of the two squared fluctuation pieces
  have hcont_re : Continuous (fun x => (T x).re - m.re) :=
    (Complex.continuous_re.comp hTcont).sub continuous_const
  have hcont_im : Continuous (fun x => (T x).im - m.im) :=
    (Complex.continuous_im.comp hTcont).sub continuous_const
  have hbound_re : ∀ x, ‖((T x).re - m.re) ^ 2‖ ≤ (2 * (z.im)⁻¹) ^ 2 := by
    intro x
    have h1 : |(T x).re - m.re| ≤ ‖T x‖ + ‖m‖ := by
      calc |(T x).re - m.re| = |(T x - m).re| := by simp
        _ ≤ ‖T x - m‖ := Complex.abs_re_le_norm _
        _ ≤ ‖T x‖ + ‖m‖ := norm_sub_le _ _
    have h2 : |(T x).re - m.re| ≤ 2 * (z.im)⁻¹ := by
      linarith [hT_bound x, hm_bound]
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have hh := pow_le_pow_left₀ (abs_nonneg ((T x).re - m.re)) h2 2
    rwa [sq_abs] at hh
  have hbound_im : ∀ x, ‖((T x).im - m.im) ^ 2‖ ≤ (2 * (z.im)⁻¹) ^ 2 := by
    intro x
    have h1 : |(T x).im - m.im| ≤ ‖T x‖ + ‖m‖ := by
      calc |(T x).im - m.im| = |(T x - m).im| := by simp
        _ ≤ ‖T x - m‖ := Complex.abs_im_le_norm _
        _ ≤ ‖T x‖ + ‖m‖ := norm_sub_le _ _
    have h2 : |(T x).im - m.im| ≤ 2 * (z.im)⁻¹ := by
      linarith [hT_bound x, hm_bound]
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have hh := pow_le_pow_left₀ (abs_nonneg ((T x).im - m.im)) h2 2
    rwa [sq_abs] at hh
  have hint_re : Integrable (fun x => ((T x).re - m.re) ^ 2) μ :=
    Integrable.of_bound (hcont_re.pow 2).aestronglyMeasurable ((2 * (z.im)⁻¹) ^ 2)
      (ae_of_all _ hbound_re)
  have hint_im : Integrable (fun x => ((T x).im - m.im) ^ 2) μ :=
    Integrable.of_bound (hcont_im.pow 2).aestronglyMeasurable ((2 * (z.im)⁻¹) ^ 2)
      (ae_of_all _ hbound_im)
  have hvar_re : (∫ x, ((T x).re - m.re) ^ 2 ∂μ) = variance (fun x => (T x).re) μ := by
    rw [variance_eq_integral (X := fun x => (T x).re) (μ := μ)
      (Complex.continuous_re.comp hTcont).aemeasurable]
    rw [← hre]
  have hvar_im : (∫ x, ((T x).im - m.im) ^ 2 ∂μ) = variance (fun x => (T x).im) μ := by
    rw [variance_eq_integral (X := fun x => (T x).im) (μ := μ)
      (Complex.continuous_im.comp hTcont).aemeasurable]
    rw [← him]
  calc ∫ x, ‖T x - m‖ ^ 2 ∂μ
      = ∫ x, ((T x - m).re ^ 2 + (T x - m).im ^ 2) ∂μ := by
        refine integral_congr_ae (ae_of_all _ fun x => ?_)
        show ‖T x - m‖ ^ 2 = (T x - m).re ^ 2 + (T x - m).im ^ 2
        rw [Complex.sq_norm, Complex.normSq_apply]
        ring
    _ = ∫ x, (((T x).re - m.re) ^ 2 + ((T x).im - m.im) ^ 2) ∂μ := by
        refine integral_congr_ae (ae_of_all _ fun x => ?_)
        show (T x - m).re ^ 2 + (T x - m).im ^ 2 =
          ((T x).re - m.re) ^ 2 + ((T x).im - m.im) ^ 2
        simp
    _ = ∫ x, ((T x).re - m.re) ^ 2 ∂μ + ∫ x, ((T x).im - m.im) ^ 2 ∂μ := by
        rw [integral_add hint_re hint_im]
    _ = variance (fun x => (T x).re) μ + variance (fun x => (T x).im) μ := by
        rw [hvar_re, hvar_im]
    _ ≤ (2 * (gueScale N) ^ 2 * (∑ i, (frob (A i)) ^ 2) * ((z.im)⁻¹) ^ 4) +
          (2 * (gueScale N) ^ 2 * (∑ i, (frob (A i)) ^ 2) * ((z.im)⁻¹) ^ 4) := by
        refine add_le_add ?_ ?_
        · simpa [hT] using variance_partialTrace_re_le A₀ A hA₀ hA z hz hN u v
        · simpa [hT] using variance_partialTrace_im_le A₀ A hA₀ hA z hz hN u v
    _ = 2 * (2 * (gueScale N) ^ 2 * (∑ i, (frob (A i)) ^ 2) * ((z.im)⁻¹) ^ 4) := by
        ring


/-- Cauchy–Schwarz for complex `L²` functions on a probability space. -/
lemma norm_integral_mul_le_sqrt {κ : Type*} [Fintype κ] {f g : EuclideanSpace ℝ κ → ℂ}
    (hf : MemLp f 2 (stdGaussian (EuclideanSpace ℝ κ)))
    (hg : MemLp g 2 (stdGaussian (EuclideanSpace ℝ κ))) :
    ‖∫ x, f x * g x ∂(stdGaussian (EuclideanSpace ℝ κ))‖
      ≤ Real.sqrt (∫ x, ‖f x‖ ^ 2 ∂(stdGaussian (EuclideanSpace ℝ κ))) *
        Real.sqrt (∫ x, ‖g x‖ ^ 2 ∂(stdGaussian (EuclideanSpace ℝ κ))) := by
  calc ‖∫ x, f x * g x ∂(stdGaussian (EuclideanSpace ℝ κ))‖
      ≤ ∫ x, ‖f x * g x‖ ∂(stdGaussian (EuclideanSpace ℝ κ)) :=
        norm_integral_le_integral_norm _
    _ = ∫ x, ‖f x‖ * ‖g x‖ ∂(stdGaussian (EuclideanSpace ℝ κ)) := by
        simp only [norm_mul]
    _ ≤ (∫ x, ‖f x‖ ^ (2 : ℝ) ∂(stdGaussian (EuclideanSpace ℝ κ))) ^ (1 / (2 : ℝ)) *
        (∫ x, ‖g x‖ ^ (2 : ℝ) ∂(stdGaussian (EuclideanSpace ℝ κ))) ^ (1 / (2 : ℝ)) :=
        integral_mul_norm_le_Lp_mul_Lq (p := 2) (q := 2) Real.HolderConjugate.two_two
          (by simpa using hf) (by simpa using hg)
    _ = Real.sqrt (∫ x, ‖f x‖ ^ 2 ∂(stdGaussian (EuclideanSpace ℝ κ))) *
        Real.sqrt (∫ x, ‖g x‖ ^ 2 ∂(stdGaussian (EuclideanSpace ℝ κ))) := by
        rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
        norm_num


/-- `∑_{a,b} ‖B_{ab}‖ ≤ (card d) * frob B`. -/
lemma sum_norm_entry_le_card_mul_frob (B : Matrix d d ℂ) :
    (∑ a : d, ∑ b : d, ‖B a b‖) ≤ (Fintype.card d : ℝ) * frob B := by
  have hsum_prod : (∑ p : d × d, ‖B p.1 p.2‖) = ∑ a : d, ∑ b : d, ‖B a b‖ := by
    rw [Fintype.sum_prod_type]
  have hprod_sq : (∑ p : d × d, ‖B p.1 p.2‖ ^ 2) = ∑ a : d, ∑ b : d, ‖B a b‖ ^ 2 := by
    rw [Fintype.sum_prod_type]
  have hsq : (∑ p : d × d, ‖B p.1 p.2‖) ^ 2
      ≤ (Fintype.card (d × d) : ℝ) * ∑ p : d × d, ‖B p.1 p.2‖ ^ 2 := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq (s := Finset.univ)
      (f := fun _ : d × d => (1 : ℝ)) (g := fun p : d × d => ‖B p.1 p.2‖)
    simpa [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using h
  have hcard : (Fintype.card (d × d) : ℝ) = (Fintype.card d : ℝ) ^ 2 := by
    rw [Fintype.card_prod, Nat.cast_mul]
    ring
  have hsq' : (∑ a : d, ∑ b : d, ‖B a b‖) ^ 2
      ≤ ((Fintype.card d : ℝ) * frob B) ^ 2 := by
    rw [hsum_prod, hprod_sq, hcard, ← frob_sq] at hsq
    rw [mul_pow]
    exact hsq
  have hnn : 0 ≤ ∑ a : d, ∑ b : d, ‖B a b‖ := by positivity
  calc (∑ a : d, ∑ b : d, ‖B a b‖) = Real.sqrt ((∑ a : d, ∑ b : d, ‖B a b‖) ^ 2) := by
        rw [Real.sqrt_sq hnn]
    _ ≤ Real.sqrt (((Fintype.card d : ℝ) * frob B) ^ 2) := Real.sqrt_le_sqrt hsq'
    _ = (Fintype.card d : ℝ) * frob B := by
        rw [Real.sqrt_sq (mul_nonneg (by positivity) (frob_nonneg B))]

/-- The mean-multiplication matrix in `E[T B T] - E[T] B E[T]`. -/
private lemma mul_mean_entry (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ) (z : ℂ)
    (B : Matrix d d ℂ) (u v : d) :
    (gueResolventMean (N := N) A₀ A z * B * gueResolventMean (N := N) A₀ A z) u v
      = ∑ a : d, ∑ b : d, B a b *
          (gueResolventMean (N := N) A₀ A z u a *
            gueResolventMean (N := N) A₀ A z b v) := by
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

/-- **Milestone (a)(2): covariance matrix bound.**  For Hermitian `B` (no normalization needed),

`frob (E[T_N B T_N] - E[T_N] B E[T_N]) ≤ 2 d² frob B · VarConst`,

where `VarConst = 2 gueScale(N)^2 (∑ frob(A_i)^2) (im z)⁻⁴ = O(1/N)`. -/
theorem covariance_partialTrace_mul_le (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    (hA₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian)
    (z : ℂ) (hz : 0 < z.im) (hN : 0 < N)
    (B : Matrix d d ℂ) (_hB : B.IsHermitian) :
    frob (Matrix.of (fun u v =>
        ∫ x, (guePartialTrace A₀ A z (x : GUECoord ι N → ℝ) * B *
            guePartialTrace A₀ A z (x : GUECoord ι N → ℝ)) u v
          ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N))))
      - gueResolventMean (N := N) A₀ A z * B * gueResolventMean (N := N) A₀ A z)
      ≤ 2 * (Fintype.card d : ℝ) ^ 2 * frob B *
          (2 * (gueScale N) ^ 2 * (∑ i, (frob (A i)) ^ 2) * ((z.im)⁻¹) ^ 4) := by
  classical
  set μ := stdGaussian (EuclideanSpace ℝ (GUECoord ι N))
  set T : EuclideanSpace ℝ (GUECoord ι N) → Matrix d d ℂ := fun x =>
    guePartialTrace A₀ A z (x : GUECoord ι N → ℝ) with hT
  set m : Matrix d d ℂ := gueResolventMean (N := N) A₀ A z with hm
  set vc : ℝ := 2 * (gueScale N) ^ 2 * (∑ i, (frob (A i)) ^ 2) * ((z.im)⁻¹) ^ 4 with hvc
  have hz' : z.im ≠ 0 := ne_of_gt hz
  have hvc0 : 0 ≤ vc := by
    rw [hvc]
    positivity
  have hTbdd : ∀ (x : EuclideanSpace ℝ (GUECoord ι N)) (a b : d), ‖T x a b‖ ≤ (z.im)⁻¹ := by
    intro x a b
    rw [hT]
    calc ‖guePartialTrace A₀ A z (x : GUECoord ι N → ℝ) a b‖ ≤ |z.im|⁻¹ :=
          norm_guePartialTrace_entry_le A₀ A hA₀ hA _ z hz' hN a b
      _ = (z.im)⁻¹ := by rw [abs_of_pos hz]
  have hTcont : ∀ a b : d, Continuous (fun x => T x a b) := by
    intro a b
    rw [hT]
    exact continuous_guePartialTrace_entry A₀ A hA₀ hA z hz' a b
  have hTint : ∀ a b : d, Integrable (fun x => T x a b) μ := by
    intro a b
    simpa [hT] using integrable_guePartialTrace_entry A₀ A hA₀ hA z hz hN a b
  have hTprod : ∀ a b c e : d, Integrable (fun x => T x a b * T x c e) μ := by
    intro a b c e
    exact (hTint a b).mul_bdd ((hTcont c e).aestronglyMeasurable)
      (ae_of_all _ fun x => hTbdd x c e)
  -- pointwise expansion of the matrix product
  have hpt : ∀ (u v : d) (x : EuclideanSpace ℝ (GUECoord ι N)),
      (T x * B * T x) u v = ∑ a : d, ∑ b : d, B a b * (T x u a * T x b v) := by
    intro u v x
    simp only [Matrix.mul_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    ring
  -- expansion of the integral of `T B T`
  have h1 : ∀ u v : d, (∫ x, (T x * B * T x) u v ∂μ)
      = ∑ a : d, ∑ b : d, B a b * ∫ x, T x u a * T x b v ∂μ := by
    intro u v
    rw [show (∫ x, (T x * B * T x) u v ∂μ)
        = ∫ x, ∑ a : d, ∑ b : d, B a b * (T x u a * T x b v) ∂μ from
      integral_congr_ae (ae_of_all _ (hpt u v))]
    rw [integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro a _
      rw [integral_finsetSum]
      · apply Finset.sum_congr rfl
        intro b _
        rw [integral_const_mul]
      · intro b _
        exact (hTprod u a b v).const_mul (B a b)
    · intro a _
      exact integrable_finsetSum _ fun b _ => (hTprod u a b v).const_mul (B a b)
  -- expansion of `m B m`
  have h2 : ∀ u v : d, (m * B * m) u v
      = ∑ a : d, ∑ b : d, B a b * (m u a * m b v) := by
    intro u v
    rw [hm]
    exact mul_mean_entry A₀ A z B u v
  -- the fluctuation bracket identity
  have h3 : ∀ (u v a b : d), (∫ x, T x u a * T x b v ∂μ) - m u a * m b v
      = ∫ x, (T x u a - m u a) * (T x b v - m b v) ∂μ := by
    intro u v a b
    have hma : m u a = ∫ x, T x u a ∂μ := rfl
    have hmb : m b v = ∫ x, T x b v ∂μ := rfl
    have hA1 : Integrable (fun x => T x u a * T x b v) μ := hTprod u a b v
    have hA2 : Integrable (fun x => m u a * T x b v) μ := (hTint b v).const_mul (m u a)
    have hA3 : Integrable (fun x => T x u a * m b v) μ :=
      ((hTint u a).const_mul (m b v)).congr (ae_of_all _ fun x => mul_comm _ _)
    have hA4 : Integrable (fun x => m u a * m b v) μ := integrable_const _
    have hpt' : ∀ x : EuclideanSpace ℝ (GUECoord ι N),
        (T x u a - m u a) * (T x b v - m b v)
          = (T x u a * T x b v - m u a * T x b v) -
              (T x u a * m b v - m u a * m b v) := by
      intro x
      ring
    have hcalc : (∫ x, (T x u a - m u a) * (T x b v - m b v) ∂μ)
        = (∫ x, T x u a * T x b v ∂μ) - m u a * m b v := by
      calc ∫ x, (T x u a - m u a) * (T x b v - m b v) ∂μ
          = ∫ x, ((T x u a * T x b v - m u a * T x b v) -
              (T x u a * m b v - m u a * m b v)) ∂μ :=
            integral_congr_ae (ae_of_all _ hpt')
        _ = (∫ x, (T x u a * T x b v - m u a * T x b v) ∂μ) -
              ∫ x, (T x u a * m b v - m u a * m b v) ∂μ :=
            integral_sub (hA1.sub hA2) (hA3.sub hA4)
        _ = ((∫ x, T x u a * T x b v ∂μ) - ∫ x, m u a * T x b v ∂μ) -
              ((∫ x, T x u a * m b v ∂μ) - ∫ x, m u a * m b v ∂μ) := by
            rw [integral_sub hA1 hA2, integral_sub hA3 hA4]
        _ = (∫ x, T x u a * T x b v ∂μ) - m u a * m b v := by
            rw [integral_const_mul, integral_mul_const, integral_const]
            rw [hma, hmb]
            simp
    exact hcalc.symm
  -- entrywise bound
  have hcov : ∀ (u v a b : d),
      ‖∫ x, (T x u a - m u a) * (T x b v - m b v) ∂μ‖ ≤ 2 * vc := by
    intro u v a b
    have hf : MemLp (fun x => T x u a - m u a) 2 μ := by
      refine MemLp.of_bound ((hTcont u a).sub continuous_const).aestronglyMeasurable
        (2 * (z.im)⁻¹) ?_
      filter_upwards with x
      calc ‖T x u a - m u a‖ ≤ ‖T x u a‖ + ‖m u a‖ := norm_sub_le _ _
        _ ≤ (z.im)⁻¹ + (z.im)⁻¹ := by
            refine add_le_add (hTbdd x u a) ?_
            rw [hm]
            exact norm_gueResolventMean_entry_le A₀ A hA₀ hA z hz hN u a
        _ = 2 * (z.im)⁻¹ := by ring
    have hg : MemLp (fun x => T x b v - m b v) 2 μ := by
      refine MemLp.of_bound ((hTcont b v).sub continuous_const).aestronglyMeasurable
        (2 * (z.im)⁻¹) ?_
      filter_upwards with x
      calc ‖T x b v - m b v‖ ≤ ‖T x b v‖ + ‖m b v‖ := norm_sub_le _ _
        _ ≤ (z.im)⁻¹ + (z.im)⁻¹ := by
            refine add_le_add (hTbdd x b v) ?_
            rw [hm]
            exact norm_gueResolventMean_entry_le A₀ A hA₀ hA z hz hN b v
        _ = 2 * (z.im)⁻¹ := by ring
    have hCS := norm_integral_mul_le_sqrt hf hg
    have hfint : (∫ x, ‖T x u a - m u a‖ ^ 2 ∂μ) ≤ 2 * vc := by
      rw [hm, hT, hvc]
      exact integral_norm_sq_fluctuation_le A₀ A hA₀ hA z hz hN u a
    have hgint : (∫ x, ‖T x b v - m b v‖ ^ 2 ∂μ) ≤ 2 * vc := by
      rw [hm, hT, hvc]
      exact integral_norm_sq_fluctuation_le A₀ A hA₀ hA z hz hN b v
    refine hCS.trans ?_
    have h2vc : 0 ≤ 2 * vc := by positivity
    calc Real.sqrt (∫ x, ‖T x u a - m u a‖ ^ 2 ∂μ) *
          Real.sqrt (∫ x, ‖T x b v - m b v‖ ^ 2 ∂μ)
        ≤ Real.sqrt (2 * vc) * Real.sqrt (2 * vc) := by
          refine mul_le_mul (Real.sqrt_le_sqrt hfint) (Real.sqrt_le_sqrt hgint)
            (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      _ = 2 * vc := by
          rw [Real.mul_self_sqrt h2vc]
  -- entry bound of the covariance matrix
  have hentry : ∀ u v : d,
      ‖(Matrix.of (fun u v => ∫ x, (T x * B * T x) u v ∂μ) - m * B * m) u v‖
        ≤ (Fintype.card d : ℝ) * frob B * (2 * vc) := by
    intro u v
    have hid : (Matrix.of (fun u v => ∫ x, (T x * B * T x) u v ∂μ) - m * B * m) u v
        = ∑ a : d, ∑ b : d, B a b * ∫ x,
            (T x u a - m u a) * (T x b v - m b v) ∂μ := by
      rw [Matrix.sub_apply, Matrix.of_apply, h1 u v, h2 u v]
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro a _
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro b _
      rw [← mul_sub, h3 u v a b]
    rw [hid]
    calc ‖∑ a : d, ∑ b : d, B a b * ∫ x,
          (T x u a - m u a) * (T x b v - m b v) ∂μ‖
        ≤ ∑ a : d, ∑ b : d, ‖B a b * ∫ x,
            (T x u a - m u a) * (T x b v - m b v) ∂μ‖ := by
          refine (norm_sum_le _ _).trans ?_
          exact Finset.sum_le_sum fun a _ => norm_sum_le _ _
      _ ≤ ∑ a : d, ∑ b : d, ‖B a b‖ * (2 * vc) := by
          refine Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => ?_
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_left (hcov u v a b) (norm_nonneg _)
      _ = (∑ a : d, ∑ b : d, ‖B a b‖) * (2 * vc) := by
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [Finset.sum_mul]
      _ ≤ ((Fintype.card d : ℝ) * frob B) * (2 * vc) := by
          exact mul_le_mul_of_nonneg_right (sum_norm_entry_le_card_mul_frob B) (by positivity)
  -- Frobenius norm bound from the entrywise one
  have hfrob : frob (Matrix.of (fun u v => ∫ x, (T x * B * T x) u v ∂μ) - m * B * m)
      ≤ (Fintype.card d : ℝ) * ((Fintype.card d : ℝ) * frob B * (2 * vc)) := by
    set X : ℝ := (Fintype.card d : ℝ) * frob B * (2 * vc) with hXdef
    have hX0 : 0 ≤ X := by
      rw [hXdef]
      exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (frob_nonneg B)) (by positivity)
    have hsq : (∑ u : d, ∑ v : d,
          ‖(Matrix.of (fun u v => ∫ x, (T x * B * T x) u v ∂μ) - m * B * m) u v‖ ^ 2)
        ≤ (Fintype.card d : ℝ) ^ 2 * X ^ 2 := by
      calc (∑ u : d, ∑ v : d,
            ‖(Matrix.of (fun u v => ∫ x, (T x * B * T x) u v ∂μ) - m * B * m) u v‖ ^ 2)
          ≤ ∑ u : d, ∑ v : d, X ^ 2 := by
            refine Finset.sum_le_sum fun u _ => Finset.sum_le_sum fun v _ => ?_
            exact pow_le_pow_left₀ (norm_nonneg _) (hentry u v) 2
        _ = (Fintype.card d : ℝ) * (Fintype.card d : ℝ) * X ^ 2 := by
            simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
            ring
        _ = (Fintype.card d : ℝ) ^ 2 * X ^ 2 := by ring
    rw [frob]
    calc Real.sqrt (∑ u : d, ∑ v : d,
          ‖(Matrix.of (fun u v => ∫ x, (T x * B * T x) u v ∂μ) - m * B * m) u v‖ ^ 2)
        ≤ Real.sqrt ((Fintype.card d : ℝ) ^ 2 * X ^ 2) := Real.sqrt_le_sqrt hsq
      _ = (Fintype.card d : ℝ) * X := by
          rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity), Real.sqrt_sq hX0]
      _ = (Fintype.card d : ℝ) * ((Fintype.card d : ℝ) * frob B * (2 * vc)) := by
          rw [hXdef]

  calc frob (Matrix.of (fun u v => ∫ x, (T x * B * T x) u v ∂μ) - m * B * m)
      ≤ (Fintype.card d : ℝ) * ((Fintype.card d : ℝ) * frob B * (2 * vc)) := hfrob
    _ = 2 * (Fintype.card d : ℝ) ^ 2 * frob B * vc := by ring


/-- An entry is bounded by the Frobenius norm. -/
lemma norm_entry_le_frob (M : Matrix d d ℂ) (u v : d) : ‖M u v‖ ≤ frob M := by
  have hrow : ‖M u v‖ ^ 2 ≤ ∑ b : d, ‖M u b‖ ^ 2 :=
    Finset.single_le_sum (f := fun b : d => ‖M u b‖ ^ 2) (fun b _ => by positivity)
      (Finset.mem_univ v)
  have hle : ‖M u v‖ ^ 2 ≤ ∑ a : d, ∑ b : d, ‖M a b‖ ^ 2 :=
    hrow.trans (Finset.single_le_sum (f := fun a : d => ∑ b : d, ‖M a b‖ ^ 2)
      (fun a _ => by positivity) (Finset.mem_univ u))
  calc ‖M u v‖ = Real.sqrt (‖M u v‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt (∑ a : d, ∑ b : d, ‖M a b‖ ^ 2) := Real.sqrt_le_sqrt hle
    _ = frob M := rfl

/-- A row is bounded by `sqrt (card d)` times the Frobenius norm. -/
lemma sum_norm_row_le_sqrt_card_mul_frob (A : Matrix d d ℂ) (u : d) :
    (∑ a : d, ‖A u a‖) ≤ Real.sqrt (Fintype.card d : ℝ) * frob A := by
  have hrow : ∑ a : d, ‖A u a‖ ^ 2 ≤ (frob A) ^ 2 := by
    rw [frob_sq]
    exact Finset.single_le_sum (f := fun a : d => ∑ b : d, ‖A a b‖ ^ 2)
      (fun a _ => by positivity) (Finset.mem_univ u)
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq (s := Finset.univ)
    (f := fun _ : d => (1 : ℝ)) (g := fun a : d => ‖A u a‖)
  simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    mul_one] at hCS
  have hsq : (∑ a : d, ‖A u a‖) ^ 2
      ≤ (Real.sqrt (Fintype.card d : ℝ) * frob A) ^ 2 := by
    calc (∑ a : d, ‖A u a‖) ^ 2
        ≤ (Fintype.card d : ℝ) * ∑ a : d, ‖A u a‖ ^ 2 := hCS
      _ ≤ (Fintype.card d : ℝ) * (frob A) ^ 2 := by
          exact mul_le_mul_of_nonneg_left hrow (by positivity)
      _ = (Real.sqrt (Fintype.card d : ℝ) * frob A) ^ 2 := by
          rw [mul_pow, Real.sq_sqrt (by positivity)]
  have hnn : 0 ≤ ∑ a : d, ‖A u a‖ := by positivity
  calc (∑ a : d, ‖A u a‖) = Real.sqrt ((∑ a : d, ‖A u a‖) ^ 2) :=
        (Real.sqrt_sq hnn).symm
    _ ≤ Real.sqrt ((Real.sqrt (Fintype.card d : ℝ) * frob A) ^ 2) := Real.sqrt_le_sqrt hsq
    _ = Real.sqrt (Fintype.card d : ℝ) * frob A := by
        rw [Real.sqrt_sq (mul_nonneg (Real.sqrt_nonneg _) (frob_nonneg A))]

/-- **Intermediate approximate Dyson equation (entrywise).**  The exact master identity and the
covariance bound give

`‖((z•1 - A₀) g_N - 1 - ∑ i, A_i g_N A_i g_N)_{uv}‖ = O(1/N)`.

The right-hand side is
`2 (card d)² sqrt(card d) (∑ frob(A_i)²) · VarConst` with
`VarConst = 2 gueScale(N)² (∑ frob(A_i)²) (im z)⁻⁴ = O(1/N)`. -/
theorem approximate_dyson_entry_le (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    (hA₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian)
    (z : ℂ) (hz : 0 < z.im) (hN : 0 < N) (u v : d) :
    ‖((z • (1 : Matrix d d ℂ) - A₀) * gueResolventMean (N := N) A₀ A z - 1
        - ∑ i, A i * (gueResolventMean (N := N) A₀ A z * A i *
            gueResolventMean (N := N) A₀ A z)) u v‖
      ≤ 2 * (Fintype.card d : ℝ) ^ 2 * Real.sqrt (Fintype.card d : ℝ) *
          (∑ i, (frob (A i)) ^ 2) *
          (2 * (gueScale N) ^ 2 * (∑ i, (frob (A i)) ^ 2) * ((z.im)⁻¹) ^ 4) := by
  classical
  set μ := stdGaussian (EuclideanSpace ℝ (GUECoord ι N))
  set g : Matrix d d ℂ := gueResolventMean (N := N) A₀ A z with hg
  set vc : ℝ := 2 * (gueScale N) ^ 2 * (∑ i, (frob (A i)) ^ 2) * ((z.im)⁻¹) ^ 4 with hvc
  set Mi : ι → Matrix d d ℂ := fun i => Matrix.of (fun u v =>
      ∫ x, (guePartialTrace A₀ A z (x : GUECoord ι N → ℝ) * A i *
          guePartialTrace A₀ A z (x : GUECoord ι N → ℝ)) u v ∂μ)
      - g * A i * g with hMidef
  have hvc0 : 0 ≤ vc := by
    rw [hvc]
    positivity
  have hMi : ∀ i : ι, frob (Mi i) ≤ 2 * (Fintype.card d : ℝ) ^ 2 * frob (A i) * vc := by
    intro i
    rw [hMidef, hvc, hg]
    exact covariance_partialTrace_mul_le A₀ A hA₀ hA z hz hN (A i) (hA i)
  have hexpr : ((z • (1 : Matrix d d ℂ) - A₀) * g - 1
        - ∑ i, A i * (g * A i * g)) u v
      = ∑ i, ∑ a, A i u a * (Mi i) a v := by
    have hm := gue_dyson_master_identity A₀ A hA₀ hA z (ne_of_gt hz)
      (by exact_mod_cast hN.ne')
    have h1 : ((z • (1 : Matrix d d ℂ) - A₀) * g - 1) u v
        = ∑ i, ∑ a, A i u a * (Matrix.of (fun u v =>
            ∫ x, (guePartialTrace A₀ A z (x : GUECoord ι N → ℝ) * A i *
                guePartialTrace A₀ A z (x : GUECoord ι N → ℝ)) u v ∂μ)) a v := by
      rw [hg]
      rw [show ((z • (1 : Matrix d d ℂ) - A₀) * gueResolventMean (N := N) A₀ A z - 1)
          = ∑ i, A i * (Matrix.of (fun u v =>
              ∫ x, (guePartialTrace A₀ A z (x : GUECoord ι N → ℝ) * A i *
                  guePartialTrace A₀ A z (x : GUECoord ι N → ℝ)) u v ∂μ)) from hm]
      simp only [Matrix.sum_apply, Matrix.mul_apply]
    have h2 : (∑ i, A i * (g * A i * g)) u v
        = ∑ i, ∑ a, A i u a * (g * A i * g) a v := by
      simp only [Matrix.sum_apply, Matrix.mul_apply]
    rw [Matrix.sub_apply, h1, h2]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro a _
    simp only [hMidef, Matrix.sub_apply, Matrix.of_apply]
    ring
  rw [hexpr]
  have hK : ∀ i : ι, 0 ≤ 2 * (Fintype.card d : ℝ) ^ 2 * frob (A i) * vc := by
    intro i
    exact mul_nonneg (mul_nonneg (mul_nonneg (by positivity) (by positivity))
      (frob_nonneg _)) hvc0
  calc ‖∑ i : ι, ∑ a : d, A i u a * (Mi i) a v‖
      ≤ ∑ i : ι, ∑ a : d, ‖A i u a‖ * ‖(Mi i) a v‖ := by
        refine (norm_sum_le _ _).trans ?_
        exact Finset.sum_le_sum fun i _ =>
          (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => by rw [norm_mul])
    _ ≤ ∑ i : ι, ∑ a : d, ‖A i u a‖ *
          (2 * (Fintype.card d : ℝ) ^ 2 * frob (A i) * vc) := by
        refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun a _ => ?_
        exact mul_le_mul_of_nonneg_left
          ((norm_entry_le_frob (Mi i) a v).trans (hMi i)) (norm_nonneg _)
    _ = ∑ i : ι, (∑ a : d, ‖A i u a‖) *
          (2 * (Fintype.card d : ℝ) ^ 2 * frob (A i) * vc) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.sum_mul]
    _ ≤ ∑ i : ι, (Real.sqrt (Fintype.card d : ℝ) * frob (A i)) *
          (2 * (Fintype.card d : ℝ) ^ 2 * frob (A i) * vc) := by
        refine Finset.sum_le_sum fun i _ => ?_
        exact mul_le_mul_of_nonneg_right (sum_norm_row_le_sqrt_card_mul_frob (A i) u) (hK i)
    _ = 2 * (Fintype.card d : ℝ) ^ 2 * Real.sqrt (Fintype.card d : ℝ) *
          (∑ i, (frob (A i)) ^ 2) * vc := by
        calc ∑ i : ι, (Real.sqrt (Fintype.card d : ℝ) * frob (A i)) *
              (2 * (Fintype.card d : ℝ) ^ 2 * frob (A i) * vc)
            = ∑ i : ι, (Real.sqrt (Fintype.card d : ℝ) *
                (2 * (Fintype.card d : ℝ) ^ 2)) * ((frob (A i)) ^ 2) * vc := by
              apply Finset.sum_congr rfl
              intro i _
              ring
          _ = (∑ i : ι, (Real.sqrt (Fintype.card d : ℝ) *
                (2 * (Fintype.card d : ℝ) ^ 2)) * ((frob (A i)) ^ 2)) * vc := by
              rw [Finset.sum_mul]
          _ = (Real.sqrt (Fintype.card d : ℝ) * (2 * (Fintype.card d : ℝ) ^ 2)) *
                (∑ i, (frob (A i)) ^ 2) * vc := by
              rw [Finset.mul_sum]
          _ = 2 * (Fintype.card d : ℝ) ^ 2 * Real.sqrt (Fintype.card d : ℝ) *
                (∑ i, (frob (A i)) ^ 2) * vc := by
              ring
    _ = 2 * (Fintype.card d : ℝ) ^ 2 * Real.sqrt (Fintype.card d : ℝ) *
          (∑ i, (frob (A i)) ^ 2) *
          (2 * (gueScale N) ^ 2 * (∑ i, (frob (A i)) ^ 2) * ((z.im)⁻¹) ^ 4) := by
        rw [hvc]

end

end GUEStrongConvergence
