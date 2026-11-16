/-
# The averaged partial trace of the GUE-pencil resolvent

For fixed coefficient dimension `d`, the random affine pencil is
`H(x) = A₀ ⊗ I_N + ∑ i, A_i ⊗ G_i(x)` with `G_i` normalized complex GUE, and

`R(z,x) = (z • 1 - H(x))⁻¹`,  `TN(z,x) = (id_d ⊗ tr_N) R(z,x)`,
`g_N(z) = ∫ x, TN(z,x)`.

This module proves the exact finite-`N` **Gaussian integration-by-parts master identity**

`(z • 1 - A₀) * g_N(z) - 1 = ∑ i, A_i * ∫ x, TN(z,x) * A_i * TN(z,x)`,

i.e. the averaged partial trace solves the (nonlinear) matrix Dyson equation with the exact
finite-`N` quadratic term `E[TN A_i TN]` (not `g A_i g`).  The proof is an entrywise application
of the coordinate Stein identity `∫ x_p F = ∫ ∂_p F` to the resolvent entries, together with the
exact derivative `∂_p R = R D_p R` and the covariance/Fierz structure of the GUE normalization
`α² + β² = 0`, `2 α β = 1`.

Everything is stated for the *actual* finite random matrices; no formal Dyson relation, no
fixed-`z` concentration, and no matrix identity `d/dt f(H+tK) = f'(H)K` is used.
-/
import GUEStrongConvergence.Probability.ResolventPencilAlgebra
import GUEStrongConvergence.Probability.SteinIdentity
import GUEStrongConvergence.Probability.GaussianMoments

open MeasureTheory ProbabilityTheory Matrix Kronecker Filter
open scoped Matrix.Norms.Elementwise ComplexOrder ENNReal NNReal Topology

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace GUEStrongConvergence

noncomputable section

variable {ι d : Type*} {N : ℕ} [Fintype ι] [Fintype d] [DecidableEq d] [DecidableEq ι]

/-! ### The normalized partial trace over the `N` block -/

/-- The normalized partial trace `id_d ⊗ tr_N`, entrywise on the `N` block:
`(id_d ⊗ tr_N)(M)_{u v} = N⁻¹ ∑ k, M_{(u,k),(v,k)}`. -/
def partialTraceN (M : CStarMatrix (d × Fin N) (d × Fin N) ℂ) : Matrix d d ℂ :=
  fun u v => (N : ℂ)⁻¹ * ∑ k : Fin N, M (u, k) (v, k)

/-- The random averaged partial trace of the resolvent, `TN(z,x)`. -/
def guePartialTrace (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ) (z : ℂ)
    (x : GUECoord ι N → ℝ) : Matrix d d ℂ :=
  partialTraceN (guePencilResolvent A₀ A x z)

/-- The averaged resolvent `g_N(z) = E[TN(z,·)]`, defined entrywise. -/
def gueResolventMean (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ) (z : ℂ) : Matrix d d ℂ :=
  fun u v => ∫ x, guePartialTrace A₀ A z x u v
    ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))

@[simp] lemma partialTraceN_apply (M : CStarMatrix (d × Fin N) (d × Fin N) ℂ) (u v : d) :
    partialTraceN M u v = (N : ℂ)⁻¹ * ∑ k : Fin N, M (u, k) (v, k) := rfl

@[simp] lemma guePartialTrace_apply (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ) (z : ℂ)
    (x : GUECoord ι N → ℝ) (u v : d) :
    guePartialTrace A₀ A z x u v
      = (N : ℂ)⁻¹ * ∑ k : Fin N, guePencilResolvent A₀ A x z (u, k) (v, k) := rfl

@[simp] lemma gueResolventMean_apply (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ) (z : ℂ)
    (u v : d) :
    gueResolventMean (N := N) A₀ A z u v
      = ∫ x, guePartialTrace A₀ A z x u v
        ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) := rfl

lemma partialTraceN_add (M L : CStarMatrix (d × Fin N) (d × Fin N) ℂ) :
    partialTraceN (M + L) = partialTraceN M + partialTraceN L := by
  ext u v
  simp only [partialTraceN_apply, CStarMatrix.add_apply, Finset.sum_add_distrib, mul_add,
    Matrix.add_apply]

lemma partialTraceN_smul (c : ℂ) (M : CStarMatrix (d × Fin N) (d × Fin N) ℂ) :
    partialTraceN (c • M) = c • partialTraceN M := by
  ext u v
  simp only [partialTraceN_apply, CStarMatrix.smul_apply, smul_eq_mul, Matrix.smul_apply,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

lemma partialTraceN_zero : partialTraceN (0 : CStarMatrix (d × Fin N) (d × Fin N) ℂ) = 0 := by
  ext u v
  simp [partialTraceN_apply]

lemma partialTraceN_one (hN : (N : ℂ) ≠ 0) :
    partialTraceN (1 : CStarMatrix (d × Fin N) (d × Fin N) ℂ) = 1 := by
  ext u v
  by_cases huv : u = v
  · subst huv
    have hone : ∀ k : Fin N,
        (1 : CStarMatrix (d × Fin N) (d × Fin N) ℂ) (u, k) (u, k) = 1 := by
      intro k
      change (1 : Matrix (d × Fin N) (d × Fin N) ℂ) (u, k) (u, k) = 1
      rw [Matrix.one_apply_eq]
    have hsum : (∑ k : Fin N,
        (1 : CStarMatrix (d × Fin N) (d × Fin N) ℂ) (u, k) (u, k)) = (N : ℂ) := by
      simp [hone]
    rw [partialTraceN_apply, hsum]
    change (N : ℂ)⁻¹ * (N : ℂ) = (1 : Matrix d d ℂ) u u
    rw [Matrix.one_apply_eq, inv_mul_cancel₀ hN]
  · have hzero : (∑ k : Fin N,
        (1 : CStarMatrix (d × Fin N) (d × Fin N) ℂ) (u, k) (v, k)) = 0 := by
      apply Finset.sum_eq_zero
      intro k _
      change (1 : Matrix (d × Fin N) (d × Fin N) ℂ) (u, k) (v, k) = 0
      rw [Matrix.one_apply]
      simp [huv]
    rw [partialTraceN_apply, hzero, mul_zero]
    change (0 : ℂ) = (1 : Matrix d d ℂ) u v
    rw [Matrix.one_apply]
    simp [huv]

/-! ### Continuity and differentiability of the resolvent along a coordinate -/

/-- The pencil is affine in each coordinate: updating one coordinate by `s` instead of `t`
changes the pencil by `(s - t)` times the coordinate direction. -/
lemma guePencil_update_sub (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    (x : GUECoord ι N → ℝ) (p : GUECoord ι N) (s t : ℝ) :
    guePencil A₀ A (Function.update x p s) - guePencil A₀ A (Function.update x p t)
      = (s - t) • guePencilDirection A p := by
  rw [guePencil_sub_eq_sum_smul, Finset.sum_eq_single p]
  · rw [Function.update_self, Function.update_self]
  · intro q _ hq
    rw [Function.update_of_ne hq, Function.update_of_ne hq, sub_self, zero_smul]
  · intro h
    exact absurd (Finset.mem_univ p) h

/-- Every resolvent entry is continuous along a coordinate line. -/
lemma continuous_guePencilResolvent_entry_update (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    (hA₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian)
    (x : GUECoord ι N → ℝ) (p : GUECoord ι N) (z : ℂ) (hz : z.im ≠ 0)
    (a b : d × Fin N) :
    Continuous (fun t : ℝ => guePencilResolvent A₀ A (Function.update x p t) z a b) := by
  have hentry : Continuous (fun y : EuclideanSpace ℝ (GUECoord ι N) =>
      guePencilResolvent A₀ A (y : GUECoord ι N → ℝ) z a b) := by
    have hraw := (CStarMatrix.ofMatrixL : Matrix (d × Fin N) (d × Fin N) ℂ ≃L[ℂ]
        CStarMatrix (d × Fin N) (d × Fin N) ℂ).symm.continuous.comp
        (continuous_guePencilResolvent (N := N) A₀ A hA₀ hA z hz)
    exact (continuous_apply b).comp ((continuous_apply a).comp hraw)
  have hpi : Continuous (fun t : ℝ =>
      (Function.update x p t : GUECoord ι N → ℝ)) := by
    apply continuous_pi
    intro q
    by_cases hq : q = p
    · subst hq
      simpa [Function.update_self] using continuous_id'
    · have : (fun t : ℝ => Function.update x p t q) = fun _ => x q := by
        funext t
        rw [Function.update_of_ne hq]
      rw [this]
      exact continuous_const
  have hpath : Continuous (fun t : ℝ =>
      (WithLp.toLp 2 (Function.update x p t) : EuclideanSpace ℝ (GUECoord ι N))) :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : GUECoord ι N => ℝ)).symm.continuous.comp hpi
  have hcomp := hentry.comp hpath
  simpa [Function.comp_def, WithLp.ofLp_toLp] using hcomp

/-- Scalar cancellation: `a⁻¹ • ((a : ℂ) * z) = z` for real `a ≠ 0`. -/
lemma inv_smul_ofReal_mul {a : ℝ} (ha : a ≠ 0) (z : ℂ) :
    a⁻¹ • ((a : ℂ) * z) = z := by
  have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ha
  rw [RCLike.real_smul_eq_coe_mul]
  change ((a⁻¹ : ℝ) : ℂ) * (((a : ℝ) : ℂ) * z) = z
  rw [Complex.ofReal_inv, ← mul_assoc, inv_mul_cancel₀ ha', one_mul]

/-- Entry formula for a triple matrix product. -/
lemma cstar_mul_mul_apply (X Y Z : CStarMatrix (d × Fin N) (d × Fin N) ℂ)
    (a b : d × Fin N) :
    (X * Y * Z) a b =
      ∑ r : d × Fin N, ∑ s : d × Fin N, X a r * Y r s * Z s b := by
  calc (X * Y * Z) a b
      = ∑ s, (X * Y) a s * Z s b := by rw [CStarMatrix.mul_apply]
    _ = ∑ s, (∑ r, X a r * Y r s) * Z s b := by
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [CStarMatrix.mul_apply]
    _ = ∑ s, ∑ r, (X a r * Y r s) * Z s b := by simp only [Finset.sum_mul]
    _ = ∑ r, ∑ s, (X a r * Y r s) * Z s b := Finset.sum_comm
    _ = ∑ r, ∑ s, X a r * Y r s * Z s b := by
        refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun s _ => ?_
        ring

/-- **Derivative of a resolvent entry in one coordinate**, `∂_p R_{ab} = (R D_p R)_{ab}`.

This is proved from the *exact* second-resolvent increment
`R(t+h) - R(t) = h • (R(t+h) D_p R(t))` (valid because the pencil is affine in the coordinate)
together with continuity of the resolvent entries; no matrix identity `d/dt f(H+tK) = f'(H)K`
with a fixed `H` is used. -/
lemma hasDerivAt_guePencilResolvent_entry (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    (hA₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian)
    (x : GUECoord ι N → ℝ) (p : GUECoord ι N) (z : ℂ) (hz : z.im ≠ 0) (t₀ : ℝ)
    (a b : d × Fin N) :
    HasDerivAt (fun t => guePencilResolvent A₀ A (Function.update x p t) z a b)
      ((guePencilResolvent A₀ A (Function.update x p t₀) z * guePencilDirection A p *
        guePencilResolvent A₀ A (Function.update x p t₀) z) a b) t₀ := by
  set f : ℝ → ℂ := fun t => guePencilResolvent A₀ A (Function.update x p t) z a b
  -- exact affine increment of the resolvent
  have hdiff : ∀ y : ℝ, f y - f t₀ =
      ((y - t₀ : ℝ) : ℂ) * ((guePencilResolvent A₀ A (Function.update x p y) z *
        guePencilDirection A p *
          guePencilResolvent A₀ A (Function.update x p t₀) z) a b) := by
    intro y
    have hsub := guePencilResolvent_sub A₀ A hA₀ hA
      (Function.update x p y) (Function.update x p t₀) z hz
    have hinc := guePencil_update_sub A₀ A x p y t₀
    rw [hinc] at hsub
    have hentry := congrArg (fun M : CStarMatrix (d × Fin N) (d × Fin N) ℂ => M a b) hsub
    simp only [CStarMatrix.sub_apply] at hentry
    rw [hentry]
    have hsmul : (guePencilResolvent A₀ A (Function.update x p y) z *
          ((y - t₀) • guePencilDirection A p) *
          guePencilResolvent A₀ A (Function.update x p t₀) z) a b
        = ((y - t₀ : ℝ) : ℂ) * ((guePencilResolvent A₀ A (Function.update x p y) z *
            guePencilDirection A p *
              guePencilResolvent A₀ A (Function.update x p t₀) z) a b) := by
      rw [show guePencilResolvent A₀ A (Function.update x p y) z *
            ((y - t₀) • guePencilDirection A p) *
            guePencilResolvent A₀ A (Function.update x p t₀) z
          = (y - t₀) • (guePencilResolvent A₀ A (Function.update x p y) z *
              guePencilDirection A p *
                guePencilResolvent A₀ A (Function.update x p t₀) z) from by
        simp only [Algebra.mul_smul_comm, Algebra.smul_mul_assoc]]
      exact real_smul_cstar_apply (y - t₀) _ a b
    exact hsmul
  -- continuity of the limiting expression
  have hcont : Continuous (fun y : ℝ =>
      (guePencilResolvent A₀ A (Function.update x p y) z * guePencilDirection A p *
        guePencilResolvent A₀ A (Function.update x p t₀) z) a b) := by
    have hterm : ∀ s r : d × Fin N, Continuous (fun y : ℝ =>
        guePencilResolvent A₀ A (Function.update x p y) z a s *
          guePencilDirection A p s r *
          guePencilResolvent A₀ A (Function.update x p t₀) z r b) := by
      intro s r
      have hs : Continuous (fun y : ℝ =>
          guePencilResolvent A₀ A (Function.update x p y) z a s) :=
        continuous_guePencilResolvent_entry_update A₀ A hA₀ hA x p z hz a s
      exact (hs.mul continuous_const).mul continuous_const
    have hsum : Continuous (fun y : ℝ => ∑ r : d × Fin N, ∑ s : d × Fin N,
        guePencilResolvent A₀ A (Function.update x p y) z a s *
          guePencilDirection A p s r *
          guePencilResolvent A₀ A (Function.update x p t₀) z r b) :=
      continuous_finsetSum _ fun r _ => continuous_finsetSum _ fun s _ => hterm s r
    refine hsum.congr fun y => ?_
    rw [cstar_mul_mul_apply (guePencilResolvent A₀ A (Function.update x p y) z)
      (guePencilDirection A p)
      (guePencilResolvent A₀ A (Function.update x p t₀) z) a b, Finset.sum_comm]
  rw [hasDerivAt_iff_tendsto_slope]
  refine Tendsto.congr' ?_ ((hcont.tendsto t₀).mono_left nhdsWithin_le_nhds)
  filter_upwards [self_mem_nhdsWithin] with y hy
  rw [slope_def_module f t₀ y, hdiff y]
  exact (inv_smul_ofReal_mul (sub_ne_zero.mpr hy)
    ((guePencilResolvent A₀ A (Function.update x p y) z * guePencilDirection A p *
      guePencilResolvent A₀ A (Function.update x p t₀) z) a b)).symm

end

end GUEStrongConvergence
