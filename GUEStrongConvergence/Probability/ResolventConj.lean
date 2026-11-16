/-
# Conjugation symmetry of the averaged resolvent and its limit

The weighted strip bound is proved on the upper half-plane; the strip itself is symmetric.  This
file records the `z ↦ z̄` symmetry that transfers a half-plane estimate to the other half.

## Main results

* `star_resolvent_of_star_eq` — for a self-adjoint element `P` of a `ℂ`-star-algebra,
  `star (resolvent P z) = resolvent P (star z)`;
* `frob_star`, `frob_sub_star` — the Frobenius norm is invariant under `star`;
* `guePencilResolvent_star`, `guePartialTrace_star`, `gueResolventMean_star` — the finite-side
  mean is `star`-equivariant: `(g_N(z))ᴴ = g_N(z̄)`;
* `frob_gueResolventMean_sub_limit_star_of_limit` — the deviation is conjugation invariant
  (given the same symmetry for the limit Cauchy transform);
* `weightedStripBound_lowerHalf_of_upperHalf_of_limit`,
  `weightedStripBound_of_upperHalf_of_limit` — a weighted strip bound on the upper half-plane
  transfers to the whole strip.

**Obstruction on the limit side.**  The Fock-side identity
`star (operatorMatrixPencilCauchy A₀ A z) = operatorMatrixPencilCauchy A₀ A (star z)` needs
`Ring.inverse_star` / `Matrix.star_apply` at the operator-valued matrix type
`CStarMatrix d d (WordSpace ι →L[ℂ] WordSpace ι)`.  That type carries its own `CStarMatrix.instStar`
while the generic lemmas elaborate `star` through `StarRing.toStarAddMonoid.toStar`; the two star
structures are not syntactically the same instance, so `rw` cannot fire at entry level.  The
scalar-valued case (`CStarMatrix … ℂ`, used for `gueResolventMean`) is unaffected because there
the instances agree.  Closing the limit side requires either the limit-side resolvent-star lemma
in `lean-free-prob` or a local `Star`-instance alignment; it is *not* used anywhere else in this
file.
-/
import GUEStrongConvergence.Probability.StripAnalytic

open MeasureTheory ProbabilityTheory Matrix Filter Complex FreeProbability FreeProbability.Fock
open scoped ComplexOrder Topology BigOperators ENNReal NNReal

namespace GUEStrongConvergence

noncomputable section

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

variable {ι d : Type*} [Fintype ι] [DecidableEq ι] [Fintype d] [DecidableEq d] [Nonempty d]
  {N : ℕ}

/-! ### Star and resolvent -/

/-- **Star of a resolvent.**  For a self-adjoint element `P` of a `ℂ`-star-algebra,
`star (resolvent P z) = resolvent P (star z)`. -/
theorem star_resolvent_of_star_eq {A : Type*} [Ring A] [StarRing A] [Algebra ℂ A]
    [StarModule ℂ A] {P : A} (hP : star P = P) (z : ℂ) :
    star (resolvent P z) = resolvent P (star z) := by
  unfold resolvent
  rw [← Ring.inverse_star, star_sub, hP, algebraMap_star_comm]

/-! ### The Frobenius norm is `star`-invariant -/

lemma frob_star (M : Matrix d d ℂ) : frob (star M) = frob M := by
  have h : (frob (star M)) ^ 2 = (frob M) ^ 2 := by
    rw [frob_sq, frob_sq, Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [Matrix.star_apply, norm_star]
  have h1 : 0 ≤ frob (star M) := frob_nonneg _
  have h2 : 0 ≤ frob M := frob_nonneg _
  nlinarith [h, h1, h2]

lemma frob_sub_star (M L : Matrix d d ℂ) : frob (star M - star L) = frob (M - L) := by
  rw [← star_sub, frob_star]

/-! ### The finite-side mean -/

/-- The pencil resolvent is `star`-equivariant in the spectral parameter. -/
theorem guePencilResolvent_star (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    (hA₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian)
    (x : GUECoord ι N → ℝ) (z : ℂ) :
    star (guePencilResolvent A₀ A x z) = guePencilResolvent A₀ A x (star z) :=
  star_resolvent_of_star_eq (P := guePencil A₀ A x)
    (by simpa [IsSelfAdjoint, isSelfAdjoint_iff] using guePencil_isSelfAdjoint A₀ A hA₀ hA x) z

/-- Entry form: the resolvent at `z̄` is the conjugate transpose of the resolvent at `z`. -/
lemma guePencilResolvent_star_apply (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    (hA₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian)
    (x : GUECoord ι N → ℝ) (z : ℂ) (i j : d × Fin N) :
    guePencilResolvent A₀ A x (star z) i j =
      star (guePencilResolvent A₀ A x z j i) := by
  have h := guePencilResolvent_star A₀ A hA₀ hA x z
  calc guePencilResolvent A₀ A x (star z) i j
      = (star (guePencilResolvent A₀ A x z)) i j := congrFun (congrFun h.symm i) j
    _ = star (guePencilResolvent A₀ A x z j i) := Matrix.star_apply _ i j


/-- The finite-side averaged partial trace is `star`-equivariant. -/
lemma guePartialTrace_star (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    (hA₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian)
    (x : GUECoord ι N → ℝ) (z : ℂ) (u v : d) :
    guePartialTrace A₀ A (star z) x u v = star (guePartialTrace A₀ A z x v u) := by
  have hentry : ∀ k : Fin N, guePencilResolvent A₀ A x (star z) (u, k) (v, k) =
      star (guePencilResolvent A₀ A x z (v, k) (u, k)) := fun k =>
    guePencilResolvent_star_apply A₀ A hA₀ hA x z (u, k) (v, k)
  have hL : guePartialTrace A₀ A (star z) x u v
      = (N : ℂ)⁻¹ * ∑ k : Fin N,
          star (guePencilResolvent A₀ A x z (v, k) (u, k)) := by
    simp only [guePartialTrace, partialTraceN_apply]
    exact congrArg (fun t => (N : ℂ)⁻¹ * t) (Finset.sum_congr rfl fun k _ => hentry k)
  have hR : star (guePartialTrace A₀ A z x v u)
      = (∑ k : Fin N, star (guePencilResolvent A₀ A x z (v, k) (u, k))) * (N : ℂ)⁻¹ := by
    simp only [guePartialTrace, partialTraceN_apply, star_mul, star_sum, star_inv₀, star_natCast]
  rw [hL, hR, mul_comm]

/-- **Conjugation symmetry of the averaged resolvent:** `(g_N(z))ᴴ = g_N(z̄)`. -/
theorem gueResolventMean_star (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    (hA₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian) (z : ℂ) :
    star (gueResolventMean (N := N) A₀ A z) = gueResolventMean (N := N) A₀ A (star z) := by
  ext u v
  rw [Matrix.star_apply, gueResolventMean_apply, gueResolventMean_apply]
  rw [show (∫ x, guePartialTrace A₀ A (star z) x u v
        ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N))))
      = ∫ x, star (guePartialTrace A₀ A z x v u)
        ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) from
    integral_congr_ae (Eventually.of_forall fun x =>
      guePartialTrace_star A₀ A hA₀ hA x z u v)]
  simp only [Complex.star_def, integral_conj]

/-- **The deviation is conjugation invariant**, given the corresponding symmetry of the limit
Cauchy transform.  The mean side is proved (`gueResolventMean_star`); the limit side
`star (operatorMatrixPencilCauchy A₀ A z) = operatorMatrixPencilCauchy A₀ A (star z)` is the
Fock-space analogue and is blocked on the instance bookkeeping of `lean-free-prob` (see the
module docstring). -/
theorem frob_gueResolventMean_sub_limit_star_of_limit (A₀ : Matrix d d ℂ)
    (A : ι → Matrix d d ℂ) (hA₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian)
    (hG : ∀ z : ℂ, star (operatorMatrixPencilCauchy A₀ A z)
      = operatorMatrixPencilCauchy A₀ A (star z)) (z : ℂ) :
    frob (gueResolventMean (N := N) A₀ A (star z) - operatorMatrixPencilCauchy A₀ A (star z))
      = frob (gueResolventMean (N := N) A₀ A z - operatorMatrixPencilCauchy A₀ A z) := by
  rw [← gueResolventMean_star A₀ A hA₀ hA z, ← hG z]
  exact frob_sub_star _ _

/-- **The weighted strip bound on the lower half-plane** follows from the upper half-plane
estimate, by the conjugation symmetry. -/
theorem weightedStripBound_lowerHalf_of_upperHalf_of_limit (A₀ : Matrix d d ℂ)
    (A : ι → Matrix d d ℂ) (hA₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian)
    (hG : ∀ z : ℂ, star (operatorMatrixPencilCauchy A₀ A z)
      = operatorMatrixPencilCauchy A₀ A (star z)) {η₀ C_s β : ℝ}
    (hupper : ∀ᶠ N : ℕ in atTop, ∀ z : ℂ, 0 < z.im → |z.im| < η₀ →
      frob (gueResolventMean (N := N) A₀ A z - operatorMatrixPencilCauchy A₀ A z)
        ≤ C_s * |z.im| ^ (-β) / (N : ℝ) ^ 2) :
    ∀ᶠ N : ℕ in atTop, ∀ z : ℂ, z.im < 0 → |z.im| < η₀ →
      frob (gueResolventMean (N := N) A₀ A z - operatorMatrixPencilCauchy A₀ A z)
        ≤ C_s * |z.im| ^ (-β) / (N : ℝ) ^ 2 := by
  filter_upwards [hupper] with N hN z hz hlt
  have hzpos : 0 < (star z).im := by simpa [Complex.star_def] using hz
  have hlt' : |(star z).im| < η₀ := by simpa [Complex.star_def] using hlt
  have h := hN (star z) hzpos hlt'
  rw [frob_gueResolventMean_sub_limit_star_of_limit A₀ A hA₀ hA hG z] at h
  simpa [Complex.star_def] using h

/-- **The full weighted strip bound from the upper half-plane estimate** (given the limit-side
conjugation symmetry). -/
theorem weightedStripBound_of_upperHalf_of_limit (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    (hA₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian)
    (hG : ∀ z : ℂ, star (operatorMatrixPencilCauchy A₀ A z)
      = operatorMatrixPencilCauchy A₀ A (star z)) (k : ℕ) {η₀ C_s β : ℝ}
    (hupper : ∀ᶠ N : ℕ in atTop, ∀ z : ℂ, 0 < z.im → |z.im| < η₀ →
      frob (gueResolventMean (N := N) A₀ A z - operatorMatrixPencilCauchy A₀ A z)
        ≤ C_s * |z.im| ^ (-β) / (N : ℝ) ^ 2) :
    WeightedStripBound A₀ A k η₀ C_s β := by
  have hlower := weightedStripBound_lowerHalf_of_upperHalf_of_limit A₀ A hA₀ hA hG hupper
  filter_upwards [hupper, hlower] with N hn hl
  intro z hz hlt
  rcases lt_trichotomy z.im 0 with h | h | h
  · exact hl z h hlt
  · exact absurd h hz
  · exact hn z h hlt

end

end GUEStrongConvergence
