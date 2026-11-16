/-
# Derivatives and norm bounds for affine resolvents

For selfadjoint `a b` in a unital complex C⋆-algebra and nonreal `z`, this module proves

* `HasDerivAt (fun t : ℝ => resolvent (a + t • b) z) (R_t * b * R_t) t`,
* the second derivative `2 • (R_t * b * R_t * b * R_t)`,
* norm bounds `≤ ‖b‖ * |z.im|⁻²` and `≤ 2 * ‖b‖² * |z.im|⁻³`,

where `R_t = resolvent (a + t • b) z`.  The proofs use the Fréchet derivative of `Ring.inverse`
and the genuine resolvent norm bound from `ResolventBounds`; no extra invertibility or norm
assumption is introduced.
-/
import GUEStrongConvergence.Analysis.ResolventBounds
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unital
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric
import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.Algebra.Star.SelfAdjoint

namespace GUEStrongConvergence

set_option linter.style.haveILetI false

/-- If `a` is selfadjoint and `z.im ≠ 0`, then `z` is in the resolvent set of `a`. -/
theorem mem_resolventSet_of_isSelfAdjoint {A : Type*} [CStarAlgebra A]
    {a : A} (ha : IsSelfAdjoint a) {z : ℂ} (hz : z.im ≠ 0) :
    z ∈ resolventSet ℂ a := by
  haveI : IsStarNormal a := IsSelfAdjoint.isStarNormal ha
  letI : ContinuousFunctionalCalculus ℂ A IsStarNormal :=
    IsStarNormal.instContinuousFunctionalCalculus
  letI : IsometricContinuousFunctionalCalculus ℂ A IsStarNormal :=
    IsStarNormal.instIsometricContinuousFunctionalCalculus
  have hne : ∀ w ∈ spectrum ℂ a, z - w ≠ 0 := by
    intro w hw hzero
    have hwim : w.im = 0 := ha.im_eq_zero_of_mem_spectrum hw
    have hzw : z = w := sub_eq_zero.mp hzero
    rw [hzw, hwim] at hz
    exact hz rfl
  have hu : IsUnit (algebraMap ℂ A z - a) := by
    let u : Aˣ := cfcUnits (fun w : ℂ => z - w) a hne
    have hval : (u : A) = algebraMap ℂ A z - a := by
      simp [u, cfc_sub (f := fun _ : ℂ => z) (g := fun w : ℂ => w) a,
        cfc_const z a, cfc_id' ℂ a]
    exact ⟨u, hval⟩
  exact spectrum.mem_resolventSet_iff.mpr hu

/-- **First derivative of an affine resolvent.** -/
theorem hasDerivAt_resolvent_affine {A : Type*} [CStarAlgebra A]
    {a b : A} (ha : IsSelfAdjoint a) (hb : IsSelfAdjoint b)
    {z : ℂ} (hz : z.im ≠ 0) (t : ℝ) :
    HasDerivAt (fun s : ℝ => resolvent (a + s • b) z)
      (resolvent (a + t • b) z * b * resolvent (a + t • b) z) t := by
  have hself : IsSelfAdjoint (a + t • b) := by
    have ht : IsSelfAdjoint (t : ℝ) := by
      rw [isSelfAdjoint_iff]
      simp
    exact ha.add (ht.smul hb)
  have hk : z ∈ resolventSet ℂ (a + t • b) :=
    mem_resolventSet_of_isSelfAdjoint hself hz
  have harg : HasDerivAt (fun s : ℝ => algebraMap ℂ A z - (a + s • b)) (-b) t := by
    have h1 : HasDerivAt (fun s : ℝ => s • b) b t := by
      simpa using (hasDerivAt_id t).smul_const b
    have h2 : HasDerivAt (fun s : ℝ => a + s • b) b t := by
      have h2' := (hasDerivAt_const (x := t) a).add h1
      have hfun : ((fun _ : ℝ => a) + fun s : ℝ => s • b)
          = fun s : ℝ => a + s • b := by
        ext s
        rfl
      rw [hfun] at h2'
      simpa using h2'
    have h3' := (hasDerivAt_const (x := t) (c := algebraMap ℂ A z)).sub h2
    have hfun : ((fun _ : ℝ => algebraMap ℂ A z) - fun s : ℝ => a + s • b)
        = fun s : ℝ => algebraMap ℂ A z - (a + s • b) := by
      ext s
      rfl
    rw [hfun] at h3'
    simpa using h3'
  have hcomp := (hasFDerivAt_ringInverse (𝕜 := ℝ) hk.unit).comp_hasDerivAt t harg
  simpa [resolvent, Function.comp_def, ContinuousLinearMap.mulLeftRight_apply,
    ← spectrum.resolvent_eq hk] using hcomp

/-- **Second derivative of an affine resolvent.** -/
theorem hasDerivAt_resolvent_affine_second {A : Type*} [CStarAlgebra A]
    {a b : A} (ha : IsSelfAdjoint a) (hb : IsSelfAdjoint b)
    {z : ℂ} (hz : z.im ≠ 0) (t : ℝ) :
    HasDerivAt (fun s : ℝ =>
        resolvent (a + s • b) z * b * resolvent (a + s • b) z)
      (2 • (resolvent (a + t • b) z * b * resolvent (a + t • b) z * b *
        resolvent (a + t • b) z)) t := by
  let R : ℝ → A := fun s => resolvent (a + s • b) z
  have hR : HasDerivAt R (R t * b * R t) t :=
    hasDerivAt_resolvent_affine ha hb hz t
  have hRb : HasDerivAt (fun s : ℝ => R s * b) ((R t * b * R t) * b) t :=
    hR.mul_const b
  have h2 := hRb.mul hR
  change HasDerivAt ((fun s : ℝ => R s * b) * R)
    (2 • (R t * b * R t * b * R t)) t
  simpa [two_smul, mul_assoc] using h2

/-- Norm bound for the first derivative: `≤ ‖b‖ * |z.im|⁻²`. -/
theorem norm_hasDerivAt_resolvent_affine_le {A : Type*} [CStarAlgebra A]
    {a b : A} (ha : IsSelfAdjoint a) (hb : IsSelfAdjoint b)
    {z : ℂ} (hz : z.im ≠ 0) (t : ℝ) :
    ‖resolvent (a + t • b) z * b * resolvent (a + t • b) z‖
      ≤ ‖b‖ * (|z.im|⁻¹) ^ 2 := by
  have hself : IsSelfAdjoint (a + t • b) := by
    have ht : IsSelfAdjoint (t : ℝ) := by
      rw [isSelfAdjoint_iff]
      simp
    exact ha.add (ht.smul hb)
  have hR : ‖resolvent (a + t • b) z‖ ≤ |z.im|⁻¹ :=
    norm_resolvent_le_inv_abs_im hself hz
  have hR0 : 0 ≤ ‖resolvent (a + t • b) z‖ := norm_nonneg _
  have hinv0 : 0 ≤ |z.im|⁻¹ := inv_nonneg.mpr (abs_nonneg _)
  calc ‖resolvent (a + t • b) z * b * resolvent (a + t • b) z‖
      ≤ ‖resolvent (a + t • b) z * b‖ * ‖resolvent (a + t • b) z‖ :=
        norm_mul_le _ _
    _ ≤ (‖resolvent (a + t • b) z‖ * ‖b‖) * ‖resolvent (a + t • b) z‖ :=
        mul_le_mul (norm_mul_le _ _) le_rfl hR0 (mul_nonneg hR0 (norm_nonneg _))
    _ ≤ (|z.im|⁻¹ * ‖b‖) * |z.im|⁻¹ := by
        refine mul_le_mul ?_ hR hR0 ?_
        · exact mul_le_mul hR le_rfl (norm_nonneg _) hinv0
        · positivity
    _ = ‖b‖ * (|z.im|⁻¹) ^ 2 := by ring

/-- Norm bound for the second derivative: `≤ 2 * ‖b‖² * |z.im|⁻³`. -/
theorem norm_hasDerivAt_resolvent_affine_second_le {A : Type*} [CStarAlgebra A]
    {a b : A} (ha : IsSelfAdjoint a) (hb : IsSelfAdjoint b)
    {z : ℂ} (hz : z.im ≠ 0) (t : ℝ) :
    ‖2 • (resolvent (a + t • b) z * b * resolvent (a + t • b) z * b *
        resolvent (a + t • b) z)‖
      ≤ 2 * ‖b‖ ^ 2 * (|z.im|⁻¹) ^ 3 := by
  have hself : IsSelfAdjoint (a + t • b) := by
    have ht : IsSelfAdjoint (t : ℝ) := by
      rw [isSelfAdjoint_iff]
      simp
    exact ha.add (ht.smul hb)
  have hR : ‖resolvent (a + t • b) z‖ ≤ |z.im|⁻¹ :=
    norm_resolvent_le_inv_abs_im hself hz
  have hR0 : 0 ≤ ‖resolvent (a + t • b) z‖ := norm_nonneg _
  have hinv0 : 0 ≤ |z.im|⁻¹ := inv_nonneg.mpr (abs_nonneg _)
  have hfirst : ‖resolvent (a + t • b) z * b * resolvent (a + t • b) z‖
      ≤ ‖b‖ * (|z.im|⁻¹) ^ 2 :=
    norm_hasDerivAt_resolvent_affine_le ha hb hz t
  have hb0 : 0 ≤ ‖b‖ := norm_nonneg _
  have hprod : ‖resolvent (a + t • b) z * b * resolvent (a + t • b) z * b *
        resolvent (a + t • b) z‖ ≤ ‖b‖ ^ 2 * (|z.im|⁻¹) ^ 3 := by
    calc ‖resolvent (a + t • b) z * b * resolvent (a + t • b) z * b *
          resolvent (a + t • b) z‖
        ≤ ‖resolvent (a + t • b) z * b * resolvent (a + t • b) z * b‖ *
            ‖resolvent (a + t • b) z‖ := norm_mul_le _ _
      _ ≤ (‖resolvent (a + t • b) z * b * resolvent (a + t • b) z‖ * ‖b‖) *
            ‖resolvent (a + t • b) z‖ :=
          mul_le_mul (norm_mul_le _ _) le_rfl hR0
            (mul_nonneg (norm_nonneg _) hb0)
      _ ≤ (‖b‖ * (|z.im|⁻¹) ^ 2 * ‖b‖) * |z.im|⁻¹ := by
          refine mul_le_mul ?_ hR hR0 ?_
          · exact mul_le_mul hfirst le_rfl hb0
              (mul_nonneg hb0 (sq_nonneg _))
          · positivity
      _ = ‖b‖ ^ 2 * (|z.im|⁻¹) ^ 3 := by ring
  calc ‖2 • (resolvent (a + t • b) z * b * resolvent (a + t • b) z * b *
        resolvent (a + t • b) z)‖
      ≤ 2 * ‖resolvent (a + t • b) z * b * resolvent (a + t • b) z * b *
          resolvent (a + t • b) z‖ := by
        rw [two_smul]
        calc ‖resolvent (a + t • b) z * b * resolvent (a + t • b) z * b *
              resolvent (a + t • b) z +
              (resolvent (a + t • b) z * b * resolvent (a + t • b) z * b *
                resolvent (a + t • b) z)‖
            ≤ ‖resolvent (a + t • b) z * b * resolvent (a + t • b) z * b *
                resolvent (a + t • b) z‖ +
              ‖resolvent (a + t • b) z * b * resolvent (a + t • b) z * b *
                resolvent (a + t • b) z‖ := norm_add_le _ _
          _ = 2 * ‖resolvent (a + t • b) z * b * resolvent (a + t • b) z * b *
                resolvent (a + t • b) z‖ := by ring
    _ ≤ 2 * (‖b‖ ^ 2 * (|z.im|⁻¹) ^ 3) :=
        mul_le_mul_of_nonneg_left hprod (by norm_num)
    _ = 2 * ‖b‖ ^ 2 * (|z.im|⁻¹) ^ 3 := by ring

end GUEStrongConvergence
