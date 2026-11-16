/-
# Norm bound for the resolvent of a selfadjoint element

For a selfadjoint element `a` of a unital complex C⋆-algebra and any nonreal `z : ℂ`, the
resolvent `(z • 1 - a)⁻¹` satisfies

`‖resolvent a z‖ ≤ |z.im|⁻¹`.

The proof uses the continuous functional calculus:
`resolvent a z = cfc (fun w => (z - w)⁻¹) a`.  The spectrum of a selfadjoint element is real,
so `|z.im| ≤ ‖z - w‖` for every `w` in the spectrum, and the isometric CFC norm estimate gives
the bound.  No spectral-radius or matrix-specific argument is used.
-/
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unital
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric
import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.Analysis.Complex.Norm
import Mathlib.Algebra.Algebra.Spectrum.Basic
import Mathlib.Algebra.Star.SelfAdjoint

namespace GUEStrongConvergence

set_option linter.style.haveILetI false

/-- **Resolvent norm bound in a unital complex C⋆-algebra.**
If `a` is selfadjoint and `z` is nonreal, then
`‖(z • 1 - a)⁻¹‖ ≤ |z.im|⁻¹`. -/
theorem norm_resolvent_le_inv_abs_im {A : Type*} [CStarAlgebra A]
    {a : A} (ha : IsSelfAdjoint a) {z : ℂ} (hz : z.im ≠ 0) :
    ‖resolvent a z‖ ≤ |z.im|⁻¹ := by
  haveI : IsStarNormal a := IsSelfAdjoint.isStarNormal ha
  have hzpos : 0 < |z.im| := abs_pos.mpr hz
  have hne : ∀ w ∈ spectrum ℂ a, z - w ≠ 0 := by
    intro w hw hzero
    have hwim : w.im = 0 := ha.im_eq_zero_of_mem_spectrum hw
    have hzw : z = w := sub_eq_zero.mp hzero
    rw [hzw, hwim] at hz
    exact hz rfl
  have hres : resolvent a z = cfc (fun w : ℂ => (z - w)⁻¹) a := by
    rw [resolvent]
    rw [cfc_inv (f := fun w : ℂ => z - w) a hne]
    rw [cfc_sub (f := fun _ : ℂ => z) (g := fun w : ℂ => w) a]
    rw [cfc_const z a, cfc_id' ℂ a]
  rw [hres]
  refine norm_cfc_le (c := |z.im|⁻¹) (by positivity) ?_
  intro w hw
  have hwim : w.im = 0 := ha.im_eq_zero_of_mem_spectrum hw
  have hne' : z - w ≠ 0 := hne w hw
  have hnorm : |z.im| ≤ ‖z - w‖ := by
    have him : (z - w).im = z.im := by simp [hwim]
    calc |z.im| = |(z - w).im| := by rw [him]
      _ ≤ ‖z - w‖ := Complex.abs_im_le_norm _
  calc ‖(z - w)⁻¹‖ = (‖z - w‖)⁻¹ := norm_inv _
    _ = 1 / ‖z - w‖ := by rw [one_div]
    _ ≤ 1 / |z.im| := one_div_le_one_div_of_le hzpos hnorm
    _ = |z.im|⁻¹ := by rw [one_div]


/-- Upper-half-plane form: for `0 < z.im`, `‖resolvent a z‖ ≤ (z.im)⁻¹`. -/
theorem norm_resolvent_le_inv_im {A : Type*} [CStarAlgebra A]
    {a : A} (ha : IsSelfAdjoint a) {z : ℂ} (hz : 0 < z.im) :
    ‖resolvent a z‖ ≤ (z.im)⁻¹ := by
  simpa [abs_of_pos hz] using norm_resolvent_le_inv_abs_im ha (ne_of_gt hz)

/-- Lower-half-plane form: for `z.im < 0`, `‖resolvent a z‖ ≤ (-z.im)⁻¹`. -/
theorem norm_resolvent_le_inv_neg_im {A : Type*} [CStarAlgebra A]
    {a : A} (ha : IsSelfAdjoint a) {z : ℂ} (hz : z.im < 0) :
    ‖resolvent a z‖ ≤ (-z.im)⁻¹ := by
  simpa [abs_of_neg hz] using norm_resolvent_le_inv_abs_im ha (ne_of_lt hz)

end GUEStrongConvergence
