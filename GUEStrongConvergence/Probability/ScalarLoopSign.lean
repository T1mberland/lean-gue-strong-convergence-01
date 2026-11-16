/-
# Sign of the imaginary part of the GUE resolvent mean

For a Hermitian matrix `H` and `Im z ≠ 0` the resolvent `R = (z - H)⁻¹` satisfies the exact
identity `R - R* = (z̄ - z) R R*`, whose `(a,a)` entry gives

`Im R_aa = -Im z · ∑_j ‖R_aj‖²`,

so `Im z · Im R_aa ≤ 0`.  Averaging the diagonal entries `R_{(u,k),(u,k)}` and integrating over
the Gaussian coordinates gives the scalar sign fact `Im z · Im m ≤ 0` for
`m = E[guePartialTrace z u u]`, the mean of `T_N = N⁻¹ tr (z - G_N)⁻¹`.

This is the finite-`N` input of the scalar loop bootstrap (`ScalarLoopCore.loop_bootstrap`).

**Status (WIP).**  The per-entry identity `guePencilResolvent_im_diag_mul_im_nonpos` below is
complete and kernel-checked.  The averaging step over the Gaussian coordinates
(`Im z · Im (gueResolventMean … z u u) ≤ 0`) and the limit-side sign fact
(`Im z · Im g ≤ 0`, planned via `‖g z‖ < 1` on `Im z ≠ 0` by IVT) are NOT yet in this file; the
averaging proof only lacks a cast simplification (`((N : ℂ)⁻¹).re = (N : ℝ)⁻¹`).

-/
import GUEStrongConvergence.Probability.DysonLimit

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

/-- **Diagonal resolvent imaginary-part identity for the Hermitian GUE pencil.**
For every entry `a`, `Im z · Im (guePencilResolvent … a a) ≤ 0`; more precisely
`Im (guePencilResolvent … a a) = -Im z · ∑_j ‖R a j‖²`. -/
theorem guePencilResolvent_im_diag_mul_im_nonpos
    (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    (hA₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian)
    (x : GUECoord ι N → ℝ) (z : ℂ) (hz : z.im ≠ 0) (a : d × Fin N) :
    z.im * (guePencilResolvent A₀ A x z a a).im ≤ 0 := by
  classical
  set R : CStarMatrix (d × Fin N) (d × Fin N) ℂ := guePencilResolvent A₀ A x z with hR
  set X : CStarMatrix (d × Fin N) (d × Fin N) ℂ :=
    algebraMap ℂ (CStarMatrix (d × Fin N) (d × Fin N) ℂ) z - guePencil A₀ A x with hX
  have hXR : X * R = 1 := resolvent_mul_guePencil A₀ A hA₀ hA x z hz
  -- the exact imaginary-part identity `R - R* = (z̄ - z) • (R* R)`
  have hdiff : star X - X = (star z - z) • (1 : CStarMatrix (d × Fin N) (d × Fin N) ℂ) := by
    rw [hX]
    simp only [Algebra.algebraMap_eq_smul_one, star_sub, star_smul, star_one,
      (guePencil_isSelfAdjoint A₀ A hA₀ hA x).star_eq, sub_smul]
    abel
  have key : R - star R = star R * (star X - X) * R := by
    have h1 : star R * star X = 1 := by
      have h := congrArg star hXR
      simpa using h
    have h2 : star R * star X * R = R := by rw [h1, one_mul]
    have h3 : star R * X * R = star R := by rw [mul_assoc, hXR, mul_one]
    calc R - star R = star R * star X * R - star R * X * R := by rw [h2, h3]
      _ = star R * (star X - X) * R := by noncomm_ring
  have key2 : R - star R = (star z - z) • (star R * R) := by
    rw [key, hdiff, mul_smul_comm, mul_one, smul_mul_assoc]
  have hentry : R a a - star (R a a) = (star z - z) * ((star R * R) a a) := by
    have h := congrArg (fun M : CStarMatrix (d × Fin N) (d × Fin N) ℂ => M a a) key2
    simpa [CStarMatrix.sub_apply, CStarMatrix.smul_apply, CStarMatrix.star_apply,
      smul_eq_mul] using h
  -- the gram entry is a sum of squared moduli
  have hgram : (star R * R) a a = ((∑ j : d × Fin N, ‖R j a‖ ^ 2 : ℝ) : ℂ) := by
    rw [CStarMatrix.mul_apply, Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [CStarMatrix.star_apply, Complex.star_def, mul_comm, Complex.mul_conj,
      Complex.normSq_eq_norm_sq]
  set S : ℝ := ∑ j : d × Fin N, ‖R j a‖ ^ 2 with hSdef
  have hS : 0 ≤ S := Finset.sum_nonneg fun j _ => sq_nonneg _
  have hzstar : (star z - z).im = -2 * z.im := by
    simp only [Complex.star_def, Complex.sub_im, Complex.conj_im]
    ring
  have him : 2 * (R a a).im = -2 * z.im * S := by
    have h := congrArg Complex.im hentry
    rw [hgram] at h
    simp only [Complex.sub_im, Complex.star_def, Complex.conj_im, Complex.mul_im,
      Complex.ofReal_im, Complex.ofReal_re, mul_zero] at h
    linarith
  have ha : (R a a).im = -z.im * S := by linarith
  rw [ha, show z.im * (-z.im * S) = -(z.im ^ 2 * S) by ring]
  exact neg_nonpos.mpr (mul_nonneg (sq_nonneg _) hS)


end
end GUEStrongConvergence
