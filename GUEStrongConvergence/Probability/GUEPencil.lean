/-
# Finite-dimensional affine GUE pencils with the genuine operator norm

For fixed coefficient dimension `d`, the random pencil is
`A₀ ⊗ I_N + ∑ i, A_i ⊗ G_i`. We use `CStarMatrix` rather than the default
entrywise matrix norm. Hermitian coefficients imply pointwise self-adjointness,
and every nonreal spectral argument is in the actual resolvent set.

This module does not assume spectral inclusion or any asymptotic estimate.
-/
import GUEStrongConvergence.Probability.GUEModel
import GUEStrongConvergence.Analysis.ResolventBounds
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Analysis.Calculus.Deriv.Prod

open MeasureTheory ProbabilityTheory Matrix Kronecker
open scoped Topology ComplexOrder Matrix.Norms.Elementwise

namespace GUEStrongConvergence

noncomputable section

variable {ι d : Type*} {N : ℕ} [Fintype ι]

/-- The raw matrix of the affine pencil, with the coefficient index first. -/
def guePencilMatrix (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    (x : GUECoord ι N → ℝ) : Matrix (d × Fin N) (d × Fin N) ℂ :=
  A₀ ⊗ₖ (1 : Matrix (Fin N) (Fin N) ℂ) + ∑ i, A i ⊗ₖ gueMatrix x i

/-- The actual C-star matrix pencil, equipped with the operator norm. -/
def guePencil (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    (x : GUECoord ι N → ℝ) : CStarMatrix (d × Fin N) (d × Fin N) ℂ :=
  CStarMatrix.ofMatrix (guePencilMatrix A₀ A x)

lemma guePencilMatrix_apply (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    (x : GUECoord ι N → ℝ) (a b : d × Fin N) :
    guePencilMatrix A₀ A x a b =
      A₀ a.1 b.1 * (1 : Matrix (Fin N) (Fin N) ℂ) a.2 b.2 +
        ∑ i, A i a.1 b.1 * gueMatrix x i a.2 b.2 := by
  simp [guePencilMatrix, Matrix.kroneckerMap, Matrix.sum_apply]

/-- Hermitian coefficients give a Hermitian matrix for every coordinate vector. -/
theorem guePencilMatrix_isHermitian (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    (hA₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian) (x : GUECoord ι N → ℝ) :
    (guePencilMatrix A₀ A x).IsHermitian := by
  change (guePencilMatrix A₀ A x)ᴴ = guePencilMatrix A₀ A x
  have h₀ : A₀ᴴ = A₀ := hA₀
  have hi : ∀ i, (A i)ᴴ = A i := hA
  simp [guePencilMatrix, Matrix.conjTranspose_sum, Matrix.conjTranspose_kronecker,
    h₀, hi, gueMatrix_conjTranspose]

/-- Pointwise self-adjointness in the genuine C-star algebra of matrices. -/
theorem guePencil_isSelfAdjoint (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    (hA₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian) (x : GUECoord ι N → ℝ) :
    IsSelfAdjoint (guePencil A₀ A x) := by
  change CStarMatrix.ofMatrix ((guePencilMatrix A₀ A x)ᴴ) =
    CStarMatrix.ofMatrix (guePencilMatrix A₀ A x)
  exact congrArg CStarMatrix.ofMatrix (guePencilMatrix_isHermitian A₀ A hA₀ hA x)

/-- Every nonreal point belongs to the true operator resolvent set of the finite pencil. -/
theorem guePencil_mem_resolventSet [Fintype d] [DecidableEq d] (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    (hA₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian) (x : GUECoord ι N → ℝ)
    (z : ℂ) (hz : z.im ≠ 0) : z ∈ resolventSet ℂ (guePencil A₀ A x) := by
  by_contra hspec
  have hmem : z ∈ spectrum ℂ (guePencil A₀ A x) := hspec
  exact hz ((guePencil_isSelfAdjoint A₀ A hA₀ hA x).im_eq_zero_of_mem_spectrum hmem)

lemma continuous_guePencilMatrix (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ) :
    Continuous (fun x : EuclideanSpace ℝ (GUECoord ι N) => guePencilMatrix A₀ A x) := by
  apply continuous_pi
  intro a
  apply continuous_pi
  intro b
  simp only [guePencilMatrix_apply]
  unfold gueMatrix gueUnscaled
  fun_prop

lemma continuous_guePencil (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ) :
    Continuous (fun x : EuclideanSpace ℝ (GUECoord ι N) => guePencil A₀ A x) := by
  have h := (CStarMatrix.ofMatrixL :
      Matrix (d × Fin N) (d × Fin N) ℂ ≃L[ℂ]
        CStarMatrix (d × Fin N) (d × Fin N) ℂ).continuous.comp
      (continuous_guePencilMatrix (N := N) A₀ A)
  exact h

/-- The coordinate derivative matrix, with the existing GUE normalization unchanged. -/
def guePencilDirection [DecidableEq ι] (A : ι → Matrix d d ℂ) (p : GUECoord ι N) :
    CStarMatrix (d × Fin N) (d × Fin N) ℂ :=
  CStarMatrix.ofMatrix fun a b => ∑ i, A i a.1 b.1 *
    ((gueScale N : ℂ) *
      (gueAlpha * (if p = (i, (a.2, b.2)) then (1:ℂ) else 0) +
        gueBeta * (if p = (i, (b.2, a.2)) then (1:ℂ) else 0)))

/-- Exact real-coordinate derivative of the affine GUE pencil in operator norm topology. -/
theorem hasDerivAt_guePencil_update [DecidableEq ι] [Fintype d] (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    (x : GUECoord ι N → ℝ) (p : GUECoord ι N) (t : ℝ) :
    HasDerivAt (fun u : ℝ => guePencil A₀ A (Function.update x p u))
      (guePencilDirection A p) t := by
  have hraw : HasDerivAt
      (fun u : ℝ => guePencilMatrix A₀ A (Function.update x p u))
      (fun a b : d × Fin N => ∑ i, A i a.1 b.1 *
        ((gueScale N : ℂ) *
          (gueAlpha * (if p = (i, (a.2, b.2)) then (1:ℂ) else 0) +
            gueBeta * (if p = (i, (b.2, a.2)) then (1:ℂ) else 0)))) t := by
    apply hasDerivAt_pi.mpr
    intro a
    apply hasDerivAt_pi.mpr
    intro b
    simp only [guePencilMatrix_apply]
    have hsum := HasDerivAt.sum (u := Finset.univ) (fun i _ =>
      (hasDerivAt_gueMatrix_update x p i a.2 b.2 t).const_mul (A i a.1 b.1))
    simpa using hsum.const_add (A₀ a.1 b.1 * (1 : Matrix (Fin N) (Fin N) ℂ) a.2 b.2)
  let L := (CStarMatrix.ofMatrixL : Matrix (d × Fin N) (d × Fin N) ℂ ≃L[ℂ]
    CStarMatrix (d × Fin N) (d × Fin N) ℂ).toContinuousLinearMap.restrictScalars ℝ
  exact L.hasFDerivAt.comp_hasDerivAt t hraw

/-- The actual inverse resolvent of the finite operator-norm pencil. -/
def guePencilResolvent [Fintype d] [DecidableEq d]
    (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ) (x : GUECoord ι N → ℝ) (z : ℂ) :
    CStarMatrix (d × Fin N) (d × Fin N) ℂ := resolvent (guePencil A₀ A x) z

/-- Uniform operator-norm bound, independent of the Gaussian coordinates. -/
theorem norm_guePencilResolvent_le [Fintype d] [DecidableEq d]
    (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    (hA₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian) (x : GUECoord ι N → ℝ)
    (z : ℂ) (hz : z.im ≠ 0) : ‖guePencilResolvent A₀ A x z‖ ≤ |z.im|⁻¹ :=
  norm_resolvent_le_inv_abs_im (guePencil_isSelfAdjoint A₀ A hA₀ hA x) hz

/-- The resolvent depends continuously on the Gaussian coordinate vector. -/
theorem continuous_guePencilResolvent [Fintype d] [DecidableEq d]
    (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    (hA₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian)
    (z : ℂ) (hz : z.im ≠ 0) :
    Continuous (fun x : EuclideanSpace ℝ (GUECoord ι N) => guePencilResolvent A₀ A x z) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  have hu : IsUnit (algebraMap ℂ (CStarMatrix (d × Fin N) (d × Fin N) ℂ) z - guePencil A₀ A x) :=
    guePencil_mem_resolventSet A₀ A hA₀ hA x z hz
  obtain ⟨u, hu⟩ := hu
  have hInv := NormedRing.inverse_continuousAt u
  rw [hu] at hInv
  have harg : ContinuousAt (fun y : EuclideanSpace ℝ (GUECoord ι N) =>
      algebraMap ℂ (CStarMatrix (d × Fin N) (d × Fin N) ℂ) z - guePencil A₀ A y) x :=
    continuous_const.continuousAt.sub (continuous_guePencil (N := N) A₀ A).continuousAt
  have h : ContinuousAt (fun y : EuclideanSpace ℝ (GUECoord ι N) =>
      Ring.inverse (algebraMap ℂ (CStarMatrix (d × Fin N) (d × Fin N) ℂ) z -
        guePencil A₀ A y)) x :=
    ContinuousAt.comp (f := fun y : EuclideanSpace ℝ (GUECoord ι N) =>
      algebraMap ℂ (CStarMatrix (d × Fin N) (d × Fin N) ℂ) z - guePencil A₀ A y)
      (x := x) hInv harg
  exact h

lemma measurable_guePencilResolvent_entry [Fintype d] [DecidableEq d]
    (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    (hA₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian)
    (z : ℂ) (hz : z.im ≠ 0) (a b : d × Fin N) :
    Measurable (fun x : EuclideanSpace ℝ (GUECoord ι N) => guePencilResolvent A₀ A x z a b) := by
  have hraw := (CStarMatrix.ofMatrixL : Matrix (d × Fin N) (d × Fin N) ℂ ≃L[ℂ]
    CStarMatrix (d × Fin N) (d × Fin N) ℂ).symm.continuous.comp
      (continuous_guePencilResolvent (N := N) A₀ A hA₀ hA z hz)
  exact ((continuous_apply b).comp ((continuous_apply a).comp hraw)).measurable

/-- Every resolvent entry belongs to every finite Gaussian `Lᵖ`, by its uniform actual
operator-norm bound. This discharges the observable `L²` prerequisite for Gaussian Poincaré. -/
theorem memLp_guePencilResolvent_entry [Fintype d] [DecidableEq d]
    (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    (hA₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian)
    (z : ℂ) (hz : z.im ≠ 0) (a b : d × Fin N) (p : ENNReal) :
    MemLp (fun x : EuclideanSpace ℝ (GUECoord ι N) => guePencilResolvent A₀ A x z a b)
      p (stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) := by
  apply MemLp.of_bound (measurable_guePencilResolvent_entry A₀ A hA₀ hA z hz a b).aestronglyMeasurable
    (|z.im|⁻¹)
  filter_upwards with x
  exact CStarMatrix.norm_entry_le_norm.trans (norm_guePencilResolvent_le A₀ A hA₀ hA x z hz)

end

end GUEStrongConvergence
