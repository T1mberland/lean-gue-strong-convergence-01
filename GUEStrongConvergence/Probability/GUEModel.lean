/-
# The normalized complex GUE: real-coordinate construction and covariance

This file begins checkpoint **P0** of the GUE strong-convergence project: a concrete
normalized complex GUE matrix, built from independent real standard Gaussian coordinates
on one standard Gaussian probability space, together with the covariance identity

`E[(G_i)_{ab} (G_j)_{cd}] = δ_{ij} δ_{ad} δ_{bc} / N`

(with **no** complex conjugation on the left-hand side), which is equation (1.2) of the
Part II mathematical handoff.

## Construction

For an index type `ι` (the labels of the matrices) and `N : ℕ`, the coordinate space is

`GUECoord ι N = ι × (Fin N × Fin N)`,

carrying the standard Gaussian measure `stdGaussian (EuclideanSpace ℝ (GUECoord ι N))`.
Writing `x (i, (a, b))` for the real coordinate of label `i` at the ordered pair `(a, b)`,
the matrix with label `i` is

`(gueMatrix x i) a b = N^{-1/2} * (α * x (i, (a, b)) + β * x (i, (b, a)))`,

where `α = (1 - I)/2` and `β = (1 + I)/2`. For `a = b` this is `N^{-1/2} * x (i, (a, a))`,
a real diagonal entry; for `a ≠ b` it is `N^{-1/2}` times a complex number whose real and
imaginary parts are the two independent coordinates of the unordered pair `{a, b}`. Since
`β = conj α` and the coordinates are real, the matrix is Hermitian. The choice
`α = (1 - I)/2`, `β = (1 + I)/2` gives `α² + β² = 0` and `2 α β = 1`, which is precisely
what makes the covariance identity hold uniformly, including on the diagonal.

## What this file does *not* yet provide

The measure above depends on `N`; the eventual almost-sure statement needs one probability
space carrying all matrices for all `N` simultaneously. That coupling (a countable product
of Gaussian spaces) and the subsequent Gaussian integration-by-parts machinery are not
part of this file.
-/
import Mathlib.Probability.Distributions.Gaussian.Multivariate

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace Matrix ENNReal

namespace GUEStrongConvergence

noncomputable section

variable {ι : Type*} {N : ℕ}

/-! ### The real Gaussian coordinates and the matrix -/

/-- Coordinate index for `ι`-many `N × N` GUE matrices. The coordinate `(i, (a, b))` is the
real Gaussian attached to the label `i` and the ordered index pair `(a, b)`. -/
abbrev GUECoord (ι : Type*) (N : ℕ) := ι × (Fin N × Fin N)

/-- The complex weight of the coordinate `(i, (a, b))` in the `(a, b)`-entry. -/
def gueAlpha : ℂ := (1 - Complex.I) / 2

/-- The complex weight of the coordinate `(i, (b, a))` in the `(a, b)`-entry. -/
def gueBeta : ℂ := (1 + Complex.I) / 2

lemma gueAlpha_add_gueBeta : gueAlpha + gueBeta = 1 := by
  simp only [gueAlpha, gueBeta]
  ring

lemma gueAlpha_mul_gueBeta : gueAlpha * gueBeta = 1 / 2 := by
  simp only [gueAlpha, gueBeta]
  ring_nf
  norm_num

lemma gueAlpha_sq_add_gueBeta_sq : gueAlpha ^ 2 + gueBeta ^ 2 = 0 := by
  simp only [gueAlpha, gueBeta]
  ring_nf
  norm_num

lemma gueAlpha_mul_gueBeta_add : gueAlpha * gueBeta + gueBeta * gueAlpha = 1 := by
  simp only [gueAlpha, gueBeta]
  ring_nf
  norm_num

lemma star_gueAlpha : star gueAlpha = gueBeta := by
  simp [gueAlpha, gueBeta]

lemma star_gueBeta : star gueBeta = gueAlpha := by
  simp [gueAlpha, gueBeta]
  ring

lemma gueAlpha_mul_self_add_gueBeta_mul_self :
    gueAlpha * gueAlpha + gueBeta * gueBeta = 0 := by
  rw [← gueAlpha_sq_add_gueBeta_sq]
  ring

/-- The unnormalized complex GUE matrix with label `i`. Its `(a, b)`-entry is the complex
combination `α x (i, (a, b)) + β x (i, (b, a))` of the two real coordinates of the pair. -/
def gueUnscaled (x : GUECoord ι N → ℝ) (i : ι) : Matrix (Fin N) (Fin N) ℂ :=
  fun a b => gueAlpha * ((x (i, (a, b)) : ℝ) : ℂ) + gueBeta * ((x (i, (b, a)) : ℝ) : ℂ)

/-- The normalization factor `N^{-1/2}`. -/
def gueScale (N : ℕ) : ℝ := Real.sqrt ((N : ℝ)⁻¹)

/-- The normalized complex GUE matrix with label `i`. -/
def gueMatrix (x : GUECoord ι N → ℝ) (i : ι) : Matrix (Fin N) (Fin N) ℂ :=
  fun a b => (gueScale N : ℂ) * gueUnscaled x i a b

lemma gueScale_sq (N : ℕ) : gueScale N ^ 2 = (N : ℝ)⁻¹ := by
  rw [gueScale, pow_two, Real.mul_self_sqrt (by positivity)]

lemma gueScale_nonneg (N : ℕ) : 0 ≤ gueScale N := by
  rw [gueScale]
  positivity

lemma gueScale_mul_self_complex (N : ℕ) :
    (gueScale N : ℂ) * (gueScale N : ℂ) = ((N : ℝ)⁻¹ : ℂ) := by
  have h : gueScale N * gueScale N = (N : ℝ)⁻¹ := by
    rw [← pow_two]; exact gueScale_sq N
  rw [← Complex.ofReal_mul, h]
  simp

/-- Diagonal entries are real (they equal the single diagonal coordinate). -/
lemma gueUnscaled_diag (x : GUECoord ι N → ℝ) (i : ι) (a : Fin N) :
    gueUnscaled x i a a = ((x (i, (a, a)) : ℝ) : ℂ) := by
  simp only [gueUnscaled, ← add_mul, gueAlpha_add_gueBeta, one_mul]

lemma gueMatrix_diag (x : GUECoord ι N → ℝ) (i : ι) (a : Fin N) :
    gueMatrix x i a a = (gueScale N : ℂ) * ((x (i, (a, a)) : ℝ) : ℂ) := by
  simp [gueMatrix, gueUnscaled_diag]

/-- The unnormalized GUE matrix is Hermitian, pointwise in the Gaussian coordinates. -/
theorem gueUnscaled_conjTranspose (x : GUECoord ι N → ℝ) (i : ι) :
    (gueUnscaled x i)ᴴ = gueUnscaled x i := by
  ext a b
  simp only [Matrix.conjTranspose_apply, gueUnscaled, star_add, star_mul, star_gueAlpha,
    star_gueBeta]
  simp
  ring

/-- The unnormalized GUE matrix is Hermitian, pointwise in the Gaussian coordinates. -/
theorem gueUnscaled_isHermitian (x : GUECoord ι N → ℝ) (i : ι) :
    (gueUnscaled x i).IsHermitian :=
  gueUnscaled_conjTranspose x i

/-- The normalized GUE matrix is Hermitian, pointwise in the Gaussian coordinates. -/
theorem gueMatrix_conjTranspose (x : GUECoord ι N → ℝ) (i : ι) :
    (gueMatrix x i)ᴴ = gueMatrix x i := by
  ext a b
  simp only [Matrix.conjTranspose_apply, gueMatrix, gueUnscaled, star_mul, star_add,
    star_gueAlpha, star_gueBeta]
  simp
  ring

/-- The normalized GUE matrix is Hermitian, pointwise in the Gaussian coordinates. -/
theorem gueMatrix_isHermitian (x : GUECoord ι N → ℝ) (i : ι) :
    (gueMatrix x i).IsHermitian :=
  gueMatrix_conjTranspose x i

/-- Each entry of the GUE matrix is a measurable function of the Gaussian coordinates. -/
theorem measurable_gueMatrix_entry [Fintype ι] (i : ι) (a b : Fin N) :
    Measurable fun x : EuclideanSpace ℝ (GUECoord ι N) => gueMatrix x i a b := by
  have hcont : Continuous fun x : EuclideanSpace ℝ (GUECoord ι N) =>
      gueMatrix x i a b := by
    unfold gueMatrix gueUnscaled
    fun_prop
  exact hcont.measurable

/-! ### Second moments of the Gaussian coordinates

The standard Gaussian measure on `EuclideanSpace ℝ κ` has coordinate covariance the identity;
this is read off from Mathlib's `covarianceBilin_stdGaussian`. -/

/-- The second moment of two real Gaussian coordinates. -/
lemma integral_coord_mul_coord {κ : Type*} [Fintype κ] [DecidableEq κ] (p q : κ) :
    ∫ x : EuclideanSpace ℝ κ, x p * x q ∂(stdGaussian (EuclideanSpace ℝ κ)) =
      if p = q then 1 else 0 := by
  have hmem : MemLp (id : EuclideanSpace ℝ κ → EuclideanSpace ℝ κ) 2
      (stdGaussian (EuclideanSpace ℝ κ)) := IsGaussian.memLp_two_id
  have hzero : ∫ z : EuclideanSpace ℝ κ, z ∂(stdGaussian (EuclideanSpace ℝ κ)) = 0 :=
    integral_id_stdGaussian
  have key := covarianceBilin_apply (μ := stdGaussian (EuclideanSpace ℝ κ)) hmem
    (EuclideanSpace.basisFun κ ℝ p) (EuclideanSpace.basisFun κ ℝ q)
  rw [covarianceBilin_stdGaussian, innerSL_apply_apply] at key
  have key' : ⟪EuclideanSpace.basisFun κ ℝ p, EuclideanSpace.basisFun κ ℝ q⟫
      = ∫ z, ⟪EuclideanSpace.basisFun κ ℝ p, z⟫ *
          ⟪EuclideanSpace.basisFun κ ℝ q, z⟫ ∂(stdGaussian (EuclideanSpace ℝ κ)) := by
    simpa [hzero] using key
  have hintegrand :
      (∫ x : EuclideanSpace ℝ κ, x p * x q ∂(stdGaussian (EuclideanSpace ℝ κ)))
        = ∫ z, ⟪EuclideanSpace.basisFun κ ℝ p, z⟫ *
            ⟪EuclideanSpace.basisFun κ ℝ q, z⟫ ∂(stdGaussian (EuclideanSpace ℝ κ)) := by
    simp only [EuclideanSpace.basisFun_inner]
  rw [hintegrand, ← key']
  simpa using (orthonormal_iff_ite.mp (EuclideanSpace.basisFun κ ℝ).orthonormal p q)

/-- The second moment of two complexified real Gaussian coordinates. -/
lemma integral_coord_mul_coord_complex {κ : Type*} [Fintype κ] [DecidableEq κ] (p q : κ) :
    ∫ x : EuclideanSpace ℝ κ, ((x p : ℝ) : ℂ) * ((x q : ℝ) : ℂ) ∂
        (stdGaussian (EuclideanSpace ℝ κ)) = if p = q then 1 else 0 := by
  rw [show (∫ x : EuclideanSpace ℝ κ, ((x p : ℝ) : ℂ) * ((x q : ℝ) : ℂ) ∂
        (stdGaussian (EuclideanSpace ℝ κ)))
      = ∫ x : EuclideanSpace ℝ κ, ((x p * x q : ℝ) : ℂ) ∂
        (stdGaussian (EuclideanSpace ℝ κ)) from by
    simp_rw [Complex.ofReal_mul]]
  rw [show (∫ x : EuclideanSpace ℝ κ, ((x p * x q : ℝ) : ℂ) ∂
        (stdGaussian (EuclideanSpace ℝ κ)))
      = ((∫ x : EuclideanSpace ℝ κ, (x p * x q : ℝ) ∂
          (stdGaussian (EuclideanSpace ℝ κ)) : ℝ) : ℂ) from integral_ofReal]
  rw [integral_coord_mul_coord]
  split_ifs <;> simp

lemma memLp_coord {κ : Type*} [Fintype κ] (p : κ) :
    MemLp (fun x : EuclideanSpace ℝ κ => x p) 2 (stdGaussian (EuclideanSpace ℝ κ)) := by
  have h := (innerSL ℝ (EuclideanSpace.basisFun κ ℝ p)).comp_memLp'
    (IsGaussian.memLp_two_id (μ := stdGaussian (EuclideanSpace ℝ κ))
      (E := EuclideanSpace ℝ κ))
  simpa [EuclideanSpace.basisFun_inner] using h

lemma memLp_coord_complex {κ : Type*} [Fintype κ] (p : κ) :
    MemLp (fun x : EuclideanSpace ℝ κ => ((x p : ℝ) : ℂ)) 2
      (stdGaussian (EuclideanSpace ℝ κ)) :=
  (memLp_coord p).ofReal

/-- Integrability of a product of two complexified Gaussian coordinates. -/
lemma integrable_coord_mul_coord_complex {κ : Type*} [Fintype κ] (p q : κ) :
    Integrable (fun x : EuclideanSpace ℝ κ => ((x p : ℝ) : ℂ) * ((x q : ℝ) : ℂ))
      (stdGaussian (EuclideanSpace ℝ κ)) := by
  exact memLp_one_iff_integrable.mp
    (MemLp.mul (p := 2) (q := 2) (r := 1) (memLp_coord_complex p) (memLp_coord_complex q))

/-! ### The covariance identity -/

/-- Four-term expansion of an integral of a sum, used for the `2 × 2` product below. -/
lemma integral_four_terms {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f₁ f₂ f₃ f₄ : α → ℂ}
    (h₁ : Integrable f₁ μ) (h₂ : Integrable f₂ μ) (h₃ : Integrable f₃ μ)
    (h₄ : Integrable f₄ μ) :
    ∫ x, ((f₁ x + f₂ x) + (f₃ x + f₄ x)) ∂μ
      = ∫ x, f₁ x ∂μ + ∫ x, f₂ x ∂μ + ∫ x, f₃ x ∂μ + ∫ x, f₄ x ∂μ := by
  have h12 : Integrable (fun x => f₁ x + f₂ x) μ := h₁.add h₂
  have h34 : Integrable (fun x => f₃ x + f₄ x) μ := h₃.add h₄
  rw [integral_add h12 h34, integral_add h₁ h₂, integral_add h₃ h₄]
  ring

/-- The covariance of the *unnormalized* GUE entries, for two matrix labels `i`, `j`.
This is the key algebraic computation: expanding the `2 × 2` product of complex
combinations of the real coordinates and using `α² + β² = 0`, `2 α β = 1`. -/
theorem integral_gueUnscaled_mul [Fintype ι] [DecidableEq ι]
    (i j : ι) (a b c d : Fin N) :
    ∫ x : EuclideanSpace ℝ (GUECoord ι N),
        gueUnscaled x i a b * gueUnscaled x j c d ∂
          (stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))
      = if i = j ∧ a = d ∧ b = c then (1 : ℂ) else 0 := by
  have hpt : ∀ x : EuclideanSpace ℝ (GUECoord ι N),
      gueUnscaled x i a b * gueUnscaled x j c d
        = (gueAlpha * gueAlpha *
            (((x (i, (a, b)) : ℝ) : ℂ) * ((x (j, (c, d)) : ℝ) : ℂ))
          + gueAlpha * gueBeta *
            (((x (i, (a, b)) : ℝ) : ℂ) * ((x (j, (d, c)) : ℝ) : ℂ)))
          + (gueBeta * gueAlpha *
            (((x (i, (b, a)) : ℝ) : ℂ) * ((x (j, (c, d)) : ℝ) : ℂ))
          + gueBeta * gueBeta *
            (((x (i, (b, a)) : ℝ) : ℂ) * ((x (j, (d, c)) : ℝ) : ℂ))) := by
    intro x
    simp only [gueUnscaled]
    ring
  have hmom : ∀ p q : GUECoord ι N,
      ∫ x : EuclideanSpace ℝ (GUECoord ι N),
          ((x p : ℝ) : ℂ) * ((x q : ℝ) : ℂ) ∂
            (stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) = if p = q then 1 else 0 :=
    integral_coord_mul_coord_complex
  have h₁ : Integrable (fun x : EuclideanSpace ℝ (GUECoord ι N) =>
      gueAlpha * gueAlpha *
        (((x (i, (a, b)) : ℝ) : ℂ) * ((x (j, (c, d)) : ℝ) : ℂ)))
      (stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) :=
    (integrable_coord_mul_coord_complex (i, (a, b)) (j, (c, d))).const_mul _
  have h₂ : Integrable (fun x : EuclideanSpace ℝ (GUECoord ι N) =>
      gueAlpha * gueBeta *
        (((x (i, (a, b)) : ℝ) : ℂ) * ((x (j, (d, c)) : ℝ) : ℂ)))
      (stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) :=
    (integrable_coord_mul_coord_complex (i, (a, b)) (j, (d, c))).const_mul _
  have h₃ : Integrable (fun x : EuclideanSpace ℝ (GUECoord ι N) =>
      gueBeta * gueAlpha *
        (((x (i, (b, a)) : ℝ) : ℂ) * ((x (j, (c, d)) : ℝ) : ℂ)))
      (stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) :=
    (integrable_coord_mul_coord_complex (i, (b, a)) (j, (c, d))).const_mul _
  have h₄ : Integrable (fun x : EuclideanSpace ℝ (GUECoord ι N) =>
      gueBeta * gueBeta *
        (((x (i, (b, a)) : ℝ) : ℂ) * ((x (j, (d, c)) : ℝ) : ℂ)))
      (stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) :=
    (integrable_coord_mul_coord_complex (i, (b, a)) (j, (d, c))).const_mul _
  simp_rw [hpt]
  rw [integral_four_terms h₁ h₂ h₃ h₄]
  simp only [integral_const_mul, hmom]
  -- The two "same pair" conditions coincide, and the target condition is the second one.
  have e1 : ((i, (b, a)) = (j, (d, c)) ↔ (i, (a, b)) = (j, (c, d))) := by
    simp [Prod.mk.injEq, and_comm]
  have e2 : ((i, (b, a)) = (j, (c, d)) ↔ (i, (a, b)) = (j, (d, c))) := by
    simp [Prod.mk.injEq, and_comm]
  have e3 : ((i, (a, b)) = (j, (d, c)) ↔ (i = j ∧ a = d ∧ b = c)) := by
    simp [Prod.mk.injEq]
  simp only [e1, e2, e3]
  split_ifs <;> simp only [gueAlpha, gueBeta] <;> ring_nf <;> norm_num

/-- **Covariance of the normalized complex GUE** (equation (1.2) of the handoff):
for `r` independent normalized complex GUE matrices `G_i` on one Gaussian probability space,

`E[(G_i)_{ab} (G_j)_{cd}] = δ_{ij} δ_{ad} δ_{bc} / N`.

There is **no** complex conjugation in the left-hand side. -/
theorem integral_gueMatrix_mul [Fintype ι] [DecidableEq ι]
    (i j : ι) (a b c d : Fin N) :
    ∫ x : EuclideanSpace ℝ (GUECoord ι N),
        gueMatrix x i a b * gueMatrix x j c d ∂
          (stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))
      = if i = j ∧ a = d ∧ b = c then ((N : ℝ)⁻¹ : ℂ) else 0 := by
  have hpt : ∀ x : EuclideanSpace ℝ (GUECoord ι N),
      gueMatrix x i a b * gueMatrix x j c d
        = ((gueScale N : ℂ) * (gueScale N : ℂ)) *
            (gueUnscaled x i a b * gueUnscaled x j c d) := by
    intro x
    simp only [gueMatrix]
    ring
  simp_rw [hpt]
  rw [integral_const_mul, integral_gueUnscaled_mul, gueScale_mul_self_complex]
  split_ifs <;> simp

/-- The modulus-squared moment of an entry: `E[(G)_{ab} (G)_{ba}] = 1 / N`. In particular
diagonal entries of the normalized GUE have variance `1 / N`. -/
theorem integral_gueMatrix_mul_swap [Fintype ι] [DecidableEq ι]
    (i : ι) (a b : Fin N) :
    ∫ x : EuclideanSpace ℝ (GUECoord ι N),
        gueMatrix x i a b * gueMatrix x i b a ∂
          (stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) = ((N : ℝ)⁻¹ : ℂ) := by
  rw [integral_gueMatrix_mul]
  simp

/-- Off-diagonal entries are centred in the sense `E[(G)_{ab}^2] = 0` for `a ≠ b`. -/
theorem integral_gueMatrix_mul_self_of_ne [Fintype ι] [DecidableEq ι]
    (i : ι) {a b : Fin N} (hab : a ≠ b) :
    ∫ x : EuclideanSpace ℝ (GUECoord ι N),
        gueMatrix x i a b * gueMatrix x i a b ∂
          (stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) = 0 := by
  rw [integral_gueMatrix_mul]
  split_ifs with h'
  · exact absurd h'.2.1 hab
  · rfl

end

section SpectralMoments

variable {ι : Type*} {N : ℕ}

lemma integrable_gueUnscaled_mul [Fintype ι] [DecidableEq ι] (i j : ι) (a b c d : Fin N) :
    Integrable (fun x : EuclideanSpace ℝ (GUECoord ι N) =>
      gueUnscaled x i a b * gueUnscaled x j c d)
      (stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) := by
  have hpt : ∀ x : EuclideanSpace ℝ (GUECoord ι N),
      gueUnscaled x i a b * gueUnscaled x j c d
        = (gueAlpha * gueAlpha *
            (((x (i, (a, b)) : ℝ) : ℂ) * ((x (j, (c, d)) : ℝ) : ℂ))
          + gueAlpha * gueBeta *
            (((x (i, (a, b)) : ℝ) : ℂ) * ((x (j, (d, c)) : ℝ) : ℂ)))
          + (gueBeta * gueAlpha *
            (((x (i, (b, a)) : ℝ) : ℂ) * ((x (j, (c, d)) : ℝ) : ℂ))
          + gueBeta * gueBeta *
            (((x (i, (b, a)) : ℝ) : ℂ) * ((x (j, (d, c)) : ℝ) : ℂ))) := by
    intro x
    simp only [gueUnscaled]
    ring
  have h₁ := (integrable_coord_mul_coord_complex (i, (a, b)) (j, (c, d))).const_mul
    (gueAlpha * gueAlpha)
  have h₂ := (integrable_coord_mul_coord_complex (i, (a, b)) (j, (d, c))).const_mul
    (gueAlpha * gueBeta)
  have h₃ := (integrable_coord_mul_coord_complex (i, (b, a)) (j, (c, d))).const_mul
    (gueBeta * gueAlpha)
  have h₄ := (integrable_coord_mul_coord_complex (i, (b, a)) (j, (d, c))).const_mul
    (gueBeta * gueBeta)
  simp_rw [hpt]
  exact (h₁.add h₂).add (h₃.add h₄)

lemma integrable_gueMatrix_mul [Fintype ι] [DecidableEq ι] (i j : ι) (a b c d : Fin N) :
    Integrable (fun x : EuclideanSpace ℝ (GUECoord ι N) =>
      gueMatrix x i a b * gueMatrix x j c d)
      (stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) := by
  have hpt : ∀ x : EuclideanSpace ℝ (GUECoord ι N),
      gueMatrix x i a b * gueMatrix x j c d
        = ((gueScale N : ℂ) * (gueScale N : ℂ)) *
            (gueUnscaled x i a b * gueUnscaled x j c d) := by
    intro x
    simp only [gueMatrix]
    ring
  simp_rw [hpt]
  exact (integrable_gueUnscaled_mul i j a b c d).const_mul _

/-- **First spectral moment**: `E[tr(G^2)] = N` for the normalized GUE. -/
theorem integral_trace_gueMatrix_mul_self [Fintype ι] [DecidableEq ι] (i : ι) (hN : 0 < N) :
    ∫ x : EuclideanSpace ℝ (GUECoord ι N),
        Matrix.trace ((gueMatrix x i) * (gueMatrix x i))
      ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) = (N : ℂ) := by
  have htr : ∀ x : EuclideanSpace ℝ (GUECoord ι N),
      Matrix.trace ((gueMatrix x i) * (gueMatrix x i))
        = ∑ a, ∑ b, gueMatrix x i a b * gueMatrix x i b a := by
    intro x
    simp [Matrix.trace, Matrix.diag, Matrix.mul_apply]
  simp_rw [htr]
  rw [integral_finsetSum Finset.univ (fun a _ => integrable_finsetSum Finset.univ
    (fun b _ => integrable_gueMatrix_mul i i a b b a))]
  have hinner : ∀ a : Fin N, (∫ x : EuclideanSpace ℝ (GUECoord ι N),
      ∑ b : Fin N, gueMatrix x i a b * gueMatrix x i b a
      ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))) = ∑ _b : Fin N, ((N : ℝ)⁻¹ : ℂ) := by
    intro a
    rw [integral_finsetSum Finset.univ (fun b _ => integrable_gueMatrix_mul i i a b b a)]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [integral_gueMatrix_mul]
    simp
  simp only [hinner, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hNc : (N : ℂ) ≠ 0 := by
    have hpos : (0:ℕ) < N := hN
    exact_mod_cast (Nat.pos_iff_ne_zero.mp hpos)
  field_simp
  norm_num
  exact_mod_cast (Nat.pos_iff_ne_zero.mp hN)

end SpectralMoments

section CoordDeriv

variable {ι : Type*} {N : ℕ} [DecidableEq ι]

/-- Differentiation in one coordinate of the unnormalized GUE entry. -/
theorem hasDerivAt_gueUnscaled_update (x : GUECoord ι N → ℝ) (p : GUECoord ι N) (i : ι)
    (a b : Fin N) (t₀ : ℝ) :
    HasDerivAt (fun t : ℝ => gueUnscaled (Function.update x p t) i a b)
      (gueAlpha * (if p = (i, (a, b)) then (1:ℂ) else 0) +
        gueBeta * (if p = (i, (b, a)) then (1:ℂ) else 0)) t₀ := by
  have hstep : ∀ (c : ℂ) (q : GUECoord ι N),
      HasDerivAt (fun t : ℝ => c * ((Function.update x p t q : ℝ) : ℂ))
        (c * (if p = q then (1:ℂ) else 0)) t₀ := by
    intro c q
    by_cases h : p = q
    · have hfun : (fun t : ℝ => c * ((Function.update x p t q : ℝ) : ℂ)) = fun t : ℝ => c * (t : ℂ) := by
        funext t
        rw [h]
        simp
      rw [hfun, h]
      simpa using (Complex.ofRealCLM.hasDerivAt (x := t₀)).const_mul c
    · have hfun : (fun t : ℝ => c * ((Function.update x p t q : ℝ) : ℂ))
          = fun _ => c * ((x q : ℝ) : ℂ) := by
        funext t
        rw [Function.update_of_ne (Ne.symm h) t x]
      rw [hfun]
      simp only [h]
      simpa using hasDerivAt_const t₀ (c * ((x q : ℝ) : ℂ))
  have h1 := hstep gueAlpha (i, (a, b))
  have h2 := hstep gueBeta (i, (b, a))
  refine (h1.add h2).congr_of_eventuallyEq (Filter.Eventually.of_forall (fun t => ?_))
  show gueAlpha * ((Function.update x p t (i, (a, b)) : ℝ) : ℂ)
      + gueBeta * ((Function.update x p t (i, (b, a)) : ℝ) : ℂ)
      = gueUnscaled (Function.update x p t) i a b
  rfl

/-- The normalized GUE entry, differentiated in one coordinate. -/
theorem hasDerivAt_gueMatrix_update (x : GUECoord ι N → ℝ) (p : GUECoord ι N) (i : ι)
    (a b : Fin N) (t₀ : ℝ) :
    HasDerivAt (fun t : ℝ => gueMatrix (Function.update x p t) i a b)
      ((gueScale N : ℂ) * (gueAlpha * (if p = (i, (a, b)) then (1:ℂ) else 0) +
        gueBeta * (if p = (i, (b, a)) then (1:ℂ) else 0))) t₀ := by
  have h := hasDerivAt_gueUnscaled_update x p i a b t₀
  have := h.const_mul ((gueScale N : ℂ))
  refine this.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun t => ?_))
  show (gueScale N : ℂ) * gueUnscaled (Function.update x p t) i a b
    = gueMatrix (Function.update x p t) i a b
  rfl

end CoordDeriv

end GUEStrongConvergence
