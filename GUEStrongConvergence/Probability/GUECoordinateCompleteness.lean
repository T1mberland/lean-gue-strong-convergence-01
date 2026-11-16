/-
# Completeness and Parseval for the actual GUE coordinate matrices

For the single-entry coordinate matrices
`C_ab = gueAlpha • E_ab + gueBeta • E_ba` (no normalization),
this module proves

* `∑ a b, C_ab * B * C_ab = trace(B) • 1` for every complex `B`,
* the Hilbert--Schmidt Parseval identity
  `∑ a b, ‖trace(B * C_ab)‖² = ∑ a b, ‖B a b‖²`,

and their normalized versions with `gueScale N`:

* `∑ a b, (s • C_ab) * B * (s • C_ab) = (N⁻¹ * trace B) • 1`,
* `∑ a b, ‖trace(B * (s • C_ab))‖² = N⁻¹ * ∑ a b, ‖B a b‖²`.

Here `C_ab` is exactly the derivative of the GUE coordinate direction `(a, b)` before the
`N^{-1/2}` normalization, so these identities are the coordinate-frame completeness needed
for the trace-variance computation.
-/
import GUEStrongConvergence.Probability.GUEModel
import GUEStrongConvergence.Probability.Fierz
open Matrix
open scoped Matrix

namespace GUEStrongConvergence

noncomputable section

variable {N : ℕ}

/-- The unnormalized single-entry GUE coordinate matrix
`C_ab = α E_ab + β E_ba`. -/
def gueCoordMatrix (a b : Fin N) : Matrix (Fin N) (Fin N) ℂ :=
  gueAlpha • Matrix.single a b (1 : ℂ) + gueBeta • Matrix.single b a (1 : ℂ)

/-- Every unnormalized GUE coordinate matrix is Hermitian. -/
lemma gueCoordMatrix_conjTranspose (a b : Fin N) :
    (gueCoordMatrix a b)ᴴ = gueCoordMatrix a b := by
  simp [gueCoordMatrix, Matrix.conjTranspose_single,
    star_gueAlpha, star_gueBeta, add_comm]

/-- Every unnormalized GUE coordinate matrix is Hermitian. -/
lemma gueCoordMatrix_isHermitian (a b : Fin N) :
    (gueCoordMatrix a b).IsHermitian :=
  gueCoordMatrix_conjTranspose a b

/-- Expansion of `C_ab * B * C_ab` into four matrix units. -/
lemma gueCoordMatrix_mul_mul (B : Matrix (Fin N) (Fin N) ℂ) (a b : Fin N) :
    gueCoordMatrix a b * B * gueCoordMatrix a b =
      (gueAlpha * gueAlpha * B b a) • Matrix.single a b (1 : ℂ) +
      (gueBeta * gueBeta * B a b) • Matrix.single b a (1 : ℂ) +
      (gueAlpha * gueBeta * B b b) • Matrix.single a a (1 : ℂ) +
      (gueBeta * gueAlpha * B a a) • Matrix.single b b (1 : ℂ) := by
  simp only [gueCoordMatrix, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.single_mul_mul_single, smul_smul, smul_add, one_mul, mul_one]
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.single_apply]
  split_ifs <;> ring

/-- The off-diagonal part of the completeness sum vanishes. -/
lemma gueCoord_offdiag_sum_zero (B : Matrix (Fin N) (Fin N) ℂ) :
    (∑ a, ∑ b, (gueAlpha * gueAlpha * B b a) • Matrix.single a b (1 : ℂ)) +
    (∑ a, ∑ b, (gueBeta * gueBeta * B a b) • Matrix.single b a (1 : ℂ)) = 0 := by
  have hswap : (∑ a, ∑ b, (gueBeta * gueBeta * B a b) • Matrix.single b a (1 : ℂ))
      = ∑ a, ∑ b, (gueBeta * gueBeta * B b a) • Matrix.single a b (1 : ℂ) := by
    rw [Finset.sum_comm]
  rw [hswap]
  have hcombine :
      (∑ a, ∑ b, (gueAlpha * gueAlpha * B b a) • Matrix.single a b (1 : ℂ)) +
        (∑ a, ∑ b, (gueBeta * gueBeta * B b a) • Matrix.single a b (1 : ℂ))
      = ∑ a, ∑ b,
          ((gueAlpha * gueAlpha * B b a) • Matrix.single a b (1 : ℂ) +
            (gueBeta * gueBeta * B b a) • Matrix.single a b (1 : ℂ)) := by
    calc
      (∑ a, ∑ b, (gueAlpha * gueAlpha * B b a) • Matrix.single a b (1 : ℂ)) +
          (∑ a, ∑ b, (gueBeta * gueBeta * B b a) • Matrix.single a b (1 : ℂ))
          = ∑ a, ((∑ b, (gueAlpha * gueAlpha * B b a) • Matrix.single a b (1 : ℂ)) +
              ∑ b, (gueBeta * gueBeta * B b a) • Matrix.single a b (1 : ℂ)) :=
            (Finset.sum_add_distrib).symm
      _ = ∑ a, ∑ b,
            ((gueAlpha * gueAlpha * B b a) • Matrix.single a b (1 : ℂ) +
              (gueBeta * gueBeta * B b a) • Matrix.single a b (1 : ℂ)) := by
          refine Finset.sum_congr rfl fun a _ => ?_
          exact (Finset.sum_add_distrib).symm
  rw [hcombine]
  have hzero : ∀ a b : Fin N,
      (gueAlpha * gueAlpha * B b a) • Matrix.single a b (1 : ℂ) +
        (gueBeta * gueBeta * B b a) • Matrix.single a b (1 : ℂ) = 0 := by
    intro a b
    rw [← add_smul]
    rw [show gueAlpha * gueAlpha * B b a + gueBeta * gueBeta * B b a = 0 by
      rw [← add_mul, show gueAlpha * gueAlpha + gueBeta * gueBeta = 0 by
        simpa [pow_two] using gueAlpha_sq_add_gueBeta_sq, zero_mul]]
    simp
  simp_rw [hzero]
  simp

/-- The diagonal part of the completeness sum is `trace(B) • 1`. -/
lemma gueCoord_diag_sum (B : Matrix (Fin N) (Fin N) ℂ) :
    (∑ a, ∑ b, (gueAlpha * gueBeta * B b b) • Matrix.single a a (1 : ℂ)) +
    (∑ a, ∑ b, (gueBeta * gueAlpha * B a a) • Matrix.single b b (1 : ℂ))
      = B.trace • (1 : Matrix (Fin N) (Fin N) ℂ) := by
  have h3 : (∑ a, ∑ b, (gueAlpha * gueBeta * B b b) • Matrix.single a a (1 : ℂ))
      = (gueAlpha * gueBeta) • (B.trace • (1 : Matrix (Fin N) (Fin N) ℂ)) := by
    calc
      (∑ a, ∑ b, (gueAlpha * gueBeta * B b b) • Matrix.single a a (1 : ℂ))
          = ∑ a, ∑ b, (gueAlpha * gueBeta) • (B b b • Matrix.single a a (1 : ℂ)) := by
            refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
            rw [mul_smul]
      _ = ∑ a, (gueAlpha * gueBeta) • (∑ b, B b b • Matrix.single a a (1 : ℂ)) := by
            refine Finset.sum_congr rfl fun a _ => ?_
            rw [Finset.smul_sum]
      _ = (gueAlpha * gueBeta) • (∑ a, ∑ b, B b b • Matrix.single a a (1 : ℂ)) := by
            rw [Finset.smul_sum]
      _ = (gueAlpha * gueBeta) • (B.trace • (1 : Matrix (Fin N) (Fin N) ℂ)) := by
            congr 1
            rw [← sum_single_diag B]
            refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
            simp [Matrix.smul_single, smul_eq_mul]
  have h4 : (∑ a, ∑ b, (gueBeta * gueAlpha * B a a) • Matrix.single b b (1 : ℂ))
      = (gueBeta * gueAlpha) • (B.trace • (1 : Matrix (Fin N) (Fin N) ℂ)) := by
    calc
      (∑ a, ∑ b, (gueBeta * gueAlpha * B a a) • Matrix.single b b (1 : ℂ))
          = ∑ a, ∑ b, (gueBeta * gueAlpha) • (B a a • Matrix.single b b (1 : ℂ)) := by
            refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
            rw [mul_smul]
      _ = ∑ a, (gueBeta * gueAlpha) • (∑ b, B a a • Matrix.single b b (1 : ℂ)) := by
            refine Finset.sum_congr rfl fun a _ => ?_
            rw [Finset.smul_sum]
      _ = (gueBeta * gueAlpha) • (∑ a, ∑ b, B a a • Matrix.single b b (1 : ℂ)) := by
            rw [Finset.smul_sum]
      _ = (gueBeta * gueAlpha) • (∑ b, ∑ a, B a a • Matrix.single b b (1 : ℂ)) := by
            rw [Finset.sum_comm]
      _ = (gueBeta * gueAlpha) • (B.trace • (1 : Matrix (Fin N) (Fin N) ℂ)) := by
            congr 1
            rw [← sum_single_diag B]
            refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
            simp [Matrix.smul_single, smul_eq_mul]
  rw [h3, h4, ← add_smul, gueAlpha_mul_gueBeta_add, one_smul]

/-- **Completeness (Fierz) identity for the actual GUE coordinate matrices.** -/
theorem gueCoord_fierz (B : Matrix (Fin N) (Fin N) ℂ) :
    ∑ a, ∑ b, gueCoordMatrix a b * B * gueCoordMatrix a b
      = B.trace • (1 : Matrix (Fin N) (Fin N) ℂ) := by
  simp_rw [gueCoordMatrix_mul_mul]
  simp only [Finset.sum_add_distrib]
  rw [add_assoc]
  rw [gueCoord_offdiag_sum_zero B]
  rw [zero_add, gueCoord_diag_sum B]

/-- The trace of `B * C_ab` is `α B_ba + β B_ab`. -/
lemma gueCoordMatrix_trace_mul (B : Matrix (Fin N) (Fin N) ℂ) (a b : Fin N) :
    (B * gueCoordMatrix a b).trace = gueAlpha * B b a + gueBeta * B a b := by
  simp [gueCoordMatrix, Matrix.mul_add, Matrix.trace_add, Matrix.trace_mul_single, mul_comm]

/-- Pairwise Hilbert--Schmidt isometry of the coordinate combination. -/
lemma gueCoord_coeff_parseval (z w : ℂ) :
    ‖gueAlpha * z + gueBeta * w‖ ^ 2 + ‖gueAlpha * w + gueBeta * z‖ ^ 2
      = ‖z‖ ^ 2 + ‖w‖ ^ 2 := by
  rw [Complex.sq_norm, Complex.sq_norm, Complex.sq_norm, Complex.sq_norm]
  simp [Complex.normSq_apply, gueAlpha, gueBeta]
  ring


/-- **Hilbert--Schmidt Parseval for the actual GUE coordinate frame.** -/
theorem gueCoord_parseval (B : Matrix (Fin N) (Fin N) ℂ) :
    ∑ a, ∑ b, ‖(B * gueCoordMatrix a b).trace‖ ^ 2
      = ∑ a, ∑ b, ‖B a b‖ ^ 2 := by
  simp_rw [gueCoordMatrix_trace_mul]
  have hpair : ∀ a b : Fin N,
      ‖gueAlpha * B b a + gueBeta * B a b‖ ^ 2 +
        ‖gueAlpha * B a b + gueBeta * B b a‖ ^ 2
      = ‖B b a‖ ^ 2 + ‖B a b‖ ^ 2 := fun a b =>
        gueCoord_coeff_parseval (B b a) (B a b)
  have hL : (∑ a, ∑ b, (‖gueAlpha * B b a + gueBeta * B a b‖ ^ 2 +
        ‖gueAlpha * B a b + gueBeta * B b a‖ ^ 2))
      = (∑ a, ∑ b, ‖gueAlpha * B b a + gueBeta * B a b‖ ^ 2) +
        (∑ a, ∑ b, ‖gueAlpha * B b a + gueBeta * B a b‖ ^ 2) := by
    calc
      (∑ a, ∑ b, (‖gueAlpha * B b a + gueBeta * B a b‖ ^ 2 +
          ‖gueAlpha * B a b + gueBeta * B b a‖ ^ 2))
          = ∑ a, ((∑ b, ‖gueAlpha * B b a + gueBeta * B a b‖ ^ 2) +
              ∑ b, ‖gueAlpha * B a b + gueBeta * B b a‖ ^ 2) := by
            refine Finset.sum_congr rfl fun a _ => ?_
            exact (Finset.sum_add_distrib (s := Finset.univ)
              (f := fun b => ‖gueAlpha * B b a + gueBeta * B a b‖ ^ 2)
              (g := fun b => ‖gueAlpha * B a b + gueBeta * B b a‖ ^ 2))
      _ = (∑ a, ∑ b, ‖gueAlpha * B b a + gueBeta * B a b‖ ^ 2) +
            (∑ a, ∑ b, ‖gueAlpha * B a b + gueBeta * B b a‖ ^ 2) :=
            (Finset.sum_add_distrib (s := Finset.univ)
              (f := fun a => ∑ b, ‖gueAlpha * B b a + gueBeta * B a b‖ ^ 2)
              (g := fun a => ∑ b, ‖gueAlpha * B a b + gueBeta * B b a‖ ^ 2))
      _ = (∑ a, ∑ b, ‖gueAlpha * B b a + gueBeta * B a b‖ ^ 2) +
            (∑ a, ∑ b, ‖gueAlpha * B b a + gueBeta * B a b‖ ^ 2) := by
            congr 1
            rw [Finset.sum_comm]
  have hR : (∑ a, ∑ b, (‖B b a‖ ^ 2 + ‖B a b‖ ^ 2))
      = (∑ a, ∑ b, ‖B a b‖ ^ 2) + (∑ a, ∑ b, ‖B a b‖ ^ 2) := by
    calc
      (∑ a, ∑ b, (‖B b a‖ ^ 2 + ‖B a b‖ ^ 2))
          = ∑ a, ((∑ b, ‖B b a‖ ^ 2) + ∑ b, ‖B a b‖ ^ 2) := by
            refine Finset.sum_congr rfl fun a _ => ?_
            exact (Finset.sum_add_distrib (s := Finset.univ)
              (f := fun b => ‖B b a‖ ^ 2) (g := fun b => ‖B a b‖ ^ 2))
      _ = (∑ a, ∑ b, ‖B b a‖ ^ 2) + (∑ a, ∑ b, ‖B a b‖ ^ 2) :=
            (Finset.sum_add_distrib (s := Finset.univ)
              (f := fun a => ∑ b, ‖B b a‖ ^ 2)
              (g := fun a => ∑ b, ‖B a b‖ ^ 2))
      _ = (∑ a, ∑ b, ‖B a b‖ ^ 2) + (∑ a, ∑ b, ‖B a b‖ ^ 2) := by
            congr 1
            rw [Finset.sum_comm]
  have hcross := Finset.sum_congr rfl fun a (_ : a ∈ Finset.univ) =>
    Finset.sum_congr rfl fun b (_ : b ∈ Finset.univ) => hpair a b
  have h2 : (∑ a, ∑ b, ‖gueAlpha * B b a + gueBeta * B a b‖ ^ 2) +
        (∑ a, ∑ b, ‖gueAlpha * B b a + gueBeta * B a b‖ ^ 2)
      = (∑ a, ∑ b, ‖B a b‖ ^ 2) + (∑ a, ∑ b, ‖B a b‖ ^ 2) := by
    rw [← hL, ← hR]
    exact hcross
  linarith

/-- Factoring a constant complex scalar out of a double sum of matrices. -/
lemma gueCoord_sum_smul_const {M : Type*} [AddCommMonoid M] [Module ℂ M]
    (c : ℂ) (F : Fin N → Fin N → M) :
    (∑ a, ∑ b, c • F a b) = c • (∑ a, ∑ b, F a b) := by
  calc
    (∑ a, ∑ b, c • F a b) = ∑ a, c • (∑ b, F a b) := by
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [← Finset.smul_sum]
    _ = c • (∑ a, ∑ b, F a b) := by
      rw [← Finset.smul_sum]

/-- Factoring a constant real scalar out of a double sum of reals. -/
lemma gueCoord_sum_mul_const (c : ℝ) (F : Fin N → Fin N → ℝ) :
    (∑ a, ∑ b, c * F a b) = c * (∑ a, ∑ b, F a b) := by
  calc
    (∑ a, ∑ b, c * F a b) = ∑ a, c * (∑ b, F a b) := by
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [← Finset.mul_sum]
    _ = c * (∑ a, ∑ b, F a b) := by
      rw [← Finset.mul_sum]

/-- Normalized completeness identity: the frame scaled by `gueScale N`. -/
theorem gueCoord_scaled_fierz (B : Matrix (Fin N) (Fin N) ℂ) :
    ∑ a, ∑ b,
        ((gueScale N : ℂ) • gueCoordMatrix a b) * B *
          ((gueScale N : ℂ) • gueCoordMatrix a b)
      = (((N : ℂ)⁻¹) * B.trace) • (1 : Matrix (Fin N) (Fin N) ℂ) := by
  have hterm : ∀ a b : Fin N,
      ((gueScale N : ℂ) • gueCoordMatrix a b) * B *
          ((gueScale N : ℂ) • gueCoordMatrix a b)
        = ((gueScale N : ℂ) * (gueScale N : ℂ)) •
            (gueCoordMatrix a b * B * gueCoordMatrix a b) := by
    intro a b
    simp [smul_smul, mul_assoc]
    ext i j
    simp [Complex.real_smul]
  calc
    (∑ a, ∑ b,
        ((gueScale N : ℂ) • gueCoordMatrix a b) * B *
          ((gueScale N : ℂ) • gueCoordMatrix a b))
        = ∑ a, ∑ b, ((gueScale N : ℂ) * (gueScale N : ℂ)) •
            (gueCoordMatrix a b * B * gueCoordMatrix a b) := by
          exact Finset.sum_congr rfl fun a _ =>
            Finset.sum_congr rfl fun b _ => hterm a b
    _ = ((gueScale N : ℂ) * (gueScale N : ℂ)) •
          (∑ a, ∑ b, gueCoordMatrix a b * B * gueCoordMatrix a b) :=
          gueCoord_sum_smul_const (c := (gueScale N : ℂ) * (gueScale N : ℂ))
            (F := fun a b => gueCoordMatrix a b * B * gueCoordMatrix a b)
    _ = ((gueScale N : ℂ) * (gueScale N : ℂ)) •
          (B.trace • (1 : Matrix (Fin N) (Fin N) ℂ)) := by
          rw [gueCoord_fierz]
    _ = (((N : ℂ)⁻¹) * B.trace) • (1 : Matrix (Fin N) (Fin N) ℂ) := by
          rw [gueScale_mul_self_complex]
          rw [smul_smul]
          congr 1

/-- Normalized trace Parseval identity: the `N⁻¹` factor of the scaled frame. -/
theorem gueCoord_scaled_parseval (B : Matrix (Fin N) (Fin N) ℂ) :
    ∑ a, ∑ b, ‖(B * ((gueScale N : ℂ) • gueCoordMatrix a b)).trace‖ ^ 2
      = ((N : ℝ)⁻¹) * ∑ a, ∑ b, ‖B a b‖ ^ 2 := by
  have hterm : ∀ a b : Fin N,
      ‖(B * ((gueScale N : ℂ) • gueCoordMatrix a b)).trace‖ ^ 2
        = ((N : ℝ)⁻¹) * ‖(B * gueCoordMatrix a b).trace‖ ^ 2 := by
    intro a b
    have htrace : (B * ((gueScale N : ℂ) • gueCoordMatrix a b)).trace
        = (gueScale N : ℂ) * (B * gueCoordMatrix a b).trace := by
      simp
    rw [htrace, norm_mul, mul_pow]
    have hc : ‖(gueScale N : ℂ)‖ = gueScale N := by
      simpa [Complex.norm_real] using abs_of_nonneg (gueScale_nonneg N)
    rw [hc, gueScale_sq]
  simp_rw [hterm]
  rw [gueCoord_sum_mul_const (c := (N : ℝ)⁻¹)
    (F := fun a b : Fin N => ‖(B * gueCoordMatrix a b).trace‖ ^ 2)]
  rw [gueCoord_parseval]

end

end GUEStrongConvergence
