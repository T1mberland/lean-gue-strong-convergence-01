/-
# An orthonormal basis of Hermitian matrices, and the elementary Fierz products

This file defines the explicit Hermitian matrix basis used in the GUE construction of the
Part II handoff (section 1.1):

* diagonal elements `E_aa`;
* symmetric off-diagonal elements `(E_ab + E_ba)/√2`, `a < b`;
* imaginary off-diagonal elements `i (E_ab - E_ba)/√2`, `a < b`.

They are packaged as one family `hermBasis a b`, indexed by the ordered pair
`(a, b) : Fin N × Fin N`, which enumerates the `N²` basis elements exactly once: for `a < b`
the index `(a, b)` gives the symmetric element and the index `(b, a)` gives (minus) the
imaginary element. Every element is Hermitian, and the family is orthonormal for the real
inner product `Re tr(U V)` of Hermitian matrices.

The purpose of the file is to provide the *elementary products* needed for the completeness
(Fierz) identity `∑ a b, hermBasis a b * B * hermBasis a b = tr(B) • 1`:

* `hermBasis_mul_self_eq_single`: `E_aa * B * E_aa = single a a (B a a)`;
* `hermBasis_mul_mul_add`: for `a ≠ b`, the two basis elements of the pair `{a, b}` together
  contribute `single a a (B b b) + single b b (B a a)`.

Summing the second identity over all unordered pairs and adding the first gives the
completeness (Fierz) identity `∑ a b, hermBasis a b * B * hermBasis a b = tr(B) • 1`; the
summation step itself is the next target on the critical path, see `CURRENT_TASK.md`.
-/
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

open Matrix
open scoped Matrix

namespace GUEStrongConvergence

noncomputable section

variable {N : ℕ}

/-- The `(a, b)`-th element of the Hermitian matrix basis.

For `a = b` this is the diagonal unit matrix `E_aa`; for `a < b` it is `(E_ab + E_ba)/√2`;
for `b < a` it is `i (E_ab - E_ba)/√2` (so that the index `(b, a)` of the pair `{a, b}` is
the imaginary partner of the symmetric element indexed by `(a, b)`). -/
def hermBasis (a b : Fin N) : Matrix (Fin N) (Fin N) ℂ :=
  if a = b then Matrix.single a b (1 : ℂ)
  else if a < b then
    ((Real.sqrt 2 : ℂ)⁻¹) • (Matrix.single a b (1 : ℂ) + Matrix.single b a (1 : ℂ))
  else
    (Complex.I * ((Real.sqrt 2 : ℂ)⁻¹)) •
      (Matrix.single a b (1 : ℂ) - Matrix.single b a (1 : ℂ))

/-- Entrywise description of the basis element `hermBasis a b`, diagonal case. -/
@[simp]
lemma hermBasis_apply_self (a : Fin N) (i j : Fin N) :
    hermBasis a a i j = if a = i ∧ a = j then 1 else 0 := by
  simp [hermBasis, Matrix.single_apply]

/-- Entrywise description of the basis element `hermBasis a b` for `a < b`. -/
lemma hermBasis_apply_of_lt {a b : Fin N} (h : a < b) (i j : Fin N) :
    hermBasis a b i j = (Real.sqrt 2 : ℂ)⁻¹ *
      ((if a = i ∧ b = j then 1 else 0) + (if b = i ∧ a = j then 1 else 0)) := by
  have hne : ¬ a = b := ne_of_lt h
  simp [hermBasis, hne, h, Matrix.single_apply]

/-- Entrywise description of the basis element `hermBasis a b` for `b < a`. -/
lemma hermBasis_apply_of_gt {a b : Fin N} (h : b < a) (i j : Fin N) :
    hermBasis a b i j = Complex.I * (Real.sqrt 2 : ℂ)⁻¹ *
      ((if a = i ∧ b = j then 1 else 0) - (if b = i ∧ a = j then 1 else 0)) := by
  have hne : ¬ a = b := ne_of_gt h
  have hlt : ¬ a < b := not_lt.mpr h.le
  simp [hermBasis, hne, hlt, Matrix.single_apply]

/-- Every element of the basis is a Hermitian matrix. -/
theorem hermBasis_conjTranspose (a b : Fin N) : (hermBasis a b)ᴴ = hermBasis a b := by
  have hs : star ((Real.sqrt 2 : ℂ)⁻¹) = (Real.sqrt 2 : ℂ)⁻¹ := by
    rw [Complex.star_def]; simp
  have hI : star Complex.I = -Complex.I := by
    rw [Complex.star_def]; exact Complex.conj_I
  rcases lt_trichotomy a b with h | h | h
  · rw [show hermBasis a b
        = ((Real.sqrt 2 : ℂ)⁻¹) • (Matrix.single a b (1 : ℂ) + Matrix.single b a (1 : ℂ))
      from by simp [hermBasis, ne_of_lt h, h]]
    simp only [conjTranspose_smul, conjTranspose_add, conjTranspose_single, star_one, hs]
    rw [add_comm]
  · subst h
    simp [hermBasis]
  · rw [show hermBasis a b
        = (Complex.I * ((Real.sqrt 2 : ℂ)⁻¹)) •
            (Matrix.single a b (1 : ℂ) - Matrix.single b a (1 : ℂ))
      from by simp [hermBasis, ne_of_gt h, not_lt.mpr h.le]]
    have hc : star (Complex.I * ((Real.sqrt 2 : ℂ)⁻¹))
        = -(Complex.I * ((Real.sqrt 2 : ℂ)⁻¹)) := by
      rw [star_mul, hI, hs]; ring
    simp only [conjTranspose_smul, conjTranspose_sub, conjTranspose_single, star_one, hc]
    rw [show (Matrix.single a b (1 : ℂ) - Matrix.single b a (1 : ℂ))
        = -(Matrix.single b a (1 : ℂ) - Matrix.single a b (1 : ℂ)) from (neg_sub _ _).symm,
      smul_neg, neg_smul]

/-- Every element of the basis is a Hermitian matrix. -/
theorem hermBasis_isHermitian (a b : Fin N) : (hermBasis a b).IsHermitian :=
  hermBasis_conjTranspose a b

/-! ### Elementary products against a matrix `B` -/

/-- The diagonal basis element gives `E_aa * B * E_aa = single a a (B a a)`. -/
theorem hermBasis_mul_self_eq_single (B : Matrix (Fin N) (Fin N) ℂ) (a : Fin N) :
    hermBasis a a * B * hermBasis a a = Matrix.single a a (B a a) := by
  rw [show hermBasis a a = Matrix.single a a (1 : ℂ) from by simp [hermBasis]]
  rw [Matrix.single_mul_mul_single]
  simp

/-- For `a ≠ b`, the two basis elements attached to the unordered pair `{a, b}` contribute
altogether `single a a (B b b) + single b b (B a a)`.

This is the pair-level input of the completeness (Fierz) identity: with
`P = single a b 1`, `Q = single b a 1`, `s = (√2)⁻¹`, one has `F_ab = s • (P + Q)` and
`F_ba = (I s) • (Q - P)` when `a < b` (and the two roles are exchanged when `b < a`), and
`(P + Q) B (P + Q) - (Q - P) B (Q - P) = 2 • (P B Q + Q B P)`, so that the two
contributions add up to `P B Q + Q B P`. -/
theorem hermBasis_mul_mul_add (B : Matrix (Fin N) (Fin N) ℂ) {a b : Fin N} (h : a ≠ b) :
    hermBasis a b * B * hermBasis a b + hermBasis b a * B * hermBasis b a
      = Matrix.single a a (B b b) + Matrix.single b b (B a a) := by
  set s : ℂ := (Real.sqrt 2 : ℂ)⁻¹
  set P : Matrix (Fin N) (Fin N) ℂ := Matrix.single a b (1 : ℂ)
  set Q : Matrix (Fin N) (Fin N) ℂ := Matrix.single b a (1 : ℂ)
  have hs2 : s * s = (1 / 2 : ℂ) := by
    have h : ((Real.sqrt 2 : ℝ) : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ) = 2 := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
      norm_num
    rw [← mul_inv, h]
    norm_num
  have hI2 : (Complex.I * s) * (Complex.I * s) = -(1 / 2 : ℂ) := by
    rw [mul_mul_mul_comm, Complex.I_mul_I]
    simp only [neg_mul, one_mul, neg_inj]
    exact hs2
  have hPBQ : P * B * Q = Matrix.single a a (B b b) := by
    simp [P, Q, Matrix.single_mul_mul_single]
  have hQBP : Q * B * P = Matrix.single b b (B a a) := by
    simp [P, Q, Matrix.single_mul_mul_single]
  have key : (P + Q) * B * (P + Q) - (Q - P) * B * (Q - P)
      = (2 : ℂ) • (P * B * Q + Q * B * P) := by
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.sub_mul, Matrix.mul_sub, two_smul]
    abel
  have hstep : ∀ (c d : ℂ), c * c = (1 / 2 : ℂ) → d * d = -(1 / 2 : ℂ) →
      (c • (P + Q)) * B * (c • (P + Q)) + (d • (Q - P)) * B * (d • (Q - P))
        = P * B * Q + Q * B * P := by
    intro c d hc hd
    rw [show (c • (P + Q)) * B * (c • (P + Q)) + (d • (Q - P)) * B * (d • (Q - P))
        = (c * c) • ((P + Q) * B * (P + Q)) + (d * d) • ((Q - P) * B * (Q - P)) from by
      simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]]
    rw [hc, hd, neg_smul, ← sub_eq_add_neg, ← smul_sub, key]
    simp
  rcases lt_or_gt_of_ne h with hlt | hlt
  · have hlt' : ¬ b < a := not_lt.mpr hlt.le
    have h1 : hermBasis a b = s • (P + Q) := by simp [hermBasis, h, hlt, s, P, Q]
    have h2 : hermBasis b a = (Complex.I * s) • (Q - P) := by
      simp [hermBasis, Ne.symm h, hlt', s, P, Q]
    rw [h1, h2, hstep s (Complex.I * s) hs2 hI2]
    rw [hPBQ, hQBP]
  · have hlt' : ¬ a < b := not_lt.mpr hlt.le
    have h1 : hermBasis a b = (Complex.I * s) • (P - Q) := by simp [hermBasis, h, hlt', s, P, Q]
    have h2 : hermBasis b a = s • (P + Q) := by
      simp [hermBasis, Ne.symm h, hlt, s, P, Q, add_comm]
    have hI2' : (-(Complex.I * s)) * (-(Complex.I * s)) = -(1 / 2 : ℂ) := by
      rw [neg_mul_neg]
      exact hI2
    rw [h1, h2,
      show (Complex.I * s) • (P - Q) = (-(Complex.I * s)) • (Q - P) from by
        rw [show (P - Q) = -(Q - P) from (neg_sub _ _).symm, smul_neg, neg_smul],
      add_comm, hstep s (-(Complex.I * s)) hs2 hI2', hPBQ, hQBP]


end

end GUEStrongConvergence
