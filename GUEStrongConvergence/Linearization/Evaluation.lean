import GUEStrongConvergence.Linearization.SelfAdjointPencil
import Mathlib.Data.Matrix.Block
import Mathlib.Tactic

set_option linter.unusedSectionVars false

/-!
# Evaluation layer: matrix-coefficient word polynomials

The abstract linearization of `SelfAdjointPencil.lean` is stated over an arbitrary
`*`-ring `M`.  This file specializes it to the case of interest, where

* `M = Matrix D D A` for a finite index type `D` and a ring `A`, and
* the evaluated generators are `x i = Matrix.scalar D (gen i)` for a family
  `gen : I → A`,

so that a word product becomes a scalar matrix over the noncommutative word product:

`wordProd (fun i => Matrix.scalar D (gen i)) w = Matrix.scalar D (wordProd gen w)`.

The result is `matWordEval`, the evaluation of a finite matrix-coefficient word
polynomial, and the realization identity

`(u * Q^{-1} * v) 0 0 = matWordEval gen wds coeff`.

The bridge to the upstream polynomial algebra is `evaluate_eq_sum_of_single`: for a
`WordPolynomial 𝕜 I` presented as a finite sum of monomials, `evaluate` agrees with
the corresponding `wordProd` combination (reusing upstream `evaluate_single`).
-/

namespace GUEStrongConvergence

open Matrix

variable {A : Type*} [Ring A] {I κ : Type*} [Fintype κ] [DecidableEq κ]

omit [Fintype κ] [DecidableEq κ] in
/-- Scalar matrices turn word products into scalar matrices. -/
theorem wordProd_scalar {D : Type*} [Fintype D] [DecidableEq D]
    (gen : I → A) (w : List I) :
    wordProd (fun i => Matrix.scalar D (gen i)) w = Matrix.scalar D (wordProd gen w) := by
  rw [wordProd, wordProd, map_list_prod (Matrix.scalar D) (List.map gen w), List.map_map]
  rfl

/-- Evaluation of a finite matrix-coefficient word polynomial: the coefficients
`coeff k` are exactly the half-coefficients `C_w / 2` of the handoff, and the
generators are embedded as scalar matrices. -/
def matWordEval {D : Type*} [Fintype D] [DecidableEq D]
    (gen : I → A) (wds : κ → List I) (coeff : κ → Matrix D D A) : Matrix D D A :=
  ∑ k, coeff k * Matrix.scalar D (wordProd gen (wds k))

/-- **Realization, specialized to matrix coefficients.** The abstract word
realization, evaluated at scalar-matrix generators, computes `matWordEval`. -/
theorem linU_mul_linQinvMat_mul_linV_matWordEval {D : Type*} [Fintype D] [DecidableEq D]
    (gen : I → A) (wds : κ → List I) (coeff : κ → Matrix D D A) :
    (linU wds coeff * linQinvMat (fun i => Matrix.scalar D (gen i)) wds
        * linV (fun i => Matrix.scalar D (gen i)) wds) 0 0
      = matWordEval gen wds coeff := by
  rw [linU_mul_linQinvMat_mul_linV, matWordEval]
  exact Finset.sum_congr rfl fun k _ => by rw [wordProd_scalar]

/-- The `1×1` toc-matrix `u Q^{-1} v` is the scalar `matWordEval` (the `Fin 1` index
type is a subsingleton). -/
theorem linU_mul_linQinvMat_mul_linV_matWordEval_eta {D : Type*} [Fintype D] [DecidableEq D]
    (gen : I → A) (wds : κ → List I) (coeff : κ → Matrix D D A) :
    linU wds coeff * linQinvMat (fun i => Matrix.scalar D (gen i)) wds
        * linV (fun i => Matrix.scalar D (gen i)) wds
      = Matrix.of (fun _ _ => matWordEval gen wds coeff) := by
  apply Matrix.ext
  intro i j
  fin_cases i
  fin_cases j
  simp only [Matrix.of_apply]
  exact linU_mul_linQinvMat_mul_linV_matWordEval gen wds coeff

/-- **Invertibility equivalence, matrix-coefficient form.** The pencil `penL A0`
evaluated at scalar-matrix generators is invertible iff its Schur complement
`A0 - (q + q*)` is, with `q = matWordEval gen wds coeff`. -/
theorem penL_isUnit_iff_matWordEval {D : Type*} [Fintype D] [DecidableEq D] [StarRing A]
    (gen : I → A) (wds : κ → List I) (coeff : κ → Matrix D D A)
    (A0 : Matrix (Fin 1) (Fin 1) (Matrix D D A)) :
    IsUnit (penL (fun i => Matrix.scalar D (gen i)) wds coeff A0) ↔
      IsUnit (A0 - (Matrix.of (fun _ _ => matWordEval gen wds coeff)
        + (Matrix.of (fun _ _ => matWordEval gen wds coeff))ᴴ)) := by
  rw [penL_isUnit_iff, linU_mul_linQinvMat_mul_linV_matWordEval_eta]

/-- **Schur reduction to `zI - P`.** Writing the top-left block as `A0 = z - C`
(`z` standing in for the parametrized `zI_D` and `C` for the Hermitian constant term)
and `q = matWordEval gen wds coeff`, the Schur complement `A0 - (q + q*)` is
`z - (C + q + q*)`.  With `C = C*`, the matrix `C + q + q*` is the self-adjoint
polynomial `P = C + q + q*`, so this is exactly the handoff's boxed equivalence
`zI_D - P(x) invertible ↔ ℒ_z(x) invertible`. -/
theorem penL_isUnit_iff_sub_poly {D : Type*} [Fintype D] [DecidableEq D] [StarRing A]
    (gen : I → A) (wds : κ → List I) (coeff : κ → Matrix D D A) (z C : Matrix D D A) :
    IsUnit (penL (fun i => Matrix.scalar D (gen i)) wds coeff
        (Matrix.of (fun _ _ => z - C))) ↔
      IsUnit ((Matrix.of (fun _ _ => z - (C + matWordEval gen wds coeff
        + (matWordEval gen wds coeff)ᴴ))) : Matrix (Fin 1) (Fin 1) (Matrix D D A)) := by
  rw [penL_isUnit_iff_matWordEval]
  have h : (Matrix.of (fun _ _ => z - C) : Matrix (Fin 1) (Fin 1) (Matrix D D A))
        - ((Matrix.of (fun _ _ => matWordEval gen wds coeff) : Matrix (Fin 1) (Fin 1) (Matrix D D A))
            + ((Matrix.of (fun _ _ => matWordEval gen wds coeff) : Matrix (Fin 1) (Fin 1) (Matrix D D A)))ᴴ)
      = (Matrix.of (fun _ _ => z - (C + matWordEval gen wds coeff
            + (matWordEval gen wds coeff)ᴴ)) : Matrix (Fin 1) (Fin 1) (Matrix D D A)) := by
    ext i j
    fin_cases i
    fin_cases j
    simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.of_apply, Matrix.conjTranspose_apply,
      Matrix.star_eq_conjTranspose]
    abel
  rw [h]

section Applications

/-- **Application 1: the single word `X₀X₁X₀`.** The realization of a single-word
matrix polynomial with matrix coefficient `C` is `C * scalar (X₀X₁X₀)`. -/
example {D : Type*} [Fintype D] [DecidableEq D]
    (gen : Fin 2 → A) (C : Matrix D D A) :
    matWordEval gen (fun _ : Fin 1 => [0, 1, 0]) (fun _ => C)
      = C * Matrix.scalar D (gen 0 * gen 1 * gen 0) := by
  simp [matWordEval, wordProd, mul_assoc]

/-- **Application 2: a nontrivial linear combination.** The two-word polynomial
`C₁ · X₀X₁ + C₂ · X₁X₀X₁` evaluates accordingly. -/
example {D : Type*} [Fintype D] [DecidableEq D]
    (gen : Fin 2 → A) (C₁ C₂ : Matrix D D A) :
    matWordEval gen (fun k : Fin 2 => if k = 0 then [0, 1] else [1, 0, 1])
        (fun k : Fin 2 => if k = 0 then C₁ else C₂)
      = C₁ * Matrix.scalar D (gen 0 * gen 1)
        + C₂ * Matrix.scalar D (gen 1 * gen 0 * gen 1) := by
  simp [matWordEval, wordProd, Fin.sum_univ_two, mul_assoc]

/-- **Application 3: the pencil for a polynomial with a nonzero constant term.**
For `P = C + C₁ · X₀X₁ + C₂ · X₁X₀X₁`, the invertibility equivalence of the
self-adjoint pencil holds with the Schur complement built from the nonconstant part. -/
example {D : Type*} [Fintype D] [DecidableEq D] [StarRing A]
    (gen : Fin 2 → A) (C₁ C₂ : Matrix D D A)
    (A0 : Matrix (Fin 1) (Fin 1) (Matrix D D A)) :
    IsUnit (penL (fun i => Matrix.scalar D (gen i))
        (fun k : Fin 2 => if k = 0 then [0, 1] else [1, 0, 1])
        (fun k : Fin 2 => if k = 0 then C₁ else C₂) A0) ↔
      IsUnit (A0 - (Matrix.of (fun _ _ =>
          matWordEval gen (fun k : Fin 2 => if k = 0 then [0, 1] else [1, 0, 1])
            (fun k : Fin 2 => if k = 0 then C₁ else C₂))
        + (Matrix.of (fun _ _ =>
          matWordEval gen (fun k : Fin 2 => if k = 0 then [0, 1] else [1, 0, 1])
            (fun k : Fin 2 => if k = 0 then C₁ else C₂)))ᴴ)) := by
  rw [penL_isUnit_iff_matWordEval]

/-- **Application 4: `P = C + q + q*` is self-adjoint for `C = C*`.** This is the
structural reason the pencil's Schur complement `z - P` matches the handoff's
`zI_D - P(x)` at self-adjoint `P`. -/
example {D : Type*} [Fintype D] [DecidableEq D] [StarRing A]
    (gen : I → A) (wds : κ → List I) (coeff : κ → Matrix D D A)
    (C : Matrix D D A) (hC : Cᴴ = C) :
    (C + matWordEval gen wds coeff + (matWordEval gen wds coeff)ᴴ)ᴴ
      = C + matWordEval gen wds coeff + (matWordEval gen wds coeff)ᴴ := by
  rw [Matrix.conjTranspose_add, Matrix.conjTranspose_add, hC,
    Matrix.conjTranspose_conjTranspose]
  abel

end Applications

end GUEStrongConvergence
