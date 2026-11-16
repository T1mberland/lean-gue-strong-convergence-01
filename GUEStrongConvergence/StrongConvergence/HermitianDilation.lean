import Mathlib.Data.Matrix.Block
import Mathlib.Tactic

/-!
# The Hermitian dilation of a matrix polynomial

§3.4 of the linearization handoff reduces the non-self-adjoint case of the
strong-convergence reduction to the self-adjoint one by the *Hermitian dilation*

`H(P) = !![0, P; P^*, 0]`.

This file records the purely algebraic content of that reduction at the level of
an arbitrary `*`-ring `M`:

* `H(P)` is self-adjoint (`hermDilation_conjTranspose`),
* `H(P)^2 = !![P P^*, 0; 0, P^* P]` (`hermDilation_mul_self`),
* `H` is additive and negation-equivariant (`hermDilation_add`,
  `hermDilation_neg`),
* the abstract norm reduction `‖H(P)‖ = ‖P‖` from the C*-identity and the
  block-diagonal max norm (`hermDilation_norm_eq`).

The two genuinely analytic steps — the C*-identity for the concrete matrix norm
and the spectrum transfer `sp(H(P)) = ± sp(|P|)` — are recorded as named open
items in `docs/math-notes/selfadjoint-linearization.md`.
-/

namespace GUEStrongConvergence

open Matrix

variable {M : Type*} [Ring M] [StarRing M] {D : Type*}

/-- The Hermitian dilation `H(P) = !![0, P; P^*, 0]`. -/
def hermDilation (P : Matrix D D M) : Matrix (D ⊕ D) (D ⊕ D) M :=
  fromBlocks 0 P Pᴴ 0

/-- `H(P)` is self-adjoint. -/
theorem hermDilation_conjTranspose (P : Matrix D D M) :
    (hermDilation P)ᴴ = hermDilation P := by
  rw [hermDilation, fromBlocks_conjTranspose]
  simp only [conjTranspose_zero, conjTranspose_conjTranspose]

/-- `H(P)^2 = !![P P^*, 0; 0, P^* P]`. -/
theorem hermDilation_mul_self [Fintype D] (P : Matrix D D M) :
    hermDilation P * hermDilation P = fromBlocks (P * Pᴴ) 0 0 (Pᴴ * P) := by
  rw [hermDilation, fromBlocks_multiply]
  congr 1 <;> simp

/-- `H` is additive. -/
theorem hermDilation_add (P Q : Matrix D D M) :
    hermDilation (P + Q) = hermDilation P + hermDilation Q := by
  simp only [hermDilation, conjTranspose_add, fromBlocks_add, add_zero]

/-- `H` is negation-equivariant. -/
theorem hermDilation_neg (P : Matrix D D M) :
    hermDilation (-P) = -hermDilation P := by
  simp only [hermDilation, conjTranspose_neg, fromBlocks_neg, neg_zero]

/-- **Abstract norm reduction for the Hermitian dilation.**  If the ambient
`Norm` on the doubled block matrix satisfies the C*-identity for `H(P)`
(`hG`), the block-diagonal max-norm rule (`hdiag`) and the C*-identity
`‖P P^*‖ = ‖P‖^2 = ‖P^* P‖` (`hP`, `hP'`), then `‖H(P)‖ = ‖P‖`. -/
theorem hermDilation_norm_eq [Fintype D] [Norm (Matrix (D ⊕ D) (D ⊕ D) M)]
    [Norm (Matrix D D M)]
    (P : Matrix D D M)
    (hG : ‖hermDilation P‖ ^ 2 = ‖(hermDilation P)ᴴ * hermDilation P‖)
    (hdiag : ‖fromBlocks (P * Pᴴ) 0 0 (Pᴴ * P)‖ = max ‖P * Pᴴ‖ ‖Pᴴ * P‖)
    (hP : ‖P * Pᴴ‖ = ‖P‖ ^ 2) (hP' : ‖Pᴴ * P‖ = ‖P‖ ^ 2)
    (hGn : 0 ≤ ‖hermDilation P‖) (hPn : 0 ≤ ‖P‖) :
    ‖hermDilation P‖ = ‖P‖ := by
  have h2 : ‖hermDilation P‖ ^ 2 = ‖P‖ ^ 2 := by
    rw [hG, hermDilation_conjTranspose, hermDilation_mul_self, hdiag, hP, hP', max_self]
  exact (mul_self_inj_of_nonneg hGn hPn).mp (by simpa [sq] using h2)

/-- Concrete instance: for a `2 × 2` complex matrix `P`, the dilation is
self-adjoint and its square is block diagonal with blocks `P P^*`, `P^* P`. -/
example (P : Matrix (Fin 2) (Fin 2) ℂ) :
    (hermDilation P)ᴴ = hermDilation P ∧
      hermDilation P * hermDilation P = fromBlocks (P * Pᴴ) 0 0 (Pᴴ * P) :=
  ⟨hermDilation_conjTranspose P, hermDilation_mul_self P⟩

end GUEStrongConvergence
