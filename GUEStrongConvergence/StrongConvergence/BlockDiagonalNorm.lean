/-
# The block-diagonal norm rule for `CStarMatrix`

The operator norm on `CStarMatrix` is the C⋆-norm of the matrix algebra.  This file
proves that for the block-diagonal matrix `fromBlocks P 0 0 Q` it is the maximum of
the norms of the two diagonal blocks:

`‖fromBlocks P 0 0 Q‖ = max ‖P‖ ‖Q‖`.

The upper bound comes from the fact that the block-diagonal embedding
`(P, Q) ↦ fromBlocks P 0 0 Q` is a non-unital ⋆-algebra homomorphism from the product
C⋆-algebra `M_D(A) × M_D(A)` (whose norm is the maximum norm) into `M_{D ⊕ D}(A)`;
star algebra homomorphisms of C⋆-algebras are contractive.  The lower bound is proved
directly on vectors: testing on vectors supported in one of the two blocks shows that
the operator norm dominates `‖P‖` and `‖Q‖`.

As an application we prove the Hermitian-dilation norm identity
`‖!![0, P; P*, 0]‖ = ‖P‖` for `CStarMatrix` elements, which is the missing input for
the non-self-adjoint case of the strong-convergence transfer.

The second half of the file carries out that reduction at the polynomial level.  Since the
pinned libraries provide no `star` structure on `WordPolynomial`, we define the
reversal–conjugation star explicitly (`starWordPoly`), prove its compatibility with
evaluation at self-adjoint generators (`evaluate_starWordPoly`), build the dilated matrix
polynomial `dilationPoly` (`dilationPolyFin` after reindexing to `Fin (d + d)`), and prove
that its evaluation is the Hermitian dilation of the evaluation of `P`
(`eval_dilationPoly`) and has the same norm (`norm_eval_dilationPolyFin`).

The final theorem `ae_tendsto_norm_evalMatrixPoly_general` is the non-self-adjoint
counterpart of the canonical capstone: assuming scalar word-trace convergence, the
spectral family inclusion and the uniform bound for the *dilated* data, it concludes
`‖evalMatrixPoly P (gueFamily r N x)‖ → ‖evalMatrixPoly P (semicircularFamily r)‖`
almost surely.  No self-adjointness of `P` and no norm convergence is assumed.
-/
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.Analysis.CStarAlgebra.Module.Constructions
import Mathlib.Data.Matrix.Block
import Mathlib.Analysis.Normed.Group.Constructions
import GUEStrongConvergence.StrongConvergence.ConcreteTransfer

noncomputable section

namespace GUEStrongConvergence

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

open Filter MeasureTheory Matrix FreeProbability FreeProbability.Fock
open scoped ComplexOrder InnerProductSpace Topology WithCStarModule

variable {D : Type*} [Fintype D] [DecidableEq D]
variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- The raw block-diagonal matrix `!![P, 0; 0, Q]` at the `Matrix` level. -/
def blockMatrix (P Q : Matrix D D A) : Matrix (D ⊕ D) (D ⊕ D) A :=
  Matrix.fromBlocks P 0 0 Q

lemma blockMatrix_add (P Q R S : Matrix D D A) :
    blockMatrix (P + R) (Q + S) = blockMatrix P Q + blockMatrix R S := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [blockMatrix, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
      Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂]

lemma blockMatrix_mul (P Q R S : Matrix D D A) :
    blockMatrix (P * R) (Q * S) = blockMatrix P Q * blockMatrix R S := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [blockMatrix, Matrix.mul_apply, Fintype.sum_sum_type,
      Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
      Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂]

lemma blockMatrix_zero : blockMatrix (0 : Matrix D D A) 0 = 0 := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [blockMatrix, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
      Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂]

lemma blockMatrix_smul (c : ℂ) (P Q : Matrix D D A) :
    blockMatrix (c • P) (c • Q) = c • blockMatrix P Q := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [blockMatrix, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
      Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂]

lemma blockMatrix_star (P Q : Matrix D D A) :
    blockMatrix (star P) (star Q) = star (blockMatrix P Q) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [blockMatrix, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
      Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂]

/-- The block-diagonal embedding `(P, Q) ↦ !![P, 0; 0, Q]` as a non-unital ⋆-algebra
homomorphism from the product C⋆-algebra `M_D(A) × M_D(A)` to `M_{D ⊕ D}(A)`. -/
def blockDiagStarAlgHom :
    CStarMatrix D D A × CStarMatrix D D A →⋆ₙₐ[ℂ] CStarMatrix (D ⊕ D) (D ⊕ D) A where
  toFun p := CStarMatrix.ofMatrix (blockMatrix p.1 p.2)
  map_add' p q :=
    congrArg CStarMatrix.ofMatrix
      (blockMatrix_add (p.1 : Matrix D D A) (p.2 : Matrix D D A)
        (q.1 : Matrix D D A) (q.2 : Matrix D D A))
  map_mul' p q :=
    congrArg CStarMatrix.ofMatrix
      (blockMatrix_mul (p.1 : Matrix D D A) (p.2 : Matrix D D A)
        (q.1 : Matrix D D A) (q.2 : Matrix D D A))
  map_zero' := congrArg CStarMatrix.ofMatrix (blockMatrix_zero (D := D) (A := A))
  map_smul' c p :=
    congrArg CStarMatrix.ofMatrix
      (blockMatrix_smul c (p.1 : Matrix D D A) (p.2 : Matrix D D A))
  map_star' p :=
    congrArg CStarMatrix.ofMatrix
      (blockMatrix_star (p.1 : Matrix D D A) (p.2 : Matrix D D A))

/-- The block-diagonal embedding is injective. -/
theorem blockDiagStarAlgHom_injective :
    Function.Injective (blockDiagStarAlgHom (D := D) (A := A)) := by
  intro p q h
  obtain ⟨P, Q⟩ := p
  obtain ⟨R, S⟩ := q
  have h1 : P = R := by
    ext i j
    exact congrArg (fun M : CStarMatrix (D ⊕ D) (D ⊕ D) A =>
      M (Sum.inl i) (Sum.inl j)) h
  have h2 : Q = S := by
    ext i j
    exact congrArg (fun M : CStarMatrix (D ⊕ D) (D ⊕ D) A =>
      M (Sum.inr i) (Sum.inr j)) h
  simp [h1, h2]

/-- The plain function supported on the first block. -/
def blockInlFun (x : D → A) : (D ⊕ D) → A :=
  fun k => Sum.rec (fun j => x j) (fun _ => 0) k

/-- The plain function supported on the second block. -/
def blockInrFun (y : D → A) : (D ⊕ D) → A :=
  fun k => Sum.rec (fun _ => 0) (fun j => y j) k

/-- The vector supported on the first block. -/
def blockInl (x : D → A) : C⋆ᵐᵒᵈ(A, (D ⊕ D) → A) := blockInlFun x

/-- The vector supported on the second block. -/
def blockInr (y : D → A) : C⋆ᵐᵒᵈ(A, (D ⊕ D) → A) := blockInrFun y

/-- The norm of a vector supported on the first block is the norm of the block. -/
theorem norm_blockInl (x : D → A) :
    ‖blockInl (A := A) x‖ = ‖(WithCStarModule.equiv A (D → A)).symm x‖ := by
  rw [show blockInl (A := A) x
      = (WithCStarModule.equiv A ((D ⊕ D) → A)).symm (blockInlFun x) from rfl]
  rw [WithCStarModule.pi_norm (E := fun _ : D ⊕ D => A),
    WithCStarModule.pi_norm (E := fun _ : D => A)]
  congr 1
  rw [Fintype.sum_sum_type]
  simp [blockInlFun]

/-- The norm of a vector supported on the second block is the norm of the block. -/
theorem norm_blockInr (y : D → A) :
    ‖blockInr (A := A) y‖ = ‖(WithCStarModule.equiv A (D → A)).symm y‖ := by
  rw [show blockInr (A := A) y
      = (WithCStarModule.equiv A ((D ⊕ D) → A)).symm (blockInrFun y) from rfl]
  rw [WithCStarModule.pi_norm (E := fun _ : D ⊕ D => A),
    WithCStarModule.pi_norm (E := fun _ : D => A)]
  congr 1
  rw [Fintype.sum_sum_type]
  simp [blockInrFun]

/-- `vecMul` by a block-diagonal matrix on a vector supported on the first block. -/
theorem vecMul_blockMatrix_blockInl (P Q : Matrix D D A) (x : D → A) :
    (blockMatrix P Q).vecMul (blockInlFun x) = blockInlFun (P.vecMul x) := by
  funext k
  rcases k with k | k <;>
    simp [blockMatrix, blockInlFun, Matrix.vecMul_apply_eq_sum, Fintype.sum_sum_type]

/-- `vecMul` by a block-diagonal matrix on a vector supported on the second block. -/
theorem vecMul_blockMatrix_blockInr (P Q : Matrix D D A) (y : D → A) :
    (blockMatrix P Q).vecMul (blockInrFun y) = blockInrFun (Q.vecMul y) := by
  funext k
  rcases k with k | k <;>
    simp [blockMatrix, blockInrFun, Matrix.vecMul_apply_eq_sum, Fintype.sum_sum_type]

/-- Evaluation of the block-diagonal matrix on a vector supported on the first block. -/
theorem toCLM_fromBlocks_blockInl (P Q : CStarMatrix D D A)
    (x : C⋆ᵐᵒᵈ(A, D → A)) :
    CStarMatrix.toCLM (CStarMatrix.ofMatrix (Matrix.fromBlocks P 0 0 Q))
        (blockInl (A := A) (WithCStarModule.equiv A (D → A) x))
      = blockInl (A := A) (WithCStarModule.equiv A (D → A)
          (CStarMatrix.toCLM P x)) := by
  apply (WithCStarModule.equiv A ((D ⊕ D) → A)).injective
  exact vecMul_blockMatrix_blockInl (P : Matrix D D A) (Q : Matrix D D A) _

/-- Evaluation of the block-diagonal matrix on a vector supported on the second block. -/
theorem toCLM_fromBlocks_blockInr (P Q : CStarMatrix D D A)
    (y : C⋆ᵐᵒᵈ(A, D → A)) :
    CStarMatrix.toCLM (CStarMatrix.ofMatrix (Matrix.fromBlocks P 0 0 Q))
        (blockInr (A := A) (WithCStarModule.equiv A (D → A) y))
      = blockInr (A := A) (WithCStarModule.equiv A (D → A)
          (CStarMatrix.toCLM Q y)) := by
  apply (WithCStarModule.equiv A ((D ⊕ D) → A)).injective
  exact vecMul_blockMatrix_blockInr (P : Matrix D D A) (Q : Matrix D D A) _

/-- The block-diagonal matrix dominates the norm of its first diagonal block. -/
theorem norm_le_norm_fromBlocks_left (P Q : CStarMatrix D D A) :
    ‖P‖ ≤ ‖CStarMatrix.ofMatrix (Matrix.fromBlocks P 0 0 Q)‖ := by
  rw [CStarMatrix.norm_def]
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun x => ?_
  set v : C⋆ᵐᵒᵈ(A, (D ⊕ D) → A) :=
    blockInl (A := A) (WithCStarModule.equiv A (D → A) x) with hv
  have hMv := toCLM_fromBlocks_blockInl (A := A) P Q x
  have hnorm : ‖CStarMatrix.toCLM (CStarMatrix.ofMatrix (Matrix.fromBlocks P 0 0 Q)) v‖
      = ‖CStarMatrix.toCLM P x‖ := by
    rw [hMv]
    exact norm_blockInl (WithCStarModule.equiv A (D → A) (CStarMatrix.toCLM P x))
  have hvnorm : ‖v‖ = ‖x‖ := by
    rw [hv]
    exact norm_blockInl (WithCStarModule.equiv A (D → A) x)
  calc ‖CStarMatrix.toCLM P x‖
      = ‖CStarMatrix.toCLM (CStarMatrix.ofMatrix (Matrix.fromBlocks P 0 0 Q)) v‖ := hnorm.symm
    _ ≤ ‖CStarMatrix.toCLM (CStarMatrix.ofMatrix (Matrix.fromBlocks P 0 0 Q))‖ * ‖v‖ :=
        ContinuousLinearMap.le_opNorm _ _
    _ = ‖CStarMatrix.ofMatrix (Matrix.fromBlocks P 0 0 Q)‖ * ‖x‖ := by
        rw [hvnorm, CStarMatrix.norm_def]

/-- The block-diagonal matrix dominates the norm of its second diagonal block. -/
theorem norm_le_norm_fromBlocks_right (P Q : CStarMatrix D D A) :
    ‖Q‖ ≤ ‖CStarMatrix.ofMatrix (Matrix.fromBlocks P 0 0 Q)‖ := by
  rw [CStarMatrix.norm_def]
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun y => ?_
  set v : C⋆ᵐᵒᵈ(A, (D ⊕ D) → A) :=
    blockInr (A := A) (WithCStarModule.equiv A (D → A) y) with hv
  have hMv := toCLM_fromBlocks_blockInr (A := A) P Q y
  have hnorm : ‖CStarMatrix.toCLM (CStarMatrix.ofMatrix (Matrix.fromBlocks P 0 0 Q)) v‖
      = ‖CStarMatrix.toCLM Q y‖ := by
    rw [hMv]
    exact norm_blockInr (WithCStarModule.equiv A (D → A) (CStarMatrix.toCLM Q y))
  have hvnorm : ‖v‖ = ‖y‖ := by
    rw [hv]
    exact norm_blockInr (WithCStarModule.equiv A (D → A) y)
  calc ‖CStarMatrix.toCLM Q y‖
      = ‖CStarMatrix.toCLM (CStarMatrix.ofMatrix (Matrix.fromBlocks P 0 0 Q)) v‖ := hnorm.symm
    _ ≤ ‖CStarMatrix.toCLM (CStarMatrix.ofMatrix (Matrix.fromBlocks P 0 0 Q))‖ * ‖v‖ :=
        ContinuousLinearMap.le_opNorm _ _
    _ = ‖CStarMatrix.ofMatrix (Matrix.fromBlocks P 0 0 Q)‖ * ‖y‖ := by
        rw [hvnorm, CStarMatrix.norm_def]

/-- The block-diagonal matrix is dominated by the maximum of its diagonal blocks. -/
theorem norm_fromBlocks_le (P Q : CStarMatrix D D A) :
    ‖CStarMatrix.ofMatrix (Matrix.fromBlocks P 0 0 Q)‖ ≤ max ‖P‖ ‖Q‖ := by
  have h := NonUnitalStarAlgHom.norm_apply_le (φ := blockDiagStarAlgHom (D := D) (A := A))
    (P, Q)
  simpa [blockDiagStarAlgHom, blockMatrix, Prod.norm_def] using h

/-- **Block-diagonal norm rule.**  The C⋆-norm of `!![P, 0; 0, Q]` is the maximum of the
norms of `P` and `Q`. -/
theorem norm_fromBlocks_diag (P Q : CStarMatrix D D A) :
    ‖CStarMatrix.ofMatrix (Matrix.fromBlocks P 0 0 Q)‖ = max ‖P‖ ‖Q‖ := by
  refine le_antisymm (norm_fromBlocks_le P Q) ?_
  exact max_le (norm_le_norm_fromBlocks_left P Q) (norm_le_norm_fromBlocks_right P Q)

/-- The Hermitian dilation `!![0, P; P*, 0]` at the `Matrix` level. -/
def hermDilationMat (P : Matrix D D A) : Matrix (D ⊕ D) (D ⊕ D) A :=
  Matrix.fromBlocks 0 P (star P) 0

lemma hermDilationMat_star (P : Matrix D D A) :
    star (hermDilationMat P) = hermDilationMat P := by
  change (Matrix.fromBlocks 0 P (star P) 0)ᴴ = Matrix.fromBlocks 0 P (star P) 0
  rw [Matrix.fromBlocks_conjTranspose]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
      Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂]

lemma hermDilationMat_mul_self (P : Matrix D D A) :
    hermDilationMat P * hermDilationMat P = blockMatrix (P * star P) (star P * P) := by
  rw [hermDilationMat, blockMatrix, Matrix.fromBlocks_multiply]
  simp

/-- The Hermitian dilation `!![0, P; P*, 0]` of a `CStarMatrix`, whose norm equals the
norm of `P`. -/
def blockHermDilation (P : CStarMatrix D D A) : CStarMatrix (D ⊕ D) (D ⊕ D) A :=
  CStarMatrix.ofMatrix (hermDilationMat (P : Matrix D D A))

/-- **Hermitian-dilation norm identity** for the operator norm on `CStarMatrix`:
`‖!![0, P; P*, 0]‖ = ‖P‖`. -/
theorem norm_blockHermDilation_eq (P : CStarMatrix D D A) :
    ‖blockHermDilation P‖ = ‖P‖ := by
  have hsa : star (blockHermDilation P) = blockHermDilation P :=
    congrArg CStarMatrix.ofMatrix (hermDilationMat_star (P : Matrix D D A))
  have hmul : blockHermDilation P * blockHermDilation P
      = CStarMatrix.ofMatrix (blockMatrix ((P : Matrix D D A) * star P) (star P * P)) :=
    congrArg CStarMatrix.ofMatrix (hermDilationMat_mul_self (P : Matrix D D A))
  have hnsq : ‖blockHermDilation P‖ * ‖blockHermDilation P‖ = ‖P‖ * ‖P‖ := by
    rw [← CStarRing.norm_star_mul_self (x := blockHermDilation P), hsa, hmul,
      show ‖CStarMatrix.ofMatrix (blockMatrix ((P : Matrix D D A) * star P) (star P * P))‖
        = max ‖P * star P‖ ‖star P * P‖ from norm_fromBlocks_diag _ _,
      CStarRing.norm_self_mul_star, CStarRing.norm_star_mul_self, max_self]
  exact (mul_self_inj_of_nonneg (norm_nonneg _) (norm_nonneg _)).mp hnsq


/-! ## Hermitian dilation of a matrix-coefficient word polynomial -/

variable {I : Type*}

/-- The reversal–conjugation star on word polynomials: the coefficient of the reversed
word is conjugated. -/
def starWordPoly (p : WordPolynomial ℂ I) : WordPolynomial ℂ I :=
  p.coeff.sum fun w c =>
    MonoidAlgebra.single (FreeMonoid.ofList (FreeMonoid.toList w).reverse) (star c)

lemma starWordPoly_single (w : FreeMonoid I) (c : ℂ) :
    starWordPoly (MonoidAlgebra.single w c)
      = MonoidAlgebra.single (FreeMonoid.ofList (FreeMonoid.toList w).reverse) (star c) := by
  classical
  simp [starWordPoly]

lemma starWordPoly_eq_sum (p : WordPolynomial ℂ I) :
    starWordPoly p
      = ∑ w ∈ p.coeff.support,
          MonoidAlgebra.single (FreeMonoid.ofList (FreeMonoid.toList w).reverse)
            (star (p.coeff w)) := by
  rw [starWordPoly, Finsupp.sum]

/-- Reversal of a word product at a self-adjoint family of generators. -/
lemma star_wordProd {A : Type*} [Ring A] [StarRing A] {g : I → A}
    (hg : ∀ i, star (g i) = g i) (l : List I) :
    star (wordProd g l) = wordProd g l.reverse := by
  induction l with
  | nil => simp [wordProd]
  | cons a l ih =>
      have ih' : star ((List.map g l).prod) = (List.map g l.reverse).prod := by
        simpa [wordProd] using ih
      simp [wordProd, List.reverse_cons, List.map_append, ih', hg a]

/-- Evaluation of the reversal–conjugation star at a self-adjoint family. -/
lemma evaluate_starWordPoly {A : Type*} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]
    (g : I → A) (hg : ∀ i, star (g i) = g i) (p : WordPolynomial ℂ I) :
    evaluate g (starWordPoly p) = star (evaluate g p) := by
  classical
  rw [starWordPoly_eq_sum, map_sum]
  conv_rhs => rw [← MonoidAlgebra.sum_coeff_single p]
  rw [Finsupp.sum, map_sum, star_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  conv_lhs => rw [evaluate_single]
  conv_rhs =>
    rw [show MonoidAlgebra.single w (p.coeff w)
      = MonoidAlgebra.single (FreeMonoid.ofList (FreeMonoid.toList w)) (p.coeff w) from by
        rw [FreeMonoid.ofList_toList]]
    rw [evaluate_single, star_smul]
  rw [show star ((List.map g (FreeMonoid.toList w)).prod)
      = (List.map g (FreeMonoid.toList w).reverse).prod from by
    simpa [wordProd] using star_wordProd hg (FreeMonoid.toList w)]



section Dilation

variable {r d : ℕ}

/-- Entrywise evaluation of a matrix of word polynomials at an arbitrary finite index
type (a generalisation of `evalMatrixPoly`, which is stated for `Fin d`). -/
def evalMatrixPolyGen {D : Type*} {A : Type*} [Ring A] [Algebra ℂ A]
    (Q : Matrix D D (WordPolynomial ℂ I)) (g : I → A) : CStarMatrix D D A :=
  CStarMatrix.ofMatrix fun i j => evaluate g (Q i j)

/-- The block Hermitian dilation `!![0, P; P*, 0]` of a matrix-coefficient word polynomial.
The `(2,1)` block is the reversal–conjugation star of the transpose of `P`. -/
def dilationPoly (P : Matrix (Fin d) (Fin d) (WordPolynomial ℂ (Fin r))) :
    Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (WordPolynomial ℂ (Fin r)) :=
  Matrix.fromBlocks 0 P (fun i j => starWordPoly (P j i)) 0

/-- The dilation reindexed to `Fin (d + d)`, so that `evalMatrixPoly` applies to it. -/
def dilationPolyFin (P : Matrix (Fin d) (Fin d) (WordPolynomial ℂ (Fin r))) :
    Matrix (Fin (d + d)) (Fin (d + d)) (WordPolynomial ℂ (Fin r)) :=
  Matrix.reindex (finSumFinEquiv (m := d) (n := d))
    (finSumFinEquiv (m := d) (n := d)) (dilationPoly P)

/-- Evaluation of the dilated polynomial is the Hermitian dilation of the evaluation. -/
lemma eval_dilationPoly {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    (P : Matrix (Fin d) (Fin d) (WordPolynomial ℂ (Fin r)))
    (g : Fin r → A) (hg : ∀ i, star (g i) = g i) :
    evalMatrixPolyGen (dilationPoly P) g = blockHermDilation (evalMatrixPoly P g) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j
  · change evaluate g (0 : WordPolynomial ℂ (Fin r)) = (0 : A)
    simp
  · change evaluate g (P i j) = evaluate g (P i j)
    rfl
  · change evaluate g (starWordPoly (P j i)) = star (evaluate g (P j i))
    exact evaluate_starWordPoly g hg (P j i)
  · change (0 : A) = (0 : A)
    rfl

/-- `evalMatrixPoly` commutes with reindexing. -/
lemma evalMatrixPoly_reindex {D : Type*} [Fintype D] [DecidableEq D]
    (e : D ≃ Fin d) (Q : Matrix D D (WordPolynomial ℂ (Fin r)))
    {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    (g : Fin r → A) :
    evalMatrixPoly (Matrix.reindex e e Q) g
      = (CStarMatrix.reindexₐ ℂ A e) (evalMatrixPolyGen Q g) := by
  ext i j
  change evaluate g (Q (e.symm i) (e.symm j)) = evaluate g (Q (e.symm i) (e.symm j))
  rfl

/-- The norm of the evaluated dilation is the norm of the evaluation. -/
lemma norm_eval_dilationPolyFin {A : Type*} [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A]
    (P : Matrix (Fin d) (Fin d) (WordPolynomial ℂ (Fin r)))
    (g : Fin r → A) (hg : ∀ i, star (g i) = g i) :
    ‖evalMatrixPoly (dilationPolyFin P) g‖ = ‖evalMatrixPoly P g‖ := by
  calc ‖evalMatrixPoly (dilationPolyFin P) g‖
      = ‖(CStarMatrix.reindexₐ ℂ A (finSumFinEquiv (m := d) (n := d)))
          (blockHermDilation (evalMatrixPoly P g))‖ := by
        rw [dilationPolyFin, evalMatrixPoly_reindex, eval_dilationPoly P g hg]
    _ = ‖blockHermDilation (evalMatrixPoly P g)‖ := StarAlgEquiv.norm_map _ _
    _ = ‖evalMatrixPoly P g‖ := norm_blockHermDilation_eq _

/-- The Hermitian dilation is self-adjoint. -/
lemma isSelfAdjoint_blockHermDilation {D : Type*} [Fintype D] [DecidableEq D]
    {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    (X : CStarMatrix D D A) : IsSelfAdjoint (blockHermDilation X) := by
  unfold IsSelfAdjoint
  exact congrArg CStarMatrix.ofMatrix (hermDilationMat_star (X : Matrix D D A))

/-- The evaluated dilated polynomial is self-adjoint. -/
lemma isSelfAdjoint_eval_dilationPolyFin {A : Type*} [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A]
    (P : Matrix (Fin d) (Fin d) (WordPolynomial ℂ (Fin r)))
    (g : Fin r → A) (hg : ∀ i, star (g i) = g i) :
    IsSelfAdjoint (evalMatrixPoly (dilationPolyFin P) g) := by
  rw [dilationPolyFin, evalMatrixPoly_reindex, eval_dilationPoly P g hg]
  exact (isSelfAdjoint_blockHermDilation _).map
    (CStarMatrix.reindexₐ ℂ A (finSumFinEquiv (m := d) (n := d)))

/-- The GUE generators are self-adjoint. -/
lemma star_gueFamily (r N : ℕ) (x : CommonSpace (Fin r)) (i : Fin r) :
    star (gueFamily r N x i) = gueFamily r N x i := by
  change (gueMatrixOn x N i)ᴴ = gueMatrixOn x N i
  exact gueMatrixOn_isHermitian x N i

/-- The semicircular generators are self-adjoint. -/
lemma star_semicircularFamily (r : ℕ) (i : Fin r) :
    star (semicircularFamily r i) = semicircularFamily r i := by
  simpa [semicircularFamily] using (isSelfAdjoint_closedSemicircular i).star_eq

end Dilation


section Final

variable {r d : ℕ} [Nonempty (Fin d)] [Nonempty (Fin (d + d))]

local instance : Nontrivial (closedSemicircularAlgebra (Fin r)) :=
  (closedGeneratedVacuumState (Fin r)).toProbabilitySpace.nontrivial

local instance : PartialOrder (closedSemicircularAlgebra (Fin r)) :=
  CStarAlgebra.spectralOrder _

local instance : StarOrderedRing (closedSemicircularAlgebra (Fin r)) :=
  CStarAlgebra.spectralOrderedRing _

/-- **Almost-sure strong convergence for an arbitrary matrix polynomial.**

This is the non-self-adjoint counterpart of `ae_tendsto_norm_evalMatrixPoly_selfAdjoint`:
the self-adjoint case is applied to the Hermitian dilation `dilationPolyFin P`, and the
norms of the dilation and of `P` agree by `norm_eval_dilationPolyFin`.  The hypotheses are
the scalar word-trace convergence, the spectral family inclusion and the uniform bound for
the *dilated* data; no norm convergence and no self-adjointness of `P` is assumed. -/
theorem ae_tendsto_norm_evalMatrixPoly_general
    (P : Matrix (Fin d) (Fin d) (WordPolynomial ℂ (Fin r)))
    [DecidableEq (polyIdx (dilationPolyFin P))]
    {Rb : ℝ}
    (hWords : ∀ᵐ x ∂(commonGaussianMeasure (Fin r)),
      ∀ w : List (Fin r),
        Tendsto (fun N : ℕ => gueNormTrace (N := N) w (x N)) atTop (𝓝 (tau r w)))
    (hH1 : ∀ᵐ x ∂(commonGaussianMeasure (Fin r)),
      SpectralFamilyInclusion (B := fun n => BlockAlg (d + d) n)
        (Binf := BlockLimit r (d + d))
        (blockSemicircular r (d + d)) (blockGUE r (d + d) x)
        (polyW (dilationPolyFin P))
        (fun n k => (1 / 2 : ℂ) •
          polyCoeff (A := CStarMatrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
            (dilationPolyFin P) k)
        (fun k => (1 / 2 : ℂ) •
          polyCoeff (A := closedSemicircularAlgebra (Fin r)) (dilationPolyFin P) k)
        (fun _ => 0) 0)
    (hB : ∀ᵐ x ∂(commonGaussianMeasure (Fin r)),
      ∀ᶠ n in atTop,
        ‖wordPolyEvalC (0 : BlockAlg (d + d) n) (blockGUE r (d + d) x n)
          (polyW (dilationPolyFin P))
          (fun k => (1 / 2 : ℂ) •
            polyCoeff (A := CStarMatrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
              (dilationPolyFin P) k)‖ ≤ Rb) :
    ∀ᵐ x ∂(commonGaussianMeasure (Fin r)),
      Tendsto (fun N : ℕ => ‖evalMatrixPoly P (gueFamily r N x)‖) atTop
        (𝓝 ‖evalMatrixPoly P (semicircularFamily r)‖) := by
  have hPsa : ∀ (x : CommonSpace (Fin r)) (n : ℕ),
      IsSelfAdjoint (evalMatrixPoly (dilationPolyFin P) (gueFamily r (n + 1) x)) :=
    fun x n => isSelfAdjoint_eval_dilationPolyFin P _
      (fun i => star_gueFamily r (n + 1) x i)
  have hPsaInf : IsSelfAdjoint (evalMatrixPoly (dilationPolyFin P) (semicircularFamily r)) :=
    isSelfAdjoint_eval_dilationPolyFin P _ (fun i => star_semicircularFamily r i)
  have hcap := ae_tendsto_norm_evalMatrixPoly_selfAdjoint
    (r := r) (d := d + d) (P := dilationPolyFin P) hPsa hPsaInf hWords hH1 hB
  filter_upwards [hcap] with x hx
  have hfun : (fun N : ℕ =>
        ‖evalMatrixPoly (dilationPolyFin P) (gueFamily r N x)‖)
      = fun N : ℕ => ‖evalMatrixPoly P (gueFamily r N x)‖ := by
    funext N
    exact norm_eval_dilationPolyFin P _ (fun i => star_gueFamily r N x i)
  have hlim : ‖evalMatrixPoly (dilationPolyFin P) (semicircularFamily r)‖
      = ‖evalMatrixPoly P (semicircularFamily r)‖ :=
    norm_eval_dilationPolyFin P _ (fun i => star_semicircularFamily r i)
  rwa [hfun, hlim] at hx

end Final

end GUEStrongConvergence
