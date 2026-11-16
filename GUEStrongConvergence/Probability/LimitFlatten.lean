/-
# Limit-side flattening of the linearization pencils

`StrongConvergence/FlattenPencil.lean` flattens the *approximating* linearization pencils
`h1PencilApprox r k F x n z` to complex matrices and proves that the C⋆-graph real spectrum
is unchanged (`specC_flatten`).  This file performs the same construction on the **limit**
side: it flattens the limiting pencil

`h1PencilLimit r k F z ∈ h1Alim r k F
  = CStarMatrix (PenIdx wds) (PenIdx wds) (BlockLimit r d0)`

to a matrix over the closed semicircular algebra `A_r`, and identifies the result with the
canonical closed pencil `closedPencil (pencilConstCoeff k F z) (pencilDirCoeff k F)` of
`Probability/LimitBridge.lean`.  The Kronecker/affine coefficient identity of
`Probability/KroneckerPencil.lean` / `Probability/KroneckerIdentity.lean` is replayed in the
limit algebra: the constant term is the block-scalar matrix of `pencilConstBlock`, and the
shift block is the block sum of the semicircular generators with coefficients
`flatDirCoeff`.

## Contents

* `reindexStarAlgEquivA` — reindexing of matrices over an arbitrary `ℝ`-algebra, as a star
  algebra equivalence;
* `flattenPencilLimitStarAlgEquiv` — the limit-side flattening;
* `flattenPencilLimit_apply_entry` — its entry formula;
* `penL_zero_eq_blockScalarLimit` — the constant term of the limit pencil;
* `pencilDir_limit_entry` — the shift-block (direction) term;
* `flattenPencilLimit_h1PencilLimit` — the flattened limit pencil is the closed pencil;
* `specC_eq_spectrum_closedPencil` — **the spectral identification**
  `specC (h1PencilLimit r k F z) = spectrum ℝ (closedPencil (pencilConstCoeff k F z)
  (pencilDirCoeff k F))`.

No `sorry`, no new axioms.
-/
import GUEStrongConvergence.Probability.KroneckerIdentity
import GUEStrongConvergence.Probability.LimitBridge

open Matrix MeasureTheory ProbabilityTheory Filter FreeProbability FreeProbability.Fock
open scoped BigOperators ComplexOrder ENNReal Pointwise Topology

namespace GUEStrongConvergence

noncomputable section

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000

variable {r : ℕ}

local instance limFlatNontrivial : Nontrivial (closedSemicircularAlgebra (Fin r)) :=
  (closedGeneratedVacuumState (Fin r)).toProbabilitySpace.nontrivial

local instance limFlatPartialOrder : PartialOrder (closedSemicircularAlgebra (Fin r)) :=
  CStarAlgebra.spectralOrder _

local instance limFlatStarOrderedRing : StarOrderedRing (closedSemicircularAlgebra (Fin r)) :=
  CStarAlgebra.spectralOrderedRing _

/-! ## 1. Flattening the limit algebra -/

section Flatten

/-- `Matrix.reindex` as a star algebra equivalence over an arbitrary `ℝ`-algebra.  This is the
general-coefficient version of `reindexStarAlgEquiv` (`StrongConvergence/PencilSpectralInclusion.lean`),
which is stated for `ℂ`-matrices only. -/
def reindexStarAlgEquivA {A : Type*} [Semiring A] [StarRing A] [Algebra ℝ A]
    {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (e : m ≃ n) : Matrix m m A ≃⋆ₐ[ℝ] Matrix n n A :=
  StarAlgEquiv.ofAlgEquiv (Matrix.reindexAlgEquiv ℝ A e) (by
    intro M
    show Matrix.reindex e e (star M) = star (Matrix.reindex e e M)
    rw [Matrix.star_eq_conjTranspose, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_reindex])

@[simp] lemma reindexStarAlgEquivA_apply {A : Type*} [Semiring A] [StarRing A] [Algebra ℝ A]
    {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (e : m ≃ n) (M : Matrix m m A) :
    reindexStarAlgEquivA (A := A) e M = Matrix.reindex e e M := rfl

/-- Entry formula for `compStarAlgEquiv`. -/
@[simp] lemma compStarAlgEquiv_apply {I J R K : Type*} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] [CommSemiring K] [Semiring R] [StarRing R] [Algebra K R]
    (M : Matrix I I (Matrix J J R)) (p q : I × J) :
    compStarAlgEquiv I J R K M p q = M p.1 q.1 p.2 q.2 := by
  obtain ⟨i₁, i₂⟩ := p
  obtain ⟨j₁, j₂⟩ := q
  rfl

/-- The identity map `CStarMatrix n n A → Matrix n n A` as a star algebra equivalence over `ℝ`.
This is the general-coefficient version of `CStarMatrix.ofMatrixStarAlgEquiv.restrictScalars ℝ`,
stated with the `ℝ`-algebra structure on the matrix algebra directly (so that the scalar
restriction is definitional). -/
def cstarMatrixStarAlgEquivReal {A : Type*} [Semiring A] [StarRing A] [Algebra ℝ A]
    {n : Type*} [Fintype n] [DecidableEq n] :
    CStarMatrix n n A ≃⋆ₐ[ℝ] Matrix n n A :=
  StarAlgEquiv.ofAlgEquiv
    { toFun := id
      invFun := id
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl
      map_add' := fun _ _ => rfl
      commutes' := fun r => by
        ext i j
        change (algebraMap ℝ (CStarMatrix n n A) r) i j =
          (algebraMap ℝ (Matrix n n A) r) i j
        rw [CStarMatrix.algebraMap_apply, Matrix.algebraMap_eq_diagonal]
        by_cases h : i = j <;> simp [h] }
    (fun _ => rfl)

@[simp] lemma cstarMatrixStarAlgEquivReal_apply {A : Type*} [Semiring A] [StarRing A]
    [Algebra ℝ A] {n : Type*} [Fintype n] [DecidableEq n] (M : CStarMatrix n n A) :
    cstarMatrixStarAlgEquivReal M = M := rfl

/-- **The limit-side flattening.**  Peeling the outer `CStarMatrix` layer, the `d0 × d0`
block structure (`compStarAlgEquiv`), and the coefficient reindexing `pencilCoeffIdx`, we
obtain a star algebra equivalence from the limiting pencil algebra to
`Matrix (Fin (pencilCoeffDim k F)) (Fin (pencilCoeffDim k F)) A_r`. -/
def flattenPencilLimitStarAlgEquiv (r k : ℕ) (F : RatPolyIdx r (k + 1)) :
    h1Alim r k F ≃⋆ₐ[ℝ]
      Matrix (Fin (pencilCoeffDim k F)) (Fin (pencilCoeffDim k F))
        (closedSemicircularAlgebra (Fin r)) :=
  let e₁ := cstarMatrixStarAlgEquivReal (A := BlockLimit r ((k + 1) + (k + 1)))
    (n := PenIdx (polyW (h1Poly r k F)))
  let e₂ : Matrix (PenIdx (polyW (h1Poly r k F))) (PenIdx (polyW (h1Poly r k F)))
      (BlockLimit r ((k + 1) + (k + 1))) ≃⋆ₐ[ℝ]
      Matrix (PenIdx (polyW (h1Poly r k F)) × Fin ((k + 1) + (k + 1)))
        (PenIdx (polyW (h1Poly r k F)) × Fin ((k + 1) + (k + 1)))
        (closedSemicircularAlgebra (Fin r)) :=
    compStarAlgEquiv (PenIdx (polyW (h1Poly r k F))) (Fin ((k + 1) + (k + 1)))
      (closedSemicircularAlgebra (Fin r)) ℝ
  let e₃ : Matrix (PenIdx (polyW (h1Poly r k F)) × Fin ((k + 1) + (k + 1)))
        (PenIdx (polyW (h1Poly r k F)) × Fin ((k + 1) + (k + 1)))
        (closedSemicircularAlgebra (Fin r)) ≃⋆ₐ[ℝ]
      Matrix (Fin (pencilCoeffDim k F)) (Fin (pencilCoeffDim k F))
        (closedSemicircularAlgebra (Fin r)) :=
    reindexStarAlgEquivA (pencilCoeffIdx k F).symm
  (e₁.trans e₂).trans e₃

/-- **The entry formula of the limit flattening**: the flattened matrix entry is the
`(u,v)`-entry of the `(i,j)`-block of the original `C⋆`-matrix. -/
lemma flattenPencilLimit_apply (r k : ℕ) (F : RatPolyIdx r (k + 1))
    (A : h1Alim r k F) (x y : Fin (pencilCoeffDim k F)) :
    flattenPencilLimitStarAlgEquiv r k F A x y
      = (A (pencilCoeffIdx k F x).1 (pencilCoeffIdx k F y).1)
          (pencilCoeffIdx k F x).2 (pencilCoeffIdx k F y).2 := by
  simp only [flattenPencilLimitStarAlgEquiv, StarAlgEquiv.trans_apply,
    reindexStarAlgEquivA_apply, Matrix.reindex_apply, Matrix.submatrix_apply,
    Equiv.symm_symm, cstarMatrixStarAlgEquivReal_apply]
  exact compStarAlgEquiv_apply _ _ _

/-- The entry formula at the block indices. -/
lemma flattenPencilLimit_apply_entry (r k : ℕ) (F : RatPolyIdx r (k + 1))
    (A : h1Alim r k F)
    (i j : PenIdx (polyW (h1Poly r k F))) (u v : Fin ((k + 1) + (k + 1))) :
    flattenPencilLimitStarAlgEquiv r k F A
        ((pencilCoeffIdx k F).symm (i, u)) ((pencilCoeffIdx k F).symm (j, v))
      = (A i j) u v := by
  rw [flattenPencilLimit_apply]
  simp only [Equiv.apply_symm_apply]

end Flatten

/-! ## 2. `specC` invariance under the limit flattening -/

section Spec

/-- **`specC` invariance under the limit flattening.** -/
theorem specC_flatten_limit (r k : ℕ) (F : RatPolyIdx r (k + 1)) (z : ℝ) :
    specC (h1PencilLimit r k F z) =
      spectrum ℝ (flattenPencilLimitStarAlgEquiv r k F (h1PencilLimit r k F z)) := by
  rw [specC]
  exact (AlgEquiv.spectrum_eq (flattenPencilLimitStarAlgEquiv r k F)
    (h1PencilLimit r k F z)).symm

end Spec

/-! ## 3. Entry computations in the limit algebra

We now replay the Kronecker coefficient computation of `Probability/KroneckerPencil.lean` in
the limit algebra.  The limit pencil is `penL` evaluated at the block-semicircular tuple

`blockSemicircular r d0 : Fin r → BlockLimit r d0`,

with coefficients `(1/2) • polyCoeff (h1Poly r k F) : polyIdx → BlockLimit r d0`.
The constant term (`penL 0`) is the block-scalar matrix of `pencilConstBlock`, and the
generator-dependent part is supported on the shift blocks with coefficients `flatDirCoeff`
and entries the semicircular generators. -/

section EntryComputations

variable (r k : ℕ) (F : RatPolyIdx r (k + 1)) (z : ℝ)

/-- The `d0 = (k+1)+(k+1)` coefficient dimension. -/
abbrev d0 (k : ℕ) : ℕ := (k + 1) + (k + 1)

/-- The limit coefficients `(1/2) • polyCoeff`, entrywise: they are the algebra-map images of
the scalar coefficients `polyCoeffScalar`. -/
lemma coeffLimit_apply (j : polyIdx (h1Poly r k F)) (u v : Fin (d0 k)) :
    ((1 / 2 : ℂ) • polyCoeff (A := closedSemicircularAlgebra (Fin r))
        (h1Poly r k F) j) u v
      = algebraMap ℂ (closedSemicircularAlgebra (Fin r))
          (polyCoeffScalar k F j u v) := by
  rw [Matrix.smul_apply, polyCoeff, Matrix.of_apply, polyCoeffScalar, Algebra.smul_def,
    map_mul]

/-- Entry formula for the block-semicircular generators. -/
@[simp] lemma blockSemicircular_apply (i : Fin r) (u v : Fin (d0 k)) :
    blockSemicircular r (d0 k) i u v
      = if u = v then semicircularFamily r i else 0 := rfl

/-- **Entry formula for the closed pencil.** -/
lemma closedPencil_apply {n : Type*} [Fintype n] [DecidableEq n]
    (C₀ : Matrix n n ℂ) (C : Fin r → Matrix n n ℂ) (a b : n) :
    closedPencil C₀ C a b =
      algebraMap ℂ (closedSemicircularAlgebra (Fin r)) (C₀ a b) +
        ∑ i, C i a b • semicircularFamily r i := by
  apply Subtype.ext
  simp only [closedPencil, CStarMatrix.ofMatrix_apply, Subtype.coe_mk,
    scalarMatrixEmbedding_apply, matrixLinearCombination, semicircularFamily]
  rw [Subalgebra.coe_add,
    show ((algebraMap ℂ (closedSemicircularAlgebra (Fin r)) (C₀ a b) :
        closedSemicircularAlgebra (Fin r)) : WordSpace (Fin r) →L[ℂ] WordSpace (Fin r)) =
      (algebraMap ℂ (WordSpace (Fin r) →L[ℂ] WordSpace (Fin r))) (C₀ a b) from rfl]
  congr 1
  change ∑ i, C i a b • semicircular i =
    (StarSubalgebra.subtype (closedSemicircularAlgebra (Fin r)))
      (∑ x, C x a b • closedSemicircular x)
  rw [map_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rfl

/-- **Entry formula for the limit pencil itself.** -/
lemma h1PencilLimit_apply_entry (p q : PenIdx (polyW (h1Poly r k F)))
    (u v : Fin (d0 k)) :
    (h1PencilLimit r k F z) p q u v
      = penL (blockSemicircular r (d0 k)) (polyW (h1Poly r k F))
          (fun j => (1 / 2 : ℂ) • polyCoeff (A := closedSemicircularAlgebra (Fin r))
            (h1Poly r k F) j)
          (penA0 (0 : BlockLimit r (d0 k)) z) p q u v := rfl

end EntryComputations

/-! ## 4. The constant term of the limit pencil -/

section ConstTerm

variable (r k : ℕ) (F : RatPolyIdx r (k + 1)) (z : ℝ)

/-- The coefficient family of the limit pencil. -/
def limitCoeff : polyIdx (h1Poly r k F) → BlockLimit r (d0 k) :=
  fun j => (1 / 2 : ℂ) • polyCoeff (A := closedSemicircularAlgebra (Fin r))
    (h1Poly r k F) j

/-- Entrywise form of the limit coefficients. -/
lemma limitCoeff_apply (j : polyIdx (h1Poly r k F)) (u v : Fin (d0 k)) :
    limitCoeff r k F j u v
      = algebraMap ℂ (closedSemicircularAlgebra (Fin r)) (polyCoeffScalar k F j u v) :=
  coeffLimit_apply r k F j u v

/-- Entrywise form of the limit coefficients, as a scalar multiple of the identity. -/
lemma limitCoeff_apply_smul (j : polyIdx (h1Poly r k F)) (u v : Fin (d0 k)) :
    limitCoeff r k F j u v
      = polyCoeffScalar k F j u v • (1 : closedSemicircularAlgebra (Fin r)) := by
  rw [limitCoeff_apply, polyCoeffScalar, Algebra.algebraMap_eq_smul_one]

@[simp] lemma smul_zero_gen {B : Type*} [Semiring B] [Algebra ℂ B] (c : ℂ) :
    c • (0 : B) = 0 := by
  rw [Algebra.smul_def, mul_zero]

@[simp] lemma zero_smul_one_gen {B : Type*} [Semiring B] [Algebra ℂ B] :
    (0 : ℂ) • (1 : B) = 0 := by
  rw [Algebra.smul_def, map_zero, zero_mul]

@[simp] lemma neg_one_smul_one_gen {B : Type*} [Ring B] [Algebra ℂ B] :
    (-1 : ℂ) • (1 : B) = -(1 : B) := by
  rw [Algebra.smul_def, map_neg, map_one]
  simp

lemma star_half_mul_A (w : ℂ) :
    star ((1 / 2 : ℂ) * w) = (1 / 2 : ℂ) * star w := by
  rw [star_mul, show star ((1 / 2 : ℂ)) = (1 / 2 : ℂ) by norm_num]
  ring

/-- The `A`-valued matrix of constant coefficients. -/
def pencilConstBlockA (p q : PenIdx (polyW (h1Poly r k F))) :
    Matrix (Fin (d0 k)) (Fin (d0 k)) (closedSemicircularAlgebra (Fin r)) :=
  fun u v => pencilConstBlock k F z p q u v • (1 : closedSemicircularAlgebra (Fin r))

/-- **The constant term of the limit pencil is the block-scalar matrix of
`pencilConstBlock`.** -/
theorem penL_zero_eq_blockScalarLimit :
    penL (0 : Fin r → BlockLimit r (d0 k)) (polyW (h1Poly r k F)) (limitCoeff r k F)
      (penA0 (0 : BlockLimit r (d0 k)) z)
    = Matrix.of fun (p q : PenIdx (polyW (h1Poly r k F))) =>
        (pencilConstBlockA r k F z p q : BlockLimit r (d0 k)) := by
  classical
  refine Matrix.ext fun p q => ?_
  refine Matrix.ext fun u v => ?_
  rcases p with a0 | (a1 | a2) <;> rcases q with b0 | (b1 | b2)
  · -- (inl, inl)
    simp only [penL, fromBlocks_apply₁₁, penA0, Matrix.of_apply, sub_zero,
      CStarMatrix.smul_apply, Matrix.smul_apply, CStarMatrix.one_apply, Matrix.one_apply, pencilConstBlockA, pencilConstBlock,
      pencilConstValue]
    by_cases h : u = v
    · rw [if_pos h, if_pos h]
    · rw [if_neg h, if_neg h, smul_zero_gen, zero_smul_one_gen]
  · -- (inl, inr (inl b))
    by_cases hb : (b1.2 : ℕ) = 0
    · simp only [penL, fromBlocks_apply₁₂, penE, Matrix.of_apply, linU, dif_pos hb,
        CStarMatrix.neg_apply, Matrix.neg_apply, pencilConstBlockA, pencilConstBlock, pencilConstValue, if_pos hb]
      rw [limitCoeff_apply_smul]
      rw [show (-(1 / 2 : ℂ)) * polyC (h1Poly r k F) b1.1 u v
            = -((1 / 2 : ℂ) * polyC (h1Poly r k F) b1.1 u v) by ring, neg_smul]
      simp only [polyCoeffScalar]
    · simp only [penL, fromBlocks_apply₁₂, penE, Matrix.of_apply, linU, dif_neg hb,
        CStarMatrix.neg_apply, Matrix.neg_apply, pencilConstBlockA, pencilConstBlock, pencilConstValue, if_neg hb]
      simp
  · -- (inl, inr (inr b))
    by_cases hb : (b2.2 : ℕ) = (polyW (h1Poly r k F) b2.1).length
    · simp only [penL, fromBlocks_apply₁₂, penE, Matrix.of_apply, linV, dif_pos hb,
        CStarMatrix.neg_apply, Matrix.neg_apply, Matrix.conjTranspose_apply, CStarMatrix.star_apply, Matrix.star_apply, CStarMatrix.one_apply, Matrix.one_apply, star_one,
        pencilConstBlockA, pencilConstBlock, pencilConstValue, if_pos hb]
      by_cases h : u = v
      · rw [if_pos h, if_pos h]
        simp
      · rw [if_neg h, if_neg h]
        simp
    · simp only [penL, fromBlocks_apply₁₂, penE, Matrix.of_apply, linV, dif_neg hb,
        CStarMatrix.neg_apply, Matrix.neg_apply, Matrix.conjTranspose_apply, CStarMatrix.star_apply, Matrix.star_apply, CStarMatrix.one_apply, Matrix.one_apply, star_one,
        pencilConstBlockA, pencilConstBlock, pencilConstValue, if_neg hb]
      simp
  · -- (inr (inl a), inl)
    by_cases ha : (a1.2 : ℕ) = 0
    · simp only [penL, fromBlocks_apply₂₁, penEconj, Matrix.of_apply, linU, dif_pos ha,
        CStarMatrix.neg_apply, Matrix.neg_apply, Matrix.conjTranspose_apply, CStarMatrix.star_apply, Matrix.star_apply, CStarMatrix.one_apply, Matrix.one_apply,
        pencilConstBlockA, pencilConstBlock, pencilConstValue, if_pos ha]
      rw [limitCoeff_apply_smul, star_smul, star_one]
      rw [show (-(1 / 2 : ℂ)) * star (polyC (h1Poly r k F) a1.1 v u)
            = -((1 / 2 : ℂ) * star (polyC (h1Poly r k F) a1.1 v u)) by ring, neg_smul]
      simp only [polyCoeffScalar, star_half_mul_A]
    · simp only [penL, fromBlocks_apply₂₁, penEconj, Matrix.of_apply, linU, dif_neg ha,
        CStarMatrix.neg_apply, Matrix.neg_apply, Matrix.conjTranspose_apply, CStarMatrix.star_apply, Matrix.star_apply, CStarMatrix.one_apply, Matrix.one_apply,
        pencilConstBlockA, pencilConstBlock, pencilConstValue, if_neg ha, star_zero]
      simp
  · -- (inr (inl a), inr (inl b))
    simp only [penL, fromBlocks_apply₂₂, penB, fromBlocks_apply₁₁, Matrix.of_apply,
      pencilConstBlockA, pencilConstBlock, pencilConstValue]
    simp
  · -- (inr (inl a), inr (inr b))
    by_cases hab : a1 = b2
    · subst hab
      simp only [penL, fromBlocks_apply₂₂, penB, fromBlocks_apply₁₂, linQMat_zero,
        Matrix.of_apply, CStarMatrix.one_apply, Matrix.one_apply, Matrix.conjTranspose_one,
        ↓reduceIte, pencilConstBlockA, pencilConstBlock, pencilConstValue]
      by_cases h : u = v
      · simp [h, Algebra.algebraMap_eq_smul_one]
      · simp [h]
    · simp only [penL, fromBlocks_apply₂₂, penB, fromBlocks_apply₁₂, linQMat_zero,
        Matrix.of_apply, CStarMatrix.one_apply, Matrix.one_apply, Matrix.conjTranspose_one,
        ↓reduceIte, pencilConstBlockA, pencilConstBlock, pencilConstValue]
      by_cases h : u = v <;> simp [hab, h]
  · -- (inr (inr a), inl)
    by_cases ha : (a2.2 : ℕ) = (polyW (h1Poly r k F) a2.1).length
    · simp only [penL, fromBlocks_apply₂₁, penEconj, Matrix.of_apply, linV, dif_pos ha,
        CStarMatrix.neg_apply, Matrix.neg_apply, CStarMatrix.one_apply, Matrix.one_apply,
        pencilConstBlockA, pencilConstBlock, pencilConstValue, if_pos ha]
      by_cases h : u = v
      · simp [h]
      · simp [h]
    · simp only [penL, fromBlocks_apply₂₁, penEconj, Matrix.of_apply, linV, dif_neg ha,
        CStarMatrix.neg_apply, Matrix.neg_apply, CStarMatrix.one_apply, Matrix.one_apply,
        pencilConstBlockA, pencilConstBlock, pencilConstValue, if_neg ha]
      simp
  · -- (inr (inr a), inr (inl b))
    by_cases hab : a2 = b1
    · subst hab
      simp only [penL, fromBlocks_apply₂₂, penB, fromBlocks_apply₂₁, linQMat_zero,
        Matrix.of_apply, CStarMatrix.one_apply, Matrix.one_apply, ↓reduceIte,
        pencilConstBlockA, pencilConstBlock, pencilConstValue]
      by_cases h : u = v
      · simp [h, Algebra.algebraMap_eq_smul_one]
      · simp [h]
    · simp only [penL, fromBlocks_apply₂₂, penB, fromBlocks_apply₂₁, linQMat_zero,
        Matrix.of_apply, CStarMatrix.one_apply, Matrix.one_apply, ↓reduceIte,
        pencilConstBlockA, pencilConstBlock, pencilConstValue]
      by_cases h : u = v <;> simp [hab, h]
  · -- (inr (inr a), inr (inr b))
    simp only [penL, fromBlocks_apply₂₂, penB, fromBlocks_apply₂₂, Matrix.of_apply,
      pencilConstBlockA, pencilConstBlock, pencilConstValue]
    simp

end ConstTerm

/-- Entrywise form of the constant term. -/
lemma penL_zero_entry (r k : ℕ) (F : RatPolyIdx r (k + 1)) (z : ℝ)
    (p q : PenIdx (polyW (h1Poly r k F))) (u v : Fin (d0 k)) :
    ((penL (0 : Fin r → BlockLimit r (d0 k)) (polyW (h1Poly r k F)) (limitCoeff r k F)
        (penA0 (0 : BlockLimit r (d0 k)) z)) p q) u v
      = pencilConstBlockA r k F z p q u v := by
  rw [penL_zero_eq_blockScalarLimit]
  simp only [Matrix.of_apply]

/-! ## 5. The shift block of the limit pencil -/

@[simp] lemma zero_smul_gen {B : Type*} [Semiring B] [Algebra ℂ B] (x : B) :
    (0 : ℂ) • x = 0 := by
  rw [Algebra.smul_def, map_zero, zero_mul]

@[simp] lemma neg_one_smul_gen {B : Type*} [Ring B] [Algebra ℂ B] (x : B) :
    (-1 : ℂ) • x = -x := by
  rw [Algebra.smul_def, map_neg, map_one, neg_mul, one_mul]

section DirTerm

variable (r k : ℕ) (F : RatPolyIdx r (k + 1)) (z : ℝ)

/-- The semicircular generators are self-adjoint. -/
lemma star_semicircularFamily_eq (i : Fin r) :
    star (semicircularFamily r i) = semicircularFamily r i := by
  show star (closedSemicircular i) = closedSemicircular i
  exact (isSelfAdjoint_closedSemicircular i).star_eq

/-- Entry formula for the shift matrix of the block-semicircular tuple. -/
lemma shiftMatrix_blockSemicircular_entry (w : List (Fin r))
    (i j : Fin (w.length + 1)) (u v : Fin (d0 k)) :
    (shiftMatrix (blockSemicircular r (d0 k)) w) i j u v
      = if h : (i : ℕ) + 1 = (j : ℕ) then
          (if u = v then semicircularFamily r (w.get ⟨i.1, by omega⟩) else 0)
        else 0 := by
  rw [shiftMatrix_apply]
  by_cases h : (i : ℕ) + 1 = (j : ℕ)
  · simp [h, blockSemicircular_apply]
  · simp [h]

/-- **The generator-dependent part of the limit pencil is the shift block with coefficients
`flatDirCoeff`.** -/
theorem pencilDir_limit_entry (p q : PenIdx (polyW (h1Poly r k F)))
    (u v : Fin (d0 k)) :
    (penL (blockSemicircular r (d0 k)) (polyW (h1Poly r k F)) (limitCoeff r k F)
        (penA0 (0 : BlockLimit r (d0 k)) z)
      - penL (0 : Fin r → BlockLimit r (d0 k)) (polyW (h1Poly r k F)) (limitCoeff r k F)
        (penA0 (0 : BlockLimit r (d0 k)) z)) p q u v
      = ∑ i : Fin r, flatDirCoeff k F i (p, u) (q, v) • semicircularFamily r i := by
  classical
  rw [penL_sub_penL_zero]
  rcases p with a0 | (a1 | a2) <;> rcases q with b0 | (b1 | b2)
  · -- (inl, inl)
    simp [flatDirCoeff_zero_l]
  · -- (inl, inr (inl b))
    simp [flatDirCoeff_zero_l]
  · -- (inl, inr (inr b))
    simp [flatDirCoeff_zero_l]
  · -- (inr (inl a), inl)
    simp [flatDirCoeff_zero_r]
  · -- (inr (inl a), inr (inl b))
    rw [fromBlocks_apply₂₂, penB_sub_penB_zero, fromBlocks_apply₁₁]
    simp [flatDirCoeff_inr_inl_inl]
  · -- (inr (inl a), inr (inr b))
    obtain ⟨kk1, r1⟩ := a1
    obtain ⟨kk2, r2⟩ := b2
    rw [fromBlocks_apply₂₂, penB_sub_penB_zero, fromBlocks_apply₁₂]
    simp only [flatDirCoeff_inr_inl_inr]
    rw [← Matrix.conjTranspose_sub, Matrix.conjTranspose_apply]
    by_cases hkk : kk1 = kk2
    · subst hkk
      rw [linQMat_sub_apply_eq, CStarMatrix.star_apply, CStarMatrix.neg_apply,
        shiftMatrix_blockSemicircular_entry]
      by_cases h : (r2 : ℕ) + 1 = (r1 : ℕ)
      · rw [dif_pos h]
        have hp : (r2 : ℕ) < (polyW (h1Poly r k F) kk1).length := by
          have := r1.isLt; omega
        rw [show (polyW (h1Poly r k F) kk1).get ⟨r2, by omega⟩
            = (polyW (h1Poly r k F) kk1).get ⟨r2, hp⟩ from by simp]
        have hsum : (∑ i : Fin r,
              (if u = v then flatDirCoeffBlock k F i ⟨kk1, r2⟩ ⟨kk1, r1⟩ else 0)
                • semicircularFamily r i)
            = if u = v then (-1 : ℂ) •
                semicircularFamily r ((polyW (h1Poly r k F) kk1).get ⟨r2, hp⟩) else 0 := by
          by_cases h2 : u = v
          · simp only [if_pos h2]
            rw [Finset.sum_eq_single ((polyW (h1Poly r k F) kk1).get ⟨r2, hp⟩)]
            · rw [flatDirCoeffBlock, dif_pos ⟨rfl, h⟩, if_pos rfl, neg_one_smul_gen]
            · intro i _ hi
              rw [flatDirCoeffBlock, dif_pos ⟨rfl, h⟩,
                if_neg (fun hh => hi hh.symm), zero_smul_gen]
            · intro hi; exact absurd (Finset.mem_univ _) hi
          · simp [h2]
        rw [hsum]
        by_cases h2 : u = v
        · rw [if_pos h2.symm, if_pos h2, star_neg, star_semicircularFamily_eq,
            neg_one_smul_gen]
        · rw [if_neg (fun hh => h2 hh.symm), if_neg h2]
          simp
      · rw [dif_neg h]
        have hsum : (∑ i : Fin r,
              (if u = v then flatDirCoeffBlock k F i ⟨kk1, r2⟩ ⟨kk1, r1⟩ else 0)
                • semicircularFamily r i) = 0 := by
          rw [Finset.sum_eq_zero]
          intro i _
          by_cases h2 : u = v <;> simp [h2, flatDirCoeffBlock, h]
        rw [hsum]
        simp
    · rw [linQMat_sub_apply_ne _ _ (Ne.symm hkk)]
      rw [Finset.sum_eq_zero]
      · simp
      · intro i _
        by_cases h2 : u = v
        · rw [if_pos h2, flatDirCoeffBlock_eq_zero_of_ne (h := Ne.symm hkk), zero_smul_gen]
        · rw [if_neg h2, zero_smul_gen]
  · -- (inr (inr a), inl)
    simp [flatDirCoeff_zero_r]
  · -- (inr (inr a), inr (inl b))
    obtain ⟨kk1, r1⟩ := a2
    obtain ⟨kk2, r2⟩ := b1
    rw [fromBlocks_apply₂₂, penB_sub_penB_zero, fromBlocks_apply₂₁]
    simp only [flatDirCoeff_inr_inr_inl]
    by_cases hkk : kk1 = kk2
    · subst hkk
      rw [linQMat_sub_apply_eq, CStarMatrix.neg_apply,
        shiftMatrix_blockSemicircular_entry]
      by_cases h : (r1 : ℕ) + 1 = (r2 : ℕ)
      · rw [dif_pos h]
        have hp : (r1 : ℕ) < (polyW (h1Poly r k F) kk1).length := by
          have := r2.isLt; omega
        rw [show (polyW (h1Poly r k F) kk1).get ⟨r1, by omega⟩
            = (polyW (h1Poly r k F) kk1).get ⟨r1, hp⟩ from by simp]
        have hsum : (∑ i : Fin r,
              (if u = v then flatDirCoeffBlock k F i ⟨kk1, r1⟩ ⟨kk1, r2⟩ else 0)
                • semicircularFamily r i)
            = if u = v then (-1 : ℂ) •
                semicircularFamily r ((polyW (h1Poly r k F) kk1).get ⟨r1, hp⟩) else 0 := by
          by_cases h2 : u = v
          · simp only [if_pos h2]
            rw [Finset.sum_eq_single ((polyW (h1Poly r k F) kk1).get ⟨r1, hp⟩)]
            · rw [flatDirCoeffBlock, dif_pos ⟨rfl, h⟩, if_pos rfl, neg_one_smul_gen]
            · intro i _ hi
              rw [flatDirCoeffBlock, dif_pos ⟨rfl, h⟩,
                if_neg (fun hh => hi hh.symm), zero_smul_gen]
            · intro hi; exact absurd (Finset.mem_univ _) hi
          · simp [h2]
        rw [hsum]
        by_cases h2 : u = v
        · rw [if_pos h2, if_pos h2, neg_one_smul_gen]
        · rw [if_neg h2, if_neg h2]
          simp
      · rw [dif_neg h]
        have hsum : (∑ i : Fin r,
              (if u = v then flatDirCoeffBlock k F i ⟨kk1, r1⟩ ⟨kk1, r2⟩ else 0)
                • semicircularFamily r i) = 0 := by
          rw [Finset.sum_eq_zero]
          intro i _
          by_cases h2 : u = v <;> simp [h2, flatDirCoeffBlock, h]
        rw [hsum]
        simp
    · rw [linQMat_sub_apply_ne _ _ hkk]
      rw [Finset.sum_eq_zero]
      · simp
      · intro i _
        by_cases h2 : u = v
        · rw [if_pos h2, flatDirCoeffBlock_eq_zero_of_ne (h := hkk), zero_smul_gen]
        · rw [if_neg h2, zero_smul_gen]
  · -- (inr (inr a), inr (inr b))
    rw [fromBlocks_apply₂₂, penB_sub_penB_zero, fromBlocks_apply₂₂]
    simp [flatDirCoeff_inr_inr_inr]

end DirTerm

/-! ## 6. The flattened limit pencil is the closed pencil -/

section ClosedPencilId

variable (r k : ℕ) (F : RatPolyIdx r (k + 1)) (z : ℝ)

lemma h1PencilLimit_apply_entry' (p q : PenIdx (polyW (h1Poly r k F)))
    (u v : Fin (d0 k)) :
    (h1PencilLimit r k F z) p q u v
      = penL (blockSemicircular r (d0 k)) (polyW (h1Poly r k F)) (limitCoeff r k F)
          (penA0 (0 : BlockLimit r (d0 k)) z) p q u v := rfl

/-- **The flattened limit pencil is the canonical closed pencil.** -/
theorem flattenPencilLimit_h1PencilLimit :
    flattenPencilLimitStarAlgEquiv r k F (h1PencilLimit r k F z)
      = closedPencil (n := Fin (pencilCoeffDim k F))
          (pencilConstCoeff k F z) (pencilDirCoeff k F) := by
  classical
  refine Matrix.ext fun x y => ?_
  rw [flattenPencilLimit_apply]
  rw [h1PencilLimit_apply_entry']
  rw [show penL (blockSemicircular r (d0 k)) (polyW (h1Poly r k F)) (limitCoeff r k F)
        (penA0 (0 : BlockLimit r (d0 k)) z)
      = penL (0 : Fin r → BlockLimit r (d0 k)) (polyW (h1Poly r k F))
          (limitCoeff r k F) (penA0 (0 : BlockLimit r (d0 k)) z)
        + (penL (blockSemicircular r (d0 k)) (polyW (h1Poly r k F)) (limitCoeff r k F)
            (penA0 (0 : BlockLimit r (d0 k)) z)
          - penL (0 : Fin r → BlockLimit r (d0 k)) (polyW (h1Poly r k F))
            (limitCoeff r k F) (penA0 (0 : BlockLimit r (d0 k)) z)) from by abel]
  rw [Matrix.add_apply, CStarMatrix.add_apply]
  rw [penL_zero_entry]
  rw [pencilDir_limit_entry]
  rw [closedPencil_apply, Algebra.algebraMap_eq_smul_one]
  simp only [pencilConstBlockA, pencilConstCoeff, pencilDirCoeff, Matrix.reindex_apply,
    Matrix.submatrix_apply, Equiv.symm_symm]

/-- **The limit-side spectral identification.**  The C⋆-graph real spectrum of the limit
pencil is the real spectrum of the canonical closed pencil of the Kronecker coefficients. -/
theorem specC_eq_spectrum_closedPencil :
    specC (h1PencilLimit r k F z) =
      spectrum ℝ (closedPencil (n := Fin (pencilCoeffDim k F))
        (pencilConstCoeff k F z) (pencilDirCoeff k F)) := by
  rw [specC_flatten_limit, flattenPencilLimit_h1PencilLimit]

end ClosedPencilId

/-! ## 7. The fully reduced weighted-strip bundle

The spectral identification `specC_eq_spectrum_closedPencil` lets us remove the remaining
limit-side fields of `WeightedStripDataAt''`:

* the limit-spectrum vanishing is now a consequence of the smooth cutoff on
  `specC (h1PencilLimit r k F z)` (which is the same set as the closed-pencil spectrum);
* the flat → GUE identification is no longer a hypothesis: at the canonical coefficient
  matrices it is the proved theorem `flatGUEStatisticEqCont_canonical`, and only the
  continuous test functions `f` and `(f')²` are consumed downstream;
* the coefficient matrices are the canonical `pencilConstCoeff` / `pencilDirCoeff` of size
  `pencilCoeffDim k F`, so the existential dimension `d'` disappears.

The resulting bundle is `WeightedStripDataAt'''` / `WeightedStripInputs'''`. -/

section ReducedBundle

/-- The coefficient dimension `pencilCoeffDim k F` is positive. -/
lemma pencilCoeffDim_pos (r k : ℕ) (F : RatPolyIdx r (k + 1)) :
    0 < pencilCoeffDim k F := by
  unfold pencilCoeffDim
  have h1 : 0 < Fintype.card (PenIdx (polyW (h1Poly r k F))) :=
    Fintype.card_pos_iff.mpr ⟨Sum.inl 0⟩
  have h2 : 0 < (k + 1) + (k + 1) := by omega
  exact Nat.mul_pos h1 h2

/-- **The closed-pencil bridge for arbitrary matrix size.**  `LimitBridge`'s
`trace_operatorMatrixPencilCauchy_eq_blockLimitResolventTrace` is stated for
`Fin (d' + 1)`; the canonical coefficients live at `Fin (pencilCoeffDim k F)`, so we need the
general-index version. -/
theorem trace_operatorMatrixPencilCauchy_eq_blockLimitResolventTrace_gen
    (m : ℕ) (C₀ : Matrix (Fin m) (Fin m) ℂ) (C : Fin r → Matrix (Fin m) (Fin m) ℂ)
    (hC₀ : C₀.IsHermitian) (hC : ∀ i, (C i).IsHermitian) {z : ℂ} (hz : z.im ≠ 0) :
    Matrix.trace (operatorMatrixPencilCauchy C₀ C z) =
      blockLimitResolventTrace (closedPencil (n := Fin m) C₀ C) z := by
  have hsa := closedPencil_isSelfAdjoint (n := Fin m) C₀ C hC₀ hC
  have hunit : IsUnit (algebraMap ℂ
      (CStarMatrix (Fin m) (Fin m) (closedSemicircularAlgebra (Fin r))) z -
        closedPencil (n := Fin m) C₀ C) := by
    rw [← spectrum.notMem_iff]
    intro hzmem
    exact hz (hsa.im_eq_zero_of_mem_spectrum hzmem)
  have hres := cmap_resolvent (f := StarSubalgebra.subtype (closedSemicircularAlgebra (Fin r)))
    (M := closedPencil (n := Fin m) C₀ C) (z := z) hunit
  rw [cmap_subtype_closedPencil] at hres
  rw [trace_operatorMatrixPencilCauchy]
  unfold blockLimitResolventTrace
  rw [← hres]
  have hsymm : CStarMatrix.ofMatrix.symm
      ((cmap (StarSubalgebra.subtype (closedSemicircularAlgebra (Fin r))))
        (resolvent (closedPencil (n := Fin m) C₀ C) z)) =
      (cmap (StarSubalgebra.subtype (closedSemicircularAlgebra (Fin r))))
        (resolvent (closedPencil (n := Fin m) C₀ C) z) := rfl
  rw [hsymm, trace_cmap]
  rfl

/-- **The weighted-strip data at one pencil, with all limit-side bookkeeping removed.**  The
limit element is the canonical closed pencil of the Kronecker coefficients, the cutoff is
stated on the limit spectrum only, and the flat → GUE identification and the vanishing are
theorems. -/
def WeightedStripDataAt''' (r k : ℕ) (F : RatPolyIdx r (k + 1)) (z ε : ℝ) : Prop :=
  letI : Nonempty (Fin (pencilCoeffDim k F)) :=
    ⟨⟨0, pencilCoeffDim_pos r k F⟩⟩
  ∃ (η₀ C_s β : ℝ) (hη₀2 : 2 < η₀) (hC_s : 0 ≤ C_s) (hβ0 : 0 ≤ β) (hβk : β < k)
    (f : ℝ → ℝ) (C' : ℝ),
    IsSmoothCutoffZeroOn (specC (h1PencilLimit r k F z)) ε f ∧
    ContDiff ℝ (k + 1) f ∧
    ContDiff ℝ (k + 1) (fun y => (deriv f y) ^ 2) ∧
    HasCompactSupport f ∧
    WeightedStripBound (pencilConstCoeff k F z) (pencilDirCoeff k F) k η₀ C_s β ∧
    0 ≤ C'

/-- **The fully reduced weighted-strip input bundle.** -/
def WeightedStripInputs''' (r : ℕ) : Prop :=
  (∀ (k : ℕ) (F : RatPolyIdx r (k + 1)) (z ε : ℝ), 1 ≤ k → 0 < ε →
    WeightedStripDataAt''' r k F z ε) ∧
  (∀ (F : RatPolyIdx r (0 + 1)) (z ε : ℝ), 0 < ε →
    ∃ (f : ℝ → ℝ) (C C' : ℝ),
      IsSmoothCutoffZeroOn (specC (h1PencilLimit r 0 F z)) ε f ∧
      FlatLemmaM r 0 F z f C ∧
      FlatLemmaM r 0 F z (fun y => (deriv f y) ^ 2) C' ∧
      0 ≤ C ∧ 0 ≤ C')

/-- **The fully reduced bundle gives the weighted mean comparisons.** -/
theorem WeightedMeanInputs_of_weightedStripInputs''' (h : WeightedStripInputs''' r) :
    WeightedMeanInputs r := by
  intro k F z ε hε
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · subst hk0
    exact h.2 F z ε hε
  · obtain ⟨η₀, C_s, β, hη₀2, hC_s, hβ0, hβk, f, C', hcut, hreg, hregw, hfc, hstrip,
      hC'⟩ := h.1 k F z ε hkpos hε
    haveI hne : NeZero (pencilCoeffDim k F) :=
      ⟨Nat.ne_of_gt (pencilCoeffDim_pos r k F)⟩
    haveI hne' : Nonempty (Fin (pencilCoeffDim k F)) :=
      ⟨⟨0, pencilCoeffDim_pos r k F⟩⟩
    have hA₀ := pencilConstCoeff_isHermitian k F z
    have hA := pencilDirCoeff_isHermitian k F
    set C₀ : Matrix (Fin (pencilCoeffDim k F)) (Fin (pencilCoeffDim k F)) ℂ :=
      pencilConstCoeff k F z with hC₀def
    set C : Fin r → Matrix (Fin (pencilCoeffDim k F)) (Fin (pencilCoeffDim k F)) ℂ :=
      pencilDirCoeff k F with hCdef
    have hsp : spectrum ℝ (closedPencil (n := Fin (pencilCoeffDim k F)) C₀ C) =
        specC (h1PencilLimit r k F z) :=
      (specC_eq_spectrum_closedPencil r k F z).symm
    have hres : ∀ z' : ℂ, z'.im ≠ 0 →
        Matrix.trace (operatorMatrixPencilCauchy C₀ C z') =
          blockLimitResolventTrace (closedPencil (n := Fin (pencilCoeffDim k F)) C₀ C) z' :=
      fun z' hz' =>
        trace_operatorMatrixPencilCauchy_eq_blockLimitResolventTrace_gen
          (pencilCoeffDim k F) C₀ C hA₀ hA hz'
    have hhh : IsSelfAdjoint (closedPencil (n := Fin (pencilCoeffDim k F)) C₀ C) :=
      closedPencil_isSelfAdjoint C₀ C hA₀ hA
    have hzerof : ∀ x ∈ spectrum ℝ (closedPencil (n := Fin (pencilCoeffDim k F)) C₀ C),
        f x = 0 := by
      intro x hx
      rw [hsp] at hx
      exact hcut.eq_zero x hx
    have hzerow : ∀ x ∈ spectrum ℝ (closedPencil (n := Fin (pencilCoeffDim k F)) C₀ C),
        (deriv f x) ^ 2 = 0 := by
      intro x hx
      rw [hsp] at hx
      rw [hcut.deriv_eq_zero x hx]
      ring
    refine ⟨f, weightedStripConstant f k C_s β,
      weightedStripConstant (fun y => (deriv f y) ^ 2) k C_s β,
      ?_, ?_, ?_, weightedStripConstant_nonneg hC_s,
      weightedStripConstant_nonneg hC_s⟩
    · exact hcut
    · refine flatLemmaM_of_weightedStrip (d' := pencilCoeffDim k F) C₀ C hA₀ hA hkpos
        hη₀2 hC_s hβ0 hβk hreg hfc hstrip
        (fun N => flatGUEStatisticEqCont_canonical k F z N f hreg.continuous)
        (guePlaneLimitOrder_eq_zero_of_eq_zero_on_spectrum hkpos hhh hres hreg le_rfl hfc
          hzerof)
        (eventually_integrable_dbarNumOrder_mul_trace_gueResolventMean C₀ C hA₀ hA hkpos
          hreg le_rfl hfc)
        (integrable_dbarNumOrder_mul_trace_operatorMatrixPencilCauchy_of_eq
          (closedPencil (n := Fin (pencilCoeffDim k F)) C₀ C) hhh hres hkpos hreg le_rfl hfc)
    · refine flatLemmaM_of_weightedStrip (d' := pencilCoeffDim k F) C₀ C hA₀ hA hkpos
        hη₀2 hC_s hβ0 hβk hregw hcut.smooth.compactSupport hstrip
        (fun N => flatGUEStatisticEqCont_canonical k F z N
          (fun y => (deriv f y) ^ 2) hregw.continuous)
        (guePlaneLimitOrder_eq_zero_of_eq_zero_on_spectrum hkpos hhh hres hregw le_rfl
          hcut.smooth.compactSupport hzerow)
        (eventually_integrable_dbarNumOrder_mul_trace_gueResolventMean C₀ C hA₀ hA hkpos
          hregw le_rfl hcut.smooth.compactSupport)
        (integrable_dbarNumOrder_mul_trace_operatorMatrixPencilCauchy_of_eq
          (closedPencil (n := Fin (pencilCoeffDim k F)) C₀ C) hhh hres hkpos hregw le_rfl
          hcut.smooth.compactSupport)

/-- **The project target from scalar spectral inclusion and the fully reduced bundle.** -/
theorem GUEStrongConvergenceStatement_of_weightedStripInputs'''
    (hScalar : ScalarSpectralInclusion r) (h : WeightedStripInputs''' r) :
    GUEStrongConvergenceStatement r :=
  GUEStrongConvergenceStatement_of_weightedMeanInputs hScalar
    (WeightedMeanInputs_of_weightedStripInputs''' h)

end ReducedBundle


end

end GUEStrongConvergence
