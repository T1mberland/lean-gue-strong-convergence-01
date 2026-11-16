/-
# The Kronecker/reindexing identity for the flattened pencil

`Probability/KroneckerPencil.lean` proves the two halves of the affine decomposition of the
flattened linearization pencil:

* the constant term is a block-scalar matrix `A₀ ⊗ 1` (`penL_zero_eq_blockScalar`);
* the affine slope is the reindexed GUE direction family (`flatStepDir_eq_reindex_gueDirMatrix`).

This file assembles them, entrywise, into the **Kronecker identity**

`flatPencilBlk r k F N z y
  = Matrix.reindex e e (guePencilMatrix (pencilConstCoeff k F z) (pencilDirCoeff k F) y)`

with `e = pencilCoeffFlatIdx k F N`, the composite of the coefficient reindexing
`pencilCoeffIdx` and the pencil flattening `pencilFlatIdx`.

## Contents

* `Matrix.reindex_reindex` — the composition law for `Matrix.reindex`;
* `Matrix.reindex_kronecker_prodCongr` — `reindex` through a product with a fixed factor;
* `sum_mul_sum_swap` — the double-sum exchange `∑ p, a p * ∑ l, b l * f p l
  = ∑ p, b p * ∑ l, a l * f l p`;
* `flatPencilBlk_eq_reindex_guePencilMatrix` — the identity.

No `sorry`, no new axioms.
-/
import GUEStrongConvergence.Probability.KroneckerPencil
import GUEStrongConvergence.Probability.LemmaVSmooth
import GUEStrongConvergence.StrongConvergence.FlatSideConditions

open Matrix Kronecker MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ComplexOrder ENNReal Pointwise Topology

namespace GUEStrongConvergence

noncomputable section

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

variable {r : ℕ}

/-! ## 1. Reindexing lemmas -/

section ReindexLemmas

variable {α β γ : Type*} {R : Type*} [Semiring R]

/-- Composition law for `Matrix.reindex`. -/
lemma Matrix.reindex_reindex (e : α ≃ β) (f : β ≃ γ) (M : Matrix α α R) :
    Matrix.reindex f f (Matrix.reindex e e M) = Matrix.reindex (e.trans f) (e.trans f) M := by
  ext a b
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_trans_apply]

/-- Reindexing only the first factor of a Kronecker product. -/
lemma Matrix.reindex_kronecker_prodCongr {d d' : Type*} [Fintype d] [Fintype d']
    {N : ℕ} (e : d ≃ d') (A : Matrix d d ℂ) (B : Matrix (Fin N) (Fin N) ℂ) :
    Matrix.reindex (e.prodCongr (Equiv.refl (Fin N))) (e.prodCongr (Equiv.refl (Fin N)))
        (A ⊗ₖ B)
      = Matrix.reindex e e A ⊗ₖ B := by
  ext a b
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.kroneckerMap_apply,
    Equiv.prodCongr_symm, Equiv.prodCongr_apply, Equiv.refl_symm, Equiv.coe_refl,
    Prod.map_fst, Prod.map_snd, id_eq]

/-- Entry of a reindexed matrix at reindexed indices. -/
lemma Matrix.reindex_apply_self {α β : Type*} {R : Type*} [Semiring R]
    (e : α ≃ β) (M : Matrix α α R) (a b : α) :
    Matrix.reindex e e M (e a) (e b) = M a b := by
  have h : Matrix.reindex e e M = M.submatrix (⇑e.symm) (⇑e.symm) := rfl
  rw [h]
  simp only [Matrix.submatrix_apply, Equiv.symm_apply_apply]

end ReindexLemmas

/-- The double-sum exchange used for the affine direction terms:
`∑ p, a p * ∑ l, b l * f p l = ∑ p, b p * ∑ l, a l * f l p`. -/
lemma sum_mul_sum_swap {α β : Type*} [Fintype α] [Fintype β]
    (a : α → ℂ) (b : β → ℂ) (f : α → β → ℂ) :
    (∑ p, a p * ∑ l, b l * f p l) = ∑ l, b l * ∑ p, a p * f p l := by
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun l _ => Finset.sum_congr rfl (fun p _ => ?_))
  ring

/-! ## 2. The coefficient flattening equivalence -/

section CoeffIndex

variable (k : ℕ) (F : RatPolyIdx r (k + 1)) (N : ℕ)

/-- The coefficient index equivalence used in the Kronecker identity: first the coefficient
reindexing `pencilCoeffIdx`, then the pencil flattening `pencilFlatIdx`. -/
def pencilCoeffFlatIdx :
    Fin (pencilCoeffDim k F) × Fin (N + 1) ≃ Fin (pencilFlatDim r k F N) :=
  ((pencilCoeffIdx k F).prodCongr (Equiv.refl (Fin (N + 1)))).trans
    (pencilFlatIdx r k F N)

end CoeffIndex

/-! ## 3. Entry computations -/

section Entries

variable (k : ℕ) (F : RatPolyIdx r (k + 1)) (N : ℕ) (z : ℝ)

/-- The zero block GUE tuple vanishes. -/
lemma blockGUEBlk_zero (d : ℕ) :
    blockGUEBlk r d N (0 : EuclideanSpace ℝ (GUECoord (Fin r) (N + 1))) = 0 := by
  funext i
  ext u v s t
  simp [blockGUEBlk, gueMatrix, gueUnscaled, blockDiag_apply_entry']

/-- Entry formula for `penLFlat`, from `flatten_apply_entry`. -/
lemma penLFlat_apply_entry (X : Fin r → BlockAlg ((k + 1) + (k + 1)) N)
    (i j : PenIdx (polyW (h1Poly r k F))) (u v : Fin ((k + 1) + (k + 1)))
    (s t : Fin (N + 1)) :
    penLFlat r k F N z X (pencilFlatIdx r k F N ((i, u), s))
        (pencilFlatIdx r k F N ((j, v), t))
      = (penL X (polyW (h1Poly r k F)) (h1Coeff r k F N)
          (penA0 (0 : BlockAlg ((k + 1) + (k + 1)) N) z) i j u v) s t := by
  rw [penLFlat]
  exact flatten_apply_entry (r := r) (k := k) (F := F) (N := N)
    (penL X (polyW (h1Poly r k F)) (h1Coeff r k F N)
      (penA0 (0 : BlockAlg ((k + 1) + (k + 1)) N) z)) i j u v s t

/-- The constant term of the flattened pencil, entrywise: it is the block-scalar matrix
`pencilConstBlock`. -/
lemma flatPencilBlk_zero_entry
    (i j : PenIdx (polyW (h1Poly r k F))) (u v : Fin ((k + 1) + (k + 1)))
    (s t : Fin (N + 1)) :
    flatPencilBlk r k F N z 0 (pencilFlatIdx r k F N ((i, u), s))
        (pencilFlatIdx r k F N ((j, v), t))
      = if s = t then pencilConstBlock k F z i j u v else 0 := by
  rw [flatPencilBlk, blockGUEBlk_zero, penLFlat_apply_entry,
    penL_zero_eq_blockScalar]
  simp only [Matrix.of_apply, blockScalar_apply]

/-- **The affine direction term, entrywise.** -/
lemma flatStepDir_apply_entry (p : GUECoord (Fin r) (N + 1))
    (i j : PenIdx (polyW (h1Poly r k F))) (u v : Fin ((k + 1) + (k + 1)))
    (s t : Fin (N + 1)) :
    flatStepDir r k F N z p (pencilFlatIdx r k F N ((i, u), s))
        (pencilFlatIdx r k F N ((j, v), t))
      = ∑ l : Fin r, flatDirCoeff k F l (i, u) (j, v) * gueMatrixCoeff p l s t := by
  rw [flatStepDir_eq_reindex_gueDirMatrix, Matrix.reindex_apply_self]
  rfl

end Entries

/-! ## 4. The Kronecker identity -/

section Identity

variable (k : ℕ) (F : RatPolyIdx r (k + 1)) (N : ℕ) (z : ℝ)

/-- **The entry form of the Kronecker identity.**  Both sides are evaluated at the flattened
indices of the block pair `((i, u), s)`. -/
lemma flatPencilBlk_apply_entry
    (y : EuclideanSpace ℝ (GUECoord (Fin r) (N + 1)))
    (x' y' : (PenIdx (polyW (h1Poly r k F)) × Fin ((k + 1) + (k + 1))) × Fin (N + 1)) :
    flatPencilBlk r k F N z y (pencilFlatIdx r k F N x') (pencilFlatIdx r k F N y')
      = guePencilMatrix (pencilConstCoeff k F z) (pencilDirCoeff k F) y
          ((pencilCoeffIdx k F).symm x'.1, x'.2)
          ((pencilCoeffIdx k F).symm y'.1, y'.2) := by
  classical
  obtain ⟨x1, x2⟩ := x'
  obtain ⟨y1, y2⟩ := y'
  obtain ⟨i, u⟩ := x1
  obtain ⟨j, v⟩ := y1
  rw [flatPencilBlk_eq_const_add_sum, Matrix.add_apply, Matrix.sum_apply,
    flatPencilBlk_zero_entry, guePencilMatrix_apply]
  -- the constant coefficient term
  have hconst : pencilConstCoeff k F z ((pencilCoeffIdx k F).symm (i, u))
        ((pencilCoeffIdx k F).symm (j, v))
        * (1 : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) x2 y2
      = if x2 = y2 then pencilConstBlock k F z i j u v else 0 := by
    rw [pencilConstCoeff, Equiv.apply_symm_apply, Equiv.apply_symm_apply, Matrix.one_apply]
    by_cases h : x2 = y2 <;> simp [h]
  rw [hconst]
  -- the constant term of the left-hand side has the same shape
  have hdir : (∑ p : GUECoord (Fin r) (N + 1),
        (y p • flatStepDir r k F N z p) (pencilFlatIdx r k F N ((i, u), x2))
          (pencilFlatIdx r k F N ((j, v), y2)))
      = ∑ p, ∑ l : Fin r, (y p : ℂ) *
          (flatDirCoeff k F l (i, u) (j, v) * gueMatrixCoeff p l x2 y2) := by
    refine Finset.sum_congr rfl (fun p _ => ?_)
    rw [Matrix.smul_apply, Complex.real_smul, flatStepDir_apply_entry, Finset.mul_sum]
  have hrhs : (∑ q : Fin r,
        pencilDirCoeff k F q ((pencilCoeffIdx k F).symm (i, u))
            ((pencilCoeffIdx k F).symm (j, v)) * gueMatrix y q x2 y2)
      = ∑ q : Fin r, ∑ l : GUECoord (Fin r) (N + 1),
          flatDirCoeff k F q (i, u) (j, v) *
          ((y l : ℂ) * gueMatrixCoeff l q x2 y2) := by
    refine Finset.sum_congr rfl (fun q _ => ?_)
    rw [pencilDirCoeff, Matrix.reindex_apply_self]
    rw [gueMatrix_eq_sum, Matrix.sum_apply]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [Matrix.smul_apply, Complex.real_smul]
    rfl
  rw [hdir, hrhs]
  congr 1
  -- pure double-sum exchange between the two direction terms
  simp only [← Finset.mul_sum]
  exact sum_mul_sum_swap (fun p => (y p : ℂ)) (fun l => flatDirCoeff k F l (i, u) (j, v))
    (fun p l => gueMatrixCoeff p l x2 y2)

end Identity

/-- **The Kronecker/affine-coefficient identity for the flattened pencil.** -/
theorem flatPencilBlk_eq_reindex_guePencilMatrix
    (k : ℕ) (F : RatPolyIdx r (k + 1)) (N : ℕ) (z : ℝ)
    (y : EuclideanSpace ℝ (GUECoord (Fin r) (N + 1))) :
    flatPencilBlk r k F N z y
      = Matrix.reindex (pencilCoeffFlatIdx k F N) (pencilCoeffFlatIdx k F N)
          (guePencilMatrix (pencilConstCoeff k F z) (pencilDirCoeff k F) y) := by
  ext a b
  obtain ⟨p, rfl⟩ := (pencilCoeffFlatIdx k F N).surjective a
  obtain ⟨q, rfl⟩ := (pencilCoeffFlatIdx k F N).surjective b
  rw [Matrix.reindex_apply_self]
  have hp : pencilCoeffFlatIdx k F N p = pencilFlatIdx r k F N (pencilCoeffIdx k F p.1, p.2) :=
    rfl
  have hq : pencilCoeffFlatIdx k F N q = pencilFlatIdx r k F N (pencilCoeffIdx k F q.1, q.2) :=
    rfl
  rw [hp, hq, flatPencilBlk_apply_entry, Equiv.symm_apply_apply, Equiv.symm_apply_apply]

/-! ## 5. Hermitianity of the canonical coefficient matrices -/

/-- `blockScalar` is injective. -/
lemma blockScalar_injective {d N : ℕ} :
    Function.Injective (fun C : Matrix (Fin d) (Fin d) ℂ =>
      (blockScalar (N := N) C : BlockAlg d N)) := by
  intro C D h
  ext u v
  have h1 := congrArg (fun M : BlockAlg d N => M u v 0 0) h
  simpa [blockScalar_apply] using h1

/-- `blockScalar C` is Hermitian iff `C` is. -/
lemma blockScalar_isHermitian_iff {d N : ℕ} (C : Matrix (Fin d) (Fin d) ℂ) :
    (blockScalar (N := N) C : BlockAlg d N).IsHermitian ↔ C.IsHermitian := by
  constructor
  · intro h
    have h' : star (blockScalar (N := N) C) = blockScalar (N := N) C :=
      Matrix.IsHermitian.star_eq h
    rw [blockScalar_star] at h'
    exact blockScalar_injective h'
  · intro h
    have hstar : star (blockScalar (N := N) C) = blockScalar (N := N) C := by
      rw [blockScalar_star, Matrix.IsHermitian.star_eq h]
    exact Matrix.isHermitian_iff_isSelfAdjoint.mpr hstar

/-- The block matrix of constant coefficients is Hermitian. -/
lemma pencilConstMat_isHermitian (k : ℕ) (F : RatPolyIdx r (k + 1)) (N : ℕ) (z : ℝ) :
    (Matrix.of fun p q : PenIdx (polyW (h1Poly r k F)) × Fin ((k + 1) + (k + 1)) =>
      pencilConstBlock k F z p.1 q.1 p.2 q.2).IsHermitian := by
  have hsa : IsSelfAdjoint (penL (0 : Fin r → BlockAlg ((k + 1) + (k + 1)) N)
      (polyW (h1Poly r k F)) (h1Coeff r k F N)
      (penA0 (0 : BlockAlg ((k + 1) + (k + 1)) N) z)) :=
    penL_isSelfAdjoint k F N z 0
  rw [penL_zero_eq_blockScalar] at hsa
  have hHerm := Matrix.isHermitian_iff_isSelfAdjoint.mpr hsa
  refine Matrix.IsHermitian.ext ?_
  intro x y
  obtain ⟨p, u⟩ := x
  obtain ⟨q, v⟩ := y
  have h3 := Matrix.IsHermitian.apply hHerm p q
  have h4 : (star ((Matrix.of fun p q : PenIdx (polyW (h1Poly r k F)) =>
        blockScalar (N := N) (pencilConstBlock k F z p q)) q p)) u v 0 0
      = (Matrix.of fun p q : PenIdx (polyW (h1Poly r k F)) =>
        blockScalar (N := N) (pencilConstBlock k F z p q)) p q u v 0 0 := by
    rw [h3]
  rw [CStarMatrix.star_apply, CStarMatrix.star_apply] at h4
  simp only [Matrix.of_apply, blockScalar_apply] at h4
  simpa [Matrix.of_apply] using h4

/-- **The constant coefficient matrix `A₀` is Hermitian.** -/
lemma pencilConstCoeff_isHermitian (k : ℕ) (F : RatPolyIdx r (k + 1)) (z : ℝ) :
    (pencilConstCoeff k F z).IsHermitian := by
  have hM := pencilConstMat_isHermitian k F 0 z
  have h := (isHermitian_reindex_iff (pencilCoeffIdx k F).symm
    (Matrix.of fun p q : PenIdx (polyW (h1Poly r k F)) × Fin ((k + 1) + (k + 1)) =>
      pencilConstBlock k F z p.1 q.1 p.2 q.2)).mpr hM
  have heq : Matrix.reindex (pencilCoeffIdx k F).symm (pencilCoeffIdx k F).symm
      (Matrix.of fun p q : PenIdx (polyW (h1Poly r k F)) × Fin ((k + 1) + (k + 1)) =>
        pencilConstBlock k F z p.1 q.1 p.2 q.2) = pencilConstCoeff k F z := by
    ext x y
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm,
      Matrix.of_apply, pencilConstCoeff]
  rwa [heq] at h

/-- Every entry of `flatDirCoeffBlock` is real. -/
lemma star_flatDirCoeffBlock (k : ℕ) (F : RatPolyIdx r (k + 1)) (i : Fin r)
    (a b : BlkIdx (polyW (h1Poly r k F))) :
    star (flatDirCoeffBlock k F i a b) = flatDirCoeffBlock k F i a b := by
  rw [flatDirCoeffBlock]
  split_ifs <;> simp

/-- The block coefficient matrix `flatDirCoeff` is Hermitian (its entries are real). -/
lemma flatDirCoeff_isHermitian (k : ℕ) (F : RatPolyIdx r (k + 1)) (i : Fin r) :
    (flatDirCoeff k F i).IsHermitian := by
  ext x y
  rw [Matrix.conjTranspose_apply]
  obtain ⟨x1, x2⟩ := x
  obtain ⟨y1, y2⟩ := y
  rcases x1 with a0 | (a1 | a2) <;> rcases y1 with b0 | (b1 | b2) <;>
    (by_cases hxy : x2 = y2
     · subst hxy
       simp [flatDirCoeff, star_flatDirCoeffBlock]
     · simp [flatDirCoeff, hxy, Ne.symm hxy])

/-- **The direction coefficient matrices `Aᵢ` are Hermitian.** -/
lemma pencilDirCoeff_isHermitian (k : ℕ) (F : RatPolyIdx r (k + 1)) (i : Fin r) :
    (pencilDirCoeff k F i).IsHermitian := by
  have h := (isHermitian_reindex_iff (pencilCoeffIdx k F).symm (flatDirCoeff k F i)).mpr
    (flatDirCoeff_isHermitian k F i)
  simpa [pencilDirCoeff] using h

/-! ## 6. The cfc statistic of the canonical data -/

/-- `normTrace` of the reindexed cfc is the pencil normalized trace, for an arbitrary
index equivalence (the general form of `normTrace_hermCfc_reindex`). -/
lemma normTrace_hermCfc_reindex' {m : ℕ} {d : Type*} [Fintype d] [DecidableEq d]
    {n : ℕ} (e : d × Fin n ≃ Fin m) (f : ℝ → ℝ) (P : Matrix (d × Fin n) (d × Fin n) ℂ)
    (hH : (Matrix.reindex e e P).IsHermitian) :
    normTrace (hermCfc (Matrix.reindex e e P) f hH) = guePencilNormTrace (cfc f P) := by
  have h1 : hermCfc (Matrix.reindex e e P) f hH = cfc f (Matrix.reindex e e P) := rfl
  have hm : Fintype.card d * n = m := by
    simpa [Fintype.card_prod, Fintype.card_fin] using Fintype.card_congr e
  rw [h1, cfc_reindex, normTrace, trace_reindex, guePencilNormTrace, gueNormConst, ← hm]

/-- **The pointwise identity of statistics**: the flattened statistic at a Gaussian block is the
GUE pencil statistic of the canonical coefficient matrices. -/
theorem flatStatBlk_eq_gueStatisticCfc (k : ℕ) (F : RatPolyIdx r (k + 1)) (N : ℕ) (z : ℝ)
    (hA₀ : (pencilConstCoeff k F z).IsHermitian)
    (hA : ∀ i, (pencilDirCoeff k F i).IsHermitian)
    (g : ℝ → ℝ) (y : EuclideanSpace ℝ (GUECoord (Fin r) (N + 1))) :
    flatStatBlk r k F z N g y
      = gueStatisticCfc (N := N + 1) g (pencilConstCoeff k F z) (pencilDirCoeff k F)
          hA₀ hA y := by
  rw [flatStatBlk]
  have h1 : hermCfc (flatPencilBlk r k F N z y) g (flatPencilBlk_isHermitian k F N z y)
      = cfc g (flatPencilBlk r k F N z y) := rfl
  rw [h1, flatPencilBlk_eq_reindex_guePencilMatrix k F N z y]
  have hH : (Matrix.reindex (pencilCoeffFlatIdx k F N) (pencilCoeffFlatIdx k F N)
      (guePencilMatrix (pencilConstCoeff k F z) (pencilDirCoeff k F) y)).IsHermitian := by
    rw [← flatPencilBlk_eq_reindex_guePencilMatrix]
    exact flatPencilBlk_isHermitian k F N z y
  have h2 : normTrace (cfc g (Matrix.reindex (pencilCoeffFlatIdx k F N)
        (pencilCoeffFlatIdx k F N)
        (guePencilMatrix (pencilConstCoeff k F z) (pencilDirCoeff k F) y)))
      = guePencilNormTrace (cfc g
          (guePencilMatrix (pencilConstCoeff k F z) (pencilDirCoeff k F) y)) :=
    normTrace_hermCfc_reindex' (pencilCoeffFlatIdx k F N) g
      (guePencilMatrix (pencilConstCoeff k F z) (pencilDirCoeff k F) y) hH
  rw [h2, gueStatisticCfc, guePencilCfc_eq_cfc]

/-- Measurability of the block statistic for continuous `g`. -/
lemma measurable_flatStatBlk (k : ℕ) (F : RatPolyIdx r (k + 1)) (N : ℕ) (z : ℝ)
    {g : ℝ → ℝ} (hg : Continuous g) :
    Measurable fun y : EuclideanSpace ℝ (GUECoord (Fin r) (N + 1)) =>
      flatStatBlk r k F z N g y :=
  measurable_normTrace_cfc
    (M := fun y => flatPencilBlk r k F N z y)
    (hM := fun a b => ((continuous_flatPencilBlk k F N z).matrix_elem a b).measurable)
    (hHerm := fun y => flatPencilBlk_isHermitian k F N z y) hg

/-- **Consequence A: the integral transport for continuous test functions.** -/
theorem integral_flatStat_eq_gueStatisticCfc (k : ℕ) (F : RatPolyIdx r (k + 1)) (N : ℕ)
    (z : ℝ) (hA₀ : (pencilConstCoeff k F z).IsHermitian)
    (hA : ∀ i, (pencilDirCoeff k F i).IsHermitian) {g : ℝ → ℝ} (hg : Continuous g) :
    ∫ x : CommonSpace (Fin r), flatStat r k F z N g x ∂(commonGaussianMeasure (Fin r))
      = ∫ y : EuclideanSpace ℝ (GUECoord (Fin r) (N + 1)),
          gueStatisticCfc (N := N + 1) g (pencilConstCoeff k F z) (pencilDirCoeff k F)
            hA₀ hA y
          ∂(stdGaussian (EuclideanSpace ℝ (GUECoord (Fin r) (N + 1)))) := by
  rw [show (∫ x : CommonSpace (Fin r), flatStat r k F z N g x
        ∂(commonGaussianMeasure (Fin r)))
      = ∫ x : CommonSpace (Fin r), flatStatBlk r k F z N g (x (N + 1))
          ∂(commonGaussianMeasure (Fin r)) from by
        simp only [flatStat_eq_blk]]
  rw [integral_eval_commonGaussian (ι := Fin r) (N := N + 1)
    (g := flatStatBlk r k F z N g) (measurable_flatStatBlk k F N z hg).aestronglyMeasurable]
  exact integral_congr_ae (ae_of_all _ (fun y =>
    flatStatBlk_eq_gueStatisticCfc k F N z hA₀ hA g y))

/-- The integral transport with the canonical Hermitian witnesses. -/
theorem integral_flatStat_eq_gueStatisticCfc_canonical (k : ℕ) (F : RatPolyIdx r (k + 1))
    (N : ℕ) (z : ℝ) {g : ℝ → ℝ} (hg : Continuous g) :
    ∫ x : CommonSpace (Fin r), flatStat r k F z N g x ∂(commonGaussianMeasure (Fin r))
      = ∫ y : EuclideanSpace ℝ (GUECoord (Fin r) (N + 1)),
          gueStatisticCfc (N := N + 1) g (pencilConstCoeff k F z) (pencilDirCoeff k F)
            (pencilConstCoeff_isHermitian k F z) (pencilDirCoeff_isHermitian k F) y
          ∂(stdGaussian (EuclideanSpace ℝ (GUECoord (Fin r) (N + 1)))) :=
  integral_flatStat_eq_gueStatisticCfc k F N z
    (pencilConstCoeff_isHermitian k F z) (pencilDirCoeff_isHermitian k F) hg

end

/-! ## 7. The flat → GUE identification for continuous test functions -/

/-- **The flat → GUE identification for continuous test functions**, the continuous-test
version of `FlatGUEStatisticEq` (`Probability/LemmaMWeighted.lean`).  The all-`g` form is not
provable without measurability of `cfc` in the matrix argument; the downstream weighted-strip
chain only consumes the identity at the smooth cutoffs `f` and `(f')²`, for which continuity
holds. -/
def FlatGUEStatisticEqCont (r k : ℕ) (F : RatPolyIdx r (k + 1)) (z : ℝ) (m : ℕ)
    (A₀ : Matrix (Fin m) (Fin m) ℂ) (A : Fin r → Matrix (Fin m) (Fin m) ℂ)
    (hA₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian) : Prop :=
  ∀ (N : ℕ) (g : ℝ → ℝ), Continuous g →
    ∫ x, flatStat r k F z N g x ∂(commonGaussianMeasure (Fin r))
      = ∫ y : EuclideanSpace ℝ (GUECoord (Fin r) (N + 1)),
          gueStatisticCfc (N := N + 1) g A₀ A hA₀ hA y
            ∂(stdGaussian (EuclideanSpace ℝ (GUECoord (Fin r) (N + 1))))

/-- **The flat → GUE identification at the canonical coefficient matrices is a theorem** for
continuous test functions. -/
theorem flatGUEStatisticEqCont_canonical {r : ℕ} (k : ℕ) (F : RatPolyIdx r (k + 1)) (z : ℝ) :
    FlatGUEStatisticEqCont r k F z (pencilCoeffDim k F) (pencilConstCoeff k F z)
      (pencilDirCoeff k F) (pencilConstCoeff_isHermitian k F z)
      (pencilDirCoeff_isHermitian k F) := by
  intro N g hg
  exact integral_flatStat_eq_gueStatisticCfc k F N z
    (pencilConstCoeff_isHermitian k F z) (pencilDirCoeff_isHermitian k F) hg

end GUEStrongConvergence
