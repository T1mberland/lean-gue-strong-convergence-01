/-
# The Kronecker identity for the flattened linearization pencil

The flattened pencil `flatPencilBlk r k F N z` (`Probability/FlatLemmaV.lean`) is, for every
Gaussian point `y`, a matrix of size `pencilFlatDim r k F N`.  The GUE model pencil
(`Probability/GUEPencil.lean`) is `A₀ ⊗ 1 + ∑ᵢ Aᵢ ⊗ Gᵢ`, of size `(d+1) * (N+1)`.

This file proves the **Kronecker/affine-coefficient identity**: there are `N`-independent
coefficient matrices `A₀` and `A` (of size `card (PenIdx wds) * ((k+1)+(k+1))`) such that for
every `N ≥ 0` and every `y`

`flatPencilBlk r k F N z y
  = Matrix.reindex (pencilFlatIdxCoeff r k F N) (pencilFlatIdxCoeff r k F N)
      (guePencilMatrix (pencilConstCoeff r k F z) (pencilDirCoeff r k F) y)`.

The proof has two halves.

* **Affine decomposition.**  `penLFlat` is affine in the generator tuple
  (`penLFlat_add_smul`), so its linear part is additive and homogeneous.  The block GUE tuple is
  a finite sum of its coordinate directions (`blockGUEBlk_eq_sum`), hence
  `flatPencilBlk y = flatPencilBlk 0 + ∑ p, y p • flatStepDir p`.
* **Constant term.**  At the zero tuple every block of `penL` is a scalar matrix
  (`penL_zero_entry`), so the flattened constant term is `A₀ ⊗ 1` for the explicit coefficient
  matrix `pencilConstCoeff`.  The slope was already identified with
  `gueDirMatrix (flatDirCoeff k F) p` by `flatStepDir_eq_reindex_gueDirMatrix`.

No `sorry`, no new axioms.
-/
import GUEStrongConvergence.Probability.FlatContraction

open Matrix MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ComplexOrder ENNReal Pointwise Topology

namespace GUEStrongConvergence

noncomputable section

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency false

variable {r : ℕ}

attribute [local simp] CStarMatrix.one_apply CStarMatrix.star_apply
  CStarMatrix.conjTranspose_apply

/-! ## 1. Finite sums concentrated on one or two points -/

section SumHelpers

/-- A finite sum whose summand vanishes away from one point. -/
lemma sum_eq_single_of_eq_zero {α : Type*} [Fintype α] (f : α → ℂ) {x : α}
    (h : ∀ z, z ≠ x → f z = 0) : ∑ z, f z = f x :=
  Finset.sum_eq_single x (fun z _ hz => h z hz)
    (fun hx => absurd (Finset.mem_univ x) hx)

/-- A finite sum whose summand vanishes away from two distinct points. -/
lemma sum_eq_two_of_eq_zero {α : Type*} [Fintype α] [DecidableEq α] (f : α → ℂ) {x y : α}
    (hxy : x ≠ y) (h : ∀ z, z ≠ x → z ≠ y → f z = 0) : ∑ z, f z = f x + f y := by
  classical
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ x), Finset.sum_eq_single y]
  · ring
  · intro z hz hzy
    exact h z (Finset.ne_of_mem_erase hz) hzy
  · intro hy
    exact absurd (show y ∈ (Finset.univ : Finset α).erase x from
      Finset.mem_erase.mpr ⟨Ne.symm hxy, Finset.mem_univ y⟩) hy

/-- Scalar multiplication entry formula in the block algebra. -/
lemma blockAlg_smul_apply {d N : ℕ} (c : ℝ) (M : BlockAlg d N) (u v : Fin d)
    (s t : Fin (N + 1)) :
    (c • M) u v s t = (c : ℂ) * M u v s t := by
  simp [Matrix.smul_apply, Complex.real_smul]

/-- Entry extraction for finite sums in the block algebra (the `CStarMatrix` type synonym
prevents the `Matrix.sum_apply` rewrite rule from matching syntactically). -/
lemma blockAlg_sum_apply {d N : ℕ} {ι : Type*} (S : Finset ι) (f : ι → BlockAlg d N)
    (u v : Fin d) (s t : Fin (N + 1)) :
    (S.sum f) u v s t = S.sum (fun i => f i u v s t) := by
  classical
  induction S using Finset.induction with
  | empty => simp
  | insert a S ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha,
        show (f a + S.sum f) u v s t = f a u v s t + (S.sum f) u v s t from rfl, ih]

end SumHelpers

/-! ## 2. The block GUE tuple as a sum of its coordinate directions -/

section BlockGUESum

/-- Entry formula for the block-diagonal embedding. -/
lemma blockDiag_apply_entry' {d N : ℕ} (a : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ)
    (u v : Fin d) (s t : Fin (N + 1)) :
    (blockDiag (A := Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) a : BlockAlg d N) u v s t
      = if u = v then a s t else 0 := by
  show (Matrix.of (fun i j : Fin d => if i = j then a else 0)) u v s t = _
  simp only [Matrix.of_apply]
  split_ifs with h
  · rfl
  · rfl

/-- A GUE matrix is the sum of its coordinate directions. -/
lemma gueMatrix_eq_sum {ι : Type*} [Fintype ι] [DecidableEq ι] {N : ℕ}
    (y : GUECoord ι N → ℝ) (i : ι) :
    gueMatrix y i = ∑ p : GUECoord ι N, y p • gueMatrixDir p i := by
  classical
  ext a b
  rw [Matrix.sum_apply]
  have hterm : ∀ p : GUECoord ι N, (y p • gueMatrixDir p i) a b
      = (y p : ℂ) * ((gueScale N : ℂ) *
          (gueAlpha * (if (i, (a, b)) = p then (1 : ℂ) else 0)
            + gueBeta * (if (i, (b, a)) = p then (1 : ℂ) else 0))) := by
    intro p
    simp [Matrix.smul_apply, gueMatrixDir, gueMatrixCoeff, Complex.real_smul]
  simp only [hterm, gueMatrix, gueUnscaled]
  push_cast
  by_cases hab : a = b
  · subst hab
    rw [sum_eq_single_of_eq_zero _ (x := (i, (a, a)))]
    · simp only [if_pos rfl]
      have hgoal : gueAlpha * (1 : ℂ) + gueBeta * 1 = 1 := by
        rw [mul_one, mul_one, gueAlpha_add_gueBeta]
      calc ↑(gueScale N) * (gueAlpha * ↑(y (i, (a, a))) + gueBeta * ↑(y (i, (a, a))))
          = ↑(gueScale N) * ↑(y (i, (a, a))) * (gueAlpha + gueBeta) := by ring
        _ = ↑(gueScale N) * ↑(y (i, (a, a))) := by rw [gueAlpha_add_gueBeta, mul_one]
        _ = ↑(y (i, (a, a))) * (↑(gueScale N) * (gueAlpha * 1 + gueBeta * 1)) := by
            rw [hgoal, mul_one]; ring
    · intro z hz
      have hz' : (i, (a, a)) ≠ z := fun h => hz h.symm
      simp [hz']
  · rw [sum_eq_two_of_eq_zero _ (x := (i, (a, b))) (y := (i, (b, a)))
      (by simp [hab])]
    · have h1 : (i, (b, a)) ≠ (i, (a, b)) := by simp [hab]
      simp only [if_pos rfl, if_neg h1, if_neg (Ne.symm h1), if_true, mul_one]
      ring
    · intro z hz₁ hz₂
      have hz₁' : (i, (a, b)) ≠ z := fun h => hz₁ h.symm
      have hz₂' : (i, (b, a)) ≠ z := fun h => hz₂ h.symm
      simp [hz₁', hz₂']

/-- The block-diagonal GUE tuple is the sum of its coordinate directions. -/
lemma blockGUEBlk_eq_sum (d : ℕ) (N : ℕ)
    (y : EuclideanSpace ℝ (GUECoord (Fin r) (N + 1))) :
    blockGUEBlk r d N y
      = ∑ p : GUECoord (Fin r) (N + 1), y p • blockGUEDir r d N p := by
  classical
  funext i
  ext u v s t
  have hL : ((blockGUEBlk r d N y) i) u v s t
      = if u = v then gueMatrix (WithLp.ofLp y) i s t else 0 := by
    simp only [blockGUEBlk, blockDiag_apply_entry']
  have hR : (((∑ p : GUECoord (Fin r) (N + 1), y p • blockGUEDir r d N p) i) u v) s t
      = ∑ p : GUECoord (Fin r) (N + 1),
          (y p : ℂ) * (if u = v then gueMatrixDir p i s t else 0) := by
    rw [Finset.sum_apply, blockAlg_sum_apply]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    simp only [Pi.smul_apply, blockGUEDir]
    rw [blockAlg_smul_apply, blockDiag_apply_entry']
  rw [hL, hR]
  by_cases huv : u = v
  · subst huv
    simp only [if_pos rfl]
    have h := congrFun (congrFun (gueMatrix_eq_sum (WithLp.ofLp y) i) s) t
    rw [h]
    simp [Matrix.sum_apply, Matrix.smul_apply, Complex.real_smul]
  · simp [huv]

end BlockGUESum

/-! ## 3. The linear part of the flattened pencil -/

section LinPart

variable (k : ℕ) (F : RatPolyIdx r (k + 1)) (N : ℕ) (z : ℝ)

/-- The linear part of the flattened pencil: the increment over the zero generator tuple. -/
def penLFlatLin (X : Fin r → BlockAlg ((k + 1) + (k + 1)) N) :
    Matrix (Fin (pencilFlatDim r k F N)) (Fin (pencilFlatDim r k F N)) ℂ :=
  penLFlat r k F N z X - penLFlat r k F N z 0

lemma penLFlatLin_zero : penLFlatLin k F N z (0 : Fin r → BlockAlg _ N) = 0 := by
  simp [penLFlatLin]

/-- The linear part of an affine combination. -/
lemma penLFlatLin_add_smul (X Y : Fin r → BlockAlg ((k + 1) + (k + 1)) N) (s : ℝ) :
    penLFlatLin k F N z (X + s • Y)
      = penLFlatLin k F N z X + s • penLFlatLin k F N z Y := by
  simp only [penLFlatLin]
  rw [penLFlat_add_smul, smul_sub]
  abel

/-- The linear part is additive. -/
lemma penLFlatLin_add (X Y : Fin r → BlockAlg ((k + 1) + (k + 1)) N) :
    penLFlatLin k F N z (X + Y) = penLFlatLin k F N z X + penLFlatLin k F N z Y := by
  have h := penLFlatLin_add_smul k F N z X Y 1
  simpa using h

/-- The linear part is homogeneous. -/
lemma penLFlatLin_smul (X : Fin r → BlockAlg ((k + 1) + (k + 1)) N) (s : ℝ) :
    penLFlatLin k F N z (s • X) = s • penLFlatLin k F N z X := by
  have h := penLFlatLin_add_smul k F N z (0 : Fin r → BlockAlg _ N) X s
  simpa [penLFlatLin] using h

/-- The linear part of a finite sum. -/
lemma penLFlatLin_sum {ι : Type*} (s : Finset ι)
    (D : ι → Fin r → BlockAlg ((k + 1) + (k + 1)) N) (a : ι → ℝ) :
    penLFlatLin k F N z (∑ p ∈ s, a p • D p)
      = ∑ p ∈ s, a p • penLFlatLin k F N z (D p) := by
  classical
  induction s using Finset.induction with
  | empty => simp [penLFlatLin]
  | insert b s hb ih =>
    rw [Finset.sum_insert hb, Finset.sum_insert hb, penLFlatLin_add,
      show a b • D b = 0 + a b • D b from (zero_add _).symm, penLFlatLin_add_smul, ih]
    simp [penLFlatLin]

/-- **Affine decomposition of the flattened block pencil.** -/
theorem flatPencilBlk_eq_const_add_sum
    (y : EuclideanSpace ℝ (GUECoord (Fin r) (N + 1))) :
    flatPencilBlk r k F N z y
      = flatPencilBlk r k F N z 0
        + ∑ p : GUECoord (Fin r) (N + 1), y p • flatStepDir r k F N z p := by
  have hb : blockGUEBlk r ((k + 1) + (k + 1)) N y
      = ∑ p : GUECoord (Fin r) (N + 1), y p • blockGUEDir r ((k + 1) + (k + 1)) N p :=
    blockGUEBlk_eq_sum ((k + 1) + (k + 1)) N y
  have h0 : blockGUEBlk r ((k + 1) + (k + 1)) N
      (0 : EuclideanSpace ℝ (GUECoord (Fin r) (N + 1))) = 0 := by
    funext i
    ext u v s t
    simp [blockGUEBlk, gueMatrix, gueUnscaled, blockDiag_apply_entry']
  have hlin : ∀ p : GUECoord (Fin r) (N + 1),
      penLFlatLin k F N z (blockGUEDir r ((k + 1) + (k + 1)) N p)
        = flatStepDir r k F N z p := fun p => rfl
  have hsum := penLFlatLin_sum (r := r) (k := k) (F := F) (N := N) (z := z) Finset.univ
    (blockGUEDir r ((k + 1) + (k + 1)) N) (fun p => y p)
  simp only [hlin] at hsum
  have hmain : penLFlat r k F N z (∑ p : GUECoord (Fin r) (N + 1),
        y p • blockGUEDir r ((k + 1) + (k + 1)) N p)
      = penLFlat r k F N z (0 : Fin r → BlockAlg _ N)
        + ∑ p : GUECoord (Fin r) (N + 1), y p • flatStepDir r k F N z p := by
    rw [show penLFlat r k F N z (∑ p : GUECoord (Fin r) (N + 1),
          y p • blockGUEDir r ((k + 1) + (k + 1)) N p)
        = penLFlat r k F N z 0
          + penLFlatLin k F N z (∑ p : GUECoord (Fin r) (N + 1),
              y p • blockGUEDir r ((k + 1) + (k + 1)) N p) from by
          rw [penLFlatLin]; abel,
      hsum]
  calc flatPencilBlk r k F N z y
      = penLFlat r k F N z (blockGUEBlk r ((k + 1) + (k + 1)) N y) := rfl
    _ = penLFlat r k F N z (∑ p : GUECoord (Fin r) (N + 1),
          y p • blockGUEDir r ((k + 1) + (k + 1)) N p) := by rw [hb]
    _ = penLFlat r k F N z (0 : Fin r → BlockAlg _ N)
          + ∑ p : GUECoord (Fin r) (N + 1), y p • flatStepDir r k F N z p := hmain
    _ = flatPencilBlk r k F N z 0
          + ∑ p : GUECoord (Fin r) (N + 1), y p • flatStepDir r k F N z p := by
        simp only [flatPencilBlk, h0]

end LinPart

/-! ## 4. The coefficient matrices of the flattened pencil -/

section Coeff

variable (k : ℕ) (F : RatPolyIdx r (k + 1)) (N : ℕ)

/-- The coefficient dimension of the flattened pencil: `card (PenIdx wds) * d` with
`d = (k+1)+(k+1)`. -/
def pencilCoeffDim : ℕ :=
  Fintype.card (PenIdx (polyW (h1Poly r k F))) * ((k + 1) + (k + 1))

/-- The coefficient index equivalence, the inverse of `pencilIndexEquiv`. -/
def pencilCoeffIdx : Fin (pencilCoeffDim k F) ≃
    PenIdx (polyW (h1Poly r k F)) × Fin ((k + 1) + (k + 1)) :=
  (pencilIndexEquiv (PenIdx (polyW (h1Poly r k F))) ((k + 1) + (k + 1))).symm

/-- The block-scalar embedding `C ↦ C ⊗ 1` of coefficient matrices into the block algebra. -/
def blockScalar {d N : ℕ} (C : Matrix (Fin d) (Fin d) ℂ) : BlockAlg d N :=
  Matrix.of fun u v => C u v • (1 : CStarMatrix (Fin (N + 1)) (Fin (N + 1)) ℂ)

@[simp] lemma blockScalar_apply {d N : ℕ} (C : Matrix (Fin d) (Fin d) ℂ) (u v : Fin d)
    (s t : Fin (N + 1)) :
    (blockScalar (N := N) C : BlockAlg d N) u v s t = if s = t then C u v else 0 := by
  simp only [blockScalar, Matrix.of_apply, Matrix.smul_apply]
  by_cases h : s = t <;> simp [Matrix.one_apply, h]

@[simp] lemma blockScalar_zero {d N : ℕ} :
    blockScalar (N := N) (0 : Matrix (Fin d) (Fin d) ℂ) = 0 := by
  apply CStarMatrix.ext; intro u v
  apply CStarMatrix.ext; intro s t
  simp

lemma blockScalar_add {d N : ℕ} (C D : Matrix (Fin d) (Fin d) ℂ) :
    blockScalar (N := N) (C + D) = blockScalar C + blockScalar D := by
  apply CStarMatrix.ext; intro u v
  apply CStarMatrix.ext; intro s t
  simp only [blockScalar_apply, Matrix.add_apply]
  by_cases h : s = t <;> simp [h]

lemma blockScalar_neg {d N : ℕ} (C : Matrix (Fin d) (Fin d) ℂ) :
    blockScalar (N := N) (-C) = -blockScalar C := by
  apply CStarMatrix.ext; intro u v
  apply CStarMatrix.ext; intro s t
  simp only [blockScalar_apply, Matrix.neg_apply]
  by_cases h : s = t <;> simp [h]

lemma blockScalar_sub {d N : ℕ} (C D : Matrix (Fin d) (Fin d) ℂ) :
    blockScalar (N := N) (C - D) = blockScalar C - blockScalar D := by
  apply CStarMatrix.ext; intro u v
  apply CStarMatrix.ext; intro s t
  simp only [blockScalar_apply, Matrix.sub_apply]
  by_cases h : s = t <;> simp [h]

lemma blockScalar_smul {d N : ℕ} (c : ℂ) (C : Matrix (Fin d) (Fin d) ℂ) :
    blockScalar (N := N) (c • C) = c • blockScalar C := by
  apply CStarMatrix.ext; intro u v
  apply CStarMatrix.ext; intro s t
  simp only [blockScalar_apply, Matrix.smul_apply]
  by_cases h : s = t <;> simp [h]

@[simp] lemma blockScalar_one {d N : ℕ} :
    blockScalar (N := N) (1 : Matrix (Fin d) (Fin d) ℂ) = 1 := by
  apply CStarMatrix.ext; intro u v
  apply CStarMatrix.ext; intro s t
  simp only [blockScalar_apply, Matrix.one_apply]
  by_cases h : s = t <;> by_cases h2 : u = v <;> simp [h, h2]

lemma blockScalar_star {d N : ℕ} (C : Matrix (Fin d) (Fin d) ℂ) :
    star (blockScalar (N := N) C) = blockScalar (star C) := by
  apply CStarMatrix.ext; intro u v
  apply CStarMatrix.ext; intro s t
  simp only [blockScalar_apply, Matrix.star_apply]
  by_cases h : s = t
  · simp [h]
  · simp [h, Ne.symm h]

/-- The scalar coefficient matrix of a word index of the canonical dilated polynomial. -/
def polyCoeffScalar (j : polyIdx (h1Poly r k F)) :
    Matrix (Fin ((k + 1) + (k + 1))) (Fin ((k + 1) + (k + 1))) ℂ :=
  fun u v => (1 / 2 : ℂ) * polyC (h1Poly r k F) j u v

/-- The word coefficient of the canonical dilated polynomial is a block-scalar matrix. -/
lemma h1Coeff_eq_blockScalar (j : polyIdx (h1Poly r k F)) :
    h1Coeff r k F N j = blockScalar (N := N) (polyCoeffScalar k F j) := by
  ext u v s t
  simp only [h1Coeff, polyCoeffScalar, blockScalar_apply, Matrix.smul_apply, polyCoeff,
    Matrix.of_apply, Algebra.algebraMap_eq_smul_one, Matrix.smul_apply]
  by_cases h : s = t <;> simp [h]

/-- The scalar value of the constant term of the flattened pencil at a coefficient slot. -/
def pencilConstValue (z : ℝ)
    (p q : PenIdx (polyW (h1Poly r k F)) × Fin ((k + 1) + (k + 1))) : ℂ :=
  match p.1, q.1 with
  | Sum.inl _, Sum.inl _ => if p.2 = q.2 then z else 0
  | Sum.inl _, Sum.inr (Sum.inl b) =>
      if (b.2 : ℕ) = 0 then -(1 / 2 : ℂ) * polyC (h1Poly r k F) b.1 p.2 q.2 else 0
  | Sum.inl _, Sum.inr (Sum.inr b) =>
      if (b.2 : ℕ) = (polyW (h1Poly r k F) b.1).length then
        (if p.2 = q.2 then -1 else 0) else 0
  | Sum.inr (Sum.inl a), Sum.inl _ =>
      if (a.2 : ℕ) = 0 then
        -(1 / 2 : ℂ) * star (polyC (h1Poly r k F) a.1 q.2 p.2) else 0
  | Sum.inr (Sum.inr a), Sum.inl _ =>
      if (a.2 : ℕ) = (polyW (h1Poly r k F) a.1).length then
        (if p.2 = q.2 then -1 else 0) else 0
  | Sum.inr (Sum.inl a), Sum.inr (Sum.inr b) =>
      if a = b then (if p.2 = q.2 then 1 else 0) else 0
  | Sum.inr (Sum.inr a), Sum.inr (Sum.inl b) =>
      if a = b then (if p.2 = q.2 then 1 else 0) else 0
  | _, _ => 0

/-- The constant-term coefficient matrix of one block of the flattened pencil. -/
def pencilConstBlock (z : ℝ) (p q : PenIdx (polyW (h1Poly r k F))) :
    Matrix (Fin ((k + 1) + (k + 1))) (Fin ((k + 1) + (k + 1))) ℂ :=
  fun u v => pencilConstValue k F z (p, u) (q, v)

/-- The constant coefficient matrix `A₀` of the flattened pencil. -/
def pencilConstCoeff (z : ℝ) :
    Matrix (Fin (pencilCoeffDim k F)) (Fin (pencilCoeffDim k F)) ℂ :=
  fun x y => pencilConstBlock k F z (pencilCoeffIdx k F x).1 (pencilCoeffIdx k F y).1
    (pencilCoeffIdx k F x).2 (pencilCoeffIdx k F y).2

/-- The direction coefficient matrices `Aᵢ` of the flattened pencil. -/
def pencilDirCoeff (i : Fin r) :
    Matrix (Fin (pencilCoeffDim k F)) (Fin (pencilCoeffDim k F)) ℂ :=
  Matrix.reindex (pencilCoeffIdx k F).symm (pencilCoeffIdx k F).symm
    (flatDirCoeff k F i)

end Coeff

/-! ## 5. The constant term is `A₀ ⊗ 1` -/

section ConstTerm

variable (k : ℕ) (F : RatPolyIdx r (k + 1)) (N : ℕ) (z : ℝ)

/-- `linQMat` at the zero generator tuple is the identity. -/
lemma linQMat_zero {I κ M : Type*} [Ring M] [StarRing M] [Module ℝ M] [StarModule ℝ M]
    [Fintype κ] [DecidableEq κ] (wds : κ → List I) : linQMat (0 : I → M) wds = 1 := by
  rw [linQMat,
    show linQ (0 : I → M) wds
      = (1 : ∀ kk, Matrix (Fin ((wds kk).length + 1)) (Fin ((wds kk).length + 1)) M) from by
        funext kk
        simp [linQ, shiftMatrix_zero_apply],
    blockDiagonal'_one]

/-- `(1/2) * star z = star ((1/2) * z)`. -/
lemma star_half_mul (w : ℂ) : star ((1 / 2 : ℂ) * w) = (1 / 2 : ℂ) * star w := by
  rw [star_mul]
  simp [mul_comm]

/-- At the zero tuple, the bilinear pencil is a block-scalar matrix of coefficient matrices. -/
lemma penL_zero_eq_blockScalar :
    penL (0 : Fin r → BlockAlg ((k + 1) + (k + 1)) N) (polyW (h1Poly r k F))
      (h1Coeff r k F N) (penA0 (0 : BlockAlg ((k + 1) + (k + 1)) N) z)
      = Matrix.of fun p q => blockScalar (N := N) (pencilConstBlock k F z p q) := by
  classical
  ext p q u v s t
  rcases p with a0 | (a1 | a2) <;> rcases q with b0 | (b1 | b2)
  · -- (inl, inl)
    simp only [penL, fromBlocks_apply₁₁, penA0, Matrix.of_apply, sub_zero, blockScalar_apply,
      pencilConstBlock, pencilConstValue, Matrix.smul_apply, Matrix.one_apply]
    by_cases h : s = t <;> by_cases h2 : u = v <;> simp [h, h2]
  · -- (inl, inr (inl b))
    have hval := h1Coeff_eq_blockScalar (r := r) (k := k) (F := F) (N := N) b1.1
    by_cases hb : (b1.2 : ℕ) = 0
    · simp only [penL, fromBlocks_apply₁₂, penE, Matrix.of_apply, linU, dif_pos hb, hval,
        Matrix.neg_apply, blockScalar_apply, pencilConstBlock, pencilConstValue]
      by_cases h : s = t <;> simp [hb, h, hval, polyCoeffScalar]
    · simp only [penL, fromBlocks_apply₁₂, penE, Matrix.of_apply, linU, dif_neg hb,
        blockScalar_zero, Matrix.neg_apply, blockScalar_apply, pencilConstBlock,
        pencilConstValue]
      by_cases h : s = t <;> simp [hb, h]
  · -- (inl, inr (inr b))
    by_cases hb : (b2.2 : ℕ) = (polyW (h1Poly r k F) b2.1).length
    · simp only [penL, fromBlocks_apply₁₂, penE, Matrix.of_apply, linV, dif_pos hb,
        blockScalar_one, star_one, Matrix.neg_apply, blockScalar_apply, pencilConstBlock,
        pencilConstValue]
      by_cases h : s = t <;> by_cases h2 : u = v <;> simp [hb, h, h2]
    · simp only [penL, fromBlocks_apply₁₂, penE, Matrix.of_apply, linV, dif_neg hb,
        blockScalar_zero, star_zero, Matrix.neg_apply, blockScalar_apply, pencilConstBlock,
        pencilConstValue]
      by_cases h : s = t <;> simp [hb, h]
  · -- (inr (inl a), inl)
    have hval := h1Coeff_eq_blockScalar (r := r) (k := k) (F := F) (N := N) a1.1
    have hlinU : linU (polyW (h1Poly r k F)) (h1Coeff r k F N) 0 a1
        = blockScalar (N := N)
            (if (a1.2 : ℕ) = 0 then polyCoeffScalar k F a1.1 else 0) := by
      by_cases ha : (a1.2 : ℕ) = 0
      · simp only [linU, Matrix.of_apply, dif_pos ha, if_pos ha, hval]
      · simp only [linU, Matrix.of_apply, dif_neg ha, if_neg ha, blockScalar_zero]
    simp only [penL, fromBlocks_apply₂₁, penEconj, Matrix.of_apply]
    rw [Matrix.conjTranspose_apply, hlinU, blockScalar_star]
    simp only [Matrix.neg_apply, blockScalar_apply, pencilConstBlock, pencilConstValue,
      polyCoeffScalar, star_half_mul]
    by_cases h : s = t <;> by_cases ha : (a1.2 : ℕ) = 0 <;> simp [h, ha, star_half_mul, polyCoeffScalar]
  · -- (inr (inl a), inr (inl b))
    simp only [penL, fromBlocks_apply₂₂, penB, fromBlocks_apply₁₁, Matrix.of_apply,
      blockScalar_apply, pencilConstBlock, pencilConstValue]
    by_cases h : s = t <;> simp [h]
  · -- (inr (inl a), inr (inr b))
    by_cases hab : a1 = b2
    · subst hab
      simp only [penL, fromBlocks_apply₂₂, penB, fromBlocks_apply₁₂, linQMat_zero,
        conjTranspose_one, Matrix.of_apply, Matrix.one_apply, blockScalar_apply,
        pencilConstBlock, pencilConstValue]
      by_cases h : s = t <;> by_cases h2 : u = v <;> simp [h, h2]
    · simp only [penL, fromBlocks_apply₂₂, penB, fromBlocks_apply₁₂, linQMat_zero,
        conjTranspose_one, Matrix.of_apply, Matrix.one_apply, blockScalar_apply,
        pencilConstBlock, pencilConstValue]
      by_cases h : s = t <;> simp [hab, h]
  · -- (inr (inr a), inl)
    by_cases ha : (a2.2 : ℕ) = (polyW (h1Poly r k F) a2.1).length
    · simp only [penL, fromBlocks_apply₂₁, penEconj, Matrix.of_apply, linV, dif_pos ha,
        blockScalar_one, Matrix.neg_apply, blockScalar_apply, pencilConstBlock,
        pencilConstValue]
      by_cases h : s = t <;> by_cases h2 : u = v <;> simp [ha, h, h2]
    · simp only [penL, fromBlocks_apply₂₁, penEconj, Matrix.of_apply, linV, dif_neg ha,
        blockScalar_zero, Matrix.neg_apply, blockScalar_apply, pencilConstBlock,
        pencilConstValue]
      by_cases h : s = t <;> simp [ha, h]
  · -- (inr (inr a), inr (inl b))
    by_cases hab : a2 = b1
    · subst hab
      simp only [penL, fromBlocks_apply₂₂, penB, fromBlocks_apply₂₁, linQMat_zero,
        Matrix.of_apply, Matrix.one_apply, blockScalar_apply, pencilConstBlock,
        pencilConstValue]
      by_cases h : s = t <;> by_cases h2 : u = v <;> simp [h, h2]
    · simp only [penL, fromBlocks_apply₂₂, penB, fromBlocks_apply₂₁, linQMat_zero,
        Matrix.of_apply, Matrix.one_apply, blockScalar_apply, pencilConstBlock,
        pencilConstValue]
      by_cases h : s = t <;> simp [hab, h]
  · -- (inr (inr a), inr (inr b))
    simp only [penL, fromBlocks_apply₂₂, penB, fromBlocks_apply₂₂, Matrix.of_apply,
      blockScalar_apply, pencilConstBlock, pencilConstValue]
    by_cases h : s = t <;> simp [h]

end ConstTerm


end

end GUEStrongConvergence
