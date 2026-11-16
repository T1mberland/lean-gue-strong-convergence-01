/-
# The sharp direction contraction for the flattened affine pencil

`StrongConvergence/FlattenPencil.lean` reduces Lemma S for the linearization pencils to six
analytic inputs for the flattened statistic `flatStat r k F z N f`; the main analytic one is
`hV` (Lemma V), which `Probability/FlatLemmaV.lean` proves *conditionally* on the deterministic
direction contraction of the flattened pencil.  This file proves that contraction.

## The statement

With `m = pencilFlatDim r k F N`, `X = cfc (deriv f) (flatPencilBlk r k F N z y)` (Hermitian)
and `flatStepDir r k F N z p` the affine slope of the flattened pencil in the Gaussian
coordinate `p`, the contraction is

`∑ p, ‖normTrace (X * flatStepDir r k F N z p)‖² ≤ 2 gueScale(N+1)² G / m² · ‖X‖_F²`

with the explicit `N`-independent constant

`G = flatContractionConst r k F = card (Fin r) · (card (PenIdx wds) · d)²`,

`d = (k+1)+(k+1)`, `wds = polyW (h1Poly r k F)`.

## The proof

1. **The direction family is an insertion of GUE directions.**  The pencil depends on the
   generator tuple only through the shift block (`penL_sub_penL_zero`,
   `penB_sub_penB_zero`), and the shift block is the block-diagonal sum of the shift matrices
   of the individual words.  Consequently the flattened slope in the coordinate
   `p : GUECoord (Fin r) (N+1)` is the matrix

   `flatStepDir r k F N z p = Σ_i (flatDirCoeff k F i) ⊗ gueMatrixCoeff p i`,

   i.e. the GUE direction family `gueDirMatrix (flatDirCoeff k F) p` reindexed along
   `pencilFlatIdx` (`flatStepDir_eq_reindex_gueDirMatrix`).  The coefficient matrices
   `flatDirCoeff k F i` are supported on the shift slots whose letter is `i`, with entries `-1`
   (`flatDirCoeffBlock`).
2. **The exact Hilbert–Schmidt contraction** `sum_sq_trace_direction_le`
   (`Probability/LemmaVSharp.lean`) then gives
   `∑_p ‖Tr(X' · gueDirMatrix C p)‖² ≤ 2 gueScale² (∑_i ‖C_i‖_F²) ‖X'‖_F²` for the
   reindexed `X'`.
3. **The constant.**  Every entry of `flatDirCoeff k F i` has norm at most `1`, so
   `∑_i ‖C_i‖_F² ≤ card (Fin r) · (card (PenIdx wds) · d)² = flatContractionConst r k F`
   (`sum_frob_flatDirCoeff_le`).
4. **Trace and Hilbert–Schmidt invariance under the flattening reindexing** converts the
   pairing `Tr(X · flatStepDir p)` into `Tr(X' · gueDirMatrix C p)`
   (`trace_mul_flatStepDir_eq`), and `‖X'‖_F = ‖X‖_F` (`hsNorm_reindex`).
5. The normalized trace `normTrace` contributes the factor `m⁻²`.

## Consequences

* `sum_sq_normTrace_flatStepDir_le` — the contraction itself.
* `flatLemmaV_hV_unconditional` — Lemma V (`hV`) for the flattened pencil with the
  contraction *discharged*: with `G = flatContractionConst r k F`,
  `Var(τ_N(f(fl 𝓛_z))) ≤ (2G / pencilVDim r k F) / N² · E[τ_N((f')²(fl 𝓛_z))]`
  eventually in `N`.  The other hypotheses (L²/integrability, polynomial growth, positivity
  of the mean) remain the analytic inputs of `flatLemmaV`.

No `sorry`, no new axioms.
-/
import GUEStrongConvergence.Probability.FlatLemmaV
import GUEStrongConvergence.Probability.LemmaVSharp
open Matrix MeasureTheory ProbabilityTheory Filter
open scoped ComplexOrder BigOperators ENNReal NNReal Topology
namespace GUEStrongConvergence
noncomputable section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false
variable {r : ℕ}
variable {k : ℕ} {F : RatPolyIdx r (k + 1)} {N : ℕ} {z : ℝ}


lemma flatten_eq_comp_apply (A : h1An r k F N) (x y : Fin (pencilFlatDim r k F N)) :
    flattenPencilStarAlgEquiv r k F N A x y
      = (Matrix.comp (PenIdx (polyW (h1Poly r k F)) × Fin ((k + 1) + (k + 1)))
          (PenIdx (polyW (h1Poly r k F)) × Fin ((k + 1) + (k + 1)))
          (Fin (N+1)) (Fin (N+1)) ℂ
          (Matrix.comp (PenIdx (polyW (h1Poly r k F))) (PenIdx (polyW (h1Poly r k F)))
            (Fin ((k + 1) + (k + 1))) (Fin ((k + 1) + (k + 1)))
            (CStarMatrix (Fin (N+1)) (Fin (N+1)) ℂ)
            (CStarMatrix.ofMatrixStarAlgEquiv.symm A)))
        ((pencilFlatIdx r k F N).symm x) ((pencilFlatIdx r k F N).symm y) := rfl

lemma flatten_apply_entry (A : h1An r k F N)
    (i j : PenIdx (polyW (h1Poly r k F))) (u v : Fin ((k + 1) + (k + 1)))
    (s t : Fin (N + 1)) :
    flattenPencilStarAlgEquiv r k F N A
        (pencilFlatIdx r k F N ((i, u), s)) (pencilFlatIdx r k F N ((j, v), t))
      = ((A i j) u v) s t := by
  classical
  rw [flatten_eq_comp_apply]
  simp only [Equiv.symm_apply_apply]
  rfl

/-- `flatten` of a difference is the difference of `flatten`s. -/
lemma flatten_sub (A B : h1An r k F N) :
    flattenPencilStarAlgEquiv r k F N (A - B)
      = flattenPencilStarAlgEquiv r k F N A - flattenPencilStarAlgEquiv r k F N B :=
  map_sub _ A B

/-- The block-diagonal embedding, entrywise. -/
lemma blockDiag_apply_entry (a : Matrix (Fin (N+1)) (Fin (N+1)) ℂ)
    (u v : Fin ((k + 1) + (k + 1))) (s t : Fin (N + 1)) :
    (blockDiag (A := Matrix (Fin (N+1)) (Fin (N+1)) ℂ) a :
        BlockAlg ((k+1)+(k+1)) N) u v s t = if u = v then a s t else 0 := by
  show (Matrix.of (fun i j : Fin ((k+1)+(k+1)) => if i = j then a else 0)) u v s t
    = if u = v then a s t else 0
  simp only [Matrix.of_apply]
  split_ifs with h
  · subst h; rfl
  · rfl


section Entry2

variable (k : ℕ) (F : RatPolyIdx r (k + 1)) (N : ℕ)

lemma neg_blockDiag_apply_entry (a : Matrix (Fin (N+1)) (Fin (N+1)) ℂ)
    (u v : Fin ((k + 1) + (k + 1))) (s t : Fin (N + 1)) :
    (-blockDiag (A := Matrix (Fin (N+1)) (Fin (N+1)) ℂ) a :
        BlockAlg ((k+1)+(k+1)) N) u v s t = -(if u = v then a s t else 0) := by
  show (-((blockDiag (A := Matrix (Fin (N+1)) (Fin (N+1)) ℂ) a :
      BlockAlg ((k+1)+(k+1)) N) u v)) s t = -(if u = v then a s t else 0)
  rw [show (blockDiag (A := Matrix (Fin (N+1)) (Fin (N+1)) ℂ) a :
      BlockAlg ((k+1)+(k+1)) N) u v = if u = v then a else 0 from rfl]
  split_ifs with h
  · rfl
  · rfl

lemma blockDiag_apply_entry_ne (a : Matrix (Fin (N+1)) (Fin (N+1)) ℂ)
    {u v : Fin ((k + 1) + (k + 1))} (h : u ≠ v) (s t : Fin (N + 1)) :
    (blockDiag (A := Matrix (Fin (N+1)) (Fin (N+1)) ℂ) a :
        BlockAlg ((k+1)+(k+1)) N) u v s t = 0 := by
  rw [show (blockDiag (A := Matrix (Fin (N+1)) (Fin (N+1)) ℂ) a :
      BlockAlg ((k+1)+(k+1)) N) u v = (if u = v then a else 0) from rfl, if_neg h]
  rfl

end Entry2

section LinQ
variable {M : Type*} [Ring M] [StarRing M] [Module ℝ M] [StarModule ℝ M] {I κ : Type*}
  [Fintype κ] [DecidableEq κ]

lemma linQMat_sub_eq (x : I → M) (wds : κ → List I) :
    linQMat x wds - linQMat (0 : I → M) wds
      = blockDiagonal' (fun k => -(shiftMatrix x (wds k))) := by
  rw [linQMat, linQMat, ← blockDiagonal'_sub]
  congr 1
  funext k
  simp only [Pi.sub_apply, linQ, shiftMatrix_zero_apply (wds k), sub_zero]
  abel

lemma linQMat_sub_apply_eq (x : I → M) (wds : κ → List I) (k : κ)
    (i j : Fin ((wds k).length + 1)) :
    (linQMat x wds - linQMat (0 : I → M) wds) ⟨k, i⟩ ⟨k, j⟩ = -(shiftMatrix x (wds k)) i j := by
  rw [linQMat_sub_eq, blockDiagonal'_apply_eq]
  rfl

lemma linQMat_sub_apply_ne (x : I → M) (wds : κ → List I) {k k' : κ} (h : k ≠ k')
    (i : Fin ((wds k).length + 1)) (j : Fin ((wds k').length + 1)) :
    (linQMat x wds - linQMat (0 : I → M) wds) ⟨k, i⟩ ⟨k', j⟩ = 0 := by
  rw [linQMat_sub_eq]
  exact blockDiagonal'_apply_ne _ _ _ h

end LinQ

section PencilDir

variable (k : ℕ) (F : RatPolyIdx r (k + 1)) (N : ℕ) (z : ℝ)

def pencilDir (x : Fin r → BlockAlg ((k+1)+(k+1)) N) :
    Matrix (PenIdx (polyW (h1Poly r k F))) (PenIdx (polyW (h1Poly r k F)))
      (BlockAlg ((k+1)+(k+1)) N) :=
  penL x (polyW (h1Poly r k F)) (h1Coeff r k F N)
      (penA0 (0 : BlockAlg ((k+1)+(k+1)) N) z)
    - penL (0 : Fin r → BlockAlg ((k+1)+(k+1)) N) (polyW (h1Poly r k F))
      (h1Coeff r k F N) (penA0 (0 : BlockAlg ((k+1)+(k+1)) N) z)


lemma flatStepDir_eq_flatten (p : GUECoord (Fin r) (N+1)) :
    flatStepDir r k F N z p
      = flattenPencilStarAlgEquiv r k F N
          (pencilDir k F N z (blockGUEDir r ((k+1)+(k+1)) N p)) := by
  rw [flatStepDir, penLFlat, penLFlat, pencilDir, map_sub]

lemma pencilDir_eq_blocks (x : Fin r → BlockAlg ((k+1)+(k+1)) N) :
    pencilDir k F N z x = fromBlocks (0 : Matrix (Fin 1) (Fin 1) (BlockAlg _ N)) 0 0
      (penB x (polyW (h1Poly r k F)) - penB (0 : Fin r → BlockAlg ((k+1)+(k+1)) N)
        (polyW (h1Poly r k F))) :=
  penL_sub_penL_zero x _ _ _

lemma penB_sub_apply_inr_inl (x : Fin r → BlockAlg ((k+1)+(k+1)) N) (a b : BlkIdx (polyW (h1Poly r k F))) :
    (penB x (polyW (h1Poly r k F)) - penB (0 : Fin r → BlockAlg ((k+1)+(k+1)) N)
        (polyW (h1Poly r k F))) (Sum.inr a) (Sum.inl b)
      = ((linQMat x (polyW (h1Poly r k F))
          - linQMat (0 : Fin r → BlockAlg ((k+1)+(k+1)) N) (polyW (h1Poly r k F))) a b) := by
  rw [penB_sub_penB_zero]
  rfl

lemma penB_sub_apply_inl_inr (x : Fin r → BlockAlg ((k+1)+(k+1)) N) (a b : BlkIdx (polyW (h1Poly r k F))) :
    (penB x (polyW (h1Poly r k F)) - penB (0 : Fin r → BlockAlg ((k+1)+(k+1)) N)
        (polyW (h1Poly r k F))) (Sum.inl a) (Sum.inr b)
      = star (((linQMat x (polyW (h1Poly r k F))
          - linQMat (0 : Fin r → BlockAlg ((k+1)+(k+1)) N) (polyW (h1Poly r k F))) b a)) := by
  rw [penB_sub_penB_zero]
  show ((linQMat x (polyW (h1Poly r k F)))ᴴ
      - (linQMat (0 : Fin r → BlockAlg ((k+1)+(k+1)) N) (polyW (h1Poly r k F)))ᴴ) a b
    = star (((linQMat x (polyW (h1Poly r k F))
      - linQMat (0 : Fin r → BlockAlg ((k+1)+(k+1)) N) (polyW (h1Poly r k F))) b a))
  simp only [Matrix.sub_apply, Matrix.conjTranspose_apply, star_sub]

lemma pencilDir_entry_inr_inr_inl (x : Fin r → BlockAlg ((k+1)+(k+1)) N)
    (a b : BlkIdx (polyW (h1Poly r k F))) (u v : Fin ((k+1)+(k+1))) (s t : Fin (N+1)) :
    ((pencilDir k F N z x) (Sum.inr (Sum.inr a)) (Sum.inr (Sum.inl b))) u v s t
      = (((linQMat x (polyW (h1Poly r k F))
          - linQMat (0 : Fin r → BlockAlg ((k+1)+(k+1)) N) (polyW (h1Poly r k F))) a b)) u v s t := by
  rw [pencilDir_eq_blocks]
  rw [show (fromBlocks (0 : Matrix (Fin 1) (Fin 1) (BlockAlg _ N)) 0 0
      (penB x (polyW (h1Poly r k F)) - penB (0 : Fin r → BlockAlg ((k+1)+(k+1)) N)
        (polyW (h1Poly r k F)))) (Sum.inr (Sum.inr a)) (Sum.inr (Sum.inl b))
      = (penB x (polyW (h1Poly r k F)) - penB (0 : Fin r → BlockAlg ((k+1)+(k+1)) N)
        (polyW (h1Poly r k F))) (Sum.inr a) (Sum.inl b) from rfl]
  rw [penB_sub_apply_inr_inl]

lemma pencilDir_entry_inr_inl_inr (x : Fin r → BlockAlg ((k+1)+(k+1)) N)
    (a b : BlkIdx (polyW (h1Poly r k F))) (u v : Fin ((k+1)+(k+1))) (s t : Fin (N+1)) :
    ((pencilDir k F N z x) (Sum.inr (Sum.inl a)) (Sum.inr (Sum.inr b))) u v s t
      = (star (((linQMat x (polyW (h1Poly r k F))
          - linQMat (0 : Fin r → BlockAlg ((k+1)+(k+1)) N) (polyW (h1Poly r k F))) b a))) u v s t := by
  rw [pencilDir_eq_blocks]
  rw [show (fromBlocks (0 : Matrix (Fin 1) (Fin 1) (BlockAlg _ N)) 0 0
      (penB x (polyW (h1Poly r k F)) - penB (0 : Fin r → BlockAlg ((k+1)+(k+1)) N)
        (polyW (h1Poly r k F)))) (Sum.inr (Sum.inl a)) (Sum.inr (Sum.inr b))
      = (penB x (polyW (h1Poly r k F)) - penB (0 : Fin r → BlockAlg ((k+1)+(k+1)) N)
        (polyW (h1Poly r k F))) (Sum.inl a) (Sum.inr b) from rfl]
  rw [penB_sub_apply_inl_inr]


lemma pencilDir_apply_zero_left (a0 : Fin 1) (b : PenIdx (polyW (h1Poly r k F))) :
    pencilDir k F N z x (Sum.inl a0) b = 0 := by
  rw [pencilDir_eq_blocks]
  rcases b with b0 | (b1 | b1) <;> simp [fromBlocks]

lemma pencilDir_apply_zero_right (a : PenIdx (polyW (h1Poly r k F))) (b0 : Fin 1) :
    pencilDir k F N z x a (Sum.inl b0) = 0 := by
  rw [pencilDir_eq_blocks]
  rcases a with a0 | (a1 | a1) <;> simp [fromBlocks]

lemma pencilDir_apply_inr_inr_inr (a b : BlkIdx (polyW (h1Poly r k F))) :
    pencilDir k F N z x (Sum.inr (Sum.inr a)) (Sum.inr (Sum.inr b)) = 0 := by
  rw [pencilDir_eq_blocks, penB_sub_penB_zero]
  simp [fromBlocks]

lemma pencilDir_apply_inr_inl_inl (a b : BlkIdx (polyW (h1Poly r k F))) :
    pencilDir k F N z x (Sum.inr (Sum.inl a)) (Sum.inr (Sum.inl b)) = 0 := by
  rw [pencilDir_eq_blocks, penB_sub_penB_zero]
  simp [fromBlocks]

end PencilDir

section Coeff

variable (k : ℕ) (F : RatPolyIdx r (k + 1)) (N : ℕ)

/-- The block-level coefficient of the flattened direction: `-1` on the shift slots
carrying the letter `i`. -/
def flatDirCoeffBlock (i : Fin r) (a b : BlkIdx (polyW (h1Poly r k F))) : ℂ :=
  if h : a.1 = b.1 ∧ (a.2 : ℕ) + 1 = (b.2 : ℕ) then
    (if (polyW (h1Poly r k F) a.1).get ⟨a.2, by
        have hb : (b.2 : ℕ) < (polyW (h1Poly r k F) b.1).length + 1 := b.2.isLt
        have hlen : (polyW (h1Poly r k F) a.1).length
            = (polyW (h1Poly r k F) b.1).length := by rw [h.1]
        omega⟩ = i then -1 else 0)
  else 0

/-- The coefficient matrix of the flattened pencil direction family. -/
def flatDirCoeff (i : Fin r) :
    Matrix (PenIdx (polyW (h1Poly r k F)) × Fin ((k+1)+(k+1)))
      (PenIdx (polyW (h1Poly r k F)) × Fin ((k+1)+(k+1))) ℂ :=
  fun x y =>
    if x.2 = y.2 then
      (match x.1, y.1 with
       | Sum.inr (Sum.inr a), Sum.inr (Sum.inl b) => flatDirCoeffBlock k F i a b
       | Sum.inr (Sum.inl a), Sum.inr (Sum.inr b) => flatDirCoeffBlock k F i b a
       | _, _ => 0)
    else 0


end Coeff

section DirEntry

variable (k : ℕ) (F : RatPolyIdx r (k + 1)) (N : ℕ) (z : ℝ)
  (p : GUECoord (Fin r) (N+1))

lemma shiftMatrix_dir_entry (kk : polyIdx (h1Poly r k F))
    (r1 r2 : Fin ((polyW (h1Poly r k F) kk).length + 1))
    (u v : Fin ((k+1)+(k+1))) (s t : Fin (N+1)) :
    (shiftMatrix (blockGUEDir r ((k+1)+(k+1)) N p) (polyW (h1Poly r k F) kk)) r1 r2 u v s t
      = if h : (r1 : ℕ) + 1 = (r2 : ℕ) then
          (if u = v then gueMatrixCoeff p
            ((polyW (h1Poly r k F) kk).get ⟨r1, by omega⟩) s t else 0)
        else 0 := by
  by_cases h : (r1 : ℕ) + 1 = (r2 : ℕ) <;> by_cases h2 : u = v <;>
    simp [shiftMatrix_apply, h, h2, blockGUEDir, blockDiag_apply_entry, gueMatrixDir]

lemma pencilDir_dir_entry_inr_inr_inl (kk : polyIdx (h1Poly r k F))
    (r1 r2 : Fin ((polyW (h1Poly r k F) kk).length + 1))
    (u v : Fin ((k+1)+(k+1))) (s t : Fin (N+1)) :
    ((pencilDir k F N z (blockGUEDir r ((k+1)+(k+1)) N p))
        (Sum.inr (Sum.inr ⟨kk, r1⟩)) (Sum.inr (Sum.inl ⟨kk, r2⟩))) u v s t
      = if h : (r1 : ℕ) + 1 = (r2 : ℕ) then
          -(if u = v then gueMatrixCoeff p
            ((polyW (h1Poly r k F) kk).get ⟨r1, by omega⟩) s t else 0)
        else 0 := by
  rw [pencilDir_entry_inr_inr_inl, linQMat_sub_apply_eq,
    show (-(shiftMatrix (blockGUEDir r ((k+1)+(k+1)) N p) (polyW (h1Poly r k F) kk)) r1 r2) u v s t
      = -((shiftMatrix (blockGUEDir r ((k+1)+(k+1)) N p) (polyW (h1Poly r k F) kk)) r1 r2 u v s t)
      from rfl]
  rw [shiftMatrix_dir_entry]
  by_cases h : (r1 : ℕ) + 1 = (r2 : ℕ) <;> by_cases h2 : u = v <;> simp [h, h2]

lemma star_apply_apply_blockAlg (X : BlockAlg ((k+1)+(k+1)) N)
    (u v : Fin ((k+1)+(k+1))) (s t : Fin (N+1)) :
    (star X) u v s t = star (X v u t s) := by
  rw [Matrix.star_apply, Matrix.star_apply]


lemma penA0_zero_star :
    (penA0 (0 : BlockAlg ((k+1)+(k+1)) N) z)ᴴ = penA0 (0 : BlockAlg ((k+1)+(k+1)) N) z := by
  ext i j
  fin_cases i; fin_cases j
  simp [penA0]

lemma penL_dir_star (x : Fin r → BlockAlg ((k+1)+(k+1)) N) :
    star (penL x (polyW (h1Poly r k F)) (h1Coeff r k F N)
        (penA0 (0 : BlockAlg ((k+1)+(k+1)) N) z))
      = penL x (polyW (h1Poly r k F)) (h1Coeff r k F N)
        (penA0 (0 : BlockAlg ((k+1)+(k+1)) N) z) := by
  rw [Matrix.star_eq_conjTranspose, penL_conjTranspose, penA0_zero_star]

lemma pencilDir_star (x : Fin r → BlockAlg ((k+1)+(k+1)) N) :
    star (pencilDir k F N z x) = pencilDir k F N z x := by
  simp only [pencilDir, star_sub, penL_dir_star]

lemma pencilDir_dir_entry_inr_inl_inr (kk : polyIdx (h1Poly r k F))
    (r1 r2 : Fin ((polyW (h1Poly r k F) kk).length + 1))
    (u v : Fin ((k+1)+(k+1))) (s t : Fin (N+1)) :
    ((pencilDir k F N z (blockGUEDir r ((k+1)+(k+1)) N p))
        (Sum.inr (Sum.inl ⟨kk, r1⟩)) (Sum.inr (Sum.inr ⟨kk, r2⟩))) u v s t
      = if h : (r2 : ℕ) + 1 = (r1 : ℕ) then
          -(if u = v then gueMatrixCoeff p
            ((polyW (h1Poly r k F) kk).get ⟨r2, by omega⟩) s t else 0)
        else 0 := by
  rw [show ((pencilDir k F N z (blockGUEDir r ((k+1)+(k+1)) N p))
        (Sum.inr (Sum.inl ⟨kk, r1⟩)) (Sum.inr (Sum.inr ⟨kk, r2⟩))) u v s t
      = star (((pencilDir k F N z (blockGUEDir r ((k+1)+(k+1)) N p))
        (Sum.inr (Sum.inr ⟨kk, r2⟩)) (Sum.inr (Sum.inl ⟨kk, r1⟩))) v u t s) from by
    conv_lhs => rw [← pencilDir_star k F N z (blockGUEDir r ((k+1)+(k+1)) N p)]
    rw [← star_apply_apply_blockAlg]
    rfl]
  rw [pencilDir_dir_entry_inr_inr_inl]
  by_cases h : (r2 : ℕ) + 1 = (r1 : ℕ) <;> by_cases h2 : u = v <;>
    simp [h, h2, star_gueMatrixCoeff, eq_comm]


lemma gueMatrixCoeff_eq_zero_of_ne (p : GUECoord (Fin r) (N+1)) {i : Fin r} (h : i ≠ p.1)
    (a b : Fin (N+1)) : gueMatrixCoeff p i a b = 0 := by
  have h1 : (i, (a, b)) ≠ p := fun hp => h (congrArg Prod.fst hp)
  have h2 : (i, (b, a)) ≠ p := fun hp => h (congrArg Prod.fst hp)
  simp [gueMatrixCoeff, h1, h2]

lemma pencilDir_dir_entry_inr_inr_inl_ne (kk kk' : polyIdx (h1Poly r k F)) (h : kk ≠ kk')
    (r1 : Fin ((polyW (h1Poly r k F) kk).length + 1))
    (r2 : Fin ((polyW (h1Poly r k F) kk').length + 1))
    (u v : Fin ((k+1)+(k+1))) (s t : Fin (N+1)) :
    ((pencilDir k F N z (blockGUEDir r ((k+1)+(k+1)) N p))
        (Sum.inr (Sum.inr ⟨kk, r1⟩)) (Sum.inr (Sum.inl ⟨kk', r2⟩))) u v s t = 0 := by
  rw [pencilDir_entry_inr_inr_inl, linQMat_sub_apply_ne _ _ h]
  rfl

lemma pencilDir_dir_entry_inr_inl_inr_ne (kk kk' : polyIdx (h1Poly r k F)) (h : kk ≠ kk')
    (r1 : Fin ((polyW (h1Poly r k F) kk).length + 1))
    (r2 : Fin ((polyW (h1Poly r k F) kk').length + 1))
    (u v : Fin ((k+1)+(k+1))) (s t : Fin (N+1)) :
    ((pencilDir k F N z (blockGUEDir r ((k+1)+(k+1)) N p))
        (Sum.inr (Sum.inl ⟨kk, r1⟩)) (Sum.inr (Sum.inr ⟨kk', r2⟩))) u v s t = 0 := by
  rw [pencilDir_entry_inr_inl_inr, linQMat_sub_apply_ne _ _ (Ne.symm h)]
  simp

lemma flatDirCoeff_inr_inr_inl (i : Fin r) (a b : BlkIdx (polyW (h1Poly r k F)))
    (u v : Fin ((k+1)+(k+1))) :
    flatDirCoeff k F i (Sum.inr (Sum.inr a), u) (Sum.inr (Sum.inl b), v)
      = if u = v then flatDirCoeffBlock k F i a b else 0 := by
  simp [flatDirCoeff]

lemma flatDirCoeff_inr_inl_inr (i : Fin r) (a b : BlkIdx (polyW (h1Poly r k F)))
    (u v : Fin ((k+1)+(k+1))) :
    flatDirCoeff k F i (Sum.inr (Sum.inl a), u) (Sum.inr (Sum.inr b), v)
      = if u = v then flatDirCoeffBlock k F i b a else 0 := by
  simp [flatDirCoeff]

lemma flatDirCoeff_zero_l (i : Fin r) (a : Fin 1) (b : PenIdx (polyW (h1Poly r k F)))
    (u v : Fin ((k+1)+(k+1))) :
    flatDirCoeff k F i (Sum.inl a, u) (b, v) = 0 := by
  obtain ⟨b, rfl⟩ : ∃ b', b = b' := ⟨b, rfl⟩
  rcases b with b0 | (b1 | b1) <;> simp [flatDirCoeff]

lemma flatDirCoeff_zero_r (i : Fin r) (a : PenIdx (polyW (h1Poly r k F))) (b : Fin 1)
    (u v : Fin ((k+1)+(k+1))) :
    flatDirCoeff k F i (a, u) (Sum.inl b, v) = 0 := by
  rcases a with a0 | (a1 | a1) <;> simp [flatDirCoeff]

lemma flatDirCoeff_inr_inr_inr (i : Fin r) (a b : BlkIdx (polyW (h1Poly r k F)))
    (u v : Fin ((k+1)+(k+1))) :
    flatDirCoeff k F i (Sum.inr (Sum.inr a), u) (Sum.inr (Sum.inr b), v) = 0 := by
  simp [flatDirCoeff]

lemma flatDirCoeff_inr_inl_inl (i : Fin r) (a b : BlkIdx (polyW (h1Poly r k F)))
    (u v : Fin ((k+1)+(k+1))) :
    flatDirCoeff k F i (Sum.inr (Sum.inl a), u) (Sum.inr (Sum.inl b), v) = 0 := by
  simp [flatDirCoeff]


lemma flatDirCoeffBlock_eq_zero_of_ne (i : Fin r) {a b : BlkIdx (polyW (h1Poly r k F))}
    (h : a.1 ≠ b.1) : flatDirCoeffBlock k F i a b = 0 := by
  simp [flatDirCoeffBlock, h]

lemma pencilDir_entry_eq_sum (p : GUECoord (Fin r) (N+1))
    (a b : PenIdx (polyW (h1Poly r k F))) (u v : Fin ((k+1)+(k+1))) (s t : Fin (N+1)) :
    ((pencilDir k F N z (blockGUEDir r ((k+1)+(k+1)) N p)) a b) u v s t
      = ∑ i : Fin r, flatDirCoeff k F i (a, u) (b, v) * gueMatrixCoeff p i s t := by
  rw [Finset.sum_eq_single p.1]
  · rcases a with a0 | (a1 | a1)
    · rw [pencilDir_apply_zero_left, flatDirCoeff_zero_l]
      simp
    · rcases b with b0 | (b1 | b1)
      · rw [pencilDir_apply_zero_right, flatDirCoeff_zero_r]
        simp
      · rw [pencilDir_apply_inr_inl_inl, flatDirCoeff_inr_inl_inl]
        simp
      · obtain ⟨kk1, r1⟩ := a1
        obtain ⟨kk2, r2⟩ := b1
        by_cases hkk : kk1 = kk2
        · subst hkk
          rw [pencilDir_dir_entry_inr_inl_inr, flatDirCoeff_inr_inl_inr]
          by_cases h : (r2 : ℕ) + 1 = (r1 : ℕ)
          · rw [dif_pos h]
            by_cases h2 : u = v
            · rw [if_pos h2]
              have hp : (r2 : ℕ) < (polyW (h1Poly r k F) kk1).length := by
                have := r1.isLt; omega
              rw [show ((polyW (h1Poly r k F) kk1).get ⟨r2, by omega⟩)
                  = ((polyW (h1Poly r k F) kk1).get ⟨r2, hp⟩) from by simp]
              rw [flatDirCoeffBlock, dif_pos ⟨rfl, h⟩]
              by_cases hl : ((polyW (h1Poly r k F) kk1).get ⟨r2, hp⟩) = p.1
              · rw [if_pos hl, if_pos h2, hl]; ring
              · rw [if_neg hl, if_pos h2]
                have h1 : ((polyW (h1Poly r k F) kk1).get ⟨r2, hp⟩, (s, t)) ≠ p :=
                  fun hp' => hl (congrArg Prod.fst hp')
                have h2' : ((polyW (h1Poly r k F) kk1).get ⟨r2, hp⟩, (t, s)) ≠ p :=
                  fun hp' => hl (congrArg Prod.fst hp')
                rw [gueMatrixCoeff, if_neg h1, if_neg h2']
                simp
            · rw [if_neg h2, if_neg h2]; simp
          · rw [dif_neg h]
            rw [flatDirCoeffBlock, dif_neg (fun hh => h hh.2)]
            by_cases h2 : u = v <;> simp [h2]
        · rw [pencilDir_dir_entry_inr_inl_inr_ne (kk := kk1) (kk' := kk2) (h := hkk)]
          rw [flatDirCoeff_inr_inl_inr, flatDirCoeffBlock_eq_zero_of_ne (k := k) (F := F) (i := p.1) (h := Ne.symm hkk)]
          simp
    · rcases b with b0 | (b1 | b1)
      · rw [pencilDir_apply_zero_right, flatDirCoeff_zero_r]
        simp
      · cases a1 with
        | mk kk1 r1 =>
        cases b1 with
        | mk kk2 r2 =>
        by_cases hkk : kk1 = kk2
        · subst hkk
          rw [pencilDir_dir_entry_inr_inr_inl, flatDirCoeff_inr_inr_inl]
          by_cases h : (r1 : ℕ) + 1 = (r2 : ℕ)
          · rw [dif_pos h]
            by_cases h2 : u = v
            · rw [if_pos h2]
              have hp : (r1 : ℕ) < (polyW (h1Poly r k F) kk1).length := by
                have := r2.isLt; omega
              rw [show ((polyW (h1Poly r k F) kk1).get ⟨r1, by omega⟩)
                  = ((polyW (h1Poly r k F) kk1).get ⟨r1, hp⟩) from by simp]
              rw [flatDirCoeffBlock, dif_pos ⟨rfl, h⟩]
              by_cases hl : ((polyW (h1Poly r k F) kk1).get ⟨r1, hp⟩) = p.1
              · rw [if_pos hl, if_pos h2, hl]; ring
              · rw [if_neg hl, if_pos h2]
                have h1 : ((polyW (h1Poly r k F) kk1).get ⟨r1, hp⟩, (s, t)) ≠ p :=
                  fun hp' => hl (congrArg Prod.fst hp')
                have h2' : ((polyW (h1Poly r k F) kk1).get ⟨r1, hp⟩, (t, s)) ≠ p :=
                  fun hp' => hl (congrArg Prod.fst hp')
                rw [gueMatrixCoeff, if_neg h1, if_neg h2']
                simp
            · rw [if_neg h2, if_neg h2]; simp
          · rw [dif_neg h]
            rw [flatDirCoeffBlock, dif_neg (fun hh => h hh.2)]
            by_cases h2 : u = v <;> simp [h2]
        · rw [pencilDir_dir_entry_inr_inr_inl_ne (kk := kk1) (kk' := kk2) (h := hkk)]
          rw [flatDirCoeff_inr_inr_inl, flatDirCoeffBlock_eq_zero_of_ne (k := k) (F := F) (i := p.1) (h := hkk)]
          simp
      · rw [pencilDir_apply_inr_inr_inr, flatDirCoeff_inr_inr_inr]
        simp
  · intro i _ hi
    have h1 : (i, (s, t)) ≠ p := fun hp => hi (congrArg Prod.fst hp)
    have h2 : (i, (t, s)) ≠ p := fun hp => hi (congrArg Prod.fst hp)
    rw [gueMatrixCoeff, if_neg h1, if_neg h2]
    simp
  · intro h; exact absurd (Finset.mem_univ _) h

end DirEntry

lemma trace_reindex_eq {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (e : m ≃ n) (A : Matrix m m ℂ) :
    Matrix.trace (Matrix.reindex e e A) = Matrix.trace A := by
  rw [Matrix.trace, Matrix.trace]
  simp only [Matrix.diag_apply, Matrix.reindex_apply, Matrix.submatrix_apply,
    Equiv.symm_apply_apply]
  exact Fintype.sum_equiv e.symm _ _ (fun x => rfl)

lemma hsNorm_eq_sum_prod {o : Type*} [Fintype o] (A : Matrix o o ℂ) :
    hsNorm A = ∑ x : o × o, ‖A x.1 x.2‖ ^ 2 := by
  rw [hsNorm, Fintype.sum_prod_type]

lemma hsNorm_reindex {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (e : m ≃ n) (A : Matrix m m ℂ) :
    hsNorm (Matrix.reindex e e A) = hsNorm A := by
  rw [hsNorm_eq_sum_prod, hsNorm_eq_sum_prod]
  refine (Fintype.sum_equiv (e.prodCongr e) (fun x : m × m => ‖A x.1 x.2‖ ^ 2)
    (fun x : n × n => ‖(Matrix.reindex e e A) x.1 x.2‖ ^ 2) ?_).symm
  intro x
  simp [Matrix.reindex_apply]



section Bridge

variable (k : ℕ) (F : RatPolyIdx r (k + 1)) (N : ℕ) (z : ℝ)

local instance : DecidableEq (PenIdx (polyW (h1Poly r k F))) := Classical.decEq _
local instance : DecidableEq (PenIdx (polyW (h1Poly r k F)) × Fin ((k+1)+(k+1))) :=
  Classical.decEq _
local instance : DecidableEq ((PenIdx (polyW (h1Poly r k F)) × Fin ((k+1)+(k+1))) × Fin (N+1)) :=
  Classical.decEq _

lemma reindex_mul_apply {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (e : m ≃ n) (A B : Matrix m m ℂ) :
    Matrix.reindex e e A * Matrix.reindex e e B = Matrix.reindex e e (A * B) := by
  simp only [Matrix.reindex_apply]
  exact Matrix.submatrix_mul_equiv A B e.symm e.symm e.symm

theorem reindex_symm_flatStepDir_eq_gueDirMatrix (p : GUECoord (Fin r) (N+1)) :
    Matrix.reindex (pencilFlatIdx r k F N).symm (pencilFlatIdx r k F N).symm
        (flatStepDir r k F N z p) = gueDirMatrix (flatDirCoeff k F) p := by
  classical
  ext ⟨⟨a, u⟩, s⟩ ⟨⟨b, v⟩, t⟩
  rw [Matrix.reindex_apply, Equiv.symm_symm]
  rw [flatStepDir_eq_flatten]
  simp only [Matrix.submatrix_apply]
  rw [flatten_apply_entry]
  exact pencilDir_entry_eq_sum k F N z p a b u v s t

theorem flatStepDir_eq_reindex_gueDirMatrix (p : GUECoord (Fin r) (N+1)) :
    flatStepDir r k F N z p
      = Matrix.reindex (pencilFlatIdx r k F N) (pencilFlatIdx r k F N)
          (gueDirMatrix (flatDirCoeff k F) p) := by
  rw [show flatStepDir r k F N z p
      = Matrix.reindex (pencilFlatIdx r k F N) (pencilFlatIdx r k F N)
          (Matrix.reindex (pencilFlatIdx r k F N).symm (pencilFlatIdx r k F N).symm
            (flatStepDir r k F N z p)) from by
    simp [Matrix.reindex_apply]]
  rw [reindex_symm_flatStepDir_eq_gueDirMatrix]

lemma trace_mul_flatStepDir_eq (p : GUECoord (Fin r) (N+1))
    (X : Matrix (Fin (pencilFlatDim r k F N)) (Fin (pencilFlatDim r k F N)) ℂ) :
    Matrix.trace (X * flatStepDir r k F N z p)
      = Matrix.trace (Matrix.reindex (pencilFlatIdx r k F N).symm (pencilFlatIdx r k F N).symm X
          * gueDirMatrix (flatDirCoeff k F) p) := by
  rw [flatStepDir_eq_reindex_gueDirMatrix]
  conv_lhs => rw [show X = Matrix.reindex (pencilFlatIdx r k F N) (pencilFlatIdx r k F N)
      (Matrix.reindex (pencilFlatIdx r k F N).symm (pencilFlatIdx r k F N).symm X) from by
    simp [Matrix.reindex_apply]]
  rw [reindex_mul_apply, trace_reindex_eq]

end Bridge


section Contraction

variable (k : ℕ) (F : RatPolyIdx r (k + 1)) (N : ℕ) (z : ℝ)

/-- The explicit amplification constant of the flattened direction family: the number of
letters times the square of the coefficient-matrix dimension. -/
def flatContractionConst (r k : ℕ) (F : RatPolyIdx r (k + 1)) : ℝ :=
  (r : ℝ) * (((Fintype.card (PenIdx (polyW (h1Poly r k F))) : ℝ)
    * (((k+1)+(k+1)) : ℝ)) ^ 2)

lemma flatDirCoeff_norm_le_one (i : Fin r)
    (x y : PenIdx (polyW (h1Poly r k F)) × Fin ((k+1)+(k+1))) :
    ‖flatDirCoeff k F i x y‖ ≤ 1 := by
  rcases x with ⟨a, u⟩
  rcases y with ⟨b, v⟩
  rcases a with a0 | (a1 | a1) <;> rcases b with b0 | (b1 | b1) <;>
    simp only [flatDirCoeff]
  all_goals try split_ifs with h
  all_goals
    try simp only [flatDirCoeffBlock]
    try split_ifs with h2
    all_goals try split_ifs with h3
    all_goals norm_num

lemma sum_frob_flatDirCoeff_le :
    (∑ i : Fin r, (frob (flatDirCoeff k F i)) ^ 2) ≤ flatContractionConst r k F := by
  have hcard : (Fintype.card (PenIdx (polyW (h1Poly r k F)) × Fin ((k+1)+(k+1))) : ℝ)
      = (Fintype.card (PenIdx (polyW (h1Poly r k F))) : ℝ) * (((k+1)+(k+1)) : ℝ) := by
    rw [Fintype.card_prod, Fintype.card_fin]
    push_cast
    ring
  have hterm : ∀ i : Fin r, (frob (flatDirCoeff k F i)) ^ 2
      ≤ ((Fintype.card (PenIdx (polyW (h1Poly r k F))) : ℝ)
          * (((k+1)+(k+1)) : ℝ)) ^ 2 := by
    intro i
    rw [frob_sq]
    calc (∑ x, ∑ y, ‖flatDirCoeff k F i x y‖ ^ 2)
        ≤ ∑ x, ∑ y, (1 : ℝ) := by
          refine Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => ?_
          exact pow_le_one₀ (norm_nonneg _) (flatDirCoeff_norm_le_one k F i x y)
      _ = (Fintype.card (PenIdx (polyW (h1Poly r k F)) × Fin ((k+1)+(k+1))) : ℝ) ^ 2 := by
          simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          ring
      _ = ((Fintype.card (PenIdx (polyW (h1Poly r k F))) : ℝ) * (((k+1)+(k+1)) : ℝ)) ^ 2 := by
          rw [hcard]
  calc (∑ i : Fin r, (frob (flatDirCoeff k F i)) ^ 2)
      ≤ ∑ _i : Fin r, ((Fintype.card (PenIdx (polyW (h1Poly r k F))) : ℝ)
          * (((k+1)+(k+1)) : ℝ)) ^ 2 := Finset.sum_le_sum fun i _ => hterm i
    _ = flatContractionConst r k F := by
        rw [Finset.sum_const, Finset.card_fin, nsmul_eq_mul, flatContractionConst]

end Contraction


section FinalContraction

variable (k : ℕ) (F : RatPolyIdx r (k + 1)) (N : ℕ) (z : ℝ)

lemma pencilFlatDim_pos_real : (0 : ℝ) < (pencilFlatDim r k F N : ℝ) := by
  haveI : Nonempty (PenIdx (polyW (h1Poly r k F))) := inferInstance
  have hpos : 0 < pencilFlatDim r k F N :=
    Nat.mul_pos Fintype.card_pos (Nat.mul_pos (by omega) (Nat.succ_pos N))
  exact_mod_cast hpos

/-- **The sharp direction contraction of the flattened affine pencil.**  With the explicit
constant `G = flatContractionConst r k F`,

`∑_p ‖τ_N(X · ∂_p 𝓛_z)‖² ≤ 2 · gueScale(N+1)² · G / m² · ‖X‖_F²`

for every matrix `X`, where `m = pencilFlatDim r k F N` and `∂_p 𝓛_z = flatStepDir`. -/
theorem sum_sq_normTrace_flatStepDir_le
    (X : Matrix (Fin (pencilFlatDim r k F N)) (Fin (pencilFlatDim r k F N)) ℂ) :
    ∑ p : GUECoord (Fin r) (N+1), ‖normTrace (X * flatStepDir r k F N z p)‖ ^ 2
      ≤ 2 * (gueScale (N+1)) ^ 2 * flatContractionConst r k F
          / (pencilFlatDim r k F N : ℝ) ^ 2 * hsNorm X := by
  classical
  set m : ℝ := (pencilFlatDim r k F N : ℝ) with hm
  have hmpos : 0 < m := by rw [hm]; exact pencilFlatDim_pos_real k F N
  set X' : Matrix ((PenIdx (polyW (h1Poly r k F)) × Fin ((k+1)+(k+1))) × Fin (N+1))
      ((PenIdx (polyW (h1Poly r k F)) × Fin ((k+1)+(k+1))) × Fin (N+1)) ℂ :=
    Matrix.reindex (pencilFlatIdx r k F N).symm (pencilFlatIdx r k F N).symm X with hX'
  have hdir := sum_sq_trace_direction_le (ι := Fin r)
    (d := PenIdx (polyW (h1Poly r k F)) × Fin ((k+1)+(k+1))) (N := N+1) X' (flatDirCoeff k F)
  have hsum_le : ∑ p : GUECoord (Fin r) (N+1),
      ‖Matrix.trace (X' * gueDirMatrix (flatDirCoeff k F) p)‖ ^ 2
        ≤ 2 * (gueScale (N+1)) ^ 2 * flatContractionConst r k F * hsNorm X' := by
    have h1 : ∑ p : GUECoord (Fin r) (N+1),
        ‖Matrix.trace (X' * gueDirMatrix (flatDirCoeff k F) p)‖ ^ 2
          = ∑ p : GUECoord (Fin r) (N+1),
            ‖Matrix.trace (gueDirMatrix (flatDirCoeff k F) p * X')‖ ^ 2 := by
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [Matrix.trace_mul_comm]
    rw [h1]
    refine hdir.trans ?_
    have hG := sum_frob_flatDirCoeff_le k F
    have h1' : 2 * (gueScale (N+1)) ^ 2 * (∑ i : Fin r, (frob (flatDirCoeff k F i)) ^ 2)
        ≤ 2 * (gueScale (N+1)) ^ 2 * flatContractionConst r k F :=
      mul_le_mul_of_nonneg_left hG (by positivity)
    exact mul_le_mul_of_nonneg_right h1' (hsNorm_nonneg X')
  have hpt : ∀ p : GUECoord (Fin r) (N+1),
      ‖normTrace (X * flatStepDir r k F N z p)‖ ^ 2
        ≤ m⁻¹ ^ 2 * ‖Matrix.trace (X' * gueDirMatrix (flatDirCoeff k F) p)‖ ^ 2 := by
    intro p
    simp only [normTrace]
    rw [trace_mul_flatStepDir_eq k F N z p X]
    have h1 : ‖m⁻¹ * (Matrix.trace (X' * gueDirMatrix (flatDirCoeff k F) p)).re‖
        ≤ m⁻¹ * ‖Matrix.trace (X' * gueDirMatrix (flatDirCoeff k F) p)‖ := by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity)]
      exact mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm _) (by positivity)
    calc ‖m⁻¹ * (Matrix.trace (X' * gueDirMatrix (flatDirCoeff k F) p)).re‖ ^ 2
        ≤ (m⁻¹ * ‖Matrix.trace (X' * gueDirMatrix (flatDirCoeff k F) p)‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ = m⁻¹ ^ 2 * ‖Matrix.trace (X' * gueDirMatrix (flatDirCoeff k F) p)‖ ^ 2 := by ring
  have hstep : ∑ p : GUECoord (Fin r) (N+1), ‖normTrace (X * flatStepDir r k F N z p)‖ ^ 2
      ≤ m⁻¹ ^ 2 * (2 * (gueScale (N+1)) ^ 2 * flatContractionConst r k F * hsNorm X') := by
    calc ∑ p : GUECoord (Fin r) (N+1), ‖normTrace (X * flatStepDir r k F N z p)‖ ^ 2
        ≤ ∑ p : GUECoord (Fin r) (N+1),
            m⁻¹ ^ 2 * ‖Matrix.trace (X' * gueDirMatrix (flatDirCoeff k F) p)‖ ^ 2 :=
          Finset.sum_le_sum fun p _ => hpt p
      _ = m⁻¹ ^ 2 * ∑ p : GUECoord (Fin r) (N+1),
            ‖Matrix.trace (X' * gueDirMatrix (flatDirCoeff k F) p)‖ ^ 2 := by
          rw [Finset.mul_sum]
      _ ≤ m⁻¹ ^ 2 * (2 * (gueScale (N+1)) ^ 2 * flatContractionConst r k F * hsNorm X') :=
          mul_le_mul_of_nonneg_left hsum_le (sq_nonneg _)
  refine hstep.trans (le_of_eq ?_)
  rw [hsNorm_reindex (e := (pencilFlatIdx r k F N).symm) X]
  have hcoef : m⁻¹ ^ 2 * (2 * (gueScale (N+1)) ^ 2 * flatContractionConst r k F * hsNorm X)
      = 2 * (gueScale (N+1)) ^ 2 * flatContractionConst r k F / m ^ 2 * hsNorm X := by
    field_simp
  exact hcoef

end FinalContraction


section Unconditional

variable (k : ℕ) (F : RatPolyIdx r (k + 1)) (z : ℝ)

lemma flatContractionConst_nonneg : 0 ≤ flatContractionConst r k F := by
  rw [flatContractionConst]
  positivity

/-- **Lemma V for the flattened polynomial pencil with the direction contraction
discharged.**  The constant `G` is the explicit `flatContractionConst r k F`, so the variance
bound reads

`Var(τ_N(f(fl 𝓛_z))) ≤ (2 G / pencilVDim) / N² · E[τ_N((f')²(fl 𝓛_z))]`

eventually in `N`. -/
theorem flatLemmaV_hV_unconditional (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f)
    (hF : ∀ N : ℕ, MemLp (flatStatBlk r k F z N f)
      2 (stdGaussian (EuclideanSpace ℝ (GUECoord (Fin r) (N + 1)))))
    (hDmem : ∀ (N : ℕ) (p : GUECoord (Fin r) (N + 1)),
      MemLp (fun y => flatDerivStat r k F z N f y p)
        2 (stdGaussian (EuclideanSpace ℝ (GUECoord (Fin r) (N + 1)))))
    (hpoly : ∀ (N : ℕ) (p : GUECoord (Fin r) (N + 1)),
      ∀ᵐ y ∂(stdGaussian (EuclideanSpace ℝ (GUECoord (Fin r) (N + 1)))),
        PolyGrowth (fun u : ℝ => flatStatBlk r k F z N f (euclidUpdate y p u)) ∧
        PolyGrowth (fun u : ℝ => flatDerivStat r k F z N f (euclidUpdate y p u) p))
    (hint : ∀ N : ℕ, Integrable (fun y => hsNorm (cfc (deriv f) (flatPencilBlk r k F N z y)))
      (stdGaussian (EuclideanSpace ℝ (GUECoord (Fin r) (N + 1)))))
    (hWint : ∀ N : ℕ, Integrable (flatStatBlk r k F z N (fun t => (deriv f t) ^ 2))
      (stdGaussian (EuclideanSpace ℝ (GUECoord (Fin r) (N + 1)))))
    (hW0 : ∀ N : ℕ, 0 ≤ ∫ x, flatStat r k F z N (fun t => (deriv f t) ^ 2) x
      ∂(commonGaussianMeasure (Fin r))) :
    ∀ᶠ N : ℕ in atTop,
      variance (flatStat r k F z N f) (commonGaussianMeasure (Fin r))
        ≤ 2 * flatContractionConst r k F / pencilVDim r k F / (N : ℝ) ^ 2
            * ∫ x, flatStat r k F z N (fun t => (deriv f t) ^ 2) x
                ∂(commonGaussianMeasure (Fin r)) := by
  refine flatLemmaV_hV k F z f hf (flatContractionConst r k F)
    (flatContractionConst_nonneg k F) hF hDmem hpoly hint hWint ?_ hW0
  intro N y
  have h := sum_sq_normTrace_flatStepDir_le k F N z
    (cfc (deriv f) (flatPencilBlk r k F N z y))
  simpa only [flatDerivStat, Real.norm_eq_abs, sq_abs] using h

end Unconditional

end
end GUEStrongConvergence
