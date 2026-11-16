/-
# Block-diagonal pairings: juxtaposition, split and multiplicativity

This file develops the *block-diagonal pairing split* which underlies the hypothesis `hblock` of
`variance_bound_gueNormTrace`: the factorisation of the non-crossing (block-diagonal) part of the
two-walk pairing sum as the square of the single-walk genus sum.

## What is proved here

* `eraseIdx_append_left`: deleting a position of the first block commutes with concatenation, and
  `get_append_left'`: the entries of the first block of a concatenation are the entries of the
  first factor.
* `GUEPairing.append l₁ l₂ p₁ p₂ : GUEPairing (l₁ ++ l₂)`: **juxtaposition**, the pairing that
  places a pairing of `l₁` and a pairing of `l₂` side by side (no pair crosses between blocks).
* `GUEPairing.gueLabelWeight_append` and `GUEPairing.gueIndexWeight_append`: the label weight and
  the index weight are **multiplicative** under juxtaposition.
* `BlockDiag l₁ l₂ q`: the *constructive* block-diagonality of `q : GUEPairing (l₁ ++ l₂)`
  (i.e. `q` is a juxtaposition).
* `GUEPairing.append_injective`: juxtaposition is injective in the pair (strong induction on the
  length of the first block).
* `GUEPairing.blockDiagEquiv`:
  `GUEPairing l₁ × GUEPairing l₂ ≃ {q : GUEPairing (l₁ ++ l₂) // BlockDiag l₁ l₂ q}`.
* `GUEPairing.sum_blockDiag`: **the block-diagonal sum factorises** through the equivalence, and
  `GUEPairing.sum_gueLabelWeight_blockDiag`: the label-weight sum over the block-diagonal pairings
  is the product of the two single-block label-weight sums.
* `val_succAbove`, `val_predAbove`, `eraseIndex_val`: the value formulas for the two `Fin`
  insertion/deletion maps used by the partner recursion.
* `slotBlock₁`, `slotBlock₂`, `slotList_eq_append`: the canonical slot list of `w` and `w.reverse`
  is the concatenation of its two blocks, and `slotBlock₁_get_label` / `slotBlock₂_get_label`:
  the labels of the two blocks are those of `w` and of `w.reverse`.
* `genusSumCanon`: the even-length single-walk genus sum `∑_p labelW(p) * N ^ c(p)`;
  `star_gueLabelCov`, `star_gueLabelWeight`, `star_genusSumCanon`: it is real;
  `genusSumCanon_reverse`: `S(w.reverse) = S(w)` for even-length words;
* **`genusSum_reverse'`** (reversal invariance, for the one-walk genus sum `genusSum` of
  `GUEAllWords`, i.e. the `S` appearing in `hblock`):
  `1 ≤ N → genusSum w.reverse N = genusSum w N`; with `star_genusSum`: `genusSum` is real.  The
  proof is analytic: `integral_eq_genusSum` for `w` and for `w.reverse`, the conjugation identity
  `star (gueNormTrace w x) = gueNormTrace w.reverse x`, and cancellation of the nonzero factor
  `N ^ (-(w.length/2+1))`.  It is non-circular: the mean formula does not use the variance bound;
* `sum_pairOrbitCount_eq_of_label_eq`: the genus sum depends only on the label sequence (transport
  of the pairing sum along `GUEPairing.castLength`).

## What remains for `hblock`

One companion fact is *not* proved here and is the remaining gap:

1. **Partner positions of a juxtaposition** (the linchpin of the loop-count split, needed to
   identify `BlockDiag` with `¬ SlotCross ...` and to split the loop count):
   `(partner (l₁ ++ l₂) (append l₁ l₂ p₁ p₂) ⟨i.val, _⟩).val = (partner l₁ p₁ i).val` for
   `i : Fin l₁.length`, and the analogous statement for the second block.  The ingredients are
   `partner_cons_zero`, `partner_cons_head`, `partner_cons_other`, `partner_eqRec` together with
   `eraseIndex_val` and `val_succAbove`; the induction is on the length of `l₁` and mirrors the
   definition of `partner`.
2. From 1: `twoWalkLoopCount k₁ k₂ (slotPerm q) = pairOrbitCount p₁ + pairOrbitCount p₂` for a
   block-diagonal slot pairing `q = append p₁ p₂` (via `twoWalkLoopCount_sumCongr` and the
   identification of `partnerPerm` with the `finSumFinEquiv`-conjugate direct sum), together with
   `¬ SlotCross ... ↔ BlockDiag ...` (the forward direction uses that a fixed-point-free involution
   mapping the first block into itself maps the second block into itself).

No `sorry`/axiom is used.
-/
import GUEStrongConvergence.Probability.GUEVarianceFinal
import GUEStrongConvergence.Probability.GUEWordGenusExpansionInstance
import GUEStrongConvergence.Probability.FinRotateCongr
import GUEStrongConvergence.Probability.GUEPairingMapEntries
import GUEStrongConvergence.Probability.GUEAllWords

open MeasureTheory ProbabilityTheory Filter
open scoped RealInnerProductSpace Matrix ENNReal Topology

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false
set_option linter.unusedVariables false

namespace GUEStrongConvergence

attribute [local instance] Classical.propDecidable

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {N : ℕ}

/-! ### List bookkeeping for the concatenation split -/

/-- Deleting a position of the first block is deleting it in the first factor. -/
theorem eraseIdx_append_left {α : Type*} (l₁ l₂ : List α) (k : Fin l₁.length) :
    (l₁ ++ l₂).eraseIdx k.val = l₁.eraseIdx k.val ++ l₂ := by
  induction l₁ with
  | nil => exact Fin.elim0 k
  | cons a l ih =>
    match k with
    | ⟨0, _⟩ => simp
    | ⟨m + 1, hk⟩ =>
      have hk' : m < l.length := by simpa using hk
      have := ih ⟨m, hk'⟩
      simpa using this

/-- The `k`-th entry of a concatenation inside the first block. -/
theorem get_append_left' {α : Type*} (l₁ l₂ : List α) (k : Fin l₁.length) :
    (l₁ ++ l₂).get ⟨k.val, by have := k.isLt; simp; omega⟩ = l₁.get k := by
  rw [List.get_eq_getElem, List.get_eq_getElem]
  rw [List.getElem_append_left (by simp [k.isLt])]

/-- Dependent transport of a pairing along an equality of lists does not change the index
weight. -/
lemma gueIndexWeight_eqRec {l₁ l₂ : List (GUEEntry ι N)} (h : l₁ = l₂) (p : GUEPairing l₁) :
    gueIndexWeight l₂ (h ▸ p) = gueIndexWeight l₁ p := by
  cases h
  rfl

/-! ### Juxtaposition of pairings -/

namespace GUEPairing

variable {l₁ l₂ : List (GUEEntry ι N)}

/-- **Juxtaposition**: put a pairing of `l₁` and a pairing of `l₂` side by side.  Every pair of
the resulting pairing of `l₁ ++ l₂` has both endpoints in the same block. -/
def append : (l₁ l₂ : List (GUEEntry ι N)) → GUEPairing l₁ → GUEPairing l₂ →
    GUEPairing (l₁ ++ l₂)
  | [], l₂, GUEPairing.nil, p₂ => p₂
  | _ :: l, l₂, GUEPairing.cons e _ k p, p₂ =>
    GUEPairing.cons e (l ++ l₂) ⟨k.val, by have := k.isLt; simp; omega⟩
      ((eraseIdx_append_left l l₂ k).symm ▸ append (l.eraseIdx k) l₂ p p₂)

/-- The computation rule of `append` at a `cons` pairing. -/
theorem append_cons (e : GUEEntry ι N) (l : List (GUEEntry ι N)) (k : Fin l.length)
    (p : GUEPairing (l.eraseIdx k)) (p₂ : GUEPairing l₂) :
    append (e :: l) l₂ (GUEPairing.cons e l k p) p₂ =
      GUEPairing.cons e (l ++ l₂) ⟨k.val, by have := k.isLt; simp; omega⟩
        ((eraseIdx_append_left l l₂ k).symm ▸ append (l.eraseIdx k) l₂ p p₂) := rfl

/-- The computation rule of `append` at the empty pairing. -/
@[simp] theorem append_nil (p₂ : GUEPairing l₂) :
    append [] l₂ (GUEPairing.nil : GUEPairing []) p₂ = p₂ := rfl

/-- The label weight is multiplicative under juxtaposition. -/
theorem gueLabelWeight_append (p₁ : GUEPairing l₁) :
    (p₂ : GUEPairing l₂) →
      gueLabelWeight (l₁ ++ l₂) (append l₁ l₂ p₁ p₂) =
        gueLabelWeight l₁ p₁ * gueLabelWeight l₂ p₂ := by
  induction p₁ with
  | nil => intro p₂; simp
  | cons e l k p ih =>
    intro p₂
    rw [append_cons]
    simp only [List.cons_append, gueLabelWeight_cons]
    rw [get_append_left' l l₂ k,
      gueLabelWeight_eqRec (l₁ := l.eraseIdx k ++ l₂) (l₂ := (l ++ l₂).eraseIdx k)
        (eraseIdx_append_left l l₂ k).symm, ih p₂]
    ring

/-- The index weight is multiplicative under juxtaposition. -/
theorem gueIndexWeight_append (p₁ : GUEPairing l₁) :
    (p₂ : GUEPairing l₂) →
      gueIndexWeight (l₁ ++ l₂) (append l₁ l₂ p₁ p₂) =
        gueIndexWeight l₁ p₁ * gueIndexWeight l₂ p₂ := by
  induction p₁ with
  | nil => intro p₂; simp
  | cons e l k p ih =>
    intro p₂
    rw [append_cons]
    simp only [List.cons_append, gueIndexWeight_cons]
    rw [get_append_left' l l₂ k,
      gueIndexWeight_eqRec (l₁ := l.eraseIdx k ++ l₂) (l₂ := (l ++ l₂).eraseIdx k)
        (eraseIdx_append_left l l₂ k).symm, ih p₂]
    ring

end GUEPairing

/-- Dependent-transport cancellation: transport along an equality is injective. -/
theorem eqRec_inj {α : Sort*} {F : α → Sort*} {a b : α} (h : a = b) {x y : F a}
    (hh : (h ▸ x) = (h ▸ y)) : x = y := by
  cases h
  exact hh

/-- **Block-diagonal pairings** of `l₁ ++ l₂`: pairings obtained by putting a pairing of `l₁` and
a pairing of `l₂` side by side, so that no pair crosses between the two blocks. -/
def BlockDiag (l₁ l₂ : List (GUEEntry ι N)) (q : GUEPairing (l₁ ++ l₂)) : Prop :=
  ∃ (p₁ : GUEPairing l₁) (p₂ : GUEPairing l₂), q = GUEPairing.append l₁ l₂ p₁ p₂

namespace GUEPairing

variable {l₁ l₂ : List (GUEEntry ι N)}

/-- **Juxtaposition is injective in its two arguments.** -/
theorem append_injective_aux : ∀ (n : ℕ) (l₁ : List (GUEEntry ι N)), l₁.length = n →
    ∀ (l₂ : List (GUEEntry ι N)),
      Function.Injective
        (fun p : GUEPairing l₁ × GUEPairing l₂ => append l₁ l₂ p.1 p.2) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro l₁ hl l₂ p q hpq
    obtain ⟨p₁, p₂⟩ := p
    obtain ⟨q₁, q₂⟩ := q
    cases p₁ with
    | nil =>
      cases q₁ with
      | nil => simpa [append] using hpq
    | cons e l k p' =>
      cases q₁ with
      | cons e' l' k' q' =>
        beta_reduce at hpq
        rw [append_cons, append_cons] at hpq
        obtain ⟨hk, hX⟩ :=
          (GUEPairing.cons.injEq e (l ++ l₂) ⟨k.val, by have := k.isLt; simp; omega⟩
            ((eraseIdx_append_left l l₂ k).symm ▸ append (l.eraseIdx k) l₂ p' p₂)
            ⟨k'.val, by have := k'.isLt; simp; omega⟩
            ((eraseIdx_append_left l l₂ k').symm ▸ append (l.eraseIdx k') l₂ q' q₂)).mp hpq
        have hkk : k = k' := Fin.ext (by
          have := congrArg Fin.val hk
          simpa using this)
        subst hkk
        have hxy : append (l.eraseIdx k) l₂ p' p₂ = append (l.eraseIdx k) l₂ q' q₂ := by
          refine eqRec_inj (eraseIdx_append_left l l₂ k).symm ?_
          exact eq_of_heq hX
        have hlen : (l.eraseIdx k).length < n := by
          have hl' : l.length + 1 = n := by simpa using hl
          rw [List.length_eraseIdx]
          split <;> omega
        have hpq' : (p', p₂) = (q', q₂) :=
          ih (l.eraseIdx k).length hlen (l.eraseIdx k) rfl l₂ hxy
        obtain ⟨rfl, rfl⟩ := hpq'
        rfl

/-- **Juxtaposition is injective in its two arguments.** -/
theorem append_injective :
    Function.Injective
      (fun p : GUEPairing l₁ × GUEPairing l₂ => append l₁ l₂ p.1 p.2) :=
  append_injective_aux l₁.length l₁ rfl l₂

/-- **Block-diagonal pairings are exactly the juxtaposed ones**: the equivalence between
block-diagonal pairings of `l₁ ++ l₂` and pairs of pairings of the two blocks. -/
def blockDiagEquiv (l₁ l₂ : List (GUEEntry ι N)) :
    GUEPairing l₁ × GUEPairing l₂ ≃ {q : GUEPairing (l₁ ++ l₂) // BlockDiag l₁ l₂ q} :=
  Equiv.ofBijective (fun p => ⟨append l₁ l₂ p.1 p.2, p.1, p.2, rfl⟩)
    ⟨fun p q h => append_injective (Subtype.ext_iff.mp h),
     fun q => by
      obtain ⟨p₁, p₂, hp⟩ := q.2
      exact ⟨(p₁, p₂), Subtype.ext hp.symm⟩⟩

/-- **The number of block-diagonal pairings** is the product of the two block counts. -/
theorem card_blockDiag (l₁ l₂ : List (GUEEntry ι N)) :
    Fintype.card {q : GUEPairing (l₁ ++ l₂) // BlockDiag l₁ l₂ q} =
      Fintype.card (GUEPairing l₁) * Fintype.card (GUEPairing l₂) := by
  calc Fintype.card {q : GUEPairing (l₁ ++ l₂) // BlockDiag l₁ l₂ q}
      = Fintype.card (GUEPairing l₁ × GUEPairing l₂) :=
        (Fintype.card_congr (blockDiagEquiv l₁ l₂)).symm
    _ = Fintype.card (GUEPairing l₁) * Fintype.card (GUEPairing l₂) :=
        Fintype.card_prod (GUEPairing l₁) (GUEPairing l₂)

/-- **Factorization of a sum over the block-diagonal pairings.** -/
theorem sum_blockDiag {M : Type*} [AddCommMonoid M]
    (F : GUEPairing (l₁ ++ l₂) → M) :
    (∑ q : {q : GUEPairing (l₁ ++ l₂) // BlockDiag l₁ l₂ q}, F q.val) =
      ∑ p : GUEPairing l₁ × GUEPairing l₂, F (append l₁ l₂ p.1 p.2) := by
  exact (Equiv.sum_comp (blockDiagEquiv l₁ l₂)
    (fun q : {q : GUEPairing (l₁ ++ l₂) // BlockDiag l₁ l₂ q} => F q.val)).symm

/-- **Factorization of the label-weight sum over the block-diagonal pairings.** -/
theorem sum_gueLabelWeight_blockDiag :
    (∑ q : {q : GUEPairing (l₁ ++ l₂) // BlockDiag l₁ l₂ q},
        gueLabelWeight (l₁ ++ l₂) q.val) =
      (∑ p₁ : GUEPairing l₁, gueLabelWeight l₁ p₁) *
        (∑ p₂ : GUEPairing l₂, gueLabelWeight l₂ p₂) := by
  rw [sum_blockDiag, Fintype.sum_prod_type]
  simp_rw [gueLabelWeight_append]
  rw [Finset.sum_mul_sum]

end GUEPairing


/-! ### Value formulas for `Fin.succAbove` and `eraseIndex` -/

/-- The value of `Fin.succAbove`: it embeds `Fin n` into `Fin (n+1)` skipping `p`. -/
theorem val_succAbove {n : ℕ} (p : Fin (n + 1)) (y : Fin n) :
    (p.succAbove y).val = if y.val < p.val then y.val else y.val + 1 := by
  rcases lt_or_ge y.val p.val with h | h
  · rw [Fin.succAbove_of_castSucc_lt _ _ (by simp only [Fin.lt_def, Fin.val_castSucc]; exact h)]
    rw [ite_eq_left h]
    rfl
  · rw [Fin.succAbove_of_le_castSucc _ _ (by simp only [Fin.le_def, Fin.val_castSucc]; exact h)]
    rw [ite_eq_right (by omega : ¬ y.val < p.val)]
    rfl

/-- The value of `Fin.predAbove`: it subtracts one from values above `p`. -/
theorem val_predAbove {n : ℕ} (p : Fin n) (i : Fin (n + 1)) :
    (p.predAbove i).val = if p.val < i.val then i.val - 1 else i.val := by
  rcases lt_or_ge p.val i.val with h | h
  · rw [Fin.predAbove_of_castSucc_lt _ _ (by simp only [Fin.lt_def, Fin.val_castSucc]; exact h)]
    rw [ite_eq_left h]
    simp only [Fin.val_pred]
  · rw [Fin.predAbove_of_le_castSucc _ _ (by simp only [Fin.le_def, Fin.val_castSucc]; exact h)]
    rw [ite_eq_right (by omega : ¬ p.val < i.val)]
    simp only [Fin.castPred, Fin.val_castLT]

/-- The value of `eraseIndex`: the position after deleting `k` is `j` if it lies below `k` and
`j - 1` otherwise. -/
theorem eraseIndex_val : ∀ (n : ℕ) (k j : Fin (n + 1)) (h : j ≠ k),
    (eraseIndex n k j h).val = if j.val < k.val then j.val else j.val - 1
  | 0, k, j, h => by
    exfalso
    exact h (Fin.ext (by have hk := k.isLt; have hj := j.isLt; omega))
  | n + 1, k, j, h => by
    rw [eraseIndex]
    by_cases hk : k = Fin.last (n + 1)
    · rw [dite_eq_left hk]
      have hkv : k.val = n + 1 := by rw [hk]; rfl
      have hjv : j.val < k.val := by
        have h1 := j.isLt
        have h2 : j.val ≠ n + 1 := by
          intro hh
          exact h (Fin.ext (by rw [hkv]; exact hh))
        omega
      rw [ite_eq_left hjv]
      rfl
    · rw [dite_eq_right hk]
      have hklt : k.val < n + 1 := by
        have h1 := k.isLt
        have h2 : k.val ≠ n + 1 := by intro hh; exact hk (Fin.ext (by simpa using hh))
        omega
      show ((Fin.castLT k hklt).predAbove j).val = _
      rw [val_predAbove]
      simp only [Fin.val_castLT]
      by_cases hjk : j.val < k.val
      · rw [ite_eq_left hjk, ite_eq_right (by omega : ¬ k.val < j.val)]
      · rw [ite_eq_right hjk, ite_eq_left (by omega : k.val < j.val)]


/-! ### The block decomposition of the canonical slot list -/

/-- The entries of the first block of the canonical slot list of `w` and `w.reverse`. -/
def slotBlock₁ (w : List ι) (V : Fin (w.length + w.reverse.length) → Fin N) :
    List (GUEEntry ι N) :=
  List.ofFn (fun i : Fin w.length =>
    slotEntry w.length w.reverse.length (twoWalkLabel w w.reverse) V
      (Fin.castAdd w.reverse.length i))

/-- The entries of the second block of the canonical slot list of `w` and `w.reverse`. -/
def slotBlock₂ (w : List ι) (V : Fin (w.length + w.reverse.length) → Fin N) :
    List (GUEEntry ι N) :=
  List.ofFn (fun j : Fin w.reverse.length =>
    slotEntry w.length w.reverse.length (twoWalkLabel w w.reverse) V
      (Fin.natAdd w.length j))

/-- **The canonical slot list is the concatenation of its two blocks.** -/
theorem slotList_eq_append (w : List ι) (V : Fin (w.length + w.reverse.length) → Fin N) :
    slotList w V = slotBlock₁ w V ++ slotBlock₂ w V := by
  have hfun : Fin.append
      (fun i : Fin w.length =>
        slotEntry w.length w.reverse.length (twoWalkLabel w w.reverse) V
          (Fin.castAdd w.reverse.length i))
      (fun j : Fin w.reverse.length =>
        slotEntry w.length w.reverse.length (twoWalkLabel w w.reverse) V
          (Fin.natAdd w.length j)) =
      (fun i : Fin (w.length + w.reverse.length) =>
        slotEntry w.length w.reverse.length (twoWalkLabel w w.reverse) V i) := by
    funext i
    cases i using Fin.addCases <;> simp
  simp only [slotList, twoWalkSlotList, slotBlock₁, slotBlock₂]
  rw [← List.ofFn_fin_append, hfun]

/-- The label of a first-block slot is the label of the word `w`. -/
theorem slotBlock₁_get_label (w : List ι) (V : Fin (w.length + w.reverse.length) → Fin N)
    (i : Fin w.length) :
    ((twoWalkLabel w w.reverse (Fin.castAdd w.reverse.length i),
        (V (Fin.castAdd w.reverse.length i),
          V (blockSuccPerm w.length w.reverse.length (Fin.castAdd w.reverse.length i)))) :
      GUEEntry ι N).1 = w.get i :=
  twoWalkLabel_castAdd w w.reverse i

/-- The label of a second-block slot is the label of the word `w.reverse`. -/
theorem slotBlock₂_get_label (w : List ι) (V : Fin (w.length + w.reverse.length) → Fin N)
    (j : Fin w.reverse.length) :
    ((twoWalkLabel w w.reverse (Fin.natAdd w.length j),
        (V (Fin.natAdd w.length j),
          V (blockSuccPerm w.length w.reverse.length (Fin.natAdd w.length j)))) :
      GUEEntry ι N).1 = w.reverse.get j :=
  twoWalkLabel_natAdd w w.reverse j


/-! ### Reversal invariance of the single-walk genus sum -/

/-- The label covariance is real. -/
theorem star_gueLabelCov (e f : GUEEntry ι N) : star (gueLabelCov e f) = gueLabelCov e f := by
  simp only [gueLabelCov]
  split_ifs <;> simp

/-- The label weight of a pairing is real. -/
theorem star_gueLabelWeight (l : List (GUEEntry ι N)) (p : GUEPairing l) :
    star (gueLabelWeight l p) = gueLabelWeight l p := by
  induction p with
  | nil => simp
  | cons e l k p ih =>
    rw [gueLabelWeight_cons, star_mul, star_gueLabelCov, ih]
    ring

/-- **The single-walk genus sum** `S(v) = ∑_p labelW(p) * N ^ c(p)` of a word `v` of even
length, summed over the pairings of the canonical entry list. -/
def genusSumCanon (v : List ι) (m : ℕ) (hl : v.length = 2 * m) (hN : 1 ≤ N) : ℂ :=
  ∑ p : GUEPairing (gueCanonicalEntries v m hl hN),
    gueLabelWeight (gueCanonicalEntries v m hl hN) p * (N : ℂ) ^ (pairOrbitCount p)

/-- The even-length genus sum is real. -/
theorem star_genusSumCanon (v : List ι) (m : ℕ) (hl : v.length = 2 * m) (hN : 1 ≤ N) :
    star (genusSumCanon (N := N) v m hl hN) = genusSumCanon (N := N) v m hl hN := by
  rw [genusSumCanon, star_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [star_mul, star_gueLabelWeight, star_pow, star_natCast]
  ring

/-- **Reversal invariance**: the genus sum of a word and of its reversal agree. -/
theorem genusSumCanon_reverse (w : List ι) (m : ℕ) (hl : w.length = 2 * m) (hm : 1 ≤ m)
    (hN : 1 ≤ N) :
    genusSumCanon (N := N) w.reverse m (by rw [List.length_reverse]; exact hl) hN =
      genusSumCanon (N := N) w m hl hN := by
  have hpos : 1 ≤ w.length := by omega
  have hpos' : 1 ≤ w.reverse.length := by simpa using hpos
  have h1 : (∫ x : EuclideanSpace ℝ (GUECoord ι N), gueNormTrace w x
        ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))) =
      ((N : ℂ) ^ (-(m + 1) : ℤ)) * genusSumCanon (N := N) w m hl hN :=
    integral_gueNormTrace_eq_genus_canonical w m hl hpos hN
  have h2 : (∫ x : EuclideanSpace ℝ (GUECoord ι N), gueNormTrace w.reverse x
        ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))) =
      ((N : ℂ) ^ (-(m + 1) : ℤ)) *
        genusSumCanon (N := N) w.reverse m (by rw [List.length_reverse]; exact hl) hN :=
    integral_gueNormTrace_eq_genus_canonical w.reverse m
      (by rw [List.length_reverse]; exact hl) hpos' hN
  -- conjugation of the mean
  have hconj :
      (∫ x : EuclideanSpace ℝ (GUECoord ι N), gueNormTrace w.reverse x
          ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))) =
        star (∫ x : EuclideanSpace ℝ (GUECoord ι N), gueNormTrace w x
          ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))) := by
    have h : (∫ x : EuclideanSpace ℝ (GUECoord ι N), star (gueNormTrace w x)
        ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))) =
        star (∫ x : EuclideanSpace ℝ (GUECoord ι N), gueNormTrace w x
          ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))) := integral_conj
    rw [← h]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => (star_gueNormTrace w x).symm)
  rw [h2, h1] at hconj
  simp only [star_mul, star_genusSumCanon] at hconj
  simp only [star_zpow₀, star_natCast] at hconj
  have hAne : ((N : ℂ) ^ (-(m + 1) : ℤ)) ≠ 0 := by
    have hNne : (N : ℂ) ≠ 0 := by
      have : N ≠ 0 := by omega
      exact_mod_cast this
    exact zpow_ne_zero _ hNne
  rw [mul_comm (genusSumCanon (N := N) w m hl hN)] at hconj
  exact mul_left_cancel₀ hAne hconj

/-- **The genus sum depends only on the label sequence**: two entry lists of the same length and
with pointwise equal labels have the same genus sum. -/
theorem sum_pairOrbitCount_eq_of_label_eq {l₁ l₂ : List (GUEEntry ι N)}
    (h : l₁.length = l₂.length)
    (hlab : ∀ i : Fin l₁.length, (l₁.get i).1 = (l₂.get (Fin.cast h i)).1) :
    (∑ p : GUEPairing l₂, gueLabelWeight l₂ p * (N : ℂ) ^ (pairOrbitCount p)) =
      ∑ p : GUEPairing l₁, gueLabelWeight l₁ p * (N : ℂ) ^ (pairOrbitCount p) := by
  rw [← GUEPairing.sum_castLength (M := ℂ) h
    (fun p : GUEPairing l₂ => gueLabelWeight l₂ p * (N : ℂ) ^ (pairOrbitCount p))]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [GUEPairing.gueLabelWeight_castLength p l₂ h hlab, pairOrbitCount_castLength]


/-- The first block has the length of the word. -/
theorem length_slotBlock₁ (w : List ι) (V : Fin (w.length + w.reverse.length) → Fin N) :
    (slotBlock₁ w V).length = w.length := List.length_ofFn

/-- The second block has the length of the reversed word. -/
theorem length_slotBlock₂ (w : List ι) (V : Fin (w.length + w.reverse.length) → Fin N) :
    (slotBlock₂ w V).length = w.reverse.length := List.length_ofFn

/-! ### Reversal invariance of the one-walk genus sum `genusSum` -/

/-- The one-walk genus sum (`GUEAllWords.genusSum`) is real. -/
theorem star_genusSum (w : List ι) (N : ℕ) : star (genusSum (ι := ι) w N) = genusSum (ι := ι) w N := by
  unfold genusSum
  split_ifs with h
  · rw [star_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [star_mul, star_gueLabelWeight, star_pow, star_natCast]
    ring
  · simp

/-- **Reversal invariance of the one-walk genus sum**: `S(w.reverse) = S(w)`. -/
theorem genusSum_reverse' (w : List ι) (N : ℕ) (hN : 1 ≤ N) :
    genusSum (ι := ι) w.reverse N = genusSum (ι := ι) w N := by
  match w with
  | [] => rfl
  | a :: t =>
    have hk : 1 ≤ (a :: t).length := by simp
    have hk' : 1 ≤ (a :: t).reverse.length := by simpa using hk
    have h1 : (∫ x : EuclideanSpace ℝ (GUECoord ι N), gueNormTrace (a :: t) x
          ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))) =
        ((N : ℂ) ^ (-((a :: t).length / 2 + 1) : ℤ)) * genusSum (ι := ι) (a :: t) N :=
      integral_eq_genusSum (a :: t) hk hN
    have h2 : (∫ x : EuclideanSpace ℝ (GUECoord ι N), gueNormTrace (a :: t).reverse x
          ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))) =
        ((N : ℂ) ^ (-((a :: t).reverse.length / 2 + 1) : ℤ)) *
          genusSum (ι := ι) (a :: t).reverse N :=
      integral_eq_genusSum (a :: t).reverse hk' hN
    have hconj :
        (∫ x : EuclideanSpace ℝ (GUECoord ι N), gueNormTrace (a :: t).reverse x
            ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))) =
          star (∫ x : EuclideanSpace ℝ (GUECoord ι N), gueNormTrace (a :: t) x
            ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))) := by
      have h : (∫ x : EuclideanSpace ℝ (GUECoord ι N), star (gueNormTrace (a :: t) x)
          ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))) =
          star (∫ x : EuclideanSpace ℝ (GUECoord ι N), gueNormTrace (a :: t) x
            ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))) := integral_conj
      rw [← h]
      exact integral_congr_ae (Filter.Eventually.of_forall fun x => (star_gueNormTrace _ x).symm)
    rw [h2, h1] at hconj
    simp only [List.length_reverse] at hconj
    simp only [star_mul, star_genusSum] at hconj
    simp only [star_zpow₀, star_natCast] at hconj
    rw [mul_comm (genusSum (ι := ι) (a :: t) N)] at hconj
    refine mul_left_cancel₀ (zpow_ne_zero _ ?_) hconj
    have hNne : (N : ℂ) ≠ 0 := by
      have : N ≠ 0 := by omega
      exact_mod_cast this
    exact hNne


end

end GUEStrongConvergence