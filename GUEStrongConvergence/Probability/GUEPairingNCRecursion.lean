/-
# First-partner recursion for the project's non-crossing label sum

Given a list `K = e :: rest` and a pairing `GUEPairing.cons e rest k p`, the head `e` is paired
with position `k+1` and the remaining pairing `p` acts on the erased list `rest.eraseIdx k`.  This
file relates the crossing structure of the full pairing to that of `p`, in a form suitable for
splitting the non-crossing sum into the interior and exterior blocks.

No `sorry`/axiom is used.
-/
import GUEStrongConvergence.Probability.GUEBlockSplitFinal

open MeasureTheory ProbabilityTheory Filter
open scoped RealInnerProductSpace Matrix ENNReal Topology

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false
set_option linter.unusedVariables false
set_option linter.deprecated false
set_option linter.unusedSimpArgs false

namespace GUEStrongConvergence

attribute [local instance] Classical.propDecidable

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {N : ℕ}

namespace GUEPairing

variable {e x : GUEEntry ι N} {l' : List (GUEEntry ι N)}

/-- The position in `e :: x :: l'` corresponding to the erased position `q` of
`(x :: l').eraseIdx k` (recall that `e` and position `k` of `x :: l'` are removed from the
`k`-pairing). -/
def origIdx (k : Fin (x :: l').length) (q : Fin l'.length) : Fin (e :: x :: l').length :=
  (k.succAbove q).succ

@[simp] lemma origIdx_val (k : Fin (x :: l').length) (q : Fin l'.length) :
    (origIdx (e := e) k q).val = if q.val < k.val then q.val + 1 else q.val + 2 := by
  simp only [origIdx, Fin.val_succ, val_succAbove]
  by_cases h : q.val < k.val <;> simp [h]

/-- Positions of the erased list are strictly increasing in the original list. -/
lemma origIdx_strictMono (k : Fin (x :: l').length) :
    StrictMono (origIdx (e := e) (l' := l') k) := by
  intro a b hab
  rw [Fin.lt_def, origIdx_val, origIdx_val]
  by_cases ha : a.val < k.val <;> by_cases hb : b.val < k.val <;> simp [ha, hb] <;> omega

lemma origIdx_injective (k : Fin (x :: l').length) :
    Function.Injective (origIdx (e := e) (l' := l') k) :=
  (origIdx_strictMono k).injective

/-- Erased positions never map to the head. -/
lemma origIdx_ne_zero (k : Fin (x :: l').length) (q : Fin l'.length) :
    origIdx (e := e) (l' := l') k q ≠ 0 := by
  intro h
  have hv := congrArg Fin.val h
  rw [origIdx_val] at hv
  by_cases h' : q.val < k.val <;> simp [h'] at hv

/-- Erased positions never map to the position paired with the head. -/
lemma origIdx_ne_head (k : Fin (x :: l').length) (q : Fin l'.length) :
    origIdx (e := e) (l' := l') k q ≠ k.succ := by
  intro h
  have hv := congrArg Fin.val h
  rw [origIdx_val] at hv
  have hk := k.isLt
  by_cases h' : q.val < k.val <;> simp [h', Fin.val_succ] at hv <;> omega

/-- **The partner recursion in erased coordinates.**  The partner of the original position
`origIdx k q` is the original position of the partner of `q` in the erased pairing. -/
theorem partner_cons_orig' (k : Fin (x :: l').length) (p : GUEPairing ((x :: l').eraseIdx k))
    (hlen : ((x :: l').eraseIdx k).length = l'.length) (q : Fin l'.length) :
    partner (e :: x :: l') (GUEPairing.cons e (x :: l') k p) ((k.succAbove q).succ) =
      (k.succAbove (Fin.cast hlen
        (partner ((x :: l').eraseIdx k) p (Fin.cast hlen.symm q)))).succ := by
  have h0 : (k.succAbove q).succ ≠ (0 : Fin (l'.length + 2)) := Fin.succ_ne_zero _
  have hk : (k.succAbove q).succ ≠ k.succ := by
    intro h
    exact Fin.succAbove_ne k q (Fin.succ_inj.mp h)
  rw [partner_cons_other e x l' k p hlen _ h0 hk]
  simp only [Fin.pred_succ, eraseIndex_succAbove]

/-- **The partner recursion in erased coordinates.** -/
theorem partner_cons_orig (k : Fin (x :: l').length) (p : GUEPairing ((x :: l').eraseIdx k))
    (hlen : ((x :: l').eraseIdx k).length = l'.length) (q : Fin l'.length) :
    partner (e :: x :: l') (GUEPairing.cons e (x :: l') k p)
        (origIdx (e := e) (l' := l') k q) =
      origIdx (e := e) (l' := l') k
        (Fin.cast hlen (partner ((x :: l').eraseIdx k) p (Fin.cast hlen.symm q))) :=
  partner_cons_orig' k p hlen q


/-- Comparison form of `origIdx_strictMono`. -/
lemma origIdx_lt {k : Fin (x :: l').length} {a b : Fin l'.length} (h : a.val < b.val) :
    (origIdx (e := e) (l' := l') k a).val < (origIdx (e := e) (l' := l') k b).val :=
  origIdx_strictMono k (Fin.lt_def.mpr h)

/-- Value of `origIdx` on the interior side of the cut. -/
lemma origIdx_val_of_lt {k : Fin (x :: l').length} {q : Fin l'.length} (h : q.val < k.val) :
    (origIdx (e := e) (l' := l') k q).val = q.val + 1 := by
  rw [origIdx_val, if_pos h]

/-- Value of `origIdx` on the exterior side of the cut. -/
lemma origIdx_val_of_ge {k : Fin (x :: l').length} {q : Fin l'.length} (h : ¬ q.val < k.val) :
    (origIdx (e := e) (l' := l') k q).val = q.val + 2 := by
  rw [origIdx_val, if_neg h]

/-- The partner of the head has value `k.val + 1`. -/
lemma head_val (k : Fin (x :: l').length) :
    (k.succ : Fin (e :: x :: l').length).val = k.val + 1 := rfl

/-- An erased position lies on the interior side of the cut iff its original position is left of
the partner of the head. -/
lemma origIdx_lt_head_iff (k : Fin (x :: l').length) (q : Fin l'.length) :
    (origIdx (e := e) (l' := l') k q).val < (k.succ : Fin (e :: x :: l').length).val ↔
      q.val < k.val := by
  rw [head_val]
  by_cases h : q.val < k.val
  · rw [origIdx_val_of_lt h]
    omega
  · rw [origIdx_val_of_ge h]
    omega

/-- Every original position other than the head and its partner is `origIdx` of an erased
position. -/
lemma exists_origIdx (k : Fin (x :: l').length) (i : Fin (e :: x :: l').length)
    (h0 : i ≠ 0) (hk : i ≠ (k.succ : Fin (e :: x :: l').length)) :
    ∃ q : Fin l'.length, origIdx (e := e) (l' := l') k q = i := by
  have hL1 : (x :: l').length = l'.length + 1 := rfl
  have hL2 : (e :: x :: l').length = l'.length + 2 := rfl
  have hiL : i.val < l'.length + 2 := by rw [← hL2]; exact i.isLt
  have hkL : k.val < l'.length + 1 := by rw [← hL1]; exact k.isLt
  have hval : (k.succ : Fin (e :: x :: l').length).val = k.val + 1 := rfl
  have hi0 : i.val ≠ 0 := by intro h; exact h0 (Fin.ext h)
  have hik : i.val ≠ k.val + 1 := by intro h; exact hk (Fin.ext (by rw [hval]; exact h))
  by_cases hi : i.val < k.val + 1
  · refine ⟨⟨i.val - 1, by omega⟩, ?_⟩
    apply Fin.ext
    rw [origIdx_val]
    have h1 : i.val - 1 < k.val := by omega
    simp [h1]
    omega
  · refine ⟨⟨i.val - 2, by omega⟩, ?_⟩
    apply Fin.ext
    rw [origIdx_val]
    have h1 : ¬ (i.val - 2 < k.val) := by omega
    simp [h1]
    omega

/-- The partner map of the erased pairing, written in `l'`-coordinates. -/
def partnerE (k : Fin (x :: l').length) (p : GUEPairing ((x :: l').eraseIdx k))
    (hlen : ((x :: l').eraseIdx k).length = l'.length) (q : Fin l'.length) : Fin l'.length :=
  Fin.cast hlen (partner ((x :: l').eraseIdx k) p (Fin.cast hlen.symm q))

@[simp] lemma partnerE_apply (k : Fin (x :: l').length) (p : GUEPairing ((x :: l').eraseIdx k))
    (hlen : ((x :: l').eraseIdx k).length = l'.length) (q : Fin l'.length) :
    partnerE k p hlen q =
      Fin.cast hlen (partner ((x :: l').eraseIdx k) p (Fin.cast hlen.symm q)) := rfl

/-- The erased partner map is an involution. -/
lemma partnerE_involutive (k : Fin (x :: l').length) (p : GUEPairing ((x :: l').eraseIdx k))
    (hlen : ((x :: l').eraseIdx k).length = l'.length) :
    Function.Involutive (partnerE k p hlen) := by
  intro q
  rw [partnerE_apply, partnerE_apply, Fin.cast_cast, Fin.cast_eq_self]
  rw [partner_involutive p]
  simp

/-- The erased partner recursion, stated with `partnerE`. -/
lemma partner_cons_origE (k : Fin (x :: l').length) (p : GUEPairing ((x :: l').eraseIdx k))
    (hlen : ((x :: l').eraseIdx k).length = l'.length) (q : Fin l'.length) :
    partner (e :: x :: l') (GUEPairing.cons e (x :: l') k p)
        (origIdx (e := e) (l' := l') k q) =
      origIdx (e := e) (l' := l') k (partnerE k p hlen q) :=
  partner_cons_orig k p hlen q

/-- A position whose partner is the head is the partner of the head. -/
lemma eq_head_of_partner_eq_zero (k : Fin (x :: l').length)
    (p : GUEPairing ((x :: l').eraseIdx k)) (a : Fin (e :: x :: l').length)
    (h : partner (e :: x :: l') (GUEPairing.cons e (x :: l') k p) a = 0) :
    a = (k.succ : Fin (e :: x :: l').length) := by
  calc a = partner (e :: x :: l') (GUEPairing.cons e (x :: l') k p)
        (partner (e :: x :: l') (GUEPairing.cons e (x :: l') k p) a) :=
        (partner_involutive (GUEPairing.cons e (x :: l') k p) a).symm
    _ = partner (e :: x :: l') (GUEPairing.cons e (x :: l') k p) 0 := by rw [h]
    _ = (k.succ : Fin (e :: x :: l').length) := partner_cons_zero e x l' k p

/-- A position whose partner is the partner of the head is the head. -/
lemma eq_zero_of_partner_eq_head (k : Fin (x :: l').length)
    (p : GUEPairing ((x :: l').eraseIdx k)) (a : Fin (e :: x :: l').length)
    (h : partner (e :: x :: l') (GUEPairing.cons e (x :: l') k p) a =
      (k.succ : Fin (e :: x :: l').length)) :
    a = 0 := by
  calc a = partner (e :: x :: l') (GUEPairing.cons e (x :: l') k p)
        (partner (e :: x :: l') (GUEPairing.cons e (x :: l') k p) a) :=
        (partner_involutive (GUEPairing.cons e (x :: l') k p) a).symm
    _ = partner (e :: x :: l') (GUEPairing.cons e (x :: l') k p)
        (k.succ : Fin (e :: x :: l').length) := by rw [h]
    _ = 0 := partner_cons_head e x l' k p _ rfl

/-- Block diagonality of the erased pairing with respect to the cut at `k`: every position
strictly left of the cut is paired with a position strictly left of the cut. -/
def IsBlockDiagRel (k : Fin (x :: l').length) (p : GUEPairing ((x :: l').eraseIdx k))
    (hlen : ((x :: l').eraseIdx k).length = l'.length) : Prop :=
  ∀ q : Fin l'.length, q.val < k.val → (partnerE k p hlen q).val < k.val

/-- The erased pairing is non-crossing in erased coordinates. -/
def IsNCRel (k : Fin (x :: l').length) (p : GUEPairing ((x :: l').eraseIdx k))
    (hlen : ((x :: l').eraseIdx k).length = l'.length) : Prop :=
  ∀ a b c d : Fin l'.length, a.val < b.val → b.val < c.val → c.val < d.val →
    ¬ (partnerE k p hlen a = c ∧ partnerE k p hlen b = d)

/-- **The non-crossing condition of a `cons` pairing, in erased coordinates.**  The pairing
`cons e (x :: l') k p` is non-crossing iff the erased pairing `p` is block diagonal with respect
to the cut at `k` and non-crossing on the erased positions. -/
theorem isNonCrossing_cons_iff (k : Fin (x :: l').length)
    (p : GUEPairing ((x :: l').eraseIdx k))
    (hlen : ((x :: l').eraseIdx k).length = l'.length) :
    IsNonCrossing (GUEPairing.cons e (x :: l') k p) ↔
      IsBlockDiagRel k p hlen ∧ IsNCRel k p hlen := by
  unfold IsNonCrossing
  simp only [partnerPerm_apply]
  constructor
  · intro hnc
    constructor
    · -- block diagonality
      intro q hq
      by_contra hge
      have hv : (k.succ : Fin (e :: x :: l').length).val
          < (origIdx (e := e) (l' := l') k (partnerE k p hlen q)).val := by
        rw [head_val]
        rw [origIdx_val_of_ge hge]
        omega
      have h := hnc 0 (origIdx (e := e) (l' := l') k q)
        (k.succ : Fin (e :: x :: l').length) (origIdx (e := e) (l' := l') k (partnerE k p hlen q))
        (by rw [Fin.val_zero]
            exact Nat.pos_of_ne_zero (by intro h; exact origIdx_ne_zero k q (Fin.ext h)))
        ((origIdx_lt_head_iff k q).mpr hq)
        hv
      exact h ⟨partner_cons_zero e x l' k p, partner_cons_origE k p hlen q⟩
    · -- non-crossing in erased coordinates
      intro a b c d hab hbc hcd hcr
      have h := hnc (origIdx (e := e) (l' := l') k a) (origIdx (e := e) (l' := l') k b)
        (origIdx (e := e) (l' := l') k c) (origIdx (e := e) (l' := l') k d)
        (origIdx_lt hab) (origIdx_lt hbc) (origIdx_lt hcd)
      refine h ⟨?_, ?_⟩
      · rw [partner_cons_origE k p hlen a, hcr.1]
      · rw [partner_cons_origE k p hlen b, hcr.2]
  · rintro ⟨hBD, hNC⟩
    intro a b c d hab hbc hcd hcr
    have hkv : (k.succ : Fin (e :: x :: l').length).val = k.val + 1 := head_val k
    rcases eq_or_ne a 0 with ha0 | ha0
    · -- the head is paired with `k`, so `c = k.succ`
      subst ha0
      have hc : c = (k.succ : Fin (e :: x :: l').length) := by
        rw [← hcr.1, partner_cons_zero]
      have hb0 : b ≠ 0 := by intro h; rw [h] at hab; exact absurd hab (by simp)
      have hbk : b ≠ (k.succ : Fin (e :: x :: l').length) := by
        intro h; rw [h, hc] at hbc; exact absurd hbc (by simp)
      obtain ⟨q, hq⟩ := exists_origIdx k b hb0 hbk
      have hbv : b.val < (k.succ : Fin (e :: x :: l').length).val := by rw [← hc]; exact hbc
      have hqv : q.val < k.val := (origIdx_lt_head_iff k q).mp (by rw [hq]; exact hbv)
      have hpv : (partnerE k p hlen q).val < k.val := hBD q hqv
      have hdv : d.val = (origIdx (e := e) (l' := l') k (partnerE k p hlen q)).val := by
        rw [← hcr.2, ← hq, partner_cons_origE k p hlen q]
      rw [hdv, origIdx_val_of_lt hpv, hc, hkv] at hcd
      omega
    · -- no position of the crossing is the head or its partner
      have hak : a ≠ (k.succ : Fin (e :: x :: l').length) := by
        intro h
        have hp : partner (e :: x :: l') (GUEPairing.cons e (x :: l') k p) a = 0 := by
          rw [h, partner_cons_head e x l' k p _ rfl]
        have hc0 : c = 0 := by rw [← hcr.1, hp]
        rw [hc0] at hbc
        exact absurd hbc (by simp)
      have hc0 : c ≠ 0 := by intro h; rw [h] at hbc; exact absurd hbc (by simp)
      have hck : c ≠ (k.succ : Fin (e :: x :: l').length) := by
        intro h
        have hp : partner (e :: x :: l') (GUEPairing.cons e (x :: l') k p) a =
            (k.succ : Fin (e :: x :: l').length) := by rw [hcr.1, h]
        exact ha0 (eq_zero_of_partner_eq_head k p a hp)
      have hb0 : b ≠ 0 := by intro h; rw [h] at hab; exact absurd hab (by simp)
      have hbk : b ≠ (k.succ : Fin (e :: x :: l').length) := by
        intro h
        have hp : partner (e :: x :: l') (GUEPairing.cons e (x :: l') k p) b = 0 := by
          rw [h, partner_cons_head e x l' k p _ rfl]
        have hd : d = 0 := by rw [← hcr.2, hp]
        rw [hd] at hcd
        exact absurd hcd (by simp)
      have hd0 : d ≠ 0 := by intro h; rw [h] at hcd; exact absurd hcd (by simp)
      have hdk : d ≠ (k.succ : Fin (e :: x :: l').length) := by
        intro h
        have hp : partner (e :: x :: l') (GUEPairing.cons e (x :: l') k p) b =
            (k.succ : Fin (e :: x :: l').length) := by rw [hcr.2, h]
        exact hb0 (eq_zero_of_partner_eq_head k p b hp)
      obtain ⟨qa, hqa⟩ := exists_origIdx k a ha0 hak
      obtain ⟨qb, hqb⟩ := exists_origIdx k b hb0 hbk
      obtain ⟨qc, hqc⟩ := exists_origIdx k c hc0 hck
      obtain ⟨qd, hqd⟩ := exists_origIdx k d hd0 hdk
      have hpac : partnerE k p hlen qa = qc := by
        apply origIdx_injective k
        rw [← partner_cons_origE k p hlen qa, hqa, hcr.1, hqc]
      have hpbd : partnerE k p hlen qb = qd := by
        apply origIdx_injective k
        rw [← partner_cons_origE k p hlen qb, hqb, hcr.2, hqd]
      have hab' : qa.val < qb.val := by
        by_contra h
        push Not at h
        have := (origIdx_strictMono (e := e) (l' := l') k).monotone (Fin.le_def.mpr h)
        rw [hqa, hqb, Fin.le_def] at this
        omega
      have hbc' : qb.val < qc.val := by
        by_contra h
        push Not at h
        have := (origIdx_strictMono (e := e) (l' := l') k).monotone (Fin.le_def.mpr h)
        rw [hqb, hqc, Fin.le_def] at this
        omega
      have hcd' : qc.val < qd.val := by
        by_contra h
        push Not at h
        have := (origIdx_strictMono (e := e) (l' := l') k).monotone (Fin.le_def.mpr h)
        rw [hqc, hqd, Fin.le_def] at this
        omega
      exact hNC qa qb qc qd hab' hbc' hcd' ⟨hpac, hpbd⟩

/-- Inclusion of the first block of a concatenation. -/
def liftFst (l₁ l₂ : List (GUEEntry ι N)) (i : Fin l₁.length) : Fin (l₁ ++ l₂).length :=
  ⟨i.val, by rw [List.length_append]; exact Nat.lt_add_right _ i.isLt⟩

/-- Inclusion of the second block of a concatenation. -/
def liftSnd (l₁ l₂ : List (GUEEntry ι N)) (j : Fin l₂.length) : Fin (l₁ ++ l₂).length :=
  ⟨l₁.length + j.val, by rw [List.length_append]; omega⟩

@[simp] lemma liftFst_val (l₁ l₂ : List (GUEEntry ι N)) (i : Fin l₁.length) :
    (liftFst l₁ l₂ i).val = i.val := rfl

@[simp] lemma liftSnd_val (l₁ l₂ : List (GUEEntry ι N)) (j : Fin l₂.length) :
    (liftSnd l₁ l₂ j).val = l₁.length + j.val := rfl

lemma liftFst_lt (l₁ l₂ : List (GUEEntry ι N)) (i : Fin l₁.length) :
    (liftFst l₁ l₂ i).val < l₁.length := i.isLt

lemma liftSnd_ge (l₁ l₂ : List (GUEEntry ι N)) (j : Fin l₂.length) :
    l₁.length ≤ (liftSnd l₁ l₂ j).val := Nat.le_add_right _ _

/-- Transport of the partner in the first block of a juxtaposition. -/
theorem partner_liftFst (l₁ l₂ : List (GUEEntry ι N)) (p₁ : GUEPairing l₁)
    (p₂ : GUEPairing l₂) (i : Fin l₁.length) :
    partner (l₁ ++ l₂) (GUEPairing.append l₁ l₂ p₁ p₂) (liftFst l₁ l₂ i) =
      liftFst l₁ l₂ (partner l₁ p₁ i) := by
  apply Fin.ext
  exact (GUEPairing.partner_append_aux l₁.length l₁ rfl l₂ p₁ p₂).1 i

/-- Transport of the partner in the second block of a juxtaposition. -/
theorem partner_liftSnd (l₁ l₂ : List (GUEEntry ι N)) (p₁ : GUEPairing l₁)
    (p₂ : GUEPairing l₂) (j : Fin l₂.length) :
    partner (l₁ ++ l₂) (GUEPairing.append l₁ l₂ p₁ p₂) (liftSnd l₁ l₂ j) =
      liftSnd l₁ l₂ (partner l₂ p₂ j) := by
  apply Fin.ext
  exact (GUEPairing.partner_append_aux l₁.length l₁ rfl l₂ p₁ p₂).2 j

/-- A position of a concatenation lies in one of the two blocks. -/
lemma eq_lift_of_append (l₁ l₂ : List (GUEEntry ι N)) (i : Fin (l₁ ++ l₂).length) :
    (∃ a : Fin l₁.length, liftFst l₁ l₂ a = i) ∨ ∃ b : Fin l₂.length, liftSnd l₁ l₂ b = i := by
  by_cases h : i.val < l₁.length
  · exact Or.inl ⟨⟨i.val, h⟩, Fin.ext rfl⟩
  · refine Or.inr ⟨⟨i.val - l₁.length, by
      have hi := i.isLt
      have hlen : (l₁ ++ l₂).length = l₁.length + l₂.length := List.length_append
      omega⟩, Fin.ext ?_⟩
    simp only [liftSnd_val]
    omega

lemma liftFst_injective (l₁ l₂ : List (GUEEntry ι N)) :
    Function.Injective (liftFst l₁ l₂) := by
  intro i j h
  exact Fin.ext (by simpa using congrArg Fin.val h)

lemma liftSnd_injective (l₁ l₂ : List (GUEEntry ι N)) :
    Function.Injective (liftSnd l₁ l₂) := by
  intro i j h
  have hv := congrArg Fin.val h
  simp only [liftSnd_val] at hv
  exact Fin.ext (by omega)

lemma exists_liftFst (l₁ l₂ : List (GUEEntry ι N)) (i : Fin (l₁ ++ l₂).length)
    (h : i.val < l₁.length) : ∃ a : Fin l₁.length, liftFst l₁ l₂ a = i :=
  ⟨⟨i.val, h⟩, Fin.ext rfl⟩

lemma exists_liftSnd (l₁ l₂ : List (GUEEntry ι N)) (i : Fin (l₁ ++ l₂).length)
    (h : l₁.length ≤ i.val) : ∃ b : Fin l₂.length, liftSnd l₁ l₂ b = i := by
  have hlen : (l₁ ++ l₂).length = l₁.length + l₂.length := List.length_append
  have hi := i.isLt
  exact ⟨⟨i.val - l₁.length, by omega⟩, Fin.ext (by simp only [liftSnd_val]; omega)⟩

lemma eq_of_partner_liftFst (l₁ l₂ : List (GUEEntry ι N)) (p₁ : GUEPairing l₁)
    (p₂ : GUEPairing l₂) {i j : Fin l₁.length}
    (h : partner (l₁ ++ l₂) (GUEPairing.append l₁ l₂ p₁ p₂) (liftFst l₁ l₂ i) =
      liftFst l₁ l₂ j) : partner l₁ p₁ i = j :=
  liftFst_injective l₁ l₂ (by rw [← partner_liftFst]; exact h)

lemma eq_of_partner_liftSnd (l₁ l₂ : List (GUEEntry ι N)) (p₁ : GUEPairing l₁)
    (p₂ : GUEPairing l₂) {i j : Fin l₂.length}
    (h : partner (l₁ ++ l₂) (GUEPairing.append l₁ l₂ p₁ p₂) (liftSnd l₁ l₂ i) =
      liftSnd l₁ l₂ j) : partner l₂ p₂ i = j :=
  liftSnd_injective l₁ l₂ (by rw [← partner_liftSnd]; exact h)

/-- **Non-crossing pairings of a juxtaposition.**  A juxtaposed pairing is non-crossing iff both
of its blocks are. -/
theorem isNonCrossing_append (l₁ l₂ : List (GUEEntry ι N)) (p₁ : GUEPairing l₁)
    (p₂ : GUEPairing l₂) :
    IsNonCrossing (GUEPairing.append l₁ l₂ p₁ p₂) ↔ IsNonCrossing p₁ ∧ IsNonCrossing p₂ := by
  unfold IsNonCrossing
  simp only [partnerPerm_apply]
  constructor
  · intro hnc
    constructor
    · rintro a b c d hab hbc hcd ⟨hac, hbd⟩
      refine hnc (liftFst l₁ l₂ a) (liftFst l₁ l₂ b) (liftFst l₁ l₂ c) (liftFst l₁ l₂ d)
        (by simpa using hab) (by simpa using hbc) (by simpa using hcd) ⟨?_, ?_⟩
      · rw [partner_liftFst, hac]
      · rw [partner_liftFst, hbd]
    · rintro a b c d hab hbc hcd ⟨hac, hbd⟩
      have hlt : ∀ j : Fin l₂.length, (liftSnd l₁ l₂ j).val = l₁.length + j.val := fun j => rfl
      refine hnc (liftSnd l₁ l₂ a) (liftSnd l₁ l₂ b) (liftSnd l₁ l₂ c) (liftSnd l₁ l₂ d)
        (by simp only [hlt]; omega) (by simp only [hlt]; omega) (by simp only [hlt]; omega)
        ⟨?_, ?_⟩
      · rw [partner_liftSnd, hac]
      · rw [partner_liftSnd, hbd]
  · rintro ⟨h₁, h₂⟩ a b c d hab hbc hcd ⟨hac, hbd⟩
    -- the partner of a position in the first block stays in the first block
    have hside : ∀ i : Fin (l₁ ++ l₂).length,
        (partner (l₁ ++ l₂) (GUEPairing.append l₁ l₂ p₁ p₂) i).val < l₁.length ↔
          i.val < l₁.length := by
      intro i
      rcases eq_lift_of_append l₁ l₂ i with ⟨a, rfl⟩ | ⟨b, rfl⟩
      · rw [partner_liftFst]
        constructor
        · intro _; exact liftFst_lt l₁ l₂ a
        · intro _; exact liftFst_lt l₁ l₂ (partner l₁ p₁ a)
      · rw [partner_liftSnd]
        constructor
        · intro h
          exact absurd h (by simpa using liftSnd_ge l₁ l₂ (partner l₂ p₂ b))
        · intro h
          exact absurd h (by simpa using liftSnd_ge l₁ l₂ b)
    have hca : c.val < l₁.length ↔ a.val < l₁.length := by
      rw [← hac]; exact hside _
    have hdb : d.val < l₁.length ↔ b.val < l₁.length := by
      rw [← hbd]; exact hside _
    by_cases ha1 : a.val < l₁.length
    · -- the first position is in the first block
      have hc1 : c.val < l₁.length := hca.mpr ha1
      by_cases hb1 : b.val < l₁.length
      · have hd1 : d.val < l₁.length := hdb.mpr hb1
        obtain ⟨a', rfl⟩ := exists_liftFst l₁ l₂ a ha1
        obtain ⟨b', rfl⟩ := exists_liftFst l₁ l₂ b hb1
        obtain ⟨c', rfl⟩ := exists_liftFst l₁ l₂ c hc1
        obtain ⟨d', rfl⟩ := exists_liftFst l₁ l₂ d hd1
        refine h₁ a' b' c' d' (by simpa using hab) (by simpa using hbc) (by simpa using hcd)
          ⟨eq_of_partner_liftFst l₁ l₂ p₁ p₂ hac, eq_of_partner_liftFst l₁ l₂ p₁ p₂ hbd⟩
      · have hb2 : l₁.length ≤ b.val := by omega
        omega
    · -- the first position is in the second block
      have ha2 : l₁.length ≤ a.val := by omega
      have hb2 : l₁.length ≤ b.val := by omega
      have hc2 : l₁.length ≤ c.val := by omega
      have hd2 : l₁.length ≤ d.val := by
        rcases Nat.lt_or_ge d.val l₁.length with h | h
        · have : b.val < l₁.length := hdb.mp h
          omega
        · exact h
      obtain ⟨a', rfl⟩ := exists_liftSnd l₁ l₂ a ha2
      obtain ⟨b', rfl⟩ := exists_liftSnd l₁ l₂ b hb2
      obtain ⟨c', rfl⟩ := exists_liftSnd l₁ l₂ c hc2
      obtain ⟨d', rfl⟩ := exists_liftSnd l₁ l₂ d hd2
      refine h₂ a' b' c' d' ?_ ?_ ?_
        ⟨eq_of_partner_liftSnd l₁ l₂ p₁ p₂ hac, eq_of_partner_liftSnd l₁ l₂ p₁ p₂ hbd⟩
      · simpa using hab
      · simpa using hbc
      · simpa using hcd

/-- Deleting the `n`-th entry is taking the prefix and skipping one entry. -/
theorem eraseIdx_eq_take_append_drop {α : Type*} (l : List α) (n : ℕ) :
    l.eraseIdx n = l.take n ++ l.drop (n + 1) := by
  induction l generalizing n with
  | nil => cases n <;> rfl
  | cons a t ih =>
    match n with
    | 0 => rfl
    | m + 1 =>
      rw [List.eraseIdx_cons_succ, List.take_succ_cons, List.drop_succ_cons, ih m]
      rfl

/-- The prefix of the erased list is the prefix of the original list. -/
theorem take_eraseIdx {α : Type*} (l : List α) (k : Fin l.length) :
    (l.eraseIdx k.val).take k.val = l.take k.val :=
  List.take_eraseIdx_eq_take_of_le l k.val k.val (le_refl _)

/-- The tail of the erased list is the tail of the original list. -/
theorem drop_eraseIdx {α : Type*} (l : List α) (k : Fin l.length) :
    (l.eraseIdx k.val).drop k.val = l.drop (k.val + 1) := by
  rw [eraseIdx_eq_take_append_drop, List.drop_append]
  have hlen : (l.take k.val).length = k.val := by
    rw [List.length_take]
    omega
  simp [hlen]

/-- Splitting the prefix off an erased list. -/
theorem eq_take_append_drop_eraseIdx {α : Type*} (l : List α) (k : Fin l.length) :
    l.eraseIdx k.val = (l.eraseIdx k.val).take k.val ++ (l.eraseIdx k.val).drop k.val :=
  (List.take_append_drop _ _).symm

/-- The partner of a cast position in `partnerE` coordinates. -/
lemma partnerE_cast (k : Fin (x :: l').length) (p : GUEPairing ((x :: l').eraseIdx k))
    (hlen : ((x :: l').eraseIdx k).length = l'.length)
    (q : Fin ((x :: l').eraseIdx k).length) :
    partnerE k p hlen (Fin.cast hlen q) = Fin.cast hlen (partner ((x :: l').eraseIdx k) p q) := by
  rw [partnerE_apply, Fin.cast_cast]
  simp

/-- The erased-coordinate non-crossing condition is the non-crossing condition of the erased
pairing. -/
theorem isNCRel_iff (k : Fin (x :: l').length) (p : GUEPairing ((x :: l').eraseIdx k))
    (hlen : ((x :: l').eraseIdx k).length = l'.length) :
    IsNCRel k p hlen ↔ IsNonCrossing p := by
  unfold IsNCRel IsNonCrossing
  simp only [partnerPerm_apply]
  constructor
  · intro h a b c d hab hbc hcd hcr
    refine h (Fin.cast hlen a) (Fin.cast hlen b) (Fin.cast hlen c) (Fin.cast hlen d)
      (by simpa using hab) (by simpa using hbc) (by simpa using hcd) ⟨?_, ?_⟩
    · rw [partnerE_cast, hcr.1]
    · rw [partnerE_cast, hcr.2]
  · intro h a b c d hab hbc hcd hcr
    refine h (Fin.cast hlen.symm a) (Fin.cast hlen.symm b) (Fin.cast hlen.symm c)
      (Fin.cast hlen.symm d) (by simpa using hab) (by simpa using hbc) (by simpa using hcd)
      ⟨?_, ?_⟩
    · have hp : partnerE k p hlen a =
          Fin.cast hlen (partner ((x :: l').eraseIdx k) p (Fin.cast hlen.symm a)) := by
        simpa using partnerE_cast k p hlen (Fin.cast hlen.symm a)
      rw [hcr.1] at hp
      have h2 := congrArg (Fin.cast hlen.symm) hp
      simpa using h2.symm
    · have hp : partnerE k p hlen b =
          Fin.cast hlen (partner ((x :: l').eraseIdx k) p (Fin.cast hlen.symm b)) := by
        simpa using partnerE_cast k p hlen (Fin.cast hlen.symm b)
      rw [hcr.2] at hp
      have h2 := congrArg (Fin.cast hlen.symm) hp
      simpa using h2.symm

/-- The erased-coordinate block-diagonality condition is the cut condition on the erased
pairing. -/
theorem isBlockDiagRel_iff (k : Fin (x :: l').length) (p : GUEPairing ((x :: l').eraseIdx k))
    (hlen : ((x :: l').eraseIdx k).length = l'.length) :
    IsBlockDiagRel k p hlen ↔
      ∀ q : Fin ((x :: l').eraseIdx k).length,
        q.val < k.val → (partner ((x :: l').eraseIdx k) p q).val < k.val := by
  unfold IsBlockDiagRel
  constructor
  · intro h q hq
    have := h (Fin.cast hlen q) (by simpa using hq)
    rwa [partnerE_cast] at this
  · intro h q hq
    have := h (Fin.cast hlen.symm q) (by simpa using hq)
    have hp : partnerE k p hlen q =
        Fin.cast hlen (partner ((x :: l').eraseIdx k) p (Fin.cast hlen.symm q)) := by
      simpa using partnerE_cast k p hlen (Fin.cast hlen.symm q)
    rw [hp]
    simpa using this

end GUEPairing

/-- The label-weighted non-crossing pairing sum of a list of GUE entries. -/
def ncLabelSum (K : List (GUEEntry ι N)) : ℂ :=
  ∑ p ∈ (Finset.univ : Finset (GUEPairing K)).filter IsNonCrossing, gueLabelWeight K p

namespace GUEPairing

/-- Non-crossing is invariant under a length-preserving cast of pairings. -/
theorem isNonCrossing_castLength {l₁ l₂ : List (GUEEntry ι N)} (h : l₁.length = l₂.length)
    (p : GUEPairing l₁) : IsNonCrossing (GUEPairing.castLength l₁ l₂ h p) ↔ IsNonCrossing p := by
  unfold IsNonCrossing
  simp only [partnerPerm_apply]
  constructor
  · intro hnc a b c d hab hbc hcd hcr
    refine hnc (Fin.cast h a) (Fin.cast h b) (Fin.cast h c) (Fin.cast h d)
      (by simpa using hab) (by simpa using hbc) (by simpa using hcd) ⟨?_, ?_⟩
    · rw [GUEPairing.partner_castLength]; exact congrArg (Fin.cast h) hcr.1
    · rw [GUEPairing.partner_castLength]; exact congrArg (Fin.cast h) hcr.2
  · intro hnc a b c d hab hbc hcd hcr
    refine hnc (Fin.cast h.symm a) (Fin.cast h.symm b) (Fin.cast h.symm c) (Fin.cast h.symm d)
      (by simpa using hab) (by simpa using hbc) (by simpa using hcd) ⟨?_, ?_⟩
    · have hp : partner l₂ (GUEPairing.castLength l₁ l₂ h p) a =
          Fin.cast h (partner l₁ p (Fin.cast h.symm a)) := by
        simpa using GUEPairing.partner_castLength p l₂ h (Fin.cast h.symm a)
      rw [hcr.1] at hp
      have h2 := congrArg (Fin.cast h.symm) hp
      simpa using h2.symm
    · have hp : partner l₂ (GUEPairing.castLength l₁ l₂ h p) b =
          Fin.cast h (partner l₁ p (Fin.cast h.symm b)) := by
        simpa using GUEPairing.partner_castLength p l₂ h (Fin.cast h.symm b)
      rw [hcr.2] at hp
      have h2 := congrArg (Fin.cast h.symm) hp
      simpa using h2.symm

/-- The cut condition is invariant under a length-preserving cast of pairings. -/
theorem cut_castLength {l₁ l₂ : List (GUEEntry ι N)} (h : l₁.length = l₂.length) (m : ℕ)
    (p : GUEPairing l₁) :
    (∀ q : Fin l₂.length, q.val < m →
        (partner l₂ (GUEPairing.castLength l₁ l₂ h p) q).val < m) ↔
      ∀ q : Fin l₁.length, q.val < m → (partner l₁ p q).val < m := by
  constructor
  · intro hq q hqm
    have hcast := hq (Fin.cast h q) (by simpa using hqm)
    rwa [GUEPairing.partner_castLength] at hcast
  · intro hq q hqm
    have hp : partner l₂ (GUEPairing.castLength l₁ l₂ h p) q =
        Fin.cast h (partner l₁ p (Fin.cast h.symm q)) := by
      simpa using GUEPairing.partner_castLength p l₂ h (Fin.cast h.symm q)
    rw [hp]
    have hq' := hq (Fin.cast h.symm q) (by simpa using hqm)
    simpa using hq'

/-- The label weight is invariant under a cast between equal lists. -/
theorem gueLabelWeight_castLength_eq {l₁ l₂ : List (GUEEntry ι N)} (h : l₁ = l₂)
    (p : GUEPairing l₁) :
    gueLabelWeight l₂ (GUEPairing.castLength l₁ l₂ (congrArg List.length h) p) =
      gueLabelWeight l₁ p := by
  subst h
  exact (GUEPairing.gueLabelWeight_castLength p l₁ rfl (fun i => rfl)).symm

/-- **The non-crossing label sum of a juxtaposition factorizes** over the two blocks: summing the
label weights of the non-crossing pairings that do not cross the block boundary gives the product
of the two single-block non-crossing label sums. -/
theorem sum_split_nc (A B : List (GUEEntry ι N)) :
    (∑ q : GUEPairing (A ++ B),
        (if (NoCrossList A B q ∧ IsNonCrossing q) then gueLabelWeight (A ++ B) q else 0))
      = ncLabelSum A * ncLabelSum B := by
  have hbd : ∀ q : GUEPairing (A ++ B), NoCrossList A B q ↔ BlockDiag A B q :=
    fun q => ⟨fun h => blockDiag_of_noCross q h, fun h => noCross_of_blockDiag q h⟩
  -- Step 1: the indicator sum over cut-respecting non-crossing pairings
  have hstep1 : (∑ q : GUEPairing (A ++ B),
        (if (NoCrossList A B q ∧ IsNonCrossing q) then gueLabelWeight (A ++ B) q else 0))
      = ∑ q : {q : GUEPairing (A ++ B) // NoCrossList A B q ∧ IsNonCrossing q},
          gueLabelWeight (A ++ B) q.val := by
    rw [← Finset.sum_filter]
    exact Finset.sum_subtype
      (s := Finset.univ.filter (fun q : GUEPairing (A ++ B) =>
        NoCrossList A B q ∧ IsNonCrossing q))
      (p := fun q : GUEPairing (A ++ B) => NoCrossList A B q ∧ IsNonCrossing q)
      (h := fun q => by
        constructor
        · intro h; exact (Finset.mem_filter.mp h).2
        · intro h; exact Finset.mem_filter.mpr ⟨Finset.mem_univ q, h⟩)
      (f := fun q => gueLabelWeight (A ++ B) q)
  -- Step 2: replace cut-respecting by block diagonal and pull out the indicator
  have hstep2 : (∑ q : {q : GUEPairing (A ++ B) // NoCrossList A B q ∧ IsNonCrossing q},
        gueLabelWeight (A ++ B) q.val)
      = ∑ y : {q : GUEPairing (A ++ B) // BlockDiag A B q},
          (if IsNonCrossing y.val then gueLabelWeight (A ++ B) y.val else 0) := by
    have h1 : (∑ q : {q : GUEPairing (A ++ B) // NoCrossList A B q ∧ IsNonCrossing q},
        gueLabelWeight (A ++ B) q.val)
        = ∑ q ∈ (Finset.univ : Finset (GUEPairing (A ++ B))).filter
            (fun q => NoCrossList A B q ∧ IsNonCrossing q), gueLabelWeight (A ++ B) q :=
      (Finset.sum_subtype
        (s := Finset.univ.filter (fun q : GUEPairing (A ++ B) =>
          NoCrossList A B q ∧ IsNonCrossing q))
        (p := fun q : GUEPairing (A ++ B) => NoCrossList A B q ∧ IsNonCrossing q)
        (h := fun q => by
          constructor
          · intro h; exact (Finset.mem_filter.mp h).2
          · intro h; exact Finset.mem_filter.mpr ⟨Finset.mem_univ q, h⟩)
        (f := fun q => gueLabelWeight (A ++ B) q)).symm
    have h2 : (∑ y : {q : GUEPairing (A ++ B) // BlockDiag A B q},
          (if IsNonCrossing y.val then gueLabelWeight (A ++ B) y.val else 0))
        = ∑ q ∈ (Finset.univ : Finset (GUEPairing (A ++ B))).filter
            (fun q => BlockDiag A B q), (if IsNonCrossing q then gueLabelWeight (A ++ B) q else 0) :=
      (Finset.sum_subtype
        (s := Finset.univ.filter (fun q : GUEPairing (A ++ B) => BlockDiag A B q))
        (p := fun q : GUEPairing (A ++ B) => BlockDiag A B q)
        (h := fun q => by
          constructor
          · intro h; exact (Finset.mem_filter.mp h).2
          · intro h; exact Finset.mem_filter.mpr ⟨Finset.mem_univ q, h⟩)
        (f := fun q => if IsNonCrossing q then gueLabelWeight (A ++ B) q else 0)).symm
    rw [h1, h2, ← Finset.sum_filter, Finset.filter_filter]
    apply Finset.sum_congr
    · apply Finset.filter_congr
      intro q _
      constructor
      · rintro ⟨h, hnc⟩; exact ⟨(hbd q).mp h, hnc⟩
      · rintro ⟨h, hnc⟩; exact ⟨(hbd q).mpr h, hnc⟩
    · intro q _
      rfl
  rw [hstep1, hstep2]
  -- Step 3: decompose a block diagonal pairing into its two blocks
  rw [← Equiv.sum_comp (GUEPairing.blockDiagEquiv A B)
    (fun q : {q : GUEPairing (A ++ B) // BlockDiag A B q} =>
      if IsNonCrossing q.val then gueLabelWeight (A ++ B) q.val else 0)]
  -- Step 4: the product of the two single-block sums
  rw [Fintype.sum_prod_type]
  have hfac : ∀ (a : GUEPairing A) (b : GUEPairing B),
      (if IsNonCrossing (GUEPairing.append A B a b) then
          gueLabelWeight (A ++ B) (GUEPairing.append A B a b) else 0) =
      (if IsNonCrossing a then gueLabelWeight A a else 0) *
        (if IsNonCrossing b then gueLabelWeight B b else 0) := by
    intro a b
    by_cases ha : IsNonCrossing a <;> by_cases hb : IsNonCrossing b
    · rw [if_pos ((isNonCrossing_append A B a b).mpr ⟨ha, hb⟩), if_pos ha, if_pos hb,
        gueLabelWeight_append a b]
    · rw [if_neg (fun h => hb ((isNonCrossing_append A B a b).mp h).2), if_pos ha, if_neg hb,
        mul_zero]
    · rw [if_neg (fun h => ha ((isNonCrossing_append A B a b).mp h).1), if_neg ha, zero_mul]
    · rw [if_neg (fun h => ha ((isNonCrossing_append A B a b).mp h).1), if_neg ha, zero_mul]
  simp_rw [show ∀ (x : GUEPairing A) (y : GUEPairing B),
      ((GUEPairing.blockDiagEquiv A B) (x, y)).val = GUEPairing.append A B x y from
    fun x y => rfl]
  simp_rw [hfac]
  rw [← Finset.sum_mul_sum]
  rw [ncLabelSum, ncLabelSum, ← Finset.sum_filter, ← Finset.sum_filter]

/-- `NoCrossList` as a threshold condition on all positions of the concatenation. -/
lemma noCrossList_iff (A B : List (GUEEntry ι N)) (q : GUEPairing (A ++ B)) :
    NoCrossList A B q ↔
      ∀ i : Fin (A ++ B).length, i.val < A.length →
        (partner (A ++ B) q i).val < A.length := by
  unfold NoCrossList
  constructor
  · intro h i hi
    exact h ⟨i.val, hi⟩
  · intro h i
    exact h (liftFst A B i) (liftFst_lt A B i)

/-- **One step of the head-partner recursion for the non-crossing label sum.**  The erased pairing
sum for a fixed partner `k` of the head factorizes into the two blocks of the erased list. -/
theorem ncLabelSum_cons_step (e x : GUEEntry ι N) (l' : List (GUEEntry ι N))
    (k : Fin (x :: l').length) :
    (∑ p' : GUEPairing ((x :: l').eraseIdx k),
        (if IsNonCrossing (GUEPairing.cons e (x :: l') k p')
          then gueLabelWeight ((x :: l').eraseIdx k) p' else 0))
      = ncLabelSum ((x :: l').take k.val) * ncLabelSum ((x :: l').drop (k.val + 1)) := by
  classical
  have hEq : (x :: l').eraseIdx k.val = (x :: l').take k.val ++ (x :: l').drop (k.val + 1) :=
    eraseIdx_eq_take_append_drop (x :: l') k.val
  have hE : ((x :: l').eraseIdx k.val).length =
      ((x :: l').take k.val ++ (x :: l').drop (k.val + 1)).length := congrArg List.length hEq
  have hlen : ((x :: l').eraseIdx k).length = l'.length := by
    rw [List.length_eraseIdx, if_pos k.isLt]
    simp
  have hA : ((x :: l').take k.val).length = k.val := by
    rw [List.length_take]
    omega
  refine Eq.trans ?_ (sum_split_nc ((x :: l').take k.val) ((x :: l').drop (k.val + 1)))
  rw [← GUEPairing.sum_castLength hE
    (fun q : GUEPairing ((x :: l').take k.val ++ (x :: l').drop (k.val + 1)) =>
      if (NoCrossList ((x :: l').take k.val) ((x :: l').drop (k.val + 1)) q ∧ IsNonCrossing q)
      then gueLabelWeight ((x :: l').take k.val ++ (x :: l').drop (k.val + 1)) q else 0)]
  apply Finset.sum_congr rfl
  intro p' _
  have hiff : IsNonCrossing (GUEPairing.cons e (x :: l') k p') ↔
      (NoCrossList ((x :: l').take k.val) ((x :: l').drop (k.val + 1))
          (GUEPairing.castLength ((x :: l').eraseIdx k.val)
            ((x :: l').take k.val ++ (x :: l').drop (k.val + 1)) hE p') ∧
        IsNonCrossing (GUEPairing.castLength ((x :: l').eraseIdx k.val)
          ((x :: l').take k.val ++ (x :: l').drop (k.val + 1)) hE p')) := by
    rw [isNonCrossing_cons_iff k p' hlen, isBlockDiagRel_iff k p' hlen, isNCRel_iff k p' hlen]
    rw [← cut_castLength hE k.val p', ← isNonCrossing_castLength hE p', noCrossList_iff]
    constructor
    · rintro ⟨hcut, hnc⟩
      refine ⟨fun i hi => ?_, hnc⟩
      have hp := hcut i (by rw [hA] at hi; exact hi)
      rw [hA]
      exact hp
    · rintro ⟨hcut, hnc⟩
      refine ⟨fun i hi => ?_, hnc⟩
      have hp := hcut i (by rw [hA]; exact hi)
      rw [hA] at hp
      exact hp
  have hW : gueLabelWeight ((x :: l').take k.val ++ (x :: l').drop (k.val + 1))
      (GUEPairing.castLength ((x :: l').eraseIdx k.val)
        ((x :: l').take k.val ++ (x :: l').drop (k.val + 1)) hE p')
      = gueLabelWeight ((x :: l').eraseIdx k.val) p' :=
    gueLabelWeight_castLength_eq hEq p'
  by_cases h : IsNonCrossing (GUEPairing.cons e (x :: l') k p')
  · rw [if_pos h, if_pos (hiff.mp h), hW]
  · rw [if_neg h, if_neg (fun hh => h (hiff.mpr hh))]

/-- **First-partner recursion for the non-crossing label sum.**  Pairing the head `e` with a
position `k` of `x :: l'` leaves the interior `(x :: l').take k` and the exterior
`(x :: l').drop (k+1)` as independent blocks. -/
theorem ncLabelSum_cons (e x : GUEEntry ι N) (l' : List (GUEEntry ι N)) :
    ncLabelSum (e :: x :: l') =
      ∑ k : Fin (x :: l').length, gueLabelCov e ((x :: l').get k) *
        (ncLabelSum ((x :: l').take k.val) * ncLabelSum ((x :: l').drop (k.val + 1))) := by
  classical
  rw [ncLabelSum, Finset.sum_filter]
  rw [Fintype.sum_equiv (GUEPairing.consEquiv e (x :: l'))
    (fun p : GUEPairing (e :: x :: l') =>
      if IsNonCrossing p then gueLabelWeight (e :: x :: l') p else 0)
    (fun s : Sigma (fun k : Fin (x :: l').length => GUEPairing ((x :: l').eraseIdx k)) =>
      if IsNonCrossing (GUEPairing.cons e (x :: l') s.1 s.2)
      then gueLabelWeight (e :: x :: l') (GUEPairing.cons e (x :: l') s.1 s.2) else 0)
    (fun p => by cases p; rfl)]
  rw [sum_sigma_univ]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [gueLabelWeight_cons]
  have hfac : ∀ p' : GUEPairing ((x :: l').eraseIdx k),
      (if IsNonCrossing (GUEPairing.cons e (x :: l') k p')
        then gueLabelCov e ((x :: l').get k) * gueLabelWeight ((x :: l').eraseIdx k) p' else 0)
      = gueLabelCov e ((x :: l').get k) *
        (if IsNonCrossing (GUEPairing.cons e (x :: l') k p')
          then gueLabelWeight ((x :: l').eraseIdx k) p' else 0) := by
    intro p'
    by_cases h : IsNonCrossing (GUEPairing.cons e (x :: l') k p') <;> simp [h]
  simp_rw [hfac]
  rw [← Finset.mul_sum, ncLabelSum_cons_step]

end GUEPairing

end

end GUEStrongConvergence
