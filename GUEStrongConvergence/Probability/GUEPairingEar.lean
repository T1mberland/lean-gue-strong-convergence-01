/-
# The ear lemma for non-crossing pairings

A pairing of entry positions is **non-crossing** when no four positions `a < b < c < d` are paired
as `a ↔ c` and `b ↔ d` (the two chords interleave).  Such a pairing always contains an **ear**:
two cyclically consecutive positions that are paired with each other.

The mathematical content is proved at the level of permutations of `Fin n`: for a fixed-point-free
involution `σ` without interleaving chords there is an index `i` with `σ i = finRotate n i`.

Main results of this file:

* `interval_closed_of_chord`: a chord `a -- c` (`a < c`) has its open interval `(a, c)` closed
  under `σ`.
* `exists_adjacent_in_interval`: a `σ`-closed interval with at least two interior points contains
  an adjacent pair (`σ x = x + 1`).
* `exists_ear_of_nonCrossing`: a non-crossing fixed-point-free involution has an ear.
* `hasEar_of_isNonCrossing`: the same statement for GUE pairings.

Ear removal and the exact face count:

* `noInterleaving_conjBy_finRotate(_pow)`: the crossing-free condition is invariant under cyclic
  rotation of the positions.
* `compressedPerm`: deleting a wrap ear (`σ last = 0`) compresses the pairing involution to
  `Fin n`; `compressedPerm_mul_self`, `compressedPerm_ne_self`, `noInterleaving_compressedPerm`.
* `ear_removal_wrap_count`: `c (finRotate (n+2) * σ) = c (finRotate n * compressedPerm) + 1`.
* `exists_ear_removal`: the same decrement for an ear at an arbitrary position (after a cyclic
  shift), including the inheritance of the crossing-free condition.
* `permOrbitCount_eq_of_noInterleaving(_two_mul)`: a crossing-free fixed-point-free involution of
  `Fin (2*m)` has exactly `m + 1` face orbits.
* `pairOrbitCount_eq_iff_isNonCrossing`: for a pairing of `2*m` positions (`m ≥ 1`),
  `pairOrbitCount p = m + 1 ↔ IsNonCrossing p`.

The ear-existence induction is on the width `hi - lo` of the interval, so no cyclic gap case
analysis is needed; the removal is proved by the split/merge law for orbit counts.  No
`sorry`/axiom is used.
-/
import GUEStrongConvergence.Probability.GUEPairingGenusSplit
import GUEStrongConvergence.Probability.GUEWordVarianceGenus

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

/-! ### Interval closure -/

/-- A crossing-free involution: `NoInterleaving σ` forbids two interleaving chords `a < b < c < d`
with `σ a = c` and `σ b = d`. -/
def NoInterleaving {n : ℕ} (σ : Equiv.Perm (Fin n)) : Prop :=
  ∀ a b c d : Fin n, a.val < b.val → b.val < c.val → c.val < d.val →
    ¬ (σ a = c ∧ σ b = d)

/-- Value of the cyclic shift at an index whose successor is not the last one. -/
theorem finRotate_val_of_succ_lt {n : ℕ} {x : Fin n} (h : x.val + 1 < n) :
    (finRotate n x).val = x.val + 1 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  have hx : x.val < m := by simpa using h
  rw [show x = (⟨x.val, by omega⟩ : Fin (m + 1)) from Fin.ext rfl, finRotate_of_lt hx]

/-- Value of the cyclic shift, in general. -/
theorem finRotate_val_eq (n : ℕ) (y : Fin n) :
    (finRotate n y).val = if y.val + 1 < n then y.val + 1 else 0 := by
  by_cases h : y.val + 1 < n
  · rw [if_pos h]
    exact finRotate_val_of_succ_lt h
  · rw [if_neg h]
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    have hy : y = Fin.last m := by
      apply Fin.ext
      rw [Fin.val_last]
      simp at h ⊢
      omega
    rw [hy, finRotate_last]
    rfl

/-- **Interval closure**: if `σ a = c` with `a < c`, then the open interval `(a, c)` is closed
under `σ`; otherwise the chord `a -- c` interleaves with the chord through the offending point. -/
theorem interval_closed_of_chord {n : ℕ} {σ : Equiv.Perm (Fin n)} (hinv : ∀ x, σ (σ x) = x)
    (hnc : NoInterleaving σ) {a c : Fin n} (hac : a.val < c.val) (hchord : σ a = c)
    {x : Fin n} (h1 : a.val < x.val) (h2 : x.val < c.val) :
    a.val < (σ x).val ∧ (σ x).val < c.val := by
  have hxa : σ x ≠ a := by
    intro h
    have hxc : x = c := by
      calc x = σ (σ x) := (hinv x).symm
        _ = σ a := by rw [h]
        _ = c := hchord
    rw [hxc] at h2
    exact absurd h2 (by omega)
  constructor
  · by_contra hle
    rw [not_lt] at hle
    have hlt : (σ x).val < a.val := by
      rcases Nat.lt_or_eq_of_le hle with h | h
      · exact h
      · exact absurd (Fin.ext h) hxa
    exact hnc (σ x) a x c hlt h1 h2 ⟨hinv x, hchord⟩
  · by_contra hle
    rw [not_lt] at hle
    have hlt : c.val < (σ x).val := by
      rcases Nat.lt_or_eq_of_le hle with h | h
      · exact h
      · have hcx : σ x = c := Fin.ext h.symm
        have hxa' : x = a := by
          have h2' : σ (σ x) = σ c := congrArg σ hcx
          rw [hinv x, ← hchord, hinv a] at h2'
          exact h2'
        omega
    exact hnc a x c (σ x) h1 h2 hlt ⟨hchord, rfl⟩

/-! ### An adjacent pair inside a closed interval -/

variable {n : ℕ} {σ : Equiv.Perm (Fin n)}

/-- **Ear in a closed interval**: a `σ`-closed interval with at least two interior points contains
an adjacent pair.  The proof is a strong induction on the width `hi - lo`: look at the first
interior point `a = lo + 1`; if `σ a = a + 1` we are done, and otherwise the sub-interval
`(a, σ a)` is shorter, nonempty and again `σ`-closed, so the induction hypothesis applies. -/
theorem exists_adjacent_in_interval (hinv : ∀ x, σ (σ x) = x) (hfix : ∀ x, σ x ≠ x)
    (hnc : NoInterleaving σ) :
    ∀ (w lo hi : ℕ), hi - lo = w → hi ≤ n → lo + 2 ≤ hi →
      (∀ x : Fin n, lo < x.val → x.val < hi → lo < (σ x).val ∧ (σ x).val < hi) →
      ∃ x : Fin n, lo < x.val ∧ (σ x).val = x.val + 1 ∧ x.val + 1 < hi := by
  intro w
  induction w using Nat.strong_induction_on with
  | h w ih =>
    intro lo hi hw hhi h2 hcl
    have hlo1 : lo + 1 < n := by omega
    set a : Fin n := ⟨lo + 1, hlo1⟩ with ha
    have haval : a.val = lo + 1 := rfl
    have ha_lo : lo < a.val := by omega
    have ha_hi : a.val < hi := by omega
    obtain ⟨hlo_sa, hsa_hi⟩ := hcl a ha_lo ha_hi
    have hane : σ a ≠ a := hfix a
    by_cases hAdj : (σ a).val = a.val + 1
    · exact ⟨a, ha_lo, hAdj, by omega⟩
    · have hsa_ge : a.val + 2 ≤ (σ a).val := by
        have hne : (σ a).val ≠ a.val := fun h => hane (Fin.ext h)
        omega
      have hcl' : ∀ x : Fin n, a.val < x.val → x.val < (σ a).val →
          a.val < (σ x).val ∧ (σ x).val < (σ a).val :=
        fun x hx1 hx2 => interval_closed_of_chord hinv hnc (c := σ a) (by omega) rfl hx1 hx2
      have hlt : (σ a).val - a.val < w := by omega
      have hhi' : (σ a).val ≤ n := (σ a).isLt.le
      obtain ⟨x, hx1, hx2, hx3⟩ :=
        ih ((σ a).val - a.val) hlt a.val (σ a).val (by omega) hhi' hsa_ge hcl'
      exact ⟨x, by omega, hx2, by omega⟩

/-! ### Ear existence -/

/-- **Ear existence** (permutation form): a fixed-point-free involution of `Fin n` with no two
interleaving chords maps some index to its cyclic successor. -/
theorem exists_ear_of_nonCrossing (hn : 0 < n) (hσ : σ * σ = 1) (hfix : ∀ x, σ x ≠ x)
    (hnc : NoInterleaving σ) : ∃ i : Fin n, σ i = finRotate n i := by
  have hinv : ∀ x, σ (σ x) = x := by
    intro x
    have h := congrArg (fun f : Equiv.Perm (Fin n) => f x) hσ
    simpa [Equiv.Perm.mul_apply] using h
  set a : Fin n := ⟨0, hn⟩ with ha
  have haval : a.val = 0 := rfl
  have hane : σ a ≠ a := hfix a
  have hsa_pos : 0 < (σ a).val := by
    rcases Nat.eq_zero_or_pos (σ a).val with h | h
    · exact absurd (Fin.ext (by omega)) hane
    · exact h
  rcases Nat.lt_or_ge (σ a).val 2 with h2 | h2
  · -- `σ a` is the successor of `a`: an ear at `a`
    have hval : (σ a).val = a.val + 1 := by omega
    refine ⟨a, Fin.ext ?_⟩
    rw [hval, finRotate_val_of_succ_lt (by omega)]
  · -- the interior of the chord `a -- σ a` is a closed interval
    have hcl : ∀ x : Fin n, 0 < x.val → x.val < (σ a).val →
        0 < (σ x).val ∧ (σ x).val < (σ a).val := by
      intro x hx1 hx2
      exact interval_closed_of_chord hinv hnc (a := a) (c := σ a) (by omega) rfl
        (by omega) hx2
    obtain ⟨x, hx1, hxval, hxlt⟩ :=
      exists_adjacent_in_interval hinv hfix hnc _ 0 (σ a).val rfl
        (σ a).isLt.le (by omega) hcl
    refine ⟨x, Fin.ext ?_⟩
    rw [hxval, finRotate_val_of_succ_lt (by omega)]

/-- **Ear existence for non-crossing pairings**: a non-crossing pairing of a nonempty list has two
cyclically consecutive paired positions. -/
theorem hasEar_of_isNonCrossing {l : List (GUEEntry ι N)} (p : GUEPairing l)
    (h : IsNonCrossing p) (hlen : 0 < l.length) : HasEar p := by
  have hσ : partnerPerm p * partnerPerm p = 1 := by
    refine Equiv.Perm.ext fun i => ?_
    show (partnerPerm p * partnerPerm p) i = (1 : Equiv.Perm (Fin l.length)) i
    rw [Equiv.Perm.mul_apply, Equiv.Perm.one_apply]
    exact partnerPerm_involutive p i
  exact exists_ear_of_nonCrossing hlen hσ (partnerPerm_ne_self p) h


/-! ### Auxiliary permutation lemmas -/

/-- The identity permutation has one orbit per point. -/
theorem permOrbitCount_one {α : Type*} [Fintype α] :
    permOrbitCount (1 : Equiv.Perm α) = Fintype.card α := by
  have hsame : ∀ a b : α, (sameCycleSetoid (1 : Equiv.Perm α)).r a b ↔ a = b := by
    intro a b
    show Equiv.Perm.SameCycle (1 : Equiv.Perm α) a b ↔ a = b
    constructor
    · rintro ⟨k, hk⟩
      simpa using hk
    · rintro rfl
      exact ⟨0, by simp⟩
  exact Fintype.card_congr
    { toFun := Quotient.lift id (fun a b h => (hsame a b).mp h)
      invFun := Quotient.mk (sameCycleSetoid (1 : Equiv.Perm α))
      left_inv := fun q => by
        induction q using Quotient.inductionOn with
        | h a => rfl
      right_inv := fun a => rfl }

/-- Conjugation is multiplicative. -/
theorem conjBy_mul {α β : Type*} (e : α ≃ β) (f g : Equiv.Perm α) :
    conjBy e (f * g) = conjBy e f * conjBy e g := by
  ext x
  simp [conjBy_apply, Equiv.Perm.mul_apply]

/-- Conjugation sends the identity to the identity. -/
theorem conjBy_one {α β : Type*} (e : α ≃ β) : conjBy e (1 : Equiv.Perm α) = 1 := by
  ext x
  simp [conjBy_apply]

/-- Conjugating twice is conjugating by the composite. -/
theorem conjBy_conjBy {α β γ : Type*} (e : α ≃ β) (e' : β ≃ γ) (σ : Equiv.Perm α) :
    conjBy e' (conjBy e σ) = conjBy (e.trans e') σ := by
  ext x
  simp [conjBy_apply]

/-- Conjugation preserves involutivity. -/
theorem conjBy_involutive {α β : Type*} (e : α ≃ β) {σ : Equiv.Perm α}
    (h : ∀ x, σ (σ x) = x) : ∀ x, conjBy e σ (conjBy e σ x) = x := by
  intro x
  simp [conjBy_apply, h]

/-- Conjugation preserves fixed-point-freeness. -/
theorem conjBy_ne_self {α β : Type*} (e : α ≃ β) {σ : Equiv.Perm α}
    (h : ∀ x, σ x ≠ x) : ∀ x, conjBy e σ x ≠ x := by
  intro x hx
  apply h (e.symm x)
  have := congrArg e.symm hx
  simpa [conjBy_apply] using this

/-- Conjugation by the identity is the identity. -/
theorem conjBy_refl {α : Type*} (σ : Equiv.Perm α) :
    conjBy (Equiv.refl α) σ = σ := by
  ext x
  simp [conjBy_apply]

/-- Conjugation by the identity permutation is the identity. -/
theorem conjBy_one_perm {α : Type*} (σ : Equiv.Perm α) :
    conjBy (1 : Equiv.Perm α) σ = σ := by
  ext x
  rfl

/-- The cyclic shift is invariant under conjugation by its own powers. -/
theorem conjBy_finRotate_pow (n t : ℕ) :
    conjBy (finRotate n ^ t) (finRotate n) = finRotate n := by
  have hmul : (finRotate n ^ t) * finRotate n = finRotate n * (finRotate n ^ t) := by
    rw [← pow_succ, ← pow_succ']
  ext x
  simp only [conjBy_apply]
  rw [← Equiv.Perm.mul_apply, hmul, Equiv.Perm.mul_apply, Equiv.apply_symm_apply]

/-! ### Rotation invariance of the crossing-free condition -/

/-- **One-step rotation invariance**: cyclically shifting all positions by one preserves the
absence of interleaving chords. -/
theorem noInterleaving_conjBy_finRotate {n : ℕ} [NeZero n] {σ : Equiv.Perm (Fin n)}
    (hinv : ∀ x, σ (σ x) = x) (h : NoInterleaving σ) :
    NoInterleaving (conjBy (finRotate n) σ) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne n)
  set ρ := finRotate (m + 1) with hρ
  have hval_ne : ∀ x : Fin (m + 1), x ≠ 0 → (ρ.symm x).val = x.val - 1 := by
    intro x hx
    exact coe_finRotate_symm_of_ne_zero (n := m + 1) (by simpa using hx)
  have hval_zero : (ρ.symm (0 : Fin (m + 1))).val = m := by
    have h1 : ρ (Fin.last m) = 0 := finRotate_last
    have h2 : ρ.symm 0 = Fin.last m := by
      rw [Equiv.symm_apply_eq]
      exact h1.symm
    rw [h2, Fin.val_last]
  intro a b c d hab hbc hcd hcross
  obtain ⟨hac, hbd⟩ := hcross
  have hsya : σ (ρ.symm a) = ρ.symm c := by
    have h' := congrArg ρ.symm hac
    simpa [conjBy_apply, hρ] using h'
  have hsyb : σ (ρ.symm b) = ρ.symm d := by
    have h' := congrArg ρ.symm hbd
    simpa [conjBy_apply, hρ] using h'
  have haval : a.val < b.val := hab
  by_cases ha0 : a = 0
  · have hb0 : b ≠ 0 := by
      intro hb
      rw [hb] at haval
      simp [ha0] at haval
    have hc0 : c ≠ 0 := by
      intro hc
      rw [hc] at hbc
      exact absurd hbc (by simp)
    have hd0 : d ≠ 0 := by
      intro hd
      rw [hd] at hcd
      exact absurd hcd (by simp)
    have hav : (ρ.symm a).val = m := by rw [ha0, hval_zero]
    have hbv : (ρ.symm b).val = b.val - 1 := hval_ne b hb0
    have hcv : (ρ.symm c).val = c.val - 1 := hval_ne c hc0
    have hdv : (ρ.symm d).val = d.val - 1 := hval_ne d hd0
    have ha0' : a.val = 0 := by simpa using congrArg Fin.val ha0
    have hd_le : d.val ≤ m := by have := d.isLt; omega
    have hsyb' : σ (ρ.symm b) = ρ.symm d := hsyb
    have hcya : σ (ρ.symm c) = ρ.symm a := by
      rw [← hinv (ρ.symm a), hsya]
    exact h (ρ.symm b) (ρ.symm c) (ρ.symm d) (ρ.symm a)
      (by rw [hbv, hcv]; omega) (by rw [hcv, hdv]; omega)
      (by rw [hdv, hav]; omega) ⟨hsyb', hcya⟩
  · have hb0 : b ≠ 0 := by
      intro hb
      rw [hb] at haval
      exact ha0 (Fin.ext (by simpa using haval))
    have hc0 : c ≠ 0 := by
      intro hc
      rw [hc] at hbc
      exact absurd hbc (by simp)
    have hd0 : d ≠ 0 := by
      intro hd
      rw [hd] at hcd
      exact absurd hcd (by simp)
    have ha1 : 1 ≤ a.val := by
      have := a.isLt
      have : a.val ≠ 0 := by
        intro h'
        exact ha0 (Fin.ext (by simpa using h'))
      omega
    have hav : (ρ.symm a).val = a.val - 1 := hval_ne a ha0
    have hbv : (ρ.symm b).val = b.val - 1 := hval_ne b hb0
    have hcv : (ρ.symm c).val = c.val - 1 := hval_ne c hc0
    have hdv : (ρ.symm d).val = d.val - 1 := hval_ne d hd0
    exact h (ρ.symm a) (ρ.symm b) (ρ.symm c) (ρ.symm d)
      (by rw [hav, hbv]; omega) (by rw [hbv, hcv]; omega)
      (by rw [hcv, hdv]; omega) ⟨hsya, hsyb⟩

/-- **Rotation invariance**: cyclically shifting all positions by any amount preserves the absence
of interleaving chords. -/
theorem noInterleaving_conjBy_finRotate_pow {n : ℕ} [NeZero n] {σ : Equiv.Perm (Fin n)}
    (hinv : ∀ x, σ (σ x) = x) (h : NoInterleaving σ) (k : ℕ) :
    NoInterleaving (conjBy (finRotate n ^ k) σ) := by
  induction k with
  | zero => simpa [conjBy_one_perm] using h
  | succ k ih =>
    have hstep : conjBy (finRotate n ^ (k + 1)) σ =
        conjBy (finRotate n) (conjBy (finRotate n ^ k) σ) := by
      rw [conjBy_conjBy]
      congr 1
      ext x
      rw [Equiv.trans_apply, ← Equiv.Perm.mul_apply, ← pow_succ']
    rw [hstep]
    exact noInterleaving_conjBy_finRotate (conjBy_involutive _ hinv) ih


/-! ### Compression of a pairing involution at a wrap ear -/

/-- An involution satisfies `σ (σ x) = x`. -/
theorem apply_apply_of_mul_eq_one {α : Type*} {σ : Equiv.Perm α} (hσ : σ * σ = 1) (x : α) :
    σ (σ x) = x := by
  have h := congrArg (fun f : Equiv.Perm α => f x) hσ
  simpa [Equiv.Perm.mul_apply] using h

/-- If the last position is paired with `0`, then every interior position `1 ≤ x ≤ n` is paired
with an interior position. -/
theorem interior_bounds {n : ℕ} {σ : Equiv.Perm (Fin (n + 2))} (hσ : σ * σ = 1)
    (hlast : σ (Fin.last (n + 1)) = 0) {x : Fin (n + 2)} (hx0 : x ≠ 0)
    (hxlast : x ≠ Fin.last (n + 1)) : 1 ≤ (σ x).val ∧ (σ x).val ≤ n := by
  have hinv := apply_apply_of_mul_eq_one hσ
  have hσ0 : σ 0 = Fin.last (n + 1) := by
    have h := congrArg σ hlast
    rw [hinv (Fin.last (n + 1))] at h
    exact h.symm
  constructor
  · rcases Nat.eq_zero_or_pos (σ x).val with h | h
    · exfalso
      have hy : σ x = 0 := Fin.ext (by simpa using h)
      have hx' : x = Fin.last (n + 1) := by
        calc x = σ (σ x) := (hinv x).symm
          _ = σ 0 := by rw [hy]
          _ = Fin.last (n + 1) := hσ0
      exact hxlast hx'
    · exact h
  · have hlt := (σ x).isLt
    rcases Nat.eq_or_lt_of_le (by omega : (σ x).val ≤ n + 1) with h | h
    · exfalso
      have hy : σ x = Fin.last (n + 1) := Fin.ext (by rw [Fin.val_last]; omega)
      have hx' : x = 0 := by
        calc x = σ (σ x) := (hinv x).symm
          _ = σ (Fin.last (n + 1)) := by rw [hy]
          _ = 0 := hlast
      exact hx0 hx'
    · omega

/-- The partner permutation of the interior interval `{1, …, n}`, renumbered from `0`, for a
pairing involution of `Fin (n+2)` that pairs the last position with `0`. -/
def compressEar {n : ℕ} (σ : Equiv.Perm (Fin (n + 2))) (hσ : σ * σ = 1)
    (hlast : σ (Fin.last (n + 1)) = 0) (k : Fin n) : Fin n :=
  ⟨(σ ⟨k.val + 1, by omega⟩).val - 1, by
    have hx0 : (⟨k.val + 1, by omega⟩ : Fin (n + 2)) ≠ 0 := by
      intro h
      have := congrArg Fin.val h
      simp at this
    have hxlast : (⟨k.val + 1, by omega⟩ : Fin (n + 2)) ≠ Fin.last (n + 1) := by
      intro h
      have := congrArg Fin.val h
      simp [Fin.val_last] at this
      omega
    have hb := interior_bounds hσ hlast hx0 hxlast
    omega⟩

theorem compressEar_val {n : ℕ} (σ : Equiv.Perm (Fin (n + 2))) (hσ : σ * σ = 1)
    (hlast : σ (Fin.last (n + 1)) = 0) (k : Fin n) (h : k.val + 1 < n + 2) :
    (compressEar σ hσ hlast k).val = (σ ⟨k.val + 1, h⟩).val - 1 := rfl

/-- The compressed interior partner map is an involution. -/
theorem compressEar_involutive {n : ℕ} (σ : Equiv.Perm (Fin (n + 2))) (hσ : σ * σ = 1)
    (hlast : σ (Fin.last (n + 1)) = 0) (k : Fin n) :
    compressEar σ hσ hlast (compressEar σ hσ hlast k) = k := by
  have hinv := apply_apply_of_mul_eq_one hσ
  have hx0 : (⟨k.val + 1, by omega⟩ : Fin (n + 2)) ≠ 0 := by
    intro h
    have := congrArg Fin.val h
    simp at this
  have hxlast : (⟨k.val + 1, by omega⟩ : Fin (n + 2)) ≠ Fin.last (n + 1) := by
    intro h
    have := congrArg Fin.val h
    simp [Fin.val_last] at this
    omega
  have hb := interior_bounds hσ hlast hx0 hxlast
  set j := compressEar σ hσ hlast k with hj
  have hjval : j.val = (σ ⟨k.val + 1, by omega⟩).val - 1 := rfl
  have hjlt : j.val < n := by omega
  have hj0 : (⟨j.val + 1, by omega⟩ : Fin (n + 2)) ≠ 0 := by
    intro h
    have := congrArg Fin.val h
    simp at this
  have hjlast : (⟨j.val + 1, by omega⟩ : Fin (n + 2)) ≠ Fin.last (n + 1) := by
    intro h
    have := congrArg Fin.val h
    simp [Fin.val_last] at this
    omega
  have hjb := interior_bounds hσ hlast hj0 hjlast
  have hgoal : (compressEar σ hσ hlast j).val = k.val := by
    rw [compressEar_val σ hσ hlast j (by omega)]
    have hpt : (⟨j.val + 1, by omega⟩ : Fin (n + 2)) = σ ⟨k.val + 1, by omega⟩ := by
      apply Fin.ext
      show j.val + 1 = (σ ⟨k.val + 1, by omega⟩).val
      omega
    rw [hpt, hinv]
    simp
  exact Fin.ext hgoal

/-- The compressed interior partner permutation. -/
def compressedPerm {n : ℕ} (σ : Equiv.Perm (Fin (n + 2))) (hσ : σ * σ = 1)
    (hlast : σ (Fin.last (n + 1)) = 0) : Equiv.Perm (Fin n) where
  toFun := compressEar σ hσ hlast
  invFun := compressEar σ hσ hlast
  left_inv := compressEar_involutive σ hσ hlast
  right_inv := compressEar_involutive σ hσ hlast

@[simp] theorem compressedPerm_apply {n : ℕ} (σ : Equiv.Perm (Fin (n + 2))) (hσ : σ * σ = 1)
    (hlast : σ (Fin.last (n + 1)) = 0) (k : Fin n) :
    compressedPerm σ hσ hlast k = compressEar σ hσ hlast k := rfl

/-- The compressed permutation is an involution. -/
theorem compressedPerm_mul_self {n : ℕ} (σ : Equiv.Perm (Fin (n + 2))) (hσ : σ * σ = 1)
    (hlast : σ (Fin.last (n + 1)) = 0) :
    compressedPerm σ hσ hlast * compressedPerm σ hσ hlast = 1 := by
  refine Equiv.ext (fun k => ?_)
  rw [Equiv.Perm.mul_apply, Equiv.Perm.one_apply]
  exact compressEar_involutive σ hσ hlast k

/-- The compressed permutation has no fixed points. -/
theorem compressedPerm_ne_self {n : ℕ} (σ : Equiv.Perm (Fin (n + 2))) (hσ : σ * σ = 1)
    (hlast : σ (Fin.last (n + 1)) = 0) (hfix : ∀ x, σ x ≠ x) (k : Fin n) :
    compressedPerm σ hσ hlast k ≠ k := by
  intro h
  have hval : (σ ⟨k.val + 1, by omega⟩).val - 1 = k.val := by
    have h1 : (compressEar σ hσ hlast k).val = k.val := congrArg Fin.val h
    rw [compressEar_val σ hσ hlast k (by omega)] at h1
    exact h1
  have hx0 : (⟨k.val + 1, by omega⟩ : Fin (n + 2)) ≠ 0 := by
    intro hh
    have := congrArg Fin.val hh
    simp at this
  have hxlast : (⟨k.val + 1, by omega⟩ : Fin (n + 2)) ≠ Fin.last (n + 1) := by
    intro hh
    have := congrArg Fin.val hh
    simp [Fin.val_last] at this
    omega
  have hb := interior_bounds hσ hlast hx0 hxlast
  have : (σ ⟨k.val + 1, by omega⟩).val = k.val + 1 := by omega
  exact hfix _ (Fin.ext this)

/-- **Non-crossing is inherited by the compressed interior pairing.** -/
theorem noInterleaving_compressedPerm {n : ℕ} (σ : Equiv.Perm (Fin (n + 2))) (hσ : σ * σ = 1)
    (hlast : σ (Fin.last (n + 1)) = 0) (h : NoInterleaving σ) :
    NoInterleaving (compressedPerm σ hσ hlast) := by
  intro a b c d hab hbc hcd hcross
  obtain ⟨hac, hbd⟩ := hcross
  have hlift : ∀ (p q : Fin n), compressedPerm σ hσ hlast p = q →
      σ ⟨p.val + 1, by omega⟩ = ⟨q.val + 1, by omega⟩ := by
    intro p q hpq
    have hv : (σ ⟨p.val + 1, by omega⟩).val - 1 = q.val := by
      have h1 : (compressEar σ hσ hlast p).val = q.val := congrArg Fin.val hpq
      rw [compressEar_val σ hσ hlast p (by omega)] at h1
      exact h1
    have hx0 : (⟨p.val + 1, by omega⟩ : Fin (n + 2)) ≠ 0 := by
      intro hh
      have := congrArg Fin.val hh
      simp at this
    have hxlast : (⟨p.val + 1, by omega⟩ : Fin (n + 2)) ≠ Fin.last (n + 1) := by
      intro hh
      have := congrArg Fin.val hh
      simp [Fin.val_last] at this
      omega
    have hb := interior_bounds hσ hlast hx0 hxlast
    refine Fin.ext ?_
    show (σ ⟨p.val + 1, by omega⟩).val = q.val + 1
    omega
  exact h ⟨a.val + 1, by omega⟩ ⟨b.val + 1, by omega⟩ ⟨c.val + 1, by omega⟩
    ⟨d.val + 1, by omega⟩ (by simp; omega) (by simp; omega) (by simp; omega)
    ⟨hlift a c hac, hlift b d hbd⟩


/-- The forward map of the reindexing: interior positions become `1, …, n`, and the two extra
positions become `0` and the last position. -/
def earToFun (n : ℕ) : (Fin n ⊕ Fin 2) → Fin (n + 2)
  | Sum.inl k => ⟨k.val + 1, by omega⟩
  | Sum.inr j => if j = 0 then 0 else Fin.last (n + 1)

/-- The inverse reindexing. -/
def earInvFun (n : ℕ) (x : Fin (n + 2)) : Fin n ⊕ Fin 2 :=
  if hx0 : x = 0 then Sum.inr 0
  else if hxl : x = Fin.last (n + 1) then Sum.inr 1
  else Sum.inl ⟨x.val - 1, by
    have h1 : x.val ≠ 0 := by
      intro h
      exact hx0 (Fin.ext (by simpa using h))
    have h2 : x.val ≠ n + 1 := by
      intro h
      exact hxl (Fin.ext (by rw [Fin.val_last]; omega))
    have h3 := x.isLt
    omega⟩

@[simp] theorem earToFun_inr_zero (n : ℕ) : earToFun n (Sum.inr (0 : Fin 2)) = 0 := by
  show (if (0 : Fin 2) = 0 then (0 : Fin (n + 2)) else Fin.last (n + 1)) = 0
  rfl

@[simp] theorem earToFun_inr_one (n : ℕ) :
    earToFun n (Sum.inr (1 : Fin 2)) = Fin.last (n + 1) := by
  show (if (1 : Fin 2) = 0 then (0 : Fin (n + 2)) else Fin.last (n + 1)) = Fin.last (n + 1)
  rfl

theorem earInvFun_earToFun (n : ℕ) (s : Fin n ⊕ Fin 2) : earInvFun n (earToFun n s) = s := by
  rcases s with k | j
  · have h0 : (⟨k.val + 1, by omega⟩ : Fin (n + 2)) ≠ 0 := by
      intro h
      have := congrArg Fin.val h
      simp at this
    have hl : (⟨k.val + 1, by omega⟩ : Fin (n + 2)) ≠ Fin.last (n + 1) := by
      intro h
      have := congrArg Fin.val h
      simp [Fin.val_last] at this
      omega
    show earInvFun n (⟨k.val + 1, by omega⟩ : Fin (n + 2)) = Sum.inl k
    rw [earInvFun, dif_neg h0, dif_neg hl]
    congr 1
  · fin_cases j <;> simp [earToFun, earInvFun]

theorem earToFun_earInvFun (n : ℕ) (x : Fin (n + 2)) : earToFun n (earInvFun n x) = x := by
  by_cases hx0 : x = 0
  · subst hx0
    simp [earInvFun]
  · by_cases hxl : x = Fin.last (n + 1)
    · subst hxl
      simp [earInvFun]
    · have h1 : x.val ≠ 0 := by
        intro h
        exact hx0 (Fin.ext (by simpa using h))
      have h2 : x.val ≠ n + 1 := by
        intro h
        exact hxl (Fin.ext (by rw [Fin.val_last]; omega))
      rw [earInvFun, dif_neg hx0, dif_neg hxl]
      show (⟨(⟨x.val - 1, _⟩ : Fin n).val + 1, by omega⟩ : Fin (n + 2)) = x
      apply Fin.ext
      show (⟨x.val - 1, _⟩ : Fin n).val + 1 = x.val
      have h3 := x.isLt
      simp
      omega

/-- Reindexing the interior positions `{1, …, n}` and the two ear positions `0`, `last` as
`Fin n ⊕ Fin 2`. -/
def earEquiv (n : ℕ) : (Fin n ⊕ Fin 2) ≃ Fin (n + 2) where
  toFun := earToFun n
  invFun := earInvFun n
  left_inv := earInvFun_earToFun n
  right_inv := earToFun_earInvFun n

@[simp] theorem earEquiv_inl (n : ℕ) (k : Fin n) :
    earEquiv n (Sum.inl k) = ⟨k.val + 1, by omega⟩ := rfl

@[simp] theorem earEquiv_inr_zero (n : ℕ) :
    earEquiv n (Sum.inr (0 : Fin 2)) = 0 := by
  show earToFun n (Sum.inr 0) = 0
  rfl

@[simp] theorem earEquiv_inr_one (n : ℕ) :
    earEquiv n (Sum.inr (1 : Fin 2)) = Fin.last (n + 1) := by
  show earToFun n (Sum.inr 1) = Fin.last (n + 1)
  rfl

@[simp] theorem earEquiv_symm_zero (n : ℕ) :
    (earEquiv n).symm (0 : Fin (n + 2)) = Sum.inr 0 := by
  rw [Equiv.symm_apply_eq]
  simp

@[simp] theorem earEquiv_symm_last (n : ℕ) :
    (earEquiv n).symm (Fin.last (n + 1)) = Sum.inr 1 := by
  rw [Equiv.symm_apply_eq]
  have h : (1 : Fin 2) ≠ 0 := by decide
  simp [earToFun, h]

/-- A point fixed by a permutation is alone in its same-cycle class. -/
theorem not_sameCycle_of_fixed {α : Type*} [Finite α] (g : Equiv.Perm α) {x y : α} (hx : g x = x)
    (hy : y ≠ x) : ¬ Equiv.Perm.SameCycle g x y := by
  intro hsc
  have hfixpow : ∀ k : ℕ, (g ^ k) x = x := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ', Equiv.Perm.mul_apply, ih, hx]
  obtain ⟨k, hk⟩ := hsc.exists_nat_pow_eq
  rw [hfixpow k] at hk
  exact hy hk.symm

/-- **Ear removal at the wrap position (orbit count)**: deleting the paired positions `0` and the
last position of `Fin (n+2)` decreases the number of face orbits by exactly one. -/
theorem ear_removal_wrap_count {n : ℕ} (hn : 1 ≤ n) (σ : Equiv.Perm (Fin (n + 2)))
    (hσ : σ * σ = 1) (hlast : σ (Fin.last (n + 1)) = 0) :
    permOrbitCount (finRotate (n + 2) * σ) =
      permOrbitCount (finRotate n * compressedPerm σ hσ hlast) + 1 := by
  set σ' := compressedPerm σ hσ hlast with hσ'
  set F : Equiv.Perm (Fin n ⊕ Fin 2) := Equiv.Perm.sumCongr (finRotate n * σ') 1 with hF
  set h : Equiv.Perm (Fin (n + 2)) := (earEquiv n).permCongr F with hh
  have hcount : permOrbitCount h = permOrbitCount (finRotate n * σ') + 2 := by
    rw [hh, permOrbitCount_permCongr, hF, permOrbitCount_sumCongr, permOrbitCount_one]
    simp [Fintype.card_fin]
  have happ : ∀ k : Fin n, h (earEquiv n (Sum.inl k)) =
      earEquiv n (Sum.inl ((finRotate n * σ') k)) := by
    intro k
    rw [hh, Equiv.permCongr_apply, Equiv.symm_apply_apply, hF, Equiv.Perm.sumCongr_apply]
    rfl
  have hhzero : h 0 = 0 := by
    have h0 : (0 : Fin (n + 2)) = earEquiv n (Sum.inr 0) := by simp
    rw [h0, hh, Equiv.permCongr_apply, Equiv.symm_apply_apply, hF, Equiv.Perm.sumCongr_apply]
    simp
  have hhlast : h (Fin.last (n + 1)) = Fin.last (n + 1) := by
    have hl : (Fin.last (n + 1) : Fin (n + 2)) = earEquiv n (Sum.inr 1) := by simp
    rw [hl, hh, Equiv.permCongr_apply, Equiv.symm_apply_apply, hF, Equiv.Perm.sumCongr_apply]
    simp
  have hident : finRotate (n + 2) * σ =
      Equiv.swap (Fin.last (n + 1)) (1 : Fin (n + 2)) * h := by
    refine Equiv.ext (fun x => ?_)
    apply Fin.ext
    by_cases hx0 : x = 0
    · subst hx0
      have hσ0 : σ (0 : Fin (n + 2)) = Fin.last (n + 1) := by
        have hinv := apply_apply_of_mul_eq_one hσ
        have h := congrArg σ hlast
        rw [hinv (Fin.last (n + 1))] at h
        exact h.symm
      have hz : ((finRotate (n + 2) * σ) (0 : Fin (n + 2))).val = 0 := by
        rw [Equiv.Perm.mul_apply, hσ0, finRotate_last]
        rfl
      have hz2 : ((Equiv.swap (Fin.last (n + 1)) (1 : Fin (n + 2)) * h)
          (0 : Fin (n + 2))).val = 0 := by
        rw [Equiv.Perm.mul_apply, hhzero]
        rw [Equiv.swap_apply_of_ne_of_ne]
        · rfl
        · intro hh'
          have := congrArg Fin.val hh'
          simp [Fin.val_last] at this
        · intro hh'
          have := congrArg Fin.val hh'
          simp at this
      rw [hz, hz2]
    · by_cases hxl : x = Fin.last (n + 1)
      · subst hxl
        have hz : ((finRotate (n + 2) * σ) (Fin.last (n + 1))).val = 1 := by
          rw [Equiv.Perm.mul_apply, hlast, finRotate_apply_zero]
          simp
        have hz2 : ((Equiv.swap (Fin.last (n + 1)) (1 : Fin (n + 2)) * h)
            (Fin.last (n + 1))).val = 1 := by
          rw [Equiv.Perm.mul_apply, hhlast, Equiv.swap_apply_left]
          simp
        rw [hz, hz2]
      · -- interior position
        have hx1 : 1 ≤ x.val := by
          have h := x.isLt
          have : x.val ≠ 0 := by
            intro h'
            exact hx0 (Fin.ext (by simpa using h'))
          omega
        have hxn : x.val ≤ n := by
          have h := x.isLt
          have : x.val ≠ n + 1 := by
            intro h'
            exact hxl (Fin.ext (by rw [Fin.val_last]; omega))
          omega
        set k : Fin n := ⟨x.val - 1, by omega⟩ with hk
        have hkv : k.val = x.val - 1 := rfl
        have hxe : earEquiv n (Sum.inl k) = x := by
          rw [earEquiv_inl]
          exact Fin.ext (by show k.val + 1 = x.val; omega)
        have hb := interior_bounds hσ hlast hx0 hxl
        have hσ'k : (σ' k).val = (σ x).val - 1 := by
          rw [hσ', compressedPerm_apply, compressEar_val σ hσ hlast k (by omega)]
          have hpt : (⟨k.val + 1, by omega⟩ : Fin (n + 2)) = x := by
            apply Fin.ext
            show k.val + 1 = x.val
            omega
          rw [hpt]
        have hm : ((finRotate n * σ') k).val = (if (σ x).val < n then (σ x).val else 0) := by
          rw [show ((finRotate n * σ') k).val = (finRotate n (σ' k)).val from rfl,
            finRotate_val_eq, hσ'k]
          by_cases hlt : (σ x).val < n
          · rw [if_pos (by omega), if_pos hlt]
            omega
          · rw [if_neg (by omega), if_neg hlt]
        have hL : ((finRotate (n + 2) * σ) x).val = (σ x).val + 1 := by
          rw [Equiv.Perm.mul_apply, finRotate_val_of_succ_lt (by omega)]
        have hhx : h x = earEquiv n (Sum.inl ((finRotate n * σ') k)) := by
          rw [← hxe]
          exact happ k
        have hRval : (Equiv.swap (Fin.last (n + 1)) (1 : Fin (n + 2)) (h x)).val =
            (σ x).val + 1 := by
          have hyval : (h x).val = ((finRotate n * σ') k).val + 1 := by
            rw [hhx, earEquiv_inl]
          have hyval2 : (h x).val = (if (σ x).val < n then (σ x).val else 0) + 1 := by
            rw [hyval, hm]
          by_cases hlt : (σ x).val < n
          · have hy1 : (h x).val = (σ x).val + 1 := by rw [hyval2, if_pos hlt]
            have hxe2 : h x = (⟨(σ x).val + 1, by omega⟩ : Fin (n + 2)) := Fin.ext hy1
            rw [hxe2]
            have hne_last : (⟨(σ x).val + 1, by omega⟩ : Fin (n + 2)) ≠ Fin.last (n + 1) := by
              intro hh'
              have hvv : (σ x).val + 1 = n + 1 := by
                have := congrArg Fin.val hh'
                simpa [Fin.val_last] using this
              omega
            have hne_one : (⟨(σ x).val + 1, by omega⟩ : Fin (n + 2)) ≠ (1 : Fin (n + 2)) := by
              intro hh'
              have hvv : (σ x).val + 1 = 1 := by
                have := congrArg Fin.val hh'
                simpa using this
              omega
            rw [Equiv.swap_apply_of_ne_of_ne hne_last hne_one]
          · have hyn : (σ x).val = n := by omega
            have hy1 : (h x).val = 1 := by rw [hyval2, if_neg hlt]
            have hxe2 : h x = (1 : Fin (n + 2)) := Fin.ext (by rw [hy1]; rfl)
            rw [hxe2, Equiv.swap_apply_right]
            show (Fin.last (n + 1) : Fin (n + 2)).val = (σ x).val + 1
            rw [Fin.val_last]
            omega
        rw [hL, Equiv.Perm.mul_apply, hRval]
  have hnotsame : ¬ Equiv.Perm.SameCycle h (Fin.last (n + 1)) (1 : Fin (n + 2)) :=
    not_sameCycle_of_fixed h hhlast (by
      intro hh'
      have hvv : (1 : Fin (n + 2)).val = (Fin.last (n + 1)).val := congrArg Fin.val hh'
      rw [Fin.val_last] at hvv
      have h1 : (1 : Fin (n + 2)).val = 1 := by simp
      omega)
  have hmerge := permOrbitCount_swap_mul_eq_sub_one h (Fin.last (n + 1)) (1 : Fin (n + 2)) hnotsame
  rw [hident, hmerge, hcount]
  rfl


/-! ### Removing an ear at an arbitrary position -/

/-- **Ear removal** (permutation form): a fixed-point-free involution of `Fin (n+2)` with an ear
`σ i = i + 1` (cyclically) can be compressed to a fixed-point-free involution of `Fin n` whose face
count is exactly one smaller.  The ear is first moved to the wrap position by a cyclic shift, which
preserves both the face count and the crossing-free condition. -/
theorem exists_ear_removal {n : ℕ} (hn : 1 ≤ n) (σ : Equiv.Perm (Fin (n + 2)))
    (hσ : σ * σ = 1) (hfix : ∀ x, σ x ≠ x) (i : Fin (n + 2))
    (hear : σ i = finRotate (n + 2) i) :
    ∃ σ' : Equiv.Perm (Fin n), σ' * σ' = 1 ∧ (∀ x, σ' x ≠ x) ∧
      (NoInterleaving σ → NoInterleaving σ') ∧
      permOrbitCount (finRotate (n + 2) * σ) = permOrbitCount (finRotate n * σ') + 1 := by
  have hinv : ∀ x, σ (σ x) = x := apply_apply_of_mul_eq_one hσ
  set t : ℕ := n + 1 - i.val with ht
  have hit : i.val + t = n + 1 := by
    have := i.isLt
    simp only [ht]
    omega
  have htlt : i.val + t < n + 2 := by omega
  have hpow : (finRotate (n + 2) ^ t) i = Fin.last (n + 1) := by
    apply Fin.ext
    rw [finRotate_iterate_val (n + 2) i t htlt, hit]
    rfl
  have hsymm : (finRotate (n + 2) ^ t).symm (Fin.last (n + 1)) = i := by
    rw [Equiv.symm_apply_eq]
    exact hpow.symm
  have hcomm : ∀ y : Fin (n + 2),
      (finRotate (n + 2) ^ t) (finRotate (n + 2) y) = finRotate (n + 2) ((finRotate (n + 2) ^ t) y) := by
    intro y
    rw [← Equiv.Perm.mul_apply, ← Equiv.Perm.mul_apply]
    congr 1
    rw [← pow_succ, ← pow_succ']
  have hear' : conjBy (finRotate (n + 2) ^ t) σ (Fin.last (n + 1)) = 0 := by
    rw [conjBy_apply, hsymm, hear, hcomm, hpow, finRotate_last]
  have hσ1mul : conjBy (finRotate (n + 2) ^ t) σ * conjBy (finRotate (n + 2) ^ t) σ = 1 := by
    rw [← conjBy_mul, hσ, conjBy_one]
  refine ⟨compressedPerm (conjBy (finRotate (n + 2) ^ t) σ) hσ1mul hear', ?_, ?_, ?_, ?_⟩
  · exact compressedPerm_mul_self _ _ _
  · exact compressedPerm_ne_self _ _ _ (conjBy_ne_self _ hfix)
  · intro hnc
    exact noInterleaving_compressedPerm _ _ _
      (noInterleaving_conjBy_finRotate_pow hinv hnc t)
  · have hcount := ear_removal_wrap_count hn (conjBy (finRotate (n + 2) ^ t) σ) hσ1mul hear'
    calc permOrbitCount (finRotate (n + 2) * σ)
        = permOrbitCount (conjBy (finRotate (n + 2) ^ t) (finRotate (n + 2) * σ)) :=
          (permOrbitCount_conjBy _ _).symm
      _ = permOrbitCount (conjBy (finRotate (n + 2) ^ t) (finRotate (n + 2)) *
            conjBy (finRotate (n + 2) ^ t) σ) := by rw [conjBy_mul]
      _ = permOrbitCount (finRotate (n + 2) * conjBy (finRotate (n + 2) ^ t) σ) := by
            rw [conjBy_finRotate_pow]
      _ = permOrbitCount (finRotate n *
            compressedPerm (conjBy (finRotate (n + 2) ^ t) σ) hσ1mul hear') + 1 := hcount

/-! ### The exact face count of a non-crossing pairing -/

/-- The cyclic shift of `Fin 2` is the transposition `0 ↔ 1`. -/
theorem finRotate_two : finRotate 2 = Equiv.swap (0 : Fin 2) 1 := by
  ext x
  fin_cases x <;> decide

/-- **Exact face count for a crossing-free involution** (`Fin (2*k+2)` form): the induction is
stated in this shifted form so that deleting an ear lands exactly on the previous case. -/
theorem permOrbitCount_eq_of_noInterleaving_succ (k : ℕ) (σ : Equiv.Perm (Fin (2 * k + 2)))
    (hσ : σ * σ = 1) (hfix : ∀ x, σ x ≠ x) (hnc : NoInterleaving σ) :
    permOrbitCount (finRotate (2 * k + 2) * σ) = k + 2 := by
  induction k with
  | zero =>
    -- base case: the only fixed-point-free involution of `Fin 2` is the cyclic shift
    have hσ2 : σ = finRotate (2 * 0 + 2) := by
      refine Equiv.ext (fun x => ?_)
      fin_cases x
      · have h0 : (σ 0).val ≠ 0 := fun h => hfix 0 (Fin.ext (by simpa using h))
        have hlt : (σ 0).val < 2 := (σ 0).isLt
        apply Fin.ext
        show (σ 0).val = (finRotate (2 * 0 + 2) (0 : Fin (2 * 0 + 2))).val
        rw [show (finRotate (2 * 0 + 2) (0 : Fin (2 * 0 + 2))).val = 1 from
          finRotate_val_of_succ_lt (by decide)]
        omega
      · have h1 : (σ 1).val ≠ 1 := fun h => hfix 1 (Fin.ext (by simpa using h))
        have hlt : (σ 1).val < 2 := (σ 1).isLt
        apply Fin.ext
        show (σ 1).val = (finRotate (2 * 0 + 2) (1 : Fin (2 * 0 + 2))).val
        have hfr : (finRotate (2 * 0 + 2) (1 : Fin (2 * 0 + 2))).val = 0 := by
          rw [show (1 : Fin (2 * 0 + 2)) = Fin.last 1 from rfl, finRotate_last]
          rfl
        rw [hfr]
        omega
    have hρρ : finRotate (2 * 0 + 2) * finRotate (2 * 0 + 2) = 1 := by
      rw [show finRotate (2 * 0 + 2) = Equiv.swap (0 : Fin 2) 1 from finRotate_two,
        Equiv.swap_mul_self]
    rw [hσ2, hρρ, permOrbitCount_one]
    simp
  | succ k ih =>
    show permOrbitCount (finRotate (2 * k + 2 + 2) * σ) = k + 1 + 2
    obtain ⟨i, hear⟩ := exists_ear_of_nonCrossing (by omega : 0 < 2 * (k + 1) + 2) hσ hfix hnc
    obtain ⟨σ', hσ', hfix', hnc', hcount⟩ :=
      exists_ear_removal (n := 2 * k + 2) (by omega) σ hσ hfix i hear
    rw [hcount, ih σ' hσ' hfix' (hnc' hnc)]

/-- **Exact face count for a crossing-free involution**: a fixed-point-free involution of `Fin (2*m)`
with no interleaving chords has exactly `m + 1` face orbits. -/
theorem permOrbitCount_eq_of_noInterleaving_two_mul (m : ℕ) (hm : 1 ≤ m)
    (σ : Equiv.Perm (Fin (2 * m))) (hσ : σ * σ = 1) (hfix : ∀ x, σ x ≠ x)
    (hnc : NoInterleaving σ) :
    permOrbitCount (finRotate (2 * m) * σ) = m + 1 := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  exact permOrbitCount_eq_of_noInterleaving_succ k σ hσ hfix hnc

/-- **Exact face count for a crossing-free involution** (length form). -/
theorem permOrbitCount_eq_of_noInterleaving {n m : ℕ} (σ : Equiv.Perm (Fin n)) (hm : 1 ≤ m)
    (hn : n = 2 * m) (hσ : σ * σ = 1) (hfix : ∀ x, σ x ≠ x) (hnc : NoInterleaving σ) :
    permOrbitCount (finRotate n * σ) = m + 1 := by
  subst hn
  exact permOrbitCount_eq_of_noInterleaving_two_mul m hm σ hσ hfix hnc

/-- **The mean-limit equality characterization**: a pairing of `2*m` positions has exactly `m + 1`
faces if and only if it is non-crossing (`m ≥ 1`). -/
theorem pairOrbitCount_eq_iff_isNonCrossing {l : List (GUEEntry ι N)} (p : GUEPairing l) (m : ℕ)
    (hm : 1 ≤ m) (hl : l.length = 2 * m) :
    pairOrbitCount p = m + 1 ↔ IsNonCrossing p := by
  constructor
  · intro hcount
    by_contra hnc'
    have hle := pairOrbitCount_le_of_not_isNonCrossing l p m hl hnc'
    omega
  · intro hnc'
    have hσ : partnerPerm p * partnerPerm p = 1 := by
      refine Equiv.ext fun i => ?_
      show (partnerPerm p * partnerPerm p) i = (1 : Equiv.Perm (Fin l.length)) i
      rw [Equiv.Perm.mul_apply, Equiv.Perm.one_apply]
      exact partnerPerm_involutive p i
    have hmain := permOrbitCount_eq_of_noInterleaving (σ := partnerPerm p) hm hl hσ
      (partnerPerm_ne_self p) hnc'
    exact hmain


/-- **The mean-limit equality, forward form**: a non-crossing pairing of `2*m` positions has exactly
`m + 1` faces (`m ≥ 1`). -/
theorem pairOrbitCount_eq_of_isNonCrossing {l : List (GUEEntry ι N)} (p : GUEPairing l) (m : ℕ)
    (hm : 1 ≤ m) (hl : l.length = 2 * m) (h : IsNonCrossing p) :
    pairOrbitCount p = m + 1 :=
  (pairOrbitCount_eq_iff_isNonCrossing p m hm hl).mpr h

end

end GUEStrongConvergence
