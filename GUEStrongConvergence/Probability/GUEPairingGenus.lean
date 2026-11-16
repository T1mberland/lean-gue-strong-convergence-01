/-
# Genus bound for the face count of a GUE pairing: `c(p) ≤ m + 1`

The face count `c(p)` of `GUEPairingOrbits` (number of cycles of `i ↦ σ(i) + 1`) satisfies the
genus inequality `c(p) ≤ m + 1` for a pairing of `2m` entries.  The proof follows the classical
cycle-joining argument: a pairing is a product of `m` transpositions, and left multiplication by a
transposition changes the number of orbits of a permutation by at most one.

Main results:

* `permOrbitCount_inv`, `permOrbitCount_conj`: the orbit count is invariant under inverses and
  conjugation.
* `permOrbitCount_swap_mul_le`: multiplying a permutation on the left by a transposition increases
  its number of orbits by at most one.
* `permOrbitCount_mul_swap_le`: the same for right multiplication.
* `pairOrbitCount_le`: `c(p) ≤ m + 1` for every pairing of a list of `2m` entries.

The equality case (`c(p) = m + 1` iff `p` is non-crossing) needs the *exact* `±1` split/merge
lemma together with the arc bookkeeping; it is **not** proved here.
-/
import GUEStrongConvergence.Probability.GUEPairingOrbits
import Mathlib.GroupTheory.Perm.Fin

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

variable {α : Type*} [Fintype α] [DecidableEq α]

/-! ### Invariance of the orbit count -/

/-- Inverting a permutation does not change its number of orbits. -/
theorem permOrbitCount_inv (ρ : Equiv.Perm α) : permOrbitCount ρ⁻¹ = permOrbitCount ρ := by
  refine Fintype.card_congr ?_
  refine
    { toFun := Quotient.map id (fun a b h => (Equiv.Perm.sameCycle_inv).mp h)
      invFun := Quotient.map id (fun a b h => (Equiv.Perm.sameCycle_inv).mpr h)
      left_inv := fun q => by
        induction q using Quotient.inductionOn with
        | h a => rfl
      right_inv := fun q => by
        induction q using Quotient.inductionOn with
        | h a => rfl }

/-- Conjugating a permutation does not change its number of orbits. -/
theorem permOrbitCount_conj (f g : Equiv.Perm α) :
    permOrbitCount (g * f * g⁻¹) = permOrbitCount f := by
  have key : ∀ a b : α,
      (sameCycleSetoid (g * f * g⁻¹)) a b ↔ (sameCycleSetoid f) ((g⁻¹ : Equiv.Perm α) a)
        ((g⁻¹ : Equiv.Perm α) b) := fun a b => Equiv.Perm.sameCycle_conj
  refine Fintype.card_congr ?_
  refine
    { toFun := Quotient.map (fun a => (g⁻¹ : Equiv.Perm α) a) (fun a b h => (key a b).mp h)
      invFun := Quotient.map (fun a => (g : Equiv.Perm α) a)
        (fun a b h => (key (g a) (g b)).mpr (by simpa using h))
      left_inv := fun q => by
        induction q using Quotient.inductionOn with
        | h a => exact Quotient.sound (by simp)
      right_inv := fun q => by
        induction q using Quotient.inductionOn with
        | h a => exact Quotient.sound (by simp) }

/-! ### Cycle joining: left multiplication by a transposition -/

/-- **Cycle-joining lemma**: left multiplication by a transposition increases the number of
orbits of a permutation by at most one. -/
theorem permOrbitCount_swap_mul_le (π : Equiv.Perm α) (x y : α) :
    permOrbitCount (Equiv.swap x y * π) ≤ permOrbitCount π + 1 := by
  classical
  set g : Equiv.Perm α := Equiv.swap x y * π with hg
  have hgw : ∀ a : α, g a = Equiv.swap x y (π a) := fun a => rfl
  have hgx : g (π⁻¹ x) = y := by simp [hg]
  have hgy : g (π⁻¹ y) = x := by simp [hg]
  have hxne : ∀ z : α, ¬ Equiv.Perm.SameCycle g z x → z ≠ x := by
    intro z h hz; exact h (hz ▸ Equiv.Perm.SameCycle.refl g x)
  have hyne : ∀ z : α, ¬ Equiv.Perm.SameCycle g z y → z ≠ y := by
    intro z h hz; exact h (hz ▸ Equiv.Perm.SameCycle.refl g y)
  -- (F) the `π`-iterates of a point avoiding the two exceptional orbits are `g`-connected
  have hF : ∀ z : α, ¬ Equiv.Perm.SameCycle g z x → ¬ Equiv.Perm.SameCycle g z y →
      ∀ n : ℕ, Equiv.Perm.SameCycle π z ((g ^ n) z) := by
    intro z hx hy n
    induction n with
    | zero => exact Equiv.Perm.SameCycle.refl π z
    | succ n ih =>
      have hstep : (g ^ (n + 1)) z = g ((g ^ n) z) := by
        rw [pow_succ', Equiv.Perm.mul_apply]
      rw [hstep]
      have hux : (g ^ n) z ≠ x := by
        intro h; exact hx (h ▸ ⟨(n : ℤ), rfl⟩)
      have huy : (g ^ n) z ≠ y := by
        intro h; exact hy (h ▸ ⟨(n : ℤ), rfl⟩)
      have hnx : π ((g ^ n) z) ≠ x := by
        intro h
        have hpred : (g ^ n) z = π⁻¹ x := by
          have := congrArg (fun w : α => (π⁻¹ : Equiv.Perm α) w) h
          simpa using this
        have : g ((g ^ n) z) = y := by rw [hpred]; exact hgx
        exact hy ((show Equiv.Perm.SameCycle g z ((g ^ n) z) from ⟨(n : ℤ), rfl⟩).trans
          ⟨1, by rw [zpow_one]; exact this⟩)
      have hny : π ((g ^ n) z) ≠ y := by
        intro h
        have hpred : (g ^ n) z = π⁻¹ y := by
          have := congrArg (fun w : α => (π⁻¹ : Equiv.Perm α) w) h
          simpa using this
        have : g ((g ^ n) z) = x := by rw [hpred]; exact hgy
        exact hx ((show Equiv.Perm.SameCycle g z ((g ^ n) z) from ⟨(n : ℤ), rfl⟩).trans
          ⟨1, by rw [zpow_one]; exact this⟩)
      have hgu : g ((g ^ n) z) = π ((g ^ n) z) := by
        rw [hgw, Equiv.swap_apply_of_ne_of_ne hnx hny]
      rw [hgu]
      exact ih.trans ⟨1, by rw [zpow_one]⟩
  -- (D) the `π`-iterates of such a point are `g`-connected and stay away from `x`, `y`
  have hD : ∀ z : α, ¬ Equiv.Perm.SameCycle g z x → ¬ Equiv.Perm.SameCycle g z y →
      ∀ n : ℕ, Equiv.Perm.SameCycle g z ((π ^ n) z) ∧
        Equiv.Perm.SameCycle π z ((π ^ n) z) ∧ (π ^ n) z ≠ x ∧ (π ^ n) z ≠ y := by
    intro z hx hy n
    induction n with
    | zero =>
      refine ⟨Equiv.Perm.SameCycle.refl g z, Equiv.Perm.SameCycle.refl π z,
        hxne z hx, hyne z hy⟩
    | succ n ih =>
      obtain ⟨hgu, hpu, hux, huy⟩ := ih
      have hstep : (π ^ (n + 1)) z = π ((π ^ n) z) := by
        rw [pow_succ', Equiv.Perm.mul_apply]
      rw [hstep]
      have hnx : π ((π ^ n) z) ≠ x := by
        intro h
        have hpred : (π ^ n) z = π⁻¹ x := by
          have := congrArg (fun w : α => (π⁻¹ : Equiv.Perm α) w) h
          simpa using this
        have : g ((π ^ n) z) = y := by rw [hpred]; exact hgx
        exact hy (hgu.trans ⟨1, by rw [zpow_one]; exact this⟩)
      have hny : π ((π ^ n) z) ≠ y := by
        intro h
        have hpred : (π ^ n) z = π⁻¹ y := by
          have := congrArg (fun w : α => (π⁻¹ : Equiv.Perm α) w) h
          simpa using this
        have : g ((π ^ n) z) = x := by rw [hpred]; exact hgy
        exact hx (hgu.trans ⟨1, by rw [zpow_one]; exact this⟩)
      have hπg : g ((π ^ n) z) = π ((π ^ n) z) := by
        rw [hgw, Equiv.swap_apply_of_ne_of_ne hnx hny]
      refine ⟨?_, hpu.trans ⟨1, by rw [zpow_one]⟩, hnx, hny⟩
      rw [← hπg]
      exact hgu.trans ⟨1, by rw [zpow_one]⟩
  -- exceptional orbits
  set X : Quotient (sameCycleSetoid π) := Quotient.mk _ x with hX
  set qx : Quotient (sameCycleSetoid g) := Quotient.mk _ x with hqx
  set qy : Quotient (sameCycleSetoid g) := Quotient.mk _ y with hqy
  set Ag : Finset (Quotient (sameCycleSetoid g)) :=
    Finset.univ.filter (fun q => q ≠ qx ∧ q ≠ qy) with hAg
  set Bπ : Finset (Quotient (sameCycleSetoid π)) := Finset.univ.filter (fun q => q ≠ X) with hBπ
  -- every element of a non-exceptional `g`-orbit avoids `x` and `y`
  have hAgprop : ∀ q ∈ Ag, (¬ Equiv.Perm.SameCycle g q.out x) ∧
      ¬ Equiv.Perm.SameCycle g q.out y := by
    intro q hq
    rw [hAg, Finset.mem_filter] at hq
    exact ⟨fun h => hq.2.1 ((Quotient.out_eq q).symm.trans (Quotient.sound h)),
      fun h => hq.2.2 ((Quotient.out_eq q).symm.trans (Quotient.sound h))⟩
  have himg : ∀ q ∈ Ag, (Quotient.mk (sameCycleSetoid π) q.out) ∈ Bπ := by
    intro q hq
    obtain ⟨h1, h2⟩ := hAgprop q hq
    rw [hBπ, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    intro h
    have hsc : Equiv.Perm.SameCycle π q.out x := Quotient.exact h
    obtain ⟨n, hn⟩ := Equiv.Perm.SameCycle.exists_nat_pow_eq hsc
    have := (hD q.out h1 h2 n).1
    rw [hn] at this
    exact h1 this
  have hinj : Set.InjOn (fun q : Quotient (sameCycleSetoid g) =>
      Quotient.mk (sameCycleSetoid π) q.out) ↑Ag := by
    intro q1 hq1 q2 hq2 heq
    obtain ⟨h1x, h1y⟩ := hAgprop q1 hq1
    have hsc : Equiv.Perm.SameCycle π q1.out q2.out := Quotient.exact heq
    obtain ⟨n, hn⟩ := Equiv.Perm.SameCycle.exists_nat_pow_eq hsc
    have := (hD q1.out h1x h1y n).1
    rw [hn] at this
    exact (Quotient.out_eq q1).symm.trans ((Quotient.sound this).trans (Quotient.out_eq q2))
  have hAgB : Ag.card ≤ Bπ.card := Finset.card_le_card_of_injOn _ himg hinj
  have hB : Bπ.card + 1 ≤ permOrbitCount π := by
    have he : Bπ = Finset.univ.erase X := by
      ext q
      simp [hBπ]
    rw [he, Finset.card_erase_of_mem (Finset.mem_univ X)]
    have hpos : 1 ≤ (Finset.univ : Finset (Quotient (sameCycleSetoid π))).card :=
      Finset.card_pos.mpr ⟨X, Finset.mem_univ X⟩
    have : permOrbitCount π = (Finset.univ : Finset (Quotient (sameCycleSetoid π))).card :=
      Finset.card_univ.symm
    omega
  have hcover : (Finset.univ : Finset (Quotient (sameCycleSetoid g))) ⊆ Ag ∪ {qx, qy} := by
    intro q _
    by_cases h1 : q = qx
    · simp [h1]
    · by_cases h2 : q = qy
      · simp [h2]
      · simp [hAg, h1, h2]
  have hgcard : permOrbitCount g ≤ Ag.card + 2 := by
    have h1 : (Finset.univ : Finset (Quotient (sameCycleSetoid g))).card ≤ (Ag ∪ {qx, qy}).card :=
      Finset.card_le_card hcover
    have h2 : (Ag ∪ {qx, qy}).card ≤ Ag.card + 2 := by
      have := Finset.card_union_le Ag ({qx, qy} : Finset (Quotient (sameCycleSetoid g)))
      have h3 : ({qx, qy} : Finset (Quotient (sameCycleSetoid g))).card ≤ 2 := by
        rcases eq_or_ne qx qy with h | h
        · rw [h]; simp
        · rw [Finset.card_pair h]
      omega
    have : permOrbitCount g = (Finset.univ : Finset (Quotient (sameCycleSetoid g))).card :=
      Finset.card_univ.symm
    omega
  omega

/-- **Right multiplication** by a transposition also increases the number of orbits by at most
one. -/
theorem permOrbitCount_mul_swap_le (π : Equiv.Perm α) (x y : α) :
    permOrbitCount (π * Equiv.swap x y) ≤ permOrbitCount π + 1 := by
  have h : (Equiv.swap x y * π⁻¹)⁻¹ = π * Equiv.swap x y := by
    rw [mul_inv_rev, inv_inv, Equiv.swap_inv]
  calc permOrbitCount (π * Equiv.swap x y)
      = permOrbitCount ((Equiv.swap x y * π⁻¹)⁻¹) := by rw [h]
    _ = permOrbitCount (Equiv.swap x y * π⁻¹) := permOrbitCount_inv _
    _ ≤ permOrbitCount π⁻¹ + 1 := permOrbitCount_swap_mul_le π⁻¹ x y
    _ = permOrbitCount π + 1 := by rw [permOrbitCount_inv]

/-! ### Involution bound -/

/-- The number of pairs of an involution: `(n - 2) / 2 + 1 = n / 2` for `n ≥ 2`. -/
lemma div_two_sub_two (n : ℕ) (h : 2 ≤ n) : (n - 2) / 2 + 1 = n / 2 := by
  have h1 := Nat.div_add_mod n 2
  have h2 := Nat.div_add_mod (n - 2) 2
  have h3 : n % 2 = (n - 2) % 2 := by omega
  omega

/-- **Transposition peeling**: if `σ` is an involution, then multiplying `τ` on the right by `σ`
adds at most half the number of moved points to the number of orbits. -/
theorem permOrbitCount_mul_involution_le_aux :
    ∀ (d : ℕ) (τ σ : Equiv.Perm α), σ * σ = 1 → σ.support.card ≤ d →
      permOrbitCount (τ * σ) ≤ permOrbitCount τ + σ.support.card / 2 := by
  intro d
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro τ σ hσ hd
    rcases Nat.eq_zero_or_pos σ.support.card with h0 | hpos
    · have hsupp : σ.support = ∅ := Finset.card_eq_zero.mp h0
      have hone : σ = 1 := Equiv.ext fun a => by
        by_contra h
        have ha : a ∈ σ.support := by rwa [Equiv.Perm.mem_support]
        rw [hsupp] at ha
        simpa using ha
      rw [hone] at h0 ⊢
      rw [h0]
      simp
    · obtain ⟨a, ha⟩ := Finset.card_pos.mp hpos
      have hσa : σ a ≠ a := by rwa [Equiv.Perm.mem_support] at ha
      have hane : a ≠ σ a := fun h => hσa h.symm
      have hσσ : ∀ w : α, σ (σ w) = w := by
        intro w
        have := congrArg (fun f : Equiv.Perm α => f w) hσ
        simpa [Equiv.Perm.mul_apply] using this
      have hσ'a : σ (σ a) = a := hσσ a
      have hb : σ a ∈ σ.support := by
        rw [Equiv.Perm.mem_support, hσ'a]
        exact hane
      have h2 : 2 ≤ σ.support.card := by
        have hsub : ({a, σ a} : Finset α) ⊆ σ.support := by
          intro z hz
          rw [Finset.mem_insert, Finset.mem_singleton] at hz
          rcases hz with rfl | rfl
          · exact ha
          · exact hb
        have := Finset.card_le_card hsub
        rwa [Finset.card_pair hane] at this
      set s : Equiv.Perm α := Equiv.swap a (σ a) with hs
      set σ' : Equiv.Perm α := s * σ with hσ'def
      have hsplit : σ = s * σ' := by
        rw [hσ'def, hs, ← mul_assoc, Equiv.swap_mul_self, one_mul]
      have hcomm : s * σ = σ * s := by
        rw [hs]
        ext z
        simp only [Equiv.Perm.mul_apply]
        by_cases h1 : z = a
        · rw [h1]
          simp [hσ'a]
        by_cases hz2 : z = σ a
        · rw [hz2]
          simp [hσ'a]
        have h1' : σ z ≠ a := by
          intro h
          exact hz2 (by rw [← hσσ z, h])
        have h2' : σ z ≠ σ a := fun h => h1 (Equiv.injective σ h)
        rw [Equiv.swap_apply_of_ne_of_ne h1' h2', Equiv.swap_apply_of_ne_of_ne h1 hz2]
      have hσ'inv : σ' * σ' = 1 := by
        rw [hσ'def, mul_assoc s σ (s * σ), ← mul_assoc σ s σ, ← hcomm, mul_assoc s σ σ,
          ← mul_assoc s s (σ * σ), hs, Equiv.swap_mul_self, one_mul, hσ]
      have hσ'a' : σ' a = a := by
        rw [hσ'def, Equiv.Perm.mul_apply]
        simp [hs]
      have hσ'b : σ' (σ a) = σ a := by
        rw [hσ'def, Equiv.Perm.mul_apply]
        simp [hs, hσ'a]
      have hσ'z : ∀ z, z ≠ a → z ≠ σ a → σ' z = σ z := by
        intro z h1 hz2
        have h1' : σ z ≠ a := fun h => hz2 (by rw [← hσσ z, h])
        have h2' : σ z ≠ σ a := fun h => h1 (Equiv.injective σ h)
        rw [hσ'def, hs, Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne h1' h2']
      have hsupp' : σ'.support = (σ.support.erase a).erase (σ a) := by
        ext z
        rw [Equiv.Perm.mem_support, Finset.mem_erase, Finset.mem_erase, Equiv.Perm.mem_support]
        constructor
        · intro h
          have h1 : z ≠ a := by
            intro hz; rw [hz] at h; exact h hσ'a'
          have hz2 : z ≠ σ a := by
            intro hz; rw [hz] at h; exact h hσ'b
          exact ⟨hz2, h1, by rwa [hσ'z z h1 hz2] at h⟩
        · rintro ⟨hz2, h1, hmem⟩
          rw [hσ'z z h1 hz2]
          exact hmem
      have hcard' : σ'.support.card = σ.support.card - 2 := by
        have hmem : σ a ∈ σ.support.erase a := by
          rw [Finset.mem_erase]
          exact ⟨hane.symm, hb⟩
        rw [hsupp', Finset.card_erase_of_mem hmem, Finset.card_erase_of_mem ha]
        omega
      have hlt : σ'.support.card < d := by omega
      have ih' := ih σ'.support.card hlt (τ * s) σ' hσ'inv le_rfl
      have hswap : permOrbitCount (τ * s) ≤ permOrbitCount τ + 1 := by
        rw [hs]
        exact permOrbitCount_mul_swap_le τ a (σ a)
      calc permOrbitCount (τ * σ) = permOrbitCount ((τ * s) * σ') := by rw [hsplit, ← mul_assoc]
        _ ≤ permOrbitCount (τ * s) + σ'.support.card / 2 := ih'
        _ ≤ (permOrbitCount τ + 1) + σ'.support.card / 2 := by omega
        _ ≤ permOrbitCount τ + σ.support.card / 2 := by
            have hd2 := div_two_sub_two σ.support.card h2
            rw [← hd2, ← hcard']
            omega

/-- **Involution bound**: `c (τ σ) ≤ c τ + #{moved points of σ} / 2` for an involution `σ`. -/
theorem permOrbitCount_mul_involution_le (τ σ : Equiv.Perm α) (hσ : σ * σ = 1) :
    permOrbitCount (τ * σ) ≤ permOrbitCount τ + σ.support.card / 2 :=
  permOrbitCount_mul_involution_le_aux σ.support.card τ σ hσ le_rfl

/-! ### The rotation is a single cycle -/

/-- The cyclic shift `finRotate n` has at most one orbit. -/
theorem permOrbitCount_finRotate_le (n : ℕ) : permOrbitCount (finRotate n) ≤ 1 := by
  have hsub : Subsingleton (Quotient (sameCycleSetoid (finRotate n))) := by
    refine ⟨fun q1 q2 => ?_⟩
    induction q1 using Quotient.inductionOn with
    | h a =>
      induction q2 using Quotient.inductionOn with
      | h b =>
        rcases Nat.lt_or_ge n 2 with hlt | hge
        · interval_cases n
          · exact a.elim0
          · exact Quotient.sound (by rw [Subsingleton.elim a b])
        · obtain ⟨x0, hx0, hall⟩ := isCycle_finRotate_of_le hge
          have hsupp := support_finRotate_of_le hge
          have ha : finRotate n a ≠ a := by
            rw [← Equiv.Perm.mem_support, hsupp]
            exact Finset.mem_univ a
          have hb : finRotate n b ≠ b := by
            rw [← Equiv.Perm.mem_support, hsupp]
            exact Finset.mem_univ b
          exact Quotient.sound ((hall ha).symm.trans (hall hb))
  exact Fintype.card_le_one_iff_subsingleton.mpr hsub

/-! ### The genus bound for pairings -/

/-- **Genus bound for the face count** (Target 2, inequality): a pairing of `2m` entries has at
most `m + 1` faces. -/
theorem pairOrbitCount_le {ι : Type*} [Fintype ι] [DecidableEq ι] {N : ℕ}
    (l : List (GUEEntry ι N)) (p : GUEPairing l) (m : ℕ) (hl : l.length = 2 * m) :
    pairOrbitCount p ≤ m + 1 := by
  have hσ : partnerPerm p * partnerPerm p = 1 := by
    refine Equiv.Perm.ext fun i => ?_
    show (partnerPerm p * partnerPerm p) i = (1 : Equiv.Perm (Fin l.length)) i
    rw [Equiv.Perm.mul_apply, Equiv.Perm.one_apply]
    exact partnerPerm_involutive p i
  have hsupp : (partnerPerm p).support = Finset.univ := by
    ext i
    constructor
    · intro _; exact Finset.mem_univ i
    · intro _
      rw [Equiv.Perm.mem_support]
      exact partnerPerm_ne_self p i
  have hcard : (partnerPerm p).support.card = 2 * m := by
    rw [hsupp, Finset.card_univ, Fintype.card_fin, hl]
  have hmain := permOrbitCount_mul_involution_le (finRotate l.length) (partnerPerm p) hσ
  have hrot := permOrbitCount_finRotate_le l.length
  have hhalf : (partnerPerm p).support.card / 2 = m := by rw [hcard]; omega
  have hpair : pairOrbitCount p = permOrbitCount (finRotate l.length * partnerPerm p) := rfl
  rw [hpair]
  omega

end

end GUEStrongConvergence
