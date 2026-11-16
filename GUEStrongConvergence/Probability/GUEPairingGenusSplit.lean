/-
# The exact split/merge lemma for orbit counts under a transposition

For a permutation `π` of a finite type and a transposition `swap x y`, the number of orbits of
`swap x y * π` differs from that of `π` by exactly `+1` (when `x` and `y` lie in the same
`π`-cycle: that cycle splits into two) or exactly `-1` (when they lie in different cycles: the two
cycles merge).

Main results:

* `sameCycle_iff_exists_nat`: `SameCycle ρ a b` iff some forward iterate of `a` is `b` or some
  forward iterate of `b` is `a`.
* `sameCycle_of_invariant`: a set containing `a` and invariant under `ρ` and `ρ⁻¹` contains the
  `SameCycle`-class of `a`.
* `swap_mul_merge_subset`: in the merge case the union of the two `π`-cycles is a single cycle of
  `swap x y * π`.
* `permOrbitCount_swap_mul_le_sub_one`: the merge bound `c (swap x y * π) ≤ c π - 1`.
* `swap_mul_not_sameCycle`: in the split case `x` and `y` are separated by `swap x y * π`.
* `permOrbitCount_swap_mul_eq_add_one`, `permOrbitCount_swap_mul_eq_sub_one`: the exact `±1` laws.

All of the above are proved; `/print axioms` reports only `propext`, `Classical.choice` and
`Quot.sound`.
-/
import GUEStrongConvergence.Probability.GUEPairingGenus

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

/-! ### Forward iteration and invariant sets -/

/-- `SameCycle` in terms of forward iterates of one of the two points. -/
theorem sameCycle_iff_exists_nat {β : Type*} [Finite β] (ρ : Equiv.Perm β) (a b : β) :
    Equiv.Perm.SameCycle ρ a b ↔ ∃ k : ℕ, (ρ ^ k) a = b ∨ (ρ ^ k) b = a := by
  constructor
  · intro h
    obtain ⟨k, hk⟩ := Equiv.Perm.SameCycle.exists_nat_pow_eq h
    exact ⟨k, Or.inl hk⟩
  · rintro ⟨k, hk | hk⟩
    · exact ⟨(k : ℤ), by simpa using hk⟩
    · exact Equiv.Perm.SameCycle.symm ⟨(k : ℤ), by simpa using hk⟩

/-- A set containing `a` and invariant under `ρ` and `ρ⁻¹` contains the `ρ`-class of `a`. -/
theorem sameCycle_of_invariant {β : Type*} [Finite β] {ρ : Equiv.Perm β} {S : Set β}
    (hS : ∀ z ∈ S, ρ z ∈ S) (hSi : ∀ z ∈ S, ρ⁻¹ z ∈ S) {a : β} (ha : a ∈ S)
    {z : β} (hz : Equiv.Perm.SameCycle ρ a z) : z ∈ S := by
  have hfwd : ∀ (k : ℕ) (u : β), u ∈ S → (ρ ^ k) u ∈ S := by
    intro k
    induction k with
    | zero => intro u hu; simpa using hu
    | succ k ih => intro u hu; rw [pow_succ', Equiv.Perm.mul_apply]; exact hS _ (ih u hu)
  have hbwd : ∀ (k : ℕ) (u : β), u ∈ S → ((ρ⁻¹) ^ k) u ∈ S := by
    intro k
    induction k with
    | zero => intro u hu; simpa using hu
    | succ k ih =>
      intro u hu
      rw [pow_succ', Equiv.Perm.mul_apply]
      exact hSi _ (ih u hu)
  obtain ⟨k, hk | hk⟩ := (sameCycle_iff_exists_nat ρ a z).mp hz
  · rw [← hk]; exact hfwd k a ha
  · have hz_eq : ((ρ⁻¹) ^ k) a = z := by
      have h := congrArg (fun w => ((ρ⁻¹) ^ k) w) hk
      rw [inv_pow] at h
      simpa using h.symm
    rw [← hz_eq]
    exact hbwd k a ha

/-! ### Merge case geometry -/

/-- **Forward march through the `π`-cycle of `x`** (merge case): if `y` is not in that cycle then
all its iterates stay in one cycle of `swap x y * π`. -/
theorem swap_mul_march (π : Equiv.Perm α) (x y : α)
    (hxy : ¬ Equiv.Perm.SameCycle π x y) :
    ∀ k : ℕ, Equiv.Perm.SameCycle (Equiv.swap x y * π) x ((π ^ k) x) := by
  intro k
  induction k with
  | zero => exact Equiv.Perm.SameCycle.refl _ x
  | succ k ih =>
    have hu : (π ^ (k + 1)) x = π ((π ^ k) x) := by rw [pow_succ', Equiv.Perm.mul_apply]
    have hX : Equiv.Perm.SameCycle π x (π ((π ^ k) x)) :=
      (Equiv.Perm.sameCycle_apply_right).mpr
        (show Equiv.Perm.SameCycle π x ((π ^ k) x) from ⟨(k : ℤ), rfl⟩)
    rw [hu]
    by_cases h1 : π ((π ^ k) x) = x
    · rw [h1]
    by_cases h2 : π ((π ^ k) x) = y
    · exact absurd (h2 ▸ hX) hxy
    · refine ih.trans ⟨1, ?_⟩
      rw [zpow_one]
      show Equiv.swap x y (π ((π ^ k) x)) = _
      rw [Equiv.swap_apply_of_ne_of_ne h1 h2]

/-- **Merge case**: when `x` and `y` lie in different `π`-cycles, the union of the two cycles lies
in a single cycle of `swap x y * π`. -/
theorem swap_mul_merge_subset (π : Equiv.Perm α) (x y : α)
    (hxy : ¬ Equiv.Perm.SameCycle π x y) :
    ∀ z, Equiv.Perm.SameCycle π x z ∨ Equiv.Perm.SameCycle π y z →
      Equiv.Perm.SameCycle (Equiv.swap x y * π) x z := by
  have hxY : ¬ Equiv.Perm.SameCycle π y x := fun h => hxy h.symm
  have hmarch := swap_mul_march π x y hxy
  -- `x` and `y` lie in the same cycle of `g = swap x y * π`
  have hxyg : Equiv.Perm.SameCycle (Equiv.swap x y * π) x y := by
    obtain ⟨i, -, hi⟩ := Equiv.Perm.SameCycle.exists_pow_eq' (f := π) (x := x) (y := π⁻¹ x)
      ⟨-1, by rw [zpow_neg, zpow_one]⟩
    have hstep : (Equiv.swap x y * π) ((π ^ i) x) = y := by
      show Equiv.swap x y (π ((π ^ i) x)) = y
      have h1 : π ((π ^ i) x) = x := by
        rw [hi]
        simp
      rw [h1]
      simp
    exact (hmarch i).trans ⟨1, by rw [zpow_one]; exact hstep⟩
  -- march through the cycle of `y`
  have hmarchY : ∀ k : ℕ, Equiv.Perm.SameCycle (Equiv.swap x y * π) y ((π ^ k) y) := by
    intro k
    induction k with
    | zero => exact Equiv.Perm.SameCycle.refl _ y
    | succ k ih =>
      have hu : (π ^ (k + 1)) y = π ((π ^ k) y) := by rw [pow_succ', Equiv.Perm.mul_apply]
      have hY : Equiv.Perm.SameCycle π y (π ((π ^ k) y)) :=
        (Equiv.Perm.sameCycle_apply_right).mpr
          (show Equiv.Perm.SameCycle π y ((π ^ k) y) from ⟨(k : ℤ), rfl⟩)
      rw [hu]
      by_cases h1 : π ((π ^ k) y) = x
      · have hc : Equiv.Perm.SameCycle π x y := by rw [← h1]; exact hY.symm
        exact absurd hc hxy
      by_cases h2 : π ((π ^ k) y) = y
      · rw [h2]
      · refine ih.trans ⟨1, ?_⟩
        rw [zpow_one]
        show Equiv.swap x y (π ((π ^ k) y)) = _
        rw [Equiv.swap_apply_of_ne_of_ne h1 h2]
  intro z hz
  rcases hz with hz | hz
  · obtain ⟨k, hk⟩ := Equiv.Perm.SameCycle.exists_nat_pow_eq hz
    rw [← hk]
    exact hmarch k
  · obtain ⟨k, hk⟩ := Equiv.Perm.SameCycle.exists_nat_pow_eq hz
    rw [← hk]
    exact hxyg.trans (hmarchY k)

/-! ### The merge bound -/

/-- `π`-iterates of a point outside the classes of `x` and `y` stay in the orbit of
`swap x y * π`. -/
theorem swap_mul_iterate (π : Equiv.Perm α) (x y : α) :
    ∀ z : α, ¬ Equiv.Perm.SameCycle (Equiv.swap x y * π) z x →
      ¬ Equiv.Perm.SameCycle (Equiv.swap x y * π) z y →
      ∀ n : ℕ, Equiv.Perm.SameCycle (Equiv.swap x y * π) z ((π ^ n) z) := by
  set g : Equiv.Perm α := Equiv.swap x y * π with hg
  have hgw : ∀ a : α, g a = Equiv.swap x y (π a) := fun a => rfl
  have hgx : g (π⁻¹ x) = y := by simp [hg]
  have hgy : g (π⁻¹ y) = x := by simp [hg]
  intro z hx hy n
  induction n with
  | zero => exact Equiv.Perm.SameCycle.refl _ z
  | succ n ih =>
    have hstep : (π ^ (n + 1)) z = π ((π ^ n) z) := by rw [pow_succ', Equiv.Perm.mul_apply]
    rw [hstep]
    have hnx : π ((π ^ n) z) ≠ x := by
      intro h
      have hpred : (π ^ n) z = π⁻¹ x := by
        have := congrArg (fun w : α => (π⁻¹ : Equiv.Perm α) w) h
        simpa using this
      have h' : g ((π ^ n) z) = y := by rw [hpred]; exact hgx
      exact hy (ih.trans ⟨1, by rw [zpow_one]; exact h'⟩)
    have hny : π ((π ^ n) z) ≠ y := by
      intro h
      have hpred : (π ^ n) z = π⁻¹ y := by
        have := congrArg (fun w : α => (π⁻¹ : Equiv.Perm α) w) h
        simpa using this
      have h' : g ((π ^ n) z) = x := by rw [hpred]; exact hgy
      exact hx (ih.trans ⟨1, by rw [zpow_one]; exact h'⟩)
    have hπg : g ((π ^ n) z) = π ((π ^ n) z) := by
      rw [hgw, Equiv.swap_apply_of_ne_of_ne hnx hny]
    rw [← hπg]
    exact ih.trans ⟨1, by rw [zpow_one]⟩

/-- **Merge bound**: if `x` and `y` lie in different `π`-cycles, then `swap x y * π` has strictly
fewer orbits than `π`. -/
theorem permOrbitCount_swap_mul_le_sub_one (π : Equiv.Perm α) (x y : α)
    (hxy : ¬ Equiv.Perm.SameCycle π x y) :
    permOrbitCount (Equiv.swap x y * π) ≤ permOrbitCount π - 1 := by
  set g : Equiv.Perm α := Equiv.swap x y * π with hg
  have hmerge : ∀ z, Equiv.Perm.SameCycle π x z ∨ Equiv.Perm.SameCycle π y z →
      Equiv.Perm.SameCycle g x z := by
    have h := swap_mul_merge_subset π x y hxy
    rw [← hg] at h
    exact h
  have hiter := swap_mul_iterate π x y
  set X : Quotient (sameCycleSetoid π) := Quotient.mk _ x with hX
  set Y : Quotient (sameCycleSetoid π) := Quotient.mk _ y with hY
  set qx : Quotient (sameCycleSetoid g) := Quotient.mk _ x with hqx
  set qy : Quotient (sameCycleSetoid g) := Quotient.mk _ y with hqy
  have hXY : X ≠ Y := fun h => hxy (Quotient.exact h)
  set Ag : Finset (Quotient (sameCycleSetoid g)) :=
    Finset.univ.filter (fun q => q ≠ qx ∧ q ≠ qy) with hAg
  set Bπ : Finset (Quotient (sameCycleSetoid π)) :=
    Finset.univ.filter (fun q => q ≠ X ∧ q ≠ Y) with hBπ
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
    refine ⟨Finset.mem_univ _, ?_, ?_⟩
    · intro h
      obtain ⟨n, hn⟩ := Equiv.Perm.SameCycle.exists_nat_pow_eq (Quotient.exact h)
      have := hiter q.out h1 h2 n
      rw [hn] at this
      exact h1 this
    · intro h
      obtain ⟨n, hn⟩ := Equiv.Perm.SameCycle.exists_nat_pow_eq (Quotient.exact h)
      have := hiter q.out h1 h2 n
      rw [hn] at this
      exact h2 this
  have hinj : Set.InjOn (fun q : Quotient (sameCycleSetoid g) =>
      Quotient.mk (sameCycleSetoid π) q.out) ↑Ag := by
    intro q1 hq1 q2 hq2 heq
    obtain ⟨h1x, h1y⟩ := hAgprop q1 hq1
    obtain ⟨n, hn⟩ := Equiv.Perm.SameCycle.exists_nat_pow_eq (Quotient.exact heq)
    have := hiter q1.out h1x h1y n
    rw [hn] at this
    exact (Quotient.out_eq q1).symm.trans ((Quotient.sound this).trans (Quotient.out_eq q2))
  have hAgB : Ag.card ≤ Bπ.card := Finset.card_le_card_of_injOn _ himg hinj
  have hBcard : Bπ.card + 2 ≤ permOrbitCount π := by
    have he : Bπ = (Finset.univ.erase X).erase Y := by
      ext q
      simp only [hBπ, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
      tauto
    have hYmem : Y ∈ (Finset.univ : Finset (Quotient (sameCycleSetoid π))).erase X :=
      Finset.mem_erase.mpr ⟨hXY.symm, Finset.mem_univ Y⟩
    rw [he, Finset.card_erase_of_mem hYmem, Finset.card_erase_of_mem (Finset.mem_univ X)]
    have hpos : 2 ≤ (Finset.univ : Finset (Quotient (sameCycleSetoid π))).card := by
      have h1 : ({X, Y} : Finset (Quotient (sameCycleSetoid π))) ⊆ Finset.univ :=
        Finset.subset_univ _
      have := Finset.card_le_card h1
      rwa [Finset.card_pair hXY] at this
    have hc : permOrbitCount π = (Finset.univ : Finset (Quotient (sameCycleSetoid π))).card :=
      Finset.card_univ.symm
    omega
  have hcover : (Finset.univ : Finset (Quotient (sameCycleSetoid g))) ⊆ Ag ∪ {qx} := by
    intro q _
    by_cases h : q ∈ Ag
    · simp [h]
    · simp only [hAg, Finset.mem_filter, Finset.mem_univ, true_and, not_and_or, not_not] at h
      rcases h with h | h
      · rw [h]; simp
      · have hxyg : Equiv.Perm.SameCycle g x y := hmerge y (Or.inr (Equiv.Perm.SameCycle.refl π y))
        have hq : q = qx := by
          rw [h]
          simpa [hqx, hqy] using (Quotient.sound hxyg).symm
        rw [hq]
        simp
  have hcard : permOrbitCount g ≤ Ag.card + 1 := by
    have h1 : (Finset.univ : Finset (Quotient (sameCycleSetoid g))).card ≤ (Ag ∪ {qx}).card :=
      Finset.card_le_card hcover
    have h2 : (Ag ∪ {qx} : Finset (Quotient (sameCycleSetoid g))).card ≤ Ag.card + 1 := by
      have := Finset.card_union_le Ag ({qx} : Finset (Quotient (sameCycleSetoid g)))
      simp only [Finset.card_singleton] at this ⊢
      omega
    have hg_card : permOrbitCount g = (Finset.univ : Finset (Quotient (sameCycleSetoid g))).card :=
      Finset.card_univ.symm
    omega
  have hfin : permOrbitCount g ≤ permOrbitCount π - 1 := by omega
  exact hg ▸ hfin

/-! ### Split case geometry -/

/-- **Split case**: if `x ≠ y` lie in the same `π`-cycle, then `swap x y * π` separates them: the
class of `x` is trapped in the arc running from `x` up to (but excluding) `y`. -/
theorem swap_mul_not_sameCycle (π : Equiv.Perm α) (x y : α)
    (hxy : Equiv.Perm.SameCycle π x y) (hne : x ≠ y) :
    ¬ Equiv.Perm.SameCycle (Equiv.swap x y * π) x y := by
  obtain ⟨i, -, hi⟩ := Equiv.Perm.SameCycle.exists_pow_eq' (f := π) (x := x) (y := y) hxy
  have hi0 : 0 < i := by
    rcases Nat.eq_zero_or_pos i with h | h
    · rw [h] at hi
      simp only [pow_zero] at hi
      exact absurd hi hne
    · exact h
  have hex : ∃ k : ℕ, 0 < k ∧ (π ^ k) x = y := ⟨i, hi0, hi⟩
  set m := Nat.find hex with hm
  have hmpos : 0 < m := (Nat.find_spec hex).1
  have hmval : (π ^ m) x = y := (Nat.find_spec hex).2
  have hmin : ∀ k, k < m → ¬ (0 < k ∧ (π ^ k) x = y) := fun k hk => Nat.find_min hex hk
  have hxin : ∀ k, 0 < k → k < m → (π ^ k) x ≠ x := by
    intro k hk hkm hkx
    have hy : (π ^ (m - k)) x = y := by
      have h2 : (π ^ m) x = (π ^ (m - k)) ((π ^ k) x) := by
        rw [← Equiv.Perm.mul_apply, ← pow_add, Nat.sub_add_cancel (by omega)]
      rw [hkx, hmval] at h2
      exact h2.symm
    exact hmin (m - k) (by omega) ⟨by omega, hy⟩
  set S : Set α := {z | ∃ k : ℕ, k < m ∧ (π ^ k) x = z} with hS
  have hxS : x ∈ S := ⟨0, hmpos, rfl⟩
  have hyS : y ∉ S := by
    rintro ⟨k, hkm, hk⟩
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · have h1 : x = y := by
        rw [h0] at hk
        simpa using hk
      exact hne h1
    · exact hmin k hkm ⟨h0, hk⟩
  -- the arc is invariant under `swap x y * π`
  have hfwd : ∀ z ∈ S, (Equiv.swap x y * π) z ∈ S := by
    rintro z ⟨k, hkm, rfl⟩
    show Equiv.swap x y (π ((π ^ k) x)) ∈ S
    by_cases h1 : k + 1 < m
    · have hne1 : π ((π ^ k) x) ≠ x := by
        have hpow : (π ^ (k + 1)) x = π ((π ^ k) x) := by rw [pow_succ', Equiv.Perm.mul_apply]
        rw [← hpow]
        exact hxin (k + 1) (by omega) h1
      have hne2 : π ((π ^ k) x) ≠ y := by
        intro h
        have hmem : (π ^ (k + 1)) x = y := by
          rw [pow_succ', Equiv.Perm.mul_apply]
          exact h
        exact hyS ⟨k + 1, h1, hmem⟩
      rw [Equiv.swap_apply_of_ne_of_ne hne1 hne2]
      exact ⟨k + 1, h1, by rw [pow_succ', Equiv.Perm.mul_apply]⟩
    · have hk1 : k + 1 = m := by omega
      have hy : π ((π ^ k) x) = y := by
        have h1' : (π ^ (k + 1)) x = π ((π ^ k) x) := by
          rw [pow_succ', Equiv.Perm.mul_apply]
        rw [← h1', hk1]
        exact hmval
      rw [hy]
      rw [show Equiv.swap x y y = x from by simp]
      exact hxS
  have hbwd : ∀ z ∈ S, (Equiv.swap x y * π)⁻¹ z ∈ S := by
    rintro z ⟨k, hkm, rfl⟩
    have hinv : (Equiv.swap x y * π)⁻¹ ((π ^ k) x) =
        π⁻¹ (Equiv.swap x y ((π ^ k) x)) := by
      rw [mul_inv_rev, Equiv.swap_inv, Equiv.Perm.mul_apply]
    rw [hinv]
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · -- `z = x`: one step back gives the last element of the arc
      rw [h0]
      have hval : π ((π ^ (m - 1)) x) = y := by
        rw [← Equiv.Perm.mul_apply, ← pow_succ', Nat.sub_add_cancel hmpos]
        exact hmval
      have hstep : π⁻¹ (Equiv.swap x y ((π ^ 0) x)) = (π ^ (m - 1)) x := by
        have h1 : Equiv.swap x y ((π ^ 0) x) = π ((π ^ (m - 1)) x) := by
          rw [pow_zero]
          rw [show Equiv.swap x y ((1 : Equiv.Perm α) x) = y from by simp, hval]
        rw [h1]
        simp
      rw [hstep]
      exact ⟨m - 1, by omega, rfl⟩
    · have hneq1 : (π ^ k) x ≠ y := by
        intro h
        exact hyS ⟨k, hkm, h⟩
      have hneq2 : (π ^ k) x ≠ x := hxin k h0 hkm
      rw [Equiv.swap_apply_of_ne_of_ne hneq2 hneq1]
      have hstep : π⁻¹ ((π ^ k) x) = (π ^ (k - 1)) x := by
        have h2 : (π ^ k) x = π ((π ^ (k - 1)) x) := by
          rw [← Equiv.Perm.mul_apply, ← pow_succ', Nat.sub_add_cancel h0]
        rw [h2]
        simp
      rw [hstep]
      exact ⟨k - 1, by omega, rfl⟩
  intro hbad
  have := sameCycle_of_invariant hfwd hbwd hxS hbad
  exact hyS this

/-! ### The exact `±1` laws -/

/-- **Merge law**: if `x` and `y` lie in different `π`-cycles, then `swap x y * π` has exactly one
orbit fewer. -/
theorem permOrbitCount_swap_mul_eq_sub_one (π : Equiv.Perm α) (x y : α)
    (hxy : ¬ Equiv.Perm.SameCycle π x y) :
    permOrbitCount (Equiv.swap x y * π) = permOrbitCount π - 1 := by
  refine le_antisymm (permOrbitCount_swap_mul_le_sub_one π x y hxy) ?_
  have h := permOrbitCount_swap_mul_le (Equiv.swap x y * π) x y
  rw [← mul_assoc, Equiv.swap_mul_self, one_mul] at h
  omega

/-- **Split law**: if `x ≠ y` lie in the same `π`-cycle, then `swap x y * π` has exactly one orbit
more. -/
theorem permOrbitCount_swap_mul_eq_add_one (π : Equiv.Perm α) (x y : α)
    (hxy : Equiv.Perm.SameCycle π x y) (hne : x ≠ y) :
    permOrbitCount (Equiv.swap x y * π) = permOrbitCount π + 1 := by
  refine le_antisymm (permOrbitCount_swap_mul_le π x y) ?_
  have hns := swap_mul_not_sameCycle π x y hxy hne
  have h := permOrbitCount_swap_mul_le_sub_one (Equiv.swap x y * π) x y hns
  rw [← mul_assoc, Equiv.swap_mul_self, one_mul] at h
  have hpos : 1 ≤ permOrbitCount π := by
    have h1 : 0 < permOrbitCount π :=
      Fintype.card_pos_iff.mpr ⟨Quotient.mk (sameCycleSetoid π) x⟩
    omega
  omega

/-! ### The arc description of a split cycle -/

/-- A positive `k < m` with `(π ^ k) x = x` is impossible when `m` is the least positive exponent
with `(π ^ m) x = y ≠ x`. -/
theorem pow_ne_self (π : Equiv.Perm α) (x y : α) (m : ℕ)
    (hmval : (π ^ m) x = y)
    (hmin : ∀ k, 0 < k → k < m → (π ^ k) x ≠ y) :
    ∀ k, 0 < k → k < m → (π ^ k) x ≠ x := by
  intro k hk hkm hkx
  have hy : (π ^ (m - k)) x = y := by
    have h2 : (π ^ m) x = (π ^ (m - k)) ((π ^ k) x) := by
      rw [← Equiv.Perm.mul_apply, ← pow_add, Nat.sub_add_cancel (by omega)]
    rw [hkx, hmval] at h2
    exact h2.symm
  exact hmin (m - k) (by omega) (by omega) hy

/-- **Forward march along the arc**: each `π ^ k x` with `k < m` is in the `swap x y * π`-class
of `x`. -/
theorem arc_march (π : Equiv.Perm α) (x y : α) (m : ℕ)
    (hmval : (π ^ m) x = y)
    (hmin : ∀ k, 0 < k → k < m → (π ^ k) x ≠ y) :
    ∀ k : ℕ, k < m → Equiv.Perm.SameCycle (Equiv.swap x y * π) x ((π ^ k) x) := by
  intro k
  induction k with
  | zero => intro _; exact Equiv.Perm.SameCycle.refl _ x
  | succ k ih =>
    intro hk
    have hk' : k < m := by omega
    have huk : Equiv.Perm.SameCycle (Equiv.swap x y * π) x ((π ^ k) x) := ih hk'
    have hne1 : π ((π ^ k) x) ≠ x := by
      have h := pow_ne_self π x y m hmval hmin (k + 1) (by omega) hk
      rwa [pow_succ', Equiv.Perm.mul_apply] at h
    have hne2 : π ((π ^ k) x) ≠ y := by
      have h := hmin (k + 1) (by omega) hk
      rwa [pow_succ', Equiv.Perm.mul_apply] at h
    have hg : (Equiv.swap x y * π) ((π ^ k) x) = π ((π ^ k) x) := by
      show Equiv.swap x y (π ((π ^ k) x)) = π ((π ^ k) x)
      rw [Equiv.swap_apply_of_ne_of_ne hne1 hne2]
    rw [show (π ^ (k + 1)) x = π ((π ^ k) x) from by rw [pow_succ', Equiv.Perm.mul_apply]]
    rw [← hg]
    exact huk.trans ⟨1, by rw [zpow_one]⟩

/-- **Arc description**: the `swap x y * π`-class of `x` is exactly the arc `{π ^ k x : k < m}`. -/
theorem arc_class_eq (π : Equiv.Perm α) (x y : α) (m : ℕ) (hne : x ≠ y)
    (hmval : (π ^ m) x = y)
    (hmin : ∀ k, 0 < k → k < m → (π ^ k) x ≠ y)
    (hmpos : 0 < m) :
    ∀ z, Equiv.Perm.SameCycle (Equiv.swap x y * π) x z ↔ ∃ k : ℕ, k < m ∧ (π ^ k) x = z := by
  have hxin := pow_ne_self π x y m hmval hmin
  set S : Set α := {z | ∃ k : ℕ, k < m ∧ (π ^ k) x = z} with hS
  have hxS : x ∈ S := ⟨0, hmpos, rfl⟩
  have hyS : y ∉ S := by
    rintro ⟨k, hkm, hk⟩
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · have h1 : x = y := by
        rw [h0] at hk
        simpa using hk
      exact hne h1
    · exact hmin k h0 hkm hk
  have hfwd : ∀ z ∈ S, (Equiv.swap x y * π) z ∈ S := by
    rintro z ⟨k, hkm, rfl⟩
    show Equiv.swap x y (π ((π ^ k) x)) ∈ S
    by_cases h1 : k + 1 < m
    · have hne1 : π ((π ^ k) x) ≠ x := by
        have hpow : (π ^ (k + 1)) x = π ((π ^ k) x) := by rw [pow_succ', Equiv.Perm.mul_apply]
        rw [← hpow]
        exact hxin (k + 1) (by omega) h1
      have hne2 : π ((π ^ k) x) ≠ y := by
        intro h
        have hmem : (π ^ (k + 1)) x = y := by
          rw [pow_succ', Equiv.Perm.mul_apply]
          exact h
        exact hmin (k + 1) (by omega) h1 hmem
      rw [Equiv.swap_apply_of_ne_of_ne hne1 hne2]
      exact ⟨k + 1, h1, by rw [pow_succ', Equiv.Perm.mul_apply]⟩
    · have hk1 : k + 1 = m := by omega
      have hy : π ((π ^ k) x) = y := by
        have h1' : (π ^ (k + 1)) x = π ((π ^ k) x) := by
          rw [pow_succ', Equiv.Perm.mul_apply]
        rw [← h1', hk1]
        exact hmval
      rw [hy]
      rw [show Equiv.swap x y y = x from by simp]
      exact hxS
  have hbwd : ∀ z ∈ S, (Equiv.swap x y * π)⁻¹ z ∈ S := by
    rintro z ⟨k, hkm, rfl⟩
    have hinv : (Equiv.swap x y * π)⁻¹ ((π ^ k) x) =
        π⁻¹ (Equiv.swap x y ((π ^ k) x)) := by
      rw [mul_inv_rev, Equiv.swap_inv, Equiv.Perm.mul_apply]
    rw [hinv]
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · rw [h0]
      have hval : π ((π ^ (m - 1)) x) = y := by
        rw [← Equiv.Perm.mul_apply, ← pow_succ', Nat.sub_add_cancel hmpos]
        exact hmval
      have hstep : π⁻¹ (Equiv.swap x y ((π ^ 0) x)) = (π ^ (m - 1)) x := by
        have h1 : Equiv.swap x y ((π ^ 0) x) = π ((π ^ (m - 1)) x) := by
          rw [pow_zero]
          rw [show Equiv.swap x y ((1 : Equiv.Perm α) x) = y from by simp, hval]
        rw [h1]
        simp
      rw [hstep]
      exact ⟨m - 1, by omega, rfl⟩
    · have hneq1 : (π ^ k) x ≠ y := by
        intro h
        exact hyS ⟨k, hkm, h⟩
      have hneq2 : (π ^ k) x ≠ x := hxin k h0 hkm
      rw [Equiv.swap_apply_of_ne_of_ne hneq2 hneq1]
      have hstep : π⁻¹ ((π ^ k) x) = (π ^ (k - 1)) x := by
        have h2 : (π ^ k) x = π ((π ^ (k - 1)) x) := by
          rw [← Equiv.Perm.mul_apply, ← pow_succ', Nat.sub_add_cancel h0]
        rw [h2]
        simp
      rw [hstep]
      exact ⟨k - 1, by omega, rfl⟩
  intro z
  constructor
  · intro hz
    exact sameCycle_of_invariant hfwd hbwd hxS hz
  · rintro ⟨k, hkm, rfl⟩
    exact arc_march π x y m hmval hmin k hkm

/-! ### (C) towards `crossing ⇒ c ≤ m - 1` -/

/-- The number of orbits of the cyclic shift is exactly one. -/
theorem permOrbitCount_finRotate_eq (n : ℕ) (h : 2 ≤ n) : permOrbitCount (finRotate n) = 1 := by
  refine le_antisymm (permOrbitCount_finRotate_le n) ?_
  have h1 : 0 < permOrbitCount (finRotate n) :=
    Fintype.card_pos_iff.mpr ⟨Quotient.mk (sameCycleSetoid (finRotate n)) ⟨0, by omega⟩⟩
  omega

/-- Iterates of the cyclic shift on the linear arc `[i, n)`. -/
theorem finRotate_iterate_val (n : ℕ) (i : Fin n) :
    ∀ k : ℕ, i.val + k < n → ((finRotate n ^ k) i).val = i.val + k := by
  match n with
  | 0 => intro k hk; exact absurd i.isLt (by omega)
  | (m + 1) =>
    intro k
    induction k with
    | zero => intro _; simp
    | succ k ih =>
      intro hk
      have h1 : i.val + k < m + 1 := by omega
      have hk' : ((finRotate (m + 1) ^ k) i).val = i.val + k := ih h1
      rw [show (finRotate (m + 1) ^ (k + 1)) i =
          finRotate (m + 1) ((finRotate (m + 1) ^ k) i) from by
        rw [pow_succ', Equiv.Perm.mul_apply]]
      rw [show ((finRotate (m + 1) ^ k) i) = (⟨i.val + k, by omega⟩ : Fin (m + 1)) from
        Fin.ext hk']
      have hne : (⟨i.val + k, by omega⟩ : Fin (m + 1)) ≠ Fin.last m := by
        intro hlast
        have : i.val + k = m := by simpa [Fin.last, Fin.ext_iff] using hlast
        omega
      rw [coe_finRotate_of_ne_last hne]
      simp
      omega

/-- **A crossing pair is separated**: in the cyclic order `a < b < c < d`, the transposition
`(a,c)` splits the cycle so that `b` and `d` end up in different cycles. -/
theorem finRotate_swap_not_sameCycle (n : ℕ) (a b c d : Fin n)
    (hab : a.val < b.val) (hbc : b.val < c.val) (hcd : c.val < d.val) :
    ¬ Equiv.Perm.SameCycle (Equiv.swap a c * finRotate n) b d := by
  have hlt : a.val < c.val := by omega
  have hmpos : 0 < c.val - a.val := by omega
  have hne : a ≠ c := by
    intro h
    have : a.val = c.val := by rw [h]
    omega
  have hmval : (finRotate n ^ (c.val - a.val)) a = c := by
    refine Fin.ext ?_
    rw [finRotate_iterate_val n a (c.val - a.val) (by omega)]
    omega
  have hmin : ∀ k, 0 < k → k < c.val - a.val → (finRotate n ^ k) a ≠ c := by
    intro k hk hkm hkc
    have hv : ((finRotate n ^ k) a).val = c.val := by rw [hkc]
    rw [finRotate_iterate_val n a k (by omega)] at hv
    omega
  have harc := arc_class_eq (finRotate n) a c (c.val - a.val) hne hmval hmin hmpos
  -- `b` lies on the arc of `a`
  have hb : Equiv.Perm.SameCycle (Equiv.swap a c * finRotate n) a b := by
    refine (harc b).mpr ⟨b.val - a.val, by omega, ?_⟩
    refine Fin.ext ?_
    rw [finRotate_iterate_val n a (b.val - a.val) (by omega)]
    omega
  intro hbad
  have had : Equiv.Perm.SameCycle (Equiv.swap a c * finRotate n) a d := hb.trans hbad
  obtain ⟨k, hkm, hk⟩ := (harc d).mp had
  have hv : ((finRotate n ^ k) a).val = d.val := by rw [hk]
  rw [finRotate_iterate_val n a k (by omega)] at hv
  omega

/-! ### Peeling one transposition pair off an involution -/

/-- **Peeling**: if `σ` is an involution with `σ i = j ≠ i`, then `σ = swap i j * σ'` where `σ'` is
an involution moving exactly two points fewer. -/
theorem exists_mul_swap_of_involution (σ : Equiv.Perm α) (hσ : σ * σ = 1) {i j : α}
    (hij : σ i = j) (hne : i ≠ j) :
    ∃ σ' : Equiv.Perm α, σ' * σ' = 1 ∧ σ'.support.card = σ.support.card - 2 ∧
      σ = Equiv.swap i j * σ' := by
  have hσa : σ i ≠ i := by
    rw [hij]
    exact fun h => hne h.symm
  have hσσ : ∀ w : α, σ (σ w) = w := by
    intro w
    have := congrArg (fun f : Equiv.Perm α => f w) hσ
    simpa [Equiv.Perm.mul_apply] using this
  have hane : i ≠ j := hne
  have ha_supp : i ∈ σ.support := by rwa [Equiv.Perm.mem_support]
  have hb : j ∈ σ.support := by
    rw [Equiv.Perm.mem_support, ← hij, hσσ, hij]
    exact hne
  set s : Equiv.Perm α := Equiv.swap i j with hs
  set σ' : Equiv.Perm α := s * σ with hσ'def
  refine ⟨σ', ?_, ?_, ?_⟩
  · have hcomm : s * σ = σ * s := by
      rw [hs]
      ext z
      simp only [Equiv.Perm.mul_apply]
      have hji : σ j = i := by rw [← hij, hσσ]
      by_cases h1 : z = i
      · rw [h1]
        show Equiv.swap i j (σ i) = σ (Equiv.swap i j i)
        rw [hij, show Equiv.swap i j j = i from by simp, show Equiv.swap i j i = j from by simp,
          hji]
      by_cases hz2 : z = j
      · rw [hz2]
        show Equiv.swap i j (σ j) = σ (Equiv.swap i j j)
        rw [hji, show Equiv.swap i j i = j from by simp, show Equiv.swap i j j = i from by simp,
          hij]
      have h1' : σ z ≠ i := by
        intro h
        apply hz2
        rw [← hσσ z, h, hij]
      have h2' : σ z ≠ j := by
        intro h
        apply h1
        exact Equiv.injective σ (by rw [h, hij])
      rw [Equiv.swap_apply_of_ne_of_ne h1' h2', Equiv.swap_apply_of_ne_of_ne h1 hz2]
    rw [hσ'def, mul_assoc s σ (s * σ), ← mul_assoc σ s σ, ← hcomm, mul_assoc s σ σ,
      ← mul_assoc s s (σ * σ), hs, Equiv.swap_mul_self, one_mul, hσ]
  · -- support: `σ'` fixes `i` and `j` and agrees with `σ` elsewhere
    have hσ'i : σ' i = i := by
      rw [hσ'def, Equiv.Perm.mul_apply]
      simp [hs, hij]
    have hji : σ j = i := by rw [← hij, hσσ]
    have hσ'j : σ' j = j := by
      rw [hσ'def, Equiv.Perm.mul_apply]
      rw [hji]
      simp [hs]
    have hσ'z : ∀ z, z ≠ i → z ≠ j → σ' z = σ z := by
      intro z h1 hz2
      have h1' : σ z ≠ i := by
        intro h
        apply hz2
        rw [← hσσ z, h, hij]
      have h2' : σ z ≠ j := by
        intro h
        apply h1
        exact Equiv.injective σ (by rw [h, hij])
      rw [hσ'def, hs, Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne h1' h2']
    have hsupp' : σ'.support = (σ.support.erase i).erase j := by
      ext z
      rw [Equiv.Perm.mem_support, Finset.mem_erase, Finset.mem_erase, Equiv.Perm.mem_support]
      constructor
      · intro h
        have h1 : z ≠ i := by
          intro hz; rw [hz] at h; exact h hσ'i
        have hz2 : z ≠ j := by
          intro hz; rw [hz] at h; exact h hσ'j
        exact ⟨hz2, h1, by rwa [hσ'z z h1 hz2] at h⟩
      · rintro ⟨hz2, h1, hmem⟩
        rw [hσ'z z h1 hz2]
        exact hmem
    have hmem : j ∈ σ.support.erase i := by
      rw [Finset.mem_erase]
      exact ⟨hne.symm, hb⟩
    rw [hsupp', Finset.card_erase_of_mem hmem, Finset.card_erase_of_mem ha_supp]
    omega
  · rw [hσ'def, hs, ← mul_assoc, Equiv.swap_mul_self, one_mul]

/-- **Left multiplication by an involution** adds at most half its support to the orbit count. -/
theorem permOrbitCount_mul_involution_le' (σ π : Equiv.Perm α) (hσ : σ * σ = 1) :
    permOrbitCount (σ * π) ≤ permOrbitCount π + σ.support.card / 2 := by
  have h := permOrbitCount_mul_involution_le π⁻¹ σ hσ
  have h1 : permOrbitCount (π⁻¹ * σ) = permOrbitCount (σ * π) := by
    rw [← permOrbitCount_inv (π⁻¹ * σ)]
    congr 1
    rw [mul_inv_rev, inv_inv, inv_eq_of_mul_eq_one_right hσ]
  have h2 : permOrbitCount π⁻¹ = permOrbitCount π := permOrbitCount_inv π
  rw [h1, h2] at h
  exact h

/-! ### (C): commutation lemmas for the crossing argument -/

/-- The transposition of a partner pair commutes with the involution. -/
theorem swap_mul_comm_of_involution {σ : Equiv.Perm α} (hσ : σ * σ = 1) {i j : α}
    (hij : σ i = j) (hne : i ≠ j) : Equiv.swap i j * σ = σ * Equiv.swap i j := by
  have hσσ : ∀ w : α, σ (σ w) = w := by
    intro w
    have := congrArg (fun f : Equiv.Perm α => f w) hσ
    simpa [Equiv.Perm.mul_apply] using this
  have hji : σ j = i := by rw [← hij, hσσ]
  ext z
  simp only [Equiv.Perm.mul_apply]
  by_cases h1 : z = i
  · rw [h1, hij, Equiv.swap_apply_right, Equiv.swap_apply_left, hji]
  by_cases h2 : z = j
  · rw [h2, hji, Equiv.swap_apply_left, Equiv.swap_apply_right, hij]
  have h1' : σ z ≠ i := by
    intro h
    apply h2
    rw [← hσσ z, h, hij]
  have h2' : σ z ≠ j := by
    intro h
    apply h1
    exact Equiv.injective σ (by rw [h, hij])
  rw [Equiv.swap_apply_of_ne_of_ne h1' h2', Equiv.swap_apply_of_ne_of_ne h1 h2]

/-- Transpositions of disjoint pairs commute. -/
theorem swap_mul_swap_comm {a b c d : α} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    Equiv.swap a c * Equiv.swap b d = Equiv.swap b d * Equiv.swap a c := by
  have hba : b ≠ a := hab.symm
  have hca : c ≠ a := hac.symm
  have hda : d ≠ a := had.symm
  have hcb : c ≠ b := hbc.symm
  have hdb : d ≠ b := hbd.symm
  have hdc : d ≠ c := hcd.symm
  have e1 : Equiv.swap b d a = a := Equiv.swap_apply_of_ne_of_ne hab had
  have e2 : Equiv.swap a c a = c := Equiv.swap_apply_left a c
  have e3 : Equiv.swap b d c = c := Equiv.swap_apply_of_ne_of_ne hcb hcd
  have e4 : Equiv.swap a c b = b := Equiv.swap_apply_of_ne_of_ne hba hbc
  have e5 : Equiv.swap b d b = d := Equiv.swap_apply_left b d
  have e6 : Equiv.swap a c d = d := Equiv.swap_apply_of_ne_of_ne hda hdc
  have e7 : Equiv.swap b d d = b := Equiv.swap_apply_right b d
  have e8 : Equiv.swap a c c = a := Equiv.swap_apply_right a c
  ext z
  simp only [Equiv.Perm.mul_apply]
  rcases eq_or_ne z a with rfl | h1
  · rw [e1, e2, e3]
  rcases eq_or_ne z b with rfl | h2
  · rw [e5, e6, e4, e5]
  rcases eq_or_ne z c with rfl | h3
  · rw [e3, e8, e1]
  rcases eq_or_ne z d with rfl | h4
  · rw [e7, e4, e6, e7]
  have f1 : Equiv.swap b d z = z := Equiv.swap_apply_of_ne_of_ne h2 h4
  have f2 : Equiv.swap a c z = z := Equiv.swap_apply_of_ne_of_ne h1 h3
  rw [f1, f2, f1]

/-- `(n - 4) / 2 = n / 2 - 2`. -/
lemma div_two_sub_four (n : ℕ) (h : 4 ≤ n) : (n - 4) / 2 = n / 2 - 2 := by
  have h1 := Nat.div_add_mod n 2
  have h2 := Nat.div_add_mod (n - 4) 2
  have h3 : n % 2 = (n - 4) % 2 := by omega
  omega

/-! ### (C): the crossing bound -/

/-- **Crossing bound** (involution form): an involution `σ` on `Fin n` whose pairing contains a
crossing `a < b < c < d` (`σ a = c`, `σ b = d`) has at most `#support / 2 - 1` cycles in
`finRotate n * σ`. -/
theorem involution_crossing_le (n : ℕ) (σ : Equiv.Perm (Fin n)) (hσ : σ * σ = 1)
    (a b c d : Fin n) (hab : a.val < b.val) (hbc : b.val < c.val) (hcd : c.val < d.val)
    (hac : σ a = c) (hbd : σ b = d) :
    permOrbitCount (finRotate n * σ) ≤ σ.support.card / 2 - 1 := by
  have hn : 2 ≤ n := by have := a.isLt; omega
  have hab' : a ≠ b := fun h => by rw [h] at hab; exact absurd hab (lt_irrefl _)
  have hacn : a ≠ c := fun h => by rw [h] at hab; omega
  have hadn : a ≠ d := fun h => by rw [h] at hab; omega
  have hbcn : b ≠ c := fun h => by rw [h] at hbc; exact absurd hbc (lt_irrefl _)
  have hbdn : b ≠ d := fun h => by rw [h] at hbc; omega
  have hcdn : c ≠ d := fun h => by rw [h] at hcd; exact absurd hcd (lt_irrefl _)
  have hσσ : ∀ w : Fin n, σ (σ w) = w := by
    intro w
    have := congrArg (fun f : Equiv.Perm (Fin n) => f w) hσ
    simpa [Equiv.Perm.mul_apply] using this
  -- conjugation: the two orientations have the same orbit count
  have hconj : permOrbitCount (finRotate n * σ) = permOrbitCount (σ * finRotate n) := by
    have h := permOrbitCount_conj (finRotate n * σ) σ
    rw [inv_eq_of_mul_eq_one_right hσ] at h
    have h2 : σ * (finRotate n * σ) * σ = σ * finRotate n := by
      calc σ * (finRotate n * σ) * σ = σ * finRotate n * (σ * σ) := by group
        _ = σ * finRotate n := by rw [hσ, mul_one]
    rw [h2] at h
    exact h.symm
  -- the cyclic shift is transitive
  have hτac : Equiv.Perm.SameCycle (finRotate n) a c := by
    obtain ⟨x0, -, hall⟩ := isCycle_finRotate_of_le hn
    have hsupp := support_finRotate_of_le hn
    have ha : finRotate n a ≠ a := by
      rw [← Equiv.Perm.mem_support, hsupp]; exact Finset.mem_univ a
    have hc : finRotate n c ≠ c := by
      rw [← Equiv.Perm.mem_support, hsupp]; exact Finset.mem_univ c
    exact (hall ha).symm.trans (hall hc)
  -- two peels
  obtain ⟨σ₁, hσ₁inv, hσ₁card, hσ₁eq⟩ := exists_mul_swap_of_involution σ hσ hac hacn
  have hσ₁form : σ₁ = Equiv.swap a c * σ := by
    rw [hσ₁eq, ← mul_assoc, Equiv.swap_mul_self, one_mul]
  have hbd₁ : σ₁ b = d := by
    rw [hσ₁form]
    show Equiv.swap a c (σ b) = d
    rw [hbd, Equiv.swap_apply_of_ne_of_ne (Ne.symm hadn) (Ne.symm hcdn)]
  obtain ⟨σ₂, hσ₂inv, hσ₂card, hσ₂eq⟩ := exists_mul_swap_of_involution σ₁ hσ₁inv hbd₁ hbdn
  have hσ₂form : σ₂ = Equiv.swap b d * σ₁ := by
    rw [hσ₂eq, ← mul_assoc, Equiv.swap_mul_self, one_mul]
  -- `T = swap b d * swap a c` is an involution commuting with `σ`
  have hcomm_ac : Equiv.swap a c * σ = σ * Equiv.swap a c :=
    swap_mul_comm_of_involution hσ hac hacn
  have hcomm_bd : Equiv.swap b d * σ = σ * Equiv.swap b d :=
    swap_mul_comm_of_involution hσ hbd hbdn
  have hcomm_s : Equiv.swap a c * Equiv.swap b d = Equiv.swap b d * Equiv.swap a c :=
    swap_mul_swap_comm hab' hacn hadn hbcn hbdn hcdn
  have hT_comm : (Equiv.swap b d * Equiv.swap a c) * σ =
      σ * (Equiv.swap b d * Equiv.swap a c) := by
    rw [mul_assoc, hcomm_ac, ← mul_assoc, hcomm_bd, mul_assoc]
  have hT_inv : (Equiv.swap b d * Equiv.swap a c) * (Equiv.swap b d * Equiv.swap a c) = 1 := by
    have h1 : Equiv.swap a c * (Equiv.swap b d * Equiv.swap a c) =
        Equiv.swap b d * (Equiv.swap a c * Equiv.swap a c) := by
      rw [← mul_assoc, hcomm_s, mul_assoc]
    calc (Equiv.swap b d * Equiv.swap a c) * (Equiv.swap b d * Equiv.swap a c)
        = Equiv.swap b d * (Equiv.swap a c * (Equiv.swap b d * Equiv.swap a c)) := by group
      _ = Equiv.swap b d * (Equiv.swap b d * (Equiv.swap a c * Equiv.swap a c)) := by rw [h1]
      _ = 1 := by rw [← mul_assoc, Equiv.swap_mul_self, one_mul, Equiv.swap_mul_self]
  have hfac : σ = σ₂ * Equiv.swap b d * Equiv.swap a c := by
    rw [hσ₂form, hσ₁form]
    have h1 : Equiv.swap b d * (Equiv.swap a c * σ) =
        (Equiv.swap b d * Equiv.swap a c) * σ := (mul_assoc _ _ _).symm
    have h2 : (σ * (Equiv.swap b d * Equiv.swap a c)) * Equiv.swap b d * Equiv.swap a c =
        σ * ((Equiv.swap b d * Equiv.swap a c) * (Equiv.swap b d * Equiv.swap a c)) := by
      group
    rw [h1, hT_comm, h2, hT_inv, mul_one]
  -- counts along the transposition order `(a,c)` then `(b,d)`
  have hτ1 : permOrbitCount (finRotate n) = 1 := permOrbitCount_finRotate_eq n hn
  have hc1 : permOrbitCount (Equiv.swap a c * finRotate n) =
      permOrbitCount (finRotate n) + 1 :=
    permOrbitCount_swap_mul_eq_add_one (finRotate n) a c hτac hacn
  have hc2 : permOrbitCount (Equiv.swap b d * (Equiv.swap a c * finRotate n)) =
      permOrbitCount (Equiv.swap a c * finRotate n) - 1 :=
    permOrbitCount_swap_mul_eq_sub_one (Equiv.swap a c * finRotate n) b d
      (finRotate_swap_not_sameCycle n a b c d hab hbc hcd)
  have hc3 := permOrbitCount_mul_involution_le' σ₂
    (Equiv.swap b d * (Equiv.swap a c * finRotate n)) hσ₂inv
  have hj : permOrbitCount (Equiv.swap a c * finRotate n) = 2 := by
    rw [hc1, hτ1]
  have hk : permOrbitCount (Equiv.swap b d * (Equiv.swap a c * finRotate n)) = 1 := by
    rw [hc2, hj]
  -- support bookkeeping
  have hcard : σ₂.support.card = σ.support.card - 4 := by
    rw [hσ₂card, hσ₁card]
    omega
  have hbig : 4 ≤ σ.support.card := by
    have hsub : ({a, b, c, d} : Finset (Fin n)) ⊆ σ.support := by
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with h | h | h | h
      · rw [h, Equiv.Perm.mem_support, hac]
        exact fun hh => hacn hh.symm
      · rw [h, Equiv.Perm.mem_support, hbd]
        exact fun hh => hbdn hh.symm
      · rw [h, Equiv.Perm.mem_support, show σ c = a from by rw [← hac, hσσ]]
        exact fun hh => hacn hh
      · rw [h, Equiv.Perm.mem_support, show σ d = b from by rw [← hbd, hσσ]]
        exact fun hh => hbdn hh
    have hcard4 : ({a, b, c, d} : Finset (Fin n)).card = 4 := by
      rw [Finset.card_insert_of_notMem (by simp [hab', hacn, hadn]),
        Finset.card_insert_of_notMem (by simp [hbcn, hbdn]),
        Finset.card_insert_of_notMem (by simp [hcdn])]
      simp
    have := Finset.card_le_card hsub
    omega
  have hdiv : σ₂.support.card / 2 = σ.support.card / 2 - 2 := by
    rw [hcard, div_two_sub_four σ.support.card hbig]
  have hp : 2 ≤ σ.support.card / 2 := by omega
  -- assembly
  rw [hconj]
  rw [show σ * finRotate n =
      σ₂ * (Equiv.swap b d * (Equiv.swap a c * finRotate n)) from by
    rw [hfac]
    group]
  calc permOrbitCount (σ₂ * (Equiv.swap b d * (Equiv.swap a c * finRotate n)))
      ≤ permOrbitCount (Equiv.swap b d * (Equiv.swap a c * finRotate n)) +
          σ₂.support.card / 2 := hc3
    _ = 1 + σ₂.support.card / 2 := by rw [hk]
    _ = 1 + (σ.support.card / 2 - 2) := by rw [hdiv]
    _ = σ.support.card / 2 - 1 := by omega

/-- **Crossing bound for a GUE pairing**: if the partner involution of a pairing of `2 * m` entries
contains a crossing `a < b < c < d` (partners `a ↔ c` and `b ↔ d`), then the face count is at most
`m - 1`. -/
theorem pairOrbitCount_le_of_crossing {ι : Type*} [Fintype ι] [DecidableEq ι] {N : ℕ}
    (l : List (GUEEntry ι N)) (p : GUEPairing l) (m : ℕ) (hl : l.length = 2 * m)
    (a b c d : Fin l.length) (hab : a.val < b.val) (hbc : b.val < c.val) (hcd : c.val < d.val)
    (hac : partnerPerm p a = c) (hbd : partnerPerm p b = d) :
    pairOrbitCount p ≤ m - 1 := by
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
  have h := involution_crossing_le l.length (partnerPerm p) hσ a b c d hab hbc hcd hac hbd
  rw [hsupp, Finset.card_univ, Fintype.card_fin] at h
  have hlen : l.length / 2 = m := by omega
  have hpair : pairOrbitCount p = permOrbitCount (finRotate l.length * partnerPerm p) := rfl
  rw [hpair, ← hlen]
  exact h

/-! ### Parity of the face count (the genus formula `c ≡ m + 1` mod 2) -/

/-- Left multiplication by a transposition flips the parity of the orbit count. -/
theorem permOrbitCount_swap_mul_mod_two {ρ : Equiv.Perm α} {x y : α} (hne : x ≠ y) :
    permOrbitCount (Equiv.swap x y * ρ) % 2 = (permOrbitCount ρ + 1) % 2 := by
  by_cases hsc : Equiv.Perm.SameCycle ρ x y
  · rw [permOrbitCount_swap_mul_eq_add_one ρ x y hsc hne]
  · rw [permOrbitCount_swap_mul_eq_sub_one ρ x y hsc]
    have hpos : 0 < permOrbitCount ρ :=
      Fintype.card_pos_iff.mpr ⟨Quotient.mk (sameCycleSetoid ρ) x⟩
    omega

/-- **Parity**: multiplying a permutation by an involution changes the number of orbits by half of
its support, modulo two. -/
theorem permOrbitCount_mul_involution_mod_two :
    ∀ (d : ℕ) (σ π : Equiv.Perm α), σ * σ = 1 → σ.support.card ≤ d →
      permOrbitCount (σ * π) % 2 = (permOrbitCount π + σ.support.card / 2) % 2 := by
  intro d
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro σ π hσ hd
    rcases Nat.eq_zero_or_pos σ.support.card with h0 | hpos
    · have hsupp : σ.support = ∅ := Finset.card_eq_zero.mp h0
      have hone : σ = 1 := Equiv.ext fun a => by
        by_contra h
        have ha : a ∈ σ.support := by rwa [Equiv.Perm.mem_support]
        rw [hsupp] at ha
        simpa using ha
      rw [hone] at h0 ⊢
      rw [one_mul, h0]
      simp
    · obtain ⟨a, ha⟩ := Finset.card_pos.mp hpos
      have hσa : σ a ≠ a := by rwa [Equiv.Perm.mem_support] at ha
      have hane : a ≠ σ a := fun h => hσa h.symm
      obtain ⟨σ', hσ'inv, hσ'card, hσ'eq⟩ :=
        exists_mul_swap_of_involution σ hσ (i := a) (j := σ a) rfl hane
      have hcard2 : σ'.support.card = σ.support.card - 2 := hσ'card
      have hlt : σ'.support.card < d := by omega
      have hstep : permOrbitCount (σ * π) % 2 =
          (permOrbitCount (σ' * π) + 1) % 2 := by
        rw [hσ'eq, mul_assoc]
        exact permOrbitCount_swap_mul_mod_two hane
      have hih := ih σ'.support.card hlt σ' π hσ'inv (le_refl _)
      have hσsupp : σ a ∈ σ.support := by
        rw [Equiv.Perm.mem_support]
        intro hh
        exact hane.symm (Equiv.injective σ hh)
      have h2le : 2 ≤ σ.support.card := by
        have hsub : ({a, σ a} : Finset α) ⊆ σ.support := by
          intro z hz
          rw [Finset.mem_insert, Finset.mem_singleton] at hz
          rcases hz with h | h
          · rw [h]; exact ha
          · rw [h]; exact hσsupp
        have := Finset.card_le_card hsub
        rwa [Finset.card_pair hane] at this
      have hdiv : σ'.support.card / 2 + 1 = σ.support.card / 2 := by
        rw [hcard2, div_two_sub_two σ.support.card h2le]
      have h1 : (permOrbitCount (σ' * π) + 1) % 2 =
          ((permOrbitCount π + σ'.support.card / 2) + 1) % 2 := by
        rw [Nat.add_mod (permOrbitCount (σ' * π)) 1 2, hih,
          ← Nat.add_mod (permOrbitCount π + σ'.support.card / 2) 1 2]
      rw [hstep, h1, Nat.add_assoc, hdiv]

/-- **Parity of the face count**: a pairing of `2 * m` entries (`m ≥ 1`) has `c(p) ≡ m + 1`
modulo two. -/
theorem pairOrbitCount_mod_two {ι : Type*} [Fintype ι] [DecidableEq ι] {N : ℕ}
    (l : List (GUEEntry ι N)) (p : GUEPairing l) (m : ℕ) (hm : 1 ≤ m) (hl : l.length = 2 * m) :
    pairOrbitCount p % 2 = (m + 1) % 2 := by
  have hn : 2 ≤ l.length := by omega
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
  have hconj : permOrbitCount (finRotate l.length * partnerPerm p) =
      permOrbitCount (partnerPerm p * finRotate l.length) := by
    have h := permOrbitCount_conj (finRotate l.length * partnerPerm p) (partnerPerm p)
    rw [inv_eq_of_mul_eq_one_right hσ] at h
    have h2 : partnerPerm p * (finRotate l.length * partnerPerm p) * partnerPerm p =
        partnerPerm p * finRotate l.length := by
      calc partnerPerm p * (finRotate l.length * partnerPerm p) * partnerPerm p
          = partnerPerm p * finRotate l.length * (partnerPerm p * partnerPerm p) := by group
        _ = partnerPerm p * finRotate l.length := by rw [hσ, mul_one]
    rw [h2] at h
    exact h.symm
  have h := permOrbitCount_mul_involution_mod_two (l.length) (partnerPerm p) (finRotate l.length)
    hσ (by rw [hsupp, Finset.card_univ, Fintype.card_fin])
  rw [hsupp, Finset.card_univ, Fintype.card_fin] at h
  have hτ : permOrbitCount (finRotate l.length) = 1 := permOrbitCount_finRotate_eq l.length hn
  have hlen : l.length / 2 = m := by omega
  rw [hτ, hlen] at h
  have hpair : pairOrbitCount p = permOrbitCount (finRotate l.length * partnerPerm p) := rfl
  rw [hpair, hconj]
  simpa [Nat.add_comm] using h

/-! ### Non-crossing pairings and ears -/

/-- A pairing is **non-crossing** in the cyclic order of the entry positions if no four positions
`a < b < c < d` are paired as `a ↔ c` and `b ↔ d`. -/
def IsNonCrossing {ι : Type*} [Fintype ι] [DecidableEq ι] {N : ℕ}
    {l : List (GUEEntry ι N)} (p : GUEPairing l) : Prop :=
  ∀ a b c d : Fin l.length, a.val < b.val → b.val < c.val → c.val < d.val →
    ¬ (partnerPerm p a = c ∧ partnerPerm p b = d)

/-- A pairing has an **ear** if two cyclically consecutive positions are paired. -/
def HasEar {ι : Type*} [Fintype ι] [DecidableEq ι] {N : ℕ}
    {l : List (GUEEntry ι N)} (p : GUEPairing l) : Prop :=
  ∃ i : Fin l.length, partnerPerm p i = finRotate l.length i

/-- A crossing witness of a pairing that is not non-crossing. -/
theorem exists_crossing_of_not_isNonCrossing {ι : Type*} [Fintype ι] [DecidableEq ι] {N : ℕ}
    {l : List (GUEEntry ι N)} {p : GUEPairing l} (h : ¬ IsNonCrossing p) :
    ∃ a b c d : Fin l.length, a.val < b.val ∧ b.val < c.val ∧ c.val < d.val ∧
      partnerPerm p a = c ∧ partnerPerm p b = d := by
  simp only [IsNonCrossing, not_forall, not_not] at h
  obtain ⟨a, b, c, d, hab, hbc, hcd, hcross⟩ := h
  exact ⟨a, b, c, d, hab, hbc, hcd, hcross.1, hcross.2⟩

/-- **A pairing that is not non-crossing has at most `m - 1` faces** (the crossing bound). -/
theorem pairOrbitCount_le_of_not_isNonCrossing {ι : Type*} [Fintype ι] [DecidableEq ι] {N : ℕ}
    (l : List (GUEEntry ι N)) (p : GUEPairing l) (m : ℕ) (hl : l.length = 2 * m)
    (h : ¬ IsNonCrossing p) : pairOrbitCount p ≤ m - 1 := by
  obtain ⟨a, b, c, d, hab, hbc, hcd, hac, hbd⟩ := exists_crossing_of_not_isNonCrossing h
  exact pairOrbitCount_le_of_crossing l p m hl a b c d hab hbc hcd hac hbd

/-! ### Equivariance of the orbit count across a bijection -/

/-- Conjugation of a permutation by a bijection between (possibly different) types. -/
def conjBy {β : Type*} (e : α ≃ β) (σ : Equiv.Perm α) : Equiv.Perm β where
  toFun b := e (σ (e.symm b))
  invFun b := e (σ.symm (e.symm b))
  left_inv b := by
    show e (σ.symm (e.symm (e (σ (e.symm b))))) = b
    simp
  right_inv b := by
    show e (σ (e.symm (e (σ.symm (e.symm b))))) = b
    simp

theorem conjBy_apply {β : Type*} (e : α ≃ β) (σ : Equiv.Perm α) (b : β) :
    conjBy e σ b = e (σ (e.symm b)) := rfl

theorem conjBy_pow_apply {β : Type*} (e : α ≃ β) (σ : Equiv.Perm α) (n : ℕ) (b : β) :
    ((conjBy e σ) ^ n) b = e ((σ ^ n) (e.symm b)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', Equiv.Perm.mul_apply, ih, conjBy_apply]
    simp only [Equiv.symm_apply_apply]
    rw [← Equiv.Perm.mul_apply, ← pow_succ']

/-- `SameCycle` is transported by conjugation with a bijection. -/
theorem conjBy_sameCycle_iff {β : Type*} [Finite β] (e : α ≃ β) (σ : Equiv.Perm α) (a b : β) :
    Equiv.Perm.SameCycle (conjBy e σ) a b ↔ Equiv.Perm.SameCycle σ (e.symm a) (e.symm b) := by
  rw [sameCycle_iff_exists_nat, sameCycle_iff_exists_nat]
  constructor
  · rintro ⟨n, h | h⟩
    · refine ⟨n, Or.inl ?_⟩
      have hh := conjBy_pow_apply e σ n a
      rw [h] at hh
      exact e.injective (by rw [hh, Equiv.apply_symm_apply])
    · refine ⟨n, Or.inr ?_⟩
      have hh := conjBy_pow_apply e σ n b
      rw [h] at hh
      exact e.injective (by rw [hh, Equiv.apply_symm_apply])
  · rintro ⟨n, h | h⟩
    · refine ⟨n, Or.inl ?_⟩
      rw [conjBy_pow_apply, h, Equiv.apply_symm_apply]
    · refine ⟨n, Or.inr ?_⟩
      rw [conjBy_pow_apply, h, Equiv.apply_symm_apply]

/-- **Equivariance**: conjugating a permutation by a bijection preserves its number of orbits. -/
theorem permOrbitCount_conjBy {β : Type*} [Fintype β] (e : α ≃ β) (σ : Equiv.Perm α) :
    permOrbitCount (conjBy e σ) = permOrbitCount σ := by
  refine Fintype.card_congr ?_
  refine
    { toFun := Quotient.map (fun b => e.symm b)
        (fun a b h => (conjBy_sameCycle_iff e σ a b).mp h)
      invFun := Quotient.map (fun a => e a)
        (fun a b h => (conjBy_sameCycle_iff e σ (e a) (e b)).mpr (by
          rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]
          exact h))
      left_inv := fun q => by
        induction q using Quotient.inductionOn with
        | h b => exact Quotient.sound (by simp)
      right_inv := fun q => by
        induction q using Quotient.inductionOn with
        | h a => exact Quotient.sound (by simp) }

end

end GUEStrongConvergence
