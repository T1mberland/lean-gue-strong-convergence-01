/-
# Orbit-count bookkeeping for the two-walk variance bound

This file supplies the permutation-orbit bookkeeping needed by the `O(N⁻²)` variance bound for a
fixed GUE trace word (`GUEWordSecondMoment`, `GUEWordVarianceBound`).

The two-walk loop count of a pairing with position permutation `σ` is
`twoWalkLoopCount k₁ k₂ σ = permOrbitCount (blockSuccPerm k₁ k₂ * σ)`.  The results here are:

* `permOrbitCount_sumCongr` (**block-diagonal split**): the number of orbits of a direct sum of
  permutations is the sum of the numbers of orbits,
  `permOrbitCount (f.sumCongr g) = permOrbitCount f + permOrbitCount g`.
  For a pairing that respects the two walks this is exactly the identity
  `L(σ₁ ⊞ σ₂) = c(σ₁) + c(σ₂)` used for the mean-square cancellation.
* `permOrbitCount_finRotate_eq_one`: the cyclic shift of a nonempty `Fin n` has exactly one orbit.
* `permOrbitCount_blockSuccPerm`: the two-block cyclic successor has exactly two orbits.
* `twoWalkLoopCount_le` (**two-walk genus inequality**): for every fixed-point-free involution
  `σ` on the `k₁ + k₂` slots with `k₁, k₂ ≥ 1`,
  `L(σ) ≤ (k₁ + k₂) / 2 + 2`.
  This is the two-boundary analogue of `pairOrbitCount_le` and the input to the genus expansion of
  the two-trace moment.
* `twoWalkLoopCount_sumCongr` (**block-diagonal loop count in slot form**): if `σ` is the
  conjugation by `finSumFinEquiv` of `σ₁ ⊞ σ₂`, then
  `L(σ) = c(σ₁) + c(σ₂)` with `c(σᵢ) = permOrbitCount (finRotate kᵢ * σᵢ)` the single-walk face
  count.
* `twoWalkLoopCount_cross_le` (**sharp cross-pairing bound**): if `σ` is a fixed-point-free
  involution with at least one pair crossing the two blocks, then `L(σ) ≤ (k₁ + k₂) / 2`.  The
  proof peels off a cross transposition `τ`: `c (S τ) = c (S⁻¹) - 1 = 1` by the exact merge law,
  and the remaining involution `τ σ` fixes the two endpoints, so
  `L(σ) = c ((S τ) (τ σ)) ≤ 1 + (k₁ + k₂ - 2) / 2 = (k₁ + k₂) / 2`.

All statements are exact for every `N`; no asymptotic or probabilistic statement is made here.
-/
import GUEStrongConvergence.Probability.GUEWordVarianceBound
import GUEStrongConvergence.Probability.GUEPairingGenus
import GUEStrongConvergence.Probability.GUEPairingGenusSplit

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

/-! ### Direct sums of permutations -/

variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

/-- Powers of a direct sum of permutations are computed blockwise. -/
theorem sumCongr_pow (f : Equiv.Perm α) (g : Equiv.Perm β) (n : ℕ) :
    (f.sumCongr g) ^ n = (f ^ n).sumCongr (g ^ n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, pow_succ, pow_succ, ih, Equiv.Perm.sumCongr_mul]

/-- Same-cycle classes of a direct sum, left block. -/
theorem sameCycle_sumCongr_inl (f : Equiv.Perm α) (g : Equiv.Perm β) (a b : α) :
    Equiv.Perm.SameCycle (f.sumCongr g) (Sum.inl a) (Sum.inl b) ↔
      Equiv.Perm.SameCycle f a b := by
  constructor
  · rintro ⟨n, hn⟩
    obtain ⟨m, hm⟩ := Equiv.Perm.SameCycle.exists_nat_pow_eq
      (show Equiv.Perm.SameCycle (f.sumCongr g) (Sum.inl a) (Sum.inl b) from ⟨n, hn⟩)
    rw [sumCongr_pow] at hm
    have hfab : (f ^ m) a = b := by simpa using hm
    refine ⟨(m : ℤ), ?_⟩
    rw [zpow_natCast]
    exact hfab
  · intro h
    obtain ⟨n, hn⟩ := Equiv.Perm.SameCycle.exists_nat_pow_eq h
    refine ⟨(n : ℤ), ?_⟩
    rw [zpow_natCast, sumCongr_pow]
    simpa using hn

/-- Same-cycle classes of a direct sum, right block. -/
theorem sameCycle_sumCongr_inr (f : Equiv.Perm α) (g : Equiv.Perm β) (a b : β) :
    Equiv.Perm.SameCycle (f.sumCongr g) (Sum.inr a) (Sum.inr b) ↔
      Equiv.Perm.SameCycle g a b := by
  constructor
  · rintro ⟨n, hn⟩
    obtain ⟨m, hm⟩ := Equiv.Perm.SameCycle.exists_nat_pow_eq
      (show Equiv.Perm.SameCycle (f.sumCongr g) (Sum.inr a) (Sum.inr b) from ⟨n, hn⟩)
    rw [sumCongr_pow] at hm
    have hgab : (g ^ m) a = b := by simpa using hm
    refine ⟨(m : ℤ), ?_⟩
    rw [zpow_natCast]
    exact hgab
  · intro h
    obtain ⟨n, hn⟩ := Equiv.Perm.SameCycle.exists_nat_pow_eq h
    refine ⟨(n : ℤ), ?_⟩
    rw [zpow_natCast, sumCongr_pow]
    simpa using hn

/-- The two blocks are never in the same cycle of a direct sum. -/
theorem not_sameCycle_sumCongr_inl_inr (f : Equiv.Perm α) (g : Equiv.Perm β) (a : α)
    (b : β) : ¬ Equiv.Perm.SameCycle (f.sumCongr g) (Sum.inl a) (Sum.inr b) := by
  rintro ⟨n, hn⟩
  obtain ⟨m, hm⟩ := Equiv.Perm.SameCycle.exists_nat_pow_eq
    (show Equiv.Perm.SameCycle (f.sumCongr g) (Sum.inl a) (Sum.inr b) from ⟨n, hn⟩)
  rw [sumCongr_pow] at hm
  simpa using hm

/-- The two blocks are never in the same cycle of a direct sum (other order). -/
theorem not_sameCycle_sumCongr_inr_inl (f : Equiv.Perm α) (g : Equiv.Perm β) (a : β)
    (b : α) : ¬ Equiv.Perm.SameCycle (f.sumCongr g) (Sum.inr a) (Sum.inl b) :=
  fun h => not_sameCycle_sumCongr_inl_inr f g b a h.symm

/-- The quotient by same-cycle classes of a direct sum is the sum of the two quotients. -/
def sumCongrQuotEquiv (f : Equiv.Perm α) (g : Equiv.Perm β) :
    Quotient (sameCycleSetoid (f.sumCongr g)) ≃
      Quotient (sameCycleSetoid f) ⊕ Quotient (sameCycleSetoid g) where
  toFun := Quotient.lift
    (fun x : α ⊕ β => match x with
      | Sum.inl a => Sum.inl (Quotient.mk (sameCycleSetoid f) a)
      | Sum.inr b => Sum.inr (Quotient.mk (sameCycleSetoid g) b))
    (by
      intro x y hxy
      cases x with
      | inl a =>
        cases y with
        | inl b =>
          exact congrArg Sum.inl (Quotient.sound (s := sameCycleSetoid f)
            (show (sameCycleSetoid f).r a b from
              (sameCycle_sumCongr_inl f g a b).mp
                (show Equiv.Perm.SameCycle (f.sumCongr g) (Sum.inl a) (Sum.inl b) from hxy)))
        | inr b =>
          exact absurd (show Equiv.Perm.SameCycle (f.sumCongr g) (Sum.inl a) (Sum.inr b)
            from hxy) (not_sameCycle_sumCongr_inl_inr f g a b)
      | inr a =>
        cases y with
        | inl b =>
          exact absurd (show Equiv.Perm.SameCycle (f.sumCongr g) (Sum.inr a) (Sum.inl b)
            from hxy) (not_sameCycle_sumCongr_inr_inl f g a b)
        | inr b =>
          exact congrArg Sum.inr (Quotient.sound (s := sameCycleSetoid g)
            (show (sameCycleSetoid g).r a b from
              (sameCycle_sumCongr_inr f g a b).mp
                (show Equiv.Perm.SameCycle (f.sumCongr g) (Sum.inr a) (Sum.inr b) from hxy))))
  invFun := Sum.elim
    (Quotient.map Sum.inl (by
      intro a b hab
      exact (sameCycle_sumCongr_inl f g a b).mpr
        (show Equiv.Perm.SameCycle f a b from hab)))
    (Quotient.map Sum.inr (by
      intro a b hab
      exact (sameCycle_sumCongr_inr f g a b).mpr
        (show Equiv.Perm.SameCycle g a b from hab)))
  left_inv := by
    intro q
    induction q using Quotient.inductionOn with
    | h x =>
      cases x with
      | inl a => rfl
      | inr b => rfl
  right_inv := by
    intro s
    cases s with
    | inl q =>
      induction q using Quotient.inductionOn with
      | h a => rfl
    | inr q =>
      induction q using Quotient.inductionOn with
      | h b => rfl

/-- **Block-diagonal split of the orbit count**: the number of orbits of a direct sum of
permutations is the sum of the numbers of orbits. -/
theorem permOrbitCount_sumCongr (f : Equiv.Perm α) (g : Equiv.Perm β) :
    permOrbitCount (f.sumCongr g) = permOrbitCount f + permOrbitCount g := by
  have h1 := Fintype.card_congr (sumCongrQuotEquiv f g)
  simp only [permOrbitCount]
  rwa [Fintype.card_sum] at h1

/-! ### Orbit count of an equivalent permutation -/

/-- The transport of permutations along an equivalence is multiplicative. -/
theorem permCongr_mul {α β : Type*} (e : α ≃ β) (p q : Equiv.Perm α) :
    e.permCongr (p * q) = e.permCongr p * e.permCongr q := by
  ext x
  simp [Equiv.permCongr_apply, Equiv.Perm.mul_apply]

/-- Same-cycle classes are transported by an equivalence of the underlying types. -/
theorem sameCycle_permCongr (e : α ≃ β) (f : Equiv.Perm α) (a b : α) :
    (e.permCongr f).SameCycle (e a) (e b) ↔ f.SameCycle a b := by
  have hpow : ∀ n : ℕ, (e.permCongr f) ^ n = e.permCongr (f ^ n) := by
    intro n
    induction n with
    | zero => exact (Equiv.permCongr_refl e).symm
    | succ n ih => rw [pow_succ, pow_succ, ih, permCongr_mul]
  constructor
  · rintro ⟨n, hn⟩
    obtain ⟨m, hm⟩ := Equiv.Perm.SameCycle.exists_nat_pow_eq
      (show Equiv.Perm.SameCycle (e.permCongr f) (e a) (e b) from ⟨n, hn⟩)
    rw [hpow, Equiv.permCongr_apply, Equiv.symm_apply_apply] at hm
    exact ⟨(m : ℤ), by rw [zpow_natCast]; exact e.injective hm⟩
  · intro h
    obtain ⟨m, hm⟩ := Equiv.Perm.SameCycle.exists_nat_pow_eq h
    refine ⟨(m : ℤ), ?_⟩
    rw [zpow_natCast, hpow, Equiv.permCongr_apply, Equiv.symm_apply_apply]
    exact congrArg e hm

/-- The quotient by same-cycle classes is invariant under an equivalence of the underlying
types. -/
def permCongrQuotEquiv {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (e : α ≃ β) (f : Equiv.Perm α) :
    Quotient (sameCycleSetoid f) ≃ Quotient (sameCycleSetoid (e.permCongr f)) where
  toFun := Quotient.map e (by
    intro a b hab
    exact (sameCycle_permCongr e f a b).mpr
      (show Equiv.Perm.SameCycle f a b from hab))
  invFun := Quotient.map e.symm (by
    intro x y hxy
    have hxy' : (e.permCongr f).SameCycle (e (e.symm x)) (e (e.symm y)) := by
      rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
      exact hxy
    have h : Equiv.Perm.SameCycle f (e.symm x) (e.symm y) :=
      (sameCycle_permCongr e f (e.symm x) (e.symm y)).mp hxy'
    show (sameCycleSetoid f).r (e.symm x) (e.symm y)
    exact h)
  left_inv := by
    intro q
    induction q using Quotient.inductionOn with
    | h a =>
      change Quotient.mk (sameCycleSetoid f) (e.symm (e a)) = Quotient.mk _ a
      simp
  right_inv := by
    intro q
    induction q using Quotient.inductionOn with
    | h b =>
      change Quotient.mk (sameCycleSetoid (e.permCongr f)) (e (e.symm b)) = Quotient.mk _ b
      simp

/-- The orbit count is invariant under an equivalence of the underlying types. -/
theorem permOrbitCount_permCongr {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β]
    [DecidableEq β] (e : α ≃ β) (f : Equiv.Perm α) :
    permOrbitCount (e.permCongr f) = permOrbitCount f := by
  have h := Fintype.card_congr (permCongrQuotEquiv e f)
  simp only [permOrbitCount] at h ⊢
  exact h.symm

/-! ### The two-block successor and the two-walk genus inequality -/

/-- The cyclic shift of a nonempty `Fin n` has exactly one orbit. -/
theorem permOrbitCount_finRotate_eq_one {n : ℕ} (hn : 1 ≤ n) :
    permOrbitCount (finRotate n) = 1 := by
  have hle := permOrbitCount_finRotate_le n
  have hpos : 0 < permOrbitCount (finRotate n) := by
    rw [permOrbitCount]
    exact Fintype.card_pos_iff.mpr ⟨Quotient.mk _ ⟨0, hn⟩⟩
  omega

/-- Every point of `Fin n` is in the cycle of `0` under the cyclic shift. -/
theorem sameCycle_finRotate_zero {n : ℕ} (hn : 1 ≤ n) (i : Fin n) :
    Equiv.Perm.SameCycle (finRotate n) i ⟨0, hn⟩ := by
  rcases Nat.lt_or_ge n 2 with hlt | hge
  · have hn1 : n = 1 := by omega
    subst hn1
    rw [Subsingleton.elim i ⟨0, hn⟩]
  · obtain ⟨x0, hx0, hall⟩ := isCycle_finRotate_of_le hge
    have hsupp := support_finRotate_of_le hge
    have hi : finRotate n i ≠ i := by
      rw [← Equiv.Perm.mem_support, hsupp]
      exact Finset.mem_univ i
    have h0 : finRotate n ⟨0, hn⟩ ≠ ⟨0, hn⟩ := by
      rw [← Equiv.Perm.mem_support, hsupp]
      exact Finset.mem_univ _
    exact (hall hi).symm.trans (hall h0)

/-- **The two-block cyclic successor has exactly two orbits** (one per walk), for nonempty
blocks. -/
theorem permOrbitCount_blockSuccPerm (k₁ k₂ : ℕ) (h₁ : 1 ≤ k₁) (h₂ : 1 ≤ k₂) :
    permOrbitCount (blockSuccPerm k₁ k₂) = 2 := by
  set e : Fin k₁ ⊕ Fin k₂ ≃ Fin (k₁ + k₂) := finSumFinEquiv with he
  have hblock : blockSuccPerm k₁ k₂ =
      e.permCongr ((finRotate k₁).sumCongr (finRotate k₂)) := by
    rw [Equiv.permCongr_def, Equiv.trans_assoc]
    rfl
  rw [hblock, permOrbitCount_permCongr, permOrbitCount_sumCongr,
    permOrbitCount_finRotate_eq_one h₁, permOrbitCount_finRotate_eq_one h₂]

/-- **Two-walk genus inequality**: a fixed-point-free involution pairing the `k₁ + k₂` walk slots
has at most `(k₁ + k₂) / 2 + 2` loops. -/
theorem twoWalkLoopCount_le (k₁ k₂ : ℕ) (h₁ : 1 ≤ k₁) (h₂ : 1 ≤ k₂)
    (σ : Equiv.Perm (Fin (k₁ + k₂))) (hσ : σ * σ = 1) (hfix : ∀ i, σ i ≠ i) :
    twoWalkLoopCount k₁ k₂ σ ≤ (k₁ + k₂) / 2 + 2 := by
  have hbound := permOrbitCount_mul_involution_le (blockSuccPerm k₁ k₂) σ hσ
  have hsupp : σ.support = Finset.univ := by
    ext i
    rw [Equiv.Perm.mem_support]
    simp [hfix i]
  have hcard : σ.support.card = k₁ + k₂ := by
    rw [hsupp, Finset.card_univ, Fintype.card_fin]
  have hS : permOrbitCount (blockSuccPerm k₁ k₂) = 2 :=
    permOrbitCount_blockSuccPerm k₁ k₂ h₁ h₂
  have hL : twoWalkLoopCount k₁ k₂ σ =
      permOrbitCount (blockSuccPerm k₁ k₂ * σ) := rfl
  rw [hcard, hS] at hbound
  rw [hL]
  omega

/-- **Block-diagonal loop count in slot form**: if the pairing permutation is the conjugate by
`finSumFinEquiv` of a direct sum `σ₁ ⊞ σ₂`, its two-walk loop count is the sum of the two
single-walk face counts `permOrbitCount (finRotate kᵢ * σᵢ)`. -/
theorem twoWalkLoopCount_sumCongr (k₁ k₂ : ℕ) (σ₁ : Equiv.Perm (Fin k₁))
    (σ₂ : Equiv.Perm (Fin k₂)) :
    twoWalkLoopCount k₁ k₂ (finSumFinEquiv.permCongr (σ₁.sumCongr σ₂)) =
      permOrbitCount (finRotate k₁ * σ₁) + permOrbitCount (finRotate k₂ * σ₂) := by
  set e : Fin k₁ ⊕ Fin k₂ ≃ Fin (k₁ + k₂) := finSumFinEquiv with he
  have hS : blockSuccPerm k₁ k₂ =
      e.permCongr ((finRotate k₁).sumCongr (finRotate k₂)) := by
    rw [Equiv.permCongr_def, Equiv.trans_assoc]
    rfl
  have hσ : (e.symm.trans (σ₁.sumCongr σ₂)).trans e =
      e.permCongr (σ₁.sumCongr σ₂) := by
    rw [Equiv.permCongr_def]
  rw [twoWalkLoopCount, hS, ← permCongr_mul, permOrbitCount_permCongr,
    Equiv.Perm.sumCongr_mul, permOrbitCount_sumCongr]

/-- The two blocks of `blockSuccPerm` lie in different orbits: a slot of the first block is never
in the same `blockSuccPerm`-cycle as a slot of the second block. -/
theorem blockSuccPerm_not_sameCycle (k₁ k₂ : ℕ) (i : Fin k₁) (j : Fin k₂) :
    ¬ Equiv.Perm.SameCycle (blockSuccPerm k₁ k₂) (Fin.castAdd k₂ i) (Fin.natAdd k₁ j) := by
  rintro ⟨n, hn⟩
  obtain ⟨m, hm⟩ := Equiv.Perm.SameCycle.exists_nat_pow_eq
    (show Equiv.Perm.SameCycle (blockSuccPerm k₁ k₂) (Fin.castAdd k₂ i)
      (Fin.natAdd k₁ j) from ⟨n, hn⟩)
  have hpow : ∀ m : ℕ, ∃ a : Fin k₁,
      ((blockSuccPerm k₁ k₂) ^ m) (Fin.castAdd k₂ i) = Fin.castAdd k₂ a := by
    intro m
    induction m with
    | zero => exact ⟨i, by simp⟩
    | succ m ih =>
      obtain ⟨a, ha⟩ := ih
      refine ⟨finRotate k₁ a, ?_⟩
      rw [pow_succ', Equiv.Perm.mul_apply, ha]
      simpa using blockSuccPerm_inl k₁ k₂ a
  obtain ⟨a, ha⟩ := hpow m
  rw [ha] at hm
  have hval := congrArg Fin.val hm
  simp only [Fin.val_castAdd, Fin.val_natAdd] at hval
  omega

/-- **Sharp cross-pairing bound**: a fixed-point-free involution with a pair crossing the two
blocks has at most `(k₁ + k₂) / 2` loops. -/
theorem twoWalkLoopCount_cross_le (k₁ k₂ : ℕ) (h₁ : 1 ≤ k₁) (h₂ : 1 ≤ k₂)
    (σ : Equiv.Perm (Fin (k₁ + k₂))) (hσ : σ * σ = 1) (hfix : ∀ i, σ i ≠ i)
    (hcross : ∃ (i : Fin k₁) (j : Fin k₂), σ (Fin.castAdd k₂ i) = Fin.natAdd k₁ j) :
    twoWalkLoopCount k₁ k₂ σ ≤ (k₁ + k₂) / 2 := by
  obtain ⟨i, j, hij⟩ := hcross
  set x : Fin (k₁ + k₂) := Fin.castAdd k₂ i with hx
  set y : Fin (k₁ + k₂) := Fin.natAdd k₁ j with hy
  have hxy : x ≠ y := by
    intro h
    have := congrArg Fin.val h
    simp only [hx, hy, Fin.val_castAdd, Fin.val_natAdd] at this
    omega
  have hσx : σ x = y := hij
  have hσσ : ∀ z, σ (σ z) = z := by
    intro z
    have h := congrArg (fun f : Equiv.Perm (Fin (k₁ + k₂)) => f z) hσ
    simpa [Equiv.Perm.mul_apply] using h
  have hσy : σ y = x := σ.injective (by rw [hσσ, hσx])
  set τ : Equiv.Perm (Fin (k₁ + k₂)) := Equiv.swap x y with hτ
  set σ' : Equiv.Perm (Fin (k₁ + k₂)) := τ * σ with hσ'def
  have hτx : τ x = y := by rw [hτ]; exact Equiv.swap_apply_left x y
  have hτy : τ y = x := by rw [hτ]; exact Equiv.swap_apply_right x y
  have hτ_of_ne : ∀ z, z ≠ x → z ≠ y → τ z = z := by
    intro z hzx hzy
    rw [hτ]
    exact Equiv.swap_apply_of_ne_of_ne hzx hzy
  have hσ'x : σ' x = x := by rw [hσ'def, Equiv.Perm.mul_apply, hσx, hτy]
  have hσ'y : σ' y = y := by rw [hσ'def, Equiv.Perm.mul_apply, hσy, hτx]
  have hσ'_of_ne : ∀ z, z ≠ x → z ≠ y → σ' z = σ z := by
    intro z hzx hzy
    rw [hσ'def, Equiv.Perm.mul_apply]
    exact hτ_of_ne (σ z)
      (fun h => hzy (σ.injective (h.trans hσy.symm)))
      (fun h => hzx (σ.injective (h.trans hσx.symm)))
  have hσ'inv : σ' * σ' = 1 := by
    refine Equiv.Perm.ext fun z => ?_
    rw [Equiv.Perm.mul_apply, Equiv.Perm.one_apply]
    by_cases hzx : z = x
    · subst hzx; rw [hσ'x, hσ'x]
    by_cases hzy : z = y
    · subst hzy; rw [hσ'y, hσ'y]
    · rw [hσ'_of_ne z hzx hzy, hσ'_of_ne (σ z)
        (fun h => hzy (σ.injective (h.trans hσy.symm)))
        (fun h => hzx (σ.injective (h.trans hσx.symm))), hσσ z]
  have hsupp : σ'.support = (Finset.univ.erase x).erase y := by
    ext z
    rw [Equiv.Perm.mem_support]
    constructor
    · intro hz
      have hzx : z ≠ x := by
        intro h; subst h; exact hz hσ'x
      have hzy : z ≠ y := by
        intro h; subst h; exact hz hσ'y
      exact Finset.mem_erase.mpr ⟨hzy, Finset.mem_erase.mpr ⟨hzx, Finset.mem_univ z⟩⟩
    · intro hz
      rw [Finset.mem_erase] at hz
      obtain ⟨hzy, hz'⟩ := hz
      rw [Finset.mem_erase] at hz'
      obtain ⟨hzx, -⟩ := hz'
      rw [hσ'_of_ne z hzx hzy]
      exact hfix z
  have hcard : σ'.support.card = k₁ + k₂ - 2 := by
    rw [hsupp]
    have hy' : y ∈ (Finset.univ.erase x : Finset (Fin (k₁ + k₂))) :=
      Finset.mem_erase.mpr ⟨hxy.symm, Finset.mem_univ y⟩
    rw [Finset.card_erase_of_mem hy', Finset.card_erase_of_mem (Finset.mem_univ x),
      Finset.card_univ, Fintype.card_fin]
    omega
  have hSτ : permOrbitCount (blockSuccPerm k₁ k₂ * τ) = 1 := by
    have hinv : (blockSuccPerm k₁ k₂ * τ)⁻¹ = τ * (blockSuccPerm k₁ k₂)⁻¹ := by
      rw [mul_inv_rev, Equiv.swap_inv]
    have hns : ¬ Equiv.Perm.SameCycle (blockSuccPerm k₁ k₂)⁻¹ x y := by
      rw [Equiv.Perm.sameCycle_inv]
      exact blockSuccPerm_not_sameCycle k₁ k₂ i j
    have hmerge := permOrbitCount_swap_mul_eq_sub_one (blockSuccPerm k₁ k₂)⁻¹ x y hns
    rw [← permOrbitCount_inv (blockSuccPerm k₁ k₂ * τ), hinv]
    rw [show τ * (blockSuccPerm k₁ k₂)⁻¹ =
      Equiv.swap x y * (blockSuccPerm k₁ k₂)⁻¹ from by rw [hτ]]
    rw [hmerge, permOrbitCount_inv, permOrbitCount_blockSuccPerm k₁ k₂ h₁ h₂]
  have hL : twoWalkLoopCount k₁ k₂ σ =
      permOrbitCount ((blockSuccPerm k₁ k₂ * τ) * σ') := by
    rw [twoWalkLoopCount]
    congr 1
    rw [hσ'def]
    simp only [mul_assoc]
    rw [← mul_assoc τ τ σ, Equiv.swap_mul_self, one_mul]
  have hbound := permOrbitCount_mul_involution_le (blockSuccPerm k₁ k₂ * τ) σ' hσ'inv
  rw [hcard, hSτ] at hbound
  rw [hL]
  have hdiv := div_two_sub_two (k₁ + k₂) (by omega)
  omega

end

end GUEStrongConvergence
