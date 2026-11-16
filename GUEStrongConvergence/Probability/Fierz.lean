/-
# The completeness (Fierz) identity for the Hermitian matrix basis

This file proves the completeness identity of the Part II handoff, equation (1.3):

`∑ a b, hermBasis a b * B * hermBasis a b = tr(B) • 1`

for every complex `N × N` matrix `B`, where `hermBasis a b` is the explicit orthonormal
Hermitian basis of `GUEStrongConvergence.Probability.HermitianCoordinates`.

The proof reduces the double sum over the `N²` ordered pairs to the pair-level identity
`hermBasis_mul_mul_add` (the two basis elements attached to an unordered pair `{a, b}`
contribute `single a a (B b b) + single b b (B a a)`) plus the diagonal identity
`hermBasis_mul_self_eq_single`, and then evaluates the resulting sum of diagonal matrix units.
The reduction uses only the symmetry of the index condition `a ≠ b` under exchanging the two
indices, so no ordering of `Fin N` is needed.
-/
import GUEStrongConvergence.Probability.HermitianCoordinates

open Matrix
open scoped Matrix

namespace GUEStrongConvergence

noncomputable section

variable {N : ℕ}

/-! ### Auxiliary summation lemmas -/

/-- Removing the diagonal from a double sum and exchanging the two indices leaves the value
unchanged. -/
lemma sum_ite_ne_swap (f : Fin N → Fin N → Matrix (Fin N) (Fin N) ℂ) :
    ∑ a, ∑ b, (if a = b then 0 else f b a) = ∑ a, ∑ b, (if a = b then 0 else f a b) := by
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by
    by_cases hab : a = b
    · subst hab
      simp
    · have hba : ¬ b = a := fun h => hab h.symm
      simp [hab, hba]

/-- Off-diagonal double sum of a symmetrized kernel is twice the off-diagonal double sum of
the kernel. -/
lemma sum_ite_ne_add_swap (f : Fin N → Fin N → Matrix (Fin N) (Fin N) ℂ) :
    ∑ a, ∑ b, (if a = b then 0 else (f a b + f b a))
      = (2 : ℂ) • ∑ a, ∑ b, (if a = b then 0 else f a b) := by
  have h1 : ∀ a b : Fin N,
      (if a = b then 0 else (f a b + f b a))
        = (if a = b then 0 else f a b) + (if a = b then 0 else f b a) := by
    intro a b
    split_ifs <;> simp
  calc ∑ a, ∑ b, (if a = b then 0 else (f a b + f b a))
      = ∑ a, ∑ b, ((if a = b then 0 else f a b) + (if a = b then 0 else f b a)) := by
        exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => h1 a b
    _ = ∑ a, ∑ b, (if a = b then 0 else f a b) + ∑ a, ∑ b, (if a = b then 0 else f b a) := by
        simp only [Finset.sum_add_distrib]
    _ = (2 : ℂ) • ∑ a, ∑ b, (if a = b then 0 else f a b) := by
        rw [sum_ite_ne_swap f, two_smul, add_comm]

/-- Splitting a double sum into its diagonal part and its off-diagonal part. -/
lemma sum_split_diag (f : Fin N → Fin N → Matrix (Fin N) (Fin N) ℂ) :
    ∑ a, ∑ b, f a b
      = (∑ a, f a a) + ∑ a, ∑ b, (if a = b then 0 else f a b) := by
  have h : ∀ a, (∑ b, f a b)
      = (∑ b, (if a = b then f a a else 0)) + (∑ b, (if a = b then 0 else f a b)) := by
    intro a
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun b _ => by split_ifs with h <;> simp_all
  calc ∑ a, ∑ b, f a b
      = ∑ a, ((∑ b, (if a = b then f a a else 0)) + (∑ b, (if a = b then 0 else f a b))) := by
        exact Finset.sum_congr rfl fun a _ => h a
    _ = (∑ a, ∑ b, (if a = b then f a a else 0)) + ∑ a, ∑ b, (if a = b then 0 else f a b) := by
        simp only [Finset.sum_add_distrib]
    _ = (∑ a, f a a) + ∑ a, ∑ b, (if a = b then 0 else f a b) := by
        rw [show (∑ a, ∑ b, (if a = b then f a a else 0)) = ∑ a, f a a from
          Finset.sum_congr rfl fun a _ => by simp]

/-! ### The Fierz identity -/

/-- Summing the diagonal matrix units: `∑ a b, single a a (B b b) = tr(B) • 1`. -/
theorem sum_single_diag (B : Matrix (Fin N) (Fin N) ℂ) :
    ∑ a, ∑ b, Matrix.single a a (B b b) = B.trace • (1 : Matrix (Fin N) (Fin N) ℂ) := by
  ext i j
  simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.single_apply,
    Matrix.trace]
  have hswap : (∑ a, ∑ b, (if a = i ∧ a = j then B b b else 0))
      = ∑ b, (if i = j then B b b else 0) := by
    rw [Finset.sum_comm (f := fun a b => if a = i ∧ a = j then B b b else 0)]
    refine Finset.sum_congr rfl fun b _ => ?_
    calc ∑ a, (if a = i ∧ a = j then B b b else 0)
        = ∑ a, (if a = i then (if i = j then B b b else 0) else 0) := by
          refine Finset.sum_congr rfl fun a _ => ?_
          by_cases h1 : a = i <;> by_cases h2 : i = j <;> simp_all
      _ = (if i = j then B b b else 0) := by
          simp [Finset.sum_ite_eq']
  rw [hswap]
  by_cases hij : i = j
  · simp [hij]
  · simp [hij]

/-- **Completeness (Fierz) identity** for the Hermitian basis, equation (1.3) of the handoff:
`∑ a b, hermBasis a b * B * hermBasis a b = tr(B) • 1`. -/
theorem fierz (B : Matrix (Fin N) (Fin N) ℂ) :
    ∑ a, ∑ b, hermBasis a b * B * hermBasis a b
      = B.trace • (1 : Matrix (Fin N) (Fin N) ℂ) := by
  have hoff : (∑ a, ∑ b, (if a = b then 0
        else hermBasis a b * B * hermBasis a b))
      = ∑ a, ∑ b, (if a = b then 0 else Matrix.single a a (B b b)) := by
    have hpair : ∀ a b : Fin N, (if a = b then 0
          else (hermBasis a b * B * hermBasis a b + hermBasis b a * B * hermBasis b a))
        = (if a = b then 0
          else (Matrix.single a a (B b b) + Matrix.single b b (B a a))) := by
      intro a b
      split_ifs with h
      · rfl
      · rw [hermBasis_mul_mul_add B h]
    have e1 := sum_ite_ne_add_swap (fun a b => hermBasis a b * B * hermBasis a b)
    have e2 := sum_ite_ne_add_swap (fun a b => Matrix.single a a (B b b))
    have key : (2 : ℂ) • (∑ a, ∑ b, (if a = b then 0
          else hermBasis a b * B * hermBasis a b))
        = (2 : ℂ) • ∑ a, ∑ b, (if a = b then 0 else Matrix.single a a (B b b)) := by
      rw [← e1, ← e2]
      exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => hpair a b
    have h2 : ((2 : ℂ)⁻¹) * 2 = 1 := by norm_num
    have := congrArg (fun M : Matrix (Fin N) (Fin N) ℂ => ((2 : ℂ)⁻¹) • M) key
    simpa [smul_smul, h2, one_smul] using this
  calc ∑ a, ∑ b, hermBasis a b * B * hermBasis a b
      = (∑ a, hermBasis a a * B * hermBasis a a)
          + ∑ a, ∑ b, (if a = b then 0 else hermBasis a b * B * hermBasis a b) :=
        sum_split_diag _
    _ = (∑ a, Matrix.single a a (B a a))
          + ∑ a, ∑ b, (if a = b then 0 else Matrix.single a a (B b b)) := by
        rw [hoff,
          show (∑ a, hermBasis a a * B * hermBasis a a) = ∑ a, Matrix.single a a (B a a) from
            Finset.sum_congr rfl fun a _ => hermBasis_mul_self_eq_single B a]
    _ = ∑ a, ∑ b, Matrix.single a a (B b b) :=
        (sum_split_diag (fun a b => Matrix.single a a (B b b))).symm
    _ = B.trace • (1 : Matrix (Fin N) (Fin N) ℂ) := sum_single_diag B

end

end GUEStrongConvergence
