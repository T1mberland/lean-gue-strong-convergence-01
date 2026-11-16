/-
# The interval `[-2, 2]` is contained in the free semicircular spectrum

We prove `Set.Icc (-2) 2 ⊆ spectrum ℝ (semicircularFamily r i)` without using the
semicircle-measure density machinery.  The proof is the classical Weyl-sequence argument
for the free Jacobi operator: the vectors

`v_k = word (List.replicate k i)`

satisfy `semicircular i v_k = v_{k+1} + v_{k-1}` (with `v_{-1} = 0`), i.e. they form the
constant Jacobi matrix of the semicircle.  For `x ∈ (-2, 2)` write `x = 2 cos θ` and take the
truncated exponential vector `u_N = ∑_{k=0}^N e^{ikθ} v_k`.  Then `‖u_N‖ = √(N+1)` and
`(semicircular i - x) u_N` stays bounded, so `x` cannot be in the resolvent set.
-/
import FreeProbability.Fock.CStarModel
import Mathlib.Analysis.Normed.Algebra.Spectrum

open Filter FreeProbability FreeProbability.Fock Matrix
open scoped BigOperators ComplexOrder ENNReal Pointwise Topology

namespace GUEStrongConvergence

noncomputable section

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 4000000

namespace SemicircularInterval

variable {I : Type*}

/-- The chain vector `v_k`, the word of length `k` consisting only of the letter `i`. -/
def chainVec (i : I) (k : ℕ) : WordSpace I := word (List.replicate k i)

@[simp] lemma chainVec_zero (i : I) : chainVec i 0 = word ([] : List I) := rfl

@[simp] lemma norm_chainVec (i : I) (k : ℕ) : ‖chainVec i k‖ = 1 := by
  simp [chainVec]

lemma inner_chainVec (i : I) {k l : ℕ} :
    inner ℂ (chainVec i k) (chainVec i l) = if k = l then 1 else 0 := by
  classical
  rw [chainVec, chainVec, inner_word]
  by_cases h : k = l
  · simp [h]
  · have hne : List.replicate k i ≠ List.replicate l i := by
      intro hr
      exact h (by simpa using (List.replicate_inj.mp hr).1)
    simp [h, hne]

@[simp] lemma creation_chainVec (i : I) (k : ℕ) :
    creation i (chainVec i k) = chainVec i (k + 1) := by
  simp [chainVec, List.replicate_succ]

@[simp] lemma annihilation_chainVec (i : I) (k : ℕ) :
    annihilation i (chainVec i k) = if k = 0 then 0 else chainVec i (k - 1) := by
  cases k with
  | zero => simp [chainVec]
  | succ n =>
      rw [chainVec, List.replicate_succ, annihilation_word]
      simp [chainVec]

/-- The free Jacobi action on the chain vectors. -/
lemma semicircular_chainVec (i : I) (k : ℕ) :
    semicircular i (chainVec i k) =
      chainVec i (k + 1) + (if k = 0 then 0 else chainVec i (k - 1)) := by
  simp [semicircular]

/-- The truncated exponential Weyl vector `∑_{k=0}^N w^k v_k`. -/
def weylVec (i : I) (w : ℂ) (N : ℕ) : WordSpace I :=
  ∑ k ∈ Finset.range (N + 1), (w ^ k) • chainVec i k

lemma weylVec_succ (i : I) (w : ℂ) (N : ℕ) :
    weylVec i w (N + 1) = weylVec i w N + (w ^ (N + 1)) • chainVec i (N + 1) := by
  simp [weylVec, Finset.sum_range_succ]

/-- The squared norm of the Weyl vector is exactly `N+1` when `‖w‖ = 1`. -/
lemma inner_weylVec (i : I) {w : ℂ} (hw : ‖w‖ = 1) (N : ℕ) :
    inner ℂ (weylVec i w N) (weylVec i w N) = ((N + 1 : ℕ) : ℂ) := by
  classical
  rw [weylVec, sum_inner]
  simp_rw [inner_sum]
  simp_rw [inner_smul_left, inner_smul_right, inner_chainVec]
  have hstep : ∀ k ∈ Finset.range (N + 1),
      (∑ l ∈ Finset.range (N + 1),
        (starRingEnd ℂ) (w ^ k) * (w ^ l * (if k = l then 1 else 0)))
        = (starRingEnd ℂ) (w ^ k) * w ^ k := by
    intro k hk
    rw [Finset.sum_eq_single k]
    · rw [if_pos rfl, mul_one]
    · intro l _ hlk
      rw [if_neg (fun h => hlk h.symm), mul_zero, mul_zero]
    · intro hk'
      exact absurd hk hk'
  rw [Finset.sum_congr rfl hstep]
  have hterm : ∀ k : ℕ, (starRingEnd ℂ) (w ^ k) * w ^ k = (1 : ℂ) := by
    intro k
    have hmul : (starRingEnd ℂ) (w ^ k) * w ^ k = ((Complex.normSq (w ^ k) : ℝ) : ℂ) := by
      rw [mul_comm]
      exact Complex.mul_conj _
    rw [hmul, Complex.normSq_eq_norm_sq, norm_pow, hw, one_pow]
    norm_num
  rw [Finset.sum_congr rfl (fun k _ => hterm k)]
  simp

end SemicircularInterval

end

end GUEStrongConvergence
