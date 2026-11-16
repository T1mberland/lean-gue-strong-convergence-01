/-
# GUE Wick pairings as an explicit finite pairing sum

This file gives an intrinsic finite pairing enumeration for a list of GUE entries and proves
that the recursive pairing sum `gueWick` is exactly the sum of the products of the actual
`gueCov` values over all pairings.

The local enumeration is a dependent inductive type `GUEPairing l`: a pairing of `e :: l` is a
choice of partner `l.get k` for `e` together with a pairing of `l.eraseIdx k`.  Its weight is the
product of `gueCov e (l.get k)` over the chosen pairs.  This is the partner-of-first
decomposition; it is an equivalent kernel-checked pairing enumeration to the upstream quotient
`FreeProbability.Orthogonal.OrdinaryPairing`, whose definition was inspected but whose import
chain has no compiled local oleans in this workspace (so importing it would require building the
pinned dependency).  No asymptotic statement is made.

The main theorem is

`gueWick l = ∑ p : GUEPairing l, weight l p`,

together with the specialization `∫ gueProd l = ∑ p, p.weight` via `integral_gueProd_eq_gueWick`.
-/
import GUEStrongConvergence.Probability.GUETraceWords

open MeasureTheory ProbabilityTheory Filter
open scoped RealInnerProductSpace Matrix ENNReal Topology

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

namespace GUEStrongConvergence

noncomputable section

universe u

variable {ι : Type u} [Fintype ι] [DecidableEq ι] {N : ℕ}

/-- A pairing of a list of GUE entries, decomposed by the partner of the head. -/
inductive GUEPairing : List (GUEEntry ι N) → Type u
  | nil : GUEPairing []
  | cons (e : GUEEntry ι N) (l : List (GUEEntry ι N)) (k : Fin l.length)
      (p : GUEPairing (l.eraseIdx k)) : GUEPairing (e :: l)

namespace GUEPairing

variable {l : List (GUEEntry ι N)}

/-- Weight of a pairing: product of the actual `gueCov` values over its pairs. -/
def weight : (l : List (GUEEntry ι N)) → GUEPairing l → ℂ
  | _, .nil => 1
  | _, .cons e l k p => gueCov e (l.get k) * weight (l.eraseIdx k) p

@[simp] lemma weight_nil :
    weight ([] : List (GUEEntry ι N)) (nil : GUEPairing []) = 1 := rfl

@[simp] lemma weight_cons (e : GUEEntry ι N) (l : List (GUEEntry ι N))
    (k : Fin l.length) (p : GUEPairing (l.eraseIdx k)) :
    weight (e :: l) (cons e l k p) = gueCov e (l.get k) * weight (l.eraseIdx k) p := rfl

/-- The head-partner decomposition is an equivalence with a sigma type. -/
def consEquiv (e : GUEEntry ι N) (l : List (GUEEntry ι N)) :
    GUEPairing (e :: l) ≃ (Σ k : Fin l.length, GUEPairing (l.eraseIdx k)) where
  toFun
    | .cons _ _ k p => ⟨k, p⟩
  invFun x := .cons e l x.1 x.2
  left_inv p := by cases p; rfl
  right_inv x := by rcases x with ⟨k, p⟩; rfl

/-- Finiteness of the recursive pairing type. -/
def fintype : (l : List (GUEEntry ι N)) → Fintype (GUEPairing l)
  | [] =>
    { elems := {GUEPairing.nil}
      complete := by intro p; cases p; simp }
  | e :: l =>
    letI : ∀ k : Fin l.length, Fintype (GUEPairing (l.eraseIdx k)) :=
      fun k => fintype (l.eraseIdx k)
    Fintype.ofEquiv (Σ k : Fin l.length, GUEPairing (l.eraseIdx k))
      (consEquiv e l).symm
termination_by l => l.length
decreasing_by
  simp_wf
  rw [List.length_eraseIdx, ite_eq_left k.isLt]
  omega

instance (l : List (GUEEntry ι N)) : Fintype (GUEPairing l) := fintype l

end GUEPairing

/-- Sum over a sigma type as an iterated sum. -/
lemma sum_sigma_univ {α : Type*} [Fintype α] {β : α → Type*}
    [∀ a, Fintype (β a)] {M : Type*} [AddCommMonoid M]
    (f : Sigma β → M) :
    (∑ x : Sigma β, f x) = ∑ a, ∑ b, f ⟨a, b⟩ := by
  simpa using (Finset.sum_sigma' (Finset.univ : Finset α)
    (fun a => (Finset.univ : Finset (β a))) (fun a b => f ⟨a, b⟩)).symm

/-- The recursive Wick pairing sum equals the explicit finite sum over pairings. -/
theorem gueWick_eq_sum_pairing (l : List (GUEEntry ι N)) :
    gueWick l = ∑ p : GUEPairing l, GUEPairing.weight l p := by
  suffices h : ∀ n : ℕ, ∀ l : List (GUEEntry ι N), l.length = n →
      gueWick l = ∑ p : GUEPairing l, GUEPairing.weight l p from
    h l.length l rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro l hl
    cases l with
    | nil =>
      have hsingle : ∀ p : GUEPairing ([] : List (GUEEntry ι N)), p = GUEPairing.nil := by
        intro p
        cases p
        rfl
      rw [Finset.sum_eq_single (GUEPairing.nil)]
      · rw [gueWick_nil]
        rfl
      · intro p _ hp
        exact (hp (hsingle p)).elim
      · intro h
        exact (h (Finset.mem_univ _)).elim
    | cons e l =>
      have hlen : l.length < n := by
        rw [List.length_cons] at hl
        omega
      rw [gueWick_cons]
      rw [Fintype.sum_equiv (GUEPairing.consEquiv e l) (fun p : GUEPairing (e :: l) => GUEPairing.weight (e :: l) p)
        (fun x : Sigma (fun k : Fin l.length => GUEPairing (l.eraseIdx k)) =>
          GUEPairing.weight (e :: l) (GUEPairing.cons e l x.1 x.2)) ?_]
      · rw [sum_sigma_univ]
        refine Finset.sum_congr rfl fun k _ => ?_
        simp only [GUEPairing.weight_cons]
        rw [← Finset.mul_sum]
        congr 1
        exact ih (l.eraseIdx k).length (by
          have h1 : (l.eraseIdx k).length ≤ l.length := by
            rw [List.length_eraseIdx]
            split <;> omega
          omega) (l.eraseIdx k) rfl
      · intro p
        cases p
        rfl

/-- Entry-product expectation as an explicit finite pairing sum. -/
theorem integral_gueProd_eq_sum_pairing (l : List (GUEEntry ι N)) :
    ∫ x : EuclideanSpace ℝ (GUECoord ι N), gueProd l x
        ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) =
      ∑ p : GUEPairing l, GUEPairing.weight l p := by
  rw [integral_gueProd_eq_gueWick, gueWick_eq_sum_pairing]

end

end GUEStrongConvergence
