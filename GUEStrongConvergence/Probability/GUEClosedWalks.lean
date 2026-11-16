/-
# GUE closed walks: one-shot path sums

This file converts the recursive iterated index sum `guePathSum` of `GUETraceWords` into an
explicit finite sum over all assignments of intermediate matrix indices.  For a word `w` of
length `n` the encoding is:

* start index `a : Fin N`;
* destinations `d : Fin n → Fin N`, where `d k` is the vertex after the `k`-th matrix;
* terminal index `guePathLast a w d` (equal to `a` for the empty word, otherwise the last
  destination);
* entry list `guePathEntries w a d` of length `n`, with the `k`-th entry carrying the edge
  `(start of step k, d k)`.

The resulting one-shot sum is `guePathSumOneShot w a b x`, and we prove

`guePathSum w x a b = guePathSumOneShot w a b x`.

Summing over `a = b` gives the closed-walk expansion of the trace, and summing over all closed
walks gives the normalized trace expansion.  Empty words and `N = 0` are included; no
large-`N` asymptotic statement is made.
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

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {N : ℕ}

/-- Terminal vertex of a path with fixed start `a` and destinations `d`. -/
def guePathLast (a : Fin N) : (w : List ι) → (Fin w.length → Fin N) → Fin N
  | [], _ => a
  | _ :: w, d => guePathLast (d 0) w (Fin.tail d)

/-- Entry list of a path with fixed start `a` and destinations `d`. -/
def guePathEntries (a : Fin N) : (w : List ι) → (Fin w.length → Fin N) →
    List (GUEEntry ι N)
  | [], _ => []
  | i :: w, d => (i, (a, d 0)) :: guePathEntries (d 0) w (Fin.tail d)

@[simp] lemma guePathLast_nil (a : Fin N) (d : Fin 0 → Fin N) :
    guePathLast (ι := ι) a ([] : List ι) d = a := rfl

@[simp] lemma guePathLast_cons (a : Fin N) (i : ι) (w : List ι)
    (d : Fin (w.length + 1) → Fin N) :
    guePathLast a (i :: w) d = guePathLast (d 0) w (Fin.tail d) := rfl

@[simp] lemma guePathEntries_nil (a : Fin N) (d : Fin 0 → Fin N) :
    guePathEntries (ι := ι) a ([] : List ι) d = [] := rfl

@[simp] lemma guePathEntries_cons (a : Fin N) (i : ι) (w : List ι)
    (d : Fin (w.length + 1) → Fin N) :
    guePathEntries a (i :: w) d =
      (i, (a, d 0)) :: guePathEntries (d 0) w (Fin.tail d) := rfl

/-- One-shot finite sum over all assignments of intermediate indices. -/
def guePathSumOneShot (w : List ι) (a b : Fin N)
    (x : EuclideanSpace ℝ (GUECoord ι N)) : ℂ :=
  ∑ d : Fin w.length → Fin N,
    if guePathLast a w d = b then gueProd (guePathEntries a w d) x else 0

/-- Sum over all functions `Fin (n+1) → α` split by first value and tail. -/
lemma sum_fin_cons (n : ℕ) {α M : Type*} [Fintype α] [AddCommMonoid M]
    (F : (Fin (n + 1) → α) → M) :
    (∑ d : Fin (n + 1) → α, F d) =
      ∑ c : α, ∑ e : Fin n → α, F (Fin.cons c e) := by
  have h1 : (∑ d : Fin (n + 1) → α, F d) =
      ∑ p : α × (Fin n → α), F (Fin.cons p.1 p.2) := by
    refine Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (n + 1) => α)).symm F
      (fun p : α × (Fin n → α) => F (Fin.cons p.1 p.2)) ?_
    intro d
    rw [Fin.consEquiv_symm_apply, Fin.cons_self_tail]
  rw [h1]
  simpa using (Finset.sum_product (Finset.univ : Finset α) (Finset.univ : Finset (Fin n → α))
    (fun p : α × (Fin n → α) => F (Fin.cons p.1 p.2)))

/-- The recursive iterated index sum equals the one-shot sum over all intermediate index
assignments. -/
theorem guePathSum_eq_oneShot (w : List ι) (a b : Fin N)
    (x : EuclideanSpace ℝ (GUECoord ι N)) :
    guePathSum w x a b = guePathSumOneShot w a b x := by
  induction w generalizing a b with
  | nil =>
    simp [guePathSumOneShot, guePathLast, guePathEntries, gueProd]
  | cons i w ih =>
    calc
      guePathSum (i :: w) x a b =
          ∑ c : Fin N, gueMatrix x i a c * guePathSum w x c b := by
        rw [guePathSum_cons]
      _ = ∑ c : Fin N, ∑ e : Fin w.length → Fin N,
            if guePathLast c w e = b then
              gueMatrix x i a c * gueProd (guePathEntries c w e) x else 0 := by
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [ih c b, guePathSumOneShot, Finset.mul_sum]
        simp only [mul_ite, mul_zero]
      _ = guePathSumOneShot (i :: w) a b x := by
        rw [guePathSumOneShot]
        symm
        exact (sum_fin_cons w.length (fun d : Fin (w.length + 1) → Fin N =>
          if guePathLast a (i :: w) d = b then
            gueProd (guePathEntries a (i :: w) d) x else 0))

/-- Closed-walk sum: sum over all starts and destinations whose terminal vertex is the start. -/
def gueClosedWalkSum (w : List ι) (x : EuclideanSpace ℝ (GUECoord ι N)) : ℂ :=
  ∑ a : Fin N, guePathSumOneShot w a a x

/-- Finite sum of the recursive Wick values over all closed walks. -/
def gueWickClosedWalk (w : List ι) : ℂ :=
  ∑ a : Fin N, ∑ d : Fin w.length → Fin N,
    if guePathLast a w d = a then gueWick (guePathEntries a w d) else 0

/-- Entrywise one-shot expansion of a matrix word. -/
theorem gueWord_entry_oneShot (w : List ι)
    (x : EuclideanSpace ℝ (GUECoord ι N)) (a b : Fin N) :
    gueWord w x a b = guePathSumOneShot w a b x := by
  rw [gueWord_entry_pathSum, guePathSum_eq_oneShot]

/-- Trace closed-walk expansion. -/
theorem trace_gueWord_eq_closedWalkSum (w : List ι)
    (x : EuclideanSpace ℝ (GUECoord ι N)) :
    Matrix.trace (gueWord w x) = gueClosedWalkSum w x := by
  rw [trace_gueWord_eq_sum_pathSum]
  simp only [gueClosedWalkSum]
  refine Finset.sum_congr rfl fun a _ => ?_
  exact guePathSum_eq_oneShot w a a x

/-- Normalized trace closed-walk expansion. -/
theorem gueNormTrace_eq_closedWalkSum (w : List ι)
    (x : EuclideanSpace ℝ (GUECoord ι N)) :
    gueNormTrace w x = ((N : ℂ)⁻¹) * gueClosedWalkSum w x := by
  simp [gueNormTrace, trace_gueWord_eq_closedWalkSum]

/-- Expectation of a trace word as the finite sum of Wick values over closed walks. -/
theorem integral_trace_gueWord_eq_wick_sum (w : List ι) :
    ∫ x : EuclideanSpace ℝ (GUECoord ι N), Matrix.trace (gueWord w x)
        ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) = gueWickClosedWalk (N := N) w := by
  simp_rw [trace_gueWord_eq_closedWalkSum]
  simp only [gueClosedWalkSum]
  rw [integral_finsetSum]
  · refine Finset.sum_congr rfl fun a _ => ?_
    simp only [guePathSumOneShot]
    rw [integral_finsetSum]
    · refine Finset.sum_congr rfl fun d _ => ?_
      by_cases h : guePathLast a w d = a
      · simp_rw [ite_eq_left h]
        rw [integral_gueProd_eq_gueWick]
      · simp_rw [ite_eq_right h]
        simp
    · intro d _
      by_cases h : guePathLast a w d = a
      · simpa [h] using integrable_gueProd (guePathEntries a w d)
      · simpa [h] using integrable_zero
          (EuclideanSpace ℝ (GUECoord ι N)) ℂ
          (stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))
  · intro a _
    refine integrable_finsetSum Finset.univ fun d _ => ?_
    by_cases h : guePathLast a w d = a
    · simpa [h] using integrable_gueProd (guePathEntries a w d)
    · simpa [h] using integrable_zero
        (EuclideanSpace ℝ (GUECoord ι N)) ℂ
        (stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))

/-- Expectation of a normalized trace word as `N⁻¹` times the finite Wick closed-walk sum. -/
theorem integral_gueNormTrace_eq_wick_sum (w : List ι) :
    ∫ x : EuclideanSpace ℝ (GUECoord ι N), gueNormTrace w x
        ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) =
      ((N : ℂ)⁻¹) * gueWickClosedWalk (N := N) w := by
  simp only [gueNormTrace]
  rw [integral_const_mul, integral_trace_gueWord_eq_wick_sum]

/-- The closed-walk sum of the empty word is `N` (zero at `N = 0`). -/
@[simp] lemma gueClosedWalkSum_nil (x : EuclideanSpace ℝ (GUECoord ι N)) :
    gueClosedWalkSum ([] : List ι) x = (N : ℂ) := by
  simp [gueClosedWalkSum, guePathSumOneShot, guePathLast, guePathEntries, gueProd]

/-- The Wick closed-walk sum of the empty word is `N` (zero at `N = 0`). -/
@[simp] lemma gueWickClosedWalk_nil :
    gueWickClosedWalk (N := N) ([] : List ι) = (N : ℂ) := by
  simp [gueWickClosedWalk, guePathLast, guePathEntries]

/-- Normalized empty-word expectation: `0` at `N = 0` and `1` for positive `N`. -/
theorem integral_gueNormTrace_nil :
    ∫ x : EuclideanSpace ℝ (GUECoord ι N), gueNormTrace ([] : List ι) x
        ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) = if N = 0 then 0 else 1 := by
  rw [integral_gueNormTrace_eq_wick_sum, gueWickClosedWalk_nil]
  by_cases h : N = 0 <;> simp [h]

end

end GUEStrongConvergence
