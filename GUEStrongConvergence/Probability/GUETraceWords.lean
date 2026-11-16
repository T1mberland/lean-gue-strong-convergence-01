/-
# GUE trace words: finite index expansion and first parity results

This file starts the bridge from entry-wise GUE Wick theory to matrix-word moments.  For a
word `w : List ι` (labels of the matrices in the word) we define the ordered matrix product

`gueWord w x = ∏_{i ∈ w} G_i(x)`

and the normalized trace `gueNormTrace w x = N⁻¹ * tr (gueWord w x)`.  The matrix size `N`
is arbitrary; for `N = 0` the normalization is `(0 : ℂ)⁻¹ = 0` and all these traces vanish,
while the empty word has normalized trace `1` exactly when `N ≠ 0`.

The main finite expansion is the iterated index sum `guePathSum`, which satisfies

`(gueWord w x) a b = guePathSum w x a b`

and hence `tr (gueWord w x) = ∑ a, guePathSum w x a a`.  Every `guePathSum` is a polynomial in
the Gaussian coordinates, so it is integrable; consequently every trace word and every
normalized trace word is integrable.

On top of the entry Wick recursion of `GUEWick` we define the recursive pairing sum
`gueWick` and prove `∫ gueProd l = gueWick l`.  Odd-length entry products have zero
expectation (by strong induction on the length), and odd-length trace words have zero
expectation (proved via the sign symmetry of the centered Gaussian measure, independently of
any asymptotic statement).

No large-`N` asymptotic statement is made or assumed here.
-/
import GUEStrongConvergence.Probability.GUEWick

open MeasureTheory ProbabilityTheory Filter
open scoped RealInnerProductSpace Matrix ENNReal Topology

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace GUEStrongConvergence

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {N : ℕ}

/-- The ordered product of the GUE matrices indexed by the word `w`. -/
def gueWord (w : List ι) (x : EuclideanSpace ℝ (GUECoord ι N)) :
    Matrix (Fin N) (Fin N) ℂ :=
  (w.map (fun i => gueMatrix x i)).prod

/-- The normalized trace `N⁻¹ tr (gueWord w)`.  At `N = 0` the factor `N⁻¹` is `0`. -/
def gueNormTrace (w : List ι) (x : EuclideanSpace ℝ (GUECoord ι N)) : ℂ :=
  ((N : ℂ)⁻¹) * Matrix.trace (gueWord w x)

/-- Iterated index sum for an entry of a matrix word: it is the sum over all intermediate
matrix indices of the product of the corresponding GUE entries. -/
def guePathSum (w : List ι) (x : EuclideanSpace ℝ (GUECoord ι N)) :
    Fin N → Fin N → ℂ :=
  match w with
  | [] => fun a b => if a = b then 1 else 0
  | i :: w => fun a b => ∑ c : Fin N,
      gueMatrix x i a c * guePathSum w x c b

@[simp] lemma guePathSum_nil (x : EuclideanSpace ℝ (GUECoord ι N)) (a b : Fin N) :
    guePathSum [] x a b = if a = b then 1 else 0 := rfl

@[simp] lemma guePathSum_cons (i : ι) (w : List ι)
    (x : EuclideanSpace ℝ (GUECoord ι N)) (a b : Fin N) :
    guePathSum (i :: w) x a b =
      ∑ c : Fin N, gueMatrix x i a c * guePathSum w x c b := rfl

@[simp] lemma gueEntry_mk (i : ι) (a b : Fin N)
    (x : EuclideanSpace ℝ (GUECoord ι N)) :
    gueEntry (i, (a, b)) x = gueMatrix x i a b := rfl

/-- Entrywise expansion of a matrix word into the iterated index sum. -/
lemma gueWord_entry_pathSum (w : List ι)
    (x : EuclideanSpace ℝ (GUECoord ι N)) (a b : Fin N) :
    gueWord w x a b = guePathSum w x a b := by
  induction w generalizing a b with
  | nil =>
    simp [gueWord, guePathSum, Matrix.one_apply]
  | cons i w ih =>
    rw [gueWord, List.map_cons, List.prod_cons, Matrix.mul_apply]
    simp only [guePathSum_cons]
    refine Finset.sum_congr rfl fun c _ => ?_
    change gueMatrix x i a c * gueWord w x c b =
      gueMatrix x i a c * guePathSum w x c b
    rw [ih c b]

/-- Trace expansion into the iterated index sum. -/
lemma trace_gueWord_eq_sum_pathSum (w : List ι)
    (x : EuclideanSpace ℝ (GUECoord ι N)) :
    Matrix.trace (gueWord w x) = ∑ a : Fin N, guePathSum w x a a := by
  simp [Matrix.trace, Matrix.diag, gueWord_entry_pathSum]

/-! ### Integrability of path sums and trace words -/

/-- The Hölder triple `(2n, 2n, n)`. -/
lemma holder_two_mul {n : ℕ} (hn : 1 ≤ n) :
    ENNReal.HolderTriple ((2 * n : ℕ) : ℝ≥0∞) ((2 * n : ℕ) : ℝ≥0∞)
      (n : ℝ≥0∞) := by
  constructor
  have hn0 : n ≠ 0 := Nat.ne_of_gt hn
  have h2 : ((2 * n : ℕ) : ℝ≥0∞) = 2 * (n : ℝ≥0∞) := by norm_num
  rw [h2, ENNReal.mul_inv (Or.inl two_ne_zero) (Or.inr (by exact_mod_cast hn0))]
  rw [← add_mul, ENNReal.inv_two_add_inv_two, one_mul]

/-- A finite sum of `L^p` complex functions is in `L^p`. -/
lemma memLp_finset_sum {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {p : ℝ≥0∞} {β : Type*} {s : Finset β} {f : β → α → ℂ}
    (h : ∀ i ∈ s, MemLp (f i) p μ) :
    MemLp (fun x : α => ∑ i ∈ s, f i x) p μ := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    simp_rw [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self _ _)).add
      (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))

/-- Every path sum is in `L^n` for every `n ≥ 1`. -/
lemma memLp_guePathSum (w : List ι) :
    ∀ (n : ℕ) (_hn : 1 ≤ n) (a b : Fin N),
      MemLp (fun x : EuclideanSpace ℝ (GUECoord ι N) => guePathSum w x a b)
        (n : ℝ≥0∞) (stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) := by
  induction w with
  | nil =>
    intro n _hn a b
    simpa [guePathSum] using
      memLp_const (if a = b then (1 : ℂ) else 0)
  | cons i w ih =>
    intro n hn a b
    letI : ENNReal.HolderTriple ((2 * n : ℕ) : ℝ≥0∞)
        ((2 * n : ℕ) : ℝ≥0∞) (n : ℝ≥0∞) := holder_two_mul hn
    have hterm : ∀ c : Fin N,
        MemLp (fun x : EuclideanSpace ℝ (GUECoord ι N) =>
          gueMatrix x i a c * guePathSum w x c b) (n : ℝ≥0∞)
          (stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) := by
      intro c
      have hentry : MemLp (fun x : EuclideanSpace ℝ (GUECoord ι N) =>
          gueMatrix x i a c) ((2 * n : ℕ) : ℝ≥0∞)
          (stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) := by
        convert memLp_gueEntry (ι := ι) (N := N) (i, (a, c)) (2 * n) (by omega) using 1
        ext x
        rw [gueEntry_mk]
      have hpath : MemLp (fun x : EuclideanSpace ℝ (GUECoord ι N) =>
          guePathSum w x c b) ((2 * n : ℕ) : ℝ≥0∞)
          (stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) :=
        ih (2 * n) (by omega) c b
      exact hentry.mul hpath
    simpa [guePathSum] using
      (memLp_finset_sum (s := Finset.univ) (fun c _ => hterm c))

/-- Every path sum is integrable. -/
lemma integrable_guePathSum (w : List ι) (a b : Fin N) :
    Integrable (fun x : EuclideanSpace ℝ (GUECoord ι N) => guePathSum w x a b)
      (stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) :=
  memLp_one_iff_integrable.mp (by simpa using memLp_guePathSum w 1 le_rfl a b)

/-- Every trace word is integrable. -/
theorem integrable_trace_gueWord (w : List ι) :
    Integrable (fun x : EuclideanSpace ℝ (GUECoord ι N) => Matrix.trace (gueWord w x))
      (stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) := by
  have hfun : (fun x : EuclideanSpace ℝ (GUECoord ι N) => Matrix.trace (gueWord w x)) =
      fun x => ∑ a : Fin N, guePathSum w x a a := by
    funext x
    rw [trace_gueWord_eq_sum_pathSum]
  rw [hfun]
  exact integrable_finsetSum Finset.univ
    (fun a _ => integrable_guePathSum w a a)

/-- Every normalized trace word is integrable. -/
theorem integrable_gueNormTrace (w : List ι) :
    Integrable (fun x : EuclideanSpace ℝ (GUECoord ι N) => gueNormTrace w x)
      (stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) :=
  (integrable_trace_gueWord w).const_mul ((N : ℂ)⁻¹)

/-! ### Recursive Wick pairing sum for entry lists -/

/-- Recursive Gaussian pairing sum for a list of GUE entries. -/
def gueWick : List (GUEEntry ι N) → ℂ
  | [] => 1
  | e :: l => ∑ k : Fin l.length,
      gueCov e (l.get k) * gueWick (l.eraseIdx k)
termination_by l => l.length
decreasing_by
  simp_wf
  rw [List.length_eraseIdx, ite_eq_left k.isLt]
  omega

@[simp] lemma gueWick_nil : gueWick ([] : List (GUEEntry ι N)) = 1 := by
  rw [gueWick.eq_1]

lemma gueWick_cons (e : GUEEntry ι N) (l : List (GUEEntry ι N)) :
    gueWick (e :: l) = ∑ k : Fin l.length,
      gueCov e (l.get k) * gueWick (l.eraseIdx k) := by
  rw [gueWick.eq_2]

/-- The actual entry-product expectation equals the recursive Wick pairing sum. -/
theorem integral_gueProd_eq_gueWick (l : List (GUEEntry ι N)) :
    ∫ x : EuclideanSpace ℝ (GUECoord ι N), gueProd l x
        ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) = gueWick l := by
  suffices h : ∀ n : ℕ, ∀ l : List (GUEEntry ι N), l.length = n →
      (∫ x : EuclideanSpace ℝ (GUECoord ι N), gueProd l x
        ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))) = gueWick l from
    h l.length l rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro l hl
    cases l with
    | nil => simp [gueProd]
    | cons e l =>
      have hlen : l.length < n := by
        rw [List.length_cons] at hl
        omega
      have hstep : (∫ x : EuclideanSpace ℝ (GUECoord ι N), gueProd (e :: l) x
          ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))) =
          ∫ x : EuclideanSpace ℝ (GUECoord ι N), gueEntry e x * gueProd l x
            ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) := by
        refine integral_congr_ae (ae_of_all _ fun x => ?_)
        simp [gueProd]
      rw [hstep, integral_gueEntry_mul_gueProd, gueWick_cons]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [ih (l.eraseIdx k).length ?_ (l.eraseIdx k) rfl]
      have h1 : (l.eraseIdx k).length ≤ l.length := by
        rw [List.length_eraseIdx]
        split <;> omega
      omega

/-- Odd-length entry products have zero expectation. -/
lemma integral_gueProd_odd_zero (l : List (GUEEntry ι N)) (hodd : Odd l.length) :
    ∫ x : EuclideanSpace ℝ (GUECoord ι N), gueProd l x
        ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) = 0 := by
  rw [integral_gueProd_eq_gueWick]
  suffices h : ∀ n : ℕ, ∀ l : List (GUEEntry ι N), l.length = n → Odd n →
      gueWick l = 0 from h l.length l rfl hodd
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro l hl hnodd
    cases l with
    | nil =>
      have hn0 : n = 0 := by simpa using hl.symm
      rw [hn0] at hnodd
      exact (Nat.not_odd_zero hnodd).elim
    | cons e l =>
      have hlen : l.length < n := by
        rw [List.length_cons] at hl
        omega
      rw [gueWick_cons]
      refine Finset.sum_eq_zero fun k _ => ?_
      have hle : l.length + 1 = n := by
        rw [List.length_cons] at hl
        exact hl
      have heven : Even l.length := by
        have hnodd' : Odd (l.length + 1) := by rwa [← hle] at hnodd
        rcases hnodd' with ⟨m, hm⟩
        exact ⟨m, by omega⟩
      have hkodd : Odd (l.eraseIdx k).length := by
        rw [List.length_eraseIdx, ite_eq_left k.isLt]
        have hkpos : 0 < l.length := by have := k.isLt; omega
        rcases heven with ⟨m, hm⟩
        have hmpos : 0 < m := by omega
        refine ⟨m - 1, ?_⟩
        omega
      have hklt : (l.eraseIdx k).length < n := by
        have h1 : (l.eraseIdx k).length ≤ l.length := by
          rw [List.length_eraseIdx]
          split <;> omega
        omega
      rw [ih (l.eraseIdx k).length hklt (l.eraseIdx k) rfl hkodd, mul_zero]

/-! ### Empty word and odd trace words -/

@[simp] lemma gueMatrix_neg (i : ι) (x : EuclideanSpace ℝ (GUECoord ι N)) :
    gueMatrix (-x) i = -gueMatrix x i := by
  ext a b
  simp [gueMatrix, gueUnscaled]
  ring

/-- A word of odd length is an odd function of the Gaussian coordinates. -/
lemma gueWord_neg (w : List ι) (x : EuclideanSpace ℝ (GUECoord ι N)) :
    gueWord w (-x) = ((-1 : ℂ) ^ w.length) • gueWord w x := by
  induction w with
  | nil => simp [gueWord]
  | cons i w ih =>
    change gueMatrix (-x) i * gueWord w (-x) =
      ((-1 : ℂ) ^ (w.length + 1)) • (gueMatrix x i * gueWord w x)
    rw [ih, gueMatrix_neg, Matrix.neg_mul, Matrix.mul_smul]
    rw [show ((-1 : ℂ) ^ (w.length + 1)) = -((-1 : ℂ) ^ w.length) by
      rw [pow_succ]
      ring]
    rw [neg_smul]

lemma trace_gueWord_neg (w : List ι) (x : EuclideanSpace ℝ (GUECoord ι N)) :
    Matrix.trace (gueWord w (-x)) =
      ((-1 : ℂ) ^ w.length) * Matrix.trace (gueWord w x) := by
  rw [gueWord_neg, Matrix.trace_smul, smul_eq_mul]

lemma gueNormTrace_neg (w : List ι) (x : EuclideanSpace ℝ (GUECoord ι N)) :
    gueNormTrace w (-x) = ((-1 : ℂ) ^ w.length) * gueNormTrace w x := by
  simp only [gueNormTrace, trace_gueWord_neg]
  ring

@[simp] lemma gueWord_nil (x : EuclideanSpace ℝ (GUECoord ι N)) :
    gueWord [] x = 1 := rfl

lemma trace_gueWord_nil (x : EuclideanSpace ℝ (GUECoord ι N)) :
    Matrix.trace (gueWord [] x) = (N : ℂ) := by
  simp [gueWord, Matrix.trace_one]

/-- The empty word has normalized trace `1` for positive `N` and `0` for `N = 0`. -/
lemma gueNormTrace_nil (x : EuclideanSpace ℝ (GUECoord ι N)) :
    gueNormTrace [] x = if N = 0 then 0 else 1 := by
  simp only [gueNormTrace, gueWord, List.map_nil, List.prod_nil, Matrix.trace_one]
  by_cases h : N = 0 <;> simp [h]

/-- `stdGaussian` on a Euclidean space is invariant under `x ↦ -x`. -/
lemma stdGaussian_isNegInvariant :
    (stdGaussian (EuclideanSpace ℝ (GUECoord ι N))).IsNegInvariant := by
  refine ⟨?_⟩
  have h := stdGaussian_map (LinearIsometryEquiv.neg ℝ
    (E := EuclideanSpace ℝ (GUECoord ι N)))
  simpa [Measure.neg] using h

/-- Expectation expansion of a trace word into the iterated index sums. -/
theorem integral_trace_gueWord_eq_sum_pathSum (w : List ι) :
    ∫ x : EuclideanSpace ℝ (GUECoord ι N), Matrix.trace (gueWord w x)
        ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) =
      ∑ a : Fin N, ∫ x : EuclideanSpace ℝ (GUECoord ι N), guePathSum w x a a
        ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) := by
  have hfun : (fun x : EuclideanSpace ℝ (GUECoord ι N) => Matrix.trace (gueWord w x)) =
      fun x => ∑ a : Fin N, guePathSum w x a a := by
    funext x
    rw [trace_gueWord_eq_sum_pathSum]
  rw [hfun, integral_finsetSum]
  intro a _
  exact integrable_guePathSum w a a

/-- Expectation expansion of a normalized trace word. -/
theorem integral_gueNormTrace_eq_sum_pathSum (w : List ι) :
    ∫ x : EuclideanSpace ℝ (GUECoord ι N), gueNormTrace w x
        ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) =
      ((N : ℂ)⁻¹) * ∑ a : Fin N,
        ∫ x : EuclideanSpace ℝ (GUECoord ι N), guePathSum w x a a
          ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) := by
  simp only [gueNormTrace]
  rw [integral_const_mul, integral_trace_gueWord_eq_sum_pathSum]

/-- Odd-length trace words have zero expectation. -/
theorem integral_trace_gueWord_odd_zero (w : List ι) (hodd : Odd w.length) :
    ∫ x : EuclideanSpace ℝ (GUECoord ι N), Matrix.trace (gueWord w x)
        ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) = 0 := by
  letI := stdGaussian_isNegInvariant (ι := ι) (N := N)
  have hodd_fun : ∀ x : EuclideanSpace ℝ (GUECoord ι N),
      Matrix.trace (gueWord w (-x)) = -Matrix.trace (gueWord w x) := by
    intro x
    rw [trace_gueWord_neg, Odd.neg_one_pow hodd]
    ring
  have hmap := integral_neg_eq_self
    (fun x : EuclideanSpace ℝ (GUECoord ι N) => Matrix.trace (gueWord w x))
    (stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))
  have hneg : (∫ x : EuclideanSpace ℝ (GUECoord ι N),
      Matrix.trace (gueWord w (-x))
        ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))) =
      -(∫ x : EuclideanSpace ℝ (GUECoord ι N), Matrix.trace (gueWord w x)
        ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))) := by
    simp_rw [hodd_fun]
    rw [integral_neg]
  rw [hneg] at hmap
  have htwo : (2 : ℂ) * (∫ x : EuclideanSpace ℝ (GUECoord ι N),
      Matrix.trace (gueWord w x)
        ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))) = 0 := by
    calc (2 : ℂ) * (∫ x : EuclideanSpace ℝ (GUECoord ι N),
          Matrix.trace (gueWord w x)
            ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N))))
        = (∫ x : EuclideanSpace ℝ (GUECoord ι N), Matrix.trace (gueWord w x)
            ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))) +
          (∫ x : EuclideanSpace ℝ (GUECoord ι N), Matrix.trace (gueWord w x)
            ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))) := by ring
      _ = -(∫ x : EuclideanSpace ℝ (GUECoord ι N), Matrix.trace (gueWord w x)
            ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))) +
          (∫ x : EuclideanSpace ℝ (GUECoord ι N), Matrix.trace (gueWord w x)
            ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))) := by
        nth_rewrite 1 [← hmap]
        ring
      _ = 0 := by ring
  exact (mul_eq_zero.mp htwo).resolve_left (by norm_num)

/-- Odd-length normalized trace words have zero expectation. -/
theorem integral_gueNormTrace_odd_zero (w : List ι) (hodd : Odd w.length) :
    ∫ x : EuclideanSpace ℝ (GUECoord ι N), gueNormTrace w x
        ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) = 0 := by
  simp only [gueNormTrace]
  rw [integral_const_mul, integral_trace_gueWord_odd_zero w hodd, mul_zero]

end

end GUEStrongConvergence
