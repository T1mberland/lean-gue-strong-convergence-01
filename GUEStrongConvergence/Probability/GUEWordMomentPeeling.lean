/-
# Peeling a doubled GUE matrix out of a trace word

This module proves the trace-preserving peeling identity

`E[tr (G_i G_i · W)] = E[tr W]`   whenever the label `i` does not occur in the word of `W`,

together with its rotated form `E[tr (G_i · W · G_i)] = E[tr W]`.  Iterating the peeling identity
gives the exact normalized expectation `1` for two infinite families of words of every length:

* the *doubled* words `i₀ i₀ i₁ i₁ ⋯ i_{m-1} i_{m-1}`, and
* the *nested* words `i₀ i₁ ⋯ i_{m-1} i_{m-1} ⋯ i₁ i₀`,

for pairwise distinct labels.

The proof of the peeling identity is at the matrix level: expanding `tr (G G W)` as a triple index
sum and using the covariance of two entries of the same GUE matrix (the label `i` occurs exactly
twice, so the two-entry Wick factorization forces the two `i`-entries to be contracted with each
other), one obtains `E[tr (G G W)] = E[tr W]` for `N > 0`.

No general-`k` Catalan limit is claimed: the results here are exact identities for the structured
families and their `Tendsto` corollaries.
-/
import GUEStrongConvergence.Probability.GUEWordMomentLimit

open MeasureTheory ProbabilityTheory Filter
open scoped RealInnerProductSpace Matrix ENNReal Topology

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

namespace GUEStrongConvergence

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {N : ℕ}

/-! ### Labels of path entries -/

/-- The labels of the entry list of a path are exactly the letters of the word. -/
lemma map_fst_guePathEntries (w : List ι) (a : Fin N) (d : Fin w.length → Fin N) :
    (guePathEntries a w d).map (fun e => e.1) = w := by
  induction w generalizing a with
  | nil => simp
  | cons i w ih =>
    simp only [guePathEntries_cons, List.map_cons]
    rw [ih (d 0) (Fin.tail d)]

/-- If the label `i` does not occur in the word, no entry of the path carries label `i`. -/
lemma guePathEntries_label_ne {i : ι} {w : List ι} (hi : i ∉ w)
    (a : Fin N) (d : Fin w.length → Fin N) :
    ∀ e ∈ guePathEntries a w d, e.1 ≠ i := by
  intro e he h
  have hmem : e.1 ∈ (guePathEntries a w d).map (fun e => e.1) :=
    List.mem_map_of_mem (f := fun e => e.1) he
  rw [map_fst_guePathEntries] at hmem
  exact hi (h ▸ hmem)

/-- Expectation of a path sum as a finite sum of Wick values over all intermediate indices. -/
lemma integral_guePathSum_eq_sum_wick (w : List ι) (a b : Fin N) :
    ∫ x : EuclideanSpace ℝ (GUECoord ι N), guePathSum w x a b
        ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) =
      ∑ d : Fin w.length → Fin N,
        if guePathLast a w d = b then gueWick (guePathEntries a w d) else 0 := by
  simp only [guePathSum_eq_oneShot, guePathSumOneShot]
  rw [integral_finsetSum]
  · refine Finset.sum_congr rfl fun d _ => ?_
    by_cases h : guePathLast a w d = b
    · simp only [h, ite_true]
      rw [integral_gueProd_eq_gueWick]
    · simp [h]
  · intro d _
    by_cases h : guePathLast a w d = b
    · simp only [h, ite_true]
      exact integrable_gueProd (guePathEntries a w d)
    · simp [h]

/-! ### Integrability of the triple products -/

/-- The product of two entries of one matrix with an entry of another word is integrable. -/
lemma integrable_gueEntry_mul_gueEntry_mul_guePathSum (i : ι) (a b c : Fin N) (B : List ι) :
    Integrable (fun x : EuclideanSpace ℝ (GUECoord ι N) =>
        gueEntry (i, (a, b)) x * gueEntry (i, (b, c)) x * guePathSum B x c a)
      (stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) := by
  letI : ENNReal.HolderTriple (2 : ℝ≥0∞) (2 : ℝ≥0∞) 1 := by
    simpa using holder_two_mul (n := 1) le_rfl
  letI : ENNReal.HolderTriple (4 : ℝ≥0∞) (4 : ℝ≥0∞) 2 := by
    simpa using holder_two_mul (n := 2) (by norm_num)
  have h0 : MemLp (fun x : EuclideanSpace ℝ (GUECoord ι N) => gueEntry (i, (a, b)) x)
      (4 : ℝ≥0∞) (stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) :=
    memLp_gueEntry (i, (a, b)) 4 (by norm_num)
  have h1 : MemLp (fun x : EuclideanSpace ℝ (GUECoord ι N) => gueEntry (i, (b, c)) x)
      (4 : ℝ≥0∞) (stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) :=
    memLp_gueEntry (i, (b, c)) 4 (by norm_num)
  have h2 : MemLp (fun x : EuclideanSpace ℝ (GUECoord ι N) => guePathSum B x c a)
      (2 : ℝ≥0∞) (stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) := by
    simpa using memLp_guePathSum B 2 (by norm_num) c a
  have h01 : MemLp (fun x : EuclideanSpace ℝ (GUECoord ι N) =>
      gueEntry (i, (a, b)) x * gueEntry (i, (b, c)) x)
      (2 : ℝ≥0∞) (stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) := h0.mul h1
  have h012 : MemLp (fun x : EuclideanSpace ℝ (GUECoord ι N) =>
      gueEntry (i, (a, b)) x * gueEntry (i, (b, c)) x * guePathSum B x c a)
      (1 : ℝ≥0∞) (stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) := h01.mul h2
  exact h012.integrable (by norm_num)

/-! ### The peeling identity -/

/-- The product of a word splits over concatenation. -/
lemma gueWord_append (u v : List ι) (x : EuclideanSpace ℝ (GUECoord ι N)) :
    gueWord (u ++ v) x = gueWord u x * gueWord v x := by
  simp [gueWord, List.map_append, List.prod_append]

/-- Trace expansion of a word beginning with two equal letters. -/
lemma trace_gueWord_cons_cons (i : ι) (B : List ι)
    (x : EuclideanSpace ℝ (GUECoord ι N)) :
    Matrix.trace (gueWord ([i, i] ++ B) x) =
      ∑ a : Fin N, ∑ b : Fin N, ∑ c : Fin N,
        gueEntry (i, (a, c)) x * gueEntry (i, (c, b)) x * (gueWord B x) b a := by
  have hw : gueWord ([i, i] ++ B) x = gueMatrix x i * gueMatrix x i * gueWord B x := by
    rw [gueWord_append]
    simp [gueWord]
  rw [hw, Matrix.trace]
  simp only [Matrix.diag, Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  refine Finset.sum_congr rfl fun c _ => ?_
  simp [gueEntry, mul_assoc]

/-- The covariance of two entries of the same matrix, in the index pattern of the trace
expansion. -/
lemma gueCov_entry_entry (i : ι) (a b c : Fin N) :
    gueCov (i, (a, c)) (i, (c, b)) = if a = b then ((N : ℂ)⁻¹) else 0 := by
  rw [gueCov]
  by_cases h : a = b <;> simp [h]

/-- **Two-entry Wick factorization for a word**: if the label `i` occurs nowhere in `B`, then the
expectation of `G_{ab} G_{bc} (gueWord B)_{ca}` factorizes into the covariance of the two `G_i`
entries times the expectation of `(gueWord B)_{ca}`. -/
lemma integral_gueEntry_mul_gueEntry_mul_gueWord (i : ι) (a b c : Fin N) (B : List ι)
    (hiB : i ∉ B) :
    ∫ x : EuclideanSpace ℝ (GUECoord ι N),
        gueEntry (i, (a, b)) x * gueEntry (i, (b, c)) x * (gueWord B x) c a
        ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) =
      gueCov (i, (a, b)) (i, (b, c)) *
        ∫ x : EuclideanSpace ℝ (GUECoord ι N), (gueWord B x) c a
          ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) := by
  have hfun : (fun x : EuclideanSpace ℝ (GUECoord ι N) =>
        gueEntry (i, (a, b)) x * gueEntry (i, (b, c)) x * (gueWord B x) c a) =
      fun x => gueEntry (i, (a, b)) x * gueEntry (i, (b, c)) x * guePathSum B x c a := by
    funext x
    rw [gueWord_entry_pathSum]
  rw [hfun]
  simp only [guePathSum_eq_oneShot, guePathSumOneShot]
  have hpt : (fun x : EuclideanSpace ℝ (GUECoord ι N) =>
        gueEntry (i, (a, b)) x * gueEntry (i, (b, c)) x *
          (∑ d : Fin B.length → Fin N,
            if guePathLast c B d = a then gueProd (guePathEntries c B d) x else 0)) =
      fun x => ∑ d : Fin B.length → Fin N,
        if guePathLast c B d = a then
          gueProd ((i, (a, b)) :: (i, (b, c)) :: guePathEntries c B d) x else 0 := by
    funext x
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun d _ => ?_
    by_cases hc : guePathLast c B d = a
    · simp only [hc, ite_true]
      rw [gueProd_cons, gueProd_cons]
      ring
    · simp [hc]
  rw [hpt]
  rw [integral_finsetSum]
  · have hR : (∫ x : EuclideanSpace ℝ (GUECoord ι N), (gueWord B x) c a
        ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))) =
        ∑ d : Fin B.length → Fin N,
          if guePathLast c B d = a then gueWick (guePathEntries c B d) else 0 := by
      rw [show (fun x : EuclideanSpace ℝ (GUECoord ι N) => (gueWord B x) c a) =
          fun x => guePathSum B x c a from by
        funext x
        rw [gueWord_entry_pathSum]]
      exact integral_guePathSum_eq_sum_wick B c a
    rw [hR, Finset.mul_sum]
    refine Finset.sum_congr rfl fun d _ => ?_
    by_cases hc : guePathLast c B d = a
    · simp only [hc, ite_true]
      rw [integral_gueProd_eq_gueWick,
        gueWick_cons_cons_of_label_ne (i := i)
          (e := (i, (a, b))) (f := (i, (b, c))) (chain := guePathEntries c B d)
          rfl rfl (fun j => guePathEntries_label_ne hiB c d _ (List.get_mem _ _))]
    · simp [hc]
  · intro d _
    by_cases hc : guePathLast c B d = a
    · simp only [hc, ite_true]
      exact integrable_gueProd _
    · simp [hc]

/-- Trace of a word as the sum of the expectations of its diagonal entries. -/
lemma integral_trace_gueWord_eq_sum_diag (B : List ι) :
    ∫ x : EuclideanSpace ℝ (GUECoord ι N), Matrix.trace (gueWord B x)
        ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) =
      ∑ a : Fin N, ∫ x : EuclideanSpace ℝ (GUECoord ι N), (gueWord B x) a a
        ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) := by
  simp only [Matrix.trace, Matrix.diag]
  rw [integral_finsetSum]
  intro a _
  exact (integrable_guePathSum B a a).congr
    (ae_of_all _ fun x => (gueWord_entry_pathSum B x a a).symm)

/-- Integrating a triple finite sum of integrable functions. -/
lemma integral_finset_sum_three
    {F : Fin N → Fin N → Fin N → EuclideanSpace ℝ (GUECoord ι N) → ℂ}
    (h : ∀ a b c, Integrable (F a b c) (stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))) :
    ∫ x : EuclideanSpace ℝ (GUECoord ι N),
        ∑ a : Fin N, ∑ b : Fin N, ∑ c : Fin N, F a b c x
        ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) =
      ∑ a : Fin N, ∑ b : Fin N, ∑ c : Fin N,
        ∫ x : EuclideanSpace ℝ (GUECoord ι N), F a b c x
          ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) := by
  rw [integral_finsetSum]
  · refine Finset.sum_congr rfl fun a _ => ?_
    rw [integral_finsetSum]
    · refine Finset.sum_congr rfl fun b _ => ?_
      rw [integral_finsetSum]
      · intro c _
        exact h a b c
    · intro b _
      exact integrable_finsetSum Finset.univ fun c _ => h a b c
  · intro a _
    exact integrable_finsetSum Finset.univ fun b _ =>
      integrable_finsetSum Finset.univ fun c _ => h a b c

/-- **Trace-preserving peeling identity**: if the label `i` does not occur in the word `B`, then
`E[tr (G_i G_i · gueWord B)] = E[tr (gueWord B)]` for `N > 0`. -/
theorem integral_trace_gueWord_cons_cons (i : ι) (B : List ι) (hiB : i ∉ B) (hN : 0 < N) :
    ∫ x : EuclideanSpace ℝ (GUECoord ι N), Matrix.trace (gueWord ([i, i] ++ B) x)
        ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) =
      ∫ x : EuclideanSpace ℝ (GUECoord ι N), Matrix.trace (gueWord B x)
        ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) := by
  rw [show (∫ x : EuclideanSpace ℝ (GUECoord ι N), Matrix.trace (gueWord ([i, i] ++ B) x)
        ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))) =
      ∫ x : EuclideanSpace ℝ (GUECoord ι N),
        ∑ a : Fin N, ∑ b : Fin N, ∑ c : Fin N,
          gueEntry (i, (a, c)) x * gueEntry (i, (c, b)) x * (gueWord B x) b a
        ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) from by
    simp only [trace_gueWord_cons_cons]]
  rw [integral_finset_sum_three (F := fun a b c x =>
    gueEntry (i, (a, c)) x * gueEntry (i, (c, b)) x * (gueWord B x) b a)
    (fun a b c => (integrable_gueEntry_mul_gueEntry_mul_guePathSum i a c b B).congr
      (ae_of_all _ fun x => by simp only [gueWord_entry_pathSum]))]
  rw [integral_trace_gueWord_eq_sum_diag]
  have h1 : ∀ (a b c : Fin N),
      (∫ x : EuclideanSpace ℝ (GUECoord ι N),
          gueEntry (i, (a, c)) x * gueEntry (i, (c, b)) x * (gueWord B x) b a
          ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))) =
        ((N : ℂ)⁻¹) * (if a = b then
          (∫ x : EuclideanSpace ℝ (GUECoord ι N), (gueWord B x) b a
            ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))) else 0) := by
    intro a b c
    rw [integral_gueEntry_mul_gueEntry_mul_gueWord i a c b B hiB, gueCov_entry_entry]
    by_cases h : a = b <;> simp [h]
  simp only [h1]
  have hNR : (N : ℂ) * ((N : ℂ)⁻¹) = 1 :=
    mul_inv_cancel₀ (by exact_mod_cast Nat.ne_of_gt hN)
  have hstep : (∑ a : Fin N, ∑ b : Fin N, ∑ c : Fin N,
        ((N : ℂ)⁻¹) * (if a = b then
          (∫ x : EuclideanSpace ℝ (GUECoord ι N), (gueWord B x) b a
            ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))) else 0)) =
      ∑ a : Fin N, (∫ x : EuclideanSpace ℝ (GUECoord ι N), (gueWord B x) a a
        ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))) := by
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [show (∑ b : Fin N, ∑ c : Fin N, ((N : ℂ)⁻¹) * (if a = b then
          (∫ x : EuclideanSpace ℝ (GUECoord ι N), (gueWord B x) b a
            ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))) else 0)) =
        (∑ b : Fin N, (N : ℂ) * (((N : ℂ)⁻¹) * (if a = b then
          (∫ x : EuclideanSpace ℝ (GUECoord ι N), (gueWord B x) b a
            ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))) else 0))) from
      Finset.sum_congr rfl fun b _ => by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]]
    rw [← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_ite_eq]
    simp only [Finset.mem_univ, ite_true, ← mul_assoc, hNR, one_mul]
  rw [hstep]

theorem integral_trace_gueWord_rotate (i : ι) (B : List ι) (hiB : i ∉ B) (hN : 0 < N) :
    ∫ x : EuclideanSpace ℝ (GUECoord ι N),
        Matrix.trace (gueWord (i :: (B ++ [i])) x)
        ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) =
      ∫ x : EuclideanSpace ℝ (GUECoord ι N), Matrix.trace (gueWord B x)
        ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) := by
  have hstep : ∀ x : EuclideanSpace ℝ (GUECoord ι N),
      Matrix.trace (gueWord (i :: (B ++ [i])) x) =
        Matrix.trace (gueWord ([i, i] ++ B) x) := by
    intro x
    have h1 : gueWord (i :: (B ++ [i])) x = gueMatrix x i * (gueWord B x * gueMatrix x i) := by
      rw [show i :: (B ++ [i]) = [i] ++ (B ++ [i]) from rfl, gueWord_append, gueWord_append]
      simp [gueWord, mul_assoc]
    have h2 : gueWord ([i, i] ++ B) x = gueMatrix x i * gueMatrix x i * gueWord B x := by
      rw [gueWord_append]
      simp [gueWord]
    rw [h1, h2, ← Matrix.mul_assoc,
      Matrix.trace_mul_comm (gueMatrix x i * gueWord B x) (gueMatrix x i),
      Matrix.mul_assoc]
  simp_rw [hstep]
  exact integral_trace_gueWord_cons_cons i B hiB hN


/-! ### The doubled and nested word families -/

/-- The doubled word `i₀ i₀ i₁ i₁ ⋯ i_{m-1} i_{m-1}`. -/
def doubledWord : (m : ℕ) → (Fin m → ι) → List ι
  | 0, _ => []
  | m + 1, i => i 0 :: i 0 :: doubledWord m (fun j => i j.succ)

/-- The nested word `i₀ i₁ ⋯ i_{m-1} i_{m-1} ⋯ i₁ i₀`. -/
def nestedWord : (m : ℕ) → (Fin m → ι) → List ι
  | 0, _ => []
  | m + 1, i => i 0 :: (nestedWord m (fun j => i j.succ) ++ [i 0])

/-- Every letter of a doubled word is one of the labels. -/
lemma exists_label_of_mem_doubledWord : ∀ (m : ℕ) (i : Fin m → ι) {x : ι},
    x ∈ doubledWord m i → ∃ t : Fin m, i t = x
  | 0, _, _, hx => by simp [doubledWord] at hx
  | m + 1, i, x, hx => by
    simp only [doubledWord, List.mem_cons] at hx
    rcases hx with hx | hx | hx
    · exact ⟨0, hx.symm⟩
    · exact ⟨0, hx.symm⟩
    · obtain ⟨t, ht⟩ := exists_label_of_mem_doubledWord m (fun j => i j.succ) hx
      exact ⟨t.succ, ht⟩

/-- Every letter of a nested word is one of the labels. -/
lemma exists_label_of_mem_nestedWord : ∀ (m : ℕ) (i : Fin m → ι) {x : ι},
    x ∈ nestedWord m i → ∃ t : Fin m, i t = x
  | 0, _, _, hx => by simp [nestedWord] at hx
  | m + 1, i, x, hx => by
    simp only [nestedWord, List.mem_cons, List.mem_append, List.mem_singleton,
      List.not_mem_nil, or_false] at hx
    rcases hx with hx | hx | hx
    · exact ⟨0, hx.symm⟩
    · obtain ⟨t, ht⟩ := exists_label_of_mem_nestedWord m (fun j => i j.succ) hx
      exact ⟨t.succ, ht⟩
    · exact ⟨0, hx.symm⟩

/-- For injective labels the first letter does not occur in the tail of a doubled word. -/
lemma label_not_mem_doubledWord {m : ℕ} {i : Fin (m + 1) → ι} (hinj : Function.Injective i) :
    i 0 ∉ doubledWord m (fun j => i j.succ) := by
  intro h
  obtain ⟨t, ht⟩ := exists_label_of_mem_doubledWord m (fun j => i j.succ) h
  exact Fin.succ_ne_zero t (hinj ht)

/-- For injective labels the first letter does not occur in the tail of a nested word. -/
lemma label_not_mem_nestedWord {m : ℕ} {i : Fin (m + 1) → ι} (hinj : Function.Injective i) :
    i 0 ∉ nestedWord m (fun j => i j.succ) := by
  intro h
  obtain ⟨t, ht⟩ := exists_label_of_mem_nestedWord m (fun j => i j.succ) h
  exact Fin.succ_ne_zero t (hinj ht)

/-- Exact trace expectation of a doubled word: `E[tr (doubledWord)] = N`. -/
theorem integral_trace_doubled : ∀ (m : ℕ) (i : Fin m → ι), Function.Injective i →
    (0 < N) →
      ∫ x : EuclideanSpace ℝ (GUECoord ι N), Matrix.trace (gueWord (doubledWord m i) x)
        ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) = (N : ℂ)
  | 0, _, _, _ => by simp [doubledWord]
  | m + 1, i, hinj, hN => by
    rw [show doubledWord (m + 1) i = [i 0, i 0] ++ doubledWord m (fun j => i j.succ) from rfl]
    rw [integral_trace_gueWord_cons_cons (i 0) _ (label_not_mem_doubledWord hinj) hN]
    exact integral_trace_doubled m (fun j => i j.succ) (fun a b h => Fin.succ_inj.mp (hinj h)) hN

/-- Exact trace expectation of a nested word: `E[tr (nestedWord)] = N`. -/
theorem integral_trace_nested : ∀ (m : ℕ) (i : Fin m → ι), Function.Injective i →
    (0 < N) →
      ∫ x : EuclideanSpace ℝ (GUECoord ι N), Matrix.trace (gueWord (nestedWord m i) x)
        ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) = (N : ℂ)
  | 0, _, _, _ => by simp [nestedWord]
  | m + 1, i, hinj, hN => by
    show ∫ x : EuclideanSpace ℝ (GUECoord ι N),
        Matrix.trace (gueWord (i 0 :: (nestedWord m (fun j => i j.succ) ++ [i 0])) x)
        ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) = (N : ℂ)
    rw [integral_trace_gueWord_rotate (i 0) _ (label_not_mem_nestedWord hinj) hN]
    exact integral_trace_nested m (fun j => i j.succ) (fun a b h => Fin.succ_inj.mp (hinj h)) hN

/-- Normalized expectation of a doubled word equals `1`. -/
theorem integral_gueNormTrace_doubled (m : ℕ) (i : Fin m → ι) (hinj : Function.Injective i)
    (hN : 0 < N) :
    ∫ x : EuclideanSpace ℝ (GUECoord ι N), gueNormTrace (doubledWord m i) x
        ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) = 1 := by
  have h : (∫ x : EuclideanSpace ℝ (GUECoord ι N), gueNormTrace (doubledWord m i) x
        ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))) =
      ((N : ℂ)⁻¹) * ∫ x : EuclideanSpace ℝ (GUECoord ι N),
        Matrix.trace (gueWord (doubledWord m i) x)
        ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) := by
    simp only [gueNormTrace]
    rw [integral_const_mul]
  rw [h, integral_trace_doubled m i hinj hN]
  exact inv_mul_cancel₀ (by exact_mod_cast Nat.ne_of_gt hN)

/-- Normalized expectation of a nested word equals `1`. -/
theorem integral_gueNormTrace_nested (m : ℕ) (i : Fin m → ι) (hinj : Function.Injective i)
    (hN : 0 < N) :
    ∫ x : EuclideanSpace ℝ (GUECoord ι N), gueNormTrace (nestedWord m i) x
        ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) = 1 := by
  have h : (∫ x : EuclideanSpace ℝ (GUECoord ι N), gueNormTrace (nestedWord m i) x
        ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))) =
      ((N : ℂ)⁻¹) * ∫ x : EuclideanSpace ℝ (GUECoord ι N),
        Matrix.trace (gueWord (nestedWord m i) x)
        ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) := by
    simp only [gueNormTrace]
    rw [integral_const_mul]
  rw [h, integral_trace_nested m i hinj hN]
  exact inv_mul_cancel₀ (by exact_mod_cast Nat.ne_of_gt hN)

/-- The `N`-indexed normalized expectation of a doubled word tends to `1`. -/
theorem tendsto_integral_gueNormTrace_doubled (m : ℕ) (i : Fin m → ι)
    (hinj : Function.Injective i) :
    Tendsto (fun N : ℕ => ∫ x : EuclideanSpace ℝ (GUECoord ι N),
        gueNormTrace (N := N) (doubledWord m i) x
        ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))) atTop (𝓝 1) := by
  have h : (fun N : ℕ => ∫ x : EuclideanSpace ℝ (GUECoord ι N),
      gueNormTrace (N := N) (doubledWord m i) x
      ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))) =ᶠ[atTop] fun _ => (1 : ℂ) := by
    filter_upwards [eventually_gt_atTop 0] with N hN
    exact integral_gueNormTrace_doubled (N := N) m i hinj hN
  exact tendsto_const_nhds.congr' h.symm

/-- The `N`-indexed normalized expectation of a nested word tends to `1`. -/
theorem tendsto_integral_gueNormTrace_nested (m : ℕ) (i : Fin m → ι)
    (hinj : Function.Injective i) :
    Tendsto (fun N : ℕ => ∫ x : EuclideanSpace ℝ (GUECoord ι N),
        gueNormTrace (N := N) (nestedWord m i) x
        ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))) atTop (𝓝 1) := by
  have h : (fun N : ℕ => ∫ x : EuclideanSpace ℝ (GUECoord ι N),
      gueNormTrace (N := N) (nestedWord m i) x
      ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))) =ᶠ[atTop] fun _ => (1 : ℂ) := by
    filter_upwards [eventually_gt_atTop 0] with N hN
    exact integral_gueNormTrace_nested (N := N) m i hinj hN
  exact tendsto_const_nhds.congr' h.symm

end

end GUEStrongConvergence
