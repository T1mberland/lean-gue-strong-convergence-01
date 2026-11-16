/-
# Walk vertices: the positional description of a GUE closed walk

This file supplies the first ingredient of the reindexing used by `GUEWordVarianceBound` and by the
genus expansion of `GUEPairingOrbits`: the entries of a walk over a word `w` are read off from a
single *vertex function* on `Fin (w.length + 1)`.

For a start index `a : Fin N` and destination function `d : Fin w.length → Fin N`, the vertex
function is

`walkVertex a d = Fin.cons a d : Fin (w.length + 1) → Fin N`,

i.e. `v 0 = a` and `v (i + 1) = d i`.  The main results are

* `guePathEntries_eq_ofFn`: the walk entry list is `i ↦ (w.get i, (v i, v (i + 1)))`;
* `walkVertex_last`: the terminal vertex is `v (Fin.last w.length)`, so the closing condition
  `guePathLast a w d = a` is exactly the cyclic identification `v (last) = v 0`;
* `walkVertex_cons_tail`: the vertex function of the tail walk is `fun t => v (t + 1)`.

Combined with the bijection between closed walks and cyclic vertex assignments (`Fin k → Fin N`)
this converts the walk sums of `gueTwoTraceDelta` into sums over vertex assignments, where
`sum_twoWalk_index_eq_pow` of `GUEWordVarianceBound` gives the exact loop count.
-/
import GUEStrongConvergence.Probability.GUEPairingGenus
import GUEStrongConvergence.Probability.GUEWordMoments

open MeasureTheory ProbabilityTheory Filter
open scoped RealInnerProductSpace Matrix ENNReal Topology

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false
set_option linter.unusedVariables false

namespace GUEStrongConvergence

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {N : ℕ}

/-- The vertex function of a walk: `v 0 = a` is the start and `v (i + 1) = d i` is the vertex
after the `i`-th step. -/
def walkVertex (a : Fin N) {k : ℕ} (d : Fin k → Fin N) : Fin (k + 1) → Fin N :=
  Fin.cons a d

@[simp] lemma walkVertex_zero (a : Fin N) {k : ℕ} (d : Fin k → Fin N) :
    walkVertex a d 0 = a := by
  simp [walkVertex]

@[simp] lemma walkVertex_succ (a : Fin N) {k : ℕ} (d : Fin k → Fin N) (i : Fin k) :
    walkVertex a d i.succ = d i := by
  simp [walkVertex]

/-- The vertex function of the tail walk is the original vertex function shifted by one. -/
lemma walkVertex_cons_tail (a : Fin N) {k : ℕ} (d : Fin (k + 1) → Fin N) :
    walkVertex (d 0) (Fin.tail d) = fun t : Fin (k + 1) => walkVertex a d t.succ := by
  funext t
  cases t using Fin.cases with
  | zero => simp [walkVertex]
  | succ i => simp [walkVertex, Fin.tail]

/-- **Positional description of the walk entry list**: the entry at position `i` carries the label
`w.get i` and the vertex pair `(v i, v (i + 1))`. -/
theorem guePathEntries_eq_ofFn (w : List ι) (a : Fin N) (d : Fin w.length → Fin N) :
    guePathEntries a w d =
      List.ofFn (fun i : Fin w.length =>
        (w.get i, (walkVertex a d i.castSucc, walkVertex a d i.succ))) := by
  induction w generalizing a with
  | nil => simp [guePathEntries]
  | cons x w ih =>
    rw [guePathEntries_cons, ih (d 0) (Fin.tail d), List.ofFn_succ]
    have htail : (fun i : Fin w.length =>
        (w.get i, (walkVertex (d 0) (Fin.tail d) i.castSucc,
          walkVertex (d 0) (Fin.tail d) i.succ))) =
        fun i : Fin w.length =>
          ((x :: w).get i.succ,
            (walkVertex a d (i.succ.castSucc), walkVertex a d (i.succ.succ))) := by
      funext i
      rw [walkVertex_cons_tail a d]
      simp
    rw [htail]
    congr 1

/-- **The terminal vertex is the last vertex function value**. -/
theorem walkVertex_last (a : Fin N) (w : List ι) (d : Fin w.length → Fin N) :
    walkVertex a d (Fin.last w.length) = guePathLast a w d := by
  induction w generalizing a with
  | nil => simp [guePathLast, walkVertex]
  | cons x w ih =>
    rw [guePathLast_cons, ← ih (d 0) (Fin.tail d), walkVertex_cons_tail a d]
    congr 1

/-- **The closing condition is the cyclic vertex identification**: a walk closes exactly when the
first and last vertices agree. -/
theorem guePathLast_eq_iff (w : List ι) (a : Fin N) (d : Fin w.length → Fin N) :
    guePathLast a w d = a ↔ walkVertex a d (Fin.last w.length) = walkVertex a d 0 := by
  rw [← walkVertex_last a w d, walkVertex_zero]

/-! ### The delta weight as a product over the explicit pair list

These are the easy halves of the product identity for `gueDeltaWeight`: the Kronecker covariance is
symmetric, and the recursive delta weight is the product of the covariances over the explicit
recursive pair list.  The remaining step (relating that pair list to the *positions* via
`partner l p`, which is what the vertex-count argument needs) is not formalized here. -/

/-- The GUE Kronecker covariance is symmetric. -/
lemma gueDeltaCov_comm (e f : GUEEntry ι N) : gueDeltaCov e f = gueDeltaCov f e := by
  simp only [gueDeltaCov, and_comm, eq_comm]

/-- The explicit pair list of a pairing (head paired with position `k`, then recurse). -/
def guePairList : (l : List (GUEEntry ι N)) → GUEPairing l → List (GUEEntry ι N × GUEEntry ι N)
  | _, .nil => []
  | _, .cons e l k p => (e, l.get k) :: guePairList (l.eraseIdx k) p

@[simp] lemma guePairList_nil :
    guePairList ([] : List (GUEEntry ι N)) (GUEPairing.nil : GUEPairing []) = [] := rfl

@[simp] lemma guePairList_cons (e : GUEEntry ι N) (l : List (GUEEntry ι N))
    (k : Fin l.length) (p : GUEPairing (l.eraseIdx k)) :
    guePairList (e :: l) (GUEPairing.cons e l k p) =
      (e, l.get k) :: guePairList (l.eraseIdx k) p := rfl

/-- **Delta weight as a product over the explicit pair list.** -/
theorem gueDeltaWeight_eq_prod_pairList (l : List (GUEEntry ι N)) (p : GUEPairing l) :
    gueDeltaWeight l p =
      ((guePairList l p).map
        (fun q : GUEEntry ι N × GUEEntry ι N => gueDeltaCov q.1 q.2)).prod := by
  induction p with
  | nil => rfl
  | cons e l k p ih =>
    rw [gueDeltaWeight_cons, guePairList_cons, List.map_cons, List.prod_cons, ih]

/-- The Kronecker covariance takes the values `0` and `1`. -/
lemma gueDeltaCov_eq_zero_or_one (e f : GUEEntry ι N) :
    gueDeltaCov e f = 0 ∨ gueDeltaCov e f = 1 := by
  simp only [gueDeltaCov]
  split_ifs <;> simp

/-- A product over a list of Kronecker indicators is `0` or `1`. -/
lemma gueDeltaWeight_eq_zero_or_one (l : List (GUEEntry ι N)) (p : GUEPairing l) :
    gueDeltaWeight l p = 0 ∨ gueDeltaWeight l p = 1 := by
  induction p with
  | nil => simp [gueDeltaWeight]
  | cons e l k p ih =>
    rw [gueDeltaWeight_cons]
    rcases gueDeltaCov_eq_zero_or_one e (l.get k) with h | h
    · exact Or.inl (by rw [h, zero_mul])
    · rcases ih with h' | h'
      · exact Or.inl (by rw [h', mul_zero])
      · exact Or.inr (by rw [h, h', mul_one])

/-! ### R2: closed-walk sums as sums over cyclic vertex functions -/

/-- The last cyclic position of a nonempty walk. -/
def cyclicLastIdx {k : ℕ} (hk : 1 ≤ k) : Fin k := ⟨k - 1, by omega⟩

/-- The closed vertex function attached to a cyclic vertex function `u` of a nonempty walk:
`v = Fin.cons (u last) u`, which satisfies `v (last) = v 0`. -/
def cyclicVertex {k : ℕ} (hk : 1 ≤ k) (u : Fin k → Fin N) : Fin (k + 1) → Fin N :=
  Fin.cons (u (cyclicLastIdx hk)) u

lemma cyclicLastIdx_succ {k : ℕ} (hk : 1 ≤ k) :
    (cyclicLastIdx hk).succ = (Fin.last k : Fin (k + 1)) := by
  ext
  simp [cyclicLastIdx]
  omega

lemma cyclicVertex_last {k : ℕ} (hk : 1 ≤ k) (u : Fin k → Fin N) :
    cyclicVertex hk u (Fin.last k) = cyclicVertex hk u 0 := by
  rw [← cyclicLastIdx_succ hk]
  simp [cyclicVertex]

lemma cyclicVertex_tail {k : ℕ} (hk : 1 ≤ k) (u : Fin k → Fin N) :
    Fin.tail (cyclicVertex hk u) = u := by
  simp [cyclicVertex, Fin.tail_def]

/-- Every closed vertex function of a nonempty walk is `cyclicVertex` of its tail. -/
lemma cyclicVertex_eta {k : ℕ} (hk : 1 ≤ k) (v : Fin (k + 1) → Fin N)
    (hv : v (Fin.last k) = v 0) : cyclicVertex hk (Fin.tail v) = v := by
  have hlast : (cyclicLastIdx hk).succ = (Fin.last k : Fin (k + 1)) := cyclicLastIdx_succ hk
  funext j
  cases j using Fin.cases with
  | zero =>
    simp only [cyclicVertex, Fin.cons_zero]
    show v (cyclicLastIdx hk).succ = v 0
    rw [hlast, hv]
  | succ i =>
    simp only [cyclicVertex, Fin.cons_succ, Fin.tail_def]

/-- **R2**: for a nonempty word, the closed-walk sum over `(a, d)` equals the sum over cyclic
vertex functions `u : Fin w.length → Fin N` (start `u (last)`, destination `j ↦ u j`). -/
theorem sum_closedWalk_eq_sum_vertex (w : List ι) (hpos : 1 ≤ w.length)
    (F : Fin N → (Fin w.length → Fin N) → ℂ) :
    (∑ a : Fin N, ∑ d : Fin w.length → Fin N,
        (if guePathLast a w d = a then F a d else 0)) =
      ∑ u : Fin w.length → Fin N, F (u (cyclicLastIdx hpos)) u := by
  classical
  -- Pair the two sums.
  have hA : (∑ a : Fin N, ∑ d : Fin w.length → Fin N,
        (if guePathLast a w d = a then F a d else 0)) =
      ∑ p : Fin N × (Fin w.length → Fin N),
        (if guePathLast p.1 w p.2 = p.1 then F p.1 p.2 else 0) :=
    (Fintype.sum_prod_type' (f := fun a d =>
      if guePathLast a w d = a then F a d else 0)).symm
  rw [hA]
  -- Reindex `(a, d)` by the vertex function `Fin.cons a d`.
  have hB : (∑ p : Fin N × (Fin w.length → Fin N),
        (if guePathLast p.1 w p.2 = p.1 then F p.1 p.2 else 0)) =
      ∑ v : Fin (w.length + 1) → Fin N,
        (if v (Fin.last w.length) = v 0 then F (v 0) (Fin.tail v) else 0) := by
    refine Fintype.sum_equiv
      (Fin.consEquiv (fun _ : Fin (w.length + 1) => Fin N)) _ _ ?_
    intro p
    obtain ⟨a, d⟩ := p
    have hcons : ((Fin.consEquiv (fun _ : Fin (w.length + 1) => Fin N)) (a, d))
        = Fin.cons a d := by
      funext i
      rw [Fin.consEquiv_apply]
    rw [hcons, Fin.tail_cons]
    have h1 : (Fin.cons a d : Fin (w.length + 1) → Fin N) (Fin.last w.length) =
        guePathLast a w d := walkVertex_last a w d
    have h2 : (Fin.cons a d : Fin (w.length + 1) → Fin N) 0 = a := walkVertex_zero a d
    rw [h1, h2]
  rw [hB]
  -- Identify closed vertex functions with cyclic vertex functions.
  have himg : (Finset.univ.filter fun v : Fin (w.length + 1) → Fin N =>
        v (Fin.last w.length) = v 0) =
      Finset.univ.image (fun u : Fin w.length → Fin N => cyclicVertex hpos u) := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro hv
      exact ⟨Fin.tail v, cyclicVertex_eta hpos v hv⟩
    · rintro ⟨u, rfl⟩
      exact cyclicVertex_last hpos u
  have hinj : ∀ u ∈ (Finset.univ : Finset (Fin w.length → Fin N)),
      ∀ u' ∈ Finset.univ, cyclicVertex hpos u = cyclicVertex hpos u' → u = u' := by
    intro u _ u' _ h
    rw [← cyclicVertex_tail hpos u, ← cyclicVertex_tail hpos u', h]
  rw [← Finset.sum_filter, himg, Finset.sum_image hinj]
  refine Finset.sum_congr rfl fun u _ => ?_
  simp only [cyclicVertex, Fin.cons_zero, Fin.tail_cons]

/-- The empty-word case of the closed-walk reindexing: there is a single destination function, and
the closing condition is automatic. -/
theorem sum_closedWalk_nil (F : Fin N → (Fin 0 → Fin N) → ℂ) :
    (∑ a : Fin N, ∑ d : Fin 0 → Fin N,
        (if guePathLast a ([] : List ι) d = a then F a d else 0)) =
      ∑ a : Fin N, F a default := by
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_eq_single (default : Fin 0 → Fin N)]
  · simp [guePathLast_nil]
  · intro b _ hb
    exact absurd (Subsingleton.elim b default) hb
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- **The entry list in cyclic vertex form**: for a nonempty word, the walk with start `u (last)`
and destinations `u` has `i`-th entry `(w.get i, (v i, v (i + 1)))`, where `v = cyclicVertex u` is
the closed vertex function. -/
theorem guePathEntries_cyclicVertex (w : List ι) (hpos : 1 ≤ w.length)
    (u : Fin w.length → Fin N) :
    guePathEntries (u (cyclicLastIdx hpos)) w u =
      List.ofFn (fun i : Fin w.length =>
        (w.get i, (cyclicVertex hpos u i.castSucc, cyclicVertex hpos u i.succ))) := by
  rw [guePathEntries_eq_ofFn]
  rfl

/-- **Closed-walk sum of an entry-list functional in vertex form**: the sum over closed walks of any
functional of the entry list becomes a sum over cyclic vertex functions. -/
theorem sum_closedWalk_entries (w : List ι) (hpos : 1 ≤ w.length)
    (G : List (GUEEntry ι N) → ℂ) :
    (∑ a : Fin N, ∑ d : Fin w.length → Fin N,
        (if guePathLast a w d = a then G (guePathEntries a w d) else 0)) =
      ∑ u : Fin w.length → Fin N,
        G (List.ofFn (fun i : Fin w.length =>
          (w.get i, (cyclicVertex hpos u i.castSucc, cyclicVertex hpos u i.succ)))) := by
  rw [sum_closedWalk_eq_sum_vertex w hpos
    (fun a d => G (guePathEntries a w d))]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [guePathEntries_cyclicVertex w hpos]

end

end GUEStrongConvergence
