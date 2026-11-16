/-
# Transport of GUE pairings across entry types

A recursive pairing `GUEPairing l` of a list of GUE entries only depends on the *positions* of
the entries, not on the entries themselves.  `GUEPairing.castLength` exploits this for two lists
of the *same* entry type.  For the mean limit of the GUE trace-word moments we need more: the
canonical entry list `gueCanonicalEntries w m hl hN` carries a junk matrix index in `Fin N`, so
the dimension-`M` genus sum lives over pairings of a list whose entry type depends on `M`.  To
identify these sums we have to transport pairings along an arbitrary map of entries
`φ : GUEEntry ι N → GUEEntry ι N'`, which changes the entry type.

This file constructs

* `GUEPairing.mapEntries φ : GUEPairing l → GUEPairing (l.map φ)`, by recursion mirroring the
  head-partner decomposition;
* `partner_mapEntries`: the partner positions are preserved (for label-preserving `φ`);
* `partnerPerm_mapEntries`, `pairOrbitCount_mapEntries`: consequently the face count is preserved;
* `gueLabelWeight_mapEntries`: the label weight is preserved;
* `mapEntries_injective`, `card_mapEntries` and `sum_mapEntries`: the transport is a bijection, so
  finite sums over pairings reindex along it.

No asymptotic statement is made, and no `sorry`/axiom is used.
-/
import GUEStrongConvergence.Probability.FinRotateCongr
import GUEStrongConvergence.Probability.GUEWordGenusExpansionInstance

open MeasureTheory ProbabilityTheory Filter
open scoped RealInnerProductSpace Matrix ENNReal Topology

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false
set_option linter.deprecated false
set_option linter.unusedSimpArgs false

namespace GUEStrongConvergence

noncomputable section

attribute [local instance] Classical.propDecidable

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {N N' : ℕ}

namespace GUEPairing

/-! ### The entry-map transport -/

/-- The position of `k` in the image list `l.map φ`, as a `Fin` index. -/
def mapIndex (φ : GUEEntry ι N → GUEEntry ι N') {l : List (GUEEntry ι N)} (k : Fin l.length) :
    Fin (l.map φ).length :=
  ⟨k.val, by simpa using k.isLt⟩

@[simp] lemma mapIndex_val (φ : GUEEntry ι N → GUEEntry ι N') {l : List (GUEEntry ι N)}
    (k : Fin l.length) : (mapIndex φ k).val = k.val := rfl

/-- Erasing a position commutes with the entry map, at the transported position. -/
theorem map_eraseIdx (φ : GUEEntry ι N → GUEEntry ι N') (l : List (GUEEntry ι N))
    (k : Fin l.length) :
    (l.eraseIdx k).map φ = (l.map φ).eraseIdx (mapIndex φ k) :=
  (List.eraseIdx_map φ l k.val).symm

/-- **Transport of a recursive pairing along a map of entries.**  A pairing of `l` is sent to the
pairing of `l.map φ` that chooses the same partner positions, recursively along the head-partner
decomposition. -/
def mapEntries (φ : GUEEntry ι N → GUEEntry ι N') :
    (l : List (GUEEntry ι N)) → GUEPairing l → GUEPairing (l.map φ)
  | [], .nil => .nil
  | e :: l, .cons _ _ k p =>
      .cons (φ e) (l.map φ) (mapIndex φ k)
        (map_eraseIdx φ l k ▸ mapEntries φ (l.eraseIdx k) p)

@[simp] lemma mapEntries_nil (φ : GUEEntry ι N → GUEEntry ι N') :
    mapEntries φ ([] : List (GUEEntry ι N)) (nil : GUEPairing []) = nil := rfl

/-- The computation rule of `mapEntries` on a `cons` pairing. -/
@[simp] lemma mapEntries_cons (φ : GUEEntry ι N → GUEEntry ι N') (e : GUEEntry ι N)
    (l : List (GUEEntry ι N)) (k : Fin l.length) (p : GUEPairing (l.eraseIdx k)) :
    mapEntries φ (e :: l) (GUEPairing.cons e l k p) =
      GUEPairing.cons (φ e) (l.map φ) (mapIndex φ k)
        (map_eraseIdx φ l k ▸ mapEntries φ (l.eraseIdx k) p) := rfl


/-- Dependent transport along an equality of lists does not change the partner map. -/
lemma partner_eqRec {l₁ l₂ : List (GUEEntry ι N)} (h : l₁ = l₂) (p : GUEPairing l₁)
    (i : Fin l₁.length) :
    partner l₂ (h ▸ p) (Fin.cast (congrArg List.length h) i)
      = Fin.cast (congrArg List.length h) (partner l₁ p i) := by
  cases h
  rfl

/-- **The partner positions are preserved by the entry-map transport.** -/
theorem partner_mapEntries (φ : GUEEntry ι N → GUEEntry ι N') :
    ∀ (l : List (GUEEntry ι N)) (p : GUEPairing l) (h : l.length = (l.map φ).length)
      (i : Fin l.length),
      partner (l.map φ) (mapEntries φ l p) (Fin.cast h i) =
        Fin.cast h (partner l p i) := by
  intro l p
  induction p with
  | nil =>
      intro h i
      exact Fin.elim0 i
  | cons e l k p₀ ih =>
      intro h i
      cases l with
      | nil => exact Fin.elim0 k
      | cons x l' =>
          rw [mapEntries_cons]
          change partner (φ e :: φ x :: l'.map φ)
            (GUEPairing.cons (φ e) (φ x :: l'.map φ) (mapIndex φ k)
              (map_eraseIdx φ (x :: l') k ▸ mapEntries φ ((x :: l').eraseIdx k) p₀))
            (Fin.cast h i) =
            Fin.cast h (partner (e :: x :: l') (GUEPairing.cons e (x :: l') k p₀) i)
          have hk₁ : (x :: l').length = (φ x :: l'.map φ).length := by simp
          have hk₀ : l'.length = (l'.map φ).length := by simp
          have hlen : ((x :: l').eraseIdx k).length = l'.length := by
            have h := List.length_eraseIdx_add_one (l := x :: l') (i := k.val) k.isLt
            have h2 : (x :: l').length = l'.length + 1 := rfl
            omega
          have hlen₂ : ((φ x :: l'.map φ).eraseIdx (mapIndex φ k)).length
              = (l'.map φ).length := by
            have h := List.length_eraseIdx_add_one (l := φ x :: l'.map φ)
              (i := (mapIndex φ k).val) (mapIndex φ k).isLt
            have h2 : (φ x :: l'.map φ).length = (l'.map φ).length + 1 := rfl
            omega
          have h₁ : ((x :: l').eraseIdx k).length
              = ((φ x :: l'.map φ).eraseIdx (mapIndex φ k)).length := by
            rw [hlen, hlen₂, List.length_map]
          by_cases h0 : i = 0
          · have hcast : Fin.cast h i = (0 : Fin (φ e :: φ x :: l'.map φ).length) := by
              rw [h0]
              exact fin_cast_zero hk₁
            have hpart : partner (e :: x :: l') (GUEPairing.cons e (x :: l') k p₀) i
                = k.succ := by
              rw [h0]
              exact partner_cons_zero e x l' k p₀
            rw [hcast, hpart, partner_cons_zero, fin_cast_succ hk₁ k]
            rfl
          · by_cases hkc : i = k.succ
            · have hcast : Fin.cast h i = (mapIndex φ k).succ := by
                rw [hkc]
                exact fin_cast_succ hk₁ k
              have hpart : partner (e :: x :: l') (GUEPairing.cons e (x :: l') k p₀) i
                  = 0 := by
                rw [hkc]
                exact partner_cons_head e x l' k p₀ k.succ rfl
              rw [hcast, hpart,
                partner_cons_head (e := φ e) (x := φ x) (l := l'.map φ) (k := mapIndex φ k)
                  (p := map_eraseIdx φ (x :: l') k ▸ mapEntries φ ((x :: l').eraseIdx k) p₀)
                  (i := (mapIndex φ k).succ) rfl]
              rw [show Fin.cast h (0 : Fin (e :: x :: l').length)
                  = (⟨0, by simp⟩ : Fin ((e :: x :: l').map φ).length) from fin_cast_zero hk₁]
              rfl
            · have h0' : Fin.cast h i ≠ (0 : Fin (φ e :: φ x :: l'.map φ).length) := by
                intro hc
                exact h0 (Fin.cast_injective h (hc.trans (fin_cast_zero hk₁).symm))
              have hkc' : Fin.cast h i ≠ (mapIndex φ k).succ := by
                intro hc
                refine hkc (Fin.cast_injective h ?_)
                rw [hc]
                exact fin_cast_succ hk₁ k
              set qs : Fin ((x :: l').eraseIdx k).length :=
                Fin.cast hlen.symm (eraseIndex l'.length k (i.pred h0)
                  (pred_ne_of_ne_succ h0 hkc)) with hqs
              set qt : Fin ((φ x :: l'.map φ).eraseIdx (mapIndex φ k)).length :=
                Fin.cast hlen₂.symm (eraseIndex (l'.map φ).length (mapIndex φ k)
                  ((Fin.cast h i).pred h0') (pred_ne_of_ne_succ h0' hkc')) with hqt
              rw [partner_cons_other (e := φ e) (x := φ x) (l := l'.map φ)
                (k := mapIndex φ k)
                (p := map_eraseIdx φ (x :: l') k ▸ mapEntries φ ((x :: l').eraseIdx k) p₀)
                hlen₂ (Fin.cast h i) h0' hkc']
              rw [partner_cons_other e x l' k p₀ hlen i h0 hkc]
              rw [← hqt, ← hqs]
              rw [fin_cast_succ hk₁
                (k.succAbove (Fin.cast hlen
                  (partner ((x :: l').eraseIdx k) p₀ qs)))]
              rw [fin_cast_succAbove hk₁ hk₀ k
                (Fin.cast hlen (partner ((x :: l').eraseIdx k) p₀ qs))]
              rw [Fin.succ_inj]
              change (Fin.cast hk₁ k).succAbove
                  (Fin.cast hlen₂
                    (partner ((φ x :: l'.map φ).eraseIdx (mapIndex φ k))
                      (map_eraseIdx φ (x :: l') k ▸ mapEntries φ ((x :: l').eraseIdx k) p₀) qt)) =
                (Fin.cast hk₁ k).succAbove
                  (Fin.cast hk₀ (Fin.cast hlen (partner ((x :: l').eraseIdx k) p₀ qs)))
              rw [Fin.succAbove_inj]
              have hpred_eq : (Fin.cast h i).pred h0' = Fin.cast hk₁ (i.pred h0) :=
                (fin_cast_pred hk₁ i h0 h0').symm
              have hqt_eq : qt = Fin.cast h₁ qs := by
                rw [hqt, hqs]
                simp only [hpred_eq, show mapIndex φ k = Fin.cast hk₁ k from rfl]
                rw [eraseIndex_cast hk₁ hk₀ k (i.pred h0), Fin.cast_cast, Fin.cast_cast]
              rw [hqt_eq]
              rw [show Fin.cast h₁ qs
                  = Fin.cast (congrArg List.length (map_eraseIdx φ (x :: l') k))
                      (Fin.cast (List.length_map (f := φ)).symm qs) from by
                conv_rhs => rw [Fin.cast_cast]]
              change Fin.cast hlen₂
                  (partner (((x :: l').map φ).eraseIdx (mapIndex φ k))
                    (map_eraseIdx φ (x :: l') k ▸ mapEntries φ ((x :: l').eraseIdx k) p₀)
                    (Fin.cast (congrArg List.length (map_eraseIdx φ (x :: l') k))
                      (Fin.cast (List.length_map (f := φ)).symm qs))) =
                Fin.cast hk₀ (Fin.cast hlen (partner ((x :: l').eraseIdx k) p₀ qs))
              rw [partner_eqRec (map_eraseIdx φ (x :: l') k)
                (mapEntries φ ((x :: l').eraseIdx k) p₀)
                (Fin.cast (List.length_map (f := φ)).symm qs)]
              rw [ih (List.length_map (f := φ)).symm qs]
              rfl

/-- Dependent transport of a pairing along an equality of lists does not change the label
weight. -/
lemma gueLabelWeight_eqRec {l₁ l₂ : List (GUEEntry ι N)} (h : l₁ = l₂) (p : GUEPairing l₁) :
    gueLabelWeight l₂ (h ▸ p) = gueLabelWeight l₁ p := by
  cases h
  rfl

/-- **The partner permutation is transported by the entry map**, i.e. the two partner
permutations are conjugate under the position equivalence induced by `List.map`. -/
theorem partnerPerm_mapEntries (φ : GUEEntry ι N → GUEEntry ι N') (l : List (GUEEntry ι N))
    (p : GUEPairing l) (h : l.length = (l.map φ).length) :
    partnerPerm (mapEntries φ l p) = conjBy (finCongr h) (partnerPerm p) := by
  apply Equiv.ext
  intro i
  simp only [conjBy_apply, Equiv.symm_apply_apply, partnerPerm_apply, finCongr_apply,
    finCongr_symm_apply]
  rw [← partner_mapEntries φ l p h (Fin.cast h.symm i)]
  congr 1

/-- **The face count is invariant under the entry-map transport.** -/
theorem pairOrbitCount_mapEntries (φ : GUEEntry ι N → GUEEntry ι N') (l : List (GUEEntry ι N))
    (p : GUEPairing l) (h : l.length = (l.map φ).length) :
    pairOrbitCount (mapEntries φ l p) = pairOrbitCount p := by
  have hpartner : partnerPerm (mapEntries φ l p) = conjBy (finCongr h) (partnerPerm p) :=
    partnerPerm_mapEntries φ l p h
  have hperm : pairOrbitPerm (mapEntries φ l p)
      = conjBy (finCongr h) (pairOrbitPerm p) := by
    rw [pairOrbitPerm, hpartner, pairOrbitPerm, conjBy_mul,
      conjBy_finCongr_finRotate h]
  rw [pairOrbitCount, hperm, pairOrbitCount, permOrbitCount_conjBy]

/-- **The label weight is invariant under the entry-map transport.**  Indeed `gueLabelCov` only
inspects the label (first) component of an entry, and `hφ` says the entry map preserves it. -/
theorem gueLabelWeight_mapEntries (φ : GUEEntry ι N → GUEEntry ι N')
    (hφ : ∀ e : GUEEntry ι N, (φ e).1 = e.1) :
    ∀ (l : List (GUEEntry ι N)) (p : GUEPairing l),
      gueLabelWeight (l.map φ) (mapEntries φ l p) = gueLabelWeight l p := by
  intro l p
  induction p with
  | nil =>
      rw [mapEntries_nil]
      rfl
  | cons e l k p₀ ih =>
      cases l with
      | nil => exact absurd k.isLt (by simp)
      | cons x l' =>
          rw [mapEntries_cons]
          change gueLabelWeight (φ e :: φ x :: l'.map φ)
              (GUEPairing.cons (φ e) (φ x :: l'.map φ) (mapIndex φ k)
                (map_eraseIdx φ (x :: l') k ▸ mapEntries φ ((x :: l').eraseIdx k) p₀)) =
            gueLabelCov e ((x :: l').get k) * gueLabelWeight ((x :: l').eraseIdx k) p₀
          rw [gueLabelWeight_cons]
          have hget : (φ x :: l'.map φ).get (mapIndex φ k) = φ ((x :: l').get k) := by
            simpa using List.getElem_map (f := φ) (l := x :: l') (i := k.val)
              (h := by simpa using k.isLt)
          have hcov : gueLabelCov (φ e) ((φ x :: l'.map φ).get (mapIndex φ k))
              = gueLabelCov e ((x :: l').get k) := by
            simp only [gueLabelCov, hget, hφ]
          rw [hcov]
          change gueLabelCov e ((x :: l').get k) *
              gueLabelWeight (((x :: l').map φ).eraseIdx (mapIndex φ k))
                (map_eraseIdx φ (x :: l') k ▸ mapEntries φ ((x :: l').eraseIdx k) p₀) =
            gueLabelCov e ((x :: l').get k) * gueLabelWeight ((x :: l').eraseIdx k) p₀
          rw [gueLabelWeight_eqRec (map_eraseIdx φ (x :: l') k)
            (mapEntries φ ((x :: l').eraseIdx k) p₀)]
          rw [ih]

/-- Dependent transport along an equality is injective. -/
lemma eqRec_injective {α : Sort*} {F : α → Sort*} {a b : α} (h : a = b) :
    Function.Injective (fun x : F a => h ▸ x) := by
  cases h
  intro x y hxy
  exact hxy

/-- **The entry-map transport is injective** (it only depends on the partner positions). -/
theorem mapEntries_injective (φ : GUEEntry ι N → GUEEntry ι N') (l : List (GUEEntry ι N)) :
    Function.Injective (mapEntries φ l) := by
  intro p
  induction p with
  | nil =>
      intro q _
      cases q
      rfl
  | cons e l k p₀ ih =>
      intro q hq
      cases l with
      | nil => exact absurd k.isLt (by simp)
      | cons x l' =>
          cases q with
          | cons _ _ k₂ q₂ =>
              rw [mapEntries_cons] at hq
              obtain ⟨hk, htail⟩ :=
                (GUEPairing.cons.injEq (φ e) ((x :: l').map φ) (mapIndex φ k)
                  (map_eraseIdx φ (x :: l') k ▸ mapEntries φ ((x :: l').eraseIdx k) p₀)
                  (mapIndex φ k₂)
                  (map_eraseIdx φ (x :: l') k₂
                    ▸ mapEntries φ ((x :: l').eraseIdx k₂) q₂)).mp hq
              have hk' : k = k₂ := Fin.ext (by simpa [mapIndex] using congrArg Fin.val hk)
              cases hk'
              have htail' : (map_eraseIdx φ (x :: l') k ▸ mapEntries φ ((x :: l').eraseIdx k) p₀)
                  = (map_eraseIdx φ (x :: l') k
                    ▸ mapEntries φ ((x :: l').eraseIdx k) q₂) := eq_of_heq htail
              have h2 : mapEntries φ ((x :: l').eraseIdx k) p₀
                  = mapEntries φ ((x :: l').eraseIdx k) q₂ :=
                eqRec_injective (map_eraseIdx φ (x :: l') k) htail'
              exact congrArg (GUEPairing.cons e (x :: l') k) (ih h2)

/-- **The number of pairings depends only on the length of the list**, also across entry types. -/
theorem card_mapEntries (φ : GUEEntry ι N → GUEEntry ι N') :
    ∀ (l : List (GUEEntry ι N)),
      Fintype.card (GUEPairing l) = Fintype.card (GUEPairing (l.map φ)) := by
  intro l
  suffices h : ∀ n, ∀ l : List (GUEEntry ι N), l.length = n →
      Fintype.card (GUEPairing l) = Fintype.card (GUEPairing (l.map φ)) from h _ l rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro l hl
    cases l with
    | nil =>
        have h1 : Fintype.card (GUEPairing ([] : List (GUEEntry ι N))) = 1 := by
          rw [Fintype.card_eq_one_iff]
          exact ⟨GUEPairing.nil, fun p => by cases p; rfl⟩
        have h2 : Fintype.card (GUEPairing (List.map φ ([] : List (GUEEntry ι N)))) = 1 := by
          change Fintype.card (GUEPairing ([] : List (GUEEntry ι N'))) = 1
          rw [Fintype.card_eq_one_iff]
          exact ⟨GUEPairing.nil, fun p => by cases p; rfl⟩
        rw [h1, h2]
    | cons e l =>
        have hlen : l.length < n := by
          rw [List.length_cons] at hl
          omega
        rw [Fintype.card_congr (GUEPairing.consEquiv e l)]
        have hcongr : Fintype.card (GUEPairing (List.map φ (e :: l)))
            = Fintype.card ((k : Fin (l.map φ).length) × GUEPairing ((l.map φ).eraseIdx k)) :=
          Fintype.card_congr (GUEPairing.consEquiv (φ e) (l.map φ))
        rw [hcongr, Fintype.card_sigma, Fintype.card_sigma]
        rw [← Equiv.sum_comp (finCongr (List.length_map φ)).symm
          (fun k' => Fintype.card (GUEPairing ((l.map φ).eraseIdx k')))]
        refine Finset.sum_congr rfl fun k _ => ?_
        have hlist : (l.map φ).eraseIdx ((finCongr (List.length_map φ)).symm k)
            = (l.eraseIdx k).map φ := by
          rw [← List.eraseIdx_map φ l k.val]
          congr 1
        rw [hlist]
        have hlt : (l.eraseIdx k).length < n := by
          have h1 : (l.eraseIdx k).length ≤ l.length := by
            rw [List.length_eraseIdx]
            split <;> omega
          omega
        exact ih (l.eraseIdx k).length hlt (l.eraseIdx k) rfl

/-- **The entry-map transport is bijective.** -/
theorem mapEntries_bijective (φ : GUEEntry ι N → GUEEntry ι N') (l : List (GUEEntry ι N)) :
    Function.Bijective (mapEntries φ l) := by
  refine ⟨mapEntries_injective φ l, ?_⟩
  by_contra hsurj
  have hlt : Fintype.card (GUEPairing l) < Fintype.card (GUEPairing (l.map φ)) :=
    Fintype.card_lt_of_injective_not_surjective (mapEntries φ l)
      (mapEntries_injective φ l) hsurj
  have hcard := card_mapEntries φ l
  omega

/-- **Reindexing a finite sum over pairings along the entry map.** -/
theorem sum_mapEntries {M : Type*} [AddCommMonoid M] (φ : GUEEntry ι N → GUEEntry ι N')
    (l : List (GUEEntry ι N)) (F : GUEPairing (l.map φ) → M) :
    (∑ p : GUEPairing l, F (mapEntries φ l p)) = ∑ q : GUEPairing (l.map φ), F q :=
  Equiv.sum_comp (Equiv.ofBijective (mapEntries φ l) (mapEntries_bijective φ l)) F

/-! ### The cross-dimension identity for the canonical lists -/

/-- The junk-index collapse of GUE entries to `Fin 1`. -/
def collapseEntries : GUEEntry ι N → GUEEntry ι 1 :=
  fun e => (e.1, ((0 : Fin 1), (0 : Fin 1)))

@[simp] lemma collapseEntries_label (e : GUEEntry ι N) : (collapseEntries e).1 = e.1 := rfl

/-- The canonical entry lists at different dimensions are related by the junk collapse. -/
theorem map_collapseEntries_gueCanonicalEntries (w : List ι) (m : ℕ) (hl : w.length = 2 * m)
    (hN : 1 ≤ N) :
    (gueCanonicalEntries w m hl hN).map (collapseEntries (ι := ι) (N := N))
      = gueCanonicalEntries w m hl (le_refl 1) := by
  simp only [gueCanonicalEntries, List.map_ofFn, Function.comp_apply]
  rfl

/-- **Cross-dimension identity for the canonical pairing sums.** -/
theorem sum_gueCanonicalEntries_crossdim (w : List ι) (m : ℕ) (hl : w.length = 2 * m)
    (hN : 1 ≤ N) (M : ℂ) :
    (∑ q : GUEPairing (gueCanonicalEntries w m hl hN),
        gueLabelWeight (gueCanonicalEntries w m hl hN) q * M ^ (pairOrbitCount q))
      = ∑ q : GUEPairing (gueCanonicalEntries w m hl (le_refl 1)),
          gueLabelWeight (gueCanonicalEntries w m hl (le_refl 1)) q * M ^ (pairOrbitCount q) := by
  have hmap := map_collapseEntries_gueCanonicalEntries (ι := ι) w m hl hN
  have hlen : (gueCanonicalEntries w m hl hN).length
      = ((gueCanonicalEntries w m hl hN).map (collapseEntries (ι := ι) (N := N))).length := by
    simp
  have hsum := sum_mapEntries (collapseEntries (ι := ι) (N := N))
    (gueCanonicalEntries w m hl hN)
    (fun q => gueLabelWeight ((gueCanonicalEntries w m hl hN).map
        (collapseEntries (ι := ι) (N := N))) q * M ^ (pairOrbitCount q))
  trans ∑ p : GUEPairing (gueCanonicalEntries w m hl hN),
      gueLabelWeight ((gueCanonicalEntries w m hl hN).map
        (collapseEntries (ι := ι) (N := N)))
        (mapEntries (collapseEntries (ι := ι) (N := N)) (gueCanonicalEntries w m hl hN) p) *
        M ^ pairOrbitCount (mapEntries (collapseEntries (ι := ι) (N := N))
          (gueCanonicalEntries w m hl hN) p)
  · refine Finset.sum_congr rfl fun p _ => ?_
    rw [gueLabelWeight_mapEntries (collapseEntries (ι := ι) (N := N))
      (collapseEntries_label (ι := ι) (N := N))]
    rw [pairOrbitCount_mapEntries (collapseEntries (ι := ι) (N := N))
      (gueCanonicalEntries w m hl hN) p hlen]
  · trans ∑ q : GUEPairing ((gueCanonicalEntries w m hl hN).map
        (collapseEntries (ι := ι) (N := N))),
        gueLabelWeight ((gueCanonicalEntries w m hl hN).map
          (collapseEntries (ι := ι) (N := N))) q * M ^ (pairOrbitCount q)
    · exact hsum
    · rw [hmap]

/-! ### The mean limit -/

/-- **The mean limit of the normalized GUE trace-word moments**: the expectation of `tr_N(G_w)`
converges to the sum of the label weights of the non-crossing pairings. -/
theorem mean_limit (w : List ι) (m : ℕ) (hl : w.length = 2 * m) (hpos : 1 ≤ w.length)
    (hm : 1 ≤ m) :
    Tendsto (fun N : ℕ => ∫ x : EuclideanSpace ℝ (GUECoord ι N), gueNormTrace w x
        ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))) atTop
      (𝓝 (∑ p ∈ (Finset.univ : Finset
            (GUEPairing (gueCanonicalEntries w m hl (le_refl 1)))).filter IsNonCrossing,
          gueLabelWeight (gueCanonicalEntries w m hl (le_refl 1)) p)) := by
  have hK : (gueCanonicalEntries w m hl (le_refl 1)).length = 2 * m :=
    length_gueCanonicalEntries w m hl (le_refl 1)
  refine tendsto_of_genus_expansion hm (gueCanonicalEntries w m hl (le_refl 1)) hK
    (fun p => gueLabelWeight (gueCanonicalEntries w m hl (le_refl 1)) p)
    (fun N : ℕ => ∫ x : EuclideanSpace ℝ (GUECoord ι N), gueNormTrace w x
      ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))) ?_
  intro M
  by_cases hM : 1 ≤ M
  · rw [integral_gueNormTrace_eq_genus_canonical w m hl hpos hM]
    have hscalar : (M : ℂ) ^ (-(m + 1) : ℤ) = ((M : ℂ) ^ (m + 1))⁻¹ := by
      have h1 : (-(m + 1) : ℤ) = -((m + 1 : ℕ) : ℤ) := by omega
      rw [h1, zpow_neg, zpow_natCast]
    rw [hscalar]
    congr 1
    exact sum_gueCanonicalEntries_crossdim w m hl hM (M : ℂ)
  · have hM0 : M = 0 := by omega
    subst hM0
    have hm1 : m + 1 ≠ 0 := by omega
    simp [gueNormTrace, zero_pow hm1]

end GUEPairing

end

end GUEStrongConvergence




