/-
# The genus expansion, instantiated at the vertex parametrization

This file assembles the exact genus expansion of a GUE trace-word moment

`∫ tr_N (G_w) = ∑_p label(p) N^{c(p) - m - 1}`

from the vertex-sum form of the moment (`integral_gueNormTrace_eq_sum_vertex_label_index`),
the slot reindexing of the cyclic vertex functions and the loop count
`sum_prod_indexConstraints_cyclicVertex`.

The main result is `integral_gueNormTrace_eq_genus`: for a word of length `2 * m` and any list of
entries `K` of length `2 * m` with the same labels as `w`, the normalized moment is
`N^{-(m+1)}` times the sum over pairings of `K` of the label weight times `N^{c(p)}`.
-/
import GUEStrongConvergence.Probability.GUEWordGenusExpansion
import GUEStrongConvergence.Probability.GUEWordGenusLimit
import GUEStrongConvergence.Probability.FinRotateCongr
import GUEStrongConvergence.Probability.GUEPairingEar

open MeasureTheory ProbabilityTheory Filter
open scoped RealInnerProductSpace Matrix ENNReal Topology BigOperators

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace GUEStrongConvergence

attribute [local instance] Classical.propDecidable

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {N : ℕ}

/-- The vertex entry list has the length of the word. -/
theorem length_gueVertexEntries (w : List ι) (hpos : 1 ≤ w.length)
    (u : Fin w.length → Fin N) :
    (gueVertexEntries w hpos u).length = w.length := by
  simp [gueVertexEntries]

/-- **Entry evaluation at the vertex parametrization.** -/
theorem gueVertexEntries_get (w : List ι) (hpos : 1 ≤ w.length)
    (u : Fin w.length → Fin N) (i : Fin w.length) :
    (gueVertexEntries w hpos u).get
        (Fin.cast (length_gueVertexEntries w hpos u).symm i) =
      (w.get i, (cyclicVertex hpos u i.castSucc, cyclicVertex hpos u i.succ)) := by
  simp only [gueVertexEntries, List.get_ofFn]
  congr 1

/-- Cast-free access to the vertex entry list at an arbitrary position. -/
theorem gueVertexEntries_get_apply' (w : List ι) (hpos : 1 ≤ w.length)
    (u : Fin w.length → Fin N) (i : Fin (gueVertexEntries w hpos u).length) :
    (gueVertexEntries w hpos u).get i =
      (w.get (Fin.cast (length_gueVertexEntries w hpos u) i),
        (cyclicVertex hpos u (Fin.cast (length_gueVertexEntries w hpos u) i).castSucc,
         cyclicVertex hpos u (Fin.cast (length_gueVertexEntries w hpos u) i).succ)) := by
  unfold gueVertexEntries at *
  rw [List.get_ofFn]

/-! ### Label access -/

theorem gueVertexEntries_get_label (w : List ι) (hpos : 1 ≤ w.length)
    (u : Fin w.length → Fin N) (i : Fin (gueVertexEntries w hpos u).length) :
    ((gueVertexEntries w hpos u).get i).1 =
      w.get (Fin.cast (length_gueVertexEntries w hpos u) i) := by
  rw [gueVertexEntries_get_apply']

/-- A canonical list of `2 * m` entries carrying the labels of `w`; the matrix indices are a
fixed junk value. -/
def gueCanonicalEntries (w : List ι) (m : ℕ) (hl : w.length = 2 * m) (hN : 1 ≤ N) :
    List (GUEEntry ι N) :=
  List.ofFn (fun i : Fin (2 * m) =>
    (w.get (Fin.cast hl.symm i), ((⟨0, hN⟩ : Fin N), (⟨0, hN⟩ : Fin N))))

theorem length_gueCanonicalEntries (w : List ι) (m : ℕ) (hl : w.length = 2 * m) (hN : 1 ≤ N) :
    (gueCanonicalEntries w m hl hN).length = 2 * m :=
  List.length_ofFn

theorem gueCanonicalEntries_get (w : List ι) (m : ℕ) (hl : w.length = 2 * m) (hN : 1 ≤ N)
    (i : Fin (gueCanonicalEntries w m hl hN).length) :
    (gueCanonicalEntries w m hl hN).get i =
      (w.get (Fin.cast hl.symm (Fin.cast (length_gueCanonicalEntries w m hl hN) i)),
        ((⟨0, hN⟩ : Fin N), (⟨0, hN⟩ : Fin N))) := by
  unfold gueCanonicalEntries at *
  rw [List.get_ofFn]

theorem gueCanonicalEntries_get_label (w : List ι) (m : ℕ) (hl : w.length = 2 * m) (hN : 1 ≤ N)
    (i : Fin (gueCanonicalEntries w m hl hN).length) :
    ((gueCanonicalEntries w m hl hN).get i).1 =
      w.get (Fin.cast hl.symm (Fin.cast (length_gueCanonicalEntries w m hl hN) i)) := by
  rw [gueCanonicalEntries_get]

/-! ### The index product in slot form -/

/-- **Pointwise index covariance in slot form.** -/
theorem gueIndexCov_vertexEntries (w : List ι) (hpos : 1 ≤ w.length)
    (u : Fin w.length → Fin N) (p : GUEPairing (gueVertexEntries w hpos u))
    (i : Fin (gueVertexEntries w hpos u).length) :
    gueIndexCov ((gueVertexEntries w hpos u).get i)
        ((gueVertexEntries w hpos u).get (partner (gueVertexEntries w hpos u) p i)) =
      (if (slotVertex hpos u (Fin.cast (length_gueVertexEntries w hpos u) i) =
            slotVertex hpos u (finRotate w.length
              (Fin.cast (length_gueVertexEntries w hpos u)
                (partner (gueVertexEntries w hpos u) p i))) ∧
          slotVertex hpos u (finRotate w.length (Fin.cast (length_gueVertexEntries w hpos u) i)) =
            slotVertex hpos u (Fin.cast (length_gueVertexEntries w hpos u)
              (partner (gueVertexEntries w hpos u) p i)))
        then (1 : ℂ) else 0) := by
  rw [gueVertexEntries_get_apply' w hpos u i,
      gueVertexEntries_get_apply' w hpos u (partner (gueVertexEntries w hpos u) p i)]
  simp only [gueIndexCov, slotVertex]
  rw [cyclicVertex_succ_eq hpos u (Fin.cast (length_gueVertexEntries w hpos u)
        (partner (gueVertexEntries w hpos u) p i)),
      cyclicVertex_succ_eq hpos u (Fin.cast (length_gueVertexEntries w hpos u) i)]
  exact if_congr Iff.rfl rfl rfl

/-- **The index product in slot form.** -/
theorem prod_gueIndexCov_vertexEntries (w : List ι) (hpos : 1 ≤ w.length)
    (u : Fin w.length → Fin N) (p : GUEPairing (gueVertexEntries w hpos u)) :
    (∏ i : Fin (gueVertexEntries w hpos u).length,
        gueIndexCov ((gueVertexEntries w hpos u).get i)
          ((gueVertexEntries w hpos u).get
            (partner (gueVertexEntries w hpos u) p i))) =
      ∏ j : Fin w.length,
        (if (slotVertex hpos u j =
              slotVertex hpos u (finRotate w.length
                (conjBy (finCongr (length_gueVertexEntries w hpos u)) (partnerPerm p) j)) ∧
            slotVertex hpos u (finRotate w.length j) =
              slotVertex hpos u
                (conjBy (finCongr (length_gueVertexEntries w hpos u)) (partnerPerm p) j))
          then (1 : ℂ) else 0) := by
  have hσeq : ∀ i : Fin (gueVertexEntries w hpos u).length,
      conjBy (finCongr (length_gueVertexEntries w hpos u)) (partnerPerm p)
          (Fin.cast (length_gueVertexEntries w hpos u) i) =
        Fin.cast (length_gueVertexEntries w hpos u)
          (partner (gueVertexEntries w hpos u) p i) := by
    intro i
    rw [conjBy_apply, finCongr_apply]
    have h1 : (finCongr (length_gueVertexEntries w hpos u)).symm
        (Fin.cast (length_gueVertexEntries w hpos u) i) = i := by
      rw [← finCongr_apply]
      exact Equiv.symm_apply_apply _ _
    rw [h1, partnerPerm_apply]
  rw [Finset.prod_congr rfl (fun i _ => gueIndexCov_vertexEntries w hpos u p i)]
  rw [← Equiv.prod_comp (finCongr (length_gueVertexEntries w hpos u))
    (fun j : Fin w.length =>
      (if (slotVertex hpos u j =
            slotVertex hpos u (finRotate w.length
              (conjBy (finCongr (length_gueVertexEntries w hpos u)) (partnerPerm p) j)) ∧
          slotVertex hpos u (finRotate w.length j) =
            slotVertex hpos u
              (conjBy (finCongr (length_gueVertexEntries w hpos u)) (partnerPerm p) j))
        then (1 : ℂ) else 0))]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp only [finCongr_apply]
  rw [hσeq i]

/-! ### The vertex sum of the index weights -/

/-- `finCongr` is compatible with composition of length equalities. -/
lemma finCongr_trans {n m k : ℕ} (h : n = m) (h' : m = k) :
    (finCongr h).trans (finCongr h') = finCongr (h.trans h') := by
  ext x
  simp [finCongr_apply, Fin.cast_cast]

/-- **The sum over vertex functions of the index product** for a transported pairing equals `N` to
the face count. -/
theorem sum_gueIndexCov_vertexEntries (w : List ι) (m : ℕ) (hl : w.length = 2 * m)
    (hpos : 1 ≤ w.length) (K : List (GUEEntry ι N)) (hK : K.length = 2 * m)
    (q : GUEPairing K) :
    (∑ u : Fin w.length → Fin N,
        ∏ i : Fin (gueVertexEntries w hpos u).length,
          gueIndexCov ((gueVertexEntries w hpos u).get i)
            ((gueVertexEntries w hpos u).get
              (partner (gueVertexEntries w hpos u)
                (GUEPairing.castLength K (gueVertexEntries w hpos u)
                  ((hK.trans hl.symm).trans (length_gueVertexEntries w hpos u).symm) q) i)))
      = (N : ℂ) ^ pairOrbitCount q := by
  set σ : Equiv.Perm (Fin w.length) := conjBy (finCongr (hK.trans hl.symm)) (partnerPerm q)
    with hσdef
  have hσvu : ∀ (u : Fin w.length → Fin N),
      conjBy (finCongr (length_gueVertexEntries w hpos u))
          (partnerPerm (GUEPairing.castLength K (gueVertexEntries w hpos u)
            ((hK.trans hl.symm).trans (length_gueVertexEntries w hpos u).symm) q)) = σ := by
    intro u
    rw [GUEPairing.partnerPerm_castLength]
    rw [show (finCongr ((hK.trans hl.symm).trans (length_gueVertexEntries w hpos u).symm)).symm.trans
          ((partnerPerm q).trans (finCongr ((hK.trans hl.symm).trans (length_gueVertexEntries w hpos u).symm)))
        = conjBy (finCongr ((hK.trans hl.symm).trans (length_gueVertexEntries w hpos u).symm))
            (partnerPerm q) from by
      ext x
      rfl]
    rw [conjBy_conjBy, finCongr_trans, hσdef, show ((hK.trans hl.symm).trans (length_gueVertexEntries w hpos u).symm).trans (length_gueVertexEntries w hpos u) = hK.trans hl.symm from Subsingleton.elim _ _]
  have hsummand : ∀ u : Fin w.length → Fin N,
      (∏ i : Fin (gueVertexEntries w hpos u).length,
          gueIndexCov ((gueVertexEntries w hpos u).get i)
            ((gueVertexEntries w hpos u).get
              (partner (gueVertexEntries w hpos u)
                (GUEPairing.castLength K (gueVertexEntries w hpos u)
                  ((hK.trans hl.symm).trans (length_gueVertexEntries w hpos u).symm) q) i))) =
        ∏ i : Fin w.length,
          (if (slotVertex hpos u i = slotVertex hpos u (finRotate w.length (σ i)) ∧
              slotVertex hpos u (finRotate w.length i) = slotVertex hpos u (σ i))
            then (1 : ℂ) else 0) := by
    intro u
    rw [prod_gueIndexCov_vertexEntries]
    rw [hσvu u]
  rw [Finset.sum_congr rfl (fun u _ => hsummand u)]
  have hσ2 : σ * σ = 1 := by
    have hq2 : partnerPerm q * partnerPerm q = 1 := by
      refine Equiv.ext fun i => ?_
      show (partnerPerm q * partnerPerm q) i = (1 : Equiv.Perm (Fin K.length)) i
      rw [Equiv.Perm.mul_apply, Equiv.Perm.one_apply]
      exact partnerPerm_involutive q i
    rw [hσdef, ← conjBy_mul, hq2, conjBy_one]
  rw [sum_prod_indexConstraints_cyclicVertex w.length hpos σ hσ2]
  congr 1
  rw [hσdef]
  rw [← conjBy_finCongr_finRotate (hK.trans hl.symm)]
  rw [← conjBy_mul]
  rw [permOrbitCount_conjBy]
  rfl

/-! ### The exact genus expansion -/

/-- **The exact genus expansion of a GUE trace-word moment**: for a word `w` of even length `2 * m`
and any list `K` of `2 * m` entries with the same labels as `w`, the normalized moment is
`N^{-(m+1)}` times the sum over pairings of `K` of the label weight times `N` to the face count. -/
theorem integral_gueNormTrace_eq_genus (w : List ι) (m : ℕ) (hl : w.length = 2 * m)
    (hpos : 1 ≤ w.length) (K : List (GUEEntry ι N)) (hK : K.length = 2 * m)
    (hlabel : ∀ i : Fin w.length, (K.get (Fin.cast (hl.trans hK.symm) i)).1 = w.get i) :
    ∫ x : EuclideanSpace ℝ (GUECoord ι N), gueNormTrace w x
        ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) =
      (N : ℂ) ^ (-(m + 1) : ℤ) *
        ∑ q : GUEPairing K, gueLabelWeight K q * (N : ℂ) ^ (pairOrbitCount q) := by
  rw [integral_gueNormTrace_eq_sum_vertex_label_index w hpos]
  have hscalar : ((N : ℂ)⁻¹) ^ (w.length / 2 + 1) = (N : ℂ) ^ (-(m + 1) : ℤ) := by
    have hk : w.length / 2 + 1 = m + 1 := by omega
    rw [hk, show (-(m + 1) : ℤ) = -((m + 1 : ℕ) : ℤ) from by omega,
      zpow_neg, zpow_natCast, inv_pow]
  rw [hscalar]
  congr 1
  -- rewrite each label product as the label weight
  have hterm : ∀ (u : Fin w.length → Fin N) (p : GUEPairing (gueVertexEntries w hpos u)),
      (∏ i : Fin (gueVertexEntries w hpos u).length,
          gueLabelCov ((gueVertexEntries w hpos u).get i)
            ((gueVertexEntries w hpos u).get (partner (gueVertexEntries w hpos u) p i))) *
        (∏ i : Fin (gueVertexEntries w hpos u).length,
          gueIndexCov ((gueVertexEntries w hpos u).get i)
            ((gueVertexEntries w hpos u).get (partner (gueVertexEntries w hpos u) p i)))
      = gueLabelWeight (gueVertexEntries w hpos u) p *
        ∏ i : Fin (gueVertexEntries w hpos u).length,
          gueIndexCov ((gueVertexEntries w hpos u).get i)
            ((gueVertexEntries w hpos u).get (partner (gueVertexEntries w hpos u) p i)) := by
    intro u p
    rw [← gueLabelWeight_eq_prod_partner]
  simp only [hterm]
  -- transport the pairings of each vertex list to the canonical list `K`
  have htrans : ∀ u : Fin w.length → Fin N,
      (∑ p : GUEPairing (gueVertexEntries w hpos u),
          gueLabelWeight (gueVertexEntries w hpos u) p *
            ∏ i : Fin (gueVertexEntries w hpos u).length,
              gueIndexCov ((gueVertexEntries w hpos u).get i)
                ((gueVertexEntries w hpos u).get
                  (partner (gueVertexEntries w hpos u) p i))) =
        ∑ q : GUEPairing K,
          gueLabelWeight K q *
            ∏ i : Fin (gueVertexEntries w hpos u).length,
              gueIndexCov ((gueVertexEntries w hpos u).get i)
                ((gueVertexEntries w hpos u).get
                  (partner (gueVertexEntries w hpos u)
                    (GUEPairing.castLength K (gueVertexEntries w hpos u)
                      ((hK.trans hl.symm).trans
                        (length_gueVertexEntries w hpos u).symm) q) i)) := by
    intro u
    have hKu : K.length = (gueVertexEntries w hpos u).length :=
      (hK.trans hl.symm).trans (length_gueVertexEntries w hpos u).symm
    have hlab : ∀ i : Fin (gueVertexEntries w hpos u).length,
        ((gueVertexEntries w hpos u).get i).1 = (K.get (Fin.cast hKu.symm i)).1 := by
      intro i
      rw [gueVertexEntries_get_label]
      have hji : Fin.cast (hl.trans hK.symm)
          (Fin.cast (hl.trans hK.symm).symm (Fin.cast hKu.symm i)) = Fin.cast hKu.symm i :=
        Fin.ext rfl
      have hh := hlabel (Fin.cast (hl.trans hK.symm).symm (Fin.cast hKu.symm i))
      rw [hji] at hh
      rw [hh]
      exact congrArg w.get (Fin.ext rfl)
    rw [← GUEPairing.sum_castLength (M := ℂ) (l₁ := gueVertexEntries w hpos u) (l₂ := K)
      hKu.symm
      (fun q : GUEPairing K => gueLabelWeight K q *
        ∏ i : Fin (gueVertexEntries w hpos u).length,
          gueIndexCov ((gueVertexEntries w hpos u).get i)
            ((gueVertexEntries w hpos u).get
              (partner (gueVertexEntries w hpos u)
                (GUEPairing.castLength K (gueVertexEntries w hpos u) hKu q) i)))]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [GUEPairing.castLength_castLength]
    rw [← GUEPairing.gueLabelWeight_castLength p K hKu.symm hlab]
  rw [Finset.sum_congr rfl (fun u _ => htrans u)]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [← Finset.mul_sum]
  rw [sum_gueIndexCov_vertexEntries w m hl hpos K hK q]

/-- **The exact genus expansion for the canonical list of labels.** -/
theorem integral_gueNormTrace_eq_genus_canonical (w : List ι) (m : ℕ) (hl : w.length = 2 * m)
    (hpos : 1 ≤ w.length) (hN : 1 ≤ N) :
    ∫ x : EuclideanSpace ℝ (GUECoord ι N), gueNormTrace w x
        ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) =
      (N : ℂ) ^ (-(m + 1) : ℤ) *
        ∑ q : GUEPairing (gueCanonicalEntries w m hl hN),
          gueLabelWeight (gueCanonicalEntries w m hl hN) q * (N : ℂ) ^ (pairOrbitCount q) := by
  refine integral_gueNormTrace_eq_genus w m hl hpos (gueCanonicalEntries w m hl hN)
    (length_gueCanonicalEntries w m hl hN) ?_
  intro i
  rw [gueCanonicalEntries_get_label]
  exact congrArg w.get (Fin.ext rfl)

/-! ### Wiring the mean limit -/

/-- **The mean limit, with the dimension-independent genus expansion as the only input.**

If the normalized moment at dimension `M` is the genus sum over a *fixed* list `K` of `2 * m`
entries (with the labels of `w`), then it tends to the sum of the labels of the non-crossing
pairings.  This is the final combinatorial step of the mean side of II.B; the remaining input is
the identification of the dimension-`M` pairing sum with the fixed-list pairing sum (the
length-preserving transport of the entry list across dimensions). -/
theorem tendsto_of_genus_expansion {m : ℕ} (hm : 1 ≤ m) (K : List (GUEEntry ι N))
    (hK : K.length = 2 * m) (label : GUEPairing K → ℂ) (u : ℕ → ℂ)
    (hgenus : ∀ M : ℕ, u M = ((M : ℂ) ^ (m + 1))⁻¹ *
      ∑ p : GUEPairing K, label p * (M : ℂ) ^ (pairOrbitCount p)) :
    Tendsto u atTop
      (𝓝 (∑ p ∈ (Finset.univ : Finset (GUEPairing K)).filter IsNonCrossing, label p)) :=
  genus_limit_isNonCrossing K hK label
    (fun p hp => pairOrbitCount_eq_of_isNonCrossing p m hm hK hp) u hgenus

/-! ### The remaining cross-dimension identification (for the unconditional mean limit)

The moment at dimension `M` is `integral_gueNormTrace_eq_genus_canonical`, a sum over pairings of
`gueCanonicalEntries w m hl (N := M)`, whose entries have index type `Fin M`.  To feed it into
`tendsto_of_genus_expansion` one needs the dimension-independent pairing sum

  `∑ p : GUEPairing (gueCanonicalEntries w m hl (N := M)), label p * (M : ℂ) ^ c(p)`
    `= ∑ p : GUEPairing (gueCanonicalEntries w m hl (N := 1)), label p * (M : ℂ) ^ c(p)`,

i.e. a reindexing of pairings between entry lists of *different* index types that preserves the
partner permutation (hence the face count) and the labels.  `GUEPairing.castLength` only covers
lists of one fixed entry type.  Two possible supply routes:

* a recursive `GUEPairing.mapEntries (φ : GUEEntry ι M → GUEEntry ι N) : GUEPairing l →
  GUEPairing (l.map φ)` with the companion lemmas
  `partner_mapEntries` (`partner (l.map φ) (mapEntries φ l p) (Fin.cast h i)
  = Fin.cast h (partner l p i)`), `pairOrbitCount_mapEntries` and `gueLabelWeight_mapEntries`
  (for label-preserving `φ`), followed by `GUEPairing.castLength` to the canonical list;
* or surjectivity of `partnerPerm` onto the fixed-point-free involutions of `Fin (2 * m)`, which
  identifies both sums with the dimension-independent sum over all such involutions.
-/

end

end GUEStrongConvergence
