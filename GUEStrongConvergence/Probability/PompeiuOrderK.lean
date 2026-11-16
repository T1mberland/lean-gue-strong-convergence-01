/-
# The generic (order-`k`) Cauchy--Pompeiu plane identity

`Probability/HelfferSjostrand.lean` proves the plane Cauchy--Pompeiu representation

`f lam = (I / 2π) ∫∫ (I • fderiv F z 1 − fderiv F z I) (z − lam)⁻¹`

for the *concrete* first-order cut-off extension `F = almostAnalyticExtCut f`.  The analytic
content of the Helffer--Sjöstrand argument is however independent of which extension is used:
only the following properties of `F` enter.

* `F` is `C¹` (`hF1`);
* `F` has compact support (`hsupp`);
* `F` agrees with `f` on the real axis (`hFreal`);
* the weighted `∂̄` integrand `pompeiuIntegrand F lam` is globally bounded (`hM`).

The present file isolates that argument as `pompeiu_plane_generic`, so that it applies to the
higher-order extensions `almostAnalyticExtOrderCut k f` of `Probability/HigherExtension.lean`.
For those, `∂̄ = O(|Im z|^(k-1))`, so the order-6 extension gives the `|Im z|⁵` vanishing needed
for the strip integral of the sharp resolvent comparison to converge.

## Main results

* `pompeiuIntegrandGeneric`, `planeIntegrandGeneric` — the generic `∂̄` integrand (definitionally
  the already existing `pompeiuIntegrand`);
* `integrableOn_planeIntegrand_generic`, `setIntegral_holeSurround_eq_generic`,
  `tendsto_area_hole_generic` — the rectangle/hole decomposition lemmas, restated for an
  arbitrary `C¹` compactly supported `F`;
* `exists_lipschitz_of_contDiff_one` — a `C¹` compactly supported `F` is globally Lipschitz (only
  this is needed from the extension in the residue estimate);
* **`pompeiu_plane_generic`** — the generic plane identity
  `f lam = (I/2π) ∫∫ pompeiuIntegrandGeneric F lam`;
* `exists_norm_pompeiuIntegrandOrder_le` — the global bound for the order-`k` cut-off extension
  (`k ≥ 1`);
* **`pompeiu_plane_order`** — the order-`k` instance, and `pompeiu_plane_order_six` for `k = 6`.

No `sorry`, no new axioms.
-/
import GUEStrongConvergence.Probability.HelfferSjostrand
import GUEStrongConvergence.Probability.HigherExtension
import GUEStrongConvergence.Probability.TracePompeiu
import GUEStrongConvergence.Probability.LemmaMMeanBound

open MeasureTheory ProbabilityTheory Matrix Filter Topology intervalIntegral
open FreeProbability FreeProbability.Fock
open Complex
open scoped Real Topology NNReal ENNReal Interval Matrix.Norms.Frobenius BigOperators

namespace GUEStrongConvergence

noncomputable section

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 4000000

/-! ## The generic `∂̄` integrand -/

/-- The generic Cauchy--Pompeiu integrand
`(I • fderiv F z 1 − fderiv F z I) * (z − lam)⁻¹`.  It is definitionally the `pompeiuIntegrand`
of `Probability/HelfferSjostrand.lean`; the new name records that no property of the
almost-analytic extension is used. -/
def pompeiuIntegrandGeneric (F : ℂ → ℂ) (lam z : ℂ) : ℂ :=
  (I • fderiv ℝ F z 1 - fderiv ℝ F z I) * (z - lam)⁻¹

lemma pompeiuIntegrandGeneric_eq (F : ℂ → ℂ) (lam z : ℂ) :
    pompeiuIntegrandGeneric F lam z = pompeiuIntegrand F lam z := rfl

/-- The generic plane integrand. -/
@[reducible] def planeIntegrandGeneric (F : ℂ → ℂ) (lam : ℂ) (p : ℝ × ℝ) : ℂ :=
  pompeiuIntegrand F lam ((p.1 : ℂ) + (p.2 : ℂ) * I)

/-! ## Continuity and measurability of the generic integrand -/

/-- The `∂̄` numerator of a `C¹` function is continuous. -/
lemma continuous_dbarGeneric {F : ℂ → ℂ} (hF : ContDiff ℝ 1 F) :
    Continuous (fun z : ℂ => I • fderiv ℝ F z 1 - fderiv ℝ F z I) := by
  have hfd : Continuous (fderiv ℝ F) := hF.continuous_fderiv (by norm_num)
  have h1 : Continuous (fun z : ℂ => fderiv ℝ F z 1) := hfd.clm_apply continuous_const
  have h2 : Continuous (fun z : ℂ => fderiv ℝ F z I) := hfd.clm_apply continuous_const
  exact (continuous_const.mul h1).sub h2

/-- The uncurried generic Cauchy--Pompeiu integrand is a.e. strongly measurable. -/
lemma aestronglyMeasurable_uncurry_pompeiuIntegrand_generic {F : ℂ → ℂ} (hF : ContDiff ℝ 1 F)
    (lam : ℂ) :
    AEStronglyMeasurable (Function.uncurry (fun x y : ℝ =>
      pompeiuIntegrand F lam ((x : ℂ) + (y : ℂ) * I))) volume := by
  have hnum : Continuous (fun z : ℂ => I • fderiv ℝ F z 1 - fderiv ℝ F z I) :=
    continuous_dbarGeneric hF
  have hinv : Measurable (fun z : ℂ => (z - lam)⁻¹) := by fun_prop
  have hQ : Measurable (fun z : ℂ => pompeiuIntegrand F lam z) := by
    simp only [pompeiuIntegrand]
    exact hnum.measurable.mul hinv
  have hφ : Measurable (fun p : ℝ × ℝ => ((p.1 : ℂ) + (p.2 : ℂ) * I)) := by fun_prop
  exact (hQ.comp hφ).aestronglyMeasurable

/-- The uncurried generic Cauchy--Pompeiu integrand is integrable on every rectangle, under a
global bound on the integrand. -/
lemma integrableOn_uncurry_pompeiuIntegrand_generic {F : ℂ → ℂ} (hF : ContDiff ℝ 1 F) {lam : ℂ}
    {M : ℝ} (hM : ∀ z : ℂ, ‖pompeiuIntegrand F lam z‖ ≤ M) (a b c d : ℝ) :
    IntegrableOn (Function.uncurry (fun x y : ℝ =>
      pompeiuIntegrand F lam ((x : ℂ) + (y : ℂ) * I)))
      (Set.Ioc a b ×ˢ Set.Ioc c d) volume := by
  have hfin : (volume.prod volume) (Set.Ioc a b ×ˢ Set.Ioc c d) < ⊤ := by
    rw [Measure.prod_prod, Real.volume_Ioc, Real.volume_Ioc]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top
  refine IntegrableOn.of_bound hfin
    ((aestronglyMeasurable_uncurry_pompeiuIntegrand_generic hF lam).restrict) M ?_
  filter_upwards with p
  exact hM _

/-- Integrability of the generic plane integrand on a rectangle. -/
lemma integrableOn_planeIntegrand_generic {F : ℂ → ℂ} (hF : ContDiff ℝ 1 F) {lam : ℂ}
    {M : ℝ} (hM : ∀ z : ℂ, ‖pompeiuIntegrand F lam z‖ ≤ M) (a b c d : ℝ) :
    IntegrableOn (planeIntegrandGeneric F lam) (Set.Ioc a b ×ˢ Set.Ioc c d) volume :=
  integrableOn_uncurry_pompeiuIntegrand_generic hF hM a b c d

/-- An iterated interval integral of the generic Cauchy--Pompeiu integrand is the set integral
over the corresponding half-open rectangle. -/
lemma integral_interval_prod_pompeiuIntegrand_generic {F : ℂ → ℂ} (hF : ContDiff ℝ 1 F)
    (lam : ℂ) {M : ℝ} (hM : ∀ z : ℂ, ‖pompeiuIntegrand F lam z‖ ≤ M)
    {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d) :
    (∫ x : ℝ in a..b, ∫ y : ℝ in c..d,
        pompeiuIntegrand F lam ((x : ℂ) + (y : ℂ) * I))
      = ∫ p : ℝ × ℝ in Set.Ioc a b ×ˢ Set.Ioc c d,
          pompeiuIntegrand F lam ((p.1 : ℂ) + (p.2 : ℂ) * I) := by
  simp only [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hcd]
  exact (setIntegral_prod _ (integrableOn_uncurry_pompeiuIntegrand_generic hF hM a b c d)).symm

/-! ## The set decomposition of the rectangle with a hole -/

/-- The integral over the four surrounding rectangles is the sum of the four slab integrals
(generic version; the set decomposition itself has no dependence on the integrand). -/
lemma setIntegral_holeSurround_eq_generic {F : ℂ → ℂ} (hF : ContDiff ℝ 1 F) {lam X Y ε M : ℝ}
    (hM : ∀ z : ℂ, ‖pompeiuIntegrand F (lam : ℂ) z‖ ≤ M)
    (hε : 0 < ε) (hX : |lam| < X) (hεX : ε < X - |lam|) (hεY : ε < Y) :
    (∫ p in holeSurround lam ε X Y, planeIntegrandGeneric F (lam : ℂ) p)
      = (∫ p in Set.Ioc (-X) (lam - ε) ×ˢ Set.Ioc (-Y) Y,
            planeIntegrandGeneric F (lam : ℂ) p)
        + (∫ p in Set.Ioc (lam + ε) X ×ˢ Set.Ioc (-Y) Y,
            planeIntegrandGeneric F (lam : ℂ) p)
        + (∫ p in Set.Ioc (lam - ε) (lam + ε) ×ˢ Set.Ioc ε Y,
            planeIntegrandGeneric F (lam : ℂ) p)
        + (∫ p in Set.Ioc (lam - ε) (lam + ε) ×ˢ Set.Ioc (-Y) (-ε),
            planeIntegrandGeneric F (lam : ℂ) p) := by
  have hlam1 : lam ≤ |lam| := le_abs_self lam
  have hlam2 : -|lam| ≤ lam := neg_abs_le lam
  have hAB : Disjoint (Set.Ioc (-X) (lam - ε) ×ˢ Set.Ioc (-Y) Y)
      (Set.Ioc (lam + ε) X ×ˢ Set.Ioc (-Y) Y) :=
    disjoint_Ioc_prod_left (by linarith) _ _
  have hAC : Disjoint (Set.Ioc (-X) (lam - ε) ×ˢ Set.Ioc (-Y) Y)
      (Set.Ioc (lam - ε) (lam + ε) ×ˢ Set.Ioc ε Y) :=
    disjoint_Ioc_prod_left (by linarith) _ _
  have hAD : Disjoint (Set.Ioc (-X) (lam - ε) ×ˢ Set.Ioc (-Y) Y)
      (Set.Ioc (lam - ε) (lam + ε) ×ˢ Set.Ioc (-Y) (-ε)) :=
    disjoint_Ioc_prod_left (by linarith) _ _
  have hBC : Disjoint (Set.Ioc (lam + ε) X ×ˢ Set.Ioc (-Y) Y)
      (Set.Ioc (lam - ε) (lam + ε) ×ˢ Set.Ioc ε Y) :=
    (disjoint_Ioc_prod_left (a := lam - ε) (b := lam + ε) (c := lam + ε)
      (le_refl _) _ _).symm
  have hBD : Disjoint (Set.Ioc (lam + ε) X ×ˢ Set.Ioc (-Y) Y)
      (Set.Ioc (lam - ε) (lam + ε) ×ˢ Set.Ioc (-Y) (-ε)) :=
    (disjoint_Ioc_prod_left (a := lam - ε) (b := lam + ε) (c := lam + ε)
      (le_refl _) _ _).symm
  have hCD : Disjoint (Set.Ioc (lam - ε) (lam + ε) ×ˢ Set.Ioc ε Y)
      (Set.Ioc (lam - ε) (lam + ε) ×ˢ Set.Ioc (-Y) (-ε)) :=
    (disjoint_Ioc_prod_right (a := -Y) (b := -ε) (c := ε) (d := Y) (by linarith) _ _).symm
  have hcol : IntegrableOn (planeIntegrandGeneric F (lam : ℂ))
      (Set.Ioc (lam - ε) X ×ˢ Set.Ioc (-Y) Y) (volume.prod volume) :=
    integrableOn_planeIntegrand_generic hF hM (lam - ε) X (-Y) Y
  have hBCD : IntegrableOn (planeIntegrandGeneric F (lam : ℂ))
      (Set.Ioc (lam + ε) X ×ˢ Set.Ioc (-Y) Y
        ∪ (Set.Ioc (lam - ε) (lam + ε) ×ˢ Set.Ioc ε Y
          ∪ Set.Ioc (lam - ε) (lam + ε) ×ˢ Set.Ioc (-Y) (-ε))) (volume.prod volume) := by
    refine hcol.mono_set ?_
    rintro p hp
    simp only [Set.mem_prod, Set.mem_union, Set.mem_Ioc] at hp ⊢
    rcases hp with ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩
    · exact ⟨⟨by linarith [hx.1], hx.2⟩, hy⟩
    · exact ⟨⟨by linarith [hx.1], by linarith [hx.2]⟩, ⟨by linarith [hy.1, hεY], hy.2⟩⟩
    · exact ⟨⟨by linarith [hx.1], by linarith [hx.2]⟩, ⟨hy.1, by linarith [hy.2]⟩⟩
  have hCD' : IntegrableOn (planeIntegrandGeneric F (lam : ℂ))
      (Set.Ioc (lam - ε) (lam + ε) ×ˢ Set.Ioc ε Y
        ∪ Set.Ioc (lam - ε) (lam + ε) ×ˢ Set.Ioc (-Y) (-ε)) (volume.prod volume) := by
    refine hcol.mono_set ?_
    rintro p hp
    simp only [Set.mem_prod, Set.mem_union, Set.mem_Ioc] at hp ⊢
    rcases hp with ⟨hx, hy⟩ | ⟨hx, hy⟩
    · exact ⟨⟨hx.1, by linarith [hx.2]⟩, ⟨by linarith [hy.1, hεY], hy.2⟩⟩
    · exact ⟨⟨hx.1, by linarith [hx.2]⟩, ⟨hy.1, by linarith [hy.2]⟩⟩
  have hstep1 : (∫ p in (Set.Ioc (-X) (lam - ε) ×ˢ Set.Ioc (-Y) Y)
        ∪ ((Set.Ioc (lam + ε) X ×ˢ Set.Ioc (-Y) Y)
          ∪ ((Set.Ioc (lam - ε) (lam + ε) ×ˢ Set.Ioc ε Y)
            ∪ (Set.Ioc (lam - ε) (lam + ε) ×ˢ Set.Ioc (-Y) (-ε)))),
        planeIntegrandGeneric F (lam : ℂ) p)
      = (∫ p in Set.Ioc (-X) (lam - ε) ×ˢ Set.Ioc (-Y) Y,
            planeIntegrandGeneric F (lam : ℂ) p)
        + ∫ p in (Set.Ioc (lam + ε) X ×ˢ Set.Ioc (-Y) Y)
          ∪ ((Set.Ioc (lam - ε) (lam + ε) ×ˢ Set.Ioc ε Y)
            ∪ (Set.Ioc (lam - ε) (lam + ε) ×ˢ Set.Ioc (-Y) (-ε))),
            planeIntegrandGeneric F (lam : ℂ) p :=
    setIntegral_union (hAB.union_right (hAC.union_right hAD))
      (by repeat' first
            | apply MeasurableSet.union
            | exact measurableSet_Ioc.prod measurableSet_Ioc)
      (integrableOn_planeIntegrand_generic hF hM (-X) (lam - ε) (-Y) Y) hBCD
  have hstep2 : (∫ p in (Set.Ioc (lam + ε) X ×ˢ Set.Ioc (-Y) Y)
          ∪ ((Set.Ioc (lam - ε) (lam + ε) ×ˢ Set.Ioc ε Y)
            ∪ (Set.Ioc (lam - ε) (lam + ε) ×ˢ Set.Ioc (-Y) (-ε))),
        planeIntegrandGeneric F (lam : ℂ) p)
      = (∫ p in Set.Ioc (lam + ε) X ×ˢ Set.Ioc (-Y) Y,
            planeIntegrandGeneric F (lam : ℂ) p)
        + ∫ p in (Set.Ioc (lam - ε) (lam + ε) ×ˢ Set.Ioc ε Y)
            ∪ (Set.Ioc (lam - ε) (lam + ε) ×ˢ Set.Ioc (-Y) (-ε)),
            planeIntegrandGeneric F (lam : ℂ) p :=
    setIntegral_union (hBC.union_right hBD)
      (by repeat' first
            | apply MeasurableSet.union
            | exact measurableSet_Ioc.prod measurableSet_Ioc)
      (integrableOn_planeIntegrand_generic hF hM (lam + ε) X (-Y) Y) hCD'
  have hstep3 : (∫ p in (Set.Ioc (lam - ε) (lam + ε) ×ˢ Set.Ioc ε Y)
          ∪ (Set.Ioc (lam - ε) (lam + ε) ×ˢ Set.Ioc (-Y) (-ε)),
        planeIntegrandGeneric F (lam : ℂ) p)
      = (∫ p in Set.Ioc (lam - ε) (lam + ε) ×ˢ Set.Ioc ε Y,
            planeIntegrandGeneric F (lam : ℂ) p)
        + ∫ p in Set.Ioc (lam - ε) (lam + ε) ×ˢ Set.Ioc (-Y) (-ε),
            planeIntegrandGeneric F (lam : ℂ) p :=
    setIntegral_union hCD (measurableSet_Ioc.prod measurableSet_Ioc)
      (integrableOn_planeIntegrand_generic hF hM (lam - ε) (lam + ε) ε Y)
      (integrableOn_planeIntegrand_generic hF hM (lam - ε) (lam + ε) (-Y) (-ε))
  rw [show holeSurround lam ε X Y
      = (Set.Ioc (-X) (lam - ε) ×ˢ Set.Ioc (-Y) Y)
        ∪ ((Set.Ioc (lam + ε) X ×ˢ Set.Ioc (-Y) Y)
          ∪ ((Set.Ioc (lam - ε) (lam + ε) ×ˢ Set.Ioc ε Y)
            ∪ (Set.Ioc (lam - ε) (lam + ε) ×ˢ Set.Ioc (-Y) (-ε)))) from rfl,
    hstep1, hstep2, hstep3]
  ring

/-! ## The area limit -/

/-- **Area limit** (generic version): the sum of the four slab integrals converges to the integral
over the big rectangle, the hole integral tending to zero. -/
lemma tendsto_area_hole_generic {F : ℂ → ℂ} (hF : ContDiff ℝ 1 F) {lam X Y M : ℝ}
    (hM : ∀ z : ℂ, ‖pompeiuIntegrand F (lam : ℂ) z‖ ≤ M)
    (hX : |lam| < X) (hY : 2 < Y) :
    Tendsto (fun ε : ℝ =>
        (∫ x : ℝ in -X..lam - ε, ∫ y : ℝ in -Y..Y,
            pompeiuIntegrand F (lam : ℂ) ((x : ℂ) + (y : ℂ) * I))
        + ((∫ x : ℝ in lam + ε..X, ∫ y : ℝ in -Y..Y,
            pompeiuIntegrand F (lam : ℂ) ((x : ℂ) + (y : ℂ) * I))
          + ((∫ x : ℝ in lam - ε..lam + ε, ∫ y : ℝ in ε..Y,
              pompeiuIntegrand F (lam : ℂ) ((x : ℂ) + (y : ℂ) * I))
            + (∫ x : ℝ in lam - ε..lam + ε, ∫ y : ℝ in -Y..-ε,
              pompeiuIntegrand F (lam : ℂ) ((x : ℂ) + (y : ℂ) * I)))))
      (𝓝[>] (0 : ℝ))
      (𝓝 (∫ p in bigRectSet X Y, planeIntegrandGeneric F (lam : ℂ) p)) := by
  have hMnn : 0 ≤ M := le_trans (norm_nonneg _) (hM 0)
  have hlam1 : lam ≤ |lam| := le_abs_self lam
  have hlam2 : -|lam| ≤ lam := neg_abs_le lam
  have hε₀ : 0 < X - |lam| := by
    have := abs_lt.mp hX; linarith [this.2]
  have hhole : Tendsto (fun ε : ℝ => ∫ p in holeSet lam ε, planeIntegrandGeneric F (lam : ℂ) p)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    refine squeeze_zero_norm' (a := fun ε : ℝ => M * (4 * ε ^ 2)) ?_ ?_
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      have hεpos : (0 : ℝ) < ε := hε
      have hfin : (volume.prod volume) (holeSet lam ε) < ⊤ := by
        rw [holeSet, Measure.prod_prod, Real.volume_Ioc, Real.volume_Ioc]
        exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top
      have hle : ‖∫ p in holeSet lam ε, planeIntegrandGeneric F (lam : ℂ) p‖
          ≤ M * (volume.prod volume).real (holeSet lam ε) := by
        refine norm_setIntegral_le_of_norm_le_const hfin ?_
        intro p _
        exact hM _
      have h1 : lam + ε - (lam - ε) = 2 * ε := by ring
      have h2 : ε - -ε = 2 * ε := by ring
      have hvol : (volume.prod volume).real (holeSet lam ε) = 4 * ε ^ 2 := by
        have hdef : (volume.prod volume).real (holeSet lam ε)
            = ((volume.prod volume) (holeSet lam ε)).toReal := rfl
        rw [hdef, holeSet, Measure.prod_prod, Real.volume_Ioc, Real.volume_Ioc, h1, h2,
          ENNReal.toReal_mul, ENNReal.toReal_ofReal (by linarith [hεpos] : (0:ℝ) ≤ 2 * ε)]
        ring
      rw [hvol] at hle
      exact hle
    · have h2 : Tendsto (fun ε : ℝ => (4 : ℝ) * ε ^ 2) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
        have h : Tendsto (fun ε : ℝ => ε) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
          tendsto_id.mono_left nhdsWithin_le_nhds
        simpa using (tendsto_const_nhds.mul (h.pow 2))
      have h3 : Tendsto (fun ε : ℝ => M * (4 * ε ^ 2)) (𝓝[>] (0 : ℝ)) (𝓝 (M * 0)) :=
        h2.const_mul M
      simpa using h3
  have hdec : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
      (∫ x : ℝ in -X..lam - ε, ∫ y : ℝ in -Y..Y,
          pompeiuIntegrand F (lam : ℂ) ((x : ℂ) + (y : ℂ) * I))
        + ((∫ x : ℝ in lam + ε..X, ∫ y : ℝ in -Y..Y,
            pompeiuIntegrand F (lam : ℂ) ((x : ℂ) + (y : ℂ) * I))
          + ((∫ x : ℝ in lam - ε..lam + ε, ∫ y : ℝ in ε..Y,
              pompeiuIntegrand F (lam : ℂ) ((x : ℂ) + (y : ℂ) * I))
            + (∫ x : ℝ in lam - ε..lam + ε, ∫ y : ℝ in -Y..-ε,
              pompeiuIntegrand F (lam : ℂ) ((x : ℂ) + (y : ℂ) * I))))
      = (∫ p in bigRectSet X Y, planeIntegrandGeneric F (lam : ℂ) p)
        - (∫ p in holeSet lam ε, planeIntegrandGeneric F (lam : ℂ) p) := by
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Iio_mem_nhds (show (0:ℝ) < X - |lam| from hε₀)),
      nhdsWithin_le_nhds (Iio_mem_nhds (show (0:ℝ) < 1 from one_pos))] with ε hε hεX hε1
    have hεpos : (0 : ℝ) < ε := hε
    have hεX' : ε < X - |lam| := hεX
    have hε1' : ε < 1 := hε1
    have hεY : ε < Y := by linarith
    have hsurr : (∫ p in holeSurround lam ε X Y, planeIntegrandGeneric F (lam : ℂ) p)
        = (∫ p in Set.Ioc (-X) (lam - ε) ×ˢ Set.Ioc (-Y) Y,
              planeIntegrandGeneric F (lam : ℂ) p)
          + ((∫ p in Set.Ioc (lam + ε) X ×ˢ Set.Ioc (-Y) Y,
              planeIntegrandGeneric F (lam : ℂ) p)
            + ((∫ p in Set.Ioc (lam - ε) (lam + ε) ×ˢ Set.Ioc ε Y,
              planeIntegrandGeneric F (lam : ℂ) p)
              + (∫ p in Set.Ioc (lam - ε) (lam + ε) ×ˢ Set.Ioc (-Y) (-ε),
              planeIntegrandGeneric F (lam : ℂ) p))) := by
      have h := setIntegral_holeSurround_eq_generic hF hM hε hX hεX hεY
      simpa only [add_assoc] using h
    rw [integral_interval_prod_pompeiuIntegrand_generic hF (lam : ℂ) hM
        (by linarith [hεX', hlam2] : -X ≤ lam - ε) (by linarith : -Y ≤ Y),
      integral_interval_prod_pompeiuIntegrand_generic hF (lam : ℂ) hM
        (by linarith [hεX', hlam1] : lam + ε ≤ X) (by linarith : -Y ≤ Y),
      integral_interval_prod_pompeiuIntegrand_generic hF (lam : ℂ) hM
        (by linarith [hεpos] : lam - ε ≤ lam + ε) (by linarith [hεY] : ε ≤ Y),
      integral_interval_prod_pompeiuIntegrand_generic hF (lam : ℂ) hM
        (by linarith [hεpos] : lam - ε ≤ lam + ε) (by linarith [hεY] : -Y ≤ -ε),
      ← hsurr, bigRectSet_eq_holeSurround_union hX hY hε hεX hεY]
    have hdisj : Disjoint (holeSurround lam ε X Y) (holeSet lam ε) := by
      rw [Set.disjoint_left]
      intro p hp hq
      rw [holeSurround] at hp
      simp only [holeSet, Set.mem_prod, Set.mem_union, Set.mem_Ioc] at hp hq
      rcases hp with ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩
      · linarith [hx.1, hx.2, hq.1, hq.2]
      · linarith [hx.1, hx.2, hq.1, hq.2]
      · linarith [hx.1, hx.2, hq.1, hq.2]
      · linarith [hx.1, hx.2, hq.1, hq.2]
    rw [setIntegral_union (f := planeIntegrandGeneric F (lam : ℂ))
      hdisj (measurableSet_holeSet lam ε)
      (by
        have hbig : IntegrableOn (planeIntegrandGeneric F (lam : ℂ))
            (Set.Ioc (-X) X ×ˢ Set.Ioc (-Y) Y) (volume.prod volume) :=
          integrableOn_planeIntegrand_generic hF hM (-X) X (-Y) Y
        refine hbig.mono_set ?_
        intro p hp
        rw [holeSurround] at hp
        simp only [Set.mem_prod, Set.mem_union, Set.mem_Ioc] at hp ⊢
        rcases hp with ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩
        · exact ⟨⟨hx.1, by linarith [hx.2]⟩, hy⟩
        · exact ⟨⟨by linarith [hx.1], hx.2⟩, hy⟩
        · exact ⟨⟨by linarith [hx.1], by linarith [hx.2]⟩, ⟨by linarith [hy.1], hy.2⟩⟩
        · exact ⟨⟨by linarith [hx.1], by linarith [hx.2]⟩, ⟨hy.1, by linarith [hy.2]⟩⟩)
      (integrableOn_planeIntegrand_generic hF hM (lam - ε) (lam + ε) (-ε) ε)]
    ring
  have hlim : Tendsto (fun ε : ℝ => (∫ p in bigRectSet X Y, planeIntegrandGeneric F (lam : ℂ) p)
        - (∫ p in holeSet lam ε, planeIntegrandGeneric F (lam : ℂ) p))
      (𝓝[>] (0 : ℝ)) (𝓝 (∫ p in bigRectSet X Y, planeIntegrandGeneric F (lam : ℂ) p)) := by
    have h := hhole.const_sub (∫ p in bigRectSet X Y, planeIntegrandGeneric F (lam : ℂ) p)
    simpa using h
  exact hlim.congr' (by filter_upwards [hdec] with ε hε; exact hε.symm)

/-! ## Vanishing off the support -/

/-- The generic Cauchy--Pompeiu integrand vanishes off the support of `F`. -/
lemma pompeiuIntegrand_eq_zero_of_notMem_tsupport {F : ℂ → ℂ} {lam z : ℂ}
    (hz : z ∉ tsupport F) : pompeiuIntegrand F lam z = 0 := by
  have hzt : F =ᶠ[𝓝 z] 0 := by
    rw [← notMem_tsupport_iff_eventuallyEq]; exact hz
  have hfd : fderiv ℝ F z = 0 := by
    rw [hzt.fderiv_eq]; simp
  simp [pompeiuIntegrand, hfd]

/-- Points with `|Re z| ≥ X` are outside the support, provided `X` dominates `|Re|` there. -/
lemma notMem_tsupport_of_le_abs_re_generic {F : ℂ → ℂ} {X : ℝ}
    (hXsupp : ∀ z ∈ tsupport F, |z.re| < X) {z : ℂ} (h : X ≤ |z.re|) :
    z ∉ tsupport F := by
  intro hz
  linarith [hXsupp z hz]

/-! ## Global Lipschitz bound for a `C¹` compactly supported function -/

/-- A `C¹` function with compact support is globally Lipschitz (its derivative is continuous and
compactly supported). -/
lemma exists_lipschitz_of_contDiff_one {F : ℂ → ℂ} (hF : ContDiff ℝ 1 F)
    (hsupp : HasCompactSupport F) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z w : ℂ, ‖F z - F w‖ ≤ C * ‖z - w‖ := by
  have hcont : Continuous (fun z : ℂ => fderiv ℝ F z) := hF.continuous_fderiv (by norm_num)
  have hsupp' : HasCompactSupport (fun z : ℂ => fderiv ℝ F z) := by
    refine hsupp.mono' ?_
    intro z hz
    by_contra hzt
    rw [notMem_tsupport_iff_eventuallyEq] at hzt
    apply hz
    show fderiv ℝ F z = 0
    rw [hzt.fderiv_eq]
    simp
  have hK : IsCompact (tsupport (fun z : ℂ => fderiv ℝ F z)) := hsupp'
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hcont.continuousOn
  have hC' : ∀ z : ℂ, ‖fderiv ℝ F z‖ ≤ max C 0 := by
    intro z
    by_cases hz : z ∈ tsupport (fun z : ℂ => fderiv ℝ F z)
    · exact le_trans (hC z hz) (le_max_left _ _)
    · rw [image_eq_zero_of_notMem_tsupport hz]
      simp
  refine ⟨max C 0, le_max_right _ _, fun z w => ?_⟩
  have h := Convex.norm_image_sub_le_of_norm_fderiv_le
    (f := F) (s := Set.univ) (C := max C 0)
    (fun x _ => hF.differentiable (by norm_num) |>.differentiableAt)
    (fun x _ => hC' x) convex_univ (Set.mem_univ z) (Set.mem_univ w)
  simpa [norm_sub_rev] using h

/-! ## The generic plane identity -/

/-- **The generic Cauchy--Pompeiu plane identity.**  For a `C¹` compactly supported `F : ℂ → ℂ`
that agrees with `f : ℝ → ℝ` on the real axis, and whose weighted `∂̄` integrand
`pompeiuIntegrand F lam` is globally bounded, one has

`f lam = (I / 2π) ∫∫ (I • fderiv F z 1 − fderiv F z I) (z − lam)⁻¹`.

Nothing specific to the almost-analytic extension enters: the proof is the Helffer--Sjöstrand
rectangle-with-hole argument, with the residue estimate fed by the Lipschitz bound
`exists_lipschitz_of_contDiff_one` and the vertical truncation by the compact support of `F`. -/
theorem pompeiu_plane_generic {F : ℂ → ℂ} {f : ℝ → ℝ} {lam : ℝ}
    (hFreal : ∀ x : ℝ, F (x : ℂ) = (f x : ℂ))
    (hF1 : ContDiff ℝ 1 F) (hsupp : HasCompactSupport F)
    (hM : ∃ M : ℝ, ∀ z : ℂ, ‖pompeiuIntegrand F (lam : ℂ) z‖ ≤ M) :
    (f lam : ℂ) = (I / (2 * (Real.pi : ℂ))) *
      ∫ p : ℝ × ℝ, planeIntegrandGeneric F (lam : ℂ) p := by
  obtain ⟨M, hM⟩ := hM
  obtain ⟨C, hC, hLipall⟩ := exists_lipschitz_of_contDiff_one hF1 hsupp
  have hFc : Continuous F := hF1.continuous
  -- the horizontal bound `X`
  have hKc : IsCompact (tsupport F) := hsupp
  have hKr : IsCompact (Complex.re '' tsupport F) := hKc.image Complex.continuous_re
  obtain ⟨X₀, hX₀⟩ := hKr.exists_bound_of_continuousOn continuous_id.continuousOn
  set X : ℝ := max X₀ |lam| + 1 with hXdef
  have hX : |lam| < X := by
    rw [hXdef]; have := le_max_right X₀ |lam|; linarith
  have hXpos : (0 : ℝ) < X := by
    rw [hXdef]; have := le_max_right X₀ |lam|; have := abs_nonneg lam; linarith
  have hXsupp : ∀ z ∈ tsupport F, |z.re| < X := by
    intro z hz
    have h1 : ‖z.re‖ ≤ X₀ := hX₀ _ ⟨z, hz, rfl⟩
    have h2 : |z.re| ≤ X₀ := by simpa [Real.norm_eq_abs] using h1
    have h3 : X₀ < X := by
      rw [hXdef]; have := le_max_left X₀ |lam|; linarith
    linarith
  -- the vertical bound `Y`, from compact support
  have hKi : IsCompact (Complex.im '' tsupport F) := hKc.image Complex.continuous_im
  obtain ⟨Y₀, hY₀⟩ := hKi.exists_bound_of_continuousOn continuous_id.continuousOn
  set Y : ℝ := max Y₀ 2 + 1 with hYdef
  have hY : (2 : ℝ) < Y := by
    rw [hYdef]; have := le_max_right Y₀ 2; linarith
  have hYsupp : ∀ z ∈ tsupport F, |z.im| < Y := by
    intro z hz
    have h1 : ‖z.im‖ ≤ Y₀ := hY₀ _ ⟨z, hz, rfl⟩
    have h2 : |z.im| ≤ Y₀ := by simpa [Real.norm_eq_abs] using h1
    have h3 : Y₀ < Y := by
      rw [hYdef]; have := le_max_left Y₀ 2; linarith
    linarith
  -- the two limits
  have hlimB : Tendsto (fun ε : ℝ => rectBoundary
      (fun z => F z / (z - (lam : ℂ)))
      ((lam : ℂ).re - ε) ((lam : ℂ).re + ε) ((lam : ℂ).im - ε) ((lam : ℂ).im + ε))
      (𝓝[>] (0 : ℝ)) (𝓝 (2 * (Real.pi : ℂ) * I * (f lam : ℂ))) := by
    have h := tendsto_boundary_hole (F := F) hFc hC (fun z => hLipall z (lam : ℂ))
    simpa [hFreal lam] using h
  have hlimA := tendsto_area_hole_generic hF1 hM (lam := lam) (X := X) (Y := Y) hX hY
  -- the master identity at every small scale
  have hident : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
      - rectBoundary (fun z => F z / (z - (lam : ℂ)))
          (lam - ε) (lam + ε) (-ε) ε
        = (∫ x : ℝ in -X..lam - ε, ∫ y : ℝ in -Y..Y,
            pompeiuIntegrand F (lam : ℂ) ((x : ℂ) + (y : ℂ) * I))
          + ((∫ x : ℝ in lam + ε..X, ∫ y : ℝ in -Y..Y,
              pompeiuIntegrand F (lam : ℂ) ((x : ℂ) + (y : ℂ) * I))
            + ((∫ x : ℝ in lam - ε..lam + ε, ∫ y : ℝ in ε..Y,
              pompeiuIntegrand F (lam : ℂ) ((x : ℂ) + (y : ℂ) * I))
              + (∫ x : ℝ in lam - ε..lam + ε, ∫ y : ℝ in -Y..-ε,
              pompeiuIntegrand F (lam : ℂ) ((x : ℂ) + (y : ℂ) * I)))) := by
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Iio_mem_nhds (show (0:ℝ) < X - |lam| from by
        have := abs_lt.mp hX; linarith [this.2])),
      nhdsWithin_le_nhds (Iio_mem_nhds (show (0:ℝ) < (1:ℝ) from one_pos)),
      nhdsWithin_le_nhds (Iio_mem_nhds (show (0:ℝ) < Y - 2 from by linarith))] with ε hε hεX hε1 hεY2
    have hεpos : (0 : ℝ) < ε := hε
    have hεX' : ε < X - |lam| := hεX
    have hlam1 : lam ≤ |lam| := le_abs_self lam
    have hlam2 : -|lam| ≤ lam := neg_abs_le lam
    have hεY3 : ε < Y - 2 := hεY2
    -- the boundary functional over the big rectangle vanishes
    have hbnd0 : rectBoundary (fun z => F z / (z - (lam : ℂ)))
        (-X) X (-Y) Y = 0 := by
      have hzero : ∀ z : ℂ, |z.re| ≥ X ∨ |z.im| ≥ Y →
          F z / (z - (lam : ℂ)) = 0 := by
        intro z hz
        have hz0 : F z = 0 := by
          rcases hz with h | h
          · exact image_eq_zero_of_notMem_tsupport
              (notMem_tsupport_of_le_abs_re_generic hXsupp h)
          · exact image_eq_zero_of_notMem_tsupport (fun hmem => by linarith [hYsupp z hmem])
        rw [hz0, zero_div]
      simp only [rectBoundary]
      have h1 : (∫ x : ℝ in -X..X,
          F ((x : ℂ) + ((-Y : ℝ) : ℂ) * I) /
            (((x : ℂ) + ((-Y : ℝ) : ℂ) * I) - (lam : ℂ))) = 0 := by
        rw [show (0 : ℂ) = ∫ x : ℝ in -X..X, (0 : ℂ) from by simp]
        refine intervalIntegral.integral_congr (fun x _ => ?_)
        refine hzero _ (Or.inr ?_)
        have hz : (((x : ℂ) + ((-Y : ℝ) : ℂ) * I)).im = -Y := by simp
        rw [hz, abs_neg, abs_of_nonneg (by linarith : (0:ℝ) ≤ Y)]
      have h2 : (∫ x : ℝ in -X..X,
          F ((x : ℂ) + ((Y : ℝ) : ℂ) * I) /
            (((x : ℂ) + ((Y : ℝ) : ℂ) * I) - (lam : ℂ))) = 0 := by
        rw [show (0 : ℂ) = ∫ x : ℝ in -X..X, (0 : ℂ) from by simp]
        refine intervalIntegral.integral_congr (fun x _ => ?_)
        refine hzero _ (Or.inr ?_)
        have hz : (((x : ℂ) + ((Y : ℝ) : ℂ) * I)).im = Y := by simp
        rw [hz, abs_of_nonneg (by linarith : (0:ℝ) ≤ Y)]
      have h3 : (∫ y : ℝ in -Y..Y,
          F (((X : ℝ) : ℂ) + (y : ℂ) * I) /
            ((((X : ℝ) : ℂ) + (y : ℂ) * I) - (lam : ℂ))) = 0 := by
        rw [show (0 : ℂ) = ∫ y : ℝ in -Y..Y, (0 : ℂ) from by simp]
        refine intervalIntegral.integral_congr (fun y _ => ?_)
        refine hzero _ (Or.inl ?_)
        have hz : ((↑X : ℂ) + ↑y * I).re = X := by simp
        rw [hz, abs_of_nonneg hXpos.le]
      have h4 : (∫ y : ℝ in -Y..Y,
          F (((-X : ℝ) : ℂ) + (y : ℂ) * I) /
            ((((-X : ℝ) : ℂ) + (y : ℂ) * I) - (lam : ℂ))) = 0 := by
        rw [show (0 : ℂ) = ∫ y : ℝ in -Y..Y, (0 : ℂ) from by simp]
        refine intervalIntegral.integral_congr (fun y _ => ?_)
        refine hzero _ (Or.inl ?_)
        have hz : ((↑(-X) : ℂ) + ↑y * I).re = -X := by simp
        rw [hz, abs_of_nonpos (by linarith : (-X : ℝ) ≤ 0)]
        linarith
      rw [h1, h2, h3, h4]
      ring
    -- apply the hole identity
    have hmain := rectBoundary_sub_hole_eq (F := F) hF1
      (a := -X) (b := X) (c := -Y) (d := Y) (lam := (lam : ℂ)) hεpos
      (show -X < (lam : ℂ).re - ε by
        simp only [Complex.ofReal_re]; linarith [hεX', hlam2])
      (show (lam : ℂ).re + ε < X by
        simp only [Complex.ofReal_re]; linarith [hεX', hlam1])
      (show (-Y : ℝ) < (lam : ℂ).im - ε by
        simp only [Complex.ofReal_im]; linarith)
      (show (lam : ℂ).im + ε < Y by
        simp only [Complex.ofReal_im]; linarith)
    rw [hbnd0] at hmain
    simp only [Complex.ofReal_re, Complex.ofReal_im, zero_sub, zero_add] at hmain
    rw [hmain]
    ring
  -- take limits
  have hneg : Tendsto (fun ε : ℝ => - rectBoundary
      (fun z => F z / (z - (lam : ℂ))) (lam - ε) (lam + ε) (-ε) ε)
      (𝓝[>] (0 : ℝ)) (𝓝 (-(2 * (Real.pi : ℂ) * I * (f lam : ℂ)))) := by
    simpa using hlimB.neg
  have hsum : Tendsto (fun ε : ℝ =>
      (∫ x : ℝ in -X..lam - ε, ∫ y : ℝ in -Y..Y,
          pompeiuIntegrand F (lam : ℂ) ((x : ℂ) + (y : ℂ) * I))
        + ((∫ x : ℝ in lam + ε..X, ∫ y : ℝ in -Y..Y,
            pompeiuIntegrand F (lam : ℂ) ((x : ℂ) + (y : ℂ) * I))
          + ((∫ x : ℝ in lam - ε..lam + ε, ∫ y : ℝ in ε..Y,
              pompeiuIntegrand F (lam : ℂ) ((x : ℂ) + (y : ℂ) * I))
            + (∫ x : ℝ in lam - ε..lam + ε, ∫ y : ℝ in -Y..-ε,
              pompeiuIntegrand F (lam : ℂ) ((x : ℂ) + (y : ℂ) * I)))))
      (𝓝[>] (0 : ℝ)) (𝓝 (-(2 * (Real.pi : ℂ) * I * (f lam : ℂ)))) :=
    hneg.congr' (by filter_upwards [hident] with ε hε; exact hε)
  have hval : (-(2 * (Real.pi : ℂ) * I * (f lam : ℂ)))
      = ∫ p in bigRectSet X Y, planeIntegrandGeneric F (lam : ℂ) p :=
    tendsto_nhds_unique hsum hlimA
  -- algebra
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hI : (I : ℂ) ≠ 0 := Complex.I_ne_zero
  have h2pi : (2 * (Real.pi : ℂ)) ≠ 0 := by
    have : (2 : ℂ) ≠ 0 := by norm_num
    exact mul_ne_zero this hpi
  have hkey : (2 * (Real.pi : ℂ) * I) * (f lam : ℂ) =
      - ∫ p in bigRectSet X Y, planeIntegrandGeneric F (lam : ℂ) p := by
    have := hval
    linear_combination -this
  have halg : (f lam : ℂ) = (I / (2 * (Real.pi : ℂ))) *
      (∫ p in bigRectSet X Y, planeIntegrandGeneric F (lam : ℂ) p) := by
    have h1 : (f lam : ℂ) = -(∫ p in bigRectSet X Y, planeIntegrandGeneric F (lam : ℂ) p) /
        (2 * (Real.pi : ℂ) * I) := by
      rw [eq_div_iff (mul_ne_zero h2pi hI)]
      rw [mul_comm (f lam : ℂ) (2 * (Real.pi : ℂ) * I)]
      exact hkey
    rw [h1]
    rw [show -(∫ p in bigRectSet X Y, planeIntegrandGeneric F (lam : ℂ) p) /
        (2 * (Real.pi : ℂ) * I)
        = -(∫ p in bigRectSet X Y, planeIntegrandGeneric F (lam : ℂ) p) *
            (2 * (Real.pi : ℂ) * I)⁻¹ from rfl]
    rw [show (2 * (Real.pi : ℂ) * I)⁻¹ = -I / (2 * (Real.pi : ℂ)) from by
      have hIinv : (I : ℂ)⁻¹ = -I := by
        rw [inv_eq_of_mul_eq_one_right]
        rw [mul_neg, Complex.I_mul_I]
        norm_num
      rw [show (2 * (Real.pi : ℂ) * I) = (2 * (Real.pi : ℂ)) * I from rfl, mul_inv, hIinv,
        div_eq_mul_inv]
      ring]
    ring
  have hconv : (∫ p in bigRectSet X Y, planeIntegrandGeneric F (lam : ℂ) p)
      = ∫ p : ℝ × ℝ, planeIntegrandGeneric F (lam : ℂ) p := by
    -- the plane integrand vanishes off the big rectangle
    refine setIntegral_eq_integral_of_forall_compl_eq_zero (fun p hp => ?_)
    rw [bigRectSet, Set.mem_prod] at hp
    have hznot : ((p.1 : ℂ) + (p.2 : ℂ) * I) ∉ tsupport F := by
      rcases not_and_or.mp hp with h | h
      · rw [Set.mem_Ioc, not_and_or] at h
        rcases h with h | h
        · rw [not_lt] at h
          refine notMem_tsupport_of_le_abs_re_generic hXsupp ?_
          rw [show (((p.1 : ℂ) + (p.2 : ℂ) * I)).re = p.1 from by simp,
            abs_of_nonpos (by linarith)]
          linarith
        · rw [not_le] at h
          refine notMem_tsupport_of_le_abs_re_generic hXsupp ?_
          rw [show (((p.1 : ℂ) + (p.2 : ℂ) * I)).re = p.1 from by simp,
            abs_of_pos (by linarith)]
          linarith
      · rw [Set.mem_Ioc, not_and_or] at h
        rcases h with h | h
        · rw [not_lt] at h
          refine fun hmem => ?_
          have him : Y ≤ |(((p.1 : ℂ) + (p.2 : ℂ) * I)).im| := by
            rw [show (((p.1 : ℂ) + (p.2 : ℂ) * I)).im = p.2 from by simp,
              abs_of_nonpos (by linarith)]
            linarith
          linarith [hYsupp _ hmem]
        · rw [not_le] at h
          refine fun hmem => ?_
          have him : Y ≤ |(((p.1 : ℂ) + (p.2 : ℂ) * I)).im| := by
            rw [show (((p.1 : ℂ) + (p.2 : ℂ) * I)).im = p.2 from by simp,
              abs_of_pos (by linarith)]
            linarith
          linarith [hYsupp _ hmem]
    exact pompeiuIntegrand_eq_zero_of_notMem_tsupport hznot
  rw [halg, hconv]


/-- **Consistency check: the first-order `pompeiu_plane` is the `k = 1` case.**  The generic
identity reproduces the original first-order plane representation of
`Probability/HelfferSjostrand.lean` (whose proof is untouched). -/
theorem pompeiu_plane_of_generic {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (lam : ℝ) :
    (f lam : ℂ) = (I / (2 * (Real.pi : ℂ))) *
      ∫ p : ℝ × ℝ, planeIntegrandGeneric (almostAnalyticExtCut f) (lam : ℂ) p :=
  pompeiu_plane_generic (lam := lam)
    (fun x => almostAnalyticExtCut_ofReal f x)
    (contDiff_almostAnalyticExtCut_one hf)
    (hasCompactSupport_almostAnalyticExtCut hfc)
    (exists_norm_pompeiuIntegrand_le hf hfc lam)

/-! ## The order-`k` cut-off extension -/

/-- Off the strip `|Im z| ≤ 2` the cut-off order-`k` extension vanishes. -/
lemma almostAnalyticExtOrderCut_eq_zero_of_two_le_abs_im {f : ℝ → ℝ} {k : ℕ} {z : ℂ}
    (h : 2 ≤ |z.im|) : almostAnalyticExtOrderCut k f z = 0 := by
  rw [almostAnalyticExtOrderCut, yCut_zero_of_two_le h, Complex.ofReal_zero, mul_zero]

/-- Points with `|Im z| > 2` are not in the support of the cut-off order-`k` extension. -/
lemma notMem_tsupport_almostAnalyticExtOrderCut_of_lt_abs_im {f : ℝ → ℝ} {k : ℕ} {z : ℂ}
    (h : 2 < |z.im|) : z ∉ tsupport (almostAnalyticExtOrderCut k f) := by
  rw [notMem_tsupport_iff_eventuallyEq]
  filter_upwards [((Complex.continuous_im.abs).continuousAt.eventually (Ioi_mem_nhds h))] with w hw
  exact almostAnalyticExtOrderCut_eq_zero_of_two_le_abs_im (le_of_lt hw)

/-- A bound on the `k`-th iterated derivative of a compactly supported `C^k` function. -/
lemma exists_norm_iteratedDeriv_le {f : ℝ → ℝ} {k K : ℕ} (hf : ContDiff ℝ K f) (hK : k ≤ K)
    (hfc : HasCompactSupport f) : ∃ M, ∀ x : ℝ, ‖iteratedDeriv k f x‖ ≤ M := by
  have hcont : Continuous (iteratedDeriv k f) :=
    ContDiff.continuous_iteratedDeriv k hf (by exact_mod_cast hK)
  have hsupp : HasCompactSupport (iteratedDeriv k f) :=
    hfc.mono' (subset_trans (subset_tsupport (iteratedDeriv k f)) (tsupport_iteratedDeriv_subset k))
  have hKc : IsCompact (tsupport (iteratedDeriv k f)) := hsupp
  obtain ⟨M, hM⟩ := hKc.exists_bound_of_continuousOn hcont.continuousOn
  refine ⟨max M 0, fun x => ?_⟩
  by_cases hx : x ∈ tsupport (iteratedDeriv k f)
  · exact le_trans (hM x hx) (le_max_left _ _)
  · rw [image_eq_zero_of_notMem_tsupport hx, norm_zero]
    exact le_max_right _ _

/-- The cut-off order-`k` extension is `C¹` for `k ≥ 1` and `f` of class `C^k`. -/
lemma contDiff_almostAnalyticExtOrderCut_one' {f : ℝ → ℝ} {k K : ℕ} (hk : 1 ≤ k)
    (hf : ContDiff ℝ K f) (hK : k ≤ K) : ContDiff ℝ 1 (almostAnalyticExtOrderCut k f) := by
  have hk0 : k ≠ 0 := by omega
  have hk' : (k - 1) + 1 ≤ K := by omega
  simpa [Nat.sub_one_add_one hk0] using
    contDiff_almostAnalyticExtOrderCut_one (f := f) (k := k - 1) (K := K) hf hk'

/-- **Global boundedness of the order-`k` Cauchy--Pompeiu integrand** for `k ≥ 2`: on the strip
`|Im z| < 1` the `|Im z|^{k-1}` vanishing beats the `|Im z|⁻¹` of the resolvent, and off the
strip the global `∂̄` bound is divided by `|Im z| ≥ 1`. -/
lemma exists_norm_pompeiuIntegrandOrder_le {f : ℝ → ℝ} {k K : ℕ} (hk : 2 ≤ k)
    (hf : ContDiff ℝ K f) (hK : k ≤ K) (hfc : HasCompactSupport f) (lam : ℝ) :
    ∃ M : ℝ, ∀ z : ℂ,
      ‖pompeiuIntegrand (almostAnalyticExtOrderCut k f) (lam : ℂ) z‖ ≤ M := by
  have hk0 : k ≠ 0 := by omega
  have hk1 : k - 1 ≠ 0 := by omega
  have hk' : (k - 1) + 1 ≤ K := by omega
  obtain ⟨B, hB0, hB⟩ := exists_norm_dbarNumOrder_le (f := f) (k := k - 1) (K := K) hf hk' hfc
  have hB' : ∀ z : ℂ, ‖dbarNumOrder k f z‖ ≤ B := by
    intro z
    simpa [Nat.sub_one_add_one hk0] using hB z
  obtain ⟨M₂, hM₂⟩ := exists_norm_iteratedDeriv_le (k := k) hf hK hfc
  have hfac : (0 : ℝ) < ((k - 1).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos (k - 1)
  have hM₂0 : 0 ≤ M₂ := le_trans (norm_nonneg _) (hM₂ 0)
  set M : ℝ := max B (M₂ / ((k - 1).factorial : ℝ)) with hMdef
  have hMn : M₂ / ((k - 1).factorial : ℝ) ≤ M := le_max_right _ _
  have hBM : B ≤ M := le_max_left _ _
  have hM0 : 0 ≤ M := le_trans (div_nonneg hM₂0 hfac.le) (le_max_right _ _)
  refine ⟨M, fun z => ?_⟩
  have hdeneq : (z - (lam : ℂ)).im = z.im := by simp
  have hden : |z.im| ≤ ‖z - (lam : ℂ)‖ := by
    calc |z.im| = |(z - (lam : ℂ)).im| := by rw [hdeneq]
      _ ≤ ‖z - (lam : ℂ)‖ := Complex.abs_im_le_norm _
  rcases lt_or_ge |z.im| 1 with h1 | h1
  · -- inner strip: use the vanishing of `∂̄`
    have hnum := norm_dbar_almostAnalyticExtOrderCut_le (f := f) (k := k - 1) (K := K) hf hk'
      (z := z) h1 (M := M₂) (fun x => by simpa [Nat.sub_one_add_one hk0] using hM₂ x)
    have hnum' : ‖I • fderiv ℝ (almostAnalyticExtOrderCut k f) z 1
        - fderiv ℝ (almostAnalyticExtOrderCut k f) z I‖
          ≤ |z.im| ^ (k - 1) / ((k - 1).factorial : ℝ) * M₂ := by
      simpa [Nat.sub_one_add_one hk0] using hnum
    rcases eq_or_ne z.im 0 with h0 | h0
    · have hzero : ‖I • fderiv ℝ (almostAnalyticExtOrderCut k f) z 1
          - fderiv ℝ (almostAnalyticExtOrderCut k f) z I‖ = 0 := by
        have := hnum'
        rw [h0, abs_zero, zero_pow hk1, zero_div, zero_mul] at this
        exact le_antisymm this (norm_nonneg _)
      rw [pompeiuIntegrand,
        show I • fderiv ℝ (almostAnalyticExtOrderCut k f) z 1
            - fderiv ℝ (almostAnalyticExtOrderCut k f) z I = 0 from
          norm_eq_zero.mp hzero]
      simp only [zero_mul, norm_zero]
      exact hM0
    · have hypos : 0 < |z.im| := abs_pos.mpr h0
      have hy1 : |z.im| ≤ 1 := le_of_lt h1
      have hzneq : z - (lam : ℂ) ≠ 0 := by
        intro h
        exact h0 (by rw [sub_eq_zero.mp h]; simp)
      have hnormpos : 0 < ‖z - (lam : ℂ)‖ := norm_pos_iff.mpr hzneq
      have hinv : ‖(z - (lam : ℂ))⁻¹‖ ≤ (|z.im|)⁻¹ := by
        rw [norm_inv]
        exact (inv_le_inv₀ hnormpos hypos).mpr hden
      have hyk : |z.im| ^ (k - 1) ≤ |z.im| := by
        simpa using pow_le_of_le_one (abs_nonneg z.im) hy1 hk1
      have hcomb : |z.im| ^ (k - 1) * (|z.im|)⁻¹ ≤ 1 := by
        rw [← div_eq_mul_inv]
        exact (div_le_one hypos).mpr hyk
      calc ‖pompeiuIntegrand (almostAnalyticExtOrderCut k f) (lam : ℂ) z‖
          = ‖I • fderiv ℝ (almostAnalyticExtOrderCut k f) z 1
              - fderiv ℝ (almostAnalyticExtOrderCut k f) z I‖
            * ‖(z - (lam : ℂ))⁻¹‖ := by
            rw [pompeiuIntegrand, norm_mul]
        _ ≤ (|z.im| ^ (k - 1) / ((k - 1).factorial : ℝ) * M₂) * (|z.im|)⁻¹ :=
            mul_le_mul hnum' hinv (norm_nonneg _)
              (by positivity)
        _ = (|z.im| ^ (k - 1) * (|z.im|)⁻¹) * (M₂ / ((k - 1).factorial : ℝ)) := by ring
        _ ≤ 1 * (M₂ / ((k - 1).factorial : ℝ)) := by
            exact mul_le_mul_of_nonneg_right hcomb (by positivity)
        _ = M₂ / ((k - 1).factorial : ℝ) := one_mul _
        _ ≤ M := hMn
  · -- off the strip: use the global `∂̄` bound
    have hnum : ‖I • fderiv ℝ (almostAnalyticExtOrderCut k f) z 1
        - fderiv ℝ (almostAnalyticExtOrderCut k f) z I‖ ≤ B := by
      have := hB' z
      simpa [dbarNumOrder] using this
    have hnormpos : 0 < ‖z - (lam : ℂ)‖ := by
      refine norm_pos_iff.mpr (sub_ne_zero.mpr ?_)
      intro h'
      have him0 : z.im = 0 := by rw [h']; simp
      rw [him0, abs_zero] at h1
      linarith
    have hinv : ‖(z - (lam : ℂ))⁻¹‖ ≤ 1 := by
      rw [norm_inv]
      refine inv_le_one_of_one_le₀ ?_
      linarith
    calc ‖pompeiuIntegrand (almostAnalyticExtOrderCut k f) (lam : ℂ) z‖
        = ‖I • fderiv ℝ (almostAnalyticExtOrderCut k f) z 1
            - fderiv ℝ (almostAnalyticExtOrderCut k f) z I‖
          * ‖(z - (lam : ℂ))⁻¹‖ := by
          rw [pompeiuIntegrand, norm_mul]
      _ ≤ B * 1 := mul_le_mul hnum hinv (norm_nonneg _) hB0
      _ = B := mul_one _
      _ ≤ M := hBM

/-- **The order-`k` Cauchy--Pompeiu plane identity** (`k ≥ 2`, `f` of class `C^k` with compact
support): `∂̄` of the cut-off order-`k` extension vanishes to order `k-1` at the real axis. -/
theorem pompeiu_plane_order {f : ℝ → ℝ} {k K : ℕ} (hk : 2 ≤ k) (hf : ContDiff ℝ K f)
    (hK : k ≤ K) (hfc : HasCompactSupport f) (lam : ℝ) :
    (f lam : ℂ) = (I / (2 * (Real.pi : ℂ))) *
      ∫ p : ℝ × ℝ, planeIntegrandGeneric (almostAnalyticExtOrderCut k f) (lam : ℂ) p := by
  exact pompeiu_plane_generic (lam := lam)
    (fun x => almostAnalyticExtOrderCut_ofReal k (by omega : 1 ≤ k) f x)
    (contDiff_almostAnalyticExtOrderCut_one' (by omega) hf hK)
    (hasCompactSupport_almostAnalyticExtOrderCut (k := k) hfc)
    (exists_norm_pompeiuIntegrandOrder_le hk hf hK hfc lam)

/-- The order-`k` plane identity in the explicit `dbarNumOrder` form. -/
theorem pompeiu_plane_order_dbarNum {f : ℝ → ℝ} {k K : ℕ} (hk : 2 ≤ k) (hf : ContDiff ℝ K f)
    (hK : k ≤ K) (hfc : HasCompactSupport f) (lam : ℝ) :
    (f lam : ℂ) = (I / (2 * (Real.pi : ℂ))) *
      ∫ p : ℝ × ℝ, dbarNumOrder k f ((p.1 : ℂ) + (p.2 : ℂ) * I)
        * (((p.1 : ℂ) + (p.2 : ℂ) * I) - (lam : ℂ))⁻¹ :=
  pompeiu_plane_order hk hf hK hfc lam

/-- **The order-6 plane identity**: `∂̄` of `almostAnalyticExtOrderCut 6 f` is `O(|Im z|⁵)`. -/
theorem pompeiu_plane_order_six {f : ℝ → ℝ} (hf : ContDiff ℝ 6 f) (hfc : HasCompactSupport f)
    (lam : ℝ) :
    (f lam : ℂ) = (I / (2 * (Real.pi : ℂ))) *
      ∫ p : ℝ × ℝ, planeIntegrandGeneric (almostAnalyticExtOrderCut 6 f) (lam : ℂ) p :=
  pompeiu_plane_order (k := 6) (K := 6) (by norm_num) hf le_rfl hfc lam

/-- The order-6 plane identity in the explicit `dbarNumOrder` form. -/
theorem pompeiu_plane_order_six_dbarNum {f : ℝ → ℝ} (hf : ContDiff ℝ 6 f)
    (hfc : HasCompactSupport f) (lam : ℝ) :
    (f lam : ℂ) = (I / (2 * (Real.pi : ℂ))) *
      ∫ p : ℝ × ℝ, dbarNumOrder 6 f ((p.1 : ℂ) + (p.2 : ℂ) * I)
        * (((p.1 : ℂ) + (p.2 : ℂ) * I) - (lam : ℂ))⁻¹ :=
  pompeiu_plane_order_dbarNum (k := 6) (K := 6) (by norm_num) hf le_rfl hfc lam

/-! ## Integrability of the generic plane integrand on the whole plane -/

/-- The generic plane integrand vanishes outside any rectangle containing the support. -/
lemma planeIntegrandGeneric_eq_zero_of_not_mem_rect {F : ℂ → ℂ} {X Y : ℝ}
    (hXpos : 0 < X) (hYpos : 0 < Y)
    (hXsupp : ∀ z ∈ tsupport F, |z.re| < X) (hYsupp : ∀ z ∈ tsupport F, |z.im| < Y)
    {p : ℝ × ℝ} (hp : p ∉ Set.Ioc (-X) X ×ˢ Set.Ioc (-Y) Y) (lam : ℂ) :
    planeIntegrandGeneric F lam p = 0 := by
  rw [Set.mem_prod] at hp
  have hznot : ((p.1 : ℂ) + (p.2 : ℂ) * I) ∉ tsupport F := by
    rcases not_and_or.mp hp with h | h
    · rw [Set.mem_Ioc, not_and_or] at h
      rcases h with h | h
      · rw [not_lt] at h
        refine notMem_tsupport_of_le_abs_re_generic hXsupp ?_
        rw [show (((p.1 : ℂ) + (p.2 : ℂ) * I)).re = p.1 from by simp,
          abs_of_nonpos (by linarith)]
        linarith
      · rw [not_le] at h
        refine notMem_tsupport_of_le_abs_re_generic hXsupp ?_
        rw [show (((p.1 : ℂ) + (p.2 : ℂ) * I)).re = p.1 from by simp,
          abs_of_pos (by linarith)]
        linarith
    · rw [Set.mem_Ioc, not_and_or] at h
      rcases h with h | h
      · rw [not_lt] at h
        refine fun hmem => ?_
        have him : Y ≤ |(((p.1 : ℂ) + (p.2 : ℂ) * I)).im| := by
          rw [show (((p.1 : ℂ) + (p.2 : ℂ) * I)).im = p.2 from by simp,
            abs_of_nonpos (by linarith)]
          linarith
        linarith [hYsupp _ hmem]
      · rw [not_le] at h
        refine fun hmem => ?_
        have him : Y ≤ |(((p.1 : ℂ) + (p.2 : ℂ) * I)).im| := by
          rw [show (((p.1 : ℂ) + (p.2 : ℂ) * I)).im = p.2 from by simp,
            abs_of_pos (by linarith)]
          linarith
        linarith [hYsupp _ hmem]
  exact pompeiuIntegrand_eq_zero_of_notMem_tsupport hznot

/-- The generic plane integrand is integrable on `ℝ × ℝ`. -/
lemma integrable_planeIntegrandGeneric {F : ℂ → ℂ} (hF : ContDiff ℝ 1 F)
    (hsupp : HasCompactSupport F) {lam : ℂ} {M : ℝ}
    (hM : ∀ z : ℂ, ‖pompeiuIntegrand F lam z‖ ≤ M) :
    Integrable (planeIntegrandGeneric F lam) (volume : Measure (ℝ × ℝ)) := by
  classical
  obtain ⟨X, hXpos, hXsupp⟩ : ∃ X : ℝ, 0 < X ∧
      ∀ z ∈ tsupport F, |z.re| < X := by
    have hKc : IsCompact (tsupport F) := hsupp
    have hKr : IsCompact (Complex.re '' tsupport F) := hKc.image Complex.continuous_re
    obtain ⟨X₀, hX₀⟩ := hKr.exists_bound_of_continuousOn continuous_id.continuousOn
    refine ⟨max X₀ 0 + 1, by have := le_max_right X₀ 0; linarith, fun z hz => ?_⟩
    have h1 : ‖z.re‖ ≤ X₀ := hX₀ _ ⟨z, hz, rfl⟩
    have h2 : |z.re| ≤ X₀ := by simpa [Real.norm_eq_abs] using h1
    have h3 : X₀ ≤ max X₀ 0 := le_max_left _ _
    linarith
  obtain ⟨Y, hYpos, hYsupp⟩ : ∃ Y : ℝ, 0 < Y ∧
      ∀ z ∈ tsupport F, |z.im| < Y := by
    have hKc : IsCompact (tsupport F) := hsupp
    have hKi : IsCompact (Complex.im '' tsupport F) := hKc.image Complex.continuous_im
    obtain ⟨Y₀, hY₀⟩ := hKi.exists_bound_of_continuousOn continuous_id.continuousOn
    refine ⟨max Y₀ 0 + 1, by have := le_max_right Y₀ 0; linarith, fun z hz => ?_⟩
    have h1 : ‖z.im‖ ≤ Y₀ := hY₀ _ ⟨z, hz, rfl⟩
    have h2 : |z.im| ≤ Y₀ := by simpa [Real.norm_eq_abs] using h1
    have h3 : Y₀ ≤ max Y₀ 0 := le_max_left _ _
    linarith
  set R : Set (ℝ × ℝ) := Set.Ioc (-X) X ×ˢ Set.Ioc (-Y) Y with hR
  have hmeas : MeasurableSet R := measurableSet_Ioc.prod measurableSet_Ioc
  have hrect : IntegrableOn (planeIntegrandGeneric F lam) R (volume : Measure (ℝ × ℝ)) :=
    integrableOn_planeIntegrand_generic hF hM (-X) X (-Y) Y
  have hcompl : IntegrableOn (planeIntegrandGeneric F lam) Rᶜ
      (volume : Measure (ℝ × ℝ)) := by
    have hae : planeIntegrandGeneric F lam =ᵐ[volume.restrict Rᶜ] (0 : ℝ × ℝ → ℂ) := by
      filter_upwards [ae_restrict_mem hmeas.compl] with p hp
      exact planeIntegrandGeneric_eq_zero_of_not_mem_rect hXpos hYpos hXsupp hYsupp hp lam
    exact (integrable_zero (α := ℝ × ℝ) ℂ _).congr hae.symm
  have hunion : IntegrableOn (planeIntegrandGeneric F lam) (R ∪ Rᶜ)
      (volume : Measure (ℝ × ℝ)) :=
    hrect.union hcompl
  rwa [Set.union_compl_self, integrableOn_univ] at hunion

/-- The two-dimensional plane integral of the generic integrand is the iterated one. -/
lemma integral_planeIntegrandGeneric_eq_iterated {F : ℂ → ℂ} (hF : ContDiff ℝ 1 F)
    (hsupp : HasCompactSupport F) {lam : ℂ} {M : ℝ}
    (hM : ∀ z : ℂ, ‖pompeiuIntegrand F lam z‖ ≤ M) :
    (∫ p : ℝ × ℝ, planeIntegrandGeneric F lam p)
      = ∫ x : ℝ, ∫ y : ℝ, pompeiuIntegrand F lam ((x : ℂ) + (y : ℂ) * I) := by
  rw [show (volume : Measure (ℝ × ℝ)) = (volume : Measure ℝ).prod (volume : Measure ℝ) from rfl]
  rw [integral_prod]
  exact integrable_planeIntegrandGeneric hF hsupp hM

/-! ## The order-`k` plane integrand on the whole plane -/

/-- The order-`k` plane integrand is integrable on the whole plane (`k ≥ 2`). -/
lemma integrable_planeIntegrandOrder {f : ℝ → ℝ} {k K : ℕ} (hk : 2 ≤ k) (hf : ContDiff ℝ K f)
    (hK : k ≤ K) (hfc : HasCompactSupport f) (lam : ℝ) :
    Integrable (planeIntegrandGeneric (almostAnalyticExtOrderCut k f) (lam : ℂ))
      (volume : Measure (ℝ × ℝ)) := by
  obtain ⟨M, hM⟩ := exists_norm_pompeiuIntegrandOrder_le hk hf hK hfc lam
  exact integrable_planeIntegrandGeneric
    (contDiff_almostAnalyticExtOrderCut_one' (by omega) hf hK)
    (hasCompactSupport_almostAnalyticExtOrderCut (k := k) hfc) hM

/-- The two-dimensional order-`k` plane integral is the iterated one. -/
lemma integral_planeIntegrandOrder_eq_iterated {f : ℝ → ℝ} {k K : ℕ} (hk : 2 ≤ k)
    (hf : ContDiff ℝ K f) (hK : k ≤ K) (hfc : HasCompactSupport f) (lam : ℝ) :
    (∫ p : ℝ × ℝ, planeIntegrandGeneric (almostAnalyticExtOrderCut k f) (lam : ℂ) p)
      = ∫ x : ℝ, ∫ y : ℝ,
          pompeiuIntegrand (almostAnalyticExtOrderCut k f) (lam : ℂ) ((x : ℂ) + (y : ℂ) * I) := by
  obtain ⟨M, hM⟩ := exists_norm_pompeiuIntegrandOrder_le hk hf hK hfc lam
  exact integral_planeIntegrandGeneric_eq_iterated
    (contDiff_almostAnalyticExtOrderCut_one' (by omega) hf hK)
    (hasCompactSupport_almostAnalyticExtOrderCut (k := k) hfc) hM

/-! ## The trace/operator form of the order-`k` representation -/

/-- **Trace form of the order-`k` Cauchy--Pompeiu representation.**  Summing
`pompeiu_plane_order` over the eigenvalues of a Hermitian matrix gives
`Tr(f(H)) = (I/2π) ∫∫ ∂̄_k f(z) · Tr((z - H)⁻¹)`. -/
theorem trace_cfc_eq_plane_integral_order {n : Type*} [Fintype n] [DecidableEq n]
    (H : Matrix n n ℂ) (hH : H.IsHermitian) {f : ℝ → ℝ} {k K : ℕ} (hk : 2 ≤ k)
    (hf : ContDiff ℝ K f) (hK : k ≤ K) (hfc : HasCompactSupport f) :
    (hH.cfc f).trace =
      (I / (2 * (Real.pi : ℂ))) *
        ∫ p : ℝ × ℝ,
          dbarNumOrder k f ((p.1 : ℂ) + (p.2 : ℂ) * I) *
            resolventTrace H hH ((p.1 : ℂ) + (p.2 : ℂ) * I) := by
  classical
  rw [trace_cfc_eq_sum_eigenvalues_general H hH f]
  have hlam : ∀ i : n, ((f (hH.eigenvalues i) : ℝ) : ℂ) =
      (I / (2 * (Real.pi : ℂ))) *
        ∫ p : ℝ × ℝ,
          planeIntegrandGeneric (almostAnalyticExtOrderCut k f)
            (((hH.eigenvalues i : ℝ)) : ℂ) p :=
    fun i => pompeiu_plane_order hk hf hK hfc (hH.eigenvalues i)
  rw [Finset.sum_congr rfl (fun i _ => hlam i)]
  rw [← Finset.mul_sum]
  congr 1
  have hswap : (∑ i : n, ∫ p : ℝ × ℝ,
        planeIntegrandGeneric (almostAnalyticExtOrderCut k f)
          (((hH.eigenvalues i : ℝ)) : ℂ) p)
      = ∫ p : ℝ × ℝ, ∑ i : n,
          planeIntegrandGeneric (almostAnalyticExtOrderCut k f)
            (((hH.eigenvalues i : ℝ)) : ℂ) p := by
    rw [MeasureTheory.integral_finsetSum]
    intro i _
    exact integrable_planeIntegrandOrder hk hf hK hfc (hH.eigenvalues i)
  rw [hswap]
  refine integral_congr_ae ?_
  filter_upwards [ae_not_eigenvalue H hH] with p hne
  rw [resolventTrace, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rfl

/-- **Trace form with the matrix resolvent, order `k`.**
`Tr(f(H)) = (i/2π) ∫∫ ∂̄_k f(z) Tr((z - H)⁻¹)`. -/
theorem trace_cfc_eq_plane_integral_resolvent_order {n : Type*} [Fintype n] [DecidableEq n]
    (H : Matrix n n ℂ) (hH : H.IsHermitian) {f : ℝ → ℝ} {k K : ℕ} (hk : 2 ≤ k)
    (hf : ContDiff ℝ K f) (hK : k ≤ K) (hfc : HasCompactSupport f) :
    (hH.cfc f).trace =
      (I / (2 * (Real.pi : ℂ))) *
        ∫ p : ℝ × ℝ,
          dbarNumOrder k f ((p.1 : ℂ) + (p.2 : ℂ) * I) *
            Matrix.trace ((((p.1 : ℂ) + (p.2 : ℂ) * I)) • (1 : Matrix n n ℂ) - H)⁻¹ := by
  rw [trace_cfc_eq_plane_integral_order H hH hk hf hK hfc]
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [ae_not_eigenvalue H hH] with p hne
  rw [resolventTrace_eq_trace_inv H hH _ (fun i => hne i)]


/-! ## The mean-level identity for the order-`k` extension

The order-`k` analogue of `integral_gueStatisticCfc_eq_plane_integral'`: the mean of
`τ_N(f(H_N))` is `(card d)⁻¹` times the real part of the plane integral of `∂̄_k f` against the
trace of the averaged partial-trace resolvent `g_N`.  The analytic input is the order-`k` trace
identity `trace_cfc_eq_plane_integral_resolvent_order`; the Fubini step is the same as in
`Probability/LemmaMSmooth.lean`, with the weight `‖∂̄_k f‖ ≤ |Im z|^k/k! · M` replacing
`‖∂̄F‖ ≤ |Im z| · M`.
-/

section MeanIdentity

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- `∂̄_k` vanishes on the real axis for `k ≥ 2`. -/
lemma dbarNumOrder_succ_ofReal {f : ℝ → ℝ} {k K : ℕ} (hk : 1 ≤ k) (hf : ContDiff ℝ K f)
    (hK : k + 1 ≤ K) (x : ℝ) : dbarNumOrder (k + 1) f (x : ℂ) = 0 := by
  have hk0 : k ≠ 0 := by omega
  have hderiv : deriv yCut (0 : ℝ) = 0 := by
    have hmem : (0 : ℝ) ∈ Metric.ball (0 : ℝ) yBump.rIn := by
      have h1 : yBump.rIn = 1 := rfl
      rw [h1, Real.ball_zero_eq_Ioo]; norm_num
    have h1 : yCut =ᶠ[𝓝 (0 : ℝ)] 1 := by
      simpa [yCut] using ContDiffBump.eventuallyEq_one_of_mem_ball (f := yBump) hmem
    rw [Filter.EventuallyEq.deriv_eq h1]
    simp
  rw [dbarNumOrder, dbar_almostAnalyticExtOrderCut (f := f) hf hK]
  simp only [Complex.ofReal_im, hderiv, Complex.ofReal_zero, zero_mul, sub_zero]
  rw [show (I * ((0 : ℂ))) = 0 from by simp]
  simp [zero_pow hk0]

/-- **Joint measurability of the order-`k` plane integrand.** -/
lemma measurable_uncurry_planeIntegrand_order
    {Ω : Type*} [MeasurableSpace Ω]
    (H : Ω → Matrix n n ℂ) (hHm : Measurable H) {f : ℝ → ℝ} {k K : ℕ}
    (hf : ContDiff ℝ K f) (hK : k + 1 ≤ K) :
    Measurable (Function.uncurry fun ω (p : ℝ × ℝ) =>
      dbarNumOrder (k + 1) f (zOf p) * Matrix.trace ((zOf p) • (1 : Matrix n n ℂ) - H ω)⁻¹) := by
  have hz_meas : Measurable (fun q : Ω × (ℝ × ℝ) => zOf q.2) :=
    continuous_zOf.measurable.comp measurable_snd
  have hmat : Measurable (fun q : Ω × (ℝ × ℝ) =>
      (zOf q.2) • (1 : Matrix n n ℂ) - H q.1) := by
    refine Matrix.measurable_iff.mpr (fun a b => ?_)
    have hentry : ∀ q : Ω × (ℝ × ℝ),
        ((zOf q.2) • (1 : Matrix n n ℂ) - H q.1) a b
          = (if a = b then zOf q.2 else 0) - H q.1 a b := by
      intro q
      rw [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
      by_cases hab : a = b <;> simp [hab]
    simp only [hentry]
    refine Measurable.sub ?_ ?_
    · by_cases hab : a = b
      · simp only [hab, ite_true]; exact hz_meas
      · simp only [hab, ite_false]; exact measurable_const
    · exact Matrix.measurable_apply.comp (hHm.comp measurable_fst)
  have hmeas_inner : Measurable (fun q : Ω × (ℝ × ℝ) =>
      Matrix.trace ((zOf q.2) • (1 : Matrix n n ℂ) - H q.1)⁻¹) :=
    measurable_matrix_trace.comp (measurable_matrix_inv.comp hmat)
  have h2 : Measurable (fun q : Ω × (ℝ × ℝ) => dbarNumOrder (k + 1) f (zOf q.2)) :=
    (continuous_dbarNumOrder hf hK).measurable.comp hz_meas
  exact h2.mul hmeas_inner

/-- **Finite-side Cauchy--Pompeiu trace identity, order `k`.** -/
theorem integral_trace_cfc_eq_plane_integral_order
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (H : Ω → Matrix n n ℂ) (hH : ∀ ω, (H ω).IsHermitian) (hHm : Measurable H)
    {f : ℝ → ℝ} {k K : ℕ} (hk : 1 ≤ k) (hf : ContDiff ℝ K f) (hK : k + 1 ≤ K)
    (hfc : HasCompactSupport f) :
    ∫ ω, (cfc f (H ω)).trace ∂μ =
      (I / (2 * (Real.pi : ℂ))) *
        ∫ p : ℝ × ℝ, dbarNumOrder (k + 1) f (zOf p) *
          (∫ ω, Matrix.trace ((zOf p) • (1 : Matrix n n ℂ) - H ω)⁻¹ ∂μ) := by
  classical
  have hpt : ∀ ω, (cfc f (H ω)).trace =
      (I / (2 * (Real.pi : ℂ))) * ∫ p : ℝ × ℝ,
        dbarNumOrder (k + 1) f (zOf p) *
          Matrix.trace ((zOf p) • (1 : Matrix n n ℂ) - H ω)⁻¹ := by
    intro ω
    rw [Matrix.IsHermitian.cfc_eq (hH ω) f]
    exact trace_cfc_eq_plane_integral_resolvent_order (H ω) (hH ω) (k := k + 1) (K := K)
      (by omega) hf hK hfc
  simp_rw [hpt, MeasureTheory.integral_const_mul]
  congr 1
  -- measurability of the joint integrand
  have hmeas : Measurable (Function.uncurry fun ω (p : ℝ × ℝ) =>
      dbarNumOrder (k + 1) f (zOf p) * Matrix.trace ((zOf p) • (1 : Matrix n n ℂ) - H ω)⁻¹) :=
    measurable_uncurry_planeIntegrand_order H hHm hf hK
  -- the support rectangle of `∂̄_k f`
  have hKc : IsCompact (tsupport (dbarNumOrder (k + 1) f)) :=
    hasCompactSupport_dbarNumOrder (k := k + 1) hfc
  obtain ⟨X, hXpos, hX⟩ : ∃ X : ℝ, 0 < X ∧
      ∀ z ∈ tsupport (dbarNumOrder (k + 1) f), |z.re| < X := by
    have hKr : IsCompact (Complex.re '' tsupport (dbarNumOrder (k + 1) f)) :=
      hKc.image Complex.continuous_re
    obtain ⟨X₀, hX₀⟩ := hKr.exists_bound_of_continuousOn continuous_id.continuousOn
    refine ⟨max X₀ 0 + 1, by have := le_max_right X₀ 0; linarith, fun z hz => ?_⟩
    have h1 : ‖z.re‖ ≤ X₀ := hX₀ _ ⟨z, hz, rfl⟩
    have h2 : |z.re| ≤ X₀ := by simpa [Real.norm_eq_abs] using h1
    have h3 : X₀ ≤ max X₀ 0 := le_max_left _ _
    linarith
  obtain ⟨Y, hYpos, hY⟩ : ∃ Y : ℝ, 0 < Y ∧
      ∀ z ∈ tsupport (dbarNumOrder (k + 1) f), |z.im| < Y := by
    have hKi : IsCompact (Complex.im '' tsupport (dbarNumOrder (k + 1) f)) :=
      hKc.image Complex.continuous_im
    obtain ⟨Y₀, hY₀⟩ := hKi.exists_bound_of_continuousOn continuous_id.continuousOn
    refine ⟨max Y₀ 0 + 1, by have := le_max_right Y₀ 0; linarith, fun z hz => ?_⟩
    have h1 : ‖z.im‖ ≤ Y₀ := hY₀ _ ⟨z, hz, rfl⟩
    have h2 : |z.im| ≤ Y₀ := by simpa [Real.norm_eq_abs] using h1
    have h3 : Y₀ ≤ max Y₀ 0 := le_max_left _ _
    linarith
  -- bounds on `∂̄_k f`
  obtain ⟨M, hM0, hM⟩ := exists_norm_dbarNumOrder_le (f := f) (k := k) (K := K) hf hK hfc
  obtain ⟨M₂, hM₂⟩ := exists_norm_iteratedDeriv_le (k := k + 1) hf hK hfc
  have hM₂0 : 0 ≤ M₂ := le_trans (norm_nonneg _) (hM₂ 0)
  have hfac : (0 : ℝ) < (k.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos k
  set C : ℝ := max M M₂ * (Fintype.card n : ℝ) with hCdef
  have hmax0 : 0 ≤ max M M₂ := le_trans hM0 (le_max_left _ _)
  have hC0 : 0 ≤ C := mul_nonneg hmax0 (by positivity)
  -- vanishing near the real axis
  have hlin : ∀ z : ℂ, |z.im| < 1 →
      ‖dbarNumOrder (k + 1) f z‖ ≤ |z.im| ^ k / (k.factorial : ℝ) * M₂ := by
    intro z hz
    have h := norm_dbar_almostAnalyticExtOrderCut_le (f := f) (k := k) (K := K) hf hK
      (z := z) hz hM₂
    simpa [dbarNumOrder] using h
  -- the pointwise bound by the rectangle indicator
  have hbound : ∀ q : Ω × (ℝ × ℝ),
      ‖Function.uncurry (fun ω (p : ℝ × ℝ) => dbarNumOrder (k + 1) f (zOf p) *
        Matrix.trace ((zOf p) • (1 : Matrix n n ℂ) - H ω)⁻¹) q‖
      ≤ C * (Set.Icc (-X) X ×ˢ Set.Icc (-Y) Y).indicator (fun _ => (1 : ℝ)) q.2 := by
    intro q
    obtain ⟨ω, p⟩ := q
    show ‖dbarNumOrder (k + 1) f (zOf p) *
        Matrix.trace ((zOf p) • (1 : Matrix n n ℂ) - H ω)⁻¹‖
      ≤ C * (Set.Icc (-X) X ×ˢ Set.Icc (-Y) Y).indicator (fun _ => (1 : ℝ)) p
    rw [norm_mul]
    by_cases hp : p ∈ Set.Icc (-X) X ×ˢ Set.Icc (-Y) Y
    · rw [Set.indicator_of_mem hp, mul_one]
      rcases eq_or_ne p.2 0 with h0 | h0
      · have hzp : zOf p = ((p.1 : ℝ) : ℂ) := by simp [zOf, h0]
        rw [hzp, dbarNumOrder_succ_ofReal hk hf hK]
        simp [hC0]
      · have hzpim : (zOf p).im = p.2 := zOf_im p
        have htr := norm_trace_resolvent_le (H ω) (hH ω) (by rw [hzpim]; exact h0)
        have hcard0 : 0 ≤ (Fintype.card n : ℝ) := by positivity
        rcases lt_or_ge |p.2| 1 with h1 | h1
        · have hdb : ‖dbarNumOrder (k + 1) f (zOf p)‖
              ≤ |p.2| ^ k / (k.factorial : ℝ) * M₂ := by
            have h2 := hlin _ (by rw [hzpim]; exact h1)
            rwa [hzpim] at h2
          have hk0 : k ≠ 0 := by omega
          have hyp : |p.2| ≠ 0 := ne_of_gt (abs_pos.mpr h0)
          have hyle : |p.2| ^ k * (|p.2|)⁻¹ = |p.2| ^ (k - 1) := by
            rw [← div_eq_mul_inv,
              show |p.2| ^ k = |p.2| ^ (k - 1) * |p.2| from (pow_sub_one_mul hk0 |p.2|).symm]
            field_simp
          have hbound1 : |p.2| ^ (k - 1) ≤ 1 := by
            simpa using pow_le_one₀ (abs_nonneg p.2) (le_of_lt h1)
          calc ‖dbarNumOrder (k + 1) f (zOf p)‖ *
                ‖Matrix.trace ((zOf p) • (1 : Matrix n n ℂ) - H ω)⁻¹‖
              ≤ (|p.2| ^ k / (k.factorial : ℝ) * M₂) *
                  ((Fintype.card n : ℝ) * |(zOf p).im|⁻¹) := by
                refine mul_le_mul hdb htr (norm_nonneg _) (by positivity)
            _ = (|p.2| ^ k * (|p.2|)⁻¹) * (M₂ / (k.factorial : ℝ) * (Fintype.card n : ℝ)) := by
                rw [hzpim]; ring
            _ = |p.2| ^ (k - 1) * (M₂ / (k.factorial : ℝ) * (Fintype.card n : ℝ)) := by
                rw [hyle]
            _ ≤ 1 * (M₂ / (k.factorial : ℝ) * (Fintype.card n : ℝ)) := by
                refine mul_le_mul_of_nonneg_right hbound1 (by positivity)
            _ ≤ C := by
                rw [hCdef]
                have h1' : M₂ / (k.factorial : ℝ) ≤ max M M₂ := by
                  refine (div_le_self hM₂0 (by exact_mod_cast Nat.succ_le_of_lt (Nat.factorial_pos k))).trans
                    (le_max_right _ _)
                nlinarith [hcard0, h1']
        · calc ‖dbarNumOrder (k + 1) f (zOf p)‖ *
              ‖Matrix.trace ((zOf p) • (1 : Matrix n n ℂ) - H ω)⁻¹‖
              ≤ M * ((Fintype.card n : ℝ) * |(zOf p).im|⁻¹) := by
                refine mul_le_mul (hM _) htr (norm_nonneg _) hM0
          _ ≤ M * ((Fintype.card n : ℝ) * 1) := by
                refine mul_le_mul_of_nonneg_left ?_ hM0
                refine mul_le_mul_of_nonneg_left ?_ hcard0
                rw [hzpim]
                exact inv_le_one_of_one_le₀ h1
          _ ≤ C := by
                rw [hCdef]
                have h1' : M ≤ max M M₂ := le_max_left _ _
                nlinarith [hcard0, h1']
    · rw [Set.indicator_of_notMem hp, mul_zero]
      have hznot : zOf p ∉ tsupport (dbarNumOrder (k + 1) f) := by
        intro hmem
        apply hp
        refine ⟨?_, ?_⟩
        · rw [Set.mem_Icc]
          have h1 := hX _ hmem
          rw [zOf_re] at h1
          exact abs_le.mp h1.le
        · rw [Set.mem_Icc]
          have h1 := hY _ hmem
          rw [zOf_im] at h1
          exact abs_le.mp h1.le
      rw [image_eq_zero_of_notMem_tsupport hznot]
      simp
  -- the dominating integrable function
  have hdom : Integrable (fun q : Ω × (ℝ × ℝ) =>
      C * (Set.Icc (-X) X ×ˢ Set.Icc (-Y) Y).indicator (fun _ => (1 : ℝ)) q.2)
      (μ.prod (volume : Measure (ℝ × ℝ))) := by
    have hKmeas : MeasurableSet (Set.Icc (-X) X ×ˢ Set.Icc (-Y) Y : Set (ℝ × ℝ)) :=
      measurableSet_Icc.prod measurableSet_Icc
    have hKfin : (volume : Measure (ℝ × ℝ)) (Set.Icc (-X) X ×ˢ Set.Icc (-Y) Y) < ∞ :=
      (isCompact_Icc.prod isCompact_Icc).measure_lt_top
    have hg : Integrable (fun p : ℝ × ℝ =>
        C * (Set.Icc (-X) X ×ˢ Set.Icc (-Y) Y).indicator (fun _ => (1 : ℝ)) p)
        (volume : Measure (ℝ × ℝ)) := by
      have h1 : Integrable ((Set.Icc (-X) X ×ˢ Set.Icc (-Y) Y).indicator
          (fun _ => (1 : ℝ))) (volume : Measure (ℝ × ℝ)) := by
        rw [integrable_indicator_iff hKmeas]
        exact integrableOn_const hKfin.ne
      exact h1.const_mul C
    exact hg.comp_snd μ
  have hInt : Integrable (Function.uncurry fun ω (p : ℝ × ℝ) =>
      dbarNumOrder (k + 1) f (zOf p) *
        Matrix.trace ((zOf p) • (1 : Matrix n n ℂ) - H ω)⁻¹)
      (μ.prod (volume : Measure (ℝ × ℝ))) := by
    refine Integrable.mono' hdom hmeas.aestronglyMeasurable ?_
    filter_upwards with q
    exact hbound q
  -- Fubini
  rw [integral_integral_swap hInt]
  refine integral_congr_ae (Eventually.of_forall fun p => ?_)
  exact MeasureTheory.integral_const_mul _ _

end MeanIdentity

/-! ## The GUE pencil at order `k` -/

section PencilOrder

variable {ι d : Type*} [Fintype ι] [DecidableEq ι] [Fintype d] [DecidableEq d] [Nonempty d]
  {N : ℕ}

/-- **The mean of the trace of `f(H_N)` as a plane integral, order `k`.** -/
theorem integral_trace_guePencilCfc_eq_plane_integral_order
    (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    (hA₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian)
    (hN : 0 < N) {f : ℝ → ℝ} {k K : ℕ} (hk : 1 ≤ k) (hf : ContDiff ℝ K f)
    (hK : k + 1 ≤ K) (hfc : HasCompactSupport f) :
    ∫ x : EuclideanSpace ℝ (GUECoord ι N), (cfc f (guePencilMatrix A₀ A x)).trace
        ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))
      = (I / (2 * (Real.pi : ℂ))) *
          ∫ p : ℝ × ℝ, dbarNumOrder (k + 1) f (zOf p) *
            ((N : ℂ) * Matrix.trace (gueResolventMean (N := N) A₀ A (zOf p))) := by
  rw [integral_trace_cfc_eq_plane_integral_order (fun x : EuclideanSpace ℝ (GUECoord ι N) =>
      guePencilMatrix A₀ A x)
      (fun x => guePencilMatrix_isHermitian A₀ A hA₀ hA _)
      (continuous_guePencilMatrix A₀ A).measurable hk hf hK hfc]
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [compl_mem_ae_iff.mpr volume_im_eq_zero] with p hp
  rw [integral_trace_guePencilResolvent_eq A₀ A hA₀ hA hN (by rw [zOf_im]; exact hp)]

/-- **Lemma M, smooth form, finite side, in the normalization of the pencil statistic, order `k`.** -/
theorem integral_gueStatisticCfc_eq_plane_integral_order
    (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    (hA₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian)
    (hN : 0 < N) {f : ℝ → ℝ} {k K : ℕ} (hk : 1 ≤ k) (hf : ContDiff ℝ K f)
    (hK : k + 1 ≤ K) (hfc : HasCompactSupport f) :
    ∫ x : EuclideanSpace ℝ (GUECoord ι N), gueStatisticCfc (N := N) f A₀ A hA₀ hA x
        ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))
      = gueNormConst d N *
          ((I / (2 * (Real.pi : ℂ))) *
            ∫ p : ℝ × ℝ, dbarNumOrder (k + 1) f (zOf p) *
              ((N : ℂ) * Matrix.trace (gueResolventMean (N := N) A₀ A (zOf p)))).re := by
  have h2K : ((2 : ℕ∞) : WithTop ℕ∞) ≤ ((K : ℕ∞) : WithTop ℕ∞) :=
    by exact_mod_cast (by omega : 2 ≤ K)
  have hInt : Integrable (fun x : EuclideanSpace ℝ (GUECoord ι N) =>
      (cfc f (guePencilMatrix A₀ A x)).trace)
      (stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) :=
    integrable_trace_cfc (fun x : EuclideanSpace ℝ (GUECoord ι N) => guePencilMatrix A₀ A x)
      (fun x => guePencilMatrix_isHermitian A₀ A hA₀ hA _)
      (continuous_guePencilMatrix A₀ A).measurable (hf.of_le h2K) hfc
  simp_rw [gueStatisticCfc, guePencilNormTrace, guePencilCfc_eq_cfc]
  rw [MeasureTheory.integral_const_mul]
  congr 1
  have hre : ∫ x : EuclideanSpace ℝ (GUECoord ι N),
      (cfc f (guePencilMatrix A₀ A x)).trace.re
        ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))
      = (∫ x : EuclideanSpace ℝ (GUECoord ι N),
          (cfc f (guePencilMatrix A₀ A x)).trace
            ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))).re := by
    simpa using Complex.reCLM.integral_comp_comm hInt
  rw [hre, integral_trace_guePencilCfc_eq_plane_integral_order A₀ A hA₀ hA hN hk hf hK hfc]

/-- **The order-`k` mean identity in the normalization of the limit statistic** (the `hM` shape):
`E τ_N(f(H_N)) = (card d)⁻¹ Re ((I/2π) ∫∫ ∂̄_k f · Tr_d(g_N))`. -/
theorem integral_gueStatisticCfc_eq_plane_integral_order' (A₀ : Matrix d d ℂ)
    (A : ι → Matrix d d ℂ) (hA₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian)
    (hN : 0 < N) {f : ℝ → ℝ} {k K : ℕ} (hk : 1 ≤ k) (hf : ContDiff ℝ K f)
    (hK : k + 1 ≤ K) (hfc : HasCompactSupport f) :
    ∫ x : EuclideanSpace ℝ (GUECoord ι N), gueStatisticCfc (N := N) f A₀ A hA₀ hA x
        ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))
      = (Fintype.card d : ℝ)⁻¹ *
          ((I / (2 * (Real.pi : ℂ))) *
            ∫ p : ℝ × ℝ, dbarNumOrder (k + 1) f (zOf p) *
              Matrix.trace (gueResolventMean (N := N) A₀ A (zOf p))).re := by
  rw [integral_gueStatisticCfc_eq_plane_integral_order A₀ A hA₀ hA hN hk hf hK hfc]
  have hInt : (∫ p : ℝ × ℝ, dbarNumOrder (k + 1) f (zOf p) *
        ((N : ℂ) * Matrix.trace (gueResolventMean (N := N) A₀ A (zOf p))))
      = (N : ℂ) * ∫ p : ℝ × ℝ, dbarNumOrder (k + 1) f (zOf p) *
          Matrix.trace (gueResolventMean (N := N) A₀ A (zOf p)) := by
    have h1 : ∀ p : ℝ × ℝ, dbarNumOrder (k + 1) f (zOf p) *
        ((N : ℂ) * Matrix.trace (gueResolventMean (N := N) A₀ A (zOf p)))
        = (N : ℂ) * (dbarNumOrder (k + 1) f (zOf p) *
            Matrix.trace (gueResolventMean (N := N) A₀ A (zOf p))) := fun p => by ring
    simp_rw [h1]
    exact MeasureTheory.integral_const_mul _ _
  rw [hInt]
  have hcomm : (I / (2 * (Real.pi : ℂ))) *
      ((N : ℂ) * ∫ p : ℝ × ℝ, dbarNumOrder (k + 1) f (zOf p) *
        Matrix.trace (gueResolventMean (N := N) A₀ A (zOf p)))
      = (N : ℂ) * ((I / (2 * (Real.pi : ℂ))) *
        ∫ p : ℝ × ℝ, dbarNumOrder (k + 1) f (zOf p) *
          Matrix.trace (gueResolventMean (N := N) A₀ A (zOf p))) := by ring
  rw [hcomm, natCast_mul_re]
  have hcard : (Fintype.card d : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hNne : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hnorm : gueNormConst d N * ((N : ℝ) *
      ((I / (2 * (Real.pi : ℂ))) *
      ∫ p : ℝ × ℝ, dbarNumOrder (k + 1) f (zOf p) *
        Matrix.trace (gueResolventMean (N := N) A₀ A (zOf p))).re)
      = (Fintype.card d : ℝ)⁻¹ * ((I / (2 * (Real.pi : ℂ))) *
      ∫ p : ℝ × ℝ, dbarNumOrder (k + 1) f (zOf p) *
        Matrix.trace (gueResolventMean (N := N) A₀ A (zOf p))).re := by
    rw [gueNormConst]
    have hcast : (((Fintype.card d * N : ℕ)) : ℝ) = (Fintype.card d : ℝ) * (N : ℝ) := by
      push_cast
      ring
    rw [hcast]
    field_simp
  exact hnorm

end PencilOrder


/-! ## The plane weights of `∂̄_k f` and the order-`k` comparison theorem -/

section ComparisonOrder

variable {ι d : Type*} [Fintype ι] [DecidableEq ι] [Fintype d] [DecidableEq d] [Nonempty d]
  {N : ℕ}

/-- The plane weight `‖∂̄_k f(z)‖` is integrable. -/
lemma integrable_norm_dbarNumOrder_zOf {f : ℝ → ℝ} {k K : ℕ} (hf : ContDiff ℝ K f)
    (hK : k + 1 ≤ K) (hfc : HasCompactSupport f) :
    Integrable (fun p : ℝ × ℝ => ‖dbarNumOrder (k + 1) f (zOf p)‖)
      (volume : Measure (ℝ × ℝ)) := by
  obtain ⟨B, hB0, hB⟩ := exists_norm_dbarNumOrder_le (f := f) (k := k) (K := K) hf hK hfc
  obtain ⟨X, Y, hXpos, hYpos, hsupp⟩ : ∃ (X Y : ℝ), 0 < X ∧ 0 < Y ∧ ∀ p : ℝ × ℝ,
      p ∉ Set.Icc (-X) X ×ˢ Set.Icc (-Y) Y → ‖dbarNumOrder (k + 1) f (zOf p)‖ = 0 := by
    have hKc : IsCompact (tsupport (dbarNumOrder (k + 1) f)) :=
      hasCompactSupport_dbarNumOrder (k := k + 1) hfc
    obtain ⟨X, hXpos, hX⟩ : ∃ X : ℝ, 0 < X ∧
        ∀ z ∈ tsupport (dbarNumOrder (k + 1) f), |z.re| < X := by
      have hKr : IsCompact (Complex.re '' tsupport (dbarNumOrder (k + 1) f)) :=
        hKc.image Complex.continuous_re
      obtain ⟨X₀, hX₀⟩ := hKr.exists_bound_of_continuousOn continuous_id.continuousOn
      refine ⟨max X₀ 0 + 1, by have := le_max_right X₀ 0; linarith, fun z hz => ?_⟩
      have h1 : ‖z.re‖ ≤ X₀ := hX₀ _ ⟨z, hz, rfl⟩
      have h2 : |z.re| ≤ X₀ := by simpa [Real.norm_eq_abs] using h1
      linarith [le_max_left X₀ 0]
    obtain ⟨Y, hYpos, hY⟩ : ∃ Y : ℝ, 0 < Y ∧
        ∀ z ∈ tsupport (dbarNumOrder (k + 1) f), |z.im| < Y := by
      have hKi : IsCompact (Complex.im '' tsupport (dbarNumOrder (k + 1) f)) :=
        hKc.image Complex.continuous_im
      obtain ⟨Y₀, hY₀⟩ := hKi.exists_bound_of_continuousOn continuous_id.continuousOn
      refine ⟨max Y₀ 0 + 1, by have := le_max_right Y₀ 0; linarith, fun z hz => ?_⟩
      have h1 : ‖z.im‖ ≤ Y₀ := hY₀ _ ⟨z, hz, rfl⟩
      have h2 : |z.im| ≤ Y₀ := by simpa [Real.norm_eq_abs] using h1
      linarith [le_max_left Y₀ 0]
    refine ⟨X, Y, hXpos, hYpos, fun p hp => ?_⟩
    have hznot : zOf p ∉ tsupport (dbarNumOrder (k + 1) f) := by
      intro hmem
      apply hp
      refine ⟨?_, ?_⟩
      · rw [Set.mem_Icc]
        have h1 := hX _ hmem
        rw [zOf_re] at h1
        exact abs_le.mp h1.le
      · rw [Set.mem_Icc]
        have h1 := hY _ hmem
        rw [zOf_im] at h1
        exact abs_le.mp h1.le
    rw [image_eq_zero_of_notMem_tsupport hznot, norm_zero]
  refine Integrable.mono' (integrable_rect_indicator X Y B)
    (((continuous_dbarNumOrder hf hK).comp continuous_zOf).norm.aestronglyMeasurable)
    (Eventually.of_forall fun p => ?_)
  by_cases hp : p ∈ Set.Icc (-X) X ×ˢ Set.Icc (-Y) Y
  · rw [Set.indicator_of_mem hp, mul_one]
    simpa using hB (zOf p)
  · rw [Set.indicator_of_notMem hp, mul_zero, hsupp p hp]
    simp

/-- The weighted plane integral `∫∫ ‖∂̄_k f(z)‖ |Im z|⁻¹` is finite: the order-`k` vanishing of
`∂̄_k f` on the real axis makes the weight integrable. -/
lemma integrable_norm_dbarNumOrder_mul_inv_im_zOf {f : ℝ → ℝ} {k K : ℕ} (hk : 1 ≤ k)
    (hf : ContDiff ℝ K f) (hK : k + 1 ≤ K) (hfc : HasCompactSupport f) :
    Integrable (fun p : ℝ × ℝ => ‖dbarNumOrder (k + 1) f (zOf p)‖ * |p.2|⁻¹)
      (volume : Measure (ℝ × ℝ)) := by
  obtain ⟨X, Y, hXpos, hYpos, hsupp⟩ : ∃ (X Y : ℝ), 0 < X ∧ 0 < Y ∧ ∀ p : ℝ × ℝ,
      p ∉ Set.Icc (-X) X ×ˢ Set.Icc (-Y) Y → ‖dbarNumOrder (k + 1) f (zOf p)‖ = 0 := by
    have hKc : IsCompact (tsupport (dbarNumOrder (k + 1) f)) :=
      hasCompactSupport_dbarNumOrder (k := k + 1) hfc
    obtain ⟨X, hXpos, hX⟩ : ∃ X : ℝ, 0 < X ∧
        ∀ z ∈ tsupport (dbarNumOrder (k + 1) f), |z.re| < X := by
      have hKr : IsCompact (Complex.re '' tsupport (dbarNumOrder (k + 1) f)) :=
        hKc.image Complex.continuous_re
      obtain ⟨X₀, hX₀⟩ := hKr.exists_bound_of_continuousOn continuous_id.continuousOn
      refine ⟨max X₀ 0 + 1, by have := le_max_right X₀ 0; linarith, fun z hz => ?_⟩
      have h1 : ‖z.re‖ ≤ X₀ := hX₀ _ ⟨z, hz, rfl⟩
      have h2 : |z.re| ≤ X₀ := by simpa [Real.norm_eq_abs] using h1
      linarith [le_max_left X₀ 0]
    obtain ⟨Y, hYpos, hY⟩ : ∃ Y : ℝ, 0 < Y ∧
        ∀ z ∈ tsupport (dbarNumOrder (k + 1) f), |z.im| < Y := by
      have hKi : IsCompact (Complex.im '' tsupport (dbarNumOrder (k + 1) f)) :=
        hKc.image Complex.continuous_im
      obtain ⟨Y₀, hY₀⟩ := hKi.exists_bound_of_continuousOn continuous_id.continuousOn
      refine ⟨max Y₀ 0 + 1, by have := le_max_right Y₀ 0; linarith, fun z hz => ?_⟩
      have h1 : ‖z.im‖ ≤ Y₀ := hY₀ _ ⟨z, hz, rfl⟩
      have h2 : |z.im| ≤ Y₀ := by simpa [Real.norm_eq_abs] using h1
      linarith [le_max_left Y₀ 0]
    refine ⟨X, Y, hXpos, hYpos, fun p hp => ?_⟩
    have hznot : zOf p ∉ tsupport (dbarNumOrder (k + 1) f) := by
      intro hmem
      apply hp
      refine ⟨?_, ?_⟩
      · rw [Set.mem_Icc]
        have h1 := hX _ hmem
        rw [zOf_re] at h1
        exact abs_le.mp h1.le
      · rw [Set.mem_Icc]
        have h1 := hY _ hmem
        rw [zOf_im] at h1
        exact abs_le.mp h1.le
    rw [image_eq_zero_of_notMem_tsupport hznot, norm_zero]
  obtain ⟨B, hB0, hB⟩ := exists_norm_dbarNumOrder_le (f := f) (k := k) (K := K) hf hK hfc
  obtain ⟨M₂, hM₂⟩ := exists_norm_iteratedDeriv_le (k := k + 1) hf hK hfc
  have hM₂0 : 0 ≤ M₂ := le_trans (norm_nonneg _) (hM₂ 0)
  have hfac : (0 : ℝ) < (k.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos k
  have hmeas : AEStronglyMeasurable
      (fun p : ℝ × ℝ => ‖dbarNumOrder (k + 1) f (zOf p)‖ * |p.2|⁻¹)
      (volume : Measure (ℝ × ℝ)) :=
    (((continuous_dbarNumOrder hf hK).comp continuous_zOf).norm.measurable.mul
      ((continuous_abs.comp continuous_snd).measurable.inv)).aestronglyMeasurable
  refine Integrable.mono' (integrable_rect_indicator X Y (max (M₂ / (k.factorial : ℝ)) B)) hmeas
    (Eventually.of_forall fun p => ?_)
  show ‖‖dbarNumOrder (k + 1) f (zOf p)‖ * |p.2|⁻¹‖ ≤
    max (M₂ / (k.factorial : ℝ)) B *
      (Set.Icc (-X) X ×ˢ Set.Icc (-Y) Y).indicator (fun _ => (1 : ℝ)) p
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  by_cases hp : p ∈ Set.Icc (-X) X ×ˢ Set.Icc (-Y) Y
  · rw [Set.indicator_of_mem hp, mul_one]
    rcases eq_or_ne p.2 0 with h0 | h0
    · rw [h0]
      simp only [abs_zero]
      rw [_root_.inv_zero, mul_zero]
      exact le_trans (div_nonneg hM₂0 hfac.le) (le_max_left _ _)
    · have hpos : 0 < |p.2| := abs_pos.mpr h0
      rcases lt_or_ge |p.2| 1 with h1 | h1
      · have hlin := norm_dbar_almostAnalyticExtOrderCut_le (f := f) (k := k) (K := K) hf hK
          (z := zOf p) (by rw [zOf_im]; exact h1) hM₂
        rw [zOf_im] at hlin
        have hk0 : k ≠ 0 := by omega
        have hyp : |p.2| ≠ 0 := ne_of_gt hpos
        have hyle : |p.2| ^ k * (|p.2|)⁻¹ = |p.2| ^ (k - 1) := by
          rw [← div_eq_mul_inv,
            show |p.2| ^ k = |p.2| ^ (k - 1) * |p.2| from (pow_sub_one_mul hk0 |p.2|).symm]
          field_simp
        have hyle1 : |p.2| ^ (k - 1) ≤ 1 := by
          simpa using pow_le_one₀ (abs_nonneg p.2) (le_of_lt h1)
        calc ‖dbarNumOrder (k + 1) f (zOf p)‖ * |p.2|⁻¹
            ≤ (|p.2| ^ k / (k.factorial : ℝ) * M₂) * |p.2|⁻¹ :=
              mul_le_mul_of_nonneg_right hlin (by positivity)
          _ = (|p.2| ^ k * (|p.2|)⁻¹) * (M₂ / (k.factorial : ℝ)) := by ring
          _ = |p.2| ^ (k - 1) * (M₂ / (k.factorial : ℝ)) := by rw [hyle]
          _ ≤ 1 * (M₂ / (k.factorial : ℝ)) :=
              mul_le_mul_of_nonneg_right hyle1 (by positivity)
          _ = M₂ / (k.factorial : ℝ) := one_mul _
          _ ≤ max (M₂ / (k.factorial : ℝ)) B := le_max_left _ _
      · calc ‖dbarNumOrder (k + 1) f (zOf p)‖ * |p.2|⁻¹
            ≤ B * |p.2|⁻¹ := mul_le_mul_of_nonneg_right (hB (zOf p)) (by positivity)
          _ ≤ B * 1 := by
              refine mul_le_mul_of_nonneg_left ?_ hB0
              exact inv_le_one_of_one_le₀ h1
          _ = B := mul_one B
          _ ≤ max (M₂ / (k.factorial : ℝ)) B := le_max_right _ _
  · rw [Set.indicator_of_notMem hp, mul_zero, hsupp p hp]
    simp

/-- The order-`k` limit statistic in plane-integral form. -/
def guePlaneLimitOrder (k : ℕ) (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ) (f : ℝ → ℝ) : ℝ :=
  (Fintype.card d : ℝ)⁻¹ * ((I / (2 * (Real.pi : ℂ))) *
    ∫ p : ℝ × ℝ, dbarNumOrder (k + 1) f (zOf p) *
      Matrix.trace (operatorMatrixPencilCauchy A₀ A (zOf p))).re

/-- **Lemma M, smooth form, under a mean-resolvent bound, order `k`.**
The order-`k` analogue of `smooth_trace_comparison_of_mean_bound`. -/
theorem smooth_trace_comparison_of_mean_bound_order (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    (hA₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian) (hN : 0 < N) {f : ℝ → ℝ}
    {k K : ℕ} (hk : 1 ≤ k) (hf : ContDiff ℝ K f) (hK : k + 1 ≤ K) (hfc : HasCompactSupport f)
    {M η₀ : ℝ} (hM0 : 0 ≤ M) (hη₀1 : 1 ≤ η₀)
    (hη : 2 * M ^ 2 * (∑ i, (frob (A i)) ^ 2) ≤ 1)
    (hMd : (Fintype.card d : ℝ) ≤ M * η₀)
    (hgN : ∀ (N' : ℕ) (z : ℂ), z.im ≠ 0 →
      frob (gueResolventMean (N := N') A₀ A z) ≤ M)
    (hIntN : Integrable (fun p : ℝ × ℝ => dbarNumOrder (k + 1) f (zOf p) *
      Matrix.trace (gueResolventMean (N := N) A₀ A (zOf p))))
    (hIntLim : Integrable (fun p : ℝ × ℝ => dbarNumOrder (k + 1) f (zOf p) *
      Matrix.trace (operatorMatrixPencilCauchy A₀ A (zOf p)))) :
    |∫ x : EuclideanSpace ℝ (GUECoord ι N), gueStatisticCfc (N := N) f A₀ A hA₀ hA x
        ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) - guePlaneLimitOrder k A₀ A f|
      ≤ (2 * Real.pi)⁻¹ *
          ∫ p : ℝ × ℝ, ‖dbarNumOrder (k + 1) f (zOf p)‖ *
            (2 * M * (Fintype.card d : ℝ) *
                (2 * (Fintype.card d : ℝ) ^ 2 * Real.sqrt (Fintype.card d : ℝ) *
                  (∑ i, (frob (A i)) ^ 2) * (2 * (∑ i, (frob (A i)) ^ 2))) / (N : ℝ) ^ 2
              + M + (Fintype.card d : ℝ) * |p.2|⁻¹) := by
  classical
  rw [integral_gueStatisticCfc_eq_plane_integral_order' A₀ A hA₀ hA hN hk hf hK hfc,
    guePlaneLimitOrder]
  set c : ℝ := (Fintype.card d : ℝ) with hc
  set Kc : ℝ := 2 * c ^ 2 * Real.sqrt c * (∑ i, (frob (A i)) ^ 2) *
    (2 * (∑ i, (frob (A i)) ^ 2)) with hKc
  set Cf : ℝ := 2 * M * c * Kc with hCf
  have hc0 : (0 : ℝ) ≤ c := by positivity
  have hS0 : (0 : ℝ) ≤ ∑ i, (frob (A i)) ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hK0 : 0 ≤ Kc := by rw [hKc]; positivity
  have hCf0 : 0 ≤ Cf := by rw [hCf]; positivity
  set W : ℝ × ℝ → ℝ := fun p => Cf / (N : ℝ) ^ 2 + M + c * |p.2|⁻¹ with hW
  have hW0 : ∀ p, 0 ≤ W p := by
    intro p; rw [hW]; positivity
  set Ai : ℂ := ∫ p : ℝ × ℝ, dbarNumOrder (k + 1) f (zOf p) *
    Matrix.trace (gueResolventMean (N := N) A₀ A (zOf p)) with hAi
  set Bi : ℂ := ∫ p : ℝ × ℝ, dbarNumOrder (k + 1) f (zOf p) *
    Matrix.trace (operatorMatrixPencilCauchy A₀ A (zOf p)) with hBi
  set Di : ℂ := ∫ p : ℝ × ℝ, dbarNumOrder (k + 1) f (zOf p) *
    Matrix.trace (gueResolventMean (N := N) A₀ A (zOf p) - operatorMatrixPencilCauchy A₀ A (zOf p))
    with hDi
  have hAB : Ai - Bi = Di := by
    rw [hAi, hBi, hDi, ← integral_sub hIntN hIntLim]
    congr 1
    ext p
    rw [Matrix.trace_sub]
    ring
  have hWmeas : Measurable (fun p : ℝ × ℝ => Cf / (N : ℝ) ^ 2 + M + c * |p.2|⁻¹) := by
    refine Measurable.add (Measurable.add measurable_const measurable_const) ?_
    have hcont : Continuous fun p : ℝ × ℝ => |p.2| :=
      continuous_abs.comp (continuous_snd : Continuous fun p : ℝ × ℝ => p.2)
    exact hcont.measurable.inv.const_mul c
  have hWint : Integrable (fun p : ℝ × ℝ => ‖dbarNumOrder (k + 1) f (zOf p)‖ * W p)
      (volume : Measure (ℝ × ℝ)) := by
    have hC0 : (0 : ℝ) ≤ Cf / (N : ℝ) ^ 2 + M + c := by positivity
    refine Integrable.mono' (((integrable_norm_dbarNumOrder_zOf hf hK hfc).add
      (integrable_norm_dbarNumOrder_mul_inv_im_zOf hk hf hK hfc)).mul_const
        (Cf / (N : ℝ) ^ 2 + M + c)) ?_ (Filter.Eventually.of_forall fun p => ?_)
    · exact ((continuous_dbarNumOrder hf hK).comp continuous_zOf).norm.measurable.mul hWmeas
        |>.aestronglyMeasurable
    · rw [hW]
      show ‖‖dbarNumOrder (k + 1) f (zOf p)‖ * (Cf / (N : ℝ) ^ 2 + M + c * |p.2|⁻¹)‖ ≤
        (‖dbarNumOrder (k + 1) f (zOf p)‖ + ‖dbarNumOrder (k + 1) f (zOf p)‖ * |p.2|⁻¹) *
          (Cf / (N : ℝ) ^ 2 + M + c)
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      have hinv : |p.2|⁻¹ ≤ 1 + |p.2|⁻¹ := by linarith [inv_nonneg.mpr (abs_nonneg p.2)]
      have hWy : Cf / (N : ℝ) ^ 2 + M + c * |p.2|⁻¹
          ≤ (Cf / (N : ℝ) ^ 2 + M + c) * (1 + |p.2|⁻¹) := by
        have h1 : c ≤ Cf / (N : ℝ) ^ 2 + M + c := by
          have := div_nonneg hCf0 (by positivity : (0:ℝ) ≤ (N:ℝ)^2)
          linarith
        have h2 : 0 ≤ |p.2|⁻¹ := inv_nonneg.mpr (abs_nonneg _)
        nlinarith [mul_le_mul_of_nonneg_right h1 h2, hC0, hc0]
      calc ‖dbarNumOrder (k + 1) f (zOf p)‖ * W p
          ≤ ‖dbarNumOrder (k + 1) f (zOf p)‖ *
              ((Cf / (N : ℝ) ^ 2 + M + c) * (1 + |p.2|⁻¹)) :=
            mul_le_mul_of_nonneg_left hWy (norm_nonneg _)
        _ = (‖dbarNumOrder (k + 1) f (zOf p)‖ +
              ‖dbarNumOrder (k + 1) f (zOf p)‖ * |p.2|⁻¹) *
              (Cf / (N : ℝ) ^ 2 + M + c) := by ring
  have hbd : ‖Di‖ ≤ c * ∫ p : ℝ × ℝ, ‖dbarNumOrder (k + 1) f (zOf p)‖ * W p := by
    rw [hDi]
    have hmaj : Integrable (fun p : ℝ × ℝ =>
        (‖dbarNumOrder (k + 1) f (zOf p)‖ * W p) * c) (volume : Measure (ℝ × ℝ)) :=
      hWint.mul_const c
    refine (MeasureTheory.norm_integral_le_of_norm_le hmaj ?_).trans ?_
    · filter_upwards [(compl_mem_ae_iff).mpr volume_im_eq_zero] with p hp
      have hz : (zOf p).im ≠ 0 := by rwa [zOf_im]
      rw [norm_mul]
      have hcmp := frob_sub_pencilCauchy_le_of_mean_bound A₀ A hA₀ hA hN hM0 hη₀1 hη hMd hgN hz
      have hbound : frob (gueResolventMean (N := N) A₀ A (zOf p) -
          operatorMatrixPencilCauchy A₀ A (zOf p)) ≤ W p := by
        have h1 : (if η₀ ≤ p.2 then
            2 * M * c * Kc / (N : ℝ) ^ 2 else 0) ≤ Cf / (N : ℝ) ^ 2 := by
          split_ifs with h
          · rw [hCf]
          · exact div_nonneg hCf0 (by positivity)
        rw [zOf_im] at hcmp
        rw [hW, hc]
        linarith
      calc ‖dbarNumOrder (k + 1) f (zOf p)‖ *
            ‖Matrix.trace (gueResolventMean (N := N) A₀ A (zOf p) -
              operatorMatrixPencilCauchy A₀ A (zOf p))‖
          ≤ ‖dbarNumOrder (k + 1) f (zOf p)‖ * (c * W p) := by
            refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
            refine (norm_trace_le_card_mul_frob _).trans ?_
            exact mul_le_mul_of_nonneg_left hbound hc0
        _ = (‖dbarNumOrder (k + 1) f (zOf p)‖ * W p) * c := by ring
    · rw [MeasureTheory.integral_mul_const]
      exact le_of_eq (by ring)
  have hre : (I / (2 * (Real.pi : ℂ)) * Ai).re - (I / (2 * (Real.pi : ℂ)) * Bi).re
      = (I / (2 * (Real.pi : ℂ)) * Di).re := by
    rw [← Complex.sub_re, ← mul_sub, hAB]
  have hnorm : ‖(I / (2 * (Real.pi : ℂ))) * Di‖ = (2 * Real.pi)⁻¹ * ‖Di‖ := by
    rw [norm_mul]
    congr 1
    rw [norm_div, Complex.norm_I]
    have h2 : ‖(2 * (Real.pi : ℂ))‖ = 2 * Real.pi := by
      rw [show (2 * (Real.pi : ℂ)) = ((2 * Real.pi : ℝ) : ℂ) from by push_cast; ring]
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    rw [h2, one_div]
  calc |c⁻¹ * (I / (2 * (Real.pi : ℂ)) * Ai).re - c⁻¹ * (I / (2 * (Real.pi : ℂ)) * Bi).re|
      = c⁻¹ * |(I / (2 * (Real.pi : ℂ)) * Di).re| := by
        rw [← mul_sub, ← hre, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < c⁻¹)]
    _ ≤ c⁻¹ * ‖(I / (2 * (Real.pi : ℂ))) * Di‖ :=
        mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm _) (by positivity)
    _ = c⁻¹ * ((2 * Real.pi)⁻¹ * ‖Di‖) := by rw [hnorm]
    _ ≤ c⁻¹ * ((2 * Real.pi)⁻¹ *
          (c * ∫ p : ℝ × ℝ, ‖dbarNumOrder (k + 1) f (zOf p)‖ * W p)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact mul_le_mul_of_nonneg_left hbd (by positivity)
    _ = (2 * Real.pi)⁻¹ * ∫ p : ℝ × ℝ, ‖dbarNumOrder (k + 1) f (zOf p)‖ *
          (2 * M * c * (2 * c ^ 2 * Real.sqrt c * (∑ i, (frob (A i)) ^ 2) *
              (2 * (∑ i, (frob (A i)) ^ 2))) / (N : ℝ) ^ 2 + M + c * |p.2|⁻¹) := by
        rw [hW, hCf, hKc]
        have hcne : c ≠ 0 := by
          rw [hc]
          exact_mod_cast Fintype.card_ne_zero (α := d)
        field_simp

end ComparisonOrder


end

end GUEStrongConvergence
