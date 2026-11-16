/-
# The scalar measure form of the Cauchy–Pompeiu representation

For a finite measure `ν` on `ℝ` and a `C²` compactly supported `f : ℝ → ℝ`, the scalar
Cauchy–Pompeiu identity `pompeiu_plane` can be integrated against `ν`:

`∫ t, f t ∂ν = (I / 2π) ∫∫ ∂̄F(z) · S_ν(z)`,

where `S_ν(z) = ∫ t, (z - t)⁻¹ ∂ν(t)` is the Stieltjes transform of `ν` and
`∂̄F(z) = dbarNum f z` is the `∂̄` numerator of the cut-off almost-analytic extension of `f`.

The proof is a direct Fubini argument.  The key point is that, although the plane
integrand `∂̄F(z)/(z - t)` is not integrable on the product of the *Lebesgue* measures
(the singularity along `z = t` is too large), the linear vanishing of `∂̄F` on the real
axis gives a bound

`‖dbarNum f z * (z - t)⁻¹‖ ≤ M`

which is uniform in both `z` and `t`.  Hence the joint integrand is bounded, and Fubini
applies against the finite measure `ν` times the (σ-finite) plane Lebesgue measure.

## Main results

* `zOfPlane` — the complex number attached to a point of the plane;
* `stieltjesTransform` — the Stieltjes transform of a finite measure on `ℝ`;
* `exists_norm_dbarNum_mul_inv_sub_le` — the uniform bound on the `∂̄` integrand;
* `integral_eq_plane_integral_stieltjes` — the scalar measure Cauchy–Pompeiu identity.
-/
import GUEStrongConvergence.Probability.TracePompeiu

noncomputable section

open MeasureTheory Complex
open scoped Topology

namespace GUEStrongConvergence

variable {f : ℝ → ℝ}

/-- The complex number `x + i y` attached to a point `(x, y)` of the plane. -/
def zOfPlane (p : ℝ × ℝ) : ℂ := (p.1 : ℂ) + (p.2 : ℂ) * I

lemma continuous_zOfPlane : Continuous zOfPlane := by
  unfold zOfPlane
  fun_prop

lemma measurable_zOfPlane : Measurable zOfPlane := continuous_zOfPlane.measurable

/-- The Stieltjes transform of a finite measure on `ℝ`. -/
def stieltjesTransform (ν : Measure ℝ) (z : ℂ) : ℂ :=
  ∫ t : ℝ, (z - (t : ℂ))⁻¹ ∂ν

/-- **Uniform bound on the `∂̄` integrand.**  For a `C²` compactly supported `f` the quotient
`∂̄F(z)/(z - t)` is bounded uniformly in `z : ℂ` and `t : ℝ`.  This is the key estimate
that makes the Fubini argument work. -/
lemma exists_norm_dbarNum_mul_inv_sub_le (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) :
    ∃ M : ℝ, ∀ (z : ℂ) (t : ℝ), ‖dbarNum f z * (z - (t : ℂ))⁻¹‖ ≤ M := by
  obtain ⟨M₁, hM₁⟩ := exists_norm_dbarNum_le hf hfc
  obtain ⟨M₂, hM₂⟩ := exists_norm_deriv_deriv_le hf hfc
  have hM₁nn : 0 ≤ M₁ := le_trans (norm_nonneg _) (hM₁ 0)
  have hM₂nn : 0 ≤ M₂ := le_trans (norm_nonneg _) (hM₂ 0)
  have hmaxnn : 0 ≤ max M₁ M₂ := le_trans hM₁nn (le_max_left _ _)
  refine ⟨max M₁ M₂, fun z t => ?_⟩
  have hnum : ‖dbarNum f z‖ ≤ |z.im| * max M₁ M₂ := by
    rcases eq_or_lt_of_le (abs_nonneg z.im) with h0 | h0
    · have him0 : z.im = 0 := abs_eq_zero.mp h0.symm
      have hle := norm_dbar_almostAnalyticExtCut_le hf (z := z)
        (by rw [him0]; norm_num) hM₂
      have hzero : ‖dbarNum f z‖ ≤ 0 := by
        simpa [dbarNum, him0] using hle
      simpa [him0] using hzero
    · rcases lt_or_ge |z.im| 1 with h1 | h1
      · exact le_trans (norm_dbar_almostAnalyticExtCut_le hf h1 hM₂)
          (mul_le_mul_of_nonneg_left (le_max_right _ _) (abs_nonneg _))
      · have hb : ‖dbarNum f z‖ ≤ M₁ := hM₁ z
        calc ‖dbarNum f z‖ ≤ M₁ := hb
          _ ≤ max M₁ M₂ := le_max_left _ _
          _ = 1 * max M₁ M₂ := (one_mul _).symm
          _ ≤ |z.im| * max M₁ M₂ :=
            mul_le_mul_of_nonneg_right h1 (le_trans hM₁nn (le_max_left _ _))
  rw [norm_mul, norm_inv]
  rcases eq_or_ne z (t : ℂ) with rfl | hz
  · simp only [sub_self, inv_zero, norm_zero, mul_zero]
    exact hmaxnn
  · have hnorm : 0 < ‖z - (t : ℂ)‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hz)
    have hden : |z.im| ≤ ‖z - (t : ℂ)‖ := by
      have h1 : (z - (t : ℂ)).im = z.im := by simp
      calc |z.im| = |(z - (t : ℂ)).im| := by rw [h1]
        _ ≤ ‖z - (t : ℂ)‖ := Complex.abs_im_le_norm _
    rcases eq_or_lt_of_le (abs_nonneg z.im) with h0 | h0
    · have him0 : z.im = 0 := abs_eq_zero.mp h0.symm
      have hzero : ‖dbarNum f z‖ ≤ 0 := by
        have hle := norm_dbar_almostAnalyticExtCut_le hf (z := z)
          (by rw [him0]; norm_num) hM₂
        simpa [dbarNum, him0] using hle
      rw [show dbarNum f z = 0 from norm_eq_zero.mp (le_antisymm hzero (norm_nonneg _))]
      simp only [norm_zero, zero_mul]
      exact hmaxnn
    · have hinvle : (‖z - (t : ℂ)‖)⁻¹ ≤ (|z.im|)⁻¹ := by
        rw [inv_le_inv₀ hnorm h0]
        exact hden
      calc ‖dbarNum f z‖ * (‖z - (t : ℂ)‖)⁻¹
          ≤ (|z.im| * max M₁ M₂) * (|z.im|)⁻¹ :=
            mul_le_mul hnum hinvle (inv_nonneg.mpr (norm_nonneg _))
              (mul_nonneg (abs_nonneg _) (le_trans hM₁nn (le_max_left _ _)))
        _ = max M₁ M₂ := by
            rw [mul_comm (|z.im|) (max M₁ M₂), mul_assoc,
              mul_inv_cancel₀ (ne_of_gt h0), mul_one]

/-- A horizontal bound `X` for the support of the cut-off extension. -/
lemma exists_abs_re_lt_of_tsupport_almostAnalyticExtCut (hfc : HasCompactSupport f) :
    ∃ X : ℝ, 0 < X ∧ ∀ z ∈ tsupport (almostAnalyticExtCut f), |z.re| < X := by
  have hKc : IsCompact (tsupport (almostAnalyticExtCut f)) :=
    hasCompactSupport_almostAnalyticExtCut hfc
  have hKr : IsCompact (Complex.re '' tsupport (almostAnalyticExtCut f)) :=
    hKc.image Complex.continuous_re
  obtain ⟨X₀, hX₀⟩ := hKr.exists_bound_of_continuousOn continuous_id.continuousOn
  refine ⟨max X₀ 0 + 1, by have := le_max_right X₀ 0; linarith, fun z hz => ?_⟩
  have h1 : ‖z.re‖ ≤ X₀ := hX₀ _ ⟨z, hz, rfl⟩
  have h2 : |z.re| ≤ X₀ := by simpa [Real.norm_eq_abs] using h1
  have h3 : X₀ ≤ max X₀ 0 := le_max_left _ _
  linarith

/-- The `∂̄` numerator vanishes off the support of the cut-off extension. -/
lemma dbarNum_eq_zero_of_notMem_tsupport {f : ℝ → ℝ}
    {z : ℂ} (hz : z ∉ tsupport (almostAnalyticExtCut f)) : dbarNum f z = 0 := by
  rw [notMem_tsupport_iff_eventuallyEq] at hz
  simp only [dbarNum]
  rw [hz.fderiv_eq]
  simp

/-- **Scalar measure Cauchy–Pompeiu representation.**  For a finite measure `ν` on `ℝ` and a
`C²` compactly supported `f`,
`∫ f dν = (I / 2π) ∫∫ ∂̄F(z) · S_ν(z)`,
where `S_ν` is the Stieltjes transform of `ν`. -/
theorem integral_eq_plane_integral_stieltjes {ν : Measure ℝ} [IsFiniteMeasure ν]
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    (∫ t : ℝ, (f t : ℂ) ∂ν) =
      (I / (2 * (Real.pi : ℂ))) *
        ∫ p : ℝ × ℝ, dbarNum f (zOfPlane p) * stieltjesTransform ν (zOfPlane p) := by
  -- the pointwise identity, obtained from `pompeiu_plane` after uncurrying the plane integral
  have hpt : ∀ t : ℝ, (f t : ℂ) =
      (I / (2 * (Real.pi : ℂ))) *
        ∫ p : ℝ × ℝ, dbarNum f (zOfPlane p) * (zOfPlane p - (t : ℂ))⁻¹ := by
    intro t
    rw [pompeiu_plane hf hfc t, ← integral_planeIntegrand_eq_iterated hf hfc t]
    congr 1
  -- uniform bound and compact support of the joint integrand
  obtain ⟨M, hM⟩ := exists_norm_dbarNum_mul_inv_sub_le (f := f) hf hfc
  obtain ⟨X, hXpos, hXsupp⟩ := exists_abs_re_lt_of_tsupport_almostAnalyticExtCut
    (f := f) hfc
  set R : Set (ℝ × ℝ) := Set.Ioc (-X) X ×ˢ Set.Ioc (-3 : ℝ) 3 with hRdef
  have hRmeas : MeasurableSet R := measurableSet_Ioc.prod measurableSet_Ioc
  set S : Set (ℝ × (ℝ × ℝ)) := Set.univ ×ˢ R with hSdef
  have hSmeas : MeasurableSet S := MeasurableSet.univ.prod hRmeas
  -- vanishing of the integrand off `S`
  have hzero : ∀ q : ℝ × (ℝ × ℝ), q ∉ S →
      dbarNum f (zOfPlane q.2) * (zOfPlane q.2 - (q.1 : ℂ))⁻¹ = 0 := by
    intro q hq
    have hp : q.2 ∉ R := by
      intro hp
      exact hq (Set.mk_mem_prod trivial hp)
    have hz : zOfPlane q.2 ∉ tsupport (almostAnalyticExtCut f) := by
      rw [Set.mem_prod, not_and_or] at hp
      rcases hp with h | h
      · rw [Set.mem_Ioc, not_and_or] at h
        rcases h with h | h
        · rw [not_lt] at h
          refine notMem_tsupport_of_le_abs_re hXsupp ?_
          have hre : (zOfPlane q.2).re = q.2.1 := by simp [zOfPlane]
          rw [hre, abs_of_nonpos (by linarith)]
          linarith
        · rw [not_le] at h
          refine notMem_tsupport_of_le_abs_re hXsupp ?_
          have hre : (zOfPlane q.2).re = q.2.1 := by simp [zOfPlane]
          rw [hre, abs_of_pos (by linarith)]
          linarith
      · rw [Set.mem_Ioc, not_and_or] at h
        rcases h with h | h
        · rw [not_lt] at h
          refine notMem_tsupport_almostAnalyticExtCut_of_lt_abs_im ?_
          have him : (zOfPlane q.2).im = q.2.2 := by simp [zOfPlane]
          rw [him, abs_of_nonpos (by linarith)]
          linarith
        · rw [not_le] at h
          refine notMem_tsupport_almostAnalyticExtCut_of_lt_abs_im ?_
          have him : (zOfPlane q.2).im = q.2.2 := by simp [zOfPlane]
          rw [him, abs_of_pos (by linarith)]
          linarith
    rw [dbarNum_eq_zero_of_notMem_tsupport hz, zero_mul]
  have hfin : (ν.prod (volume : Measure (ℝ × ℝ))) S < ⊤ := by
    rw [hSdef, Measure.prod_prod, hRdef, Measure.volume_eq_prod, Measure.prod_prod]
    have hν : ν Set.univ < ⊤ := IsFiniteMeasure.measure_univ_lt_top
    have h1 : (volume : Measure ℝ) (Set.Ioc (-X) X) < ⊤ := by
      rw [Real.volume_Ioc]; exact ENNReal.ofReal_lt_top
    have h2 : (volume : Measure ℝ) (Set.Ioc (-3 : ℝ) 3) < ⊤ := by
      rw [Real.volume_Ioc]; exact ENNReal.ofReal_lt_top
    exact ENNReal.mul_lt_top hν (ENNReal.mul_lt_top h1 h2)
  -- measurability of the joint integrand
  have hmeas : AEStronglyMeasurable
      (Function.uncurry fun (t : ℝ) (p : ℝ × ℝ) =>
        dbarNum f (zOfPlane p) * (zOfPlane p - (t : ℂ))⁻¹)
      (ν.prod (volume : Measure (ℝ × ℝ))) := by
    have hnum : Continuous (fun p : ℝ × ℝ => dbarNum f (zOfPlane p)) :=
      (continuous_dbarNum hf).comp continuous_zOfPlane
    have hinv : Measurable (fun q : ℝ × (ℝ × ℝ) =>
        (zOfPlane q.2 - (q.1 : ℂ))⁻¹) := by
      have hb : Measurable (fun q : ℝ × (ℝ × ℝ) => zOfPlane q.2 - (q.1 : ℂ)) := by
        unfold zOfPlane
        fun_prop
      exact hb.inv
    have hm : Measurable (Function.uncurry fun (t : ℝ) (p : ℝ × ℝ) =>
        dbarNum f (zOfPlane p) * (zOfPlane p - (t : ℂ))⁻¹) := by
      have hc : Measurable (fun q : ℝ × (ℝ × ℝ) => dbarNum f (zOfPlane q.2)) :=
        hnum.measurable.comp measurable_snd
      exact hc.mul hinv
    exact hm.aestronglyMeasurable
  have hbound : ∀ᵐ q ∂(ν.prod (volume : Measure (ℝ × ℝ))),
      ‖Function.uncurry (fun (t : ℝ) (p : ℝ × ℝ) =>
        dbarNum f (zOfPlane p) * (zOfPlane p - (t : ℂ))⁻¹) q‖ ≤ M :=
    Filter.Eventually.of_forall fun q => hM (zOfPlane q.2) q.1
  have hSint : IntegrableOn
      (Function.uncurry fun (t : ℝ) (p : ℝ × ℝ) =>
        dbarNum f (zOfPlane p) * (zOfPlane p - (t : ℂ))⁻¹) S
      (ν.prod (volume : Measure (ℝ × ℝ))) :=
    IntegrableOn.of_bound hfin hmeas.restrict M (ae_restrict_of_ae hbound)
  have hcint : IntegrableOn
      (Function.uncurry fun (t : ℝ) (p : ℝ × ℝ) =>
        dbarNum f (zOfPlane p) * (zOfPlane p - (t : ℂ))⁻¹) Sᶜ
      (ν.prod (volume : Measure (ℝ × ℝ))) := by
    have hae : (Function.uncurry fun (t : ℝ) (p : ℝ × ℝ) =>
        dbarNum f (zOfPlane p) * (zOfPlane p - (t : ℂ))⁻¹)
        =ᵐ[(ν.prod (volume : Measure (ℝ × ℝ))).restrict Sᶜ] 0 := by
      filter_upwards [ae_restrict_mem hSmeas.compl] with q hq
      exact hzero q hq
    exact (integrable_zero (α := ℝ × (ℝ × ℝ)) ℂ _).congr hae.symm
  have hInt : Integrable
      (Function.uncurry fun (t : ℝ) (p : ℝ × ℝ) =>
        dbarNum f (zOfPlane p) * (zOfPlane p - (t : ℂ))⁻¹)
      (ν.prod (volume : Measure (ℝ × ℝ))) := by
    have hunion : IntegrableOn
        (Function.uncurry fun (t : ℝ) (p : ℝ × ℝ) =>
          dbarNum f (zOfPlane p) * (zOfPlane p - (t : ℂ))⁻¹) (S ∪ Sᶜ)
        (ν.prod (volume : Measure (ℝ × ℝ))) := hSint.union hcint
    rwa [Set.union_compl_self, integrableOn_univ] at hunion
  calc ∫ t : ℝ, (f t : ℂ) ∂ν
      = ∫ t : ℝ, (I / (2 * (Real.pi : ℂ))) *
          (∫ p : ℝ × ℝ, dbarNum f (zOfPlane p) * (zOfPlane p - (t : ℂ))⁻¹) ∂ν := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun t => hpt t)
    _ = (I / (2 * (Real.pi : ℂ))) *
          ∫ t : ℝ, (∫ p : ℝ × ℝ,
            dbarNum f (zOfPlane p) * (zOfPlane p - (t : ℂ))⁻¹) ∂ν := by
        rw [integral_const_mul]
    _ = (I / (2 * (Real.pi : ℂ))) *
          ∫ p : ℝ × ℝ, (∫ t : ℝ,
            dbarNum f (zOfPlane p) * (zOfPlane p - (t : ℂ))⁻¹ ∂ν) ∂volume := by
        rw [integral_integral_swap hInt]
    _ = (I / (2 * (Real.pi : ℂ))) *
          ∫ p : ℝ × ℝ, dbarNum f (zOfPlane p) * stieltjesTransform ν (zOfPlane p) := by
        congr 1
        refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
        simp only [stieltjesTransform]
        rw [integral_const_mul]

end GUEStrongConvergence
