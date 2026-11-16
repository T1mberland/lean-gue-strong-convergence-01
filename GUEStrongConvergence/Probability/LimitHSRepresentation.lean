/-
# The limit-side Helffer–Sjöstrand trace representation

This file proves `LimitHSTraceRepresentation`: the operator-valued Cauchy–Pompeiu
representation of the limit trace.  The route avoids GNS theory and only uses the
Riesz–Markov–Kakutani spectral measure of a self-adjoint element in a state.

## Route

* `blockLimitSpectralMeasure` — the spectral probability measure of a self-adjoint
  element `h` of the block limit algebra in the matrix-amplified vacuum state
  `τ_d ⊗ τ` (`blockLimitState`), obtained from `FreeProbability.spectralMeasure`;
* `blockLimitState_expectation_limitCfc_eq_integral` — its defining property
  `τ_d(τ(f(h))) = ∫ f dν_h` for continuous `f`;
* `stieltjesTransform_blockLimitSpectralMeasure` — the Stieltjes transform of `ν_h`
  is `(card d)⁻¹ τ(Tr_d((z - h)⁻¹))`;
* `expectation_limitCfc_eq_planeIntegral` — combining the scalar measure
  Cauchy–Pompeiu identity `integral_eq_plane_integral_stieltjes` with the Stieltjes
  identification gives the exact `LimitHSTraceRepresentation` identity;
* `limitHSTraceRepresentation_of_contDiff` — the representation for `C²` compactly
  supported `f`.

No GNS representation, and no unproved analytic input, is used.
-/
import GUEStrongConvergence.Probability.LimitSideSpectral
import GUEStrongConvergence.Probability.MeasurePompeiu

noncomputable section

open MeasureTheory Complex Matrix FreeProbability FreeProbability.Fock
open scoped ComplexOrder Topology BigOperators

namespace GUEStrongConvergence

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

variable {r d : ℕ} [Nonempty (Fin d)]

local instance limitHsNontrivial : Nontrivial (closedSemicircularAlgebra (Fin r)) :=
  (closedGeneratedVacuumState (Fin r)).toProbabilitySpace.nontrivial

local instance limitHsPartialOrder : PartialOrder (closedSemicircularAlgebra (Fin r)) :=
  CStarAlgebra.spectralOrder _

local instance limitHsStarOrderedRing : StarOrderedRing (closedSemicircularAlgebra (Fin r)) :=
  CStarAlgebra.spectralOrderedRing _

local instance limitHsCfcComplex : ContinuousFunctionalCalculus ℂ (BlockLimit r d) IsStarNormal :=
  IsStarNormal.instContinuousFunctionalCalculus

local instance limitHsCfcReal : ContinuousFunctionalCalculus ℝ (BlockLimit r d) IsSelfAdjoint :=
  @IsSelfAdjoint.instContinuousFunctionalCalculus (BlockLimit r d) _ _ _ _ _

/-! ## 1. The spectral measure of the limit element -/

/-- The spectral probability measure of `h` in the matrix-amplified vacuum state
`τ_d ⊗ τ`.  By the Riesz–Markov–Kakutani theorem for the state
`f ↦ τ_d(τ(f(h)))`, it satisfies `τ_d(τ(f(h))) = ∫ f dν_h` for every continuous `f`. -/
abbrev blockLimitSpectralMeasure (h : BlockLimit r d) (hh : IsSelfAdjoint h) : Measure ℝ :=
  FreeProbability.spectralMeasure (A := BlockLimit r d) (blockLimitState r d) hh

instance blockLimitSpectralMeasure_isProbability (h : BlockLimit r d) (hh : IsSelfAdjoint h) :
    IsProbabilityMeasure (blockLimitSpectralMeasure h hh) := by
  unfold blockLimitSpectralMeasure
  infer_instance

/-- The spectral measure is concentrated on the compact real spectrum of `h`. -/
theorem support_blockLimitSpectralMeasure_subset_spectrum
    (h : BlockLimit r d) (hh : IsSelfAdjoint h) :
    (blockLimitSpectralMeasure h hh).support ⊆ spectrum ℝ h := by
  unfold blockLimitSpectralMeasure
  refine Measure.support_subset_of_isClosed
    (ContinuousFunctionalCalculus.isCompact_spectrum (A := BlockLimit r d) h).isClosed ?_
  rw [mem_ae_iff]
  exact FreeProbability.spectralMeasure_spectrum_compl (blockLimitState r d) hh

/-- The spectral measure is compactly supported: its support is contained in the compact
real spectrum. -/
theorem isCompact_support_blockLimitSpectralMeasure
    (h : BlockLimit r d) (hh : IsSelfAdjoint h) :
    IsCompact (blockLimitSpectralMeasure h hh).support :=
  (ContinuousFunctionalCalculus.isCompact_spectrum (A := BlockLimit r d) h).of_isClosed_subset
    Measure.isClosed_support (support_blockLimitSpectralMeasure_subset_spectrum h hh)

/-- **The spectral measure represents the amplified limit state.**  For continuous
`f : ℝ → ℝ`, the amplified state of `f(h)` is the integral of `f` against
`blockLimitSpectralMeasure`. -/
theorem blockLimitState_expectation_limitCfc_eq_integral
    (h : BlockLimit r d) (hh : IsSelfAdjoint h) (f : ℝ → ℝ) (hf : Continuous f) :
    (blockLimitState r d).expectation (limitCfc f h) =
      (∫ t : ℝ, f t ∂(blockLimitSpectralMeasure h hh) : ℝ) := by
  unfold limitCfc blockLimitSpectralMeasure
  exact FreeProbability.expectation_cfc_eq_integral (A := BlockLimit r d) (blockLimitState r d) hh f hf

/-- **Step B in trace form.**  The unnormalized limit trace of `f(h)` is the cardinality
of the matrix-amplification times the integral of `f` against the spectral measure. -/
theorem trace_limitCfc_eq_card_mul_integral
    (h : BlockLimit r d) (hh : IsSelfAdjoint h) (f : ℝ → ℝ) (hf : Continuous f) :
    (closedGeneratedVacuumState (Fin r)).expectation (Matrix.trace (limitCfc f h)) =
      (Fintype.card (Fin d) : ℂ) *
        ∫ t : ℝ, (f t : ℂ) ∂(blockLimitSpectralMeasure h hh) := by
  rw [trace_cfc_eq_card_mul_limitTraceCfcC]
  rw [show limitTraceCfcC f h = (blockLimitState r d).expectation (limitCfc f h) from rfl]
  rw [blockLimitState_expectation_limitCfc_eq_integral h hh f hf]
  rw [@integral_complex_ofReal ℝ _ (blockLimitSpectralMeasure h hh) f]

/-! ## 2. The complex functional calculus decomposition

We need the standard decomposition of the complex continuous functional calculus of a
self-adjoint element into real and imaginary parts, expressed through the real
calculus.  This is the statement of `cfc_complex_re_im` in the dependency, reproved
here because the file containing it is not part of the built dependency artifacts.
-/

/-- Real and imaginary parts give the complex continuous functional calculus
decomposition for a self-adjoint input. -/
theorem cfc_complex_re_im_of_selfAdjoint {A : Type*} [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] [T2Space A]
    [ContinuousFunctionalCalculus ℂ A IsStarNormal]
    [ContinuousFunctionalCalculus ℝ A IsSelfAdjoint]
    {a : A} (ha : IsSelfAdjoint a) (f : ℂ → ℂ)
    (hf : ContinuousOn f (spectrum ℂ a)) :
    cfc f a = cfc (fun x : ℝ => (f x).re) a +
      Complex.I • cfc (fun x : ℝ => (f x).im) a := by
  have hr : ContinuousOn (fun x => ((f x).re : ℂ)) (spectrum ℂ a) :=
    Complex.continuous_ofReal.comp_continuousOn (Complex.continuous_re.comp_continuousOn hf)
  have hi : ContinuousOn (fun x => ((f x).im : ℂ)) (spectrum ℂ a) :=
    Complex.continuous_ofReal.comp_continuousOn (Complex.continuous_im.comp_continuousOn hf)
  have he : f = fun x => ((f x).re : ℂ) + Complex.I • ((f x).im : ℂ) := by
    funext x
    simpa only [smul_eq_mul, mul_comm] using (Complex.re_add_im (f x)).symm
  calc
    cfc f a = cfc (fun x => ((f x).re : ℂ) + Complex.I • ((f x).im : ℂ)) a :=
      congrArg (fun g => cfc g a) he
    _ = cfc (fun x => ((f x).re : ℂ)) a +
          Complex.I • cfc (fun x => ((f x).im : ℂ)) a := by
      have hadd := cfc_add a (fun x => ((f x).re : ℂ))
        (fun x => Complex.I • ((f x).im : ℂ)) hr (hi.const_smul Complex.I)
      exact hadd.trans (congrArg (fun t => cfc (fun x => ((f x).re : ℂ)) a + t)
        (cfc_smul Complex.I (fun x => ((f x).im : ℂ)) a hi))
    _ = _ := by
      rw [cfc_complex_eq_real a (fun _ _ => by simp) ha,
        cfc_complex_eq_real a (fun _ _ => by simp) ha]
      simp only [Complex.ofReal_re]

/-! ## 3. The limit Stieltjes transform -/

/-- **The Stieltjes transform of the limit spectral measure.**  For nonreal `z`,
`∫ (z - t)⁻¹ dν_h(t) = (card d)⁻¹ τ(Tr_d((z - h)⁻¹))`. -/
theorem stieltjesTransform_blockLimitSpectralMeasure
    (h : BlockLimit r d) (hh : IsSelfAdjoint h) {z : ℂ} (hz : z.im ≠ 0) :
    stieltjesTransform (FreeProbability.spectralMeasure (A := BlockLimit r d)
        (blockLimitState r d) hh) z =
      (Fintype.card (Fin d) : ℂ)⁻¹ * blockLimitResolventTrace h z := by
  classical
  -- continuity of the real and imaginary parts on the real line
  have hcont : Continuous (fun t : ℝ => (z - (t : ℂ))⁻¹) := by
    refine Continuous.inv₀ (by fun_prop) ?_
    intro t ht
    have him := congrArg Complex.im ht
    simp at him
    exact hz him
  have hre : Continuous (fun t : ℝ => ((z - (t : ℂ))⁻¹).re) :=
    Complex.continuous_re.comp hcont
  have him : Continuous (fun t : ℝ => ((z - (t : ℂ))⁻¹).im) :=
    Complex.continuous_im.comp hcont
  -- integrability of the complex Stieltjes kernel against a probability measure
  have hne : ∀ t : ℝ, z - (t : ℂ) ≠ 0 := by
    intro t hzt
    have him := congrArg Complex.im hzt
    simp at him
    exact hz him
  have hInt : Integrable (fun t : ℝ => (z - (t : ℂ))⁻¹)
      (FreeProbability.spectralMeasure (A := BlockLimit r d) (blockLimitState r d) hh) := by
    refine Integrable.of_bound hcont.aestronglyMeasurable (|z.im|⁻¹) ?_
    filter_upwards with t
    have hzpos : 0 < |z.im| := abs_pos.mpr hz
    have hden : |z.im| ≤ ‖z - (t : ℂ)‖ := by
      have h1 : (z - (t : ℂ)).im = z.im := by simp
      calc |z.im| = |(z - (t : ℂ)).im| := by rw [h1]
        _ ≤ ‖z - (t : ℂ)‖ := Complex.abs_im_le_norm _
    have hnormpos : 0 < ‖z - (t : ℂ)‖ := norm_pos_iff.mpr (hne t)
    calc ‖(z - (t : ℂ))⁻¹‖ = (‖z - (t : ℂ)‖)⁻¹ := norm_inv _
      _ ≤ (|z.im|)⁻¹ := (inv_le_inv₀ hnormpos hzpos).mpr hden
  -- the resolvent is the complex cfc of the kernel
  have hspec : ∀ w ∈ spectrum ℂ h, z - w ≠ 0 := by
    intro w hw hzero
    have hwim : w.im = 0 := hh.im_eq_zero_of_mem_spectrum hw
    have hzw : z = w := sub_eq_zero.mp hzero
    rw [hzw, hwim] at hz
    exact hz rfl
  have hres : resolvent h z = cfc (fun w : ℂ => (z - w)⁻¹) h := by
    rw [resolvent, cfc_inv (f := fun w : ℂ => z - w) h hspec]
    rw [cfc_sub (f := fun _ : ℂ => z) (g := fun w : ℂ => w) h]
    rw [cfc_const z h, cfc_id' ℂ h]
  have hcontOn : ContinuousOn (fun w : ℂ => (z - w)⁻¹) (spectrum ℂ h) := by
    refine ContinuousOn.inv₀ (by fun_prop) ?_
    intro w hw hzero
    exact hspec w hw hzero
  have hdecomp := cfc_complex_re_im_of_selfAdjoint (A := BlockLimit r d) hh
    (fun w : ℂ => (z - w)⁻¹) hcontOn
  calc stieltjesTransform (FreeProbability.spectralMeasure (A := BlockLimit r d) (blockLimitState r d) hh) z
      = ∫ t : ℝ, (z - (t : ℂ))⁻¹ ∂(FreeProbability.spectralMeasure (A := BlockLimit r d) (blockLimitState r d) hh) := rfl
    _ = ((∫ t : ℝ, ((z - (t : ℂ))⁻¹).re ∂(FreeProbability.spectralMeasure (A := BlockLimit r d) (blockLimitState r d) hh) : ℝ) : ℂ) +
          (∫ t : ℝ, ((z - (t : ℂ))⁻¹).im ∂(FreeProbability.spectralMeasure (A := BlockLimit r d) (blockLimitState r d) hh) : ℝ) * I :=
        (integral_re_add_im hInt).symm
    _ = (blockLimitState r d).expectation
            (cfc (fun t : ℝ => ((z - (t : ℂ))⁻¹).re) h) +
          (blockLimitState r d).expectation
            (cfc (fun t : ℝ => ((z - (t : ℂ))⁻¹).im) h) * I := by
        rw [← FreeProbability.expectation_cfc_eq_integral (A := BlockLimit r d) (blockLimitState r d) hh _ hre,
          ← FreeProbability.expectation_cfc_eq_integral (A := BlockLimit r d) (blockLimitState r d) hh _ him]
        rfl
    _ = (blockLimitState r d).expectation
            (cfc (fun t : ℝ => ((z - (t : ℂ))⁻¹).re) h +
              I • cfc (fun t : ℝ => ((z - (t : ℂ))⁻¹).im) h) := by
        rw [map_add, map_smul, smul_eq_mul]
        ring
    _ = (blockLimitState r d).expectation (resolvent h z) := by
        rw [hres]
        exact congrArg (fun y => (blockLimitState r d).expectation y) hdecomp.symm
    _ = (Fintype.card (Fin d) : ℂ)⁻¹ * blockLimitResolventTrace h z := by
        unfold blockLimitState blockLimitResolventTrace
        rw [matrixStarState_expectation_eq_trace]
        rfl

/-! ## 4. The change of variables `ℂ ↔ ℝ × ℝ` -/

/-- Lebesgue measure on `ℂ` is the pushforward of the plane Lebesgue measure under
`p ↦ p.1 + i p.2`. -/
theorem integral_complex_eq_integral_plane (F : ℂ → ℂ) :
    (∫ z : ℂ, F z ∂volume) = ∫ p : ℝ × ℝ, F (zOfPlane p) ∂volume := by
  rw [← (Complex.volume_preserving_equiv_real_prod.symm).integral_comp' F]
  refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
  apply congrArg F
  apply Complex.ext <;> simp [zOfPlane]

/-! ## 5. The limit representation -/

/-- **The limit-side Cauchy–Pompeiu representation**, in the plane-integral form. -/
theorem expectation_limitCfc_eq_planeIntegral
    (h : BlockLimit r d) (hh : IsSelfAdjoint h) (f : ℝ → ℝ)
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    (closedGeneratedVacuumState (Fin r)).expectation (Matrix.trace (limitCfc f h)) =
      (I / (2 * (Real.pi : ℂ))) *
        ∫ z : ℂ, hsDbarWeight f z * blockLimitResolventTrace h z ∂volume := by
  classical
  have hcont : Continuous f := hf.continuous
  -- Step B: the trace is the cardinality times the integral against `ν_h`
  have hB := trace_limitCfc_eq_card_mul_integral h hh f hcont
  -- Step A: the scalar measure Cauchy--Pompeiu identity
  have hA := integral_eq_plane_integral_stieltjes
    (ν := blockLimitSpectralMeasure h hh) hf hfc
  -- Step C: the Stieltjes transform is the normalized limit resolvent trace a.e.
  have hC : ∀ᵐ p : ℝ × ℝ ∂(volume : Measure (ℝ × ℝ)),
      stieltjesTransform (blockLimitSpectralMeasure h hh) (zOfPlane p) =
        (Fintype.card (Fin d) : ℂ)⁻¹ * blockLimitResolventTrace h (zOfPlane p) := by
    have hnull : (volume : Measure (ℝ × ℝ)) {p : ℝ × ℝ | p.2 = 0} = 0 := by
      have hsub : {p : ℝ × ℝ | p.2 = 0} ⊆ Set.univ ×ˢ ({0} : Set ℝ) := by
        intro p hp
        exact Set.mem_prod.mpr ⟨trivial, by simpa using hp⟩
      refine measure_mono_null hsub ?_
      rw [Measure.volume_eq_prod, Measure.prod_prod]
      simp
    filter_upwards [(compl_mem_ae_iff).mpr hnull] with p hp
    have hp' : p.2 ≠ 0 := by simpa using hp
    have hz : (zOfPlane p).im ≠ 0 := by simpa [zOfPlane] using hp'
    exact stieltjesTransform_blockLimitSpectralMeasure h hh hz
  -- multiply by `card d` under the integral
  have hA' : (Fintype.card (Fin d) : ℂ) *
      ∫ p : ℝ × ℝ, dbarNum f (zOfPlane p) *
        stieltjesTransform (blockLimitSpectralMeasure h hh) (zOfPlane p) =
      ∫ p : ℝ × ℝ, dbarNum f (zOfPlane p) * blockLimitResolventTrace h (zOfPlane p) := by
    rw [← integral_const_mul]
    refine integral_congr_ae (hC.mono ?_)
    intro p hp
    change (Fintype.card (Fin d) : ℂ) * (dbarNum f (zOfPlane p) *
      stieltjesTransform (blockLimitSpectralMeasure h hh) (zOfPlane p)) =
      dbarNum f (zOfPlane p) * blockLimitResolventTrace h (zOfPlane p)
    rw [hp]
    have hcard : (Fintype.card (Fin d) : ℂ) ≠ 0 := by
      exact_mod_cast Fintype.card_ne_zero
    field_simp [hcard]
  calc (closedGeneratedVacuumState (Fin r)).expectation (Matrix.trace (limitCfc f h))
      = (Fintype.card (Fin d) : ℂ) *
          ∫ t : ℝ, (f t : ℂ) ∂(blockLimitSpectralMeasure h hh) := hB
    _ = (Fintype.card (Fin d) : ℂ) *
          ((I / (2 * (Real.pi : ℂ))) *
            ∫ p : ℝ × ℝ, dbarNum f (zOfPlane p) *
              stieltjesTransform (blockLimitSpectralMeasure h hh) (zOfPlane p)) := by
        rw [hA]
    _ = (I / (2 * (Real.pi : ℂ))) *
          ((Fintype.card (Fin d) : ℂ) *
            ∫ p : ℝ × ℝ, dbarNum f (zOfPlane p) *
              stieltjesTransform (blockLimitSpectralMeasure h hh) (zOfPlane p)) := by
        ring
    _ = (I / (2 * (Real.pi : ℂ))) *
          ∫ p : ℝ × ℝ, dbarNum f (zOfPlane p) * blockLimitResolventTrace h (zOfPlane p) := by
        rw [hA']
    _ = (I / (2 * (Real.pi : ℂ))) *
          ∫ z : ℂ, hsDbarWeight f z * blockLimitResolventTrace h z ∂volume := by
        rw [integral_complex_eq_integral_plane]
        congr 1

/-- **The limit-side Helffer–Sjöstrand trace representation.**  For `C²` compactly
supported `f` and self-adjoint `h` in the block limit algebra,
`τ(Tr_d(f(h))) = (I / 2π) ∫∫ ∂̄F(z) · τ(Tr_d((z - h)⁻¹))`. -/
theorem limitHSTraceRepresentation_of_contDiff
    (h : BlockLimit r d) (hh : IsSelfAdjoint h) (f : ℝ → ℝ)
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    LimitHSTraceRepresentation f h hh := by
  unfold LimitHSTraceRepresentation
  exact expectation_limitCfc_eq_planeIntegral h hh f hf hfc

/-! ## 6. The finite-matrix side -/

section FiniteSide

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **The finite-matrix trace Helffer–Sjöstrand representation.**  For a Hermitian matrix
`H` and `C²` compactly supported `f`,
`Tr(f(H)) = (I / 2π) ∫∫ ∂̄F(z) · Tr((z - H)⁻¹)`.
This is the finite-side counterpart of `LimitHSTraceRepresentation`, obtained from
`trace_cfc_eq_plane_integral_resolvent` and the change of variables `ℂ ↔ ℝ × ℝ`. -/
theorem finiteHSTraceRepresentation_of_contDiff
    (H : Matrix n n ℂ) (hH : H.IsHermitian) (f : ℝ → ℝ)
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    FiniteHSTraceRepresentation f H hH := by
  unfold FiniteHSTraceRepresentation finiteResolventTrace
  rw [Matrix.IsHermitian.cfc_eq hH f]
  rw [trace_cfc_eq_plane_integral_resolvent H hH hf hfc]
  congr 1
  rw [integral_complex_eq_integral_plane]
  congr 1
  funext p
  have hz : zOfPlane p = ((p.1 : ℂ) + (p.2 : ℂ) * I) := by simp [zOfPlane]
  rw [hz]
  have hw : hsDbarWeight f ((p.1 : ℂ) + (p.2 : ℂ) * I) =
      dbarNum f ((p.1 : ℂ) + (p.2 : ℂ) * I) := rfl
  have hr : resolvent H ((p.1 : ℂ) + (p.2 : ℂ) * I) =
      (((p.1 : ℂ) + (p.2 : ℂ) * I) • (1 : Matrix n n ℂ) - H)⁻¹ := by
    rw [resolvent, ← Matrix.nonsing_inv_eq_ringInverse, Algebra.algebraMap_eq_smul_one]
  rw [hw, hr]

end FiniteSide

end GUEStrongConvergence
