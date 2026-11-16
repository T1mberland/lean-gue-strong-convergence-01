/-
# Limit-side bookkeeping for the final reduction

This file closes the *limit-side bookkeeping* of the conditional final theorem
(`Probability/LemmaMWeighted.lean`): the vanishing of the plane limit statistic on the limit
spectrum, and the plane-integrability side conditions of the order-`k` comparison.

## Route

* `integral_eq_plane_integral_stieltjes_order` — the order-`k` scalar-measure
  Cauchy--Pompeiu identity, i.e. `integral_eq_plane_integral_stieltjes` with
  `dbarNumOrder (k+1)` in place of `dbarNum`, obtained from `pompeiu_plane_order_dbarNum`
  and a Fubini argument whose dominating function is the *already proved*
  `integrable_norm_dbarNumOrder_mul_inv_im_zOf`;
* `expectation_limitCfc_eq_planeIntegral_order` — **the order-`k` limit identity**:
  for `C^{k+1}` compactly supported `f` and self-adjoint `h` in the block limit algebra,
  `τ(Tr_d(f(h))) = (I/2π) ∫∫ ∂̄_k f(z) · Tr_d((z-h)⁻¹)`;
* `guePlaneLimitOrder_eq_re_limitTraceCfcC` — identification of the plane limit statistic
  `guePlaneLimitOrder` with the real limit statistic `Re τ_d(τ(f(h)))`, given the (definitional,
  at the canonical instantiation) identification of `Matrix.trace (operatorMatrixPencilCauchy)`
  with `blockLimitResolventTrace`;
* `guePlaneLimitOrder_eq_zero_of_eq_zero_on_spectrum` — **the vanishing**: if `f` vanishes on
  the limit spectrum then the plane limit statistic is zero;
* `integrable_dbarNumOrder_mul_trace_gueResolventMean` /
  `integrable_dbarNumOrder_mul_trace_operatorMatrixPencilCauchy` — the two plane-integrability
  side conditions, from the majorants `integrable_norm_dbarNumOrder_mul_inv_im_zOf` and the
  resolvent trace bounds;
* `WeightedStripInputs'` and `GUEStrongConvergenceStatement_of_weightedStripInputs'` — the
  shrunk bundle: the four plane-integrability fields and the two vanishing fields are gone;
* `trace_operatorMatrixPencilCauchy_eq_blockLimitResolventTrace` — **the closed-pencil
  bridge**: `Tr(operatorMatrixPencilCauchy A₀ A z)` is the block-limit resolvent trace of the
  canonical limit element `closedPencil A₀ A` (the pencil read in the closed semicircular
  algebra), for `z` in the resolvent set.  This turns the trace *identification* of
  `WeightedStripDataAt'` into a theorem;
* `WeightedStripInputs''` and `GUEStrongConvergenceStatement_of_weightedStripInputs''` — the
  **fully reduced** bundle: both identification fields of `WeightedStripDataAt'` are gone.  The
  limit element is the canonical `closedPencil A₀ A`, the trace identity is the bridge above,
  and the cutoff vanishing is stated on the honest limit spectrum
  `spectrum ℝ (closedPencil A₀ A)` rather than identified with
  `specC (h1PencilLimit r k F z)`.  The only statement that the previous bundle implies but this
  one does not is exactly that spectral identification (the Kronecker/affine coefficient identity
  recorded at `FlatGUEStatisticEq`).

No `sorry`, no new axioms.
-/
import GUEStrongConvergence.Probability.LemmaMWeighted
import GUEStrongConvergence.Probability.LemmaMLimitZero
import GUEStrongConvergence.Probability.LimitHSRepresentation

noncomputable section

open MeasureTheory Complex Matrix FreeProbability FreeProbability.Fock Filter ProbabilityTheory
open scoped ComplexOrder Topology BigOperators Ring

namespace GUEStrongConvergence

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

/-! ## 1. The order-`k` scalar measure Cauchy--Pompeiu identity -/

/-- **Scalar measure Cauchy--Pompeiu representation, order `k`.**  For a finite measure `ν` on
`ℝ`, `1 ≤ k`, and `C^{k+1}` compactly supported `f`,

`∫ f dν = (I / 2π) ∫∫ ∂̄_k f(z) · S_ν(z)`,

where `S_ν` is the Stieltjes transform of `ν` and `∂̄_k f = dbarNumOrder (k+1) f`.

The proof is the Fubini argument of `integral_eq_plane_integral_stieltjes`, with the uniform
dominating function `‖∂̄_k f(z)‖ |Im z|⁻¹` (integrable by
`integrable_norm_dbarNumOrder_mul_inv_im_zOf`) replacing the first-order uniform bound. -/
theorem integral_eq_plane_integral_stieltjes_order {ν : Measure ℝ} [IsFiniteMeasure ν]
    {f : ℝ → ℝ} {k K : ℕ} (hk : 1 ≤ k) (hf : ContDiff ℝ K f) (hK : k + 1 ≤ K)
    (hfc : HasCompactSupport f) :
    (∫ t : ℝ, (f t : ℂ) ∂ν) =
      (I / (2 * (Real.pi : ℂ))) *
        ∫ p : ℝ × ℝ, dbarNumOrder (k + 1) f (zOf p) * stieltjesTransform ν (zOf p) := by
  classical
  -- the pointwise identity, from the order-`k` plane identity
  have hpt : ∀ t : ℝ, (f t : ℂ) =
      (I / (2 * (Real.pi : ℂ))) * ∫ p : ℝ × ℝ,
        dbarNumOrder (k + 1) f (zOf p) * (zOf p - (t : ℂ))⁻¹ := by
    intro t
    have h := pompeiu_plane_order_dbarNum (f := f) (k := k + 1) (K := K) (by omega) hf hK hfc t
    simpa [zOf] using h
  -- joint measurability
  have hmeas : Measurable (Function.uncurry fun (t : ℝ) (p : ℝ × ℝ) =>
      dbarNumOrder (k + 1) f (zOf p) * (zOf p - (t : ℂ))⁻¹) := by
    have hz : Measurable (fun q : ℝ × (ℝ × ℝ) => zOf q.2) :=
      continuous_zOf.measurable.comp measurable_snd
    have hd : Measurable (fun q : ℝ × (ℝ × ℝ) => dbarNumOrder (k + 1) f (zOf q.2)) :=
      (continuous_dbarNumOrder hf hK).measurable.comp hz
    have hb : Measurable (fun q : ℝ × (ℝ × ℝ) => zOf q.2 - (q.1 : ℂ)) :=
      (continuous_zOf.comp continuous_snd).sub
        (Complex.continuous_ofReal.comp continuous_fst) |>.measurable
    exact hd.mul hb.inv
  -- the pointwise dominating bound
  have hbnd : ∀ q : ℝ × (ℝ × ℝ),
      ‖Function.uncurry (fun (t : ℝ) (p : ℝ × ℝ) =>
        dbarNumOrder (k + 1) f (zOf p) * (zOf p - (t : ℂ))⁻¹) q‖
      ≤ ‖dbarNumOrder (k + 1) f (zOf q.2)‖ * |q.2.2|⁻¹ := by
    intro q
    obtain ⟨t, p⟩ := q
    rw [Function.uncurry_apply_pair, norm_mul]
    rcases eq_or_ne p.2 0 with h0 | h0
    · have hzp : zOf p = ((p.1 : ℝ) : ℂ) := by simp [zOf, h0]
      have hz0 : dbarNumOrder (k + 1) f (zOf p) = 0 := by
        rw [hzp]
        exact dbarNumOrder_succ_ofReal hk hf hK p.1
      simp [hz0, h0]
    · have him : (zOf p).im = p.2 := zOf_im p
      have hden : |p.2| ≤ ‖zOf p - (t : ℂ)‖ := by
        calc |p.2| = |(zOf p - (t : ℂ)).im| := by
              rw [Complex.sub_im, zOf_im]; simp
          _ ≤ ‖zOf p - (t : ℂ)‖ := Complex.abs_im_le_norm _
      have hpos : 0 < |p.2| := abs_pos.mpr h0
      have hnormpos : 0 < ‖zOf p - (t : ℂ)‖ := lt_of_lt_of_le hpos hden
      have hinv : ‖(zOf p - (t : ℂ))⁻¹‖ ≤ |p.2|⁻¹ := by
        rw [norm_inv]
        exact (inv_le_inv₀ hnormpos hpos).mpr hden
      exact mul_le_mul_of_nonneg_left hinv (norm_nonneg _)
  -- the dominating function is integrable on the product
  have hg : Integrable (fun p : ℝ × ℝ => ‖dbarNumOrder (k + 1) f (zOf p)‖ * |p.2|⁻¹)
      (volume : Measure (ℝ × ℝ)) :=
    integrable_norm_dbarNumOrder_mul_inv_im_zOf hk hf hK hfc
  have hdom : Integrable (fun q : ℝ × (ℝ × ℝ) =>
      ‖dbarNumOrder (k + 1) f (zOf q.2)‖ * |q.2.2|⁻¹)
      (ν.prod (volume : Measure (ℝ × ℝ))) := hg.comp_snd ν
  have hInt : Integrable (Function.uncurry fun (t : ℝ) (p : ℝ × ℝ) =>
      dbarNumOrder (k + 1) f (zOf p) * (zOf p - (t : ℂ))⁻¹)
      (ν.prod (volume : Measure (ℝ × ℝ))) :=
    Integrable.mono' hdom hmeas.aestronglyMeasurable (Eventually.of_forall hbnd)
  calc ∫ t : ℝ, (f t : ℂ) ∂ν
      = ∫ t : ℝ, (I / (2 * (Real.pi : ℂ))) * (∫ p : ℝ × ℝ,
          dbarNumOrder (k + 1) f (zOf p) * (zOf p - (t : ℂ))⁻¹) ∂ν :=
        integral_congr_ae (Eventually.of_forall hpt)
    _ = (I / (2 * (Real.pi : ℂ))) * ∫ t : ℝ, (∫ p : ℝ × ℝ,
          dbarNumOrder (k + 1) f (zOf p) * (zOf p - (t : ℂ))⁻¹) ∂ν :=
        integral_const_mul _ _
    _ = (I / (2 * (Real.pi : ℂ))) * ∫ p : ℝ × ℝ, (∫ t : ℝ,
          dbarNumOrder (k + 1) f (zOf p) * (zOf p - (t : ℂ))⁻¹ ∂ν) ∂volume := by
        rw [integral_integral_swap hInt]
    _ = (I / (2 * (Real.pi : ℂ))) * ∫ p : ℝ × ℝ,
          dbarNumOrder (k + 1) f (zOf p) * stieltjesTransform ν (zOf p) := by
        congr 1
        refine integral_congr_ae (Eventually.of_forall fun p => ?_)
        simp only [stieltjesTransform]
        rw [integral_const_mul]

/-! ## 2. The order-`k` limit identity -/

section LimitIdentity

variable {r d : ℕ} [Nonempty (Fin d)]

local instance bridgeNontrivial : Nontrivial (closedSemicircularAlgebra (Fin r)) :=
  (closedGeneratedVacuumState (Fin r)).toProbabilitySpace.nontrivial

local instance bridgePartialOrder : PartialOrder (closedSemicircularAlgebra (Fin r)) :=
  CStarAlgebra.spectralOrder _

local instance bridgeStarOrderedRing : StarOrderedRing (closedSemicircularAlgebra (Fin r)) :=
  CStarAlgebra.spectralOrderedRing _

local instance bridgeCfcComplex : ContinuousFunctionalCalculus ℂ (BlockLimit r d) IsStarNormal :=
  IsStarNormal.instContinuousFunctionalCalculus

local instance bridgeCfcReal : ContinuousFunctionalCalculus ℝ (BlockLimit r d) IsSelfAdjoint :=
  @IsSelfAdjoint.instContinuousFunctionalCalculus (BlockLimit r d) _ _ _ _ _

/-- **The order-`k` limit-side Cauchy--Pompeiu representation.**  For `1 ≤ k`, self-adjoint
`h` in the block limit algebra and `C^{k+1}` compactly supported `f`,

`τ(Tr_d(f(h))) = (I / 2π) ∫∫ ∂̄_k f(z) · Tr_d((z - h)⁻¹)`,

the order-`k` analogue of `expectation_limitCfc_eq_planeIntegral` (which is the `k = 1` case,
with the first-order extension `almostAnalyticExtCut`).  The test function meets the order-`k`
extension `almostAnalyticExtOrderCut (k+1)`, so the weight is `dbarNumOrder (k+1) f`. -/
theorem expectation_limitCfc_eq_planeIntegral_order {k K : ℕ} (hk : 1 ≤ k)
    (h : BlockLimit r d) (hh : IsSelfAdjoint h) (f : ℝ → ℝ)
    (hf : ContDiff ℝ K f) (hK : k + 1 ≤ K) (hfc : HasCompactSupport f) :
    (closedGeneratedVacuumState (Fin r)).expectation (Matrix.trace (limitCfc f h)) =
      (I / (2 * (Real.pi : ℂ))) *
        ∫ p : ℝ × ℝ, dbarNumOrder (k + 1) f (zOf p) * blockLimitResolventTrace h (zOf p) := by
  classical
  have hcont : Continuous f := hf.continuous
  -- Step B: the trace is the cardinality times the integral against `ν_h`
  have hB := trace_limitCfc_eq_card_mul_integral h hh f hcont
  -- Step A: the order-`k` scalar measure Cauchy--Pompeiu identity
  have hA := integral_eq_plane_integral_stieltjes_order
    (ν := blockLimitSpectralMeasure h hh) hk hf hK hfc
  -- Step C: the Stieltjes transform is the normalized limit resolvent trace a.e.
  have hC : ∀ᵐ p : ℝ × ℝ ∂(volume : Measure (ℝ × ℝ)),
      stieltjesTransform (blockLimitSpectralMeasure h hh) (zOf p) =
        (Fintype.card (Fin d) : ℂ)⁻¹ * blockLimitResolventTrace h (zOf p) := by
    have hnull : (volume : Measure (ℝ × ℝ)) {p : ℝ × ℝ | p.2 = 0} = 0 := by
      have hsub : {p : ℝ × ℝ | p.2 = 0} ⊆ Set.univ ×ˢ ({0} : Set ℝ) := by
        intro p hp
        exact Set.mem_prod.mpr ⟨trivial, by simpa using hp⟩
      refine measure_mono_null hsub ?_
      rw [Measure.volume_eq_prod, Measure.prod_prod]
      simp
    filter_upwards [(compl_mem_ae_iff).mpr hnull] with p hp
    have hp' : p.2 ≠ 0 := by simpa using hp
    have hz : (zOf p).im ≠ 0 := by simpa [zOf] using hp'
    exact stieltjesTransform_blockLimitSpectralMeasure h hh hz
  -- multiply by `card d` under the integral
  have hA' : (Fintype.card (Fin d) : ℂ) *
      ∫ p : ℝ × ℝ, dbarNumOrder (k + 1) f (zOf p) *
        stieltjesTransform (blockLimitSpectralMeasure h hh) (zOf p) =
      ∫ p : ℝ × ℝ, dbarNumOrder (k + 1) f (zOf p) * blockLimitResolventTrace h (zOf p) := by
    rw [← integral_const_mul]
    refine integral_congr_ae (hC.mono ?_)
    intro p hp
    change (Fintype.card (Fin d) : ℂ) * (dbarNumOrder (k + 1) f (zOf p) *
      stieltjesTransform (blockLimitSpectralMeasure h hh) (zOf p)) =
      dbarNumOrder (k + 1) f (zOf p) * blockLimitResolventTrace h (zOf p)
    rw [hp]
    have hcard : (Fintype.card (Fin d) : ℂ) ≠ 0 := by
      exact_mod_cast Fintype.card_ne_zero
    field_simp [hcard]
  calc (closedGeneratedVacuumState (Fin r)).expectation (Matrix.trace (limitCfc f h))
      = (Fintype.card (Fin d) : ℂ) *
          ∫ t : ℝ, (f t : ℂ) ∂(blockLimitSpectralMeasure h hh) := hB
    _ = (Fintype.card (Fin d) : ℂ) *
          ((I / (2 * (Real.pi : ℂ))) *
            ∫ p : ℝ × ℝ, dbarNumOrder (k + 1) f (zOf p) *
              stieltjesTransform (blockLimitSpectralMeasure h hh) (zOf p)) := by
        rw [hA]
    _ = (I / (2 * (Real.pi : ℂ))) *
          ((Fintype.card (Fin d) : ℂ) *
            ∫ p : ℝ × ℝ, dbarNumOrder (k + 1) f (zOf p) *
              stieltjesTransform (blockLimitSpectralMeasure h hh) (zOf p)) := by
        ring
    _ = (I / (2 * (Real.pi : ℂ))) *
          ∫ p : ℝ × ℝ, dbarNumOrder (k + 1) f (zOf p) *
            blockLimitResolventTrace h (zOf p) := by
        rw [hA']

end LimitIdentity

/-! ## 3. Identification with the limit trace statistic, and vanishing -/

section Vanishing

variable {r d : ℕ} [Nonempty (Fin d)]

/-- **The plane limit statistic is the real limit trace statistic.**  If the trace of the
operator-valued Cauchy transform is the limit resolvent trace of `h`, then

`guePlaneLimitOrder k A₀ A f = Re τ_d(τ(f(h)))`.

At the canonical instantiation `h` is the affine Fock pencil read in the block algebra, and the
identification is `trace_operatorMatrixPencilCauchy` (with `Matrix.trace` of the pencil resolvent
in place of the block-limit resolvent trace). -/
theorem guePlaneLimitOrder_eq_re_limitTraceCfcC {k K : ℕ} (hk : 1 ≤ k)
    {A₀ : Matrix (Fin d) (Fin d) ℂ} {A : Fin r → Matrix (Fin d) (Fin d) ℂ}
    {h : BlockLimit r d} (hh : IsSelfAdjoint h)
    (hres : ∀ z : ℂ, z.im ≠ 0 → Matrix.trace (operatorMatrixPencilCauchy A₀ A z) =
      blockLimitResolventTrace h z)
    {f : ℝ → ℝ} (hf : ContDiff ℝ K f) (hK : k + 1 ≤ K) (hfc : HasCompactSupport f) :
    guePlaneLimitOrder k A₀ A f = (limitTraceCfcC f h).re := by
  have hlim := expectation_limitCfc_eq_planeIntegral_order (d := d) hk h hh f hf hK hfc
  have hint : (∫ p : ℝ × ℝ, dbarNumOrder (k + 1) f (zOf p) *
        Matrix.trace (operatorMatrixPencilCauchy A₀ A (zOf p))) =
      ∫ p : ℝ × ℝ, dbarNumOrder (k + 1) f (zOf p) * blockLimitResolventTrace h (zOf p) := by
    refine integral_congr_ae ?_
    filter_upwards [(compl_mem_ae_iff).mpr volume_im_eq_zero] with p hp
    have hz : (zOf p).im ≠ 0 := by simpa [zOf] using hp
    simp only [hres _ hz]
  have htr : limitTraceCfcC f h = ((Fintype.card (Fin d) : ℂ))⁻¹ *
      ((I / (2 * (Real.pi : ℂ))) *
        ∫ p : ℝ × ℝ, dbarNumOrder (k + 1) f (zOf p) *
          blockLimitResolventTrace h (zOf p)) := by
    rw [limitTraceCfcC_eq_trace, hlim]
  rw [show guePlaneLimitOrder k A₀ A f = (Fintype.card (Fin d) : ℝ)⁻¹ *
      ((I / (2 * (Real.pi : ℂ))) *
        ∫ p : ℝ × ℝ, dbarNumOrder (k + 1) f (zOf p) *
          Matrix.trace (operatorMatrixPencilCauchy A₀ A (zOf p))).re from rfl,
    hint, htr]
  have hcast : ((Fintype.card (Fin d) : ℂ))⁻¹ =
      (((Fintype.card (Fin d) : ℝ))⁻¹ : ℂ) := by
    push_cast
    ring
  rw [hcast, Complex.mul_re]
  simp

/-- **Vanishing of the plane limit statistic on the limit spectrum.**  If `f` vanishes on the
spectrum of the limit element `h`, then `guePlaneLimitOrder k A₀ A f = 0`.

This is the order-`k` analogue of `limitTraceCfc_eq_zero_of_eq_zero_on_spectrum`, and it removes
the two vanishing fields of `WeightedStripDataAt` from the analytic input. -/
theorem guePlaneLimitOrder_eq_zero_of_eq_zero_on_spectrum {k K : ℕ} (hk : 1 ≤ k)
    {A₀ : Matrix (Fin d) (Fin d) ℂ} {A : Fin r → Matrix (Fin d) (Fin d) ℂ}
    {h : BlockLimit r d} (hh : IsSelfAdjoint h)
    (hres : ∀ z : ℂ, z.im ≠ 0 → Matrix.trace (operatorMatrixPencilCauchy A₀ A z) =
      blockLimitResolventTrace h z)
    {f : ℝ → ℝ} (hf : ContDiff ℝ K f) (hK : k + 1 ≤ K) (hfc : HasCompactSupport f)
    (hzero : ∀ x ∈ spectrum ℝ h, f x = 0) :
    guePlaneLimitOrder k A₀ A f = 0 := by
  rw [guePlaneLimitOrder_eq_re_limitTraceCfcC hk hh hres hf hK hfc,
    limitTraceCfcC_eq_zero_of_eq_zero_on_spectrum hh hf.continuous.continuousOn hzero]
  simp

/-- **The limit-spectrum vanishing from a strengthened cutoff.**  If a smooth cutoff vanishes,
together with its derivative, on a set `S` containing the spectrum of the limit element, then it
vanishes on the limit spectrum.  This is the mechanical step that produces the `hzero` field of
`WeightedStripDataAt'` from `IsSmoothCutoffZeroOn (specC (h1PencilLimit r k F z)) ε f`; the only
remaining input is the linearization identity
`spectrum ℝ (operatorMatrixPencil A₀ A) ⊆ specC (h1PencilLimit r k F z)` (at the canonical
instantiation the two spectra are the spectrum of the same canonical polynomial). -/
theorem eq_zero_and_deriv_eq_zero_on_spectrum_of_isSmoothCutoffZeroOn
    {f : ℝ → ℝ} {S : Set ℝ} {ε : ℝ} {h : BlockLimit r d}
    (hcut : IsSmoothCutoffZeroOn S ε f) (hsub : spectrum ℝ h ⊆ S) :
    ∀ x ∈ spectrum ℝ h, f x = 0 ∧ deriv f x = 0 :=
  fun x hx => ⟨hcut.eq_zero x (hsub hx), hcut.deriv_eq_zero x (hsub hx)⟩

end Vanishing


/-! ## 4. The plane-integrability side conditions

Both side conditions of `smooth_trace_comparison_of_mean_bound_order` are discharged from the
majorant `‖∂̄_k f(z)‖ |Im z|⁻¹` (`integrable_norm_dbarNumOrder_mul_inv_im_zOf`) and the resolvent
trace bounds `‖Tr(g_N(z))‖ ≤ (card d)² |Im z|⁻¹` and `‖Tr(g(z))‖ ≤ card d · |Im z|⁻¹`.  The only
non-trivial point is the joint measurability of the resolvent trace in the spectral parameter;
on the limit side we obtain it from the Stieltjes transform `∫ (z - t)⁻¹ dν` of the limit
spectral measure, which is an integral over the measure variable. -/

/-! ### The finite side -/

section FiniteIntegrability

variable {ι d : Type*} {N : ℕ} [Fintype ι] [Fintype d] [DecidableEq d] [DecidableEq ι]
  [Nonempty d]

/-- The plane trace of the finite-`N` averaged resolvent is a.e. strongly measurable:
`Tr(g_N(z)) = N⁻¹ ∫ Tr((z - H_N(x))⁻¹) dx` and the joint integrand is measurable. -/
theorem aestronglyMeasurable_trace_gueResolventMean (hN : 0 < N)
    (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    (hA₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian) :
    AEStronglyMeasurable (fun p : ℝ × ℝ =>
      Matrix.trace (gueResolventMean (N := N) A₀ A (zOf p)))
      (volume : Measure (ℝ × ℝ)) := by
  have hjoint : Measurable (fun q : (EuclideanSpace ℝ (GUECoord ι N)) × ℂ =>
      Matrix.trace ((q.2 • (1 : Matrix (d × Fin N) (d × Fin N) ℂ) -
        guePencilMatrix A₀ A q.1)⁻¹)) := by
    have hmat : Measurable (fun q : (EuclideanSpace ℝ (GUECoord ι N)) × ℂ =>
        q.2 • (1 : Matrix (d × Fin N) (d × Fin N) ℂ) - guePencilMatrix A₀ A q.1) := by
      refine Matrix.measurable_iff.mpr (fun a b => ?_)
      have hentry : ∀ q : (EuclideanSpace ℝ (GUECoord ι N)) × ℂ,
          (q.2 • (1 : Matrix (d × Fin N) (d × Fin N) ℂ) - guePencilMatrix A₀ A q.1) a b
            = (if a = b then q.2 else 0) - guePencilMatrix A₀ A q.1 a b := by
        intro q
        rw [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
        by_cases hab : a = b <;> simp [hab]
      simp only [hentry]
      refine Measurable.sub ?_ ?_
      · by_cases hab : a = b
        · simp only [hab, ite_true]; exact measurable_snd
        · simp only [hab, ite_false]; exact measurable_const
      · exact Matrix.measurable_apply.comp
          ((continuous_guePencilMatrix A₀ A).measurable.comp measurable_fst)
    exact measurable_matrix_trace.comp (measurable_matrix_inv.comp hmat)
  have hint : StronglyMeasurable (fun z : ℂ => ∫ x : EuclideanSpace ℝ (GUECoord ι N),
      Matrix.trace ((z • (1 : Matrix (d × Fin N) (d × Fin N) ℂ) -
        guePencilMatrix A₀ A x)⁻¹)
        ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))) :=
    hjoint.stronglyMeasurable.integral_prod_left
  have h1 : AEStronglyMeasurable (fun p : ℝ × ℝ => (N : ℂ)⁻¹ *
      ∫ x : EuclideanSpace ℝ (GUECoord ι N),
        Matrix.trace ((zOf p • (1 : Matrix (d × Fin N) (d × Fin N) ℂ) -
          guePencilMatrix A₀ A x)⁻¹)
          ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))) (volume : Measure (ℝ × ℝ)) :=
    ((hint.measurable.comp continuous_zOf.measurable).const_mul _).aestronglyMeasurable
  refine h1.congr ?_
  filter_upwards [(compl_mem_ae_iff).mpr volume_im_eq_zero] with p hp
  have hz : (zOf p).im ≠ 0 := by simpa [zOf] using hp
  have heq := integral_trace_guePencilResolvent_eq A₀ A hA₀ hA hN (z := zOf p) hz
  rw [heq]
  have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  field_simp

/-- **The finite-side plane integrability.**  Eventually in `N`, the product of `∂̄_k f` with the
trace of the averaged resolvent is integrable on the plane. -/
theorem eventually_integrable_dbarNumOrder_mul_trace_gueResolventMean
    (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ) (hA₀ : A₀.IsHermitian)
    (hA : ∀ i, (A i).IsHermitian) {f : ℝ → ℝ} {k K : ℕ} (hk : 1 ≤ k)
    (hf : ContDiff ℝ K f) (hK : k + 1 ≤ K) (hfc : HasCompactSupport f) :
    ∀ᶠ N : ℕ in atTop, Integrable (fun p : ℝ × ℝ =>
      dbarNumOrder (k + 1) f (zOf p) *
        Matrix.trace (gueResolventMean (N := N) A₀ A (zOf p)))
      (volume : Measure (ℝ × ℝ)) := by
  filter_upwards [Filter.eventually_gt_atTop (0 : ℕ)] with N hN
  have hg := integrable_norm_dbarNumOrder_mul_inv_im_zOf hk hf hK hfc
  set C : ℝ := (Fintype.card d : ℝ) * (Fintype.card d : ℝ) with hC
  refine Integrable.mono' (hg.mul_const C) ?_ ?_
  · exact (((continuous_dbarNumOrder hf hK).comp continuous_zOf).measurable
      |>.aestronglyMeasurable).mul
      (aestronglyMeasurable_trace_gueResolventMean hN A₀ A hA₀ hA)
  · filter_upwards with p
    rw [norm_mul]
    rcases eq_or_ne p.2 0 with h0 | h0
    · have hzp : zOf p = ((p.1 : ℝ) : ℂ) := by simp [zOf, h0]
      have hz0 : dbarNumOrder (k + 1) f (zOf p) = 0 := by
        rw [hzp]
        exact dbarNumOrder_succ_ofReal hk hf hK p.1
      simp [hz0]
    · have hz : (zOf p).im ≠ 0 := by simpa [zOf] using h0
      have hcard : (0 : ℝ) ≤ (Fintype.card d : ℝ) := by positivity
      have hfrob := frob_gueResolventMean_le_abs A₀ A hA₀ hA (zOf p) hz hN
      have htr : ‖Matrix.trace (gueResolventMean (N := N) A₀ A (zOf p))‖ ≤
          (Fintype.card d : ℝ) * ((Fintype.card d : ℝ) * |p.2|⁻¹) := by
        refine (norm_trace_gueResolventMean_le A₀ A (zOf p) hfrob).trans ?_
        refine mul_le_mul_of_nonneg_left ?_ hcard
        simp
      refine (mul_le_mul_of_nonneg_left htr (norm_nonneg _)).trans (le_of_eq ?_)
      rw [hC]
      ring

end FiniteIntegrability

/-! ### The limit side -/

section LimitIntegrability

variable {r d : ℕ} [Nonempty (Fin d)]

local instance limIntNontrivial : Nontrivial (closedSemicircularAlgebra (Fin r)) :=
  (closedGeneratedVacuumState (Fin r)).toProbabilitySpace.nontrivial

local instance limIntPartialOrder : PartialOrder (closedSemicircularAlgebra (Fin r)) :=
  CStarAlgebra.spectralOrder _

local instance limIntStarOrderedRing : StarOrderedRing (closedSemicircularAlgebra (Fin r)) :=
  CStarAlgebra.spectralOrderedRing _

local instance limIntCfcComplex : ContinuousFunctionalCalculus ℂ (BlockLimit r d) IsStarNormal :=
  IsStarNormal.instContinuousFunctionalCalculus

local instance limIntCfcReal : ContinuousFunctionalCalculus ℝ (BlockLimit r d) IsSelfAdjoint :=
  @IsSelfAdjoint.instContinuousFunctionalCalculus (BlockLimit r d) _ _ _ _ _

/-- The Stieltjes transform of a finite measure is measurable in the spectral parameter: it is
the integral of the jointly measurable kernel `(z - t)⁻¹` in the measure variable. -/
theorem aestronglyMeasurable_stieltjesTransform_zOf {ν : Measure ℝ} [IsFiniteMeasure ν] :
    AEStronglyMeasurable (fun p : ℝ × ℝ => stieltjesTransform ν (zOf p))
      (volume : Measure (ℝ × ℝ)) := by
  have hker : Measurable (fun q : ℝ × ℂ => (q.2 - (q.1 : ℂ))⁻¹) := by
    refine Measurable.inv ?_
    exact (measurable_snd.sub (Complex.measurable_ofReal.comp measurable_fst))
  have hSm : StronglyMeasurable (fun z : ℂ => ∫ t : ℝ, (z - (t : ℂ))⁻¹ ∂ν) :=
    hker.stronglyMeasurable.integral_prod_left
  exact (hSm.measurable.comp continuous_zOf.measurable).aestronglyMeasurable

/-- Uniform bound on the limit resolvent trace: `‖Tr_d((z-h)⁻¹)‖ ≤ card d · |Im z|⁻¹`. -/
theorem norm_blockLimitResolventTrace_le (h : BlockLimit r d) (hh : IsSelfAdjoint h) {z : ℂ}
    (hz : z.im ≠ 0) :
    ‖blockLimitResolventTrace h z‖ ≤ (Fintype.card (Fin d) : ℝ) * |z.im|⁻¹ := by
  have hS : ‖stieltjesTransform (blockLimitSpectralMeasure h hh) z‖ ≤ |z.im|⁻¹ := by
    have hbound : ∀ t : ℝ, ‖(z - (t : ℂ))⁻¹‖ ≤ |z.im|⁻¹ := by
      intro t
      rw [norm_inv]
      have hden : |z.im| ≤ ‖z - (t : ℂ)‖ := by
        calc |z.im| = |(z - (t : ℂ)).im| := by simp
          _ ≤ ‖z - (t : ℂ)‖ := Complex.abs_im_le_norm _
      have hpos : 0 < |z.im| := abs_pos.mpr hz
      exact (inv_le_inv₀ (lt_of_lt_of_le hpos hden) hpos).mpr hden
    have h := norm_integral_le_of_norm_le_const
      (μ := blockLimitSpectralMeasure h hh)
      (f := fun t : ℝ => (z - (t : ℂ))⁻¹) (C := |z.im|⁻¹)
      (Eventually.of_forall hbound)
    simpa [stieltjesTransform] using h
  have heq := stieltjesTransform_blockLimitSpectralMeasure h hh hz
  calc ‖blockLimitResolventTrace h z‖
      = ‖(Fintype.card (Fin d) : ℂ) * stieltjesTransform (blockLimitSpectralMeasure h hh) z‖ := by
        rw [heq]
        have hcard : (Fintype.card (Fin d) : ℂ) ≠ 0 := by
          exact_mod_cast Fintype.card_ne_zero
        field_simp
    _ = (Fintype.card (Fin d) : ℝ) * ‖stieltjesTransform (blockLimitSpectralMeasure h hh) z‖ := by
        rw [norm_mul, Complex.norm_natCast]
    _ ≤ (Fintype.card (Fin d) : ℝ) * |z.im|⁻¹ :=
        mul_le_mul_of_nonneg_left hS (by positivity)

/-- **The limit-side plane integrability** (in the block-limit form): the product of `∂̄_k f`
with the limit resolvent trace is integrable on the plane. -/
theorem integrable_dbarNumOrder_mul_blockLimitResolventTrace
    (h : BlockLimit r d) (hh : IsSelfAdjoint h) {f : ℝ → ℝ} {k K : ℕ} (hk : 1 ≤ k)
    (hf : ContDiff ℝ K f) (hK : k + 1 ≤ K) (hfc : HasCompactSupport f) :
    Integrable (fun p : ℝ × ℝ =>
      dbarNumOrder (k + 1) f (zOf p) * blockLimitResolventTrace h (zOf p))
      (volume : Measure (ℝ × ℝ)) := by
  have hg := integrable_norm_dbarNumOrder_mul_inv_im_zOf hk hf hK hfc
  set C : ℝ := (Fintype.card (Fin d) : ℝ) with hC
  refine Integrable.mono' (hg.mul_const C) ?_ ?_
  · have hS := aestronglyMeasurable_stieltjesTransform_zOf
      (ν := blockLimitSpectralMeasure h hh)
    have h2 : AEStronglyMeasurable (fun p : ℝ × ℝ => dbarNumOrder (k + 1) f (zOf p) *
        ((Fintype.card (Fin d) : ℂ) *
          stieltjesTransform (blockLimitSpectralMeasure h hh) (zOf p)))
        (volume : Measure (ℝ × ℝ)) :=
      ((continuous_dbarNumOrder hf hK).comp continuous_zOf).measurable.aestronglyMeasurable.mul
        (hS.const_mul _)
    refine h2.congr ?_
    filter_upwards [(compl_mem_ae_iff).mpr volume_im_eq_zero] with p hp
    have hz : (zOf p).im ≠ 0 := by simpa [zOf] using hp
    rw [stieltjesTransform_blockLimitSpectralMeasure h hh hz]
    have hcard : (Fintype.card (Fin d) : ℂ) ≠ 0 := by
      exact_mod_cast Fintype.card_ne_zero
    have hone : (Fintype.card (Fin d) : ℂ) *
        ((Fintype.card (Fin d) : ℂ)⁻¹ * blockLimitResolventTrace h (zOf p)) =
        blockLimitResolventTrace h (zOf p) := by
      rw [← mul_assoc, mul_inv_cancel₀ hcard, one_mul]
    rw [hone]
  · filter_upwards with p
    rw [norm_mul]
    rcases eq_or_ne p.2 0 with h0 | h0
    · have hzp : zOf p = ((p.1 : ℝ) : ℂ) := by simp [zOf, h0]
      have hz0 : dbarNumOrder (k + 1) f (zOf p) = 0 := by
        rw [hzp]
        exact dbarNumOrder_succ_ofReal hk hf hK p.1
      simp [hz0]
    · have hz : (zOf p).im ≠ 0 := by simpa [zOf] using h0
      have htr := norm_blockLimitResolventTrace_le h hh hz
      have htr' : ‖blockLimitResolventTrace h (zOf p)‖ ≤
          (Fintype.card (Fin d) : ℝ) * |p.2|⁻¹ := by simpa using htr
      refine (mul_le_mul_of_nonneg_left htr' (norm_nonneg _)).trans (le_of_eq ?_)
      rw [hC]
      ring

/-- **The limit-side plane integrability**, in the form consumed by the order-`k` comparison:
given the identification of the pencil trace with the block-limit resolvent trace, the product
of `∂̄_k f` with `Tr(operatorMatrixPencilCauchy)` is integrable. -/
theorem integrable_dbarNumOrder_mul_trace_operatorMatrixPencilCauchy_of_eq
    (h : BlockLimit r d) (hh : IsSelfAdjoint h)
    {A₀ : Matrix (Fin d) (Fin d) ℂ} {A : Fin r → Matrix (Fin d) (Fin d) ℂ}
    (hres : ∀ z : ℂ, z.im ≠ 0 → Matrix.trace (operatorMatrixPencilCauchy A₀ A z) =
      blockLimitResolventTrace h z)
    {f : ℝ → ℝ} {k K : ℕ} (hk : 1 ≤ k) (hf : ContDiff ℝ K f) (hK : k + 1 ≤ K)
    (hfc : HasCompactSupport f) :
    Integrable (fun p : ℝ × ℝ => dbarNumOrder (k + 1) f (zOf p) *
      Matrix.trace (operatorMatrixPencilCauchy A₀ A (zOf p)))
      (volume : Measure (ℝ × ℝ)) := by
  refine (integrable_dbarNumOrder_mul_blockLimitResolventTrace h hh hk hf hK hfc).congr ?_
  filter_upwards [(compl_mem_ae_iff).mpr volume_im_eq_zero] with p hp
  have hz : (zOf p).im ≠ 0 := by simpa [zOf] using hp
  simp only [hres _ hz]

end LimitIntegrability


/-! ## 4b. The closed-pencil bridge: the ambient Cauchy trace *is* the block-limit resolvent
trace

The affine Fock pencil `operatorMatrixPencil A₀ A` has all its entries in the (norm-closed)
semicircular algebra `closedSemicircularAlgebra (Fin r)`.  We may therefore read it as an element
`closedPencil A₀ A` of `BlockLimit r (d'+1)`; this is the **canonical limit element** of the
pencil.  Because the inclusion of a closed `C⋆`-subalgebra preserves inverses
(`StarSubalgebra.coe_isUnit`), the resolvent of the closed pencil, read in the ambient algebra,
is the resolvent of the ambient pencil.  Consequently the vacuum expectation of the trace of the
ambient resolvent — the matrix trace of `operatorMatrixPencilCauchy` — is exactly
`blockLimitResolventTrace (closedPencil A₀ A)`.

This turns the former identification field of `WeightedStripDataAt'` into a theorem: once the
limit element is *defined* as the pencil read in the block-limit algebra, the identity is
unconditional on the resolvent set. -/

section ClosedPencilBridge

variable {r : ℕ}

local instance brNontrivial : Nontrivial (closedSemicircularAlgebra (Fin r)) :=
  (closedGeneratedVacuumState (Fin r)).toProbabilitySpace.nontrivial

local instance brPartialOrder : PartialOrder (closedSemicircularAlgebra (Fin r)) :=
  CStarAlgebra.spectralOrder _

local instance brStarOrderedRing : StarOrderedRing (closedSemicircularAlgebra (Fin r)) :=
  CStarAlgebra.spectralOrderedRing _

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Entrywise application of a star algebra hom to `C⋆`-matrices. -/
def cmap {S T : Type*} [Ring S] [StarRing S] [Algebra ℂ S]
    [Ring T] [StarRing T] [Algebra ℂ T]
    (f : S →⋆ₐ[ℂ] T) : CStarMatrix n n S →⋆ₐ[ℂ] CStarMatrix n n T where
  toFun M := M.map f
  map_one' := by ext i j; rw [CStarMatrix.map_apply]; simp [CStarMatrix.one_apply]
  map_mul' x y := by
    ext i j
    simp only [CStarMatrix.map_apply, CStarMatrix.mul_apply, map_sum, map_mul]
  map_zero' := by ext i j; simp
  map_add' x y := by ext i j; simp
  commutes' c := by
    ext i j
    rw [CStarMatrix.map_apply, CStarMatrix.algebraMap_apply, CStarMatrix.algebraMap_apply]
    by_cases h : i = j
    · simp only [h, ite_true]; exact f.commutes c
    · simp [h]
  map_star' M := by
    ext i j
    rw [CStarMatrix.map_apply, CStarMatrix.star_apply, CStarMatrix.star_apply]
    exact map_star f (M j i)

@[simp] lemma cmap_apply {S T : Type*} [Ring S] [StarRing S] [Algebra ℂ S]
    [Ring T] [StarRing T] [Algebra ℂ T] (f : S →⋆ₐ[ℂ] T) (M : CStarMatrix n n S) (i j : n) :
    cmap f M i j = f (M i j) := rfl

/-- `cmap` of the inclusion of the closed semicircular algebra is injective. -/
lemma cmap_subtype_injective :
    Function.Injective (cmap (StarSubalgebra.subtype (closedSemicircularAlgebra (Fin r)))
      (n := n)) := by
  intro M N h
  have h' : ∀ i j, ((M i j : closedSemicircularAlgebra (Fin r)) :
      WordSpace (Fin r) →L[ℂ] WordSpace (Fin r)) = ↑(N i j) := by
    intro i j
    have := congrArg (fun X : CStarMatrix n n
      (WordSpace (Fin r) →L[ℂ] WordSpace (Fin r)) => X i j) h
    simpa using this
  refine CStarMatrix.ext fun i j => ?_
  exact Subtype.ext (h' i j)

/-- A unital ring hom commutes with the totalized inverse `Ring.inverse` at units. -/
lemma ringHom_map_inverse {R S : Type*} [Ring R] [Ring S] (f : R →+* S) {x : R}
    (h : IsUnit x) : f x⁻¹ʳ = (f x)⁻¹ʳ := by
  rw [Ring.inverse_of_isUnit h, Ring.inverse_of_isUnit (h.map f)]
  have hu : (h.map f).unit = Units.map f.toMonoidHom h.unit := by
    ext
    rw [IsUnit.unit_spec]
    rfl
  rw [hu, ← MonoidHom.map_inv (Units.map f.toMonoidHom) h.unit]
  rfl

/-- `cmap` commutes with the resolvent on the resolvent set. -/
lemma cmap_resolvent {S T : Type*} [Ring S] [StarRing S] [Algebra ℂ S]
    [Ring T] [StarRing T] [Algebra ℂ T] (f : S →⋆ₐ[ℂ] T)
    (M : CStarMatrix n n S) (z : ℂ)
    (h : IsUnit (algebraMap ℂ (CStarMatrix n n S) z - M)) :
    cmap f (resolvent M z) = resolvent (cmap f M) z := by
  unfold resolvent
  have key := ringHom_map_inverse (cmap f).toRingHom h
  simpa [map_sub, AlgHom.commutes] using key

/-- `cmap` commutes with the matrix trace. -/
lemma trace_cmap {S T : Type*} [Ring S] [StarRing S] [Algebra ℂ S]
    [Ring T] [StarRing T] [Algebra ℂ T] (f : S →⋆ₐ[ℂ] T) (M : CStarMatrix n n S) :
    Matrix.trace (cmap f M) = f (Matrix.trace M) := by
  simp only [Matrix.trace, map_sum]
  exact Finset.sum_congr rfl fun i _ => rfl

/-- **The affine Fock pencil read in the closed semicircular algebra.**  All entries of
`operatorMatrixPencil C₀ C` lie in the closed semicircular algebra, so the pencil has a
canonical copy in `BlockLimit r d = M_d(A_r)`. -/
def closedPencil (C₀ : Matrix n n ℂ) (C : Fin r → Matrix n n ℂ) :
    CStarMatrix n n (closedSemicircularAlgebra (Fin r)) :=
  CStarMatrix.ofMatrix fun i j =>
    ⟨scalarMatrixEmbedding C₀ i j + matrixLinearCombination (semicircular (I := Fin r)) C i j, by
      have h1 : algebraMap ℂ (WordSpace (Fin r) →L[ℂ] WordSpace (Fin r)) (C₀ i j) ∈
          semicircularAlgebra (Fin r) :=
        (semicircularAlgebra (Fin r)).algebraMap_mem _
      have h2 : matrixLinearCombination (semicircular (I := Fin r)) C i j ∈
          semicircularAlgebra (Fin r) := by
        rw [matrixLinearCombination]
        exact Subalgebra.sum_mem _ fun i _ => Subalgebra.smul_mem _ (semicircular_mem_algebra i) _
      exact (semicircularAlgebra (Fin r)).le_topologicalClosure (add_mem h1 h2)⟩

@[simp] lemma cmap_subtype_closedPencil (C₀ : Matrix n n ℂ) (C : Fin r → Matrix n n ℂ) :
    cmap (StarSubalgebra.subtype (closedSemicircularAlgebra (Fin r))) (closedPencil C₀ C)
      = operatorMatrixPencil C₀ C := by
  refine CStarMatrix.ext fun i j => ?_
  rfl

/-- The canonical limit element of a Hermitian affine pencil is self-adjoint. -/
lemma closedPencil_isSelfAdjoint (C₀ : Matrix n n ℂ) (C : Fin r → Matrix n n ℂ)
    (hC₀ : C₀.IsHermitian) (hC : ∀ i, (C i).IsHermitian) :
    IsSelfAdjoint (closedPencil C₀ C) := by
  have hamb : IsSelfAdjoint (operatorMatrixPencil C₀ C) :=
    operatorMatrixPencil_isSelfAdjoint C₀ C hC₀ hC
  have hmap : IsSelfAdjoint (cmap (StarSubalgebra.subtype (closedSemicircularAlgebra (Fin r)))
      (closedPencil C₀ C)) := by
    rw [cmap_subtype_closedPencil]; exact hamb
  have hstar : star (closedPencil C₀ C) = closedPencil C₀ C := by
    apply cmap_subtype_injective
    rw [map_star]
    exact hmap
  exact hstar

/-- **The closed-pencil bridge.**  On the resolvent set (`z.im ≠ 0` for a self-adjoint pencil),
the matrix trace of the operator-valued Cauchy transform of `(A₀, A)` is the block-limit
resolvent trace of the canonical limit element `closedPencil A₀ A`. -/
theorem trace_operatorMatrixPencilCauchy_eq_blockLimitResolventTrace
    (d' : ℕ) (C₀ : Matrix (Fin (d' + 1)) (Fin (d' + 1)) ℂ)
    (C : Fin r → Matrix (Fin (d' + 1)) (Fin (d' + 1)) ℂ)
    (hC₀ : C₀.IsHermitian) (hC : ∀ i, (C i).IsHermitian) {z : ℂ} (hz : z.im ≠ 0) :
    Matrix.trace (operatorMatrixPencilCauchy C₀ C z) =
      blockLimitResolventTrace (closedPencil (n := Fin (d' + 1)) C₀ C) z := by
  have hsa := closedPencil_isSelfAdjoint (n := Fin (d' + 1)) C₀ C hC₀ hC
  have hunit : IsUnit (algebraMap ℂ
      (CStarMatrix (Fin (d' + 1)) (Fin (d' + 1)) (closedSemicircularAlgebra (Fin r))) z -
        closedPencil (n := Fin (d' + 1)) C₀ C) := by
    rw [← spectrum.notMem_iff]
    intro hzmem
    exact hz (hsa.im_eq_zero_of_mem_spectrum hzmem)
  have hres := cmap_resolvent (f := StarSubalgebra.subtype (closedSemicircularAlgebra (Fin r)))
    (M := closedPencil (n := Fin (d' + 1)) C₀ C) (z := z) hunit
  rw [cmap_subtype_closedPencil] at hres
  rw [trace_operatorMatrixPencilCauchy]
  unfold blockLimitResolventTrace
  rw [← hres]
  have hsymm : CStarMatrix.ofMatrix.symm
      ((cmap (StarSubalgebra.subtype (closedSemicircularAlgebra (Fin r))))
        (resolvent (closedPencil (n := Fin (d' + 1)) C₀ C) z)) =
      (cmap (StarSubalgebra.subtype (closedSemicircularAlgebra (Fin r))))
        (resolvent (closedPencil (n := Fin (d' + 1)) C₀ C) z) := rfl
  rw [hsymm, trace_cmap]
  rfl

end ClosedPencilBridge

/-! ## 5. The shrunk final bundle

`WeightedStripInputs` carries thirteen fields per canonical dilated polynomial, four of which are
plane-integrability side conditions and two of which are the vanishing of the plane limit
statistics.  Those six are *derived* here, so the honest bundle keeps only

* the strengthened smooth cut-off `IsSmoothCutoffZeroOn` (smoothness, nonnegativity, `≤ 1`,
  `= 1` far away, compact support of `(f')²`);
* the regularity `C^{k+1}` of `f` and of `(f')²` and the compact support of `f`;
* the single analytic input `WeightedStripBound` (the weighted resolvent-strip estimate);
* the flat ⟶ GUE identification `FlatGUEStatisticEq`;
* **one** limit-spectrum vanishing hypothesis, `f = 0` and `f' = 0` on the spectrum of the
  limit element;
* the (definitional at the canonical instantiation) identification of the pencil Cauchy trace
  with the block-limit resolvent trace.

The last two replace the two plane-limit vanishing fields. -/

section FinalConditionalPrime

variable {r : ℕ}

local instance primeNontrivial : Nontrivial (closedSemicircularAlgebra (Fin r)) :=
  (closedGeneratedVacuumState (Fin r)).toProbabilitySpace.nontrivial

local instance primePartialOrder : PartialOrder (closedSemicircularAlgebra (Fin r)) :=
  CStarAlgebra.spectralOrder _

local instance primeStarOrderedRing : StarOrderedRing (closedSemicircularAlgebra (Fin r)) :=
  CStarAlgebra.spectralOrderedRing _

/-- **The weighted-strip data at one pencil, with the limit-side bookkeeping removed.**  Compared
with `WeightedStripDataAt`, the four plane-integrability fields and the two vanishing fields are
gone; in their place is the primitive vanishing `f = 0`, `f' = 0` on the spectrum of the limit
element `h` and the identification of the pencil Cauchy trace with `blockLimitResolventTrace h`. -/
def WeightedStripDataAt' (r k : ℕ) (F : RatPolyIdx r (k + 1)) (z ε : ℝ) : Prop :=
  ∃ (d' : ℕ) (A₀ : Matrix (Fin (d' + 1)) (Fin (d' + 1)) ℂ)
    (A : Fin r → Matrix (Fin (d' + 1)) (Fin (d' + 1)) ℂ)
    (hA₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian)
    (η₀ C_s β : ℝ) (hη₀2 : 2 < η₀) (hC_s : 0 ≤ C_s) (hβ0 : 0 ≤ β) (hβk : β < k)
    (f : ℝ → ℝ) (C' : ℝ)
    (h : BlockLimit r (d' + 1)) (hh : IsSelfAdjoint h),
    IsSmoothCutoffZeroOn (specC (h1PencilLimit r k F z)) ε f ∧
    ContDiff ℝ (k + 1) f ∧
    ContDiff ℝ (k + 1) (fun y => (deriv f y) ^ 2) ∧
    HasCompactSupport f ∧
    WeightedStripBound A₀ A k η₀ C_s β ∧
    FlatGUEStatisticEq r k F z d' A₀ A hA₀ hA ∧
    (∀ z' : ℂ, z'.im ≠ 0 → Matrix.trace (operatorMatrixPencilCauchy A₀ A z') =
      blockLimitResolventTrace h z') ∧
    (∀ x ∈ spectrum ℝ h, f x = 0 ∧ deriv f x = 0) ∧
    0 ≤ C'

/-- **The shrunk weighted-strip input bundle**: the order-`k` data in the reduced form, plus the
unchanged first-order (`k = 0`) mean-comparison field. -/
def WeightedStripInputs' (r : ℕ) : Prop :=
  (∀ (k : ℕ) (F : RatPolyIdx r (k + 1)) (z ε : ℝ), 1 ≤ k → 0 < ε →
    WeightedStripDataAt' r k F z ε) ∧
  (∀ (F : RatPolyIdx r (0 + 1)) (z ε : ℝ), 0 < ε →
    ∃ (f : ℝ → ℝ) (C C' : ℝ),
      IsSmoothCutoffZeroOn (specC (h1PencilLimit r 0 F z)) ε f ∧
      FlatLemmaM r 0 F z f C ∧
      FlatLemmaM r 0 F z (fun y => (deriv f y) ^ 2) C' ∧
      0 ≤ C ∧ 0 ≤ C')

/-- **The reduced data imply the original data**: the two vanishing fields follow from the
limit-spectrum vanishing through the order-`k` limit identity, and the four integrability fields
are unconditional. -/
theorem WeightedStripDataAt_of' {k : ℕ} {F : RatPolyIdx r (k + 1)} {z ε : ℝ}
    (hk : 1 ≤ k) (h : WeightedStripDataAt' r k F z ε) :
    WeightedStripDataAt r k F z ε := by
  obtain ⟨d', A₀, A, hA₀, hA, η₀, C_s, β, hη₀2, hC_s, hβ0, hβk, f, C', h, hh,
    hcut, hreg, hregw, hfc, hstrip, hstat, hres, hzero, hC'⟩ := h
  refine ⟨d', A₀, A, hA₀, hA, η₀, C_s, β, hη₀2, hC_s, hβ0, hβk, f, C',
    hcut, hreg, hregw, hfc, hstrip, hstat, ?_, ?_, ?_, ?_, ?_, ?_, hC'⟩
  · exact guePlaneLimitOrder_eq_zero_of_eq_zero_on_spectrum hk hh hres hreg le_rfl hfc
      (fun x hx => (hzero x hx).1)
  · refine guePlaneLimitOrder_eq_zero_of_eq_zero_on_spectrum hk hh hres hregw le_rfl
      hcut.smooth.compactSupport (fun x hx => ?_)
    rw [(hzero x hx).2]
    ring
  · exact eventually_integrable_dbarNumOrder_mul_trace_gueResolventMean A₀ A hA₀ hA hk
      hreg le_rfl hfc
  · exact integrable_dbarNumOrder_mul_trace_operatorMatrixPencilCauchy_of_eq h hh hres hk
      hreg le_rfl hfc
  · exact eventually_integrable_dbarNumOrder_mul_trace_gueResolventMean A₀ A hA₀ hA hk
      hregw le_rfl hcut.smooth.compactSupport
  · exact integrable_dbarNumOrder_mul_trace_operatorMatrixPencilCauchy_of_eq h hh hres hk
      hregw le_rfl hcut.smooth.compactSupport

/-- **The reduced bundle implies the weighted-strip bundle.** -/
theorem WeightedStripInputs_of_weightedStripInputs' (h : WeightedStripInputs' r) :
    WeightedStripInputs r := by
  refine ⟨?_, h.2⟩
  intro k F z ε hk _hε
  exact WeightedStripDataAt_of' hk (h.1 k F z ε hk _hε)

/-- **The project target from scalar spectral inclusion and the reduced bundle.**

The reduced bundle `WeightedStripInputs'` differs from `WeightedStripInputs` exactly by the six
limit-side bookkeeping fields discharged in this file (four plane-integrability conditions and
the two plane-limit vanishing statements, the latter replaced by the primitive vanishing of `f`
and `f'` on the limit spectrum). -/
theorem GUEStrongConvergenceStatement_of_weightedStripInputs'
    (hScalar : ScalarSpectralInclusion r) (h : WeightedStripInputs' r) :
    GUEStrongConvergenceStatement r :=
  GUEStrongConvergenceStatement_of_weightedStripInputs hScalar
    (WeightedStripInputs_of_weightedStripInputs' h)


/-! ## 6. Eliminating the two identification fields

`WeightedStripDataAt'` still carries two fields that are *identifications* rather than analytic
or cutoff data:

* `∀ z', Tr(operatorMatrixPencilCauchy A₀ A z') = blockLimitResolventTrace h z'`, and
* `∀ x ∈ spectrum ℝ h, f x = 0 ∧ f' x = 0` for a **freely chosen** witness `h`.

Both are removed here by *defining* the limit element of the pencil: it is `closedPencil A₀ A`,
the pencil read in the closed semicircular algebra.  Then

* the trace identification is the **theorem**
  `trace_operatorMatrixPencilCauchy_eq_blockLimitResolventTrace` (the closed-pencil bridge of
  §4b), and
* the vanishing is **cutoff data on the honest limit spectrum**: since `h` is now determined by
  `(A₀, A)`, the condition `f = 0`, `f' = 0` on `spectrum ℝ h` no longer asks one to identify two
  spectra — it is a property of the cutoff alone.

The remaining fields are exactly the smooth cutoff (still phrased on the canonical linearization
spectrum `specC (h1PencilLimit r k F z)`, which is what the downstream spectral-exclusion chain
consumes), the `C^{k+1}` regularity, the compact support, the single analytic input
`WeightedStripBound`, the flat ⟶ GUE bookkeeping identification `FlatGUEStatisticEq`, the cutoff
vanishing on the honest limit spectrum, and `0 ≤ C'`.

The one statement not derivable from the previous bundle is the spectral inclusion
`spectrum ℝ (closedPencil A₀ A) ⊆ specC (h1PencilLimit r k F z)`: it is the Kronecker/affine
coefficient identity `flatPencilBlk = reindex (guePencilMatrix A₀ A)` (the same bookkeeping gap
recorded at `FlatGUEStatisticEq`).  Rather than assume it, the cutoff vanishing is stated on the
honest spectrum; at the canonical data the two sets coincide. -/

section FinalConditionalDoublePrime

variable {r : ℕ}

local instance dpNontrivial : Nontrivial (closedSemicircularAlgebra (Fin r)) :=
  (closedGeneratedVacuumState (Fin r)).toProbabilitySpace.nontrivial

local instance dpPartialOrder : PartialOrder (closedSemicircularAlgebra (Fin r)) :=
  CStarAlgebra.spectralOrder _

local instance dpStarOrderedRing : StarOrderedRing (closedSemicircularAlgebra (Fin r)) :=
  CStarAlgebra.spectralOrderedRing _

/-- **The weighted-strip data at one pencil with the identification fields removed.**  The limit
element is `closedPencil A₀ A` (not a witness), the trace identification is proved in §4b, and
the vanishing is stated on the honest limit spectrum `spectrum ℝ (closedPencil A₀ A)`. -/
def WeightedStripDataAt'' (r k : ℕ) (F : RatPolyIdx r (k + 1)) (z ε : ℝ) : Prop :=
  ∃ (d' : ℕ) (A₀ : Matrix (Fin (d' + 1)) (Fin (d' + 1)) ℂ)
    (A : Fin r → Matrix (Fin (d' + 1)) (Fin (d' + 1)) ℂ)
    (hA₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian)
    (η₀ C_s β : ℝ) (hη₀2 : 2 < η₀) (hC_s : 0 ≤ C_s) (hβ0 : 0 ≤ β) (hβk : β < k)
    (f : ℝ → ℝ) (C' : ℝ),
    IsSmoothCutoffZeroOn (specC (h1PencilLimit r k F z)) ε f ∧
    ContDiff ℝ (k + 1) f ∧
    ContDiff ℝ (k + 1) (fun y => (deriv f y) ^ 2) ∧
    HasCompactSupport f ∧
    WeightedStripBound A₀ A k η₀ C_s β ∧
    FlatGUEStatisticEq r k F z d' A₀ A hA₀ hA ∧
    (∀ x ∈ spectrum ℝ (closedPencil (n := Fin (d' + 1)) A₀ A), f x = 0 ∧ deriv f x = 0) ∧
    0 ≤ C'

/-- **The double-prime data imply the single-prime data.**  The limit element is instantiated as
`closedPencil A₀ A`; its trace identification is the closed-pencil bridge and its vanishing is
the cutoff field. -/
theorem WeightedStripDataAt'_of_'' {k : ℕ} {F : RatPolyIdx r (k + 1)} {z ε : ℝ}
    (h : WeightedStripDataAt'' r k F z ε) :
    WeightedStripDataAt' r k F z ε := by
  obtain ⟨d', A₀, A, hA₀, hA, η₀, C_s, β, hη₀2, hC_s, hβ0, hβk, f, C',
    hcut, hreg, hregw, hfc, hstrip, hstat, hzero, hC'⟩ := h
  exact ⟨d', A₀, A, hA₀, hA, η₀, C_s, β, hη₀2, hC_s, hβ0, hβk, f, C',
    closedPencil (n := Fin (d' + 1)) A₀ A,
    closedPencil_isSelfAdjoint (n := Fin (d' + 1)) A₀ A hA₀ hA,
    hcut, hreg, hregw, hfc, hstrip, hstat,
    fun z' hz' => trace_operatorMatrixPencilCauchy_eq_blockLimitResolventTrace
      d' A₀ A hA₀ hA hz',
    hzero, hC'⟩

/-- **The fully reduced weighted-strip input bundle**: `WeightedStripDataAt''` for `1 ≤ k`, plus
the unchanged first-order (`k = 0`) mean-comparison field. -/
def WeightedStripInputs'' (r : ℕ) : Prop :=
  (∀ (k : ℕ) (F : RatPolyIdx r (k + 1)) (z ε : ℝ), 1 ≤ k → 0 < ε →
    WeightedStripDataAt'' r k F z ε) ∧
  (∀ (F : RatPolyIdx r (0 + 1)) (z ε : ℝ), 0 < ε →
    ∃ (f : ℝ → ℝ) (C C' : ℝ),
      IsSmoothCutoffZeroOn (specC (h1PencilLimit r 0 F z)) ε f ∧
      FlatLemmaM r 0 F z f C ∧
      FlatLemmaM r 0 F z (fun y => (deriv f y) ^ 2) C' ∧
      0 ≤ C ∧ 0 ≤ C')

/-- **The double-prime data imply the original weighted-strip data** (the thirteen-field
bundle of `Probability/LemmaMWeighted.lean`): the trace identification and the two plane-limit
vanishing statements are derived there from the closed-pencil bridge and the cutoff vanishing. -/
theorem WeightedStripDataAt_of_'' {k : ℕ} {F : RatPolyIdx r (k + 1)} {z ε : ℝ}
    (hk : 1 ≤ k) (h : WeightedStripDataAt'' r k F z ε) :
    WeightedStripDataAt r k F z ε :=
  WeightedStripDataAt_of' hk (WeightedStripDataAt'_of_'' h)

/-- **The double-prime bundle implies the reduced (single-prime) bundle.** -/
theorem WeightedStripInputs'_of_'' (h : WeightedStripInputs'' r) :
    WeightedStripInputs' r := by
  refine ⟨?_, h.2⟩
  intro k F z ε hk hε
  exact WeightedStripDataAt'_of_'' (h.1 k F z ε hk hε)

/-- **The double-prime bundle implies the original weighted-strip bundle.**  Hence the new bundle
is a genuine reduction of `WeightedStripInputs`, not only of `WeightedStripInputs'`. -/
theorem WeightedStripInputs_of_'' (h : WeightedStripInputs'' r) :
    WeightedStripInputs r :=
  WeightedStripInputs_of_weightedStripInputs' (WeightedStripInputs'_of_'' h)

/-- **The project target from scalar spectral inclusion and the fully reduced bundle.**

Neither of the two identification fields of `WeightedStripDataAt'` is a hypothesis here: the
limit element is the canonical `closedPencil A₀ A`, the trace identity is proved in §4b, and the
cutoff vanishing is stated on the honest limit spectrum. -/
theorem GUEStrongConvergenceStatement_of_weightedStripInputs''
    (hScalar : ScalarSpectralInclusion r) (h : WeightedStripInputs'' r) :
    GUEStrongConvergenceStatement r :=
  GUEStrongConvergenceStatement_of_weightedStripInputs' hScalar
    (WeightedStripInputs'_of_'' h)

end FinalConditionalDoublePrime

end FinalConditionalPrime

end GUEStrongConvergence
