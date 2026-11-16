/-
# The corrected (non-vacuous) endgame bundle

`StrongConvergence/FinalReduction.lean` proves
`GUEStrongConvergenceStatement_of_weightedStripInputsFinal` from a two-field bundle
`WeightedStripInputsFinal`.  That bundle is **uninhabited**
(`Verification/TerminalAudit.lean`, `weightedStripInputsFinal_uninhabited`): each of its
fields contains the contradictory pair

* `IsSmoothCutoffZeroOn S ε f`, whose `IsSmoothCutoff.eq_one` forces `f = 1` outside the
  bounded set `S + Ioo (-ε) ε`, and
* `HasCompactSupport f`, which forces `f = 0` outside a compact set.

The conditional theorem is therefore true but vacuous.  This file assembles the *corrected*
bundle from the repair bricks on main:

* `HasCompactSupport (fun y => f y - 1)` instead of `HasCompactSupport f`
  (`hasCompactSupport_sub_one_of_isSmoothCutoffZeroOn` is the producer-side form);
* the honest strip hypothesis `WeightedStripBoundProven`
  (`C_s (K + ‖z‖)² |Im z|⁻⁷ / N²`, `StrongConvergence/WeightedStripRepair.lean`) instead of the
  `β < max k 1` hypothesis `WeightedStripBound`, which is not implied by the intended input;
* extension order `m = 8` (regularity `C⁹`), independent of the polynomial index `k`
  (`flatLemmaM_of_weightedStripProven`), instead of the tied order `max k 1`.

The constants `C` and `C'` of `WeightedMeanInputs` are no longer bundle fields: they are the
explicit `weightedStripConstantProven` terms produced by the repaired transfer.

Main results:

* `WeightedStripDataAtRepairGen` — corrected data at general coefficients;
* `WeightedStripDataAtRepair` / `ScalarWeightedStripDataAtRepair` — corrected data at the
  canonical pencils;
* `WeightedStripInputsRepair` — the corrected two-field bundle;
* `WeightedMeanInputs_of_weightedStripDataAtRepair` — the corrected pencil field implies the
  `FlatLemmaM` footprint;
* `scalarSpectralInclusion_of_weightedStripDataAtRepair` — the corrected scalar field implies
  `ScalarSpectralInclusion`;
* `GUEStrongConvergenceStatement_of_weightedStripInputsRepair` — **the corrected endgame**.

Non-vacuity (the key evidence that the repair works, unlike the old bundle):

* `weightedStripDataAtRepairGen_of_stripBound` — the corrected bundle is inhabited at *every*
  coefficient matrix for which the honest strip bound holds: the shifted cutoff `f − 1` may be
  taken identically zero (`f ≡ 1` on `S = ∅`), so the only remaining conjunct is the analytic
  strip bound itself;
* `weightedStripDataAtRepairGen_nonempty_zeroDim` — an unconditional inhabitant at coefficient
  dimension `0`, where the strip inequality is trivially true (both sides vanish);
* `shiftedCutoff_nonempty` — a genuine `C⁹` cutoff with compactly supported shift exists at any
  compact target spectrum, so the cutoff conjuncts are jointly satisfiable (the old bundle's
  cutoff conjuncts were not);
* `shiftedCutoff_not_compactSupport` — that cutoff is provably *not* compactly supported, so the
  corrected bundle is not the old bundle in disguise and the old vacuity lemma does not apply.

Reduction of the analytic input (section 8): `WeightedStripBoundProven_of_nearAxis` shows the
honest strip bound on the whole strip follows from the near-axis annulus `|Im w| <
stripThreshold A` (both half-planes) plus the lower half-plane above the threshold — the upper
half-plane above the threshold is the theorem `frob_gueResolventMean_sub_limit_le_rpow_top`
(`Probability/StripAnalytic.lean`).  Hence `weightedStripDataAtRepair_of_nearAxis` and
`scalarWeightedStripDataAtRepair_of_nearAxis` inhabit the corrected bundle above the threshold.

No `sorry`, no new axioms.
-/
import GUEStrongConvergence.StrongConvergence.WeightedStripRepairBundle
import GUEStrongConvergence.StrongConvergence.StripSideConditions
import GUEStrongConvergence.StrongConvergence.CutoffCompactSupport
import GUEStrongConvergence.Probability.StripAnalytic

open Filter MeasureTheory ProbabilityTheory FreeProbability FreeProbability.Fock Matrix
open scoped BigOperators ComplexOrder ENNReal NNReal Pointwise Topology

namespace GUEStrongConvergence

noncomputable section

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 800000

variable {r : ℕ}

local instance correctedNontrivial : Nontrivial (closedSemicircularAlgebra (Fin r)) :=
  (closedGeneratedVacuumState (Fin r)).toProbabilitySpace.nontrivial

local instance correctedPartialOrder : PartialOrder (closedSemicircularAlgebra (Fin r)) :=
  CStarAlgebra.spectralOrder _

local instance correctedStarOrderedRing : StarOrderedRing (closedSemicircularAlgebra (Fin r)) :=
  CStarAlgebra.spectralOrderedRing _

/-- The pencil coefficient dimension is positive, as a local instance so that the target
statements can mention `stripThreshold` at the canonical pencils. -/
local instance correctedPencilCoeffNonempty (k : ℕ) (F : RatPolyIdx r (k + 1)) :
    Nonempty (Fin (pencilCoeffDim k F)) :=
  ⟨⟨0, pencilCoeffDim_pos r k F⟩⟩

/-! ## 1. The corrected bundle -/

/-- **The corrected weighted-strip data at general coefficients.**

Compared with `WeightedStripDataAtFinal`, the two defects are repaired:

* `HasCompactSupport (fun y => f y - 1)` replaces `HasCompactSupport f` (which together with
  `IsSmoothCutoffZeroOn` is contradictory);
* `WeightedStripBoundProven A₀ A η₀ Kc C_s` (honest `|Im z|⁻⁷`, polynomial weight
  `(Kc + ‖z‖)²`) replaces `WeightedStripBound A₀ A (max k 1) η₀ C_s β` with `β < max k 1`;
  the extension order is the fixed `9`, not the polynomial index.

`S` is the target spectrum the cutoff has to vanish on.  The mean constants are *not* fields:
they are the explicit `weightedStripConstantProven` terms. -/
def WeightedStripDataAtRepairGen (r d : ℕ)
    (A₀ : Matrix (Fin d) (Fin d) ℂ) (A : Fin r → Matrix (Fin d) (Fin d) ℂ)
    (S : Set ℝ) (ε : ℝ) : Prop :=
  ∃ (η₀ Kc C_s : ℝ) (_hη₀2 : 2 < η₀) (_hC_s : 0 ≤ C_s) (f : ℝ → ℝ),
    IsSmoothCutoffZeroOn S ε f ∧
    ContDiff ℝ 9 f ∧
    ContDiff ℝ 9 (fun y => (deriv f y) ^ 2) ∧
    HasCompactSupport (fun y => f y - 1) ∧
    WeightedStripBoundProven A₀ A η₀ Kc C_s

/-- **The corrected per-pencil data at the canonical linearization pencils.** -/
def WeightedStripDataAtRepair (r k : ℕ) (F : RatPolyIdx r (k + 1)) (z ε : ℝ) : Prop :=
  letI : Nonempty (Fin (pencilCoeffDim k F)) := ⟨⟨0, pencilCoeffDim_pos r k F⟩⟩
  WeightedStripDataAtRepairGen r (pencilCoeffDim k F) (pencilConstCoeff k F z)
    (pencilDirCoeff k F) (specC (h1PencilLimit r k F z)) ε

/-- **The corrected scalar (`d = 1`) data for the individual GUE generators.** -/
def ScalarWeightedStripDataAtRepair (r : ℕ) (i : Fin r) (ε : ℝ) : Prop :=
  letI : Nonempty (Fin 1) := ⟨⟨0, by norm_num⟩⟩
  WeightedStripDataAtRepairGen r 1 (0 : Matrix (Fin 1) (Fin 1) ℂ) (scalarPencilCoeff i)
    (spectrum ℝ (semicircularFamily r i)) ε

/-- **The corrected two-field bundle.** -/
def WeightedStripInputsRepair (r : ℕ) : Prop :=
  (∀ (k : ℕ) (F : RatPolyIdx r (k + 1)) (z ε : ℝ), 0 < ε →
    WeightedStripDataAtRepair r k F z ε) ∧
  (∀ (i : Fin r) (ε : ℝ), 0 < ε → ScalarWeightedStripDataAtRepair r i ε)

/-! ## 2. Auxiliary facts -/

/-- A continuous compactly supported function is globally bounded in absolute value. -/
lemma exists_abs_bound_of_continuous_hasCompactSupport {g : ℝ → ℝ}
    (hg : Continuous g) (hgc : HasCompactSupport g) : ∃ C : ℝ, 0 ≤ C ∧ ∀ x, |g x| ≤ C := by
  obtain ⟨C, hC⟩ := hgc.isCompact.exists_bound_of_continuousOn hg.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun x => ?_⟩
  by_cases hx : x ∈ tsupport g
  · have h1 : ‖g x‖ ≤ C := hC x hx
    rw [Real.norm_eq_abs] at h1
    exact h1.trans (le_max_left _ _)
  · have hzero : g x = 0 := image_eq_zero_of_notMem_tsupport hx
    rw [hzero, abs_zero]
    exact le_max_right _ _

/-! ## 3. The block-level mean bound for the cutoff itself (shifted comparison) -/

/-- **The mean bound for `f` from the honest comparison for `f − 1`.**

The comparison at order `k ≥ 8` is applied to the compactly supported `f − 1`, whose limit
statistic is `−1`.  Since `∫ τ_N(f) = ∫ τ_N(f−1) + 1` (`gueStatisticCfc_sub_one`), the exact
cancellation gives `|∫ τ_N(f)| = |∫ τ_N(f−1) − (−1)| ≤ C/N²`. -/
theorem eventually_abs_integral_gueStatisticCfc_le_of_weighted_strip_proven_sub_one
    {ι : Type*} [Fintype ι] [DecidableEq ι] {d : Type*} [Fintype d] [DecidableEq d]
    [Nonempty d] (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ) (hA₀ : A₀.IsHermitian)
    (hA : ∀ i, (A i).IsHermitian) {f : ℝ → ℝ} {k K : ℕ} (hk : 1 ≤ k) (hk8 : 7 < k)
    (hf : ContDiff ℝ K (fun y => f y - 1)) (hK : k + 1 ≤ K)
    (hfc : HasCompactSupport (fun y => f y - 1))
    {η₀ Kc C_s : ℝ} (hη₀2 : 2 < η₀) (hC_s : 0 ≤ C_s)
    (hstrip : WeightedStripBoundProven A₀ A η₀ Kc C_s)
    (hIntN : ∀ᶠ N : ℕ in atTop, Integrable (fun p : ℝ × ℝ =>
      dbarNumOrder (k + 1) (fun y => f y - 1) (zOf p) *
        Matrix.trace (gueResolventMean (N := N) A₀ A (zOf p))))
    (hIntLim : Integrable (fun p : ℝ × ℝ =>
      dbarNumOrder (k + 1) (fun y => f y - 1) (zOf p) *
        Matrix.trace (operatorMatrixPencilCauchy A₀ A (zOf p))))
    (hlim : guePlaneLimitOrder k A₀ A (fun y => f y - 1) = -1)
    (hInt : ∀ (N : ℕ), 0 < N →
      Integrable (gueStatisticCfc (N := N) (fun y => f y - 1) A₀ A hA₀ hA)
        (stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))) :
    ∀ᶠ N : ℕ in atTop,
      |∫ y : EuclideanSpace ℝ (GUECoord ι N),
        gueStatisticCfc (N := N) f A₀ A hA₀ hA y
        ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))| ≤
        weightedStripConstantProven (fun y => f y - 1) k Kc C_s / (N : ℝ) ^ 2 := by
  have hcomp := eventually_smooth_trace_comparison_of_weighted_strip_proven A₀ A hA₀ hA
    hk hk8 hf hK hfc hη₀2 hC_s hstrip hIntN hIntLim
  filter_upwards [hcomp, eventually_ge_atTop (1 : ℕ)] with N hN hN1
  have hNpos : 0 < N := by omega
  rw [hlim] at hN
  -- `∫ τ_N(f) = ∫ τ_N(f − 1) + 1`
  have hcongr : (fun y : EuclideanSpace ℝ (GUECoord ι N) =>
        gueStatisticCfc (N := N) f A₀ A hA₀ hA y)
      = fun y => gueStatisticCfc (N := N) (fun y => f y - 1) A₀ A hA₀ hA y + 1 := by
    funext y
    exact (gueStatisticCfc_sub_one f A₀ A hA₀ hA y hNpos).symm
  have hshift : ∫ y : EuclideanSpace ℝ (GUECoord ι N),
      gueStatisticCfc (N := N) (fun y => f y - 1) A₀ A hA₀ hA y
        ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))
      = (∫ y : EuclideanSpace ℝ (GUECoord ι N),
          gueStatisticCfc (N := N) f A₀ A hA₀ hA y
            ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))) - 1 := by
    rw [hcongr, integral_add (hInt N hNpos) (integrable_const 1), integral_const]
    simp
  have hgoal : |∫ y : EuclideanSpace ℝ (GUECoord ι N),
        gueStatisticCfc (N := N) f A₀ A hA₀ hA y
          ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))|
      = |(∫ y : EuclideanSpace ℝ (GUECoord ι N),
            gueStatisticCfc (N := N) (fun y => f y - 1) A₀ A hA₀ hA y
              ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))) - (-1)| := by
    rw [hshift]
    congr 1
    ring
  rw [hgoal]
  exact hN

/-! ## 4. The `FlatLemmaM` footprint of the corrected pencil bundle -/

/-- **The corrected bundle gives the mean comparisons.**  This is
`WeightedMeanInputs_of_weightedStripDataAtFinal` with the corrected field: the comparison for
`f` goes through `flatLemmaM_of_weightedStripProven_sub_one` (shift `f → f − 1`) and the
comparison for `(f')²` through `flatLemmaM_of_weightedStripProven`. -/
theorem WeightedMeanInputs_of_weightedStripDataAtRepair
    (h : ∀ (k : ℕ) (F : RatPolyIdx r (k + 1)) (z ε : ℝ), 0 < ε →
      WeightedStripDataAtRepair r k F z ε) :
    WeightedMeanInputs r := by
  intro k F z ε hε
  obtain ⟨η₀, Kc, C_s, hη₀2, hC_s, f, hcut, hreg, hregw, hfc, hstrip⟩ := h k F z ε hε
  haveI hne : NeZero (pencilCoeffDim k F) :=
    ⟨Nat.ne_of_gt (pencilCoeffDim_pos r k F)⟩
  haveI hne' : Nonempty (Fin (pencilCoeffDim k F)) :=
    ⟨⟨0, pencilCoeffDim_pos r k F⟩⟩
  have hm : 1 ≤ 8 := by norm_num
  have hm8 : 7 < 8 := by norm_num
  have hreg' : ContDiff ℝ 9 (fun y => f y - 1) := hreg.sub contDiff_const
  have hA₀ := pencilConstCoeff_isHermitian k F z
  have hA := pencilDirCoeff_isHermitian k F
  have hsp : spectrum ℝ (closedPencil (n := Fin (pencilCoeffDim k F))
        (pencilConstCoeff k F z) (pencilDirCoeff k F)) = specC (h1PencilLimit r k F z) :=
    (specC_eq_spectrum_closedPencil r k F z).symm
  have hres : ∀ z' : ℂ, z'.im ≠ 0 →
      Matrix.trace (operatorMatrixPencilCauchy (pencilConstCoeff k F z) (pencilDirCoeff k F) z') =
        blockLimitResolventTrace (closedPencil (n := Fin (pencilCoeffDim k F))
          (pencilConstCoeff k F z) (pencilDirCoeff k F)) z' :=
    fun z' hz' =>
      trace_operatorMatrixPencilCauchy_eq_blockLimitResolventTrace_gen
        (pencilCoeffDim k F) (pencilConstCoeff k F z) (pencilDirCoeff k F) hA₀ hA hz'
  have hhh : IsSelfAdjoint (closedPencil (n := Fin (pencilCoeffDim k F))
      (pencilConstCoeff k F z) (pencilDirCoeff k F)) :=
    closedPencil_isSelfAdjoint _ _ hA₀ hA
  have hzerof : ∀ x ∈ spectrum ℝ (closedPencil (n := Fin (pencilCoeffDim k F))
      (pencilConstCoeff k F z) (pencilDirCoeff k F)), f x = 0 := by
    intro x hx
    rw [hsp] at hx
    exact hcut.eq_zero x hx
  have hzerow : ∀ x ∈ spectrum ℝ (closedPencil (n := Fin (pencilCoeffDim k F))
      (pencilConstCoeff k F z) (pencilDirCoeff k F)), (deriv f x) ^ 2 = 0 := by
    intro x hx
    rw [hsp] at hx
    rw [hcut.deriv_eq_zero x hx]
    ring
  -- the limit statistic of `f − 1` is `−1`
  have hlim : guePlaneLimitOrder 8 (pencilConstCoeff k F z) (pencilDirCoeff k F)
      (fun y => f y - 1) = -1 :=
    guePlaneLimitOrder_sub_one_eq_neg_one (m := 8) (K := 9) hm hhh hres hreg'
      (by norm_num) hfc hzerof
  -- the flat ⟶ GUE identification for the shifted test function
  have hstat : ∀ N : ℕ,
      ∫ x, flatStat r k F z N (fun y => f y - 1) x ∂(commonGaussianMeasure (Fin r))
        = ∫ y : EuclideanSpace ℝ (GUECoord (Fin r) (N + 1)),
            gueStatisticCfc (N := N + 1) (fun y => f y - 1)
              (pencilConstCoeff k F z) (pencilDirCoeff k F) hA₀ hA y
              ∂(stdGaussian (EuclideanSpace ℝ (GUECoord (Fin r) (N + 1)))) :=
    fun N => flatGUEStatisticEqCont_canonical k F z N (fun y => f y - 1) hreg'.continuous
  have hIntN : ∀ᶠ N : ℕ in atTop, Integrable (fun p : ℝ × ℝ =>
      dbarNumOrder (8 + 1) (fun y => f y - 1) (zOf p) *
        Matrix.trace (gueResolventMean (N := N) (pencilConstCoeff k F z)
          (pencilDirCoeff k F) (zOf p))) :=
    eventually_integrable_dbarNumOrder_mul_trace_gueResolventMean
      (pencilConstCoeff k F z) (pencilDirCoeff k F) hA₀ hA (k := 8) (K := 9)
      (by norm_num) hreg' le_rfl hfc
  have hIntLim : Integrable (fun p : ℝ × ℝ =>
      dbarNumOrder (8 + 1) (fun y => f y - 1) (zOf p) *
        Matrix.trace (operatorMatrixPencilCauchy (pencilConstCoeff k F z)
          (pencilDirCoeff k F) (zOf p))) :=
    integrable_dbarNumOrder_mul_trace_operatorMatrixPencilCauchy_fin
      (pencilCoeffDim k F) (pencilConstCoeff k F z) (pencilDirCoeff k F) hA₀ hA
      (k := 8) (K := 9) (by norm_num) hreg' le_rfl hfc
  obtain ⟨M, hM0, hMbound⟩ :=
    exists_abs_bound_of_continuous_hasCompactSupport hreg'.continuous hfc
  have hInt : ∀ N : ℕ,
      Integrable (flatStat r k F z N (fun y => f y - 1)) (commonGaussianMeasure (Fin r)) :=
    fun N => (flatStat_memLp k F z hreg'.continuous hMbound hM0 N).integrable (by norm_num)
  refine ⟨f, weightedStripConstantProven (fun y => f y - 1) 8 Kc C_s,
    weightedStripConstantProven (fun y => (deriv f y) ^ 2) 8 Kc C_s,
    hcut, ?_, ?_, weightedStripConstantProven_nonneg hC_s,
    weightedStripConstantProven_nonneg hC_s⟩
  · exact flatLemmaM_of_weightedStripProven_sub_one (m := 8) _ _ hA₀ hA hm hm8
      hη₀2 hC_s hreg' hfc hstrip hstat hlim hIntN hIntLim hInt
  · refine flatLemmaM_of_weightedStripProven (m := 8) _ _ hA₀ hA hm hm8 hη₀2 hC_s
      hregw hcut.smooth.compactSupport hstrip ?_ ?_ ?_ ?_
    · intro N
      exact flatGUEStatisticEqCont_canonical k F z N (fun y => (deriv f y) ^ 2)
        hregw.continuous
    · exact guePlaneLimitOrder_eq_zero_of_eq_zero_on_spectrum (k := 8) (K := 9)
        (by norm_num) hhh hres hregw le_rfl hcut.smooth.compactSupport hzerow
    · exact eventually_integrable_dbarNumOrder_mul_trace_gueResolventMean
        (pencilConstCoeff k F z) (pencilDirCoeff k F) hA₀ hA (k := 8) (K := 9)
        (by norm_num) hregw le_rfl hcut.smooth.compactSupport
    · exact integrable_dbarNumOrder_mul_trace_operatorMatrixPencilCauchy_fin
        (pencilCoeffDim k F) (pencilConstCoeff k F z) (pencilDirCoeff k F) hA₀ hA
        (k := 8) (K := 9) (by norm_num) hregw le_rfl hcut.smooth.compactSupport

/-! ## 5. The scalar spectral inclusion from the corrected scalar field -/

/-- **`ScalarSpectralInclusion` from the corrected scalar weighted-strip data.**

This is `scalarSpectralInclusion_of_weightedStrip` with the corrected field: the mean bound for
the cutoff `f` is obtained from the honest comparison for the *shifted* cutoff `f − 1` (whose
limit statistic is `−1`), and the `(W)` bound for `(f')²` from the honest comparison at vanishing
limit statistic.  Both use `WeightedStripBoundProven`, i.e. the honest `|Im z|⁻⁷` exponent. -/
theorem scalarSpectralInclusion_of_weightedStripDataAtRepair
    (h : ∀ (i : Fin r) (ε : ℝ), 0 < ε → ScalarWeightedStripDataAtRepair r i ε) :
    ScalarSpectralInclusion r := by
  classical
  have hstep : ∀ (i : Fin r) (k : ℕ),
      ∀ᵐ x ∂(commonGaussianMeasure (Fin r)), ∀ᶠ N : ℕ in atTop,
        spectrum ℝ (gueFamily r N x i) ⊆
          spectrum ℝ (semicircularFamily r i) +
            Set.Ioo (-(1 / (k + 1 : ℝ))) (1 / (k + 1 : ℝ)) := by
    intro i k
    have hε : (0 : ℝ) < 1 / (k + 1 : ℝ) := by positivity
    haveI hne1 : Nonempty (Fin 1) := ⟨⟨0, by norm_num⟩⟩
    obtain ⟨η₀, Kc, C_s, hη₀2, hC_s, f, hcut, hreg, hregw, hfc, hstrip⟩ := h i _ hε
    have hsa : IsSelfAdjoint
        (closedPencil (n := Fin 1) (0 : Matrix (Fin 1) (Fin 1) ℂ) (scalarPencilCoeff i)) :=
      closedPencil_isSelfAdjoint _ _ isHermitian_zero (scalarPencilCoeff_isHermitian i)
    have hres : ∀ z : ℂ, z.im ≠ 0 →
        Matrix.trace (operatorMatrixPencilCauchy (0 : Matrix (Fin 1) (Fin 1) ℂ)
          (scalarPencilCoeff i) z) =
          blockLimitResolventTrace
            (closedPencil (n := Fin 1) (0 : Matrix (Fin 1) (Fin 1) ℂ)
              (scalarPencilCoeff i)) z :=
      fun z hz =>
        trace_operatorMatrixPencilCauchy_eq_blockLimitResolventTrace_gen 1
          (0 : Matrix (Fin 1) (Fin 1) ℂ) (scalarPencilCoeff i) isHermitian_zero
          (scalarPencilCoeff_isHermitian i) hz
    have hspec : spectrum ℝ
        (closedPencil (n := Fin 1) (0 : Matrix (Fin 1) (Fin 1) ℂ) (scalarPencilCoeff i)) =
        spectrum ℝ (semicircularFamily r i) := spectrum_closedPencil_scalarPencilCoeff i
    have hreg' : ContDiff ℝ 9 (fun y => f y - 1) := hreg.sub contDiff_const
    have hzerof : ∀ x ∈ spectrum ℝ
        (closedPencil (n := Fin 1) (0 : Matrix (Fin 1) (Fin 1) ℂ) (scalarPencilCoeff i)),
        f x = 0 := by
      intro x hx
      rw [hspec] at hx
      exact hcut.eq_zero x hx
    have hzerow : ∀ x ∈ spectrum ℝ
        (closedPencil (n := Fin 1) (0 : Matrix (Fin 1) (Fin 1) ℂ) (scalarPencilCoeff i)),
        (deriv f x) ^ 2 = 0 := by
      intro x hx
      rw [hspec] at hx
      rw [hcut.deriv_eq_zero x hx]
      ring
    have hlimf : guePlaneLimitOrder 8 (0 : Matrix (Fin 1) (Fin 1) ℂ) (scalarPencilCoeff i)
        (fun y => f y - 1) = -1 :=
      guePlaneLimitOrder_sub_one_eq_neg_one (m := 8) (K := 9) (by norm_num) hsa hres hreg'
        (by norm_num) hfc hzerof
    have hlim0w : guePlaneLimitOrder 8 (0 : Matrix (Fin 1) (Fin 1) ℂ) (scalarPencilCoeff i)
        (fun y => (deriv f y) ^ 2) = 0 :=
      guePlaneLimitOrder_eq_zero_of_eq_zero_on_spectrum (k := 8) (K := 9) (by norm_num)
        hsa hres hregw le_rfl hcut.smooth.compactSupport hzerow
    obtain ⟨Cb, hCb0, hCbb⟩ :=
      exists_abs_bound_of_continuous_hasCompactSupport hreg'.continuous hfc
    have hIntShift : ∀ (N : ℕ), 0 < N →
        Integrable (gueStatisticCfc (N := N) (ι := Fin r) (d := Fin 1)
          (fun y => f y - 1) (0 : Matrix (Fin 1) (Fin 1) ℂ) (scalarPencilCoeff i)
            isHermitian_zero (scalarPencilCoeff_isHermitian i))
          (stdGaussian (EuclideanSpace ℝ (GUECoord (Fin r) N))) :=
      fun N _ =>
        (memLp_gueStatisticCfc_scalarPencilCoeff hreg'.continuous hCbb hCb0 i
          isHermitian_zero (scalarPencilCoeff_isHermitian i)).integrable (by norm_num)
    -- the comparison for `f` through the shift
    have hMeBlock :=
      eventually_abs_integral_gueStatisticCfc_le_of_weighted_strip_proven_sub_one
        (0 : Matrix (Fin 1) (Fin 1) ℂ) (scalarPencilCoeff i) isHermitian_zero
        (scalarPencilCoeff_isHermitian i) (k := 8) (K := 9) (by norm_num) (by norm_num)
        hreg' le_rfl hfc hη₀2 hC_s hstrip
        (eventually_integrable_dbarNumOrder_mul_trace_gueResolventMean
          (0 : Matrix (Fin 1) (Fin 1) ℂ) (scalarPencilCoeff i) isHermitian_zero
          (scalarPencilCoeff_isHermitian i) (k := 8) (K := 9) (by norm_num) hreg' le_rfl hfc)
        (integrable_dbarNumOrder_mul_trace_operatorMatrixPencilCauchy_fin 1
          (0 : Matrix (Fin 1) (Fin 1) ℂ) (scalarPencilCoeff i) isHermitian_zero
          (scalarPencilCoeff_isHermitian i) (k := 8) (K := 9) (by norm_num) hreg' le_rfl hfc)
        hlimf hIntShift
    -- transport to the common space
    have hMe' : ∀ᶠ N : ℕ in atTop,
        |∫ x : CommonSpace (Fin r),
          normTrace (hermCfc (gueFamily r N x i) f (gueMatrixOn_isHermitian x N i))
          ∂(commonGaussianMeasure (Fin r))| ≤
          weightedStripConstantProven (fun y => f y - 1) 8 Kc C_s / (N : ℝ) ^ 2 := by
      filter_upwards [hMeBlock] with N hN
      have hB : AEStronglyMeasurable
          (fun y : EuclideanSpace ℝ (GUECoord (Fin r) N) =>
            gueStatisticCfc (N := N) (ι := Fin r) (d := Fin 1) f
              (0 : Matrix (Fin 1) (Fin 1) ℂ) (scalarPencilCoeff i) isHermitian_zero
              (scalarPencilCoeff_isHermitian i) y)
          (stdGaussian (EuclideanSpace ℝ (GUECoord (Fin r) N))) :=
        (memLp_gueStatisticCfc_scalarPencilCoeff hreg.continuous
          (fun y => hcut.smooth.abs_le_one y) zero_le_one i isHermitian_zero
          (scalarPencilCoeff_isHermitian i)).aestronglyMeasurable
      rw [integral_commonSpace_scalarPencilStat_eq i f isHermitian_zero
        (scalarPencilCoeff_isHermitian i) hB]
      exact hN
    -- the `(W)` bound for `(f')²`
    have hWeBlock :=
      eventually_abs_integral_gueStatisticCfc_le_of_weighted_strip_proven
        (0 : Matrix (Fin 1) (Fin 1) ℂ) (scalarPencilCoeff i) isHermitian_zero
        (scalarPencilCoeff_isHermitian i) (k := 8) (K := 9) (by norm_num) (by norm_num)
        hregw le_rfl hcut.smooth.compactSupport hη₀2 hC_s hstrip
        (eventually_integrable_dbarNumOrder_mul_trace_gueResolventMean
          (0 : Matrix (Fin 1) (Fin 1) ℂ) (scalarPencilCoeff i) isHermitian_zero
          (scalarPencilCoeff_isHermitian i) (k := 8) (K := 9) (by norm_num) hregw le_rfl
          hcut.smooth.compactSupport)
        (integrable_dbarNumOrder_mul_trace_operatorMatrixPencilCauchy_fin 1
          (0 : Matrix (Fin 1) (Fin 1) ℂ) (scalarPencilCoeff i) isHermitian_zero
          (scalarPencilCoeff_isHermitian i) (k := 8) (K := 9) (by norm_num) hregw le_rfl
          hcut.smooth.compactSupport)
        hlim0w
    have hWe' : ∀ᶠ N : ℕ in atTop,
        ∫ x : CommonSpace (Fin r),
          normTrace (hermCfc (gueFamily r N x i) (fun y => (deriv f y) ^ 2)
            (gueMatrixOn_isHermitian x N i)) ∂(commonGaussianMeasure (Fin r)) ≤
          weightedStripConstantProven (fun y => (deriv f y) ^ 2) 8 Kc C_s / (N : ℝ) ^ 2 := by
      filter_upwards [hWeBlock] with N hN
      have hB : AEStronglyMeasurable
          (fun y : EuclideanSpace ℝ (GUECoord (Fin r) N) =>
            gueStatisticCfc (N := N) (ι := Fin r) (d := Fin 1) (fun y => (deriv f y) ^ 2)
              (0 : Matrix (Fin 1) (Fin 1) ℂ) (scalarPencilCoeff i) isHermitian_zero
              (scalarPencilCoeff_isHermitian i) y)
          (stdGaussian (EuclideanSpace ℝ (GUECoord (Fin r) N))) := by
        obtain ⟨M, hM0, hMbound⟩ := hcut.smooth.exists_deriv_bound
        have hbound : ∀ y : ℝ, |(deriv f y) ^ 2| ≤ M ^ 2 := fun y => by
          rw [abs_of_nonneg (sq_nonneg (deriv f y))]
          calc (deriv f y) ^ 2 = |deriv f y| ^ 2 := by rw [sq_abs]
            _ ≤ M ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (hMbound y) 2
        exact (memLp_gueStatisticCfc_scalarPencilCoeff hregw.continuous hbound
          (sq_nonneg M) i isHermitian_zero (scalarPencilCoeff_isHermitian i)).aestronglyMeasurable
      rw [integral_commonSpace_scalarPencilStat_eq i (fun y => (deriv f y) ^ 2)
        isHermitian_zero (scalarPencilCoeff_isHermitian i) hB]
      exact le_trans (le_abs_self _) hN
    exact ae_eventually_spectrum_subset_scalar_smooth_eventual i hε hcut.smooth
      (weightedStripConstantProven_nonneg hC_s) (weightedStripConstantProven_nonneg hC_s)
      hMe' hWe'
  have hall : ∀ᵐ x ∂(commonGaussianMeasure (Fin r)),
      ∀ i : Fin r, ∀ k : ℕ, ∀ᶠ N : ℕ in atTop,
        spectrum ℝ (gueFamily r N x i) ⊆
          spectrum ℝ (semicircularFamily r i) +
            Set.Ioo (-(1 / (k + 1 : ℝ))) (1 / (k + 1 : ℝ)) := by
    have h := ae_all_iff.2 (fun p : Fin r × ℕ => hstep p.1 p.2)
    filter_upwards [h] with x hx
    intro i k
    exact hx (i, k)
  filter_upwards [hall] with x hx
  intro i ε hε
  obtain ⟨k, hk⟩ : ∃ k : ℕ, (1 : ℝ) / (k + 1 : ℝ) < ε := by
    obtain ⟨n, hn⟩ := exists_nat_gt (1 / ε)
    refine ⟨n, ?_⟩
    rw [div_lt_iff₀ (by positivity : (0 : ℝ) < n + 1)]
    have hn' : (1 : ℝ) < ε * (n + 1) := by
      have h : (1 : ℝ) / ε < n + 1 := by linarith
      rw [div_lt_iff₀ hε] at h
      rw [mul_comm]
      exact h
    linarith
  have hsub : Set.Ioo (-(1 / (k + 1 : ℝ))) (1 / (k + 1 : ℝ)) ⊆ Set.Ioo (-ε) ε := by
    intro y hy
    exact ⟨lt_trans (neg_lt_neg hk) hy.1, lt_trans hy.2 hk⟩
  filter_upwards [hx i k] with N hN
  intro a ha
  have hmem : a ∈ spectrum ℝ (semicircularFamily r i) + Set.Ioo (-ε) ε := by
    have h1 : a ∈ spectrum ℝ (semicircularFamily r i) +
        Set.Ioo (-(1 / (k + 1 : ℝ))) (1 / (k + 1 : ℝ)) := hN ha
    rw [Set.mem_add] at h1 ⊢
    obtain ⟨b, hb, c, hc, hbc⟩ := h1
    exact ⟨b, hb, c, hsub hc, hbc⟩
  exact exists_mem_of_mem_add_Ioo hmem

/-! ## 6. The corrected endgame -/

/-- **The project target from the corrected weighted-strip bundle.**

The scalar spectral inclusion is derived from the corrected scalar field
(`scalarSpectralInclusion_of_weightedStripDataAtRepair`) and the pencil mean comparisons from the
corrected pencil field (`WeightedMeanInputs_of_weightedStripDataAtRepair`); the two are combined
by the already verified reduction `GUEStrongConvergenceStatement_of_weightedMeanInputs`.

Unlike `GUEStrongConvergenceStatement_of_weightedStripInputsFinal`, the hypothesis bundle here is
*not* uninhabited: see `weightedStripDataAtRepairGen_of_stripBound` and
`weightedStripDataAtRepair_nonempty`. -/
theorem GUEStrongConvergenceStatement_of_weightedStripInputsRepair
    (h : WeightedStripInputsRepair r) : GUEStrongConvergenceStatement r :=
  GUEStrongConvergenceStatement_of_weightedMeanInputs
    (scalarSpectralInclusion_of_weightedStripDataAtRepair h.2)
    (WeightedMeanInputs_of_weightedStripDataAtRepair h.1)

/-! ## 7. Non-vacuity of the corrected bundle

The old bundle was uninhabited because `IsSmoothCutoffZeroOn S ε f` and `HasCompactSupport f`
are contradictory.  The corrected bundle replaces the second conjunct by
`HasCompactSupport (fun y => f y - 1)`; here we show that

* the cutoff conjuncts (including `C⁹` regularity and the compactly supported shift) are
  jointly satisfiable at *every* compact target set (`shiftedCutoff_nonempty`);
* consequently the canonical corrected bundle is inhabited as soon as the honest analytic strip
  bound holds (`weightedStripDataAtRepair_of_stripBound`, and the scalar analogue) — the strip
  bound is the *only* remaining conjunct;
* unconditionally, the corrected bundle has a genuine inhabitant at coefficient dimension `0`,
  where the strip inequality is trivially true (`weightedStripDataAtRepairGen_nonempty_zeroDim`).
-/

open Set Metric in
/-- **A `C^n` smooth cutoff separating a compact set from the complement of its
`ε`-neighbourhood.**

This is `exists_contDiff_cutoff` (`Probability/CutoffConstruction.lean`) with the regularity
`C¹` replaced by `C^n`; the construction (a finite product of `1 - φ x` with smooth bumps `φ x`)
is unchanged, and `ContDiffBump.contDiff` is available at every order. -/
theorem exists_contDiff_cutoff_order (n : ℕ) {S : Set ℝ} (hS : IsCompact S) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ f : ℝ → ℝ,
      ContDiff ℝ n f ∧
      (∀ x, 0 ≤ f x) ∧
      (∀ x ∈ S, f x = 0) ∧
      (∀ x, x ∉ S + Set.Ioo (-ε) ε → f x = 1) ∧
      (∀ x, f x ≤ 1) ∧
      (∀ x ∈ S, deriv f x = 0) ∧
      HasCompactSupport (fun x => (deriv f x) ^ 2) := by
  classical
  let φ : (i : S) → ContDiffBump (i : ℝ) :=
    fun _ => { rIn := ε / 4, rOut := ε / 2, rIn_pos := by linarith
               rIn_lt_rOut := by linarith }
  have hcover : S ⊆ ⋃ i : S, Metric.ball (i : ℝ) (ε / 4) := by
    intro x hx
    refine Set.mem_iUnion.2 ⟨⟨x, hx⟩, ?_⟩
    rw [Metric.mem_ball]
    simpa using (show (0 : ℝ) < ε / 4 by linarith)
  obtain ⟨t, ht⟩ := hS.elim_finite_subcover (fun i : S => Metric.ball (i : ℝ) (ε / 4))
    (fun _ => Metric.isOpen_ball) hcover
  let f : ℝ → ℝ := fun x => ∏ i ∈ t, (1 - (φ i : ℝ → ℝ) x)
  have hf_def : ∀ x, f x = ∏ i ∈ t, (1 - (φ i : ℝ → ℝ) x) := fun _ => rfl
  have htsupp_subset : ∀ i : S, tsupport (φ i) ⊆ S + Set.Ioo (-ε) ε := by
    intro i y hy
    have hbase : tsupport (φ i) = Metric.closedBall (i : ℝ) (ε / 2) := by
      simpa [φ] using ContDiffBump.tsupport_eq (f := φ i)
    have hd : dist y (i : ℝ) ≤ ε / 2 := by
      rw [hbase] at hy
      simpa using hy
    refine ⟨i, i.2, y - i, ?_, by ring⟩
    rw [Set.mem_Ioo]
    have hd' : |y - (i : ℝ)| ≤ ε / 2 := by
      rw [← Real.dist_eq]
      exact hd
    rw [abs_le] at hd'
    constructor <;> linarith [hd'.1, hd'.2]
  have hzero_on_cover :
      ∀ y ∈ ⋃ i ∈ (t : Set S), Metric.ball (i : ℝ) (ε / 4), f y = 0 := by
    intro y hy
    obtain ⟨i, hit, hyi⟩ := Set.mem_iUnion₂.1 hy
    rw [hf_def]
    refine Finset.prod_eq_zero hit ?_
    have hmem : y ∈ Metric.closedBall (i : ℝ) (ε / 4) := Metric.ball_subset_closedBall hyi
    have hone : (φ i : ℝ → ℝ) y = 1 :=
      ContDiffBump.one_of_mem_closedBall (f := φ i) (by simpa [φ] using hmem)
    simp [hone]
  have hf_nonneg : ∀ x, 0 ≤ f x := by
    intro x
    rw [hf_def]
    exact Finset.prod_nonneg fun i _ =>
      sub_nonneg.2 (ContDiffBump.le_one (f := φ i) (x := x))
  have hf_le_one : ∀ x, f x ≤ 1 := by
    intro x
    rw [hf_def]
    refine Finset.prod_le_one₀ (fun i _ =>
      sub_nonneg.2 (ContDiffBump.le_one (f := φ i) (x := x))) ?_
    intro i _
    have h0 : 0 ≤ (φ i : ℝ → ℝ) x := ContDiffBump.nonneg (f := φ i) (x := x)
    linarith
  have hf_one_outside : ∀ x, x ∉ S + Set.Ioo (-ε) ε → f x = 1 := by
    intro x hx
    rw [hf_def]
    refine Finset.prod_eq_one ?_
    intro i hit
    have hzero : (φ i : ℝ → ℝ) x = 0 := by
      by_contra hne
      exact hx (htsupp_subset i (subset_tsupport (φ i) (by
        simpa [Function.mem_support] using hne)))
    simp [hzero]
  have hf_zero_S : ∀ x ∈ S, f x = 0 := by
    intro x hx
    exact hzero_on_cover x (ht hx)
  have hf_contDiff : ContDiff ℝ n f := by
    have hfun : f = fun x => ∏ i ∈ t, (1 - (φ i : ℝ → ℝ) x) := funext hf_def
    rw [hfun]
    exact contDiff_prod fun i _ =>
      contDiff_const.sub (ContDiffBump.contDiff (f := φ i))
  have hf_eventually_zero : ∀ x ∈ S, f =ᶠ[𝓝 x] 0 := by
    intro x hx
    have hWopen : IsOpen (⋃ i ∈ (t : Set S), Metric.ball (i : ℝ) (ε / 4)) :=
      isOpen_biUnion fun i _ => Metric.isOpen_ball
    have hxW : x ∈ ⋃ i ∈ (t : Set S), Metric.ball (i : ℝ) (ε / 4) := ht hx
    filter_upwards [hWopen.mem_nhds hxW] with y hy
    exact hzero_on_cover y hy
  have hderiv_zero_S : ∀ x ∈ S, deriv f x = 0 := by
    intro x hx
    have h := (hf_eventually_zero x hx).deriv_eq
    simpa using h
  let K : Set ℝ := ⋃ i ∈ (t : Set S), tsupport (φ i)
  have hKcompact : IsCompact K := by
    have h := Finset.isCompact_biUnion t (f := fun i : S => tsupport (φ i))
      (fun i _ => (ContDiffBump.hasCompactSupport (f := φ i)).isCompact)
    simpa [K] using h
  have hderiv_zero_off : ∀ x, x ∉ K → deriv f x = 0 := by
    intro x hx
    have hN : (⋂ i ∈ (t : Set S), (tsupport (φ i))ᶜ) ∈ 𝓝 x := by
      rw [Filter.biInter_mem t.finite_toSet]
      intro i hit
      exact (isClosed_tsupport (φ i)).isOpen_compl.mem_nhds (by
        intro hmem
        exact hx (by
          show x ∈ ⋃ i ∈ (t : Set S), tsupport (φ i)
          exact Set.mem_iUnion₂.2 ⟨i, hit, hmem⟩))
    have heq : f =ᶠ[𝓝 x] (fun _ => (1 : ℝ)) := by
      filter_upwards [hN] with y hy
      rw [hf_def]
      refine Finset.prod_eq_one ?_
      intro i hit
      have hyi : y ∉ tsupport (φ i) := by
        have := Set.mem_iInter₂.1 hy i hit
        simpa using this
      have hzero : (φ i : ℝ → ℝ) y = 0 := by
        by_contra hne
        exact hyi (subset_tsupport (φ i) (by
          simpa [Function.mem_support] using hne))
      simp [hzero]
    have h := heq.deriv_eq
    simpa using h
  have hsquare : HasCompactSupport (fun x => (deriv f x) ^ 2) := by
    refine HasCompactSupport.intro (K := K) hKcompact ?_
    intro x hx
    simp [hderiv_zero_off x hx]
  exact ⟨f, hf_contDiff, hf_nonneg, hf_zero_S, hf_one_outside, hf_le_one,
    hderiv_zero_S, hsquare⟩

/-- A continuous derivative-smoothness bookkeeping lemma. -/
theorem contDiff_deriv_of_contDiff {n : ℕ} {f : ℝ → ℝ} (hf : ContDiff ℝ (n + 1) f) :
    ContDiff ℝ n (deriv f) := by
  have h : ContDiff ℝ ((n : WithTop ℕ∞) + 1) f := hf
  exact h.deriv'

/-- **The cutoff conjuncts of the corrected bundle are jointly satisfiable.**

At every compact target set `S` and `ε > 0` there is a `C⁹` function which is a smooth cutoff
vanishing (with vanishing derivative) on `S`, whose `(f')²` is `C⁹`, and whose *shift* `f − 1`
is compactly supported.  This is precisely the conjunct that was contradictory in
`WeightedStripDataAtFinal` (`HasCompactSupport f`); here it is not. -/
theorem shiftedCutoff_nonempty {S : Set ℝ} (hS : IsCompact S) {ε : ℝ} (hε : 0 < ε) :
    ∃ f : ℝ → ℝ,
      IsSmoothCutoffZeroOn S ε f ∧
      ContDiff ℝ 9 f ∧
      ContDiff ℝ 9 (fun y => (deriv f y) ^ 2) ∧
      HasCompactSupport (fun y => f y - 1) := by
  obtain ⟨f, hcd, h0, hzero, hone, hle, hderiv, hsupp⟩ :=
    exists_contDiff_cutoff_order 10 hS hε
  have hcut : IsSmoothCutoffZeroOn S ε f :=
    ⟨⟨hcd.of_le (by norm_num), h0, hle, hone, hsupp⟩, hzero, hderiv⟩
  refine ⟨f, hcut, hcd.of_le (by norm_num), ?_,
    hasCompactSupport_sub_one_of_isSmoothCutoffZeroOn hS hcut⟩
  have hd : ContDiff ℝ 9 (deriv f) := contDiff_deriv_of_contDiff hcd
  simpa [Pi.pow_apply] using hd.pow 2

/-- **The repaired cutoff is genuinely not compactly supported.**

For a compact target set, the cutoff produced by `shiftedCutoff_nonempty` satisfies all
the corrected conjuncts (in particular `HasCompactSupport (fun y => f y - 1)`) and is **not**
compactly supported: it vanishes on `S` and equals `1` far away.  Hence the corrected bundle is
not the old bundle in disguise — the old vacuity lemma
(`not_exists_isSmoothCutoffZeroOn_and_hasCompactSupport`) does not apply to it. -/
theorem shiftedCutoff_not_compactSupport {S : Set ℝ} (hS : IsCompact S)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ f : ℝ → ℝ,
      IsSmoothCutoffZeroOn S ε f ∧
      ContDiff ℝ 9 f ∧
      ContDiff ℝ 9 (fun y => (deriv f y) ^ 2) ∧
      HasCompactSupport (fun y => f y - 1) ∧
      ¬ HasCompactSupport f := by
  obtain ⟨f, hcut, h9, h9w, hfc⟩ := shiftedCutoff_nonempty hS hε
  refine ⟨f, hcut, h9, h9w, hfc, ?_⟩
  intro hf
  obtain ⟨C, hC⟩ := hS.exists_bound_of_continuousOn continuous_id.continuousOn
  have hCabs : ∀ s ∈ S, |s| ≤ max C 0 := by
    intro s hs
    have h1 : ‖s‖ ≤ C := hC s hs
    rw [Real.norm_eq_abs] at h1
    exact h1.trans (le_max_left _ _)
  obtain ⟨r₀, hr₀⟩ := hf.isCompact.isBounded.subset_closedBall (0 : ℝ)
  have hr₀' : ∀ x ∈ tsupport f, |x| ≤ r₀ := by
    intro x hx
    have h1 := hr₀ hx
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at h1
    exact h1
  set R : ℝ := max (max C 0 + ε) r₀ + 1 with hR
  have hRpos : 0 < R := by rw [hR]; positivity
  have hRabs : |R| = R := abs_of_pos hRpos
  have hR1 : max C 0 + ε < |R| := by
    rw [hRabs, hR]
    have hle : max C 0 + ε ≤ max (max C 0 + ε) r₀ := le_max_left _ _
    linarith
  have hR2 : r₀ < |R| := by
    rw [hRabs, hR]
    have hle : r₀ ≤ max (max C 0 + ε) r₀ := le_max_right _ _
    linarith
  have hnot : R ∉ S + Set.Ioo (-ε) ε := by
    intro hmem
    obtain ⟨s, hs, t, ht, hst⟩ := Set.mem_add.mp hmem
    have ht' : |t| < ε := by
      rw [Set.mem_Ioo] at ht
      rw [abs_lt]
      exact ⟨ht.1, ht.2⟩
    have h1 : |R| = |s + t| := by rw [← hst]
    have h2 : |s + t| ≤ |s| + |t| := abs_add_le _ _
    linarith [hCabs s hs, ht'.le]
  have hone : f R = 1 := hcut.smooth.eq_one R hnot
  have hzero : f R = 0 := by
    refine image_eq_zero_of_notMem_tsupport ?_
    intro hmem
    exact absurd (hr₀' R hmem) (not_le.mpr hR2)
  rw [hzero] at hone
  exact absurd hone (by norm_num)

/-- The limit spectrum `specC (h1PencilLimit r k F z)` is compact. -/
theorem isCompact_specC_h1PencilLimit' {k : ℕ} (F : RatPolyIdx r (k + 1)) (z : ℝ) :
    IsCompact (specC (h1PencilLimit r k F z)) := by
  rw [specC]
  exact spectrum.isCompact _

/-- **The corrected bundle at general coefficients is inhabited from the strip bound alone.**

Taking the target set `S = ∅` and the shifted-zero cutoff `f ≡ 1` (so `f − 1 ≡ 0` is compactly
supported and smooth), *every* conjunct of `WeightedStripDataAtRepairGen` except the honest strip
bound is discharged.  Hence the corrected bundle is inhabited at every coefficient matrix for
which `WeightedStripBoundProven` holds: the packaging adds no obstruction. -/
theorem weightedStripDataAtRepairGen_of_stripBound {d : ℕ}
    (A₀ : Matrix (Fin d) (Fin d) ℂ) (A : Fin r → Matrix (Fin d) (Fin d) ℂ)
    {η₀ Kc C_s : ℝ} (hη₀2 : 2 < η₀) (hC_s : 0 ≤ C_s)
    (hstrip : WeightedStripBoundProven A₀ A η₀ Kc C_s) (ε : ℝ) :
    WeightedStripDataAtRepairGen r d A₀ A ∅ ε := by
  refine ⟨η₀, Kc, C_s, hη₀2, hC_s, fun _ => 1, ?_, contDiff_const, ?_, ?_, hstrip⟩
  · refine ⟨⟨contDiff_const, fun x => zero_le_one, fun x => le_refl 1, ?_, ?_⟩, ?_, ?_⟩
    · intro x hx
      rfl
    · have hz : (fun x : ℝ => (deriv (fun _ : ℝ => (1 : ℝ)) x) ^ 2)
          = fun _ => (0 : ℝ) := by
        funext x
        simp
      rw [hz]
      exact HasCompactSupport.zero
    · intro x hx
      exact absurd hx (by simp)
    · intro x hx
      exact absurd hx (by simp)
  · simpa using (contDiff_const : ContDiff ℝ 9 (fun _ : ℝ => (0 : ℝ)))
  · have hz : (fun y : ℝ => (1 : ℝ) - 1) = fun _ => (0 : ℝ) := by
      funext y
      norm_num
    rw [hz]
    exact HasCompactSupport.zero

/-- **The canonical corrected bundle is inhabited from the honest strip bound.**

The cutoff, its `C⁹` regularity, the `C⁹` regularity of `(f')²` and the compact support of the
shift are *theorems* (`shiftedCutoff_nonempty`); the only remaining conjunct is
`WeightedStripBoundProven` at the canonical coefficients. -/
theorem weightedStripDataAtRepair_of_stripBound {k : ℕ} {F : RatPolyIdx r (k + 1)} {z ε : ℝ}
    (hε : 0 < ε) {η₀ Kc C_s : ℝ} (hη₀2 : 2 < η₀) (hC_s : 0 ≤ C_s)
    (hstrip : WeightedStripBoundProven (pencilConstCoeff k F z) (pencilDirCoeff k F) η₀ Kc C_s) :
    WeightedStripDataAtRepair r k F z ε := by
  obtain ⟨f, hcut, h9, h9w, hfc⟩ :=
    shiftedCutoff_nonempty (isCompact_specC_h1PencilLimit' (r := r) F z) hε
  exact ⟨η₀, Kc, C_s, hη₀2, hC_s, f, hcut, h9, h9w, hfc, hstrip⟩

/-- **The scalar corrected bundle is inhabited from the honest strip bound.** -/
theorem scalarWeightedStripDataAtRepair_of_stripBound {i : Fin r} {ε : ℝ} (hε : 0 < ε)
    {η₀ Kc C_s : ℝ} (hη₀2 : 2 < η₀) (hC_s : 0 ≤ C_s)
    (hstrip : WeightedStripBoundProven (0 : Matrix (Fin 1) (Fin 1) ℂ) (scalarPencilCoeff i)
      η₀ Kc C_s) :
    ScalarWeightedStripDataAtRepair r i ε := by
  obtain ⟨f, hcut, h9, h9w, hfc⟩ :=
    shiftedCutoff_nonempty (isCompact_spectrum_semicircular (r := r) i) hε
  exact ⟨η₀, Kc, C_s, hη₀2, hC_s, f, hcut, h9, h9w, hfc, hstrip⟩

/-- **An unconditional inhabitant of the corrected bundle.**

At coefficient dimension `0` the matrix resolvents are `0 × 0` matrices, so both sides of the
strip inequality vanish identically and `WeightedStripBoundProven` holds with `C_s = 0`.  Together
with `shiftedCutoff_nonempty` this gives a genuine inhabitant of the full corrected bundle — in
particular the conjunction is consistent, unlike `WeightedStripInputsFinal`. -/
theorem weightedStripDataAtRepairGen_nonempty_zeroDim {S : Set ℝ} (hS : IsCompact S) {ε : ℝ}
    (hε : 0 < ε) (A₀ : Matrix (Fin 0) (Fin 0) ℂ)
    (A : Fin r → Matrix (Fin 0) (Fin 0) ℂ) :
    WeightedStripDataAtRepairGen r 0 A₀ A S ε := by
  obtain ⟨f, hcut, h9, h9w, hfc⟩ := shiftedCutoff_nonempty hS hε
  refine ⟨3, 0, 0, by norm_num, le_rfl, f, hcut, h9, h9w, hfc, ?_⟩
  filter_upwards with N
  intro z hz hlt
  have hzero : frob (gueResolventMean (N := N) A₀ A z -
      operatorMatrixPencilCauchy A₀ A z) = 0 := by
    simp [frob]
  rw [hzero]
  simp

/-! ## 8. Reduction of the honest strip bound to the near-axis annulus

`Probability/StripAnalytic.lean` proves the sharp weighted comparison **above**
`stripThreshold A` on the upper half-plane (`frob_gueResolventMean_sub_limit_le_rpow_top`).
Here we put that theorem into the shape of the honest hypothesis `WeightedStripBoundProven` at
exponent `7`: the whole strip follows from

* the near-axis annulus `0 < |Im w| < stripThreshold A` (both half-planes), and
* the lower half-plane part `Im w < 0` above the threshold,

the upper half-plane part above the threshold being a theorem.  (There is no conjugation
symmetry lemma in the repository, so the lower half-plane above the threshold cannot currently be
derived from the upper one.)

Consequently the corrected bundle is inhabited above the threshold with only the annulus data as
a hypothesis: `weightedStripDataAtRepair_of_nearAxis` and
`scalarWeightedStripDataAtRepair_of_nearAxis`. -/

/-- **The honest strip bound from the near-axis annulus and the lower half-plane.** -/
theorem WeightedStripBoundProven_of_nearAxis {ι : Type*} [Fintype ι] [DecidableEq ι]
    {d : Type*} [Fintype d] [DecidableEq d] [Nonempty d]
    (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ) (hA₀ : A₀.IsHermitian)
    (hA : ∀ i, (A i).IsHermitian) {η₀ Kc Cn Ct : ℝ} (hKc : 0 ≤ Kc)
    (hη₀ : stripThreshold A < η₀)
    (hnear : ∀ᶠ N : ℕ in atTop, ∀ w : ℂ, w.im ≠ 0 → |w.im| < stripThreshold A →
      frob (gueResolventMean (N := N) A₀ A w - operatorMatrixPencilCauchy A₀ A w)
        ≤ Cn * (Kc + ‖w‖) ^ 2 * |w.im| ^ (-(7 : ℝ)) / (N : ℝ) ^ 2)
    (hlow : ∀ᶠ N : ℕ in atTop, ∀ w : ℂ, w.im < 0 → stripThreshold A ≤ |w.im| →
      |w.im| < η₀ →
      frob (gueResolventMean (N := N) A₀ A w - operatorMatrixPencilCauchy A₀ A w)
        ≤ Ct * (Kc + ‖w‖) ^ 2 * |w.im| ^ (-(7 : ℝ)) / (N : ℝ) ^ 2) :
    WeightedStripBoundProven A₀ A η₀ Kc
      (max Cn (max Ct (sharpConstant A * max 1 (η₀ ^ ((7 : ℝ) - 5))))) := by
  set Cs : ℝ := sharpConstant A * max 1 (η₀ ^ ((7 : ℝ) - 5)) with hCs
  have hCs0 : 0 ≤ Cs := by
    rw [hCs]
    exact mul_nonneg (sharpConstant_nonneg A) (le_trans zero_le_one (le_max_left _ _))
  filter_upwards [hnear, hlow, eventually_gt_atTop (0 : ℕ)] with N hn hl hN
  intro w hw hlt
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hpow : 0 ≤ |w.im| ^ (-(7 : ℝ)) := Real.rpow_nonneg (abs_nonneg _) _
  rcases lt_or_ge |w.im| (stripThreshold A) with hnear' | hfar'
  · refine (hn w hw hnear').trans ?_
    gcongr
    exact le_max_left _ _
  · rcases lt_trichotomy w.im 0 with hneg | hzero | hpos
    · have habs : |w.im| = -w.im := abs_of_neg hneg
      have htop : |w.im| < η₀ := hlt
      refine (hl w hneg hfar' htop).trans ?_
      gcongr
      exact le_trans (le_max_left _ _) (le_max_right _ _)
    · exact absurd hzero hw
    · -- upper half-plane, above the threshold: the sharp comparison is a theorem
      have htop : w.im < η₀ := by
        rw [abs_of_pos hpos] at hlt
        exact hlt
      have hfar_up : stripThreshold A ≤ w.im := by
        rw [abs_of_pos hpos] at hfar'
        exact hfar'
      have hsharp := frob_gueResolventMean_sub_limit_le_rpow_top A₀ A hA₀ hA
        (β := (7 : ℝ)) (by norm_num) (le_of_lt hη₀) hpos hN hfar_up htop
      have hz1 : (1 : ℝ) ≤ ‖w‖ := by
        have h1 : (1 : ℝ) ≤ w.im := le_trans (one_le_stripThreshold A) hfar_up
        have h2 : w.im ≤ |w.im| := le_abs_self w.im
        have h3 : |w.im| ≤ ‖w‖ := Complex.abs_im_le_norm w
        linarith
      have hbase : (1 : ℝ) ≤ (Kc + ‖w‖) ^ 2 := by
        have h0 : (1 : ℝ) ≤ Kc + ‖w‖ := by
          have := norm_nonneg w
          linarith
        calc (1 : ℝ) = 1 ^ 2 := by norm_num
          _ ≤ (Kc + ‖w‖) ^ 2 := pow_le_pow_left₀ zero_le_one h0 2
      have ha : 0 ≤ w.im ^ (-(7 : ℝ)) := Real.rpow_nonneg (le_of_lt hpos) _
      have habs : |w.im| = w.im := abs_of_pos hpos
      have hstep : frob (gueResolventMean (N := N) A₀ A w -
          operatorMatrixPencilCauchy A₀ A w)
          ≤ Cs * (Kc + ‖w‖) ^ 2 * |w.im| ^ (-(7 : ℝ)) / (N : ℝ) ^ 2 := by
        rw [habs] at *
        refine hsharp.trans ?_
        have hCa : 0 ≤ Cs * w.im ^ (-(7 : ℝ)) := mul_nonneg hCs0 ha
        calc sharpConstant A * max 1 (η₀ ^ ((7 : ℝ) - 5)) * w.im ^ (-(7 : ℝ)) / (N : ℝ) ^ 2
            = Cs * w.im ^ (-(7 : ℝ)) / (N : ℝ) ^ 2 := by rw [hCs]
          _ ≤ Cs * ((Kc + ‖w‖) ^ 2 * w.im ^ (-(7 : ℝ))) / (N : ℝ) ^ 2 := by
              refine div_le_div_of_nonneg_right ?_ (by positivity)
              calc Cs * w.im ^ (-(7 : ℝ)) = Cs * w.im ^ (-(7 : ℝ)) * 1 := by ring
                _ ≤ Cs * w.im ^ (-(7 : ℝ)) * (Kc + ‖w‖) ^ 2 :=
                    mul_le_mul_of_nonneg_left hbase hCa
                _ = Cs * ((Kc + ‖w‖) ^ 2 * w.im ^ (-(7 : ℝ))) := by ring
          _ = Cs * (Kc + ‖w‖) ^ 2 * w.im ^ (-(7 : ℝ)) / (N : ℝ) ^ 2 := by ring
      refine hstep.trans ?_
      gcongr
      exact le_trans (le_max_right _ _) (le_max_right _ _)

/-- **The corrected canonical bundle above the threshold.**  Only the near-axis annulus and the
lower half-plane above the threshold remain as hypotheses. -/
theorem weightedStripDataAtRepair_of_nearAxis {k : ℕ} {F : RatPolyIdx r (k + 1)} {z ε : ℝ}
    (hε : 0 < ε) {Cn Ct : ℝ} (hCn : 0 ≤ Cn) (hCt : 0 ≤ Ct)
    (hnear : ∀ᶠ N : ℕ in atTop, ∀ w : ℂ, w.im ≠ 0 →
      |w.im| < stripThreshold (pencilDirCoeff k F) →
      frob (gueResolventMean (N := N) (pencilConstCoeff k F z) (pencilDirCoeff k F) w -
          operatorMatrixPencilCauchy (pencilConstCoeff k F z) (pencilDirCoeff k F) w)
        ≤ Cn * (0 + ‖w‖) ^ 2 * |w.im| ^ (-(7 : ℝ)) / (N : ℝ) ^ 2)
    (hlow : ∀ᶠ N : ℕ in atTop, ∀ w : ℂ, w.im < 0 →
      stripThreshold (pencilDirCoeff k F) ≤ |w.im| →
      |w.im| < stripThreshold (pencilDirCoeff k F) + 3 →
      frob (gueResolventMean (N := N) (pencilConstCoeff k F z) (pencilDirCoeff k F) w -
          operatorMatrixPencilCauchy (pencilConstCoeff k F z) (pencilDirCoeff k F) w)
        ≤ Ct * (0 + ‖w‖) ^ 2 * |w.im| ^ (-(7 : ℝ)) / (N : ℝ) ^ 2) :
    WeightedStripDataAtRepair r k F z ε := by
  refine weightedStripDataAtRepair_of_stripBound (η₀ := stripThreshold (pencilDirCoeff k F) + 3)
    (Kc := 0) (C_s := max Cn (max Ct (sharpConstant (pencilDirCoeff k F) *
      max 1 ((stripThreshold (pencilDirCoeff k F) + 3) ^ ((7 : ℝ) - 5))))) hε ?_
    (le_trans hCn (le_max_left _ _)) ?_
  · have h1 := one_le_stripThreshold (pencilDirCoeff k F)
    linarith
  · exact WeightedStripBoundProven_of_nearAxis (pencilConstCoeff k F z) (pencilDirCoeff k F)
      (pencilConstCoeff_isHermitian k F z) (pencilDirCoeff_isHermitian k F) le_rfl
      (by linarith [one_le_stripThreshold (pencilDirCoeff k F)]) hnear hlow

/-- **The corrected scalar bundle above the threshold.** -/
theorem scalarWeightedStripDataAtRepair_of_nearAxis {i : Fin r} {ε : ℝ} (hε : 0 < ε)
    {Cn Ct : ℝ} (hCn : 0 ≤ Cn) (hCt : 0 ≤ Ct)
    (hnear : ∀ᶠ N : ℕ in atTop, ∀ w : ℂ, w.im ≠ 0 →
      |w.im| < stripThreshold (scalarPencilCoeff i) →
      frob (gueResolventMean (N := N) (0 : Matrix (Fin 1) (Fin 1) ℂ) (scalarPencilCoeff i) w -
          operatorMatrixPencilCauchy (0 : Matrix (Fin 1) (Fin 1) ℂ) (scalarPencilCoeff i) w)
        ≤ Cn * (0 + ‖w‖) ^ 2 * |w.im| ^ (-(7 : ℝ)) / (N : ℝ) ^ 2)
    (hlow : ∀ᶠ N : ℕ in atTop, ∀ w : ℂ, w.im < 0 →
      stripThreshold (scalarPencilCoeff i) ≤ |w.im| →
      |w.im| < stripThreshold (scalarPencilCoeff i) + 3 →
      frob (gueResolventMean (N := N) (0 : Matrix (Fin 1) (Fin 1) ℂ) (scalarPencilCoeff i) w -
          operatorMatrixPencilCauchy (0 : Matrix (Fin 1) (Fin 1) ℂ) (scalarPencilCoeff i) w)
        ≤ Ct * (0 + ‖w‖) ^ 2 * |w.im| ^ (-(7 : ℝ)) / (N : ℝ) ^ 2) :
    ScalarWeightedStripDataAtRepair r i ε := by
  refine scalarWeightedStripDataAtRepair_of_stripBound (η₀ := stripThreshold (scalarPencilCoeff i) + 3)
    (Kc := 0) (C_s := max Cn (max Ct (sharpConstant (scalarPencilCoeff i) *
      max 1 ((stripThreshold (scalarPencilCoeff i) + 3) ^ ((7 : ℝ) - 5))))) hε ?_
    (le_trans hCn (le_max_left _ _)) ?_
  · have h1 := one_le_stripThreshold (scalarPencilCoeff i)
    linarith
  · exact WeightedStripBoundProven_of_nearAxis (0 : Matrix (Fin 1) (Fin 1) ℂ)
      (scalarPencilCoeff i) isHermitian_zero (scalarPencilCoeff_isHermitian i) le_rfl
      (by linarith [one_le_stripThreshold (scalarPencilCoeff i)]) hnear hlow

end

end GUEStrongConvergence
