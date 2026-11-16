/-
# Worker D — machine-checked audit of the terminal analytic hypotheses

This file is the kernel-checked companion of `docs/handoffs/TERMINAL_AUDIT.md`.

It records, for the two final conditional theorems of the project

* `GUEStrongConvergenceStatement_of_weightedStripInputsFinal`
  (`StrongConvergence/FinalReduction.lean:683`), and
* `GUEStrongConvergenceStatement_of_pencilStrip_and_edgeBound`
  (`StrongConvergence/EdgeBound.lean:152`),

the following facts about the `Prop`-valued objects in their dependency graph.

## 1. The pencil bundle is UNINHABITED as stated (vacuity defect)

`WeightedStripDataAtFinal` (`FinalReduction.lean:134`) requires simultaneously
`IsSmoothCutoffZeroOn S ε f`, whose field `IsSmoothCutoff.eq_one` forces `f = 1` outside the
bounded set `S + Ioo (-ε) ε`, and `HasCompactSupport f`, which forces `f = 0` outside a compact
set.  For compact `S` (the actual instantiation: `S = specC (h1PencilLimit r k F z)` or the
spectrum of a semicircular element) these are contradictory.  Hence

`not_exists_isSmoothCutoffZeroOn_and_hasCompactSupport`, and consequently
`weightedStripDataAtFinal_uninhabited`, `scalarWeightedStripDataAt_uninhabited`,
`weightedStripInputsFinal_uninhabited`, `pencilStripField_uninhabited`.

So both final theorems are *vacuously* true as stated on main: they prove nothing about GUE
until the compact-support field is replaced by `HasCompactSupport (fun x => f x - 1)`
(the repair bricks `hasCompactSupport_sub_one_of_isSmoothCutoffZeroOn`,
`gueStatisticCfc_sub_one`, `flatStat_sub_one` are already on main).

## 2. Genuinely discharged terminal hypotheses

* `IsSmoothCutoffZeroOn` / `IsSmoothCutoff`: producer `exists_isSmoothCutoffZeroOn` /
  `exists_isSmoothCutoff` (`Probability/LemmaMWeighted.lean:526`,
  `StrongConvergence/ScalarInclusionSmooth.lean:428`), instantiated below at the concrete
  spectra.
* the variance field `hV` of `PencilLemmaSResidual` is *not* a hypothesis: producer
  `hV_field_residual_shape` (`StrongConvergence/FlatHVField.lean:305`).
* `hWords` / II.B: producer `ae_all_words_gueNormTrace_tau_unconditional`
  (`StrongConvergence/FreeMomentBridgeProof.lean:257`).
* `hEdge` from `GUEEdgeBound`, `hB` from the generator bound: producers in `EdgeBound.lean` /
  `FinalWiring.lean`.

## 3. Non-vacuity witnesses

`flatLemmaM_zero` is a genuine instance of the terminal mean-comparison shape with the zero
test function.  It shows that `FlatLemmaM` itself is not an inconsistent predicate.

## 4. The scalar edge: the missing tail input

`GUEEdgeTail` is the summability of the one-eigenvalue tail probabilities; `gueEdgeBound_of_tail`
proves `GUEEdgeTail r → GUEEdgeBound r` by Borel--Cantelli
(`Probability/CommonSpaceBorelCantelli.lean`).  This isolates exactly the probabilistic input
that concentration/large deviations have to supply (Gaussian LSI is available in the pinned
`lean-log-sobolev`).
-/
import GUEStrongConvergence.StrongConvergence.EdgeBound
import GUEStrongConvergence.Probability.CommonSpaceBorelCantelli

open Filter MeasureTheory ProbabilityTheory FreeProbability FreeProbability.Fock Matrix
open scoped BigOperators ComplexOrder ENNReal Pointwise Topology

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

local instance auditNontrivial : Nontrivial (closedSemicircularAlgebra (Fin r)) :=
  (closedGeneratedVacuumState (Fin r)).toProbabilitySpace.nontrivial

local instance auditPartialOrder : PartialOrder (closedSemicircularAlgebra (Fin r)) :=
  CStarAlgebra.spectralOrder _

local instance auditStarOrderedRing : StarOrderedRing (closedSemicircularAlgebra (Fin r)) :=
  CStarAlgebra.spectralOrderedRing _

/-! ## 1. The vacuity defect: no cutoff is both `1` at infinity and compactly supported -/

/-- **Vacuity lemma.**  For a compact `S` and `ε > 0` there is no function that is a smooth
cutoff vanishing on `S` (in the sense of `IsSmoothCutoffZeroOn`, whose `IsSmoothCutoff`
component forces `f = 1` outside the bounded set `S + Ioo (-ε) ε`) and has compact support.

This is the exact reason why `WeightedStripDataAtFinal` and `ScalarWeightedStripDataAt` are
uninhabited, and hence why the two final conditional theorems are vacuous as stated. -/
theorem not_exists_isSmoothCutoffZeroOn_and_hasCompactSupport {S : Set ℝ} (hS : IsCompact S)
    {ε : ℝ} (hε : 0 < ε) :
    ¬ ∃ f : ℝ → ℝ, IsSmoothCutoffZeroOn S ε f ∧ HasCompactSupport f := by
  rintro ⟨f, hcut, hfc⟩
  obtain ⟨C, hC⟩ := hS.exists_bound_of_continuousOn continuous_id.continuousOn
  have hCabs : ∀ s ∈ S, |s| ≤ max C 0 := by
    intro s hs
    have h1 : ‖s‖ ≤ C := hC s hs
    rw [Real.norm_eq_abs] at h1
    exact h1.trans (le_max_left _ _)
  obtain ⟨r₀, hr₀⟩ := hfc.isCompact.isBounded.subset_closedBall (0 : ℝ)
  have hr₀' : ∀ x ∈ tsupport f, |x| ≤ r₀ := by
    intro x hx
    have h1 := hr₀ hx
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at h1
    exact h1
  -- a point far beyond both the `S`-neighbourhood and the support of `f`
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


/-! ### 1b. The concrete instantiations -/

/-- The limit spectrum `specC (h1PencilLimit r k F z)` is compact. -/
theorem isCompact_specC_h1PencilLimit {k : ℕ} (F : RatPolyIdx r (k + 1)) (z : ℝ) :
    IsCompact (specC (h1PencilLimit r k F z)) := by
  rw [specC]
  exact spectrum.isCompact _

/-- **`WeightedStripDataAtFinal` is uninhabited at every actual parameter.**
(`FinalReduction.lean:134`.) -/
theorem weightedStripDataAtFinal_uninhabited {k : ℕ} {F : RatPolyIdx r (k + 1)} {z ε : ℝ}
    (hε : 0 < ε) : ¬ WeightedStripDataAtFinal r k F z ε := by
  intro h
  obtain ⟨η₀, C_s, β, hη₀2, hC_s, hβ0, hβm, f, C', hcut, _hreg, _hregw, hfc,
    _hstrip, _hC'⟩ := h
  exact not_exists_isSmoothCutoffZeroOn_and_hasCompactSupport
    (isCompact_specC_h1PencilLimit (r := r) F z) hε ⟨f, hcut, hfc⟩

/-- **`ScalarWeightedStripDataAt` is uninhabited at every actual parameter.**
(`FinalReduction.lean:399`.) -/
theorem scalarWeightedStripDataAt_uninhabited {i : Fin r} {ε : ℝ} (hε : 0 < ε) :
    ¬ ScalarWeightedStripDataAt r i ε := by
  intro h
  obtain ⟨η₀, C_s, β, hη₀2, hC_s, hβ0, hβ1, f, C', hcut, _hreg, _hregw, hfc,
    _hstrip, _hC'⟩ := h
  exact not_exists_isSmoothCutoffZeroOn_and_hasCompactSupport
    (isCompact_spectrum_semicircular (r := r) i) hε ⟨f, hcut, hfc⟩

/-- **`WeightedStripDataAt'''` is uninhabited at every actual parameter.**
(`LimitFlatten.lean:679`.) -/
theorem weightedStripDataAtTriplePrime_uninhabited {k : ℕ} {F : RatPolyIdx r (k + 1)}
    {z ε : ℝ} (hε : 0 < ε) : ¬ WeightedStripDataAt''' r k F z ε := by
  intro h
  obtain ⟨η₀, C_s, β, hη₀2, hC_s, hβ0, hβk, f, C', hcut, _hreg, _hregw, hfc,
    _hstrip, _hC'⟩ := h
  exact not_exists_isSmoothCutoffZeroOn_and_hasCompactSupport
    (isCompact_specC_h1PencilLimit (r := r) F z) hε ⟨f, hcut, hfc⟩

/-- **The two-field final bundle `WeightedStripInputsFinal` is uninhabited.**
(`FinalReduction.lean:659`.)  Hence
`GUEStrongConvergenceStatement_of_weightedStripInputsFinal` is vacuous. -/
theorem weightedStripInputsFinal_uninhabited (r : ℕ) : ¬ WeightedStripInputsFinal r := by
  intro h
  have h0 : WeightedStripDataAtFinal r 0 (0 : RatPolyIdx r 1) 0 1 :=
    h.1 0 (0 : RatPolyIdx r 1) 0 1 one_pos
  exact weightedStripDataAtFinal_uninhabited
    (r := r) (k := 0) (F := (0 : RatPolyIdx r 1)) (z := 0) (ε := 1) one_pos h0

/-- **The pencil field of `GUEStrongConvergenceStatement_of_pencilStrip_and_edgeBound` is
uninhabited.**  (`EdgeBound.lean:152`.)  Hence that theorem is vacuous as stated too. -/
theorem pencilStripField_uninhabited (r : ℕ) :
    ¬ (∀ (k : ℕ) (F : RatPolyIdx r (k + 1)) (z ε : ℝ), 0 < ε →
        WeightedStripDataAtFinal r k F z ε) := by
  intro h
  exact weightedStripDataAtFinal_uninhabited
    (r := r) (k := 0) (F := (0 : RatPolyIdx r 1)) (z := 0) (ε := 1) one_pos
    (h 0 (0 : RatPolyIdx r 1) 0 1 one_pos)


/-! ## 2. Genuinely discharged terminal hypotheses -/

/-- **Discharged (general form).**  A smooth cutoff vanishing, with vanishing derivative, on a
compact set exists.  Producer: `exists_isSmoothCutoffZeroOn`
(`Probability/LemmaMWeighted.lean:526`). -/
theorem terminal_isSmoothCutoffZeroOn_discharged {S : Set ℝ} (hS : IsCompact S) {ε : ℝ}
    (hε : 0 < ε) : ∃ f : ℝ → ℝ, IsSmoothCutoffZeroOn S ε f :=
  (exists_isSmoothCutoffZeroOn hS hε).imp fun _ h => h.1

/-- **Discharged at the pencil limit spectrum** `specC (h1PencilLimit r k F z)`. -/
theorem terminal_isSmoothCutoffZeroOn_pencil_discharged {k : ℕ} (F : RatPolyIdx r (k + 1))
    (z : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ f : ℝ → ℝ, IsSmoothCutoffZeroOn (specC (h1PencilLimit r k F z)) ε f :=
  terminal_isSmoothCutoffZeroOn_discharged (isCompact_specC_h1PencilLimit F z) hε

/-- **Discharged at the scalar limit spectrum** `spectrum ℝ (semicircularFamily r i)`. -/
theorem terminal_isSmoothCutoffZeroOn_scalar_discharged {i : Fin r} {ε : ℝ} (hε : 0 < ε) :
    ∃ f : ℝ → ℝ, IsSmoothCutoffZeroOn (spectrum ℝ (semicircularFamily r i)) ε f :=
  terminal_isSmoothCutoffZeroOn_discharged (isCompact_spectrum_semicircular (r := r) i) hε

/-- **Discharged.**  The plain smooth-cutoff predicate also has a producer,
`exists_isSmoothCutoff` (`StrongConvergence/ScalarInclusionSmooth.lean:428`). -/
theorem terminal_isSmoothCutoff_discharged {S : Set ℝ} (hS : IsCompact S) {ε : ℝ}
    (hε : 0 < ε) : ∃ f : ℝ → ℝ, IsSmoothCutoff S ε f :=
  exists_isSmoothCutoff hS hε

/-- **Discharged.**  The `hV` (Lemma V) field of `PencilLemmaSResidual` is *not* a hypothesis:
producer `hV_field_residual_shape` (`StrongConvergence/FlatHVField.lean:305`), built on the
unconditional Poincaré/Cauchy--Schwarz variance bound `flatLemmaV_hV_unconditional`. -/
theorem terminal_lemmaV_field_discharged {k : ℕ} (F : RatPolyIdx r (k + 1)) (z : ℝ)
    {ε : ℝ} {f : ℝ → ℝ} (hf : IsSmoothCutoff (specC (h1PencilLimit r k F z)) ε f) :
    ∀ᶠ N : ℕ in atTop,
      variance (flatStat r k F z N f) (commonGaussianMeasure (Fin r))
        ≤ (2 * flatContractionConst r k F / pencilVDim r k F) / (N : ℝ) ^ 2
            * ∫ x, flatStat r k F z N (fun y => (deriv f y) ^ 2) x
                ∂(commonGaussianMeasure (Fin r)) :=
  hV_field_residual_shape k F z hf hf.contDiff

/-- **Discharged.**  Target part II.B: all scalar trace-word moments converge almost surely to
the free moments.  Producer `ae_all_words_gueNormTrace_tau_unconditional`
(`StrongConvergence/FreeMomentBridgeProof.lean:257`); ingredients `hblock`
(`Probability/GUEBlockSplitFinal.lean:652`) and `freeMomentBridge`
(`StrongConvergence/FreeMomentBridgeProof.lean:249`) are theorems, not hypotheses. -/
theorem terminal_hWords_discharged (r : ℕ) :
    ∀ᵐ x ∂(commonGaussianMeasure (Fin r)), ∀ w : List (Fin r),
      Tendsto (fun N : ℕ => gueNormTrace (N := N) w (x N)) atTop (𝓝 (tau r w)) :=
  ae_all_words_gueNormTrace_tau_unconditional r

/-- **Discharged.**  The `ℓ¹` edge input `hEdge` of `FinalStatement.lean` follows
deterministically from `GUEEdgeBound`; producer
`eventually_tupleNorm_gueFamily_le_of_gueEdgeBound` (`StrongConvergence/EdgeBound.lean`). -/
theorem terminal_hEdge_discharged (h : GUEEdgeBound r) :
    ∀ᵐ x ∂(commonGaussianMeasure (Fin r)),
      ∀ᶠ N : ℕ in atTop, tupleNorm (gueFamily r N x) ≤ 3 * r :=
  eventually_tupleNorm_gueFamily_le_of_gueEdgeBound h

/-! ## 3. A non-vacuity witness for `FlatLemmaM` -/

/-- **Genuine instance of the terminal mean-comparison shape.**  With the zero test function
the flattened statistic is identically zero, so `FlatLemmaM r k F z (fun _ => 0) 0` holds
outright.  This shows that `FlatLemmaM` (and hence the mean-comparison shape consumed by
Lemma S) is a consistent predicate, independently of the vacuous bundle. -/
theorem flatLemmaM_zero (k : ℕ) (F : RatPolyIdx r (k + 1)) (z : ℝ) :
    FlatLemmaM r k F z (fun _ => 0) 0 := by
  rw [FlatLemmaM]
  filter_upwards with N
  simp [flatStat, hermCfc, normTrace]

/-! ## 4. The scalar edge: the missing tail input -/

/-- **The missing tail input for the GUE edge bound.**  Summability over `N` of the probability
that the `N`-th normalized GUE block has operator norm exceeding `2 + ε`.

This is exactly what Borel--Cantelli consumes.  It is classically true (large deviations for
GUE, or Gaussian concentration + `E ‖G_i‖ ≤ 2 + ε`), and it is the honest residual
probabilistic input behind `GUEEdgeBound`; it is *not* implied by fixed-order moment limits. -/
def GUEEdgeTail (r : ℕ) : Prop :=
  ∀ i : Fin r, ∀ ε : ℝ, 0 < ε →
    Summable fun N : ℕ =>
      (stdGaussian (EuclideanSpace ℝ (GUECoord (Fin r) N))).real
        {y | 2 + ε < ‖CStarMatrix.ofMatrix (gueMatrix (ι := Fin r) y i)‖}

/-- **The tail input implies the GUE edge bound** (Borel--Cantelli,
`ae_eventually_not_mem_of_summable`).  The measurability side condition is immediate in
practice (each entry of `y ↦ gueMatrix y i` is measurable, and the operator norm is continuous);
it is kept explicit only because the `CStarMatrix` type synonym carries no `MeasurableSpace`
instance in this toolchain. -/
theorem gueEdgeBound_of_tailMeasures (h : GUEEdgeTail r)
    (hmeas : ∀ (i : Fin r) (ε : ℝ) (N : ℕ), MeasurableSet
      {y : EuclideanSpace ℝ (GUECoord (Fin r) N) |
        2 + ε < ‖CStarMatrix.ofMatrix (gueMatrix (ι := Fin r) y i)‖}) :
    GUEEdgeBound r := by
  have key : ∀ (i : Fin r) (ε : ℝ), 0 < ε → ∀ᵐ x ∂(commonGaussianMeasure (Fin r)),
      ∀ᶠ N : ℕ in atTop, ‖gueFamily r N x i‖ ≤ 2 + ε := by
    intro i ε hε
    have hsum := h i ε hε
    have hb := ae_eventually_not_mem_of_summable (ι := Fin r)
      (fun N => {y : EuclideanSpace ℝ (GUECoord (Fin r) N) |
        2 + ε < ‖CStarMatrix.ofMatrix (gueMatrix (ι := Fin r) y i)‖})
      (hmeas i ε) hsum
    filter_upwards [hb] with x hx
    filter_upwards [hx] with N hN
    have hval : ‖gueFamily r N x i‖
        = ‖CStarMatrix.ofMatrix (gueMatrix (ι := Fin r) (x N) i)‖ := rfl
    rw [hval]
    exact not_lt.mp hN
  have hcount : ∀ᵐ x ∂(commonGaussianMeasure (Fin r)),
      ∀ i : Fin r, ∀ m : ℕ, ∀ᶠ N : ℕ in atTop,
        ‖gueFamily r N x i‖ ≤ 2 + 1 / ((m : ℝ) + 1) := by
    rw [ae_all_iff]
    intro i
    rw [ae_all_iff]
    intro m
    exact key i (1 / ((m : ℝ) + 1)) (by positivity)
  rw [GUEEdgeBound]
  filter_upwards [hcount] with x hx i ε hε
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt hε
  filter_upwards [hx i m] with N hN
  linarith


/-! ## 5. NOT DISCHARGED — exact statements of the terminal undischarged hypotheses

The blocks below are comments (not Lean declarations) because these objects are *assumed*,
not proved.  Each block gives the exact Lean name, file:line and the verbatim statement.
Every one of them is moreover **inhabited only vacuously**: the pencil/scalar bundles contain
the contradictory pair `IsSmoothCutoffZeroOn … f` (which forces `f = 1` outside a bounded set)
and `HasCompactSupport f` (which forces `f = 0` outside a compact set) — see §1.
 -/

-- NOT DISCHARGED ------------------------------------------------------------------------
-- WeightedStripBound            Probability/LemmaMWeighted.lean:123
--   No producer anywhere in the repository: every occurrence is a hypothesis
--   (LemmaMWeighted.lean:420,485,552; ExtensionOrderFree.lean:99,148;
--    FinalReduction.lean:87).  It is the single analytic input of the mean comparison.
--   The matched near-axis form is *not* a consequence of the sharp Dyson estimate
--   `frob_gueResolventMean_sub_limit_le_sharp` (Probability/DysonLimitSharp.lean:38), which
--   only gives `C |Im z|^{-5}/N^2` under the threshold `(Im z)^2 ≥ 2 d^2 ∑ frob(A_i)^2`.
--
-- def WeightedStripBound (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
--     (_k : ℕ) (η₀ C_s β : ℝ) : Prop :=
--   ∀ᶠ N : ℕ in atTop, ∀ z : ℂ, z.im ≠ 0 → |z.im| < η₀ →
--     frob (gueResolventMean (N := N) A₀ A z - operatorMatrixPencilCauchy A₀ A z)
--       ≤ C_s * |z.im| ^ (-β) / (N : ℝ) ^ 2
--
-- MATHEMATICAL STATUS: (c) likely FALSE as stated.  `operatorMatrixPencilCauchy` is the
-- vacuum expectation of the resolvent of the operator-valued pencil
-- (`.lake/packages/lean-free-prob/FreeProbability/OperatorValued/MatrixPencilResolvent.lean:21`),
-- i.e. the fixed point of the operator-valued Dyson equation — not an explicit integral.  The
-- inequality is a *pointwise-in-z* statement on the whole strip `|Im z| < η₀`, with
-- `0 ≤ β < max k 1` (so `β < 1` at `k = 0`/scalar).  Near the spectral edge at scale
-- `|Im z| ≍ N^{-2/3}` the mean resolvent differs from its limit at order `N^{-1/3}` (Airy
-- scaling), while the required right side is at most `C N^{-4/3}`; and the repo's own sharp
-- Dyson bound needs `|z.im|^{-5}` and a lower threshold.  Only an *integrated* (weighted
-- Cauchy–Pompeiu) form is plausibly true; the pointwise form is not.
-- ----------------------------------------------------------------------------------------

-- NOT DISCHARGED ------------------------------------------------------------------------
-- WeightedStripDataAtFinal       StrongConvergence/FinalReduction.lean:134
--   Assumed by `GUEStrongConvergenceStatement_of_weightedStripInputsFinal` (:683) and by
--   `GUEStrongConvergenceStatement_of_pencilStrip_and_edgeBound` (EdgeBound.lean:152, via
--   `WeightedStripInputs'''_of_weightedStripDataAtFinal`).  Machine-checked uninhabited:
--   `weightedStripDataAtFinal_uninhabited` above.
--
-- def WeightedStripDataAtFinal (r k : ℕ) (F : RatPolyIdx r (k + 1)) (z ε : ℝ) : Prop :=
--   letI : Nonempty (Fin (pencilCoeffDim k F)) :=
--     ⟨⟨0, pencilCoeffDim_pos r k F⟩⟩
--   ∃ (η₀ C_s β : ℝ) (hη₀2 : 2 < η₀) (hC_s : 0 ≤ C_s) (hβ0 : 0 ≤ β)
--     (hβm : β < max k 1) (f : ℝ → ℝ) (C' : ℝ),
--     IsSmoothCutoffZeroOn (specC (h1PencilLimit r k F z)) ε f ∧
--     ContDiff ℝ (max k 1 + 1) f ∧
--     ContDiff ℝ (max k 1 + 1) (fun y => (deriv f y) ^ 2) ∧
--     HasCompactSupport f ∧
--     WeightedStripBound (pencilConstCoeff k F z) (pencilDirCoeff k F) (max k 1) η₀ C_s β ∧
--     0 ≤ C'
--
-- MATHEMATICAL STATUS: (c) FALSE as stated (uninhabited).  After replacing `HasCompactSupport f`
-- by `HasCompactSupport (fun x => f x - 1)` the residual content is exactly the existence of
-- `η₀ > 2, C_s ≥ 0, 0 ≤ β < max k 1` with `WeightedStripBound` at the canonical coefficients;
-- the cutoff/regularity fields are then producers (`exists_isSmoothCutoffZeroOn`,
-- `hasCompactSupport_sub_one_of_isSmoothCutoffZeroOn`).
-- ----------------------------------------------------------------------------------------

-- NOT DISCHARGED ------------------------------------------------------------------------
-- ScalarWeightedStripDataAt      StrongConvergence/FinalReduction.lean:399
--   Assumed by `WeightedStripInputsFinal`; used to derive `ScalarSpectralInclusion` via
--   `scalarSpectralInclusion_of_weightedStrip`.  Machine-checked uninhabited:
--   `scalarWeightedStripDataAt_uninhabited` above.
--
-- def ScalarWeightedStripDataAt (r : ℕ) (i : Fin r) (ε : ℝ) : Prop :=
--   letI : Nonempty (Fin 1) := ⟨⟨0, by norm_num⟩⟩
--   ∃ (η₀ C_s β : ℝ) (hη₀2 : 2 < η₀) (hC_s : 0 ≤ C_s) (hβ0 : 0 ≤ β) (hβ1 : β < 1)
--     (f : ℝ → ℝ) (C' : ℝ),
--     IsSmoothCutoffZeroOn (spectrum ℝ (semicircularFamily r i)) ε f ∧
--     ContDiff ℝ 2 f ∧
--     ContDiff ℝ 2 (fun y => (deriv f y) ^ 2) ∧
--     HasCompactSupport f ∧
--     WeightedStripBound (0 : Matrix (Fin 1) (Fin 1) ℂ) (scalarPencilCoeff i) 1 η₀ C_s β ∧
--     0 ≤ C'
--
-- MATHEMATICAL STATUS: (c) FALSE as stated (uninhabited), same reason.  It is *not* implied by
-- the (now classical) edge statement `GUEEdgeBound`, and in the newer architecture
-- (`EdgeBound.lean`) this field is no longer used at all.
-- ----------------------------------------------------------------------------------------

-- NOT DISCHARGED ------------------------------------------------------------------------
-- WeightedStripInputsFinal       StrongConvergence/FinalReduction.lean:659
--   Machine-checked uninhabited: `weightedStripInputsFinal_uninhabited` above.  Hence
--   `GUEStrongConvergenceStatement_of_weightedStripInputsFinal` is vacuous.
--
-- def WeightedStripInputsFinal (r : ℕ) : Prop :=
--   (∀ (k : ℕ) (F : RatPolyIdx r (k + 1)) (z ε : ℝ), 0 < ε →
--     WeightedStripDataAtFinal r k F z ε) ∧
--   (∀ (i : Fin r) (ε : ℝ), 0 < ε → ScalarWeightedStripDataAt r i ε)
-- ----------------------------------------------------------------------------------------

-- NOT DISCHARGED ------------------------------------------------------------------------
-- WeightedStripDataAt'''         Probability/LimitFlatten.lean:679
--   Machine-checked uninhabited: `weightedStripDataAtTriplePrime_uninhabited` above.  The
--   same defect affects the earlier lineage `WeightedStripDataAt`
--   (Probability/LemmaMWeighted.lean:715), `WeightedStripDataAt'`
--   (Probability/LimitBridge.lean:758) and `WeightedStripDataAt''`
--   (Probability/LimitBridge.lean:879): each contains `HasCompactSupport f` together with
--   `IsSmoothCutoffZeroOn … f`.  The "producers" in that lineage
--   (`WeightedStripDataAt_of'`, `WeightedStripDataAt'_of_''`, `WeightedStripInputs_of_''`,
--   `WeightedStripInputs'''_of_weightedStripDataAtFinal`) only pass an equally strong
--   renamed hypothesis along, so none of them discharges the analytic input.
-- ----------------------------------------------------------------------------------------

/-! ## 6. Objects that are *not* terminal (they have conditional producers)

For completeness, the remaining `Prop` objects in the dependency graph of the two final
theorems are NOT terminal:

* `FlatLemmaM` (FlatSideConditions.lean:271): producer `flatLemmaM_of_weightedStrip`
  (LemmaMWeighted.lean:552) / `flatLemmaM_of_weightedStrip_order` (FinalReduction.lean:87),
  conditional on `WeightedStripBound`.  Genuine (trivial) instance: `flatLemmaM_zero` above.
* `WeightedMeanInputs` (LemmaMWeighted.lean:640): producer
  `WeightedMeanInputs_of_weightedStripDataAtFinal` (FinalReduction.lean:157).
* `PencilLemmaSResidualInputs` (FlatSideConditions.lean:312): producer
  `PencilLemmaSResidualInputs_of_weightedMeanInputs` (LemmaMWeighted.lean:651).
* `PencilLemmaSInputs` (FlattenPencil.lean:201): producer
  `PencilLemmaSInputs_of_weightedMeanInputs` (LemmaMWeighted.lean:674).
* `PencilSpectralInclusionData` (PencilSpectralInclusion.lean:580): producer
  `pencilSpectralInclusionData_of_lemmaSInputs` (FlattenPencil.lean:325).  It is an
  *inclusion of spectra*, strictly weaker than the norm-convergence target.
* `H1CanonicalDilated` (FinalWiring.lean:313): producer
  `H1CanonicalDilated_of_lemmaSInputs` (FlattenPencil.lean:332).
* `ScalarSpectralInclusion` (CutoffExclusion.lean:331): producer
  `scalarSpectralInclusion_of_weightedStrip` (FinalReduction.lean:497) conditional on the
  vacuous scalar bundle; equivalent to `GUEEdgeBound` in the newer architecture
  (`EdgeBoundSpectrum.lean`, not registered because a pinned dependency module is unbuilt).
* `GUEEdgeBound` (EdgeBound.lean:60): no producer; classical no-outlier statement.  The clean
  missing tail input is `GUEEdgeTail` above, and `gueEdgeBound_of_tailMeasures` reduces
  `GUEEdgeTail` to it.

The identification fields `hstat` / `hlim0` / `hIntLim` of the older bundles do **not** occur in
the two final theorems: at the canonical coefficients they are theorems
(`flatGUEStatisticEqCont_canonical`, `guePlaneLimitOrder_eq_zero_of_eq_zero_on_spectrum`,
`eventually_integrable_dbarNumOrder_...`), see `FinalReduction.lean:730-760`.
-/


/-! ## 7. Axiom audit -/

#print axioms not_exists_isSmoothCutoffZeroOn_and_hasCompactSupport
#print axioms weightedStripDataAtFinal_uninhabited
#print axioms scalarWeightedStripDataAt_uninhabited
#print axioms weightedStripDataAtTriplePrime_uninhabited
#print axioms weightedStripInputsFinal_uninhabited
#print axioms pencilStripField_uninhabited
#print axioms terminal_isSmoothCutoffZeroOn_discharged
#print axioms terminal_isSmoothCutoffZeroOn_pencil_discharged
#print axioms terminal_isSmoothCutoffZeroOn_scalar_discharged
#print axioms terminal_isSmoothCutoff_discharged
#print axioms terminal_lemmaV_field_discharged
#print axioms terminal_hWords_discharged
#print axioms terminal_hEdge_discharged
#print axioms flatLemmaM_zero
#print axioms gueEdgeBound_of_tailMeasures

end

end GUEStrongConvergence
