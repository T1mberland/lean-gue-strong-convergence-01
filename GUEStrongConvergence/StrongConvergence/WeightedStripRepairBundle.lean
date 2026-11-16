/-
# The repaired weighted-strip bundle (honest `|Im z|⁻⁷`, extension order 8)

`StrongConvergence/WeightedStripRepair.lean` proves the Cauchy–Pompeiu transfer at the honest
exponent `−7` and extension order `8`.  This file packages the result at the level of the
*cutoff* bundle, i.e. it reproduces the downstream objects of
`WeightedMeanInputs_of_weightedStripDataAtFinal` from a corrected bundle.

The corrections relative to `WeightedStripDataAtFinal`
(`StrongConvergence/FinalReduction.lean`) are exactly the two defects of the old bundle:

1. **The exponent.**  `β` is fixed at the honest HT05 value `7` (no `β < max k 1`), and the
   extension order is the free parameter `8`, independent of the polynomial index `k`.
   Regularity is `C⁹` (`ContDiff ℝ 9`), the `(q+1)`-regularity of an order-`8` extension.
2. **The cutoff at infinity.**  `IsSmoothCutoffZeroOn` forces `f ≡ 1` outside a compact set, so
   `HasCompactSupport f` is contradictory; the honest condition is
   `HasCompactSupport (fun y => f y - 1)`.  The mean comparison is applied to the compactly
   supported difference `g = f − 1`; the exact identities
   `∫ τ_N(f) = ∫ τ_N(f − 1) + 1` and `guePlaneLimitOrder 8 A₀ A (f − 1) = −1`
   convert the comparison for `g` into `FlatLemmaM … f`.

Main results:

* `flatLemmaM_of_weightedStripProven` — `FlatLemmaM` for a compactly supported test function
  with vanishing limit statistic, from `WeightedStripBoundProven` at any order `m ≥ 8`
  (the honest analogue of `flatLemmaM_of_weightedStrip_order`);
* `limitTraceCfcC_sub_one_eq_neg_one` — the limit statistic of `f − 1` is `−1` when `f`
  vanishes on the limit spectrum;
* `integral_flatStat_sub_one` — `∫ flatStat (f − 1) + 1 = ∫ flatStat f`;
* `flatLemmaM_of_weightedStripProven_sub_one` — `FlatLemmaM … f` from the comparison for
  `f − 1` and the two identities above;
## Status (honest)

The single-pencil results above are kernel-checked.  The *bundle-level* producer
(`WeightedStripDataAtRepair`, `WeightedStripInputsRepair`,
`WeightedMeanInputs_of_weightedStripRepair`, and the scalar/final-theorem plumbing) is **not**
yet in this module: the definition `WeightedStripDataAtRepair` needs the local
`CStarAlgebra (h1Alim r k F)` instance that `StrongConvergence/FinalReduction.lean` installs
privately, and the first draft of the producer timed out during elaboration.  The intended
statement is recorded in `docs/handoffs/STRIP_EXPONENT_REPAIR.md`; no `sorry`/axiom is used
anywhere.

No `sorry`, no new axioms.
-/
import GUEStrongConvergence.StrongConvergence.WeightedStripRepair

open MeasureTheory ProbabilityTheory Matrix Filter Topology Complex
open FreeProbability FreeProbability.Fock
open scoped Matrix.Norms.Frobenius ComplexOrder ENNReal NNReal Topology BigOperators

namespace GUEStrongConvergence

noncomputable section

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 10000000

variable {ι d : Type*} [Fintype ι] [DecidableEq ι] [Fintype d] [DecidableEq d] [Nonempty d]
  {N : ℕ}

/-! ## 1. `FlatLemmaM` from the honest bound at a free order `m ≥ 8` -/

/-- **`FlatLemmaM` from the honest weighted strip bound.**

This is `flatLemmaM_of_weightedStrip_order` with the pointwise exponent replaced by the honest
`|Im z|⁻⁷` and the order constraint by `8 ≤ m` (i.e. `7 < m`).  The constant is the explicit
`weightedStripConstantProven g m Kc C_s`. -/
theorem flatLemmaM_of_weightedStripProven {r : ℕ} {k m : ℕ} {F : RatPolyIdx r (k + 1)} {z : ℝ}
    {g : ℝ → ℝ} {d' : ℕ} [NeZero d'] (A₀ : Matrix (Fin d') (Fin d') ℂ)
    (A : Fin r → Matrix (Fin d') (Fin d') ℂ) (hA₀ : A₀.IsHermitian)
    (hA : ∀ i, (A i).IsHermitian) (hm : 1 ≤ m) (hm8 : 7 < m)
    {η₀ Kc C_s : ℝ} (hη₀2 : 2 < η₀) (hC_s : 0 ≤ C_s) (hg : ContDiff ℝ (m + 1) g)
    (hgc : HasCompactSupport g) (hstrip : WeightedStripBoundProven A₀ A η₀ Kc C_s)
    (hstat : ∀ N : ℕ,
      ∫ x, flatStat r k F z N g x ∂(commonGaussianMeasure (Fin r))
        = ∫ y : EuclideanSpace ℝ (GUECoord (Fin r) (N + 1)),
            gueStatisticCfc (N := N + 1) g A₀ A hA₀ hA y
              ∂(stdGaussian (EuclideanSpace ℝ (GUECoord (Fin r) (N + 1)))))
    (hlim0 : guePlaneLimitOrder m A₀ A g = 0)
    (hIntN : ∀ᶠ N : ℕ in atTop, Integrable (fun p : ℝ × ℝ =>
      dbarNumOrder (m + 1) g (zOf p) *
        Matrix.trace (gueResolventMean (N := N) A₀ A (zOf p))))
    (hIntLim : Integrable (fun p : ℝ × ℝ => dbarNumOrder (m + 1) g (zOf p) *
      Matrix.trace (operatorMatrixPencilCauchy A₀ A (zOf p)))) :
    FlatLemmaM r k F z g (weightedStripConstantProven g m Kc C_s) := by
  have hmain : ∀ᶠ N : ℕ in atTop,
      |∫ y : EuclideanSpace ℝ (GUECoord (Fin r) (N + 1)),
          gueStatisticCfc (N := N + 1) g A₀ A hA₀ hA y
            ∂(stdGaussian (EuclideanSpace ℝ (GUECoord (Fin r) (N + 1))))|
        ≤ weightedStripConstantProven g m Kc C_s / ((N + 1 : ℕ) : ℝ) ^ 2 := by
    obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 hstrip
    obtain ⟨M₀, hM₀⟩ := eventually_atTop.1 hIntN
    refine eventually_atTop.2 ⟨max N₀ M₀, fun n hn => ?_⟩
    have hn₀ : N₀ ≤ n + 1 := le_trans (le_max_left N₀ M₀) (by omega)
    have hm₀ : M₀ ≤ n + 1 := le_trans (le_max_right N₀ M₀) (by omega)
    have hfixed := smooth_trace_comparison_of_weighted_strip_proven
      (N := n + 1) A₀ A hA₀ hA (by omega) hm hm8 hg (K := m + 1) le_rfl hgc hη₀2 hC_s
      (fun z hz hlt => hN₀ (n + 1) hn₀ z hz hlt)
      (hM₀ (n + 1) hm₀) hIntLim
    simpa [weightedStripConstantProven, hlim0] using hfixed
  filter_upwards [hmain, eventually_ge_atTop (1 : ℕ)] with N hN hN1
  rw [hstat N]
  refine hN.trans ?_
  have hC0 : 0 ≤ weightedStripConstantProven g m Kc C_s :=
    weightedStripConstantProven_nonneg (f := g) hC_s
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hsq : (N : ℝ) ^ 2 ≤ ((N : ℝ) + 1) ^ 2 := by nlinarith
  push_cast
  exact div_le_div_of_nonneg_left hC0 (by positivity) hsq

/-! ## 2. The `f ↔ f − 1` shift -/

section Shift

variable {r d : ℕ} [Nonempty (Fin d)]

local instance repairNontrivial : Nontrivial (closedSemicircularAlgebra (Fin r)) :=
  (closedGeneratedVacuumState (Fin r)).toProbabilitySpace.nontrivial

local instance repairPartialOrder : PartialOrder (closedSemicircularAlgebra (Fin r)) :=
  CStarAlgebra.spectralOrder _

local instance repairStarOrderedRing : StarOrderedRing (closedSemicircularAlgebra (Fin r)) :=
  CStarAlgebra.spectralOrderedRing _

local instance repairCfcComplex : ContinuousFunctionalCalculus ℂ (BlockLimit r d) IsStarNormal :=
  IsStarNormal.instContinuousFunctionalCalculus

local instance repairCfcReal : ContinuousFunctionalCalculus ℝ (BlockLimit r d) IsSelfAdjoint :=
  @IsSelfAdjoint.instContinuousFunctionalCalculus (BlockLimit r d) _ _ _ _ _

/-- **The limit statistic of `f − 1` is `−1` when `f` vanishes on the limit spectrum.**

On the spectrum, `f − 1 = −1`, and the continuous functional calculus is determined by the
values on the spectrum (`cfc_congr`), so `(f − 1)(h) = −1` and hence `τ_d(τ((f − 1)(h))) = −1`.
-/
theorem limitTraceCfcC_sub_one_eq_neg_one {f : ℝ → ℝ} {h : BlockLimit r d}
    (hh : IsSelfAdjoint h) (hzero : ∀ x ∈ spectrum ℝ h, f x = 0) :
    limitTraceCfcC (fun y => f y - 1) h = -1 := by
  unfold limitTraceCfcC limitCfc
  have hcongr : cfc (fun y => f y - 1) h = cfc (fun _ => (-1 : ℝ)) h := by
    refine cfc_congr (g := fun _ => (-1 : ℝ)) (a := h) ?_
    intro x hx
    show f x - 1 = -1
    rw [hzero x hx]
    ring
  have hstep : cfc (fun _ => (-1 : ℝ)) h = algebraMap ℝ (BlockLimit r d) (-1) :=
    cfc_const (-1 : ℝ) h hh
  rw [hcongr, hstep]
  simp

/-- **The limit statistic of the shifted cutoff.**  If `f` vanishes on the limit spectrum, then
the plane limit statistic of `f − 1` (compactly supported, so the identification with the trace
statistic applies) equals `−1`. -/
theorem guePlaneLimitOrder_sub_one_eq_neg_one {m K : ℕ} (hm : 1 ≤ m)
    {A₀ : Matrix (Fin d) (Fin d) ℂ} {A : Fin r → Matrix (Fin d) (Fin d) ℂ}
    {h : BlockLimit r d} (hh : IsSelfAdjoint h)
    (hres : ∀ z : ℂ, z.im ≠ 0 → Matrix.trace (operatorMatrixPencilCauchy A₀ A z) =
      blockLimitResolventTrace h z)
    {f : ℝ → ℝ} (hf : ContDiff ℝ K (fun y => f y - 1)) (hK : m + 1 ≤ K)
    (hfc : HasCompactSupport (fun y => f y - 1))
    (hzero : ∀ x ∈ spectrum ℝ h, f x = 0) :
    guePlaneLimitOrder m A₀ A (fun y => f y - 1) = -1 := by
  rw [guePlaneLimitOrder_eq_re_limitTraceCfcC hm hh hres hf hK hfc,
    limitTraceCfcC_sub_one_eq_neg_one hh hzero]
  norm_num

/-- **The integral of the shifted flat statistic.**  This is the pointwise cancellation
`flatStat (f − 1) + 1 = flatStat f` (`flatStat_sub_one`) integrated against the probability
measure; integrability of the shifted statistic is the only side condition. -/
theorem integral_flatStat_sub_one {r k : ℕ} {F : RatPolyIdx r (k + 1)} {z : ℝ} (N : ℕ)
    {f : ℝ → ℝ}
    (hInt : Integrable (flatStat r k F z N (fun y => f y - 1))
      (commonGaussianMeasure (Fin r))) :
    ∫ x, flatStat r k F z N (fun y => f y - 1) x ∂(commonGaussianMeasure (Fin r)) + 1
      = ∫ x, flatStat r k F z N f x ∂(commonGaussianMeasure (Fin r)) := by
  have hcongr : (fun x => flatStat r k F z N f x)
      = fun x => flatStat r k F z N (fun y => f y - 1) x + 1 := by
    funext x
    exact (flatStat_sub_one k F z N f x).symm
  rw [hcongr, integral_add hInt (integrable_const 1)]
  simp

end Shift

/-! ## 3. `FlatLemmaM` for the cutoff itself, via the shift -/

/-- **`FlatLemmaM` for the cutoff `f` from the honest comparison for `f − 1`.**

The comparison at order `m ≥ 8` is applied to the compactly supported `g = f − 1`, whose limit
statistic is `−1`; the exact identities `∫ τ_N(f) = ∫ τ_N(f − 1) + 1` and `L(f − 1) = −1`
then give `|E τ_N(f)| = |E τ_N(f − 1) + 1| ≤ C/N²`. -/
theorem flatLemmaM_of_weightedStripProven_sub_one {r : ℕ} {k m : ℕ} {F : RatPolyIdx r (k + 1)} {z : ℝ}
    {d' : ℕ} [NeZero d'] (A₀ : Matrix (Fin d') (Fin d') ℂ)
    (A : Fin r → Matrix (Fin d') (Fin d') ℂ) (hA₀ : A₀.IsHermitian)
    (hA : ∀ i, (A i).IsHermitian) (hm : 1 ≤ m) (hm8 : 7 < m)
    {η₀ Kc C_s : ℝ} (hη₀2 : 2 < η₀) (hC_s : 0 ≤ C_s) {f : ℝ → ℝ}
    (hreg : ContDiff ℝ (m + 1) (fun y => f y - 1))
    (hgc : HasCompactSupport (fun y => f y - 1))
    (hstrip : WeightedStripBoundProven A₀ A η₀ Kc C_s)
    (hstat : ∀ N : ℕ,
      ∫ x, flatStat r k F z N (fun y => f y - 1) x ∂(commonGaussianMeasure (Fin r))
        = ∫ y : EuclideanSpace ℝ (GUECoord (Fin r) (N + 1)),
            gueStatisticCfc (N := N + 1) (fun y => f y - 1) A₀ A hA₀ hA y
              ∂(stdGaussian (EuclideanSpace ℝ (GUECoord (Fin r) (N + 1)))))
    (hlim : guePlaneLimitOrder m A₀ A (fun y => f y - 1) = -1)
    (hIntN : ∀ᶠ N : ℕ in atTop, Integrable (fun p : ℝ × ℝ =>
      dbarNumOrder (m + 1) (fun y => f y - 1) (zOf p) *
        Matrix.trace (gueResolventMean (N := N) A₀ A (zOf p))))
    (hIntLim : Integrable (fun p : ℝ × ℝ =>
      dbarNumOrder (m + 1) (fun y => f y - 1) (zOf p) *
        Matrix.trace (operatorMatrixPencilCauchy A₀ A (zOf p))))
    (hInt : ∀ N : ℕ, Integrable (flatStat r k F z N (fun y => f y - 1))
      (commonGaussianMeasure (Fin r))) :
    FlatLemmaM r k F z f (weightedStripConstantProven (fun y => f y - 1) m Kc C_s) := by
  -- the eventual comparison for `g = f − 1` (no vanishing of the limit: it is `−1`)
  have hcomp : ∀ᶠ N : ℕ in atTop,
      |∫ y : EuclideanSpace ℝ (GUECoord (Fin r) (N + 1)),
          gueStatisticCfc (N := N + 1) (fun y => f y - 1) A₀ A hA₀ hA y
            ∂(stdGaussian (EuclideanSpace ℝ (GUECoord (Fin r) (N + 1)))) - (-1)|
        ≤ weightedStripConstantProven (fun y => f y - 1) m Kc C_s /
            ((N + 1 : ℕ) : ℝ) ^ 2 := by
    obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 hstrip
    obtain ⟨M₀, hM₀⟩ := eventually_atTop.1 hIntN
    refine eventually_atTop.2 ⟨max N₀ M₀, fun n hn => ?_⟩
    have hn₀ : N₀ ≤ n + 1 := le_trans (le_max_left N₀ M₀) (by omega)
    have hm₀ : M₀ ≤ n + 1 := le_trans (le_max_right N₀ M₀) (by omega)
    have hfixed := smooth_trace_comparison_of_weighted_strip_proven
      (N := n + 1) A₀ A hA₀ hA (by omega) hm hm8 hreg (K := m + 1) le_rfl hgc hη₀2 hC_s
      (fun z hz hlt => hN₀ (n + 1) hn₀ z hz hlt)
      (hM₀ (n + 1) hm₀) hIntLim
    rwa [hlim] at hfixed
  filter_upwards [hcomp, eventually_ge_atTop (1 : ℕ)] with N hN hN1
  -- convert the comparison for `f − 1` into the bound on `∫ flatStat f`
  rw [← hstat N] at hN
  have hshift := integral_flatStat_sub_one (r := r) (k := k) (F := F) (z := z) N (f := f) (hInt N)
  have hgoal : |∫ x, flatStat r k F z N f x ∂(commonGaussianMeasure (Fin r))|
      = |∫ x, flatStat r k F z N (fun y => f y - 1) x
          ∂(commonGaussianMeasure (Fin r)) - (-1)| := by
    rw [← hshift]
    congr 1
    ring
  rw [hgoal]
  refine hN.trans ?_
  have hC0 : 0 ≤ weightedStripConstantProven (fun y => f y - 1) m Kc C_s :=
    weightedStripConstantProven_nonneg (f := fun y => f y - 1) hC_s
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hsq : (N : ℝ) ^ 2 ≤ ((N : ℝ) + 1) ^ 2 := by nlinarith
  push_cast
  exact div_le_div_of_nonneg_left hC0 (by positivity) hsq

end

end GUEStrongConvergence
