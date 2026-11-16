/-
# A smooth cutoff separating a compact set from the complement of its `ε`-neighbourhood

For a compact set `S : Set ℝ` and `ε > 0` we construct a `C¹` function `f : ℝ → ℝ` with
`0 ≤ f ≤ 1`, `f = 0` on `S`, `f = 1` outside `S + Set.Ioo (-ε) ε`, `deriv f = 0` on `S`, and
`(deriv f) ^ 2` compactly supported.

The construction is the standard finite product of bump functions.  Choose, for each `x ∈ S`, the
`ContDiffBump` `φ x` with `rIn = ε / 4` and `rOut = ε / 2`.  Compactness of `S` gives a finite
`t : Finset S` such that the open balls `ball x (ε / 4)` (`x ∈ t`) cover `S`, and we set
`f = ∏ x ∈ t, (1 - φ x)`.  Each factor vanishes on `ball x (ε / 4)`, so `f` vanishes on the open
neighbourhood `⋃ x ∈ t, ball x (ε / 4)` of `S`; each `φ x` is supported in
`closedBall x (ε / 2) ⊆ S + Set.Ioo (-ε) ε`, so `f = 1` outside `S + Set.Ioo (-ε) ε`.  The
derivative `deriv f` vanishes outside the finite union of the compact sets `tsupport (φ x)`,
hence `(deriv f) ^ 2` is compactly supported.

## Main result

* `GUEStrongConvergence.exists_contDiff_cutoff`
-/

import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Order.Filter.Finite

open Set Metric
open scoped Pointwise Topology

noncomputable section

namespace GUEStrongConvergence

variable {S : Set ℝ} {ε : ℝ}

/-- For a compact set `S : Set ℝ` and `0 < ε`, there is a `C¹` cutoff `f : ℝ → ℝ` with
`0 ≤ f ≤ 1`, `f = 0` on `S`, `f = 1` outside `S + Set.Ioo (-ε) ε`, `deriv f = 0` on `S`, and
`(deriv f) ^ 2` compactly supported. -/
theorem exists_contDiff_cutoff (hS : IsCompact S) (hε : 0 < ε) :
    ∃ f : ℝ → ℝ,
      ContDiff ℝ 1 f ∧
      (∀ x, 0 ≤ f x) ∧
      (∀ x ∈ S, f x = 0) ∧
      (∀ x, x ∉ S + Set.Ioo (-ε) ε → f x = 1) ∧
      (∀ x, f x ≤ 1) ∧
      (∀ x ∈ S, deriv f x = 0) ∧
      HasCompactSupport (fun x => (deriv f x) ^ 2) := by
  classical
  -- Bump functions with `rIn = ε / 4` and `rOut = ε / 2`, centered at points of `S`.
  let φ : (i : S) → ContDiffBump (i : ℝ) :=
    fun _ => { rIn := ε / 4, rOut := ε / 2, rIn_pos := by linarith
               rIn_lt_rOut := by linarith }
  -- The open balls on which the corresponding bump equals one.
  have hcover : S ⊆ ⋃ i : S, Metric.ball (i : ℝ) (ε / 4) := by
    intro x hx
    refine Set.mem_iUnion.2 ⟨⟨x, hx⟩, ?_⟩
    rw [Metric.mem_ball]
    simpa using (show (0 : ℝ) < ε / 4 by linarith)
  obtain ⟨t, ht⟩ := hS.elim_finite_subcover (fun i : S => Metric.ball (i : ℝ) (ε / 4))
    (fun _ => Metric.isOpen_ball) hcover
  -- The cutoff function: a finite product of `1 - φ i`.
  let f : ℝ → ℝ := fun x => ∏ i ∈ t, (1 - (φ i : ℝ → ℝ) x)
  have hf_def : ∀ x, f x = ∏ i ∈ t, (1 - (φ i : ℝ → ℝ) x) := fun _ => rfl
  -- Each bump is supported in `S + Set.Ioo (-ε) ε`.
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
  -- `f` vanishes on the open cover of `S`.
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
  -- `f` is one outside `S + Set.Ioo (-ε) ε`.
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
  have hf_contDiff : ContDiff ℝ 1 f := by
    have hfun : f = fun x => ∏ i ∈ t, (1 - (φ i : ℝ → ℝ) x) := funext hf_def
    rw [hfun]
    exact contDiff_prod fun i _ =>
      contDiff_const.sub (ContDiffBump.contDiff (f := φ i))
  -- `f` is eventually zero at every point of `S`.
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
  -- The support of `deriv f` is contained in a finite union of compact sets.
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

/-- **`C²` version of the cutoff.**  The construction of `exists_contDiff_cutoff` gives a
smooth (`C^∞`) cutoff, so it is in particular `C²`; the smooth Cauchy–Pompeiu representation
of `Probability/LemmaMSmooth.lean` requires the `C²` regularity.  All the other properties
(nonnegativity, vanishing on `S`, being `1` off the `ε`-neighbourhood, vanishing derivative on
`S`, compactly supported squared derivative) are unchanged. -/
theorem exists_contDiff_two_cutoff (hS : IsCompact S) (hε : 0 < ε) :
    ∃ f : ℝ → ℝ,
      ContDiff ℝ 2 f ∧
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
  have hf_contDiff : ContDiff ℝ 2 f := by
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

end GUEStrongConvergence

