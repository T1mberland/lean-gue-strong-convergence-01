/-
# Limits of normalized GUE trace-word expectations

This file derives honest `Tendsto` statements for normalized trace-word expectations from the
exact finite-`N` formulas of `GUEWordMoments`.

For a fixed word `w` the normalized expectation is a function of `N` (the integral runs over the
`N`-dependent Gaussian space), so a limit statement is a statement about the sequence
`N ↦ ∫ gueNormTrace w ∂stdGaussian`.

Results:

* `tendsto_integral_gueNormTrace_odd`: odd-length words have zero normalized expectation for
  every `N`, hence the limit is `0`.
* `tendsto_integral_gueNormTrace_four`: `E[tr_N (G_i G_j G_k G_l)]` equals the sum of the two
  non-crossing label pairings plus `N⁻²` times the crossing label pairing, hence the limit is the
  non-crossing (Catalan) pairing sum `δ_{ij}δ_{kl} + δ_{il}δ_{jk}`.
* `tendsto_integral_gueNormTrace_four_self`: the special case `E[tr_N (G_i^4)] → 2`.
* `tendsto_integral_gueNormTrace_nil`: the empty word has limit `1`.

The general-length limit requires the general face count (the number of cycles of the pairing
composed with the cyclic shift, together with the genus bound `c ≤ m+1`); that is not claimed
here.
-/
import GUEStrongConvergence.Probability.GUEWordMoments

open MeasureTheory ProbabilityTheory Filter
open scoped RealInnerProductSpace Matrix ENNReal Topology

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

namespace GUEStrongConvergence

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The complex inverse of `N` tends to zero along `N → ∞`. -/
lemma tendsto_inv_natCast_complex :
    Tendsto (fun N : ℕ => ((N : ℂ)⁻¹)) atTop (𝓝 0) := by
  have hreal : Tendsto (fun N : ℕ => ((N : ℝ)⁻¹)) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hcast : Tendsto (fun N : ℕ => Complex.ofReal ((N : ℝ)⁻¹)) atTop
      (𝓝 (Complex.ofReal 0)) :=
    (Complex.continuous_ofReal.tendsto (0 : ℝ)).comp hreal
  have hfun : (fun N : ℕ => Complex.ofReal ((N : ℝ)⁻¹)) = fun N : ℕ => ((N : ℂ)⁻¹) := by
    funext N
    simpa using Complex.ofReal_inv (N : ℝ)
  rw [hfun] at hcast
  simpa using hcast

/-- The normalized expectation of the empty word tends to `1`. -/
theorem tendsto_integral_gueNormTrace_nil :
    Tendsto (fun N : ℕ => ∫ x : EuclideanSpace ℝ (GUECoord ι N),
        gueNormTrace (N := N) [] x
        ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))) atTop (𝓝 1) := by
  have h : (fun N : ℕ => ∫ x : EuclideanSpace ℝ (GUECoord ι N),
      gueNormTrace (N := N) [] x
      ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))) =ᶠ[atTop] fun _ => (1 : ℂ) := by
    filter_upwards [eventually_gt_atTop 0] with N hN
    rw [integral_gueNormTrace_nil]
    simp [Nat.ne_of_gt hN]
  exact tendsto_const_nhds.congr' h.symm

/-- Odd-length normalized expectations vanish for every `N`, hence tend to `0`. -/
theorem tendsto_integral_gueNormTrace_odd (w : List ι) (hodd : Odd w.length) :
    Tendsto (fun N : ℕ => ∫ x : EuclideanSpace ℝ (GUECoord ι N),
        gueNormTrace (N := N) w x
        ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))) atTop (𝓝 0) := by
  have h : (fun N : ℕ => ∫ x : EuclideanSpace ℝ (GUECoord ι N),
      gueNormTrace (N := N) w x
      ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))) = fun _ => (0 : ℂ) := by
    funext N
    exact integral_gueNormTrace_odd_zero w hodd
  rw [h]
  exact tendsto_const_nhds

/-- Limits of the form `a + N⁻² * b`. -/
lemma tendsto_const_add_inv_sq_mul (a b : ℂ) :
    Tendsto (fun N : ℕ => a + ((N : ℂ)⁻¹) ^ 2 * b) atTop (𝓝 a) := by
  have h0 : Tendsto (fun N : ℕ => ((N : ℂ)⁻¹) ^ 2) atTop (𝓝 0) := by
    simpa using tendsto_inv_natCast_complex.pow 2
  have h1 : Tendsto (fun N : ℕ => ((N : ℂ)⁻¹) ^ 2 * b) atTop (𝓝 0) := by
    have := h0.mul_const b
    simpa using this
  have h2 : Tendsto (fun N : ℕ => a + ((N : ℂ)⁻¹) ^ 2 * b) atTop (𝓝 (a + 0)) :=
    tendsto_const_nhds.add h1
  simpa using h2

/-- The normalized fourth moment tends to the non-crossing (Catalan) pairing sum. -/
theorem tendsto_integral_gueNormTrace_four (i j k l : ι) :
    Tendsto (fun N : ℕ => ∫ x : EuclideanSpace ℝ (GUECoord ι N),
        gueNormTrace (N := N) [i, j, k, l] x
        ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))) atTop
      (𝓝 ((if i = j then (1 : ℂ) else 0) * (if k = l then (1 : ℂ) else 0) +
        (if i = l then (1 : ℂ) else 0) * (if j = k then (1 : ℂ) else 0))) := by
  have h : (fun N : ℕ => ∫ x : EuclideanSpace ℝ (GUECoord ι N),
      gueNormTrace (N := N) [i, j, k, l] x
      ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))) =ᶠ[atTop]
      fun N => ((if i = j then (1 : ℂ) else 0) * (if k = l then (1 : ℂ) else 0) +
        (if i = l then (1 : ℂ) else 0) * (if j = k then (1 : ℂ) else 0)) +
        ((N : ℂ)⁻¹) ^ 2 *
          ((if i = k then (1 : ℂ) else 0) * (if j = l then (1 : ℂ) else 0)) := by
    filter_upwards [eventually_gt_atTop 0] with N hN
    exact integral_gueNormTrace_four (N := N) i j k l hN
  have hlim := tendsto_const_add_inv_sq_mul
    (a := ((if i = j then (1 : ℂ) else 0) * (if k = l then (1 : ℂ) else 0) +
      (if i = l then (1 : ℂ) else 0) * (if j = k then (1 : ℂ) else 0)))
    (b := ((if i = k then (1 : ℂ) else 0) * (if j = l then (1 : ℂ) else 0)))
  exact Tendsto.congr' h.symm hlim

/-- The fourth normalized moment of a single GUE matrix tends to the Catalan number `2`. -/
theorem tendsto_integral_gueNormTrace_four_self (i : ι) :
    Tendsto (fun N : ℕ => ∫ x : EuclideanSpace ℝ (GUECoord ι N),
        gueNormTrace (N := N) [i, i, i, i] x
        ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))) atTop (𝓝 2) := by
  have h : (fun N : ℕ => ∫ x : EuclideanSpace ℝ (GUECoord ι N),
      gueNormTrace (N := N) [i, i, i, i] x
      ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))) =ᶠ[atTop]
      fun N => 2 + ((N : ℂ)⁻¹) ^ 2 := by
    filter_upwards [eventually_gt_atTop 0] with N hN
    exact integral_gueNormTrace_four_self (N := N) i hN
  have hlim : Tendsto (fun N : ℕ => (2 : ℂ) + ((N : ℂ)⁻¹) ^ 2 * 1) atTop (𝓝 2) :=
    tendsto_const_add_inv_sq_mul 2 1
  have hfun : (fun N : ℕ => (2 : ℂ) + ((N : ℂ)⁻¹) ^ 2 * 1) = fun N : ℕ => 2 + ((N : ℂ)⁻¹) ^ 2 := by
    funext N; ring
  rw [hfun] at hlim
  exact Tendsto.congr' h.symm hlim


/-! ### Wick factorization for a label occurring in two adjacent entries

If a list of GUE entries has the shape `e :: f :: chain` where `e` and `f` carry the same label `i`
and no entry of `chain` carries label `i`, then every nonzero Wick pairing pairs `e` with `f`, so
the Wick value factorizes as the covariance of `e` and `f` times the Wick value of `chain`.  This
is the key structural step for peeling a doubled matrix out of a trace word. -/

/-- The covariance of entries with different labels vanishes. -/
lemma gueCov_eq_zero_of_label_ne {N : ℕ} {e f : GUEEntry ι N} (h : e.1 ≠ f.1) :
    gueCov e f = 0 := by
  rw [gueCov]
  simp [h]

/-- **Doubled-label factorization**: for `e`, `f` with label `i` and a chain whose entries all
have labels different from `i`, the Wick value of `e :: f :: chain` is the covariance of `e` and
`f` times the Wick value of the chain. -/
lemma gueWick_cons_cons_of_label_ne {N : ℕ} {i : ι} {e f : GUEEntry ι N}
    {chain : List (GUEEntry ι N)} (he : e.1 = i) (hf : f.1 = i)
    (hchain : ∀ j : Fin chain.length, (chain.get j).1 ≠ i) :
    gueWick (e :: f :: chain) = gueCov e f * gueWick chain := by
  rw [gueWick_cons]
  simp only [List.length_cons]
  rw [Fin.sum_univ_succ]
  have hget0 : (f :: chain).get (0 : Fin (chain.length + 1)) = f := by simp
  have herase0 : (f :: chain).eraseIdx (0 : Fin (chain.length + 1)) = chain := by simp
  rw [hget0, herase0]
  rw [Finset.sum_eq_zero (fun j _ => by
    have hjj : (f :: chain).get j.succ = chain.get j := by simp
    have hlab : e.1 ≠ ((f :: chain).get j.succ).1 := by
      rw [hjj, he]
      exact fun hh => hchain j hh.symm
    rw [gueCov_eq_zero_of_label_ne (N := N) hlab, zero_mul])]
  simp

end

end GUEStrongConvergence
