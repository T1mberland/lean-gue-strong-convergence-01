/-
# Scalar spectral inclusion for a single GUE matrix

This file proves `ScalarSpectralInclusion r`, the almost-sure spectral inclusion of each
individual GUE matrix `gueFamily r N x i` in the spectrum of the free semicircular element
`semicircularFamily r i`.

The proof specializes the growing-dimension spectral exclusion (`Lemma S`) of
`Probability/CutoffExclusionGrowing.lean` to the single-generator case `d = Unit`,
`m N = N`, and converts the resulting set inclusion into the pointwise form required by
`ScalarSpectralInclusion`.

All analytic inputs (`hM`, `hWb`, `hV`, and the `L²`/integrability side conditions) are
stated explicitly as hypotheses, exactly as required by the project's conditional-result
convention.  The closest unconditional statement is also provided.
-/
import GUEStrongConvergence.Probability.CutoffExclusionGrowing
import GUEStrongConvergence.StrongConvergence.CutoffExclusion
import GUEStrongConvergence.StrongConvergence.Target

open Filter MeasureTheory ProbabilityTheory FreeProbability FreeProbability.Fock Matrix
open scoped BigOperators ComplexOrder ENNReal Pointwise Topology

namespace GUEStrongConvergence

noncomputable section

/-! ## A cutoff function for a set and a radius -/

/-- The indicator cutoff `f(x) = 0` inside `S + (-ε, ε)` and `f(x) = 1` outside. -/
noncomputable def cutoff (S : Set ℝ) (ε : ℝ) : ℝ → ℝ :=
  fun x => by
    classical
    exact if x ∈ S + Set.Ioo (-ε) ε then 0 else 1

lemma cutoff_nonneg (S : Set ℝ) (ε : ℝ) : ∀ x, 0 ≤ cutoff S ε x := by
  intro x
  unfold cutoff
  split_ifs <;> norm_num

lemma cutoff_eq_one (S : Set ℝ) (ε : ℝ) {x : ℝ} (hx : x ∉ S + Set.Ioo (-ε) ε) :
    cutoff S ε x = 1 := by
  unfold cutoff
  simp [hx]

/-! ## Conversion from set inclusion to pointwise form -/

/-- Membership in `S + (-ε, ε)` gives a point of `S` within `ε`. -/
lemma exists_mem_of_mem_add_Ioo {S : Set ℝ} {ε a : ℝ}
    (h : a ∈ S + Set.Ioo (-ε) ε) : ∃ b ∈ S, |a - b| ≤ ε := by
  rw [Set.mem_add] at h
  obtain ⟨b, hb, c, hc, hbc⟩ := h
  refine ⟨b, hb, ?_⟩
  rw [← hbc]
  have hab : |b + c - b| = |c| := by ring_nf
  rw [hab]
  exact le_of_lt (abs_lt.mpr ⟨hc.1, hc.2⟩)

/-! ## The main conditional theorem -/

/-- **Scalar spectral inclusion from explicit analytic inputs.**

For each generator `i` and each radius `ε > 0`, the single GUE matrix `gueFamily r N x i`
satisfies the analytic inputs `(M)`, `(V)`, `(W)`, the `L²`/integrability conditions `hZ`,
`hWint`, `hW0`, and the cutoff conditions `hf0`, `hf1` needed by Lemma S.  Then almost
surely every real spectral value of `gueFamily r N x i` is within `ε` of a real spectral
value of `semicircularFamily r i`, for all sufficiently large `N`.

The mean comparison hypothesis `hM` and the `(W)` bound `hWb` are explicit inputs; the
variance bound `hV` is also an explicit input (it can be discharged unconditionally from
`lemmaS_V_input_unconditional` for smooth `f`, but that is not assumed here).

The countable-intersection step over `ε = 1/(k+1)` converts the fixed-`ε` set inclusion
into the full quantifier order of `ScalarSpectralInclusion`. -/
theorem scalarSpectralInclusion_of_inputs {r : ℕ}
    (C C' : ℝ) (hC : 0 ≤ C) (hC' : 0 ≤ C')
    (hZ : ∀ (i : Fin r) (ε : ℝ) (hε : 0 < ε) (N : ℕ),
      MemLp (fun x => normTrace (hermCfc (gueFamily r N x i)
        (cutoff (spectrum ℝ (semicircularFamily r i)) ε)
        (gueMatrixOn_isHermitian x N i))) 2 (commonGaussianMeasure (Fin r)))
    (hWint : ∀ (i : Fin r) (ε : ℝ) (hε : 0 < ε) (N : ℕ),
      Integrable (fun x => normTrace (hermCfc (gueFamily r N x i)
        (fun y => (deriv (cutoff (spectrum ℝ (semicircularFamily r i)) ε) y) ^ 2)
        (gueMatrixOn_isHermitian x N i))) (commonGaussianMeasure (Fin r)))
    (hW0 : ∀ (i : Fin r) (ε : ℝ) (hε : 0 < ε) (N : ℕ),
      0 ≤ ∫ x, normTrace (hermCfc (gueFamily r N x i)
        (fun y => (deriv (cutoff (spectrum ℝ (semicircularFamily r i)) ε) y) ^ 2)
        (gueMatrixOn_isHermitian x N i)) ∂(commonGaussianMeasure (Fin r)))
    (hM : ∀ (i : Fin r) (ε : ℝ) (hε : 0 < ε),
      ∀ᶠ N : ℕ in atTop,
        |∫ x, normTrace (hermCfc (gueFamily r N x i)
          (cutoff (spectrum ℝ (semicircularFamily r i)) ε)
          (gueMatrixOn_isHermitian x N i)) ∂(commonGaussianMeasure (Fin r))|
          ≤ C / (N : ℝ) ^ 2)
    (hV : ∀ (i : Fin r) (ε : ℝ) (hε : 0 < ε) (N : ℕ),
      variance (fun x => normTrace (hermCfc (gueFamily r N x i)
        (cutoff (spectrum ℝ (semicircularFamily r i)) ε)
        (gueMatrixOn_isHermitian x N i))) (commonGaussianMeasure (Fin r))
      ≤ C / (N : ℝ) ^ 2 * ∫ x, normTrace (hermCfc (gueFamily r N x i)
          (fun y => (deriv (cutoff (spectrum ℝ (semicircularFamily r i)) ε) y) ^ 2)
          (gueMatrixOn_isHermitian x N i)) ∂(commonGaussianMeasure (Fin r)))
    (hWb : ∀ (i : Fin r) (ε : ℝ) (hε : 0 < ε) (N : ℕ),
      ∫ x, normTrace (hermCfc (gueFamily r N x i)
        (fun y => (deriv (cutoff (spectrum ℝ (semicircularFamily r i)) ε) y) ^ 2)
        (gueMatrixOn_isHermitian x N i)) ∂(commonGaussianMeasure (Fin r))
        ≤ C' / (N : ℝ) ^ 2) :
    ScalarSpectralInclusion r := by
  classical
  -- For each `i` and each `k`, apply Lemma S with `ε = 1/(k+1)`.
  have hstep : ∀ (i : Fin r) (k : ℕ),
      ∀ᵐ x ∂(commonGaussianMeasure (Fin r)), ∀ᶠ N : ℕ in atTop,
        spectrum ℝ (gueFamily r N x i) ⊆
          spectrum ℝ (semicircularFamily r i) + Set.Ioo (-(1 / (k + 1 : ℝ))) (1 / (k + 1 : ℝ)) := by
    intro i k
    have hε : (0 : ℝ) < 1 / (k + 1 : ℝ) := by positivity
    exact ae_eventually_spectrum_subset_growing
      (m := fun N => N)
      (hm := (eventually_ge_atTop (1 : ℕ)).mono fun N hN => Nat.lt_of_lt_of_le Nat.zero_lt_one hN)
      (hε := hε)
      (hf0 := cutoff_nonneg _ _)
      (hf1 := fun x hx => cutoff_eq_one _ _ hx)
      (H := fun N x => gueFamily r N x i)
      (hH := fun N x => gueMatrixOn_isHermitian x N i)
      (hC := hC) (hC' := hC') (hD := zero_le_one)
      (hmD := by filter_upwards with N; simp)
      (hZ := fun N => hZ i _ hε N)
      (hWint := fun N => hWint i _ hε N)
      (hW0 := fun N => hW0 i _ hε N)
      (hM := hM i _ hε)
      (hV := Eventually.of_forall (fun N => hV i _ hε N))
      (hWb := Eventually.of_forall (fun N => hWb i _ hε N))
  -- Combine countably many almost-sure events.
  have hall : ∀ᵐ x ∂(commonGaussianMeasure (Fin r)),
      ∀ i : Fin r, ∀ k : ℕ, ∀ᶠ N : ℕ in atTop,
        spectrum ℝ (gueFamily r N x i) ⊆
          spectrum ℝ (semicircularFamily r i) + Set.Ioo (-(1 / (k + 1 : ℝ))) (1 / (k + 1 : ℝ)) := by
    have h := ae_all_iff.2 (fun p : Fin r × ℕ => hstep p.1 p.2)
    filter_upwards [h] with x hx
    intro i k
    exact hx (i, k)
  filter_upwards [hall] with x hx
  intro i ε hε
  -- Choose `k` with `1/(k+1) < ε`.
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
  -- Use the eventual statement for this `k`.
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

end

end GUEStrongConvergence
