/-
# Finite-product Efron--Stein / variance tensorization

For a probability measure `μ` on a measurable space `α` and `F : (Fin n → α) → ℝ` in
`L²(Measure.pi (fun _ => μ))`, this module proves the finite-product Efron--Stein inequality

`Var_{μ^⊗n}(F) ≤ ∑ p, ∫ x, Var_μ (fun t => F (Function.update x p t)) dμ^⊗n(x)`.

The proof is an induction on `n`.  The successor step splits `Fin (n+1)` into the first
coordinate and its tail using `MeasurableEquiv.piFinSuccAbove`, applies the verified two-factor
tensorization theorem `variance_prod_le_integral_variance_fst_add_integral_variance_snd`, and
uses the tail induction hypothesis integrated over the new coordinate.

The supporting top-level lemmas show that replacing a coordinate is measure preserving
(`measurePreserving_piReplace`), that coordinate variances are integrable from `MemLp F 2`
(`integrable_coordVar`), and transport the coordinate-variance integrals across the
first-coordinate/tail splitting (`integral_coordVar_zero_eq`, `integral_coordVar_succ_eq`).
No derivative assumptions and no coordinate tensorization inequality are assumed.
-/
import GUEStrongConvergence.Probability.GaussianTensorization
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Data.Fin.Tuple.Basic
open MeasureTheory ProbabilityTheory Filter
open scoped ProbabilityTheory ENNReal NNReal Topology

namespace GUEStrongConvergence

noncomputable section

variable {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]

/-- The `n`-fold product measure of a fixed probability measure `μ`. -/
abbrev piFinMeasure (n : ℕ) : Measure (Fin n → α) :=
  Measure.pi (fun _ : Fin n => μ)

/-- The variance of the `p`-th coordinate section of `F`, as a function of the other
coordinates.  The full tuple `x` is used as the base point; `Function.update x p t` replaces
the `p`-th coordinate. -/
def coordVar {n : ℕ} (F : (Fin n → α) → ℝ) (p : Fin n) (x : Fin n → α) : ℝ :=
  variance (fun t => F (Function.update x p t)) μ

theorem variance_pi_fin_zero (F : (Fin 0 → α) → ℝ) :
    variance F (piFinMeasure (α := α) μ 0) = 0 := by
  have : Subsingleton (Fin 0 → α) := inferInstance
  have hconst : F = fun _ => F (fun i => i.elim0) := by
    funext x
    congr 1
    exact Subsingleton.elim x _
  rw [hconst]
  simp [variance, evariance]

/-- The measurable equivalence splitting `Fin (n+1)` into coordinate `0` and its tail. -/
def piFinZeroEquiv (n : ℕ) : (Fin (n + 1) → α) ≃ᵐ α × (Fin n → α) :=
  MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => α) 0

theorem piFinZeroEquiv_symm_cons {n : ℕ} (a : α) (y : Fin n → α) :
    (piFinZeroEquiv (α := α) n).symm (a, y)
      = Fin.cons (α := fun _ : Fin (n + 1) => α) a y := by
  ext i
  simp [piFinZeroEquiv, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
    Fin.cons]

theorem update_zero_piFinZeroEquiv {n : ℕ} (a t : α) (y : Fin n → α) :
    Function.update ((piFinZeroEquiv (α := α) n).symm (a, y)) 0 t
      = (piFinZeroEquiv (α := α) n).symm (t, y) := by
  rw [piFinZeroEquiv_symm_cons a y, piFinZeroEquiv_symm_cons t y]
  ext i
  rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩
  · simp [Fin.cons, Function.update]
  · simp [Fin.cons, Function.update]

theorem update_succ_piFinZeroEquiv {n : ℕ} (a t : α) (y : Fin n → α) (j : Fin n) :
    Function.update ((piFinZeroEquiv (α := α) n).symm (a, y)) (Fin.succ j) t
      = (piFinZeroEquiv (α := α) n).symm (a, Function.update y j t) := by
  rw [piFinZeroEquiv_symm_cons a y, piFinZeroEquiv_symm_cons a (Function.update y j t)]
  ext i
  rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨k, rfl⟩
  · have h0 : (0 : Fin (n + 1)) ≠ Fin.succ j := (Fin.succ_ne_zero j).symm
    simp [Fin.cons, Function.update, h0]
  · by_cases hk : k = j
    · subst hk
      simp [Fin.cons, Function.update]
    · simp [Fin.cons, Function.update, hk]




/-! ## Replacement maps and coordinate-variance integrability -/

/-- Delete the `p`-th coordinate of a tuple. -/
def piDrop {n : ℕ} (p : Fin (n + 1)) (x : Fin (n + 1) → α) : Fin n → α :=
  fun j => x (p.succAbove j)

/-- Replace the `p`-th coordinate of a tuple by a fresh value. -/
def piReplace {n : ℕ} (p : Fin (n + 1)) (z : (Fin (n + 1) → α) × α) : Fin (n + 1) → α :=
  Function.update z.1 p z.2

theorem piFinSuccAbove_snd {n : ℕ} (p : Fin (n + 1)) (x : Fin (n + 1) → α) :
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => α) p x).2 = piDrop p x := by
  ext j
  simp only [MeasurableEquiv.piFinSuccAbove_apply, Fin.insertNthEquiv, piDrop]
  exact Fin.removeNth_apply p x j

theorem piReplace_eq_symm {n : ℕ} (p : Fin (n + 1)) (x : Fin (n + 1) → α) (t : α) :
    piReplace p (x, t)
      = (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => α) p).symm
          (t, piDrop p x) := by
  have h : (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => α) p)
        (piReplace p (x, t)) = (t, piDrop p x) := by
    ext
    · simp [piReplace, Function.update]
    · simp [piReplace, piDrop, MeasurableEquiv.piFinSuccAbove_apply, Fin.insertNthEquiv,
        Function.update]
      rfl
  rw [← h]
  exact ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => α) p).symm_apply_apply _).symm

theorem measurePreserving_piDrop {n : ℕ} (p : Fin (n + 1)) :
    MeasurePreserving (piDrop (α := α) p) (piFinMeasure (α := α) μ (n + 1))
      (piFinMeasure (α := α) μ n) := by
  have hsplit := measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => μ) p
  have hsnd : MeasurePreserving Prod.snd
      (μ.prod (Measure.pi (fun _ : Fin n => μ))) (Measure.pi (fun _ : Fin n => μ)) :=
    measurePreserving_snd
  have hcomp := hsnd.comp hsplit
  change MeasurePreserving (fun x : Fin (n + 1) → α => p.removeNth x)
    (piFinMeasure (α := α) μ (n + 1)) (piFinMeasure (α := α) μ n)
  exact hcomp

theorem measurePreserving_piReplace {n : ℕ} (p : Fin (n + 1)) :
    MeasurePreserving (piReplace (α := α) p)
      ((piFinMeasure (α := α) μ (n + 1)).prod μ) (piFinMeasure (α := α) μ (n + 1)) := by
  have hsplit := measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => μ) p
  have hdrop := measurePreserving_piDrop (α := α) (μ := μ) p
  have hprod : MeasurePreserving
      (fun z : (Fin (n + 1) → α) × α => (piDrop p z.1, z.2))
      ((piFinMeasure (α := α) μ (n + 1)).prod μ)
      ((piFinMeasure (α := α) μ n).prod μ) :=
    hdrop.prod (MeasurePreserving.id μ)
  have hswap : MeasurePreserving Prod.swap
      ((piFinMeasure (α := α) μ n).prod μ)
      (μ.prod (piFinMeasure (α := α) μ n)) := Measure.measurePreserving_swap
  have hcomp1 : MeasurePreserving
      (fun z : (Fin (n + 1) → α) × α => (z.2, piDrop p z.1))
      ((piFinMeasure (α := α) μ (n + 1)).prod μ)
      (μ.prod (piFinMeasure (α := α) μ n)) :=
    hswap.comp hprod
  have hcomp2 : MeasurePreserving
      (fun z : (Fin (n + 1) → α) × α =>
        (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => α) p).symm
          (z.2, piDrop p z.1))
      ((piFinMeasure (α := α) μ (n + 1)).prod μ)
      (piFinMeasure (α := α) μ (n + 1)) :=
    hsplit.symm.comp hcomp1
  convert hcomp2 using 1
  funext z
  exact piReplace_eq_symm p z.1 z.2

/-- The `p`-th replacement section of `F`, as a function of `(x,t)`. -/
def replaceSection {n : ℕ} (F : (Fin (n + 1) → α) → ℝ) (p : Fin (n + 1)) :
    (Fin (n + 1) → α) × α → ℝ :=
  fun z => F (piReplace p z)

theorem memLp_replaceSection {n : ℕ} {F : (Fin (n + 1) → α) → ℝ}
    (hF : MemLp F 2 (piFinMeasure (α := α) μ (n + 1))) (p : Fin (n + 1)) :
    MemLp (replaceSection (α := α) F p) 2
      ((piFinMeasure (α := α) μ (n + 1)).prod μ) :=
  hF.comp_measurePreserving (measurePreserving_piReplace (α := α) (μ := μ) p)

/-- **Integrability of the coordinate variance** from `MemLp F 2`.  This is the missing
integrability side condition for the finite-product Efron--Stein induction. -/
theorem integrable_coordVar {n : ℕ} {F : (Fin (n + 1) → α) → ℝ}
    (hF : MemLp F 2 (piFinMeasure (α := α) μ (n + 1))) (p : Fin (n + 1)) :
    Integrable (coordVar (μ := μ) F p) (piFinMeasure (α := α) μ (n + 1)) := by
  have h := integrable_variance_sectionSnd (μ := piFinMeasure (α := α) μ (n + 1))
    (ν := μ) (memLp_replaceSection (α := α) (μ := μ) hF p)
  change Integrable (fun x => variance (sectionSnd (replaceSection (α := α) F p) x) μ)
    (piFinMeasure (α := α) μ (n + 1))
  exact h


theorem measurePreserving_piFinZeroEquiv (n : ℕ) :
    MeasurePreserving (piFinZeroEquiv (α := α) n)
      (piFinMeasure (α := α) μ (n + 1)) (μ.prod (piFinMeasure (α := α) μ n)) :=
  measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => μ) 0

/-- The coordinate variance in the first factor after splitting off coordinate `0`. -/
def zeroFstVar {n : ℕ} (F : (Fin (n + 1) → α) → ℝ) (y : Fin n → α) : ℝ :=
  variance (fun t => F ((piFinZeroEquiv (α := α) n).symm (t, y))) μ

/-- Transport of the `0`-th coordinate-variance integral to the first factor of the split
product. -/
theorem integral_coordVar_zero_eq {n : ℕ} {F : (Fin (n + 1) → α) → ℝ} :
    (∫ x, coordVar (μ := μ) F 0 x ∂(piFinMeasure (α := α) μ (n + 1)))
      = ∫ y, zeroFstVar (α := α) (μ := μ) F y ∂(piFinMeasure (α := α) μ n) := by
  have hmp := measurePreserving_piFinZeroEquiv (α := α) (μ := μ) n
  have h1 : (∫ x, coordVar (μ := μ) F 0 x ∂(piFinMeasure (α := α) μ (n + 1)))
      = ∫ z : α × (Fin n → α),
          variance (fun t => F (Function.update ((piFinZeroEquiv (α := α) n).symm z) 0 t)) μ
          ∂(μ.prod (piFinMeasure (α := α) μ n)) := by
    refine (hmp.symm.integral_comp'
      (fun x => variance (fun t => F (Function.update x 0 t)) μ)).symm
  have h2 : (∫ z : α × (Fin n → α),
        variance (fun t => F (Function.update ((piFinZeroEquiv (α := α) n).symm z) 0 t)) μ
        ∂(μ.prod (piFinMeasure (α := α) μ n)))
      = ∫ z : α × (Fin n → α), zeroFstVar (α := α) (μ := μ) F z.2
          ∂(μ.prod (piFinMeasure (α := α) μ n)) := by
    refine integral_congr_ae (ae_of_all _ fun z => ?_)
    obtain ⟨a, y⟩ := z
    change variance (fun t => F (Function.update ((piFinZeroEquiv (α := α) n).symm (a, y)) 0 t)) μ
      = zeroFstVar (α := α) (μ := μ) F y
    simp only [zeroFstVar, update_zero_piFinZeroEquiv]
  have h3 : (∫ z : α × (Fin n → α), zeroFstVar (α := α) (μ := μ) F z.2
        ∂(μ.prod (piFinMeasure (α := α) μ n)))
      = ∫ y, zeroFstVar (α := α) (μ := μ) F y ∂(piFinMeasure (α := α) μ n) := by
    rw [integral_fun_snd]
    simp
  exact h1.trans (h2.trans h3)


/-- The coordinate variance in the second factor after splitting off coordinate `0`, for one of
the tail coordinates. -/
def succFstVar {n : ℕ} (F : (Fin (n + 1) → α) → ℝ) (j : Fin n)
    (z : α × (Fin n → α)) : ℝ :=
  variance (fun t => F ((piFinZeroEquiv (α := α) n).symm (z.1, Function.update z.2 j t))) μ

theorem integrable_succFstVar {n : ℕ} {F : (Fin (n + 1) → α) → ℝ}
    (hF : MemLp F 2 (piFinMeasure (α := α) μ (n + 1))) (j : Fin n) :
    Integrable (succFstVar (α := α) (μ := μ) F j)
      (μ.prod (piFinMeasure (α := α) μ n)) := by
  have hmp := measurePreserving_piFinZeroEquiv (α := α) (μ := μ) n
  have hint : Integrable (fun z : α × (Fin n → α) =>
        coordVar (μ := μ) F (Fin.succ j) ((piFinZeroEquiv (α := α) n).symm z))
      (μ.prod (piFinMeasure (α := α) μ n)) :=
    hmp.symm.integrable_comp_of_integrable
      (integrable_coordVar (α := α) (μ := μ) hF (Fin.succ j))
  refine hint.congr (ae_of_all _ fun z => ?_)
  obtain ⟨a, y⟩ := z
  change coordVar (μ := μ) F (Fin.succ j) ((piFinZeroEquiv (α := α) n).symm (a, y))
    = succFstVar (α := α) (μ := μ) F j (a, y)
  simp only [coordVar, succFstVar, update_succ_piFinZeroEquiv]

/-- Transport of a tail-coordinate variance integral to the split product. -/
theorem integral_coordVar_succ_eq {n : ℕ} {F : (Fin (n + 1) → α) → ℝ}
    (hF : MemLp F 2 (piFinMeasure (α := α) μ (n + 1))) (j : Fin n) :
    (∫ x, coordVar (μ := μ) F (Fin.succ j) x ∂(piFinMeasure (α := α) μ (n + 1)))
      = ∫ a, (∫ y, variance (fun t =>
            F ((piFinZeroEquiv (α := α) n).symm (a, Function.update y j t))) μ
          ∂(piFinMeasure (α := α) μ n)) ∂μ := by
  have hmp := measurePreserving_piFinZeroEquiv (α := α) (μ := μ) n
  have h1 : (∫ x, coordVar (μ := μ) F (Fin.succ j) x
        ∂(piFinMeasure (α := α) μ (n + 1)))
      = ∫ z : α × (Fin n → α),
          variance (fun t => F (Function.update ((piFinZeroEquiv (α := α) n).symm z)
            (Fin.succ j) t)) μ ∂(μ.prod (piFinMeasure (α := α) μ n)) := by
    exact (hmp.symm.integral_comp'
      (fun x => variance (fun t => F (Function.update x (Fin.succ j) t)) μ)).symm
  have h2 : (∫ z : α × (Fin n → α),
        variance (fun t => F (Function.update ((piFinZeroEquiv (α := α) n).symm z)
          (Fin.succ j) t)) μ ∂(μ.prod (piFinMeasure (α := α) μ n)))
      = ∫ z : α × (Fin n → α), succFstVar (α := α) (μ := μ) F j z
          ∂(μ.prod (piFinMeasure (α := α) μ n)) := by
    refine integral_congr_ae (ae_of_all _ fun z => ?_)
    obtain ⟨a, y⟩ := z
    change variance (fun t => F (Function.update ((piFinZeroEquiv (α := α) n).symm (a, y))
      (Fin.succ j) t)) μ = succFstVar (α := α) (μ := μ) F j (a, y)
    simp only [succFstVar, update_succ_piFinZeroEquiv]
  have h3 : (∫ z : α × (Fin n → α), succFstVar (α := α) (μ := μ) F j z
        ∂(μ.prod (piFinMeasure (α := α) μ n)))
      = ∫ a, (∫ y, succFstVar (α := α) (μ := μ) F j (a, y)
          ∂(piFinMeasure (α := α) μ n)) ∂μ :=
    integral_prod (succFstVar (α := α) (μ := μ) F j) (integrable_succFstVar (α := α) (μ := μ) hF j)
  exact h1.trans (h2.trans h3)


/-- **Finite-product Efron--Stein inequality** for `Fin n` and a fixed probability measure `μ`:
`Var_{μ^⊗n}(F) ≤ ∑ p, ∫ x, Var_μ (fun t => F (Function.update x p t))`.

This is proved by induction on `n`, using the verified two-factor tensorization theorem and the
top-level coordinate transport/integrability lemmas above.  No coordinate tensorization
inequality and no extra integrability hypothesis is assumed. -/
theorem variance_pi_fin_le_sum_coordVar (n : ℕ) (F : (Fin n → α) → ℝ)
    (hF : MemLp F 2 (piFinMeasure (α := α) μ n)) :
    variance F (piFinMeasure (α := α) μ n)
      ≤ ∑ p : Fin n,
          ∫ x, coordVar (μ := μ) F p x ∂(piFinMeasure (α := α) μ n) := by
  induction n with
  | zero =>
      rw [variance_pi_fin_zero]
      simp
  | succ n ih =>
      let γs : Measure (Fin (n + 1) → α) := piFinMeasure (α := α) μ (n + 1)
      let γn : Measure (Fin n → α) := piFinMeasure (α := α) μ n
      let e := piFinZeroEquiv (α := α) n
      have hmp : MeasurePreserving e γs (μ.prod γn) :=
        measurePreserving_piFinZeroEquiv (α := α) (μ := μ) n
      let G : α × (Fin n → α) → ℝ := fun z => F (e.symm z)
      have hG : MemLp G 2 (μ.prod γn) := hF.comp_measurePreserving hmp.symm
      have hvar : variance G (μ.prod γn) = variance F γs := by
        simpa [G] using hmp.symm.variance_fun_comp (f := F) hF.aemeasurable
      have hten := variance_prod_le_integral_variance_fst_add_integral_variance_snd
        (μ := μ) (ν := γn) hG
      rw [hvar] at hten
      have hA : (∫ y, variance (sectionFst G y) μ ∂γn)
          = ∫ x, coordVar (μ := μ) F 0 x ∂γs := by
        rw [integral_coordVar_zero_eq]
        rfl
      rw [hA] at hten
      have hIH : (∫ a, variance (sectionSnd G a) γn ∂μ)
          ≤ ∫ a, (∑ j : Fin n,
              ∫ y, coordVar (μ := μ) (sectionSnd G a) j y ∂γn) ∂μ := by
        refine integral_mono_ae (integrable_variance_sectionSnd hG) ?_ ?_
        · refine integrable_finsetSum _ (fun j _ => ?_)
          have h : Integrable (fun a => ∫ y, succFstVar (α := α) (μ := μ) F j (a, y)
              ∂γn) μ :=
            (integrable_succFstVar (α := α) (μ := μ) hF j).integral_prod_left
          refine h.congr (ae_of_all _ fun a => ?_)
          refine integral_congr_ae (ae_of_all _ fun y => ?_)
          rfl
        · filter_upwards [ae_memLp_sectionSnd hG] with a ha
          exact ih (sectionSnd G a) ha
      have hsum_int : (∫ a, (∑ j : Fin n,
            ∫ y, coordVar (μ := μ) (sectionSnd G a) j y ∂γn) ∂μ)
          = ∑ j : Fin n, ∫ a,
              (∫ y, coordVar (μ := μ) (sectionSnd G a) j y ∂γn) ∂μ := by
        rw [integral_finsetSum]
        intro j _
        have h : Integrable (fun a => ∫ y, succFstVar (α := α) (μ := μ) F j (a, y)
            ∂γn) μ :=
          (integrable_succFstVar (α := α) (μ := μ) hF j).integral_prod_left
        refine h.congr (ae_of_all _ fun a => ?_)
        refine integral_congr_ae (ae_of_all _ fun y => ?_)
        rfl
      have hB : (∫ a, variance (sectionSnd G a) γn ∂μ)
          ≤ ∑ j : Fin n, ∫ x, coordVar (μ := μ) F (Fin.succ j) x ∂γs := by
        calc (∫ a, variance (sectionSnd G a) γn ∂μ)
            ≤ ∫ a, (∑ j : Fin n,
                ∫ y, coordVar (μ := μ) (sectionSnd G a) j y ∂γn) ∂μ := hIH
          _ = ∑ j : Fin n, ∫ a,
                (∫ y, coordVar (μ := μ) (sectionSnd G a) j y ∂γn) ∂μ := hsum_int
          _ = ∑ j : Fin n, ∫ x, coordVar (μ := μ) F (Fin.succ j) x ∂γs := by
              refine Finset.sum_congr rfl (fun j _ => ?_)
              rw [integral_coordVar_succ_eq (α := α) (μ := μ) hF j]
              refine integral_congr_ae (ae_of_all _ fun a => ?_)
              refine integral_congr_ae (ae_of_all _ fun y => ?_)
              rfl
      have hten' : variance F γs
          ≤ (∫ x, coordVar (μ := μ) F 0 x ∂γs)
            + ∑ j : Fin n, ∫ x, coordVar (μ := μ) F (Fin.succ j) x ∂γs :=
        hten.trans (add_le_add_right hB _)
      simpa [Fin.sum_univ_succ] using hten'

end

end GUEStrongConvergence
