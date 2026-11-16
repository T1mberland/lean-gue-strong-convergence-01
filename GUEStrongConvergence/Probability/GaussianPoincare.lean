/-
# Gaussian Poincaré on arbitrary finite index types and Euclidean space

This module transports the `Fin n` Gaussian gradient bound
`gaussian_poincare_fin` (from `FiniteGaussianPoincare`) to

* an arbitrary finite index type `κ` (via `Fintype.equivFin` and `piCongrLeft`), and
* the standard Gaussian measure on `EuclideanSpace ℝ κ` (via `MeasurableEquiv.toLp 2`).

The hypotheses stay honest: `L²` of the function and of each coordinate derivative, a.e. fibre
differentiability with the stated derivative, and a.e. fibre polynomial growth.  No desired
variance bound is assumed; the one-dimensional Gaussian Poincaré inequality is applied fibre-wise
inside `gaussian_poincare_fin`.
-/
import GUEStrongConvergence.Probability.FiniteGaussianPoincare
import GUEStrongConvergence.Probability.CommonSpace
open MeasureTheory ProbabilityTheory Filter
open scoped ProbabilityTheory ENNReal NNReal Topology

namespace GUEStrongConvergence

noncomputable section

/-- Updating a coordinate commutes with the reindexing equivalence `piCongrLeft`. -/
theorem piCongrLeft_symm_update {κ : Type*} [Fintype κ] [DecidableEq κ] {n : ℕ}
    (e : κ ≃ Fin n) (y : Fin n → ℝ) (p : Fin n) (t : ℝ) :
    (MeasurableEquiv.piCongrLeft (fun _ : Fin n => ℝ) e).symm (Function.update y p t)
      = Function.update ((MeasurableEquiv.piCongrLeft (fun _ : Fin n => ℝ) e).symm y)
          (e.symm p) t := by
  ext a
  conv_lhs =>
    change (Equiv.piCongrLeft (fun _ : Fin n => ℝ) e).symm (Function.update y p t) a
    rw [Equiv.piCongrLeft_symm_apply]
  have hsym : (MeasurableEquiv.piCongrLeft (fun _ : Fin n => ℝ) e).symm y a = y (e a) := by
    conv_lhs =>
      change (Equiv.piCongrLeft (fun _ : Fin n => ℝ) e).symm y a
      rw [Equiv.piCongrLeft_symm_apply]
  rw [Function.update_apply, Function.update_apply, hsym]
  by_cases h : a = e.symm p
  · subst h
    simp
  · have h' : e a ≠ p := by
      intro hh
      apply h
      rw [← e.symm_apply_apply a, hh]
    simp [h, h']

/-- **Gaussian Poincaré inequality on an arbitrary finite index type.**
For `F : (κ → ℝ) → ℝ` with coordinate derivatives `D p`,
`Var_{γ^⊗κ}(F) ≤ ∑ p, ∫ x, (D p x)^2 dγ^⊗κ(x)`. -/
theorem gaussian_poincare_fintype {κ : Type*} [Fintype κ] [DecidableEq κ]
    {F : (κ → ℝ) → ℝ} {D : κ → (κ → ℝ) → ℝ}
    (hF : MemLp F 2 (Measure.pi (fun _ : κ => gaussianReal 0 1)))
    (hDmem : ∀ p : κ, MemLp (D p) 2 (Measure.pi (fun _ : κ => gaussianReal 0 1)))
    (hderiv : ∀ p : κ, ∀ᵐ x ∂(Measure.pi (fun _ : κ => gaussianReal 0 1)), ∀ t : ℝ,
      HasDerivAt (fun u : ℝ => F (Function.update x p u)) (D p (Function.update x p t)) t)
    (hpoly : ∀ p : κ, ∀ᵐ x ∂(Measure.pi (fun _ : κ => gaussianReal 0 1)),
      PolyGrowth (fun u : ℝ => F (Function.update x p u)) ∧
        PolyGrowth (fun u : ℝ => D p (Function.update x p u))) :
    variance F (Measure.pi (fun _ : κ => gaussianReal 0 1))
      ≤ ∑ p : κ, ∫ x, (D p x) ^ 2 ∂(Measure.pi (fun _ : κ => gaussianReal 0 1)) := by
  classical
  let n : ℕ := Fintype.card κ
  let e : κ ≃ Fin n := Fintype.equivFin κ
  let Ψ : (κ → ℝ) ≃ᵐ (Fin n → ℝ) :=
    MeasurableEquiv.piCongrLeft (fun _ : Fin n => ℝ) e
  have hmp : MeasurePreserving Ψ
      (Measure.pi (fun _ : κ => gaussianReal 0 1)) (gaussianFinMeasure n) := by
    simpa [Ψ, n, gaussianFinMeasure] using
      (measurePreserving_piCongrLeft (α := fun _ : Fin n => ℝ)
        (μ := fun _ : Fin n => gaussianReal 0 1) e)
  let F' : (Fin n → ℝ) → ℝ := fun y => F (Ψ.symm y)
  let D' : Fin n → (Fin n → ℝ) → ℝ := fun p y => D (e.symm p) (Ψ.symm y)
  have hF' : MemLp F' 2 (gaussianFinMeasure n) := by
    simpa [F', Function.comp_def] using hF.comp_measurePreserving hmp.symm
  have hD'mem : ∀ p : Fin n, MemLp (D' p) 2 (gaussianFinMeasure n) := by
    intro p
    simpa [D', Function.comp_def] using
      (hDmem (e.symm p)).comp_measurePreserving hmp.symm
  have hderiv' : ∀ p : Fin n, ∀ᵐ y ∂(gaussianFinMeasure n), ∀ t : ℝ,
      HasDerivAt (fun u : ℝ => F' (Function.update y p u)) (D' p (Function.update y p t)) t := by
    intro p
    have hd := hmp.symm.quasiMeasurePreserving.ae (hderiv (e.symm p))
    filter_upwards [hd] with y hy
    intro t
    convert hy t using 1
    · funext u
      simp [F', Ψ, piCongrLeft_symm_update e y p u]
    · simp [D', Ψ, piCongrLeft_symm_update e y p t]
  have hpoly' : ∀ p : Fin n, ∀ᵐ y ∂(gaussianFinMeasure n),
      PolyGrowth (fun u : ℝ => F' (Function.update y p u)) ∧
        PolyGrowth (fun u : ℝ => D' p (Function.update y p u)) := by
    intro p
    have hp := hmp.symm.quasiMeasurePreserving.ae (hpoly (e.symm p))
    filter_upwards [hp] with y hy
    constructor
    · have hfun : (fun u : ℝ => F' (Function.update y p u))
          = fun u : ℝ => F (Function.update (Ψ.symm y) (e.symm p) u) := by
        funext u
        simp [F', Ψ, piCongrLeft_symm_update e y p u]
      rw [hfun]
      exact hy.1
    · have hfun : (fun u : ℝ => D' p (Function.update y p u))
          = fun u : ℝ => D (e.symm p) (Function.update (Ψ.symm y) (e.symm p) u) := by
        funext u
        simp [D', Ψ, piCongrLeft_symm_update e y p u]
      rw [hfun]
      exact hy.2
  have hmain := gaussian_poincare_fin (n := n) (F := F') (D := D')
    hF' hD'mem hderiv' hpoly'
  have hvar : variance F' (gaussianFinMeasure n)
      = variance F (Measure.pi (fun _ : κ => gaussianReal 0 1)) := by
    simpa [F'] using hmp.symm.variance_fun_comp (f := F) hF.aemeasurable
  have hterm : ∀ p : Fin n,
      (∫ y, (D' p y) ^ 2 ∂(gaussianFinMeasure n))
        = ∫ x, (D (e.symm p) x) ^ 2 ∂(Measure.pi (fun _ : κ => gaussianReal 0 1)) := by
    intro p
    simpa [D'] using hmp.symm.integral_comp'
      (fun x => (D (e.symm p) x) ^ 2)
  calc variance F (Measure.pi (fun _ : κ => gaussianReal 0 1))
      = variance F' (gaussianFinMeasure n) := hvar.symm
    _ ≤ ∑ p : Fin n, ∫ y, (D' p y) ^ 2 ∂(gaussianFinMeasure n) := hmain
    _ = ∑ p : Fin n,
          ∫ x, (D (e.symm p) x) ^ 2 ∂(Measure.pi (fun _ : κ => gaussianReal 0 1)) := by
        exact Finset.sum_congr rfl (fun p _ => hterm p)
    _ = ∑ q : κ,
          ∫ x, (D q x) ^ 2 ∂(Measure.pi (fun _ : κ => gaussianReal 0 1)) :=
        Equiv.sum_comp e.symm
          (fun q : κ => ∫ x, (D q x) ^ 2 ∂(Measure.pi (fun _ : κ => gaussianReal 0 1)))


/-- **Gaussian Poincaré inequality on `EuclideanSpace ℝ κ` under `stdGaussian`.**
The coordinate fibre is `t ↦ F (WithLp.toLp 2 (Function.update x.ofLp p t))`. -/
theorem gaussian_poincare_stdGaussian {κ : Type*} [Fintype κ] [DecidableEq κ]
    {F : EuclideanSpace ℝ κ → ℝ} {D : κ → EuclideanSpace ℝ κ → ℝ}
    (hF : MemLp F 2 (stdGaussian (EuclideanSpace ℝ κ)))
    (hDmem : ∀ p : κ, MemLp (D p) 2 (stdGaussian (EuclideanSpace ℝ κ)))
    (hderiv : ∀ p : κ, ∀ᵐ x ∂(stdGaussian (EuclideanSpace ℝ κ)), ∀ t : ℝ,
      HasDerivAt (fun u : ℝ => F (WithLp.toLp 2 (Function.update (WithLp.ofLp x) p u)))
        (D p (WithLp.toLp 2 (Function.update (WithLp.ofLp x) p t))) t)
    (hpoly : ∀ p : κ, ∀ᵐ x ∂(stdGaussian (EuclideanSpace ℝ κ)),
      PolyGrowth (fun u : ℝ =>
        F (WithLp.toLp 2 (Function.update (WithLp.ofLp x) p u))) ∧
      PolyGrowth (fun u : ℝ =>
        D p (WithLp.toLp 2 (Function.update (WithLp.ofLp x) p u)))) :
    variance F (stdGaussian (EuclideanSpace ℝ κ))
      ≤ ∑ p : κ, ∫ x, (D p x) ^ 2 ∂(stdGaussian (EuclideanSpace ℝ κ)) := by
  classical
  let toE : (κ → ℝ) → EuclideanSpace ℝ κ := WithLp.toLp 2
  let F' : (κ → ℝ) → ℝ := fun y => F (toE y)
  let D' : κ → (κ → ℝ) → ℝ := fun p y => D p (toE y)
  have hmp_symm : MeasurePreserving (MeasurableEquiv.toLp 2 (κ → ℝ)).symm
      (stdGaussian (EuclideanSpace ℝ κ)) (Measure.pi (fun _ : κ => gaussianReal 0 1)) :=
    ⟨(MeasurableEquiv.toLp 2 (κ → ℝ)).symm.measurable, stdGaussian_map_toLp_symm κ⟩
  have hmp : MeasurePreserving (MeasurableEquiv.toLp 2 (κ → ℝ))
      (Measure.pi (fun _ : κ => gaussianReal 0 1)) (stdGaussian (EuclideanSpace ℝ κ)) :=
    hmp_symm.symm
  have hF' : MemLp F' 2 (Measure.pi (fun _ : κ => gaussianReal 0 1)) := by
    simpa [F', toE, Function.comp_def, MeasurableEquiv.coe_toLp] using
      hF.comp_measurePreserving hmp
  have hD'mem : ∀ p : κ, MemLp (D' p) 2 (Measure.pi (fun _ : κ => gaussianReal 0 1)) := by
    intro p
    simpa [D', toE, Function.comp_def, MeasurableEquiv.coe_toLp] using
      (hDmem p).comp_measurePreserving hmp
  have hderiv' : ∀ p : κ,
      ∀ᵐ y ∂(Measure.pi (fun _ : κ => gaussianReal 0 1)), ∀ t : ℝ,
        HasDerivAt (fun u : ℝ => F' (Function.update y p u))
          (D' p (Function.update y p t)) t := by
    intro p
    have hd := hmp.quasiMeasurePreserving.ae (hderiv p)
    filter_upwards [hd] with y hy
    intro t
    convert hy t using 1
    · funext u
      simp [F', toE, WithLp.ofLp_toLp]
    · simp [D', toE, WithLp.ofLp_toLp]
  have hpoly' : ∀ p : κ,
      ∀ᵐ y ∂(Measure.pi (fun _ : κ => gaussianReal 0 1)),
        PolyGrowth (fun u : ℝ => F' (Function.update y p u)) ∧
          PolyGrowth (fun u : ℝ => D' p (Function.update y p u)) := by
    intro p
    have hp := hmp.quasiMeasurePreserving.ae (hpoly p)
    filter_upwards [hp] with y hy
    constructor
    · have hfun : (fun u : ℝ => F' (Function.update y p u))
          = fun u : ℝ => F (WithLp.toLp 2
              (Function.update (WithLp.ofLp (WithLp.toLp 2 y)) p u)) := by
        funext u
        simp [F', toE]
      rw [hfun]
      exact hy.1
    · have hfun : (fun u : ℝ => D' p (Function.update y p u))
          = fun u : ℝ => D p (WithLp.toLp 2
              (Function.update (WithLp.ofLp (WithLp.toLp 2 y)) p u)) := by
        funext u
        simp [D', toE]
      rw [hfun]
      exact hy.2
  have hmain := gaussian_poincare_fintype (κ := κ) (F := F') (D := D')
    hF' hD'mem hderiv' hpoly'
  have hvar : variance F' (Measure.pi (fun _ : κ => gaussianReal 0 1))
      = variance F (stdGaussian (EuclideanSpace ℝ κ)) := by
    simpa [F', toE, MeasurableEquiv.coe_toLp] using
      hmp.variance_fun_comp (f := F) hF.aemeasurable
  have hterm : ∀ p : κ,
      (∫ y, (D' p y) ^ 2 ∂(Measure.pi (fun _ : κ => gaussianReal 0 1)))
        = ∫ x, (D p x) ^ 2 ∂(stdGaussian (EuclideanSpace ℝ κ)) := by
    intro p
    simpa [D', toE, MeasurableEquiv.coe_toLp] using
      hmp.integral_comp' (fun x => (D p x) ^ 2)
  calc variance F (stdGaussian (EuclideanSpace ℝ κ))
      = variance F' (Measure.pi (fun _ : κ => gaussianReal 0 1)) := hvar.symm
    _ ≤ ∑ p : κ, ∫ y, (D' p y) ^ 2 ∂(Measure.pi (fun _ : κ => gaussianReal 0 1)) := hmain
    _ = ∑ p : κ, ∫ x, (D p x) ^ 2 ∂(stdGaussian (EuclideanSpace ℝ κ)) := by
        exact Finset.sum_congr rfl (fun p _ => hterm p)

end

end GUEStrongConvergence
