/-
# Gaussian Wick recursion for standard Gaussian coordinates

This file develops the Gaussian moment (Wick) recursion needed for GUE word moments.
Working on `EuclideanSpace ℝ κ` with the standard Gaussian measure, we define the
monomial `coordProd l x = ∏_{q ∈ l} x q` for a list of coordinates, prove that every such
monomial is integrable, and prove the coordinate-Stein recurrence

`E[x_p ∏_{q ∈ l} x_q] = ∑_{i : Fin l.length} [l.get i = p] E[∏_{j ≠ i} l_j]`.

Iterating the recurrence gives the full pairing/Wick formula: the expectation of `coordProd l`
equals the recursively defined `wick l`, which sums over the choices of the partner of the
first coordinate (`gaussianMoment_eq_wick`).  Odd-length lists therefore have zero moment,
and the mixed four-coordinate moment is the classical sum of the three pairings
(`integral_coord_four`).  The specialized square moment `integral_coord_sq_mul_coord_sq`
records `E[x_p² x_q²] = 3` for `p = q` and `1` otherwise.  All statements assume only
`[Fintype κ] [DecidableEq κ]`; the empty index type is allowed (`l = []` gives moment `1`).

All analytic hypotheses of the coordinate Stein identity (`integral_eval_smul_stdGaussian`)
are discharged: the polynomial monomial is split as `t ^ count * (product of the remaining
coordinates)`, the one-dimensional density moments are Mathlib/project lemmas
(`integrable_gaussianPDFReal_mul_pow`, `tendsto_gaussianPDFReal_mul_pow_atTop/atBot`), and the
remaining coordinate product is integrable by Hölder (`MemLp.prod`) using that Gaussian
coordinates have moments of all orders.
-/
import Mathlib.Probability.Independence.InfinitePi
import GUEStrongConvergence.Probability.SteinIdentity
import GUEStrongConvergence.Probability.GaussianMoments
import GUEStrongConvergence.Probability.GUEModel

open MeasureTheory ProbabilityTheory Filter
open scoped RealInnerProductSpace Matrix ENNReal Topology

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace GUEStrongConvergence

noncomputable section

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-! ### Monomials in Gaussian coordinates -/

/-- The monomial `∏_{q ∈ l} x q`. -/
def coordProd (l : List κ) (x : EuclideanSpace ℝ κ) : ℝ :=
  (l.map (fun q => x q)).prod

@[simp] lemma coordProd_nil (x : EuclideanSpace ℝ κ) : coordProd [] x = 1 := rfl

@[simp] lemma coordProd_cons (q : κ) (l : List κ) (x : EuclideanSpace ℝ κ) :
    coordProd (q :: l) x = x q * coordProd l x := by
  simp [coordProd]

/-- The derivative of `coordProd l` in the direction of the coordinate `p`, written
recursively so that it differentiates cleanly along `piRecon`. -/
def coordProdDeriv (p : κ) : List κ → EuclideanSpace ℝ κ → ℝ
  | [], _ => 0
  | q :: l, x => (if q = p then coordProd l x else 0) + x q * coordProdDeriv p l x

@[simp] lemma coordProdDeriv_nil (p : κ) (x : EuclideanSpace ℝ κ) :
    coordProdDeriv p [] x = 0 := rfl

@[simp] lemma coordProdDeriv_cons (p q : κ) (l : List κ) (x : EuclideanSpace ℝ κ) :
    coordProdDeriv p (q :: l) x =
      (if q = p then coordProd l x else 0) + x q * coordProdDeriv p l x := rfl

/-- The product of the coordinates of `l` which are not equal to `p`, as a function of the
remaining coordinates `y` on `{i // i ≠ p}`.  It is written as a product over positions so
that its integrability follows directly from Hölder. -/
def coordProdOff (p : κ) (l : List κ) (y : {i : κ // ¬ i = p} → ℝ) : ℝ :=
  ∏ i : Fin l.length, if h : l.get i = p then 1 else y ⟨l.get i, h⟩

@[simp] lemma coordProdOff_nil (p : κ) (y : {i : κ // ¬ i = p} → ℝ) :
    coordProdOff p [] y = 1 := by
  simp [coordProdOff]

/-- Decomposition of a monomial along the coordinate `p`: the `p`-coordinate contributes
`t ^ (number of occurrences of p)`, and the other coordinates are collected in
`coordProdOff`. -/
lemma coordProd_piRecon (p : κ) (l : List κ) (t : ℝ)
    (y : {i : κ // ¬ i = p} → ℝ) :
    coordProd l (WithLp.toLp 2 (piRecon p t y)) =
      t ^ l.count p * coordProdOff p l y := by
  induction l with
  | nil => simp [coordProd, coordProdOff]
  | cons q l ih =>
    rw [coordProd_cons, ih]
    have hq : (WithLp.toLp 2 (piRecon p t y)) q =
        if h : q = p then t else y ⟨q, h⟩ := by
      simp [piRecon]
    rw [hq]
    have hoff : coordProdOff p (q :: l) y =
        (if h : q = p then 1 else y ⟨q, h⟩) * coordProdOff p l y := by
      rw [coordProdOff, coordProdOff]
      change (∏ i : Fin (l.length + 1),
          if h : (q :: l).get i = p then 1 else y ⟨(q :: l).get i, h⟩) =
        (if h : q = p then 1 else y ⟨q, h⟩) *
          ∏ i : Fin l.length,
            if h : l.get i = p then 1 else y ⟨l.get i, h⟩
      rw [Fin.prod_univ_succ]
      congr 1
    rw [hoff]
    by_cases h : q = p
    · have hcount : (q :: l).count p = l.count p + 1 := by
        rw [h, List.count_cons_self]
      rw [hcount, pow_succ]
      simp [h]
      ring
    · have hcount : (q :: l).count p = l.count p := List.count_cons_of_ne h
      rw [hcount]
      simp [h]
      ring

/-- The recursive derivative is the sum over the occurrences of `p` of the product of all
other coordinates. -/
lemma coordProdDeriv_eq_sum (p : κ) (l : List κ) (x : EuclideanSpace ℝ κ) :
    coordProdDeriv p l x =
      ∑ i : Fin l.length,
        if l.get i = p then coordProd (l.eraseIdx i) x else 0 := by
  induction l with
  | nil => simp [coordProdDeriv]
  | cons q l ih =>
    rw [coordProdDeriv_cons, ih]
    change (if q = p then coordProd l x else 0) +
        x q * (∑ i : Fin l.length,
          if l.get i = p then coordProd (l.eraseIdx i) x else 0) =
      ∑ i : Fin (l.length + 1),
        if (q :: l).get i = p then coordProd ((q :: l).eraseIdx i) x else 0
    rw [Fin.sum_univ_succ, Finset.mul_sum]
    simp only [List.get_cons_zero]
    simp [coordProd_cons]

/-- Differentiation of `coordProd l` along the coordinate `p` in the `piRecon`
parameterization. -/
lemma hasDerivAt_coordProd (p : κ) (l : List κ) (y : {i : κ // ¬ i = p} → ℝ)
    (a : ℝ) :
    HasDerivAt (fun t => coordProd l (WithLp.toLp 2 (piRecon p t y)))
      (coordProdDeriv p l (WithLp.toLp 2 (piRecon p a y))) a := by
  induction l with
  | nil => simpa [coordProd, coordProdDeriv] using hasDerivAt_const a (1 : ℝ)
  | cons q l ih =>
    have hq : HasDerivAt (fun t : ℝ => (WithLp.toLp 2 (piRecon p t y)) q)
        (if q = p then 1 else 0) a := by
      by_cases h : q = p
      · have hfun : (fun t : ℝ => (WithLp.toLp 2 (piRecon p t y)) q) = fun t => t := by
          funext t
          simp [piRecon, h]
        rw [hfun, ite_eq_left h]
        exact hasDerivAt_id a
      · have hfun : (fun t : ℝ => (WithLp.toLp 2 (piRecon p t y)) q) =
            fun _ => y ⟨q, h⟩ := by
          funext t
          simp [piRecon, h]
        rw [hfun, ite_eq_right h]
        exact hasDerivAt_const a (y ⟨q, h⟩)
    have h := hq.mul ih
    have hEq : (fun t => (WithLp.toLp 2 (piRecon p t y)) q *
        coordProd l (WithLp.toLp 2 (piRecon p t y))) =
        (fun t => coordProd (q :: l) (WithLp.toLp 2 (piRecon p t y))) := by
      funext t; rw [coordProd_cons]
    rw [← hEq]
    refine h.congr_deriv ?_
    rw [coordProdDeriv_cons]
    by_cases hqp : q = p <;> simp [hqp]


/-! ### Moments of all orders and integrability of monomials -/

/-- The coordinate function on `Measure.pi` of standard Gaussians is in `L^n` for every
`n ≥ 1`. -/
lemma memLp_coord_pi (q : κ) (n : ℕ) (_hn : 1 ≤ n) :
    MemLp (fun y : κ → ℝ => y q) (n : ℝ≥0∞)
      (Measure.pi (fun _ : κ => gaussianReal 0 1)) := by
  have h1 : MemLp (fun x : ℝ => x) (n : ℝ≥0∞) (gaussianReal 0 1) :=
    IsGaussian.memLp_id (gaussianReal 0 1) n (by simp)
  have h2 := h1.comp_measurePreserving
    (measurePreserving_eval (fun _ : κ => gaussianReal 0 1) q)
  simpa [Function.comp_def] using h2

/-- The coordinate function of the standard Gaussian on a Euclidean space is in `L^n` for
every `n ≥ 1`. -/
lemma memLp_coord_stdGaussian (q : κ) (n : ℕ) (_hn : 1 ≤ n) :
    MemLp (fun x : EuclideanSpace ℝ κ => x q) (n : ℝ≥0∞)
      (stdGaussian (EuclideanSpace ℝ κ)) := by
  have hid : MemLp (fun x : EuclideanSpace ℝ κ => x) (n : ℝ≥0∞)
      (stdGaussian (EuclideanSpace ℝ κ)) :=
    IsGaussian.memLp_id (stdGaussian (EuclideanSpace ℝ κ)) n (by simp)
  have h2 := (innerSL ℝ (EuclideanSpace.basisFun κ ℝ q)).comp_memLp' hid
  have h2' : MemLp (fun x : EuclideanSpace ℝ κ =>
      inner ℝ (EuclideanSpace.basisFun κ ℝ q) x) (n : ℝ≥0∞)
      (stdGaussian (EuclideanSpace ℝ κ)) := by
    simpa [Function.comp_def] using h2
  have hinner : ∀ x : EuclideanSpace ℝ κ,
      inner ℝ (EuclideanSpace.basisFun κ ℝ q) x = x q := by
    intro x
    simpa using EuclideanSpace.basisFun_inner κ ℝ x q
  simpa only [hinner] using h2' 

/-- A product of `n` functions, each in `L^n`, is in `L^1` (`n` factors of exponent `n`
give Hölder exponent `1`). -/
lemma memLp_finProd_one {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {n : ℕ} (hn : 1 ≤ n) {f : Fin n → α → ℝ}
    (hf : ∀ i, MemLp (f i) (n : ℝ≥0∞) μ) :
    MemLp (fun y : α => ∏ i, f i y) 1 μ := by
  have hn0 : (n : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hn)
  have hsum : (∑ _i : Fin n, ((n : ℝ≥0∞)⁻¹)) = 1 := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    exact ENNReal.mul_inv_cancel hn0 (by simp)
  have h := MemLp.prod (s := Finset.univ) (f := f) (p := fun _ => (n : ℝ≥0∞))
    (fun i _ => hf i)
  rw [hsum, inv_one] at h
  change MemLp (fun y : α => ∏ i, f i y) 1 μ
  refine MemLp.ae_eq ?_ h
  filter_upwards with y
  simp [Finset.prod_apply]

/-- The list monomial as a product over the positions `Fin l.length`. -/
lemma coordProd_toLp_eq_prod_get (l : List κ) (y : κ → ℝ) :
    coordProd l (WithLp.toLp 2 y) = ∏ i : Fin l.length, y (l.get i) := by
  induction l with
  | nil => simp [coordProd]
  | cons q l ih =>
    rw [coordProd_cons, ih]
    change (WithLp.toLp 2 y) q * (∏ i : Fin l.length, y (l.get i)) =
      ∏ i : Fin (l.length + 1), y ((q :: l).get i)
    rw [Fin.prod_univ_succ]
    simp

/-- Every monomial in Gaussian coordinates is integrable on the product Gaussian space. -/
lemma integrable_coordProd_pi (l : List κ) :
    Integrable (fun y : κ → ℝ => coordProd l (WithLp.toLp 2 y))
      (Measure.pi (fun _ : κ => gaussianReal 0 1)) := by
  cases l with
  | nil => simp [coordProd]
  | cons q l =>
    have hn : 1 ≤ (q :: l).length := by simp
    have hf : ∀ i : Fin (q :: l).length,
        MemLp (fun y : κ → ℝ => y ((q :: l).get i))
          ((q :: l).length : ℝ≥0∞)
          (Measure.pi (fun _ : κ => gaussianReal 0 1)) :=
      fun i => memLp_coord_pi _ _ hn
    have h := memLp_finProd_one hn hf
    rw [memLp_one_iff_integrable] at h
    simpa [coordProd_toLp_eq_prod_get] using h

/-- Every monomial in Gaussian coordinates is integrable for the standard Gaussian measure
on `EuclideanSpace ℝ κ`. -/
lemma integrable_coordProd_stdGaussian (l : List κ) :
    Integrable (fun x : EuclideanSpace ℝ κ => coordProd l x)
      (stdGaussian (EuclideanSpace ℝ κ)) := by
  have hmp : MeasurePreserving (MeasurableEquiv.toLp 2 (κ → ℝ))
      (Measure.pi (fun _ : κ => gaussianReal 0 1))
      (stdGaussian (EuclideanSpace ℝ κ)) :=
    ⟨(MeasurableEquiv.toLp 2 (κ → ℝ)).measurable, map_pi_eq_stdGaussian⟩
  have hcont : Continuous (fun x : EuclideanSpace ℝ κ => coordProd l x) := by
    induction l with
    | nil => simpa [coordProd] using continuous_const
    | cons q l ih =>
      have hq : Continuous (fun x : EuclideanSpace ℝ κ => x q) := by fun_prop
      have hcont := hq.mul ih
      convert hcont using 1
      ext x
      simp [Pi.mul_apply, coordProd_cons]
  have hmeas : AEStronglyMeasurable (fun x : EuclideanSpace ℝ κ => coordProd l x)
      (stdGaussian (EuclideanSpace ℝ κ)) := hcont.aestronglyMeasurable
  have h' : Integrable ((fun x : EuclideanSpace ℝ κ => coordProd l x) ∘
      MeasurableEquiv.toLp 2 (κ → ℝ)) (Measure.pi (fun _ : κ => gaussianReal 0 1)) := by
    simpa [Function.comp_def, MeasurableEquiv.coe_toLp] using integrable_coordProd_pi l
  exact (hmp.integrable_comp hmeas).mp h'


/-- The off-`p` coordinate product is integrable on the product Gaussian space. -/
lemma integrable_coordProdOff_pi (p : κ) (l : List κ) :
    Integrable (coordProdOff p l)
      (Measure.pi (fun _ : {i : κ // ¬ i = p} => gaussianReal 0 1)) := by
  cases l with
  | nil =>
    convert integrable_const (1 : ℝ) using 1
    · ext y
      simp [coordProdOff]
    · infer_instance
  | cons q l =>
    have hn : 1 ≤ (q :: l).length := by simp
    have hf : ∀ i : Fin (q :: l).length,
        MemLp (fun y : {j : κ // ¬ j = p} → ℝ =>
            if h : (q :: l).get i = p then 1 else y ⟨(q :: l).get i, h⟩)
          ((q :: l).length : ℝ≥0∞)
          (Measure.pi (fun _ : {j : κ // ¬ j = p} => gaussianReal 0 1)) := by
      intro i
      by_cases h : (q :: l).get i = p
      · simp only [h, dite_true]
        exact memLp_const (1 : ℝ)
      · simp only [h, dite_false]
        exact memLp_coord_pi (⟨(q :: l).get i, h⟩ : {j : κ // ¬ j = p}) _ hn
    have h := memLp_finProd_one (α := {j : κ // ¬ j = p} → ℝ) hn hf
    rw [memLp_one_iff_integrable] at h
    convert h using 1
    ext y
    simp [coordProdOff]

/-- Off-product times `t^n ρ(t)` is integrable on the product space. -/
lemma integrable_density_prod_coordProdOff (p : κ) (l : List κ) (n : ℕ) :
    Integrable (fun z : ({i : κ // ¬ i = p} → ℝ) × ℝ =>
        coordProdOff p l z.1 * (gaussianPDFReal 0 1 z.2 * z.2 ^ n))
      ((Measure.pi (fun _ : {i : κ // ¬ i = p} => gaussianReal 0 1)).prod
        (volume : Measure ℝ)) :=
  Integrable.mul_prod (integrable_coordProdOff_pi p l)
    (integrable_gaussianPDFReal_mul_pow n)

/-- **Coordinate Stein recurrence for monomials**:
`E[x_p ∏_{q ∈ l} x_q] = ∑_{i} [l_i = p] E[∏_{j ≠ i} l_j]`. -/
theorem integral_coord_mul_coordProd (p : κ) (l : List κ) :
    ∫ x : EuclideanSpace ℝ κ, x p * coordProd l x
        ∂(stdGaussian (EuclideanSpace ℝ κ)) =
      ∑ i : Fin l.length,
        if l.get i = p then
          ∫ x : EuclideanSpace ℝ κ, coordProd (l.eraseIdx i) x
            ∂(stdGaussian (EuclideanSpace ℝ κ))
        else 0 := by
  have hderiv : ∀ (y : {i : κ // ¬ i = p} → ℝ) (a : ℝ),
      HasDerivAt (fun t => coordProd l (WithLp.toLp 2 (piRecon p t y)))
        (coordProdDeriv p l (WithLp.toLp 2 (piRecon p a y))) a :=
    fun y a => hasDerivAt_coordProd p l y a
  have hint1 : Integrable (fun z : ({i : κ // ¬ i = p} → ℝ) × ℝ =>
      gaussianPDFReal 0 1 z.2 •
        coordProdDeriv p l (WithLp.toLp 2 (piRecon p z.2 z.1)))
      ((Measure.pi (fun _ : {i : κ // ¬ i = p} => gaussianReal 0 1)).prod
        (volume : Measure ℝ)) := by
    have hEq : (fun z : ({i : κ // ¬ i = p} → ℝ) × ℝ =>
        gaussianPDFReal 0 1 z.2 •
          coordProdDeriv p l (WithLp.toLp 2 (piRecon p z.2 z.1))) =
        fun z => ∑ i : Fin l.length,
          if l.get i = p then
            coordProdOff p (l.eraseIdx i) z.1 *
              (gaussianPDFReal 0 1 z.2 * z.2 ^ (l.eraseIdx i).count p)
          else 0 := by
      funext z
      rw [coordProdDeriv_eq_sum, Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      by_cases h : l.get i = p
      · rw [ite_eq_left h, ite_eq_left h, coordProd_piRecon]
        simp only [smul_eq_mul]
        ring
      · rw [ite_eq_right h, ite_eq_right h]
        simp
    rw [hEq]
    refine integrable_finsetSum Finset.univ fun i _ => ?_
    by_cases h : l.get i = p
    · simp only [h, ite_true]
      exact integrable_density_prod_coordProdOff p (l.eraseIdx i) _
    · simp only [h, ite_false]
      exact integrable_zero (({i : κ // ¬ i = p} → ℝ) × ℝ) ℝ
        ((Measure.pi (fun _ : {i : κ // ¬ i = p} => gaussianReal 0 1)).prod
          (volume : Measure ℝ))
  have hint2 : Integrable (fun z : ({i : κ // ¬ i = p} → ℝ) × ℝ =>
      z.2 • (gaussianPDFReal 0 1 z.2 •
        coordProd l (WithLp.toLp 2 (piRecon p z.2 z.1))))
      ((Measure.pi (fun _ : {i : κ // ¬ i = p} => gaussianReal 0 1)).prod
        (volume : Measure ℝ)) := by
    have hEq : (fun z : ({i : κ // ¬ i = p} → ℝ) × ℝ =>
        z.2 • (gaussianPDFReal 0 1 z.2 •
          coordProd l (WithLp.toLp 2 (piRecon p z.2 z.1)))) =
        fun z => coordProdOff p l z.1 *
          (gaussianPDFReal 0 1 z.2 * z.2 ^ (l.count p + 1)) := by
      funext z
      rw [coordProd_piRecon]
      simp only [smul_eq_mul]
      rw [pow_succ]
      ring
    rw [hEq]
    exact integrable_density_prod_coordProdOff p l (l.count p + 1)
  have hbot : ∀ᵐ (y : {i : κ // ¬ i = p} → ℝ)
      ∂(Measure.pi (fun _ : {i : κ // ¬ i = p} => gaussianReal 0 1)),
      Tendsto (fun t => gaussianPDFReal 0 1 t •
        coordProd l (WithLp.toLp 2 (piRecon p t y))) atBot (𝓝 0) := by
    filter_upwards with y
    have hfun : (fun t => gaussianPDFReal 0 1 t •
        coordProd l (WithLp.toLp 2 (piRecon p t y))) =
        fun t => coordProdOff p l y * (gaussianPDFReal 0 1 t * t ^ l.count p) := by
      funext t
      rw [coordProd_piRecon]
      simp only [smul_eq_mul]
      ring
    rw [hfun]
    simpa using (tendsto_gaussianPDFReal_mul_pow_atBot (l.count p)).const_mul
      (coordProdOff p l y)
  have htop : ∀ᵐ (y : {i : κ // ¬ i = p} → ℝ)
      ∂(Measure.pi (fun _ : {i : κ // ¬ i = p} => gaussianReal 0 1)),
      Tendsto (fun t => gaussianPDFReal 0 1 t •
        coordProd l (WithLp.toLp 2 (piRecon p t y))) atTop (𝓝 0) := by
    filter_upwards with y
    have hfun : (fun t => gaussianPDFReal 0 1 t •
        coordProd l (WithLp.toLp 2 (piRecon p t y))) =
        fun t => coordProdOff p l y * (gaussianPDFReal 0 1 t * t ^ l.count p) := by
      funext t
      rw [coordProd_piRecon]
      simp only [smul_eq_mul]
      ring
    rw [hfun]
    simpa using (tendsto_gaussianPDFReal_mul_pow_atTop (l.count p)).const_mul
      (coordProdOff p l y)
  have hstein := integral_eval_smul_stdGaussian (κ := κ) p
    (F := fun x => coordProd l x) (F' := fun x => coordProdDeriv p l x)
    hderiv hint1 hint2 hbot htop
  have hL : (∫ x : EuclideanSpace ℝ κ, x p • coordProd l x
      ∂(stdGaussian (EuclideanSpace ℝ κ))) =
      ∫ x : EuclideanSpace ℝ κ, x p * coordProd l x
        ∂(stdGaussian (EuclideanSpace ℝ κ)) := by
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    simp [smul_eq_mul]
  rw [hL] at hstein
  rw [hstein]
  simp_rw [coordProdDeriv_eq_sum]
  rw [integral_finsetSum]
  · refine Finset.sum_congr rfl fun i _ => ?_
    by_cases h : l.get i = p
    · simp only [h, ite_true]
    · simp only [h, ite_false]
      simp
  · intro i _
    by_cases h : l.get i = p
    · simp only [h, ite_true]
      exact integrable_coordProd_stdGaussian (l.eraseIdx i)
    · simp only [h, ite_false]
      exact integrable_zero (EuclideanSpace ℝ κ) ℝ (stdGaussian (EuclideanSpace ℝ κ))

/-- The Gaussian moment of the monomial indexed by `l`. -/
def gaussianMoment (l : List κ) : ℝ :=
  ∫ x : EuclideanSpace ℝ κ, coordProd l x ∂(stdGaussian (EuclideanSpace ℝ κ))

/-- The recursive Wick pairing sum: the first coordinate is paired with each occurrence of
itself in the tail, and the remaining coordinates contribute recursively. -/
def wick : List κ → ℝ
  | [] => 1
  | q :: l => ∑ i : Fin l.length,
      if l.get i = q then wick (l.eraseIdx i) else 0
termination_by l => l.length
decreasing_by
  simp_wf
  rw [List.length_eraseIdx, ite_eq_left i.isLt]
  omega

@[simp] lemma wick_nil : wick ([] : List κ) = 1 := by
  rw [wick.eq_1]

lemma wick_cons (q : κ) (l : List κ) :
    wick (q :: l) = ∑ i : Fin l.length,
      if l.get i = q then wick (l.eraseIdx i) else 0 := by
  rw [wick.eq_2]

/-- **Full Wick pairing formula**: the Gaussian moment of any finite monomial equals the
recursive pairing sum.  In particular odd-length monomials have zero moment. -/
theorem gaussianMoment_eq_wick (l : List κ) : gaussianMoment l = wick l := by
  suffices h : ∀ n : ℕ, ∀ l : List κ, l.length = n → gaussianMoment l = wick l from
    h l.length l rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro l hl
    cases l with
    | nil => simp [gaussianMoment, coordProd, wick_nil]
    | cons q l =>
      have hlen : l.length < n := by
        rw [List.length_cons] at hl
        omega
      have hstep : gaussianMoment (q :: l) =
          ∑ i : Fin l.length,
            if l.get i = q then gaussianMoment (l.eraseIdx i) else 0 := by
        rw [gaussianMoment]
        rw [show (∫ x : EuclideanSpace ℝ κ, coordProd (q :: l) x
            ∂(stdGaussian (EuclideanSpace ℝ κ))) =
            ∫ x : EuclideanSpace ℝ κ, x q * coordProd l x
              ∂(stdGaussian (EuclideanSpace ℝ κ)) by
          simp [coordProd]]
        rw [integral_coord_mul_coordProd q l]
        refine Finset.sum_congr rfl fun i _ => ?_
        simp [gaussianMoment]
      rw [hstep]
      simp only [wick]
      refine Finset.sum_congr rfl fun i _ => ?_
      by_cases h : l.get i = q
      · rw [ite_eq_left h, ite_eq_left h]
        refine ih (l.eraseIdx i).length ?_ (l.eraseIdx i) rfl
        have h1 : (l.eraseIdx i).length ≤ l.length := by
          rw [List.length_eraseIdx]
          split <;> omega
        omega
      · rw [ite_eq_right h, ite_eq_right h]

/-- Pair moment as a special case of the Wick formula. -/
lemma wick_pair (a b : κ) : wick [a, b] = if a = b then 1 else 0 := by
  rw [wick_cons]
  by_cases h : a = b
  · simp [h]
  · have h' : ¬ b = a := fun h' => h h'.symm
    simp [h, h']

lemma gaussianMoment_pair (a b : κ) :
    gaussianMoment [a, b] = if a = b then 1 else 0 := by
  rw [gaussianMoment_eq_wick, wick_pair]

/-- Pair moment as an integral of the two-coordinate monomial. -/
lemma integral_coordProd_pair (a b : κ) :
    ∫ x : EuclideanSpace ℝ κ, coordProd [a, b] x
        ∂(stdGaussian (EuclideanSpace ℝ κ)) = if a = b then 1 else 0 := by
  have h : (∫ x : EuclideanSpace ℝ κ, coordProd [a, b] x
      ∂(stdGaussian (EuclideanSpace ℝ κ))) =
      ∫ x : EuclideanSpace ℝ κ, x a * x b ∂(stdGaussian (EuclideanSpace ℝ κ)) := by
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    simp [coordProd]
  rw [h, integral_coord_mul_coord a b]

/-- **Mixed fourth moment**: `E[x_p x_q x_r x_s]` is the sum of the three pairings. -/
theorem integral_coord_four (p q r s : κ) :
    ∫ x : EuclideanSpace ℝ κ, x p * x q * x r * x s
        ∂(stdGaussian (EuclideanSpace ℝ κ)) =
      (if p = q then (if r = s then 1 else 0) else 0) +
      (if p = r then (if q = s then 1 else 0) else 0) +
      (if p = s then (if q = r then 1 else 0) else 0) := by
  have h1 : (∫ x : EuclideanSpace ℝ κ, x p * x q * x r * x s
      ∂(stdGaussian (EuclideanSpace ℝ κ))) =
      ∫ x : EuclideanSpace ℝ κ, x p * coordProd [q, r, s] x
        ∂(stdGaussian (EuclideanSpace ℝ κ)) := by
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    simp [coordProd]
    ring
  rw [h1, integral_coord_mul_coordProd p [q, r, s]]
  change (∑ i : Fin 3,
      if ([q, r, s]).get i = p then
        ∫ x : EuclideanSpace ℝ κ, coordProd (([q, r, s]).eraseIdx i) x
          ∂(stdGaussian (EuclideanSpace ℝ κ))
      else 0) = _
  rw [Fin.sum_univ_three]
  by_cases hpq : p = q <;> by_cases hpr : p = r <;> by_cases hps : p = s <;>
    simp [hpq, hpr, hps, eq_comm, integral_coord_mul_coord]

/-! ### The four-coordinate moment and square moments

As a first concrete Wick case (and the input needed for the second almost-sure moment),
we prove `E[x_p² x_q²] = 3` if `p = q` and `1` otherwise, together with the integrability
of `x_p² x_q²`.  The proof is the coordinate Stein identity applied to `F x = x_p x_q²`;
in each of the two cases `q = p` and `q ≠ p` the Stein hypotheses reduce to one-dimensional
Gaussian density moments. -/

section FourthMoment

variable (p q : κ)

/-- Squares of standard Gaussian coordinates are integrable. -/
lemma integrable_coord_sq (r : κ) :
    Integrable (fun x : EuclideanSpace ℝ κ => x r * x r)
      (stdGaussian (EuclideanSpace ℝ κ)) := by
  have h2 : MemLp (fun x : EuclideanSpace ℝ κ => x r) 2
      (stdGaussian (EuclideanSpace ℝ κ)) := memLp_coord_stdGaussian r 2 (by norm_num)
  have h := memLp_finProd_one (μ := stdGaussian (EuclideanSpace ℝ κ)) (n := 2)
    (by norm_num) (f := fun _ : Fin 2 => fun x : EuclideanSpace ℝ κ => x r)
    (fun _ => h2)
  rw [memLp_one_iff_integrable] at h
  convert h using 1
  ext x
  simp
  ring

/-- Products of squares of standard Gaussian coordinates are integrable. -/
lemma integrable_coord_sq_mul_coord_sq (r s : κ) :
    Integrable (fun x : EuclideanSpace ℝ κ => (x r * x r) * (x s * x s))
      (stdGaussian (EuclideanSpace ℝ κ)) := by
  have h4 : ∀ t : κ, MemLp (fun x : EuclideanSpace ℝ κ => x t) 4
      (stdGaussian (EuclideanSpace ℝ κ)) :=
    fun t => memLp_coord_stdGaussian t 4 (by norm_num)
  let f : Fin 4 → EuclideanSpace ℝ κ → ℝ :=
    ![fun x => x r, fun x => x r, fun x => x s, fun x => x s]
  have hf : ∀ i, MemLp (f i) (4 : ℝ≥0∞) (stdGaussian (EuclideanSpace ℝ κ)) := by
    intro i
    fin_cases i
    · simpa [f] using h4 r
    · simpa [f] using h4 r
    · simpa [f] using h4 s
    · simpa [f] using h4 s
  have h := memLp_finProd_one (μ := stdGaussian (EuclideanSpace ℝ κ)) (n := 4)
    (by norm_num) hf
  rw [memLp_one_iff_integrable] at h
  convert h using 1
  ext x
  simp [f, Fin.prod_univ_four]
  ring

/-- Squares of coordinates on the product Gaussian space are integrable. -/
lemma integrable_coord_sq_pi (r : {i : κ // ¬ i = p}) :
    Integrable (fun y : {i : κ // ¬ i = p} → ℝ => y r * y r)
      (Measure.pi (fun _ : {i : κ // ¬ i = p} => gaussianReal 0 1)) := by
  have h2 : MemLp (fun y : {i : κ // ¬ i = p} → ℝ => y r) 2
      (Measure.pi (fun _ : {i : κ // ¬ i = p} => gaussianReal 0 1)) :=
    memLp_coord_pi r 2 (by norm_num)
  have h := memLp_finProd_one
    (μ := Measure.pi (fun _ : {i : κ // ¬ i = p} => gaussianReal 0 1)) (n := 2)
    (by norm_num) (f := fun _ : Fin 2 => fun y : {i : κ // ¬ i = p} → ℝ => y r)
    (fun _ => h2)
  rw [memLp_one_iff_integrable] at h
  convert h using 1
  ext y
  simp
  ring

/-- A constant times `t^n`, weighted by the Gaussian density, is integrable on the product
space `(κ' → ℝ) × ℝ`. -/
lemma integrable_density_prod_const (n : ℕ) (c : ℝ) :
    Integrable (fun z : ({i : κ // ¬ i = p} → ℝ) × ℝ =>
        gaussianPDFReal 0 1 z.2 • (c * z.2 ^ n))
      ((Measure.pi (fun _ : {i : κ // ¬ i = p} => gaussianReal 0 1)).prod
        (volume : Measure ℝ)) := by
  have hvol : Integrable (fun t : ℝ => gaussianPDFReal 0 1 t * (c * t ^ n)) := by
    have h := (integrable_gaussianPDFReal_mul_pow n).const_mul c
    refine h.congr (ae_of_all _ fun t => ?_)
    ring
  have h := Integrable.mul_prod
    (μ := Measure.pi (fun _ : {i : κ // ¬ i = p} => gaussianReal 0 1))
    (ν := (volume : Measure ℝ))
    (f := fun _ : {i : κ // ¬ i = p} → ℝ => (1 : ℝ))
    (g := fun t : ℝ => gaussianPDFReal 0 1 t * (c * t ^ n))
    (integrable_const 1) hvol
  refine h.congr (ae_of_all _ fun z => ?_)
  simp [smul_eq_mul]

/-- A square of one remaining coordinate times `t^n ρ(t)` is integrable on the product
space `(κ' → ℝ) × ℝ`. -/
lemma integrable_density_prod_coord_sq (r : {i : κ // ¬ i = p}) (n : ℕ) :
    Integrable (fun z : ({i : κ // ¬ i = p} → ℝ) × ℝ =>
        (z.1 r * z.1 r) * (gaussianPDFReal 0 1 z.2 * z.2 ^ n))
      ((Measure.pi (fun _ : {i : κ // ¬ i = p} => gaussianReal 0 1)).prod
        (volume : Measure ℝ)) := by
  exact Integrable.mul_prod (integrable_coord_sq_pi (p := p) r)
    (integrable_gaussianPDFReal_mul_pow n)

/-- **Fourth mixed moment of standard Gaussian coordinates**:
`E[x_p² x_q²] = 3` if `p = q`, and `1` otherwise. -/
theorem integral_coord_sq_mul_coord_sq :
    ∫ x : EuclideanSpace ℝ κ, (x p * x p) * (x q * x q)
        ∂(stdGaussian (EuclideanSpace ℝ κ)) =
      if p = q then 3 else 1 := by
  let F : EuclideanSpace ℝ κ → ℝ := fun x => x p * (x q * x q)
  let F' : EuclideanSpace ℝ κ → ℝ :=
    fun x => if q = p then 3 * (x p * x p) else x q * x q
  have hderiv : ∀ (y : {i : κ // ¬ i = p} → ℝ) (a : ℝ),
      HasDerivAt (fun t => F (WithLp.toLp 2 (piRecon p t y)))
        (F' (WithLp.toLp 2 (piRecon p a y))) a := by
    intro y a
    by_cases h : q = p
    · have hfun : (fun t => F (WithLp.toLp 2 (piRecon p t y))) = fun t => t ^ 3 := by
        funext t
        simp [F, h, piRecon]
        ring
      have hF' : F' (WithLp.toLp 2 (piRecon p a y)) = 3 * a ^ 2 := by
        simp [F', h, piRecon]
        ring
      rw [hfun, hF']
      convert hasDerivAt_pow 3 a using 1
    · have hfun : (fun t => F (WithLp.toLp 2 (piRecon p t y))) =
          fun t => t * (y ⟨q, h⟩ * y ⟨q, h⟩) := by
        funext t
        simp [F, h, piRecon]
      have hF' : F' (WithLp.toLp 2 (piRecon p a y)) = y ⟨q, h⟩ * y ⟨q, h⟩ := by
        simp [F', h, piRecon]
      rw [hfun, hF']
      simpa using (hasDerivAt_id a).mul_const (y ⟨q, h⟩ * y ⟨q, h⟩)
  have hint1 : Integrable (fun z : ({i : κ // ¬ i = p} → ℝ) × ℝ =>
      gaussianPDFReal 0 1 z.2 • F' (WithLp.toLp 2 (piRecon p z.2 z.1)))
      ((Measure.pi (fun _ : {i : κ // ¬ i = p} => gaussianReal 0 1)).prod
        (volume : Measure ℝ)) := by
    by_cases h : q = p
    · have hEq : (fun z : ({i : κ // ¬ i = p} → ℝ) × ℝ =>
          gaussianPDFReal 0 1 z.2 • F' (WithLp.toLp 2 (piRecon p z.2 z.1))) =
          fun z => gaussianPDFReal 0 1 z.2 • (3 * z.2 ^ 2) := by
        funext z
        simp [F', h, piRecon, smul_eq_mul]
        left
        ring
      rw [hEq]
      exact integrable_density_prod_const (p := p) 2 3
    · have hEq : (fun z : ({i : κ // ¬ i = p} → ℝ) × ℝ =>
          gaussianPDFReal 0 1 z.2 • F' (WithLp.toLp 2 (piRecon p z.2 z.1))) =
          fun z => (z.1 ⟨q, h⟩ * z.1 ⟨q, h⟩) * gaussianPDFReal 0 1 z.2 := by
        funext z
        simp [F', h, piRecon, smul_eq_mul]
        ring
      rw [hEq]
      simpa using integrable_density_prod_coord_sq (p := p) ⟨q, h⟩ 0
  have hint2 : Integrable (fun z : ({i : κ // ¬ i = p} → ℝ) × ℝ =>
      z.2 • (gaussianPDFReal 0 1 z.2 • F (WithLp.toLp 2 (piRecon p z.2 z.1))))
      ((Measure.pi (fun _ : {i : κ // ¬ i = p} => gaussianReal 0 1)).prod
        (volume : Measure ℝ)) := by
    by_cases h : q = p
    · have hEq : (fun z : ({i : κ // ¬ i = p} → ℝ) × ℝ =>
          z.2 • (gaussianPDFReal 0 1 z.2 • F (WithLp.toLp 2 (piRecon p z.2 z.1)))) =
          fun z => gaussianPDFReal 0 1 z.2 • (1 * z.2 ^ 4) := by
        funext z
        simp [F, h, piRecon, smul_eq_mul]
        ring
      rw [hEq]
      exact integrable_density_prod_const (p := p) 4 1
    · have hEq : (fun z : ({i : κ // ¬ i = p} → ℝ) × ℝ =>
          z.2 • (gaussianPDFReal 0 1 z.2 • F (WithLp.toLp 2 (piRecon p z.2 z.1)))) =
          fun z => (z.1 ⟨q, h⟩ * z.1 ⟨q, h⟩) *
            (gaussianPDFReal 0 1 z.2 * z.2 ^ 2) := by
        funext z
        simp [F, h, piRecon, smul_eq_mul]
        ring
      rw [hEq]
      exact integrable_density_prod_coord_sq (p := p) ⟨q, h⟩ 2
  have hbot : ∀ᵐ (y : {i : κ // ¬ i = p} → ℝ)
      ∂(Measure.pi (fun _ : {i : κ // ¬ i = p} => gaussianReal 0 1)),
      Tendsto (fun t => gaussianPDFReal 0 1 t •
        F (WithLp.toLp 2 (piRecon p t y))) atBot (𝓝 0) := by
    filter_upwards with y
    by_cases h : q = p
    · have hfun : (fun t => gaussianPDFReal 0 1 t •
          F (WithLp.toLp 2 (piRecon p t y))) =
          fun t => gaussianPDFReal 0 1 t * t ^ 3 := by
        funext t
        simp [F, h, piRecon, smul_eq_mul]
        left
        ring
      rw [hfun]
      exact tendsto_gaussianPDFReal_mul_pow_atBot 3
    · have hfun : (fun t => gaussianPDFReal 0 1 t •
          F (WithLp.toLp 2 (piRecon p t y))) =
          fun t => (y ⟨q, h⟩ * y ⟨q, h⟩) * (gaussianPDFReal 0 1 t * t) := by
        funext t
        simp [F, h, piRecon, smul_eq_mul]
        ring
      rw [hfun]
      simpa using (tendsto_gaussianPDFReal_mul_pow_atBot 1).const_mul
        (y ⟨q, h⟩ * y ⟨q, h⟩)
  have htop : ∀ᵐ (y : {i : κ // ¬ i = p} → ℝ)
      ∂(Measure.pi (fun _ : {i : κ // ¬ i = p} => gaussianReal 0 1)),
      Tendsto (fun t => gaussianPDFReal 0 1 t •
        F (WithLp.toLp 2 (piRecon p t y))) atTop (𝓝 0) := by
    filter_upwards with y
    by_cases h : q = p
    · have hfun : (fun t => gaussianPDFReal 0 1 t •
          F (WithLp.toLp 2 (piRecon p t y))) =
          fun t => gaussianPDFReal 0 1 t * t ^ 3 := by
        funext t
        simp [F, h, piRecon, smul_eq_mul]
        left
        ring
      rw [hfun]
      exact tendsto_gaussianPDFReal_mul_pow_atTop 3
    · have hfun : (fun t => gaussianPDFReal 0 1 t •
          F (WithLp.toLp 2 (piRecon p t y))) =
          fun t => (y ⟨q, h⟩ * y ⟨q, h⟩) * (gaussianPDFReal 0 1 t * t) := by
        funext t
        simp [F, h, piRecon, smul_eq_mul]
        ring
      rw [hfun]
      simpa using (tendsto_gaussianPDFReal_mul_pow_atTop 1).const_mul
        (y ⟨q, h⟩ * y ⟨q, h⟩)
  have hstein := integral_eval_smul_stdGaussian (κ := κ) p
    (F := F) (F' := F') hderiv hint1 hint2 hbot htop
  have hL : (∫ x : EuclideanSpace ℝ κ, x p • F x
      ∂(stdGaussian (EuclideanSpace ℝ κ))) =
      ∫ x : EuclideanSpace ℝ κ, (x p * x p) * (x q * x q)
        ∂(stdGaussian (EuclideanSpace ℝ κ)) := by
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    simp [F, smul_eq_mul]
    ring
  rw [hL] at hstein
  rw [hstein]
  by_cases h : p = q
  · subst h
    simp only [F', ite_true]
    rw [integral_const_mul, integral_coord_mul_coord p p]
    norm_num
  · have hqp : ¬ q = p := fun h' => h h'.symm
    simp only [F', hqp, ite_false, h]
    rw [integral_coord_mul_coord q q]
    norm_num

end FourthMoment

end

end GUEStrongConvergence
