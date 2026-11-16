/-
# Wick recursion for complex GUE entries

This file proves the joint Gaussian Wick recursion for the actual complex GUE entries, with
the covariance kernel of equation (1.2) (no complex conjugation):

`E[G_e G_f] = δ_{ij} δ_{ad} δ_{bc} / N` for `e = (i,a,b)`, `f = (j,c,d)`.

Writing an entry as the complex linear form
`G_e = N^{-1/2} (α x_e + β x_{swap e})` in the real Gaussian coordinates
(`x_e` is the coordinate `(i,(a,b))`, `swap e = (i,(b,a))`), we prove:

* `gueProd l` is integrable for every finite list of entries (all Gaussian moments);
* the coordinate derivative `gueProdDeriv p l` is the sum over the occurrences of the
  coordinate `p` of the coefficient times the product with that entry removed;
* the Stein/Wick recurrence
  `E[G_e ∏_{f ∈ l} G_f] = ∑_{k} E[G_e G_{l_k}] E[∏_{j ≠ k} G_{l_j}]`,
  with the existing covariance `integral_gueMatrix_mul`, and with no recurrence or covariance
  bound assumed.

The analytic hypotheses of the coordinate Stein identity are discharged by expanding a
product of entries into a finite sum of coordinate monomials (`gueExpand`) and reusing the
one-dimensional density moments and the monomial integrability of `GaussianWick`.

The recurrence is stated with `gueCov e f`, whose definition is exactly the kernel
`if e.1 = f.1 ∧ e.2.1 = f.2.2 ∧ e.2.2 = f.2.1 then N⁻¹ else 0`; the two-entry identity
`integral_gueEntry_mul_gueEntry` proves it equals `E[G_e G_f]` using the existing covariance
theorem of `GUEModel`.  Empty lists are covered: the recurrence gives `E[G_e] = 0`
(`integral_gueEntry_eq_zero`).

All statements assume only `[Fintype ι] [DecidableEq ι]`; the matrix size `N` is arbitrary
(including `N = 0`) and no positivity of `N` is required beyond the definition of the
normalization.
-/
import Mathlib.Probability.Independence.InfinitePi
import GUEStrongConvergence.Probability.GaussianWick
import GUEStrongConvergence.Probability.GUEModel

open MeasureTheory ProbabilityTheory Filter
open scoped RealInnerProductSpace Matrix ENNReal Topology

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace GUEStrongConvergence

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {N : ℕ}

/-- The entry index type is the same as the Gaussian coordinate index. -/
abbrev GUEEntry (ι : Type*) (N : ℕ) := GUECoord ι N

/-- The transposed coordinate index: `(i,(a,b)) ↦ (i,(b,a))`. -/
def gueSwap (e : GUEEntry ι N) : GUEEntry ι N := (e.1, (e.2.2, e.2.1))

@[simp] lemma gueSwap_swap (e : GUEEntry ι N) : gueSwap (gueSwap e) = e := by
  simp [gueSwap]

/-- The complex GUE entry indexed by `e = (i,(a,b))`. -/
def gueEntry (e : GUEEntry ι N) (x : EuclideanSpace ℝ (GUECoord ι N)) : ℂ :=
  gueMatrix x e.1 e.2.1 e.2.2

/-- The coefficient of the coordinate `x_e` in the entry `G_e`. -/
def gueAlphaScaled : ℂ := (gueScale N : ℂ) * gueAlpha

/-- The coefficient of the coordinate `x_{swap e}` in the entry `G_e`. -/
def gueBetaScaled : ℂ := (gueScale N : ℂ) * gueBeta

lemma gueEntry_eq (e : GUEEntry ι N) (x : EuclideanSpace ℝ (GUECoord ι N)) :
    gueEntry e x = gueAlphaScaled (N := N) * ((x e : ℝ) : ℂ) +
      gueBetaScaled (N := N) * ((x (gueSwap e) : ℝ) : ℂ) := by
  simp [gueEntry, gueAlphaScaled, gueBetaScaled, gueMatrix, gueUnscaled, gueSwap]
  ring

/-- The derivative of `G_e` in the direction of the real coordinate `p`. -/
def gueCoeff (p e : GUEEntry ι N) : ℂ :=
  (gueScale N : ℂ) * (gueAlpha * (if p = e then (1 : ℂ) else 0) +
    gueBeta * (if p = gueSwap e then (1 : ℂ) else 0))

/-- The product of the GUE entries in the list `l`. -/
def gueProd (l : List (GUEEntry ι N)) (x : EuclideanSpace ℝ (GUECoord ι N)) : ℂ :=
  (l.map (fun e => gueEntry e x)).prod

@[simp] lemma gueProd_nil (x : EuclideanSpace ℝ (GUECoord ι N)) : gueProd [] x = 1 := rfl

@[simp] lemma gueProd_cons (e : GUEEntry ι N) (l : List (GUEEntry ι N))
    (x : EuclideanSpace ℝ (GUECoord ι N)) :
    gueProd (e :: l) x = gueEntry e x * gueProd l x := by
  simp [gueProd]

/-- The coordinate derivative of a product of GUE entries. -/
def gueProdDeriv (p : GUEEntry ι N) :
    List (GUEEntry ι N) → EuclideanSpace ℝ (GUECoord ι N) → ℂ
  | [], _ => 0
  | e :: l, x => gueCoeff p e * gueProd l x + gueEntry e x * gueProdDeriv p l x

@[simp] lemma gueProdDeriv_nil (p : GUEEntry ι N)
    (x : EuclideanSpace ℝ (GUECoord ι N)) : gueProdDeriv p [] x = 0 := rfl

@[simp] lemma gueProdDeriv_cons (p e : GUEEntry ι N) (l : List (GUEEntry ι N))
    (x : EuclideanSpace ℝ (GUECoord ι N)) :
    gueProdDeriv p (e :: l) x =
      gueCoeff p e * gueProd l x + gueEntry e x * gueProdDeriv p l x := rfl

/-- Derivative of a coordinate along the `piRecon` parameterization. -/
lemma hasDerivAt_eval_piRecon (p q : GUEEntry ι N) (y : {i : GUEEntry ι N // ¬ i = p} → ℝ)
    (a : ℝ) :
    HasDerivAt (fun t => (WithLp.toLp 2 (piRecon p t y)) q)
      (if p = q then (1 : ℝ) else 0) a := by
  by_cases h : q = p
  · have hfun : (fun t : ℝ => (WithLp.toLp 2 (piRecon p t y)) q) = fun t => t := by
      funext t
      simp [piRecon, h]
    rw [hfun]
    have hif : (if p = q then (1 : ℝ) else 0) = 1 := by simp [h]
    rw [hif]
    exact hasDerivAt_id a
  · have hfun : (fun t : ℝ => (WithLp.toLp 2 (piRecon p t y)) q) =
        fun _ => y ⟨q, h⟩ := by
      funext t
      simp [piRecon, h]
    rw [hfun]
    have h' : ¬ p = q := fun hp => h hp.symm
    have hif : (if p = q then (1 : ℝ) else 0) = 0 := by simp [h']
    rw [hif]
    exact hasDerivAt_const a (y ⟨q, h⟩)

/-- Derivative of a GUE entry along the `piRecon` parameterization. -/
lemma hasDerivAt_gueEntry (p e : GUEEntry ι N)
    (y : {i : GUEEntry ι N // ¬ i = p} → ℝ) (a : ℝ) :
    HasDerivAt (fun t => gueEntry e (WithLp.toLp 2 (piRecon p t y)))
      (gueCoeff p e) a := by
  have h1 := HasDerivAt.const_mul (gueAlphaScaled (N := N))
    (hasDerivAt_eval_piRecon p e y a).ofReal_comp
  have h2 := HasDerivAt.const_mul (gueBetaScaled (N := N))
    (hasDerivAt_eval_piRecon p (gueSwap e) y a).ofReal_comp
  have h := h1.add h2
  have hfun : (fun t => gueEntry e (WithLp.toLp 2 (piRecon p t y))) =
      fun t => gueAlphaScaled (N := N) * ((WithLp.toLp 2 (piRecon p t y) e : ℝ) : ℂ) +
        gueBetaScaled (N := N) * ((WithLp.toLp 2 (piRecon p t y) (gueSwap e) : ℝ) : ℂ) := by
    funext t
    rw [gueEntry_eq]
  rw [hfun]
  refine h.congr_deriv ?_
  simp only [gueCoeff, gueAlphaScaled, gueBetaScaled]
  split_ifs <;> (push_cast; ring)

/-- Derivative of a product of GUE entries. -/
lemma hasDerivAt_gueProd (p : GUEEntry ι N) (l : List (GUEEntry ι N))
    (y : {i : GUEEntry ι N // ¬ i = p} → ℝ) (a : ℝ) :
    HasDerivAt (fun t => gueProd l (WithLp.toLp 2 (piRecon p t y)))
      (gueProdDeriv p l (WithLp.toLp 2 (piRecon p a y))) a := by
  induction l with
  | nil => simpa [gueProd, gueProdDeriv] using hasDerivAt_const a (1 : ℂ)
  | cons e l ih =>
    have he := hasDerivAt_gueEntry p e y a
    have h := he.mul ih
    have hfun : (fun t => gueEntry e (WithLp.toLp 2 (piRecon p t y)) *
        gueProd l (WithLp.toLp 2 (piRecon p t y))) =
        fun t => gueProd (e :: l) (WithLp.toLp 2 (piRecon p t y)) := by
      funext t
      rw [gueProd_cons]
    rw [← hfun]
    refine h.congr_deriv ?_
    rw [gueProdDeriv_cons]

/-- The recursive derivative is the sum over the occurrences of the coordinate. -/
lemma gueProdDeriv_eq_sum (p : GUEEntry ι N) (l : List (GUEEntry ι N))
    (x : EuclideanSpace ℝ (GUECoord ι N)) :
    gueProdDeriv p l x =
      ∑ k : Fin l.length,
        gueCoeff p (l.get k) * gueProd (l.eraseIdx k) x := by
  induction l with
  | nil => simp [gueProdDeriv]
  | cons e l ih =>
    rw [gueProdDeriv_cons, ih]
    change gueCoeff p e * gueProd l x +
        gueEntry e x * (∑ k : Fin l.length,
          gueCoeff p (l.get k) * gueProd (l.eraseIdx k) x) =
      ∑ k : Fin (l.length + 1),
        gueCoeff p ((e :: l).get k) * gueProd ((e :: l).eraseIdx k) x
    rw [Fin.sum_univ_succ, Finset.mul_sum]
    simp only [List.get_cons_zero]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    change gueEntry e x * (gueCoeff p (l.get k) * gueProd (l.eraseIdx k) x) =
      gueCoeff p (l.get k) * gueProd (e :: l.eraseIdx k) x
    rw [gueProd_cons]
    ring

/-! ### Integrability of arbitrary finite products of entries -/

/-- Every GUE entry is in `L^n` for every `n ≥ 1` (it is a complex linear form in two
Gaussian coordinates). -/
lemma memLp_gueEntry (e : GUEEntry ι N) (n : ℕ) (hn : 1 ≤ n) :
    MemLp (gueEntry e) (n : ℝ≥0∞)
      (stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) := by
  have h1 := MemLp.ofReal (K := ℂ) (memLp_coord_stdGaussian e n hn)
  have h2 := MemLp.ofReal (K := ℂ) (memLp_coord_stdGaussian (gueSwap e) n hn)
  have h := (h1.const_mul (gueAlphaScaled (N := N))).add
    (h2.const_mul (gueBetaScaled (N := N)))
  convert h using 1
  ext x
  rw [gueEntry_eq]
  simp [Pi.add_apply]

/-- A product of `n` complex functions, each in `L^n`, is in `L^1`. -/
lemma memLp_finProd_one_complex {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {n : ℕ} (hn : 1 ≤ n) {f : Fin n → α → ℂ}
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

/-- The product of entries as a product over positions. -/
lemma gueProd_eq_prod_get (l : List (GUEEntry ι N))
    (x : EuclideanSpace ℝ (GUECoord ι N)) :
    gueProd l x = ∏ i : Fin l.length, gueEntry (l.get i) x := by
  induction l with
  | nil => simp [gueProd]
  | cons e l ih =>
    rw [gueProd_cons, ih]
    change gueEntry e x * (∏ i : Fin l.length, gueEntry (l.get i) x) =
      ∏ i : Fin (l.length + 1), gueEntry ((e :: l).get i) x
    rw [Fin.prod_univ_succ]
    simp

/-- A finite product of GUE entries is in `L^1`. -/
lemma memLp_gueProd_one (l : List (GUEEntry ι N)) :
    MemLp (gueProd l) 1
      (stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) := by
  cases l with
  | nil =>
    convert memLp_const (1 : ℂ) using 1
    · ext x
      simp [gueProd]
    · infer_instance
  | cons e l =>
    have hlen : 1 ≤ (e :: l).length := by simp
    have hf : ∀ i : Fin (e :: l).length,
        MemLp (fun x : EuclideanSpace ℝ (GUECoord ι N) =>
          gueEntry ((e :: l).get i) x) ((e :: l).length : ℝ≥0∞)
          (stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) :=
      fun i => memLp_gueEntry _ _ hlen
    have h := memLp_finProd_one_complex hlen hf
    convert h using 1
    ext x
    rw [gueProd_eq_prod_get]

/-- **Every finite product of complex GUE entries is integrable.** -/
theorem integrable_gueProd (l : List (GUEEntry ι N)) :
    Integrable (gueProd l) (stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) := by
  cases l with
  | nil =>
    convert integrable_const (1 : ℂ) using 1
    · ext x
      simp [gueProd]
    · infer_instance
  | cons e l =>
    have h := memLp_gueProd_one (e :: l)
    exact memLp_one_iff_integrable.mp h

/-! ### Expansion of an entry product into coordinate monomials -/

/-- Recursive expansion of a product of GUE entries into complex multiples of coordinate
monomials. -/
def gueExpand : List (GUEEntry ι N) → List (ℂ × List (GUEEntry ι N))
  | [] => [(1, [])]
  | e :: l => (gueExpand l).flatMap fun t =>
      [(t.1 * gueAlphaScaled (N := N), e :: t.2),
       (t.1 * gueBetaScaled (N := N), gueSwap e :: t.2)]

/-- Evaluation of an expanded list of monomials. -/
def gueExpandEval (E : List (ℂ × List (GUEEntry ι N)))
    (x : EuclideanSpace ℝ (GUECoord ι N)) : ℂ :=
  (E.map fun t => t.1 * ((coordProd t.2 x : ℝ) : ℂ)).sum

@[simp] lemma gueExpandEval_nil (x : EuclideanSpace ℝ (GUECoord ι N)) :
    gueExpandEval [] x = 0 := rfl

@[simp] lemma gueExpandEval_cons (c : ℂ) (m : List (GUEEntry ι N))
    (E : List (ℂ × List (GUEEntry ι N))) (x : EuclideanSpace ℝ (GUECoord ι N)) :
    gueExpandEval ((c, m) :: E) x =
      c * ((coordProd m x : ℝ) : ℂ) + gueExpandEval E x := by
  simp [gueExpandEval]

lemma gueExpandEval_append (E₁ E₂ : List (ℂ × List (GUEEntry ι N)))
    (x : EuclideanSpace ℝ (GUECoord ι N)) :
    gueExpandEval (E₁ ++ E₂) x = gueExpandEval E₁ x + gueExpandEval E₂ x := by
  simp [gueExpandEval, List.map_append, List.sum_append]

lemma gueExpandEval_flatMap {α : Type*} (l : List α)
    (f : α → List (ℂ × List (GUEEntry ι N)))
    (x : EuclideanSpace ℝ (GUECoord ι N)) :
    gueExpandEval (l.flatMap f) x =
      (l.map (fun a => gueExpandEval (f a) x)).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.flatMap_cons, gueExpandEval_append, ih]
    simp

lemma gueExpandEval_gueExpand_cons (e : GUEEntry ι N) (l : List (GUEEntry ι N))
    (x : EuclideanSpace ℝ (GUECoord ι N)) :
    gueExpandEval (gueExpand (e :: l)) x =
      gueEntry e x * gueExpandEval (gueExpand l) x := by
  rw [gueExpand, gueExpandEval_flatMap]
  have hterm : ∀ t : ℂ × List (GUEEntry ι N),
      gueExpandEval
        [(t.1 * gueAlphaScaled (N := N), e :: t.2),
         (t.1 * gueBetaScaled (N := N), gueSwap e :: t.2)] x =
      t.1 * (gueEntry e x * ((coordProd t.2 x : ℝ) : ℂ)) := by
    intro t
    rw [gueExpandEval_cons, gueExpandEval_cons, gueExpandEval_nil]
    rw [coordProd_cons, coordProd_cons]
    rw [gueEntry_eq]
    push_cast
    ring
  simp only [hterm]
  have hmap : (fun a : ℂ × List (GUEEntry ι N) =>
        a.1 * (gueEntry e x * ((coordProd a.2 x : ℝ) : ℂ))) =
      fun a => gueEntry e x * (a.1 * ((coordProd a.2 x : ℝ) : ℂ)) := by
    funext a
    ring
  rw [hmap, List.sum_map_mul_left]
  rfl

lemma gueProd_eq_gueExpand (l : List (GUEEntry ι N))
    (x : EuclideanSpace ℝ (GUECoord ι N)) :
    gueProd l x = gueExpandEval (gueExpand l) x := by
  induction l with
  | nil => simp [gueProd, gueExpand, gueExpandEval]
  | cons e l ih =>
    rw [gueProd_cons, ih, gueExpandEval_gueExpand_cons]

/-- Number of occurrences of the coordinate `p` in a list of entries, using `countP` so that
the instance is independent of the `BEq` choice. -/
def gueCount (p : GUEEntry ι N) (m : List (GUEEntry ι N)) : ℕ :=
  m.countP (fun q => decide (q = p))

lemma coordProdOff_cons (p e : GUEEntry ι N) (l : List (GUEEntry ι N))
    (y : {i : GUEEntry ι N // ¬ i = p} → ℝ) :
    coordProdOff p (e :: l) y =
      (if h : e = p then 1 else y ⟨e, h⟩) * coordProdOff p l y := by
  rw [coordProdOff, coordProdOff]
  change (∏ i : Fin (l.length + 1),
      if h : (e :: l).get i = p then 1 else y ⟨(e :: l).get i, h⟩) =
    (if h : e = p then 1 else y ⟨e, h⟩) *
      ∏ i : Fin l.length,
        if h : l.get i = p then 1 else y ⟨l.get i, h⟩
  rw [Fin.prod_univ_succ]
  congr 1

/-- Decomposition of a coordinate monomial along `piRecon`, with `gueCount`. -/
lemma coordProd_piRecon_gueCount (p : GUEEntry ι N) (m : List (GUEEntry ι N))
    (t : ℝ) (y : {i : GUEEntry ι N // ¬ i = p} → ℝ) :
    coordProd m (WithLp.toLp 2 (piRecon p t y)) =
      t ^ gueCount p m * coordProdOff p m y := by
  induction m with
  | nil => simp [coordProd, coordProdOff, gueCount]
  | cons e l ih =>
    rw [coordProd_cons, ih, coordProdOff_cons]
    have hq : (WithLp.toLp 2 (piRecon p t y)) e =
        if h : e = p then t else y ⟨e, h⟩ := by
      simp [piRecon]
    rw [hq]
    by_cases h : e = p
    · have hcount : gueCount p (e :: l) = gueCount p l + 1 := by
        simp [gueCount, h]
      rw [hcount, pow_succ]
      simp [h]
      ring
    · have hcount : gueCount p (e :: l) = gueCount p l := by
        simp [gueCount, h]
      rw [hcount]
      simp [h]
      ring

/-! ### Analytic hypotheses for the coordinate Stein identity -/

/-- Density-weighted integrability of a single expansion monomial. -/
lemma integrable_density_expandTerm (p : GUEEntry ι N) (c : ℂ)
    (m : List (GUEEntry ι N)) :
    Integrable (fun z : ({i : GUEEntry ι N // ¬ i = p} → ℝ) × ℝ =>
        gaussianPDFReal 0 1 z.2 •
          (c * ((coordProd m (WithLp.toLp 2 (piRecon p z.2 z.1)) : ℝ) : ℂ)))
      ((Measure.pi (fun _ : {i : GUEEntry ι N // ¬ i = p} => gaussianReal 0 1)).prod
        (volume : Measure ℝ)) := by
  have hreal := integrable_density_prod_coordProdOff (p := p) m (gueCount p m)
  have hc : Integrable (fun z : ({i : GUEEntry ι N // ¬ i = p} → ℝ) × ℝ =>
      ((coordProdOff p m z.1 *
        (gaussianPDFReal 0 1 z.2 * z.2 ^ gueCount p m) : ℝ) : ℂ))
      ((Measure.pi (fun _ : {i : GUEEntry ι N // ¬ i = p} => gaussianReal 0 1)).prod
        (volume : Measure ℝ)) :=
    Complex.ofRealCLM.integrable_comp hreal
  have hcc := hc.const_mul c
  refine hcc.congr (ae_of_all _ fun z => ?_)
  beta_reduce
  rw [coordProd_piRecon_gueCount]
  simp only [Complex.real_smul]
  push_cast
  ring_nf

/-- Density-weighted integrability of an expansion monomial with an extra `z.2` factor. -/
lemma integrable_density_t_expandTerm (p : GUEEntry ι N) (c : ℂ)
    (m : List (GUEEntry ι N)) :
    Integrable (fun z : ({i : GUEEntry ι N // ¬ i = p} → ℝ) × ℝ =>
        z.2 • (gaussianPDFReal 0 1 z.2 •
          (c * ((coordProd m (WithLp.toLp 2 (piRecon p z.2 z.1)) : ℝ) : ℂ))))
      ((Measure.pi (fun _ : {i : GUEEntry ι N // ¬ i = p} => gaussianReal 0 1)).prod
        (volume : Measure ℝ)) := by
  have hreal := integrable_density_prod_coordProdOff (p := p) m (gueCount p m + 1)
  have hc : Integrable (fun z : ({i : GUEEntry ι N // ¬ i = p} → ℝ) × ℝ =>
      ((coordProdOff p m z.1 *
        (gaussianPDFReal 0 1 z.2 * z.2 ^ (gueCount p m + 1)) : ℝ) : ℂ))
      ((Measure.pi (fun _ : {i : GUEEntry ι N // ¬ i = p} => gaussianReal 0 1)).prod
        (volume : Measure ℝ)) :=
    Complex.ofRealCLM.integrable_comp hreal
  have hcc := hc.const_mul c
  refine hcc.congr (ae_of_all _ fun z => ?_)
  beta_reduce
  rw [coordProd_piRecon_gueCount]
  simp only [Complex.real_smul]
  push_cast
  ring_nf

/-- Boundary decay of a single expansion monomial at `atBot`. -/
lemma tendsto_density_expandTerm_atBot (p : GUEEntry ι N) (c : ℂ)
    (m : List (GUEEntry ι N)) (y : {i : GUEEntry ι N // ¬ i = p} → ℝ) :
    Tendsto (fun t : ℝ => gaussianPDFReal 0 1 t •
      (c * ((coordProd m (WithLp.toLp 2 (piRecon p t y)) : ℝ) : ℂ))) atBot (𝓝 0) := by
  have hreal := tendsto_gaussianPDFReal_mul_pow_atBot (gueCount p m)
  have hcomplex : Tendsto (fun t : ℝ =>
      ((gaussianPDFReal 0 1 t * t ^ gueCount p m : ℝ) : ℂ)) atBot (𝓝 0) := by
    have := (Complex.ofRealCLM.continuous.tendsto (0 : ℝ)).comp hreal
    simpa only [Function.comp_def, Complex.ofRealCLM_apply, Complex.ofReal_mul,
      Complex.ofReal_pow, map_zero] using this
  have h := Tendsto.const_mul (c * ((coordProdOff p m y : ℝ) : ℂ)) hcomplex
  have h' : Tendsto (fun t : ℝ =>
      c * ((coordProdOff p m y : ℝ) : ℂ) *
        ((gaussianPDFReal 0 1 t * t ^ gueCount p m : ℝ) : ℂ)) atBot (𝓝 0) := by
    simpa using h
  refine Tendsto.congr' (Filter.Eventually.of_forall fun t => ?_) h'
  beta_reduce
  rw [coordProd_piRecon_gueCount]
  simp only [Complex.real_smul]
  push_cast
  ring_nf

/-- Boundary decay of a single expansion monomial at `atTop`. -/
lemma tendsto_density_expandTerm_atTop (p : GUEEntry ι N) (c : ℂ)
    (m : List (GUEEntry ι N)) (y : {i : GUEEntry ι N // ¬ i = p} → ℝ) :
    Tendsto (fun t : ℝ => gaussianPDFReal 0 1 t •
      (c * ((coordProd m (WithLp.toLp 2 (piRecon p t y)) : ℝ) : ℂ))) atTop (𝓝 0) := by
  have hreal := tendsto_gaussianPDFReal_mul_pow_atTop (gueCount p m)
  have hcomplex : Tendsto (fun t : ℝ =>
      ((gaussianPDFReal 0 1 t * t ^ gueCount p m : ℝ) : ℂ)) atTop (𝓝 0) := by
    have := (Complex.ofRealCLM.continuous.tendsto (0 : ℝ)).comp hreal
    simpa only [Function.comp_def, Complex.ofRealCLM_apply, Complex.ofReal_mul,
      Complex.ofReal_pow, map_zero] using this
  have h := Tendsto.const_mul (c * ((coordProdOff p m y : ℝ) : ℂ)) hcomplex
  have h' : Tendsto (fun t : ℝ =>
      c * ((coordProdOff p m y : ℝ) : ℂ) *
        ((gaussianPDFReal 0 1 t * t ^ gueCount p m : ℝ) : ℂ)) atTop (𝓝 0) := by
    simpa using h
  refine Tendsto.congr' (Filter.Eventually.of_forall fun t => ?_) h'
  beta_reduce
  rw [coordProd_piRecon_gueCount]
  simp only [Complex.real_smul]
  push_cast
  ring_nf

/-- Density-weighted integrability of an expanded product. -/
lemma integrable_density_gueExpandEval (p : GUEEntry ι N)
    (E : List (ℂ × List (GUEEntry ι N))) :
    Integrable (fun z : ({i : GUEEntry ι N // ¬ i = p} → ℝ) × ℝ =>
        gaussianPDFReal 0 1 z.2 •
          gueExpandEval E (WithLp.toLp 2 (piRecon p z.2 z.1)))
      ((Measure.pi (fun _ : {i : GUEEntry ι N // ¬ i = p} => gaussianReal 0 1)).prod
        (volume : Measure ℝ)) := by
  induction E with
  | nil => simp [gueExpandEval]
  | cons t E ih =>
    obtain ⟨c, m⟩ := t
    have h1 := integrable_density_expandTerm (p := p) c m
    have h := h1.add ih
    refine h.congr (ae_of_all _ fun z => ?_)
    simp only [gueExpandEval_cons, Pi.add_apply, smul_add]

/-- Density-weighted integrability of an expanded product with an extra `z.2` factor. -/
lemma integrable_density_t_gueExpandEval (p : GUEEntry ι N)
    (E : List (ℂ × List (GUEEntry ι N))) :
    Integrable (fun z : ({i : GUEEntry ι N // ¬ i = p} → ℝ) × ℝ =>
        z.2 • (gaussianPDFReal 0 1 z.2 •
          gueExpandEval E (WithLp.toLp 2 (piRecon p z.2 z.1))))
      ((Measure.pi (fun _ : {i : GUEEntry ι N // ¬ i = p} => gaussianReal 0 1)).prod
        (volume : Measure ℝ)) := by
  induction E with
  | nil => simp [gueExpandEval]
  | cons t E ih =>
    obtain ⟨c, m⟩ := t
    have h1 := integrable_density_t_expandTerm (p := p) c m
    have h := h1.add ih
    refine h.congr (ae_of_all _ fun z => ?_)
    simp only [gueExpandEval_cons, Pi.add_apply, smul_add]

/-- Boundary decay of an expanded product at `atBot`. -/
lemma tendsto_density_gueExpandEval_atBot (p : GUEEntry ι N)
    (E : List (ℂ × List (GUEEntry ι N)))
    (y : {i : GUEEntry ι N // ¬ i = p} → ℝ) :
    Tendsto (fun t : ℝ => gaussianPDFReal 0 1 t •
      gueExpandEval E (WithLp.toLp 2 (piRecon p t y))) atBot (𝓝 0) := by
  induction E with
  | nil => simp [gueExpandEval]
  | cons t E ih =>
    obtain ⟨c, m⟩ := t
    have h1 := tendsto_density_expandTerm_atBot (p := p) c m y
    have h := h1.add ih
    have h' : Tendsto (fun s : ℝ => gaussianPDFReal 0 1 s •
        (c * ((coordProd m (WithLp.toLp 2 (piRecon p s y)) : ℝ) : ℂ)) +
        gaussianPDFReal 0 1 s • gueExpandEval E (WithLp.toLp 2 (piRecon p s y)))
        atBot (𝓝 0) := by simpa using h
    refine Tendsto.congr' (Filter.Eventually.of_forall fun s => ?_) h'
    simp only [gueExpandEval_cons, smul_add]

/-- Boundary decay of an expanded product at `atTop`. -/
lemma tendsto_density_gueExpandEval_atTop (p : GUEEntry ι N)
    (E : List (ℂ × List (GUEEntry ι N)))
    (y : {i : GUEEntry ι N // ¬ i = p} → ℝ) :
    Tendsto (fun t : ℝ => gaussianPDFReal 0 1 t •
      gueExpandEval E (WithLp.toLp 2 (piRecon p t y))) atTop (𝓝 0) := by
  induction E with
  | nil => simp [gueExpandEval]
  | cons t E ih =>
    obtain ⟨c, m⟩ := t
    have h1 := tendsto_density_expandTerm_atTop (p := p) c m y
    have h := h1.add ih
    have h' : Tendsto (fun s : ℝ => gaussianPDFReal 0 1 s •
        (c * ((coordProd m (WithLp.toLp 2 (piRecon p s y)) : ℝ) : ℂ)) +
        gaussianPDFReal 0 1 s • gueExpandEval E (WithLp.toLp 2 (piRecon p s y)))
        atTop (𝓝 0) := by simpa using h
    refine Tendsto.congr' (Filter.Eventually.of_forall fun s => ?_) h'
    simp only [gueExpandEval_cons, smul_add]

/-- Density-weighted integrability of a product of entries. -/
lemma integrable_density_gueProd (p : GUEEntry ι N) (l : List (GUEEntry ι N)) :
    Integrable (fun z : ({i : GUEEntry ι N // ¬ i = p} → ℝ) × ℝ =>
        gaussianPDFReal 0 1 z.2 •
          gueProd l (WithLp.toLp 2 (piRecon p z.2 z.1)))
      ((Measure.pi (fun _ : {i : GUEEntry ι N // ¬ i = p} => gaussianReal 0 1)).prod
        (volume : Measure ℝ)) := by
  refine (integrable_density_gueExpandEval p (gueExpand l)).congr
    (ae_of_all _ fun z => ?_)
  simp only [gueProd_eq_gueExpand]

/-- Density-weighted integrability of a product of entries with an extra `z.2` factor. -/
lemma integrable_density_t_gueProd (p : GUEEntry ι N) (l : List (GUEEntry ι N)) :
    Integrable (fun z : ({i : GUEEntry ι N // ¬ i = p} → ℝ) × ℝ =>
        z.2 • (gaussianPDFReal 0 1 z.2 •
          gueProd l (WithLp.toLp 2 (piRecon p z.2 z.1))))
      ((Measure.pi (fun _ : {i : GUEEntry ι N // ¬ i = p} => gaussianReal 0 1)).prod
        (volume : Measure ℝ)) := by
  refine (integrable_density_t_gueExpandEval p (gueExpand l)).congr
    (ae_of_all _ fun z => ?_)
  simp only [gueProd_eq_gueExpand]

/-- Boundary decay of a product of entries at `atBot`. -/
lemma tendsto_density_gueProd_atBot (p : GUEEntry ι N)
    (l : List (GUEEntry ι N)) (y : {i : GUEEntry ι N // ¬ i = p} → ℝ) :
    Tendsto (fun t : ℝ => gaussianPDFReal 0 1 t •
      gueProd l (WithLp.toLp 2 (piRecon p t y))) atBot (𝓝 0) := by
  refine Tendsto.congr' (Filter.Eventually.of_forall fun t => ?_)
    (tendsto_density_gueExpandEval_atBot p (gueExpand l) y)
  simp only [gueProd_eq_gueExpand]

/-- Boundary decay of a product of entries at `atTop`. -/
lemma tendsto_density_gueProd_atTop (p : GUEEntry ι N)
    (l : List (GUEEntry ι N)) (y : {i : GUEEntry ι N // ¬ i = p} → ℝ) :
    Tendsto (fun t : ℝ => gaussianPDFReal 0 1 t •
      gueProd l (WithLp.toLp 2 (piRecon p t y))) atTop (𝓝 0) := by
  refine Tendsto.congr' (Filter.Eventually.of_forall fun t => ?_)
    (tendsto_density_gueExpandEval_atTop p (gueExpand l) y)
  simp only [gueProd_eq_gueExpand]

/-- Integrability of `x_r` times an expanded product on the standard Gaussian space. -/
lemma integrable_coord_mul_gueExpandEval (r : GUEEntry ι N)
    (E : List (ℂ × List (GUEEntry ι N))) :
    Integrable (fun x : EuclideanSpace ℝ (GUECoord ι N) =>
        (x r : ℂ) * gueExpandEval E x)
      (stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) := by
  induction E with
  | nil => simp [gueExpandEval]
  | cons t E ih =>
    obtain ⟨c, m⟩ := t
    have hm : Integrable (fun x : EuclideanSpace ℝ (GUECoord ι N) =>
        ((coordProd (r :: m) x : ℝ) : ℂ))
        (stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) :=
      Complex.ofRealCLM.integrable_comp (integrable_coordProd_stdGaussian (r :: m))
    have h1 : Integrable (fun x : EuclideanSpace ℝ (GUECoord ι N) =>
        c * ((coordProd (r :: m) x : ℝ) : ℂ))
        (stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) := hm.const_mul c
    have h := h1.add ih
    refine h.congr (ae_of_all _ fun x => ?_)
    simp only [gueExpandEval_cons, coordProd_cons, Pi.add_apply]
    push_cast
    ring

/-- Integrability of `x_r` times a product of GUE entries. -/
lemma integrable_coord_mul_gueProd (r : GUEEntry ι N) (l : List (GUEEntry ι N)) :
    Integrable (fun x : EuclideanSpace ℝ (GUECoord ι N) =>
        (x r : ℂ) * gueProd l x)
      (stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) := by
  refine (integrable_coord_mul_gueExpandEval r (gueExpand l)).congr
    (ae_of_all _ fun x => ?_)
  simp only [gueProd_eq_gueExpand]


/-- The covariance kernel of two GUE entries (no complex conjugation). -/
def gueCov (e f : GUEEntry ι N) : ℂ :=
  if e.1 = f.1 ∧ e.2.1 = f.2.2 ∧ e.2.2 = f.2.1 then ((N : ℝ)⁻¹ : ℂ) else 0

/-- Single-entry Stein identity: the first coordinate moment of an entry is its derivative
coefficient. -/
lemma integral_coord_mul_gueEntry (r f : GUEEntry ι N) :
    ∫ x : EuclideanSpace ℝ (GUECoord ι N), x r • gueEntry f x
        ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) = gueCoeff r f := by
  have hderiv : ∀ (y : {i : GUEEntry ι N // ¬ i = r} → ℝ) (a : ℝ),
      HasDerivAt (fun t => gueEntry f (WithLp.toLp 2 (piRecon r t y)))
        (gueCoeff r f) a :=
    fun y a => hasDerivAt_gueEntry r f y a
  have hint1 : Integrable (fun z : ({i : GUEEntry ι N // ¬ i = r} → ℝ) × ℝ =>
      gaussianPDFReal 0 1 z.2 • gueCoeff r f)
      ((Measure.pi (fun _ : {i : GUEEntry ι N // ¬ i = r} => gaussianReal 0 1)).prod
        (volume : Measure ℝ)) := by
    have hρreal : Integrable (fun t : ℝ => gaussianPDFReal 0 1 t)
        (volume : Measure ℝ) := by
      simpa using integrable_gaussianPDFReal_mul_pow 0
    have hρ : Integrable (fun t : ℝ => ((gaussianPDFReal 0 1 t : ℝ) : ℂ))
        (volume : Measure ℝ) :=
      Complex.ofRealCLM.integrable_comp hρreal
    have hvol : Integrable (fun t : ℝ => gaussianPDFReal 0 1 t • gueCoeff r f)
        (volume : Measure ℝ) := by
      refine (hρ.const_mul (gueCoeff r f)).congr (ae_of_all _ fun t => ?_)
      beta_reduce
      rw [show gaussianPDFReal 0 1 t • gueCoeff r f =
        ((gaussianPDFReal 0 1 t : ℝ) : ℂ) * gueCoeff r f from Complex.real_smul]
      ring
    have h := Integrable.mul_prod
      (μ := Measure.pi (fun _ : {i : GUEEntry ι N // ¬ i = r} => gaussianReal 0 1))
      (ν := (volume : Measure ℝ))
      (f := fun _ : {i : GUEEntry ι N // ¬ i = r} → ℝ => (1 : ℂ))
      (g := fun t : ℝ => gaussianPDFReal 0 1 t • gueCoeff r f)
      (integrable_const 1) hvol
    simpa using h
  have hint2 : Integrable (fun z : ({i : GUEEntry ι N // ¬ i = r} → ℝ) × ℝ =>
      z.2 • (gaussianPDFReal 0 1 z.2 • gueEntry f (WithLp.toLp 2 (piRecon r z.2 z.1))))
      ((Measure.pi (fun _ : {i : GUEEntry ι N // ¬ i = r} => gaussianReal 0 1)).prod
        (volume : Measure ℝ)) := by
    simpa [gueProd] using integrable_density_t_gueProd (p := r) [f]
  have hbot : ∀ᵐ (y : {i : GUEEntry ι N // ¬ i = r} → ℝ)
      ∂(Measure.pi (fun _ : {i : GUEEntry ι N // ¬ i = r} => gaussianReal 0 1)),
      Tendsto (fun t => gaussianPDFReal 0 1 t •
        gueEntry f (WithLp.toLp 2 (piRecon r t y))) atBot (𝓝 0) := by
    filter_upwards with y
    simpa [gueProd] using tendsto_density_gueProd_atBot r [f] y
  have htop : ∀ᵐ (y : {i : GUEEntry ι N // ¬ i = r} → ℝ)
      ∂(Measure.pi (fun _ : {i : GUEEntry ι N // ¬ i = r} => gaussianReal 0 1)),
      Tendsto (fun t => gaussianPDFReal 0 1 t •
        gueEntry f (WithLp.toLp 2 (piRecon r t y))) atTop (𝓝 0) := by
    filter_upwards with y
    simpa [gueProd] using tendsto_density_gueProd_atTop r [f] y
  have hstein := integral_eval_smul_stdGaussian (κ := GUECoord ι N) r
    (F := fun x => gueEntry f x) (F' := fun _ => gueCoeff r f)
    hderiv hint1 hint2 hbot htop
  simpa using hstein

/-- Density-weighted integrability of the derivative of a product of entries. -/
lemma integrable_density_gueProdDeriv (p : GUEEntry ι N) (l : List (GUEEntry ι N)) :
    Integrable (fun z : ({i : GUEEntry ι N // ¬ i = p} → ℝ) × ℝ =>
        gaussianPDFReal 0 1 z.2 •
          gueProdDeriv p l (WithLp.toLp 2 (piRecon p z.2 z.1)))
      ((Measure.pi (fun _ : {i : GUEEntry ι N // ¬ i = p} => gaussianReal 0 1)).prod
        (volume : Measure ℝ)) := by
  have hEq : (fun z : ({i : GUEEntry ι N // ¬ i = p} → ℝ) × ℝ =>
      gaussianPDFReal 0 1 z.2 •
        gueProdDeriv p l (WithLp.toLp 2 (piRecon p z.2 z.1))) =
      fun z => ∑ k : Fin l.length,
        gueCoeff p (l.get k) *
          (gaussianPDFReal 0 1 z.2 •
            gueProd (l.eraseIdx k) (WithLp.toLp 2 (piRecon p z.2 z.1))) := by
    funext z
    rw [gueProdDeriv_eq_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [show gaussianPDFReal 0 1 z.2 •
          (gueCoeff p (l.get k) * gueProd (l.eraseIdx k) _) =
        ((gaussianPDFReal 0 1 z.2 : ℝ) : ℂ) *
          (gueCoeff p (l.get k) * gueProd (l.eraseIdx k) _) from Complex.real_smul,
      show gaussianPDFReal 0 1 z.2 • gueProd (l.eraseIdx k) _ =
        ((gaussianPDFReal 0 1 z.2 : ℝ) : ℂ) *
          gueProd (l.eraseIdx k) _ from Complex.real_smul]
    ring
  rw [hEq]
  refine integrable_finsetSum Finset.univ fun k _ => ?_
  exact (integrable_density_gueProd p (l.eraseIdx k)).const_mul _

/-- Two-entry covariance as an integral (the existing covariance identity). -/
lemma integral_gueEntry_mul_gueEntry (e f : GUEEntry ι N) :
    ∫ x : EuclideanSpace ℝ (GUECoord ι N), gueEntry e x * gueEntry f x
        ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) = gueCov e f := by
  have h := integral_gueMatrix_mul (ι := ι) (N := N)
    e.1 f.1 e.2.1 e.2.2 f.2.1 f.2.2
  simpa [gueEntry, gueCov] using h

/-- The covariance kernel equals the coefficient combination from the Stein derivative. -/
lemma gueCov_eq_coeff (e f : GUEEntry ι N) :
    gueCov e f = gueAlphaScaled (N := N) * gueCoeff e f +
      gueBetaScaled (N := N) * gueCoeff (gueSwap e) f := by
  rw [← integral_gueEntry_mul_gueEntry e f]
  have hfun : (fun x : EuclideanSpace ℝ (GUECoord ι N) => gueEntry e x * gueEntry f x) =
      fun x => gueAlphaScaled (N := N) *
          (((x e : ℝ) : ℂ) * gueEntry f x) +
        gueBetaScaled (N := N) *
          (((x (gueSwap e) : ℝ) : ℂ) * gueEntry f x) := by
    funext x
    rw [gueEntry_eq]
    ring
  rw [hfun]
  have he : Integrable (fun x : EuclideanSpace ℝ (GUECoord ι N) =>
      ((x e : ℝ) : ℂ) * gueEntry f x)
      (stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) := by
    simpa [gueProd, Complex.real_smul] using integrable_coord_mul_gueProd e [f]
  have hse : Integrable (fun x : EuclideanSpace ℝ (GUECoord ι N) =>
      ((x (gueSwap e) : ℝ) : ℂ) * gueEntry f x)
      (stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) := by
    simpa [gueProd, Complex.real_smul] using
      integrable_coord_mul_gueProd (gueSwap e) [f]
  rw [integral_add (he.const_mul _) (hse.const_mul _)]
  rw [integral_const_mul, integral_const_mul]
  have h1 : (∫ x : EuclideanSpace ℝ (GUECoord ι N),
      ((x e : ℝ) : ℂ) * gueEntry f x
        ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))) = gueCoeff e f := by
    rw [show (fun x : EuclideanSpace ℝ (GUECoord ι N) =>
        ((x e : ℝ) : ℂ) * gueEntry f x) =
        fun x => x e • gueEntry f x by
      funext x
      rw [Complex.real_smul]]
    exact integral_coord_mul_gueEntry e f
  have h2 : (∫ x : EuclideanSpace ℝ (GUECoord ι N),
      ((x (gueSwap e) : ℝ) : ℂ) * gueEntry f x
        ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))) = gueCoeff (gueSwap e) f := by
    rw [show (fun x : EuclideanSpace ℝ (GUECoord ι N) =>
        ((x (gueSwap e) : ℝ) : ℂ) * gueEntry f x) =
        fun x => x (gueSwap e) • gueEntry f x by
      funext x
      rw [Complex.real_smul]]
    exact integral_coord_mul_gueEntry (gueSwap e) f
  rw [h1, h2]

/-- **Wick recurrence for complex GUE entries**:
`E[G_e ∏_{f ∈ l} G_f] = ∑_k E[G_e G_{l_k}] E[∏_{j ≠ k} G_{l_j}]`. -/
theorem integral_gueEntry_mul_gueProd (e : GUEEntry ι N)
    (l : List (GUEEntry ι N)) :
    ∫ x : EuclideanSpace ℝ (GUECoord ι N), gueEntry e x * gueProd l x
        ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) =
      ∑ k : Fin l.length,
        gueCov e (l.get k) *
          ∫ x : EuclideanSpace ℝ (GUECoord ι N), gueProd (l.eraseIdx k) x
            ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) := by
  have hstein_e := integral_eval_smul_stdGaussian (κ := GUECoord ι N) e
    (F := fun x => gueProd l x) (F' := fun x => gueProdDeriv e l x)
    (fun y a => hasDerivAt_gueProd e l y a)
    (integrable_density_gueProdDeriv e l)
    (integrable_density_t_gueProd e l)
    (by filter_upwards with y; exact tendsto_density_gueProd_atBot e l y)
    (by filter_upwards with y; exact tendsto_density_gueProd_atTop e l y)
  have hstein_se := integral_eval_smul_stdGaussian (κ := GUECoord ι N) (gueSwap e)
    (F := fun x => gueProd l x) (F' := fun x => gueProdDeriv (gueSwap e) l x)
    (fun y a => hasDerivAt_gueProd (gueSwap e) l y a)
    (integrable_density_gueProdDeriv (gueSwap e) l)
    (integrable_density_t_gueProd (gueSwap e) l)
    (by filter_upwards with y; exact tendsto_density_gueProd_atBot (gueSwap e) l y)
    (by filter_upwards with y; exact tendsto_density_gueProd_atTop (gueSwap e) l y)
  have he : Integrable (fun x : EuclideanSpace ℝ (GUECoord ι N) =>
      x e • gueProd l x)
      (stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) := by
    simpa [Complex.real_smul] using integrable_coord_mul_gueProd e l
  have hse : Integrable (fun x : EuclideanSpace ℝ (GUECoord ι N) =>
      x (gueSwap e) • gueProd l x)
      (stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) := by
    simpa [Complex.real_smul] using integrable_coord_mul_gueProd (gueSwap e) l
  have hL : (∫ x : EuclideanSpace ℝ (GUECoord ι N), gueEntry e x * gueProd l x
      ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))) =
      gueAlphaScaled (N := N) *
        (∫ x : EuclideanSpace ℝ (GUECoord ι N), x e • gueProd l x
          ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))) +
      gueBetaScaled (N := N) *
        (∫ x : EuclideanSpace ℝ (GUECoord ι N), x (gueSwap e) • gueProd l x
          ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))) := by
    have hfun : (fun x : EuclideanSpace ℝ (GUECoord ι N) =>
        gueEntry e x * gueProd l x) =
        fun x => gueAlphaScaled (N := N) * (x e • gueProd l x) +
          gueBetaScaled (N := N) * (x (gueSwap e) • gueProd l x) := by
      funext x
      rw [gueEntry_eq, add_mul]
      rw [show gueAlphaScaled (N := N) * ((x e : ℝ) : ℂ) * gueProd l x =
          gueAlphaScaled (N := N) * (x e • gueProd l x) by
        rw [mul_assoc, ← Complex.real_smul],
        show gueBetaScaled (N := N) * ((x (gueSwap e) : ℝ) : ℂ) * gueProd l x =
          gueBetaScaled (N := N) * (x (gueSwap e) • gueProd l x) by
        rw [mul_assoc, ← Complex.real_smul]]
    rw [hfun]
    rw [integral_add (he.const_mul _) (hse.const_mul _)]
    rw [integral_const_mul, integral_const_mul]
  rw [hL, hstein_e, hstein_se]
  have hde : (∫ x : EuclideanSpace ℝ (GUECoord ι N), gueProdDeriv e l x
      ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))) =
      ∑ k : Fin l.length,
        gueCoeff e (l.get k) *
          ∫ x : EuclideanSpace ℝ (GUECoord ι N), gueProd (l.eraseIdx k) x
            ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) := by
    simp_rw [gueProdDeriv_eq_sum]
    rw [integral_finsetSum]
    · refine Finset.sum_congr rfl fun k _ => ?_
      rw [integral_const_mul]
    · intro k _
      exact (integrable_gueProd (l.eraseIdx k)).const_mul _
  have hds : (∫ x : EuclideanSpace ℝ (GUECoord ι N), gueProdDeriv (gueSwap e) l x
      ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N)))) =
      ∑ k : Fin l.length,
        gueCoeff (gueSwap e) (l.get k) *
          ∫ x : EuclideanSpace ℝ (GUECoord ι N), gueProd (l.eraseIdx k) x
            ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) := by
    simp_rw [gueProdDeriv_eq_sum]
    rw [integral_finsetSum]
    · refine Finset.sum_congr rfl fun k _ => ?_
      rw [integral_const_mul]
    · intro k _
      exact (integrable_gueProd (l.eraseIdx k)).const_mul _
  rw [hde, hds, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [gueCov_eq_coeff e (l.get k)]
  ring

/-- First moment of a single entry (the empty-list case of the recurrence). -/
theorem integral_gueEntry_eq_zero (e : GUEEntry ι N) :
    ∫ x : EuclideanSpace ℝ (GUECoord ι N), gueEntry e x
        ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) = 0 := by
  have h := integral_gueEntry_mul_gueProd e []
  simpa [gueProd] using h

end

end GUEStrongConvergence
