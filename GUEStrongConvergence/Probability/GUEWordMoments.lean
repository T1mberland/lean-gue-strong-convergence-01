/-
# Higher GUE trace-word moments: exact finite-`N` pairing expansion

This file continues the bridge from entry-wise GUE Wick theory to matrix-word moments, beyond the
existing one-shot closed-walk expansion.

For a word `w : List ι` of matrix labels, the one-shot closed-walk expansion of
`GUEClosedWalks` writes the trace as a finite sum over starts `a : Fin N` and destination
functions `d : Fin w.length → Fin N` whose terminal vertex returns to `a`, of the product of the
entries along the corresponding closed walk.  Applying the exact entry-pairing formula
`integral_gueProd_eq_sum_pairing` to each of these closed walks gives the exact finite-`N`
identity

`E[tr (G_{w})] = ∑_{a, d closed} ∑_{p : GUEPairing (entries a w d)} p.weight`,

which is `integral_trace_gueWord_eq_sum_pairing` below: a finite, clearly computable sum over
closed walks and Wick pairings, valid for every `N` (including `N = 0`) and every word.

The covariance factorization `gueCov e f = N⁻¹ * gueDeltaCov e f`, where `gueDeltaCov` is a
Kronecker delta, is then used to isolate the normalization: for a word of length `k` every
pairing carries exactly `k / 2` covariance factors, so

`E[tr (G_w)] = N^{-k/2} * ∑_{a, d closed} ∑_p ∏_{(e,f) ∈ p} gueDeltaCov e f`

(`integral_trace_gueWord_eq_delta_sum`).  The remaining sum is a purely combinatorial count of
closed walks satisfying Kronecker constraints; no asymptotic statement about it is made here.

Consequences recorded here: the normalized version (`integral_gueNormTrace_eq_delta_sum`), the
odd-length vanishing of the closed-walk Wick sum (`gueWickClosedWalk_eq_zero_of_odd`), and the
length-`2` evaluation `E[tr (G_i G_j)] = N * δ_{ij}` (`integral_trace_gueWord_two`), which
shows that the pairing sum computes the expected semicircular value in the simplest case.
-/
import GUEStrongConvergence.Probability.GUEPairingPositions
import GUEStrongConvergence.Probability.GUEClosedWalks

open MeasureTheory ProbabilityTheory Filter
open scoped RealInnerProductSpace Matrix ENNReal Topology

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

namespace GUEStrongConvergence

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {N : ℕ}

/-! ### The Kronecker-delta part of the GUE covariance -/

/-- The Kronecker-delta part of the GUE covariance: it is `1` when the two entry indices are
transpose to each other and the labels agree, and `0` otherwise. -/
def gueDeltaCov (e f : GUEEntry ι N) : ℂ :=
  if e.1 = f.1 ∧ e.2.1 = f.2.2 ∧ e.2.2 = f.2.1 then 1 else 0

/-- The real and complex normalizations agree. -/
lemma ofReal_inv_natCast (N : ℕ) : ((N : ℝ)⁻¹ : ℂ) = ((N : ℂ)⁻¹) := by
  have h : ((N : ℂ)) = (((N : ℝ)) : ℂ) := by norm_num
  rw [h]

/-- The GUE covariance is `N⁻¹` times the Kronecker-delta part. -/
lemma gueCov_eq_inv_mul_deltaCov (e f : GUEEntry ι N) :
    gueCov e f = ((N : ℂ)⁻¹) * gueDeltaCov e f := by
  rw [gueCov, gueDeltaCov, ofReal_inv_natCast]
  split_ifs <;> simp

/-! ### Delta weight of a pairing -/

/-- The product of the Kronecker-delta parts of the covariances of a pairing. -/
def gueDeltaWeight : (l : List (GUEEntry ι N)) → GUEPairing l → ℂ
  | _, .nil => 1
  | _, .cons e l k p => gueDeltaCov e (l.get k) * gueDeltaWeight (l.eraseIdx k) p

@[simp] lemma gueDeltaWeight_nil :
    gueDeltaWeight ([] : List (GUEEntry ι N)) (GUEPairing.nil : GUEPairing []) = 1 := rfl

@[simp] lemma gueDeltaWeight_cons (e : GUEEntry ι N) (l : List (GUEEntry ι N))
    (k : Fin l.length) (p : GUEPairing (l.eraseIdx k)) :
    gueDeltaWeight (e :: l) (GUEPairing.cons e l k p) =
      gueDeltaCov e (l.get k) * gueDeltaWeight (l.eraseIdx k) p := rfl

/-- Arithmetic of the covariance exponent: a list of positive length contributes one covariance
factor for the head and `(n-1)/2` for the erased tail. -/
lemma Nat.sub_one_div_two_add_one {m : ℕ} (hm : 1 ≤ m) : (m - 1) / 2 + 1 = (m + 1) / 2 := by
  have h : m = (m - 1) + 1 := by omega
  conv_rhs => rw [h]
  rw [show (m - 1) + 1 + 1 = (m - 1) + 2 by ring]
  rw [Nat.add_div_right _ (by norm_num : 0 < 2)]

/-- **Covariance factorization of a pairing weight**: the weight of a pairing of a list of length
`k` is `N^{-k/2}` times the corresponding product of Kronecker deltas. -/
theorem weight_eq_inv_pow_mul_deltaWeight (l : List (GUEEntry ι N)) (p : GUEPairing l) :
    GUEPairing.weight l p = ((N : ℂ)⁻¹) ^ (l.length / 2) * gueDeltaWeight l p := by
  suffices h : ∀ n : ℕ, ∀ (l : List (GUEEntry ι N)), l.length = n → ∀ p : GUEPairing l,
      GUEPairing.weight l p = ((N : ℂ)⁻¹) ^ (l.length / 2) * gueDeltaWeight l p from
    h l.length l rfl p
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro l hl p
    cases p with
    | nil => simp [GUEPairing.weight, gueDeltaWeight]
    | cons e l' k p' =>
      have hk : 1 ≤ l'.length := by
        have := k.isLt
        omega
      have hl' : l'.length + 1 = n := by
        rw [List.length_cons] at hl
        exact hl
      have hlen : (l'.eraseIdx k).length = l'.length - 1 := by
        rw [List.length_eraseIdx, ite_eq_left k.isLt]
      have hlt : (l'.eraseIdx k).length < n := by
        omega
      calc GUEPairing.weight (e :: l') (GUEPairing.cons e l' k p')
          = gueCov e (l'.get k) * GUEPairing.weight (l'.eraseIdx k) p' := rfl
        _ = (((N : ℂ)⁻¹) * gueDeltaCov e (l'.get k)) *
              (((N : ℂ)⁻¹) ^ ((l'.eraseIdx k).length / 2) *
                gueDeltaWeight (l'.eraseIdx k) p') := by
            rw [gueCov_eq_inv_mul_deltaCov, ih (l'.eraseIdx k).length hlt _ rfl p']
        _ = ((N : ℂ)⁻¹) ^ ((l'.eraseIdx k).length / 2 + 1) *
              (gueDeltaCov e (l'.get k) * gueDeltaWeight (l'.eraseIdx k) p') := by
            rw [pow_add, pow_one]
            ring
        _ = ((N : ℂ)⁻¹) ^ ((l'.length + 1) / 2) *
              (gueDeltaCov e (l'.get k) * gueDeltaWeight (l'.eraseIdx k) p') := by
            rw [hlen, Nat.sub_one_div_two_add_one hk]
        _ = ((N : ℂ)⁻¹) ^ ((e :: l').length / 2) * gueDeltaWeight (e :: l')
              (GUEPairing.cons e l' k p') := by
            rw [gueDeltaWeight_cons]
            norm_num

/-! ### The exact finite-`N` expectation as a pairing sum -/

/-- The entry list of a path has the length of the word. -/
lemma length_guePathEntries (w : List ι) (a : Fin N) (d : Fin w.length → Fin N) :
    (guePathEntries a w d).length = w.length := by
  induction w generalizing a with
  | nil => simp
  | cons i w ih =>
    simp only [guePathEntries_cons, List.length_cons]
    rw [ih]

/-- The Wick closed-walk sum expanded as an explicit finite sum over pairings. -/
theorem gueWickClosedWalk_eq_sum_pairing (w : List ι) :
    gueWickClosedWalk (N := N) w =
      ∑ a : Fin N, ∑ d : Fin w.length → Fin N,
        if guePathLast a w d = a then
          ∑ p : GUEPairing (guePathEntries (N := N) a w d), GUEPairing.weight _ p
        else 0 := by
  simp only [gueWickClosedWalk]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun d _ => ?_
  by_cases h : guePathLast a w d = a
  · rw [ite_eq_left h, ite_eq_left h, gueWick_eq_sum_pairing]
  · rw [ite_eq_right h, ite_eq_right h]

/-- **Exact finite-`N` expectation formula for a general trace word**: the expectation of the
trace of a matrix word is the finite sum over closed walks and Wick pairings of the pairing
weights. -/
theorem integral_trace_gueWord_eq_sum_pairing (w : List ι) :
    ∫ x : EuclideanSpace ℝ (GUECoord ι N), Matrix.trace (gueWord w x)
        ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) =
      ∑ a : Fin N, ∑ d : Fin w.length → Fin N,
        if guePathLast a w d = a then
          ∑ p : GUEPairing (guePathEntries (N := N) a w d), GUEPairing.weight _ p
        else 0 := by
  rw [integral_trace_gueWord_eq_wick_sum, gueWickClosedWalk_eq_sum_pairing]

/-- **Normalized covariance form**: for a word of length `k`, the trace expectation is `N^{-k/2}`
times the finite sum over closed walks and pairings of the products of Kronecker deltas. -/
theorem integral_trace_gueWord_eq_delta_sum (w : List ι) :
    ∫ x : EuclideanSpace ℝ (GUECoord ι N), Matrix.trace (gueWord w x)
        ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) =
      ((N : ℂ)⁻¹) ^ (w.length / 2) *
        (∑ a : Fin N, ∑ d : Fin w.length → Fin N,
          if guePathLast a w d = a then
            ∑ p : GUEPairing (guePathEntries (N := N) a w d), gueDeltaWeight _ p
          else 0) := by
  rw [integral_trace_gueWord_eq_sum_pairing, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  by_cases h : guePathLast a w d = a
  · rw [ite_eq_left h, ite_eq_left h, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [weight_eq_inv_pow_mul_deltaWeight, length_guePathEntries]
  · rw [ite_eq_right h, ite_eq_right h]
    simp

/-- Normalized trace version of the exact pairing expansion. -/
theorem integral_gueNormTrace_eq_delta_sum (w : List ι) :
    ∫ x : EuclideanSpace ℝ (GUECoord ι N), gueNormTrace w x
        ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) =
      ((N : ℂ)⁻¹) ^ (w.length / 2 + 1) *
        (∑ a : Fin N, ∑ d : Fin w.length → Fin N,
          if guePathLast a w d = a then
            ∑ p : GUEPairing (guePathEntries (N := N) a w d), gueDeltaWeight _ p
          else 0) := by
  rw [integral_gueNormTrace_eq_wick_sum, ← integral_trace_gueWord_eq_wick_sum,
    integral_trace_gueWord_eq_delta_sum, pow_succ']
  ring

/-- Odd-length words have zero closed-walk Wick sum (the pairing sum is empty in weight). -/
theorem gueWickClosedWalk_eq_zero_of_odd (w : List ι) (hodd : Odd w.length) :
    gueWickClosedWalk (N := N) w = 0 := by
  have h := integral_trace_gueWord_eq_wick_sum (N := N) w
  rw [integral_trace_gueWord_odd_zero w hodd] at h
  exact h.symm


/-! ### Evaluation of the length-`4` expectation

The closed-walk pairing sum for a word of length four consists of three pairing terms, each a
product of two Kronecker deltas.  The lemmas below evaluate the resulting index sums (the face
counts `N^3`, `N`, `N^3` of the three pairings) and assemble the general length-four trace
expectation.  The two non-crossing pairings carry `N^3` and the crossing pairing carries `N`,
which is exactly the genus expansion `2 N + N^{-1}` for the fourth moment.
-/

lemma gueWick_two (e f : GUEEntry ι N) : gueWick [e, f] = gueCov e f := by
  rw [gueWick_cons]
  simp only [List.length_cons, List.length_nil]
  rw [Fin.sum_univ_one]
  simp [gueWick_nil]
lemma gueWick_four (e0 e1 e2 e3 : GUEEntry ι N) :
    gueWick [e0, e1, e2, e3] =
      gueCov e0 e1 * gueCov e2 e3 + gueCov e0 e2 * gueCov e1 e3 +
        gueCov e0 e3 * gueCov e1 e2 := by
  rw [gueWick_cons]
  simp only [List.length_cons, List.length_nil]
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ]
  simp only [Fin.val_zero, Fin.val_succ, Nat.reduceAdd, List.get_eq_getElem,
    List.getElem_cons_zero, List.getElem_cons_succ, List.eraseIdx,
    List.length_cons, List.length_nil]
  rw [gueWick_two, gueWick_two, gueWick_two]
  ring
lemma guePathEntries_four (i j k l : ι) (a : Fin N) (d : Fin 4 → Fin N) :
    guePathEntries a [i, j, k, l] d =
      [(i, (a, d 0)), (j, (d 0, d 1)), (k, (d 1, d 2)), (l, (d 2, d 3))] := by
  simp [guePathEntries_cons, Fin.tail_def]
  rfl
lemma guePathLast_four (i j k l : ι) (a : Fin N) (d : Fin 4 → Fin N) :
    guePathLast a [i, j, k, l] d = d 3 := by
  simp [guePathLast, Fin.tail_def]
  rfl

lemma sum_fin_ite_eq_insertNth {n : ℕ} {α M : Type*} [Fintype α] [DecidableEq α]
    [AddCommMonoid M] (j : Fin (n + 1)) (c : α) (F : (Fin (n + 1) → α) → M) :
    (∑ d : Fin (n + 1) → α, if d j = c then F d else 0) =
      ∑ e : Fin n → α, F (Fin.insertNth j c e) := by
  let eqv : (Fin (n + 1) → α) ≃ (α × (Fin n → α)) :=
    { toFun := fun d => (d j, Fin.removeNth j d)
      invFun := fun p => Fin.insertNth j p.1 p.2
      left_inv := fun d => by simp
      right_inv := fun p => by simp }
  rw [Fintype.sum_equiv eqv (fun d => if d j = c then F d else 0)
    (fun p : α × (Fin n → α) => if p.1 = c then F (Fin.insertNth j p.1 p.2) else 0) ?_]
  · rw [Fintype.sum_prod_type, Finset.sum_comm]
    simp
  · intro d
    simp [eqv]

lemma sum_fin_fun_one (n : ℕ) :
    (∑ _ : Fin n → Fin N, (1 : ℂ)) = (N : ℂ) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_fin_cons n (fun _ => (1 : ℂ)), Finset.sum_const, ih]
    simp [Finset.card_univ, pow_succ]
    ring

lemma sum_fin_one : (∑ _ : Fin N, (1 : ℂ)) = (N : ℂ) := by
  simp [Finset.card_univ]

-- insertNth evaluations
lemma ins_last4_zero (a : Fin N) (e : Fin 3 → Fin N) :
    (@Fin.insertNth 3 (fun _ => Fin N) 3 a e) 0 = e 0 := by
  rw [show (0 : Fin 4) = (3 : Fin 4).succAbove (0 : Fin 3) from rfl,
    Fin.insertNth_apply_succAbove]
lemma ins_last4_one (a : Fin N) (e : Fin 3 → Fin N) :
    (@Fin.insertNth 3 (fun _ => Fin N) 3 a e) 1 = e 1 := by
  rw [show (1 : Fin 4) = (3 : Fin 4).succAbove (1 : Fin 3) from rfl,
    Fin.insertNth_apply_succAbove]
lemma ins_last4_two (a : Fin N) (e : Fin 3 → Fin N) :
    (@Fin.insertNth 3 (fun _ => Fin N) 3 a e) 2 = e 2 := by
  rw [show (2 : Fin 4) = (3 : Fin 4).succAbove (2 : Fin 3) from rfl,
    Fin.insertNth_apply_succAbove]
lemma ins_last3_zero (a : Fin N) (e : Fin 2 → Fin N) :
    (@Fin.insertNth 2 (fun _ => Fin N) 2 a e) 0 = e 0 := by
  rw [show (0 : Fin 3) = (2 : Fin 3).succAbove (0 : Fin 2) from rfl,
    Fin.insertNth_apply_succAbove]
lemma ins_last3_one (a : Fin N) (e : Fin 2 → Fin N) :
    (@Fin.insertNth 2 (fun _ => Fin N) 2 a e) 1 = e 1 := by
  rw [show (1 : Fin 3) = (2 : Fin 3).succAbove (1 : Fin 2) from rfl,
    Fin.insertNth_apply_succAbove]
lemma ins_last2_zero (a : Fin N) (e : Fin 1 → Fin N) :
    (@Fin.insertNth 1 (fun _ => Fin N) 1 a e) 0 = e 0 := by
  rw [show (0 : Fin 2) = (1 : Fin 2).succAbove (0 : Fin 1) from rfl,
    Fin.insertNth_apply_succAbove]
lemma ins_mid3_zero (a : Fin N) (e : Fin 2 → Fin N) :
    (@Fin.insertNth 2 (fun _ => Fin N) 1 a e) 0 = e 0 := by
  rw [show (0 : Fin 3) = (1 : Fin 3).succAbove (0 : Fin 2) from rfl,
    Fin.insertNth_apply_succAbove]
lemma ins_mid3_two (a : Fin N) (e : Fin 2 → Fin N) :
    (@Fin.insertNth 2 (fun _ => Fin N) 1 a e) 2 = e 1 := by
  rw [show (2 : Fin 3) = (1 : Fin 3).succAbove (1 : Fin 2) from rfl,
    Fin.insertNth_apply_succAbove]
lemma ins_zero3_zero (c : Fin N) (e : Fin 2 → Fin N) :
    (@Fin.insertNth 2 (fun _ => Fin N) 0 c e) 0 = c := by
  rw [Fin.insertNth_zero']; simp
lemma ins_zero3_two (c : Fin N) (e : Fin 2 → Fin N) :
    (@Fin.insertNth 2 (fun _ => Fin N) 0 c e) 2 = e 1 := by
  rw [Fin.insertNth_zero']
  rw [show (2 : Fin 3) = (1 : Fin 2).succ from rfl, Fin.cons_succ]

lemma C1 :
    (∑ a : Fin N, ∑ d : Fin 4 → Fin N,
      if d 3 = a then (if a = d 1 then (1 : ℂ) else 0) *
        (if d 1 = d 3 then (1 : ℂ) else 0) else 0) = (N : ℂ) ^ 3 := by
  have hpt : ∀ (a : Fin N) (d : Fin 4 → Fin N),
      (if d 3 = a then (if a = d 1 then (1 : ℂ) else 0) *
        (if d 1 = d 3 then (1 : ℂ) else 0) else 0) =
      (if d 3 = a then (if d 1 = a then (1 : ℂ) else 0) else 0) := by
    intro a d
    by_cases h3 : d 3 = a <;> by_cases h1 : d 1 = a <;> simp [h3, h1]
  simp only [hpt]
  have step1 : (∑ a : Fin N, ∑ d : Fin 4 → Fin N,
        if d 3 = a then (if d 1 = a then (1 : ℂ) else 0) else 0)
      = ∑ a : Fin N, ∑ e : Fin 3 → Fin N, (if e 1 = a then (1 : ℂ) else 0) := by
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [sum_fin_ite_eq_insertNth 3 a (fun d => if d 1 = a then (1 : ℂ) else 0)]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [ins_last4_one]
  have step2 : (∑ a : Fin N, ∑ e : Fin 3 → Fin N, (if e 1 = a then (1 : ℂ) else 0))
      = ∑ a : Fin N, ∑ _ : Fin 2 → Fin N, (1 : ℂ) := by
    refine Finset.sum_congr rfl fun a _ => ?_
    exact sum_fin_ite_eq_insertNth 1 a (fun _ => (1 : ℂ))
  rw [step1, step2, sum_fin_fun_one 2]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

lemma C2 :
    (∑ a : Fin N, ∑ d : Fin 4 → Fin N,
      if d 3 = a then (if a = d 2 ∧ d 0 = d 1 then (1 : ℂ) else 0) *
        (if d 0 = d 3 ∧ d 1 = d 2 then (1 : ℂ) else 0) else 0) = (N : ℂ) := by
  have step1 : (∑ a : Fin N, ∑ d : Fin 4 → Fin N,
      if d 3 = a then (if a = d 2 ∧ d 0 = d 1 then (1 : ℂ) else 0) *
        (if d 0 = d 3 ∧ d 1 = d 2 then (1 : ℂ) else 0) else 0)
      = ∑ a : Fin N, ∑ e : Fin 3 → Fin N,
          ((if a = e 2 ∧ e 0 = e 1 then (1 : ℂ) else 0) *
            (if e 0 = a ∧ e 1 = e 2 then (1 : ℂ) else 0)) := by
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [sum_fin_ite_eq_insertNth 3 a (fun d =>
      (if a = d 2 ∧ d 0 = d 1 then (1 : ℂ) else 0) *
        (if d 0 = d 3 ∧ d 1 = d 2 then (1 : ℂ) else 0))]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [ins_last4_zero, ins_last4_one, ins_last4_two, Fin.insertNth_apply_same]
  rw [step1]
  have hpt2 : ∀ (a : Fin N) (e : Fin 3 → Fin N),
      ((if a = e 2 ∧ e 0 = e 1 then (1 : ℂ) else 0) *
        (if e 0 = a ∧ e 1 = e 2 then (1 : ℂ) else 0)) =
      (if e 2 = a then ((if e 0 = e 1 then (1 : ℂ) else 0) *
        (if e 0 = a ∧ e 1 = a then (1 : ℂ) else 0)) else 0) := by
    intro a e
    by_cases h2 : e 2 = a
    · rw [h2]; simp
    · have h2' : ¬ a = e 2 := fun h => h2 h.symm
      simp [h2, h2']
  simp only [hpt2]
  have step2 : (∑ a : Fin N, ∑ e : Fin 3 → Fin N,
          (if e 2 = a then ((if e 0 = e 1 then (1 : ℂ) else 0) *
            (if e 0 = a ∧ e 1 = a then (1 : ℂ) else 0)) else 0))
      = ∑ a : Fin N, ∑ e' : Fin 2 → Fin N,
          ((if e' 0 = e' 1 then (1 : ℂ) else 0) *
            (if e' 0 = a ∧ e' 1 = a then (1 : ℂ) else 0)) := by
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [sum_fin_ite_eq_insertNth 2 a (fun e =>
      ((if e 0 = e 1 then (1 : ℂ) else 0) *
        (if e 0 = a ∧ e 1 = a then (1 : ℂ) else 0)))]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [ins_last3_zero, ins_last3_one]
  rw [step2]
  have hpt3 : ∀ (a : Fin N) (e : Fin 2 → Fin N),
      ((if e 0 = e 1 then (1 : ℂ) else 0) *
        (if e 0 = a ∧ e 1 = a then (1 : ℂ) else 0)) =
      (if e 1 = a then (if e 0 = a then (1 : ℂ) else 0) else 0) := by
    intro a e
    by_cases h1 : e 1 = a
    · rw [h1]; simp
    · have h1' : ¬ a = e 1 := fun h => h1 h.symm
      simp [h1, h1']
  simp only [hpt3]
  have step3 : (∑ a : Fin N, ∑ e : Fin 2 → Fin N,
          (if e 1 = a then (if e 0 = a then (1 : ℂ) else 0) else 0))
      = ∑ a : Fin N, ∑ e' : Fin 1 → Fin N, (if e' 0 = a then (1 : ℂ) else 0) := by
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [sum_fin_ite_eq_insertNth 1 a (fun e => if e 0 = a then (1 : ℂ) else 0)]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [ins_last2_zero]
  rw [step3]
  have step4 : (∑ a : Fin N, ∑ e : Fin 1 → Fin N, (if e 0 = a then (1 : ℂ) else 0))
      = ∑ a : Fin N, ∑ _ : Fin 0 → Fin N, (1 : ℂ) := by
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [sum_fin_ite_eq_insertNth 0 a (fun _ => (1 : ℂ))]
  rw [step4, sum_fin_fun_one 0]
  simp only [pow_zero]
  rw [sum_fin_one]

lemma C3 :
    (∑ a : Fin N, ∑ d : Fin 4 → Fin N,
      if d 3 = a then (if d 0 = d 2 then (1 : ℂ) else 0) *
        (if d 0 = d 2 then (1 : ℂ) else 0) else 0) = (N : ℂ) ^ 3 := by
  have hpt : ∀ (a : Fin N) (d : Fin 4 → Fin N),
      (if d 3 = a then (if d 0 = d 2 then (1 : ℂ) else 0) *
        (if d 0 = d 2 then (1 : ℂ) else 0) else 0) =
      (if d 3 = a then (if d 0 = d 2 then (1 : ℂ) else 0) else 0) := by
    intro a d
    by_cases h3 : d 3 = a <;> by_cases h : d 0 = d 2 <;> simp [h3, h]
  simp only [hpt]
  have step1 : (∑ a : Fin N, ∑ d : Fin 4 → Fin N,
        if d 3 = a then (if d 0 = d 2 then (1 : ℂ) else 0) else 0)
      = ∑ a : Fin N, ∑ e : Fin 3 → Fin N, (if e 0 = e 2 then (1 : ℂ) else 0) := by
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [sum_fin_ite_eq_insertNth 3 a (fun d => if d 0 = d 2 then (1 : ℂ) else 0)]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [ins_last4_zero, ins_last4_two]
  rw [step1]
  have hpt2 : ∀ e : Fin 3 → Fin N, (if e 0 = e 2 then (1 : ℂ) else 0) =
      ∑ c : Fin N, (if e 0 = c then (if e 2 = c then (1 : ℂ) else 0) else 0) := by
    intro e
    rw [Finset.sum_ite_eq]
    by_cases h : e 0 = e 2 <;> simp [h, eq_comm]
  simp only [hpt2]
  have step2 : (∑ a : Fin N, ∑ e : Fin 3 → Fin N, ∑ c : Fin N,
          (if e 0 = c then (if e 2 = c then (1 : ℂ) else 0) else 0))
      = ∑ a : Fin N, ∑ c : Fin N, ∑ e : Fin 3 → Fin N,
          (if e 0 = c then (if e 2 = c then (1 : ℂ) else 0) else 0) := by
    refine Finset.sum_congr rfl fun a _ => ?_
    exact Finset.sum_comm
  rw [step2]
  have step3 : (∑ a : Fin N, ∑ c : Fin N, ∑ e : Fin 3 → Fin N,
          (if e 0 = c then (if e 2 = c then (1 : ℂ) else 0) else 0))
      = ∑ a : Fin N, ∑ c : Fin N, ∑ e' : Fin 2 → Fin N,
          (if e' 1 = c then (1 : ℂ) else 0) := by
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => ?_
    rw [sum_fin_ite_eq_insertNth 0 c (fun e => if e 2 = c then (1 : ℂ) else 0)]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [ins_zero3_two]
  rw [step3]
  have step4 : (∑ a : Fin N, ∑ c : Fin N, ∑ e' : Fin 2 → Fin N,
          (if e' 1 = c then (1 : ℂ) else 0))
      = ∑ a : Fin N, ∑ c : Fin N, ∑ _ : Fin 1 → Fin N, (1 : ℂ) := by
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => ?_
    exact sum_fin_ite_eq_insertNth 1 c (fun _ => (1 : ℂ))
  rw [step4, sum_fin_fun_one 1]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring


/-- The covariance of two entry indices in terms of the label Kronecker delta. -/
lemma gueCov_mk (i j : ι) (a b c e : Fin N) :
    gueCov (i, (a, b)) (j, (c, e)) =
      ((N : ℂ)⁻¹) * (if i = j ∧ a = e ∧ b = c then (1 : ℂ) else 0) := by
  rw [gueCov_eq_inv_mul_deltaCov, gueDeltaCov]

/-- The length-four closed-walk Wick value, expanded into the three pairing indicators. -/
lemma gueWick_four_path (i j k l : ι) (a d0 d1 d2 d3 : Fin N) :
    gueWick [(i, (a, d0)), (j, (d0, d1)), (k, (d1, d2)), (l, (d2, d3))] =
      ((N : ℂ)⁻¹) ^ 2 * ((if i = j ∧ a = d1 then (1 : ℂ) else 0) * (if k = l ∧ d1 = d3 then (1 : ℂ) else 0) + (if i = k ∧ a = d2 ∧ d0 = d1 then (1 : ℂ) else 0) * (if j = l ∧ d0 = d3 ∧ d1 = d2 then (1 : ℂ) else 0) + (if i = l ∧ a = d3 ∧ d0 = d2 then (1 : ℂ) else 0) * (if j = k ∧ d0 = d2 then (1 : ℂ) else 0)) := by
  rw [gueWick_four, gueCov_mk, gueCov_mk, gueCov_mk, gueCov_mk, gueCov_mk, gueCov_mk]
  simp only [eq_self_iff_true, and_true]
  ring

/-- First (non-crossing) pairing count for the length-four closed-walk sum. -/
lemma sum_closedWalk_pairing_one (i j k l : ι) :
    (∑ a : Fin N, ∑ d : Fin 4 → Fin N,
      if d 3 = a then (if i = j ∧ a = d 1 then (1 : ℂ) else 0) * (if k = l ∧ d 1 = d 3 then (1 : ℂ) else 0) else 0) =
      (if i = j then (1 : ℂ) else 0) * (if k = l then (1 : ℂ) else 0) * (N : ℂ) ^ 3 := by
  by_cases hij : i = j <;> by_cases hkl : k = l
  · have h : (∑ a : Fin N, ∑ d : Fin 4 → Fin N,
        if d 3 = a then (if i = j ∧ a = d 1 then (1 : ℂ) else 0) * (if k = l ∧ d 1 = d 3 then (1 : ℂ) else 0) else 0) = (N : ℂ) ^ 3 := by
      simpa only [hij, hkl, eq_self_iff_true, and_true, true_and, ite_true, one_mul] using
        (C1 (N := N))
    rw [h]
    simp [hij, hkl]
  · simp [hij, hkl]
  · simp [hij, hkl]
  · simp [hij, hkl]

/-- Second (crossing) pairing count for the length-four closed-walk sum. -/
lemma sum_closedWalk_pairing_two (i j k l : ι) :
    (∑ a : Fin N, ∑ d : Fin 4 → Fin N,
      if d 3 = a then (if i = k ∧ a = d 2 ∧ d 0 = d 1 then (1 : ℂ) else 0) * (if j = l ∧ d 0 = d 3 ∧ d 1 = d 2 then (1 : ℂ) else 0) else 0) =
      (if i = k then (1 : ℂ) else 0) * (if j = l then (1 : ℂ) else 0) * (N : ℂ) := by
  by_cases hik : i = k <;> by_cases hjl : j = l
  · have h : (∑ a : Fin N, ∑ d : Fin 4 → Fin N,
        if d 3 = a then (if i = k ∧ a = d 2 ∧ d 0 = d 1 then (1 : ℂ) else 0) * (if j = l ∧ d 0 = d 3 ∧ d 1 = d 2 then (1 : ℂ) else 0) else 0) = (N : ℂ) := by
      simpa only [hik, hjl, eq_self_iff_true, and_true, true_and, ite_true, one_mul] using
        (C2 (N := N))
    rw [h]
    simp [hik, hjl]
  · simp [hik, hjl]
  · simp [hik, hjl]
  · simp [hik, hjl]

/-- Third (non-crossing) pairing count for the length-four closed-walk sum. -/
lemma sum_closedWalk_pairing_three (i j k l : ι) :
    (∑ a : Fin N, ∑ d : Fin 4 → Fin N,
      if d 3 = a then (if i = l ∧ a = d 3 ∧ d 0 = d 2 then (1 : ℂ) else 0) * (if j = k ∧ d 0 = d 2 then (1 : ℂ) else 0) else 0) =
      (if i = l then (1 : ℂ) else 0) * (if j = k then (1 : ℂ) else 0) * (N : ℂ) ^ 3 := by
  by_cases hil : i = l <;> by_cases hjk : j = k
  · have h : (∑ a : Fin N, ∑ d : Fin 4 → Fin N,
        if d 3 = a then (if i = l ∧ a = d 3 ∧ d 0 = d 2 then (1 : ℂ) else 0) * (if j = k ∧ d 0 = d 2 then (1 : ℂ) else 0) else 0) = (N : ℂ) ^ 3 := by
      have hpt : ∀ (a : Fin N) (d : Fin 4 → Fin N),
          (if d 3 = a then (if i = l ∧ a = d 3 ∧ d 0 = d 2 then (1 : ℂ) else 0) * (if j = k ∧ d 0 = d 2 then (1 : ℂ) else 0) else 0) =
          (if d 3 = a then (if d 0 = d 2 then (1 : ℂ) else 0) *
            (if d 0 = d 2 then (1 : ℂ) else 0) else 0) := by
        intro a d
        by_cases h3 : d 3 = a
        · rw [h3]
          simp [hil, hjk]
        · simp [h3]
      simpa only [hpt] using (C3 (N := N))
    rw [h]
    simp [hil, hjk]
  · simp [hil, hjk]
  · simp [hil, hjk]
  · simp [hil, hjk]


/-! ### The three pairing contributions to the length-four moment -/

/-- The closed-walk Wick sum for a four-letter word, with the index function typed as
`Fin 4 → Fin N`. -/
lemma gueWickClosedWalk_four (i j k l : ι) :
    gueWickClosedWalk (N := N) [i, j, k, l] =
      ∑ a : Fin N, ∑ d : (Fin 4 → Fin N),
        if d 3 = a then
          gueWick [(i, (a, d 0)), (j, (d 0, d 1)), (k, (d 1, d 2)), (l, (d 2, d 3))]
        else 0 := by
  simp only [gueWickClosedWalk]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun d _ => ?_
  rw [guePathLast_four, guePathEntries_four]

/-- The first (non-crossing) pairing contribution including its covariance normalization. -/
lemma sum_closedWalk_product_one (i j k l : ι) :
    (∑ a : Fin N, ∑ d : (Fin 4 → Fin N),
      if d 3 = a then ((((N : ℂ)⁻¹)) * (if i = j ∧ a = d 1 then (1 : ℂ) else 0)) * ((((N : ℂ)⁻¹)) * (if k = l ∧ d 1 = d 3 then (1 : ℂ) else 0)) else 0) =
      (if i = j then (1 : ℂ) else 0) * (if k = l then (1 : ℂ) else 0) * (N : ℂ) := by
  have hpt : ∀ (a : Fin N) (d : (Fin 4 → Fin N)),
      (if d 3 = a then ((((N : ℂ)⁻¹)) * (if i = j ∧ a = d 1 then (1 : ℂ) else 0)) * ((((N : ℂ)⁻¹)) * (if k = l ∧ d 1 = d 3 then (1 : ℂ) else 0)) else 0) =
      (((N : ℂ)⁻¹) * ((N : ℂ)⁻¹)) * (if d 3 = a then (if i = j ∧ a = d 1 then (1 : ℂ) else 0) * (if k = l ∧ d 1 = d 3 then (1 : ℂ) else 0) else 0) := by
    intro a d
    by_cases h : d 3 = a
    · rw [ite_eq_left h, ite_eq_left h]
      ring
    · rw [ite_eq_right h, ite_eq_right h]
      simp
  rw [show (∑ a : Fin N, ∑ d : (Fin 4 → Fin N),
        if d 3 = a then ((((N : ℂ)⁻¹)) * (if i = j ∧ a = d 1 then (1 : ℂ) else 0)) * ((((N : ℂ)⁻¹)) * (if k = l ∧ d 1 = d 3 then (1 : ℂ) else 0)) else 0)
      = (((N : ℂ)⁻¹) * ((N : ℂ)⁻¹)) * (∑ a : Fin N, ∑ d : (Fin 4 → Fin N),
          if d 3 = a then (if i = j ∧ a = d 1 then (1 : ℂ) else 0) * (if k = l ∧ d 1 = d 3 then (1 : ℂ) else 0) else 0) from by
    simp only [hpt]
    simp only [Finset.mul_sum]]
  rw [sum_closedWalk_pairing_one]
  rcases eq_or_ne N 0 with hN | hN
  · subst hN; simp
  · have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast hN
    field_simp

/-- The second (crossing) pairing contribution including its covariance normalization. -/
lemma sum_closedWalk_product_two (i j k l : ι) :
    (∑ a : Fin N, ∑ d : (Fin 4 → Fin N),
      if d 3 = a then ((((N : ℂ)⁻¹)) * (if i = k ∧ a = d 2 ∧ d 0 = d 1 then (1 : ℂ) else 0)) * ((((N : ℂ)⁻¹)) * (if j = l ∧ d 0 = d 3 ∧ d 1 = d 2 then (1 : ℂ) else 0)) else 0) =
      (if i = k then (1 : ℂ) else 0) * (if j = l then (1 : ℂ) else 0) * (((N : ℂ)⁻¹)) := by
  have hpt : ∀ (a : Fin N) (d : (Fin 4 → Fin N)),
      (if d 3 = a then ((((N : ℂ)⁻¹)) * (if i = k ∧ a = d 2 ∧ d 0 = d 1 then (1 : ℂ) else 0)) * ((((N : ℂ)⁻¹)) * (if j = l ∧ d 0 = d 3 ∧ d 1 = d 2 then (1 : ℂ) else 0)) else 0) =
      (((N : ℂ)⁻¹) * ((N : ℂ)⁻¹)) * (if d 3 = a then (if i = k ∧ a = d 2 ∧ d 0 = d 1 then (1 : ℂ) else 0) * (if j = l ∧ d 0 = d 3 ∧ d 1 = d 2 then (1 : ℂ) else 0) else 0) := by
    intro a d
    by_cases h : d 3 = a
    · rw [ite_eq_left h, ite_eq_left h]
      ring
    · rw [ite_eq_right h, ite_eq_right h]
      simp
  rw [show (∑ a : Fin N, ∑ d : (Fin 4 → Fin N),
        if d 3 = a then ((((N : ℂ)⁻¹)) * (if i = k ∧ a = d 2 ∧ d 0 = d 1 then (1 : ℂ) else 0)) * ((((N : ℂ)⁻¹)) * (if j = l ∧ d 0 = d 3 ∧ d 1 = d 2 then (1 : ℂ) else 0)) else 0)
      = (((N : ℂ)⁻¹) * ((N : ℂ)⁻¹)) * (∑ a : Fin N, ∑ d : (Fin 4 → Fin N),
          if d 3 = a then (if i = k ∧ a = d 2 ∧ d 0 = d 1 then (1 : ℂ) else 0) * (if j = l ∧ d 0 = d 3 ∧ d 1 = d 2 then (1 : ℂ) else 0) else 0) from by
    simp only [hpt]
    simp only [Finset.mul_sum]]
  rw [sum_closedWalk_pairing_two]
  rcases eq_or_ne N 0 with hN | hN
  · subst hN; simp
  · have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast hN
    field_simp

/-- The third (non-crossing) pairing contribution including its covariance normalization. -/
lemma sum_closedWalk_product_three (i j k l : ι) :
    (∑ a : Fin N, ∑ d : (Fin 4 → Fin N),
      if d 3 = a then ((((N : ℂ)⁻¹)) * (if i = l ∧ a = d 3 ∧ d 0 = d 2 then (1 : ℂ) else 0)) * ((((N : ℂ)⁻¹)) * (if j = k ∧ d 0 = d 2 then (1 : ℂ) else 0)) else 0) =
      (if i = l then (1 : ℂ) else 0) * (if j = k then (1 : ℂ) else 0) * (N : ℂ) := by
  have hpt : ∀ (a : Fin N) (d : (Fin 4 → Fin N)),
      (if d 3 = a then ((((N : ℂ)⁻¹)) * (if i = l ∧ a = d 3 ∧ d 0 = d 2 then (1 : ℂ) else 0)) * ((((N : ℂ)⁻¹)) * (if j = k ∧ d 0 = d 2 then (1 : ℂ) else 0)) else 0) =
      (((N : ℂ)⁻¹) * ((N : ℂ)⁻¹)) * (if d 3 = a then (if i = l ∧ a = d 3 ∧ d 0 = d 2 then (1 : ℂ) else 0) * (if j = k ∧ d 0 = d 2 then (1 : ℂ) else 0) else 0) := by
    intro a d
    by_cases h : d 3 = a
    · rw [ite_eq_left h, ite_eq_left h]
      ring
    · rw [ite_eq_right h, ite_eq_right h]
      simp
  rw [show (∑ a : Fin N, ∑ d : (Fin 4 → Fin N),
        if d 3 = a then ((((N : ℂ)⁻¹)) * (if i = l ∧ a = d 3 ∧ d 0 = d 2 then (1 : ℂ) else 0)) * ((((N : ℂ)⁻¹)) * (if j = k ∧ d 0 = d 2 then (1 : ℂ) else 0)) else 0)
      = (((N : ℂ)⁻¹) * ((N : ℂ)⁻¹)) * (∑ a : Fin N, ∑ d : (Fin 4 → Fin N),
          if d 3 = a then (if i = l ∧ a = d 3 ∧ d 0 = d 2 then (1 : ℂ) else 0) * (if j = k ∧ d 0 = d 2 then (1 : ℂ) else 0) else 0) from by
    simp only [hpt]
    simp only [Finset.mul_sum]]
  rw [sum_closedWalk_pairing_three]
  rcases eq_or_ne N 0 with hN | hN
  · subst hN; simp
  · have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast hN
    field_simp

/-- **Exact length-four trace expectation**: `N` times the two non-crossing label pairings plus
`N⁻¹` times the crossing label pairing. -/
theorem integral_trace_gueWord_four (i j k l : ι) :
    ∫ x : EuclideanSpace ℝ (GUECoord ι N), Matrix.trace (gueWord [i, j, k, l] x)
        ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) =
      (N : ℂ) * ((if i = j then (1 : ℂ) else 0) * (if k = l then (1 : ℂ) else 0) +
        (if i = l then (1 : ℂ) else 0) * (if j = k then (1 : ℂ) else 0)) +
      ((N : ℂ)⁻¹) * ((if i = k then (1 : ℂ) else 0) * (if j = l then (1 : ℂ) else 0)) := by
  rw [integral_trace_gueWord_eq_wick_sum, gueWickClosedWalk_four]
  simp only [gueWick_four_path]
  have hstep : (∑ a : Fin N, ∑ d : (Fin 4 → Fin N),
        if d 3 = a then ((N : ℂ)⁻¹ ^ 2) * ((if i = j ∧ a = d 1 then (1 : ℂ) else 0) * (if k = l ∧ d 1 = d 3 then (1 : ℂ) else 0) + (if i = k ∧ a = d 2 ∧ d 0 = d 1 then (1 : ℂ) else 0) * (if j = l ∧ d 0 = d 3 ∧ d 1 = d 2 then (1 : ℂ) else 0) + (if i = l ∧ a = d 3 ∧ d 0 = d 2 then (1 : ℂ) else 0) * (if j = k ∧ d 0 = d 2 then (1 : ℂ) else 0)) else 0)
      = ∑ a : Fin N, ∑ d : (Fin 4 → Fin N),
          ((if d 3 = a then (((N : ℂ)⁻¹) * (if i = j ∧ a = d 1 then (1 : ℂ) else 0)) * (((N : ℂ)⁻¹) * (if k = l ∧ d 1 = d 3 then (1 : ℂ) else 0)) else 0) +
            ((if d 3 = a then (((N : ℂ)⁻¹) * (if i = k ∧ a = d 2 ∧ d 0 = d 1 then (1 : ℂ) else 0)) * (((N : ℂ)⁻¹) * (if j = l ∧ d 0 = d 3 ∧ d 1 = d 2 then (1 : ℂ) else 0)) else 0) +
             (if d 3 = a then (((N : ℂ)⁻¹) * (if i = l ∧ a = d 3 ∧ d 0 = d 2 then (1 : ℂ) else 0)) * (((N : ℂ)⁻¹) * (if j = k ∧ d 0 = d 2 then (1 : ℂ) else 0)) else 0))) := by
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun d _ => ?_
    by_cases h : d 3 = a
    · rw [ite_eq_left h, ite_eq_left h, ite_eq_left h, ite_eq_left h]
      ring
    · rw [ite_eq_right h, ite_eq_right h, ite_eq_right h, ite_eq_right h]
      simp
  rw [hstep]
  simp only [Finset.sum_add_distrib]
  simp only [sum_closedWalk_product_one, sum_closedWalk_product_two, sum_closedWalk_product_three]
  ring

/-- **Normalized length-four limit with explicit error**: for every fixed four-letter word the
normalized expectation equals the sum over the two non-crossing label pairings plus an explicit
`N⁻²` correction from the crossing pairing.  This identifies the semicircular (Catalan `2`) leading
term for length four. -/
theorem integral_gueNormTrace_four (i j k l : ι) (hN : 0 < N) :
    ∫ x : EuclideanSpace ℝ (GUECoord ι N), gueNormTrace [i, j, k, l] x
        ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) =
      ((if i = j then (1 : ℂ) else 0) * (if k = l then (1 : ℂ) else 0) +
        (if i = l then (1 : ℂ) else 0) * (if j = k then (1 : ℂ) else 0)) +
      ((N : ℂ)⁻¹) ^ 2 *
        ((if i = k then (1 : ℂ) else 0) * (if j = l then (1 : ℂ) else 0)) := by
  have h := integral_trace_gueWord_four (N := N) i j k l
  have h2 : ∫ x : EuclideanSpace ℝ (GUECoord ι N), gueNormTrace [i, j, k, l] x
      ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) =
      ((N : ℂ)⁻¹) * ∫ x : EuclideanSpace ℝ (GUECoord ι N),
        Matrix.trace (gueWord [i, j, k, l] x)
        ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) := by
    simp only [gueNormTrace]
    rw [integral_const_mul]
  rw [h2, h]
  have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
  field_simp

/-- **Fourth normalized moment of a single GUE matrix**: `E[tr_N (G_i^4)] = 2 + N^-2`, the
Catalan number `C_2 = 2` plus the explicit crossing correction. -/
theorem integral_gueNormTrace_four_self (i : ι) (hN : 0 < N) :
    ∫ x : EuclideanSpace ℝ (GUECoord ι N), gueNormTrace [i, i, i, i] x
        ∂(stdGaussian (EuclideanSpace ℝ (GUECoord ι N))) = 2 + ((N : ℂ)⁻¹) ^ 2 := by
  have h := integral_gueNormTrace_four (N := N) i i i i hN
  rw [h]
  simp
  norm_num

end

end GUEStrongConvergence
