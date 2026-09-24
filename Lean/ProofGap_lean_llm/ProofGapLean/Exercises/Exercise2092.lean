import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise2092
noncomputable section

def Family (U : Set ℝ) (f : ℝ → ℝ) :=
  {F : ℝ → ℝ | ∀ x ∈ U, HasDerivAt F (f x) x}
def Regular (U : Set ℝ) :=
  IsOpen U ∧ IsPreconnected U ∧ U.Nonempty ∧ ∀ x ∈ U, x ≠ 0
def term (a : ℕ → ℝ) (k : ℕ) (x : ℝ) :=
  a k * Real.exp x / x ^ k
def invPoly (n : ℕ) (a : ℕ → ℝ) (x : ℝ) :=
  ∑ k ∈ Finset.range (n + 1), a k / x ^ k
def Cancellation (n : ℕ) (a : ℕ → ℝ) : Prop :=
  ∑ k ∈ Finset.range n, a (k + 1) / (Nat.factorial k : ℝ) = 0
def ReductionStep (U : Set ℝ) (a : ℕ → ℝ) (k : ℕ) :=
  {F : ℝ → ℝ | ∃ G ∈ Family U
      (fun x => Real.exp x / x ^ (k - 1)), ∃ C, ∀ x ∈ U,
    F x = -a k / ((k : ℝ) - 1) * Real.exp x / x ^ (k - 1) +
      a k / ((k : ℝ) - 1) * G x + C}
def elementaryTerm (a : ℕ → ℝ) (k : ℕ) (x : ℝ) :=
  -a k * Real.exp x *
    ∑ r ∈ Finset.Icc 1 (k - 1),
      (Nat.factorial (k - r - 1) : ℝ) /
        (Nat.factorial (k - 1) : ℝ) / x ^ (k - r)
def ReductionClosed (U : Set ℝ) (a : ℕ → ℝ) (k : ℕ) :=
  {F : ℝ → ℝ | ∃ L ∈ Family U (fun x => Real.exp x / x), ∃ C,
    ∀ x ∈ U, F x = elementaryTerm a k x +
      a k / (Nat.factorial (k - 1) : ℝ) * L x + C}
def SumFamily (U : Set ℝ) (n : ℕ) (a : ℕ → ℝ) :=
  {F : ℝ → ℝ | ∃ H : Fin (n + 1) → ℝ → ℝ,
    (∀ k : Fin (n + 1), H k ∈ Family U (term a k)) ∧ ∃ C, ∀ x ∈ U,
      F x = ∑ k, H k x + C}
def elementaryPrimitive (n : ℕ) (a : ℕ → ℝ) (x : ℝ) :=
  a 0 * Real.exp x +
    ∑ k ∈ Finset.Icc 2 n, elementaryTerm a k x
def Translates (U : Set ℝ) (p : ℝ → ℝ) :=
  {F : ℝ → ℝ | ∃ C, ∀ x ∈ U, F x = p x + C}

private theorem term_continuousAt (a : ℕ → ℝ) (k : ℕ) {x : ℝ} (hx : x ≠ 0) :
    ContinuousAt (term a k) x := by
  unfold term
  exact (continuousAt_const.mul Real.continuous_exp.continuousAt).div
    (continuousAt_id.pow k) (pow_ne_zero k hx)

private theorem term_continuousOn (U : Set ℝ) (a : ℕ → ℝ) (k : ℕ)
    (hU : Regular U) : ContinuousOn (term a k) U := by
  intro x hx
  exact (term_continuousAt a k (hU.2.2.2 x hx)).continuousWithinAt

private theorem family_term_nonempty (U : Set ℝ) (a : ℕ → ℝ) (k : ℕ)
    (hU : Regular U) : (Family U (term a k)).Nonempty := by
  rcases hU.2.2.1 with ⟨u, hu⟩
  let H : ℝ → ℝ := fun x => ∫ t in u..x, term a k t
  refine ⟨H, ?_⟩
  intro x hx
  have hcont := term_continuousOn U a k hU
  have hsub : Set.uIcc u x ⊆ U := hU.2.1.ordConnected.uIcc_subset hu hx
  have hint : IntervalIntegrable (term a k) MeasureTheory.volume u x :=
    (hcont.mono hsub).intervalIntegrable
  have hmeas : StronglyMeasurableAtFilter
      (term a k) (nhds x) MeasureTheory.volume :=
    hcont.stronglyMeasurableAtFilter hU.1 x hx
  have hcx : ContinuousAt (term a k) x := term_continuousAt a k (hU.2.2.2 x hx)
  exact intervalIntegral.integral_hasDerivAt_right hint hmeas hcx

private theorem family_eq_translates_of_mem (U : Set ℝ) (f p : ℝ → ℝ)
    (hU : Regular U) (hp : p ∈ Family U f) : Family U f = Translates U p := by
  ext F
  constructor
  · intro hF
    have hFd : DifferentiableOn ℝ F U := fun x hx =>
      (hF x hx).differentiableAt.differentiableWithinAt
    have hpd : DifferentiableOn ℝ p U := fun x hx =>
      (hp x hx).differentiableAt.differentiableWithinAt
    obtain ⟨C, hC⟩ := hU.1.exists_eq_add_of_deriv_eq hU.2.1 hFd hpd fun x hx =>
      (hF x hx).deriv.trans (hp x hx).deriv.symm
    exact ⟨C, hC⟩
  · rintro ⟨C, hC⟩
    intro x hx
    apply ((hp x hx).add_const C).congr_of_eventuallyEq
    filter_upwards [hU.1.mem_nhds hx] with y hy
    exact hC y hy

private theorem sum_terms_eq (n : ℕ) (a : ℕ → ℝ) (x : ℝ) :
    (∑ k : Fin (n + 1), term a k x) =
      (∑ k ∈ Finset.range (n + 1), a k / x ^ k) * Real.exp x := by
  rw [Finset.sum_fin_eq_sum_range, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [term]
  rw [dif_pos (Finset.mem_range.mp hk)]
  ring

private theorem sum_member_family (U : Set ℝ) (n : ℕ) (a : ℕ → ℝ)
    (H : Fin (n + 1) → ℝ → ℝ)
    (hH : ∀ k : Fin (n + 1), H k ∈ Family U (term a k)) :
    (fun x => ∑ k, H k x) ∈ Family U (fun x =>
      (∑ k ∈ Finset.range (n + 1), a k / x ^ k) * Real.exp x) := by
  intro x hx
  exact (HasDerivAt.fun_sum (u := Finset.univ) fun k _ => hH k x hx).congr_deriv
    (sum_terms_eq n a x)

private theorem sum_Icc_two_eq_shift (k : ℕ) (f : ℕ → ℝ) (hk : 1 ≤ k) :
    (∑ r ∈ Finset.Icc 2 k, f r) =
      ∑ s ∈ Finset.Icc 1 (k - 1), f (s + 1) := by
  symm
  apply Finset.sum_bij (fun s _ => s + 1)
  · intro s hs
    simp only [Finset.mem_Icc] at hs ⊢
    omega
  · intro s₁ hs₁ s₂ hs₂ heq
    omega
  · intro r hr
    refine ⟨r - 1, ?_, ?_⟩
    · simp only [Finset.mem_Icc] at hr ⊢
      omega
    · have hr2 : 2 ≤ r := (Finset.mem_Icc.mp hr).1
      omega
  · intro s hs
    rfl

private theorem sum_Icc_two_succ (n : ℕ) (f : ℕ → ℝ) (hn : 1 ≤ n) :
    (∑ k ∈ Finset.Icc 2 (n + 1), f k) =
      (∑ k ∈ Finset.Icc 2 n, f k) + f (n + 1) := by
  rw [← Finset.insert_Icc_right_eq_Icc_add_one (by omega : 2 ≤ n + 1)]
  rw [Finset.sum_insert]
  · ring
  · simp

private theorem cancellation_sum_succ (m : ℕ) (a : ℕ → ℝ) :
    (∑ k ∈ Finset.range (m + 1),
        a (k + 1) / (Nat.factorial k : ℝ)) =
      a 1 + ∑ k ∈ Finset.Icc 2 (m + 1),
        a k / (Nat.factorial (k - 1) : ℝ) := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [show m + 1 + 1 = (m + 1) + 1 by rfl, Finset.sum_range_succ, ih]
      rw [sum_Icc_two_succ (m + 1) _ (by omega)]
      simp only [Nat.add_sub_cancel]
      ring

private theorem cancellation_succ_iff (m : ℕ) (a : ℕ → ℝ) :
    Cancellation (m + 1) a ↔
      a 1 + ∑ k ∈ Finset.Icc 2 (m + 1),
        a k / (Nat.factorial (k - 1) : ℝ) = 0 := by
  unfold Cancellation
  rw [cancellation_sum_succ]

private def coeffSum (k : ℕ) (x : ℝ) :=
  ∑ r ∈ Finset.Icc 1 (k - 1),
    (Nat.factorial (k - r - 1) : ℝ) /
      (Nat.factorial (k - 1) : ℝ) / x ^ (k - r)

private theorem coeffSum_succ (k : ℕ) (x : ℝ) (hk : 2 ≤ k) :
    coeffSum (k + 1) x =
      1 / (k : ℝ) / x ^ k + 1 / (k : ℝ) * coeffSum k x := by
  unfold coeffSum
  simp only [Nat.add_sub_cancel]
  rw [Finset.Icc_eq_cons_Ioc (by omega : 1 ≤ k), Finset.sum_cons]
  rw [← Finset.Icc_add_one_left_eq_Ioc]
  rw [one_add_one_eq_two]
  rw [sum_Icc_two_eq_shift k _ (by omega)]
  have hk0 : (k : ℝ) ≠ 0 := by positivity
  have hfac : (Nat.factorial k : ℝ) =
      (k : ℝ) * (Nat.factorial (k - 1) : ℝ) := by
    rw [show k = (k - 1) + 1 by omega, Nat.factorial_succ]
    push_cast
    ring
  have hfac0 : (Nat.factorial (k - 1) : ℝ) ≠ 0 := by positivity
  have hcoeff (m : ℕ) :
      (Nat.factorial m : ℝ) / (Nat.factorial k : ℝ) =
        1 / (k : ℝ) *
          ((Nat.factorial m : ℝ) / (Nat.factorial (k - 1) : ℝ)) := by
    rw [hfac]
    field_simp [hk0, hfac0]
  rw [Finset.mul_sum]
  apply congrArg₂ (· + ·)
  · have h₁ : k + 1 - 1 = k := by omega
    rw [h₁, hcoeff]
    simp [hfac0]
  · apply Finset.sum_congr rfl
    intro s hs
    have h₁ : k + 1 - (s + 1) = k - s := by omega
    rw [h₁, hcoeff]
    ring

private theorem elementaryTerm_succ (a : ℕ → ℝ) (k : ℕ) (x : ℝ) (hk : 2 ≤ k) :
    elementaryTerm a (k + 1) x =
      -a (k + 1) / (k : ℝ) * Real.exp x / x ^ k +
        a (k + 1) / (k : ℝ) * elementaryTerm (fun _ => 1) k x := by
  change -a (k + 1) * Real.exp x * coeffSum (k + 1) x = _
  rw [coeffSum_succ k x hk]
  change _ = _ + _ * (-1 * Real.exp x * coeffSum k x)
  ring

private def stepBase (a : ℕ → ℝ) (k : ℕ) (G : ℝ → ℝ) (x : ℝ) :=
  -a k / ((k : ℝ) - 1) * Real.exp x / x ^ (k - 1) +
    a k / ((k : ℝ) - 1) * G x

private theorem stepBase_member (U : Set ℝ) (a : ℕ → ℝ) (k : ℕ) (G : ℝ → ℝ)
    (hU : Regular U) (hk : 2 ≤ k)
    (hG : G ∈ Family U (fun x => Real.exp x / x ^ (k - 1))) :
    stepBase a k G ∈ Family U (term a k) := by
  intro x hx
  have hx0 := hU.2.2.2 x hx
  have hkR : (k : ℝ) - 1 ≠ 0 := by
    apply sub_ne_zero.mpr
    exact ne_of_gt (by exact_mod_cast (show 1 < k by omega))
  have hpow := (hasDerivAt_id x).pow (k - 1)
  have hquot := ((Real.hasDerivAt_exp x).const_mul
    (-a k / ((k : ℝ) - 1))).div hpow (pow_ne_zero _ hx0)
  have hd := hquot.add
    ((hG x hx).const_mul (a k / ((k : ℝ) - 1)))
  have hd' := hd.congr_deriv (g' := term a k x) (by
    simp only [term, Pi.pow_apply, id_eq]
    have hkone : 1 ≤ k := by omega
    have hmone : 1 ≤ k - 1 := by omega
    have hcast : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
      rw [Nat.cast_sub hkone]
      norm_num
    have hpowk : x ^ k = x ^ (k - 1) * x := by
      nth_rw 1 [← Nat.sub_add_cancel hkone]
      rw [pow_succ]
    have hpowm : x ^ (k - 1) = x ^ (k - 1 - 1) * x := by
      nth_rw 1 [← Nat.sub_add_cancel hmone]
      rw [pow_succ]
    rw [hcast, hpowk, hpowm]
    field_simp [hx0, hkR]
    ring)
  simpa only [stepBase, id_eq] using hd'

private def closedBase (a : ℕ → ℝ) (k : ℕ) (L : ℝ → ℝ) (x : ℝ) :=
  elementaryTerm a k x +
    a k / (Nat.factorial (k - 1) : ℝ) * L x

private theorem closedBase_two (a : ℕ → ℝ) (L : ℝ → ℝ) :
    closedBase a 2 L = stepBase a 2 L := by
  funext x
  simp [closedBase, stepBase, elementaryTerm]
  ring

private theorem closedBase_succ (a : ℕ → ℝ) (k : ℕ) (L : ℝ → ℝ) (hk : 2 ≤ k) :
    closedBase a (k + 1) L =
      stepBase a (k + 1) (closedBase (fun _ => 1) k L) := by
  funext x
  rw [show closedBase a (k + 1) L x =
      elementaryTerm a (k + 1) x +
        a (k + 1) / (Nat.factorial k : ℝ) * L x by rfl]
  rw [elementaryTerm_succ a k x hk]
  simp only [stepBase, closedBase, Nat.cast_add, Nat.cast_one, add_sub_cancel_right]
  rw [show k + 1 - 1 = k by omega]
  have hk0 : (k : ℝ) ≠ 0 := by positivity
  have hfac0 : (Nat.factorial (k - 1) : ℝ) ≠ 0 := by positivity
  have hfac : (Nat.factorial k : ℝ) =
      (k : ℝ) * (Nat.factorial (k - 1) : ℝ) := by
    rw [show k = (k - 1) + 1 by omega, Nat.factorial_succ]
    push_cast
    ring
  rw [hfac]
  field_simp [hk0, hfac0]
  ring

private theorem closedBase_member_add (U : Set ℝ) (a : ℕ → ℝ) (m : ℕ)
    (L : ℝ → ℝ) (hU : Regular U)
    (hL : L ∈ Family U (fun x => Real.exp x / x)) :
    closedBase a (2 + m) L ∈ Family U (term a (2 + m)) := by
  induction m generalizing a with
  | zero =>
      have hstep := stepBase_member U a 2 L hU (by omega) (by simpa using hL)
      rw [Nat.add_zero, closedBase_two]
      exact hstep
  | succ m ih =>
      let one : ℕ → ℝ := fun _ => 1
      have hG' := ih one
      have hG : closedBase one (2 + m) L ∈
          Family U (fun x => Real.exp x / x ^ (2 + m)) := by
        intro x hx
        exact (hG' x hx).congr_deriv (by simp [term, one])
      have hstep := stepBase_member U a ((2 + m) + 1)
        (closedBase one (2 + m) L) hU (by omega) hG
      rw [show 2 + (m + 1) = (2 + m) + 1 by omega]
      rw [closedBase_succ a (2 + m) L (by omega)]
      exact hstep

private theorem closedBase_member (U : Set ℝ) (a : ℕ → ℝ) (k : ℕ)
    (L : ℝ → ℝ) (hU : Regular U) (hk : 2 ≤ k)
    (hL : L ∈ Family U (fun x => Real.exp x / x)) :
    closedBase a k L ∈ Family U (term a k) := by
  rw [← show 2 + (k - 2) = k by omega]
  exact closedBase_member_add U a (k - 2) L hU hL

private def component (a : ℕ → ℝ) (L : ℝ → ℝ) (k : ℕ) : ℝ → ℝ :=
  if k = 0 then fun x => a 0 * Real.exp x
  else if k = 1 then fun x => a 1 * L x
  else closedBase a k L

private theorem component_member (U : Set ℝ) (a : ℕ → ℝ) (L : ℝ → ℝ)
    (k : ℕ) (hU : Regular U)
    (hL : L ∈ Family U (fun x => Real.exp x / x)) :
    component a L k ∈ Family U (term a k) := by
  rcases k with _ | k
  · intro x hx
    simpa [component, term] using (Real.hasDerivAt_exp x).const_mul (a 0)
  · rcases k with _ | k
    · intro x hx
      simpa [component] using ((hL x hx).const_mul (a 1)).congr_deriv (by
        simp only [term]
        ring)
    · simpa [component] using closedBase_member U a (k + 2) L hU (by omega) hL

private theorem component_sum_range_succ (m : ℕ) (a : ℕ → ℝ) (L : ℝ → ℝ)
    (x : ℝ) :
    (∑ k ∈ Finset.range ((m + 1) + 1), component a L k x) =
      elementaryPrimitive (m + 1) a x +
        (a 1 + ∑ k ∈ Finset.Icc 2 (m + 1),
          a k / (Nat.factorial (k - 1) : ℝ)) * L x := by
  induction m with
  | zero =>
      simp [Finset.sum_range_succ, component, elementaryPrimitive]
  | succ m ih =>
      rw [Finset.sum_range_succ, ih]
      have hcomponent : component a L (m + 1 + 1) x =
          closedBase a (m + 1 + 1) L x := by
        simp [component]
      rw [hcomponent]
      simp only [elementaryPrimitive]
      rw [sum_Icc_two_succ (m + 1) (fun k => elementaryTerm a k x) (by omega)]
      rw [sum_Icc_two_succ (m + 1)
        (fun k => a k / (Nat.factorial (k - 1) : ℝ)) (by omega)]
      simp only [closedBase]
      ring

private theorem component_sum_fin_succ (m : ℕ) (a : ℕ → ℝ) (L : ℝ → ℝ)
    (x : ℝ) :
    (∑ k : Fin ((m + 1) + 1), component a L k x) =
      elementaryPrimitive (m + 1) a x +
        (a 1 + ∑ k ∈ Finset.Icc 2 (m + 1),
          a k / (Nat.factorial (k - 1) : ℝ)) * L x := by
  rw [Finset.sum_fin_eq_sum_range]
  calc
    (∑ k ∈ Finset.range ((m + 1) + 1),
        if h : k < (m + 1) + 1 then component a L (↑(⟨k, h⟩ : Fin _)) x else 0) =
        ∑ k ∈ Finset.range ((m + 1) + 1), component a L k x := by
          apply Finset.sum_congr rfl
          intro k hk
          rw [dif_pos (Finset.mem_range.mp hk)]
    _ = _ := component_sum_range_succ m a L x

private theorem family_eq_reductionClosed (U : Set ℝ) (a : ℕ → ℝ) (k : ℕ)
    (hU : Regular U) (hk : 2 ≤ k) :
    Family U (term a k) = ReductionClosed U a k := by
  let one : ℕ → ℝ := fun _ => 1
  obtain ⟨L, hL'⟩ := family_term_nonempty U one 1 hU
  have hL : L ∈ Family U (fun x => Real.exp x / x) := by
    intro x hx
    exact (hL' x hx).congr_deriv (by simp [term, one])
  have hbase := closedBase_member U a k L hU hk hL
  ext F
  constructor
  · intro hF
    have htrans : F ∈ Translates U (closedBase a k L) := by
      rw [← family_eq_translates_of_mem U _ _ hU hbase]
      exact hF
    rcases htrans with ⟨C, hC⟩
    exact ⟨L, hL, C, by simpa [closedBase] using hC⟩
  · rintro ⟨L', hL', C, hC⟩
    have hbase' := closedBase_member U a k L' hU hk hL'
    rw [family_eq_translates_of_mem U _ _ hU hbase']
    exact ⟨C, by simpa [closedBase] using hC⟩

theorem gap1 (U : Set ℝ) (n : ℕ) (a : ℕ → ℝ) (hU : Regular U) :
    ∀ k, 2 ≤ k → k ≤ n →
      Family U (term a k) = ReductionStep U a k := by
  intro k hk hkn
  let one : ℕ → ℝ := fun _ => 1
  obtain ⟨G, hG'⟩ := family_term_nonempty U one (k - 1) hU
  have hG : G ∈ Family U (fun x => Real.exp x / x ^ (k - 1)) := by
    intro x hx
    exact (hG' x hx).congr_deriv (by simp [term, one])
  have hbase := stepBase_member U a k G hU hk hG
  ext F
  constructor
  · intro hF
    have htrans : F ∈ Translates U (stepBase a k G) := by
      rw [← family_eq_translates_of_mem U _ _ hU hbase]
      exact hF
    rcases htrans with ⟨C, hC⟩
    exact ⟨G, hG, C, by simpa [stepBase] using hC⟩
  · rintro ⟨G', hG', C, hC⟩
    have hbase' := stepBase_member U a k G' hU hk hG'
    rw [family_eq_translates_of_mem U _ _ hU hbase']
    exact ⟨C, by simpa [stepBase] using hC⟩
theorem gap2 (U : Set ℝ) (n : ℕ) (a : ℕ → ℝ) (hU : Regular U) :
    ∀ k, 2 ≤ k → k ≤ n →
      ReductionStep U a k = ReductionClosed U a k := by
  intro k hk hkn
  exact (gap1 U n a hU k hk hkn).symm.trans
    (family_eq_reductionClosed U a k hU hk)
theorem gap3 (U : Set ℝ) (n : ℕ) (a : ℕ → ℝ) (hU : Regular U) :
    ∀ k, 2 ≤ k → k ≤ n →
      Family U (term a k) = ReductionClosed U a k := by
  intro k hk hkn
  exact (gap1 U n a hU k hk hkn).trans (gap2 U n a hU k hk hkn)
theorem gap4 (U : Set ℝ) (n : ℕ) (a : ℕ → ℝ) (hU : Regular U) :
    ∀ k, 2 ≤ k → k ≤ n →
      Family U (term a k) = ReductionClosed U a k := by
  exact gap3 U n a hU
theorem gap5 (U : Set ℝ) (n : ℕ) (a : ℕ → ℝ) (hU : Regular U) :
    Family U (fun x => invPoly n a x * Real.exp x) =
      Family U (fun x =>
        (∑ k ∈ Finset.range (n + 1), a k / x ^ k) * Real.exp x) := by
  rfl
theorem gap6 (U : Set ℝ) (n : ℕ) (a : ℕ → ℝ) (hU : Regular U) :
    Family U (fun x =>
      (∑ k ∈ Finset.range (n + 1), a k / x ^ k) * Real.exp x) =
      SumFamily U n a := by
  ext F
  constructor
  · intro hF
    let H : Fin (n + 1) → ℝ → ℝ := fun k =>
      Classical.choose (family_term_nonempty U a k hU)
    have hH : ∀ k : Fin (n + 1), H k ∈ Family U (term a k) := fun k =>
      Classical.choose_spec (family_term_nonempty U a k hU)
    have hsum := sum_member_family U n a H hH
    have htrans : F ∈ Translates U (fun x => ∑ k, H k x) := by
      rw [← family_eq_translates_of_mem U _ _ hU hsum]
      exact hF
    exact ⟨H, hH, htrans⟩
  · rintro ⟨H, hH, htrans⟩
    have hsum := sum_member_family U n a H hH
    rw [family_eq_translates_of_mem U _ _ hU hsum]
    exact htrans
theorem gap7 (U : Set ℝ) (n : ℕ) (a : ℕ → ℝ) (hU : Regular U) :
    Family U (fun x => invPoly n a x * Real.exp x) =
      SumFamily U n a := by
  exact (gap5 U n a hU).trans (gap6 U n a hU)
theorem gap8 (U : Set ℝ) (n : ℕ) (a : ℕ → ℝ) (hU : Regular U) :
    Cancellation n a ↔
      Family U (fun x => invPoly n a x * Real.exp x) =
        Translates U (elementaryPrimitive n a) := by
  rcases n with _ | m
  · have hp : elementaryPrimitive 0 a ∈
        Family U (fun x => invPoly 0 a x * Real.exp x) := by
      intro x hx
      rw [show elementaryPrimitive 0 a = (fun y => a 0 * Real.exp y) by
        funext y
        simp [elementaryPrimitive]]
      simpa [invPoly] using
        (Real.hasDerivAt_exp x).const_mul (a 0)
    constructor
    · intro h
      exact family_eq_translates_of_mem U _ _ hU hp
    · intro h
      simp [Cancellation]
  · let one : ℕ → ℝ := fun _ => 1
    obtain ⟨L, hL'⟩ := family_term_nonempty U one 1 hU
    have hL : L ∈ Family U (fun x => Real.exp x / x) := by
      intro x hx
      exact (hL' x hx).congr_deriv (by simp [term, one])
    let H : Fin ((m + 1) + 1) → ℝ → ℝ := fun k => component a L k
    have hH : ∀ k : Fin ((m + 1) + 1), H k ∈ Family U (term a k) := by
      intro k
      simpa [H] using component_member U a L k hU hL
    have hsum' := sum_member_family U (m + 1) a H hH
    have hsum : (fun x => ∑ k, H k x) ∈
        Family U (fun x => invPoly (m + 1) a x * Real.exp x) := by
      simpa only [invPoly] using hsum'
    let c : ℝ := a 1 + ∑ k ∈ Finset.Icc 2 (m + 1),
      a k / (Nat.factorial (k - 1) : ℝ)
    have hid (x : ℝ) : (∑ k, H k x) =
        elementaryPrimitive (m + 1) a x + c * L x := by
      simpa [H, c] using component_sum_fin_succ m a L x
    constructor
    · intro hc
      have hc0 : c = 0 := by
        simpa [c] using (cancellation_succ_iff m a).mp hc
      have hfun : (fun x => ∑ k, H k x) = elementaryPrimitive (m + 1) a := by
        funext x
        rw [hid x, hc0]
        ring
      have hp : elementaryPrimitive (m + 1) a ∈
          Family U (fun x => invPoly (m + 1) a x * Real.exp x) := by
        rw [← hfun]
        exact hsum
      exact family_eq_translates_of_mem U _ _ hU hp
    · intro heq
      have hself : elementaryPrimitive (m + 1) a ∈
          Translates U (elementaryPrimitive (m + 1) a) := by
        exact ⟨0, by simp⟩
      have hp : elementaryPrimitive (m + 1) a ∈
          Family U (fun x => invPoly (m + 1) a x * Real.exp x) := by
        rw [heq]
        exact hself
      rcases hU.2.2.1 with ⟨u, hu⟩
      have hplus : HasDerivAt
          (fun x => elementaryPrimitive (m + 1) a x + c * L x)
          (invPoly (m + 1) a u * Real.exp u +
            c * (Real.exp u / u)) u :=
        (hp u hu).add ((hL u hu).const_mul c)
      have hsumViaPlus : HasDerivAt (fun x => ∑ k, H k x)
          (invPoly (m + 1) a u * Real.exp u +
            c * (Real.exp u / u)) u := by
        apply hplus.congr_of_eventuallyEq
        exact Filter.Eventually.of_forall hid
      have hder := hsumViaPlus.unique (hsum u hu)
      have hcprod : c * (Real.exp u / u) = 0 := by
        linarith
      have hquot : Real.exp u / u ≠ 0 :=
        div_ne_zero (Real.exp_ne_zero u) (hU.2.2.2 u hu)
      have hc0 : c = 0 := (mul_eq_zero.mp hcprod).resolve_right hquot
      exact (cancellation_succ_iff m a).mpr (by simpa [c] using hc0)
theorem gap9 (n : ℕ) (a : ℕ → ℝ) (hn : 1 ≤ n) :
    Cancellation n a ↔
      a 1 + ∑ k ∈ Finset.Icc 2 n,
        a k / (Nat.factorial (k - 1) : ℝ) = 0 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  exact cancellation_succ_iff m a
theorem gap10 (n : ℕ) (a : ℕ → ℝ) :
    a ∈ {b : ℕ → ℝ | Cancellation n b} ↔ Cancellation n a := by
  rfl

end
end ProofGap.Exercise2092
