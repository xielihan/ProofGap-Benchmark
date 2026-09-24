import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Order.Filter.Tendsto
import Mathlib.Topology.Defs.Filter
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise2057
noncomputable section

def q (a b x : ℝ) := a * Real.sin x + b * Real.cos x
def radius (a b : ℝ) := Real.sqrt (a ^ 2 + b ^ 2)
def Family (U : Set ℝ) (f : ℝ → ℝ) :=
  {F : ℝ → ℝ | ∀ x ∈ U, HasDerivAt F (f x) x}
def Regular (U : Set ℝ) (a b : ℝ) :=
  IsOpen U ∧ IsPreconnected U ∧ ∀ x ∈ U, q a b x ≠ 0
def PhaseData (a b α : ℝ) : Prop :=
  (∀ x, q a b x = radius a b * Real.sin (x + α)) ∧
    Real.sin α = b / radius a b ∧ Real.cos α = a / radius a b
def ScaledFamily (U : Set ℝ) (c : ℝ) (f : ℝ → ℝ) :=
  {F : ℝ → ℝ | ∃ G ∈ Family U f, ∀ x ∈ U, F x = c * G x}
def recurrenceTerm (a b : ℝ) (n : ℕ) (x : ℝ) :=
  (b * Real.sin x - a * Real.cos x) /
    (((n : ℝ) - 1) * (a ^ 2 + b ^ 2) * q a b x ^ (n - 1))
def RecurrenceFamily (U : Set ℝ) (a b : ℝ) (n : ℕ) :=
  {F : ℝ → ℝ | ∃ G ∈ Family U (fun x => 1 / q a b x ^ (n - 2)),
    ∃ C, ∀ x ∈ U, F x = recurrenceTerm a b n x +
      ((n : ℝ) - 2) / (((n : ℝ) - 1) * (a ^ 2 + b ^ 2)) * G x + C}
def ImplicitRecurrenceFamily (U : Set ℝ) (a b : ℝ) (n : ℕ) :=
  {F : ℝ → ℝ | ∃ G ∈ Family U (fun x => 1 / q a b x ^ (n - 2)),
    ∃ C, ∀ x ∈ U,
      F x =
        (b / (a ^ 2 + b ^ 2) * Real.sin x -
          a / (a ^ 2 + b ^ 2) * Real.cos x) / q a b x ^ (n - 1) +
        (2 - (n : ℝ)) * F x +
        ((n : ℝ) - 2) / (a ^ 2 + b ^ 2) * G x + C}
def PhaseReduction (U : Set ℝ) (a b : ℝ) (n : ℕ) : Prop :=
  ∃ α, PhaseData a b α ∧
    Family U (fun x => 1 / q a b x ^ n) =
      ScaledFamily U (1 / radius a b ^ n)
        (fun x => 1 / Real.sin (x + α) ^ n)
def PhaseIntegrationStep (U : Set ℝ) (a b : ℝ) (n : ℕ) : Prop :=
  ∃ α, PhaseData a b α ∧
    Family U (fun x => 1 / q a b x ^ n) = ImplicitRecurrenceFamily U a b n

private theorem _integration_results (U : Set ℝ) (a b : ℝ) (n : ℕ) (hn : 2 ≤ n)
    (hab : a ≠ 0 ∨ b ≠ 0) (hU : Regular U a b) :
    Family U (fun x => 1 / q a b x ^ n) = ImplicitRecurrenceFamily U a b n ∧
      Family U (fun x => 1 / q a b x ^ n) = RecurrenceFamily U a b n := by
  have hspos : 0 < a ^ 2 + b ^ 2 := by
    rcases hab with ha | hb
    · nlinarith [sq_pos_of_ne_zero ha]
    · nlinarith [sq_pos_of_ne_zero hb]
  have hS : a ^ 2 + b ^ 2 ≠ 0 := ne_of_gt hspos
  have quotient_identity (m : ℕ) (Q P S : ℝ) (hQ : Q ≠ 0)
      (hS0 : S ≠ 0) (hcircle : Q ^ 2 + P ^ 2 = S) :
      (Q * (((m : ℝ) + 1) * S * Q ^ (m + 1)) -
          P * (((m : ℝ) + 1) * S *
            (((m : ℝ) + 1) * Q ^ m * (-P)))) /
          ((((m : ℝ) + 1) * S * Q ^ (m + 1)) ^ 2) =
        1 / Q ^ (m + 2) -
          (m : ℝ) / (((m : ℝ) + 1) * S) * (1 / Q ^ m) := by
    have hc : (m : ℝ) + 1 ≠ 0 := by positivity
    have hpow1 : Q ^ (m + 1) = Q ^ m * Q := by
      simpa using (pow_succ Q m)
    have hpow2 : Q ^ (m + 2) = Q ^ m * Q ^ 2 := by
      rw [pow_add]
    simp only [hpow1, hpow2]
    field_simp [hQ, hS0, hc]
    simp only [← hcircle]
    ring
  have aux (k : ℕ) :
      Family U (fun x => 1 / q a b x ^ (k + 2)) =
          ImplicitRecurrenceFamily U a b (k + 2) ∧
        Family U (fun x => 1 / q a b x ^ (k + 2)) =
          RecurrenceFamily U a b (k + 2) := by
    have hk2 : k + 2 - 2 = k := by omega
    have recurrence_deriv (m : ℕ) (x : ℝ) (hx : x ∈ U) :
        HasDerivAt (recurrenceTerm a b (m + 2))
          (1 / q a b x ^ (m + 2) -
            (m : ℝ) / (((m : ℝ) + 1) * (a ^ 2 + b ^ 2)) *
              (1 / q a b x ^ m)) x := by
      have hqx := hU.2.2 x hx
      have hqd : HasDerivAt (q a b)
          (a * Real.cos x - b * Real.sin x) x := by
        simpa [q, sub_eq_add_neg, mul_assoc] using
          (Real.hasDerivAt_sin x).const_mul a |>.add
            ((Real.hasDerivAt_cos x).const_mul b)
      have hnum : HasDerivAt
          (fun y => b * Real.sin y - a * Real.cos y) (q a b x) x := by
        convert ((Real.hasDerivAt_sin x).const_mul b).sub
          ((Real.hasDerivAt_cos x).const_mul a) using 1 <;>
          simp [q, sub_eq_add_neg] <;> ring
      have hD : ((m : ℝ) + 1) * (a ^ 2 + b ^ 2) ≠ 0 := by positivity
      have hmexp : m + 2 - 1 = m + 1 := by omega
      have hmcast : (((m + 2 : ℕ) : ℝ) - 1) = (m : ℝ) + 1 := by
        norm_num [Nat.cast_add] <;> ring
      have hfun : recurrenceTerm a b (m + 2) =
          ((fun y => b * Real.sin y - a * Real.cos y) /
            fun y => ((m : ℝ) + 1) * (a ^ 2 + b ^ 2) *
              q a b y ^ (m + 1)) := by
        funext y
        change
          (b * Real.sin y - a * Real.cos y) /
              ((((m + 2 : ℕ) : ℝ) - 1) * (a ^ 2 + b ^ 2) *
                q a b y ^ (m + 2 - 1)) =
            (b * Real.sin y - a * Real.cos y) /
              (((m : ℝ) + 1) * (a ^ 2 + b ^ 2) *
                q a b y ^ (m + 1))
        rw [hmexp, hmcast]
      have hcircle :
          q a b x ^ 2 + (b * Real.sin x - a * Real.cos x) ^ 2 =
            a ^ 2 + b ^ 2 := by
        unfold q
        calc
          (a * Real.sin x + b * Real.cos x) ^ 2 +
              (b * Real.sin x - a * Real.cos x) ^ 2 =
            (a ^ 2 + b ^ 2) *
              (Real.sin x ^ 2 + Real.cos x ^ 2) := by ring
          _ = a ^ 2 + b ^ 2 := by
            rw [Real.sin_sq_add_cos_sq]
            ring
      have hqprime :
          a * Real.cos x - b * Real.sin x =
            -(b * Real.sin x - a * Real.cos x) := by ring
      have hmderiv : m + 1 - 1 = m := by omega
      have hmderivcast : ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by
        norm_num [Nat.cast_add]
      have hden : HasDerivAt
          (fun y => ((m : ℝ) + 1) * (a ^ 2 + b ^ 2) *
            q a b y ^ (m + 1))
          (((m : ℝ) + 1) * (a ^ 2 + b ^ 2) *
            (((m : ℝ) + 1) * q a b x ^ m *
              (-(b * Real.sin x - a * Real.cos x)))) x := by
        simpa only [hmderiv, hmderivcast, hqprime] using
          ((hqd.pow (m + 1)).const_mul
            (((m : ℝ) + 1) * (a ^ 2 + b ^ 2)))
      have hdclean : HasDerivAt
          ((fun y => b * Real.sin y - a * Real.cos y) /
            fun y => ((m : ℝ) + 1) * (a ^ 2 + b ^ 2) *
              q a b y ^ (m + 1))
          ((q a b x *
                (((m : ℝ) + 1) * (a ^ 2 + b ^ 2) *
                  q a b x ^ (m + 1)) -
              (b * Real.sin x - a * Real.cos x) *
                (((m : ℝ) + 1) * (a ^ 2 + b ^ 2) *
                  (((m : ℝ) + 1) * q a b x ^ m *
                    (-(b * Real.sin x - a * Real.cos x))))) /
            ((((m : ℝ) + 1) * (a ^ 2 + b ^ 2) *
              q a b x ^ (m + 1)) ^ 2)) x := by
        exact hnum.div hden
          (mul_ne_zero hD (pow_ne_zero _ hqx))
      have hid := quotient_identity m (q a b x)
        (b * Real.sin x - a * Real.cos x) (a ^ 2 + b ^ 2)
        hqx hS hcircle
      rw [hid] at hdclean
      rw [hfun]
      exact hdclean
    have hcoef :
        (((k + 2 : ℕ) : ℝ) - 2) /
            ((((k + 2 : ℕ) : ℝ) - 1) * (a ^ 2 + b ^ 2)) =
          (k : ℝ) / (((k : ℝ) + 1) * (a ^ 2 + b ^ 2)) := by
      norm_num [Nat.cast_add] <;> ring
    have hkexp : k + 2 - 1 = k + 1 := by omega
    have hkcast1 : (((k + 2 : ℕ) : ℝ) - 1) = (k : ℝ) + 1 := by
      norm_num [Nat.cast_add] <;> ring
    have hkcast2 : (((k + 2 : ℕ) : ℝ) - 2) = (k : ℝ) := by
      norm_num [Nat.cast_add] <;> ring
    have hneg : 2 - ((k + 2 : ℕ) : ℝ) = -(k : ℝ) := by
      norm_num [Nat.cast_add] <;> ring
    have hk1 : (k : ℝ) + 1 ≠ 0 := by positivity
    have hrec : Family U (fun x => 1 / q a b x ^ (k + 2)) =
        RecurrenceFamily U a b (k + 2) := by
      classical
      ext F
      simp only [Family, RecurrenceFamily, Set.mem_setOf_eq]
      rw [hcoef]
      constructor
      · intro hF
        by_cases hk : k = 0
        · subst k
          by_cases hne : U.Nonempty
          · rcases hne with ⟨x₀, hx₀⟩
            let H : ℝ → ℝ := fun y => F y - recurrenceTerm a b 2 y
            have hzero : ∀ y ∈ U, HasDerivAt H 0 y := by
              intro y hy
              dsimp [H]
              convert (hF y hy).sub (recurrence_deriv 0 y hy) using 1 <;> simp
            have hdiff : DifferentiableOn ℝ H U := by
              intro y hy
              exact (hzero y hy).differentiableAt.differentiableWithinAt
            have hderiv : ∀ y ∈ U, deriv H y = 0 := by
              intro y hy
              exact (hzero y hy).deriv
            refine ⟨fun y => y, ?_, F x₀ - recurrenceTerm a b 2 x₀, ?_⟩
            · intro y hy
              simpa using hasDerivAt_id y
            · intro y hy
              have hc :=
                hU.1.is_const_of_deriv_eq_zero hU.2.1 hdiff hderiv hy hx₀
              dsimp [H] at hc
              simp at hc ⊢
              linarith
          · refine ⟨fun y => y, ?_, 0, ?_⟩
            · intro y hy
              exact False.elim (hne ⟨y, hy⟩)
            · intro y hy
              exact False.elim (hne ⟨y, hy⟩)
        · have hkpos : 0 < (k : ℝ) := by
            exact_mod_cast Nat.pos_of_ne_zero hk
          let c : ℝ := (k : ℝ) /
            (((k : ℝ) + 1) * (a ^ 2 + b ^ 2))
          have hc : c ≠ 0 := by
            dsimp [c]
            positivity
          refine ⟨fun x => (F x - recurrenceTerm a b (k + 2) x) / c, ?_, 0, ?_⟩
          · intro x hx
            have hrd := recurrence_deriv k x hx
            have hd := (hF x hx).sub hrd
            have hd' : HasDerivAt
                (fun y => F y - recurrenceTerm a b (k + 2) y)
                (c * (1 / q a b x ^ k)) x := by
              convert hd using 1 <;> dsimp [c] <;> ring
            have hddiv := hd'.div_const c
            convert hddiv using 1 <;> simp [hk2, hc]
          · intro x hx
            dsimp [c]
            field_simp [hc]
            ring
      · rintro ⟨G, hG, C, hFG⟩
        intro x hx
        have hrd := recurrence_deriv k x hx
        have hd := hrd.add
          ((hG x hx).const_mul
            ((k : ℝ) / (((k : ℝ) + 1) * (a ^ 2 + b ^ 2)))) |>.add_const C
        have heq : F =ᶠ[nhds x] fun y =>
            recurrenceTerm a b (k + 2) y +
              (k : ℝ) / (((k : ℝ) + 1) * (a ^ 2 + b ^ 2)) * G y + C := by
          filter_upwards [hU.1.mem_nhds hx] with y hy
          exact hFG y hy
        have hdF := hd.congr_of_eventuallyEq heq
        convert hdF using 1 <;> simp [hk2] <;> ring
    have himp : Family U (fun x => 1 / q a b x ^ (k + 2)) =
        ImplicitRecurrenceFamily U a b (k + 2) := by
      rw [hrec]
      unfold RecurrenceFamily ImplicitRecurrenceFamily
      ext F
      simp only [Set.mem_setOf_eq]
      rw [hcoef]
      have hlead (x : ℝ) (hx : x ∈ U) :
          (b / (a ^ 2 + b ^ 2) * Real.sin x -
              a / (a ^ 2 + b ^ 2) * Real.cos x) /
              q a b x ^ (k + 2 - 1) =
            ((k : ℝ) + 1) * recurrenceTerm a b (k + 2) x := by
        have hqx := hU.2.2 x hx
        unfold recurrenceTerm
        simp only [hkexp, hkcast1]
        field_simp [hqx, hS, hk1] <;> ring
      have hGcoef :
          (((k + 2 : ℕ) : ℝ) - 2) / (a ^ 2 + b ^ 2) =
            ((k : ℝ) + 1) *
              ((k : ℝ) / (((k : ℝ) + 1) * (a ^ 2 + b ^ 2))) := by
        rw [hkcast2]
        field_simp [hS, hk1] <;> ring
      constructor
      · rintro ⟨G, hG, C₀, hF⟩
        refine ⟨G, hG, ((k : ℝ) + 1) * C₀, ?_⟩
        intro x hx
        rw [hF x hx]
        simp only [hlead x hx, hneg, hGcoef]
        ring
      · rintro ⟨G, hG, C₀, hF⟩
        refine ⟨G, hG, C₀ / ((k : ℝ) + 1), ?_⟩
        intro x hx
        have heq := hF x hx
        simp only [hlead x hx, hneg, hGcoef] at heq
        let T : ℝ := recurrenceTerm a b (k + 2) x
        let c : ℝ := (k : ℝ) /
          (((k : ℝ) + 1) * (a ^ 2 + b ^ 2))
        have heq' :
            F x = ((k : ℝ) + 1) * T + (-(k : ℝ)) * F x +
              ((k : ℝ) + 1) * c * G x + C₀ := by
          simpa only [T, c] using heq
        have hmul :
            ((k : ℝ) + 1) * F x =
              ((k : ℝ) + 1) * T +
                ((k : ℝ) + 1) * c * G x + C₀ := by
          calc
            ((k : ℝ) + 1) * F x = F x + (k : ℝ) * F x := by ring
            _ = (((k : ℝ) + 1) * T + (-(k : ℝ)) * F x +
                  ((k : ℝ) + 1) * c * G x + C₀) +
                (k : ℝ) * F x :=
              congrArg (fun z : ℝ => z + (k : ℝ) * F x) heq'
            _ = ((k : ℝ) + 1) * T +
                ((k : ℝ) + 1) * c * G x + C₀ := by ring
        have hC :
            ((k : ℝ) + 1) * (C₀ / ((k : ℝ) + 1)) = C₀ := by
          field_simp [hk1] <;> ring
        have hprod :
            ((k : ℝ) + 1) * F x =
              ((k : ℝ) + 1) *
                (T + c * G x + C₀ / ((k : ℝ) + 1)) := by
          calc
            ((k : ℝ) + 1) * F x =
                ((k : ℝ) + 1) * T +
                  ((k : ℝ) + 1) * c * G x + C₀ := hmul
            _ = ((k : ℝ) + 1) * T +
                ((k : ℝ) + 1) * (c * G x) +
                ((k : ℝ) + 1) * (C₀ / ((k : ℝ) + 1)) := by
              rw [hC] <;> ring
            _ = ((k : ℝ) + 1) *
                (T + c * G x + C₀ / ((k : ℝ) + 1)) := by ring
        have htarget :
            F x = T + c * G x + C₀ / ((k : ℝ) + 1) :=
          (mul_left_cancel₀ hk1) hprod
        simpa only [T, c] using htarget
    exact ⟨himp, hrec⟩
  have hnk : n - 2 + 2 = n := Nat.sub_add_cancel hn
  simpa only [hnk] using aux (n - 2)

theorem gap1 (a b : ℝ) : ∃ α, ∀ x, q a b x = radius a b * Real.sin (x + α) := by
  by_cases hzero : a = 0 ∧ b = 0
  · rcases hzero with ⟨rfl, rfl⟩
    exact ⟨0, by simp [q, radius]⟩
  · have hspos : 0 < a ^ 2 + b ^ 2 := by
      rcases not_and_or.mp hzero with ha | hb
      · nlinarith [sq_pos_of_ne_zero ha]
      · nlinarith [sq_pos_of_ne_zero hb]
    have hrpos : 0 < radius a b := Real.sqrt_pos.2 hspos
    have hr : radius a b ≠ 0 := ne_of_gt hrpos
    have hrsq : radius a b ^ 2 = a ^ 2 + b ^ 2 := by
      unfold radius
      exact Real.sq_sqrt (le_of_lt hspos)
    let t := Real.arcsin (b / radius a b)
    have hzsq : (b / radius a b) ^ 2 ≤ 1 := by
      field_simp [hr]
      nlinarith [sq_nonneg a]
    have hzlo : -(1 : ℝ) ≤ b / radius a b := by nlinarith
    have hzhi : b / radius a b ≤ 1 := by nlinarith
    have ht : Real.sin t = b / radius a b := by
      dsimp [t]
      exact Real.sin_arcsin hzlo hzhi
    have hbsin : radius a b * Real.sin t = b := by
      rw [ht]
      field_simp [hr]
    have hcost : 0 ≤ Real.cos t := by
      dsimp [t]
      rw [Real.cos_arcsin]
      exact Real.sqrt_nonneg _
    have hprod_nonneg : 0 ≤ radius a b * Real.cos t :=
      mul_nonneg (le_of_lt hrpos) hcost
    have hpcos_sq : (radius a b * Real.cos t) ^ 2 = a ^ 2 := by
      have hbssq := congrArg (fun z : ℝ => z ^ 2) hbsin
      nlinarith [Real.sin_sq_add_cos_sq t]
    by_cases ha : 0 ≤ a
    · have hpcos : radius a b * Real.cos t = a := by
        nlinarith [hpcos_sq]
      have hc : Real.cos t = a / radius a b := by
        apply (eq_div_iff hr).2
        simpa [mul_comm] using hpcos
      refine ⟨t, ?_⟩
      intro x
      rw [Real.sin_add, ht, hc]
      unfold q
      field_simp [hr]
    · have ha' : a < 0 := lt_of_not_ge ha
      have hpcos : radius a b * Real.cos t = -a := by
        nlinarith [hpcos_sq]
      have hst : Real.sin (Real.pi - t) = Real.sin t := by
        rw [Real.sin_sub]
        simp
      have hct : Real.cos (Real.pi - t) = -Real.cos t := by
        rw [Real.cos_sub]
        simp
      have hs : Real.sin (Real.pi - t) = b / radius a b := by
        rw [hst, ht]
      have hc : Real.cos (Real.pi - t) = a / radius a b := by
        rw [hct]
        apply (eq_div_iff hr).2
        nlinarith
      refine ⟨Real.pi - t, ?_⟩
      intro x
      rw [Real.sin_add, hs, hc]
      unfold q
      field_simp [hr]
theorem gap2 (a b : ℝ) : ∃ α, Real.sin α = b / radius a b := by
  by_cases hr : radius a b = 0
  · exact ⟨0, by simp [hr]⟩
  · obtain ⟨α, hα⟩ := gap1 a b
    refine ⟨α, ?_⟩
    have h0 := hα 0
    simp [q] at h0
    apply (eq_div_iff hr).2
    simpa [mul_comm] using h0.symm
theorem gap3 (a b : ℝ) : ∃ α, Real.cos α = a / radius a b := by
  by_cases hr : radius a b = 0
  · exact ⟨Real.pi / 2, by simp [hr]⟩
  · obtain ⟨α, hα⟩ := gap1 a b
    refine ⟨α, ?_⟩
    have hpi := hα (Real.pi / 2)
    rw [Real.sin_add] at hpi
    simp [q] at hpi
    apply (eq_div_iff hr).2
    simpa [mul_comm] using hpi.symm
theorem gap4 (U : Set ℝ) (a b : ℝ) (n : ℕ) (hab : a ≠ 0 ∨ b ≠ 0)
    (hU : Regular U a b) : PhaseReduction U a b n := by
  obtain ⟨α, hα⟩ := gap1 a b
  have hspos : 0 < a ^ 2 + b ^ 2 := by
    rcases hab with ha | hb
    · nlinarith [sq_pos_of_ne_zero ha]
    · nlinarith [sq_pos_of_ne_zero hb]
  have hr : radius a b ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hspos)
  have hs : Real.sin α = b / radius a b := by
    have h0 := hα 0
    simp [q] at h0
    apply (eq_div_iff hr).2
    simpa [mul_comm] using h0.symm
  have hc : Real.cos α = a / radius a b := by
    have hpi := hα (Real.pi / 2)
    rw [Real.sin_add] at hpi
    simp [q] at hpi
    apply (eq_div_iff hr).2
    simpa [mul_comm] using hpi.symm
  refine ⟨α, ⟨hα, hs, hc⟩, ?_⟩
  ext F
  constructor
  · intro hF
    refine ⟨fun x => radius a b ^ n * F x, ?_, ?_⟩
    · intro x hx
      have hsx : Real.sin (x + α) ≠ 0 := by
        intro hz
        apply hU.2.2 x hx
        rw [hα x, hz]
        simp
      have hd := (hF x hx).const_mul (radius a b ^ n)
      convert hd using 1
      change 1 / Real.sin (x + α) ^ n =
        radius a b ^ n * (1 / q a b x ^ n)
      rw [hα x, mul_pow]
      field_simp [hr, hsx]
    · intro x hx
      field_simp [hr]
  · rintro ⟨G, hG, hFG⟩
    intro x hx
    have hsx : Real.sin (x + α) ≠ 0 := by
      intro hz
      apply hU.2.2 x hx
      rw [hα x, hz]
      simp
    have hd := (hG x hx).const_mul (1 / radius a b ^ n)
    have heq : F =ᶠ[nhds x] fun y => 1 / radius a b ^ n * G y := by
      filter_upwards [hU.1.mem_nhds hx] with y hy
      exact hFG y hy
    have hdF := hd.congr_of_eventuallyEq heq
    convert hdF using 1
    change 1 / q a b x ^ n =
      1 / radius a b ^ n * (1 / Real.sin (x + α) ^ n)
    rw [hα x, mul_pow]
    field_simp [hr, hsx]
theorem gap5 (U : Set ℝ) (a b : ℝ) (n : ℕ) (hn : 2 ≤ n)
    (hab : a ≠ 0 ∨ b ≠ 0) (hU : Regular U a b) :
    PhaseIntegrationStep U a b n := by
  obtain ⟨α, hα⟩ := gap1 a b
  have hspos : 0 < a ^ 2 + b ^ 2 := by
    rcases hab with ha | hb
    · nlinarith [sq_pos_of_ne_zero ha]
    · nlinarith [sq_pos_of_ne_zero hb]
  have hr : radius a b ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hspos)
  have hs : Real.sin α = b / radius a b := by
    have h0 := hα 0
    simp [q] at h0
    apply (eq_div_iff hr).2
    simpa [mul_comm] using h0.symm
  have hc : Real.cos α = a / radius a b := by
    have hpi := hα (Real.pi / 2)
    rw [Real.sin_add] at hpi
    simp [q] at hpi
    apply (eq_div_iff hr).2
    simpa [mul_comm] using hpi.symm
  exact ⟨α, ⟨hα, hs, hc⟩, (_integration_results U a b n hn hab hU).1⟩
theorem gap6 (U : Set ℝ) (a b : ℝ) (n : ℕ) (hn : 2 ≤ n)
    (hab : a ≠ 0 ∨ b ≠ 0) (hU : Regular U a b) :
    Family U (fun x => 1 / q a b x ^ n) = ImplicitRecurrenceFamily U a b n := by
  exact (_integration_results U a b n hn hab hU).1
theorem gap7 (U : Set ℝ) (a b : ℝ) (n : ℕ) (hn : 2 ≤ n)
    (hab : a ≠ 0 ∨ b ≠ 0) (hU : Regular U a b) :
    Family U (fun x => 1 / q a b x ^ n) = RecurrenceFamily U a b n := by
  exact (_integration_results U a b n hn hab hU).2
theorem gap8 (a b : ℝ) (n : ℕ) :
    ∃ A : ℝ, A = b / (((n : ℝ) - 1) * (a ^ 2 + b ^ 2)) := by
  exact ⟨b / (((n : ℝ) - 1) * (a ^ 2 + b ^ 2)), rfl⟩
theorem gap9 (a b : ℝ) (n : ℕ) :
    ∃ B : ℝ, B = -a / (((n : ℝ) - 1) * (a ^ 2 + b ^ 2)) := by
  exact ⟨-a / (((n : ℝ) - 1) * (a ^ 2 + b ^ 2)), rfl⟩
theorem gap10 (a b : ℝ) (n : ℕ) :
    ∃ C : ℝ, C = ((n : ℝ) - 2) / (((n : ℝ) - 1) * (a ^ 2 + b ^ 2)) := by
  exact ⟨((n : ℝ) - 2) / (((n : ℝ) - 1) * (a ^ 2 + b ^ 2)), rfl⟩
theorem gap11 (U : Set ℝ) (a b : ℝ) (n : ℕ) (hn : 2 ≤ n)
    (hab : a ≠ 0 ∨ b ≠ 0) (hU : Regular U a b) :
    ∃ A B C : ℝ, Family U (fun x => 1 / q a b x ^ n) =
      {F : ℝ → ℝ | ∃ G ∈ Family U (fun x => 1 / q a b x ^ (n - 2)),
        ∃ C₀, ∀ x ∈ U,
          F x = (A * Real.sin x + B * Real.cos x) / q a b x ^ (n - 1) +
            C * G x + C₀} := by
  have hspos : 0 < a ^ 2 + b ^ 2 := by
    rcases hab with ha | hb
    · nlinarith [sq_pos_of_ne_zero ha]
    · nlinarith [sq_pos_of_ne_zero hb]
  have hS : a ^ 2 + b ^ 2 ≠ 0 := ne_of_gt hspos
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast hn
  have hn1 : (n : ℝ) - 1 ≠ 0 := by nlinarith
  refine ⟨b / (((n : ℝ) - 1) * (a ^ 2 + b ^ 2)),
    -a / (((n : ℝ) - 1) * (a ^ 2 + b ^ 2)),
    ((n : ℝ) - 2) / (((n : ℝ) - 1) * (a ^ 2 + b ^ 2)), ?_⟩
  rw [gap7 U a b n hn hab hU]
  unfold RecurrenceFamily
  ext F
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨G, hG, C₀, hF⟩
    exact ⟨G, hG, C₀, fun x hx => by
      have hqx := hU.2.2 x hx
      rw [hF x hx]
      unfold recurrenceTerm
      field_simp [hn1, hS, hqx]
      ring⟩
  · rintro ⟨G, hG, C₀, hF⟩
    exact ⟨G, hG, C₀, fun x hx => by
      have hqx := hU.2.2 x hx
      rw [hF x hx]
      unfold recurrenceTerm
      field_simp [hn1, hS, hqx]
      ring⟩

end
end ProofGap.Exercise2057
