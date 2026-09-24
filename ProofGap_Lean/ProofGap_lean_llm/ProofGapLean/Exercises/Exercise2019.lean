import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise2019
noncomputable section

def integrand (a b x : ℝ) := 1 / (Real.sin (x + a) * Real.sin (x + b))
def firstReduced (a b x : ℝ) :=
  Real.sin ((x + a) - (x + b)) / (Real.sin (x + a) * Real.sin (x + b))
def secondReduced (a b x : ℝ) :=
  Real.cos (x + b) / Real.sin (x + b) - Real.cos (x + a) / Real.sin (x + a)
def primitive (a b x : ℝ) :=
  1 / Real.sin (a - b) * Real.log |Real.sin (x + b) / Real.sin (x + a)|
def Family (U : Set ℝ) (f : ℝ → ℝ) :=
  {F : ℝ → ℝ | ∀ x ∈ U, HasDerivAt F (f x) x}
def ScaledFamily (U : Set ℝ) (f : ℝ → ℝ) (c : ℝ) :=
  {F : ℝ → ℝ | ∃ G ∈ Family U f, ∀ x ∈ U, F x = c * G x}
def Translates (U : Set ℝ) (p : ℝ → ℝ) :=
  {F : ℝ → ℝ | ∃ C, ∀ x ∈ U, F x = p x + C}
def Regular (U : Set ℝ) (a b : ℝ) : Prop :=
  IsOpen U ∧ IsPreconnected U ∧
    (∀ x ∈ U, Real.sin (x + a) ≠ 0 ∧ Real.sin (x + b) ≠ 0)

private theorem hasDerivAt_of_eqOn_open
    {U : Set ℝ} {F G : ℝ → ℝ} {f x : ℝ}
    (hU : IsOpen U) (hx : x ∈ U)
    (hFG : ∀ y ∈ U, F y = G y)
    (hG : HasDerivAt G f x) : HasDerivAt F f x := by
  apply hG.congr_of_eventuallyEq
  filter_upwards [hU.mem_nhds hx] with y hy
  exact hFG y hy

private theorem firstReduced_eq_scaled_integrand (a b x : ℝ) :
    firstReduced a b x = Real.sin (a - b) * integrand a b x := by
  unfold firstReduced integrand
  have hsub : (x + a) - (x + b) = a - b := by ring
  rw [hsub]
  simp [div_eq_mul_inv]

private theorem firstReduced_eq_secondReduced (a b x : ℝ)
    (ha : Real.sin (x + a) ≠ 0) (hb : Real.sin (x + b) ≠ 0) :
    firstReduced a b x = secondReduced a b x := by
  unfold firstReduced secondReduced
  rw [Real.sin_sub]
  field_simp [ha, hb]

private theorem hasDerivAt_primitive (a b x : ℝ)
    (ha : Real.sin (x + a) ≠ 0) (hb : Real.sin (x + b) ≠ 0)
    (hab : Real.sin (a - b) ≠ 0) :
    HasDerivAt (primitive a b) (integrand a b x) x := by
  have hda : HasDerivAt (fun y => Real.sin (y + a)) (Real.cos (x + a)) x := by
    simpa using
      (Real.hasDerivAt_sin (x + a)).comp x ((hasDerivAt_id x).add_const a)
  have hdb : HasDerivAt (fun y => Real.sin (y + b)) (Real.cos (x + b)) x := by
    simpa using
      (Real.hasDerivAt_sin (x + b)).comp x ((hasDerivAt_id x).add_const b)
  have hq : Real.sin (x + b) / Real.sin (x + a) ≠ 0 := div_ne_zero hb ha
  have hdq := hdb.div hda ha
  have hdlog := (Real.hasDerivAt_log hq).comp x hdq
  have hdlogAbs :
      HasDerivAt
        (fun y => Real.log |Real.sin (y + b) / Real.sin (y + a)|)
        ((Real.sin (x + b) / Real.sin (x + a))⁻¹ *
          ((Real.cos (x + b) * Real.sin (x + a) -
              Real.sin (x + b) * Real.cos (x + a)) /
            Real.sin (x + a) ^ 2)) x := by
    simpa only [Real.log_abs, Function.comp_apply] using hdlog
  have hdsecond :
      HasDerivAt
        (fun y => Real.log |Real.sin (y + b) / Real.sin (y + a)|)
        (secondReduced a b x) x := by
    convert hdlogAbs using 1
    unfold secondReduced
    field_simp [ha, hb]
  have hdprim :
      HasDerivAt (primitive a b)
        ((1 / Real.sin (a - b)) * secondReduced a b x) x := by
    simpa only [primitive] using hdsecond.const_mul (1 / Real.sin (a - b))
  have hscale :
      (1 / Real.sin (a - b)) * secondReduced a b x = integrand a b x := by
    rw [← firstReduced_eq_secondReduced a b x ha hb]
    rw [firstReduced_eq_scaled_integrand]
    field_simp [hab]
  rw [hscale] at hdprim
  exact hdprim

theorem gap1 (U : Set ℝ) (a b : ℝ) (hU : Regular U a b)
    (hab : Real.sin (a - b) ≠ 0) :
    Family U (integrand a b) =
      ScaledFamily U (firstReduced a b) (1 / Real.sin (a - b)) := by
  rcases hU with ⟨hUopen, _, _⟩
  ext F
  simp only [Family, ScaledFamily, Set.mem_setOf_eq]
  constructor
  · intro hF
    refine ⟨fun x => Real.sin (a - b) * F x, ?_, ?_⟩
    · intro x hx
      have hd := (hF x hx).const_mul (Real.sin (a - b))
      rw [← firstReduced_eq_scaled_integrand a b x] at hd
      exact hd
    · intro x _
      dsimp
      field_simp [hab]
  · rintro ⟨G, hG, hFG⟩
    intro x hx
    have hd := (hG x hx).const_mul (1 / Real.sin (a - b))
    have hscale :
        (1 / Real.sin (a - b)) * firstReduced a b x =
          integrand a b x := by
      rw [firstReduced_eq_scaled_integrand]
      field_simp [hab]
    rw [hscale] at hd
    exact hasDerivAt_of_eqOn_open hUopen hx hFG hd
theorem gap2 (U : Set ℝ) (a b : ℝ) (hU : Regular U a b)
    (hab : Real.sin (a - b) ≠ 0) :
    Family U (integrand a b) =
      ScaledFamily U (secondReduced a b) (1 / Real.sin (a - b)) := by
  rw [gap1 U a b hU hab]
  have hreg := hU.2.2
  ext F
  simp only [ScaledFamily, Family, Set.mem_setOf_eq]
  constructor
  · rintro ⟨G, hG, hFG⟩
    refine ⟨G, ?_, hFG⟩
    intro x hx
    have heq := firstReduced_eq_secondReduced a b x (hreg x hx).1 (hreg x hx).2
    rw [← heq]
    exact hG x hx
  · rintro ⟨G, hG, hFG⟩
    refine ⟨G, ?_, hFG⟩
    intro x hx
    have heq := firstReduced_eq_secondReduced a b x (hreg x hx).1 (hreg x hx).2
    rw [heq]
    exact hG x hx
theorem gap3 (U : Set ℝ) (a b : ℝ) (hU : Regular U a b)
    (hab : Real.sin (a - b) ≠ 0) :
    Family U (integrand a b) = Translates U (primitive a b) := by
  rcases hU with ⟨hUopen, hUconn, hreg⟩
  ext F
  simp only [Family, Translates, Set.mem_setOf_eq]
  constructor
  · intro hF
    by_cases hne : U.Nonempty
    · rcases hne with ⟨x₀, hx₀⟩
      let H : ℝ → ℝ := fun x => F x - primitive a b x
      have hH : ∀ x ∈ U, HasDerivAt H 0 x := by
        intro x hx
        rcases hreg x hx with ⟨ha, hb⟩
        have hp := hasDerivAt_primitive a b x ha hb hab
        simpa [H] using (hF x hx).sub hp
      have hdiff : DifferentiableOn ℝ H U := by
        intro x hx
        exact (hH x hx).differentiableAt.differentiableWithinAt
      have hderiv : ∀ x ∈ U, deriv H x = 0 := by
        intro x hx
        exact (hH x hx).deriv
      refine ⟨F x₀ - primitive a b x₀, ?_⟩
      intro x hx
      have heq : H x = H x₀ :=
        hUopen.is_const_of_deriv_eq_zero hUconn hdiff hderiv hx hx₀
      dsimp [H] at heq
      linarith
    · refine ⟨0, ?_⟩
      intro x hx
      exact False.elim (hne ⟨x, hx⟩)
  · rintro ⟨C, hFC⟩
    intro x hx
    rcases hreg x hx with ⟨ha, hb⟩
    have hp := hasDerivAt_primitive a b x ha hb hab
    exact hasDerivAt_of_eqOn_open hUopen hx hFC (hp.add_const C)

end
end ProofGap.Exercise2019
