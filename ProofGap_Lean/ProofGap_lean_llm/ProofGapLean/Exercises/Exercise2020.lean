import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise2020
noncomputable section

def integrand (a b x : ℝ) := 1 / (Real.sin (x + a) * Real.cos (x + b))
def firstReduced (a b x : ℝ) :=
  Real.cos ((x + a) - (x + b)) / (Real.sin (x + a) * Real.cos (x + b))
def secondReduced (a b x : ℝ) :=
  Real.cos (x + a) / Real.sin (x + a) + Real.sin (x + b) / Real.cos (x + b)
def primitive (a b x : ℝ) :=
  1 / Real.cos (a - b) * Real.log |Real.sin (x + a) / Real.cos (x + b)|
def Family (U : Set ℝ) (f : ℝ → ℝ) :=
  {F : ℝ → ℝ | ∀ x ∈ U, HasDerivAt F (f x) x}
def ScaledFamily (U : Set ℝ) (f : ℝ → ℝ) (c : ℝ) :=
  {F : ℝ → ℝ | ∃ G ∈ Family U f, ∀ x ∈ U, F x = c * G x}
def Translates (U : Set ℝ) (p : ℝ → ℝ) :=
  {F : ℝ → ℝ | ∃ C, ∀ x ∈ U, F x = p x + C}
def Regular (U : Set ℝ) (a b : ℝ) : Prop :=
  IsOpen U ∧ IsPreconnected U ∧
    (∀ x ∈ U, Real.sin (x + a) ≠ 0 ∧ Real.cos (x + b) ≠ 0)

private theorem firstReduced_eq_scaled_integrand (a b x : ℝ) :
    firstReduced a b x = Real.cos (a - b) * integrand a b x := by
  have harg : (x + a) - (x + b) = a - b := by ring
  rw [firstReduced, integrand, harg]
  ring

private theorem secondReduced_eq_scaled_integrand
    (a b x : ℝ) (hs : Real.sin (x + a) ≠ 0)
    (hc : Real.cos (x + b) ≠ 0) :
    secondReduced a b x = Real.cos (a - b) * integrand a b x := by
  have harg : a - b = (x + a) - (x + b) := by ring
  rw [secondReduced, integrand, harg, Real.cos_sub]
  field_simp [hs, hc]

private theorem family_eq_scaledFamily
    (U : Set ℝ) (f g : ℝ → ℝ) (k : ℝ)
    (hU : IsOpen U) (hk : k ≠ 0)
    (hfg : ∀ x ∈ U, g x = k * f x) :
    Family U f = ScaledFamily U g (1 / k) := by
  apply Set.ext
  intro F
  change
    (∀ x ∈ U, HasDerivAt F (f x) x) ↔
      ∃ G, (∀ x ∈ U, HasDerivAt G (g x) x) ∧
        ∀ x ∈ U, F x = (1 / k) * G x
  constructor
  · intro hF
    refine ⟨fun y : ℝ => k * F y, ?_, ?_⟩
    · intro x hx
      have hd := (hF x hx).const_mul k
      rw [← hfg x hx] at hd
      exact hd
    · intro x hx
      field_simp [hk]
  · rintro ⟨G, hG, hFG⟩ x hx
    have hd := (hG x hx).const_mul (1 / k)
    have hder : (1 / k) * g x = f x := by
      rw [hfg x hx]
      field_simp [hk]
    rw [hder] at hd
    apply hd.congr_of_eventuallyEq
    filter_upwards [hU.mem_nhds hx] with y hy
    exact hFG y hy

private theorem primitive_hasDerivAt
    (a b x : ℝ) (hs : Real.sin (x + a) ≠ 0)
    (hc : Real.cos (x + b) ≠ 0)
    (hab : Real.cos (a - b) ≠ 0) :
    HasDerivAt (primitive a b) (integrand a b x) x := by
  have hsin :
      HasDerivAt (fun y : ℝ => Real.sin (y + a))
        (Real.cos (x + a)) x := by
    simpa using
      (Real.hasDerivAt_sin (x + a)).comp x
        ((hasDerivAt_id x).add_const a)
  have hcos :
      HasDerivAt (fun y : ℝ => Real.cos (y + b))
        (-Real.sin (x + b)) x := by
    simpa using
      (Real.hasDerivAt_cos (x + b)).comp x
        ((hasDerivAt_id x).add_const b)
  have hq :
      HasDerivAt
        (fun y : ℝ => Real.sin (y + a) / Real.cos (y + b))
        ((Real.cos (x + a) * Real.cos (x + b) -
            Real.sin (x + a) * (-Real.sin (x + b))) /
          Real.cos (x + b) ^ 2) x :=
    hsin.div hcos hc
  have hlogq :
      HasDerivAt
        (fun y : ℝ => Real.log
          (Real.sin (y + a) / Real.cos (y + b)))
        ((Real.sin (x + a) / Real.cos (x + b))⁻¹ *
          ((Real.cos (x + a) * Real.cos (x + b) -
              Real.sin (x + a) * (-Real.sin (x + b))) /
            Real.cos (x + b) ^ 2)) x := by
    simpa only [Function.comp_def] using
      (Real.hasDerivAt_log (div_ne_zero hs hc)).comp x hq
  have hder :
      (Real.sin (x + a) / Real.cos (x + b))⁻¹ *
          ((Real.cos (x + a) * Real.cos (x + b) -
              Real.sin (x + a) * (-Real.sin (x + b))) /
            Real.cos (x + b) ^ 2) =
        secondReduced a b x := by
    rw [secondReduced]
    field_simp [hs, hc]
    ring
  rw [hder] at hlogq
  have hlogabs :
      HasDerivAt
        (fun y : ℝ => Real.log
          |Real.sin (y + a) / Real.cos (y + b)|)
        (secondReduced a b x) x := by
    simpa only [Real.log_abs] using hlogq
  have hp :
      HasDerivAt (primitive a b)
        ((1 / Real.cos (a - b)) * secondReduced a b x) x := by
    simpa only [primitive] using
      hlogabs.const_mul (1 / Real.cos (a - b))
  have heq :
      (1 / Real.cos (a - b)) * secondReduced a b x =
        integrand a b x := by
    rw [secondReduced_eq_scaled_integrand a b x hs hc]
    field_simp [hab]
  rw [heq] at hp
  exact hp

theorem gap1 (U : Set ℝ) (a b : ℝ) (hU : Regular U a b)
    (hab : Real.cos (a - b) ≠ 0) :
    Family U (integrand a b) =
      ScaledFamily U (firstReduced a b) (1 / Real.cos (a - b)) := by
  exact family_eq_scaledFamily
    (U := U) (f := integrand a b) (g := firstReduced a b)
    (k := Real.cos (a - b)) hU.1 hab (by
      intro x hx
      exact firstReduced_eq_scaled_integrand a b x)
theorem gap2 (U : Set ℝ) (a b : ℝ) (hU : Regular U a b)
    (hab : Real.cos (a - b) ≠ 0) :
    Family U (integrand a b) =
      ScaledFamily U (secondReduced a b) (1 / Real.cos (a - b)) := by
  exact family_eq_scaledFamily
    (U := U) (f := integrand a b) (g := secondReduced a b)
    (k := Real.cos (a - b)) hU.1 hab (by
      intro x hx
      rcases hU.2.2 x hx with ⟨hs, hc⟩
      exact secondReduced_eq_scaled_integrand a b x hs hc)
theorem gap3 (U : Set ℝ) (a b : ℝ) (hU : Regular U a b)
    (hab : Real.cos (a - b) ≠ 0) :
    Family U (integrand a b) = Translates U (primitive a b) := by
  apply Set.ext
  intro F
  change
    (∀ x ∈ U, HasDerivAt F (integrand a b x) x) ↔
      ∃ C, ∀ x ∈ U, F x = primitive a b x + C
  constructor
  · intro hF
    by_cases hne : U.Nonempty
    · rcases hne with ⟨x₀, hx₀⟩
      refine ⟨F x₀ - primitive a b x₀, ?_⟩
      have hd : ∀ y ∈ U,
          HasDerivAt (fun z : ℝ => F z - primitive a b z) 0 y := by
        intro y hy
        simpa using
          ((hF y hy).sub
            (primitive_hasDerivAt a b y
              (hU.2.2 y hy).1 (hU.2.2 y hy).2 hab))
      have hdiff :
          DifferentiableOn ℝ (fun z : ℝ => F z - primitive a b z) U := by
        intro y hy
        exact (hd y hy).differentiableAt.differentiableWithinAt
      have hderiv : ∀ y ∈ U,
          deriv (fun z : ℝ => F z - primitive a b z) y = 0 := by
        intro y hy
        exact (hd y hy).deriv
      intro x hx
      have hconst :=
        hU.1.is_const_of_deriv_eq_zero hU.2.1 hdiff hderiv hx hx₀
      linarith
    · refine ⟨0, ?_⟩
      intro x hx
      exact False.elim (hne ⟨x, hx⟩)
  · rintro ⟨C, hFC⟩ x hx
    have hp :=
      (primitive_hasDerivAt a b x
        (hU.2.2 x hx).1 (hU.2.2 x hx).2 hab).add_const C
    apply hp.congr_of_eventuallyEq
    filter_upwards [hU.1.mem_nhds hx] with y hy
    exact hFC y hy

end
end ProofGap.Exercise2020
