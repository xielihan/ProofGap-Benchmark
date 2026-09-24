import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Topology.Defs.Filter
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise2021
noncomputable section

def integrand (a b x : ℝ) := 1 / (Real.cos (x + a) * Real.cos (x + b))
def firstReduced (a b x : ℝ) :=
  Real.sin ((x + a) - (x + b)) / (Real.cos (x + a) * Real.cos (x + b))
def secondReduced (a b x : ℝ) :=
  Real.sin (x + a) / Real.cos (x + a) - Real.sin (x + b) / Real.cos (x + b)
def primitive (a b x : ℝ) :=
  1 / Real.sin (a - b) * Real.log |Real.cos (x + b) / Real.cos (x + a)|
def Family (U : Set ℝ) (f : ℝ → ℝ) :=
  {F : ℝ → ℝ | ∀ x ∈ U, HasDerivAt F (f x) x}
def ScaledFamily (U : Set ℝ) (f : ℝ → ℝ) (c : ℝ) :=
  {F : ℝ → ℝ | ∃ G ∈ Family U f, ∀ x ∈ U, F x = c * G x}
def Translates (U : Set ℝ) (p : ℝ → ℝ) :=
  {F : ℝ → ℝ | ∃ C, ∀ x ∈ U, F x = p x + C}
def Regular (U : Set ℝ) (a b : ℝ) : Prop :=
  IsOpen U ∧ IsPreconnected U ∧
    (∀ x ∈ U, Real.cos (x + a) ≠ 0 ∧ Real.cos (x + b) ≠ 0)

private theorem primitive_hasDerivAt (a b x : ℝ)
    (ha : Real.cos (x + a) ≠ 0) (hb : Real.cos (x + b) ≠ 0)
    (hab : Real.sin (a - b) ≠ 0) :
    HasDerivAt (primitive a b) (integrand a b x) x := by
  have hcosA :
      HasDerivAt (fun y : ℝ => Real.cos (y + a))
        (-Real.sin (x + a)) x := by
    simpa using
      (Real.hasDerivAt_cos (x + a)).comp x
        ((hasDerivAt_id x).add_const a)
  have hcosB :
      HasDerivAt (fun y : ℝ => Real.cos (y + b))
        (-Real.sin (x + b)) x := by
    simpa using
      (Real.hasDerivAt_cos (x + b)).comp x
        ((hasDerivAt_id x).add_const b)
  have hquot :
      HasDerivAt
        (fun y : ℝ => Real.cos (y + b) / Real.cos (y + a))
        (((-Real.sin (x + b)) * Real.cos (x + a) -
            Real.cos (x + b) * (-Real.sin (x + a))) /
          Real.cos (x + a) ^ 2) x :=
    hcosB.div hcosA ha
  have hqne :
      Real.cos (x + b) / Real.cos (x + a) ≠ 0 :=
    div_ne_zero hb ha
  have htrig :
      Real.sin (a - b) =
        Real.sin (x + a) * Real.cos (x + b) -
          Real.cos (x + a) * Real.sin (x + b) := by
    calc
      Real.sin (a - b) =
          Real.sin ((x + a) - (x + b)) := by
            congr 1
            ring
      _ = Real.sin (x + a) * Real.cos (x + b) -
          Real.cos (x + a) * Real.sin (x + b) :=
        Real.sin_sub (x + a) (x + b)
  convert (hquot.log hqne).const_mul (1 / Real.sin (a - b)) using 1
  · funext y
    simp [primitive, Real.log_abs]
  · unfold integrand
    field_simp [hab, ha, hb]
    <;> rw [htrig]
    <;> ring

theorem gap1 (U : Set ℝ) (a b : ℝ) (hU : Regular U a b)
    (hab : Real.sin (a - b) ≠ 0) :
    Family U (integrand a b) =
      ScaledFamily U (firstReduced a b) (1 / Real.sin (a - b)) := by
  apply Set.ext
  intro F
  constructor
  · intro hF
    change ∀ x ∈ U, HasDerivAt F (integrand a b x) x at hF
    change ∃ G ∈ Family U (firstReduced a b),
      ∀ x ∈ U, F x = (1 / Real.sin (a - b)) * G x
    refine ⟨fun x => Real.sin (a - b) * F x, ?_, ?_⟩
    · change ∀ x ∈ U,
        HasDerivAt (fun y => Real.sin (a - b) * F y)
          (firstReduced a b x) x
      intro x hx
      have hred :
          firstReduced a b x =
            Real.sin (a - b) * integrand a b x := by
        unfold firstReduced integrand
        rw [show (x + a) - (x + b) = a - b by ring]
        ring
      simpa only [hred] using
        (hF x hx).const_mul (Real.sin (a - b))
    · intro x hx
      field_simp [hab]
  · intro hF
    change (∃ G ∈ Family U (firstReduced a b),
      ∀ x ∈ U, F x = (1 / Real.sin (a - b)) * G x) at hF
    rcases hF with ⟨G, hG, hFG⟩
    change ∀ x ∈ U, HasDerivAt F (integrand a b x) x
    intro x hx
    have hred :
        firstReduced a b x =
          Real.sin (a - b) * integrand a b x := by
      unfold firstReduced integrand
      rw [show (x + a) - (x + b) = a - b by ring]
      ring
    have hd :
        HasDerivAt (fun y => (1 / Real.sin (a - b)) * G y)
          (integrand a b x) x := by
      convert (hG x hx).const_mul (1 / Real.sin (a - b)) using 1
      rw [hred]
      field_simp [hab]
    have hev :
        F =ᶠ[nhds x] fun y => (1 / Real.sin (a - b)) * G y :=
      Filter.mem_of_superset (hU.1.mem_nhds hx)
        (fun y hy => hFG y hy)
    exact hd.congr_of_eventuallyEq hev
theorem gap2 (U : Set ℝ) (a b : ℝ) (hU : Regular U a b)
    (hab : Real.sin (a - b) ≠ 0) :
    Family U (integrand a b) =
      ScaledFamily U (secondReduced a b) (1 / Real.sin (a - b)) := by
  rw [gap1 U a b hU hab]
  have hred (x : ℝ) (hx : x ∈ U) :
      firstReduced a b x = secondReduced a b x := by
    have ha := (hU.2.2 x hx).1
    have hb := (hU.2.2 x hx).2
    unfold firstReduced secondReduced
    rw [Real.sin_sub]
    field_simp [ha, hb]
    <;> ring
  apply Set.ext
  intro F
  constructor
  · intro hF
    change (∃ G ∈ Family U (firstReduced a b),
      ∀ x ∈ U, F x = (1 / Real.sin (a - b)) * G x) at hF
    rcases hF with ⟨G, hG, hFG⟩
    change ∃ G ∈ Family U (secondReduced a b),
      ∀ x ∈ U, F x = (1 / Real.sin (a - b)) * G x
    refine ⟨G, ?_, hFG⟩
    change ∀ x ∈ U, HasDerivAt G (secondReduced a b x) x
    intro x hx
    simpa only [hred x hx] using hG x hx
  · intro hF
    change (∃ G ∈ Family U (secondReduced a b),
      ∀ x ∈ U, F x = (1 / Real.sin (a - b)) * G x) at hF
    rcases hF with ⟨G, hG, hFG⟩
    change ∃ G ∈ Family U (firstReduced a b),
      ∀ x ∈ U, F x = (1 / Real.sin (a - b)) * G x
    refine ⟨G, ?_, hFG⟩
    change ∀ x ∈ U, HasDerivAt G (firstReduced a b x) x
    intro x hx
    simpa only [hred x hx] using hG x hx
theorem gap3 (U : Set ℝ) (a b : ℝ) (hU : Regular U a b)
    (hab : Real.sin (a - b) ≠ 0) :
    Family U (integrand a b) = Translates U (primitive a b) := by
  apply Set.ext
  intro F
  constructor
  · intro hF
    change ∀ x ∈ U, HasDerivAt F (integrand a b x) x at hF
    change ∃ C, ∀ x ∈ U, F x = primitive a b x + C
    by_cases hne : U.Nonempty
    · rcases hne with ⟨x₀, hx₀⟩
      have hsub : ∀ y ∈ U,
          HasDerivAt (fun z => F z - primitive a b z) 0 y := by
        intro y hy
        simpa using
          (hF y hy).sub
            (primitive_hasDerivAt a b y (hU.2.2 y hy).1
              (hU.2.2 y hy).2 hab)
      have hdiff :
          DifferentiableOn ℝ (fun z => F z - primitive a b z) U := by
        intro y hy
        exact (hsub y hy).differentiableAt.differentiableWithinAt
      have hzero : ∀ y ∈ U,
          deriv (fun z => F z - primitive a b z) y = 0 := by
        intro y hy
        exact (hsub y hy).deriv
      refine ⟨F x₀ - primitive a b x₀, ?_⟩
      intro x hx
      have heq :
          F x - primitive a b x =
            F x₀ - primitive a b x₀ :=
        hU.1.is_const_of_deriv_eq_zero hU.2.1 hdiff hzero hx hx₀
      linarith
    · refine ⟨0, ?_⟩
      intro x hx
      exact False.elim (hne ⟨x, hx⟩)
  · intro hF
    change (∃ C, ∀ x ∈ U, F x = primitive a b x + C) at hF
    rcases hF with ⟨C, hFC⟩
    change ∀ x ∈ U, HasDerivAt F (integrand a b x) x
    intro x hx
    have hd :
        HasDerivAt (fun y => primitive a b y + C)
          (integrand a b x) x :=
      (primitive_hasDerivAt a b x (hU.2.2 x hx).1
        (hU.2.2 x hx).2 hab).add_const C
    have hev : F =ᶠ[nhds x] fun y => primitive a b y + C :=
      Filter.mem_of_superset (hU.1.mem_nhds hx)
        (fun y hy => hFC y hy)
    exact hd.congr_of_eventuallyEq hev

end
end ProofGap.Exercise2021
