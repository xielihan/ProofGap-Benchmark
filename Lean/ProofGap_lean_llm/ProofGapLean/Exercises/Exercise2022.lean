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

namespace ProofGap.Exercise2022
noncomputable section

def integrand (a x : ℝ) := 1 / (Real.sin x - Real.sin a)
def firstReduced (a x : ℝ) :=
  Real.cos ((x + a) / 2 - (x - a) / 2) / (Real.sin x - Real.sin a)
def secondReduced (a x : ℝ) :=
  Real.cos ((x - a) / 2) / Real.sin ((x - a) / 2) +
    Real.sin ((x + a) / 2) / Real.cos ((x + a) / 2)
def primitive (a x : ℝ) :=
  1 / Real.cos a *
    Real.log |Real.sin ((x - a) / 2) / Real.cos ((x + a) / 2)|
def Family (U : Set ℝ) (f : ℝ → ℝ) :=
  {F : ℝ → ℝ | ∀ x ∈ U, HasDerivAt F (f x) x}
def ScaledFamily (U : Set ℝ) (f : ℝ → ℝ) (c : ℝ) :=
  {F : ℝ → ℝ | ∃ G ∈ Family U f, ∀ x ∈ U, F x = c * G x}
def Translates (U : Set ℝ) (p : ℝ → ℝ) :=
  {F : ℝ → ℝ | ∃ C, ∀ x ∈ U, F x = p x + C}
def Regular (U : Set ℝ) (a : ℝ) : Prop :=
  IsOpen U ∧ IsPreconnected U ∧
    (∀ x ∈ U, Real.sin x ≠ Real.sin a ∧
      Real.sin ((x - a) / 2) ≠ 0 ∧ Real.cos ((x + a) / 2) ≠ 0)

private theorem cosine_half_difference_identity (a x : ℝ) :
    Real.cos ((x - a) / 2) * Real.cos ((x + a) / 2) +
        Real.sin ((x + a) / 2) * Real.sin ((x - a) / 2) =
      Real.cos a := by
  calc
    Real.cos ((x - a) / 2) * Real.cos ((x + a) / 2) +
          Real.sin ((x + a) / 2) * Real.sin ((x - a) / 2) =
        Real.cos (((x + a) / 2) - ((x - a) / 2)) := by
      rw [Real.cos_sub]
      ring
    _ = Real.cos a := by
      congr 1
      ring

theorem gap1 (U : Set ℝ) (a : ℝ) (hU : Regular U a)
    (ha : Real.cos a ≠ 0) :
    Family U (integrand a) =
      ScaledFamily U (firstReduced a) (1 / Real.cos a) := by
  ext F
  constructor
  · intro hF
    refine ⟨fun x => Real.cos a * F x, ?_, ?_⟩
    · intro x hx
      have hder := (hF x hx).const_mul (Real.cos a)
      convert hder using 1
      simp only [firstReduced]
      have harg : (x + a) / 2 - (x - a) / 2 = a := by ring
      rw [harg]
      simp only [integrand]
      field_simp
    · intro x hx
      simp only
      field_simp
  · rintro ⟨G, hG, hFG⟩
    intro x hx
    have hopen : U ∈ nhds x := hU.1.mem_nhds hx
    have heq : F =ᶠ[nhds x] fun y => (1 / Real.cos a) * G y := by
      filter_upwards [hopen] with y hy
      exact hFG y hy
    have hder := ((hG x hx).const_mul (1 / Real.cos a)).congr_of_eventuallyEq heq
    convert hder using 1
    simp only [firstReduced, integrand]
    have harg : (x + a) / 2 - (x - a) / 2 = a := by ring
    rw [harg]
    field_simp
theorem gap2 (U : Set ℝ) (a : ℝ) (hU : Regular U a)
    (ha : Real.cos a ≠ 0) :
    Family U (integrand a) =
      ScaledFamily U (secondReduced a) (1 / (2 * Real.cos a)) := by
  have hred : ∀ x ∈ U, secondReduced a x = (2 * Real.cos a) * integrand a x := by
    intro x hx
    rcases hU.2.2 x hx with ⟨hden, hsin, hcos⟩
    have htrig := cosine_half_difference_identity a x
    simp only [secondReduced, integrand]
    rw [Real.sin_sub_sin]
    field_simp [hsin, hcos] <;> nlinarith [htrig]
  ext F
  constructor
  · intro hF
    refine ⟨fun x => (2 * Real.cos a) * F x, ?_, ?_⟩
    · intro x hx
      convert (hF x hx).const_mul (2 * Real.cos a) using 1
      exact hred x hx
    · intro x hx
      simp only
      field_simp
  · rintro ⟨G, hG, hFG⟩
    intro x hx
    have hopen : U ∈ nhds x := hU.1.mem_nhds hx
    have heq : F =ᶠ[nhds x] fun y => (1 / (2 * Real.cos a)) * G y := by
      filter_upwards [hopen] with y hy
      exact hFG y hy
    have hder := ((hG x hx).const_mul (1 / (2 * Real.cos a))).congr_of_eventuallyEq heq
    convert hder using 1
    rw [hred x hx]
    field_simp
theorem gap3 (U : Set ℝ) (a : ℝ) (hU : Regular U a)
    (ha : Real.cos a ≠ 0) :
    Family U (integrand a) = Translates U (primitive a) := by
  have hp : primitive a ∈ Family U (integrand a) := by
    intro x hx
    rcases hU.2.2 x hx with ⟨hden, hsin, hcos⟩
    have htrig := cosine_half_difference_identity a x
    have hsder : HasDerivAt (fun y => Real.sin ((y - a) / 2))
        (Real.cos ((x - a) / 2) / 2) x := by
      convert (Real.hasDerivAt_sin ((x - a) / 2)).comp x
        (((hasDerivAt_id x).sub_const a).div_const 2) using 1 <;> ring
    have hcder : HasDerivAt (fun y => Real.cos ((y + a) / 2))
        (-Real.sin ((x + a) / 2) / 2) x := by
      convert (Real.hasDerivAt_cos ((x + a) / 2)).comp x
        (((hasDerivAt_id x).add_const a).div_const 2) using 1 <;> ring
    have hqder := hsder.div hcder hcos
    have hqne : Real.sin ((x - a) / 2) / Real.cos ((x + a) / 2) ≠ 0 :=
      div_ne_zero hsin hcos
    have hlogder := (Real.hasDerivAt_log hqne).comp x hqder
    have hprim := hlogder.const_mul (1 / Real.cos a)
    have hprimEq :
        primitive a = fun y =>
          (1 / Real.cos a) *
            Real.log (Real.sin ((y - a) / 2) / Real.cos ((y + a) / 2)) := by
      funext y
      simp only [primitive, Real.log_abs]
    rw [hprimEq]
    convert hprim using 1
    simp only [integrand]
    rw [Real.sin_sub_sin]
    field_simp [ha, hsin, hcos] <;> nlinarith [htrig]
  ext F
  constructor
  · intro hF
    have hdiff : ∀ x ∈ U, HasDerivAt (fun y => F y - primitive a y) 0 x := by
      intro x hx
      convert (hF x hx).sub (hp x hx) using 1
      simp
    have hdiffOn : DifferentiableOn ℝ (fun y => F y - primitive a y) U := by
      intro y hy
      exact (hdiff y hy).differentiableAt.differentiableWithinAt
    have hderivZero : ∀ y ∈ U, deriv (fun z => F z - primitive a z) y = 0 := by
      intro y hy
      exact (hdiff y hy).deriv
    by_cases hUne : U.Nonempty
    · rcases hUne with ⟨x₀, hx₀⟩
      refine ⟨F x₀ - primitive a x₀, ?_⟩
      intro x hx
      have hconst := hU.1.is_const_of_deriv_eq_zero hU.2.1
        hdiffOn hderivZero hx₀ hx
      linarith
    · refine ⟨0, ?_⟩
      intro x hx
      exact (hUne ⟨x, hx⟩).elim
  · rintro ⟨C, hFC⟩
    intro x hx
    have hopen : U ∈ nhds x := hU.1.mem_nhds hx
    have heq : F =ᶠ[nhds x] fun y => primitive a y + C := by
      filter_upwards [hopen] with y hy
      exact hFC y hy
    exact ((hp x hx).add_const C).congr_of_eventuallyEq heq

end
end ProofGap.Exercise2022
