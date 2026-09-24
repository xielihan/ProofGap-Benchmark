import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise2032
noncomputable section

def integrand (x : ℝ) := Real.sin x * Real.cos x / (Real.sin x + Real.cos x)
def reduced (x : ℝ) :=
  (Real.sin (x + Real.pi / 4) ^ 2 - 1 / 2) /
    (Real.sqrt 2 * Real.sin (x + Real.pi / 4))
def firstPart (x : ℝ) := Real.sin (x + Real.pi / 4)
def secondPart (x : ℝ) := 1 / Real.sin (x + Real.pi / 4)
def primitive₁ (x : ℝ) :=
  -(1 / Real.sqrt 2) * Real.cos (x + Real.pi / 4) -
    1 / (2 * Real.sqrt 2) *
      Real.log |Real.tan (x / 2 + Real.pi / 8)|
def primitive₂ (x : ℝ) :=
  (1 / 2 : ℝ) * (Real.sin x - Real.cos x) -
    1 / (2 * Real.sqrt 2) *
      Real.log |Real.tan (x / 2 + Real.pi / 8)|
def Family (U : Set ℝ) (f : ℝ → ℝ) :=
  {F : ℝ → ℝ | ∀ x ∈ U, HasDerivAt F (f x) x}
def PairFamily (U : Set ℝ) :=
  {F : ℝ → ℝ | ∃ P ∈ Family U firstPart, ∃ Q ∈ Family U secondPart,
    ∀ x ∈ U, F x = 1 / Real.sqrt 2 * P x -
      1 / (2 * Real.sqrt 2) * Q x}
def Translates (U : Set ℝ) (p : ℝ → ℝ) :=
  {F : ℝ → ℝ | ∃ C, ∀ x ∈ U, F x = p x + C}
def Regular (U : Set ℝ) : Prop :=
  IsOpen U ∧ IsPreconnected U ∧
    (∀ x ∈ U, Real.sin x + Real.cos x ≠ 0 ∧
      Real.tan (x / 2 + Real.pi / 8) ≠ 0)

private lemma sqrt_two_ne_zero : Real.sqrt 2 ≠ 0 := by
  exact ne_of_gt (Real.sqrt_pos.2 (by norm_num))

private lemma sqrt_two_mul_shifted_sin (x : ℝ) :
    Real.sqrt 2 * Real.sin (x + Real.pi / 4) = Real.sin x + Real.cos x := by
  rw [Real.sin_add, Real.sin_pi_div_four, Real.cos_pi_div_four]
  have hs : Real.sqrt 2 * Real.sqrt 2 = 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  calc
    Real.sqrt 2 *
          (Real.sin x * (Real.sqrt 2 / 2) +
            Real.cos x * (Real.sqrt 2 / 2)) =
        (Real.sqrt 2 * Real.sqrt 2 / 2) * (Real.sin x + Real.cos x) := by ring
    _ = Real.sin x + Real.cos x := by rw [hs]; ring

private lemma shifted_sin_sq_sub_half (x : ℝ) :
    Real.sin (x + Real.pi / 4) ^ 2 - 1 / 2 = Real.sin x * Real.cos x := by
  rw [Real.sin_add, Real.sin_pi_div_four, Real.cos_pi_div_four]
  have hs : Real.sqrt 2 * Real.sqrt 2 = 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  calc
    (Real.sin x * (Real.sqrt 2 / 2) +
          Real.cos x * (Real.sqrt 2 / 2)) ^ 2 - 1 / 2 =
        (Real.sqrt 2 * Real.sqrt 2 / 4) *
            (Real.sin x + Real.cos x) ^ 2 - 1 / 2 := by ring
    _ = Real.sin x * Real.cos x := by
      rw [hs]
      nlinarith [Real.sin_sq_add_cos_sq x]

private lemma integrand_eq_reduced (x : ℝ) : integrand x = reduced x := by
  unfold integrand reduced
  rw [shifted_sin_sq_sub_half, sqrt_two_mul_shifted_sin]

private lemma reduced_eq_linear (x : ℝ)
    (hsum : Real.sin x + Real.cos x ≠ 0) :
    reduced x =
      1 / Real.sqrt 2 * firstPart x -
        1 / (2 * Real.sqrt 2) * secondPart x := by
  have hs : Real.sin (x + Real.pi / 4) ≠ 0 := by
    intro hz
    apply hsum
    rw [← sqrt_two_mul_shifted_sin x, hz, mul_zero]
  unfold reduced firstPart secondPart
  field_simp [sqrt_two_ne_zero, hs]
  <;> ring

private lemma hasDerivAt_log_tan (x : ℝ)
    (hsum : Real.sin x + Real.cos x ≠ 0)
    (htan : Real.tan (x / 2 + Real.pi / 8) ≠ 0) :
    HasDerivAt
      (fun y : ℝ => Real.log |Real.tan (y / 2 + Real.pi / 8)|)
      (1 / Real.sin (x + Real.pi / 4)) x := by
  let u : ℝ := x / 2 + Real.pi / 8
  have hshift : Real.sin (x + Real.pi / 4) ≠ 0 := by
    intro hz
    apply hsum
    rw [← sqrt_two_mul_shifted_sin x, hz, mul_zero]
  have harg : x + Real.pi / 4 = u + u := by
    dsimp [u]
    ring
  have hcos : Real.cos u ≠ 0 := by
    intro hz
    apply hshift
    rw [harg, Real.sin_add, hz]
    ring
  have hsin : Real.sin u ≠ 0 := by
    intro hz
    apply htan
    rw [show x / 2 + Real.pi / 8 = u by rfl, Real.tan_eq_sin_div_cos, hz]
    simp
  have hu : HasDerivAt (fun y : ℝ => y / 2 + Real.pi / 8) (1 / 2) x := by
    convert ((hasDerivAt_id x).div_const 2).add_const (Real.pi / 8) using 1 <;> ring
  have ht : HasDerivAt
      (fun y : ℝ => Real.tan (y / 2 + Real.pi / 8))
      ((1 / Real.cos u ^ 2) * (1 / 2)) x := by
    simpa [u] using (Real.hasDerivAt_tan hcos).comp x hu
  have hdouble : Real.sin (u + u) = 2 * Real.sin u * Real.cos u := by
    rw [Real.sin_add]
    ring
  have hc_u :
      1 / Real.tan u * ((1 / Real.cos u ^ 2) * (1 / 2)) =
        1 / Real.sin (u + u) := by
    rw [Real.tan_eq_sin_div_cos, hdouble]
    field_simp [hsin, hcos]
    <;> ring
  have hc :
      1 / Real.tan u * ((1 / Real.cos u ^ 2) * (1 / 2)) =
        1 / Real.sin (x + Real.pi / 4) := by
    calc
      1 / Real.tan u * ((1 / Real.cos u ^ 2) * (1 / 2)) =
          1 / Real.sin (u + u) := hc_u
      _ = 1 / Real.sin (x + Real.pi / 4) := by rw [harg]
  have hc' :
      (Real.tan u)⁻¹ * ((1 / Real.cos u ^ 2) * (1 / 2)) =
        1 / Real.sin (x + Real.pi / 4) := by
    simpa only [one_div] using hc
  have hplain : HasDerivAt
      (fun y : ℝ => Real.log (Real.tan (y / 2 + Real.pi / 8)))
      (1 / Real.sin (x + Real.pi / 4)) x := by
    simpa only [Function.comp_apply,
      show x / 2 + Real.pi / 8 = u by rfl, hc'] using
      (Real.hasDerivAt_log htan).comp x ht
  simpa only [Real.log_abs] using hplain

private lemma hasDerivAt_primitive₁ (U : Set ℝ) (hU : Regular U)
    (x : ℝ) (hx : x ∈ U) : HasDerivAt primitive₁ (integrand x) x := by
  have hsum := (hU.2.2 x hx).1
  have htan := (hU.2.2 x hx).2
  have hshift : HasDerivAt (fun y : ℝ => y + Real.pi / 4) 1 x := by
    simpa using (hasDerivAt_id x).add_const (Real.pi / 4)
  have hc := (Real.hasDerivAt_cos (x + Real.pi / 4)).comp x hshift
  have ha : HasDerivAt
      (fun y : ℝ => -(1 / Real.sqrt 2) * Real.cos (y + Real.pi / 4))
      (1 / Real.sqrt 2 * Real.sin (x + Real.pi / 4)) x := by
    convert hc.const_mul (-(1 / Real.sqrt 2)) using 1 <;> ring
  have hl := hasDerivAt_log_tan x hsum htan
  have hb := hl.const_mul (1 / (2 * Real.sqrt 2))
  have hv := reduced_eq_linear x hsum
  have hi := integrand_eq_reduced x
  simpa only [primitive₁, firstPart, secondPart, hi, hv] using ha.sub hb

private theorem family_eq_translates_primitive₁ (U : Set ℝ) (hU : Regular U) :
    Family U integrand = Translates U primitive₁ := by
  ext F
  constructor
  · intro hF
    change ∀ x ∈ U, HasDerivAt F (integrand x) x at hF
    change ∃ C, ∀ x ∈ U, F x = primitive₁ x + C
    by_cases hne : U.Nonempty
    · rcases hne with ⟨x₀, hx₀⟩
      have hdiff : DifferentiableOn ℝ (fun y => F y - primitive₁ y) U := by
        intro y hy
        exact ((hF y hy).sub (hasDerivAt_primitive₁ U hU y hy)).differentiableAt.differentiableWithinAt
      have hzero : ∀ y ∈ U, deriv (fun z => F z - primitive₁ z) y = 0 := by
        intro y hy
        simpa using ((hF y hy).sub (hasDerivAt_primitive₁ U hU y hy)).deriv
      refine ⟨F x₀ - primitive₁ x₀, ?_⟩
      intro x hx
      have heq : F x - primitive₁ x = F x₀ - primitive₁ x₀ :=
        hU.1.is_const_of_deriv_eq_zero hU.2.1 hdiff hzero hx hx₀
      linarith
    · refine ⟨0, ?_⟩
      intro x hx
      exact False.elim (hne ⟨x, hx⟩)
  · rintro ⟨C, hC⟩
    change ∀ x ∈ U, HasDerivAt F (integrand x) x
    intro x hx
    have hp := (hasDerivAt_primitive₁ U hU x hx).add_const C
    apply hp.congr_of_eventuallyEq
    filter_upwards [hU.1.mem_nhds hx] with y hy
    exact hC y hy

private theorem family_eq_pairFamily (U : Set ℝ) (hU : Regular U) :
    Family U integrand = PairFamily U := by
  ext F
  constructor
  · intro hF
    have ht : F ∈ Translates U primitive₁ := by
      rw [← family_eq_translates_primitive₁ U hU]
      exact hF
    rcases ht with ⟨C, hC⟩
    refine ⟨fun y => -Real.cos (y + Real.pi / 4) + Real.sqrt 2 * C, ?_,
      fun y => Real.log |Real.tan (y / 2 + Real.pi / 8)|, ?_, ?_⟩
    · intro x hx
      have hshift : HasDerivAt (fun y : ℝ => y + Real.pi / 4) 1 x := by
        simpa using (hasDerivAt_id x).add_const (Real.pi / 4)
      have hc := (Real.hasDerivAt_cos (x + Real.pi / 4)).comp x hshift
      simpa [firstPart] using hc.neg.const_add (Real.sqrt 2 * C)
    · intro x hx
      simpa [secondPart] using
        hasDerivAt_log_tan x (hU.2.2 x hx).1 (hU.2.2 x hx).2
    · intro x hx
      rw [hC x hx]
      unfold primitive₁
      field_simp [sqrt_two_ne_zero]
      <;> ring
  · rintro ⟨P, hP, Q, hQ, hF⟩
    intro x hx
    have hc := (hP x hx).const_mul (1 / Real.sqrt 2)
    have hd := (hQ x hx).const_mul (1 / (2 * Real.sqrt 2))
    have hv := reduced_eq_linear x (hU.2.2 x hx).1
    have hi := integrand_eq_reduced x
    have hcombo : HasDerivAt
        (fun y => 1 / Real.sqrt 2 * P y - 1 / (2 * Real.sqrt 2) * Q y)
        (integrand x) x := by
      simpa only [firstPart, secondPart, hi, hv] using hc.sub hd
    apply hcombo.congr_of_eventuallyEq
    filter_upwards [hU.1.mem_nhds hx] with y hy
    exact hF y hy

private theorem primitive₁_eq_primitive₂ : primitive₁ = primitive₂ := by
  funext x
  have hfirst :
      -(1 / Real.sqrt 2) * Real.cos (x + Real.pi / 4) =
        (1 / 2 : ℝ) * (Real.sin x - Real.cos x) := by
    rw [Real.cos_add, Real.cos_pi_div_four, Real.sin_pi_div_four]
    field_simp [sqrt_two_ne_zero]
    <;> ring
  unfold primitive₁ primitive₂
  rw [hfirst]

theorem gap1 (U : Set ℝ) (hU : Regular U) :
    Family U integrand = Family U reduced := by
  ext F
  constructor <;> intro hF <;> intro x hx
  · simpa only [integrand_eq_reduced x] using hF x hx
  · simpa only [integrand_eq_reduced x] using hF x hx
theorem gap2 (U : Set ℝ) (hU : Regular U) :
    Family U integrand = PairFamily U := by
  exact family_eq_pairFamily U hU
theorem gap3 (U : Set ℝ) (hU : Regular U) :
    Family U integrand = Translates U primitive₁ := by
  exact family_eq_translates_primitive₁ U hU
theorem gap4 (U : Set ℝ) (hU : Regular U) :
    Family U integrand = Translates U primitive₂ := by
  rw [← primitive₁_eq_primitive₂]
  exact family_eq_translates_primitive₁ U hU

end
end ProofGap.Exercise2032
