import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Defs.Filter
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise2060
noncomputable section

def sec (x : ℝ) := 1 / Real.cos x
def integrand (x : ℝ) :=
  Real.sin x / (Real.cos x * Real.sqrt (1 + Real.sin x ^ 2))
def cosineForm (x : ℝ) :=
  -deriv Real.cos x / (Real.cos x * Real.sqrt (2 - Real.cos x ^ 2))
def reciprocalCosineForm (x : ℝ) :=
  deriv Real.cos x /
    (Real.cos x ^ 2 * Real.sqrt (2 * sec x ^ 2 - 1))
def secantForm (x : ℝ) := deriv sec x / Real.sqrt (2 * sec x ^ 2 - 1)
def primitive₁ (x : ℝ) :=
  1 / Real.sqrt 2 *
    Real.log |Real.sqrt 2 * sec x + Real.sqrt (2 * sec x ^ 2 - 1)|
def primitive₂ (x : ℝ) :=
  1 / Real.sqrt 2 *
    Real.log ((Real.sqrt 2 + Real.sqrt (1 + Real.sin x ^ 2)) / |Real.cos x|)
def Family (U : Set ℝ) (f : ℝ → ℝ) :=
  {F : ℝ → ℝ | ∀ x ∈ U, HasDerivAt F (f x) x}
def NegFamily (U : Set ℝ) (f : ℝ → ℝ) :=
  {F : ℝ → ℝ | ∃ G ∈ Family U f, ∀ x ∈ U, F x = -G x}
def Translates (U : Set ℝ) (p : ℝ → ℝ) :=
  {F : ℝ → ℝ | ∃ C, ∀ x ∈ U, F x = p x + C}
def Regular (U : Set ℝ) :=
  IsOpen U ∧ IsPreconnected U ∧ ∀ x ∈ U, 0 < Real.cos x

private theorem local_calculus_facts
    (U : Set ℝ) (hU : Regular U) (x : ℝ) (hx : x ∈ U) :
    integrand x = cosineForm x ∧
      reciprocalCosineForm x = -cosineForm x ∧
      secantForm x = cosineForm x ∧
      HasDerivAt primitive₁ (integrand x) x ∧
      primitive₁ x = primitive₂ x := by
  have hc : 0 < Real.cos x := hU.2.2 x hx
  have hcne : Real.cos x ≠ 0 := ne_of_gt hc
  have htrig := Real.sin_sq_add_cos_sq x
  have hrad : 2 - Real.cos x ^ 2 = 1 + Real.sin x ^ 2 := by
    nlinarith
  have hnum : 0 < 2 - Real.cos x ^ 2 := by
    rw [hrad]
    positivity
  have hqeq :
      2 * sec x ^ 2 - 1 =
        (2 - Real.cos x ^ 2) / Real.cos x ^ 2 := by
    unfold sec
    field_simp [hcne]
    <;> ring
  have hqpos : 0 < 2 * sec x ^ 2 - 1 := by
    rw [hqeq]
    positivity
  have hroot :
      Real.cos x * Real.sqrt (2 * sec x ^ 2 - 1) =
        Real.sqrt (2 - Real.cos x ^ 2) := by
    have hsquare :
        (Real.cos x * Real.sqrt (2 * sec x ^ 2 - 1)) ^ 2 =
          Real.sqrt (2 - Real.cos x ^ 2) ^ 2 := by
      calc
        (Real.cos x * Real.sqrt (2 * sec x ^ 2 - 1)) ^ 2 =
            Real.cos x ^ 2 * Real.sqrt (2 * sec x ^ 2 - 1) ^ 2 := by ring
        _ = Real.cos x ^ 2 * (2 * sec x ^ 2 - 1) := by
          rw [Real.sq_sqrt (le_of_lt hqpos)]
        _ = 2 - Real.cos x ^ 2 := by
          rw [hqeq]
          field_simp [hcne]
        _ = Real.sqrt (2 - Real.cos x ^ 2) ^ 2 := by
          rw [Real.sq_sqrt (le_of_lt hnum)]
    have hleft :
        0 ≤ Real.cos x * Real.sqrt (2 * sec x ^ 2 - 1) :=
      mul_nonneg (le_of_lt hc) (Real.sqrt_nonneg _)
    have hright : 0 ≤ Real.sqrt (2 - Real.cos x ^ 2) := Real.sqrt_nonneg _
    nlinarith
  have hf1 : integrand x = cosineForm x := by
    unfold integrand cosineForm
    rw [Real.deriv_cos, hrad]
    ring
  have hf2 : reciprocalCosineForm x = -cosineForm x := by
    unfold reciprocalCosineForm cosineForm
    rw [← hroot]
    ring
  have hsecEq : sec = (Real.cos)⁻¹ := by
    funext y
    simp [sec, one_div]
  have hdsec :
      deriv sec x = -deriv Real.cos x / Real.cos x ^ 2 := by
    have hi := (Real.hasDerivAt_cos x).inv hcne
    rw [hsecEq]
    simpa [Real.deriv_cos] using hi.deriv
  have hf3 : secantForm x = cosineForm x := by
    calc
      secantForm x = -reciprocalCosineForm x := by
        unfold secantForm reciprocalCosineForm
        rw [hdsec]
        ring
      _ = cosineForm x := by rw [hf2, neg_neg]
  have hsecDiff : DifferentiableAt ℝ sec x := by
    rw [hsecEq]
    exact ((Real.hasDerivAt_cos x).inv hcne).differentiableAt
  have hsecHas : HasDerivAt sec (deriv sec x) x := hsecDiff.hasDerivAt
  let q : ℝ → ℝ := fun y => 2 * sec y ^ 2 - 1
  let a : ℝ → ℝ := fun y => Real.sqrt 2 * sec y + Real.sqrt (q y)
  have hqpos' : 0 < q x := by simpa [q] using hqpos
  have hsqrtTwo : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hsecpos : 0 < sec x := by
    unfold sec
    positivity
  have hq : HasDerivAt q (4 * sec x * deriv sec x) x := by
    dsimp [q]
    convert ((hsecHas.pow 2).const_mul 2).sub_const 1 using 1 <;> ring
  have hr :
      HasDerivAt (fun y => Real.sqrt (q y))
        ((1 / (2 * Real.sqrt (q x))) * (4 * sec x * deriv sec x)) x := by
    convert (Real.hasDerivAt_sqrt (ne_of_gt hqpos')).comp x hq using 1 <;> ring
  have ha :
      HasDerivAt a
        (Real.sqrt 2 * deriv sec x +
          (1 / (2 * Real.sqrt (q x))) * (4 * sec x * deriv sec x)) x := by
    dsimp [a]
    convert (hsecHas.const_mul (Real.sqrt 2)).add hr using 1 <;> ring
  have haPos : 0 < a x := by
    dsimp [a]
    positivity
  have habs :
      HasDerivAt (fun y => |a y|)
        (Real.sqrt 2 * deriv sec x +
          (1 / (2 * Real.sqrt (q x))) * (4 * sec x * deriv sec x)) x := by
    simpa [haPos] using (hasDerivAt_abs (ne_of_gt haPos)).comp x ha
  have habsne : |a x| ≠ 0 := abs_ne_zero.mpr (ne_of_gt haPos)
  have hlog :
      HasDerivAt (fun y => Real.log |a y|)
        ((1 / |a x|) *
          (Real.sqrt 2 * deriv sec x +
            (1 / (2 * Real.sqrt (q x))) * (4 * sec x * deriv sec x))) x := by
    convert (Real.hasDerivAt_log habsne).comp x habs using 1 <;> ring
  have htwo : Real.sqrt 2 * Real.sqrt 2 = 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have haderiv :
      Real.sqrt 2 * deriv sec x +
          (1 / (2 * Real.sqrt (q x))) * (4 * sec x * deriv sec x) =
        (Real.sqrt 2 / Real.sqrt (q x)) * deriv sec x * a x := by
    dsimp [a]
    field_simp [ne_of_gt (Real.sqrt_pos.2 hqpos')]
    calc
      deriv sec x *
          (Real.sqrt 2 * 2 * Real.sqrt (q x) + 4 * sec x) =
          2 * Real.sqrt 2 * deriv sec x * Real.sqrt (q x) +
            4 * deriv sec x * sec x := by ring
      _ = 2 * Real.sqrt 2 * deriv sec x * Real.sqrt (q x) +
            2 * (Real.sqrt 2 * Real.sqrt 2) * deriv sec x * sec x := by
          rw [htwo]
          ring
      _ = Real.sqrt 2 * deriv sec x * 2 *
            (Real.sqrt 2 * sec x + Real.sqrt (q x)) := by ring
  have hcoef :
      1 / Real.sqrt 2 *
          ((1 / |a x|) *
            (Real.sqrt 2 * deriv sec x +
              (1 / (2 * Real.sqrt (q x))) * (4 * sec x * deriv sec x))) =
        deriv sec x / Real.sqrt (q x) := by
    rw [haderiv, abs_of_pos haPos]
    field_simp [ne_of_gt hsqrtTwo, ne_of_gt (Real.sqrt_pos.2 hqpos'),
      ne_of_gt haPos]
    <;> ring
  have hpraw :
      HasDerivAt primitive₁
        (1 / Real.sqrt 2 *
          ((1 / |a x|) *
            (Real.sqrt 2 * deriv sec x +
              (1 / (2 * Real.sqrt (q x))) * (4 * sec x * deriv sec x)))) x := by
    change HasDerivAt
      (fun y => 1 / Real.sqrt 2 * Real.log |a y|)
      (1 / Real.sqrt 2 *
        ((1 / |a x|) *
          (Real.sqrt 2 * deriv sec x +
            (1 / (2 * Real.sqrt (q x))) * (4 * sec x * deriv sec x)))) x
    exact hlog.const_mul (1 / Real.sqrt 2)
  have hp : HasDerivAt primitive₁ (secantForm x) x := by
    rw [secantForm]
    change HasDerivAt primitive₁ (deriv sec x / Real.sqrt (q x)) x
    rw [← hcoef]
    exact hpraw
  have hpInt : HasDerivAt primitive₁ (integrand x) x := by
    simpa only [hf1, hf3] using hp
  have harg :
      Real.sqrt 2 * sec x + Real.sqrt (2 * sec x ^ 2 - 1) =
        (Real.sqrt 2 + Real.sqrt (1 + Real.sin x ^ 2)) / |Real.cos x| := by
    rw [abs_of_pos hc, ← hrad, ← hroot]
    unfold sec
    field_simp [hcne]
    <;> ring
  have hargPos :
      0 < (Real.sqrt 2 + Real.sqrt (1 + Real.sin x ^ 2)) / |Real.cos x| := by
    rw [← harg]
    simpa [a, q] using haPos
  have hpEq : primitive₁ x = primitive₂ x := by
    unfold primitive₁ primitive₂
    rw [harg, abs_of_pos hargPos]
  exact ⟨hf1, hf2, hf3, hpInt, hpEq⟩

theorem gap1 (U : Set ℝ) (hU : Regular U) :
    Family U integrand = Family U cosineForm := by
  ext F
  simp only [Family, Set.mem_setOf_eq]
  constructor
  · intro hF x hx
    have hf := (local_calculus_facts U hU x hx).1
    simpa only [hf] using hF x hx
  · intro hF x hx
    have hf := (local_calculus_facts U hU x hx).1
    simpa only [hf] using hF x hx
theorem gap2 (U : Set ℝ) (hU : Regular U) :
    Family U cosineForm = NegFamily U reciprocalCosineForm := by
  ext F
  simp only [Family, NegFamily, Set.mem_setOf_eq]
  constructor
  · intro hF
    refine ⟨fun y => -F y, ?_, ?_⟩
    · intro x hx
      have hf := (local_calculus_facts U hU x hx).2.1
      simpa only [hf, neg_neg] using (hF x hx).neg
    · intro x hx
      simp
  · rintro ⟨G, hG, hFG⟩ x hx
    have hf := (local_calculus_facts U hU x hx).2.1
    have hd : HasDerivAt (fun y => -G y) (cosineForm x) x := by
      simpa only [hf, neg_neg] using (hG x hx).neg
    have heq : F =ᶠ[nhds x] (fun y => -G y) :=
      Filter.mem_of_superset (hU.1.mem_nhds hx) (fun y hy => hFG y hy)
    exact hd.congr_of_eventuallyEq heq
theorem gap3 (U : Set ℝ) (hU : Regular U) :
    NegFamily U reciprocalCosineForm = Family U secantForm := by
  calc
    NegFamily U reciprocalCosineForm = Family U cosineForm := (gap2 U hU).symm
    _ = Family U secantForm := by
      ext F
      simp only [Family, Set.mem_setOf_eq]
      constructor
      · intro hF x hx
        have hf := (local_calculus_facts U hU x hx).2.2.1
        simpa only [hf] using hF x hx
      · intro hF x hx
        have hf := (local_calculus_facts U hU x hx).2.2.1
        simpa only [hf] using hF x hx
theorem gap4 (U : Set ℝ) (hU : Regular U) :
    Family U integrand = Family U secantForm := by
  exact (gap1 U hU).trans ((gap2 U hU).trans (gap3 U hU))
theorem gap5 (U : Set ℝ) (hU : Regular U) :
    Family U integrand = Translates U primitive₁ := by
  ext F
  simp only [Family, Translates, Set.mem_setOf_eq]
  constructor
  · intro hF
    by_cases hEmpty : U = ∅
    · subst U
      exact ⟨0, by simp⟩
    · obtain ⟨x₀, hx₀⟩ := Set.nonempty_iff_ne_empty.mpr hEmpty
      refine ⟨F x₀ - primitive₁ x₀, ?_⟩
      intro x hx
      have hdiff : DifferentiableOn ℝ (fun y => F y - primitive₁ y) U := by
        intro y hy
        have hp := (local_calculus_facts U hU y hy).2.2.2.1
        exact ((hF y hy).sub hp).differentiableAt.differentiableWithinAt
      have hzero : ∀ y ∈ U, deriv (fun z => F z - primitive₁ z) y = 0 := by
        intro y hy
        have hp := (local_calculus_facts U hU y hy).2.2.2.1
        simpa using ((hF y hy).sub hp).deriv
      have hc := hU.1.is_const_of_deriv_eq_zero hU.2.1 hdiff hzero hx hx₀
      change F x - primitive₁ x = F x₀ - primitive₁ x₀ at hc
      linarith
  · rintro ⟨C, hFC⟩ x hx
    have hp := (local_calculus_facts U hU x hx).2.2.2.1
    have heq : F =ᶠ[nhds x] (fun y => primitive₁ y + C) :=
      Filter.mem_of_superset (hU.1.mem_nhds hx) (fun y hy => hFC y hy)
    exact (hp.add_const C).congr_of_eventuallyEq heq
theorem gap6 (U : Set ℝ) (hU : Regular U) :
    Translates U primitive₁ = Translates U primitive₂ := by
  ext F
  simp only [Translates, Set.mem_setOf_eq]
  constructor
  · rintro ⟨C, hF⟩
    refine ⟨C, ?_⟩
    intro x hx
    have hp := (local_calculus_facts U hU x hx).2.2.2.2
    rw [hF x hx, hp]
  · rintro ⟨C, hF⟩
    refine ⟨C, ?_⟩
    intro x hx
    have hp := (local_calculus_facts U hU x hx).2.2.2.2
    rw [hF x hx, hp]
theorem gap7 (U : Set ℝ) (hU : Regular U) :
    Family U integrand = Translates U primitive₂ := by
  exact (gap5 U hU).trans (gap6 U hU)

end
end ProofGap.Exercise2060
