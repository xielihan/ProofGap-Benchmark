import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise2035
noncomputable section

def branch : Set ℝ := Set.Ioo (-(Real.pi / 4)) (Real.pi / 4)
def integrand (x : ℝ) := 1 / (Real.sin x ^ 4 + Real.cos x ^ 4)
def firstReduced (x : ℝ) := 2 / (2 - Real.sin (2 * x) ^ 2)
def firstTan (x : ℝ) :=
  1 / (2 / Real.cos (2 * x) ^ 2 - Real.tan (2 * x) ^ 2) *
    deriv (fun y : ℝ => Real.tan (2 * y)) x
def secondTan (x : ℝ) :=
  1 / (2 + Real.tan (2 * x) ^ 2) *
    deriv (fun y : ℝ => Real.tan (2 * y)) x
def primitive (x : ℝ) :=
  1 / Real.sqrt 2 * Real.arctan (Real.tan (2 * x) / Real.sqrt 2)
def Family (f : ℝ → ℝ) :=
  {F : ℝ → ℝ | ∀ x ∈ branch, HasDerivAt F (f x) x}
def Translates (p : ℝ → ℝ) :=
  {F : ℝ → ℝ | ∃ C, ∀ x ∈ branch, F x = p x + C}

theorem gap1 (x : ℝ) : integrand x = firstReduced x := by
  unfold integrand firstReduced
  have hsc : Real.sin x ^ 2 + Real.cos x ^ 2 = 1 :=
    Real.sin_sq_add_cos_sq x
  have hden :
      2 - Real.sin (2 * x) ^ 2 =
        2 * (Real.sin x ^ 4 + Real.cos x ^ 4) := by
    calc
      2 - Real.sin (2 * x) ^ 2 =
          2 * (Real.sin x ^ 2 + Real.cos x ^ 2) ^ 2 -
            (2 * Real.sin x * Real.cos x) ^ 2 := by
              rw [hsc, Real.sin_two_mul]
              ring
      _ = 2 * (Real.sin x ^ 4 + Real.cos x ^ 4) := by ring
  have hredpos : 0 < 2 - Real.sin (2 * x) ^ 2 := by
    have hsc2 := Real.sin_sq_add_cos_sq (2 * x)
    nlinarith [sq_nonneg (Real.cos (2 * x))]
  have hne : Real.sin x ^ 4 + Real.cos x ^ 4 ≠ 0 := by
    intro hzero
    rw [hzero] at hden
    nlinarith
  rw [hden]
  field_simp [hne] <;> ring
theorem gap2 (x : ℝ) (hx : x ∈ branch) : integrand x = firstTan x := by
  change -(Real.pi / 4) < x ∧ x < Real.pi / 4 at hx
  have h2x : 2 * x ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> nlinarith [Real.pi_pos]
  have hcospos : 0 < Real.cos (2 * x) :=
    Real.cos_pos_of_mem_Ioo h2x
  have hcos : Real.cos (2 * x) ≠ 0 := ne_of_gt hcospos
  have hlin : HasDerivAt (fun y : ℝ => 2 * y) 2 x := by
    simpa using
      (hasDerivAt_const x (2 : ℝ)).mul (hasDerivAt_id x)
  have htan :
      HasDerivAt (fun y : ℝ => Real.tan (2 * y))
        (2 / Real.cos (2 * x) ^ 2) x := by
    convert (Real.hasDerivAt_tan hcos).comp x hlin using 1 <;> ring
  have hsc :
      Real.sin (2 * x) ^ 2 + Real.cos (2 * x) ^ 2 = 1 :=
    Real.sin_sq_add_cos_sq (2 * x)
  have hA : 2 - Real.sin (2 * x) ^ 2 ≠ 0 := by
    have : 0 < 2 - Real.sin (2 * x) ^ 2 := by
      nlinarith [sq_nonneg (Real.cos (2 * x))]
    exact ne_of_gt this
  have hinnerEq :
      2 / Real.cos (2 * x) ^ 2 -
          (Real.sin (2 * x) / Real.cos (2 * x)) ^ 2 =
        (2 - Real.sin (2 * x) ^ 2) / Real.cos (2 * x) ^ 2 := by
    field_simp [hcos] <;> ring
  have hinner :
      2 / Real.cos (2 * x) ^ 2 -
          (Real.sin (2 * x) / Real.cos (2 * x)) ^ 2 ≠ 0 := by
    rw [hinnerEq]
    exact div_ne_zero hA (pow_ne_zero 2 hcos)
  rw [gap1 x]
  unfold firstReduced firstTan
  rw [htan.deriv, Real.tan_eq_sin_div_cos]
  field_simp [hcos, hA, hinner] <;> nlinarith [hsc]
theorem gap3 (x : ℝ) (hx : x ∈ branch) : integrand x = secondTan x := by
  change -(Real.pi / 4) < x ∧ x < Real.pi / 4 at hx
  have h2x : 2 * x ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> nlinarith [Real.pi_pos]
  have hcospos : 0 < Real.cos (2 * x) :=
    Real.cos_pos_of_mem_Ioo h2x
  have hcos : Real.cos (2 * x) ≠ 0 := ne_of_gt hcospos
  have hlin : HasDerivAt (fun y : ℝ => 2 * y) 2 x := by
    simpa using
      (hasDerivAt_const x (2 : ℝ)).mul (hasDerivAt_id x)
  have htan :
      HasDerivAt (fun y : ℝ => Real.tan (2 * y))
        (2 / Real.cos (2 * x) ^ 2) x := by
    convert (Real.hasDerivAt_tan hcos).comp x hlin using 1 <;> ring
  have hsc :
      Real.sin (2 * x) ^ 2 + Real.cos (2 * x) ^ 2 = 1 :=
    Real.sin_sq_add_cos_sq (2 * x)
  have hA : 2 - Real.sin (2 * x) ^ 2 ≠ 0 := by
    have : 0 < 2 - Real.sin (2 * x) ^ 2 := by
      nlinarith [sq_nonneg (Real.cos (2 * x))]
    exact ne_of_gt this
  have hB :
      2 + (Real.sin (2 * x) / Real.cos (2 * x)) ^ 2 ≠ 0 := by
    have : 0 < 2 + (Real.sin (2 * x) / Real.cos (2 * x)) ^ 2 := by
      nlinarith [sq_nonneg (Real.sin (2 * x) / Real.cos (2 * x))]
    exact ne_of_gt this
  rw [gap1 x]
  unfold firstReduced secondTan
  rw [htan.deriv, Real.tan_eq_sin_div_cos]
  field_simp [hcos, hA, hB] <;> nlinarith [hsc]
theorem gap4 : Family integrand = Translates primitive := by
  have hprim : ∀ x ∈ branch, HasDerivAt primitive (integrand x) x := by
    intro x hx
    have hx' : -(Real.pi / 4) < x ∧ x < Real.pi / 4 := hx
    have h2x : 2 * x ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
      constructor <;> nlinarith [Real.pi_pos]
    have hcospos : 0 < Real.cos (2 * x) :=
      Real.cos_pos_of_mem_Ioo h2x
    have hcos : Real.cos (2 * x) ≠ 0 := ne_of_gt hcospos
    have hlin : HasDerivAt (fun y : ℝ => 2 * y) 2 x := by
      simpa using
        (hasDerivAt_const x (2 : ℝ)).mul (hasDerivAt_id x)
    have htan :
        HasDerivAt (fun y : ℝ => Real.tan (2 * y))
          (2 / Real.cos (2 * x) ^ 2) x := by
      convert (Real.hasDerivAt_tan hcos).comp x hlin using 1 <;> ring
    have hsqrtpos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
    have hsqrt : Real.sqrt 2 ≠ 0 := ne_of_gt hsqrtpos
    have hsqrtSq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    have hplus : 2 + Real.tan (2 * x) ^ 2 ≠ 0 := by
      have : 0 < 2 + Real.tan (2 * x) ^ 2 := by
        nlinarith [sq_nonneg (Real.tan (2 * x))]
      exact ne_of_gt this
    have hatanPlus :
        1 + (Real.tan (2 * x) / Real.sqrt 2) ^ 2 ≠ 0 := by
      have : 0 < 1 + (Real.tan (2 * x) / Real.sqrt 2) ^ 2 := by
        nlinarith [sq_nonneg (Real.tan (2 * x) / Real.sqrt 2)]
      exact ne_of_gt this
    have hraw :
        HasDerivAt
          (fun y : ℝ =>
            1 / Real.sqrt 2 *
              Real.arctan (Real.tan (2 * y) / Real.sqrt 2))
          ((1 / Real.sqrt 2) *
            ((1 / (1 + (Real.tan (2 * x) / Real.sqrt 2) ^ 2)) *
              ((2 / Real.cos (2 * x) ^ 2) / Real.sqrt 2))) x := by
      simpa only [one_div] using
        ((Real.hasDerivAt_arctan
            (Real.tan (2 * x) / Real.sqrt 2)).comp x
          (htan.div_const (Real.sqrt 2))).const_mul (1 / Real.sqrt 2)
    have hcoef :
        (1 / Real.sqrt 2) *
            ((1 / (1 + (Real.tan (2 * x) / Real.sqrt 2) ^ 2)) *
              ((2 / Real.cos (2 * x) ^ 2) / Real.sqrt 2)) =
          integrand x := by
      rw [gap3 x hx]
      unfold secondTan
      rw [htan.deriv]
      field_simp [hsqrt, hcos, hplus, hatanPlus]
      nlinarith [hsqrtSq]
    rw [← hcoef]
    change HasDerivAt
      (fun y : ℝ =>
        1 / Real.sqrt 2 *
          Real.arctan (Real.tan (2 * y) / Real.sqrt 2))
      ((1 / Real.sqrt 2) *
        ((1 / (1 + (Real.tan (2 * x) / Real.sqrt 2) ^ 2)) *
          ((2 / Real.cos (2 * x) ^ 2) / Real.sqrt 2))) x
    exact hraw
  apply Set.ext
  intro F
  constructor
  · intro hF
    change ∀ x ∈ branch, HasDerivAt F (integrand x) x at hF
    change ∃ C, ∀ x ∈ branch, F x = primitive x + C
    have hzero :
        ∀ x ∈ branch,
          HasDerivAt (fun y : ℝ => F y - primitive y) 0 x := by
      intro x hx
      simpa using (hF x hx).sub (hprim x hx)
    have hdiff :
        DifferentiableOn ℝ (fun y : ℝ => F y - primitive y) branch := by
      intro x hx
      exact (hzero x hx).differentiableAt.differentiableWithinAt
    have h0 : (0 : ℝ) ∈ branch := by
      change -(Real.pi / 4) < (0 : ℝ) ∧ (0 : ℝ) < Real.pi / 4
      constructor <;> nlinarith [Real.pi_pos]
    refine ⟨F 0 - primitive 0, ?_⟩
    intro x hx
    have heq : F x - primitive x = F 0 - primitive 0 :=
      isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo hdiff
        (fun y hy => (hzero y hy).deriv) hx h0
    linarith
  · rintro ⟨C, hC⟩
    change ∀ x ∈ branch, HasDerivAt F (integrand x) x
    intro x hx
    have hevent :
        F =ᶠ[nhds x] (fun y : ℝ => primitive y + C) := by
      filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
      exact hC y hy
    exact ((hprim x hx).add_const C).congr_of_eventuallyEq hevent

end
end ProofGap.Exercise2035
