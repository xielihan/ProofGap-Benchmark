import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise4250

noncomputable section

open scoped Interval

def curveY (x : ℝ) : ℝ :=
  x ^ 2

def curveMap (x : ℝ) : ℝ × ℝ :=
  (x, curveY x)

def lineIntegral : ℝ :=
  ∫ x in (-1 : ℝ)..1,
    (x ^ 2 - 2 * x * curveY x) +
      (curveY x ^ 2 - 2 * x * curveY x) * (2 * x)

theorem gap1 :
    ∀ x : ℝ, curveY x = x ^ 2 := by
  intro x
  rfl

theorem gap2 (x : ℝ) :
    deriv curveY x = 2 * x := by
  have h : HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by
    convert (hasDerivAt_id x).pow 2 using 1 <;> norm_num
  change deriv (fun y : ℝ => y ^ 2) x = 2 * x
  exact h.deriv

theorem gap3 :
    lineIntegral =
      ∫ x in (-1 : ℝ)..1,
        x ^ 2 - 2 * x ^ 3 + 2 * x * (x ^ 4 - 2 * x ^ 3) := by
  unfold lineIntegral curveY
  apply intervalIntegral.integral_congr
  intro x _
  ring

theorem gap4 :
    (∫ x in (-1 : ℝ)..1,
      x ^ 2 - 2 * x ^ 3 + 2 * x * (x ^ 4 - 2 * x ^ 3)) =
      -(14 / 15 : ℝ) := by
  let F : ℝ → ℝ := fun x =>
    x ^ 3 / 3 - x ^ 4 / 2 + x ^ 6 / 3 - 4 * x ^ 5 / 5
  have hF (x : ℝ) :
      HasDerivAt F
        (x ^ 2 - 2 * x ^ 3 + 2 * x * (x ^ 4 - 2 * x ^ 3)) x := by
    have h₁ :=
      ((((hasDerivAt_id x).pow 3).div_const 3).sub
        (((hasDerivAt_id x).pow 4).div_const 2)).add
        (((hasDerivAt_id x).pow 6).div_const 3)
    have h₂ := h₁.sub
      ((((hasDerivAt_id x).pow 5).const_mul 4).div_const 5)
    dsimp [F]
    convert h₂ using 1 <;> simp [id] <;> ring
  have hcont : Continuous (fun x : ℝ =>
      x ^ 2 - 2 * x ^ 3 + 2 * x * (x ^ 4 - 2 * x ^ 3)) := by
    fun_prop
  have hint :
      (∫ x in (-1 : ℝ)..1,
        x ^ 2 - 2 * x ^ 3 + 2 * x * (x ^ 4 - 2 * x ^ 3)) =
        F 1 - F (-1) := by
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x _ => hF x) (hcont.intervalIntegrable (-1) 1)
  calc
    (∫ x in (-1 : ℝ)..1,
      x ^ 2 - 2 * x ^ 3 + 2 * x * (x ^ 4 - 2 * x ^ 3)) =
        F 1 - F (-1) := hint
    _ = -(14 / 15 : ℝ) := by
      norm_num [F]

theorem gap5 :
    lineIntegral = -(14 / 15 : ℝ) := by
  rw [gap3]
  exact gap4

end

end ProofGap.Exercise4250
