import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise891

noncomputable section

def y (x : ℝ) : ℝ :=
  1 / (4 * (1 + x ^ 4)) +
    (1 / 4 : ℝ) * Real.log (x ^ 4 / (1 + x ^ 4))

def logarithmicForm (x : ℝ) : ℝ :=
  1 / (4 * (1 + x ^ 4)) + Real.log |x| -
    (1 / 4 : ℝ) * Real.log (1 + x ^ 4)

def expandedDerivative (x : ℝ) : ℝ :=
  -(4 * x ^ 3 / (4 * (1 + x ^ 4) ^ 2)) + 1 / x -
    (1 / 4 : ℝ) * (1 / (1 + x ^ 4)) * 4 * x ^ 3

def finalDerivative (x : ℝ) : ℝ :=
  1 / (x * (1 + x ^ 4) ^ 2)

theorem gap1 (x : ℝ) (hx : x ≠ 0) :
    y x = logarithmicForm x := by
  have hx4 : x ^ 4 ≠ 0 := pow_ne_zero 4 hx
  have hden : 1 + x ^ 4 ≠ 0 := by positivity
  unfold y logarithmicForm
  rw [Real.log_div hx4 hden, Real.log_pow]
  simp only [Real.log_abs]
  ring

theorem gap2 (x : ℝ) (hx : x ≠ 0) :
    deriv y x = expandedDerivative x := by
  have hy : y = logarithmicForm := by
    funext z
    by_cases hz : z = 0
    · subst z
      norm_num [y, logarithmicForm]
    · exact gap1 z hz
  rw [hy]
  have hqne : 1 + x ^ 4 ≠ 0 := by positivity
  have hpow : HasDerivAt (fun z : ℝ => z ^ 4) (4 * x ^ 3) x := by
    simpa using (hasDerivAt_id x).pow 4
  have hq : HasDerivAt (fun z : ℝ => 1 + z ^ 4) (4 * x ^ 3) x :=
    hpow.const_add 1
  have hD :
      HasDerivAt (fun z : ℝ => 4 * (1 + z ^ 4))
        (4 * (4 * x ^ 3)) x := by
    simpa using (hasDerivAt_const x (4 : ℝ)).mul hq
  have hDne : 4 * (1 + x ^ 4) ≠ 0 :=
    mul_ne_zero (by norm_num) hqne
  have hfirst :
      HasDerivAt (fun z : ℝ => 1 / (4 * (1 + z ^ 4)))
        (-(4 * (4 * x ^ 3)) / (4 * (1 + x ^ 4)) ^ 2) x := by
    simpa only [one_div] using hD.inv hDne
  have hlogq :
      HasDerivAt (fun z : ℝ => Real.log (1 + z ^ 4))
        ((1 / (1 + x ^ 4)) * (4 * x ^ 3)) x := by
    simpa only [one_div] using
      (Real.hasDerivAt_log hqne).comp x hq
  have hscale :
      HasDerivAt
        (fun z : ℝ => (1 / 4 : ℝ) * Real.log (1 + z ^ 4))
        ((1 / 4 : ℝ) * ((1 / (1 + x ^ 4)) * (4 * x ^ 3))) x := by
    simpa using (hasDerivAt_const x (1 / 4 : ℝ)).mul hlogq
  have hall :
      HasDerivAt
        (fun z : ℝ =>
          1 / (4 * (1 + z ^ 4)) + Real.log z -
            (1 / 4 : ℝ) * Real.log (1 + z ^ 4))
        (expandedDerivative x) x := by
    convert (hfirst.add (Real.hasDerivAt_log hx)).sub hscale using 1
    · unfold expandedDerivative
      field_simp [hx, hqne] <;> ring
  have hfun :
      logarithmicForm =
        (fun z : ℝ =>
          1 / (4 * (1 + z ^ 4)) + Real.log z -
            (1 / 4 : ℝ) * Real.log (1 + z ^ 4)) := by
    funext z
    simp [logarithmicForm, Real.log_abs]
  rw [hfun]
  exact hall.deriv

theorem gap3 (x : ℝ) (hx : x ≠ 0) :
    expandedDerivative x = finalDerivative x := by
  have hden : 1 + x ^ 4 ≠ 0 := by positivity
  unfold expandedDerivative finalDerivative
  field_simp [hx, hden] <;> ring

theorem gap4 (x : ℝ) (hx : x ≠ 0) :
    deriv y x = finalDerivative x := by
  calc
    deriv y x = expandedDerivative x := gap2 x hx
    _ = finalDerivative x := gap3 x hx

end

end ProofGap.Exercise891
