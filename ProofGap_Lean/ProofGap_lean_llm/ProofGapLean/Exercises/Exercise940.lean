import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise940

noncomputable section

def y (x : ℝ) : ℝ :=
  Real.arcsin x / Real.sqrt (1 - x ^ 2) +
    (1 / 2 : ℝ) * Real.log ((1 - x) / (1 + x))

def expandedDerivative (x : ℝ) : ℝ :=
  1 / (1 - x ^ 2) +
    x * Real.arcsin x / Real.sqrt (1 - x ^ 2) ^ 3 +
    (1 / 2 : ℝ) * (-(1 / (1 - x)) - 1 / (1 + x))

def finalDerivative (x : ℝ) : ℝ :=
  x * Real.arcsin x / Real.sqrt (1 - x ^ 2) ^ 3

theorem gap1 (x : ℝ) (hx : |x| < 1) :
    HasDerivAt y (expandedDerivative x) x := by
  have hxm : -1 < x := (abs_lt.mp hx).1
  have hxp : x < 1 := (abs_lt.mp hx).2
  have hm : 0 < 1 - x := by linarith
  have hp : 0 < 1 + x := by linarith
  have hfactor : (1 - x) * (1 + x) = 1 - x ^ 2 := by ring
  have harg : 0 < 1 - x ^ 2 := by
    rw [← hfactor]
    exact mul_pos hm hp
  have hsqrt : Real.sqrt (1 - x ^ 2) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 harg)
  have hsqsqrt : Real.sqrt (1 - x ^ 2) ^ 2 = 1 - x ^ 2 :=
    Real.sq_sqrt (le_of_lt harg)
  have hasin :
      HasDerivAt Real.arcsin (1 / Real.sqrt (1 - x ^ 2)) x := by
    simpa only using
      (Real.hasDerivAt_arcsin (ne_of_gt hxm) (ne_of_lt hxp))
  have hcos :
      HasDerivAt (fun z : ℝ => Real.cos (Real.arcsin z))
        (-x / Real.sqrt (1 - x ^ 2)) x := by
    convert hasin.cos using 1
    rw [Real.sin_arcsin (le_of_lt hxm) (le_of_lt hxp)]
    ring
  have hsqrtDeriv :
      HasDerivAt (fun z : ℝ => Real.sqrt (1 - z ^ 2))
        (-x / Real.sqrt (1 - x ^ 2)) x := by
    simpa only [Real.cos_arcsin, pow_two] using hcos
  have hfirst' :
      HasDerivAt
        (fun z : ℝ => Real.arcsin z / Real.sqrt (1 - z ^ 2))
        (1 / Real.sqrt (1 - x ^ 2) ^ 2 +
          x * Real.arcsin x / Real.sqrt (1 - x ^ 2) ^ 3) x := by
    convert hasin.div hsqrtDeriv hsqrt using 1 <;>
      field_simp [hsqrt] <;> ring
  have hfirst :
      HasDerivAt
        (fun z : ℝ => Real.arcsin z / Real.sqrt (1 - z ^ 2))
        (1 / (1 - x ^ 2) +
          x * Real.arcsin x / Real.sqrt (1 - x ^ 2) ^ 3) x := by
    simpa [hsqsqrt] using hfirst'
  have hnum : HasDerivAt (fun z : ℝ => 1 - z) (-1) x := by
    convert (hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id x) using 1 <;>
      simp <;> ring
  have hden : HasDerivAt (fun z : ℝ => 1 + z) 1 x := by
    convert (hasDerivAt_const x (1 : ℝ)).add (hasDerivAt_id x) using 1 <;>
      simp <;> ring
  have hquot :
      HasDerivAt (fun z : ℝ => (1 - z) / (1 + z))
        (-2 / (1 + x) ^ 2) x := by
    convert hnum.div hden (ne_of_gt hp) using 1 <;>
      field_simp [ne_of_gt hp] <;> ring
  have hqpos : 0 < (1 - x) / (1 + x) := div_pos hm hp
  have hlog :
      HasDerivAt (fun z : ℝ => Real.log ((1 - z) / (1 + z)))
        (-(1 / (1 - x)) - 1 / (1 + x)) x := by
    convert hquot.log (ne_of_gt hqpos) using 1 <;>
      field_simp [ne_of_gt hm, ne_of_gt hp, ne_of_gt hqpos] <;> ring
  change
    HasDerivAt
      (fun z : ℝ =>
        Real.arcsin z / Real.sqrt (1 - z ^ 2) +
          (1 / 2 : ℝ) * Real.log ((1 - z) / (1 + z)))
      (1 / (1 - x ^ 2) +
        x * Real.arcsin x / Real.sqrt (1 - x ^ 2) ^ 3 +
        (1 / 2 : ℝ) * (-(1 / (1 - x)) - 1 / (1 + x))) x
  simpa only [Pi.add_apply] using
    hfirst.add (hlog.const_mul (1 / 2 : ℝ))

theorem gap2 (x : ℝ) (hx : |x| < 1) :
    expandedDerivative x = finalDerivative x := by
  have hxm : -1 < x := (abs_lt.mp hx).1
  have hxp : x < 1 := (abs_lt.mp hx).2
  have hm : 0 < 1 - x := by linarith
  have hp : 0 < 1 + x := by linarith
  have harg : 0 < 1 - x ^ 2 := by
    nlinarith [mul_pos hm hp]
  have hcancel :
      1 / (1 - x ^ 2) +
          (1 / 2 : ℝ) * (-(1 / (1 - x)) - 1 / (1 + x)) = 0 := by
    field_simp [ne_of_gt hm, ne_of_gt hp, ne_of_gt harg] <;> ring
  unfold expandedDerivative finalDerivative
  calc
    1 / (1 - x ^ 2) +
          x * Real.arcsin x / Real.sqrt (1 - x ^ 2) ^ 3 +
          (1 / 2 : ℝ) * (-(1 / (1 - x)) - 1 / (1 + x)) =
        x * Real.arcsin x / Real.sqrt (1 - x ^ 2) ^ 3 +
          (1 / (1 - x ^ 2) +
            (1 / 2 : ℝ) * (-(1 / (1 - x)) - 1 / (1 + x))) := by ring
    _ = x * Real.arcsin x / Real.sqrt (1 - x ^ 2) ^ 3 := by
      rw [hcancel]
      ring

theorem gap3 (x : ℝ) (hx : |x| < 1) :
    HasDerivAt y (finalDerivative x) x := by
  rw [← gap2 x hx]
  exact gap1 x hx

end

end ProofGap.Exercise940
