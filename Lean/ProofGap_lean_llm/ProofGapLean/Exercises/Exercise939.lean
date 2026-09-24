import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise939

noncomputable section

def y (x : ℝ) : ℝ :=
  Real.arctan (Real.sqrt (x ^ 2 - 1)) -
    Real.log x / Real.sqrt (x ^ 2 - 1)

def expandedDerivative (x : ℝ) : ℝ :=
  1 / (1 + x ^ 2 - 1) * (x / Real.sqrt (x ^ 2 - 1)) -
    1 / (x * Real.sqrt (x ^ 2 - 1)) +
    x * Real.log x / ((x ^ 2 - 1) * Real.sqrt (x ^ 2 - 1))

def finalDerivative (x : ℝ) : ℝ :=
  x * Real.log x / Real.sqrt (x ^ 2 - 1) ^ 3

private lemma sq_sub_one_pos {x : ℝ} (hx : 1 < x) : 0 < x ^ 2 - 1 := by
  have hm : 0 < x - 1 := sub_pos.mpr hx
  have hp : 0 < x + 1 := by linarith
  nlinarith [mul_pos hm hp]

theorem gap1 (x : ℝ) (hx : 1 < x) :
    HasDerivAt y (expandedDerivative x) x := by
  have hA : 0 < x ^ 2 - 1 := sq_sub_one_pos hx
  have hA0 : x ^ 2 - 1 ≠ 0 := ne_of_gt hA
  have hs : 0 < Real.sqrt (x ^ 2 - 1) := Real.sqrt_pos.2 hA
  have hs0 : Real.sqrt (x ^ 2 - 1) ≠ 0 := ne_of_gt hs
  have hxpos : 0 < x := by linarith
  have hx0 : x ≠ 0 := ne_of_gt hxpos
  have hsq : Real.sqrt (x ^ 2 - 1) ^ 2 = x ^ 2 - 1 :=
    Real.sq_sqrt (le_of_lt hA)
  have hinner0 :=
    ((hasDerivAt_id x).pow 2).sub (hasDerivAt_const x (1 : ℝ))
  have hinner :
      HasDerivAt (fun t : ℝ => t ^ 2 - 1) (2 * x) x := by
    convert hinner0 using 1 <;> simp [id_eq] <;> ring
  have hroot0 := (Real.hasDerivAt_sqrt hA0).comp x hinner
  change HasDerivAt
    (fun t : ℝ => Real.sqrt (t ^ 2 - 1))
    (1 / (2 * Real.sqrt (x ^ 2 - 1)) * (2 * x)) x at hroot0
  have hcroot :
      1 / (2 * Real.sqrt (x ^ 2 - 1)) * (2 * x) =
        x / Real.sqrt (x ^ 2 - 1) := by
    field_simp [hs0]
  have hroot :
      HasDerivAt (fun t : ℝ => Real.sqrt (t ^ 2 - 1))
        (x / Real.sqrt (x ^ 2 - 1)) x := by
    simpa only [hcroot] using hroot0
  have htan0 :=
    (Real.hasDerivAt_arctan (Real.sqrt (x ^ 2 - 1))).comp x hroot
  change HasDerivAt
    (fun t : ℝ => Real.arctan (Real.sqrt (t ^ 2 - 1)))
    (1 / (1 + Real.sqrt (x ^ 2 - 1) ^ 2) *
      (x / Real.sqrt (x ^ 2 - 1))) x at htan0
  have htan :
      HasDerivAt
        (fun t : ℝ => Real.arctan (Real.sqrt (t ^ 2 - 1)))
        (1 / (1 + x ^ 2 - 1) * (x / Real.sqrt (x ^ 2 - 1))) x := by
    convert htan0 using 1
    rw [hsq]
    ring
  have hlog : HasDerivAt Real.log (1 / x) x := by
    simpa [one_div] using Real.hasDerivAt_log hx0
  have hquot :
      HasDerivAt
        (fun t : ℝ => Real.log t / Real.sqrt (t ^ 2 - 1))
        (1 / (x * Real.sqrt (x ^ 2 - 1)) -
          x * Real.log x /
            ((x ^ 2 - 1) * Real.sqrt (x ^ 2 - 1))) x := by
    convert hlog.div hroot hs0 using 1
    field_simp [hx0, hA0, hs0]
    rw [hsq] <;> ring
  unfold y expandedDerivative
  convert htan.sub hquot using 1 <;> ring

theorem gap2 (x : ℝ) (hx : 1 < x) :
    expandedDerivative x = finalDerivative x := by
  have hA : 0 < x ^ 2 - 1 := sq_sub_one_pos hx
  have hs : 0 < Real.sqrt (x ^ 2 - 1) := Real.sqrt_pos.2 hA
  have hs0 : Real.sqrt (x ^ 2 - 1) ≠ 0 := ne_of_gt hs
  have hxpos : 0 < x := by linarith
  have hx0 : x ≠ 0 := ne_of_gt hxpos
  have hsq : Real.sqrt (x ^ 2 - 1) ^ 2 = x ^ 2 - 1 :=
    Real.sq_sqrt (le_of_lt hA)
  have hfirst :
      1 / (1 + x ^ 2 - 1) * (x / Real.sqrt (x ^ 2 - 1)) =
        1 / (x * Real.sqrt (x ^ 2 - 1)) := by
    field_simp [hx0, hs0] <;> ring
  have hcube :
      (x ^ 2 - 1) * Real.sqrt (x ^ 2 - 1) =
        Real.sqrt (x ^ 2 - 1) ^ 3 := by
    calc
      (x ^ 2 - 1) * Real.sqrt (x ^ 2 - 1) =
          Real.sqrt (x ^ 2 - 1) ^ 2 * Real.sqrt (x ^ 2 - 1) := by
            rw [hsq]
      _ = Real.sqrt (x ^ 2 - 1) ^ 3 := by ring
  unfold expandedDerivative finalDerivative
  rw [hfirst, hcube]
  ring

theorem gap3 (x : ℝ) (hx : 1 < x) :
    HasDerivAt y (finalDerivative x) x := by
  rw [← gap2 x hx]
  exact gap1 x hx

end

end ProofGap.Exercise939
