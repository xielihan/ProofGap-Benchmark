import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

namespace ProofGap.Exercise945

noncomputable section

def arccot (x : ℝ) : ℝ := Real.pi / 2 - Real.arctan x

def y (a x : ℝ) : ℝ :=
  arccot ((a - 2 * x) / (2 * Real.sqrt (a * x - x ^ 2)))

def expandedDerivative (a x : ℝ) : ℝ :=
  -(1 / (1 + (a - 2 * x) ^ 2 / (4 * (a * x - x ^ 2)))) *
    (1 / 2 : ℝ) *
    ((-2 * Real.sqrt (a * x - x ^ 2) -
        (a - 2 * x) ^ 2 / (2 * Real.sqrt (a * x - x ^ 2))) /
      (a * x - x ^ 2))

def finalDerivative (a x : ℝ) : ℝ := 1 / Real.sqrt (a * x - x ^ 2)

private theorem expanded_eq_final_aux (a x : ℝ) (ha : 0 < a)
    (hx : 0 < a * x - x ^ 2) :
    expandedDerivative a x = finalDerivative a x := by
  unfold expandedDerivative finalDerivative
  set q : ℝ := a * x - x ^ 2 with hqdef
  set s : ℝ := Real.sqrt q with hsdef
  set d : ℝ := a - 2 * x with hddef
  have hqpos : 0 < q := by
    simpa [hqdef] using hx
  have hqne : q ≠ 0 := ne_of_gt hqpos
  have hspos : 0 < s := by
    rw [hsdef]
    exact Real.sqrt_pos.2 hqpos
  have hsne : s ≠ 0 := ne_of_gt hspos
  have hsq : s ^ 2 = q := by
    rw [hsdef]
    exact Real.sq_sqrt (le_of_lt hqpos)
  have hdenpos : 0 < 1 + d ^ 2 / (4 * q) := by positivity
  field_simp [hqne, hsne, ne_of_gt hdenpos] <;>
    nlinarith [hsq]

theorem gap1 (a x : ℝ) (ha : 0 < a) (hx : 0 < a * x - x ^ 2) :
    HasDerivAt (y a) (expandedDerivative a x) x := by
  set q : ℝ := a * x - x ^ 2 with hqdef
  set s : ℝ := Real.sqrt q with hsdef
  set d : ℝ := a - 2 * x with hddef
  have hqpos : 0 < q := by
    simpa [hqdef] using hx
  have hqne : q ≠ 0 := ne_of_gt hqpos
  have hspos : 0 < s := by
    rw [hsdef]
    exact Real.sqrt_pos.2 hqpos
  have hsne : s ≠ 0 := ne_of_gt hspos
  have hsq : s ^ 2 = q := by
    rw [hsdef]
    exact Real.sq_sqrt (le_of_lt hqpos)
  have hpoly : d ^ 2 + 4 * q = a ^ 2 := by
    rw [hddef, hqdef]
    ring
  have hQ : HasDerivAt (fun t : ℝ => a * t - t ^ 2) d x := by
    convert
      ((hasDerivAt_const x a).mul (hasDerivAt_id x)).sub
        ((hasDerivAt_id x).pow 2) using 1 <;>
      simp [hddef] <;> ring
  have hsqrt : HasDerivAt Real.sqrt (1 / (2 * s)) q := by
    simpa [hsdef] using Real.hasDerivAt_sqrt hqne
  have hS : HasDerivAt
      (fun t : ℝ => Real.sqrt (a * t - t ^ 2)) (d / (2 * s)) x := by
    convert hsqrt.comp x hQ using 1 <;> ring
  have hN : HasDerivAt (fun t : ℝ => a - 2 * t) (-2) x := by
    convert
      (hasDerivAt_const x a).sub
        ((hasDerivAt_const x (2 : ℝ)).mul (hasDerivAt_id x)) using 1 <;>
      simp <;> ring
  have hD : HasDerivAt
      (fun t : ℝ => 2 * Real.sqrt (a * t - t ^ 2)) (d / s) x := by
    convert (hasDerivAt_const x (2 : ℝ)).mul hS using 1 <;>
      simp [hsdef, hqdef] <;> field_simp [hsne] <;> ring
  have hdenne : 2 * Real.sqrt (a * x - x ^ 2) ≠ 0 := by
    simpa [hsdef, hqdef] using
      (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) hsne)
  have hU := hN.div hD hdenne
  have hA :=
    (Real.hasDerivAt_arctan
      ((a - 2 * x) / (2 * Real.sqrt (a * x - x ^ 2)))).comp x hU
  have hY := (hasDerivAt_const x (Real.pi / 2)).sub hA
  change HasDerivAt (y a) _ x at hY
  simp only [← hqdef, ← hsdef, ← hddef] at hY
  rw [expanded_eq_final_aux a x ha hx]
  unfold finalDerivative
  change HasDerivAt (y a) (1 / s) x
  have harcden : 1 + (d / (2 * s)) ^ 2 ≠ 0 := by positivity
  have harcden' : (d / (2 * s)) ^ 2 + 1 ≠ 0 := by positivity
  convert hY using 1
  field_simp [hsne, harcden, harcden'] <;>
    nlinarith [hsq, hpoly]

theorem gap2 (a x : ℝ) (ha : 0 < a) (hx : 0 < a * x - x ^ 2) :
    expandedDerivative a x = finalDerivative a x := by
  exact expanded_eq_final_aux a x ha hx

theorem gap3 (a x : ℝ) (ha : 0 < a) (hx : 0 < a * x - x ^ 2) :
    HasDerivAt (y a) (finalDerivative a x) x := by
  rw [← gap2 a x ha hx]
  exact gap1 a x ha hx

end

end ProofGap.Exercise945
