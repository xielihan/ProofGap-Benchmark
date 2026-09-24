import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise969

noncomputable section

def y (x : ℝ) : ℝ := Real.arctan (Real.tanh x)

def expandedDerivative (x : ℝ) : ℝ :=
  1 / (1 + Real.tanh x ^ 2) * (1 / Real.cosh x ^ 2)

def finalDerivative (x : ℝ) : ℝ := 1 / Real.cosh (2 * x)

theorem gap1 (x : ℝ) : HasDerivAt y (expandedDerivative x) x := by
  unfold y expandedDerivative
  have he_neg :
      HasDerivAt (fun z : ℝ => Real.exp (-z)) (-Real.exp (-x)) x := by
    convert
      (Real.hasDerivAt_exp (-x)).comp x (hasDerivAt_id x).neg using 1 <;> simp
  have hs_exp :
      HasDerivAt (fun z : ℝ => (Real.exp z - Real.exp (-z)) / 2)
        ((Real.exp x + Real.exp (-x)) / 2) x := by
    convert ((Real.hasDerivAt_exp x).sub he_neg).div_const 2 using 1 <;> ring
  have hc_exp :
      HasDerivAt (fun z : ℝ => (Real.exp z + Real.exp (-z)) / 2)
        ((Real.exp x - Real.exp (-x)) / 2) x := by
    convert ((Real.hasDerivAt_exp x).add he_neg).div_const 2 using 1 <;> ring
  have hs : HasDerivAt (fun z : ℝ => Real.sinh z) (Real.cosh x) x := by
    simpa only [Real.sinh_eq, Real.cosh_eq] using hs_exp
  have hcosh_deriv : HasDerivAt (fun z : ℝ => Real.cosh z) (Real.sinh x) x := by
    simpa only [Real.sinh_eq, Real.cosh_eq] using hc_exp
  have hc : Real.cosh x ≠ 0 := ne_of_gt (Real.cosh_pos x)
  have ht_quot :
      HasDerivAt (fun z : ℝ => Real.sinh z / Real.cosh z)
        ((Real.cosh x ^ 2 - Real.sinh x ^ 2) / Real.cosh x ^ 2) x := by
    convert hs.div hcosh_deriv hc using 1 <;> ring
  rw [Real.cosh_sq_sub_sinh_sq] at ht_quot
  have ht :
      HasDerivAt (fun z : ℝ => Real.tanh z) (1 / Real.cosh x ^ 2) x := by
    simpa only [Real.tanh_eq_sinh_div_cosh] using ht_quot
  convert ht.arctan using 1 <;> ring

theorem gap2 (x : ℝ) : expandedDerivative x = finalDerivative x := by
  unfold expandedDerivative finalDerivative
  have hc : Real.cosh x ≠ 0 := ne_of_gt (Real.cosh_pos x)
  have ht : 1 + Real.tanh x ^ 2 ≠ 0 := by
    positivity
  have hcosh :
      Real.cosh (2 * x) = Real.cosh x ^ 2 + Real.sinh x ^ 2 := by
    calc
      Real.cosh (2 * x) = Real.cosh (x + x) := by rw [two_mul]
      _ = Real.cosh x * Real.cosh x + Real.sinh x * Real.sinh x := by
        rw [Real.cosh_add]
      _ = Real.cosh x ^ 2 + Real.sinh x ^ 2 := by ring
  have hden :
      (1 + Real.tanh x ^ 2) * Real.cosh x ^ 2 = Real.cosh (2 * x) := by
    rw [Real.tanh_eq_sinh_div_cosh, hcosh]
    field_simp [hc]
  rw [← hden]
  field_simp [hc, ht]

theorem gap3 (x : ℝ) : HasDerivAt y (finalDerivative x) x := by
  rw [← gap2 x]
  exact gap1 x

end

end ProofGap.Exercise969
