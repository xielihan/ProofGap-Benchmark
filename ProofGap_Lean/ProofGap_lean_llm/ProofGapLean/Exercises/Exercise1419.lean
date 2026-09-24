import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.DerivativeTest
import Mathlib.Analysis.Complex.ExponentialBounds

namespace ProofGap.Exercise1419

noncomputable section

def y (x : ℝ) : ℝ := (x + 1) ^ 10 * Real.exp (-x)

def Approx (a b ε : ℝ) : Prop := |a - b| < ε

theorem gap1 (x : ℝ) :
    deriv y x = Real.exp (-x) * (x + 1) ^ 9 * (9 - x) := by
  unfold y
  have hbase : HasDerivAt (fun z : ℝ => z + 1) 1 x := by
    exact (hasDerivAt_id x).add_const 1
  have hpow : HasDerivAt (fun z : ℝ => (z + 1) ^ 10)
      (10 * (x + 1) ^ 9) x := by
    simpa using hbase.fun_pow 10
  have hneg : HasDerivAt (fun z : ℝ => -z) (-1) x := by
    simpa using (hasDerivAt_id x).neg
  have hexp : HasDerivAt (fun z : ℝ => Real.exp (-z))
      (-Real.exp (-x)) x := by
    convert (Real.hasDerivAt_exp (-x)).comp x hneg using 1 <;> ring
  have hprod := hpow.mul hexp
  convert hprod.deriv using 1
  rw [pow_succ]
  ring

theorem gap2 (x : ℝ) (hcrit : deriv y x = 0) :
    x = -1 ∨ x = 9 := by
  rw [gap1 x] at hcrit
  rcases mul_eq_zero.mp hcrit with hprod | hlinear
  · rcases mul_eq_zero.mp hprod with hexp | hpow
    · exact False.elim (Real.exp_ne_zero (-x) hexp)
    · left
      have hbase : x + 1 = 0 := by
        exact pow_eq_zero hpow
      linarith
  · right
    linarith

theorem gap3 (x : ℝ) (hx : x < -1) : deriv y x < 0 := by
  rw [gap1]
  have hpow : (x + 1) ^ 9 < 0 := by
    exact (show Odd 9 by exact ⟨4, by norm_num⟩).pow_neg (by linarith)
  exact mul_neg_of_neg_of_pos
    (mul_neg_of_pos_of_neg (Real.exp_pos (-x)) hpow)
    (by linarith)

theorem gap4 (x : ℝ) (h₁ : -1 < x) (h₂ : x < 9) :
    0 < deriv y x := by
  rw [gap1]
  exact mul_pos
    (mul_pos (Real.exp_pos (-x)) (pow_pos (by linarith) 9))
    (by linarith)

theorem gap5 (x : ℝ) (hx : 9 < x) : deriv y x < 0 := by
  rw [gap1]
  exact mul_neg_of_pos_of_neg
    (mul_pos (Real.exp_pos (-x)) (pow_pos (by linarith) 9))
    (by linarith)

theorem gap6 : IsMinOn y Set.univ (-1) ∧ y (-1) = 0 := by
  have hzero : y (-1) = 0 := by
    norm_num [y]
  constructor
  · rw [isMinOn_iff]
    intro x _
    rw [hzero]
    unfold y
    positivity
  · exact hzero

theorem gap7 :
    IsLocalMax y 9 ∧ y 9 = 10 ^ 10 * Real.exp (-9) := by
  have hcont : Continuous y := by
    unfold y
    exact ((continuous_id.add continuous_const).pow 10).mul
      (Real.continuous_exp.comp continuous_neg)
  have hmax : IsLocalMax y 9 := by
    apply isLocalMax_of_deriv_Ioo
      (a := (-1 : ℝ)) (b := (9 : ℝ)) (c := (10 : ℝ))
      (by norm_num) (by norm_num) hcont.continuousAt
    · intro x hx
      exact
        (differentiableAt_of_deriv_ne_zero
          (gap4 x hx.1 hx.2).ne').differentiableWithinAt
    · intro x hx
      exact
        (differentiableAt_of_deriv_ne_zero
          (gap5 x hx.1).ne).differentiableWithinAt
    · intro x hx
      exact le_of_lt (gap4 x hx.1 hx.2)
    · intro x hx
      exact le_of_lt (gap5 x hx.1)
  constructor
  · exact hmax
  · norm_num [y]

theorem gap8 :
    Approx (10 ^ 10 * Real.exp (-9)) 1234000 1000 := by
  have hexp9 : Real.exp (-9) = Real.exp (-1) ^ 9 := by
    calc
      Real.exp (-9) = Real.exp ((9 : ℕ) * (-1 : ℝ)) := by norm_num
      _ = Real.exp (-1) ^ 9 := Real.exp_nat_mul (-1) 9
  have hlowpow :
      (0.36787944116 : ℝ) ^ 9 < Real.exp (-1) ^ 9 := by
    exact pow_lt_pow_left₀ Real.exp_neg_one_gt_d9
      (by norm_num) (by norm_num)
  have huppow :
      Real.exp (-1) ^ 9 < (0.3678794412 : ℝ) ^ 9 := by
    exact pow_lt_pow_left₀ Real.exp_neg_one_lt_d9
      (Real.exp_pos (-1)).le (by norm_num)
  have hlow :
      (1233000 : ℝ) < 10 ^ 10 * Real.exp (-9) := by
    rw [hexp9]
    calc
      (1233000 : ℝ) <
          10 ^ 10 * (0.36787944116 : ℝ) ^ 9 := by norm_num
      _ < 10 ^ 10 * Real.exp (-1) ^ 9 :=
        mul_lt_mul_of_pos_left hlowpow (by norm_num)
  have hupp :
      10 ^ 10 * Real.exp (-9) < (1235000 : ℝ) := by
    rw [hexp9]
    calc
      10 ^ 10 * Real.exp (-1) ^ 9 <
          10 ^ 10 * (0.3678794412 : ℝ) ^ 9 :=
        mul_lt_mul_of_pos_left huppow (by norm_num)
      _ < (1235000 : ℝ) := by norm_num
  unfold Approx
  rw [abs_lt]
  constructor <;> linarith

theorem gap9 :
    IsLocalMax y 9 ∧ Approx (y 9) 1234000 1000 := by
  constructor
  · exact gap7.1
  · rw [gap7.2]
    exact gap8

end
end ProofGap.Exercise1419
