import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1437

noncomputable section

def y (x : ℝ) : ℝ := x * Real.exp (-x)
def Approx (a b ε : ℝ) : Prop := |a - b| < ε

private theorem pow_le_pow_nonneg {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (n : ℕ) :
    a ^ n ≤ b ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, pow_succ]
      exact mul_le_mul ih hab ha (pow_nonneg (ha.trans hab) n)

theorem gap1 (x : ℝ) :
    deriv y x = Real.exp (-x) * (1 - x) := by
  have hneg : HasDerivAt (fun z : ℝ => -z) (-1) x := by
    simpa using (hasDerivAt_id x).neg
  have hexp : HasDerivAt (fun z : ℝ => Real.exp (-z))
      (Real.exp (-x) * (-1)) x :=
    (Real.hasDerivAt_exp (-x)).comp x hneg
  have hprod : HasDerivAt y
      (Real.exp (-x) + x * (Real.exp (-x) * (-1))) x := by
    simpa [y] using (hasDerivAt_id x).mul hexp
  convert hprod.deriv using 1 <;> ring

theorem gap2 : deriv y 1 = 0 := by
  simpa using (gap1 (1 : ℝ))

theorem gap3 (x : ℝ) (hx : x < 1) : 0 < deriv y x := by
  rw [gap1]
  exact mul_pos (Real.exp_pos _) (sub_pos.mpr hx)

theorem gap4 (x : ℝ) (hx : 1 < x) : deriv y x < 0 := by
  rw [gap1]
  exact mul_neg_of_pos_of_neg (Real.exp_pos _) (sub_neg.mpr hx)

theorem gap5 : IsMaxOn y Set.univ 1 := by
  intro x hx
  have hxe : x ≤ Real.exp (x - 1) := by
    have h := Real.add_one_le_exp (x - 1)
    linarith
  calc
    y x = Real.exp (-x) * x := by simp [y, mul_comm]
    _ ≤ Real.exp (-x) * Real.exp (x - 1) :=
      mul_le_mul_of_nonneg_left hxe (Real.exp_pos _).le
    _ = Real.exp (-1) := by
      have hsum : -x + (x - 1) = (-1 : ℝ) := by ring
      rw [← Real.exp_add, hsum]
    _ = y 1 := by simp [y]

theorem gap6 : y 1 = Real.exp (-1) := by
  simp [y]

theorem gap7 : Approx (Real.exp (-1)) 0.368 0.001 := by
  unfold Approx
  have hlbase :
      1 + ((1 : ℝ) / 256) ≤ Real.exp ((1 : ℝ) / 256) := by
    simpa [add_comm] using Real.add_one_le_exp ((1 : ℝ) / 256)
  have hlpow :
      (1 + ((1 : ℝ) / 256)) ^ (256 : ℕ) ≤
        Real.exp ((1 : ℝ) / 256) ^ (256 : ℕ) :=
    pow_le_pow_nonneg (by norm_num) hlbase 256
  have hneg :
      1 - ((1 : ℝ) / 256) ≤ Real.exp (-((1 : ℝ) / 256)) := by
    have h := Real.add_one_le_exp (-((1 : ℝ) / 256))
    nlinarith
  have hprod :
      Real.exp (-((1 : ℝ) / 256)) * Real.exp ((1 : ℝ) / 256) = 1 := by
    rw [← Real.exp_add]
    norm_num
  have hscaled :
      (1 - ((1 : ℝ) / 256)) * Real.exp ((1 : ℝ) / 256) ≤ 1 := by
    calc
      (1 - ((1 : ℝ) / 256)) * Real.exp ((1 : ℝ) / 256) ≤
          Real.exp (-((1 : ℝ) / 256)) * Real.exp ((1 : ℝ) / 256) :=
        mul_le_mul_of_nonneg_right hneg (Real.exp_pos _).le
      _ = 1 := hprod
  have hubase :
      Real.exp ((1 : ℝ) / 256) ≤ (256 : ℝ) / 255 := by
    linarith [hscaled]
  have hupow :
      Real.exp ((1 : ℝ) / 256) ^ (256 : ℕ) ≤
        ((256 : ℝ) / 255) ^ (256 : ℕ) :=
    pow_le_pow_nonneg (Real.exp_pos _).le hubase 256
  have hexp_pow :
      Real.exp ((1 : ℝ) / 256) ^ (256 : ℕ) = Real.exp 1 := by
    rw [← Real.exp_nat_mul]
    norm_num
  have he_lower : (1000 : ℝ) / 369 < Real.exp 1 := by
    calc
      (1000 : ℝ) / 369 < (1 + ((1 : ℝ) / 256)) ^ (256 : ℕ) := by
        norm_num
      _ ≤ Real.exp ((1 : ℝ) / 256) ^ (256 : ℕ) := hlpow
      _ = Real.exp 1 := hexp_pow
  have he_upper : Real.exp 1 < (1000 : ℝ) / 367 := by
    calc
      Real.exp 1 = Real.exp ((1 : ℝ) / 256) ^ (256 : ℕ) := hexp_pow.symm
      _ ≤ ((256 : ℝ) / 255) ^ (256 : ℕ) := hupow
      _ < (1000 : ℝ) / 367 := by norm_num
  have hpos : 0 < Real.exp 1 := Real.exp_pos 1
  have hexp_neg : Real.exp (-(1 : ℝ)) = 1 / Real.exp 1 := by
    simp [Real.exp_neg, one_div]
  have hlower : (0.367 : ℝ) < Real.exp (-1) := by
    rw [hexp_neg]
    apply (lt_div_iff₀ hpos).2
    nlinarith [he_upper]
  have hupper : Real.exp (-1) < (0.369 : ℝ) := by
    rw [hexp_neg]
    apply (div_lt_iff₀ hpos).2
    nlinarith [he_lower]
  rw [abs_lt]
  constructor <;> nlinarith

end
end ProofGap.Exercise1437
