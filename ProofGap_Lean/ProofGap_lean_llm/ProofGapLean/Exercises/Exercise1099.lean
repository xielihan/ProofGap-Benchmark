import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

namespace ProofGap.Exercise1099

noncomputable section

def cubeRoot (x : ℝ) : ℝ := Real.rpow x (1 / 3 : ℝ)
def differential (dx : ℝ) : ℝ := deriv cubeRoot 1 * dx
def Approx (x y ε : ℝ) : Prop := |x - y| < ε

private lemma cubeRoot_51_50_between (a b : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hla : a ^ 3 < (51 / 50 : ℝ))
    (hub : (51 / 50 : ℝ) < b ^ 3) :
    a < cubeRoot (51 / 50 : ℝ) ∧ cubeRoot (51 / 50 : ℝ) < b := by
  have hrpos : 0 < cubeRoot (51 / 50 : ℝ) := by
    unfold cubeRoot
    exact Real.rpow_pos_of_pos (by norm_num) _
  have hr3 : cubeRoot (51 / 50 : ℝ) ^ 3 = (51 / 50 : ℝ) := by
    unfold cubeRoot
    convert Real.rpow_inv_natCast_pow
      (n := 3) (show (0 : ℝ) ≤ 51 / 50 by norm_num)
      (by norm_num) using 1 <;> norm_num
  constructor
  · exact lt_of_pow_lt_pow_left₀ 3 hrpos.le (by simpa [hr3] using hla)
  · exact lt_of_pow_lt_pow_left₀ 3 hb (by simpa [hr3] using hub)

theorem gap1 :
    HasDerivAt cubeRoot (1 / 3 : ℝ) 1 := by
  unfold cubeRoot
  convert
    Real.hasDerivAt_rpow_const (x := (1 : ℝ)) (p := (1 / 3 : ℝ))
      (Or.inl one_ne_zero) using 1 <;>
    norm_num

theorem gap2 :
    differential (1 / 50 : ℝ) =
      deriv cubeRoot 1 * (1 / 50 : ℝ) := by rfl

theorem gap3 :
    Approx (deriv cubeRoot 1 * (1 / 50 : ℝ))
      (66 / 10000 : ℝ) (1 / 10000 : ℝ) := by
  unfold Approx
  rw [gap1.deriv]
  norm_num [abs_of_nonneg, abs_of_nonpos]

theorem gap4 :
    Approx (differential (1 / 50 : ℝ))
      (66 / 10000 : ℝ) (1 / 10000 : ℝ) := by
  rw [gap2]
  exact gap3

theorem gap5 :
    cubeRoot (102 / 100 : ℝ) = cubeRoot (1 + 1 / 50 : ℝ) := by
  congr 1
  norm_num

theorem gap6 :
    Approx (cubeRoot (1 + 1 / 50 : ℝ))
      (cubeRoot 1 + differential (1 / 50 : ℝ))
      (1 / 10000 : ℝ) := by
  have hb := cubeRoot_51_50_between
    (1 + 1 / 150 - 1 / 10000 : ℝ)
    (1 + 1 / 150 + 1 / 10000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hd : deriv cubeRoot 1 = (1 / 3 : ℝ) := gap1.deriv
  unfold Approx differential
  norm_num [cubeRoot, hd] at hb ⊢
  rw [abs_lt]
  constructor <;> linarith [hb.1, hb.2]

theorem gap7 :
    Approx (cubeRoot 1 + differential (1 / 50 : ℝ))
      (1 + 66 / 10000 : ℝ) (1 / 10000 : ℝ) := by
  have hd : deriv cubeRoot 1 = (1 / 3 : ℝ) := gap1.deriv
  unfold Approx differential
  norm_num [cubeRoot, hd, abs_of_nonneg, abs_of_nonpos]

theorem gap8 :
    Approx (cubeRoot (102 / 100 : ℝ))
      (1 + 66 / 10000 : ℝ) (1 / 10000 : ℝ) := by
  rw [gap5]
  have hb := cubeRoot_51_50_between
    (1 + 66 / 10000 - 1 / 10000 : ℝ)
    (1 + 66 / 10000 + 1 / 10000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold Approx
  norm_num at hb ⊢
  rw [abs_lt]
  constructor <;> linarith [hb.1, hb.2]

theorem gap9 :
    Approx (cubeRoot (102 / 100 : ℝ))
      (1007 / 1000 : ℝ) (1 / 1000 : ℝ) := by
  rw [gap5]
  have hb := cubeRoot_51_50_between
    (1007 / 1000 - 1 / 1000 : ℝ)
    (1007 / 1000 + 1 / 1000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold Approx
  norm_num at hb ⊢
  rw [abs_lt]
  constructor <;> linarith [hb.1, hb.2]

end

end ProofGap.Exercise1099
