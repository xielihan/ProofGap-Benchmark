import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace ProofGap.Exercise1445

noncomputable section

def f (x : ℝ) : ℝ := Real.rpow 2 x
def domain : Set ℝ := Set.Icc (-1) 5

private theorem hasDerivAt_const_base_rpow {a x : ℝ} (ha : 0 < a) :
    HasDerivAt (fun y : ℝ => Real.rpow a y)
      (Real.rpow a x * Real.log a) x := by
  have hinner :
      HasDerivAt (fun y : ℝ => Real.log a * y) (Real.log a) x := by
    simpa using
      (hasDerivAt_const x (Real.log a)).mul (hasDerivAt_id x)
  have hexp :
      HasDerivAt (fun y : ℝ => Real.exp (Real.log a * y))
        (Real.exp (Real.log a * x) * Real.log a) x :=
    (Real.hasDerivAt_exp (Real.log a * x)).comp x hinner
  have hrpow (y : ℝ) :
      Real.rpow a y = Real.exp (Real.log a * y) := by
    change a ^ y = Real.exp (Real.log a * y)
    exact (Real.rpow_def_of_pos ha) y
  simpa only [hrpow] using hexp

theorem gap1 (x : ℝ) :
    deriv f x = Real.rpow 2 x * Real.log 2 := by
  unfold f
  simpa using
    (hasDerivAt_const_base_rpow (a := (2 : ℝ)) (x := x) (by norm_num)).deriv

theorem gap2 (x : ℝ) : 0 < Real.rpow 2 x * Real.log 2 := by
  exact mul_pos (Real.rpow_pos_of_pos (by norm_num) x) (Real.log_pos (by norm_num))

theorem gap3 (x : ℝ) : 0 < deriv f x := by
  rw [gap1]
  exact gap2 x

theorem gap4 : StrictMonoOn f domain := by
  intro x hx y hy hxy
  unfold f
  exact Real.strictMono_rpow_of_base_gt_one (by norm_num) hxy

theorem gap5 : sInf (f '' domain) = Real.rpow 2 (-1) := by
  have hmono : StrictMonoOn f domain := gap4
  have hmem : (-1 : ℝ) ∈ domain := by
    constructor <;> norm_num
  have hleast : IsLeast (f '' domain) (f (-1)) := by
    constructor
    · exact ⟨-1, hmem, rfl⟩
    · rintro y ⟨x, hx, rfl⟩
      exact (hmono.monotoneOn hmem hx) hx.1
  simpa [f] using hleast.csInf_eq

theorem gap6 : Real.rpow 2 (-1) = 1 / 2 := by
  have hpos : (0 : ℝ) < 2 := by norm_num
  have hdef : Real.rpow 2 (-1) = Real.exp (Real.log 2 * (-1)) := by
    change (2 : ℝ) ^ (-1 : ℝ) = Real.exp (Real.log 2 * (-1))
    exact (Real.rpow_def_of_pos hpos) (-1)
  rw [hdef, mul_neg_one, Real.exp_neg, Real.exp_log hpos]
  norm_num

theorem gap7 : sInf (f '' domain) = 1 / 2 := by
  rw [gap5, gap6]

theorem gap8 : sSup (f '' domain) = Real.rpow 2 5 := by
  have hmono : StrictMonoOn f domain := gap4
  have hmem : (5 : ℝ) ∈ domain := by
    constructor <;> norm_num
  have hgreatest : IsGreatest (f '' domain) (f 5) := by
    constructor
    · exact ⟨5, hmem, rfl⟩
    · rintro y ⟨x, hx, rfl⟩
      exact (hmono.monotoneOn hx hmem) hx.2
  simpa [f] using hgreatest.csSup_eq

theorem gap9 : Real.rpow 2 5 = 32 := by
  norm_num [Real.rpow_natCast]

theorem gap10 : sSup (f '' domain) = 32 := by
  rw [gap8, gap9]

end
end ProofGap.Exercise1445
