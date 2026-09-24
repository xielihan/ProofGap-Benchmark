import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

namespace ProofGap.Exercise1104_1

noncomputable section

def Approx (x y ε : ℝ) : Prop := |x - y| < ε

theorem gap1 (y₀ : ℝ) (hy : 0 < y₀) :
    HasDerivAt Real.sqrt (1 / (2 * Real.sqrt y₀)) y₀ := by
  exact Real.hasDerivAt_sqrt (ne_of_gt hy)

theorem gap2 (a : ℝ) (ha : 0 < a) :
    HasDerivAt (fun x : ℝ => Real.sqrt (a ^ 2 + x))
      (1 / (2 * a)) 0 := by
  have hinner :
      HasDerivAt (fun x : ℝ => a ^ 2 + x) 1 0 := by
    simpa only [id_eq] using
      ((hasDerivAt_id (0 : ℝ)).const_add (a ^ 2))
  have houter :
      HasDerivAt Real.sqrt (1 / (2 * Real.sqrt (a ^ 2)))
        ((fun x : ℝ => a ^ 2 + x) 0) := by
    simpa using gap1 (a ^ 2) (pow_pos ha 2)
  simpa [Function.comp_def, Real.sqrt_sq_eq_abs, abs_of_pos ha] using
    (houter.comp 0 hinner)

theorem gap3 :
    Real.sqrt 5 = Real.sqrt (2 ^ 2 + 1) := by
  norm_num

theorem gap4 :
    Approx (Real.sqrt (2 ^ 2 + 1)) (2 + (1 / 4 : ℝ))
      (2 / 100 : ℝ) := by
  rw [← gap3]
  unfold Approx
  have hs : (Real.sqrt 5) ^ 2 = (5 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  have hn : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
  rw [abs_lt]
  constructor <;> nlinarith

theorem gap5 :
    (2 + (1 / 4 : ℝ)) = (225 / 100 : ℝ) := by
  norm_num

theorem gap6 :
    Approx (Real.sqrt 5) (225 / 100 : ℝ) (2 / 100 : ℝ) := by
  rw [gap3, ← gap5]
  exact gap4

theorem gap7 :
    Approx (Real.sqrt 5) (224 / 100 : ℝ) (5 / 1000 : ℝ) := by
  unfold Approx
  have hs : (Real.sqrt 5) ^ 2 = (5 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  have hn : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
  rw [abs_lt]
  constructor <;> nlinarith

end

end ProofGap.Exercise1104_1
