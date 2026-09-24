import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise881

noncomputable section

def pow3 (x : ℝ) : ℝ := Real.rpow 3 x
def y (x : ℝ) : ℝ :=
  (Real.log 3 * Real.sin x + Real.cos x) / pow3 x

def expandedDerivative (x : ℝ) : ℝ :=
  (pow3 x * (Real.log 3 * Real.cos x - Real.sin x) -
      pow3 x * Real.log 3 *
        (Real.log 3 * Real.sin x + Real.cos x)) /
    Real.rpow 3 (2 * x)

def finalDerivative (x : ℝ) : ℝ :=
  -((1 + Real.log 3 ^ 2) * Real.sin x) / pow3 x

private theorem pow3_pos (x : ℝ) : 0 < pow3 x := by
  have h3 : (0 : ℝ) < 3 := by norm_num
  unfold pow3
  change 0 < (3 : ℝ) ^ x
  rw [Real.rpow_def_of_pos h3]
  exact Real.exp_pos _

private theorem pow3_sq (x : ℝ) :
    pow3 x ^ 2 = Real.rpow 3 (2 * x) := by
  have h3 : (0 : ℝ) < 3 := by norm_num
  unfold pow3
  change ((3 : ℝ) ^ x) ^ (2 : ℕ) = (3 : ℝ) ^ (2 * x)
  simp only [Real.rpow_def_of_pos h3]
  rw [pow_two, ← Real.exp_add]
  congr 1
  ring

theorem gap1 (x : ℝ) : deriv y x = expandedDerivative x := by
  have hn :
      HasDerivAt
        (fun t : ℝ => Real.log 3 * Real.sin t + Real.cos t)
        (Real.log 3 * Real.cos x - Real.sin x) x := by
    simpa [sub_eq_add_neg] using
      ((Real.hasDerivAt_sin x).const_mul (Real.log 3)).add
        (Real.hasDerivAt_cos x)
  have hlin :
      HasDerivAt (fun t : ℝ => Real.log 3 * t) (Real.log 3) x := by
    simpa using (hasDerivAt_id x).const_mul (Real.log 3)
  have hp : HasDerivAt pow3 (pow3 x * Real.log 3) x := by
    have h3 : (0 : ℝ) < 3 := by norm_num
    unfold pow3
    change
      HasDerivAt (fun t : ℝ => (3 : ℝ) ^ t)
        ((3 : ℝ) ^ x * Real.log 3) x
    simpa only [Real.rpow_def_of_pos h3, Function.comp_apply] using
      (Real.hasDerivAt_exp (Real.log 3 * x)).comp x hlin
  have hp0 : pow3 x ≠ 0 := ne_of_gt (pow3_pos x)
  have hd :
      deriv y x =
        ((Real.log 3 * Real.cos x - Real.sin x) * pow3 x -
            (Real.log 3 * Real.sin x + Real.cos x) *
              (pow3 x * Real.log 3)) /
          pow3 x ^ 2 := by
    simpa only [y] using (hn.div hp hp0).deriv
  calc
    deriv y x =
        ((Real.log 3 * Real.cos x - Real.sin x) * pow3 x -
            (Real.log 3 * Real.sin x + Real.cos x) *
              (pow3 x * Real.log 3)) /
          pow3 x ^ 2 := hd
    _ =
        (pow3 x * (Real.log 3 * Real.cos x - Real.sin x) -
            pow3 x * Real.log 3 *
              (Real.log 3 * Real.sin x + Real.cos x)) /
          pow3 x ^ 2 := by
      congr 1 <;> ring
    _ = expandedDerivative x := by
      rw [expandedDerivative, pow3_sq x]
theorem gap2 (x : ℝ) : expandedDerivative x = finalDerivative x := by
  have hp0 : pow3 x ≠ 0 := ne_of_gt (pow3_pos x)
  unfold expandedDerivative finalDerivative
  rw [← pow3_sq x]
  field_simp [hp0]
  ring
theorem gap3 (x : ℝ) : deriv y x = finalDerivative x := by
  calc
    deriv y x = expandedDerivative x := gap1 x
    _ = finalDerivative x := gap2 x

end

end ProofGap.Exercise881
