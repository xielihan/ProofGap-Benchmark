import ProofGapLean.Prelude.Core
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1050

theorem gap1 (a b : ℝ) (y : ℝ → ℝ) (ha : a ≠ 0) (hb : b ≠ 0)
    (hcurve : ∀ x, x ^ 2 / a ^ 2 + y x ^ 2 / b ^ 2 = 1)
    (hdiff : Differentiable ℝ y) (x : ℝ) :
    2 * x / a ^ 2 + 2 * y x * deriv y x / b ^ 2 = 0 := by
  have hy' : HasDerivAt y (deriv y x) x := (hdiff x).hasDerivAt
  have hx2 : HasDerivAt (fun t : ℝ => t * t)
      (1 * x + x * 1) x := by
    simpa only [Pi.mul_apply, id_eq] using
      HasDerivAt.mul (hasDerivAt_id x) (hasDerivAt_id x)
  have hy2 : HasDerivAt (fun t : ℝ => y t * y t)
      (deriv y x * y x + y x * deriv y x) x := by
    simpa only [Pi.mul_apply] using
      HasDerivAt.mul hy' hy'
  have hleft :
      HasDerivAt
        (fun t : ℝ => t * t / a ^ 2 + y t * y t / b ^ 2)
        ((1 * x + x * 1) / a ^ 2 +
          (deriv y x * y x + y x * deriv y x) / b ^ 2) x := by
    simpa only [Pi.add_apply] using
      HasDerivAt.add (hx2.div_const (a ^ 2)) (hy2.div_const (b ^ 2))
  have hfunctions :
      (fun t : ℝ => t * t / a ^ 2 + y t * y t / b ^ 2) =
        (fun _ : ℝ => 1) := by
    funext t
    simpa only [pow_two] using hcurve t
  have hraw :
      (1 * x + x * 1) / a ^ 2 +
          (deriv y x * y x + y x * deriv y x) / b ^ 2 = 0 := by
    calc
      (1 * x + x * 1) / a ^ 2 +
          (deriv y x * y x + y x * deriv y x) / b ^ 2 =
          deriv (fun t : ℝ => t * t / a ^ 2 + y t * y t / b ^ 2) x :=
        hleft.deriv.symm
      _ = deriv (fun _ : ℝ => 1) x :=
        congrArg (fun f : ℝ → ℝ => deriv f x) hfunctions
      _ = 0 := by simp
  convert hraw using 1 <;> ring

theorem gap2 (a b : ℝ) (y : ℝ → ℝ) (ha : a ≠ 0) (hb : b ≠ 0)
    (hcurve : ∀ x, x ^ 2 / a ^ 2 + y x ^ 2 / b ^ 2 = 1)
    (hdiff : Differentiable ℝ y) (x : ℝ) (hy : y x ≠ 0) :
    deriv y x = -(b ^ 2 * x / (a ^ 2 * y x)) := by
  have h := gap1 a b y ha hb hcurve hdiff x
  field_simp [ha, hb, hy] at h ⊢
  nlinarith

end ProofGap.Exercise1050
