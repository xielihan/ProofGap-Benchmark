import ProofGapLean.Prelude.Core
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

namespace ProofGap.Exercise3280_1

noncomputable section

def partialX (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => f t y) x

def partialY (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => f x t) y

def radialOperator (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  x * partialX f x y + y * partialY f x y

def u (x y : ℝ) : ℝ :=
  x / (x ^ 2 + y ^ 2)

private theorem hasDerivAt_sq_add_const (x c : ℝ) :
    HasDerivAt (fun t : ℝ => t ^ 2 + c) (2 * x) x := by
  convert ((hasDerivAt_id x).mul (hasDerivAt_id x)).add_const c using 1
  · funext t
    simp [pow_two]
  · simp [id, two_mul]

theorem gap1 (x y : ℝ) (hr : x ^ 2 + y ^ 2 ≠ 0) :
    partialX u x y =
      (y ^ 2 - x ^ 2) / (x ^ 2 + y ^ 2) ^ 2 := by
  unfold partialX u
  have hd := hasDerivAt_sq_add_const x (y ^ 2)
  have hq := (hasDerivAt_id x).div hd hr
  calc
    deriv (fun t : ℝ => t / (t ^ 2 + y ^ 2)) x =
        ((x ^ 2 + y ^ 2) - x * (2 * x)) /
          (x ^ 2 + y ^ 2) ^ 2 := by
      simpa using hq.deriv
    _ = (y ^ 2 - x ^ 2) / (x ^ 2 + y ^ 2) ^ 2 := by
      field_simp [hr]
      ring

theorem gap2 (x y : ℝ) (hr : x ^ 2 + y ^ 2 ≠ 0) :
    partialY u x y =
      -(2 * x * y) / (x ^ 2 + y ^ 2) ^ 2 := by
  unfold partialY u
  have hd : HasDerivAt (fun t : ℝ => x ^ 2 + t ^ 2) (2 * y) y := by
    simpa [add_comm] using hasDerivAt_sq_add_const y (x ^ 2)
  have hq := (hasDerivAt_const y x).div hd hr
  calc
    deriv (fun t : ℝ => x / (x ^ 2 + t ^ 2)) y =
        (0 * (x ^ 2 + y ^ 2) - x * (2 * y)) /
          (x ^ 2 + y ^ 2) ^ 2 := by
      simpa using hq.deriv
    _ = -(2 * x * y) / (x ^ 2 + y ^ 2) ^ 2 := by
      ring

theorem gap3 (x y : ℝ) (hr : x ^ 2 + y ^ 2 ≠ 0) :
    radialOperator u x y =
      x * (y ^ 2 - x ^ 2) / (x ^ 2 + y ^ 2) ^ 2 -
        2 * x * y ^ 2 / (x ^ 2 + y ^ 2) ^ 2 := by
  unfold radialOperator
  rw [gap1 x y hr, gap2 x y hr]
  ring

theorem gap4 (x y : ℝ) (hr : x ^ 2 + y ^ 2 ≠ 0) :
    x * (y ^ 2 - x ^ 2) / (x ^ 2 + y ^ 2) ^ 2 -
          2 * x * y ^ 2 / (x ^ 2 + y ^ 2) ^ 2 =
      -(x / (x ^ 2 + y ^ 2)) := by
  field_simp [hr]
  ring

theorem gap5 (x y : ℝ) (hr : x ^ 2 + y ^ 2 ≠ 0) :
    -(x / (x ^ 2 + y ^ 2)) = -u x y := by
  rfl

theorem gap6 (x y : ℝ) (hr : x ^ 2 + y ^ 2 ≠ 0) :
    radialOperator u x y = -u x y := by
  calc
    radialOperator u x y =
        x * (y ^ 2 - x ^ 2) / (x ^ 2 + y ^ 2) ^ 2 -
          2 * x * y ^ 2 / (x ^ 2 + y ^ 2) ^ 2 := gap3 x y hr
    _ = -(x / (x ^ 2 + y ^ 2)) := gap4 x y hr
    _ = -u x y := gap5 x y hr

theorem gap7 (x y : ℝ) (hr : x ^ 2 + y ^ 2 ≠ 0) :
    radialOperator (fun a b => radialOperator u a b) x y =
      radialOperator (fun a b => -u a b) x y := by
  apply congrArg (fun f : ℝ → ℝ → ℝ => radialOperator f x y)
  funext a b
  by_cases hab : a ^ 2 + b ^ 2 = 0
  · have ha : a = 0 := by
      nlinarith [sq_nonneg a, sq_nonneg b]
    have hb : b = 0 := by
      nlinarith [sq_nonneg a, sq_nonneg b]
    simp [ha, hb, radialOperator, u]
  · exact gap6 a b hab

theorem gap8 (x y : ℝ) (hr : x ^ 2 + y ^ 2 ≠ 0) :
    radialOperator (fun a b => -u a b) x y =
      -radialOperator u x y := by
  have hdX := hasDerivAt_sq_add_const x (y ^ 2)
  have hdY : HasDerivAt (fun t : ℝ => x ^ 2 + t ^ 2) (2 * y) y := by
    simpa [add_comm] using hasDerivAt_sq_add_const y (x ^ 2)
  have hux : DifferentiableAt ℝ (fun t : ℝ => u t y) x := by
    unfold u
    exact ((hasDerivAt_id x).div hdX hr).differentiableAt
  have huy : DifferentiableAt ℝ (fun t : ℝ => u x t) y := by
    unfold u
    exact ((hasDerivAt_const y x).div hdY hr).differentiableAt
  have hnx : deriv (fun t : ℝ => -u t y) x = -deriv (fun t : ℝ => u t y) x :=
    hux.hasDerivAt.neg.deriv
  have hny : deriv (fun t : ℝ => -u x t) y = -deriv (fun t : ℝ => u x t) y :=
    huy.hasDerivAt.neg.deriv
  unfold radialOperator partialX partialY
  rw [hnx, hny]
  ring

theorem gap9 (x y : ℝ) (hr : x ^ 2 + y ^ 2 ≠ 0) :
    -radialOperator u x y = u x y := by
  rw [gap6 x y hr]
  ring

theorem gap10 (x y : ℝ) (hr : x ^ 2 + y ^ 2 ≠ 0) :
    radialOperator (fun a b => radialOperator u a b) x y =
      u x y := by
  calc
    radialOperator (fun a b => radialOperator u a b) x y =
        radialOperator (fun a b => -u a b) x y := gap7 x y hr
    _ = -radialOperator u x y := gap8 x y hr
    _ = u x y := gap9 x y hr

end

end ProofGap.Exercise3280_1
