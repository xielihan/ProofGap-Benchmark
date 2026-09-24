import ProofGapLean.Prelude.Core
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

namespace ProofGap.Exercise846

noncomputable section

def y (x : ℝ) : ℝ :=
  (1 + x - x ^ 2) / (1 - x + x ^ 2)

private theorem denominator_pos (x : ℝ) : 0 < 1 - x + x ^ 2 := by
  nlinarith [sq_nonneg (x - (1 / 2 : ℝ))]

theorem gap1 (x : ℝ) :
    y x = 2 / (1 - x + x ^ 2) - 1 := by
  unfold y
  have hden : 1 - x + x ^ 2 ≠ 0 :=
    ne_of_gt (denominator_pos x)
  field_simp [hden]
  ring

theorem gap2 (x : ℝ) :
    HasDerivAt y (2 * (1 - 2 * x) / (1 - x + x ^ 2) ^ 2) x := by
  unfold y
  have hden : 1 - x + x ^ 2 ≠ 0 :=
    ne_of_gt (denominator_pos x)
  have hx2 : HasDerivAt (fun t : ℝ => t * t) (x + x) x := by
    convert (hasDerivAt_id x).mul (hasDerivAt_id x) using 1 <;>
      simp [id] <;> ring
  have hn :
      HasDerivAt (fun t : ℝ => 1 + t - t ^ 2) (1 - 2 * x) x := by
    convert (((hasDerivAt_const (x := x) (c := (1 : ℝ))).add
      (hasDerivAt_id x)).sub hx2) using 1
    · funext t
      dsimp [id]
      ring
    · ring
  have hd :
      HasDerivAt (fun t : ℝ => 1 - t + t ^ 2) (-1 + 2 * x) x := by
    convert (((hasDerivAt_const (x := x) (c := (1 : ℝ))).sub
      (hasDerivAt_id x)).add hx2) using 1
    · funext t
      dsimp [id]
      ring
    · ring
  have hquot :
      HasDerivAt
        (fun t : ℝ => (1 + t - t ^ 2) / (1 - t + t ^ 2))
        (((1 - 2 * x) * (1 - x + x ^ 2) -
            (1 + x - x ^ 2) * (-1 + 2 * x)) /
          (1 - x + x ^ 2) ^ 2)
        x :=
    hn.div hd hden
  convert hquot using 1 <;> ring

end

end ProofGap.Exercise846
