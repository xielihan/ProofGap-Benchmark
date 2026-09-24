import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum

namespace ProofGap.Exercise4259

noncomputable section

def oneForm (p v : ℝ × ℝ) : ℝ :=
  p.1 * v.1 + p.2 * v.2

def potential (p : ℝ × ℝ) : ℝ :=
  (p.1 ^ 2 + p.2 ^ 2) / 2

def potentialDifferential (p v : ℝ × ℝ) : ℝ :=
  p.1 * v.1 + p.2 * v.2

def lineIntegral (start finish : ℝ × ℝ) : ℝ :=
  potential finish - potential start

theorem gap1 (p v : ℝ × ℝ) :
    oneForm p v = potentialDifferential p v := by
  rfl

theorem gap2 :
    lineIntegral (0, 1) (3, -1) =
      potential (3, -1) - potential (0, 1) := by
  rfl

theorem gap3 :
    potential (3, -1) - potential (0, 1) =
      ((3 : ℝ) ^ 2 + (-1 : ℝ) ^ 2) / 2 -
        ((0 : ℝ) ^ 2 + (1 : ℝ) ^ 2) / 2 := by
  rfl

theorem gap4 :
    ((3 : ℝ) ^ 2 + (-1 : ℝ) ^ 2) / 2 -
        ((0 : ℝ) ^ 2 + (1 : ℝ) ^ 2) / 2 =
      9 / 2 := by
  norm_num

theorem gap5 :
    lineIntegral (0, 1) (3, -1) = 9 / 2 := by
  calc
    lineIntegral (0, 1) (3, -1) = potential (3, -1) - potential (0, 1) := gap2
    _ = ((3 : ℝ) ^ 2 + (-1 : ℝ) ^ 2) / 2 - ((0 : ℝ) ^ 2 + (1 : ℝ) ^ 2) / 2 := gap3
    _ = 9 / 2 := gap4

end

end ProofGap.Exercise4259
