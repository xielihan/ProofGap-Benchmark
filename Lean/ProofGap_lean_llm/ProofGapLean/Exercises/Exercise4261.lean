import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum

namespace ProofGap.Exercise4261

noncomputable section

def oneForm (p v : ℝ × ℝ) : ℝ :=
  (p.1 - p.2) * (v.1 - v.2)

def potential (p : ℝ × ℝ) : ℝ :=
  (p.1 - p.2) ^ 2 / 2

def potentialDifferential (p v : ℝ × ℝ) : ℝ :=
  (p.1 - p.2) * (v.1 - v.2)

def lineIntegral (start finish : ℝ × ℝ) : ℝ :=
  potential finish - potential start

theorem gap1 (p v : ℝ × ℝ) :
    oneForm p v = potentialDifferential p v := by
  rfl

theorem gap2 :
    lineIntegral (1, -1) (1, 1) =
      potential (1, 1) - potential (1, -1) := by
  rfl

theorem gap3 :
    potential (1, 1) - potential (1, -1) =
      ((1 : ℝ) - 1) ^ 2 / 2 - ((1 : ℝ) - (-1)) ^ 2 / 2 := by
  rfl

theorem gap4 :
    ((1 : ℝ) - 1) ^ 2 / 2 - ((1 : ℝ) - (-1)) ^ 2 / 2 = -2 := by
  norm_num

theorem gap5 :
    lineIntegral (1, -1) (1, 1) = -2 := by
  rw [gap2, gap3, gap4]

end

end ProofGap.Exercise4261
