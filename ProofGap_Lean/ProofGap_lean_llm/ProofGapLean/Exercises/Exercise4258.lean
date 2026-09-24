import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum

namespace ProofGap.Exercise4258

noncomputable section

def oneForm (p v : ℝ × ℝ) : ℝ :=
  p.1 * v.2 + p.2 * v.1

def potential (p : ℝ × ℝ) : ℝ :=
  p.1 * p.2

def potentialDifferential (p v : ℝ × ℝ) : ℝ :=
  p.2 * v.1 + p.1 * v.2

def lineIntegral (start finish : ℝ × ℝ) : ℝ :=
  potential finish - potential start

theorem gap1 (p v : ℝ × ℝ) :
    oneForm p v = potentialDifferential p v := by
  simp [oneForm, potentialDifferential, add_comm]

theorem gap2 :
    lineIntegral (-1, 2) (2, 3) =
      potential (2, 3) - potential (-1, 2) := by
  rfl

theorem gap3 :
    potential (2, 3) - potential (-1, 2) =
      (2 : ℝ) * 3 - (-1 : ℝ) * 2 := by
  norm_num [potential]

theorem gap4 :
    (2 : ℝ) * 3 - (-1 : ℝ) * 2 = 8 := by
  norm_num

theorem gap5 :
    lineIntegral (-1, 2) (2, 3) = 8 := by
  norm_num [lineIntegral, potential]

end

end ProofGap.Exercise4258
