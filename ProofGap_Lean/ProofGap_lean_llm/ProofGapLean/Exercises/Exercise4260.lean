import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

namespace ProofGap.Exercise4260

noncomputable section

def oneForm (p v : ℝ × ℝ) : ℝ :=
  (p.1 + p.2) * v.1 + (p.1 - p.2) * v.2

def expandedForm (p v : ℝ × ℝ) : ℝ :=
  p.2 * v.1 + p.1 * v.2 + p.1 * v.1 - p.2 * v.2

def potential (p : ℝ × ℝ) : ℝ :=
  p.1 * p.2 + (p.1 ^ 2 - p.2 ^ 2) / 2

def potentialDifferential (p v : ℝ × ℝ) : ℝ :=
  p.2 * v.1 + p.1 * v.2 + p.1 * v.1 - p.2 * v.2

def lineIntegral (start finish : ℝ × ℝ) : ℝ :=
  potential finish - potential start

theorem gap1 (p v : ℝ × ℝ) :
    oneForm p v = expandedForm p v := by
  unfold oneForm expandedForm
  ring

theorem gap2 (p v : ℝ × ℝ) :
    oneForm p v = potentialDifferential p v := by
  unfold oneForm potentialDifferential
  ring

theorem gap3 (p v : ℝ × ℝ) :
    oneForm p v =
      p.2 * v.1 + p.1 * v.2 + p.1 * v.1 - p.2 * v.2 := by
  unfold oneForm
  ring

theorem gap4 :
    lineIntegral (0, 1) (2, 3) =
      potential (2, 3) - potential (0, 1) := by
  rfl

theorem gap5 :
    lineIntegral (0, 1) (2, 3) =
      ((2 : ℝ) * 3 + ((2 : ℝ) ^ 2 - (3 : ℝ) ^ 2) / 2) -
        ((0 : ℝ) * 1 + ((0 : ℝ) ^ 2 - (1 : ℝ) ^ 2) / 2) := by
  rfl

theorem gap6 :
    lineIntegral (0, 1) (2, 3) = 4 := by
  norm_num [lineIntegral, potential]

end

end ProofGap.Exercise4260
