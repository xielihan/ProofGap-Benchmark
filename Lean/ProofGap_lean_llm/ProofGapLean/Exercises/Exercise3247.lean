import ProofGapLean.Prelude.Elementary
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

namespace ProofGap.Exercise3247

noncomputable section

def area (R α : ℝ) : ℝ :=
  (1 / 2 : ℝ) * R ^ 2 * α

def areaDifferential (R α dR dα : ℝ) : ℝ :=
  R * α * dR + (1 / 2 : ℝ) * R ^ 2 * dα

def radius : ℝ := 20
def angle : ℝ := Real.pi / 3
def angleChange : ℝ := Real.pi / 180

def PreservesAreaToFirstOrder (dR : ℝ) : Prop :=
  areaDifferential radius angle dR angleChange = 0

def Approx (actual expected tolerance : ℝ) : Prop :=
  |actual - expected| < tolerance

theorem gap1 (dR : ℝ) :
    PreservesAreaToFirstOrder dR ↔
      areaDifferential radius angle dR angleChange = 0 := by
  rfl

theorem gap2 (R α dR dα : ℝ) :
    areaDifferential R α dR dα =
      R * α * dR + (1 / 2 : ℝ) * R ^ 2 * dα := by
  rfl

theorem gap3 (dR : ℝ) :
    PreservesAreaToFirstOrder dR ↔
      radius * angle * dR +
          (1 / 2 : ℝ) * radius ^ 2 * angleChange =
        0 := by
  rfl

theorem gap4 (dR : ℝ) (hR : PreservesAreaToFirstOrder dR) :
    20 * (Real.pi / 3) * dR +
        (1 / 2 : ℝ) * 20 ^ 2 * (Real.pi / 180) =
      0 := by
  simpa [PreservesAreaToFirstOrder, areaDifferential, radius, angle, angleChange] using hR

theorem gap5 (dR : ℝ) (hR : PreservesAreaToFirstOrder dR) :
    dR = -(1 / 6 : ℝ) := by
  have h := gap4 dR hR
  have hpi : 0 < Real.pi := Real.pi_pos
  nlinarith

theorem gap6 :
    Approx (-(1 / 6 : ℝ)) (-0.17) (1 / 100) := by
  norm_num [Approx, abs_of_nonneg]

theorem gap7 (dR : ℝ) (hR : PreservesAreaToFirstOrder dR) :
    Approx dR (-0.17) (1 / 100) := by
  rw [gap5 dR hR]
  exact gap6

end

end ProofGap.Exercise3247
