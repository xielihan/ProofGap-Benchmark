import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1108

noncomputable section

def gravityEstimate (l T : ℝ) : ℝ :=
  4 * Real.pi ^ 2 * l / T ^ 2

def relativeError (value change : ℝ) : ℝ := |change / value|

def lengthDifferential (T dl : ℝ) : ℝ :=
  (4 * Real.pi ^ 2 / T ^ 2) * dl

def periodDifferential (l T dT : ℝ) : ℝ :=
  (-(8 * Real.pi ^ 2 * l) / T ^ 3) * dT

theorem gap1 (l T dg : ℝ) (hl : l ≠ 0) (hT : T ≠ 0) :
    relativeError (gravityEstimate l T) dg =
      |dg / gravityEstimate l T| := by
  rfl

theorem gap2 (l T dl : ℝ) (hl : l ≠ 0) (hT : T ≠ 0) :
    relativeError (gravityEstimate l T) (lengthDifferential T dl) =
      relativeError l dl := by
  unfold relativeError gravityEstimate lengthDifferential
  apply congrArg abs
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  field_simp [hl, hT, hpi] <;> ring

theorem gap3 (l T dl : ℝ) (hl : l ≠ 0) (hT : T ≠ 0) :
    relativeError (gravityEstimate l T) (lengthDifferential T dl) =
      |dl / l| := by
  simpa [relativeError] using gap2 l T dl hl hT

theorem gap4 (l T dl δg δl : ℝ) (hl : l ≠ 0) (hT : T ≠ 0)
    (hδg :
      δg = relativeError (gravityEstimate l T) (lengthDifferential T dl))
    (hδl : δl = relativeError l dl) :
    δg = δl := by
  calc
    δg = relativeError (gravityEstimate l T) (lengthDifferential T dl) := hδg
    _ = relativeError l dl := gap2 l T dl hl hT
    _ = δl := hδl.symm

theorem gap5 (l T dT : ℝ) (hl : l ≠ 0) (hT : T ≠ 0) :
    relativeError (gravityEstimate l T) (periodDifferential l T dT) =
      |((-(8 * Real.pi ^ 2 * l) * T ^ 2) * dT) /
        (T ^ 3 * 4 * Real.pi ^ 2 * l)| := by
  unfold relativeError gravityEstimate periodDifferential
  apply congrArg abs
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  field_simp [hl, hT, hpi] <;> ring

theorem gap6 (l T dT : ℝ) (hl : l ≠ 0) (hT : T ≠ 0) :
    |((-(8 * Real.pi ^ 2 * l) * T ^ 2) * dT) /
        (T ^ 3 * 4 * Real.pi ^ 2 * l)| =
      2 * relativeError T dT := by
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  have hfrac :
      (((-(8 * Real.pi ^ 2 * l) * T ^ 2) * dT) /
          (T ^ 3 * 4 * Real.pi ^ 2 * l)) =
        -2 * (dT / T) := by
    field_simp [hl, hT, hpi] <;> ring
  rw [hfrac]
  simp [relativeError, abs_mul]

theorem gap7 (l T dT : ℝ) (hl : l ≠ 0) (hT : T ≠ 0) :
    relativeError (gravityEstimate l T) (periodDifferential l T dT) =
      2 * relativeError T dT := by
  calc
    relativeError (gravityEstimate l T) (periodDifferential l T dT) =
        |((-(8 * Real.pi ^ 2 * l) * T ^ 2) * dT) /
          (T ^ 3 * 4 * Real.pi ^ 2 * l)| := gap5 l T dT hl hT
    _ = 2 * relativeError T dT := gap6 l T dT hl hT

theorem gap8 (l T dT δg δT : ℝ) (hl : l ≠ 0) (hT : T ≠ 0)
    (hδg :
      δg = relativeError (gravityEstimate l T) (periodDifferential l T dT))
    (hδT : δT = relativeError T dT) :
    δg = 2 * δT := by
  calc
    δg = relativeError (gravityEstimate l T) (periodDifferential l T dT) := hδg
    _ = 2 * relativeError T dT := gap7 l T dT hl hT
    _ = 2 * δT := by rw [hδT]

end

end ProofGap.Exercise1108
