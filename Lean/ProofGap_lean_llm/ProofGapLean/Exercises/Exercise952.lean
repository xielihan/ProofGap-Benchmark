import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise952

noncomputable section

def y (x : ℝ) : ℝ := Real.arctan (x + Real.sqrt (1 + x ^ 2))

def expandedDerivative (x : ℝ) : ℝ :=
  1 / (1 + (x + Real.sqrt (1 + x ^ 2)) ^ 2) *
    (1 + x / Real.sqrt (1 + x ^ 2))

def finalDerivative (x : ℝ) : ℝ := 1 / (2 * (1 + x ^ 2))

theorem gap1 (x : ℝ) : HasDerivAt y (expandedDerivative x) x := by
  have hpos : 0 < 1 + x ^ 2 := by
    positivity
  have hspos : 0 < Real.sqrt (1 + x ^ 2) := Real.sqrt_pos.2 hpos
  have hpow : HasDerivAt (fun z : ℝ => z ^ 2) (x * 2) x := by
    simpa [id_eq, mul_comm] using (hasDerivAt_id x).pow 2
  have hconst : HasDerivAt (fun _ : ℝ => (1 : ℝ)) 0 x :=
    hasDerivAt_const x 1
  have hbase0 :
      HasDerivAt
        ((fun _ : ℝ => (1 : ℝ)) + (fun z : ℝ => z ^ 2))
        (0 + x * 2) x :=
    hconst.add hpow
  have hbase :
      HasDerivAt (fun z : ℝ => 1 + z ^ 2) (x * 2) x := by
    simpa only [Pi.add_apply, zero_add] using hbase0
  have hsqrt0 :
      HasDerivAt (fun z : ℝ => Real.sqrt (1 + z ^ 2))
        ((1 / (2 * Real.sqrt (1 + x ^ 2))) * (x * 2)) x :=
    (Real.hasDerivAt_sqrt hpos.ne').comp x hbase
  have hcoef :
      (1 / (2 * Real.sqrt (1 + x ^ 2))) * (x * 2) =
        x / Real.sqrt (1 + x ^ 2) := by
    field_simp [hspos.ne'] <;> ring
  have hsqrt :
      HasDerivAt (fun z : ℝ => Real.sqrt (1 + z ^ 2))
        (x / Real.sqrt (1 + x ^ 2)) x := by
    simpa only [hcoef] using hsqrt0
  have hinner0 := (hasDerivAt_id x).add hsqrt
  have hinner :
      HasDerivAt
        (fun z : ℝ => z + Real.sqrt (1 + z ^ 2))
        (1 + x / Real.sqrt (1 + x ^ 2)) x := by
    simpa only [Pi.add_apply, id_eq] using hinner0
  simpa only [y, expandedDerivative] using
    (Real.hasDerivAt_arctan (x + Real.sqrt (1 + x ^ 2))).comp x hinner

theorem gap2 (x : ℝ) : expandedDerivative x = finalDerivative x := by
  unfold expandedDerivative finalDerivative
  have hpos : 0 < 1 + x ^ 2 := by
    positivity
  have hspos : 0 < Real.sqrt (1 + x ^ 2) := Real.sqrt_pos.2 hpos
  have houterpos :
      0 < 1 + (x + Real.sqrt (1 + x ^ 2)) ^ 2 := by
    positivity
  have hsq :
      Real.sqrt (1 + x ^ 2) ^ 2 = 1 + x ^ 2 :=
    Real.sq_sqrt hpos.le
  have hxmul := congrArg (fun t : ℝ => x * t) hsq
  have hsmul :=
    congrArg (fun t : ℝ => Real.sqrt (1 + x ^ 2) * t) hsq
  field_simp [hspos.ne', hpos.ne', houterpos.ne']
  nlinarith [hxmul, hsmul]

theorem gap3 (x : ℝ) : HasDerivAt y (finalDerivative x) x := by
  simpa only [gap2] using gap1 x

end

end ProofGap.Exercise952
