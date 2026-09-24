import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise894

noncomputable section

def y (x : ℝ) : ℝ :=
  Real.sqrt (x + 1) - Real.log (1 + Real.sqrt (x + 1))

def expandedDerivative (x : ℝ) : ℝ :=
  1 / (2 * Real.sqrt (x + 1)) -
    1 / (2 * Real.sqrt (x + 1) * (1 + Real.sqrt (x + 1)))

def finalDerivative (x : ℝ) : ℝ :=
  1 / (2 * (1 + Real.sqrt (x + 1)))

theorem gap1 (x : ℝ) (hx : -1 < x) :
    deriv y x = expandedDerivative x := by
  have ht : 0 < x + 1 := by
    linarith
  have hspos : 0 < Real.sqrt (x + 1) := Real.sqrt_pos.2 ht
  have hargpos : 0 < 1 + Real.sqrt (x + 1) := by
    linarith
  have hshift : HasDerivAt (fun z : ℝ => z + 1) 1 x := by
    simpa only [id_eq] using
      (HasDerivAt.add_const (1 : ℝ) (hasDerivAt_id x))
  have hsqrt :
      HasDerivAt (fun z : ℝ => Real.sqrt (z + 1))
        (1 / (2 * Real.sqrt (x + 1))) x := by
    simpa [one_div] using
      (HasDerivAt.comp x (Real.hasDerivAt_sqrt (ne_of_gt ht)) hshift)
  have hinner :
      HasDerivAt (fun z : ℝ => 1 + Real.sqrt (z + 1))
        (1 / (2 * Real.sqrt (x + 1))) x := by
    simpa only [Pi.add_apply, zero_add] using
      (HasDerivAt.add (hasDerivAt_const x (1 : ℝ)) hsqrt)
  have hlog :
      HasDerivAt (fun z : ℝ => Real.log (1 + Real.sqrt (z + 1)))
        (1 / (2 * Real.sqrt (x + 1) * (1 + Real.sqrt (x + 1)))) x := by
    convert
      HasDerivAt.comp x (Real.hasDerivAt_log (ne_of_gt hargpos)) hinner using 1 <;>
      field_simp [ne_of_gt hspos, ne_of_gt hargpos] <;>
      ring
  have hdiff : HasDerivAt y (expandedDerivative x) x := by
    simpa only [y, expandedDerivative] using
      (HasDerivAt.sub hsqrt hlog)
  exact hdiff.deriv

theorem gap2 (x : ℝ) (hx : -1 < x) :
    expandedDerivative x = finalDerivative x := by
  have ht : 0 < x + 1 := by
    linarith
  have hspos : 0 < Real.sqrt (x + 1) := Real.sqrt_pos.2 ht
  have hargpos : 0 < 1 + Real.sqrt (x + 1) := by
    linarith
  unfold expandedDerivative finalDerivative
  field_simp [ne_of_gt hspos, ne_of_gt hargpos]
  ring

theorem gap3 (x : ℝ) (hx : -1 < x) :
    deriv y x = finalDerivative x := by
  exact (gap1 x hx).trans (gap2 x hx)

end

end ProofGap.Exercise894
