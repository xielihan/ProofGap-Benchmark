import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Topology.Neighborhoods

namespace ProofGap.Exercise1117

noncomputable section

def y (x : ℝ) : ℝ := x * Real.log x

def secondDeriv (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  deriv (fun t => deriv f t) x

theorem gap1 (x : ℝ) (hx : 0 < x) :
    deriv y x = 1 + Real.log x := by
  have h : HasDerivAt y (Real.log x + 1) x := by
    change HasDerivAt (fun t : ℝ => t * Real.log t) (Real.log x + 1) x
    convert (hasDerivAt_id x).mul (Real.hasDerivAt_log hx.ne') using 1 <;>
      simp [hx.ne']
  calc
    deriv y x = Real.log x + 1 := h.deriv
    _ = 1 + Real.log x := add_comm _ _

theorem gap2 (x : ℝ) (hx : 0 < x) :
    secondDeriv y x = 1 / x := by
  unfold secondDeriv
  have hlog : HasDerivAt (fun t : ℝ => 1 + Real.log t) (1 / x) x := by
    simpa [one_div] using (Real.hasDerivAt_log hx.ne').const_add 1
  have heq :
      (fun t : ℝ => deriv y t) =ᶠ[nhds x] (fun t : ℝ => 1 + Real.log t) := by
    filter_upwards [isOpen_Ioi.mem_nhds hx] with t ht
    exact gap1 t ht
  exact (hlog.congr_of_eventuallyEq heq).deriv

end

end ProofGap.Exercise1117
