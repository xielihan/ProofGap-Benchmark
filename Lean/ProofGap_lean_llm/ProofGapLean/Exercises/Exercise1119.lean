import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Topology.Neighborhoods

namespace ProofGap.Exercise1119

noncomputable section

def y (x : ℝ) : ℝ :=
  x * (Real.sin (Real.log x) + Real.cos (Real.log x))

def secondDeriv (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  deriv (fun t => deriv f t) x

def expanded (x : ℝ) : ℝ :=
  Real.sin (Real.log x) + Real.cos (Real.log x) +
    x * (1 / x) * (Real.cos (Real.log x) - Real.sin (Real.log x))

theorem gap1 (x : ℝ) (hx : 0 < x) :
    deriv y x = expanded x := by
  unfold y expanded
  have hlog : HasDerivAt Real.log (1 / x) x := by
    simpa [one_div] using Real.hasDerivAt_log hx.ne'
  have hsin :
      HasDerivAt (fun t : ℝ => Real.sin (Real.log t))
        (Real.cos (Real.log x) * (1 / x)) x :=
    (Real.hasDerivAt_sin (Real.log x)).comp x hlog
  have hcos :
      HasDerivAt (fun t : ℝ => Real.cos (Real.log t))
        (-Real.sin (Real.log x) * (1 / x)) x :=
    (Real.hasDerivAt_cos (Real.log x)).comp x hlog
  have hprod :
      HasDerivAt
        (fun t : ℝ => t * (Real.sin (Real.log t) + Real.cos (Real.log t)))
        (Real.sin (Real.log x) + Real.cos (Real.log x) +
          x * (1 / x) * (Real.cos (Real.log x) - Real.sin (Real.log x))) x := by
    convert (hasDerivAt_id x).mul (hsin.add hcos) using 1 <;>
      simp only [id_eq, Pi.add_apply] <;> ring
  exact hprod.deriv

theorem gap2 (x : ℝ) (hx : 0 < x) :
    expanded x = 2 * Real.cos (Real.log x) := by
  unfold expanded
  field_simp [hx.ne'] <;> ring

theorem gap3 (x : ℝ) (hx : 0 < x) :
    deriv y x = 2 * Real.cos (Real.log x) := by
  rw [gap1 x hx, gap2 x hx]

theorem gap4 (x : ℝ) (hx : 0 < x) :
    secondDeriv y x = -(2 * Real.sin (Real.log x) / x) := by
  unfold secondDeriv
  have hlog : HasDerivAt Real.log (1 / x) x := by
    simpa [one_div] using Real.hasDerivAt_log hx.ne'
  have hcoslog :
      HasDerivAt (fun t : ℝ => Real.cos (Real.log t))
        (-Real.sin (Real.log x) * (1 / x)) x :=
    (Real.hasDerivAt_cos (Real.log x)).comp x hlog
  have hscaled :
      HasDerivAt (fun t : ℝ => 2 * Real.cos (Real.log t))
        (2 * (-Real.sin (Real.log x) * (1 / x))) x :=
    hcoslog.const_mul 2
  have hyderiv :
      HasDerivAt (fun t : ℝ => deriv y t)
        (2 * (-Real.sin (Real.log x) * (1 / x))) x := by
    apply hscaled.congr_of_eventuallyEq
    filter_upwards [eventually_gt_nhds hx] with t ht
    exact gap3 t ht
  convert hyderiv.deriv using 1 <;> ring

end

end ProofGap.Exercise1119
