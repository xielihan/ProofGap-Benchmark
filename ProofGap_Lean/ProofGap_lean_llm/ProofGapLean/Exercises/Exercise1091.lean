import ProofGapLean.Prelude.Core
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1091

noncomputable section

def y (u v w : ℝ → ℝ) (x : ℝ) : ℝ := u x * v x * w x
def differential (f : ℝ → ℝ) (x dx : ℝ) : ℝ := deriv f x * dx

theorem gap1 (u v w : ℝ → ℝ) (x dx du dv dw : ℝ)
    (hu : HasDerivAt u du x) (hv : HasDerivAt v dv x)
    (hw : HasDerivAt w dw x) :
    differential (y u v w) x dx =
      v x * w x * (du * dx) +
        u x * w x * (dv * dx) +
        u x * v x * (dw * dx) := by
  have h : HasDerivAt (y u v w)
      (((du * v x + u x * dv) * w x) + (u x * v x) * dw) x := by
    simpa [y] using (hu.mul hv).mul hw
  rw [differential, h.deriv]
  ring

end

end ProofGap.Exercise1091
