import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

namespace ProofGap.Exercise1095

noncomputable section

def y (u v : ℝ → ℝ) (x : ℝ) : ℝ :=
  Real.log (Real.sqrt (u x ^ 2 + v x ^ 2))

def differential (f : ℝ → ℝ) (x dx : ℝ) : ℝ := deriv f x * dx

theorem gap1 (u v : ℝ → ℝ) (x dx du dv : ℝ)
    (hu : HasDerivAt u du x) (hv : HasDerivAt v dv x)
    (hpos : 0 < u x ^ 2 + v x ^ 2) :
    differential (y u v) x dx =
      (2 * u x * (du * dx) + 2 * v x * (dv * dx)) /
        (2 * (u x ^ 2 + v x ^ 2)) := by
  have hinner :
      HasDerivAt (fun z => u z ^ 2 + v z ^ 2)
        (2 * u x * du + 2 * v x * dv) x := by
    convert (hu.pow 2).add (hv.pow 2) using 1 <;> ring
  have hsqrt :
      HasDerivAt (fun z => Real.sqrt (u z ^ 2 + v z ^ 2))
        ((2 * u x * du + 2 * v x * dv) /
          (2 * Real.sqrt (u x ^ 2 + v x ^ 2))) x :=
    hinner.sqrt hpos.ne'
  have hsqrt_pos : 0 < Real.sqrt (u x ^ 2 + v x ^ 2) :=
    Real.sqrt_pos.2 hpos
  have hchain :
      HasDerivAt (y u v)
        ((2 * u x * du + 2 * v x * dv) /
          (2 * (u x ^ 2 + v x ^ 2))) x := by
    simpa [y, div_div, mul_assoc, Real.mul_self_sqrt hpos.le] using
      (hsqrt.log hsqrt_pos.ne')
  unfold differential
  rw [hchain.deriv]
  ring

theorem gap2 (u v : ℝ → ℝ) (x dx du dv : ℝ)
    (hpos : 0 < u x ^ 2 + v x ^ 2) :
    (2 * u x * (du * dx) + 2 * v x * (dv * dx)) /
        (2 * (u x ^ 2 + v x ^ 2)) =
      (u x * (du * dx) + v x * (dv * dx)) /
        (u x ^ 2 + v x ^ 2) := by
  have hne : u x ^ 2 + v x ^ 2 ≠ 0 := hpos.ne'
  field_simp [hne] <;> ring

theorem gap3 (u v : ℝ → ℝ) (x dx du dv : ℝ)
    (hu : HasDerivAt u du x) (hv : HasDerivAt v dv x)
    (hpos : 0 < u x ^ 2 + v x ^ 2) :
    differential (y u v) x dx =
      (u x * (du * dx) + v x * (dv * dx)) /
        (u x ^ 2 + v x ^ 2) := by
  calc
    differential (y u v) x dx =
        (2 * u x * (du * dx) + 2 * v x * (dv * dx)) /
          (2 * (u x ^ 2 + v x ^ 2)) :=
      gap1 u v x dx du dv hu hv hpos
    _ = (u x * (du * dx) + v x * (dv * dx)) /
          (u x ^ 2 + v x ^ 2) :=
      gap2 u v x dx du dv hpos

end

end ProofGap.Exercise1095
