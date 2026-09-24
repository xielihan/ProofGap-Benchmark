import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1093

noncomputable section

def y (u v : ℝ → ℝ) (x : ℝ) : ℝ :=
  1 / Real.sqrt (u x ^ 2 + v x ^ 2)

def threeHalves (x : ℝ) : ℝ := Real.rpow x (3 / 2 : ℝ)
def differential (f : ℝ → ℝ) (x dx : ℝ) : ℝ := deriv f x * dx

theorem gap1 (u v : ℝ → ℝ) (x dx du dv : ℝ)
    (hu : HasDerivAt u du x) (hv : HasDerivAt v dv x)
    (hpos : 0 < u x ^ 2 + v x ^ 2) :
    differential (y u v) x dx =
      -(1 / (2 * threeHalves (u x ^ 2 + v x ^ 2))) *
        (2 * u x * (du * dx) + 2 * v x * (dv * dx)) := by
  set s : ℝ := u x ^ 2 + v x ^ 2
  have hspos : 0 < s := by
    simpa [s] using hpos
  have hu_sq :
      HasDerivAt (fun z => u z ^ 2) (2 * u x * du) x := by
    simpa using hu.pow 2
  have hv_sq :
      HasDerivAt (fun z => v z ^ 2) (2 * v x * dv) x := by
    simpa using hv.pow 2
  have hsum :
      HasDerivAt (fun z => u z ^ 2 + v z ^ 2)
        (2 * u x * du + 2 * v x * dv) x :=
    hu_sq.add hv_sq
  have hroot :
      HasDerivAt (fun z => Real.sqrt (u z ^ 2 + v z ^ 2))
        (1 / (2 * Real.sqrt s) * (2 * u x * du + 2 * v x * dv)) x := by
    simpa [s] using
      (Real.hasDerivAt_sqrt (ne_of_gt hspos)).comp x hsum
  have hrootne : Real.sqrt s ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hspos)
  have hyfun :
      y u v = fun z => (Real.sqrt (u z ^ 2 + v z ^ 2))⁻¹ := by
    funext z
    simp only [y, one_div]
  have hyderiv :
      HasDerivAt (y u v)
        (- (1 / (2 * Real.sqrt s) * (2 * u x * du + 2 * v x * dv)) /
          Real.sqrt s ^ 2) x := by
    rw [hyfun]
    exact hroot.inv hrootne
  have hthree : threeHalves s = Real.sqrt s ^ 3 := by
    unfold threeHalves
    change s ^ (3 / 2 : ℝ) = Real.sqrt s ^ 3
    rw [Real.rpow_def_of_pos hspos]
    rw [Real.sqrt_eq_rpow]
    rw [Real.rpow_def_of_pos hspos]
    have hexp :
        Real.exp (Real.log s * (3 / 2 : ℝ)) =
          Real.exp (Real.log s * (1 / 2 : ℝ)) ^ 3 := by
      calc
        Real.exp (Real.log s * (3 / 2 : ℝ)) =
            Real.exp (3 * (Real.log s * (1 / 2 : ℝ))) := by
          congr 1
          ring
        _ = Real.exp (Real.log s * (1 / 2 : ℝ)) ^ 3 := by
          rw [show (3 : ℝ) * (Real.log s * (1 / 2 : ℝ)) =
              (Real.log s * (1 / 2 : ℝ) + Real.log s * (1 / 2 : ℝ)) +
                Real.log s * (1 / 2 : ℝ) by ring]
          simp only [Real.exp_add]
          ring
    simpa using hexp
  unfold differential
  rw [hyderiv.deriv, hthree]
  field_simp [hrootne] <;> ring

theorem gap2 (u v : ℝ → ℝ) (x dx du dv : ℝ)
    (hpos : 0 < u x ^ 2 + v x ^ 2) :
    -(1 / (2 * threeHalves (u x ^ 2 + v x ^ 2))) *
        (2 * u x * (du * dx) + 2 * v x * (dv * dx)) =
      -(u x * (du * dx) + v x * (dv * dx)) /
        threeHalves (u x ^ 2 + v x ^ 2) := by
  set s : ℝ := u x ^ 2 + v x ^ 2
  have hspos : 0 < s := by
    simpa [s] using hpos
  have htne : threeHalves s ≠ 0 := by
    unfold threeHalves
    exact ne_of_gt (Real.rpow_pos_of_pos hspos _)
  field_simp [htne] <;> ring

theorem gap3 (u v : ℝ → ℝ) (x dx du dv : ℝ)
    (hu : HasDerivAt u du x) (hv : HasDerivAt v dv x)
    (hpos : 0 < u x ^ 2 + v x ^ 2) :
    differential (y u v) x dx =
      -(u x * (du * dx) + v x * (dv * dx)) /
        threeHalves (u x ^ 2 + v x ^ 2) := by
  calc
    differential (y u v) x dx =
        -(1 / (2 * threeHalves (u x ^ 2 + v x ^ 2))) *
          (2 * u x * (du * dx) + 2 * v x * (dv * dx)) :=
      gap1 u v x dx du dv hu hv hpos
    _ = -(u x * (du * dx) + v x * (dv * dx)) /
          threeHalves (u x ^ 2 + v x ^ 2) :=
      gap2 u v x dx du dv hpos

end

end ProofGap.Exercise1093
