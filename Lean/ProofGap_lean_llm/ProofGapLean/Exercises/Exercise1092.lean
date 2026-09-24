import ProofGapLean.Prelude.Core
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow

namespace ProofGap.Exercise1092

noncomputable section

def y (u v : ℝ → ℝ) (x : ℝ) : ℝ := u x / v x ^ 2
def differential (f : ℝ → ℝ) (x dx : ℝ) : ℝ := deriv f x * dx

theorem gap1 (u v : ℝ → ℝ) (x dx du dv : ℝ)
    (hu : HasDerivAt u du x) (hv : HasDerivAt v dv x)
    (hvn : v x ≠ 0) :
    differential (y u v) x dx =
      (v x ^ 2 * (du * dx) -
        2 * u x * v x * (dv * dx)) / v x ^ 4 := by
  have hvpow :
      HasDerivAt (fun z => v z ^ 2) (2 * v x * dv) x := by
    convert hv.pow 2 using 1 <;> (try simp only [Pi.pow_apply]) <;> ring
  have hy :
      HasDerivAt (y u v)
        ((du * v x ^ 2 - u x * (2 * v x * dv)) /
          (v x ^ 2) ^ 2) x := by
    unfold y
    convert HasDerivAt.div hu hvpow (pow_ne_zero 2 hvn) using 1 <;> ring
  unfold differential
  rw [hy.deriv]
  field_simp [hvn]
  <;> ring

theorem gap2 (u v : ℝ → ℝ) (x dx du dv : ℝ) (hvn : v x ≠ 0) :
    (v x ^ 2 * (du * dx) -
        2 * u x * v x * (dv * dx)) / v x ^ 4 =
      (v x * (du * dx) - 2 * u x * (dv * dx)) / v x ^ 3 := by
  field_simp [hvn]
  <;> ring

theorem gap3 (u v : ℝ → ℝ) (x dx du dv : ℝ)
    (hu : HasDerivAt u du x) (hv : HasDerivAt v dv x)
    (hvn : v x ≠ 0) :
    differential (y u v) x dx =
      (v x * (du * dx) - 2 * u x * (dv * dx)) / v x ^ 3 := by
  rw [gap1 u v x dx du dv hu hv hvn, gap2 u v x dx du dv hvn]

end

end ProofGap.Exercise1092
