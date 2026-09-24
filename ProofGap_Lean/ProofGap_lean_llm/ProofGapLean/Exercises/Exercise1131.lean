import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

namespace ProofGap.Exercise1131

noncomputable section

def y (x : ℝ) : ℝ := Real.sqrt (1 + x ^ 2)
def firstForm (x : ℝ) : ℝ := x / Real.sqrt (1 + x ^ 2)
def threeHalves (x : ℝ) : ℝ := Real.rpow x (3 / 2 : ℝ)

def differential (f : ℝ → ℝ) (x dx : ℝ) : ℝ :=
  deriv f x * dx

def secondDifferential (f : ℝ → ℝ) (x dx : ℝ) : ℝ :=
  deriv (fun t => deriv f t) x * dx ^ 2

private theorem hasDerivAtY (x : ℝ) : HasDerivAt y (firstForm x) x := by
  have hpos : 0 < 1 + x ^ 2 := by
    nlinarith [sq_nonneg x]
  have hp : HasDerivAt (fun t : ℝ => t ^ 2) (2 * x) x := by
    simpa [mul_comm] using ((hasDerivAt_id x).pow 2)
  have hinner :
      HasDerivAt (fun t : ℝ => 1 + t ^ 2) (2 * x) x := by
    simpa [add_comm] using hp.add_const 1
  unfold y firstForm
  convert (Real.hasDerivAt_sqrt (ne_of_gt hpos)).comp x hinner using 1 <;>
    field_simp [ne_of_gt (Real.sqrt_pos.2 hpos)] <;> ring

theorem gap1 (x dx : ℝ) :
    differential y x dx = firstForm x * dx := by
  unfold differential
  rw [(hasDerivAtY x).deriv]

theorem gap2 (x : ℝ) :
    deriv (fun t => deriv y t) x = deriv firstForm x := by
  have hfun : (fun t : ℝ => deriv y t) = firstForm := by
    funext t
    exact (hasDerivAtY t).deriv
  rw [hfun]

theorem gap3 (x : ℝ) :
    deriv firstForm x = 1 / threeHalves (1 + x ^ 2) := by
  have hpos : 0 < 1 + x ^ 2 := by
    nlinarith [sq_nonneg x]
  have hsqrt_ne : Real.sqrt (1 + x ^ 2) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hpos)
  have hsquare : Real.sqrt (1 + x ^ 2) ^ 2 = 1 + x ^ 2 :=
    Real.sq_sqrt (le_of_lt hpos)
  have hden :
      HasDerivAt (fun t : ℝ => Real.sqrt (1 + t ^ 2))
        (x / Real.sqrt (1 + x ^ 2)) x := by
    simpa [y, firstForm] using hasDerivAtY x
  have hfirst :
      HasDerivAt firstForm
        ((Real.sqrt (1 + x ^ 2) -
            x * (x / Real.sqrt (1 + x ^ 2))) /
          Real.sqrt (1 + x ^ 2) ^ 2) x := by
    simpa [firstForm] using (hasDerivAt_id x).div hden hsqrt_ne
  have hrpow :
      threeHalves (1 + x ^ 2) =
        (1 + x ^ 2) * Real.sqrt (1 + x ^ 2) := by
    unfold threeHalves
    rw [Real.sqrt_eq_rpow]
    calc
      Real.rpow (1 + x ^ 2) (3 / 2 : ℝ) =
          Real.exp (Real.log (1 + x ^ 2) * (3 / 2 : ℝ)) :=
        Real.rpow_def_of_pos hpos (3 / 2 : ℝ)
      _ = Real.exp (Real.log (1 + x ^ 2)) *
            Real.exp (Real.log (1 + x ^ 2) * (1 / 2 : ℝ)) := by
        rw [← Real.exp_add]
        congr 1
        ring
      _ = (1 + x ^ 2) *
            Real.exp (Real.log (1 + x ^ 2) * (1 / 2 : ℝ)) := by
        rw [Real.exp_log hpos]
      _ = (1 + x ^ 2) * Real.rpow (1 + x ^ 2) (1 / 2 : ℝ) := by
        congr 1
        exact (Real.rpow_def_of_pos hpos (1 / 2 : ℝ)).symm
  rw [hfirst.deriv, hrpow, hsquare]
  field_simp [hsqrt_ne, ne_of_gt hpos] <;> nlinarith [hsquare]

theorem gap4 (x : ℝ) :
    deriv (fun t => deriv y t) x = 1 / threeHalves (1 + x ^ 2) := by
  calc
    deriv (fun t => deriv y t) x = deriv firstForm x := gap2 x
    _ = 1 / threeHalves (1 + x ^ 2) := gap3 x

theorem gap5 (x dx : ℝ) :
    secondDifferential y x dx = dx ^ 2 / threeHalves (1 + x ^ 2) := by
  unfold secondDifferential
  rw [gap4 x]
  simp [div_eq_mul_inv, mul_comm]

end

end ProofGap.Exercise1131
