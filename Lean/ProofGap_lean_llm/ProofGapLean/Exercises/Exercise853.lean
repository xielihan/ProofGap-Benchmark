import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt

namespace ProofGap.Exercise853

noncomputable section

def signedCbrt (x : ℝ) : ℝ :=
  Real.sign x * Real.rpow |x| (1 / 3 : ℝ)

def y (x : ℝ) : ℝ :=
  signedCbrt (x ^ 2) - 2 / Real.sqrt x

/-- Source: `proof_gap/exercise_853/1.txt`; use a signed real cube root and
restore the omitted domain `x > 0`. -/
theorem gap1 (x : ℝ) (hx : 0 < x) :
    HasDerivAt y
      (2 / (3 * signedCbrt x) + 1 / (x * Real.sqrt x)) x := by
  have heq :
      (fun z : ℝ => signedCbrt (z ^ 2)) =ᶠ[nhds x]
        (fun z : ℝ => Real.rpow z (2 / 3 : ℝ)) := by
    filter_upwards [Ioi_mem_nhds hx] with z hz
    have hz2 : 0 < z ^ 2 := sq_pos_of_pos hz
    rw [signedCbrt]
    rw [Real.sign_of_pos hz2, one_mul, abs_of_pos hz2]
    have hmul :
        Real.rpow z ((2 : ℝ) * (1 / 3 : ℝ)) =
          Real.rpow (z ^ 2) (1 / 3 : ℝ) :=
      Real.rpow_natCast_mul hz.le 2 (1 / 3 : ℝ)
    calc
      Real.rpow (z ^ 2) (1 / 3 : ℝ) =
          Real.rpow z ((2 : ℝ) * (1 / 3 : ℝ)) := hmul.symm
      _ = Real.rpow z (2 / 3 : ℝ) := by congr 1 <;> ring
  have hpow :
      HasDerivAt (fun z : ℝ => Real.rpow z (2 / 3 : ℝ))
        ((2 / 3 : ℝ) * Real.rpow x ((2 / 3 : ℝ) - 1)) x :=
    Real.hasDerivAt_rpow_const (Or.inl hx.ne')
  have hfirstRaw :
      HasDerivAt (fun z : ℝ => signedCbrt (z ^ 2))
        ((2 / 3 : ℝ) * Real.rpow x ((2 / 3 : ℝ) - 1)) x :=
    hpow.congr_of_eventuallyEq heq
  have hcbrt : signedCbrt x = Real.rpow x (1 / 3 : ℝ) := by
    simp [signedCbrt, Real.sign_of_pos hx, abs_of_pos hx]
  have hcbrt_ne : Real.rpow x (1 / 3 : ℝ) ≠ 0 :=
    (Real.rpow_pos_of_pos hx _).ne'
  have hfirst :
      HasDerivAt (fun z : ℝ => signedCbrt (z ^ 2))
        (2 / (3 * signedCbrt x)) x := by
    convert hfirstRaw using 1
    rw [hcbrt, show (2 / 3 : ℝ) - 1 = -(1 / 3 : ℝ) by ring]
    have hneg :
        Real.rpow x (-(1 / 3 : ℝ)) =
          (Real.rpow x (1 / 3 : ℝ))⁻¹ :=
      Real.rpow_neg hx.le (1 / 3 : ℝ)
    rw [hneg]
    field_simp [hcbrt_ne]
    <;> ring
  have hsqrt_ne : Real.sqrt x ≠ 0 := (Real.sqrt_pos.2 hx).ne'
  have hquot :
      HasDerivAt (fun z : ℝ => 2 / Real.sqrt z)
        (-(1 / (x * Real.sqrt x))) x := by
    convert
      (hasDerivAt_const x (2 : ℝ)).div (Real.hasDerivAt_sqrt hx.ne') hsqrt_ne
      using 1
    rw [Real.sq_sqrt hx.le]
    field_simp [hsqrt_ne, hx.ne']
    <;> ring
  unfold y
  convert hfirst.sub hquot using 1 <;> ring

end

end ProofGap.Exercise853
