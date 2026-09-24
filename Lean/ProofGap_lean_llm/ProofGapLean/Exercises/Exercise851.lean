import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise851

noncomputable section

def signedCbrt (x : ℝ) : ℝ :=
  Real.sign x * Real.rpow |x| (1 / 3 : ℝ)

def y (x : ℝ) : ℝ :=
  x + Real.sqrt x + signedCbrt x

/-- Source: `proof_gap/exercise_851/1.txt`; use a signed real cube root and
restore the omitted domain `x > 0`. -/
theorem gap1 (x : ℝ) (hx : 0 < x) :
    HasDerivAt y
      (1 + 1 / (2 * Real.sqrt x) +
        1 / (3 * signedCbrt (x ^ 2))) x := by
  have hsc_event :
      signedCbrt =ᶠ[nhds x]
        (fun z : ℝ => Real.rpow z (1 / 3 : ℝ)) := by
    filter_upwards [Ioi_mem_nhds hx] with z hz
    change 0 < z at hz
    simp [signedCbrt, abs_of_pos hz, Real.sign_of_pos hz]
  have hcbrt_deriv :
      HasDerivAt signedCbrt
        ((1 / 3 : ℝ) * Real.rpow x ((1 / 3 : ℝ) - 1)) x := by
    have hpow :
        HasDerivAt (fun z : ℝ => Real.rpow z (1 / 3 : ℝ))
          ((1 / 3 : ℝ) * Real.rpow x ((1 / 3 : ℝ) - 1)) x := by
      convert (hasDerivAt_id x).rpow_const
        (Or.inl (ne_of_gt hx)) using 1 <;> simp <;> ring
    exact hpow.congr_of_eventuallyEq hsc_event
  have hsqrt_event :
      Real.sqrt =ᶠ[nhds x]
        (fun z : ℝ => Real.rpow z (1 / 2 : ℝ)) := by
    apply Filter.Eventually.of_forall
    intro z
    exact Real.sqrt_eq_rpow z
  have hsqrt_deriv :
      HasDerivAt Real.sqrt
        ((1 / 2 : ℝ) * Real.rpow x ((1 / 2 : ℝ) - 1)) x := by
    have hpow :
        HasDerivAt (fun z : ℝ => Real.rpow z (1 / 2 : ℝ))
          ((1 / 2 : ℝ) * Real.rpow x ((1 / 2 : ℝ) - 1)) x := by
      convert (hasDerivAt_id x).rpow_const
        (Or.inl (ne_of_gt hx)) using 1 <;> simp <;> ring
    exact hpow.congr_of_eventuallyEq hsqrt_event
  have hsqrt_value :
      Real.sqrt x = Real.rpow x (1 / 2 : ℝ) := by
    exact Real.sqrt_eq_rpow x
  have hsqrt_pos : 0 < Real.sqrt x := Real.sqrt_pos.2 hx
  have hsqrt_den : 2 * Real.sqrt x ≠ 0 :=
    mul_ne_zero (by norm_num) (ne_of_gt hsqrt_pos)
  have hrpow_half_product :
      Real.rpow x ((1 / 2 : ℝ) - 1) * Real.rpow x (1 / 2 : ℝ) = 1 := by
    calc
      Real.rpow x ((1 / 2 : ℝ) - 1) * Real.rpow x (1 / 2 : ℝ) =
          Real.rpow x (((1 / 2 : ℝ) - 1) + (1 / 2 : ℝ)) :=
        (Real.rpow_add hx ((1 / 2 : ℝ) - 1) (1 / 2 : ℝ)).symm
      _ = 1 := by norm_num
  have hsqrt_coeff :
      (1 / 2 : ℝ) * Real.rpow x ((1 / 2 : ℝ) - 1) =
        1 / (2 * Real.sqrt x) := by
    apply (eq_div_iff hsqrt_den).2
    rw [hsqrt_value]
    calc
      ((1 / 2 : ℝ) * Real.rpow x ((1 / 2 : ℝ) - 1)) *
          (2 * Real.rpow x (1 / 2 : ℝ)) =
          Real.rpow x ((1 / 2 : ℝ) - 1) *
            Real.rpow x (1 / 2 : ℝ) := by ring
      _ = 1 := hrpow_half_product
  rw [hsqrt_coeff] at hsqrt_deriv
  have hx2 : 0 < x ^ 2 := pow_pos hx _
  have hsigned_sq :
      signedCbrt (x ^ 2) = Real.rpow x (2 / 3 : ℝ) := by
    simp only [signedCbrt, Real.sign_of_pos hx2, one_mul, abs_of_pos hx2]
    rw [pow_two]
    calc
      Real.rpow (x * x) (1 / 3 : ℝ) =
          Real.rpow x (1 / 3 : ℝ) * Real.rpow x (1 / 3 : ℝ) :=
        Real.mul_rpow hx.le hx.le
      _ = Real.rpow x ((1 / 3 : ℝ) + (1 / 3 : ℝ)) :=
        (Real.rpow_add hx (1 / 3 : ℝ) (1 / 3 : ℝ)).symm
      _ = Real.rpow x (2 / 3 : ℝ) := by norm_num
  have hsigned_sq_pos : 0 < signedCbrt (x ^ 2) := by
    rw [hsigned_sq]
    exact Real.rpow_pos_of_pos hx _
  have hden : 3 * signedCbrt (x ^ 2) ≠ 0 :=
    mul_ne_zero (by norm_num) (ne_of_gt hsigned_sq_pos)
  have hrpow_product :
      Real.rpow x ((1 / 3 : ℝ) - 1) * Real.rpow x (2 / 3 : ℝ) = 1 := by
    calc
      Real.rpow x ((1 / 3 : ℝ) - 1) * Real.rpow x (2 / 3 : ℝ) =
          Real.rpow x (((1 / 3 : ℝ) - 1) + (2 / 3 : ℝ)) :=
        (Real.rpow_add hx ((1 / 3 : ℝ) - 1) (2 / 3 : ℝ)).symm
      _ = 1 := by norm_num
  have hcoeff :
      (1 / 3 : ℝ) * Real.rpow x ((1 / 3 : ℝ) - 1) =
        1 / (3 * signedCbrt (x ^ 2)) := by
    apply (eq_div_iff hden).2
    rw [hsigned_sq]
    calc
      ((1 / 3 : ℝ) * Real.rpow x ((1 / 3 : ℝ) - 1)) *
          (3 * Real.rpow x (2 / 3 : ℝ)) =
          Real.rpow x ((1 / 3 : ℝ) - 1) *
            Real.rpow x (2 / 3 : ℝ) := by ring
      _ = 1 := hrpow_product
  rw [hcoeff] at hcbrt_deriv
  simpa [y] using
    ((hasDerivAt_id x).add hsqrt_deriv).add hcbrt_deriv

end

end ProofGap.Exercise851
