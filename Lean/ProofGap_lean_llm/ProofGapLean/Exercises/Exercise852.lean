import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

namespace ProofGap.Exercise852

noncomputable section

def signedCbrt (x : ℝ) : ℝ :=
  Real.sign x * Real.rpow |x| (1 / 3 : ℝ)

def y (x : ℝ) : ℝ :=
  1 / x + 1 / Real.sqrt x + 1 / signedCbrt x

/-- Source: `proof_gap/exercise_852/1.txt`; use a signed real cube root and
restore the omitted domain `x > 0`. -/
theorem gap1 (x : ℝ) (hx : 0 < x) :
    HasDerivAt y
      (-(1 / x ^ 2 + 1 / (2 * x * Real.sqrt x) +
        1 / (3 * x * signedCbrt x))) x := by
  have hx0 : x ≠ 0 := ne_of_gt hx
  have hrhalf_pos : 0 < Real.rpow x (1 / 2 : ℝ) :=
    Real.rpow_pos_of_pos hx _
  have hrhalf_ne : Real.rpow x (1 / 2 : ℝ) ≠ 0 :=
    ne_of_gt hrhalf_pos
  have hrthird_ne : Real.rpow x (1 / 3 : ℝ) ≠ 0 :=
    ne_of_gt (Real.rpow_pos_of_pos hx _)
  have hrhalf_sq : (Real.rpow x (1 / 2 : ℝ)) ^ 2 = x := by
    calc
      (Real.rpow x (1 / 2 : ℝ)) ^ 2 =
          Real.rpow x (1 / 2 : ℝ) * Real.rpow x (1 / 2 : ℝ) := by
            rw [pow_two]
      _ = Real.rpow x ((1 / 2 : ℝ) + (1 / 2 : ℝ)) :=
        (Real.rpow_add hx (1 / 2 : ℝ) (1 / 2 : ℝ)).symm
      _ = x := by norm_num
  have hsqrt_eq : Real.sqrt x = Real.rpow x (1 / 2 : ℝ) := by
    have hsqrt_nonneg : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
    have hsqrt_sq : (Real.sqrt x) ^ 2 = x :=
      Real.sq_sqrt (le_of_lt hx)
    nlinarith
  have hcbrt : signedCbrt x = Real.rpow x (1 / 3 : ℝ) := by
    simp [signedCbrt, abs_of_pos hx, Real.sign_of_pos hx]
  have h₁ := (hasDerivAt_id x).inv hx0
  have hrhalf : HasDerivAt (fun z : ℝ => Real.rpow z (1 / 2 : ℝ))
      ((1 / 2 : ℝ) * Real.rpow x ((1 / 2 : ℝ) - 1)) x :=
    Real.hasDerivAt_rpow_const (Or.inl hx0)
  have h₂ := hrhalf.inv hrhalf_ne
  have hrthird : HasDerivAt (fun z : ℝ => Real.rpow z (1 / 3 : ℝ))
      ((1 / 3 : ℝ) * Real.rpow x ((1 / 3 : ℝ) - 1)) x :=
    Real.hasDerivAt_rpow_const (Or.inl hx0)
  have h₃ := hrthird.inv hrthird_ne
  have hraw := (h₁.add h₂).add h₃
  have heq : y =ᶠ[nhds x]
      (((id : ℝ → ℝ)⁻¹ +
          (fun z : ℝ => Real.rpow z (1 / 2 : ℝ))⁻¹) +
        (fun z : ℝ => Real.rpow z (1 / 3 : ℝ))⁻¹) := by
    filter_upwards [eventually_gt_nhds hx] with z hz
    simp [y, signedCbrt, abs_of_pos hz, Real.sign_of_pos hz,
      Real.sqrt_eq_rpow, one_div]
  have hyraw := hraw.congr_of_eventuallyEq heq
  have hhalfRel :
      Real.rpow x ((1 / 2 : ℝ) - 1) * x =
        Real.rpow x (1 / 2 : ℝ) := by
    calc
      Real.rpow x ((1 / 2 : ℝ) - 1) * x =
          Real.rpow x ((1 / 2 : ℝ) - 1) * Real.rpow x 1 := by simp
      _ = Real.rpow x (((1 / 2 : ℝ) - 1) + 1) :=
        (Real.rpow_add hx ((1 / 2 : ℝ) - 1) 1).symm
      _ = Real.rpow x (1 / 2 : ℝ) := by norm_num
  have hthirdRel :
      Real.rpow x ((1 / 3 : ℝ) - 1) * x =
        Real.rpow x (1 / 3 : ℝ) := by
    calc
      Real.rpow x ((1 / 3 : ℝ) - 1) * x =
          Real.rpow x ((1 / 3 : ℝ) - 1) * Real.rpow x 1 := by simp
      _ = Real.rpow x (((1 / 3 : ℝ) - 1) + 1) :=
        (Real.rpow_add hx ((1 / 3 : ℝ) - 1) 1).symm
      _ = Real.rpow x (1 / 3 : ℝ) := by norm_num
  have hcoef₂ :
      (-( (1 / 2 : ℝ) * Real.rpow x ((1 / 2 : ℝ) - 1)) /
          (Real.rpow x (1 / 2 : ℝ)) ^ 2) =
        -(1 / (2 * x * Real.sqrt x)) := by
    rw [hsqrt_eq]
    field_simp [hx0, hrhalf_ne] <;> nlinarith [hhalfRel]
  have hcoef₃ :
      (-( (1 / 3 : ℝ) * Real.rpow x ((1 / 3 : ℝ) - 1)) /
          (Real.rpow x (1 / 3 : ℝ)) ^ 2) =
        -(1 / (3 * x * signedCbrt x)) := by
    rw [hcbrt]
    field_simp [hx0, hrthird_ne] <;> nlinarith [hthirdRel]
  convert hyraw using 1
  rw [hcoef₂, hcoef₃]
  simp only [id_eq]
  ring

end

end ProofGap.Exercise852
