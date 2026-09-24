import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise857

noncomputable section

def y (a x : ℝ) : ℝ :=
  x / Real.sqrt (a ^ 2 - x ^ 2)

/-- Source: `proof_gap/exercise_857/1.txt`.
The radicand is required to be positive. -/
private lemma exp_log_half_eq_sqrt {z : ℝ} (hz : 0 < z) :
    Real.exp (Real.log z / 2) = Real.sqrt z := by
  have he : (Real.exp (Real.log z / 2)) ^ 2 = z := by
    calc
      (Real.exp (Real.log z / 2)) ^ 2 =
          Real.exp (Real.log z / 2 + Real.log z / 2) := by
            rw [pow_two, Real.exp_add]
      _ = Real.exp (Real.log z) := by
            congr 1 <;> ring
      _ = z := Real.exp_log hz
  have hs : (Real.sqrt z) ^ 2 = z := Real.sq_sqrt (le_of_lt hz)
  nlinarith [Real.exp_pos (Real.log z / 2), Real.sqrt_nonneg z]

theorem gap1 (a x : ℝ) (hrad : 0 < a ^ 2 - x ^ 2) :
    HasDerivAt (y a)
      ((Real.sqrt (a ^ 2 - x ^ 2) +
          x ^ 2 / Real.sqrt (a ^ 2 - x ^ 2)) /
        (a ^ 2 - x ^ 2)) x := by
  unfold y
  have hrne : a ^ 2 - x ^ 2 ≠ 0 := ne_of_gt hrad
  have hsne : Real.sqrt (a ^ 2 - x ^ 2) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hrad)
  have hsquare :
      (Real.sqrt (a ^ 2 - x ^ 2)) ^ 2 = a ^ 2 - x ^ 2 :=
    Real.sq_sqrt (le_of_lt hrad)
  have hinner :
      HasDerivAt (fun t : ℝ => a ^ 2 - t ^ 2) (-2 * x) x := by
    simpa using
      ((hasDerivAt_const (x := x) (c := a ^ 2)).sub
        ((hasDerivAt_id x).pow 2))
  have hlog :
      HasDerivAt (fun t : ℝ => Real.log (a ^ 2 - t ^ 2))
        ((-2 * x) / (a ^ 2 - x ^ 2)) x := by
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      ((Real.hasDerivAt_log hrne).comp x hinner)
  have hhalf :
      HasDerivAt (fun t : ℝ => Real.log (a ^ 2 - t ^ 2) / 2)
        (((-2 * x) / (a ^ 2 - x ^ 2)) / 2) x :=
    hlog.div_const 2
  have hexp :
      HasDerivAt
        (fun t : ℝ => Real.exp (Real.log (a ^ 2 - t ^ 2) / 2))
        (Real.exp (Real.log (a ^ 2 - x ^ 2) / 2) *
          (((-2 * x) / (a ^ 2 - x ^ 2)) / 2)) x :=
    hhalf.exp
  have hev : ∀ᶠ t : ℝ in nhds x, 0 < a ^ 2 - t ^ 2 :=
    hinner.continuousAt.eventually (Ioi_mem_nhds hrad)
  have heq :
      (fun t : ℝ => Real.exp (Real.log (a ^ 2 - t ^ 2) / 2)) =ᶠ[nhds x]
        (fun t : ℝ => Real.sqrt (a ^ 2 - t ^ 2)) := by
    filter_upwards [hev] with t ht
    exact exp_log_half_eq_sqrt ht
  have hroot0 :
      HasDerivAt (fun t : ℝ => Real.sqrt (a ^ 2 - t ^ 2))
        (Real.exp (Real.log (a ^ 2 - x ^ 2) / 2) *
          (((-2 * x) / (a ^ 2 - x ^ 2)) / 2)) x :=
    hexp.congr_of_eventuallyEq heq.symm
  rw [exp_log_half_eq_sqrt hrad] at hroot0
  have hroot :
      HasDerivAt (fun t : ℝ => Real.sqrt (a ^ 2 - t ^ 2))
        (-x / Real.sqrt (a ^ 2 - x ^ 2)) x := by
    convert hroot0 using 1
    field_simp [hsne, hrne] <;> rw [hsquare] <;> ring
  have hquot :
      HasDerivAt
        (fun t : ℝ => t / Real.sqrt (a ^ 2 - t ^ 2))
        ((1 * Real.sqrt (a ^ 2 - x ^ 2) -
            x * (-x / Real.sqrt (a ^ 2 - x ^ 2))) /
          (Real.sqrt (a ^ 2 - x ^ 2)) ^ 2) x :=
    (hasDerivAt_id x).div hroot hsne
  rw [hsquare] at hquot
  convert hquot using 1
  field_simp [hsne, hrne]
  ring

/-- Source: `proof_gap/exercise_857/2.txt`.
The positivity hypothesis makes every displayed denominator meaningful. -/
theorem gap2 (a x : ℝ) (hrad : 0 < a ^ 2 - x ^ 2) :
    (Real.sqrt (a ^ 2 - x ^ 2) +
          x ^ 2 / Real.sqrt (a ^ 2 - x ^ 2)) /
        (a ^ 2 - x ^ 2) =
      a ^ 2 / Real.sqrt ((a ^ 2 - x ^ 2) ^ 3) := by
  have hrne : a ^ 2 - x ^ 2 ≠ 0 := ne_of_gt hrad
  have hsne : Real.sqrt (a ^ 2 - x ^ 2) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hrad)
  have hcube_pos : 0 < (a ^ 2 - x ^ 2) ^ 3 := pow_pos hrad 3
  have hroot_cube_sq :
      (Real.sqrt ((a ^ 2 - x ^ 2) ^ 3)) ^ 2 =
        (a ^ 2 - x ^ 2) ^ 3 :=
    Real.sq_sqrt (le_of_lt hcube_pos)
  have hprod_sq :
      ((a ^ 2 - x ^ 2) * Real.sqrt (a ^ 2 - x ^ 2)) ^ 2 =
        (a ^ 2 - x ^ 2) ^ 3 := by
    rw [mul_pow, Real.sq_sqrt (le_of_lt hrad)]
    ring
  have hsqrt_cube :
      Real.sqrt ((a ^ 2 - x ^ 2) ^ 3) =
        (a ^ 2 - x ^ 2) * Real.sqrt (a ^ 2 - x ^ 2) := by
    have hfactor :
        (Real.sqrt ((a ^ 2 - x ^ 2) ^ 3) -
            (a ^ 2 - x ^ 2) * Real.sqrt (a ^ 2 - x ^ 2)) *
          (Real.sqrt ((a ^ 2 - x ^ 2) ^ 3) +
            (a ^ 2 - x ^ 2) * Real.sqrt (a ^ 2 - x ^ 2)) = 0 := by
      calc
        _ = (Real.sqrt ((a ^ 2 - x ^ 2) ^ 3)) ^ 2 -
              ((a ^ 2 - x ^ 2) * Real.sqrt (a ^ 2 - x ^ 2)) ^ 2 := by ring
        _ = 0 := by rw [hroot_cube_sq, hprod_sq]; ring
    rcases mul_eq_zero.mp hfactor with hdiff | hsum
    · exact sub_eq_zero.mp hdiff
    · exfalso
      exact
        (ne_of_gt
          (add_pos (Real.sqrt_pos.2 hcube_pos)
            (mul_pos hrad (Real.sqrt_pos.2 hrad)))) hsum
  rw [hsqrt_cube]
  field_simp [hsne, hrne] <;>
    nlinarith [Real.sq_sqrt (le_of_lt hrad)]

/-- Source: `proof_gap/exercise_857/3.txt`.
The radicand is required to be positive. -/
theorem gap3 (a x : ℝ) (hrad : 0 < a ^ 2 - x ^ 2) :
    HasDerivAt (y a)
      (a ^ 2 / Real.sqrt ((a ^ 2 - x ^ 2) ^ 3)) x := by
  simpa only [gap2 a x hrad] using (gap1 a x hrad)

end

end ProofGap.Exercise857
