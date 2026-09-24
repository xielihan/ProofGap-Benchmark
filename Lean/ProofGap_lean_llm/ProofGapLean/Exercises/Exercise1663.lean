import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1663

noncomputable section

def integrand (x : ℝ) : ℝ := 1 / Real.sqrt (2 - 3 * x ^ 2)
def primitive (x : ℝ) : ℝ :=
  1 / Real.sqrt 3 * Real.arcsin (x * Real.sqrt (3 / 2))
def domain : Set ℝ := {x | 3 * x ^ 2 < 2}

theorem gap1 (x : ℝ) (hx : x ∈ domain) :
    HasDerivAt primitive (integrand x) x := by
  change 3 * x ^ 2 < 2 at hx
  have h3 : (0 : ℝ) < 3 := by norm_num
  have h32 : (0 : ℝ) < 3 / 2 := by norm_num
  have hs3 : Real.sqrt 3 ≠ 0 := ne_of_gt (Real.sqrt_pos.2 h3)
  have hs32_sq : (Real.sqrt (3 / 2)) ^ 2 = 3 / 2 :=
    Real.sq_sqrt (le_of_lt h32)
  have hu_sq : (x * Real.sqrt (3 / 2)) ^ 2 = (3 / 2) * x ^ 2 := by
    rw [mul_pow, hs32_sq]
    ring
  have hu_sq_lt : (x * Real.sqrt (3 / 2)) ^ 2 < 1 := by
    rw [hu_sq]
    nlinarith
  have hu : -1 < x * Real.sqrt (3 / 2) ∧ x * Real.sqrt (3 / 2) < 1 := by
    constructor
    · nlinarith [sq_nonneg (x * Real.sqrt (3 / 2) + 1)]
    · nlinarith [sq_nonneg (x * Real.sqrt (3 / 2) - 1)]
  have hne_neg : x * Real.sqrt (3 / 2) ≠ -1 := ne_of_gt hu.1
  have hne_pos : x * Real.sqrt (3 / 2) ≠ 1 := ne_of_lt hu.2
  have harc : HasDerivAt
      (fun y : ℝ => Real.arcsin (y * Real.sqrt (3 / 2)))
      (Real.sqrt (3 / 2) /
        Real.sqrt (1 - (x * Real.sqrt (3 / 2)) ^ 2)) x := by
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      (Real.hasDerivAt_arcsin hne_neg hne_pos).comp x
        ((hasDerivAt_id x).mul_const (Real.sqrt (3 / 2)))
  have hrad : 0 < 2 - 3 * x ^ 2 := by linarith
  have hinner : 0 < 1 - (x * Real.sqrt (3 / 2)) ^ 2 :=
    sub_pos.mpr hu_sq_lt
  have hsinner : Real.sqrt (1 - (x * Real.sqrt (3 / 2)) ^ 2) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hinner)
  have hsrad : Real.sqrt (2 - 3 * x ^ 2) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hrad)
  have hs3_sq : (Real.sqrt 3) ^ 2 = 3 :=
    Real.sq_sqrt (le_of_lt h3)
  have hsrad_sq : (Real.sqrt (2 - 3 * x ^ 2)) ^ 2 = 2 - 3 * x ^ 2 :=
    Real.sq_sqrt (le_of_lt hrad)
  have hsinner_sq :
      (Real.sqrt (1 - (x * Real.sqrt (3 / 2)) ^ 2)) ^ 2 =
        1 - (x * Real.sqrt (3 / 2)) ^ 2 :=
    Real.sq_sqrt (le_of_lt hinner)
  have hprod_sq :
      (Real.sqrt (2 - 3 * x ^ 2) * Real.sqrt (3 / 2)) ^ 2 =
        (Real.sqrt 3 *
          Real.sqrt (1 - (x * Real.sqrt (3 / 2)) ^ 2)) ^ 2 := by
    calc
      (Real.sqrt (2 - 3 * x ^ 2) * Real.sqrt (3 / 2)) ^ 2 =
          (Real.sqrt (2 - 3 * x ^ 2)) ^ 2 *
            (Real.sqrt (3 / 2)) ^ 2 := by ring
      _ = (2 - 3 * x ^ 2) * (3 / 2) := by
        rw [hsrad_sq, hs32_sq]
      _ = 3 * (1 - (x * Real.sqrt (3 / 2)) ^ 2) := by
        rw [hu_sq]
        ring
      _ = (Real.sqrt 3) ^ 2 *
          (Real.sqrt (1 - (x * Real.sqrt (3 / 2)) ^ 2)) ^ 2 := by
        rw [hs3_sq, hsinner_sq]
      _ = (Real.sqrt 3 *
          Real.sqrt (1 - (x * Real.sqrt (3 / 2)) ^ 2)) ^ 2 := by ring
  have hprod :
      Real.sqrt (2 - 3 * x ^ 2) * Real.sqrt (3 / 2) =
        Real.sqrt 3 * Real.sqrt (1 - (x * Real.sqrt (3 / 2)) ^ 2) := by
    nlinarith [hprod_sq,
      mul_nonneg (Real.sqrt_nonneg (2 - 3 * x ^ 2))
        (Real.sqrt_nonneg (3 / 2)),
      mul_nonneg (Real.sqrt_nonneg 3)
        (Real.sqrt_nonneg (1 - (x * Real.sqrt (3 / 2)) ^ 2))]
  have hdenom :
      Real.sqrt 3 * Real.sqrt (1 - (x * Real.sqrt (3 / 2)) ^ 2) ≠ 0 :=
    mul_ne_zero hs3 hsinner
  have hfrac :
      Real.sqrt (3 / 2) /
          (Real.sqrt 3 * Real.sqrt (1 - (x * Real.sqrt (3 / 2)) ^ 2)) =
        1 / Real.sqrt (2 - 3 * x ^ 2) := by
    apply (div_eq_div_iff hdenom hsrad).2
    simpa [mul_comm] using hprod
  have hcoef :
      1 / Real.sqrt 3 *
          (Real.sqrt (3 / 2) /
            Real.sqrt (1 - (x * Real.sqrt (3 / 2)) ^ 2)) =
        1 / Real.sqrt (2 - 3 * x ^ 2) := by
    calc
      1 / Real.sqrt 3 *
          (Real.sqrt (3 / 2) /
            Real.sqrt (1 - (x * Real.sqrt (3 / 2)) ^ 2)) =
          Real.sqrt (3 / 2) /
            (Real.sqrt 3 *
              Real.sqrt (1 - (x * Real.sqrt (3 / 2)) ^ 2)) := by
                field_simp [hs3, hsinner] <;> ring
      _ = 1 / Real.sqrt (2 - 3 * x ^ 2) := hfrac
  simpa only [primitive, integrand, hcoef] using
    harc.const_mul (1 / Real.sqrt 3)

end

end ProofGap.Exercise1663
