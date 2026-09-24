import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise927

noncomputable section

def sec (x : ℝ) : ℝ := 1 / Real.cos x

def y (a b x : ℝ) : ℝ :=
  2 / Real.sqrt (a ^ 2 - b ^ 2) *
    Real.arctan
      (Real.sqrt ((a - b) / (a + b)) * Real.tan (x / 2))

def expandedDerivative (a b x : ℝ) : ℝ :=
  2 / Real.sqrt (a ^ 2 - b ^ 2) *
    (1 / (1 + (a - b) / (a + b) * Real.tan (x / 2) ^ 2)) *
    Real.sqrt ((a - b) / (a + b)) * (1 / 2) * sec (x / 2) ^ 2

def finalDerivative (a b x : ℝ) : ℝ :=
  1 / (a + b * Real.cos x)

/-- Exercise 927, gap 1; replace the inconsistent global
parameter assumptions by pointwise `b < a`, `0 ≤ b`, and exclude tangent
poles at `x/2`. -/
theorem gap1 (a b x : ℝ) (hab : b < a) (hb : 0 ≤ b)
    (hcos : Real.cos (x / 2) ≠ 0) :
    HasDerivAt (y a b) (expandedDerivative a b x) x := by
  have hsum : 0 < a + b := by
    linarith
  have hdiff : 0 < a - b := by
    linarith
  have hq : 0 ≤ (a - b) / (a + b) :=
    le_of_lt (div_pos hdiff hsum)
  have hsquare :
      (Real.sqrt ((a - b) / (a + b)) * Real.tan (x / 2)) ^ 2 =
        (a - b) / (a + b) * Real.tan (x / 2) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hq]
  have hhalf : HasDerivAt (fun z : ℝ => z / 2) (1 / 2) x := by
    simpa using (hasDerivAt_id x).div_const 2
  have htan_base :
      HasDerivAt Real.tan (1 / Real.cos (x / 2) ^ 2) (x / 2) := by
    have hquot :=
      (Real.hasDerivAt_sin (x / 2)).div
        (Real.hasDerivAt_cos (x / 2)) hcos
    change
      HasDerivAt (fun z : ℝ => Real.sin z / Real.cos z)
        ((Real.cos (x / 2) * Real.cos (x / 2) -
            Real.sin (x / 2) * -Real.sin (x / 2)) /
          Real.cos (x / 2) ^ 2) (x / 2) at hquot
    have hfun :
        (fun z : ℝ => Real.sin z / Real.cos z) = Real.tan := by
      funext z
      exact (Real.tan_eq_sin_div_cos z).symm
    rw [hfun] at hquot
    have hnum :
        Real.cos (x / 2) * Real.cos (x / 2) -
            Real.sin (x / 2) * -Real.sin (x / 2) = 1 := by
      nlinarith [Real.sin_sq_add_cos_sq (x / 2)]
    simpa only [hnum] using hquot
  have htan :
      HasDerivAt (fun z : ℝ => Real.tan (z / 2))
        ((1 / Real.cos (x / 2) ^ 2) * (1 / 2)) x := by
    simpa using htan_base.comp x hhalf
  have hinner :
      HasDerivAt
        (fun z : ℝ =>
          Real.sqrt ((a - b) / (a + b)) * Real.tan (z / 2))
        (Real.sqrt ((a - b) / (a + b)) *
          ((1 / Real.cos (x / 2) ^ 2) * (1 / 2))) x := by
    simpa using htan.const_mul (Real.sqrt ((a - b) / (a + b)))
  have harctan :=
    (Real.hasDerivAt_arctan
      (Real.sqrt ((a - b) / (a + b)) * Real.tan (x / 2))).comp x hinner
  have hraw :=
    harctan.const_mul (2 / Real.sqrt (a ^ 2 - b ^ 2))
  change
    HasDerivAt
      (fun z : ℝ =>
        2 / Real.sqrt (a ^ 2 - b ^ 2) *
          Real.arctan
            (Real.sqrt ((a - b) / (a + b)) * Real.tan (z / 2)))
      (expandedDerivative a b x) x
  convert hraw using 1
  rw [hsquare]
  simp only [expandedDerivative, sec, one_div, inv_pow]
  ring_nf

/-- Exercise 927, gap 2; the parameter inequalities make
all constant radicands and denominators positive, while `hcos` handles the
half-angle tangent. -/
theorem gap2 (a b x : ℝ) (hab : b < a) (hb : 0 ≤ b)
    (hcos : Real.cos (x / 2) ≠ 0) :
    expandedDerivative a b x = finalDerivative a b x := by
  have hsum : 0 < a + b := by
    linarith
  have hdiff : 0 < a - b := by
    linarith
  have hq : 0 < (a - b) / (a + b) :=
    div_pos hdiff hsum
  have hprod : 0 < (a - b) * (a + b) :=
    mul_pos hdiff hsum
  have hrad : 0 < a ^ 2 - b ^ 2 := by
    nlinarith [hprod]
  have hsqrtq : 0 < Real.sqrt ((a - b) / (a + b)) :=
    Real.sqrt_pos.2 hq
  have hsqrtr : 0 < Real.sqrt (a ^ 2 - b ^ 2) :=
    Real.sqrt_pos.2 hrad
  have hsquares :
      ((a + b) * Real.sqrt ((a - b) / (a + b))) ^ 2 =
        Real.sqrt (a ^ 2 - b ^ 2) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (le_of_lt hq),
      Real.sq_sqrt (le_of_lt hrad)]
    field_simp [ne_of_gt hsum]
    ring_nf
  have hsqrt_rel :
      (a + b) * Real.sqrt ((a - b) / (a + b)) =
        Real.sqrt (a ^ 2 - b ^ 2) := by
    have hl :
        0 < (a + b) * Real.sqrt ((a - b) / (a + b)) :=
      mul_pos hsum hsqrtq
    nlinarith [hsquares, hsqrtr]
  have hcos_two :
      Real.cos x = 2 * Real.cos (x / 2) ^ 2 - 1 := by
    convert Real.cos_two_mul (x / 2) using 1 <;> ring
  have hsin_sq :
      Real.sin (x / 2) ^ 2 = 1 - Real.cos (x / 2) ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq (x / 2)]
  have htrigden :
      (a + b) * Real.cos (x / 2) ^ 2 +
          (a - b) * Real.sin (x / 2) ^ 2 =
        a + b * Real.cos x := by
    rw [hsin_sq, hcos_two]
    ring
  have hbc : -b ≤ b * Real.cos x := by
    have hc := mul_le_mul_of_nonneg_left (Real.neg_one_le_cos x) hb
    nlinarith
  have hfinalpos : 0 < a + b * Real.cos x := by
    linarith
  have hfracpos :
      0 < 1 + (a - b) / (a + b) *
        (Real.sin (x / 2) / Real.cos (x / 2)) ^ 2 := by
    have hm :
        0 ≤ (a - b) / (a + b) *
          (Real.sin (x / 2) / Real.cos (x / 2)) ^ 2 :=
      mul_nonneg (le_of_lt hq) (sq_nonneg _)
    linarith
  have htrigpos :
      0 < (a + b) * Real.cos (x / 2) ^ 2 +
        (a - b) * Real.sin (x / 2) ^ 2 := by
    rw [htrigden]
    exact hfinalpos
  unfold expandedDerivative finalDerivative sec
  rw [← hsqrt_rel, Real.tan_eq_sin_div_cos, ← htrigden]
  field_simp [ne_of_gt hsum, ne_of_gt hsqrtq, hcos,
    ne_of_gt hfracpos, ne_of_gt htrigpos]

/-- Exercise 927, gap 3; retain the corrected parameter
dependencies and the half-angle tangent domain. -/
theorem gap3 (a b x : ℝ) (hab : b < a) (hb : 0 ≤ b)
    (hcos : Real.cos (x / 2) ≠ 0) :
    HasDerivAt (y a b) (finalDerivative a b x) x := by
  rw [← gap2 a b x hab hb hcos]
  exact gap1 a b x hab hb hcos

end

end ProofGap.Exercise927
