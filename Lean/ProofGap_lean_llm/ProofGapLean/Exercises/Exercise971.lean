import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise971

noncomputable section

def y (a b x : ℝ) : ℝ :=
  b / a * x +
    2 * Real.sqrt (a ^ 2 - b ^ 2) / a *
      Real.arctan
        (Real.sqrt ((a - b) / (a + b)) * Real.tanh (x / 2))

def expandedDerivative (a b x : ℝ) : ℝ :=
  b / a +
    2 * Real.sqrt (a ^ 2 - b ^ 2) / a *
      (1 / (1 + (a - b) / (a + b) * Real.tanh (x / 2) ^ 2)) *
      Real.sqrt ((a - b) / (a + b)) *
      (1 / (2 * Real.cosh (x / 2) ^ 2))

def middleDerivative (a b x : ℝ) : ℝ :=
  b / a + (a ^ 2 - b ^ 2) / (a * (b + a * Real.cosh x))

def finalDerivative (a b x : ℝ) : ℝ :=
  (a + b * Real.cosh x) / (b + a * Real.cosh x)

private theorem expandedDerivative_eq_middle
    (a b x : ℝ) (hab : |b| < a) :
    expandedDerivative a b x = middleDerivative a b x := by
  have ha : 0 < a := lt_of_le_of_lt (abs_nonneg b) hab
  have hba : b < a := lt_of_le_of_lt (le_abs_self b) hab
  have hminus : 0 < a - b := sub_pos.mpr hba
  have hplus : 0 < a + b := by
    have hneg : -b < a := lt_of_le_of_lt (neg_le_abs b) hab
    linarith
  have hD : 0 ≤ a ^ 2 - b ^ 2 := by
    rw [show a ^ 2 - b ^ 2 = (a - b) * (a + b) by ring]
    exact (mul_pos hminus hplus).le
  have hratio : 0 ≤ (a - b) / (a + b) :=
    (div_pos hminus hplus).le
  have hsqrtD : Real.sqrt (a ^ 2 - b ^ 2) ^ 2 = a ^ 2 - b ^ 2 :=
    Real.sq_sqrt hD
  have hsqrtRatio :
      Real.sqrt ((a - b) / (a + b)) ^ 2 = (a - b) / (a + b) :=
    Real.sq_sqrt hratio
  have hrootSq :
      (Real.sqrt (a ^ 2 - b ^ 2) *
        Real.sqrt ((a - b) / (a + b))) ^ 2 = (a - b) ^ 2 := by
    calc
      (Real.sqrt (a ^ 2 - b ^ 2) *
          Real.sqrt ((a - b) / (a + b))) ^ 2 =
          (a ^ 2 - b ^ 2) * ((a - b) / (a + b)) := by
            rw [mul_pow, hsqrtD, hsqrtRatio]
      _ = (a - b) ^ 2 := by
        field_simp [ne_of_gt hplus]
        ring
  have hrootNonneg :
      0 ≤ Real.sqrt (a ^ 2 - b ^ 2) *
        Real.sqrt ((a - b) / (a + b)) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hroot :
      Real.sqrt (a ^ 2 - b ^ 2) *
          Real.sqrt ((a - b) / (a + b)) = a - b := by
    nlinarith
  have hcoshPyth :
      Real.cosh (x / 2) ^ 2 - Real.sinh (x / 2) ^ 2 = 1 :=
    Real.cosh_sq_sub_sinh_sq (x / 2)
  have hcoshDouble :
      Real.cosh x =
        Real.cosh (x / 2) ^ 2 + Real.sinh (x / 2) ^ 2 := by
    calc
      Real.cosh x = Real.cosh (x / 2 + x / 2) := by
        congr 1
        ring
      _ = Real.cosh (x / 2) ^ 2 + Real.sinh (x / 2) ^ 2 := by
        rw [Real.cosh_add]
        ring
  have hdenIdentity :
      (a + b) * Real.cosh (x / 2) ^ 2 +
          (a - b) * Real.sinh (x / 2) ^ 2 =
        b + a * Real.cosh x := by
    calc
      (a + b) * Real.cosh (x / 2) ^ 2 +
          (a - b) * Real.sinh (x / 2) ^ 2 =
          a * (Real.cosh (x / 2) ^ 2 + Real.sinh (x / 2) ^ 2) +
            b * (Real.cosh (x / 2) ^ 2 - Real.sinh (x / 2) ^ 2) := by ring
      _ = a * Real.cosh x + b * 1 := by
        rw [← hcoshDouble, hcoshPyth]
      _ = b + a * Real.cosh x := by ring
  have hcombined :
      Real.cosh (x / 2) ^ 2 +
          (a - b) / (a + b) * Real.sinh (x / 2) ^ 2 =
        (b + a * Real.cosh x) / (a + b) := by
    calc
      Real.cosh (x / 2) ^ 2 +
          (a - b) / (a + b) * Real.sinh (x / 2) ^ 2 =
          ((a + b) * Real.cosh (x / 2) ^ 2 +
            (a - b) * Real.sinh (x / 2) ^ 2) / (a + b) := by
              field_simp [ne_of_gt hplus]
      _ = (b + a * Real.cosh x) / (a + b) := by rw [hdenIdentity]
  have hcoshOne : 1 ≤ Real.cosh x := by
    have hident := Real.cosh_sq_sub_sinh_sq x
    have hpos := Real.cosh_pos x
    nlinarith [sq_nonneg (Real.sinh x)]
  have hacosh : a ≤ a * Real.cosh x := by
    simpa using
      mul_le_mul_of_nonneg_left hcoshOne (le_of_lt ha)
  have hmain : 0 < b + a * Real.cosh x := by
    have hb : -a < b := by
      have hneg : -b < a := lt_of_le_of_lt (neg_le_abs b) hab
      linarith
    linarith
  have hcombinedPos :
      0 < Real.cosh (x / 2) ^ 2 +
        (a - b) / (a + b) * Real.sinh (x / 2) ^ 2 := by
    rw [hcombined]
    exact div_pos hmain hplus
  have hangle :
      0 < 1 + (a - b) / (a + b) *
        (Real.sinh (x / 2) / Real.cosh (x / 2)) ^ 2 := by
    have hnonneg := mul_nonneg hratio
      (sq_nonneg (Real.sinh (x / 2) / Real.cosh (x / 2)))
    linarith
  have hterm :
      2 * Real.sqrt (a ^ 2 - b ^ 2) / a *
          (1 / (1 + (a - b) / (a + b) * Real.tanh (x / 2) ^ 2)) *
          Real.sqrt ((a - b) / (a + b)) *
          (1 / (2 * Real.cosh (x / 2) ^ 2)) =
        (a - b) / a *
          (1 / (Real.cosh (x / 2) ^ 2 +
            (a - b) / (a + b) * Real.sinh (x / 2) ^ 2)) := by
    calc
      2 * Real.sqrt (a ^ 2 - b ^ 2) / a *
          (1 / (1 + (a - b) / (a + b) * Real.tanh (x / 2) ^ 2)) *
          Real.sqrt ((a - b) / (a + b)) *
          (1 / (2 * Real.cosh (x / 2) ^ 2)) =
          2 / a *
            (Real.sqrt (a ^ 2 - b ^ 2) *
              Real.sqrt ((a - b) / (a + b))) *
            (1 / (1 + (a - b) / (a + b) * Real.tanh (x / 2) ^ 2)) *
            (1 / (2 * Real.cosh (x / 2) ^ 2)) := by ring
      _ = 2 / a * (a - b) *
            (1 / (1 + (a - b) / (a + b) * Real.tanh (x / 2) ^ 2)) *
            (1 / (2 * Real.cosh (x / 2) ^ 2)) := by rw [hroot]
      _ = (a - b) / a *
          (1 / (Real.cosh (x / 2) ^ 2 +
            (a - b) / (a + b) * Real.sinh (x / 2) ^ 2)) := by
        rw [Real.tanh_eq_sinh_div_cosh]
        field_simp [ne_of_gt ha, ne_of_gt hplus,
          ne_of_gt (Real.cosh_pos (x / 2)), ne_of_gt hangle,
          ne_of_gt hcombinedPos]
  unfold expandedDerivative middleDerivative
  rw [hterm, hcombined]
  field_simp [ne_of_gt ha, ne_of_gt hplus, ne_of_gt hmain]
  ring

theorem gap1 (a b x : ℝ) (hab0 : 0 ≤ |b|) (hab : |b| < a) :
    HasDerivAt (y a b) (expandedDerivative a b x) x := by
  have ha : 0 < a := lt_of_le_of_lt (abs_nonneg b) hab
  have hba : b < a := lt_of_le_of_lt (le_abs_self b) hab
  have hminus : 0 < a - b := sub_pos.mpr hba
  have hplus : 0 < a + b := by
    have hneg : -b < a := lt_of_le_of_lt (neg_le_abs b) hab
    linarith
  have hratio : 0 ≤ (a - b) / (a + b) :=
    (div_pos hminus hplus).le
  have hsqrt :
      Real.sqrt ((a - b) / (a + b)) ^ 2 = (a - b) / (a + b) :=
    Real.sq_sqrt hratio
  have hangle :
      0 < 1 + (a - b) / (a + b) * Real.tanh (x / 2) ^ 2 := by
    have hnonneg :=
      mul_nonneg hratio (sq_nonneg (Real.tanh (x / 2)))
    linarith
  have hhalf :
      HasDerivAt (fun z : ℝ => z / 2) (1 / 2) x := by
    simpa [div_eq_mul_inv, mul_comm] using
      (hasDerivAt_id x).const_mul (1 / (2 : ℝ))
  have hnegHalf :
      HasDerivAt (fun z : ℝ => -(z / 2)) (-(1 / 2)) x := by
    exact hhalf.neg
  have hexpPos :
      HasDerivAt (fun z : ℝ => Real.exp (z / 2))
        (Real.exp (x / 2) * (1 / 2)) x := by
    simpa only [Function.comp_apply] using
      (Real.hasDerivAt_exp (x / 2)).comp x hhalf
  have hexpNeg :
      HasDerivAt (fun z : ℝ => Real.exp (-(z / 2)))
        (Real.exp (-(x / 2)) * (-(1 / 2))) x := by
    simpa only [Function.comp_apply] using
      (Real.hasDerivAt_exp (-(x / 2))).comp x hnegHalf
  have hrawSinh :
      HasDerivAt
        (fun z : ℝ =>
          (1 / 2) * (Real.exp (z / 2) - Real.exp (-(z / 2))))
        ((1 / 2) *
          (Real.exp (x / 2) * (1 / 2) -
            Real.exp (-(x / 2)) * (-(1 / 2)))) x := by
    exact (hexpPos.sub hexpNeg).const_mul (1 / 2)
  have hsinhFun :
      (fun z : ℝ => Real.sinh (z / 2)) =
        (fun z : ℝ =>
          (1 / 2) * (Real.exp (z / 2) - Real.exp (-(z / 2)))) := by
    funext z
    rw [Real.sinh_eq]
    ring
  have hsinhCoeff :
      Real.cosh (x / 2) * (1 / 2) =
        (1 / 2) *
          (Real.exp (x / 2) * (1 / 2) -
            Real.exp (-(x / 2)) * (-(1 / 2))) := by
    rw [Real.cosh_eq]
    ring
  have hsinh :
      HasDerivAt (fun z : ℝ => Real.sinh (z / 2))
        (Real.cosh (x / 2) * (1 / 2)) x := by
    rw [hsinhFun, hsinhCoeff]
    exact hrawSinh
  have hrawCosh :
      HasDerivAt
        (fun z : ℝ =>
          (1 / 2) * (Real.exp (z / 2) + Real.exp (-(z / 2))))
        ((1 / 2) *
          (Real.exp (x / 2) * (1 / 2) +
            Real.exp (-(x / 2)) * (-(1 / 2)))) x := by
    exact (hexpPos.add hexpNeg).const_mul (1 / 2)
  have hcoshFun :
      (fun z : ℝ => Real.cosh (z / 2)) =
        (fun z : ℝ =>
          (1 / 2) * (Real.exp (z / 2) + Real.exp (-(z / 2)))) := by
    funext z
    rw [Real.cosh_eq]
    ring
  have hcoshCoeff :
      Real.sinh (x / 2) * (1 / 2) =
        (1 / 2) *
          (Real.exp (x / 2) * (1 / 2) +
            Real.exp (-(x / 2)) * (-(1 / 2))) := by
    rw [Real.sinh_eq]
    ring
  have hcosh :
      HasDerivAt (fun z : ℝ => Real.cosh (z / 2))
        (Real.sinh (x / 2) * (1 / 2)) x := by
    rw [hcoshFun, hcoshCoeff]
    exact hrawCosh
  have hquot :
      HasDerivAt
        (fun z : ℝ => Real.sinh (z / 2) / Real.cosh (z / 2))
        (((Real.cosh (x / 2) * (1 / 2)) * Real.cosh (x / 2) -
            Real.sinh (x / 2) * (Real.sinh (x / 2) * (1 / 2))) /
          Real.cosh (x / 2) ^ 2) x := by
    exact hsinh.div hcosh (ne_of_gt (Real.cosh_pos (x / 2)))
  have hquotCoeff :
      ((Real.cosh (x / 2) * (1 / 2)) * Real.cosh (x / 2) -
          Real.sinh (x / 2) * (Real.sinh (x / 2) * (1 / 2))) /
          Real.cosh (x / 2) ^ 2 =
        (1 / Real.cosh (x / 2) ^ 2) * (1 / 2) := by
    field_simp [ne_of_gt (Real.cosh_pos (x / 2))]
    nlinarith [Real.cosh_sq_sub_sinh_sq (x / 2)]
  have htanh :
      HasDerivAt (fun z : ℝ => Real.tanh (z / 2))
        ((1 / Real.cosh (x / 2) ^ 2) * (1 / 2)) x := by
    simpa only [Real.tanh_eq_sinh_div_cosh, hquotCoeff] using hquot
  have hinner :
      HasDerivAt
        (fun z : ℝ =>
          Real.sqrt ((a - b) / (a + b)) * Real.tanh (z / 2))
        (Real.sqrt ((a - b) / (a + b)) *
          ((1 / Real.cosh (x / 2) ^ 2) * (1 / 2))) x := by
    exact htanh.const_mul (Real.sqrt ((a - b) / (a + b)))
  have hatanBase :
      HasDerivAt Real.arctan
        (1 / (1 +
          (Real.sqrt ((a - b) / (a + b)) * Real.tanh (x / 2)) ^ 2))
        (Real.sqrt ((a - b) / (a + b)) * Real.tanh (x / 2)) := by
    exact Real.hasDerivAt_arctan _
  have hatan :
      HasDerivAt
        (fun z : ℝ =>
          Real.arctan
            (Real.sqrt ((a - b) / (a + b)) * Real.tanh (z / 2)))
        ((1 / (1 +
            (Real.sqrt ((a - b) / (a + b)) *
              Real.tanh (x / 2)) ^ 2)) *
          (Real.sqrt ((a - b) / (a + b)) *
            ((1 / Real.cosh (x / 2) ^ 2) * (1 / 2)))) x := by
    simpa only [Function.comp_apply] using hatanBase.comp x hinner
  have houter :
      HasDerivAt
        (fun z : ℝ =>
          2 * Real.sqrt (a ^ 2 - b ^ 2) / a *
            Real.arctan
              (Real.sqrt ((a - b) / (a + b)) * Real.tanh (z / 2)))
        (2 * Real.sqrt (a ^ 2 - b ^ 2) / a *
          ((1 / (1 +
              (Real.sqrt ((a - b) / (a + b)) *
                Real.tanh (x / 2)) ^ 2)) *
            (Real.sqrt ((a - b) / (a + b)) *
              ((1 / Real.cosh (x / 2) ^ 2) * (1 / 2))))) x := by
    exact hatan.const_mul (2 * Real.sqrt (a ^ 2 - b ^ 2) / a)
  have hlinear :
      HasDerivAt (fun z : ℝ => b / a * z) (b / a) x := by
    simpa using (hasDerivAt_id x).const_mul (b / a)
  have htotal :
      HasDerivAt (y a b)
        (b / a +
          2 * Real.sqrt (a ^ 2 - b ^ 2) / a *
            ((1 / (1 +
                (Real.sqrt ((a - b) / (a + b)) *
                  Real.tanh (x / 2)) ^ 2)) *
              (Real.sqrt ((a - b) / (a + b)) *
                ((1 / Real.cosh (x / 2) ^ 2) * (1 / 2))))) x := by
    simpa [y] using hlinear.add houter
  have hvalue :
      b / a +
          2 * Real.sqrt (a ^ 2 - b ^ 2) / a *
            ((1 / (1 +
                (Real.sqrt ((a - b) / (a + b)) *
                  Real.tanh (x / 2)) ^ 2)) *
              (Real.sqrt ((a - b) / (a + b)) *
                ((1 / Real.cosh (x / 2) ^ 2) * (1 / 2)))) =
        expandedDerivative a b x := by
    unfold expandedDerivative
    rw [mul_pow, hsqrt]
    field_simp [ne_of_gt ha, ne_of_gt hangle,
      ne_of_gt (Real.cosh_pos (x / 2))]
  rw [← hvalue]
  exact htotal

theorem gap2 (a b x : ℝ) (hab0 : 0 ≤ |b|) (hab : |b| < a) :
    HasDerivAt (y a b) (middleDerivative a b x) x := by
  rw [← expandedDerivative_eq_middle a b x hab]
  exact gap1 a b x hab0 hab

theorem gap3 (a b x : ℝ) (hab0 : 0 ≤ |b|) (hab : |b| < a) :
    middleDerivative a b x = finalDerivative a b x := by
  have ha : 0 < a := lt_of_le_of_lt (abs_nonneg b) hab
  have hcoshOne : 1 ≤ Real.cosh x := by
    have hident := Real.cosh_sq_sub_sinh_sq x
    have hpos := Real.cosh_pos x
    nlinarith [sq_nonneg (Real.sinh x)]
  have hacosh : a ≤ a * Real.cosh x := by
    simpa using
      mul_le_mul_of_nonneg_left hcoshOne (le_of_lt ha)
  have hden : 0 < b + a * Real.cosh x := by
    have hb : -a < b := by
      have hneg : -b < a := lt_of_le_of_lt (neg_le_abs b) hab
      linarith
    linarith
  unfold middleDerivative finalDerivative
  field_simp [ne_of_gt ha, ne_of_gt hden]
  ring

theorem gap4 (a b x : ℝ) (hab0 : 0 ≤ |b|) (hab : |b| < a) :
    HasDerivAt (y a b) (finalDerivative a b x) x := by
  rw [← gap3 a b x hab0 hab]
  exact gap2 a b x hab0 hab

end

end ProofGap.Exercise971
