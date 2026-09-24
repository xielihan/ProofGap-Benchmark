import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1600

noncomputable section

def xCoord (a t : ℝ) := a * Real.cos t
def yCoord (b t : ℝ) := b * Real.sin t
def cot (t : ℝ) := Real.cos t / Real.sin t
def slope (a b t : ℝ) := deriv (yCoord b) t / deriv (xCoord a) t
def secondSlope (a b t : ℝ) := deriv (slope a b) t / deriv (xCoord a) t
def powThreeHalves (u : ℝ) := u * Real.sqrt u
def eccentricity (a b : ℝ) := Real.sqrt (a ^ 2 - b ^ 2) / a
def curvatureRadius (a b t : ℝ) :=
  powThreeHalves (1 + (slope a b t) ^ 2) / |secondSlope a b t|

private theorem derivYCoord (b t : ℝ) :
    deriv (yCoord b) t = b * Real.cos t := by
  change deriv (fun u : ℝ => b * Real.sin u) t = b * Real.cos t
  exact ((Real.hasDerivAt_sin t).const_mul b).deriv

private theorem derivXCoord (a t : ℝ) :
    deriv (xCoord a) t = -a * Real.sin t := by
  change deriv (fun u : ℝ => a * Real.cos u) t = -a * Real.sin t
  calc
    deriv (fun u : ℝ => a * Real.cos u) t = a * (-Real.sin t) :=
      ((Real.hasDerivAt_cos t).const_mul a).deriv
    _ = -a * Real.sin t := by ring

private theorem slopeFormula (a b t : ℝ) (ha : a ≠ 0) :
    slope a b t = -(b / a) * cot t := by
  unfold slope
  rw [derivYCoord, derivXCoord]
  by_cases hsin : Real.sin t = 0
  · simp [cot, hsin]
  · unfold cot
    field_simp [ha, hsin]

private theorem hasDerivAtCot (t : ℝ) (hs : Real.sin t ≠ 0) :
    HasDerivAt cot (-(1 / (Real.sin t) ^ 2)) t := by
  have hcoeff :
      ((-Real.sin t) * Real.sin t - Real.cos t * Real.cos t) /
          (Real.sin t) ^ 2 =
        -(1 / (Real.sin t) ^ 2) := by
    field_simp [hs]
    nlinarith [Real.sin_sq_add_cos_sq t]
  simpa only [cot, hcoeff] using
    (Real.hasDerivAt_cos t).div (Real.hasDerivAt_sin t) hs

theorem gap1 (a b t : ℝ) (ha : 0 < a) (hs : Real.sin t ≠ 0) :
    slope a b t = b * Real.cos t / (-a * Real.sin t) := by
  unfold slope
  rw [derivYCoord, derivXCoord]
theorem gap2 (a b t : ℝ) (ha : 0 < a) (hs : Real.sin t ≠ 0) :
    b * Real.cos t / (-a * Real.sin t) = -(b / a) * cot t := by
  unfold cot
  field_simp [ha.ne', hs]
theorem gap3 (a b t : ℝ) (ha : 0 < a) (hs : Real.sin t ≠ 0) :
    slope a b t = -(b / a) * cot t := by
  exact slopeFormula a b t ha.ne'
theorem gap4 (a b t : ℝ) (ha : 0 < a) (hs : Real.sin t ≠ 0) :
    secondSlope a b t =
      (-(b / a) * (-(1 / (Real.sin t) ^ 2))) / (-a * Real.sin t) := by
  have hfun : slope a b = fun u : ℝ => -(b / a) * cot u := by
    funext u
    exact slopeFormula a b u ha.ne'
  have hd :
      deriv (fun u : ℝ => -(b / a) * cot u) t =
        -(b / a) * (-(1 / (Real.sin t) ^ 2)) :=
    ((hasDerivAtCot t hs).const_mul (-(b / a))).deriv
  unfold secondSlope
  rw [hfun, hd, derivXCoord]
theorem gap5 (a b t : ℝ) (ha : 0 < a) (hs : Real.sin t ≠ 0) :
    (-(b / a) * (-(1 / (Real.sin t) ^ 2))) / (-a * Real.sin t) =
      -(b / (a ^ 2 * (Real.sin t) ^ 3)) := by
  field_simp [ha.ne', hs] <;> ring
theorem gap6 (a b t : ℝ) (ha : 0 < a) (hs : Real.sin t ≠ 0) :
    secondSlope a b t = -(b / (a ^ 2 * (Real.sin t) ^ 3)) := by
  rw [gap4 a b t ha hs, gap5 a b t ha hs]
theorem gap7 (a b t : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hs : Real.sin t ≠ 0) :
    curvatureRadius a b t =
      powThreeHalves (1 + b ^ 2 * (cot t) ^ 2 / a ^ 2) /
        (b / (a ^ 2 * |Real.sin t| ^ 3)) := by
  unfold curvatureRadius
  rw [gap3 a b t ha hs, gap6 a b t ha hs]
  have hsq :
      (-(b / a) * cot t) ^ 2 = b ^ 2 * (cot t) ^ 2 / a ^ 2 := by
    field_simp [ha.ne'] <;> ring
  rw [hsq]
  have habs :
      |-(b / (a ^ 2 * (Real.sin t) ^ 3))| =
        b / (a ^ 2 * |Real.sin t| ^ 3) := by
    simp [abs_div, abs_mul, abs_pow, abs_of_pos ha, abs_of_pos hb]
  rw [habs]
theorem gap8 (a b t : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hs : Real.sin t ≠ 0) :
    curvatureRadius a b t =
      powThreeHalves
          (a ^ 2 * (Real.sin t) ^ 2 + b ^ 2 * (Real.cos t) ^ 2) /
        (a * b) := by
  rw [gap7 a b t ha hb hs]
  have hQ :
      0 ≤ a ^ 2 * (Real.sin t) ^ 2 + b ^ 2 * (Real.cos t) ^ 2 := by
    positivity
  have hu :
      1 + b ^ 2 * (cot t) ^ 2 / a ^ 2 =
        (a ^ 2 * (Real.sin t) ^ 2 + b ^ 2 * (Real.cos t) ^ 2) /
          (a ^ 2 * (Real.sin t) ^ 2) := by
    unfold cot
    field_simp [ha.ne', hs] <;> ring
  have hden :
      a ^ 2 * (Real.sin t) ^ 2 = (a * |Real.sin t|) ^ 2 := by
    rw [mul_pow, sq_abs]
  have huabs :
      1 + b ^ 2 * (cot t) ^ 2 / a ^ 2 =
        (a ^ 2 * (Real.sin t) ^ 2 + b ^ 2 * (Real.cos t) ^ 2) /
          (a * |Real.sin t|) ^ 2 := by
    calc
      1 + b ^ 2 * (cot t) ^ 2 / a ^ 2 =
          (a ^ 2 * (Real.sin t) ^ 2 + b ^ 2 * (Real.cos t) ^ 2) /
            (a ^ 2 * (Real.sin t) ^ 2) := hu
      _ = (a ^ 2 * (Real.sin t) ^ 2 + b ^ 2 * (Real.cos t) ^ 2) /
            (a * |Real.sin t|) ^ 2 := by rw [hden]
  have hsqrt :
      Real.sqrt (1 + b ^ 2 * (cot t) ^ 2 / a ^ 2) =
        Real.sqrt
            (a ^ 2 * (Real.sin t) ^ 2 + b ^ 2 * (Real.cos t) ^ 2) /
          (a * |Real.sin t|) := by
    rw [huabs]
    have hquot :
        0 ≤
          (a ^ 2 * (Real.sin t) ^ 2 + b ^ 2 * (Real.cos t) ^ 2) /
            (a * |Real.sin t|) ^ 2 :=
      div_nonneg hQ (sq_nonneg _)
    have hleft := Real.sqrt_nonneg
      ((a ^ 2 * (Real.sin t) ^ 2 + b ^ 2 * (Real.cos t) ^ 2) /
        (a * |Real.sin t|) ^ 2)
    have hright :
        0 ≤
          Real.sqrt
              (a ^ 2 * (Real.sin t) ^ 2 + b ^ 2 * (Real.cos t) ^ 2) /
            (a * |Real.sin t|) := by
      positivity
    have hsquares :
        (Real.sqrt
            ((a ^ 2 * (Real.sin t) ^ 2 + b ^ 2 * (Real.cos t) ^ 2) /
              (a * |Real.sin t|) ^ 2)) ^ 2 =
          (Real.sqrt
              (a ^ 2 * (Real.sin t) ^ 2 + b ^ 2 * (Real.cos t) ^ 2) /
            (a * |Real.sin t|)) ^ 2 := by
      calc
        (Real.sqrt
            ((a ^ 2 * (Real.sin t) ^ 2 + b ^ 2 * (Real.cos t) ^ 2) /
              (a * |Real.sin t|) ^ 2)) ^ 2 =
            (a ^ 2 * (Real.sin t) ^ 2 + b ^ 2 * (Real.cos t) ^ 2) /
              (a * |Real.sin t|) ^ 2 := Real.sq_sqrt hquot
        _ = (Real.sqrt
              (a ^ 2 * (Real.sin t) ^ 2 + b ^ 2 * (Real.cos t) ^ 2)) ^ 2 /
              (a * |Real.sin t|) ^ 2 := by rw [Real.sq_sqrt hQ]
        _ = (Real.sqrt
              (a ^ 2 * (Real.sin t) ^ 2 + b ^ 2 * (Real.cos t) ^ 2) /
              (a * |Real.sin t|)) ^ 2 := by ring
    nlinarith
  unfold powThreeHalves
  rw [hsqrt, huabs]
  field_simp [ha.ne', hb.ne', abs_ne_zero.mpr hs] <;> ring
theorem gap9 (a b t : ℝ) (ha : 0 < a) (hb : 0 < b) (hba : b ≤ a)
    (hs : Real.sin t ≠ 0) :
    curvatureRadius a b t =
      a ^ 3 * powThreeHalves
          (1 - (a ^ 2 - b ^ 2) / a ^ 2 * (Real.cos t) ^ 2) /
        (a * b) := by
  rw [gap8 a b t ha hb hs]
  have hsincos :
      (Real.sin t) ^ 2 = 1 - (Real.cos t) ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq t]
  have hQV :
      a ^ 2 * (Real.sin t) ^ 2 + b ^ 2 * (Real.cos t) ^ 2 =
        a ^ 2 *
          (1 - (a ^ 2 - b ^ 2) / a ^ 2 * (Real.cos t) ^ 2) := by
    calc
      a ^ 2 * (Real.sin t) ^ 2 + b ^ 2 * (Real.cos t) ^ 2 =
          a ^ 2 - (a ^ 2 - b ^ 2) * (Real.cos t) ^ 2 := by
        rw [hsincos]
        ring
      _ = a ^ 2 *
          (1 - (a ^ 2 - b ^ 2) / a ^ 2 * (Real.cos t) ^ 2) := by
        field_simp [ha.ne'] <;> ring
  have hVeq :
      1 - (a ^ 2 - b ^ 2) / a ^ 2 * (Real.cos t) ^ 2 =
        (a ^ 2 * (Real.sin t) ^ 2 + b ^ 2 * (Real.cos t) ^ 2) / a ^ 2 := by
    calc
      1 - (a ^ 2 - b ^ 2) / a ^ 2 * (Real.cos t) ^ 2 =
          (a ^ 2 *
            (1 - (a ^ 2 - b ^ 2) / a ^ 2 * (Real.cos t) ^ 2)) / a ^ 2 := by
        field_simp [ha.ne'] <;> ring
      _ = (a ^ 2 * (Real.sin t) ^ 2 + b ^ 2 * (Real.cos t) ^ 2) / a ^ 2 := by
        rw [← hQV]
  have hQ :
      0 ≤ a ^ 2 * (Real.sin t) ^ 2 + b ^ 2 * (Real.cos t) ^ 2 := by
    positivity
  have hV :
      0 ≤ 1 - (a ^ 2 - b ^ 2) / a ^ 2 * (Real.cos t) ^ 2 := by
    rw [hVeq]
    positivity
  have hsqrt :
      Real.sqrt
          (a ^ 2 * (Real.sin t) ^ 2 + b ^ 2 * (Real.cos t) ^ 2) =
        a * Real.sqrt
          (1 - (a ^ 2 - b ^ 2) / a ^ 2 * (Real.cos t) ^ 2) := by
    have hleft := Real.sqrt_nonneg
      (a ^ 2 * (Real.sin t) ^ 2 + b ^ 2 * (Real.cos t) ^ 2)
    have hright :
        0 ≤ a * Real.sqrt
          (1 - (a ^ 2 - b ^ 2) / a ^ 2 * (Real.cos t) ^ 2) := by
      positivity
    have hsquares :
        (Real.sqrt
          (a ^ 2 * (Real.sin t) ^ 2 + b ^ 2 * (Real.cos t) ^ 2)) ^ 2 =
          (a * Real.sqrt
            (1 - (a ^ 2 - b ^ 2) / a ^ 2 * (Real.cos t) ^ 2)) ^ 2 := by
      rw [Real.sq_sqrt hQ, mul_pow, Real.sq_sqrt hV]
      exact hQV
    nlinarith
  unfold powThreeHalves
  rw [hsqrt, hQV]
  ring
theorem gap10 (a b t : ℝ) (ha : 0 < a) (hb : 0 < b) (hba : b ≤ a)
    (hs : Real.sin t ≠ 0) :
    curvatureRadius a b t =
      a ^ 2 / b *
        powThreeHalves (1 - (eccentricity a b) ^ 2 * (Real.cos t) ^ 2) := by
  have hd : 0 ≤ a ^ 2 - b ^ 2 := by
    have hp : 0 ≤ (a - b) * (a + b) :=
      mul_nonneg (sub_nonneg.mpr hba) (add_nonneg ha.le hb.le)
    nlinarith
  have he :
      (eccentricity a b) ^ 2 = (a ^ 2 - b ^ 2) / a ^ 2 := by
    unfold eccentricity
    rw [div_pow, Real.sq_sqrt hd]
  rw [gap9 a b t ha hb hba hs, he]
  field_simp [ha.ne', hb.ne'] <;> ring

end
end ProofGap.Exercise1600
