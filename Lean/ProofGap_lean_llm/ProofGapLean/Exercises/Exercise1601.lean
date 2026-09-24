import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Topology.Neighborhoods
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

namespace ProofGap.Exercise1601

noncomputable section

def xCoord (a t : ℝ) := a * (t - Real.sin t)
def yCoord (a t : ℝ) := a * (1 - Real.cos t)
def cot (t : ℝ) := Real.cos t / Real.sin t
def slope (a t : ℝ) := deriv (yCoord a) t / deriv (xCoord a) t
def secondSlope (a t : ℝ) := deriv (slope a) t / deriv (xCoord a) t
def powThreeHalves (u : ℝ) := u * Real.sqrt u
def curvatureRadius (a t : ℝ) :=
  powThreeHalves (1 + (slope a t) ^ 2) / |secondSlope a t|

private theorem halfAngleSin (t : ℝ) :
    Real.sin t =
      2 * Real.sin (t / 2) * Real.cos (t / 2) := by
  have ht : t / 2 + t / 2 = t := by ring
  calc
    Real.sin t = Real.sin (t / 2 + t / 2) :=
      congrArg Real.sin ht |>.symm
    _ = Real.sin (t / 2) * Real.cos (t / 2) +
          Real.cos (t / 2) * Real.sin (t / 2) :=
      Real.sin_add _ _
    _ = 2 * Real.sin (t / 2) * Real.cos (t / 2) := by ring

private theorem halfAngleOneSubCos (t : ℝ) :
    1 - Real.cos t =
      2 * (Real.sin (t / 2)) ^ 2 := by
  have ht : t / 2 + t / 2 = t := by ring
  have hc :
      Real.cos t =
        Real.cos (t / 2) * Real.cos (t / 2) -
          Real.sin (t / 2) * Real.sin (t / 2) := by
    calc
      Real.cos t = Real.cos (t / 2 + t / 2) :=
        congrArg Real.cos ht |>.symm
      _ = Real.cos (t / 2) * Real.cos (t / 2) -
            Real.sin (t / 2) * Real.sin (t / 2) :=
        Real.cos_add _ _
  rw [hc]
  nlinarith [Real.sin_sq_add_cos_sq (t / 2)]

theorem gap1 (a t : ℝ) (ha : 0 < a) (hh : Real.sin (t / 2) ≠ 0) :
    slope a t = a * Real.sin t / (a * (1 - Real.cos t)) := by
  have hy : HasDerivAt (yCoord a) (a * Real.sin t) t := by
    simpa [yCoord] using
      ((Real.hasDerivAt_cos t).const_sub 1).const_mul a
  have hx : HasDerivAt (xCoord a) (a * (1 - Real.cos t)) t := by
    simpa [xCoord] using
      (((hasDerivAt_id t).sub (Real.hasDerivAt_sin t)).const_mul a)
  simpa only [slope, hy.deriv, hx.deriv]
theorem gap2 (a t : ℝ) (ha : 0 < a) (hh : Real.sin (t / 2) ≠ 0) :
    a * Real.sin t / (a * (1 - Real.cos t)) = cot (t / 2) := by
  rw [halfAngleSin, halfAngleOneSubCos]
  unfold cot
  field_simp [ne_of_gt ha, hh] <;> ring
theorem gap3 (a t : ℝ) (ha : 0 < a) (hh : Real.sin (t / 2) ≠ 0) :
    slope a t = cot (t / 2) := by
  calc
    slope a t = a * Real.sin t / (a * (1 - Real.cos t)) :=
      gap1 a t ha hh
    _ = cot (t / 2) := gap2 a t ha hh
theorem gap4 (a t : ℝ) (ha : 0 < a) (hh : Real.sin (t / 2) ≠ 0) :
    secondSlope a t =
      (-(1 / (2 * (Real.sin (t / 2)) ^ 2))) /
        (a * (1 - Real.cos t)) := by
  have hinner :
      HasDerivAt (fun x : ℝ => x / 2) (1 / 2 : ℝ) t := by
    simpa using (hasDerivAt_id t).div_const 2
  have hs :
      HasDerivAt (fun x : ℝ => Real.sin (x / 2))
        (Real.cos (t / 2) * (1 / 2 : ℝ)) t := by
    simpa only [Function.comp_apply] using
      (Real.hasDerivAt_sin (t / 2)).comp t hinner
  have hc :
      HasDerivAt (fun x : ℝ => Real.cos (x / 2))
        (-Real.sin (t / 2) * (1 / 2 : ℝ)) t := by
    simpa only [Function.comp_apply] using
      (Real.hasDerivAt_cos (t / 2)).comp t hinner
  have hcot :
      HasDerivAt (fun x : ℝ => cot (x / 2))
        (-(1 / (2 * (Real.sin (t / 2)) ^ 2))) t := by
    unfold cot
    convert hc.div hs hh using 1
    field_simp [hh]
    nlinarith [Real.sin_sq_add_cos_sq (t / 2)]
  have hne :
      ∀ᶠ x in nhds t, Real.sin (x / 2) ≠ 0 :=
    hs.continuousAt.eventually_ne hh
  have heq :
      slope a =ᶠ[nhds t] fun x : ℝ => cot (x / 2) :=
    hne.mono (fun x hx => gap3 a x ha hx)
  have hd :
      deriv (slope a) t =
        -(1 / (2 * (Real.sin (t / 2)) ^ 2)) := by
    calc
      deriv (slope a) t = deriv (fun x : ℝ => cot (x / 2)) t :=
        heq.deriv_eq
      _ = -(1 / (2 * (Real.sin (t / 2)) ^ 2)) := hcot.deriv
  have hx : HasDerivAt (xCoord a) (a * (1 - Real.cos t)) t := by
    simpa [xCoord] using
      (((hasDerivAt_id t).sub (Real.hasDerivAt_sin t)).const_mul a)
  simpa only [secondSlope, hd, hx.deriv]
theorem gap5 (a t : ℝ) (ha : 0 < a) (hh : Real.sin (t / 2) ≠ 0) :
    (-(1 / (2 * (Real.sin (t / 2)) ^ 2))) /
        (a * (1 - Real.cos t)) =
      -(1 / (4 * a * (Real.sin (t / 2)) ^ 4)) := by
  rw [halfAngleOneSubCos]
  field_simp [ne_of_gt ha, hh] <;> ring
theorem gap6 (a t : ℝ) (ha : 0 < a) (hh : Real.sin (t / 2) ≠ 0) :
    secondSlope a t = -(1 / (4 * a * (Real.sin (t / 2)) ^ 4)) := by
  calc
    secondSlope a t =
        (-(1 / (2 * (Real.sin (t / 2)) ^ 2))) /
          (a * (1 - Real.cos t)) := gap4 a t ha hh
    _ = -(1 / (4 * a * (Real.sin (t / 2)) ^ 4)) :=
      gap5 a t ha hh
theorem gap7 (a t : ℝ) (ha : 0 < a) (hh : Real.sin (t / 2) ≠ 0) :
    curvatureRadius a t =
      powThreeHalves (1 + (cot (t / 2)) ^ 2) /
        (1 / (4 * a * (Real.sin (t / 2)) ^ 4)) := by
  have hpos :
      0 < 1 / (4 * a * (Real.sin (t / 2)) ^ 4) := by
    positivity
  unfold curvatureRadius
  rw [gap3 a t ha hh, gap6 a t ha hh, abs_neg, abs_of_pos hpos]
theorem gap8 (a t : ℝ) (ha : 0 < a) (hh : Real.sin (t / 2) ≠ 0) :
    curvatureRadius a t = 4 * a * |Real.sin (t / 2)| := by
  have htrig := Real.sin_sq_add_cos_sq (t / 2)
  have hcotSq :
      1 + (cot (t / 2)) ^ 2 =
        1 / (Real.sin (t / 2)) ^ 2 := by
    unfold cot
    field_simp [hh]
    nlinarith
  have hsqrt :
      Real.sqrt (1 / (Real.sin (t / 2)) ^ 2) =
        1 / |Real.sin (t / 2)| := by
    have harg :
        1 / (Real.sin (t / 2)) ^ 2 =
          (1 / Real.sin (t / 2)) ^ 2 := by
      field_simp [hh] <;> ring
    rw [harg, Real.sqrt_sq_eq_abs, abs_div]
    norm_num
  have hsabs :
      (Real.sin (t / 2)) ^ 2 / |Real.sin (t / 2)| =
        |Real.sin (t / 2)| := by
    apply (div_eq_iff (abs_ne_zero.mpr hh)).2
    simpa [pow_two] using
      (sq_abs (Real.sin (t / 2))).symm
  rw [gap7 a t ha hh, hcotSq]
  unfold powThreeHalves
  rw [hsqrt]
  calc
    (1 / (Real.sin (t / 2)) ^ 2 *
          (1 / |Real.sin (t / 2)|)) /
        (1 / (4 * a * (Real.sin (t / 2)) ^ 4)) =
        4 * a *
          ((Real.sin (t / 2)) ^ 2 / |Real.sin (t / 2)|) := by
      field_simp [ne_of_gt ha, hh, abs_ne_zero.mpr hh] <;> ring
    _ = 4 * a * |Real.sin (t / 2)| := by rw [hsabs]
theorem gap9 (a t : ℝ) (ha : 0 < a) (hh : Real.sin (t / 2) ≠ 0) :
    curvatureRadius a t = 2 * Real.sqrt (2 * a * yCoord a t) := by
  rw [gap8 a t ha hh]
  unfold yCoord
  rw [halfAngleOneSubCos]
  have hinside :
      2 * a * (a * (2 * (Real.sin (t / 2)) ^ 2)) =
        (2 * a * Real.sin (t / 2)) ^ 2 := by
    ring
  rw [hinside, Real.sqrt_sq_eq_abs]
  rw [abs_mul, abs_mul, abs_of_pos ha]
  norm_num
  ring

end
end ProofGap.Exercise1601
