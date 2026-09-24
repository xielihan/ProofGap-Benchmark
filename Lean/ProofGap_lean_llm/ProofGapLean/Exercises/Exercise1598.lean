import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Neighborhoods

namespace ProofGap.Exercise1598

noncomputable section

def hyperbolaY (a b x : ℝ) := b / a * Real.sqrt (x ^ 2 - a ^ 2)
def eccentricity (a b : ℝ) := Real.sqrt (a ^ 2 + b ^ 2) / a
def powThreeHalves (u : ℝ) := u * Real.sqrt u
def curvatureRadius (a b x : ℝ) :=
  powThreeHalves
      (1 + b ^ 4 * x ^ 2 / (a ^ 4 * (hyperbolaY a b x) ^ 2)) /
    |deriv (deriv (hyperbolaY a b)) x|

private theorem hasDerivAt_sq_sub_const (a x : ℝ) :
    HasDerivAt (fun t : ℝ => t ^ 2 - a ^ 2) (2 * x) x := by
  have hmul : HasDerivAt (fun t : ℝ => t * t) (x + x) x := by
    simpa using (hasDerivAt_id x).mul (hasDerivAt_id x)
  have hconst : HasDerivAt (fun _ : ℝ => a ^ 2) 0 x :=
    hasDerivAt_const x (a ^ 2)
  have hsub := hmul.sub hconst
  simpa only [pow_two, sub_zero, two_mul] using hsub

private theorem scale_powThreeHalves (c u : ℝ) (hc : 0 < c) :
    powThreeHalves (c ^ 2 * u) = c ^ 3 * powThreeHalves u := by
  unfold powThreeHalves
  rw [Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs, abs_of_pos hc]
  ring

theorem gap1 (a b x : ℝ) (ha : 0 < a) (hb : 0 < b) (hx : a < x) :
    deriv (hyperbolaY a b) x =
      b ^ 2 * x / (a ^ 2 * hyperbolaY a b x) := by
  have hrad : 0 < x ^ 2 - a ^ 2 := by
    nlinarith
  have hsqrt : 0 < Real.sqrt (x ^ 2 - a ^ 2) := Real.sqrt_pos.2 hrad
  have hinner := hasDerivAt_sq_sub_const a x
  have hs :
      HasDerivAt (fun t : ℝ => Real.sqrt (t ^ 2 - a ^ 2))
        ((1 / (2 * Real.sqrt (x ^ 2 - a ^ 2))) * (2 * x)) x := by
    simpa [Function.comp_def] using
      ((Real.hasDerivAt_sqrt hrad.ne').comp x hinner)
  have hscaled := hs.const_mul (b / a)
  change HasDerivAt (hyperbolaY a b)
    ((b / a) * ((1 / (2 * Real.sqrt (x ^ 2 - a ^ 2))) * (2 * x))) x at hscaled
  rw [hscaled.deriv]
  unfold hyperbolaY
  field_simp [ha.ne', hb.ne', hsqrt.ne'] <;> ring
theorem gap2 (a b x : ℝ) (ha : 0 < a) (hb : 0 < b) (hx : a < x) :
    deriv (deriv (hyperbolaY a b)) x =
      -(b ^ 4 / (a ^ 2 * (hyperbolaY a b x) ^ 3)) := by
  have hrad : 0 < x ^ 2 - a ^ 2 := by
    nlinarith
  have hsqrt : 0 < Real.sqrt (x ^ 2 - a ^ 2) := Real.sqrt_pos.2 hrad
  have hsquare : (Real.sqrt (x ^ 2 - a ^ 2)) ^ 2 = x ^ 2 - a ^ 2 :=
    Real.sq_sqrt hrad.le
  have hinner := hasDerivAt_sq_sub_const a x
  have hs :
      HasDerivAt (fun t : ℝ => Real.sqrt (t ^ 2 - a ^ 2))
        ((1 / (2 * Real.sqrt (x ^ 2 - a ^ 2))) * (2 * x)) x := by
    simpa [Function.comp_def] using
      ((Real.hasDerivAt_sqrt hrad.ne').comp x hinner)
  have hnum :
      HasDerivAt (fun t : ℝ => (b / a) * t) (b / a) x := by
    simpa using (hasDerivAt_id x).const_mul (b / a)
  have hg := hnum.div hs hsqrt.ne'
  have hlocal :
      (fun t : ℝ => deriv (hyperbolaY a b) t) =ᶠ[nhds x]
        (fun t : ℝ => b / a * t / Real.sqrt (t ^ 2 - a ^ 2)) := by
    filter_upwards [isOpen_Ioi.mem_nhds hx] with t ht
    have hat : a < t := ht
    have htpos : 0 < t := lt_trans ha hat
    have hradprod : 0 < (t - a) * (t + a) :=
      mul_pos (sub_pos.mpr hat) (add_pos htpos ha)
    have hradt : 0 < t ^ 2 - a ^ 2 := by
      nlinarith
    have hsqrtt : 0 < Real.sqrt (t ^ 2 - a ^ 2) := Real.sqrt_pos.2 hradt
    rw [gap1 a b t ha hb hat]
    unfold hyperbolaY
    field_simp [ha.ne', hb.ne', hsqrtt.ne']
  have hsecond := hg.congr_of_eventuallyEq hlocal
  change deriv (fun t : ℝ => deriv (hyperbolaY a b) t) x = _
  rw [hsecond.deriv]
  unfold hyperbolaY
  field_simp [ha.ne', hb.ne', hsqrt.ne']
  ring_nf
  rw [hsquare]
  ring
theorem gap3 (a b x : ℝ) (ha : 0 < a) (hb : 0 < b) (hx : a < x) :
    curvatureRadius a b x =
      powThreeHalves
          (1 + b ^ 4 * x ^ 2 / (a ^ 4 * (hyperbolaY a b x) ^ 2)) /
        |deriv (deriv (hyperbolaY a b)) x| := by
  rfl
theorem gap4 (a b x : ℝ) (ha : 0 < a) (hb : 0 < b) (hx : a < x) :
    curvatureRadius a b x =
      powThreeHalves
          (1 + b ^ 4 * x ^ 2 / (a ^ 4 * (hyperbolaY a b x) ^ 2)) /
        (b ^ 4 / (a ^ 2 * |hyperbolaY a b x| ^ 3)) := by
  have hrad : 0 < x ^ 2 - a ^ 2 := by
    nlinarith
  have hy : 0 < hyperbolaY a b x := by
    unfold hyperbolaY
    exact mul_pos (div_pos hb ha) (Real.sqrt_pos.2 hrad)
  have hq :
      0 < b ^ 4 / (a ^ 2 * (hyperbolaY a b x) ^ 3) :=
    div_pos (pow_pos hb 4) (mul_pos (pow_pos ha 2) (pow_pos hy 3))
  rw [gap3 a b x ha hb hx, gap2 a b x ha hb hx, abs_neg,
    abs_of_pos hq, abs_of_pos hy]
theorem gap5 (a b x : ℝ) (ha : 0 < a) (hb : 0 < b) (hx : a < x) :
    curvatureRadius a b x =
      powThreeHalves
          (a ^ 4 * (hyperbolaY a b x) ^ 2 + b ^ 4 * x ^ 2) /
        (a ^ 4 * b ^ 4) := by
  have hrad : 0 < x ^ 2 - a ^ 2 := by
    nlinarith
  have hy : 0 < hyperbolaY a b x := by
    unfold hyperbolaY
    exact mul_pos (div_pos hb ha) (Real.sqrt_pos.2 hrad)
  have hc : 0 < a ^ 2 * hyperbolaY a b x :=
    mul_pos (pow_pos ha 2) hy
  have hN :
      a ^ 4 * (hyperbolaY a b x) ^ 2 + b ^ 4 * x ^ 2 =
        (a ^ 2 * hyperbolaY a b x) ^ 2 *
          (1 + b ^ 4 * x ^ 2 /
            (a ^ 4 * (hyperbolaY a b x) ^ 2)) := by
    field_simp [ha.ne', hy.ne'] <;> ring
  rw [gap4 a b x ha hb hx, abs_of_pos hy, hN,
    scale_powThreeHalves
      (a ^ 2 * hyperbolaY a b x)
      (1 + b ^ 4 * x ^ 2 /
        (a ^ 4 * (hyperbolaY a b x) ^ 2)) hc]
  field_simp [ha.ne', hb.ne', hy.ne'] <;> ring
theorem gap6 (a b x : ℝ) (ha : 0 < a) (hb : 0 < b) (hx : a < x) :
    curvatureRadius a b x =
      powThreeHalves
          (a ^ 2 * b ^ 2 * x ^ 2 - a ^ 4 * b ^ 2 + b ^ 4 * x ^ 2) /
        (a ^ 4 * b ^ 4) := by
  have hrad : 0 < x ^ 2 - a ^ 2 := by
    nlinarith
  have hsquare : (Real.sqrt (x ^ 2 - a ^ 2)) ^ 2 = x ^ 2 - a ^ 2 :=
    Real.sq_sqrt hrad.le
  have harg :
      a ^ 4 * (hyperbolaY a b x) ^ 2 + b ^ 4 * x ^ 2 =
        a ^ 2 * b ^ 2 * x ^ 2 - a ^ 4 * b ^ 2 + b ^ 4 * x ^ 2 := by
    unfold hyperbolaY
    rw [mul_pow, div_pow, hsquare]
    field_simp [ha.ne'] <;> ring
  rw [gap5 a b x ha hb hx, harg]
theorem gap7 (a b x : ℝ) (ha : 0 < a) (hb : 0 < b) (hx : a < x) :
    curvatureRadius a b x =
      powThreeHalves ((a ^ 2 + b ^ 2) / a ^ 2 * x ^ 2 - a ^ 2) / (a * b) := by
  have harg :
      a ^ 2 * b ^ 2 * x ^ 2 - a ^ 4 * b ^ 2 + b ^ 4 * x ^ 2 =
        (a * b) ^ 2 * ((a ^ 2 + b ^ 2) / a ^ 2 * x ^ 2 - a ^ 2) := by
    field_simp [ha.ne'] <;> ring
  rw [gap6 a b x ha hb hx, harg,
    scale_powThreeHalves
      (a * b) ((a ^ 2 + b ^ 2) / a ^ 2 * x ^ 2 - a ^ 2)
      (mul_pos ha hb)]
  field_simp [ha.ne', hb.ne'] <;> ring
theorem gap8 (a b x : ℝ) (ha : 0 < a) (hb : 0 < b) (hx : a < x) :
    curvatureRadius a b x =
      powThreeHalves ((eccentricity a b) ^ 2 * x ^ 2 - a ^ 2) / (a * b) := by
  have he :
      (eccentricity a b) ^ 2 = (a ^ 2 + b ^ 2) / a ^ 2 := by
    unfold eccentricity
    rw [div_pow, Real.sq_sqrt (add_nonneg (sq_nonneg a) (sq_nonneg b))]
  rw [gap7 a b x ha hb hx, he]

end
end ProofGap.Exercise1598
