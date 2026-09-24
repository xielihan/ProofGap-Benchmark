import ProofGapLean.Prelude.Analysis
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Neighborhoods

open Filter Topology
open scoped Interval

namespace ProofGap.Exercise2250

noncomputable section

def originalIntegrand (x : ℝ) : ℝ := (1 + x ^ 2) / (1 + x ^ 4)
def tOfX (x : ℝ) : ℝ := x - 1 / x
def jacobian (x : ℝ) : ℝ := 1 + 1 / x ^ 2
def transformedIntegrand (t : ℝ) : ℝ := 1 / (t ^ 2 + 2)
def improperPartial (N : ℝ) : ℝ :=
  2 * ∫ t in N..0, transformedIntegrand t
def primitive (t : ℝ) : ℝ :=
  Real.sqrt 2 * Real.arctan (t / Real.sqrt 2)

private def originalAntiderivative (x : ℝ) : ℝ :=
  Real.sqrt 2 / 2 *
    (Real.arctan (Real.sqrt 2 * x - 1) +
      Real.arctan (Real.sqrt 2 * x + 1))

private theorem sqrtTwo_pos : 0 < Real.sqrt 2 := by
  positivity

private theorem sqrtTwo_sq : (Real.sqrt 2) ^ 2 = 2 := by
  exact Real.sq_sqrt (by norm_num)

private theorem sqrtTwo_mul_self : Real.sqrt 2 * Real.sqrt 2 = 2 := by
  simpa [pow_two] using sqrtTwo_sq

private theorem sqrtTwo_fourth : (Real.sqrt 2) ^ 4 = 4 := by
  calc
    (Real.sqrt 2) ^ 4 = ((Real.sqrt 2) ^ 2) ^ 2 := by ring
    _ = 4 := by rw [sqrtTwo_sq]; norm_num

private theorem originalIntegrand_continuous : Continuous originalIntegrand := by
  unfold originalIntegrand
  exact
    (continuous_const.add (continuous_id.pow 2)).div
      (continuous_const.add (continuous_id.pow 4)) (fun x => by positivity)

private theorem originalAntiderivative_hasDerivAt (x : ℝ) :
    HasDerivAt originalAntiderivative (originalIntegrand x) x := by
  let s : ℝ := Real.sqrt 2
  have hm :
      HasDerivAt (fun y : ℝ => Real.arctan (s * y - 1))
        (s / (1 + (s * x - 1) ^ 2)) x := by
    convert
      (Real.hasDerivAt_arctan (s * x - 1)).comp x
        (((hasDerivAt_id x).const_mul s).sub_const 1) using 1 <;> ring
  have hp :
      HasDerivAt (fun y : ℝ => Real.arctan (s * y + 1))
        (s / (1 + (s * x + 1) ^ 2)) x := by
    convert
      (Real.hasDerivAt_arctan (s * x + 1)).comp x
        (((hasDerivAt_id x).const_mul s).add_const 1) using 1 <;> ring
  have h := (hm.add hp).const_mul (s / 2)
  dsimp [s] at h
  have hm0 : 1 + (Real.sqrt 2 * x - 1) ^ 2 ≠ 0 := by positivity
  have hp0 : 1 + (Real.sqrt 2 * x + 1) ^ 2 ≠ 0 := by positivity
  have hq0 : 1 + x ^ 4 ≠ 0 := by positivity
  unfold originalAntiderivative originalIntegrand
  convert h using 1
  field_simp [hm0, hp0, hq0]
  ring_nf
  rw [sqrtTwo_fourth, sqrtTwo_sq] <;> ring

private theorem original_integral_eq_sub (a b : ℝ) :
    (∫ x in a..b, originalIntegrand x) =
      originalAntiderivative b - originalAntiderivative a := by
  exact
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x _ => originalAntiderivative_hasDerivAt x)
      (originalIntegrand_continuous.intervalIntegrable a b)

private theorem arctan_sqrtTwo_sum :
    Real.arctan (Real.sqrt 2 - 1) +
        Real.arctan (Real.sqrt 2 + 1) = Real.pi / 2 := by
  have hu : 0 < Real.sqrt 2 + 1 := by positivity
  have hinv : (Real.sqrt 2 + 1)⁻¹ = Real.sqrt 2 - 1 := by
    calc
      (Real.sqrt 2 + 1)⁻¹ = 1 / (Real.sqrt 2 + 1) := by rw [one_div]
      _ = Real.sqrt 2 - 1 := by
        apply (div_eq_iff (ne_of_gt hu)).2
        nlinarith [sqrtTwo_sq]
  calc
    Real.arctan (Real.sqrt 2 - 1) + Real.arctan (Real.sqrt 2 + 1) =
        Real.arctan ((Real.sqrt 2 + 1)⁻¹) +
          Real.arctan (Real.sqrt 2 + 1) := by rw [hinv]
    _ = Real.pi / 2 := by
      rw [Real.arctan_inv_of_pos hu]
      ring

private theorem originalAntiderivative_zero : originalAntiderivative 0 = 0 := by
  unfold originalAntiderivative
  rw [show Real.sqrt 2 * 0 - 1 = -(1 : ℝ) by ring]
  rw [show Real.sqrt 2 * 0 + 1 = (1 : ℝ) by ring]
  rw [Real.arctan_neg]
  ring

private theorem originalAntiderivative_one :
    originalAntiderivative 1 = Real.sqrt 2 * Real.pi / 4 := by
  unfold originalAntiderivative
  simp only [mul_one]
  rw [arctan_sqrtTwo_sum]
  ring

private theorem originalAntiderivative_neg_one :
    originalAntiderivative (-1) = -originalAntiderivative 1 := by
  unfold originalAntiderivative
  rw [show Real.sqrt 2 * (-1) - 1 = -(Real.sqrt 2 + 1) by ring]
  rw [show Real.sqrt 2 * (-1) + 1 = -(Real.sqrt 2 - 1) by ring]
  rw [Real.arctan_neg, Real.arctan_neg]
  ring

private theorem original_integral_symmetric :
    (∫ x in (-1 : ℝ)..1, originalIntegrand x) =
      2 * ∫ x in (0 : ℝ)..1, originalIntegrand x := by
  rw [original_integral_eq_sub, original_integral_eq_sub]
  rw [originalAntiderivative_zero, originalAntiderivative_neg_one]
  ring

private theorem sqrtTwo_pi_div_two :
    Real.sqrt 2 * Real.pi / 2 = Real.pi / Real.sqrt 2 := by
  apply (eq_div_iff (ne_of_gt sqrtTwo_pos)).2
  calc
    (Real.sqrt 2 * Real.pi / 2) * Real.sqrt 2 =
        (Real.sqrt 2 * Real.sqrt 2) * Real.pi / 2 := by ring
    _ = Real.pi := by rw [sqrtTwo_mul_self]; ring

private theorem twice_half_original_integral :
    2 * ∫ x in (0 : ℝ)..1, originalIntegrand x =
      Real.pi / Real.sqrt 2 := by
  rw [original_integral_eq_sub, originalAntiderivative_zero,
    originalAntiderivative_one]
  calc
    2 * (Real.sqrt 2 * Real.pi / 4 - 0) =
        Real.sqrt 2 * Real.pi / 2 := by ring
    _ = Real.pi / Real.sqrt 2 := sqrtTwo_pi_div_two

private theorem transformedIntegrand_continuous :
    Continuous transformedIntegrand := by
  unfold transformedIntegrand
  exact
    continuous_const.div ((continuous_id.pow 2).add continuous_const)
      (fun x => by positivity)

private theorem primitive_hasDerivAt (t : ℝ) :
    HasDerivAt primitive (2 * transformedIntegrand t) t := by
  let s : ℝ := Real.sqrt 2
  have hs : s ≠ 0 := by
    dsimp [s]
    exact ne_of_gt sqrtTwo_pos
  have hs2 : s ^ 2 = 2 := by
    simpa [s] using sqrtTwo_sq
  have harg : HasDerivAt (fun y : ℝ => y / s) (1 / s) t := by
    convert (hasDerivAt_id t).div_const s using 1 <;> ring
  have h :=
    ((Real.hasDerivAt_arctan (t / s)).comp t harg).const_mul s
  unfold primitive transformedIntegrand
  dsimp [s] at h ⊢
  convert h using 1
  field_simp [hs]
  ring_nf
  nlinarith [hs2]

private theorem improperPartial_eq_primitive_sub (N : ℝ) :
    improperPartial N = primitive 0 - primitive N := by
  have h :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t _ => primitive_hasDerivAt t)
      ((continuous_const.mul transformedIntegrand_continuous).intervalIntegrable N 0)
  simpa only [improperPartial, intervalIntegral.integral_const_mul] using h

private theorem primitive_sub_tendsto :
    Tendsto (fun N : ℝ => primitive 0 - primitive N) atBot
      (nhds (Real.pi / Real.sqrt 2)) := by
  let s : ℝ := Real.sqrt 2
  have hs : 0 < s := by simpa [s] using sqrtTwo_pos
  have hscale : Tendsto (fun N : ℝ => N / s) atBot atBot := by
    refine tendsto_atBot.2 ?_
    intro b
    filter_upwards [eventually_le_atBot (b * s)] with N hN
    exact (div_le_iff₀ hs).2 hN
  have hatanWithin := Real.tendsto_arctan_atBot.comp hscale
  have hatan :
      Tendsto (fun N : ℝ => Real.arctan (N / s)) atBot
        (nhds (-(Real.pi / 2))) := by
    simpa only [Function.comp_apply] using
      hatanWithin.mono_right inf_le_left
  have hmul :
      Tendsto (fun N : ℝ => (-s) * Real.arctan (N / s)) atBot
        (nhds ((-s) * (-(Real.pi / 2)))) :=
    tendsto_const_nhds.mul hatan
  have hvalue : (-s) * (-(Real.pi / 2)) = Real.pi / s := by
    calc
      (-s) * (-(Real.pi / 2)) = s * Real.pi / 2 := by ring
      _ = Real.pi / s := by simpa [s] using sqrtTwo_pi_div_two
  rw [hvalue] at hmul
  simpa [primitive, s] using hmul

theorem gap1 :
    (∫ x in (-1 : ℝ)..1, originalIntegrand x) =
      2 * ∫ x in (0 : ℝ)..1, originalIntegrand x := by
  exact original_integral_symmetric

theorem gap2 :
    Tendsto improperPartial atBot
      (𝓝 (2 * ∫ x in (0 : ℝ)..1, originalIntegrand x)) := by
  have hfun :
      improperPartial = fun N : ℝ => primitive 0 - primitive N := by
    funext N
    exact improperPartial_eq_primitive_sub N
  rw [hfun, twice_half_original_integral]
  exact primitive_sub_tendsto

theorem gap3 (N : ℝ) :
    improperPartial N = primitive 0 - primitive N := by
  exact improperPartial_eq_primitive_sub N

theorem gap4 :
    Tendsto (fun N : ℝ => primitive 0 - primitive N) atBot
      (𝓝 (Real.pi / Real.sqrt 2)) := by
  exact primitive_sub_tendsto

theorem gap5 :
    (∫ x in (-1 : ℝ)..1, originalIntegrand x) =
      Real.pi / Real.sqrt 2 := by
  calc
    (∫ x in (-1 : ℝ)..1, originalIntegrand x) =
        2 * ∫ x in (0 : ℝ)..1, originalIntegrand x := gap1
    _ = Real.pi / Real.sqrt 2 := twice_half_original_integral

end

end ProofGap.Exercise2250
