import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open scoped Interval

namespace ProofGap.Exercise2495_2

noncomputable section

def cycloidX (a t : ℝ) : ℝ := a * (t - Real.sin t)

def cycloidY (a t : ℝ) : ℝ := a * (1 - Real.cos t)

def speed (a t : ℝ) : ℝ :=
  Real.sqrt (deriv (cycloidX a) t ^ 2 + deriv (cycloidY a) t ^ 2)

def surfaceArea (a : ℝ) : ℝ :=
  2 * Real.pi * ∫ t in 0..(2 * Real.pi),
    cycloidX a t * speed a t

private theorem sin_double_half (t : ℝ) :
    Real.sin t = 2 * Real.sin (t / 2) * Real.cos (t / 2) := by
  calc
    Real.sin t = Real.sin (t / 2 + t / 2) := by congr 1 <;> ring
    _ = 2 * Real.sin (t / 2) * Real.cos (t / 2) := by
      rw [Real.sin_add]
      ring

private theorem cos_double_half (t : ℝ) :
    Real.cos t = Real.cos (t / 2) ^ 2 - Real.sin (t / 2) ^ 2 := by
  calc
    Real.cos t = Real.cos (t / 2 + t / 2) := by congr 1 <;> ring
    _ = Real.cos (t / 2) ^ 2 - Real.sin (t / 2) ^ 2 := by
      rw [Real.cos_add]
      ring

private theorem cycloidX_hasDerivAt (a t : ℝ) :
    HasDerivAt (cycloidX a) (a * (1 - Real.cos t)) t := by
  simpa [cycloidX] using
    (((hasDerivAt_id t).sub (Real.hasDerivAt_sin t)).const_mul a)

private theorem cycloidY_hasDerivAt (a t : ℝ) :
    HasDerivAt (cycloidY a) (a * Real.sin t) t := by
  simpa [cycloidY] using
    (((hasDerivAt_const (x := t) (c := (1 : ℝ))).sub
      (Real.hasDerivAt_cos t)).const_mul a)

private def cycloidAreaPrimitive (t : ℝ) : ℝ :=
  (-2) * (t * Real.cos (t / 2)) +
    3 * Real.sin (t / 2) +
    (1 / 3) * Real.sin (3 * t / 2)

private theorem cycloidAreaPrimitive_hasDerivAt (t : ℝ) :
    HasDerivAt cycloidAreaPrimitive
      ((t - Real.sin t) * Real.sin (t / 2)) t := by
  have hhalf : HasDerivAt (fun x : ℝ => x / 2) (1 / 2) t :=
    (hasDerivAt_id t).div_const 2
  have hsinHalf :
      HasDerivAt (fun x : ℝ => Real.sin (x / 2))
        (Real.cos (t / 2) * (1 / 2)) t := by
    simpa only [Function.comp_apply] using
      (Real.hasDerivAt_sin (t / 2)).comp t hhalf
  have hcosHalf :
      HasDerivAt (fun x : ℝ => Real.cos (x / 2))
        ((-Real.sin (t / 2)) * (1 / 2)) t := by
    simpa only [Function.comp_apply] using
      (Real.hasDerivAt_cos (t / 2)).comp t hhalf
  have hthree :
      HasDerivAt (fun x : ℝ => 3 * x / 2) (3 / 2) t := by
    simpa only [mul_one] using
      (((hasDerivAt_id t).const_mul 3).div_const 2)
  have hsinThree :
      HasDerivAt (fun x : ℝ => Real.sin (3 * x / 2))
        (Real.cos (3 * t / 2) * (3 / 2)) t := by
    simpa only [Function.comp_apply] using
      (Real.hasDerivAt_sin (3 * t / 2)).comp t hthree
  have hraw :
      HasDerivAt cycloidAreaPrimitive
        ((-2) * (Real.cos (t / 2) +
            t * ((-Real.sin (t / 2)) * (1 / 2))) +
          3 * (Real.cos (t / 2) * (1 / 2)) +
          (1 / 3) * (Real.cos (3 * t / 2) * (3 / 2))) t := by
    simpa only [cycloidAreaPrimitive, one_mul] using
      (((((hasDerivAt_id t).mul hcosHalf).const_mul (-2)).add
        (hsinHalf.const_mul 3)).add
        (hsinThree.const_mul (1 / 3)))
  have hsc : Real.sin (t / 2) ^ 2 + Real.cos (t / 2) ^ 2 = 1 :=
    Real.sin_sq_add_cos_sq (t / 2)
  have hcosThree :
      Real.cos (3 * t / 2) =
        (Real.cos (t / 2) ^ 2 - Real.sin (t / 2) ^ 2) *
            Real.cos (t / 2) -
          (2 * Real.sin (t / 2) * Real.cos (t / 2)) *
            Real.sin (t / 2) := by
    calc
      Real.cos (3 * t / 2) = Real.cos (t + t / 2) := by congr 1 <;> ring
      _ = Real.cos t * Real.cos (t / 2) -
          Real.sin t * Real.sin (t / 2) := by rw [Real.cos_add]
      _ = _ := by rw [cos_double_half t, sin_double_half t]
  have hz :
      Real.cos (3 * t / 2) - Real.cos (t / 2) +
          2 * Real.sin t * Real.sin (t / 2) = 0 := by
    calc
      Real.cos (3 * t / 2) - Real.cos (t / 2) +
          2 * Real.sin t * Real.sin (t / 2) =
          Real.cos (t / 2) *
            (Real.sin (t / 2) ^ 2 + Real.cos (t / 2) ^ 2 - 1) := by
              rw [hcosThree, sin_double_half t]
              ring
      _ = 0 := by rw [hsc]; ring
  have hdiff :
      Real.cos (3 * t / 2) - Real.cos (t / 2) =
        -2 * Real.sin t * Real.sin (t / 2) := by
    linarith
  convert hraw using 1 <;> nlinarith [hdiff]

private theorem cycloid_area_integral :
    (∫ t in 0..(2 * Real.pi),
      (t - Real.sin t) * Real.sin (t / 2)) = 4 * Real.pi := by
  have hcont : Continuous
      (fun t : ℝ => (t - Real.sin t) * Real.sin (t / 2)) := by
    simpa only [Function.comp_apply] using
      ((continuous_id.sub Real.continuous_sin).mul
        (Real.continuous_sin.comp (continuous_id.div_const 2)))
  have hzero : cycloidAreaPrimitive 0 = 0 := by
    simp [cycloidAreaPrimitive]
  have hhalf : (2 * Real.pi) / 2 = Real.pi := by ring
  have hthree :
      3 * (2 * Real.pi) / 2 = Real.pi + (Real.pi + Real.pi) := by ring
  have htwo : cycloidAreaPrimitive (2 * Real.pi) = 4 * Real.pi := by
    unfold cycloidAreaPrimitive
    rw [hthree, hhalf]
    simp [Real.sin_add, Real.cos_add]
    ring
  calc
    (∫ t in 0..(2 * Real.pi),
        (t - Real.sin t) * Real.sin (t / 2)) =
        cycloidAreaPrimitive (2 * Real.pi) - cycloidAreaPrimitive 0 :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun t _ => cycloidAreaPrimitive_hasDerivAt t)
        (hcont.intervalIntegrable 0 (2 * Real.pi))
    _ = 4 * Real.pi := by rw [htwo, hzero]; ring

theorem gap1 (a t : ℝ) :
    speed a t =
      Real.sqrt (deriv (cycloidX a) t ^ 2 + deriv (cycloidY a) t ^ 2) := by
  rfl

theorem gap2 (a t : ℝ) (ha : 0 ≤ a)
    (ht : t ∈ Set.Icc (0 : ℝ) (2 * Real.pi)) :
    speed a t = 2 * a * Real.sin (t / 2) := by
  unfold speed
  rw [(cycloidX_hasDerivAt a t).deriv,
    (cycloidY_hasDerivAt a t).deriv]
  have hsc : Real.sin (t / 2) ^ 2 + Real.cos (t / 2) ^ 2 = 1 :=
    Real.sin_sq_add_cos_sq (t / 2)
  have hone : 1 - Real.cos t = 2 * Real.sin (t / 2) ^ 2 := by
    rw [cos_double_half t]
    nlinarith
  have htrig :
      (1 - Real.cos t) ^ 2 + Real.sin t ^ 2 =
        4 * Real.sin (t / 2) ^ 2 := by
    rw [hone, sin_double_half t]
    calc
      (2 * Real.sin (t / 2) ^ 2) ^ 2 +
          (2 * Real.sin (t / 2) * Real.cos (t / 2)) ^ 2 =
          4 * Real.sin (t / 2) ^ 2 *
            (Real.sin (t / 2) ^ 2 + Real.cos (t / 2) ^ 2) := by ring
      _ = 4 * Real.sin (t / 2) ^ 2 := by rw [hsc]; ring
  have harg :
      (a * (1 - Real.cos t)) ^ 2 + (a * Real.sin t) ^ 2 =
        (2 * a * Real.sin (t / 2)) ^ 2 := by
    calc
      (a * (1 - Real.cos t)) ^ 2 + (a * Real.sin t) ^ 2 =
          a ^ 2 * ((1 - Real.cos t) ^ 2 + Real.sin t ^ 2) := by ring
      _ = a ^ 2 * (4 * Real.sin (t / 2) ^ 2) := by rw [htrig]
      _ = (2 * a * Real.sin (t / 2)) ^ 2 := by ring
  have hs : 0 ≤ Real.sin (t / 2) := by
    apply Real.sin_nonneg_of_nonneg_of_le_pi
    · linarith [ht.1]
    · linarith [ht.2]
  have hp : 0 ≤ 2 * a * Real.sin (t / 2) :=
    mul_nonneg (mul_nonneg (by linarith) ha) hs
  rw [harg, Real.sqrt_sq_eq_abs, abs_of_nonneg hp]

theorem gap3 (a : ℝ) (ha : 0 ≤ a) :
    ∀ t ∈ Set.Icc (0 : ℝ) (2 * Real.pi),
      speed a t = 2 * a * Real.sin (t / 2) := by
  intro t ht
  exact gap2 a t ha ht

theorem gap4 (a Pᵧ : ℝ) (ha : 0 ≤ a) (hP : Pᵧ = surfaceArea a) :
    Pᵧ = 2 * Real.pi * ∫ t in 0..(2 * Real.pi),
      a * (t - Real.sin t) * (2 * a * Real.sin (t / 2)) := by
  calc
    Pᵧ = surfaceArea a := hP
    _ = 2 * Real.pi * ∫ t in 0..(2 * Real.pi),
        a * (t - Real.sin t) * (2 * a * Real.sin (t / 2)) := by
      unfold surfaceArea
      apply congrArg (fun z : ℝ => 2 * Real.pi * z)
      apply intervalIntegral.integral_congr
      intro t ht
      have hab : (0 : ℝ) ≤ 2 * Real.pi :=
        mul_nonneg (by linarith) (le_of_lt Real.pi_pos)
      have ht' : t ∈ Set.Icc (0 : ℝ) (2 * Real.pi) := by
        simpa only [Set.uIcc_of_le hab] using ht
      simpa only [cycloidX] using
        congrArg (fun v : ℝ => cycloidX a t * v) (gap2 a t ha ht')

theorem gap5 (a : ℝ) :
    2 * Real.pi * (∫ t in 0..(2 * Real.pi),
      a * (t - Real.sin t) * (2 * a * Real.sin (t / 2))) =
        4 * Real.pi * a ^ 2 *
          ∫ t in 0..(2 * Real.pi),
            (t - Real.sin t) * Real.sin (t / 2) := by
  have hi :
      (∫ t in 0..(2 * Real.pi),
          a * (t - Real.sin t) * (2 * a * Real.sin (t / 2))) =
        ∫ t in 0..(2 * Real.pi),
          (2 * a ^ 2) * ((t - Real.sin t) * Real.sin (t / 2)) := by
    apply intervalIntegral.integral_congr
    intro t ht
    ring
  rw [hi, intervalIntegral.integral_const_mul]
  ring

theorem gap6 (a : ℝ) :
    4 * Real.pi * a ^ 2 *
        (∫ t in 0..(2 * Real.pi),
          (t - Real.sin t) * Real.sin (t / 2)) =
      16 * Real.pi ^ 2 * a ^ 2 := by
  rw [cycloid_area_integral]
  ring

theorem gap7 (a Pᵧ : ℝ) (ha : 0 ≤ a) (hP : Pᵧ = surfaceArea a) :
    Pᵧ = 16 * Real.pi ^ 2 * a ^ 2 := by
  calc
    Pᵧ = 2 * Real.pi * ∫ t in 0..(2 * Real.pi),
        a * (t - Real.sin t) * (2 * a * Real.sin (t / 2)) :=
      gap4 a Pᵧ ha hP
    _ = 4 * Real.pi * a ^ 2 *
        ∫ t in 0..(2 * Real.pi),
          (t - Real.sin t) * Real.sin (t / 2) := gap5 a
    _ = 16 * Real.pi ^ 2 * a ^ 2 := gap6 a

end

end ProofGap.Exercise2495_2
