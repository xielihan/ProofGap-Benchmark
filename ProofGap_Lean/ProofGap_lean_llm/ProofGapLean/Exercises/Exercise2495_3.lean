import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

open scoped Interval

namespace ProofGap.Exercise2495_3

noncomputable section

def cycloidX (a t : ℝ) : ℝ := a * (t - Real.sin t)

def cycloidY (a t : ℝ) : ℝ := a * (1 - Real.cos t)

def shiftedY (a t : ℝ) : ℝ := cycloidY a t - 2 * a

def speed (a t : ℝ) : ℝ :=
  Real.sqrt (deriv (cycloidX a) t ^ 2 + deriv (cycloidY a) t ^ 2)

def surfaceArea (a : ℝ) : ℝ :=
  |2 * Real.pi * ∫ t in 0..(2 * Real.pi),
    shiftedY a t * speed a t|

theorem gap1 (a t : ℝ) :
    speed a t =
      Real.sqrt (deriv (cycloidX a) t ^ 2 + deriv (cycloidY a) t ^ 2) := by
  rfl

theorem gap2 (a t : ℝ) (ha : 0 ≤ a)
    (ht : t ∈ Set.Icc (0 : ℝ) (2 * Real.pi)) :
    speed a t = 2 * a * Real.sin (t / 2) := by
  have hx :
      HasDerivAt (cycloidX a) (a * (1 - Real.cos t)) t := by
    simpa [cycloidX] using
      ((hasDerivAt_id t).sub (Real.hasDerivAt_sin t)).const_mul a
  have hy :
      HasDerivAt (cycloidY a) (a * Real.sin t) t := by
    simpa [cycloidY] using
      ((hasDerivAt_const (x := t) (c := (1 : ℝ))).sub
        (Real.hasDerivAt_cos t)).const_mul a
  have hdouble (u : ℝ) :
      (1 - Real.cos (2 * u)) ^ 2 + Real.sin (2 * u) ^ 2 =
        (2 * Real.sin u) ^ 2 := by
    rw [Real.sin_two_mul, Real.cos_two_mul]
    calc
      (1 - (2 * Real.cos u ^ 2 - 1)) ^ 2 +
          (2 * Real.sin u * Real.cos u) ^ 2 =
          (2 * Real.sin u) ^ 2 +
            4 * (Real.cos u ^ 2 - 1) *
              (Real.sin u ^ 2 + Real.cos u ^ 2 - 1) := by ring
      _ = (2 * Real.sin u) ^ 2 := by
        rw [Real.sin_sq_add_cos_sq]
        ring
  have htrig :
      (1 - Real.cos t) ^ 2 + Real.sin t ^ 2 =
        (2 * Real.sin (t / 2)) ^ 2 := by
    convert hdouble (t / 2) using 1 <;> ring
  have hinside :
      (a * (1 - Real.cos t)) ^ 2 + (a * Real.sin t) ^ 2 =
        (2 * a * Real.sin (t / 2)) ^ 2 := by
    calc
      (a * (1 - Real.cos t)) ^ 2 + (a * Real.sin t) ^ 2 =
          a ^ 2 * ((1 - Real.cos t) ^ 2 + Real.sin t ^ 2) := by ring
      _ = a ^ 2 * (2 * Real.sin (t / 2)) ^ 2 := by rw [htrig]
      _ = (2 * a * Real.sin (t / 2)) ^ 2 := by ring
  have ht0 : 0 ≤ t / 2 := by
    linarith [ht.1]
  have htpi : t / 2 ≤ Real.pi := by
    linarith [ht.2]
  have hs : 0 ≤ Real.sin (t / 2) :=
    Real.sin_nonneg_of_nonneg_of_le_pi ht0 htpi
  have hnonneg : 0 ≤ 2 * a * Real.sin (t / 2) :=
    mul_nonneg (mul_nonneg (by norm_num) ha) hs
  unfold speed
  rw [hx.deriv, hy.deriv, hinside, Real.sqrt_sq_eq_abs,
    abs_of_nonneg hnonneg]

theorem gap3 (a : ℝ) (ha : 0 ≤ a) :
    ∀ t ∈ Set.Icc (0 : ℝ) (2 * Real.pi),
      speed a t = 2 * a * Real.sin (t / 2) := by
  intro t ht
  exact gap2 a t ha ht

theorem gap4 (a t : ℝ) :
    shiftedY a t = -a * (1 + Real.cos t) := by
  unfold shiftedY cycloidY
  ring

theorem gap5 (a P : ℝ) (ha : 0 ≤ a) (hP : P = surfaceArea a) :
    P = |2 * Real.pi * ∫ t in 0..(2 * Real.pi),
      (-a * (1 + Real.cos t)) * (2 * a * Real.sin (t / 2))| := by
  rw [hP, surfaceArea]
  apply congrArg abs
  apply congrArg (fun z : ℝ => 2 * Real.pi * z)
  apply intervalIntegral.integral_congr
  intro t ht
  have hle : (0 : ℝ) ≤ 2 * Real.pi :=
    mul_nonneg (by norm_num) Real.pi_pos.le
  rw [Set.uIcc_of_le hle] at ht
  change shiftedY a t * speed a t =
    (-a * (1 + Real.cos t)) * (2 * a * Real.sin (t / 2))
  rw [gap4 a t, gap2 a t ha ht]

theorem gap6 (a : ℝ) :
    |2 * Real.pi * ∫ t in 0..(2 * Real.pi),
      (-a * (1 + Real.cos t)) * (2 * a * Real.sin (t / 2))| =
        32 / 3 * Real.pi * a ^ 2 := by
  let F : ℝ → ℝ := fun t =>
    (8 / 3) * a ^ 2 * Real.cos (t / 2) ^ 3
  have hderiv (t : ℝ) :
      HasDerivAt F
        ((-a * (1 + Real.cos t)) *
          (2 * a * Real.sin (t / 2))) t := by
    have hhalf :
        HasDerivAt (fun x : ℝ => x / 2) (1 / 2) t := by
      simpa using (hasDerivAt_id t).div_const 2
    have hcos :
        HasDerivAt (fun x : ℝ => Real.cos (x / 2))
          (-Real.sin (t / 2) * (1 / 2)) t := by
      exact (Real.hasDerivAt_cos (t / 2)).comp t hhalf
    have hraw :
        HasDerivAt F
          (-4 * a ^ 2 * Real.cos (t / 2) ^ 2 * Real.sin (t / 2)) t := by
      dsimp [F]
      convert (hcos.pow 3).const_mul ((8 / 3) * a ^ 2) using 1 <;>
        norm_num <;> ring
    have hcos2general (u : ℝ) :
        1 + Real.cos (2 * u) = 2 * Real.cos u ^ 2 := by
      rw [Real.cos_two_mul]
      ring
    have hcos2 :
        1 + Real.cos t = 2 * Real.cos (t / 2) ^ 2 := by
      convert hcos2general (t / 2) using 1 <;> ring
    convert hraw using 1
    rw [hcos2]
    ring
  have hhalf_cont : Continuous (fun t : ℝ => t / 2) :=
    continuous_id.div_const 2
  have hsinhalf : Continuous (fun t : ℝ => Real.sin (t / 2)) :=
    Real.continuous_sin.comp hhalf_cont
  have hleft : Continuous (fun t : ℝ => -a * (1 + Real.cos t)) :=
    continuous_const.mul (continuous_const.add Real.continuous_cos)
  have hright : Continuous (fun t : ℝ => 2 * a * Real.sin (t / 2)) :=
    continuous_const.mul hsinhalf
  have hcont : Continuous (fun t : ℝ =>
      (-a * (1 + Real.cos t)) * (2 * a * Real.sin (t / 2))) :=
    hleft.mul hright
  have hinterval :
      IntervalIntegrable
        (fun t : ℝ =>
          (-a * (1 + Real.cos t)) * (2 * a * Real.sin (t / 2)))
        MeasureTheory.volume 0 (2 * Real.pi) :=
    hcont.intervalIntegrable 0 (2 * Real.pi)
  have hint :
      (∫ t in 0..(2 * Real.pi),
        (-a * (1 + Real.cos t)) * (2 * a * Real.sin (t / 2))) =
        F (2 * Real.pi) - F 0 := by
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t _ => hderiv t) hinterval
  have hF :
      F (2 * Real.pi) - F 0 = -(16 / 3) * a ^ 2 := by
    dsimp [F]
    rw [show (2 * Real.pi) / 2 = Real.pi by ring,
      Real.cos_pi, show (0 : ℝ) / 2 = 0 by norm_num, Real.cos_zero]
    ring
  have hnonpos :
      2 * Real.pi * (-(16 / 3) * a ^ 2) ≤ 0 := by
    exact mul_nonpos_of_nonneg_of_nonpos
      (mul_nonneg (by norm_num) Real.pi_pos.le)
      (mul_nonpos_of_nonpos_of_nonneg (by norm_num) (sq_nonneg a))
  rw [hint, hF, abs_of_nonpos hnonpos]
  ring

theorem gap7 (a P : ℝ) (ha : 0 ≤ a) (hP : P = surfaceArea a) :
    P = 32 / 3 * Real.pi * a ^ 2 := by
  calc
    P = |2 * Real.pi * ∫ t in 0..(2 * Real.pi),
        (-a * (1 + Real.cos t)) *
          (2 * a * Real.sin (t / 2))| := gap5 a P ha hP
    _ = 32 / 3 * Real.pi * a ^ 2 := gap6 a

end

end ProofGap.Exercise2495_3
