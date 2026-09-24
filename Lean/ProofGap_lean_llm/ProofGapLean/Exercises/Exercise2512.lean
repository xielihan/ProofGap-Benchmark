import ProofGapLean.Prelude.Analysis
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Tactic.Positivity

open scoped Interval

namespace ProofGap.Exercise2512

noncomputable section

def cardioidRadius (a φ : ℝ) : ℝ := a * (1 + Real.cos φ)
def cartesianCentroidX (x y : ℝ → ℝ) : ℝ :=
  (∫ t in 0..Real.pi, t * y t) / (∫ t in 0..Real.pi, y t)
def polarCentroidX (r : ℝ → ℝ) : ℝ :=
  (2 / 3 : ℝ) *
    (∫ φ in 0..Real.pi, r φ * Real.cos φ * (1 / 2) * r φ ^ 2) /
      (∫ φ in 0..Real.pi, (1 / 2) * r φ ^ 2)

private lemma cancel_common_factor (c x y : ℝ) (hc : c ≠ 0) :
    (c * x) / (c * y) = x / y := by
  by_cases hy : y = 0
  · simp [hy]
  · field_simp [hc, hy]

private lemma cardioid_den_integral :
    (∫ x in 0..Real.pi,
      1 + 2 * Real.cos x + Real.cos x ^ 2) =
      3 * Real.pi / 2 := by
  let F : ℝ → ℝ := fun x =>
    3 * x / 2 + (2 * Real.sin x + Real.sin x * Real.cos x / 2)
  have hF : ∀ x : ℝ,
      HasDerivAt F (1 + 2 * Real.cos x + Real.cos x ^ 2) x := by
    intro x
    have hraw :=
      (((hasDerivAt_id x).const_mul 3).div_const 2).add
        (((Real.hasDerivAt_sin x).const_mul 2).add
          (((Real.hasDerivAt_sin x).mul
            (Real.hasDerivAt_cos x)).div_const 2))
    convert hraw using 1 <;>
      dsimp [F] <;>
      nlinarith [Real.sin_sq_add_cos_sq x]
  have hint : IntervalIntegrable
      (fun x : ℝ => 1 + 2 * Real.cos x + Real.cos x ^ 2)
      MeasureTheory.volume 0 Real.pi :=
    ((continuous_const.add
      (continuous_const.mul Real.continuous_cos)).add
      (Real.continuous_cos.pow 2)).intervalIntegrable 0 Real.pi
  calc
    (∫ x in 0..Real.pi,
      1 + 2 * Real.cos x + Real.cos x ^ 2) =
        F Real.pi - F 0 :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun x hx => hF x) hint
    _ = 3 * Real.pi / 2 := by
      simp [F]

private lemma cardioid_num_integral :
    (∫ x in 0..Real.pi,
      (1 + 3 * Real.cos x + 3 * Real.cos x ^ 2 +
        Real.cos x ^ 3) * Real.cos x) =
      15 * Real.pi / 8 := by
  let F : ℝ → ℝ := fun x =>
    (((4 * Real.sin x - Real.sin x ^ 3) + 15 * x / 8) +
      2 * (Real.sin x * Real.cos x)) +
      (Real.sin x * Real.cos x *
        (Real.cos x ^ 2 - Real.sin x ^ 2)) / 8
  have hF : ∀ x : ℝ,
      HasDerivAt F
        ((1 + 3 * Real.cos x + 3 * Real.cos x ^ 2 +
          Real.cos x ^ 3) * Real.cos x) x := by
    intro x
    have hs := Real.hasDerivAt_sin x
    have hc := Real.hasDerivAt_cos x
    have hraw :=
      ((((hs.const_mul 4).sub (hs.pow 3)).add
          (((hasDerivAt_id x).const_mul 15).div_const 8)).add
        ((hs.mul hc).const_mul 2)).add
        (((hs.mul hc).mul ((hc.pow 2).sub (hs.pow 2))).div_const 8)
    have htrig := Real.sin_sq_add_cos_sq x
    have htrig_cos :=
      congrArg (fun z : ℝ => z * Real.cos x) htrig
    have htrig_sq := congrArg (fun z : ℝ => z ^ 2) htrig
    convert hraw using 1 <;>
      dsimp [F] <;>
      ring_nf at * <;>
      nlinarith [htrig, htrig_cos, htrig_sq]
  have hint : IntervalIntegrable
      (fun x : ℝ =>
        (1 + 3 * Real.cos x + 3 * Real.cos x ^ 2 +
          Real.cos x ^ 3) * Real.cos x)
      MeasureTheory.volume 0 Real.pi :=
    ((((continuous_const.add
      (continuous_const.mul Real.continuous_cos)).add
      (continuous_const.mul (Real.continuous_cos.pow 2))).add
      (Real.continuous_cos.pow 3)).mul
      Real.continuous_cos).intervalIntegrable 0 Real.pi
  calc
    (∫ x in 0..Real.pi,
      (1 + 3 * Real.cos x + 3 * Real.cos x ^ 2 +
        Real.cos x ^ 3) * Real.cos x) =
        F Real.pi - F 0 :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun x hx => hF x) hint
    _ = 15 * Real.pi / 8 := by
      simp [F]

theorem gap1 (η : ℝ) (hη : η = 0) : η = 0 := by
  exact hη

theorem gap2 (x y : ℝ → ℝ) (ξ : ℝ)
    (hξ : ξ = cartesianCentroidX x y) :
    ξ = (∫ t in 0..Real.pi, t * y t) /
      (∫ t in 0..Real.pi, y t) := by
  simpa [cartesianCentroidX] using hξ

theorem gap3 (a : ℝ) (x y : ℝ → ℝ)
    (hChangeOfCoordinates :
      cartesianCentroidX x y =
        polarCentroidX (cardioidRadius a)) :
    cartesianCentroidX x y =
      polarCentroidX (cardioidRadius a) := by
  exact hChangeOfCoordinates

theorem gap4 (a ξ : ℝ) (x y : ℝ → ℝ)
    (hξ : ξ = cartesianCentroidX x y)
    (hChangeOfCoordinates :
      cartesianCentroidX x y =
        polarCentroidX (cardioidRadius a)) :
    ξ = polarCentroidX (cardioidRadius a) := by
  calc
    ξ = cartesianCentroidX x y := hξ
    _ = polarCentroidX (cardioidRadius a) := hChangeOfCoordinates

theorem gap5 (a ξ : ℝ) (hξ : ξ = polarCentroidX (cardioidRadius a)) :
    ξ = (2 / 3 : ℝ) *
      (∫ φ in 0..Real.pi,
        a ^ 3 * (1 + Real.cos φ) ^ 3 * Real.cos φ) /
      (∫ φ in 0..Real.pi, a ^ 2 * (1 + Real.cos φ) ^ 2) := by
  rw [hξ]
  unfold polarCentroidX cardioidRadius
  have hn :
      (∫ φ in 0..Real.pi,
        (a * (1 + Real.cos φ)) * Real.cos φ * (1 / 2) *
          (a * (1 + Real.cos φ)) ^ 2) =
        (1 / 2) *
          (∫ φ in 0..Real.pi,
            a ^ 3 * (1 + Real.cos φ) ^ 3 * Real.cos φ) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro φ hφ
    ring
  have hd :
      (∫ φ in 0..Real.pi,
        (1 / 2) * (a * (1 + Real.cos φ)) ^ 2) =
        (1 / 2) *
          (∫ φ in 0..Real.pi,
            a ^ 2 * (1 + Real.cos φ) ^ 2) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro φ hφ
    ring
  rw [hn, hd]
  calc
    (2 / 3 : ℝ) *
          ((1 / 2) *
            (∫ φ in 0..Real.pi,
              a ^ 3 * (1 + Real.cos φ) ^ 3 * Real.cos φ)) /
        ((1 / 2) *
          (∫ φ in 0..Real.pi,
            a ^ 2 * (1 + Real.cos φ) ^ 2)) =
      (1 / 2) *
          ((2 / 3 : ℝ) *
            (∫ φ in 0..Real.pi,
              a ^ 3 * (1 + Real.cos φ) ^ 3 * Real.cos φ)) /
        ((1 / 2) *
          (∫ φ in 0..Real.pi,
            a ^ 2 * (1 + Real.cos φ) ^ 2)) := by ring
    _ = (2 / 3 : ℝ) *
          (∫ φ in 0..Real.pi,
            a ^ 3 * (1 + Real.cos φ) ^ 3 * Real.cos φ) /
        (∫ φ in 0..Real.pi,
          a ^ 2 * (1 + Real.cos φ) ^ 2) := by
      apply cancel_common_factor
      norm_num

theorem gap6 (a ξ : ℝ) (ha : a ≠ 0)
    (hξ : ξ = polarCentroidX (cardioidRadius a)) :
    ξ = 2 * a / 3 *
      (∫ φ in 0..Real.pi,
        (1 + 3 * Real.cos φ + 3 * Real.cos φ ^ 2 +
          Real.cos φ ^ 3) * Real.cos φ) /
      (∫ φ in 0..Real.pi,
        1 + 2 * Real.cos φ + Real.cos φ ^ 2) := by
  rw [gap5 a ξ hξ]
  have hn :
      (∫ φ in 0..Real.pi,
        a ^ 3 * (1 + Real.cos φ) ^ 3 * Real.cos φ) =
        a ^ 3 *
          (∫ φ in 0..Real.pi,
            (1 + 3 * Real.cos φ + 3 * Real.cos φ ^ 2 +
              Real.cos φ ^ 3) * Real.cos φ) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro φ hφ
    ring
  have hd :
      (∫ φ in 0..Real.pi,
        a ^ 2 * (1 + Real.cos φ) ^ 2) =
        a ^ 2 *
          (∫ φ in 0..Real.pi,
            1 + 2 * Real.cos φ + Real.cos φ ^ 2) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro φ hφ
    ring
  rw [hn, hd]
  calc
    (2 / 3 : ℝ) *
          (a ^ 3 *
            (∫ φ in 0..Real.pi,
              (1 + 3 * Real.cos φ + 3 * Real.cos φ ^ 2 +
                Real.cos φ ^ 3) * Real.cos φ)) /
        (a ^ 2 *
          (∫ φ in 0..Real.pi,
            1 + 2 * Real.cos φ + Real.cos φ ^ 2)) =
      a ^ 2 *
          ((2 * a / 3) *
            (∫ φ in 0..Real.pi,
              (1 + 3 * Real.cos φ + 3 * Real.cos φ ^ 2 +
                Real.cos φ ^ 3) * Real.cos φ)) /
        (a ^ 2 *
          (∫ φ in 0..Real.pi,
            1 + 2 * Real.cos φ + Real.cos φ ^ 2)) := by ring
    _ = 2 * a / 3 *
          (∫ φ in 0..Real.pi,
            (1 + 3 * Real.cos φ + 3 * Real.cos φ ^ 2 +
              Real.cos φ ^ 3) * Real.cos φ) /
        (∫ φ in 0..Real.pi,
          1 + 2 * Real.cos φ + Real.cos φ ^ 2) := by
      apply cancel_common_factor
      exact pow_ne_zero 2 ha

theorem gap7 (a : ℝ) :
    2 * a / 3 *
      (∫ φ in 0..Real.pi,
        (1 + 3 * Real.cos φ + 3 * Real.cos φ ^ 2 +
          Real.cos φ ^ 3) * Real.cos φ) /
      (∫ φ in 0..Real.pi,
        1 + 2 * Real.cos φ + Real.cos φ ^ 2) =
      5 * a / 6 := by
  rw [cardioid_num_integral, cardioid_den_integral]
  field_simp [ne_of_gt Real.pi_pos]
  ring

theorem gap8 (a ξ : ℝ)
    (hξ : ξ = 2 * a / 3 *
      (∫ φ in 0..Real.pi,
        (1 + 3 * Real.cos φ + 3 * Real.cos φ ^ 2 +
          Real.cos φ ^ 3) * Real.cos φ) /
      (∫ φ in 0..Real.pi,
        1 + 2 * Real.cos φ + Real.cos φ ^ 2)) :
    ξ = 5 * a / 6 := by
  calc
    ξ = 2 * a / 3 *
        (∫ φ in 0..Real.pi,
          (1 + 3 * Real.cos φ + 3 * Real.cos φ ^ 2 +
            Real.cos φ ^ 3) * Real.cos φ) /
        (∫ φ in 0..Real.pi,
          1 + 2 * Real.cos φ + Real.cos φ ^ 2) := hξ
    _ = 5 * a / 6 := gap7 a

theorem gap9 (a ξ η φ₀ : ℝ) (ha : 0 < a)
    (hξ : ξ = 5 * a / 6) (hη : η = 0)
    (hφ₀ : φ₀ = Real.arctan (η / ξ)) :
    φ₀ = 0 := by
  rw [hη, zero_div, Real.arctan_zero] at hφ₀
  exact hφ₀

theorem gap10 (a ξ η r₀ : ℝ) (ha : 0 < a)
    (hξ : ξ = 5 * a / 6) (hη : η = 0)
    (hr : r₀ = Real.sqrt (ξ ^ 2 + η ^ 2)) :
    r₀ = 5 * a / 6 := by
  calc
    r₀ = Real.sqrt (ξ ^ 2 + η ^ 2) := hr
    _ = Real.sqrt ((5 * a / 6) ^ 2) := by rw [hξ, hη]; norm_num
    _ = 5 * a / 6 := Real.sqrt_sq (by positivity)

end

end ProofGap.Exercise2512
