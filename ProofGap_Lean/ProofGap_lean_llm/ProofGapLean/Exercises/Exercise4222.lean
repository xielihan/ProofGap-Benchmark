import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise4222

noncomputable section

open MeasureTheory
open scoped Interval

def cycloid (a t : ℝ) : ℝ × ℝ :=
  (a * (t - Real.sin t), a * (1 - Real.cos t))

def cycloidSpeed (a t : ℝ) : ℝ :=
  Real.sqrt
    ((deriv (fun s => (cycloid a s).1) t) ^ 2 +
      (deriv (fun s => (cycloid a s).2) t) ^ 2)

def weightedCurveIntegral (a : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..2 * Real.pi,
    ((cycloid a t).2) ^ 2 * cycloidSpeed a t

private lemma one_sub_cos_eq_two_sin_sq (x : ℝ) :
    1 - Real.cos x = 2 * (Real.sin (x / 2)) ^ 2 := by
  have hcos :
      Real.cos x = Real.cos (2 * (x / 2)) := by
    congr 1
    ring
  rw [hcos, Real.cos_two_mul]
  nlinarith [Real.sin_sq_add_cos_sq (x / 2)]

private lemma integral_sin_pow_five_half :
    (∫ x in (0 : ℝ)..Real.pi / 2, (Real.sin x) ^ 5) = (8 / 15 : ℝ) := by
  let F : ℝ → ℝ := fun x =>
    (-1 : ℝ) * Real.cos x +
      (2 / 3 : ℝ) * (Real.cos x) ^ 3 -
      (1 / 5 : ℝ) * (Real.cos x) ^ 5
  have hF : ∀ x : ℝ, HasDerivAt F ((Real.sin x) ^ 5) x := by
    intro x
    have h :=
      (((Real.hasDerivAt_cos x).const_mul (-1 : ℝ)).add
        (((Real.hasDerivAt_cos x).pow 3).const_mul (2 / 3 : ℝ))).sub
        (((Real.hasDerivAt_cos x).pow 5).const_mul (1 / 5 : ℝ))
    dsimp [F]
    convert h using 1
    norm_num
    have hsc : 1 - Real.cos x ^ 2 = Real.sin x ^ 2 := by
      nlinarith [Real.sin_sq_add_cos_sq x]
    have hmul :
        Real.sin x * (1 - Real.cos x ^ 2) ^ 2 = Real.sin x ^ 5 := by
      rw [hsc]
      ring
    ring_nf at hmul ⊢
    exact hmul.symm
  have hcont : Continuous (fun x : ℝ => (Real.sin x) ^ 5) :=
    Real.continuous_sin.pow 5
  calc
    (∫ x in (0 : ℝ)..Real.pi / 2, (Real.sin x) ^ 5) =
        F (Real.pi / 2) - F 0 :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun x _ => hF x) (hcont.intervalIntegrable _ _)
    _ = (8 / 15 : ℝ) := by
      dsimp [F]
      rw [Real.cos_pi_div_two, Real.cos_zero]
      norm_num

private lemma integral_sin_half_pow_five :
    (∫ x in (0 : ℝ)..2 * Real.pi, (Real.sin (x / 2)) ^ 5) =
      (32 / 15 : ℝ) := by
  let F : ℝ → ℝ := fun x =>
    (-2 : ℝ) * Real.cos (x / 2) +
      (4 / 3 : ℝ) * (Real.cos (x / 2)) ^ 3 -
      (2 / 5 : ℝ) * (Real.cos (x / 2)) ^ 5
  have hF : ∀ x : ℝ, HasDerivAt F ((Real.sin (x / 2)) ^ 5) x := by
    intro x
    have hc :
        HasDerivAt (fun y : ℝ => Real.cos (y / 2))
          (-Real.sin (x / 2) / 2) x := by
      convert ((hasDerivAt_id x).div_const 2).cos using 1
      all_goals simp only [id_eq]
      all_goals ring
    have h :=
      ((hc.const_mul (-2 : ℝ)).add
        ((hc.pow 3).const_mul (4 / 3 : ℝ))).sub
        ((hc.pow 5).const_mul (2 / 5 : ℝ))
    dsimp [F]
    convert h using 1
    norm_num
    have hsc :
        1 - Real.cos (x / 2) ^ 2 = Real.sin (x / 2) ^ 2 := by
      nlinarith [Real.sin_sq_add_cos_sq (x / 2)]
    have hmul :
        Real.sin (x / 2) * (1 - Real.cos (x / 2) ^ 2) ^ 2 =
          Real.sin (x / 2) ^ 5 := by
      rw [hsc]
      ring
    ring_nf at hmul ⊢
    exact hmul.symm
  have hcont : Continuous (fun x : ℝ => (Real.sin (x / 2)) ^ 5) :=
    (Real.continuous_sin.comp (continuous_id.div_const 2)).pow 5
  calc
    (∫ x in (0 : ℝ)..2 * Real.pi, (Real.sin (x / 2)) ^ 5) =
        F (2 * Real.pi) - F 0 :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun x _ => hF x) (hcont.intervalIntegrable _ _)
    _ = (32 / 15 : ℝ) := by
      have htwo : (2 * Real.pi : ℝ) / 2 = Real.pi := by ring
      have hzero : (0 : ℝ) / 2 = 0 := by norm_num
      dsimp [F]
      rw [htwo, hzero, Real.cos_pi, Real.cos_zero]
      norm_num

theorem gap1 (a t : ℝ) :
    cycloidSpeed a t =
      Real.sqrt
        ((deriv (fun s => (cycloid a s).1) t) ^ 2 +
          (deriv (fun s => (cycloid a s).2) t) ^ 2) := by
  rfl

theorem gap2 (a t : ℝ) :
    cycloidSpeed a t =
      Real.sqrt
        (a ^ 2 * (1 - Real.cos t) ^ 2 +
          a ^ 2 * (Real.sin t) ^ 2) := by
  have h1 :
      HasDerivAt (fun s : ℝ => a * (s - Real.sin s))
        (a * (1 - Real.cos t)) t := by
    convert
      (((hasDerivAt_id t).sub (Real.hasDerivAt_sin t)).const_mul a)
      using 1 <;> ring
  have h2 :
      HasDerivAt (fun s : ℝ => a * (1 - Real.cos s))
        (a * Real.sin t) t := by
    convert
      (((hasDerivAt_const t (1 : ℝ)).sub (Real.hasDerivAt_cos t)).const_mul a)
      using 1 <;> ring
  change
    Real.sqrt
        ((deriv (fun s : ℝ => a * (s - Real.sin s)) t) ^ 2 +
          (deriv (fun s : ℝ => a * (1 - Real.cos s)) t) ^ 2) = _
  rw [h1.deriv, h2.deriv]
  congr 1
  ring

theorem gap3
    (a t : ℝ) (ha : 0 < a)
    (ht : t ∈ Set.Icc (0 : ℝ) (2 * Real.pi)) :
    Real.sqrt
        (a ^ 2 * (1 - Real.cos t) ^ 2 +
          a ^ 2 * (Real.sin t) ^ 2) =
      2 * a * Real.sin (t / 2) := by
  have ht0 : 0 ≤ t / 2 := by
    nlinarith [ht.1]
  have htpi : t / 2 ≤ Real.pi := by
    nlinarith [ht.2]
  have hs : 0 ≤ Real.sin (t / 2) :=
    Real.sin_nonneg_of_nonneg_of_le_pi ht0 htpi
  have hsin :
      Real.sin t =
        2 * Real.sin (t / 2) * Real.cos (t / 2) := by
    calc
      Real.sin t = Real.sin (2 * (t / 2)) := by
        congr 1
        ring
      _ = 2 * Real.sin (t / 2) * Real.cos (t / 2) := by
        rw [Real.sin_two_mul]
  have htrig :
      (1 - Real.cos t) ^ 2 + (Real.sin t) ^ 2 =
        4 * (Real.sin (t / 2)) ^ 2 := by
    rw [one_sub_cos_eq_two_sin_sq, hsin]
    calc
      (2 * Real.sin (t / 2) ^ 2) ^ 2 +
          (2 * Real.sin (t / 2) * Real.cos (t / 2)) ^ 2 =
          4 * Real.sin (t / 2) ^ 2 *
            (Real.sin (t / 2) ^ 2 + Real.cos (t / 2) ^ 2) := by ring
      _ = 4 * Real.sin (t / 2) ^ 2 := by
        rw [Real.sin_sq_add_cos_sq, mul_one]
  have hrad :
      a ^ 2 * (1 - Real.cos t) ^ 2 +
          a ^ 2 * (Real.sin t) ^ 2 =
        (2 * a * Real.sin (t / 2)) ^ 2 := by
    calc
      a ^ 2 * (1 - Real.cos t) ^ 2 +
          a ^ 2 * (Real.sin t) ^ 2 =
          a ^ 2 * ((1 - Real.cos t) ^ 2 + (Real.sin t) ^ 2) := by ring
      _ = a ^ 2 * (4 * Real.sin (t / 2) ^ 2) := by rw [htrig]
      _ = (2 * a * Real.sin (t / 2)) ^ 2 := by ring
  have hrhs : 0 ≤ 2 * a * Real.sin (t / 2) := by
    positivity
  rw [hrad, Real.sqrt_sq hrhs]

theorem gap4
    (a t : ℝ) (ha : 0 < a)
    (ht : t ∈ Set.Icc (0 : ℝ) (2 * Real.pi)) :
    cycloidSpeed a t = 2 * a * Real.sin (t / 2) := by
  rw [gap2 a t, gap3 a t ha ht]

theorem gap5 (a : ℝ) (ha : 0 < a) :
    weightedCurveIntegral a =
      2 * a ^ 3 *
        ∫ t in (0 : ℝ)..2 * Real.pi,
          Real.sin (t / 2) * (1 - Real.cos t) ^ 2 := by
  unfold weightedCurveIntegral
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro t ht
  have hupper : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  rw [Set.uIcc_of_le hupper] at ht
  change
    (a * (1 - Real.cos t)) ^ 2 * cycloidSpeed a t =
      2 * a ^ 3 *
        (Real.sin (t / 2) * (1 - Real.cos t) ^ 2)
  rw [gap4 a t ha ht]
  ring

theorem gap6 (a : ℝ) :
    2 * a ^ 3 *
        (∫ t in (0 : ℝ)..2 * Real.pi,
          Real.sin (t / 2) * (1 - Real.cos t) ^ 2) =
      8 * a ^ 3 *
        ∫ t in (0 : ℝ)..2 * Real.pi,
          (Real.sin (t / 2)) ^ 5 := by
  have hi :
      (∫ t in (0 : ℝ)..2 * Real.pi,
          Real.sin (t / 2) * (1 - Real.cos t) ^ 2) =
        4 * ∫ t in (0 : ℝ)..2 * Real.pi,
          (Real.sin (t / 2)) ^ 5 := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t ht
    change
      Real.sin (t / 2) * (1 - Real.cos t) ^ 2 =
        4 * Real.sin (t / 2) ^ 5
    rw [one_sub_cos_eq_two_sin_sq]
    ring
  rw [hi]
  ring

theorem gap7 (a : ℝ) :
    8 * a ^ 3 *
        (∫ t in (0 : ℝ)..2 * Real.pi,
          (Real.sin (t / 2)) ^ 5) =
      32 * a ^ 3 *
        ∫ u in (0 : ℝ)..Real.pi / 2, (Real.sin u) ^ 5 := by
  rw [integral_sin_half_pow_five, integral_sin_pow_five_half]
  ring

theorem gap8 (a : ℝ) :
    32 * a ^ 3 *
        (∫ u in (0 : ℝ)..Real.pi / 2, (Real.sin u) ^ 5) =
      (256 / 15 : ℝ) * a ^ 3 := by
  rw [integral_sin_pow_five_half]
  ring

theorem gap9 (a : ℝ) (ha : 0 < a) :
    weightedCurveIntegral a = (256 / 15 : ℝ) * a ^ 3 := by
  rw [gap5 a ha, gap6 a, gap7 a, gap8 a]

end

end ProofGap.Exercise4222
