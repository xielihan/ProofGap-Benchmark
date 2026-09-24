import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Basic

namespace ProofGap.Exercise4252

noncomputable section

open scoped Interval

def curveMap (a b t : ℝ) : ℝ × ℝ :=
  (a * Real.cos t, b * Real.sin t)

def ellipse (a b : ℝ) : Set (ℝ × ℝ) :=
  {p | p.1 ^ 2 / a ^ 2 + p.2 ^ 2 / b ^ 2 = 1}

def curve (a b : ℝ) : Set (ℝ × ℝ) :=
  curveMap a b '' Set.Icc 0 (2 * Real.pi)

def lineIntegral (a b : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..2 * Real.pi,
    (a * Real.cos t + b * Real.sin t) * (-a * Real.sin t) +
      (a * Real.cos t - b * Real.sin t) * (b * Real.cos t)

theorem gap1 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    ellipse a b = curve a b := by
  have ha0 : a ≠ 0 := ne_of_gt ha
  have hb0 : b ≠ 0 := ne_of_gt hb
  ext p
  constructor
  · intro hp
    rcases p with ⟨x, y⟩
    change x ^ 2 / a ^ 2 + y ^ 2 / b ^ 2 = 1 at hp
    have hunit : (x / a) ^ 2 + (y / b) ^ 2 = 1 := by
      calc
        (x / a) ^ 2 + (y / b) ^ 2 =
            x ^ 2 / a ^ 2 + y ^ 2 / b ^ 2 := by
              field_simp [ha0, hb0]
        _ = 1 := hp
    have hxlow : -1 ≤ x / a := by
      nlinarith [sq_nonneg (x / a - 1), sq_nonneg (x / a + 1),
        sq_nonneg (y / b)]
    have hxhigh : x / a ≤ 1 := by
      nlinarith [sq_nonneg (x / a - 1), sq_nonneg (x / a + 1),
        sq_nonneg (y / b)]
    have har0 : 0 ≤ Real.arccos (x / a) := Real.arccos_nonneg _
    have harpi : Real.arccos (x / a) ≤ Real.pi := Real.arccos_le_pi _
    have hcos : Real.cos (Real.arccos (x / a)) = x / a :=
      Real.cos_arccos hxlow hxhigh
    have hsnonneg : 0 ≤ Real.sin (Real.arccos (x / a)) :=
      Real.sin_nonneg_of_nonneg_of_le_pi har0 harpi
    have htrig := Real.sin_sq_add_cos_sq (Real.arccos (x / a))
    rw [hcos] at htrig
    change ∃ t ∈ Set.Icc (0 : ℝ) (2 * Real.pi),
      curveMap a b t = (x, y)
    by_cases hy0 : 0 ≤ y / b
    · have hsin : Real.sin (Real.arccos (x / a)) = y / b := by
        nlinarith
      refine ⟨Real.arccos (x / a), ⟨har0, ?_⟩, ?_⟩
      · nlinarith [Real.pi_pos]
      · change
          (a * Real.cos (Real.arccos (x / a)),
            b * Real.sin (Real.arccos (x / a))) = (x, y)
        rw [hcos, hsin]
        apply Prod.ext
        · field_simp [ha0]
        · field_simp [hb0]
    · have hyneg : y / b < 0 := lt_of_not_ge hy0
      have hminus : -Real.sin (Real.arccos (x / a)) = y / b := by
        nlinarith
      have hcosT :
          Real.cos (2 * Real.pi - Real.arccos (x / a)) = x / a := by
        rw [Real.cos_sub, Real.cos_two_pi, Real.sin_two_pi, hcos]
        ring
      have hsinT :
          Real.sin (2 * Real.pi - Real.arccos (x / a)) = y / b := by
        rw [Real.sin_sub, Real.sin_two_pi, Real.cos_two_pi]
        simpa using hminus
      refine ⟨2 * Real.pi - Real.arccos (x / a), ⟨?_, ?_⟩, ?_⟩
      · nlinarith [Real.pi_pos]
      · nlinarith
      · change
          (a * Real.cos (2 * Real.pi - Real.arccos (x / a)),
            b * Real.sin (2 * Real.pi - Real.arccos (x / a))) = (x, y)
        rw [hcosT, hsinT]
        apply Prod.ext
        · field_simp [ha0]
        · field_simp [hb0]
  · intro hp
    change ∃ t ∈ Set.Icc (0 : ℝ) (2 * Real.pi),
      curveMap a b t = p at hp
    rcases hp with ⟨t, ht, rfl⟩
    change
      (a * Real.cos t) ^ 2 / a ^ 2 +
          (b * Real.sin t) ^ 2 / b ^ 2 = 1
    have hc : (a * Real.cos t) ^ 2 / a ^ 2 = Real.cos t ^ 2 := by
      field_simp [ha0]
    have hs : (b * Real.sin t) ^ 2 / b ^ 2 = Real.sin t ^ 2 := by
      field_simp [hb0]
    rw [hc, hs]
    nlinarith [Real.sin_sq_add_cos_sq t]

theorem gap2 (a b : ℝ) :
    lineIntegral a b =
      ∫ t in (0 : ℝ)..2 * Real.pi,
        (a * Real.cos t + b * Real.sin t) * (-a * Real.sin t) +
          (a * Real.cos t - b * Real.sin t) * (b * Real.cos t) := by
  rfl

theorem gap3 (a b : ℝ) :
    (∫ t in (0 : ℝ)..2 * Real.pi,
        (a * Real.cos t + b * Real.sin t) * (-a * Real.sin t) +
          (a * Real.cos t - b * Real.sin t) * (b * Real.cos t)) =
      ∫ t in (0 : ℝ)..2 * Real.pi,
        a * b * Real.cos (2 * t) -
          (a ^ 2 + b ^ 2) / 2 * Real.sin (2 * t) := by
  apply intervalIntegral.integral_congr
  intro t ht
  dsimp
  rw [Real.cos_two_mul, Real.sin_two_mul]
  have hcosdiff :
      Real.cos t ^ 2 - Real.sin t ^ 2 = 2 * Real.cos t ^ 2 - 1 := by
    nlinarith [Real.sin_sq_add_cos_sq t]
  calc
    (a * Real.cos t + b * Real.sin t) * (-a * Real.sin t) +
        (a * Real.cos t - b * Real.sin t) * (b * Real.cos t) =
        a * b * (Real.cos t ^ 2 - Real.sin t ^ 2) -
          (a ^ 2 + b ^ 2) * (Real.sin t * Real.cos t) := by
            ring
    _ = a * b * (2 * Real.cos t ^ 2 - 1) -
          (a ^ 2 + b ^ 2) / 2 * (2 * Real.sin t * Real.cos t) := by
            rw [hcosdiff]
            ring

theorem gap4 (a b : ℝ) :
    (∫ t in (0 : ℝ)..2 * Real.pi,
      a * b * Real.cos (2 * t) -
        (a ^ 2 + b ^ 2) / 2 * Real.sin (2 * t)) = 0 := by
  let F : ℝ → ℝ := fun t =>
    a * b / 2 * Real.sin (2 * t) +
      (a ^ 2 + b ^ 2) / 4 * Real.cos (2 * t)
  have htwo (t : ℝ) : HasDerivAt (fun x : ℝ => 2 * x) 2 t := by
    simpa using (hasDerivAt_id t).const_mul 2
  have hF (t : ℝ) :
      HasDerivAt F
        (a * b * Real.cos (2 * t) -
          (a ^ 2 + b ^ 2) / 2 * Real.sin (2 * t)) t := by
    have hsin :
        HasDerivAt (fun x : ℝ => Real.sin (2 * x))
          (2 * Real.cos (2 * t)) t := by
      convert (Real.hasDerivAt_sin (2 * t)).comp t (htwo t) using 1 <;> ring
    have hcos :
        HasDerivAt (fun x : ℝ => Real.cos (2 * x))
          (-2 * Real.sin (2 * t)) t := by
      convert (Real.hasDerivAt_cos (2 * t)).comp t (htwo t) using 1 <;> ring
    dsimp [F]
    convert
      (hsin.const_mul (a * b / 2)).add
        (hcos.const_mul ((a ^ 2 + b ^ 2) / 4)) using 1 <;> ring
  have htwo_cont : Continuous (fun t : ℝ => 2 * t) :=
    continuous_const.mul continuous_id
  have hcos_cont :
      Continuous (fun t : ℝ => a * b * Real.cos (2 * t)) :=
    continuous_const.mul (Real.continuous_cos.comp htwo_cont)
  have hsin_cont :
      Continuous
        (fun t : ℝ => (a ^ 2 + b ^ 2) / 2 * Real.sin (2 * t)) :=
    continuous_const.mul (Real.continuous_sin.comp htwo_cont)
  have hint : IntervalIntegrable
      (fun t : ℝ => a * b * Real.cos (2 * t) -
        (a ^ 2 + b ^ 2) / 2 * Real.sin (2 * t))
      MeasureTheory.volume 0 (2 * Real.pi) :=
    (hcos_cont.sub hsin_cont).intervalIntegrable 0 (2 * Real.pi)
  calc
    (∫ t in (0 : ℝ)..2 * Real.pi,
        a * b * Real.cos (2 * t) -
          (a ^ 2 + b ^ 2) / 2 * Real.sin (2 * t)) =
        F (2 * Real.pi) - F 0 := by
          exact intervalIntegral.integral_eq_sub_of_hasDerivAt
            (fun t _ => hF t) hint
    _ = 0 := by
      dsimp [F]
      rw [show 2 * (2 * Real.pi) = 2 * Real.pi + 2 * Real.pi by ring]
      rw [Real.sin_add_two_pi, Real.cos_add_two_pi]
      simp

theorem gap5 (a b : ℝ) :
    lineIntegral a b = 0 := by
  rw [gap2 a b, gap3 a b, gap4 a b]

end

end ProofGap.Exercise4252
