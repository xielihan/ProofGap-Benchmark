import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise4254

noncomputable section

open scoped Interval

def curveMap (a t : ℝ) : ℝ × ℝ :=
  (a * Real.cos t, a * Real.sin t)

def circle (a : ℝ) : Set (ℝ × ℝ) :=
  {p | p.1 ^ 2 + p.2 ^ 2 = a ^ 2}

def curve (a : ℝ) : Set (ℝ × ℝ) :=
  curveMap a '' Set.Icc 0 (2 * Real.pi)

def lineIntegral (a : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..2 * Real.pi,
    (-(a * Real.cos t + a * Real.sin t) * a * Real.sin t -
      (a * Real.cos t - a * Real.sin t) * a * Real.cos t) / a ^ 2

theorem gap1 (a : ℝ) (ha : 0 < a) :
    circle a = curve a := by
  ext p
  rcases p with ⟨x, y⟩
  constructor
  · intro hxy
    change x ^ 2 + y ^ 2 = a ^ 2 at hxy
    have hx_sq : x ^ 2 ≤ a ^ 2 := by
      nlinarith [sq_nonneg y]
    have hxa : -a ≤ x := by
      nlinarith [sq_nonneg (x + a)]
    have hxb : x ≤ a := by
      nlinarith [sq_nonneg (x - a)]
    have hzlow : -1 ≤ x / a := by
      apply (le_div_iff₀ ha).2
      nlinarith
    have hzup : x / a ≤ 1 := by
      apply (div_le_iff₀ ha).2
      nlinarith
    let u := Real.arccos (x / a)
    have hu : u ∈ Set.Icc 0 Real.pi := by
      exact ⟨Real.arccos_nonneg _, Real.arccos_le_pi _⟩
    have hxu : a * Real.cos u = x := by
      dsimp [u]
      rw [Real.cos_arccos hzlow hzup]
      field_simp [ha.ne']
    have hsin : 0 ≤ Real.sin u :=
      Real.sin_nonneg_of_nonneg_of_le_pi hu.1 hu.2
    have hsnonneg : 0 ≤ a * Real.sin u :=
      mul_nonneg (le_of_lt ha) hsin
    have hcircle_u :
        (a * Real.cos u) ^ 2 + (a * Real.sin u) ^ 2 = a ^ 2 := by
      calc
        (a * Real.cos u) ^ 2 + (a * Real.sin u) ^ 2 =
            a ^ 2 * (Real.sin u ^ 2 + Real.cos u ^ 2) := by ring
        _ = a ^ 2 := by rw [Real.sin_sq_add_cos_sq]; ring
    have hcircle_u' : x ^ 2 + (a * Real.sin u) ^ 2 = a ^ 2 := by
      simpa only [hxu] using hcircle_u
    have hsq : (a * Real.sin u) ^ 2 = y ^ 2 := by
      nlinarith [hxy, hcircle_u']
    change (x, y) ∈ curveMap a '' Set.Icc 0 (2 * Real.pi)
    by_cases hy : 0 ≤ y
    · have hsy : a * Real.sin u = y := by
        nlinarith
      refine ⟨u, ⟨hu.1, ?_⟩, ?_⟩
      · nlinarith [hu.2, Real.pi_pos]
      · exact Prod.ext hxu hsy
    · have hyneg : y < 0 := lt_of_not_ge hy
      have hsy : -(a * Real.sin u) = y := by
        nlinarith
      have hcos_sub :
          Real.cos (2 * Real.pi - u) = Real.cos u := by
        rw [Real.cos_sub, Real.cos_two_pi, Real.sin_two_pi]
        ring
      have hsin_sub :
          Real.sin (2 * Real.pi - u) = -Real.sin u := by
        rw [Real.sin_sub, Real.sin_two_pi, Real.cos_two_pi]
        ring
      have hx' : a * Real.cos (2 * Real.pi - u) = x := by
        rw [hcos_sub]
        exact hxu
      have hy' : a * Real.sin (2 * Real.pi - u) = y := by
        rw [hsin_sub]
        calc
          a * -Real.sin u = -(a * Real.sin u) := by ring
          _ = y := hsy
      refine ⟨2 * Real.pi - u, ⟨?_, ?_⟩, ?_⟩
      · nlinarith [hu.2, Real.pi_pos]
      · nlinarith [hu.1]
      · exact Prod.ext hx' hy'
  · rintro ⟨t, ht, hcurve⟩
    rw [← hcurve]
    change (a * Real.cos t) ^ 2 + (a * Real.sin t) ^ 2 = a ^ 2
    calc
      (a * Real.cos t) ^ 2 + (a * Real.sin t) ^ 2 =
          a ^ 2 * (Real.sin t ^ 2 + Real.cos t ^ 2) := by ring
      _ = a ^ 2 := by rw [Real.sin_sq_add_cos_sq]; ring

theorem gap2 (a : ℝ) (ha : 0 < a) :
    lineIntegral a =
      ∫ t in (0 : ℝ)..2 * Real.pi,
        (-(a * Real.cos t + a * Real.sin t) * a * Real.sin t -
          (a * Real.cos t - a * Real.sin t) * a * Real.cos t) /
            a ^ 2 := by
  rfl

theorem gap3 (a : ℝ) (ha : 0 < a) :
    (∫ t in (0 : ℝ)..2 * Real.pi,
        (-(a * Real.cos t + a * Real.sin t) * a * Real.sin t -
          (a * Real.cos t - a * Real.sin t) * a * Real.cos t) /
            a ^ 2) =
      -(∫ t in (0 : ℝ)..2 * Real.pi, (1 : ℝ)) := by
  have hpoint (t : ℝ) :
      (-(a * Real.cos t + a * Real.sin t) * a * Real.sin t -
        (a * Real.cos t - a * Real.sin t) * a * Real.cos t) /
          a ^ 2 = (-1 : ℝ) := by
    have hnum :
        -(a * Real.cos t + a * Real.sin t) * a * Real.sin t -
          (a * Real.cos t - a * Real.sin t) * a * Real.cos t =
            -(a ^ 2) := by
      calc
        -(a * Real.cos t + a * Real.sin t) * a * Real.sin t -
            (a * Real.cos t - a * Real.sin t) * a * Real.cos t =
              -(a ^ 2) * (Real.sin t ^ 2 + Real.cos t ^ 2) := by ring
        _ = -(a ^ 2) := by rw [Real.sin_sq_add_cos_sq]; ring
    rw [hnum]
    field_simp [ha.ne']
  calc
    (∫ t in (0 : ℝ)..2 * Real.pi,
        (-(a * Real.cos t + a * Real.sin t) * a * Real.sin t -
          (a * Real.cos t - a * Real.sin t) * a * Real.cos t) /
            a ^ 2) =
        ∫ _t in (0 : ℝ)..2 * Real.pi, (-1 : ℝ) := by
          apply intervalIntegral.integral_congr
          intro t _ht
          exact hpoint t
    _ = -(∫ _t in (0 : ℝ)..2 * Real.pi, (1 : ℝ)) := by
      rw [← intervalIntegral.integral_neg]

theorem gap4 :
    -(∫ t in (0 : ℝ)..2 * Real.pi, (1 : ℝ)) =
      -2 * Real.pi := by
  norm_num [intervalIntegral.integral_const] <;> ring

theorem gap5 (a : ℝ) (ha : 0 < a) :
    lineIntegral a = -2 * Real.pi := by
  rw [gap2 a ha, gap3 a ha, gap4]

end

end ProofGap.Exercise4254
