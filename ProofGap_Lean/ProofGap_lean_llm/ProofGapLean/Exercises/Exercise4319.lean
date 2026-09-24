import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise4319

noncomputable section

open MeasureTheory
open scoped Interval

def rollingParam (R : ℝ) (n : ℕ) (t : ℝ) : ℝ × ℝ :=
  (R * (1 - 1 / (n : ℝ)) * Real.cos (t / (n : ℝ)) +
      R / (n : ℝ) * Real.cos ((1 - 1 / (n : ℝ)) * t),
    R * (1 - 1 / (n : ℝ)) * Real.sin (t / (n : ℝ)) -
      R / (n : ℝ) * Real.sin ((1 - 1 / (n : ℝ)) * t))

def hypocycloid (n : ℕ) (r φ : ℝ) : ℝ × ℝ :=
  (((n : ℝ) - 1) * r * Real.cos φ +
      r * Real.cos (((n : ℝ) - 1) * φ),
    ((n : ℝ) - 1) * r * Real.sin φ -
      r * Real.sin (((n : ℝ) - 1) * φ))

def hypocycloidArea (n : ℕ) (r : ℝ) : ℝ :=
  (1 / 2 : ℝ) *
    ∫ φ in (0 : ℝ)..2 * Real.pi,
      (hypocycloid n r φ).1 *
          deriv (fun θ => (hypocycloid n r θ).2) φ -
        (hypocycloid n r φ).2 *
          deriv (fun θ => (hypocycloid n r θ).1) φ

private theorem integral_one_sub_cos_nat_mul
    (n : ℕ) (hn : 2 ≤ n) :
    ∫ x in (0 : ℝ)..2 * Real.pi,
      1 - Real.cos ((n : ℝ) * x) = 2 * Real.pi := by
  have hnNat : n ≠ 0 := by
    intro h
    subst n
    norm_num at hn
  have hn0 : (n : ℝ) ≠ 0 := by
    exact_mod_cast hnNat
  have hderiv : ∀ x : ℝ,
      HasDerivAt
        (fun y : ℝ =>
          y - (1 / (n : ℝ)) * Real.sin ((n : ℝ) * y))
        (1 - Real.cos ((n : ℝ) * x)) x := by
    intro x
    have hlin :
        HasDerivAt (fun y : ℝ => (n : ℝ) * y) (n : ℝ) x := by
      simpa using (hasDerivAt_id x).const_mul (n : ℝ)
    have hsin :
        HasDerivAt
          (fun y : ℝ => Real.sin ((n : ℝ) * y))
          (Real.cos ((n : ℝ) * x) * (n : ℝ)) x := by
      simpa using (Real.hasDerivAt_sin ((n : ℝ) * x)).comp x hlin
    convert
      (hasDerivAt_id x).sub
        (hsin.const_mul (1 / (n : ℝ))) using 1 <;>
      field_simp [hn0] <;> ring
  have hcont : Continuous
      (fun x : ℝ => 1 - Real.cos ((n : ℝ) * x)) :=
    continuous_const.sub
      (Real.continuous_cos.comp (continuous_const.mul continuous_id))
  have hint : IntervalIntegrable
      (fun x : ℝ => 1 - Real.cos ((n : ℝ) * x))
      volume 0 (2 * Real.pi) :=
    hcont.intervalIntegrable 0 (2 * Real.pi)
  have hfund :
      ∫ x in (0 : ℝ)..2 * Real.pi,
          1 - Real.cos ((n : ℝ) * x) =
        ((fun y : ℝ =>
            y - (1 / (n : ℝ)) * Real.sin ((n : ℝ) * y))
          (2 * Real.pi)) -
        ((fun y : ℝ =>
            y - (1 / (n : ℝ)) * Real.sin ((n : ℝ) * y)) 0) := by
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun y : ℝ =>
        y - (1 / (n : ℝ)) * Real.sin ((n : ℝ) * y))
      (f' := fun x : ℝ => 1 - Real.cos ((n : ℝ) * x))
      (fun x _ => hderiv x) hint
  have hsin_mul : ∀ k : ℕ,
      Real.sin ((k : ℝ) * (2 * Real.pi)) = 0 := by
    intro k
    induction k with
    | zero => norm_num
    | succ k ih =>
        rw [Nat.cast_succ]
        rw [show ((k : ℝ) + 1) * (2 * Real.pi) =
          (k : ℝ) * (2 * Real.pi) + 2 * Real.pi by ring]
        rw [Real.sin_add, ih, Real.sin_two_pi, Real.cos_two_pi]
        ring
  simpa [hsin_mul n] using hfund

theorem gap1 (R : ℝ) (n : ℕ) (hn : 2 ≤ n) (t : ℝ) :
    (rollingParam R n t).1 =
      R * (1 - 1 / (n : ℝ)) * Real.cos (t / (n : ℝ)) +
        R / (n : ℝ) * Real.cos ((1 - 1 / (n : ℝ)) * t) := by
  rfl

theorem gap2 (R : ℝ) (n : ℕ) (hn : 2 ≤ n) (t : ℝ) :
    (rollingParam R n t).2 =
      R * (1 - 1 / (n : ℝ)) * Real.sin (t / (n : ℝ)) -
        R / (n : ℝ) * Real.sin ((1 - 1 / (n : ℝ)) * t) := by
  rfl

theorem gap3
    (R r : ℝ) (n : ℕ) (hr : 0 < r)
    (hRatio : R / r = (n : ℝ)) :
    R = (n : ℝ) * r := by
  exact (div_eq_iff (ne_of_gt hr)).mp hRatio

theorem gap4 (n : ℕ) (r φ : ℝ) :
    (hypocycloid n r φ).1 =
      ((n : ℝ) - 1) * r * Real.cos φ +
        r * Real.cos (((n : ℝ) - 1) * φ) := by
  rfl

theorem gap5 (n : ℕ) (r φ : ℝ) :
    (hypocycloid n r φ).2 =
      ((n : ℝ) - 1) * r * Real.sin φ -
        r * Real.sin (((n : ℝ) - 1) * φ) := by
  rfl

theorem gap6 (n : ℕ) (hn : 2 ≤ n) (r φ : ℝ) :
    (hypocycloid n r φ).1 *
          deriv (fun θ => (hypocycloid n r θ).2) φ -
        (hypocycloid n r φ).2 *
          deriv (fun θ => (hypocycloid n r θ).1) φ =
      r ^ 2 * ((n : ℝ) - 1) * ((n : ℝ) - 2) *
        (1 - Real.cos ((n : ℝ) * φ)) := by
  have hx :
      deriv (fun θ => (hypocycloid n r θ).1) φ =
        ((n : ℝ) - 1) * r * (-Real.sin φ) +
          r * (-Real.sin (((n : ℝ) - 1) * φ) * ((n : ℝ) - 1)) := by
    change
      deriv
          (fun θ : ℝ =>
            ((n : ℝ) - 1) * r * Real.cos θ +
              r * Real.cos (((n : ℝ) - 1) * θ)) φ = _
    have hlin :
        HasDerivAt (fun θ : ℝ => ((n : ℝ) - 1) * θ) ((n : ℝ) - 1) φ := by
      simpa using (hasDerivAt_id φ).const_mul ((n : ℝ) - 1)
    simpa only [mul_one] using
      (((Real.hasDerivAt_cos φ).const_mul (((n : ℝ) - 1) * r)).add
        (((Real.hasDerivAt_cos (((n : ℝ) - 1) * φ)).comp φ hlin).const_mul r)).deriv
  have hy :
      deriv (fun θ => (hypocycloid n r θ).2) φ =
        ((n : ℝ) - 1) * r * Real.cos φ -
          r * (Real.cos (((n : ℝ) - 1) * φ) * ((n : ℝ) - 1)) := by
    change
      deriv
          (fun θ : ℝ =>
            ((n : ℝ) - 1) * r * Real.sin θ -
              r * Real.sin (((n : ℝ) - 1) * θ)) φ = _
    have hlin :
        HasDerivAt (fun θ : ℝ => ((n : ℝ) - 1) * θ) ((n : ℝ) - 1) φ := by
      simpa using (hasDerivAt_id φ).const_mul ((n : ℝ) - 1)
    simpa only [mul_one] using
      (((Real.hasDerivAt_sin φ).const_mul (((n : ℝ) - 1) * r)).sub
        (((Real.hasDerivAt_sin (((n : ℝ) - 1) * φ)).comp φ hlin).const_mul r)).deriv
  rw [gap4, gap5, hx, hy]
  calc
    (((n : ℝ) - 1) * r * Real.cos φ +
            r * Real.cos (((n : ℝ) - 1) * φ)) *
          (((n : ℝ) - 1) * r * Real.cos φ -
            r * (Real.cos (((n : ℝ) - 1) * φ) * ((n : ℝ) - 1))) -
        (((n : ℝ) - 1) * r * Real.sin φ -
            r * Real.sin (((n : ℝ) - 1) * φ)) *
          (((n : ℝ) - 1) * r * (-Real.sin φ) +
            r * (-Real.sin (((n : ℝ) - 1) * φ) * ((n : ℝ) - 1))) =
      r ^ 2 * ((n : ℝ) - 1) *
        (((n : ℝ) - 1) *
            (Real.sin φ ^ 2 + Real.cos φ ^ 2) -
          (Real.sin (((n : ℝ) - 1) * φ) ^ 2 +
            Real.cos (((n : ℝ) - 1) * φ) ^ 2) +
          (((n : ℝ) - 1) - 1) *
            (Real.sin φ * Real.sin (((n : ℝ) - 1) * φ) -
              Real.cos φ * Real.cos (((n : ℝ) - 1) * φ))) := by
        ring
    _ = r ^ 2 * ((n : ℝ) - 1) * (((n : ℝ) - 1) - 1) *
        (1 -
          (Real.cos φ * Real.cos (((n : ℝ) - 1) * φ) -
            Real.sin φ * Real.sin (((n : ℝ) - 1) * φ))) := by
      rw [Real.sin_sq_add_cos_sq, Real.sin_sq_add_cos_sq]
      ring
    _ = r ^ 2 * ((n : ℝ) - 1) * ((n : ℝ) - 2) *
        (1 - Real.cos ((n : ℝ) * φ)) := by
      rw [← Real.cos_add]
      rw [show φ + ((n : ℝ) - 1) * φ = (n : ℝ) * φ by ring]
      ring

theorem gap7 (n : ℕ) (r : ℝ) :
    hypocycloidArea n r =
      (1 / 2 : ℝ) *
        ∫ φ in (0 : ℝ)..2 * Real.pi,
          (hypocycloid n r φ).1 *
              deriv (fun θ => (hypocycloid n r θ).2) φ -
            (hypocycloid n r φ).2 *
              deriv (fun θ => (hypocycloid n r θ).1) φ := by
  rfl

theorem gap8 (n : ℕ) (hn : 2 ≤ n) (r : ℝ) :
    hypocycloidArea n r =
      r ^ 2 * ((n : ℝ) - 1) * ((n : ℝ) - 2) / 2 *
        ∫ φ in (0 : ℝ)..2 * Real.pi,
          1 - Real.cos ((n : ℝ) * φ) := by
  unfold hypocycloidArea
  simp_rw [gap6 n hn r]
  rw [intervalIntegral.integral_const_mul]
  ring

theorem gap9 (n : ℕ) (hn : 2 ≤ n) (r : ℝ) :
    hypocycloidArea n r =
      Real.pi * r ^ 2 * ((n : ℝ) - 1) * ((n : ℝ) - 2) := by
  rw [gap8 n hn r, integral_one_sub_cos_nat_mul n hn]
  ring

theorem gap10
    (R r : ℝ) (n : ℕ) (hr : 0 < r)
    (hRatio : R / r = (n : ℝ)) (hFour : R / r = 4) :
    n = 4 := by
  have h : (n : ℝ) = (4 : ℝ) := hRatio.symm.trans hFour
  exact_mod_cast h

theorem gap11
    (R r : ℝ) (n : ℕ) (hn : 2 ≤ n) (hr : 0 < r)
    (hRatio : R / r = (n : ℝ)) (hFour : R / r = 4) :
    hypocycloidArea n r = 6 * Real.pi * r ^ 2 := by
  have hn4 : n = 4 := gap10 R r n hr hRatio hFour
  subst n
  calc
    hypocycloidArea 4 r =
        Real.pi * r ^ 2 * (((4 : ℕ) : ℝ) - 1) * (((4 : ℕ) : ℝ) - 2) :=
      gap9 4 (by norm_num) r
    _ = 6 * Real.pi * r ^ 2 := by ring

end

end ProofGap.Exercise4319
