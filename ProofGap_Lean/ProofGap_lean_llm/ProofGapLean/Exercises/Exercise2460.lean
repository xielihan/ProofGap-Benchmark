import ProofGapLean.Prelude.Analysis
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

open scoped Interval

namespace ProofGap.Exercise2460

noncomputable section

def ellipseLength (a b : ℝ) : ℝ :=
  ∫ t in 0..(2 * Real.pi),
    Real.sqrt (a ^ 2 * Real.sin t ^ 2 + b ^ 2 * Real.cos t ^ 2)

def sineGraphLength (b c : ℝ) : ℝ :=
  ∫ x in 0..(2 * Real.pi * b),
    Real.sqrt (1 + c ^ 2 / b ^ 2 * Real.cos (x / b) ^ 2)

def eccentricity (a c : ℝ) : ℝ := c / a

private theorem integral_sqrt_cos_sq_eq_sin_sq (A C : ℝ) :
    (∫ t in 0..(2 * Real.pi),
      Real.sqrt (A - C * Real.cos t ^ 2)) =
    ∫ t in 0..(2 * Real.pi),
      Real.sqrt (A - C * Real.sin t ^ 2) := by
  let F : ℝ → ℝ := fun t => Real.sqrt (A - C * Real.cos t ^ 2)
  have hcont : Continuous F := by
    dsimp [F]
    fun_prop
  have hint (u v : ℝ) :
      IntervalIntegrable F MeasureTheory.volume u v :=
    hcont.intervalIntegrable u v
  have hcomp (u v d : ℝ) :
      (∫ x in u..v, F (x + d)) = ∫ x in (u + d)..(v + d), F x := by
    simpa using (intervalIntegral.integral_comp_add_right F u v d)
  have hlast :
      (∫ x in (2 * Real.pi)..(2 * Real.pi + Real.pi / 2), F x) =
        ∫ x in 0..(Real.pi / 2), F x := by
    calc
      (∫ x in (2 * Real.pi)..(2 * Real.pi + Real.pi / 2), F x) =
          ∫ x in 0..(Real.pi / 2), F (x + 2 * Real.pi) := by
        symm
        simpa [add_comm, add_left_comm, add_assoc] using
          (hcomp 0 (Real.pi / 2) (2 * Real.pi))
      _ = ∫ x in 0..(Real.pi / 2), F x := by
        apply intervalIntegral.integral_congr
        intro x hx
        simp [F, Real.cos_add_two_pi]
  have hshift :
      (∫ x in 0..(2 * Real.pi), F (x + Real.pi / 2)) =
        ∫ x in (Real.pi / 2)..(2 * Real.pi + Real.pi / 2), F x := by
    simpa [add_comm, add_left_comm, add_assoc] using
      (hcomp 0 (2 * Real.pi) (Real.pi / 2))
  calc
    (∫ t in 0..(2 * Real.pi),
        Real.sqrt (A - C * Real.cos t ^ 2)) =
        ∫ t in 0..(2 * Real.pi), F t := by
      rfl
    _ = (∫ t in 0..(Real.pi / 2), F t)
          + (∫ t in (Real.pi / 2)..(2 * Real.pi), F t) := by
      exact (intervalIntegral.integral_add_adjacent_intervals
        (hint 0 (Real.pi / 2))
        (hint (Real.pi / 2) (2 * Real.pi))).symm
    _ = (∫ t in (Real.pi / 2)..(2 * Real.pi), F t)
          + (∫ t in 0..(Real.pi / 2), F t) := by
      rw [add_comm]
    _ = (∫ t in (Real.pi / 2)..(2 * Real.pi), F t)
          + (∫ t in (2 * Real.pi)..(2 * Real.pi + Real.pi / 2), F t) := by
      rw [hlast]
    _ = ∫ t in (Real.pi / 2)..(2 * Real.pi + Real.pi / 2), F t := by
      exact intervalIntegral.integral_add_adjacent_intervals
        (hint (Real.pi / 2) (2 * Real.pi))
        (hint (2 * Real.pi) (2 * Real.pi + Real.pi / 2))
    _ = ∫ t in 0..(2 * Real.pi), F (t + Real.pi / 2) := hshift.symm
    _ = ∫ t in 0..(2 * Real.pi),
        Real.sqrt (A - C * Real.sin t ^ 2) := by
      apply intervalIntegral.integral_congr
      intro t ht
      simp [F, Real.cos_add_pi_div_two]

theorem gap1 (a b s₁ : ℝ) (hs₁ : s₁ = ellipseLength a b) :
    s₁ = ∫ t in 0..(2 * Real.pi),
      Real.sqrt (a ^ 2 * Real.sin t ^ 2 + b ^ 2 * Real.cos t ^ 2) := by
  simpa [ellipseLength] using hs₁

theorem gap2 (a b c s₁ : ℝ) (hc : c ^ 2 = a ^ 2 - b ^ 2)
    (hs₁ : s₁ = ellipseLength a b) :
    s₁ = ∫ t in 0..(2 * Real.pi),
      Real.sqrt (a ^ 2 - c ^ 2 * Real.cos t ^ 2) := by
  rw [hs₁]
  unfold ellipseLength
  apply intervalIntegral.integral_congr
  intro t ht
  apply congrArg Real.sqrt
  rw [hc]
  nlinarith [Real.sin_sq_add_cos_sq t]

theorem gap3 (a c s₁ : ℝ) (ha : 0 < a)
    (hs₁ : s₁ = ∫ t in 0..(2 * Real.pi),
      Real.sqrt (a ^ 2 - c ^ 2 * Real.cos t ^ 2)) :
    s₁ = a * ∫ t in 0..(2 * Real.pi),
      Real.sqrt (1 - eccentricity a c ^ 2 * Real.cos t ^ 2) := by
  rw [hs₁]
  have ha0 : a ≠ 0 := ne_of_gt ha
  calc
    (∫ t in 0..(2 * Real.pi),
        Real.sqrt (a ^ 2 - c ^ 2 * Real.cos t ^ 2)) =
        ∫ t in 0..(2 * Real.pi),
          a * Real.sqrt (1 - eccentricity a c ^ 2 * Real.cos t ^ 2) := by
      apply intervalIntegral.integral_congr
      intro t ht
      have harg :
          a ^ 2 - c ^ 2 * Real.cos t ^ 2 =
            a ^ 2 * (1 - eccentricity a c ^ 2 * Real.cos t ^ 2) := by
        unfold eccentricity
        field_simp [ha0]
        <;> ring
      change Real.sqrt (a ^ 2 - c ^ 2 * Real.cos t ^ 2) =
        a * Real.sqrt (1 - eccentricity a c ^ 2 * Real.cos t ^ 2)
      rw [harg, Real.sqrt_mul (sq_nonneg a)]
      simp [Real.sqrt_sq_eq_abs, abs_of_pos ha]
    _ = a * ∫ t in 0..(2 * Real.pi),
          Real.sqrt (1 - eccentricity a c ^ 2 * Real.cos t ^ 2) := by
      rw [intervalIntegral.integral_const_mul]

theorem gap4 (a c s₁ : ℝ) (ha : 0 < a)
    (hs₁ : s₁ = ∫ t in 0..(2 * Real.pi),
      Real.sqrt (a ^ 2 - c ^ 2 * Real.cos t ^ 2)) :
    s₁ = a * ∫ t in 0..(2 * Real.pi),
      Real.sqrt (1 - eccentricity a c ^ 2 * Real.sin t ^ 2) := by
  calc
    s₁ = a * ∫ t in 0..(2 * Real.pi),
        Real.sqrt (1 - eccentricity a c ^ 2 * Real.cos t ^ 2) :=
      gap3 a c s₁ ha hs₁
    _ = a * ∫ t in 0..(2 * Real.pi),
        Real.sqrt (1 - eccentricity a c ^ 2 * Real.sin t ^ 2) := by
      rw [integral_sqrt_cos_sq_eq_sin_sq]

theorem gap5 (b c s₂ : ℝ) (hs₂ : s₂ = sineGraphLength b c) :
    s₂ = ∫ x in 0..(2 * Real.pi * b),
      Real.sqrt (1 + c ^ 2 / b ^ 2 * Real.cos (x / b) ^ 2) := by
  simpa [sineGraphLength] using hs₂

theorem gap6 (b c s₂ : ℝ) (hb : 0 < b)
    (hs₂ : s₂ = sineGraphLength b c) :
    s₂ = ∫ t in 0..(2 * Real.pi),
      Real.sqrt (b ^ 2 + c ^ 2 * Real.cos t ^ 2) := by
  rw [hs₂]
  unfold sineGraphLength
  have hb0 : b ≠ 0 := ne_of_gt hb
  let f : ℝ → ℝ := fun x =>
    Real.sqrt (1 + c ^ 2 / b ^ 2 * Real.cos (x / b) ^ 2)
  change (∫ x in 0..(2 * Real.pi * b), f x) = _
  have hmul :
      (∫ t in 0..(2 * Real.pi), f (t * b)) =
        b⁻¹ * ∫ x in 0..(2 * Real.pi * b), f x := by
    simpa only [zero_mul] using
      (intervalIntegral.integral_comp_mul_right
        (a := 0) (b := 2 * Real.pi) f hb0)
  calc
    (∫ x in 0..(2 * Real.pi * b), f x) =
        b * ∫ t in 0..(2 * Real.pi), f (t * b) := by
      rw [hmul]
      field_simp [hb0]
    _ = ∫ t in 0..(2 * Real.pi), b * f (t * b) := by
      rw [intervalIntegral.integral_const_mul]
    _ = ∫ t in 0..(2 * Real.pi),
        Real.sqrt (b ^ 2 + c ^ 2 * Real.cos t ^ 2) := by
      apply intervalIntegral.integral_congr
      intro t ht
      have harg :
          b ^ 2 + c ^ 2 * Real.cos t ^ 2 =
            b ^ 2 * (1 + c ^ 2 / b ^ 2 * Real.cos t ^ 2) := by
        field_simp [hb0]
        <;> ring
      have htb : t * b / b = t := by
        field_simp [hb0]
      dsimp [f]
      rw [htb]
      rw [harg, Real.sqrt_mul (sq_nonneg b)]
      simp [Real.sqrt_sq_eq_abs, abs_of_pos hb]

theorem gap7 (a b c s₂ : ℝ) (hc : c ^ 2 = a ^ 2 - b ^ 2)
    (hb : 0 < b) (hs₂ : s₂ = sineGraphLength b c) :
    s₂ = ∫ t in 0..(2 * Real.pi),
      Real.sqrt (a ^ 2 - c ^ 2 * Real.sin t ^ 2) := by
  rw [gap6 b c s₂ hb hs₂]
  apply intervalIntegral.integral_congr
  intro t ht
  apply congrArg Real.sqrt
  rw [hc]
  nlinarith [Real.sin_sq_add_cos_sq t]

theorem gap8 (a b c s₂ : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hc : c ^ 2 = a ^ 2 - b ^ 2) (hs₂ : s₂ = sineGraphLength b c) :
    s₂ = a * ∫ t in 0..(2 * Real.pi),
      Real.sqrt (1 - eccentricity a c ^ 2 * Real.sin t ^ 2) := by
  rw [gap7 a b c s₂ hc hb hs₂]
  have ha0 : a ≠ 0 := ne_of_gt ha
  calc
    (∫ t in 0..(2 * Real.pi),
        Real.sqrt (a ^ 2 - c ^ 2 * Real.sin t ^ 2)) =
        ∫ t in 0..(2 * Real.pi),
          a * Real.sqrt (1 - eccentricity a c ^ 2 * Real.sin t ^ 2) := by
      apply intervalIntegral.integral_congr
      intro t ht
      have harg :
          a ^ 2 - c ^ 2 * Real.sin t ^ 2 =
            a ^ 2 * (1 - eccentricity a c ^ 2 * Real.sin t ^ 2) := by
        unfold eccentricity
        field_simp [ha0]
        <;> ring
      change Real.sqrt (a ^ 2 - c ^ 2 * Real.sin t ^ 2) =
        a * Real.sqrt (1 - eccentricity a c ^ 2 * Real.sin t ^ 2)
      rw [harg, Real.sqrt_mul (sq_nonneg a)]
      simp [Real.sqrt_sq_eq_abs, abs_of_pos ha]
    _ = a * ∫ t in 0..(2 * Real.pi),
          Real.sqrt (1 - eccentricity a c ^ 2 * Real.sin t ^ 2) := by
      rw [intervalIntegral.integral_const_mul]

theorem gap9 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hc : c ^ 2 = a ^ 2 - b ^ 2) :
    ellipseLength a b = sineGraphLength b c := by
  have he :
      ellipseLength a b = ∫ t in 0..(2 * Real.pi),
        Real.sqrt (a ^ 2 - c ^ 2 * Real.cos t ^ 2) :=
    gap2 a b c (ellipseLength a b) hc rfl
  have h₁ :
      ellipseLength a b = a * ∫ t in 0..(2 * Real.pi),
        Real.sqrt (1 - eccentricity a c ^ 2 * Real.sin t ^ 2) :=
    gap4 a c (ellipseLength a b) ha he
  have h₂ :
      sineGraphLength b c = a * ∫ t in 0..(2 * Real.pi),
        Real.sqrt (1 - eccentricity a c ^ 2 * Real.sin t ^ 2) :=
    gap8 a b c (sineGraphLength b c) ha hb hc rfl
  exact h₁.trans h₂.symm

theorem gap10 (a b c s₁ s₂ : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hc : c ^ 2 = a ^ 2 - b ^ 2)
    (hs₁ : s₁ = ellipseLength a b) (hs₂ : s₂ = sineGraphLength b c) :
    s₁ = s₂ := by
  calc
    s₁ = ellipseLength a b := hs₁
    _ = sineGraphLength b c := gap9 a b c ha hb hc
    _ = s₂ := hs₂.symm

end

end ProofGap.Exercise2460
