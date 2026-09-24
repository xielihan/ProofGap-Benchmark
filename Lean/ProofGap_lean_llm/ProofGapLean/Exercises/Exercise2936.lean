import ProofGapLean.Prelude.Analysis
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Positivity
import Mathlib.Analysis.Calculus.Deriv.Basic

namespace ProofGap.Exercise2936

noncomputable section

open scoped BigOperators Interval

def f (x : ℝ) : ℝ :=
  Real.sin x ^ 4

def a (n : ℕ) : ℝ :=
  2 / Real.pi * ∫ x in (0 : ℝ)..Real.pi,
    Real.sin x ^ 4 * Real.cos ((n : ℝ) * x)

def b (n : ℕ) : ℝ :=
  1 / Real.pi * ∫ x in (-Real.pi)..Real.pi,
    Real.sin x ^ 4 * Real.sin ((n : ℝ) * x)

def fourierSeries (x : ℝ) : ℝ :=
  a 0 / 2 +
    ∑' k : ℕ, (
      a (k + 1) * Real.cos ((k + 1 : ℕ) * x) +
        b (k + 1) * Real.sin ((k + 1 : ℕ) * x))

def specifiedCoefficient (n : ℕ) : ℝ :=
  if n = 2 then -(1 / 2 : ℝ)
  else if n = 4 then (1 / 8 : ℝ)
  else 0

private theorem sin_nat_mul_pi_aux (n : ℕ) :
    Real.sin ((n : ℝ) * Real.pi) = 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Nat.cast_succ, add_mul, Real.sin_add, ih]
      simp

private theorem scaled_cos_intervalIntegrable (c r : ℝ) :
    IntervalIntegrable (fun x : ℝ => r * Real.cos (c * x))
      MeasureTheory.volume (0 : ℝ) Real.pi := by
  exact
    (continuous_const.mul
      (Real.continuous_cos.comp (continuous_const.mul continuous_id))).intervalIntegrable
      _ _

private theorem scaled_cos_product_intervalIntegrable (r : ℝ) (m n : ℕ) :
    IntervalIntegrable
      (fun x : ℝ =>
        r * (Real.cos ((m : ℝ) * x) * Real.cos ((n : ℝ) * x)))
      MeasureTheory.volume (0 : ℝ) Real.pi := by
  exact
    (continuous_const.mul
      ((Real.continuous_cos.comp (continuous_const.mul continuous_id)).mul
        (Real.continuous_cos.comp
          (continuous_const.mul continuous_id)))).intervalIntegrable _ _

private theorem scaled_sin_intervalIntegrable (c r : ℝ) :
    IntervalIntegrable (fun x : ℝ => r * Real.sin (c * x))
      MeasureTheory.volume (-Real.pi) Real.pi := by
  exact
    (continuous_const.mul
      (Real.continuous_sin.comp (continuous_const.mul continuous_id))).intervalIntegrable
      _ _

private theorem sin_square_identity_aux (x : ℝ) :
    Real.sin x ^ 4 = ((1 - Real.cos (2 * x)) / 2) ^ 2 := by
  have hc : Real.cos (2 * x) = 1 - 2 * Real.sin x ^ 2 := by
    rw [Real.cos_two_mul']
    nlinarith [Real.sin_sq_add_cos_sq x]
  rw [hc]
  ring

private theorem cos_four_identity_aux (x : ℝ) :
    Real.cos (4 * x) = 2 * Real.cos (2 * x) ^ 2 - 1 := by
  calc
    Real.cos (4 * x) = Real.cos (2 * (2 * x)) := by
      congr 1
      ring
    _ = 2 * Real.cos (2 * x) ^ 2 - 1 := Real.cos_two_mul (2 * x)

private theorem square_expansion_aux (x : ℝ) :
    ((1 - Real.cos (2 * x)) / 2) ^ 2 =
      1 / 4 - 1 / 2 * Real.cos (2 * x) +
        1 / 4 * ((1 + Real.cos (4 * x)) / 2) := by
  rw [cos_four_identity_aux x]
  ring

private theorem sin_fourth_identity (x : ℝ) :
    Real.sin x ^ 4 =
      3 / 8 - 1 / 2 * Real.cos (2 * x) +
        1 / 8 * Real.cos (4 * x) := by
  calc
    Real.sin x ^ 4 = ((1 - Real.cos (2 * x)) / 2) ^ 2 :=
      sin_square_identity_aux x
    _ = 1 / 4 - 1 / 2 * Real.cos (2 * x) +
        1 / 4 * ((1 + Real.cos (4 * x)) / 2) :=
      square_expansion_aux x
    _ = 3 / 8 - 1 / 2 * Real.cos (2 * x) +
        1 / 8 * Real.cos (4 * x) := by ring

private theorem integral_cos_mul_pi (c : ℝ) (hc : c ≠ 0)
    (hs : Real.sin (c * Real.pi) = 0) :
    (∫ x in (0 : ℝ)..Real.pi, Real.cos (c * x)) = 0 := by
  have hderiv : ∀ x : ℝ,
      HasDerivAt (fun y : ℝ => Real.sin (c * y) / c)
        (Real.cos (c * x)) x := by
    intro x
    simpa [hc] using
      (((Real.hasDerivAt_sin (c * x)).comp x
        ((hasDerivAt_const x c).mul (hasDerivAt_id x))).div_const c)
  have hint : IntervalIntegrable (fun x : ℝ => Real.cos (c * x))
      MeasureTheory.volume (0 : ℝ) Real.pi := by
    exact
      (Real.continuous_cos.comp
        (continuous_const.mul continuous_id)).intervalIntegrable _ _
  calc
    (∫ x in (0 : ℝ)..Real.pi, Real.cos (c * x)) =
        Real.sin (c * Real.pi) / c - Real.sin (c * 0) / c := by
          exact intervalIntegral.integral_eq_sub_of_hasDerivAt
            (fun x hx => hderiv x) hint
    _ = 0 := by simp [hs]

private theorem integral_sin_symmetric (c : ℝ) :
    (∫ x in (-Real.pi)..Real.pi, Real.sin (c * x)) = 0 := by
  by_cases hc : c = 0
  · subst c
    simp
  · have hderiv : ∀ x : ℝ,
        HasDerivAt (fun y : ℝ => -Real.cos (c * y) / c)
          (Real.sin (c * x)) x := by
      intro x
      simpa [hc] using
        ((((Real.hasDerivAt_cos (c * x)).comp x
          ((hasDerivAt_const x c).mul (hasDerivAt_id x))).neg).div_const c)
    have hint : IntervalIntegrable (fun x : ℝ => Real.sin (c * x))
        MeasureTheory.volume (-Real.pi) Real.pi := by
      exact
        (Real.continuous_sin.comp
          (continuous_const.mul continuous_id)).intervalIntegrable _ _
    calc
      (∫ x in (-Real.pi)..Real.pi, Real.sin (c * x)) =
          -Real.cos (c * Real.pi) / c -
            (-Real.cos (c * (-Real.pi)) / c) := by
              exact intervalIntegral.integral_eq_sub_of_hasDerivAt
                (fun x hx => hderiv x) hint
      _ = 0 := by
        rw [show c * (-Real.pi) = -(c * Real.pi) by ring, Real.cos_neg]
        ring

private theorem integral_scaled_sin_symmetric (r c : ℝ) :
    (∫ x in (-Real.pi)..Real.pi, r * Real.sin (c * x)) = 0 := by
  rw [intervalIntegral.integral_const_mul, integral_sin_symmetric]
  ring

private theorem integral_cos_nat (n : ℕ) :
    (∫ x in (0 : ℝ)..Real.pi, Real.cos ((n : ℝ) * x)) =
      if n = 0 then Real.pi else 0 := by
  by_cases hn : n = 0
  · subst n
    simp
  · rw [if_neg hn]
    apply integral_cos_mul_pi
    · exact_mod_cast hn
    · exact sin_nat_mul_pi_aux n

private theorem integral_cos_nat_sub (m n : ℕ) :
    (∫ x in (0 : ℝ)..Real.pi,
      Real.cos (((m : ℝ) - (n : ℝ)) * x)) =
      if m = n then Real.pi else 0 := by
  by_cases hmn : m = n
  · subst n
    simp
  · rw [if_neg hmn]
    apply integral_cos_mul_pi
    · intro h
      apply hmn
      exact_mod_cast sub_eq_zero.mp h
    · rw [sub_mul, Real.sin_sub, sin_nat_mul_pi_aux,
        sin_nat_mul_pi_aux]
      ring

private theorem integral_cos_nat_add_of_pos (m n : ℕ) (hm : 0 < m) :
    (∫ x in (0 : ℝ)..Real.pi,
      Real.cos (((m : ℝ) + (n : ℝ)) * x)) = 0 := by
  apply integral_cos_mul_pi
  · positivity
  · rw [add_mul, Real.sin_add, sin_nat_mul_pi_aux,
      sin_nat_mul_pi_aux]
    ring

private theorem integral_cos_nat_mul_cos_nat (m n : ℕ) (hm : 0 < m) :
    (∫ x in (0 : ℝ)..Real.pi,
      Real.cos ((m : ℝ) * x) * Real.cos ((n : ℝ) * x)) =
      if m = n then Real.pi / 2 else 0 := by
  have hd : IntervalIntegrable
      (fun x : ℝ =>
        (1 / 2 : ℝ) * Real.cos (((m : ℝ) - (n : ℝ)) * x))
      MeasureTheory.volume (0 : ℝ) Real.pi :=
    scaled_cos_intervalIntegrable ((m : ℝ) - (n : ℝ)) (1 / 2)
  have hs : IntervalIntegrable
      (fun x : ℝ =>
        (1 / 2 : ℝ) * Real.cos (((m : ℝ) + (n : ℝ)) * x))
      MeasureTheory.volume (0 : ℝ) Real.pi :=
    scaled_cos_intervalIntegrable ((m : ℝ) + (n : ℝ)) (1 / 2)
  calc
    (∫ x in (0 : ℝ)..Real.pi,
      Real.cos ((m : ℝ) * x) * Real.cos ((n : ℝ) * x)) =
        ∫ x in (0 : ℝ)..Real.pi,
          (1 / 2 : ℝ) * Real.cos (((m : ℝ) - (n : ℝ)) * x) +
          (1 / 2 : ℝ) * Real.cos (((m : ℝ) + (n : ℝ)) * x) := by
            apply intervalIntegral.integral_congr
            intro x hx
            simp only
            rw [sub_mul, add_mul, Real.cos_sub, Real.cos_add]
            ring
    _ = (∫ x in (0 : ℝ)..Real.pi,
          (1 / 2 : ℝ) * Real.cos (((m : ℝ) - (n : ℝ)) * x)) +
        (∫ x in (0 : ℝ)..Real.pi,
          (1 / 2 : ℝ) * Real.cos (((m : ℝ) + (n : ℝ)) * x)) :=
          intervalIntegral.integral_add hd hs
    _ = (1 / 2 : ℝ) *
          (∫ x in (0 : ℝ)..Real.pi,
            Real.cos (((m : ℝ) - (n : ℝ)) * x)) +
        (1 / 2 : ℝ) *
          (∫ x in (0 : ℝ)..Real.pi,
            Real.cos (((m : ℝ) + (n : ℝ)) * x)) := by
          rw [intervalIntegral.integral_const_mul,
            intervalIntegral.integral_const_mul]
    _ = if m = n then Real.pi / 2 else 0 := by
          rw [integral_cos_nat_sub,
            integral_cos_nat_add_of_pos m n hm]
          by_cases hmn : m = n <;> simp [hmn]
          <;> ring

private theorem integral_expansion :
    (∫ x in (0 : ℝ)..Real.pi,
      (3 / 8 - 1 / 2 * Real.cos (2 * x) +
        1 / 8 * Real.cos (4 * x))) = 3 * Real.pi / 8 := by
  have h0 := scaled_cos_intervalIntegrable (0 : ℝ) (3 / 8 : ℝ)
  have h2 := scaled_cos_intervalIntegrable (2 : ℝ) (-1 / 2 : ℝ)
  have h4 := scaled_cos_intervalIntegrable (4 : ℝ) (1 / 8 : ℝ)
  have hi0 :
      (∫ x in (0 : ℝ)..Real.pi, Real.cos ((0 : ℝ) * x)) = Real.pi := by
    simp
  have hi2 :
      (∫ x in (0 : ℝ)..Real.pi, Real.cos ((2 : ℝ) * x)) = 0 := by
    simpa using (integral_cos_nat 2)
  have hi4 :
      (∫ x in (0 : ℝ)..Real.pi, Real.cos ((4 : ℝ) * x)) = 0 := by
    simpa using (integral_cos_nat 4)
  calc
    (∫ x in (0 : ℝ)..Real.pi,
      (3 / 8 - 1 / 2 * Real.cos (2 * x) +
        1 / 8 * Real.cos (4 * x))) =
        ∫ x in (0 : ℝ)..Real.pi,
          (3 / 8 : ℝ) * Real.cos ((0 : ℝ) * x) +
          (-1 / 2 : ℝ) * Real.cos ((2 : ℝ) * x) +
          (1 / 8 : ℝ) * Real.cos ((4 : ℝ) * x) := by
            apply intervalIntegral.integral_congr
            intro x hx
            simp
            ring
    _ = (3 / 8 : ℝ) *
          (∫ x in (0 : ℝ)..Real.pi, Real.cos ((0 : ℝ) * x)) +
        (-1 / 2 : ℝ) *
          (∫ x in (0 : ℝ)..Real.pi, Real.cos ((2 : ℝ) * x)) +
        (1 / 8 : ℝ) *
          (∫ x in (0 : ℝ)..Real.pi, Real.cos ((4 : ℝ) * x)) := by
            rw [intervalIntegral.integral_add (h0.add h2) h4,
              intervalIntegral.integral_add h0 h2,
              intervalIntegral.integral_const_mul,
              intervalIntegral.integral_const_mul,
              intervalIntegral.integral_const_mul]
    _ = 3 * Real.pi / 8 := by
          rw [hi0, hi2, hi4]
          ring

private theorem coefficient_integral (n : ℕ) (hn : 0 < n) :
    (∫ x in (0 : ℝ)..Real.pi,
      (3 / 8 * Real.cos ((n : ℝ) * x) -
        1 / 2 * Real.cos (2 * x) * Real.cos ((n : ℝ) * x) +
        1 / 8 * Real.cos (4 * x) * Real.cos ((n : ℝ) * x))) =
      Real.pi / 2 * specifiedCoefficient n := by
  have hA := scaled_cos_intervalIntegrable (n : ℝ) (3 / 8 : ℝ)
  have hB : IntervalIntegrable
      (fun x : ℝ =>
        (-1 / 2 : ℝ) *
          (Real.cos ((2 : ℝ) * x) * Real.cos ((n : ℝ) * x)))
      MeasureTheory.volume (0 : ℝ) Real.pi := by
    simpa using scaled_cos_product_intervalIntegrable (-1 / 2 : ℝ) 2 n
  have hC : IntervalIntegrable
      (fun x : ℝ =>
        (1 / 8 : ℝ) *
          (Real.cos ((4 : ℝ) * x) * Real.cos ((n : ℝ) * x)))
      MeasureTheory.volume (0 : ℝ) Real.pi := by
    simpa using scaled_cos_product_intervalIntegrable (1 / 8 : ℝ) 4 n
  have hi2 :
      (∫ x in (0 : ℝ)..Real.pi,
        Real.cos ((2 : ℝ) * x) * Real.cos ((n : ℝ) * x)) =
        if 2 = n then Real.pi / 2 else 0 := by
    simpa using integral_cos_nat_mul_cos_nat 2 n (by norm_num)
  have hi4 :
      (∫ x in (0 : ℝ)..Real.pi,
        Real.cos ((4 : ℝ) * x) * Real.cos ((n : ℝ) * x)) =
        if 4 = n then Real.pi / 2 else 0 := by
    simpa using integral_cos_nat_mul_cos_nat 4 n (by norm_num)
  calc
    (∫ x in (0 : ℝ)..Real.pi,
      (3 / 8 * Real.cos ((n : ℝ) * x) -
        1 / 2 * Real.cos (2 * x) * Real.cos ((n : ℝ) * x) +
        1 / 8 * Real.cos (4 * x) * Real.cos ((n : ℝ) * x))) =
        ∫ x in (0 : ℝ)..Real.pi,
          (3 / 8 : ℝ) * Real.cos ((n : ℝ) * x) +
          (-1 / 2 : ℝ) *
            (Real.cos ((2 : ℝ) * x) * Real.cos ((n : ℝ) * x)) +
          (1 / 8 : ℝ) *
            (Real.cos ((4 : ℝ) * x) * Real.cos ((n : ℝ) * x)) := by
              apply intervalIntegral.integral_congr
              intro x hx
              ring
    _ = (3 / 8 : ℝ) *
          (∫ x in (0 : ℝ)..Real.pi, Real.cos ((n : ℝ) * x)) +
        (-1 / 2 : ℝ) *
          (∫ x in (0 : ℝ)..Real.pi,
            Real.cos ((2 : ℝ) * x) * Real.cos ((n : ℝ) * x)) +
        (1 / 8 : ℝ) *
          (∫ x in (0 : ℝ)..Real.pi,
            Real.cos ((4 : ℝ) * x) * Real.cos ((n : ℝ) * x)) := by
              rw [intervalIntegral.integral_add (hA.add hB) hC,
                intervalIntegral.integral_add hA hB,
                intervalIntegral.integral_const_mul,
                intervalIntegral.integral_const_mul,
                intervalIntegral.integral_const_mul]
    _ = Real.pi / 2 * specifiedCoefficient n := by
          rw [integral_cos_nat n, hi2, hi4]
          by_cases hn2 : n = 2
          · subst n
            norm_num [specifiedCoefficient] <;> ring
          · by_cases hn4 : n = 4
            · subst n
              norm_num [specifiedCoefficient] <;> ring
            · simp [specifiedCoefficient, Nat.ne_of_gt hn, hn2, hn4,
                eq_comm]

private theorem odd_expansion (n : ℕ) (x : ℝ) :
    Real.sin x ^ 4 * Real.sin ((n : ℝ) * x) =
      (3 / 8 : ℝ) * Real.sin ((n : ℝ) * x) +
      (-1 / 4 : ℝ) * Real.sin (((n : ℝ) + 2) * x) +
      (-1 / 4 : ℝ) * Real.sin (((n : ℝ) - 2) * x) +
      (1 / 16 : ℝ) * Real.sin (((n : ℝ) + 4) * x) +
      (1 / 16 : ℝ) * Real.sin (((n : ℝ) - 4) * x) := by
  have h2 :
      Real.cos (2 * x) * Real.sin ((n : ℝ) * x) =
        (1 / 2 : ℝ) *
          (Real.sin (((n : ℝ) + 2) * x) +
            Real.sin (((n : ℝ) - 2) * x)) := by
    rw [show ((n : ℝ) + 2) * x = (n : ℝ) * x + 2 * x by ring,
      show ((n : ℝ) - 2) * x = (n : ℝ) * x - 2 * x by ring,
      Real.sin_add, Real.sin_sub]
    ring
  have h4 :
      Real.cos (4 * x) * Real.sin ((n : ℝ) * x) =
        (1 / 2 : ℝ) *
          (Real.sin (((n : ℝ) + 4) * x) +
            Real.sin (((n : ℝ) - 4) * x)) := by
    rw [show ((n : ℝ) + 4) * x = (n : ℝ) * x + 4 * x by ring,
      show ((n : ℝ) - 4) * x = (n : ℝ) * x - 4 * x by ring,
      Real.sin_add, Real.sin_sub]
    ring
  calc
    Real.sin x ^ 4 * Real.sin ((n : ℝ) * x) =
        (3 / 8 - 1 / 2 * Real.cos (2 * x) +
          1 / 8 * Real.cos (4 * x)) * Real.sin ((n : ℝ) * x) := by
            rw [sin_fourth_identity x]
    _ = (3 / 8 : ℝ) * Real.sin ((n : ℝ) * x) +
        (-1 / 2 : ℝ) *
          (Real.cos (2 * x) * Real.sin ((n : ℝ) * x)) +
        (1 / 8 : ℝ) *
          (Real.cos (4 * x) * Real.sin ((n : ℝ) * x)) := by ring
    _ = (3 / 8 : ℝ) * Real.sin ((n : ℝ) * x) +
        (-1 / 4 : ℝ) * Real.sin (((n : ℝ) + 2) * x) +
        (-1 / 4 : ℝ) * Real.sin (((n : ℝ) - 2) * x) +
        (1 / 16 : ℝ) * Real.sin (((n : ℝ) + 4) * x) +
        (1 / 16 : ℝ) * Real.sin (((n : ℝ) - 4) * x) := by
          rw [h2, h4]
          ring

private theorem odd_integral (n : ℕ) :
    (∫ x in (-Real.pi)..Real.pi,
      Real.sin x ^ 4 * Real.sin ((n : ℝ) * x)) = 0 := by
  have hA := scaled_sin_intervalIntegrable (n : ℝ) (3 / 8 : ℝ)
  have hB := scaled_sin_intervalIntegrable ((n : ℝ) + 2) (-1 / 4 : ℝ)
  have hC := scaled_sin_intervalIntegrable ((n : ℝ) - 2) (-1 / 4 : ℝ)
  have hD := scaled_sin_intervalIntegrable ((n : ℝ) + 4) (1 / 16 : ℝ)
  have hE := scaled_sin_intervalIntegrable ((n : ℝ) - 4) (1 / 16 : ℝ)
  calc
    (∫ x in (-Real.pi)..Real.pi,
      Real.sin x ^ 4 * Real.sin ((n : ℝ) * x)) =
        ∫ x in (-Real.pi)..Real.pi,
          (3 / 8 : ℝ) * Real.sin ((n : ℝ) * x) +
          (-1 / 4 : ℝ) * Real.sin (((n : ℝ) + 2) * x) +
          (-1 / 4 : ℝ) * Real.sin (((n : ℝ) - 2) * x) +
          (1 / 16 : ℝ) * Real.sin (((n : ℝ) + 4) * x) +
          (1 / 16 : ℝ) * Real.sin (((n : ℝ) - 4) * x) := by
            apply intervalIntegral.integral_congr
            intro x hx
            simp only
            exact odd_expansion n x
    _ = 0 := by
      rw [intervalIntegral.integral_add (((hA.add hB).add hC).add hD) hE,
        intervalIntegral.integral_add ((hA.add hB).add hC) hD,
        intervalIntegral.integral_add (hA.add hB) hC,
        intervalIntegral.integral_add hA hB,
        integral_scaled_sin_symmetric,
        integral_scaled_sin_symmetric,
        integral_scaled_sin_symmetric,
        integral_scaled_sin_symmetric,
        integral_scaled_sin_symmetric]
      ring

private theorem a_zero_value : a 0 = (3 / 4 : ℝ) := by
  unfold a
  simp only [Nat.cast_zero, zero_mul, Real.cos_zero, mul_one]
  rw [show (∫ x in (0 : ℝ)..Real.pi, Real.sin x ^ 4) =
      ∫ x in (0 : ℝ)..Real.pi,
        (3 / 8 - 1 / 2 * Real.cos (2 * x) +
          1 / 8 * Real.cos (4 * x)) by
        apply intervalIntegral.integral_congr
        intro x hx
        exact sin_fourth_identity x]
  rw [integral_expansion]
  field_simp [Real.pi_ne_zero]
  <;> ring

private theorem a_positive_value (n : ℕ) (hn : 0 < n) :
    a n = specifiedCoefficient n := by
  unfold a
  rw [show (∫ x in (0 : ℝ)..Real.pi,
      Real.sin x ^ 4 * Real.cos ((n : ℝ) * x)) =
      ∫ x in (0 : ℝ)..Real.pi,
        (3 / 8 * Real.cos ((n : ℝ) * x) -
          1 / 2 * Real.cos (2 * x) * Real.cos ((n : ℝ) * x) +
          1 / 8 * Real.cos (4 * x) * Real.cos ((n : ℝ) * x)) by
        apply intervalIntegral.integral_congr
        intro x hx
        simp only
        rw [sin_fourth_identity x]
        ring]
  rw [coefficient_integral n hn]
  field_simp [Real.pi_ne_zero]
  <;> ring

private theorem b_zero_value (n : ℕ) : b n = 0 := by
  unfold b
  rw [odd_integral n]
  ring

private theorem fourier_identity (x : ℝ) : f x = fourierSeries x := by
  unfold f fourierSeries
  rw [sin_fourth_identity x, a_zero_value]
  have hsupp : ∀ k : ℕ, k ∉ ({1, 3} : Finset ℕ) →
      a (k + 1) * Real.cos ((k + 1 : ℕ) * x) +
        b (k + 1) * Real.sin ((k + 1 : ℕ) * x) = 0 := by
    intro k hk
    have hk' : ¬(k = 1 ∨ k = 3) := by
      simpa using hk
    have hk2 : k + 1 ≠ 2 := by omega
    have hk4 : k + 1 ≠ 4 := by omega
    simp [a_positive_value (k + 1) (Nat.succ_pos k),
      b_zero_value, specifiedCoefficient, hk2, hk4]
  rw [tsum_eq_sum (s := ({1, 3} : Finset ℕ)) hsupp]
  norm_num [a_positive_value, b_zero_value, specifiedCoefficient]
  ring

theorem gap1 :
    ∀ x : ℝ, f x = fourierSeries x := by
  intro x
  exact fourier_identity x

theorem gap2 :
    ∀ x : ℝ,
      Real.sin x ^ 4 = ((1 - Real.cos (2 * x)) / 2) ^ 2 := by
  intro x
  exact sin_square_identity_aux x

theorem gap3 :
    ∀ x : ℝ,
      ((1 - Real.cos (2 * x)) / 2) ^ 2 =
        1 / 4 - 1 / 2 * Real.cos (2 * x) +
          1 / 4 * ((1 + Real.cos (4 * x)) / 2) := by
  intro x
  exact square_expansion_aux x

theorem gap4 :
    ∀ x : ℝ,
      1 / 4 - 1 / 2 * Real.cos (2 * x) +
          1 / 4 * ((1 + Real.cos (4 * x)) / 2) =
        3 / 8 - 1 / 2 * Real.cos (2 * x) +
          1 / 8 * Real.cos (4 * x) := by
  intro x
  ring

theorem gap5 :
    ∀ x : ℝ,
      Real.sin x ^ 4 =
        3 / 8 - 1 / 2 * Real.cos (2 * x) +
          1 / 8 * Real.cos (4 * x) := by
  intro x
  exact sin_fourth_identity x

theorem gap6 :
    a 0 =
      2 / Real.pi * ∫ x in (0 : ℝ)..Real.pi,
        Real.sin x ^ 4 := by
  simp [a]

theorem gap7 :
    (2 / Real.pi * ∫ x in (0 : ℝ)..Real.pi,
        Real.sin x ^ 4) =
      2 / Real.pi * ∫ x in (0 : ℝ)..Real.pi,
        (3 / 8 - 1 / 2 * Real.cos (2 * x) +
          1 / 8 * Real.cos (4 * x)) := by
  apply congrArg (fun z : ℝ => 2 / Real.pi * z)
  apply intervalIntegral.integral_congr
  intro x hx
  exact gap5 x

theorem gap8 :
    (2 / Real.pi * ∫ x in (0 : ℝ)..Real.pi,
        (3 / 8 - 1 / 2 * Real.cos (2 * x) +
          1 / 8 * Real.cos (4 * x))) =
      (3 / 4 : ℝ) := by
  rw [integral_expansion]
  field_simp [Real.pi_ne_zero]
  <;> ring

theorem gap9 :
    a 0 = (3 / 4 : ℝ) := by
  rw [gap6, gap7, gap8]

theorem gap10 :
    ∀ n : ℕ,
      a n =
        2 / Real.pi * ∫ x in (0 : ℝ)..Real.pi,
          Real.sin x ^ 4 * Real.cos ((n : ℝ) * x) := by
  intro n
  rfl

theorem gap11 :
    ∀ n : ℕ,
      a n =
        2 / Real.pi * ∫ x in (0 : ℝ)..Real.pi,
          (3 / 8 * Real.cos ((n : ℝ) * x) -
            1 / 2 * Real.cos (2 * x) * Real.cos ((n : ℝ) * x) +
            1 / 8 * Real.cos (4 * x) * Real.cos ((n : ℝ) * x)) := by
  intro n
  rw [gap10 n]
  apply congrArg (fun z : ℝ => 2 / Real.pi * z)
  apply intervalIntegral.integral_congr
  intro x hx
  simp only
  rw [gap5 x]
  ring

theorem gap12 :
    ∀ n : ℕ, 0 < n → a n = specifiedCoefficient n := by
  intro n hn
  rw [gap11 n, coefficient_integral n hn]
  field_simp [Real.pi_ne_zero]
  <;> ring

theorem gap13 :
    ∀ n : ℕ,
      b n =
        1 / Real.pi * ∫ x in (-Real.pi)..Real.pi,
          Real.sin x ^ 4 * Real.sin ((n : ℝ) * x) := by
  intro n
  rfl

theorem gap14 :
    ∀ n : ℕ,
      (1 / Real.pi * ∫ x in (-Real.pi)..Real.pi,
        Real.sin x ^ 4 * Real.sin ((n : ℝ) * x)) = 0 := by
  intro n
  rw [odd_integral n]
  ring

theorem gap15 :
    ∀ n : ℕ, b n = 0 := by
  intro n
  rw [gap13 n, gap14 n]

theorem gap16 :
    ∀ x : ℝ,
      f x =
        3 / 8 - 1 / 2 * Real.cos (2 * x) +
          1 / 8 * Real.cos (4 * x) := by
  intro x
  simpa [f] using gap5 x

end

end ProofGap.Exercise2936
