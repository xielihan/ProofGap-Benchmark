import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

open scoped Interval

namespace ProofGap.Exercise2295

noncomputable section

def targetIntegral (n : ℕ) : ℝ :=
  ∫ x in 0..Real.pi,
    Real.sin x ^ (n - 1) * Real.cos ((n + 1 : ℕ) * x)

def boundary (n : ℕ) (x : ℝ) : ℝ :=
  Real.sin x ^ n * Real.cos ((n : ℝ) * x) / (n : ℝ)

def cancellationExpression (n : ℕ) : ℝ :=
  (boundary n Real.pi - boundary n 0) -
    1 / (n : ℝ) *
      (∫ x in 0..Real.pi,
        Real.sin x ^ n * deriv (fun y : ℝ => Real.cos ((n : ℝ) * y)) x) -
    ∫ x in 0..Real.pi,
      Real.sin x ^ n * Real.sin ((n : ℝ) * x)

private theorem firstIntegral_eq_boundary (n : ℕ) (hn : 0 < n) :
    (∫ x in 0..Real.pi,
      Real.sin x ^ (n - 1) * Real.cos ((n : ℝ) * x) * deriv Real.sin x) =
      (boundary n Real.pi - boundary n 0) -
        1 / (n : ℝ) *
          (∫ x in 0..Real.pi,
            Real.sin x ^ n *
              deriv (fun y : ℝ => Real.cos ((n : ℝ) * y)) x) := by
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  have hFderiv (x : ℝ) :
      HasDerivAt (fun y : ℝ => Real.sin y ^ n / (n : ℝ))
        (Real.sin x ^ (n - 1) * Real.cos x) x := by
    convert ((Real.hasDerivAt_sin x).pow n).div_const (n : ℝ) using 1 <;>
      field_simp [hn0] <;> ring
  have hGderiv (x : ℝ) :
      HasDerivAt (fun y : ℝ => Real.cos ((n : ℝ) * y))
        (-(n : ℝ) * Real.sin ((n : ℝ) * x)) x := by
    convert
      (Real.hasDerivAt_cos ((n : ℝ) * x)).comp x
        ((hasDerivAt_id x).const_mul (n : ℝ)) using 1 <;> ring
  have hF'Int : IntervalIntegrable
      (fun x : ℝ => Real.sin x ^ (n - 1) * Real.cos x)
      MeasureTheory.volume 0 Real.pi :=
    ((Real.continuous_sin.pow (n - 1)).mul
      Real.continuous_cos).intervalIntegrable 0 Real.pi
  have hG'Int : IntervalIntegrable
      (fun x : ℝ => -(n : ℝ) * Real.sin ((n : ℝ) * x))
      MeasureTheory.volume 0 Real.pi :=
    (continuous_const.mul
      (Real.continuous_sin.comp
        (continuous_const.mul continuous_id))).intervalIntegrable 0 Real.pi
  have hibp :=
    intervalIntegral.integral_mul_deriv_eq_deriv_mul
      (u := fun x : ℝ => Real.sin x ^ n / (n : ℝ))
      (v := fun x : ℝ => Real.cos ((n : ℝ) * x))
      (u' := fun x : ℝ => Real.sin x ^ (n - 1) * Real.cos x)
      (v' := fun x : ℝ => -(n : ℝ) * Real.sin ((n : ℝ) * x))
      (a := (0 : ℝ)) (b := Real.pi)
      (fun x hx => hFderiv x) (fun x hx => hGderiv x)
      hF'Int hG'Int
  have hibp' :
      (∫ x in 0..Real.pi,
        (Real.sin x ^ (n - 1) * Real.cos x) *
          Real.cos ((n : ℝ) * x)) =
        (Real.sin Real.pi ^ n / (n : ℝ)) *
            Real.cos ((n : ℝ) * Real.pi) -
          (Real.sin 0 ^ n / (n : ℝ)) * Real.cos ((n : ℝ) * 0) -
          ∫ x in 0..Real.pi,
            (Real.sin x ^ n / (n : ℝ)) *
              (-(n : ℝ) * Real.sin ((n : ℝ) * x)) := by
    linarith [hibp]
  have hleft :
      (∫ x in 0..Real.pi,
        Real.sin x ^ (n - 1) * Real.cos ((n : ℝ) * x) * deriv Real.sin x) =
        ∫ x in 0..Real.pi,
          (Real.sin x ^ (n - 1) * Real.cos x) *
            Real.cos ((n : ℝ) * x) := by
    apply intervalIntegral.integral_congr
    intro x hx
    change
      Real.sin x ^ (n - 1) * Real.cos ((n : ℝ) * x) * deriv Real.sin x =
        (Real.sin x ^ (n - 1) * Real.cos x) *
          Real.cos ((n : ℝ) * x)
    rw [(Real.hasDerivAt_sin x).deriv]
    ring
  have hright :
      (∫ x in 0..Real.pi,
        (Real.sin x ^ n / (n : ℝ)) *
          (-(n : ℝ) * Real.sin ((n : ℝ) * x))) =
        1 / (n : ℝ) *
          (∫ x in 0..Real.pi,
            Real.sin x ^ n *
              deriv (fun y : ℝ => Real.cos ((n : ℝ) * y)) x) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x hx
    change (Real.sin x ^ n / (n : ℝ)) *
        (-(n : ℝ) * Real.sin ((n : ℝ) * x)) =
      1 / (n : ℝ) *
        (Real.sin x ^ n *
          deriv (fun y : ℝ => Real.cos ((n : ℝ) * y)) x)
    rw [(hGderiv x).deriv]
    ring
  rw [hleft, hibp', hright]
  unfold boundary
  ring

theorem gap1 (n : ℕ) (hn : 0 < n) :
    targetIntegral n =
      ∫ x in 0..Real.pi,
        Real.sin x ^ (n - 1) *
          (Real.cos ((n : ℝ) * x) * Real.cos x -
            Real.sin ((n : ℝ) * x) * Real.sin x) := by
  unfold targetIntegral
  apply intervalIntegral.integral_congr
  intro x hx
  simp only [Nat.cast_add, Nat.cast_one, add_mul, one_mul, Real.cos_add]

theorem gap2 (n : ℕ) (hn : 0 < n) :
    targetIntegral n =
      (∫ x in 0..Real.pi,
        Real.sin x ^ (n - 1) * Real.cos ((n : ℝ) * x) *
          deriv Real.sin x) -
      ∫ x in 0..Real.pi,
        Real.sin x ^ n * Real.sin ((n : ℝ) * x) := by
  rw [gap1 n hn]
  have hsin : deriv Real.sin = Real.cos := by
    funext x
    exact (Real.hasDerivAt_sin x).deriv
  rw [hsin]
  have hcosn : Continuous (fun x : ℝ => Real.cos ((n : ℝ) * x)) :=
    Real.continuous_cos.comp (continuous_const.mul continuous_id)
  have hf : IntervalIntegrable
      (fun x : ℝ => Real.sin x ^ (n - 1) * Real.cos ((n : ℝ) * x) * Real.cos x)
      MeasureTheory.volume 0 Real.pi :=
    (((Real.continuous_sin.pow (n - 1)).mul hcosn).mul
      Real.continuous_cos).intervalIntegrable 0 Real.pi
  have hg : IntervalIntegrable
      (fun x : ℝ => Real.sin x ^ n * Real.sin ((n : ℝ) * x))
      MeasureTheory.volume 0 Real.pi :=
    ((Real.continuous_sin.pow n).mul
      (Real.continuous_sin.comp
        (continuous_const.mul continuous_id))).intervalIntegrable 0 Real.pi
  calc
    (∫ x in 0..Real.pi,
      Real.sin x ^ (n - 1) *
        (Real.cos ((n : ℝ) * x) * Real.cos x -
          Real.sin ((n : ℝ) * x) * Real.sin x)) =
        ∫ x in 0..Real.pi,
          (Real.sin x ^ (n - 1) * Real.cos ((n : ℝ) * x) * Real.cos x) -
            Real.sin x ^ n * Real.sin ((n : ℝ) * x) := by
      apply intervalIntegral.integral_congr
      intro x hx
      change
        Real.sin x ^ (n - 1) *
            (Real.cos ((n : ℝ) * x) * Real.cos x -
              Real.sin ((n : ℝ) * x) * Real.sin x) =
          Real.sin x ^ (n - 1) * Real.cos ((n : ℝ) * x) * Real.cos x -
            Real.sin x ^ n * Real.sin ((n : ℝ) * x)
      have hpow : Real.sin x ^ n = Real.sin x ^ (n - 1) * Real.sin x := by
        calc
          Real.sin x ^ n = Real.sin x ^ (n - 1 + 1) := by
            rw [Nat.sub_add_cancel hn]
          _ = Real.sin x ^ (n - 1) * Real.sin x := by rw [pow_succ]
      rw [hpow]
      ring
    _ = (∫ x in 0..Real.pi,
          Real.sin x ^ (n - 1) * Real.cos ((n : ℝ) * x) * Real.cos x) -
        ∫ x in 0..Real.pi,
          Real.sin x ^ n * Real.sin ((n : ℝ) * x) :=
      intervalIntegral.integral_sub hf hg

theorem gap3 (n : ℕ) (hn : 0 < n) :
    targetIntegral n = cancellationExpression n := by
  rw [gap2 n hn, firstIntegral_eq_boundary n hn]
  rfl

theorem gap4 (n : ℕ) (hn : 0 < n) :
    cancellationExpression n = 0 := by
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  have hcos (x : ℝ) :
      HasDerivAt (fun y : ℝ => Real.cos ((n : ℝ) * y))
        (-(n : ℝ) * Real.sin ((n : ℝ) * x)) x := by
    convert
      (Real.hasDerivAt_cos ((n : ℝ) * x)).comp x
        ((hasDerivAt_id x).const_mul (n : ℝ)) using 1 <;> ring
  have hbpi : boundary n Real.pi = 0 := by
    simp [boundary, Nat.ne_of_gt hn]
  have hbzero : boundary n 0 = 0 := by
    simp [boundary, Nat.ne_of_gt hn]
  have hint :
      (∫ x in 0..Real.pi,
        Real.sin x ^ n *
          deriv (fun y : ℝ => Real.cos ((n : ℝ) * y)) x) =
        -(n : ℝ) *
          (∫ x in 0..Real.pi,
            Real.sin x ^ n * Real.sin ((n : ℝ) * x)) := by
    calc
      (∫ x in 0..Real.pi,
        Real.sin x ^ n *
          deriv (fun y : ℝ => Real.cos ((n : ℝ) * y)) x) =
          ∫ x in 0..Real.pi,
            -(n : ℝ) *
              (Real.sin x ^ n * Real.sin ((n : ℝ) * x)) := by
            apply intervalIntegral.integral_congr
            intro x hx
            change Real.sin x ^ n *
                deriv (fun y : ℝ => Real.cos ((n : ℝ) * y)) x =
              -(n : ℝ) *
                (Real.sin x ^ n * Real.sin ((n : ℝ) * x))
            rw [(hcos x).deriv]
            ring
      _ = -(n : ℝ) *
          (∫ x in 0..Real.pi,
            Real.sin x ^ n * Real.sin ((n : ℝ) * x)) := by
            rw [intervalIntegral.integral_const_mul]
  unfold cancellationExpression
  rw [hbpi, hbzero, hint]
  field_simp [hn0]
  ring

theorem gap5 (n : ℕ) (hn : 0 < n) :
    targetIntegral n = 0 := by
  rw [gap3 n hn, gap4 n hn]

end

end ProofGap.Exercise2295
