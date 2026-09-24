import Mathlib.Algebra.Ring.Periodic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

namespace ProofGap.Exercise2983

noncomputable section

open scoped Interval

def cosineCoefficient (f : ℝ → ℝ) (n : ℕ) : ℝ :=
  1 / Real.pi *
    ∫ x in -Real.pi..Real.pi, f x * Real.cos ((n : ℝ) * x)

def sineCoefficient (f : ℝ → ℝ) (n : ℕ) : ℝ :=
  1 / Real.pi *
    ∫ x in -Real.pi..Real.pi, f x * Real.sin ((n : ℝ) * x)

def shiftedCosineCoefficient (f : ℝ → ℝ) (h : ℝ) (n : ℕ) : ℝ :=
  1 / Real.pi *
    ∫ x in -Real.pi..Real.pi,
      f (x + h) * Real.cos ((n : ℝ) * x)

def changedCosineIntegral (f : ℝ → ℝ) (h : ℝ) (n : ℕ) : ℝ :=
  1 / Real.pi *
    ∫ y in -Real.pi + h..Real.pi + h,
      f y *
        (Real.cos ((n : ℝ) * h) * Real.cos ((n : ℝ) * y) +
          Real.sin ((n : ℝ) * h) * Real.sin ((n : ℝ) * y))

def centeredCosineIntegral (f : ℝ → ℝ) (h : ℝ) (n : ℕ) : ℝ :=
  1 / Real.pi *
    ((∫ x in -Real.pi..Real.pi,
        f x * Real.cos ((n : ℝ) * x) *
          Real.cos ((n : ℝ) * h)) +
      ∫ x in -Real.pi..Real.pi,
        f x * Real.sin ((n : ℝ) * x) *
          Real.sin ((n : ℝ) * h))

def shiftedSineCoefficient (f : ℝ → ℝ) (h : ℝ) (n : ℕ) : ℝ :=
  1 / Real.pi *
    ∫ x in -Real.pi..Real.pi,
      f (x + h) * Real.sin ((n : ℝ) * x)

private theorem fourierTerm_periodic (f : ℝ → ℝ)
    (hper : Function.Periodic f (2 * Real.pi)) (n : ℕ) (a b : ℝ) :
    Function.Periodic
      (fun x => f x *
        (a * Real.cos ((n : ℝ) * x) + b * Real.sin ((n : ℝ) * x)))
      (2 * Real.pi) := by
  intro x
  change f (x + 2 * Real.pi) *
      (a * Real.cos ((n : ℝ) * (x + 2 * Real.pi)) +
        b * Real.sin ((n : ℝ) * (x + 2 * Real.pi))) =
    f x * (a * Real.cos ((n : ℝ) * x) + b * Real.sin ((n : ℝ) * x))
  rw [hper x]
  rw [show (n : ℝ) * (x + 2 * Real.pi) =
    (n : ℝ) * x + (n : ℝ) * (2 * Real.pi) by ring]
  rw [Real.cos_add_nat_mul_two_pi, Real.sin_add_nat_mul_two_pi]

private theorem periodicIntegral_shift (g : ℝ → ℝ)
    (hg : Function.Periodic g (2 * Real.pi)) (h : ℝ) :
    (∫ x in -Real.pi + h..Real.pi + h, g x) =
      ∫ x in -Real.pi..Real.pi, g x := by
  convert hg.intervalIntegral_add_eq (-Real.pi + h) (-Real.pi) using 1 <;> ring

private theorem integral_fourierTerm (f : ℝ → ℝ)
    (hInt : IntervalIntegrable f MeasureTheory.volume (-Real.pi) Real.pi)
    (n : ℕ) (a b : ℝ) :
    (∫ x in -Real.pi..Real.pi,
        f x * (a * Real.cos ((n : ℝ) * x) + b * Real.sin ((n : ℝ) * x))) =
      (∫ x in -Real.pi..Real.pi, f x * Real.cos ((n : ℝ) * x)) * a +
        (∫ x in -Real.pi..Real.pi, f x * Real.sin ((n : ℝ) * x)) * b := by
  have hcos : Continuous (fun x : ℝ => Real.cos ((n : ℝ) * x)) :=
    Real.continuous_cos.comp (continuous_const.mul continuous_id)
  have hsin : Continuous (fun x : ℝ => Real.sin ((n : ℝ) * x)) :=
    Real.continuous_sin.comp (continuous_const.mul continuous_id)
  have hcosInt : IntervalIntegrable
      (fun x => f x * Real.cos ((n : ℝ) * x)) MeasureTheory.volume
      (-Real.pi) Real.pi := hInt.mul_continuousOn hcos.continuousOn
  have hsinInt : IntervalIntegrable
      (fun x => f x * Real.sin ((n : ℝ) * x)) MeasureTheory.volume
      (-Real.pi) Real.pi := hInt.mul_continuousOn hsin.continuousOn
  calc
    (∫ x in -Real.pi..Real.pi,
        f x * (a * Real.cos ((n : ℝ) * x) + b * Real.sin ((n : ℝ) * x))) =
        ∫ x in -Real.pi..Real.pi,
          (f x * Real.cos ((n : ℝ) * x) * a +
            f x * Real.sin ((n : ℝ) * x) * b) := by
      apply intervalIntegral.integral_congr
      intro x hx
      ring
    _ = (∫ x in -Real.pi..Real.pi,
          f x * Real.cos ((n : ℝ) * x) * a) +
        ∫ x in -Real.pi..Real.pi,
          f x * Real.sin ((n : ℝ) * x) * b :=
      intervalIntegral.integral_add (hcosInt.mul_const a) (hsinInt.mul_const b)
    _ = (∫ x in -Real.pi..Real.pi,
          f x * Real.cos ((n : ℝ) * x)) * a +
        (∫ x in -Real.pi..Real.pi,
          f x * Real.sin ((n : ℝ) * x)) * b := by
      rw [intervalIntegral.integral_mul_const,
        intervalIntegral.integral_mul_const]

theorem gap1 (f : ℝ → ℝ) (cbar : ℝ → ℕ → ℝ)
    (hcbar : ∀ h n, cbar h n = shiftedCosineCoefficient f h n) :
    ∀ n h, cbar h n = shiftedCosineCoefficient f h n := by
  intro n h
  exact hcbar h n

theorem gap2 (f : ℝ → ℝ) (hper : Function.Periodic f (2 * Real.pi)) :
    ∀ n h,
      shiftedCosineCoefficient f h n =
        changedCosineIntegral f h n := by
  intro n h
  unfold shiftedCosineCoefficient changedCosineIntegral
  congr 1
  rw [← intervalIntegral.integral_comp_add_right
    (fun y => f y *
      (Real.cos ((n : ℝ) * h) * Real.cos ((n : ℝ) * y) +
        Real.sin ((n : ℝ) * h) * Real.sin ((n : ℝ) * y))) h]
  apply intervalIntegral.integral_congr
  intro x hx
  change f (x + h) * Real.cos ((n : ℝ) * x) =
    f (x + h) *
      (Real.cos ((n : ℝ) * h) * Real.cos ((n : ℝ) * (x + h)) +
        Real.sin ((n : ℝ) * h) * Real.sin ((n : ℝ) * (x + h)))
  congr 1
  rw [show (n : ℝ) * x = (n : ℝ) * (x + h) - (n : ℝ) * h by ring,
    Real.cos_sub]
  ring

theorem gap3 (f : ℝ → ℝ) (cbar : ℝ → ℕ → ℝ)
    (hper : Function.Periodic f (2 * Real.pi))
    (hcbar : ∀ h n, cbar h n = shiftedCosineCoefficient f h n) :
    ∀ n h, cbar h n = changedCosineIntegral f h n := by
  intro n h
  rw [hcbar h n]
  exact gap2 f hper n h

theorem gap4 (f : ℝ → ℝ) (cbar : ℝ → ℕ → ℝ)
    (hper : Function.Periodic f (2 * Real.pi))
    (hInt : IntervalIntegrable f MeasureTheory.volume (-Real.pi) Real.pi)
    (hcbar : ∀ h n, cbar h n = shiftedCosineCoefficient f h n) :
    ∀ n h, cbar h n = centeredCosineIntegral f h n := by
  intro n h
  rw [hcbar h n, gap2 f hper n h]
  unfold changedCosineIntegral centeredCosineIntegral
  apply congrArg (fun z : ℝ => 1 / Real.pi * z)
  calc
    (∫ x in -Real.pi + h..Real.pi + h,
        f x *
          (Real.cos ((n : ℝ) * h) * Real.cos ((n : ℝ) * x) +
            Real.sin ((n : ℝ) * h) * Real.sin ((n : ℝ) * x))) =
        ∫ x in -Real.pi..Real.pi,
          f x *
            (Real.cos ((n : ℝ) * h) * Real.cos ((n : ℝ) * x) +
              Real.sin ((n : ℝ) * h) * Real.sin ((n : ℝ) * x)) :=
      periodicIntegral_shift _
        (fourierTerm_periodic f hper n
          (Real.cos ((n : ℝ) * h)) (Real.sin ((n : ℝ) * h))) h
    _ =
        (∫ x in -Real.pi..Real.pi,
          f x * Real.cos ((n : ℝ) * x)) * Real.cos ((n : ℝ) * h) +
        (∫ x in -Real.pi..Real.pi,
          f x * Real.sin ((n : ℝ) * x)) * Real.sin ((n : ℝ) * h) :=
      integral_fourierTerm f hInt n
        (Real.cos ((n : ℝ) * h)) (Real.sin ((n : ℝ) * h))
    _ =
        (∫ x in -Real.pi..Real.pi,
          f x * Real.cos ((n : ℝ) * x) * Real.cos ((n : ℝ) * h)) +
        ∫ x in -Real.pi..Real.pi,
          f x * Real.sin ((n : ℝ) * x) * Real.sin ((n : ℝ) * h) := by
      rw [intervalIntegral.integral_mul_const,
        intervalIntegral.integral_mul_const]

theorem gap5 (f : ℝ → ℝ) (c s : ℕ → ℝ) :
    (∀ n, c n = cosineCoefficient f n) →
    (∀ n, s n = sineCoefficient f n) →
    ∀ n h,
      centeredCosineIntegral f h n =
        c n * Real.cos ((n : ℝ) * h) +
          s n * Real.sin ((n : ℝ) * h) := by
  intro hc hs n h
  rw [hc n, hs n]
  unfold centeredCosineIntegral cosineCoefficient sineCoefficient
  simp only [intervalIntegral.integral_mul_const]
  ring

theorem gap6 (f : ℝ → ℝ) (c s : ℕ → ℝ)
    (cbar : ℝ → ℕ → ℝ)
    (hper : Function.Periodic f (2 * Real.pi))
    (hInt : IntervalIntegrable f MeasureTheory.volume (-Real.pi) Real.pi)
    (hc : ∀ n, c n = cosineCoefficient f n)
    (hs : ∀ n, s n = sineCoefficient f n)
    (hcbar : ∀ h n, cbar h n = shiftedCosineCoefficient f h n) :
    ∀ n h,
      cbar h n =
        c n * Real.cos ((n : ℝ) * h) +
          s n * Real.sin ((n : ℝ) * h) := by
  intro n h
  rw [gap4 f cbar hper hInt hcbar n h]
  exact gap5 f c s hc hs n h

theorem gap7 (f : ℝ → ℝ) (c s : ℕ → ℝ)
    (sbar : ℝ → ℕ → ℝ)
    (hper : Function.Periodic f (2 * Real.pi))
    (hInt : IntervalIntegrable f MeasureTheory.volume (-Real.pi) Real.pi)
    (hc : ∀ n, c n = cosineCoefficient f n)
    (hs : ∀ n, s n = sineCoefficient f n)
    (hsbar : ∀ h n, sbar h n = shiftedSineCoefficient f h n) :
    ∀ n h,
      sbar h n =
        s n * Real.cos ((n : ℝ) * h) -
          c n * Real.sin ((n : ℝ) * h) := by
  intro n h
  rw [hsbar h n, hs n, hc n]
  unfold shiftedSineCoefficient sineCoefficient cosineCoefficient
  have hshift :
      (∫ x in -Real.pi..Real.pi,
          f (x + h) * Real.sin ((n : ℝ) * x)) =
        (∫ x in -Real.pi..Real.pi,
          f x * Real.sin ((n : ℝ) * x)) * Real.cos ((n : ℝ) * h) -
        (∫ x in -Real.pi..Real.pi,
          f x * Real.cos ((n : ℝ) * x)) * Real.sin ((n : ℝ) * h) := by
    calc
      (∫ x in -Real.pi..Real.pi,
          f (x + h) * Real.sin ((n : ℝ) * x)) =
          ∫ x in -Real.pi..Real.pi,
            f (x + h) *
              (-Real.sin ((n : ℝ) * h) * Real.cos ((n : ℝ) * (x + h)) +
                Real.cos ((n : ℝ) * h) * Real.sin ((n : ℝ) * (x + h))) := by
        apply intervalIntegral.integral_congr
        intro x hx
        change f (x + h) * Real.sin ((n : ℝ) * x) =
          f (x + h) *
            (-Real.sin ((n : ℝ) * h) * Real.cos ((n : ℝ) * (x + h)) +
              Real.cos ((n : ℝ) * h) * Real.sin ((n : ℝ) * (x + h)))
        congr 1
        rw [show (n : ℝ) * x = (n : ℝ) * (x + h) - (n : ℝ) * h by ring,
          Real.sin_sub]
        ring
      _ = ∫ x in -Real.pi + h..Real.pi + h,
          f x *
            (-Real.sin ((n : ℝ) * h) * Real.cos ((n : ℝ) * x) +
              Real.cos ((n : ℝ) * h) * Real.sin ((n : ℝ) * x)) := by
        simpa only using
          (intervalIntegral.integral_comp_add_right
            (f := fun x : ℝ =>
              f x *
                (-Real.sin ((n : ℝ) * h) * Real.cos ((n : ℝ) * x) +
                  Real.cos ((n : ℝ) * h) * Real.sin ((n : ℝ) * x))) h)
      _ = ∫ x in -Real.pi..Real.pi,
          f x *
            (-Real.sin ((n : ℝ) * h) * Real.cos ((n : ℝ) * x) +
              Real.cos ((n : ℝ) * h) * Real.sin ((n : ℝ) * x)) :=
        periodicIntegral_shift _
          (fourierTerm_periodic f hper n
            (-Real.sin ((n : ℝ) * h)) (Real.cos ((n : ℝ) * h))) h
      _ =
          (∫ x in -Real.pi..Real.pi,
            f x * Real.sin ((n : ℝ) * x)) * Real.cos ((n : ℝ) * h) -
          (∫ x in -Real.pi..Real.pi,
            f x * Real.cos ((n : ℝ) * x)) * Real.sin ((n : ℝ) * h) := by
        rw [integral_fourierTerm f hInt n
          (-Real.sin ((n : ℝ) * h)) (Real.cos ((n : ℝ) * h))]
        ring
  rw [hshift]
  ring

end

end ProofGap.Exercise2983
