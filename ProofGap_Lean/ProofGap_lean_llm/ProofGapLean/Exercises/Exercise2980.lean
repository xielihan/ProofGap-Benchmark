import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

namespace ProofGap.Exercise2980

noncomputable section

open scoped Interval

def cosineCoefficient (f : ℝ → ℝ) (n : ℕ) : ℝ :=
  1 / Real.pi *
    ∫ x in -Real.pi..Real.pi, f x * Real.cos ((n : ℝ) * x)

def sineCoefficient (f : ℝ → ℝ) (n : ℕ) : ℝ :=
  1 / Real.pi *
    ∫ x in -Real.pi..Real.pi, f x * Real.sin ((n : ℝ) * x)

def firstSplitSine (f : ℝ → ℝ) (n : ℕ) : ℝ :=
  2 / Real.pi *
    ((∫ x in 0..Real.pi / 2,
        f x * Real.sin ((n : ℝ) * x)) +
      ∫ x in Real.pi / 2..Real.pi,
        -f (Real.pi - x) * Real.sin ((n : ℝ) * x))

def firstReducedSine (f : ℝ → ℝ) (n : ℕ) : ℝ :=
  2 / Real.pi *
    ∫ x in 0..Real.pi / 2,
      (1 + (-1 : ℝ) ^ n) * f x * Real.sin ((n : ℝ) * x)

def secondReducedSine (f : ℝ → ℝ) (n : ℕ) : ℝ :=
  2 / Real.pi *
    ∫ x in 0..Real.pi / 2,
      (1 + (-1 : ℝ) ^ (n + 1)) *
        f x * Real.sin ((n : ℝ) * x)

private theorem negOnePowCases (n : ℕ) :
    (-1 : ℝ) ^ n = 1 ∨ (-1 : ℝ) ^ n = -1 := by
  induction n with
  | zero =>
      left
      simp
  | succ n ih =>
      rcases ih with h | h
      · right
        simp [pow_succ, h]
      · left
        simp [pow_succ, h]

private theorem symmetricOddIntegral (g : ℝ → ℝ) (a : ℝ)
    (hodd : Function.Odd g) :
    (∫ x in -a..a, g x) = 0 := by
  have hreflection :
      (∫ x in -a..a, g (0 - x)) = ∫ x in -a..a, g x := by
    rw [intervalIntegral.integral_comp_sub_left]
    ring_nf
  have hneg :
      (∫ x in -a..a, g x) = -(∫ x in -a..a, g x) := by
    calc
      (∫ x in -a..a, g x) = ∫ x in -a..a, g (0 - x) := hreflection.symm
      _ = ∫ x in -a..a, -g x := by
        apply intervalIntegral.integral_congr
        intro x hx
        simpa using hodd x
      _ = -(∫ x in -a..a, g x) := by
        rw [intervalIntegral.integral_neg]
  linarith

private theorem symmetricEvenIntegral (g : ℝ → ℝ) (a : ℝ)
    (ha : 0 ≤ a) (heven : Function.Even g) :
    (∫ x in -a..a, g x) = 2 * ∫ x in 0..a, g x := by
  have hneg_eq :
      (∫ x in -a..0, g x) = ∫ x in 0..a, g x := by
    calc
      (∫ x in -a..0, g x) = ∫ x in -a..0, g (0 - x) := by
        apply intervalIntegral.integral_congr
        intro x hx
        simpa using (heven x).symm
      _ = ∫ x in 0..a, g x := by
        rw [intervalIntegral.integral_comp_sub_left]
        ring_nf
  by_cases hpos : IntervalIntegrable g MeasureTheory.volume 0 a
  · have hneg : IntervalIntegrable g MeasureTheory.volume (-a) 0 := by
      have h :
          IntervalIntegrable (fun x : ℝ => g (0 - x))
            MeasureTheory.volume (0 - a) (0 - 0) :=
        (hpos.comp_sub_left (0 : ℝ)).symm
      have hfun : (fun x : ℝ => g (0 - x)) = g := by
        funext x
        simpa only [zero_sub] using heven x
      rw [hfun] at h
      simpa only [zero_sub, neg_zero] using h
    calc
      (∫ x in -a..a, g x) =
          (∫ x in -a..0, g x) + ∫ x in 0..a, g x :=
        (intervalIntegral.integral_add_adjacent_intervals hneg hpos).symm
      _ = 2 * ∫ x in 0..a, g x := by rw [hneg_eq]; ring
  · have hfull : ¬IntervalIntegrable g MeasureTheory.volume (-a) a := by
      intro h
      apply hpos
      apply h.mono_set
      simpa only [Set.uIcc_of_le ha,
        Set.uIcc_of_le (by linarith : -a ≤ a)] using
        (Set.Icc_subset_Icc (neg_nonpos.mpr ha) (le_refl a))
    rw [intervalIntegral.integral_undef hfull,
      intervalIntegral.integral_undef hpos]
    ring

private theorem reflectedIntegral (g : ℝ → ℝ) (c : ℝ)
    (hc : c = 1 ∨ c = -1)
    (hreflect : ∀ x, g (Real.pi - x) = c * g x) :
    (∫ x in 0..Real.pi, g x) =
        (∫ x in 0..Real.pi / 2, g x) +
          ∫ x in Real.pi / 2..Real.pi, g x ∧
      (∫ x in Real.pi / 2..Real.pi, g x) =
        c * ∫ x in 0..Real.pi / 2, g x := by
  have hcompFull :
      (∫ x in -Real.pi / 2..Real.pi / 2,
        g (Real.pi / 2 - x)) = ∫ x in 0..Real.pi, g x := by
    rw [intervalIntegral.integral_comp_sub_left]
    ring_nf
  have hcompHalf :
      (∫ x in 0..Real.pi / 2, g (Real.pi / 2 - x)) =
        ∫ x in 0..Real.pi / 2, g x := by
    rw [intervalIntegral.integral_comp_sub_left]
    ring_nf
  have hcompUpper :
      (∫ x in 0..Real.pi / 2, g (Real.pi - x)) =
        ∫ x in Real.pi / 2..Real.pi, g x := by
    rw [intervalIntegral.integral_comp_sub_left]
    ring_nf
  have hupper :
      (∫ x in Real.pi / 2..Real.pi, g x) =
        c * ∫ x in 0..Real.pi / 2, g x := by
    calc
      (∫ x in Real.pi / 2..Real.pi, g x) =
          ∫ x in 0..Real.pi / 2, g (Real.pi - x) := hcompUpper.symm
      _ = ∫ x in 0..Real.pi / 2, c * g x := by
        apply intervalIntegral.integral_congr
        intro x hx
        exact hreflect x
      _ = c * ∫ x in 0..Real.pi / 2, g x := by
        rw [intervalIntegral.integral_const_mul]
  constructor
  · rcases hc with rfl | rfl
    · have heven : Function.Even (fun x : ℝ => g (Real.pi / 2 - x)) := by
        intro x
        have hx : g (Real.pi / 2 + x) = g (Real.pi / 2 - x) := by
          convert hreflect (Real.pi / 2 - x) using 1 <;> ring_nf
        dsimp
        convert hx using 1 <;> ring_nf
      calc
        (∫ x in 0..Real.pi, g x) =
            ∫ x in -Real.pi / 2..Real.pi / 2,
              g (Real.pi / 2 - x) := hcompFull.symm
        _ = 2 * ∫ x in 0..Real.pi / 2,
              g (Real.pi / 2 - x) := by
                simpa only [neg_div] using
                  (symmetricEvenIntegral
                    (fun x : ℝ => g (Real.pi / 2 - x))
                    (Real.pi / 2)
                    (div_nonneg Real.pi_pos.le zero_le_two) heven)
        _ = 2 * ∫ x in 0..Real.pi / 2, g x := by rw [hcompHalf]
        _ = (∫ x in 0..Real.pi / 2, g x) +
              ∫ x in Real.pi / 2..Real.pi, g x := by
                rw [hupper]
                ring
    · have hodd : Function.Odd (fun x : ℝ => g (Real.pi / 2 - x)) := by
        intro x
        have hx : g (Real.pi / 2 + x) = -g (Real.pi / 2 - x) := by
          convert hreflect (Real.pi / 2 - x) using 1 <;> ring_nf
        dsimp
        convert hx using 1 <;> ring_nf
      calc
        (∫ x in 0..Real.pi, g x) =
            ∫ x in -Real.pi / 2..Real.pi / 2,
              g (Real.pi / 2 - x) := hcompFull.symm
        _ = 0 := by
          simpa only [neg_div] using
            (symmetricOddIntegral
              (fun x : ℝ => g (Real.pi / 2 - x)) (Real.pi / 2) hodd)
        _ = (∫ x in 0..Real.pi / 2, g x) +
              ∫ x in Real.pi / 2..Real.pi, g x := by
                rw [hupper]
                ring
  · exact hupper

theorem gap1 (f : ℝ → ℝ) (c : ℕ → ℝ)
    (hodd : Function.Odd f)
    (hreflect : ∀ x, f (Real.pi - x) = -f x)
    (hc : ∀ n, c n = cosineCoefficient f n) :
    ∀ n : ℕ, c n = 0 := by
  intro n
  rw [hc n]
  unfold cosineCoefficient
  have hodd_integrand :
      Function.Odd (fun x : ℝ => f x * Real.cos ((n : ℝ) * x)) := by
    intro x
    simpa [hodd x]
  rw [symmetricOddIntegral
    (fun x : ℝ => f x * Real.cos ((n : ℝ) * x)) Real.pi hodd_integrand]
  ring

theorem gap2 (f : ℝ → ℝ) (s : ℕ → ℝ)
    (hodd : Function.Odd f)
    (hreflect : ∀ x, f (Real.pi - x) = -f x)
    (hs : ∀ n, s n = sineCoefficient f n) :
    ∀ n : ℕ, 1 ≤ n → s n = firstSplitSine f n := by
  intro n hn
  rw [hs n]
  unfold sineCoefficient firstSplitSine
  have heven_integrand :
      Function.Even (fun x : ℝ => f x * Real.sin ((n : ℝ) * x)) := by
    intro x
    simpa [hodd x]
  have hreflected : ∀ x : ℝ,
      f (Real.pi - x) * Real.sin ((n : ℝ) * (Real.pi - x)) =
        (-1 : ℝ) ^ n * (f x * Real.sin ((n : ℝ) * x)) := by
    intro x
    rw [hreflect x, mul_sub, Real.sin_sub]
    simp [Real.sin_nat_mul_pi, Real.cos_nat_mul_pi]
    ring
  have hsplit :=
    (reflectedIntegral
      (fun x : ℝ => f x * Real.sin ((n : ℝ) * x))
      ((-1 : ℝ) ^ n) (negOnePowCases n) hreflected).1
  rw [symmetricEvenIntegral
    (fun x : ℝ => f x * Real.sin ((n : ℝ) * x))
    Real.pi Real.pi_pos.le heven_integrand, hsplit]
  simp_rw [hreflect]
  simp only [neg_neg]
  ring

theorem gap3 (f : ℝ → ℝ) (s : ℕ → ℝ)
    (hodd : Function.Odd f)
    (hreflect : ∀ x, f (Real.pi - x) = -f x)
    (hs : ∀ n, s n = sineCoefficient f n) :
    ∀ n : ℕ, 1 ≤ n → s n = firstReducedSine f n := by
  intro n hn
  rw [gap2 f s hodd hreflect hs n hn]
  unfold firstSplitSine firstReducedSine
  have hreflected : ∀ x : ℝ,
      f (Real.pi - x) * Real.sin ((n : ℝ) * (Real.pi - x)) =
        (-1 : ℝ) ^ n * (f x * Real.sin ((n : ℝ) * x)) := by
    intro x
    rw [hreflect x, mul_sub, Real.sin_sub]
    simp [Real.sin_nat_mul_pi, Real.cos_nat_mul_pi]
    ring
  have hupper :=
    (reflectedIntegral
      (fun x : ℝ => f x * Real.sin ((n : ℝ) * x))
      ((-1 : ℝ) ^ n) (negOnePowCases n) hreflected).2
  have hfactor :
      (∫ x in 0..Real.pi / 2,
        (1 + (-1 : ℝ) ^ n) * f x * Real.sin ((n : ℝ) * x)) =
        (1 + (-1 : ℝ) ^ n) *
          ∫ x in 0..Real.pi / 2, f x * Real.sin ((n : ℝ) * x) := by
    calc
      _ = ∫ x in 0..Real.pi / 2,
          (1 + (-1 : ℝ) ^ n) *
            (f x * Real.sin ((n : ℝ) * x)) := by
              apply intervalIntegral.integral_congr
              intro x hx
              ring
      _ = _ := by
        rw [intervalIntegral.integral_const_mul]
  simp_rw [hreflect]
  simp only [neg_neg]
  rw [hupper, hfactor]
  ring

theorem gap4 (f : ℝ → ℝ) (s : ℕ → ℝ)
    (hodd : Function.Odd f)
    (hreflect : ∀ x, f (Real.pi - x) = -f x)
    (hs : ∀ n, s n = sineCoefficient f n) :
    ∀ n : ℕ, 1 ≤ n → s n = firstReducedSine f n := by
  exact gap3 f s hodd hreflect hs

theorem gap5 (f : ℝ → ℝ) (s : ℕ → ℝ)
    (hodd : Function.Odd f)
    (hreflect : ∀ x, f (Real.pi - x) = -f x)
    (hs : ∀ n, s n = sineCoefficient f n) :
    ∀ n : ℕ, 1 ≤ n → s (2 * n - 1) = 0 := by
  intro n hn
  have hindex : 1 ≤ 2 * n - 1 := by omega
  rw [gap3 f s hodd hreflect hs (2 * n - 1) hindex]
  unfold firstReducedSine
  have hrewrite : 2 * n - 1 = 2 * (n - 1) + 1 := by omega
  rw [hrewrite]
  simp [pow_add, pow_mul]

theorem gap6 (f : ℝ → ℝ) (c : ℕ → ℝ)
    (hodd : Function.Odd f)
    (hreflect : ∀ x, f (Real.pi - x) = f x)
    (hc : ∀ n, c n = cosineCoefficient f n) :
    ∀ n : ℕ, c n = 0 := by
  intro n
  rw [hc n]
  unfold cosineCoefficient
  have hodd_integrand :
      Function.Odd (fun x : ℝ => f x * Real.cos ((n : ℝ) * x)) := by
    intro x
    simpa [hodd x]
  rw [symmetricOddIntegral
    (fun x : ℝ => f x * Real.cos ((n : ℝ) * x)) Real.pi hodd_integrand]
  ring

theorem gap7 (f : ℝ → ℝ) (s : ℕ → ℝ)
    (hodd : Function.Odd f)
    (hreflect : ∀ x, f (Real.pi - x) = f x)
    (hs : ∀ n, s n = sineCoefficient f n) :
    ∀ n : ℕ, 1 ≤ n → s n = secondReducedSine f n := by
  intro n hn
  rw [hs n]
  unfold sineCoefficient secondReducedSine
  have heven_integrand :
      Function.Even (fun x : ℝ => f x * Real.sin ((n : ℝ) * x)) := by
    intro x
    simpa [hodd x]
  have hreflected : ∀ x : ℝ,
      f (Real.pi - x) * Real.sin ((n : ℝ) * (Real.pi - x)) =
        (-(-1 : ℝ) ^ n) * (f x * Real.sin ((n : ℝ) * x)) := by
    intro x
    rw [hreflect x, mul_sub, Real.sin_sub]
    simp [Real.sin_nat_mul_pi, Real.cos_nat_mul_pi]
    ring
  have hcoefficient :
      -(-1 : ℝ) ^ n = 1 ∨ -(-1 : ℝ) ^ n = -1 := by
    rcases negOnePowCases n with h | h
    · right
      simp [h]
    · left
      simp [h]
  have hreflection :=
    reflectedIntegral
      (fun x : ℝ => f x * Real.sin ((n : ℝ) * x))
      (-(-1 : ℝ) ^ n) hcoefficient hreflected
  have hfactor :
      (∫ x in 0..Real.pi / 2,
        (1 + (-1 : ℝ) ^ (n + 1)) *
          f x * Real.sin ((n : ℝ) * x)) =
        (1 + (-1 : ℝ) ^ (n + 1)) *
          ∫ x in 0..Real.pi / 2, f x * Real.sin ((n : ℝ) * x) := by
    calc
      _ = ∫ x in 0..Real.pi / 2,
          (1 + (-1 : ℝ) ^ (n + 1)) *
            (f x * Real.sin ((n : ℝ) * x)) := by
              apply intervalIntegral.integral_congr
              intro x hx
              ring
      _ = _ := by
        rw [intervalIntegral.integral_const_mul]
  rw [symmetricEvenIntegral
    (fun x : ℝ => f x * Real.sin ((n : ℝ) * x))
    Real.pi Real.pi_pos.le heven_integrand,
    hreflection.1, hreflection.2, hfactor]
  simp [pow_succ]
  ring

theorem gap8 (f : ℝ → ℝ) (s : ℕ → ℝ)
    (hodd : Function.Odd f)
    (hreflect : ∀ x, f (Real.pi - x) = f x)
    (hs : ∀ n, s n = sineCoefficient f n) :
    ∀ n : ℕ, 1 ≤ n → s (2 * n) = 0 := by
  intro n hn
  have hindex : 1 ≤ 2 * n := by omega
  rw [gap7 f s hodd hreflect hs (2 * n) hindex]
  unfold secondReducedSine
  simp [pow_add, pow_mul]

theorem gap9 (f : ℝ → ℝ) (c s : ℕ → ℝ)
    (hodd : Function.Odd f)
    (hc : ∀ n, c n = cosineCoefficient f n)
    (hs : ∀ n, s n = sineCoefficient f n) :
    ((∀ x, f (Real.pi - x) = -f x) →
      (∀ n, c n = 0) ∧
        ∀ n, 1 ≤ n → s (2 * n - 1) = 0) ∧
    ((∀ x, f (Real.pi - x) = f x) →
      (∀ n, c n = 0) ∧
        ∀ n, 1 ≤ n → s (2 * n) = 0) := by
  constructor
  · intro hreflect
    constructor
    · exact gap1 f c hodd hreflect hc
    · exact gap5 f s hodd hreflect hs
  · intro hreflect
    constructor
    · exact gap6 f c hodd hreflect hc
    · exact gap8 f s hodd hreflect hs

end

end ProofGap.Exercise2980
