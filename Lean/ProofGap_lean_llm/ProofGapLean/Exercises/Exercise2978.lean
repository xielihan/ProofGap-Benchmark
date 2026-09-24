import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise2978

noncomputable section

open scoped Interval

def cosineCoefficient (f : ℝ → ℝ) (n : ℕ) : ℝ :=
  1 / Real.pi *
    ∫ x in -Real.pi..Real.pi, f x * Real.cos ((n : ℝ) * x)

def sineCoefficient (f : ℝ → ℝ) (n : ℕ) : ℝ :=
  1 / Real.pi *
    ∫ x in -Real.pi..Real.pi, f x * Real.sin ((n : ℝ) * x)

def splitCosineCoefficient (f : ℝ → ℝ) (n : ℕ) : ℝ :=
  1 / Real.pi *
    (-(∫ x in -Real.pi..0,
        f (Real.pi + x) * Real.cos ((n : ℝ) * x)) +
      ∫ x in 0..Real.pi, f x * Real.cos ((n : ℝ) * x))

def reducedCosineCoefficient (f : ℝ → ℝ) (n : ℕ) : ℝ :=
  1 / Real.pi *
    ∫ x in 0..Real.pi,
      (((-1 : ℝ) ^ (n + 1) + 1) *
        f x * Real.cos ((n : ℝ) * x))

private theorem pi_shift_integral_identities
    (g : ℝ → ℝ) (q : ℝ)
    (hq : q * q = 1)
    (hshift : ∀ x, g (x + Real.pi) = q * g x) :
    ((∫ x in -Real.pi..Real.pi, g x) =
      (∫ x in -Real.pi..0, g x) + ∫ x in 0..Real.pi, g x) ∧
    ((∫ x in -Real.pi..0, g x) =
      q * ∫ x in 0..Real.pi, g x) := by
  have htranslate :
      (∫ x in 0..Real.pi, g x) =
        ∫ x in -Real.pi..0, g (x + Real.pi) := by
    simpa using
      (intervalIntegral.integral_comp_add_right g (-Real.pi) 0 Real.pi).symm
  have hBA :
      (∫ x in 0..Real.pi, g x) =
        q * ∫ x in -Real.pi..0, g x := by
    calc
      (∫ x in 0..Real.pi, g x) =
          ∫ x in -Real.pi..0, g (x + Real.pi) := htranslate
      _ = ∫ x in -Real.pi..0, q * g x := by
        apply intervalIntegral.integral_congr
        intro x hx
        exact hshift x
      _ = q * ∫ x in -Real.pi..0, g x := by
        rw [intervalIntegral.integral_const_mul]
  have hAB :
      (∫ x in -Real.pi..0, g x) =
        q * ∫ x in 0..Real.pi, g x := by
    calc
      (∫ x in -Real.pi..0, g x) =
          (q * q) * ∫ x in -Real.pi..0, g x := by rw [hq]; simp
      _ = q * (q * ∫ x in -Real.pi..0, g x) := by ring
      _ = q * ∫ x in 0..Real.pi, g x := by rw [← hBA]
  have hnegpi_le_zero : -Real.pi ≤ 0 := by
    linarith [Real.pi_pos]
  have hnegpi_le_pi : -Real.pi ≤ Real.pi := by
    linarith [Real.pi_pos]
  constructor
  · by_cases hp : IntervalIntegrable g MeasureTheory.volume 0 Real.pi
    · by_cases hn : IntervalIntegrable g MeasureTheory.volume (-Real.pi) 0
      · exact (intervalIntegral.integral_add_adjacent_intervals hn hp).symm
      · have hfull :
            ¬IntervalIntegrable g MeasureTheory.volume (-Real.pi) Real.pi := by
          intro hf
          apply hn
          refine hf.mono_set ?_
          intro x hx
          simp only [Set.uIcc_of_le hnegpi_le_zero,
            Set.uIcc_of_le hnegpi_le_pi, Set.mem_Icc] at hx ⊢
          constructor <;> linarith [Real.pi_pos]
        have hBzero :
            (∫ x in 0..Real.pi, g x) = 0 := by
          calc
            (∫ x in 0..Real.pi, g x) =
                q * ∫ x in -Real.pi..0, g x := hBA
            _ = q * 0 := by
              rw [intervalIntegral.integral_undef hn]
            _ = 0 := mul_zero q
        calc
          (∫ x in -Real.pi..Real.pi, g x) = 0 :=
            intervalIntegral.integral_undef hfull
          _ = (∫ x in -Real.pi..0, g x) +
                ∫ x in 0..Real.pi, g x := by
            simpa only [intervalIntegral.integral_undef hn, hBzero, zero_add]
    · have hfull :
          ¬IntervalIntegrable g MeasureTheory.volume (-Real.pi) Real.pi := by
        intro hf
        apply hp
        refine hf.mono_set ?_
        intro x hx
        simp only [Set.uIcc_of_le Real.pi_pos.le,
          Set.uIcc_of_le hnegpi_le_pi, Set.mem_Icc] at hx ⊢
        constructor <;> linarith [Real.pi_pos]
      have hAzero :
          (∫ x in -Real.pi..0, g x) = 0 := by
        calc
          (∫ x in -Real.pi..0, g x) =
              q * ∫ x in 0..Real.pi, g x := hAB
          _ = q * 0 := by
            rw [intervalIntegral.integral_undef hp]
          _ = 0 := mul_zero q
      calc
        (∫ x in -Real.pi..Real.pi, g x) = 0 :=
          intervalIntegral.integral_undef hfull
        _ = (∫ x in -Real.pi..0, g x) +
              ∫ x in 0..Real.pi, g x := by
          simpa only [hAzero, intervalIntegral.integral_undef hp, zero_add]
  · exact hAB

theorem gap1 (f : ℝ → ℝ) (c s : ℕ → ℝ)
    (hcoeff : ∀ n,
      c n = cosineCoefficient f n ∧ s n = sineCoefficient f n) :
    ∀ n, c n = cosineCoefficient f n := by
  intro n
  exact (hcoeff n).1

theorem gap2 (f : ℝ → ℝ)
    (hanti : ∀ x, f (x + Real.pi) = -f x) :
    ∀ n, cosineCoefficient f n = splitCosineCoefficient f n := by
  intro n
  let g : ℝ → ℝ := fun x => f x * Real.cos ((n : ℝ) * x)
  let q : ℝ := (-1 : ℝ) ^ (n + 1)
  have hq : q * q = 1 := by
    dsimp [q]
    rw [← mul_pow]
    norm_num
  have hshift : ∀ x, g (x + Real.pi) = q * g x := by
    intro x
    simp [g, q, hanti x, mul_add, Real.cos_add,
      Real.cos_nat_mul_pi, Real.sin_nat_mul_pi, pow_succ] <;> ring
  have hids := pi_shift_integral_identities g q hq hshift
  have hneg :
      (∫ x in -Real.pi..0,
        f (Real.pi + x) * Real.cos ((n : ℝ) * x)) =
        -(∫ x in -Real.pi..0, g x) := by
    calc
      (∫ x in -Real.pi..0,
          f (Real.pi + x) * Real.cos ((n : ℝ) * x)) =
          ∫ x in -Real.pi..0, -g x := by
        apply intervalIntegral.integral_congr
        intro x hx
        change f (Real.pi + x) * Real.cos ((n : ℝ) * x) = -g x
        rw [show f (Real.pi + x) = -f x by
          simpa [add_comm] using hanti x]
        dsimp [g]
        ring
      _ = -(∫ x in -Real.pi..0, g x) := by
        rw [intervalIntegral.integral_neg]
  unfold cosineCoefficient splitCosineCoefficient
  change
    1 / Real.pi * (∫ x in -Real.pi..Real.pi, g x) =
      1 / Real.pi *
        (-(∫ x in -Real.pi..0,
          f (Real.pi + x) * Real.cos ((n : ℝ) * x)) +
          ∫ x in 0..Real.pi, g x)
  rw [hids.1, hneg]
  ring

theorem gap3 (f : ℝ → ℝ) (c : ℕ → ℝ)
    (hanti : ∀ x, f (x + Real.pi) = -f x)
    (hc : ∀ n, c n = cosineCoefficient f n) :
    ∀ n, c n = splitCosineCoefficient f n := by
  intro n
  calc
    c n = cosineCoefficient f n := hc n
    _ = splitCosineCoefficient f n := gap2 f hanti n

theorem gap4 (f : ℝ → ℝ) (c : ℕ → ℝ)
    (hanti : ∀ x, f (x + Real.pi) = -f x)
    (hc : ∀ n, c n = cosineCoefficient f n) :
    ∀ n, c n = reducedCosineCoefficient f n := by
  intro n
  let g : ℝ → ℝ := fun x => f x * Real.cos ((n : ℝ) * x)
  let q : ℝ := (-1 : ℝ) ^ (n + 1)
  have hq : q * q = 1 := by
    dsimp [q]
    rw [← mul_pow]
    norm_num
  have hshift : ∀ x, g (x + Real.pi) = q * g x := by
    intro x
    simp [g, q, hanti x, mul_add, Real.cos_add,
      Real.cos_nat_mul_pi, Real.sin_nat_mul_pi, pow_succ] <;> ring
  have hids := pi_shift_integral_identities g q hq hshift
  rw [hc n]
  unfold cosineCoefficient reducedCosineCoefficient
  change
    1 / Real.pi * (∫ x in -Real.pi..Real.pi, g x) =
      1 / Real.pi *
        (∫ x in 0..Real.pi,
          (q + 1) * f x * Real.cos ((n : ℝ) * x))
  congr 1
  calc
    (∫ x in -Real.pi..Real.pi, g x) =
        (∫ x in -Real.pi..0, g x) +
          ∫ x in 0..Real.pi, g x := hids.1
    _ = q * (∫ x in 0..Real.pi, g x) +
          ∫ x in 0..Real.pi, g x := by rw [hids.2]
    _ = (q + 1) * (∫ x in 0..Real.pi, g x) := by ring
    _ = ∫ x in 0..Real.pi, (q + 1) * g x := by
      rw [intervalIntegral.integral_const_mul]
    _ = ∫ x in 0..Real.pi,
          (q + 1) * f x * Real.cos ((n : ℝ) * x) := by
      apply intervalIntegral.integral_congr
      intro x hx
      dsimp [g]
      ring

theorem gap5 (f : ℝ → ℝ) (c : ℕ → ℝ)
    (hanti : ∀ x, f (x + Real.pi) = -f x)
    (hc : ∀ n, c n = cosineCoefficient f n) :
    ∀ n : ℕ, c (2 * n) = 0 := by
  intro n
  rw [gap4 f c hanti hc (2 * n)]
  unfold reducedCosineCoefficient
  have hpow : (-1 : ℝ) ^ (2 * n + 1) = -1 := by
    rw [pow_succ, pow_mul]
    norm_num
  rw [hpow]
  simp

theorem gap6 (f : ℝ → ℝ) (s : ℕ → ℝ)
    (hanti : ∀ x, f (x + Real.pi) = -f x)
    (hs : ∀ n, s n = sineCoefficient f n) :
    ∀ n : ℕ, 1 ≤ n → s (2 * n) = 0 := by
  intro n hn
  let g : ℝ → ℝ :=
    fun x => f x * Real.sin (((2 * n : ℕ) : ℝ) * x)
  let q : ℝ := (-1 : ℝ) ^ (2 * n + 1)
  have hq : q * q = 1 := by
    dsimp [q]
    rw [← mul_pow]
    norm_num
  have hqval : q = -1 := by
    dsimp [q]
    rw [pow_succ, pow_mul]
    norm_num
  have hshift : ∀ x, g (x + Real.pi) = q * g x := by
    intro x
    dsimp [g]
    rw [hanti x]
    rw [mul_add, Real.sin_add, Real.sin_nat_mul_pi,
      Real.cos_nat_mul_pi]
    dsimp [q]
    rw [pow_succ]
    ring
  have hids := pi_shift_integral_identities g q hq hshift
  rw [hs (2 * n)]
  unfold sineCoefficient
  change 1 / Real.pi * (∫ x in -Real.pi..Real.pi, g x) = 0
  rw [hids.1, hids.2, hqval]
  ring

theorem gap7 (f : ℝ → ℝ) (c s : ℕ → ℝ)
    (hanti : ∀ x, f (x + Real.pi) = -f x)
    (hc : ∀ n, c n = cosineCoefficient f n)
    (hs : ∀ n, s n = sineCoefficient f n) :
    (∀ n : ℕ, c (2 * n) = 0) ∧
      (∀ n : ℕ, 1 ≤ n → s (2 * n) = 0) := by
  constructor
  · exact gap5 f c hanti hc
  · exact gap6 f s hanti hs

end

end ProofGap.Exercise2978
