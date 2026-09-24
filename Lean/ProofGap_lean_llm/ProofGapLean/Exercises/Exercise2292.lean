import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Lean.Elab.Tactic.Omega
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

open scoped Interval

namespace ProofGap.Exercise2292

noncomputable section

def quotient (n : ℕ) (x : ℝ) : ℝ :=
  Real.cos ((2 * n + 1 : ℕ) * x) / Real.cos x

def cosineExpansion (n : ℕ) (x : ℝ) : ℝ :=
  (-1 : ℝ) ^ n +
    2 * ∑ j ∈ Finset.range n,
      (-1 : ℝ) ^ (n - (j + 1)) *
        Real.cos ((2 * (j + 1) : ℕ) * x)

def complexExpansion (n : ℕ) (x : ℝ) : ℂ :=
  (-1 : ℂ) ^ n +
    ∑ j ∈ Finset.range n,
      (-1 : ℂ) ^ (n - (j + 1)) *
        (Complex.exp (Complex.I * ((2 * (j + 1) : ℕ) : ℝ) * x) +
          Complex.exp (-Complex.I * ((2 * (j + 1) : ℕ) : ℝ) * x))

private theorem exp_pair (y : ℝ) :
    Complex.exp (Complex.I * (y : ℂ)) +
        Complex.exp (-Complex.I * (y : ℂ)) =
      ((2 * Real.cos y : ℝ) : ℂ) := by
  have hpos : Complex.I * (y : ℂ) = (y : ℂ) * Complex.I := by
    ring
  have hneg : -Complex.I * (y : ℂ) = ((-y : ℝ) : ℂ) * Complex.I := by
    simpa [mul_comm]
  rw [hpos, hneg, Complex.exp_mul_I, Complex.exp_mul_I]
  simp [Real.cos_neg, Real.sin_neg] <;> ring

private theorem quotient_eq_cosineExpansion
    (n : ℕ) (x : ℝ) (hx : Real.cos x ≠ 0) :
    quotient n x = cosineExpansion n x := by
  induction n with
  | zero =>
      simp [quotient, cosineExpansion, hx]
  | succ n ih =>
      let c : ℝ := ((2 * (n + 1) : ℕ) : ℝ) * x
      have hnext :
          (((2 * (n + 1) + 1 : ℕ) : ℝ) * x) = c + x := by
        dsimp [c]
        push_cast
        ring
      have hprev :
          (((2 * n + 1 : ℕ) : ℝ) * x) = c - x := by
        dsimp [c]
        push_cast
        ring
      have htrig :
          Real.cos (((2 * (n + 1) + 1 : ℕ) : ℝ) * x) =
            2 * Real.cos c * Real.cos x -
              Real.cos (((2 * n + 1 : ℕ) : ℝ) * x) := by
        rw [hnext, hprev, Real.cos_add, Real.cos_sub]
        ring
      have hrec :
          quotient (n + 1) x = 2 * Real.cos c - quotient n x := by
        unfold quotient
        rw [htrig]
        field_simp [hx]
      have hsum :
          (∑ j ∈ Finset.range n,
              (-1 : ℝ) ^ ((n + 1) - (j + 1)) *
                Real.cos ((2 * (j + 1) : ℕ) * x)) =
            -(∑ j ∈ Finset.range n,
                (-1 : ℝ) ^ (n - (j + 1)) *
                  Real.cos ((2 * (j + 1) : ℕ) * x)) := by
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro j hj
        have hjn : j < n := Finset.mem_range.mp hj
        have he : (n + 1) - (j + 1) = (n - (j + 1)) + 1 := by
          omega
        rw [he, pow_succ]
        ring
      have hexp :
          cosineExpansion (n + 1) x =
            2 * Real.cos c - cosineExpansion n x := by
        unfold cosineExpansion
        rw [Finset.sum_range_succ, hsum]
        simp [c, pow_succ]
        ring
      calc
        quotient (n + 1) x = 2 * Real.cos c - quotient n x := hrec
        _ = 2 * Real.cos c - cosineExpansion n x := by rw [ih]
        _ = cosineExpansion (n + 1) x := hexp.symm

private theorem complexExpansion_eq_cosineExpansion (n : ℕ) (x : ℝ) :
    complexExpansion n x = (cosineExpansion n x : ℂ) := by
  have hterm (j : ℕ) :
      Complex.exp (Complex.I * ((2 * (j + 1) : ℕ) : ℝ) * x) +
          Complex.exp (-Complex.I * ((2 * (j + 1) : ℕ) : ℝ) * x) =
        ((2 * Real.cos (((2 * (j + 1) : ℕ) : ℝ) * x) : ℝ) : ℂ) := by
    simpa [mul_assoc] using
      exp_pair (((2 * (j + 1) : ℕ) : ℝ) * x)
  unfold complexExpansion cosineExpansion
  simp_rw [hterm]
  have hreal :
      (-1 : ℝ) ^ n +
          ∑ j ∈ Finset.range n,
            (-1 : ℝ) ^ (n - (j + 1)) *
              (2 * Real.cos (((2 * (j + 1) : ℕ) : ℝ) * x)) =
        (-1 : ℝ) ^ n +
          2 * ∑ j ∈ Finset.range n,
            (-1 : ℝ) ^ (n - (j + 1)) *
              Real.cos (((2 * (j + 1) : ℕ) : ℝ) * x) := by
    rw [Finset.mul_sum]
    apply congrArg (fun z : ℝ => (-1 : ℝ) ^ n + z)
    apply Finset.sum_congr rfl
    intro j hj
    ring
  exact_mod_cast hreal

private theorem integral_cos_nat_mul_pi (k : ℕ) (hk : k ≠ 0) :
    (∫ x in 0..Real.pi, Real.cos ((k : ℝ) * x)) = 0 := by
  have hk' : (k : ℝ) ≠ 0 := by
    exact_mod_cast hk
  have hderiv (x : ℝ) :
      HasDerivAt
        (fun t : ℝ => Real.sin ((k : ℝ) * t) / (k : ℝ))
        (Real.cos ((k : ℝ) * x)) x := by
    simpa [hk'] using
      (((Real.hasDerivAt_sin ((k : ℝ) * x)).comp x
          ((hasDerivAt_id x).const_mul (k : ℝ))).div_const (k : ℝ))
  have hint :
      IntervalIntegrable (fun x : ℝ => Real.cos ((k : ℝ) * x))
        MeasureTheory.volume 0 Real.pi :=
    (Real.continuous_cos.comp
      (continuous_const.mul continuous_id)).intervalIntegrable 0 Real.pi
  have hs : Real.sin (Real.pi * (k : ℝ)) = 0 := by
    simpa [mul_comm] using Real.sin_nat_mul_pi k
  calc
    (∫ x in 0..Real.pi, Real.cos ((k : ℝ) * x)) =
        Real.sin ((k : ℝ) * Real.pi) / (k : ℝ) -
          Real.sin ((k : ℝ) * 0) / (k : ℝ) := by
      exact intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun x _ => hderiv x) hint
    _ = 0 := by
      rw [show (k : ℝ) * Real.pi = Real.pi * (k : ℝ) by ring, hs]
      simp

theorem gap1 (n : ℕ) (x : ℝ) (hx : Real.cos x ≠ 0) :
    (quotient n x : ℂ) =
      (Complex.exp (Complex.I * ((2 * n + 1 : ℕ) : ℝ) * x) +
          Complex.exp (-Complex.I * ((2 * n + 1 : ℕ) : ℝ) * x)) /
        (Complex.exp (Complex.I * x) + Complex.exp (-Complex.I * x)) := by
  let y : ℝ := ((2 * n + 1 : ℕ) : ℝ) * x
  have hnum :
      Complex.exp (Complex.I * ((2 * n + 1 : ℕ) : ℝ) * x) +
          Complex.exp (-Complex.I * ((2 * n + 1 : ℕ) : ℝ) * x) =
        ((2 * Real.cos y : ℝ) : ℂ) := by
    simpa [y, mul_assoc] using exp_pair y
  have hden :
      Complex.exp (Complex.I * x) + Complex.exp (-Complex.I * x) =
        ((2 * Real.cos x : ℝ) : ℂ) := by
    simpa [mul_assoc] using exp_pair x
  rw [hnum, hden]
  change ((Real.cos y / Real.cos x : ℝ) : ℂ) =
    ((2 * Real.cos y : ℝ) : ℂ) / ((2 * Real.cos x : ℝ) : ℂ)
  norm_cast
  field_simp [hx]

theorem gap2 (n : ℕ) (x : ℝ) (hx : Real.cos x ≠ 0) :
    (quotient n x : ℂ) = complexExpansion n x := by
  calc
    (quotient n x : ℂ) = (cosineExpansion n x : ℂ) :=
      congrArg (fun z : ℝ => (z : ℂ))
        (quotient_eq_cosineExpansion n x hx)
    _ = complexExpansion n x :=
      (complexExpansion_eq_cosineExpansion n x).symm

theorem gap3 (n : ℕ) (x : ℝ) (hx : Real.cos x ≠ 0) :
    quotient n x = cosineExpansion n x := by
  exact quotient_eq_cosineExpansion n x hx

theorem gap4 (n : ℕ) :
    (∫ x in 0..Real.pi, quotient n x) =
      (-1 : ℝ) ^ n * Real.pi := by
  have hpi0 : 0 ≤ Real.pi := Real.pi_pos.le
  have hhalf :
      ∀ᵐ x : ℝ ∂MeasureTheory.volume, x ≠ Real.pi / 2 := by
    rw [MeasureTheory.ae_iff]
    simp
  have hAE :
      ∀ᵐ x : ℝ ∂MeasureTheory.volume,
        x ∈ Set.uIoc 0 Real.pi → quotient n x = cosineExpansion n x := by
    filter_upwards [hhalf] with x hxhalf
    intro hxmem
    have hx : x ∈ Set.Ioc (0 : ℝ) Real.pi := by
      simpa [Set.uIoc_of_le hpi0] using hxmem
    have hcos : Real.cos x ≠ 0 := by
      have hnegHalf : -(Real.pi / 2) < 0 := by
        exact neg_lt_zero.mpr (div_pos Real.pi_pos (by norm_num))
      rcases lt_trichotomy x (Real.pi / 2) with hlt | heq | hgt
      · have hy : x ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
          constructor
          · exact lt_trans hnegHalf hx.1
          · exact hlt
        exact ne_of_gt (Real.cos_pos_of_mem_Ioo hy)
      · exact (hxhalf heq).elim
      · have hy : Real.pi - x ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
          constructor
          · exact lt_of_lt_of_le hnegHalf (sub_nonneg.mpr hx.2)
          · linarith
        have hc : 0 < Real.cos (Real.pi - x) := Real.cos_pos_of_mem_Ioo hy
        intro hz
        rw [Real.cos_pi_sub, hz] at hc
        simp at hc
    exact quotient_eq_cosineExpansion n x hcos
  rw [intervalIntegral.integral_congr_ae hAE]
  let s : ℝ → ℝ := fun x =>
    ∑ j ∈ Finset.range n,
      (-1 : ℝ) ^ (n - (j + 1)) *
        Real.cos ((2 * (j + 1) : ℕ) * x)
  have hs_cont : Continuous s := by
    dsimp [s]
    fun_prop
  have hconst_int :
      IntervalIntegrable (fun _ : ℝ => (-1 : ℝ) ^ n)
        MeasureTheory.volume 0 Real.pi :=
    continuous_const.intervalIntegrable 0 Real.pi
  have hscaled_int :
      IntervalIntegrable (fun x : ℝ => 2 * s x)
        MeasureTheory.volume 0 Real.pi :=
    (continuous_const.mul hs_cont).intervalIntegrable 0 Real.pi
  have hterm_zero (j : ℕ) (hj : j ∈ Finset.range n) :
      (∫ x in 0..Real.pi,
        (-1 : ℝ) ^ (n - (j + 1)) *
          Real.cos ((2 * (j + 1) : ℕ) * x)) = 0 := by
    rw [intervalIntegral.integral_const_mul]
    rw [integral_cos_nat_mul_pi (2 * (j + 1)) (by omega)]
    simp
  have hsum_zero : (∫ x in 0..Real.pi, s x) = 0 := by
    dsimp [s]
    rw [intervalIntegral.integral_finset_sum]
    · apply Finset.sum_eq_zero
      intro j hj
      exact hterm_zero j hj
    · intro j hj
      exact
        (continuous_const.mul
          (Real.continuous_cos.comp (continuous_const.mul continuous_id))).intervalIntegrable
            0 Real.pi
  change
    (∫ x in 0..Real.pi,
      ((-1 : ℝ) ^ n + 2 * s x)) = (-1 : ℝ) ^ n * Real.pi
  rw [intervalIntegral.integral_add hconst_int hscaled_int]
  rw [intervalIntegral.integral_const_mul, hsum_zero]
  simpa [intervalIntegral.integral_const, mul_comm]

end

end ProofGap.Exercise2292
