import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Topology.Algebra.InfiniteSum.Basic

namespace ProofGap.Exercise2868

noncomputable section

def rawExponentialTerm (x α : ℝ) (n : ℕ) : ℂ :=
  1 / (Nat.factorial n : ℂ) *
    ((x : ℂ) * Complex.exp (Complex.I * α)) ^ n

def separatedExponentialTerm (x α : ℝ) (n : ℕ) : ℂ :=
  (x : ℂ) ^ n / (Nat.factorial n : ℂ) *
    Complex.exp (Complex.I * (n : ℝ) * α)

def trigonometricExponentialTerm (x α : ℝ) (n : ℕ) : ℂ :=
  (x : ℂ) ^ n / (Nat.factorial n : ℂ) *
    ((Real.cos ((n : ℝ) * α) : ℂ) +
      Complex.I * Real.sin ((n : ℝ) * α))

def realPartTerm (x α : ℝ) (n : ℕ) : ℝ :=
  Real.cos ((n : ℝ) * α) / (Nat.factorial n : ℝ) * x ^ n

def imaginaryPartTerm (x α : ℝ) (n : ℕ) : ℝ :=
  Real.sin ((n : ℝ) * α) / (Nat.factorial n : ℝ) * x ^ n

private theorem raw_eq_standard (x α : ℝ) (n : ℕ) :
    rawExponentialTerm x α n =
      ((x : ℂ) * Complex.exp (Complex.I * α)) ^ n /
        (Nat.factorial n : ℂ) := by
  unfold rawExponentialTerm
  simp only [div_eq_mul_inv, one_mul]
  ring

private theorem raw_eq_separated (x α : ℝ) (n : ℕ) :
    rawExponentialTerm x α n = separatedExponentialTerm x α n := by
  unfold rawExponentialTerm separatedExponentialTerm
  calc
    1 / (Nat.factorial n : ℂ) *
          ((x : ℂ) * Complex.exp (Complex.I * α)) ^ n =
        (x : ℂ) ^ n / (Nat.factorial n : ℂ) *
          Complex.exp (Complex.I * α) ^ n := by
      rw [mul_pow]
      ring
    _ = (x : ℂ) ^ n / (Nat.factorial n : ℂ) *
          Complex.exp ((n : ℂ) * (Complex.I * (α : ℂ))) := by
      rw [Complex.exp_nat_mul]
    _ = (x : ℂ) ^ n / (Nat.factorial n : ℂ) *
          Complex.exp (Complex.I * ((n : ℝ) : ℂ) * (α : ℂ)) := by
      congr 2
      push_cast
      ring

private theorem separated_eq_trigonometric (x α : ℝ) (n : ℕ) :
    separatedExponentialTerm x α n =
      trigonometricExponentialTerm x α n := by
  unfold separatedExponentialTerm trigonometricExponentialTerm
  have he :
      Complex.I * ((n : ℝ) : ℂ) * (α : ℂ) =
        (((n : ℝ) * α : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [he, Complex.exp_ofReal_mul_I]
  ring

private theorem trigonometric_summable (x α : ℝ) :
    Summable (fun n : ℕ => trigonometricExponentialTerm x α n) := by
  let z : ℂ := (x : ℂ) * Complex.exp (Complex.I * α)
  have hs :
      Summable (fun n : ℕ => z ^ n / (Nat.factorial n : ℂ)) :=
    NormedSpace.expSeries_div_summable z
  refine hs.congr ?_
  intro n
  calc
    z ^ n / (Nat.factorial n : ℂ) = rawExponentialTerm x α n :=
      (raw_eq_standard x α n).symm
    _ = separatedExponentialTerm x α n := raw_eq_separated x α n
    _ = trigonometricExponentialTerm x α n :=
      separated_eq_trigonometric x α n

private theorem polar_re (x α : ℝ) :
    ((x : ℂ) * Complex.exp (Complex.I * α)).re =
      x * Real.cos α := by
  rw [show Complex.I * (α : ℂ) = (α : ℂ) * Complex.I by ring,
    Complex.exp_ofReal_mul_I]
  simp only [Complex.mul_re, Complex.mul_im, Complex.add_re,
    Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im, zero_mul, mul_zero, add_zero, zero_add, sub_zero,
    mul_one]

private theorem polar_im (x α : ℝ) :
    ((x : ℂ) * Complex.exp (Complex.I * α)).im =
      x * Real.sin α := by
  rw [show Complex.I * (α : ℂ) = (α : ℂ) * Complex.I by ring,
    Complex.exp_ofReal_mul_I]
  simp only [Complex.mul_re, Complex.mul_im, Complex.add_re,
    Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im, zero_mul, mul_zero, add_zero, zero_add, sub_zero,
    mul_one]

private theorem trigonometric_re (x α : ℝ) (n : ℕ) :
    (trigonometricExponentialTerm x α n).re =
      realPartTerm x α n := by
  unfold trigonometricExponentialTerm realPartTerm
  have ha :
      (x : ℂ) ^ n / (Nat.factorial n : ℂ) =
        ((x ^ n / (Nat.factorial n : ℝ) : ℝ) : ℂ) := by
    norm_cast
  rw [ha]
  simp only [Complex.mul_re, Complex.mul_im, Complex.add_re,
    Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im, zero_mul, one_mul, mul_zero, add_zero, sub_zero]
  ring

private theorem trigonometric_im (x α : ℝ) (n : ℕ) :
    (trigonometricExponentialTerm x α n).im =
      imaginaryPartTerm x α n := by
  unfold trigonometricExponentialTerm imaginaryPartTerm
  have ha :
      (x : ℂ) ^ n / (Nat.factorial n : ℂ) =
        ((x ^ n / (Nat.factorial n : ℝ) : ℝ) : ℂ) := by
    norm_cast
  rw [ha]
  simp only [Complex.mul_re, Complex.mul_im, Complex.add_re,
    Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im, zero_mul, one_mul, mul_zero, add_zero, sub_zero]
  ring

theorem gap1 :
    ∀ x α : ℝ,
      Complex.exp ((x * Real.cos α : ℝ) + Complex.I * (x * Real.sin α)) =
        Complex.exp ((x : ℂ) *
          ((Real.cos α : ℂ) + Complex.I * Real.sin α)) := by
  intro x α
  congr 1
  push_cast
  ring

theorem gap2
    (hfactor :
      ∀ x α : ℝ,
        Complex.exp ((x * Real.cos α : ℝ) + Complex.I * (x * Real.sin α)) =
          Complex.exp ((x : ℂ) *
            ((Real.cos α : ℂ) + Complex.I * Real.sin α))) :
    ∀ x α : ℝ,
      Complex.exp ((x : ℂ) *
          ((Real.cos α : ℂ) + Complex.I * Real.sin α)) =
        Complex.exp ((x : ℂ) * Complex.exp (Complex.I * α)) := by
  intro x α
  congr 1
  rw [show Complex.I * (α : ℂ) = (α : ℂ) * Complex.I by ring,
    Complex.exp_ofReal_mul_I]
  ring

theorem gap3
    (hfactor :
      ∀ x α : ℝ,
        Complex.exp ((x * Real.cos α : ℝ) + Complex.I * (x * Real.sin α)) =
          Complex.exp ((x : ℂ) *
            ((Real.cos α : ℂ) + Complex.I * Real.sin α)))
    (heuler :
      ∀ x α : ℝ,
        Complex.exp ((x : ℂ) *
            ((Real.cos α : ℂ) + Complex.I * Real.sin α)) =
          Complex.exp ((x : ℂ) * Complex.exp (Complex.I * α))) :
    ∀ x α : ℝ,
      Complex.exp ((x * Real.cos α : ℝ) + Complex.I * (x * Real.sin α)) =
        Complex.exp ((x : ℂ) * Complex.exp (Complex.I * α)) := by
  intro x α
  calc
    Complex.exp
          ((x * Real.cos α : ℝ) + Complex.I * (x * Real.sin α)) =
        Complex.exp
          ((x : ℂ) *
            ((Real.cos α : ℂ) + Complex.I * Real.sin α)) :=
      hfactor x α
    _ = Complex.exp ((x : ℂ) * Complex.exp (Complex.I * α)) :=
      heuler x α

theorem gap4
    (hcombined :
      ∀ x α : ℝ,
        Complex.exp ((x * Real.cos α : ℝ) + Complex.I * (x * Real.sin α)) =
          Complex.exp ((x : ℂ) * Complex.exp (Complex.I * α))) :
    ∀ x α : ℝ,
      Complex.exp ((x : ℂ) * Complex.exp (Complex.I * α)) =
        ∑' n, rawExponentialTerm x α n := by
  intro x α
  let z : ℂ := (x : ℂ) * Complex.exp (Complex.I * α)
  calc
    Complex.exp z = NormedSpace.exp z :=
      congrFun Complex.exp_eq_exp_ℂ z
    _ = ∑' n : ℕ, z ^ n / (Nat.factorial n : ℂ) :=
      congrFun NormedSpace.exp_eq_tsum_div z
    _ = ∑' n, rawExponentialTerm x α n := by
      apply tsum_congr
      intro n
      exact (raw_eq_standard x α n).symm

theorem gap5
    (hexpSeries :
      ∀ x α : ℝ,
        Complex.exp ((x : ℂ) * Complex.exp (Complex.I * α)) =
          ∑' n, rawExponentialTerm x α n) :
    ∀ x α : ℝ,
      (∑' n, rawExponentialTerm x α n) =
        ∑' n, separatedExponentialTerm x α n := by
  intro x α
  apply tsum_congr
  exact raw_eq_separated x α

theorem gap6
    (hseparate :
      ∀ x α : ℝ,
        (∑' n, rawExponentialTerm x α n) =
          ∑' n, separatedExponentialTerm x α n) :
    ∀ x α : ℝ,
      (∑' n, separatedExponentialTerm x α n) =
        ∑' n, trigonometricExponentialTerm x α n := by
  intro x α
  apply tsum_congr
  exact separated_eq_trigonometric x α

theorem gap7
    (hexpSeries :
      ∀ x α : ℝ,
        Complex.exp ((x : ℂ) * Complex.exp (Complex.I * α)) =
          ∑' n, rawExponentialTerm x α n)
    (hseparate :
      ∀ x α : ℝ,
        (∑' n, rawExponentialTerm x α n) =
          ∑' n, separatedExponentialTerm x α n)
    (htrig :
      ∀ x α : ℝ,
        (∑' n, separatedExponentialTerm x α n) =
          ∑' n, trigonometricExponentialTerm x α n) :
    ∀ x α : ℝ,
      Complex.exp ((x : ℂ) * Complex.exp (Complex.I * α)) =
        ∑' n, trigonometricExponentialTerm x α n := by
  intro x α
  calc
    Complex.exp ((x : ℂ) * Complex.exp (Complex.I * α)) =
        ∑' n, rawExponentialTerm x α n := hexpSeries x α
    _ = ∑' n, separatedExponentialTerm x α n := hseparate x α
    _ = ∑' n, trigonometricExponentialTerm x α n := htrig x α

theorem gap8
    (hcomplex :
      ∀ x α : ℝ,
        Complex.exp ((x : ℂ) * Complex.exp (Complex.I * α)) =
          ∑' n, trigonometricExponentialTerm x α n) :
    ∀ x α : ℝ,
      Real.exp (x * Real.cos α) * Real.cos (x * Real.sin α) =
        ∑' n, realPartTerm x α n := by
  intro x α
  have h := congrArg Complex.re (hcomplex x α)
  rw [Complex.exp_re,
    Complex.re_tsum (trigonometric_summable x α),
    polar_re, polar_im] at h
  simpa only [trigonometric_re] using h

theorem gap9
    (hcomplex :
      ∀ x α : ℝ,
        Complex.exp ((x : ℂ) * Complex.exp (Complex.I * α)) =
          ∑' n, trigonometricExponentialTerm x α n)
    (hreal :
      ∀ x α : ℝ,
        Real.exp (x * Real.cos α) * Real.cos (x * Real.sin α) =
          ∑' n, realPartTerm x α n) :
    ∀ x α : ℝ,
      Real.exp (x * Real.cos α) * Real.sin (x * Real.sin α) =
        ∑' n, imaginaryPartTerm x α n := by
  intro x α
  have h := congrArg Complex.im (hcomplex x α)
  rw [Complex.exp_im,
    Complex.im_tsum (trigonometric_summable x α),
    polar_re, polar_im] at h
  simpa only [trigonometric_im] using h

end

end ProofGap.Exercise2868
