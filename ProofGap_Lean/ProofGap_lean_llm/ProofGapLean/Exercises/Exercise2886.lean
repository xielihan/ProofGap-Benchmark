import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Topology.Algebra.InfiniteSum.Basic

namespace ProofGap.Exercise2886

noncomputable section

open scoped BigOperators ComplexConjugate

def complexExpTerm (x : ℝ) (n : ℕ) : ℂ :=
  ((x : ℂ) ^ n / (Nat.factorial n : ℂ)) * ((1 : ℂ) + Complex.I) ^ n

def polarOnePlusITerm (x : ℝ) (n : ℕ) : ℂ :=
  ((x : ℂ) ^ n / (Nat.factorial n : ℂ)) *
    (Real.sqrt 2 : ℂ) ^ n *
    ((Real.cos ((n : ℝ) * Real.pi / 4) : ℂ) +
      Complex.I * Real.sin ((n : ℝ) * Real.pi / 4))

def realPartTerm (x : ℝ) (n : ℕ) : ℝ :=
  (Real.sqrt 2) ^ n * Real.cos ((n : ℝ) * Real.pi / 4) *
    x ^ n / (Nat.factorial n : ℝ)

private theorem one_add_I_eq_polar :
    (1 : ℂ) + Complex.I =
      (Real.sqrt 2 : ℂ) *
        ((Real.cos (Real.pi / 4) : ℂ) +
          Complex.I * Real.sin (Real.pi / 4)) := by
  rw [Real.cos_pi_div_four, Real.sin_pi_div_four]
  have hsqrt : Real.sqrt 2 * Real.sqrt 2 = 2 :=
    Real.mul_self_sqrt (by norm_num)
  apply Complex.ext <;>
    simp only [Complex.add_re, Complex.add_im, Complex.mul_re,
      Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, Complex.one_re, Complex.one_im,
      zero_mul, mul_zero, sub_zero, zero_add, one_mul]
  · nlinarith
  · nlinarith

private theorem trig_power (n : ℕ) :
    ((Real.cos (Real.pi / 4) : ℂ) +
        Complex.I * Real.sin (Real.pi / 4)) ^ n =
      (Real.cos ((n : ℝ) * Real.pi / 4) : ℂ) +
        Complex.I * Real.sin ((n : ℝ) * Real.pi / 4) := by
  have h :=
    Complex.cos_add_sin_mul_I_pow n ((Real.pi / 4 : ℝ) : ℂ)
  have harg :
      (n : ℂ) * ((Real.pi / 4 : ℝ) : ℂ) =
        (((n : ℝ) * Real.pi / 4 : ℝ) : ℂ) := by
    push_cast
    ring
  rw [harg] at h
  simpa only [← Complex.ofReal_cos, ← Complex.ofReal_sin, mul_comm] using h

private theorem standard_term_eq_complex (x : ℝ) (n : ℕ) :
    ((((1 : ℂ) + Complex.I) * x) ^ n /
        (Nat.factorial n : ℂ)) =
      complexExpTerm x n := by
  unfold complexExpTerm
  rw [mul_pow]
  ring

private theorem complex_term_eq_polar (x : ℝ) (n : ℕ) :
    complexExpTerm x n = polarOnePlusITerm x n := by
  unfold complexExpTerm polarOnePlusITerm
  rw [one_add_I_eq_polar, mul_pow, trig_power]
  ring

private theorem polar_summable (x : ℝ) :
    Summable (fun n : ℕ => polarOnePlusITerm x n) := by
  let z : ℂ := ((1 : ℂ) + Complex.I) * x
  have hs :
      Summable (fun n : ℕ => z ^ n / (Nat.factorial n : ℂ)) :=
    NormedSpace.expSeries_div_summable z
  refine hs.congr ?_
  intro n
  calc
    z ^ n / (Nat.factorial n : ℂ) = complexExpTerm x n :=
      standard_term_eq_complex x n
    _ = polarOnePlusITerm x n := complex_term_eq_polar x n

private theorem polar_term_re (x : ℝ) (n : ℕ) :
    (polarOnePlusITerm x n).re = realPartTerm x n := by
  unfold polarOnePlusITerm realPartTerm
  have hx :
      (x : ℂ) ^ n / (Nat.factorial n : ℂ) =
        ((x ^ n / (Nat.factorial n : ℝ) : ℝ) : ℂ) := by
    norm_cast
  have hsqrt :
      (Real.sqrt 2 : ℂ) ^ n = (((Real.sqrt 2) ^ n : ℝ) : ℂ) := by
    norm_cast
  rw [hx, hsqrt]
  simp only [Complex.mul_re, Complex.mul_im, Complex.add_re,
    Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, zero_mul, one_mul, mul_zero,
    add_zero, sub_zero]
  ring

theorem gap1 :
    ∀ x : ℝ, (Real.exp x : ℂ) *
      ((Real.cos x : ℂ) + Complex.I * Real.sin x) =
        (Real.exp x : ℂ) * Complex.exp (Complex.I * x) := by
  intro x
  rw [show Complex.I * (x : ℂ) = (x : ℂ) * Complex.I by ring,
    Complex.exp_ofReal_mul_I]
  ring

theorem gap2 :
    ∀ x : ℝ, (Real.exp x : ℂ) * Complex.exp (Complex.I * x) =
      Complex.exp (((1 : ℂ) + Complex.I) * x) := by
  intro x
  rw [Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  ring

theorem gap3 :
    ∀ x : ℝ, (Real.exp x : ℂ) *
      ((Real.cos x : ℂ) + Complex.I * Real.sin x) =
        Complex.exp (((1 : ℂ) + Complex.I) * x) := by
  intro x
  calc
    (Real.exp x : ℂ) *
        ((Real.cos x : ℂ) + Complex.I * Real.sin x) =
      (Real.exp x : ℂ) * Complex.exp (Complex.I * x) := gap1 x
    _ = Complex.exp (((1 : ℂ) + Complex.I) * x) := gap2 x

theorem gap4 :
    ∀ x : ℝ, Complex.exp (((1 : ℂ) + Complex.I) * x) =
      ∑' n : ℕ,
        (((1 : ℂ) + Complex.I) * x) ^ n / (Nat.factorial n : ℂ) := by
  intro x
  let z : ℂ := ((1 : ℂ) + Complex.I) * x
  calc
    Complex.exp z = NormedSpace.exp z :=
      congrFun Complex.exp_eq_exp_ℂ z
    _ = ∑' n : ℕ, z ^ n / (Nat.factorial n : ℂ) :=
      congrFun NormedSpace.exp_eq_tsum_div z

theorem gap5 :
    ∀ x : ℝ,
      (∑' n : ℕ,
        (((1 : ℂ) + Complex.I) * x) ^ n / (Nat.factorial n : ℂ)) =
      ∑' n : ℕ, complexExpTerm x n := by
  intro x
  apply tsum_congr
  exact standard_term_eq_complex x

theorem gap6 :
    ∀ x : ℝ, Complex.exp (((1 : ℂ) + Complex.I) * x) =
      ∑' n : ℕ, complexExpTerm x n := by
  intro x
  calc
    Complex.exp (((1 : ℂ) + Complex.I) * x) =
        ∑' n : ℕ,
          (((1 : ℂ) + Complex.I) * x) ^ n /
            (Nat.factorial n : ℂ) := gap4 x
    _ = ∑' n : ℕ, complexExpTerm x n := gap5 x

theorem gap7 :
    ∀ x : ℝ, Complex.exp (((1 : ℂ) + Complex.I) * x) =
      ∑' n : ℕ,
        ((x : ℂ) ^ n / (Nat.factorial n : ℂ)) *
          ((Real.sqrt 2 : ℂ) *
            ((Real.cos (Real.pi / 4) : ℂ) +
              Complex.I * Real.sin (Real.pi / 4))) ^ n := by
  intro x
  calc
    Complex.exp (((1 : ℂ) + Complex.I) * x) =
        ∑' n : ℕ, complexExpTerm x n := gap6 x
    _ = ∑' n : ℕ,
          ((x : ℂ) ^ n / (Nat.factorial n : ℂ)) *
            ((Real.sqrt 2 : ℂ) *
              ((Real.cos (Real.pi / 4) : ℂ) +
                Complex.I * Real.sin (Real.pi / 4))) ^ n := by
      apply tsum_congr
      intro n
      unfold complexExpTerm
      rw [one_add_I_eq_polar]

theorem gap8 :
    ∀ x : ℝ,
      (∑' n : ℕ,
        ((x : ℂ) ^ n / (Nat.factorial n : ℂ)) *
          ((Real.sqrt 2 : ℂ) *
            ((Real.cos (Real.pi / 4) : ℂ) +
              Complex.I * Real.sin (Real.pi / 4))) ^ n) =
      ∑' n : ℕ, polarOnePlusITerm x n := by
  intro x
  apply tsum_congr
  intro n
  unfold polarOnePlusITerm
  rw [mul_pow, trig_power]
  ring

theorem gap9 :
    ∀ x : ℝ, Complex.exp (((1 : ℂ) + Complex.I) * x) =
      ∑' n : ℕ, polarOnePlusITerm x n := by
  intro x
  calc
    Complex.exp (((1 : ℂ) + Complex.I) * x) =
        ∑' n : ℕ,
          ((x : ℂ) ^ n / (Nat.factorial n : ℂ)) *
            ((Real.sqrt 2 : ℂ) *
              ((Real.cos (Real.pi / 4) : ℂ) +
                Complex.I * Real.sin (Real.pi / 4))) ^ n := gap7 x
    _ = ∑' n : ℕ, polarOnePlusITerm x n := gap8 x

theorem gap10 :
    ∀ x : ℝ, Real.exp x * Real.cos x =
      ∑' n : ℕ, realPartTerm x n := by
  intro x
  have h := congrArg Complex.re (gap9 x)
  rw [Complex.exp_re, Complex.re_tsum (polar_summable x)] at h
  simpa only [Complex.mul_re, Complex.mul_im, Complex.add_re,
    Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, Complex.one_re, Complex.one_im,
    zero_mul, mul_zero, sub_zero, add_zero, zero_add, one_mul,
    mul_one, polar_term_re] using h

end

end ProofGap.Exercise2886
