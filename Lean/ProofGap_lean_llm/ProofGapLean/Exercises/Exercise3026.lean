import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Exponential

namespace ProofGap.Exercise3026

noncomputable section

open scoped BigOperators

def z (x : ℝ) : ℂ := Complex.exp (Complex.I * (x : ℂ))

def exponentialSeries (w : ℂ) : ℂ :=
  ∑' n : ℕ, w ^ n / (n.factorial : ℂ)

def cosineFactorialSeries (x : ℝ) : ℝ :=
  ∑' n : ℕ, Real.cos ((n : ℝ) * x) / (n.factorial : ℝ)

def sineFactorialSeries (x : ℝ) : ℝ :=
  ∑' n : ℕ, Real.sin ((n : ℝ) * x) / (n.factorial : ℝ)

private lemma z_pow_trigonometric (x : ℝ) (n : ℕ) :
    z x ^ n =
      (Real.cos ((n : ℝ) * x) : ℂ) +
        Complex.I * (Real.sin ((n : ℝ) * x) : ℂ) := by
  unfold z
  rw [← Complex.exp_nat_mul]
  have he :
      (n : ℂ) * (Complex.I * (x : ℂ)) =
        (((n : ℝ) * x : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [he, Complex.exp_ofReal_mul_I]
  ring

private lemma exponential_term_re (x : ℝ) (n : ℕ) :
    (z x ^ n / (n.factorial : ℂ)).re =
      Real.cos ((n : ℝ) * x) / (n.factorial : ℝ) := by
  rw [z_pow_trigonometric]
  rw [Complex.div_natCast_re]
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, zero_mul,
    one_mul, sub_zero, add_zero]

private lemma exponential_term_im (x : ℝ) (n : ℕ) :
    (z x ^ n / (n.factorial : ℂ)).im =
      Real.sin ((n : ℝ) * x) / (n.factorial : ℝ) := by
  rw [z_pow_trigonometric]
  rw [Complex.div_natCast_im]
  simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, zero_mul,
    one_mul, zero_add]

theorem gap1 (w : ℂ) :
    exponentialSeries w = Complex.exp w := by
  rw [exponentialSeries, Complex.exp_eq_exp_ℂ]
  exact (NormedSpace.expSeries_div_hasSum_exp w).tsum_eq

theorem gap2 (x : ℝ) :
    exponentialSeries (z x) =
      (cosineFactorialSeries x : ℂ) +
        Complex.I * (sineFactorialSeries x : ℂ) := by
  have hs :
      Summable (fun n : ℕ => z x ^ n / (n.factorial : ℂ)) :=
    NormedSpace.expSeries_div_summable (z x)
  apply Complex.ext
  · simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, zero_mul,
      one_mul, sub_zero, add_zero]
    unfold exponentialSeries cosineFactorialSeries
    rw [Complex.re_tsum hs]
    apply tsum_congr
    exact exponential_term_re x
  · simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, zero_mul,
      one_mul, zero_add]
    unfold exponentialSeries sineFactorialSeries
    rw [Complex.im_tsum hs]
    apply tsum_congr
    exact exponential_term_im x

theorem gap3 (x : ℝ) :
    Complex.exp (z x) =
      Complex.exp ((Real.cos x : ℂ) + Complex.I * (Real.sin x : ℂ)) := by
  congr 1
  unfold z
  rw [show Complex.I * (x : ℂ) = (x : ℂ) * Complex.I by ring,
    Complex.exp_ofReal_mul_I]
  ring

theorem gap4 (x : ℝ) :
    Complex.exp ((Real.cos x : ℂ) + Complex.I * (Real.sin x : ℂ)) =
      (Real.exp (Real.cos x) : ℂ) *
        ((Real.cos (Real.sin x) : ℂ) +
          Complex.I * (Real.sin (Real.sin x) : ℂ)) := by
  rw [show Complex.I * (Real.sin x : ℂ) =
      (Real.sin x : ℂ) * Complex.I by ring,
    Complex.exp_add_mul_I]
  rw [← Complex.ofReal_exp, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  ring

theorem gap5 (x : ℝ) :
    Complex.exp (z x) =
      (Real.exp (Real.cos x) : ℂ) *
        ((Real.cos (Real.sin x) : ℂ) +
          Complex.I * (Real.sin (Real.sin x) : ℂ)) := by
  rw [gap3, gap4]

theorem gap6 (x : ℝ) :
    cosineFactorialSeries x =
      Real.exp (Real.cos x) * Real.cos (Real.sin x) := by
  have h :
      (cosineFactorialSeries x : ℂ) +
          Complex.I * (sineFactorialSeries x : ℂ) =
        (Real.exp (Real.cos x) : ℂ) *
          ((Real.cos (Real.sin x) : ℂ) +
            Complex.I * (Real.sin (Real.sin x) : ℂ)) :=
    (gap2 x).symm.trans ((gap1 (z x)).trans (gap5 x))
  have hre := congrArg Complex.re h
  simpa only [Complex.add_re, Complex.add_im, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    zero_mul, mul_zero, one_mul, mul_one, add_zero, zero_add, sub_zero]
    using hre

end

end ProofGap.Exercise3026
