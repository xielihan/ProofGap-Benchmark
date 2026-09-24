import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Lean.Elab.Tactic.Omega
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Data.Nat.Choose.Sum

open scoped Interval

namespace ProofGap.Exercise2293

noncomputable section

def integrand (n : ℕ) (x : ℝ) : ℝ :=
  Real.cos x ^ n * Real.cos ((n : ℝ) * x)

def cosineExpansion (n : ℕ) (x : ℝ) : ℝ :=
  (1 + ∑ k ∈ Finset.range n,
    (Nat.choose n k : ℝ) *
      Real.cos ((2 * (n - k) : ℕ) * x)) / (2 : ℝ) ^ n

private lemma local_euler_cos_sum (t : ℝ) :
    Complex.exp (Complex.I * (t : ℂ)) + Complex.exp (-Complex.I * (t : ℂ)) =
      (2 : ℂ) * Real.cos t := by
  have hpos : Complex.I * (t : ℂ) = (t : ℂ) * Complex.I := by ring
  have hneg : -Complex.I * (t : ℂ) = ((-t : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [hpos, hneg, Complex.exp_mul_I, Complex.exp_mul_I]
  rw [(Complex.ofReal_cos t).symm, (Complex.ofReal_sin t).symm,
    (Complex.ofReal_cos (-t)).symm, (Complex.ofReal_sin (-t)).symm]
  rw [Real.cos_neg, Real.sin_neg]
  push_cast
  ring

private lemma local_euler_cos_nat_mul (n : ℕ) (x : ℝ) :
    Complex.exp (Complex.I * (n : ℝ) * x) +
        Complex.exp (-Complex.I * (n : ℝ) * x) =
      (2 : ℂ) * Real.cos ((n : ℝ) * x) := by
  have hpos :
      Complex.I * (n : ℝ) * x =
        Complex.I * ((((n : ℝ) * x : ℝ)) : ℂ) := by
    push_cast
    ring
  have hneg :
      -Complex.I * (n : ℝ) * x =
        -Complex.I * ((((n : ℝ) * x : ℝ)) : ℂ) := by
    push_cast
    ring
  rw [hpos, hneg]
  exact local_euler_cos_sum ((n : ℝ) * x)

private lemma local_exp_pow_nat (z : ℂ) (m : ℕ) :
    Complex.exp z ^ m = Complex.exp ((m : ℂ) * z) := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [pow_succ, ih, ← Complex.exp_add]
      congr 1
      push_cast
      ring

private lemma local_exp_I_mul_re (t : ℝ) :
    (Complex.exp (Complex.I * (t : ℂ))).re = Real.cos t := by
  simp [Complex.exp_re]

private lemma local_exp_product_term_re (n k : ℕ) (x : ℝ) (hk : k ≤ n) :
    ((Complex.exp (Complex.I * (x : ℂ)) ^ k *
          Complex.exp (-Complex.I * (x : ℂ)) ^ (n - k) *
          (Complex.exp (Complex.I * (n : ℝ) * x) +
            Complex.exp (-Complex.I * (n : ℝ) * x))).re) =
      Real.cos ((2 * k : ℕ) * x) +
        Real.cos ((2 * (n - k) : ℕ) * x) := by
  rw [local_exp_pow_nat, local_exp_pow_nat, mul_add]
  simp only [← Complex.exp_add]
  have hfirst :
      (k : ℂ) * (Complex.I * (x : ℂ)) +
          (((n - k : ℕ) : ℂ)) * (-Complex.I * (x : ℂ)) +
          Complex.I * (n : ℝ) * x =
        Complex.I * (((2 * k : ℕ) : ℝ) * x : ℝ) := by
    push_cast [Nat.cast_sub hk]
    ring
  have hsecond :
      (k : ℂ) * (Complex.I * (x : ℂ)) +
          (((n - k : ℕ) : ℂ)) * (-Complex.I * (x : ℂ)) +
          (-Complex.I * (n : ℝ) * x) =
        Complex.I * (-(((2 * (n - k) : ℕ) : ℝ) * x) : ℝ) := by
    push_cast [Nat.cast_sub hk]
    ring
  rw [hfirst, hsecond, Complex.add_re]
  rw [local_exp_I_mul_re, local_exp_I_mul_re]
  simp [Real.cos_neg]

private lemma local_finset_sum_re {α : Type*} (s : Finset α) (f : α → ℂ) :
    ((∑ a ∈ s, f a).re) = ∑ a ∈ s, (f a).re := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp [ha, ih]

private lemma local_complex_numerator_re (n : ℕ) (x : ℝ) :
    (((Complex.exp (Complex.I * x) + Complex.exp (-Complex.I * x)) ^ n *
        (Complex.exp (Complex.I * (n : ℝ) * x) +
          Complex.exp (-Complex.I * (n : ℝ) * x))).re) =
      ∑ k ∈ Finset.range (n + 1),
        (Nat.choose n k : ℝ) *
          (Real.cos ((2 * k : ℕ) * x) +
            Real.cos ((2 * (n - k) : ℕ) * x)) := by
  classical
  rw [add_pow, Finset.sum_mul]
  rw [local_finset_sum_re]
  apply Finset.sum_congr rfl
  intro k hk
  have hkn : k ≤ n := by
    have := Finset.mem_range.mp hk
    omega
  have ht := local_exp_product_term_re n k x hkn
  have hchoose :
      (Nat.choose n k : ℂ) = (((Nat.choose n k : ℝ) : ℂ)) := by
    norm_num
  calc
    ((Complex.exp (Complex.I * x) ^ k *
          Complex.exp (-Complex.I * x) ^ (n - k) *
          (Nat.choose n k : ℂ) *
          (Complex.exp (Complex.I * (n : ℝ) * x) +
            Complex.exp (-Complex.I * (n : ℝ) * x))).re) =
        (((Nat.choose n k : ℝ) : ℂ) *
          (Complex.exp (Complex.I * x) ^ k *
            Complex.exp (-Complex.I * x) ^ (n - k) *
            (Complex.exp (Complex.I * (n : ℝ) * x) +
              Complex.exp (-Complex.I * (n : ℝ) * x)))).re := by
          rw [← hchoose]
          ring
    _ = (Nat.choose n k : ℝ) *
          ((Complex.exp (Complex.I * x) ^ k *
            Complex.exp (-Complex.I * x) ^ (n - k) *
            (Complex.exp (Complex.I * (n : ℝ) * x) +
              Complex.exp (-Complex.I * (n : ℝ) * x))).re) := by simp
    _ = (Nat.choose n k : ℝ) *
          (Real.cos ((2 * k : ℕ) * x) +
            Real.cos ((2 * (n - k) : ℕ) * x)) := by rw [ht]

private lemma local_div_ofReal_re (z : ℂ) (r : ℝ) :
    (z / (r : ℂ)).re = z.re / r := by
  change (z * (r : ℂ)⁻¹).re = z.re * r⁻¹
  rw [show (r : ℂ)⁻¹ = ((r⁻¹ : ℝ) : ℂ) by norm_cast]
  change z.re * r⁻¹ - z.im * 0 = z.re * r⁻¹
  ring

private lemma local_integral_cos_nat_mul_zero (m : ℕ) (hm : m ≠ 0) :
    (∫ x in 0..Real.pi, Real.cos ((m : ℝ) * x)) = 0 := by
  let F : ℝ → ℝ := fun x => Real.sin ((m : ℝ) * x) / (m : ℝ)
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm
  have hF : ∀ x : ℝ, HasDerivAt F (Real.cos ((m : ℝ) * x)) x := by
    intro x
    have hinner : HasDerivAt (fun y : ℝ => (m : ℝ) * y) (m : ℝ) x := by
      simpa using (hasDerivAt_const x (m : ℝ)).mul (hasDerivAt_id x)
    have hs := (Real.hasDerivAt_sin ((m : ℝ) * x)).comp x hinner
    convert hs.div_const (m : ℝ) using 1 <;> field_simp [hmR]
  calc
    (∫ x in 0..Real.pi, Real.cos ((m : ℝ) * x)) = F Real.pi - F 0 := by
      apply intervalIntegral.integral_eq_sub_of_hasDerivAt
      · exact fun x _ => hF x
      · exact
          (Real.continuous_cos.comp (continuous_const.mul continuous_id)).intervalIntegrable
            0 Real.pi
    _ = 0 := by
      simp [F, Real.sin_nat_mul_pi]

theorem gap1 (n : ℕ) (x : ℝ) :
    (integrand n x : ℂ) =
      (Complex.exp (Complex.I * x) + Complex.exp (-Complex.I * x)) ^ n *
        (Complex.exp (Complex.I * (n : ℝ) * x) +
          Complex.exp (-Complex.I * (n : ℝ) * x)) /
        (2 : ℂ) ^ (n + 1) := by
  unfold integrand
  rw [local_euler_cos_sum x, local_euler_cos_nat_mul n x]
  push_cast
  simp only [mul_pow, pow_succ]
  field_simp

theorem gap2 (n : ℕ) (x : ℝ) :
    integrand n x = cosineExpansion n x := by
  classical
  have hre := congrArg Complex.re (gap1 n x)
  have hden :
      (2 : ℂ) ^ (n + 1) = (((2 : ℝ) ^ (n + 1) : ℝ) : ℂ) := by
    norm_num
  rw [hden, local_div_ofReal_re, local_complex_numerator_re] at hre
  simp only [Complex.ofReal_re] at hre
  simp_rw [mul_add] at hre
  rw [Finset.sum_add_distrib] at hre
  have hsym :
      (∑ k ∈ Finset.range (n + 1),
          (Nat.choose n k : ℝ) * Real.cos ((2 * k : ℕ) * x)) =
        ∑ k ∈ Finset.range (n + 1),
          (Nat.choose n k : ℝ) * Real.cos ((2 * (n - k) : ℕ) * x) := by
    let f : ℕ → ℝ := fun k =>
      (Nat.choose n k : ℝ) * Real.cos ((2 * (n - k) : ℕ) * x)
    calc
      (∑ k ∈ Finset.range (n + 1),
          (Nat.choose n k : ℝ) * Real.cos ((2 * k : ℕ) * x)) =
          ∑ k ∈ Finset.range (n + 1), f (n + 1 - 1 - k) := by
            apply Finset.sum_congr rfl
            intro k hk
            have hkn : k ≤ n := by
              have := Finset.mem_range.mp hk
              omega
            have hback : n - (n - k) = k := by omega
            simp only [f]
            rw [show n + 1 - 1 - k = n - k by omega]
            rw [Nat.choose_symm hkn, hback]
      _ = ∑ k ∈ Finset.range (n + 1), f k :=
        Finset.sum_range_reflect f (n + 1)
      _ = ∑ k ∈ Finset.range (n + 1),
          (Nat.choose n k : ℝ) * Real.cos ((2 * (n - k) : ℕ) * x) := rfl
  rw [hsym] at hre
  have hend :
      (∑ k ∈ Finset.range (n + 1),
          (Nat.choose n k : ℝ) * Real.cos ((2 * (n - k) : ℕ) * x)) =
        1 + ∑ k ∈ Finset.range n,
          (Nat.choose n k : ℝ) * Real.cos ((2 * (n - k) : ℕ) * x) := by
    rw [Finset.sum_range_succ]
    simp
    ring
  rw [hre, hend]
  unfold cosineExpansion
  rw [pow_succ]
  field_simp
  simp only [Nat.mul_comm, mul_comm]
  ring

theorem gap3 (n : ℕ) :
    (∫ x in 0..Real.pi, integrand n x) =
      Real.pi / (2 : ℝ) ^ n := by
  classical
  simp_rw [gap2 n]
  unfold cosineExpansion
  have hone :
      IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) MeasureTheory.volume 0 Real.pi := by
    exact continuous_const.intervalIntegrable 0 Real.pi
  have hterm : ∀ k ∈ Finset.range n,
      IntervalIntegrable
        (fun x : ℝ => (Nat.choose n k : ℝ) *
          Real.cos ((2 * (n - k) : ℕ) * x))
        MeasureTheory.volume 0 Real.pi := by
    intro k hk
    apply Continuous.intervalIntegrable
    fun_prop
  have hsum :
      IntervalIntegrable
        (fun x : ℝ => ∑ k ∈ Finset.range n,
          (Nat.choose n k : ℝ) * Real.cos ((2 * (n - k) : ℕ) * x))
        MeasureTheory.volume 0 Real.pi := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hdiv :
      (fun x : ℝ =>
        (1 + ∑ k ∈ Finset.range n,
          (Nat.choose n k : ℝ) *
            Real.cos ((2 * (n - k) : ℕ) * x)) / (2 : ℝ) ^ n) =
      (fun x : ℝ =>
        ((2 : ℝ) ^ n)⁻¹ *
          (1 + ∑ k ∈ Finset.range n,
            (Nat.choose n k : ℝ) *
              Real.cos ((2 * (n - k) : ℕ) * x))) := by
    funext x
    simp only [div_eq_mul_inv]
    ring
  rw [hdiv]
  rw [intervalIntegral.integral_const_mul]
  rw [intervalIntegral.integral_add hone hsum]
  rw [intervalIntegral.integral_finset_sum hterm]
  simp only [intervalIntegral.integral_const, sub_zero]
  have hz : ∀ k ∈ Finset.range n,
      (∫ x in 0..Real.pi,
        (Nat.choose n k : ℝ) * Real.cos ((2 * (n - k) : ℕ) * x)) = 0 := by
    intro k hk
    rw [intervalIntegral.integral_const_mul]
    have hkn : k < n := Finset.mem_range.mp hk
    rw [local_integral_cos_nat_mul_zero]
    · ring
    · omega
  have hsum_zero :
      (∑ k ∈ Finset.range n,
        (∫ x in 0..Real.pi,
          (Nat.choose n k : ℝ) * Real.cos ((2 * (n - k) : ℕ) * x))) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    exact hz k hk
  rw [hsum_zero]
  simp [div_eq_mul_inv, mul_comm]

end

end ProofGap.Exercise2293
