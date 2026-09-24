import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise3599

noncomputable section

open scoped BigOperators ENNReal

def f (x y : ℝ) : ℝ :=
  Real.sin (x ^ 2 + y ^ 2)

def radialSineTerm (x y : ℝ) (n : ℕ) : ℝ :=
  (-1 : ℝ) ^ n * (x ^ 2 + y ^ 2) ^ (2 * n + 1) /
    (Nat.factorial (2 * n + 1) : ℝ)

def triangularTerm (x y : ℝ) (n k : ℕ) : ℝ :=
  (-1 : ℝ) ^ n *
      (x ^ (2 * k) * y ^ (2 * (2 * n + 1 - k))) /
    ((Nat.factorial k : ℝ) * (Nat.factorial (2 * n + 1 - k) : ℝ))

def rectangularTerm (x y : ℝ) (m n : ℕ) : ℝ :=
  Real.sin ((((m + n : ℕ) : ℝ) / 2) * Real.pi) *
      (x ^ (2 * n) * y ^ (2 * m)) /
    ((Nat.factorial m : ℝ) * (Nat.factorial n : ℝ))

def convergenceRegion : Set (ℝ × ℝ) :=
  {p | Summable (fun q : ℕ × ℕ => rectangularTerm p.1 p.2 q.1 q.2)}

def finiteRadialRegion : Set (ℝ × ℝ) :=
  {p | ENNReal.ofReal (p.1 ^ 2 + p.2 ^ 2) < ⊤}

private def sineCoefficient (a : ℝ) (n : ℕ) : ℝ :=
  Real.sin (((n : ℝ) / 2) * Real.pi) * a ^ n /
    (Nat.factorial n : ℝ)

private def cosineCoefficient (a : ℝ) (n : ℕ) : ℝ :=
  Real.cos (((n : ℝ) / 2) * Real.pi) * a ^ n /
    (Nat.factorial n : ℝ)

private lemma i_pow_im (n : ℕ) :
    (Complex.I ^ n).im =
      Real.sin (((n : ℝ) / 2) * Real.pi) := by
  have h := congrArg Complex.im
    (Complex.cos_add_sin_mul_I_pow n ((Real.pi / 2 : ℝ) : ℂ))
  have harg :
      (n : ℂ) * ((Real.pi / 2 : ℝ) : ℂ) =
        (((n : ℝ) * (Real.pi / 2) : ℝ) : ℂ) := by
    push_cast
    ring
  have h' :
      (Complex.I ^ n).im =
        (Complex.cos ((((n : ℝ) * (Real.pi / 2) : ℝ) : ℂ)) +
          Complex.sin ((((n : ℝ) * (Real.pi / 2) : ℝ) : ℂ)) * Complex.I).im := by
    convert h using 1
    · simp
    · rw [harg]
  rw [Complex.add_im, Complex.cos_ofReal_im, Complex.mul_im,
    Complex.sin_ofReal_re, Complex.sin_ofReal_im] at h'
  rw [show (n : ℝ) * (Real.pi / 2) =
    ((n : ℝ) / 2) * Real.pi by ring] at h'
  simpa using h'

private lemma i_pow_re (n : ℕ) :
    (Complex.I ^ n).re =
      Real.cos (((n : ℝ) / 2) * Real.pi) := by
  have h := congrArg Complex.re
    (Complex.cos_add_sin_mul_I_pow n ((Real.pi / 2 : ℝ) : ℂ))
  have harg :
      (n : ℂ) * ((Real.pi / 2 : ℝ) : ℂ) =
        (((n : ℝ) * (Real.pi / 2) : ℝ) : ℂ) := by
    push_cast
    ring
  have h' :
      (Complex.I ^ n).re =
        (Complex.cos ((((n : ℝ) * (Real.pi / 2) : ℝ) : ℂ)) +
          Complex.sin ((((n : ℝ) * (Real.pi / 2) : ℝ) : ℂ)) * Complex.I).re := by
    convert h using 1
    · simp
    · rw [harg]
  rw [Complex.add_re, Complex.cos_ofReal_re, Complex.mul_re,
    Complex.sin_ofReal_re, Complex.sin_ofReal_im] at h'
  rw [show (n : ℝ) * (Real.pi / 2) =
    ((n : ℝ) / 2) * Real.pi by ring] at h'
  simpa using h'

private lemma hasSum_sineCoefficient (a : ℝ) :
    HasSum (sineCoefficient a) (Real.sin a) := by
  have h := Complex.hasSum_im
    (NormedSpace.expSeries_div_hasSum_exp (((a : ℂ) * Complex.I)))
  convert h using 1
  · funext n
    rw [sineCoefficient, mul_pow]
    have hfac : (Nat.factorial n : ℝ) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero n
    simp [i_pow_im, div_eq_mul_inv, hfac]
    field_simp
    have hre : ((a : ℂ) ^ n).re = a ^ n := by
      have hr := congrArg Complex.re (Complex.ofReal_pow a n)
      change a ^ n = ((a : ℂ) ^ n).re at hr
      exact hr.symm
    have him : ((a : ℂ) ^ n).im = 0 := by
      have hi := congrArg Complex.im (Complex.ofReal_pow a n)
      change 0 = ((a : ℂ) ^ n).im at hi
      exact hi.symm
    rw [hre, him]
    ring
  · rw [← Complex.exp_eq_exp_ℂ]
    exact (Complex.exp_ofReal_mul_I_im a).symm

private lemma hasSum_cosineCoefficient (a : ℝ) :
    HasSum (cosineCoefficient a) (Real.cos a) := by
  have h := Complex.hasSum_re
    (NormedSpace.expSeries_div_hasSum_exp (((a : ℂ) * Complex.I)))
  convert h using 1
  · funext n
    rw [cosineCoefficient, mul_pow]
    have hfac : (Nat.factorial n : ℝ) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero n
    simp [i_pow_re, div_eq_mul_inv, hfac]
    field_simp
    have hre : ((a : ℂ) ^ n).re = a ^ n := by
      have hr := congrArg Complex.re (Complex.ofReal_pow a n)
      change a ^ n = ((a : ℂ) ^ n).re at hr
      exact hr.symm
    have him : ((a : ℂ) ^ n).im = 0 := by
      have hi := congrArg Complex.im (Complex.ofReal_pow a n)
      change 0 = ((a : ℂ) ^ n).im at hi
      exact hi.symm
    rw [hre, him]
    ring
  · rw [← Complex.exp_eq_exp_ℂ]
    exact (Complex.exp_ofReal_mul_I_re a).symm

private lemma summable_norm_sineCoefficient (a : ℝ) :
    Summable (fun n => ‖sineCoefficient a n‖) := by
  apply Summable.of_norm_bounded (Real.summable_pow_div_factorial |a|)
  intro n
  rw [Real.norm_of_nonneg (norm_nonneg _)]
  rw [Real.norm_eq_abs, sineCoefficient, abs_div, abs_mul, abs_pow]
  have hfacnonneg : (0 : ℝ) ≤ (Nat.factorial n : ℝ) := Nat.cast_nonneg _
  rw [abs_of_nonneg hfacnonneg]
  have hmul :
      |Real.sin (((n : ℝ) / 2) * Real.pi)| * |a| ^ n ≤ |a| ^ n := by
    simpa using mul_le_mul_of_nonneg_right
      (Real.abs_sin_le_one (((n : ℝ) / 2) * Real.pi))
      (pow_nonneg (abs_nonneg a) n)
  exact div_le_div_of_nonneg_right hmul hfacnonneg

private lemma summable_norm_cosineCoefficient (a : ℝ) :
    Summable (fun n => ‖cosineCoefficient a n‖) := by
  apply Summable.of_norm_bounded (Real.summable_pow_div_factorial |a|)
  intro n
  rw [Real.norm_of_nonneg (norm_nonneg _)]
  rw [Real.norm_eq_abs, cosineCoefficient, abs_div, abs_mul, abs_pow]
  have hfacnonneg : (0 : ℝ) ≤ (Nat.factorial n : ℝ) := Nat.cast_nonneg _
  rw [abs_of_nonneg hfacnonneg]
  have hmul :
      |Real.cos (((n : ℝ) / 2) * Real.pi)| * |a| ^ n ≤ |a| ^ n := by
    simpa using mul_le_mul_of_nonneg_right
      (Real.abs_cos_le_one (((n : ℝ) / 2) * Real.pi))
      (pow_nonneg (abs_nonneg a) n)
  exact div_le_div_of_nonneg_right hmul hfacnonneg

private lemma rectangularTerm_decomposition (x y : ℝ) (m n : ℕ) :
    rectangularTerm x y m n =
      sineCoefficient (y ^ 2) m * cosineCoefficient (x ^ 2) n +
      cosineCoefficient (y ^ 2) m * sineCoefficient (x ^ 2) n := by
  unfold rectangularTerm sineCoefficient cosineCoefficient
  have hang :
      ((((m + n : ℕ) : ℝ) / 2) * Real.pi) =
        ((m : ℝ) / 2) * Real.pi + ((n : ℝ) / 2) * Real.pi := by
    push_cast
    ring
  rw [hang, Real.sin_add]
  rw [← pow_mul x 2 n, ← pow_mul y 2 m]
  have hmfac : (Nat.factorial m : ℝ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero m
  have hnfac : (Nat.factorial n : ℝ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero n
  field_simp

private lemma summable_rectangularTerm (x y : ℝ) :
    Summable (fun q : ℕ × ℕ => rectangularTerm x y q.1 q.2) := by
  have h₁ := summable_mul_of_summable_norm
    (summable_norm_sineCoefficient (y ^ 2))
    (summable_norm_cosineCoefficient (x ^ 2))
  have h₂ := summable_mul_of_summable_norm
    (summable_norm_cosineCoefficient (y ^ 2))
    (summable_norm_sineCoefficient (x ^ 2))
  have h := h₁.add h₂
  convert h using 1
  funext q
  exact rectangularTerm_decomposition x y q.1 q.2

theorem gap1 :
    ∀ x y : ℝ, f x y = ∑' n, radialSineTerm x y n := by
  intro x y
  simpa only [f, radialSineTerm, mul_div_assoc] using
    Real.sin_eq_tsum (x ^ 2 + y ^ 2)

theorem gap2 :
    ∀ x y : ℝ,
      f x y =
        ∑' n, ∑ k ∈ Finset.range (2 * n + 2), triangularTerm x y n k := by
  intro x y
  rw [gap1 x y]
  congr 1
  funext n
  rw [radialSineTerm, add_pow, Finset.mul_sum, Finset.sum_div]
  rw [show 2 * n + 1 + 1 = 2 * n + 2 by simp [Nat.add_assoc]]
  apply Finset.sum_congr rfl
  intro k hk
  have hk' : k ≤ 2 * n + 1 := by
    simpa [Nat.lt_succ_iff] using (Finset.mem_range.mp hk)
  rw [triangularTerm, Nat.cast_choose ℝ hk']
  have hfac : ((Nat.factorial (2 * n + 1) : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (2 * n + 1)
  have hkfac : ((Nat.factorial k : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero k
  have hsubfac : ((Nat.factorial (2 * n + 1 - k) : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (2 * n + 1 - k)
  field_simp
  ring

theorem gap3 :
    ∀ x y : ℝ, f x y = ∑' m, ∑' n, rectangularTerm x y m n := by
  intro x y
  have hsy := hasSum_sineCoefficient (y ^ 2)
  have hcy := hasSum_cosineCoefficient (y ^ 2)
  have hsx := hasSum_sineCoefficient (x ^ 2)
  have hcx := hasSum_cosineCoefficient (x ^ 2)
  have hprod₁ := summable_mul_of_summable_norm
    (summable_norm_sineCoefficient (y ^ 2))
    (summable_norm_cosineCoefficient (x ^ 2))
  have hprod₂ := summable_mul_of_summable_norm
    (summable_norm_cosineCoefficient (y ^ 2))
    (summable_norm_sineCoefficient (x ^ 2))
  calc
    f x y =
        Real.sin (y ^ 2) * Real.cos (x ^ 2) +
          Real.cos (y ^ 2) * Real.sin (x ^ 2) := by
            rw [f, Real.sin_add]
            ring
    _ =
        (∑' m, sineCoefficient (y ^ 2) m) *
            (∑' n, cosineCoefficient (x ^ 2) n) +
          (∑' m, cosineCoefficient (y ^ 2) m) *
            (∑' n, sineCoefficient (x ^ 2) n) := by
              rw [hsy.tsum_eq, hcy.tsum_eq, hsx.tsum_eq, hcx.tsum_eq]
    _ =
        (∑' q : ℕ × ℕ,
          sineCoefficient (y ^ 2) q.1 * cosineCoefficient (x ^ 2) q.2) +
        (∑' q : ℕ × ℕ,
          cosineCoefficient (y ^ 2) q.1 * sineCoefficient (x ^ 2) q.2) := by
            rw [tsum_mul_tsum_of_summable_norm
              (summable_norm_sineCoefficient (y ^ 2))
              (summable_norm_cosineCoefficient (x ^ 2))]
            rw [tsum_mul_tsum_of_summable_norm
              (summable_norm_cosineCoefficient (y ^ 2))
              (summable_norm_sineCoefficient (x ^ 2))]
    _ =
        ∑' q : ℕ × ℕ,
          (sineCoefficient (y ^ 2) q.1 * cosineCoefficient (x ^ 2) q.2 +
            cosineCoefficient (y ^ 2) q.1 * sineCoefficient (x ^ 2) q.2) := by
              exact (hprod₁.hasSum.add hprod₂.hasSum).tsum_eq.symm
    _ = ∑' q : ℕ × ℕ, rectangularTerm x y q.1 q.2 := by
      apply tsum_congr
      intro q
      exact (rectangularTerm_decomposition x y q.1 q.2).symm
    _ = ∑' m, ∑' n, rectangularTerm x y m n :=
      (summable_rectangularTerm x y).tsum_prod

theorem gap4 :
    convergenceRegion = finiteRadialRegion := by
  ext p
  simp only [convergenceRegion, finiteRadialRegion, Set.mem_setOf_eq]
  constructor
  · intro _
    exact ENNReal.coe_lt_top
  · intro _
    exact summable_rectangularTerm p.1 p.2

theorem gap5 :
    ∀ x y : ℝ, (x, y) ∈ finiteRadialRegion := by
  intro x y
  simp [finiteRadialRegion]

theorem gap6 :
    convergenceRegion = Set.univ := by
  rw [gap4]
  ext p
  simp [gap5 p.1 p.2]

end

end ProofGap.Exercise3599
