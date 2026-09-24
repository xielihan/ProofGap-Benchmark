import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1420_2

noncomputable section

open scoped BigOperators

def y (n : ℕ) (x : ℝ) : ℝ :=
  (∑ k ∈ Finset.range (n + 1), x ^ k / (Nat.factorial k : ℝ)) * Real.exp (-x)

private theorem partialSum_hasDerivAt (n : ℕ) (x : ℝ) :
    HasDerivAt
      (fun z : ℝ => ∑ k ∈ Finset.range (n + 1),
        z ^ k / (Nat.factorial k : ℝ))
      (∑ k ∈ Finset.range n,
        x ^ k / (Nat.factorial k : ℝ)) x := by
  induction n with
  | zero =>
      norm_num
      exact hasDerivAt_const x 1
  | succ k ih =>
      have hlast :
          HasDerivAt
            (fun z : ℝ => z ^ (k + 1) /
              (Nat.factorial (k + 1) : ℝ))
            (x ^ k / (Nat.factorial k : ℝ)) x := by
        convert (hasDerivAt_pow (k + 1) x).div_const
            (Nat.factorial (k + 1) : ℝ) using 1
        simp only [Nat.add_sub_cancel, Nat.factorial_succ,
          Nat.cast_mul, Nat.cast_add, Nat.cast_one]
        have hkfac : (Nat.factorial k : ℝ) ≠ 0 := by
          positivity
        have hkone : (k : ℝ) + 1 ≠ 0 := by
          positivity
        field_simp [hkfac, hkone]
      simpa [Finset.sum_range_succ, Nat.succ_eq_add_one] using ih.add hlast

private theorem y_hasDerivAt (n : ℕ) (x : ℝ) :
    HasDerivAt (y n)
      (-(1 / (Nat.factorial n : ℝ)) * Real.exp (-x) * x ^ n) x := by
  have he : HasDerivAt (fun z : ℝ => Real.exp (-z))
      (-Real.exp (-x)) x := by
    simpa using
      (Real.hasDerivAt_exp (-x)).comp x ((hasDerivAt_id x).neg)
  unfold y
  convert (partialSum_hasDerivAt n x).mul he using 1
  simp only [Finset.sum_range_succ]
  ring

private theorem partialSum_zero (n : ℕ) :
    (∑ k ∈ Finset.range (n + 1),
      (0 : ℝ) ^ k / (Nat.factorial k : ℝ)) = 1 := by
  induction n with
  | zero =>
      norm_num
  | succ k ih =>
      simpa [Finset.sum_range_succ, Nat.succ_eq_add_one] using ih

theorem gap1 (n : ℕ) (hn : 0 < n) (hodd : Odd n) (x : ℝ) :
    deriv (y n) x =
      -(1 / (Nat.factorial n : ℝ)) * Real.exp (-x) * x ^ n := by
  exact (y_hasDerivAt n x).deriv

theorem gap2 (n : ℕ) (hn : 0 < n) (hodd : Odd n) (x : ℝ)
    (hcrit : deriv (y n) x = 0) :
    x = 0 := by
  rw [gap1 n hn hodd x] at hcrit
  have hfacpos : 0 < (Nat.factorial n : ℝ) := by
    positivity
  have hfac : (Nat.factorial n : ℝ) ≠ 0 := ne_of_gt hfacpos
  have hone : (1 / (Nat.factorial n : ℝ)) ≠ 0 :=
    one_div_ne_zero hfac
  have hcoef :
      -(1 / (Nat.factorial n : ℝ)) * Real.exp (-x) ≠ 0 :=
    mul_ne_zero (neg_ne_zero.mpr hone) (Real.exp_ne_zero (-x))
  have hxpow : x ^ n = 0 :=
    (mul_eq_zero.mp hcrit).resolve_left hcoef
  by_contra hx0
  exact (pow_ne_zero n hx0) hxpow

theorem gap3 (n : ℕ) (hn : 0 < n) (hodd : Odd n) (x : ℝ)
    (hx : x < 0) :
    0 < deriv (y n) x := by
  have hxpow : x ^ n < 0 := by
    rcases hodd with ⟨k, hk⟩
    rw [hk, pow_add, pow_mul, pow_one]
    exact mul_neg_of_pos_of_neg (pow_pos (sq_pos_of_neg hx) k) hx
  rw [gap1 n hn hodd x]
  have hfacpos : 0 < (Nat.factorial n : ℝ) := by
    positivity
  have honepos : 0 < (1 / (Nat.factorial n : ℝ)) :=
    one_div_pos.mpr hfacpos
  have hneg : -(1 / (Nat.factorial n : ℝ)) < 0 :=
    neg_lt_zero.mpr honepos
  have hcoef :
      -(1 / (Nat.factorial n : ℝ)) * Real.exp (-x) < 0 :=
    mul_neg_of_neg_of_pos hneg (Real.exp_pos (-x))
  exact mul_pos_of_neg_of_neg hcoef hxpow

theorem gap4 (n : ℕ) (hn : 0 < n) (hodd : Odd n) (x : ℝ)
    (hx : 0 < x) :
    deriv (y n) x < 0 := by
  rw [gap1 n hn hodd x]
  have hfacpos : 0 < (Nat.factorial n : ℝ) := by
    positivity
  have honepos : 0 < (1 / (Nat.factorial n : ℝ)) :=
    one_div_pos.mpr hfacpos
  have hneg : -(1 / (Nat.factorial n : ℝ)) < 0 :=
    neg_lt_zero.mpr honepos
  have hcoef :
      -(1 / (Nat.factorial n : ℝ)) * Real.exp (-x) < 0 :=
    mul_neg_of_neg_of_pos hneg (Real.exp_pos (-x))
  exact mul_neg_of_neg_of_pos hcoef (pow_pos hx n)

theorem gap5 (n : ℕ) (hn : 0 < n) (hodd : Odd n) :
    IsMaxOn (y n) Set.univ 0 ∧ y n 0 = 1 := by
  have hycont : Continuous (y n) :=
    continuous_iff_continuousAt.mpr fun z =>
      (y_hasDerivAt n z).continuousAt
  have hmono : MonotoneOn (y n) (Set.Iic (0 : ℝ)) := by
    refine monotoneOn_of_deriv_nonneg (convex_Iic (0 : ℝ))
      hycont.continuousOn
      (fun z _ => (y_hasDerivAt n z).differentiableAt.differentiableWithinAt) ?_
    intro z hz
    have hzneg : z < 0 := by
      simpa only [interior_Iic, Set.mem_Iio] using hz
    exact (gap3 n hn hodd z hzneg).le
  have hanti : AntitoneOn (y n) (Set.Ici (0 : ℝ)) := by
    refine antitoneOn_of_deriv_nonpos (convex_Ici (0 : ℝ))
      hycont.continuousOn
      (fun z _ => (y_hasDerivAt n z).differentiableAt.differentiableWithinAt) ?_
    intro z hz
    have hzpos : 0 < z := by
      simpa only [interior_Ici, Set.mem_Ioi] using hz
    exact (gap4 n hn hodd z hzpos).le
  constructor
  · intro z hz
    rcases le_total z 0 with hzle | hzge
    · exact hmono hzle (by simp) hzle
    · exact hanti (by simp) hzge hzge
  · simpa [y] using partialSum_zero n

end
end ProofGap.Exercise1420_2
