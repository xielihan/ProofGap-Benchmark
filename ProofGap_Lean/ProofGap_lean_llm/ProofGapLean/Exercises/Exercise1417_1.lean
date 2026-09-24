import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Topology.Neighborhoods
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

namespace ProofGap.Exercise1417_1

noncomputable section

def betaShape (m n : ℕ) (x : ℝ) := x ^ m * (1 - x) ^ n

private theorem hasDerivAt_pow_succ_of_hasDerivAt
    {f : ℝ → ℝ} {f' x : ℝ} (hf : HasDerivAt f f' x) (k : ℕ) :
    HasDerivAt (fun y : ℝ => (f y) ^ (k + 1))
      (((k + 1 : ℕ) : ℝ) * (f x) ^ k * f') x := by
  induction k with
  | zero =>
      simpa using hf
  | succ k ih =>
      have h := ih.mul hf
      have hfun :
          (fun y : ℝ => (f y) ^ (Nat.succ k + 1)) =
            (fun y : ℝ => (f y) ^ (k + 1) * f y) := by
        funext y
        rw [show Nat.succ k + 1 = (k + 1) + 1 by omega, pow_succ]
      rw [hfun]
      convert h using 1
      simp only [Nat.cast_add, Nat.cast_one]
      rw [pow_succ]
      ring

theorem gap1 (m n : ℕ) (hm : 0 < m) (hn : 0 < n) (x : ℝ) :
    deriv (betaShape m n) x =
      x ^ (m - 1) * (1 - x) ^ (n - 1) *
        ((m : ℝ) - (m + n : ℕ) * x) := by
  unfold betaShape
  have hleft :
      HasDerivAt (fun y : ℝ => y ^ m) ((m : ℝ) * x ^ (m - 1)) x := by
    simpa [show m - 1 + 1 = m by omega] using
      (hasDerivAt_pow_succ_of_hasDerivAt (hasDerivAt_id x) (m - 1))
  have hsub : HasDerivAt (fun y : ℝ => 1 - y) (-1) x := by
    simpa using
      ((hasDerivAt_const (x : ℝ) (1 : ℝ)).sub (hasDerivAt_id x))
  have hright :
      HasDerivAt (fun y : ℝ => (1 - y) ^ n)
        ((n : ℝ) * (1 - x) ^ (n - 1) * (-1)) x := by
    simpa [show n - 1 + 1 = n by omega] using
      (hasDerivAt_pow_succ_of_hasDerivAt hsub (n - 1))
  have hderiv := hleft.mul hright
  have hderiv_value :
      deriv (fun y : ℝ => y ^ m * (1 - y) ^ n) x =
        (m : ℝ) * x ^ (m - 1) * (1 - x) ^ n +
          x ^ m * ((n : ℝ) * (1 - x) ^ (n - 1) * (-1)) := by
    exact hderiv.deriv
  have hxm : x ^ m = x ^ (m - 1) * x := by
    calc
      x ^ m = x ^ ((m - 1) + 1) :=
        congrArg (fun k : ℕ => x ^ k) (by omega)
      _ = x ^ (m - 1) * x := pow_succ x (m - 1)
  have hxn : (1 - x) ^ n = (1 - x) ^ (n - 1) * (1 - x) := by
    calc
      (1 - x) ^ n = (1 - x) ^ ((n - 1) + 1) :=
        congrArg (fun k : ℕ => (1 - x) ^ k) (by omega)
      _ = (1 - x) ^ (n - 1) * (1 - x) := pow_succ (1 - x) (n - 1)
  calc
    deriv (fun y : ℝ => y ^ m * (1 - y) ^ n) x =
        (m : ℝ) * x ^ (m - 1) * (1 - x) ^ n +
          x ^ m * ((n : ℝ) * (1 - x) ^ (n - 1) * (-1)) := hderiv_value
    _ = x ^ (m - 1) * (1 - x) ^ (n - 1) *
          ((m : ℝ) - (m + n : ℕ) * x) := by
      rw [hxm, hxn]
      simp only [Nat.cast_add]
      ring
theorem gap2 (m n : ℕ) (hm : 0 < m) (hn : 0 < n) (x : ℝ)
    (hcrit : deriv (betaShape m n) x = 0) :
    x = 0 ∨ x = 1 ∨ x = (m : ℝ) / (m + n : ℕ) := by
  rw [gap1 m n hm hn x] at hcrit
  rcases mul_eq_zero.mp hcrit with hprod | hlinear
  · rcases mul_eq_zero.mp hprod with hxpow | honepow
    · left
      by_contra hx
      exact (pow_ne_zero _ hx) hxpow
    · right
      left
      have hone : 1 - x = 0 := by
        by_contra hone
        exact (pow_ne_zero _ hone) honepow
      linarith
  · right
    right
    have hmR : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr hm
    have hnR : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
    have hsumR : (0 : ℝ) < ((m + n : ℕ) : ℝ) := by
      simpa only [Nat.cast_add] using add_pos hmR hnR
    apply (eq_div_iff (ne_of_gt hsumR)).2
    have heq : (m : ℝ) = ((m + n : ℕ) : ℝ) * x := sub_eq_zero.mp hlinear
    calc
      x * ((m + n : ℕ) : ℝ) = ((m + n : ℕ) : ℝ) * x := mul_comm _ _
      _ = (m : ℝ) := heq.symm
theorem gap3 (m n : ℕ) (hm : 0 < m) (hn : 0 < n)
    (x : ℝ) (hx0 : 0 < x) (hxc : x < (m : ℝ) / (m + n : ℕ)) :
    0 < deriv (betaShape m n) x := by
  have hmR : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr hm
  have hnR : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have hsumR : (0 : ℝ) < ((m + n : ℕ) : ℝ) := by
    simpa only [Nat.cast_add] using add_pos hmR hnR
  have hm_lt_sum : (m : ℝ) < ((m + n : ℕ) : ℝ) := by
    simpa only [Nat.cast_add] using
      (lt_add_of_pos_right (m : ℝ) hnR)
  have hratio_lt_one :
      (m : ℝ) / ((m + n : ℕ) : ℝ) < 1 := by
    apply (div_lt_iff₀ hsumR).2
    simpa using hm_lt_sum
  have hx1 : x < 1 := lt_trans hxc hratio_lt_one
  have hxmul : x * ((m + n : ℕ) : ℝ) < (m : ℝ) :=
    (lt_div_iff₀ hsumR).1 hxc
  have hlinear :
      0 < (m : ℝ) - ((m + n : ℕ) : ℝ) * x := by
    apply sub_pos.mpr
    simpa only [mul_comm] using hxmul
  rw [gap1 m n hm hn x]
  exact mul_pos
    (mul_pos (pow_pos hx0 _) (pow_pos (sub_pos.mpr hx1) _))
    hlinear
theorem gap4 (m n : ℕ) (hm : 0 < m) (hn : 0 < n)
    (hmeven : Even m) (x : ℝ) (hx : x < 0) :
    deriv (betaShape m n) x < 0 := by
  rcases hmeven with ⟨k, hk⟩
  have hexp : m - 1 = 2 * (k - 1) + 1 := by
    omega
  have hx2 : 0 < x ^ 2 := by
    rw [pow_two]
    exact mul_pos_of_neg_of_neg hx hx
  have hxpow : x ^ (m - 1) < 0 := by
    rw [hexp, pow_succ, pow_mul]
    exact mul_neg_of_pos_of_neg (pow_pos hx2 _) hx
  have hmR : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr hm
  have hnR : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have hsumR : (0 : ℝ) < ((m + n : ℕ) : ℝ) := by
    simpa only [Nat.cast_add] using add_pos hmR hnR
  have hproduct : ((m + n : ℕ) : ℝ) * x < 0 :=
    mul_neg_of_pos_of_neg hsumR hx
  have hlinear :
      0 < (m : ℝ) - ((m + n : ℕ) : ℝ) * x :=
    sub_pos.mpr (lt_trans hproduct hmR)
  rw [gap1 m n hm hn x]
  exact mul_neg_of_neg_of_pos
    (mul_neg_of_neg_of_pos hxpow (pow_pos (sub_pos.mpr (by linarith)) _))
    hlinear
theorem gap5 (m n : ℕ) (hm : 0 < m) (hn : 0 < n)
    (hmeven : Even m) :
    IsLocalMin (betaShape m n) 0 ∧ betaShape m n 0 = 0 := by
  rcases hmeven with ⟨k, hk⟩
  have hpow_nonneg (y : ℝ) : 0 ≤ y ^ m := by
    rw [hk, pow_add]
    exact mul_self_nonneg (y ^ k)
  have hzero : betaShape m n 0 = 0 := by
    simp [betaShape, hm.ne']
  constructor
  · change ∀ᶠ y in nhds (0 : ℝ), betaShape m n 0 ≤ betaShape m n y
    filter_upwards [eventually_lt_nhds (show (0 : ℝ) < 1 from zero_lt_one)] with y hy
    rw [hzero]
    exact mul_nonneg (hpow_nonneg y)
      (pow_nonneg (sub_nonneg.mpr (le_of_lt hy)) n)
  · exact hzero

end
end ProofGap.Exercise1417_1
