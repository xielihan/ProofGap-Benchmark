import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow

namespace ProofGap.Exercise1417_2

noncomputable section

def betaShape (m n : ℕ) (x : ℝ) := x ^ m * (1 - x) ^ n

theorem gap1 (m n : ℕ) (hm : 0 < m) (hn : 0 < n) (x : ℝ) :
    deriv (betaShape m n) x =
      x ^ (m - 1) * (1 - x) ^ (n - 1) *
        ((m : ℝ) - (m + n : ℕ) * x) := by
  unfold betaShape
  have hleft :
      HasDerivAt (fun y : ℝ => y ^ m) ((m : ℝ) * x ^ (m - 1)) x :=
    hasDerivAt_pow m x
  have hsub : HasDerivAt (fun y : ℝ => 1 - y) (-1) x := by
    simpa using
      ((hasDerivAt_const (x : ℝ) (1 : ℝ)).sub (hasDerivAt_id x))
  have hright :
      HasDerivAt (fun y : ℝ => (1 - y) ^ n)
        ((n : ℝ) * (1 - x) ^ (n - 1) * (-1)) x := by
    simpa using hsub.fun_pow n
  have hderiv := hleft.mul hright
  have hderiv_value :
      deriv (fun y : ℝ => y ^ m * (1 - y) ^ n) x =
        (m : ℝ) * x ^ (m - 1) * (1 - x) ^ n +
          x ^ m * ((n : ℝ) * (1 - x) ^ (n - 1) * (-1)) :=
    hderiv.deriv
  have hxm : x ^ m = x ^ (m - 1) * x := by
    calc
      x ^ m = x ^ ((m - 1) + 1) :=
        congrArg (fun k : ℕ => x ^ k) (by omega)
      _ = x ^ (m - 1) * x := pow_succ x (m - 1)
  have hxn : (1 - x) ^ n = (1 - x) ^ (n - 1) * (1 - x) := by
    calc
      (1 - x) ^ n = (1 - x) ^ ((n - 1) + 1) :=
        congrArg (fun k : ℕ => (1 - x) ^ k) (by omega)
      _ = (1 - x) ^ (n - 1) * (1 - x) :=
        pow_succ (1 - x) (n - 1)
  calc
    deriv (fun y : ℝ => y ^ m * (1 - y) ^ n) x =
        (m : ℝ) * x ^ (m - 1) * (1 - x) ^ n +
          x ^ m * ((n : ℝ) * (1 - x) ^ (n - 1) * (-1)) :=
      hderiv_value
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
    have hsumR : (0 : ℝ) < (m + n : ℕ) := by
      positivity
    apply (eq_div_iff (ne_of_gt hsumR)).2
    linarith
theorem gap3 (m n : ℕ) (hm : 0 < m) (hn : 0 < n)
    (hmodd : Odd m) (x : ℝ) (hx0 : 0 < |x|)
    (hx : |x| < (m : ℝ) / (m + n : ℕ)) :
    0 < deriv (betaShape m n) x *
      deriv (betaShape m n) (-x) := by
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
  have hbounds :
      -(m : ℝ) / ((m + n : ℕ) : ℝ) < x ∧
        x < (m : ℝ) / ((m + n : ℕ) : ℝ) := by
    simpa only [neg_div] using (abs_lt.mp hx)
  have hnegxratio :
      -x < (m : ℝ) / ((m + n : ℕ) : ℝ) := by
    have hlow :
        -((m : ℝ) / ((m + n : ℕ) : ℝ)) < x := by
      simpa only [neg_div] using hbounds.1
    have hneg := neg_lt_neg hlow
    simpa only [neg_neg] using hneg
  have hxne : x ≠ 0 := abs_pos.mp hx0
  have heven : Even (m - 1) :=
    hmodd.tsub_odd (by simp)
  have hxpow : 0 < x ^ (m - 1) :=
    heven.pow_pos hxne
  have hnegxpow : 0 < (-x) ^ (m - 1) :=
    heven.pow_pos (neg_ne_zero.mpr hxne)
  have hxlt1 : x < 1 :=
    lt_trans hbounds.2 hratio_lt_one
  have hnegxlt1 : -x < 1 := by
    exact lt_trans hnegxratio hratio_lt_one
  have hlinearx :
      0 < (m : ℝ) - ((m + n : ℕ) : ℝ) * x := by
    have hxmul :
        x * ((m + n : ℕ) : ℝ) < (m : ℝ) :=
      (lt_div_iff₀ hsumR).1 hbounds.2
    apply sub_pos.mpr
    simpa only [mul_comm] using hxmul
  have hlinearnegx :
      0 < (m : ℝ) - ((m + n : ℕ) : ℝ) * (-x) := by
    have hxmul :
        (-x) * ((m + n : ℕ) : ℝ) < (m : ℝ) :=
      (lt_div_iff₀ hsumR).1 hnegxratio
    apply sub_pos.mpr
    simpa only [mul_comm] using hxmul
  have hderivx : 0 < deriv (betaShape m n) x := by
    rw [gap1 m n hm hn x]
    exact mul_pos
      (mul_pos hxpow (pow_pos (sub_pos.mpr hxlt1) _))
      hlinearx
  have hderivnegx : 0 < deriv (betaShape m n) (-x) := by
    rw [gap1 m n hm hn (-x)]
    exact mul_pos
      (mul_pos hnegxpow (pow_pos (sub_pos.mpr hnegxlt1) _))
      hlinearnegx
  exact mul_pos hderivx hderivnegx
theorem gap4 (m n : ℕ) (hm : 0 < m) (hn : 0 < n)
    (hmodd : Odd m) :
    ¬ IsLocalMax (betaShape m n) 0 ∧
      ¬ IsLocalMin (betaShape m n) 0 := by
  have hzero : betaShape m n 0 = 0 := by
    simp [betaShape, Nat.ne_of_gt hm]
  constructor
  · intro hmax
    change
      {y : ℝ | betaShape m n y ≤ betaShape m n 0} ∈ nhds (0 : ℝ)
      at hmax
    rcases Metric.mem_nhds_iff.mp hmax with ⟨ε, hε, hball⟩
    let d : ℝ := min (ε / 2) (1 / 2)
    have hd : 0 < d := by
      dsimp [d]
      exact lt_min (by linarith) (by positivity)
    have hdε : d < ε :=
      lt_of_le_of_lt (min_le_left _ _) (by linarith)
    have hdhalf : d ≤ (1 : ℝ) / 2 := min_le_right _ _
    have hdball : d ∈ Metric.ball (0 : ℝ) ε := by
      simpa [Metric.mem_ball, Real.dist_eq, abs_of_pos hd] using hdε
    have hle : betaShape m n d ≤ betaShape m n 0 :=
      hball hdball
    have hpos : 0 < betaShape m n d := by
      unfold betaShape
      exact mul_pos (pow_pos hd m)
        (pow_pos (by linarith) n)
    rw [hzero] at hle
    linarith
  · intro hmin
    change
      {y : ℝ | betaShape m n 0 ≤ betaShape m n y} ∈ nhds (0 : ℝ)
      at hmin
    rcases Metric.mem_nhds_iff.mp hmin with ⟨ε, hε, hball⟩
    let d : ℝ := ε / 2
    have hd : 0 < d := by
      dsimp [d]
      linarith
    have hdε : d < ε := by
      dsimp [d]
      linarith
    have hnegdball : -d ∈ Metric.ball (0 : ℝ) ε := by
      simpa [Metric.mem_ball, Real.dist_eq, abs_of_pos hd] using hdε
    have hle : betaShape m n 0 ≤ betaShape m n (-d) :=
      hball hnegdball
    have hneg : betaShape m n (-d) < 0 := by
      unfold betaShape
      exact mul_neg_of_neg_of_pos
        (hmodd.pow_neg (by linarith))
        (pow_pos (by linarith) n)
    rw [hzero] at hle
    linarith

end
end ProofGap.Exercise1417_2
