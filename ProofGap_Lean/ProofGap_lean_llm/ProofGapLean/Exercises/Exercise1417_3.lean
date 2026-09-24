import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.MeanValue

namespace ProofGap.Exercise1417_3

noncomputable section

def betaShape (m n : ℕ) (x : ℝ) := x ^ m * (1 - x) ^ n
def criticalPoint (m n : ℕ) : ℝ := (m : ℝ) / (m + n : ℕ)

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
    x = 0 ∨ x = 1 ∨ x = criticalPoint m n := by
  unfold criticalPoint
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
    (x : ℝ) (hx0 : 0 < x) (hxc : x < criticalPoint m n) :
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
  have hx1 : x < 1 := by
    exact lt_trans hxc (by simpa [criticalPoint] using hratio_lt_one)
  have hxmul : x * ((m + n : ℕ) : ℝ) < (m : ℝ) := by
    apply (lt_div_iff₀ hsumR).1
    simpa [criticalPoint] using hxc
  have hlinear :
      0 < (m : ℝ) - ((m + n : ℕ) : ℝ) * x := by
    apply sub_pos.mpr
    simpa only [mul_comm] using hxmul
  rw [gap1 m n hm hn x]
  exact mul_pos
    (mul_pos (pow_pos hx0 _) (pow_pos (sub_pos.mpr hx1) _))
    hlinear
theorem gap4 (m n : ℕ) (hm : 0 < m) (hn : 0 < n)
    (x : ℝ) (hxc : criticalPoint m n < x) (hx1 : x < 1) :
    deriv (betaShape m n) x < 0 := by
  have hmR : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr hm
  have hnR : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have hsumR : (0 : ℝ) < ((m + n : ℕ) : ℝ) := by
    simpa only [Nat.cast_add] using add_pos hmR hnR
  have hcpos : 0 < criticalPoint m n := by
    unfold criticalPoint
    exact div_pos hmR hsumR
  have hx0 : 0 < x := lt_trans hcpos hxc
  have hmul : (m : ℝ) < x * ((m + n : ℕ) : ℝ) := by
    apply (div_lt_iff₀ hsumR).1
    simpa [criticalPoint] using hxc
  have hlinear :
      (m : ℝ) - ((m + n : ℕ) : ℝ) * x < 0 := by
    apply sub_neg.mpr
    simpa only [mul_comm] using hmul
  rw [gap1 m n hm hn x]
  exact mul_neg_of_pos_of_neg
    (mul_pos (pow_pos hx0 _) (pow_pos (sub_pos.mpr hx1) _))
    hlinear
theorem gap5 (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    IsMaxOn (betaShape m n) (Set.Icc 0 1) (criticalPoint m n) ∧
      betaShape m n (criticalPoint m n) =
        ((m : ℝ) ^ m * (n : ℝ) ^ n) / (m + n : ℕ) ^ (m + n) := by
  have hmR : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr hm
  have hnR : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have hsumR : (0 : ℝ) < ((m + n : ℕ) : ℝ) := by
    simpa only [Nat.cast_add] using add_pos hmR hnR
  have hcpos : 0 < criticalPoint m n := by
    unfold criticalPoint
    exact div_pos hmR hsumR
  have hclt1 : criticalPoint m n < 1 := by
    unfold criticalPoint
    apply (div_lt_iff₀ hsumR).2
    simpa only [one_mul, Nat.cast_add] using
      (lt_add_of_pos_right (m : ℝ) hnR)
  have hcont : Continuous (betaShape m n) := by
    unfold betaShape
    exact (continuous_id.pow m).mul
      ((continuous_const.sub continuous_id).pow n)
  have hmono :
      StrictMonoOn (betaShape m n) (Set.Icc 0 (criticalPoint m n)) := by
    apply strictMonoOn_of_deriv_pos
      (convex_Icc (0 : ℝ) (criticalPoint m n))
      hcont.continuousOn
    intro x hx
    rw [interior_Icc] at hx
    exact gap3 m n hm hn x hx.1 hx.2
  have hanti :
      StrictAntiOn (betaShape m n) (Set.Icc (criticalPoint m n) 1) := by
    apply strictAntiOn_of_deriv_neg
      (convex_Icc (criticalPoint m n) (1 : ℝ))
      hcont.continuousOn
    intro x hx
    rw [interior_Icc] at hx
    exact gap4 m n hm hn x hx.1 hx.2
  constructor
  · rw [isMaxOn_iff]
    intro x hx
    by_cases hxc : x ≤ criticalPoint m n
    · exact hmono.monotoneOn
        ⟨hx.1, hxc⟩ ⟨le_of_lt hcpos, le_rfl⟩ hxc
    · have hcx : criticalPoint m n ≤ x := le_of_lt (lt_of_not_ge hxc)
      exact hanti.antitoneOn
        ⟨le_rfl, le_of_lt hclt1⟩ ⟨hcx, hx.2⟩ hcx
  · unfold betaShape criticalPoint
    have hsum_ne : (((m + n : ℕ) : ℝ)) ≠ 0 :=
      ne_of_gt hsumR
    have hone_sub :
        1 - (m : ℝ) / ((m + n : ℕ) : ℝ) =
          (n : ℝ) / ((m + n : ℕ) : ℝ) := by
      field_simp
      simp only [Nat.cast_add]
      ring
    rw [hone_sub, div_pow, div_pow, pow_add]
    field_simp

end
end ProofGap.Exercise1417_3
