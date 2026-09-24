import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Topology.Neighborhoods
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1417_4

noncomputable section

def betaShape (m n : ℕ) (x : ℝ) := x ^ m * (1 - x) ^ n

private theorem hasDerivAt_pow_succ_real {f : ℝ → ℝ} {f' x : ℝ}
    (hf : HasDerivAt f f' x) (k : ℕ) :
    HasDerivAt (fun y => f y ^ (k + 1))
      (((k + 1 : ℕ) : ℝ) * f x ^ k * f') x := by
  induction k with
  | zero =>
      simpa using hf
  | succ k ih =>
      have hmul := ih.mul hf
      convert hmul using 1 <;>
        simp only [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one,
          pow_succ] <;>
        ring

private theorem even_pow_nonneg_real (n : ℕ) (hn : Even n) (x : ℝ) :
    0 ≤ x ^ n := by
  rcases hn with ⟨k, rfl⟩
  rw [pow_add]
  exact mul_self_nonneg (x ^ k)

private theorem betaShape_pos_between (m n : ℕ) {x : ℝ}
    (hx0 : 0 < x) (hx1 : x < 1) :
    0 < betaShape m n x := by
  unfold betaShape
  exact mul_pos (pow_pos hx0 m) (pow_pos (sub_pos.mpr hx1) n)

private theorem betaShape_neg_right (m n : ℕ) {x : ℝ}
    (hx : 1 < x) (hn : Odd n) :
    betaShape m n x < 0 := by
  unfold betaShape
  apply mul_neg_of_pos_of_neg
  · exact pow_pos (lt_trans zero_lt_one hx) m
  · rw [show 1 - x = (-1 : ℝ) * (x - 1) by ring, mul_pow,
      hn.neg_one_pow, neg_one_mul]
    exact neg_neg_of_pos (pow_pos (sub_pos.mpr hx) n)

theorem gap1 (m n : ℕ) (hm : 0 < m) (hn : 0 < n) (x : ℝ) :
    deriv (betaShape m n) x =
      x ^ (m - 1) * (1 - x) ^ (n - 1) *
        ((m : ℝ) - (m + n : ℕ) * x) := by
  obtain ⟨m, rfl⟩ :=
    Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm)
  obtain ⟨n, rfl⟩ :=
    Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  unfold betaShape
  change
    deriv (fun y : ℝ => y ^ (m + 1) * (1 - y) ^ (n + 1)) x = _
  have hsub :=
    (hasDerivAt_const (x := x) (1 : ℝ)).sub (hasDerivAt_id x)
  have hprod :=
    (hasDerivAt_pow_succ_real (hasDerivAt_id x) m).mul
      (hasDerivAt_pow_succ_real hsub n)
  have hd :
      deriv (fun y : ℝ => y ^ (m + 1) * (1 - y) ^ (n + 1)) x =
        (((m + 1 : ℕ) : ℝ) * x ^ m * 1 * (1 - x) ^ (n + 1) +
          x ^ (m + 1) *
            (((n + 1 : ℕ) : ℝ) * (1 - x) ^ n * (0 - 1))) := by
    simpa using hprod.deriv
  calc
    deriv (fun y : ℝ => y ^ (m + 1) * (1 - y) ^ (n + 1)) x = _ := hd
    _ = _ := by
      simp only [Nat.succ_sub_one, Nat.cast_succ, Nat.cast_add,
        Nat.cast_one, pow_succ]
      ring
theorem gap2 (m n : ℕ) (hm : 0 < m) (hn : 0 < n) (x : ℝ)
    (hcrit : deriv (betaShape m n) x = 0) :
    x = 0 ∨ x = 1 ∨ x = (m : ℝ) / (m + n : ℕ) := by
  rw [gap1 m n hm hn x] at hcrit
  rcases mul_eq_zero.mp hcrit with hab | hc
  · rcases mul_eq_zero.mp hab with hxpow | honepow
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
    have hmn : (0 : ℝ) < (m + n : ℕ) := by
      positivity
    apply (eq_div_iff (ne_of_gt hmn)).2
    linarith
theorem gap3 (m n : ℕ) (hm : 0 < m) (hn : 0 < n)
    (hneven : Even n) :
    IsLocalMin (betaShape m n) 1 ∧ betaShape m n 1 = 0 := by
  have hone : betaShape m n 1 = 0 := by
    simp [betaShape, Nat.ne_of_gt hn]
  constructor
  · change ∀ᶠ y in nhds (1 : ℝ), betaShape m n 1 ≤ betaShape m n y
    filter_upwards [Ioi_mem_nhds (show (0 : ℝ) < 1 by positivity)] with y hy
    rw [hone]
    unfold betaShape
    exact mul_nonneg (pow_nonneg (le_of_lt hy) m)
      (even_pow_nonneg_real n hneven (1 - y))
  · exact hone
theorem gap4 (m n : ℕ) (hm : 0 < m) (hn : 0 < n)
    (hnodd : Odd n) :
    ¬ IsLocalMax (betaShape m n) 1 ∧
      ¬ IsLocalMin (betaShape m n) 1 := by
  have hone : betaShape m n 1 = 0 := by
    simp [betaShape, Nat.ne_of_gt hn]
  constructor
  · intro hmax
    change
      {y : ℝ | betaShape m n y ≤ betaShape m n 1} ∈ nhds (1 : ℝ)
      at hmax
    rcases Metric.mem_nhds_iff.mp hmax with ⟨ε, hε, hball⟩
    let d : ℝ := min (ε / 2) (1 / 2)
    have hd : 0 < d := by
      dsimp [d]
      exact lt_min (by linarith) (by positivity)
    have hdε : d < ε :=
      lt_of_le_of_lt (min_le_left _ _) (by linarith)
    have hdhalf : d ≤ (1 : ℝ) / 2 := min_le_right _ _
    have hxball : 1 - d ∈ Metric.ball (1 : ℝ) ε := by
      rw [Metric.mem_ball, Real.dist_eq]
      have habs : |(1 - d) - 1| = d := by
        rw [show (1 - d) - 1 = -d by ring, abs_neg, abs_of_pos hd]
      rw [habs]
      exact hdε
    have hle : betaShape m n (1 - d) ≤ betaShape m n 1 :=
      hball hxball
    have hxpos : (0 : ℝ) < 1 - d := by linarith
    have hxlt : 1 - d < (1 : ℝ) := by linarith
    have hpos : 0 < betaShape m n (1 - d) :=
      betaShape_pos_between m n hxpos hxlt
    rw [hone] at hle
    linarith
  · intro hmin
    change
      {y : ℝ | betaShape m n 1 ≤ betaShape m n y} ∈ nhds (1 : ℝ)
      at hmin
    rcases Metric.mem_nhds_iff.mp hmin with ⟨ε, hε, hball⟩
    let d : ℝ := min (ε / 2) (1 / 2)
    have hd : 0 < d := by
      dsimp [d]
      exact lt_min (by linarith) (by positivity)
    have hdε : d < ε :=
      lt_of_le_of_lt (min_le_left _ _) (by linarith)
    have hxball : 1 + d ∈ Metric.ball (1 : ℝ) ε := by
      rw [Metric.mem_ball, Real.dist_eq]
      have habs : |(1 + d) - 1| = d := by
        rw [show (1 + d) - 1 = d by ring, abs_of_pos hd]
      rw [habs]
      exact hdε
    have hle : betaShape m n 1 ≤ betaShape m n (1 + d) :=
      hball hxball
    have hxgt : (1 : ℝ) < 1 + d := by linarith
    have hneg : betaShape m n (1 + d) < 0 :=
      betaShape_neg_right m n hxgt hnodd
    rw [hone] at hle
    linarith

end
end ProofGap.Exercise1417_4
