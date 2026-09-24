import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Lean.Elab.Tactic.Omega

namespace ProofGap.Exercise841

noncomputable section

def y (m n : ℕ) (x : ℝ) : ℝ :=
  (1 + n * x ^ m) * (1 + m * x ^ n)
def bracket (m n : ℕ) (x : ℝ) : ℝ :=
  x ^ (m - 1) + x ^ (n - 1) + (m + n) * x ^ (m + n - 1)

theorem gap1 (m n : ℕ) (x : ℝ) :
    deriv (y m n) x =
      m * n * x ^ (m - 1) * (1 + m * x ^ n) +
      m * n * x ^ (n - 1) * (1 + n * x ^ m) := by
  have hpowm : HasDerivAt (fun t : ℝ => t ^ m)
      ((m : ℝ) * x ^ (m - 1)) x := by
    simpa using (hasDerivAt_id x).pow m
  have hpown : HasDerivAt (fun t : ℝ => t ^ n)
      ((n : ℝ) * x ^ (n - 1)) x := by
    simpa using (hasDerivAt_id x).pow n
  have hleft : HasDerivAt (fun t : ℝ => 1 + n * t ^ m)
      ((n : ℝ) * ((m : ℝ) * x ^ (m - 1))) x := by
    simpa only [zero_add] using
      (hasDerivAt_const x (1 : ℝ)).add (hpowm.const_mul (n : ℝ))
  have hright : HasDerivAt (fun t : ℝ => 1 + m * t ^ n)
      ((m : ℝ) * ((n : ℝ) * x ^ (n - 1))) x := by
    simpa only [zero_add] using
      (hasDerivAt_const x (1 : ℝ)).add (hpown.const_mul (m : ℝ))
  change deriv ((fun t : ℝ => 1 + (n : ℝ) * t ^ m) *
      (fun t : ℝ => 1 + (m : ℝ) * t ^ n)) x = _
  rw [(hleft.mul hright).deriv]
  ring
theorem gap2 (m n : ℕ) (x : ℝ) :
    deriv (y m n) x = m * n * bracket m n x := by
  cases m with
  | zero =>
      simp [gap1, bracket]
  | succ m =>
      cases n with
      | zero =>
          simp [gap1, bracket]
      | succ n =>
          rw [gap1]
          unfold bracket
          simp only [Nat.succ_sub_one]
          rw [show Nat.succ m + Nat.succ n - 1 = m + n + 1 by omega]
          simp only [pow_succ, pow_add, Nat.cast_succ]
          ring
theorem gap3 (m n : ℕ) (x : ℝ) (hm : 0 < m) (hn : 0 < n)
    (hcrit : deriv (y m n) x = 0) :
    bracket m n x = 0 := by
  rw [gap2] at hcrit
  have hm0 : (m : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hm)
  have hn0 : (n : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hn)
  exact (mul_eq_zero.mp hcrit).resolve_left (mul_ne_zero hm0 hn0)
theorem gap4 (m n : ℕ) (x : ℝ) (hm : 0 < m) (hn : 0 < n)
    (hx : x ≠ 0) (hcrit : deriv (y m n) x = 0) :
    bracket m n x = 0 := by
  exact gap3 m n x hm hn hcrit
theorem gap5 (m n : ℕ) (x : ℝ) (hm : 0 < m) (hn : 0 < n) (hx : x = 0) :
    deriv (y m n) x = 0 ↔ 1 < m ∧ 1 < n := by
  subst x
  constructor
  · intro hcrit
    have hb : bracket m n 0 = 0 := gap3 m n 0 hm hn hcrit
    unfold bracket at hb
    have hA : 0 ≤ (0 : ℝ) ^ (m - 1) := by positivity
    have hB : 0 ≤ (0 : ℝ) ^ (n - 1) := by positivity
    have hC : 0 ≤ (m + n) * (0 : ℝ) ^ (m + n - 1) := by positivity
    have hA0 : (0 : ℝ) ^ (m - 1) = 0 := by nlinarith
    have hB0 : (0 : ℝ) ^ (n - 1) = 0 := by nlinarith
    have hm1 : m ≠ 1 := by
      intro heq
      subst m
      norm_num at hA0
    have hn1 : n ≠ 1 := by
      intro heq
      subst n
      norm_num at hB0
    exact ⟨by omega, by omega⟩
  · rintro ⟨hm2, hn2⟩
    rw [gap1]
    simp [show m - 1 ≠ 0 by omega, show n - 1 ≠ 0 by omega]
theorem gap6 (m n : ℕ) (x : ℝ) (hm : 0 < m) (hn : 0 < n) :
    x ∈ {z : ℝ |
      (z = 0 ∧ 1 < m ∧ 1 < n) ∨ (z ≠ 0 ∧ bracket m n z = 0)} ↔
      deriv (y m n) x = 0 := by
  constructor
  · intro h
    rcases h with ⟨rfl, hm2, hn2⟩ | ⟨hx, hb⟩
    · rw [gap1]
      simp [show m - 1 ≠ 0 by omega, show n - 1 ≠ 0 by omega]
    · simp [gap2, hb]
  · intro hcrit
    by_cases hx : x = 0
    · subst x
      left
      have hb : bracket m n 0 = 0 := gap3 m n 0 hm hn hcrit
      unfold bracket at hb
      have hA : 0 ≤ (0 : ℝ) ^ (m - 1) := by positivity
      have hB : 0 ≤ (0 : ℝ) ^ (n - 1) := by positivity
      have hC : 0 ≤ (m + n) * (0 : ℝ) ^ (m + n - 1) := by positivity
      have hA0 : (0 : ℝ) ^ (m - 1) = 0 := by
        nlinarith
      have hB0 : (0 : ℝ) ^ (n - 1) = 0 := by
        nlinarith
      have hm1 : m ≠ 1 := by
        intro h
        subst m
        norm_num at hA0
      have hn1 : n ≠ 1 := by
        intro h
        subst n
        norm_num at hB0
      exact ⟨rfl, by omega, by omega⟩
    · right
      exact ⟨hx, gap4 m n x hm hn hx hcrit⟩

end

end ProofGap.Exercise841
