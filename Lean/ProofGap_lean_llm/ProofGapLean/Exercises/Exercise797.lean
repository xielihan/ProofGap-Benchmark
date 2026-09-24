import ProofGapLean.Prelude.Analysis
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

namespace ProofGap.Exercise797

noncomputable section

def f (x : ℝ) : ℝ := Real.exp x * Real.cos (1 / x)
def xseq (n : ℕ) : ℝ := 2 / ((2 * n + 1 : ℕ) * Real.pi)
def xseq' (n : ℕ) : ℝ := 1 / ((n : ℝ) * Real.pi)

/-- Source: `proof_gap/exercise_797/1.txt`; add `n≥1`. -/
private lemma one_lt_pi : (1 : ℝ) < Real.pi := by
  exact lt_of_lt_of_le (by norm_num) Real.two_le_pi

private lemma nat_mul_pi_trig (n : ℕ) :
    Real.cos ((n : ℝ) * Real.pi) = (-1 : ℝ) ^ n ∧
      Real.sin ((n : ℝ) * Real.pi) = 0 := by
  induction n with
  | zero =>
      norm_num
  | succ n ih =>
      have harg :
          ((Nat.succ n : ℕ) : ℝ) * Real.pi =
            (n : ℝ) * Real.pi + Real.pi := by
        rw [Nat.cast_succ]
        ring
      constructor
      · rw [harg, Real.cos_add, ih.1, ih.2, Real.cos_pi, Real.sin_pi]
        simp [pow_succ]
      · rw [harg, Real.sin_add, ih.1, ih.2, Real.cos_pi, Real.sin_pi]
        simp

theorem gap1 (n : ℕ) (hn : 1 ≤ n) : xseq n ∈ Set.Ioo (0 : ℝ) 1 := by
  constructor
  · unfold xseq
    positivity
  · unfold xseq
    have hn3 : 3 ≤ 2 * n + 1 := by omega
    have hn3R : (3 : ℝ) ≤ ((2 * n + 1 : ℕ) : ℝ) := by
      exact_mod_cast hn3
    have hden : (2 : ℝ) < ((2 * n + 1 : ℕ) : ℝ) * Real.pi := by
      calc
        (2 : ℝ) < 3 * 1 := by norm_num
        _ ≤ ((2 * n + 1 : ℕ) : ℝ) * Real.pi :=
          mul_le_mul hn3R one_lt_pi.le (by norm_num) (by positivity)
    have hdenpos : 0 < ((2 * n + 1 : ℕ) : ℝ) * Real.pi := by
      positivity
    apply (div_lt_iff₀ hdenpos).2
    simpa using hden

/-- Source: `proof_gap/exercise_797/2.txt`; bind the primed sequence index and
add `n≥1`. -/
theorem gap2 (n : ℕ) (hn : 1 ≤ n) : xseq' n ∈ Set.Ioo (0 : ℝ) 1 := by
  constructor
  · unfold xseq'
    have hnpos : (0 : ℝ) < (n : ℝ) := by
      exact_mod_cast (show 0 < n by omega)
    positivity
  · unfold xseq'
    have hnR : (1 : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast hn
    have hden : (1 : ℝ) < (n : ℝ) * Real.pi := by
      calc
        (1 : ℝ) < 1 * Real.pi := by simpa using one_lt_pi
        _ ≤ (n : ℝ) * Real.pi :=
          mul_le_mul_of_nonneg_right hnR Real.pi_pos.le
    have hdenpos : 0 < (n : ℝ) * Real.pi := by
      have hnpos : (0 : ℝ) < (n : ℝ) := by
        exact_mod_cast (show 0 < n by omega)
      positivity
    apply (div_lt_iff₀ hdenpos).2
    simpa using hden

/-- Source: `proof_gap/exercise_797/3.txt`; replace `BigEnough(n)` by an
explicit eventual statement. -/
theorem gap3 :
    ∃ N, ∀ n ≥ N,
      |xseq n - xseq' n| = 1 / ((2 * n + 1 : ℕ) * n * Real.pi) := by
  refine ⟨1, ?_⟩
  intro n hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by
    exact_mod_cast (show 0 < n by omega)
  have hoddpos : (0 : ℝ) < ((2 * n + 1 : ℕ) : ℝ) := by
    positivity
  have hpi0 : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  have hid :
      xseq n - xseq' n =
        -(1 / ((2 * n + 1 : ℕ) * n * Real.pi)) := by
    unfold xseq xseq'
    norm_num [Nat.cast_add, Nat.cast_mul]
    field_simp [ne_of_gt hnpos, ne_of_gt hoddpos, hpi0] <;> ring
  rw [hid, abs_neg, abs_of_pos (by positivity)]

/-- Source: `proof_gap/exercise_797/4.txt`; replace `BigEnough`. -/
theorem gap4 :
    ∀ δ > 0, ∃ N, ∀ n ≥ N,
      1 / ((2 * n + 1 : ℕ) * n * Real.pi) < δ := by
  intro δ hδ
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / δ)
  refine ⟨N, ?_⟩
  intro n hn
  change 1 / (((2 * n + 1 : ℕ) : ℝ) * (n : ℝ) * Real.pi) < δ
  have hnR : (N : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast hn
  have hfrac : 1 / δ < (n : ℝ) := lt_of_lt_of_le hN hnR
  have hone : (1 : ℝ) < (n : ℝ) * δ :=
    (div_lt_iff₀ hδ).mp hfrac
  have hnpos : (0 : ℝ) < (n : ℝ) := by
    exact lt_trans (by positivity : (0 : ℝ) < 1 / δ) hfrac
  have hoddge : (1 : ℝ) ≤ ((2 * n + 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 1 ≤ 2 * n + 1 by omega)
  have hfactor :
      (1 : ℝ) ≤ ((2 * n + 1 : ℕ) : ℝ) * Real.pi := by
    calc
      (1 : ℝ) = 1 * 1 := by ring
      _ ≤ ((2 * n + 1 : ℕ) : ℝ) * Real.pi :=
        mul_le_mul hoddge one_lt_pi.le (by norm_num) (by positivity)
  have hden_ge :
      (n : ℝ) ≤ ((2 * n + 1 : ℕ) : ℝ) * (n : ℝ) * Real.pi := by
    calc
      (n : ℝ) = 1 * (n : ℝ) := by ring
      _ ≤ (((2 * n + 1 : ℕ) : ℝ) * Real.pi) * (n : ℝ) :=
        mul_le_mul_of_nonneg_right hfactor hnpos.le
      _ = ((2 * n + 1 : ℕ) : ℝ) * (n : ℝ) * Real.pi := by ring
  have hdenpos :
      0 < ((2 * n + 1 : ℕ) : ℝ) * (n : ℝ) * Real.pi := by
    positivity
  apply (div_lt_iff₀ hdenpos).2
  have hscale := mul_le_mul_of_nonneg_right hden_ge hδ.le
  nlinarith

/-- Source: `proof_gap/exercise_797/5.txt`. -/
theorem gap5 :
    ∀ δ > 0, ∃ N, ∀ n ≥ N, |xseq n - xseq' n| < δ := by
  intro δ hδ
  obtain ⟨N₁, h₁⟩ := gap3
  obtain ⟨N₂, h₂⟩ := gap4 δ hδ
  refine ⟨max N₁ N₂, ?_⟩
  intro n hn
  calc
    |xseq n - xseq' n| =
        1 / ((2 * n + 1 : ℕ) * n * Real.pi) :=
      h₁ n (le_trans (Nat.le_max_left N₁ N₂) hn)
    _ < δ := h₂ n (le_trans (Nat.le_max_right N₁ N₂) hn)

/-- Source: `proof_gap/exercise_797/6.txt`; bind `n≥1`. -/
theorem gap6 (n : ℕ) (hn : 1 ≤ n) :
    |f (xseq n) - f (xseq' n)| =
      Real.exp (1 / ((n : ℝ) * Real.pi)) := by
  have hx :
      1 / xseq n = (n : ℝ) * Real.pi + Real.pi / 2 := by
    unfold xseq
    rw [one_div_div]
    norm_num [Nat.cast_add, Nat.cast_mul] <;> ring
  have hx' : 1 / xseq' n = (n : ℝ) * Real.pi := by
    simp [xseq']
  have htrig := nat_mul_pi_trig n
  have hcos : Real.cos (1 / xseq n) = 0 := by
    rw [hx, Real.cos_add, htrig.1, htrig.2,
      Real.cos_pi_div_two, Real.sin_pi_div_two]
    ring
  have hcos' : |Real.cos (1 / xseq' n)| = 1 := by
    rw [hx', htrig.1]
    simp
  unfold f
  rw [hcos]
  simp only [mul_zero, zero_sub, abs_neg, abs_mul]
  rw [abs_of_pos (Real.exp_pos _), hcos']
  simp [xseq']

/-- Source: `proof_gap/exercise_797/7.txt`; bind `n≥1`. -/
theorem gap7 (n : ℕ) (hn : 1 ≤ n) :
    1 < Real.exp (1 / ((n : ℝ) * Real.pi)) := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by
    exact_mod_cast (show 0 < n by omega)
  calc
    (1 : ℝ) = Real.exp 0 := Real.exp_zero.symm
    _ < Real.exp (1 / ((n : ℝ) * Real.pi)) :=
      Real.exp_lt_exp.mpr (by positivity)

/-- Source: `proof_gap/exercise_797/8.txt`; make the fixed witness explicit. -/
theorem gap8 : (1 : ℝ) = 1 := by
  rfl

/-- Source: `proof_gap/exercise_797/9.txt`; replace `BigEnough` by `n≥1`. -/
theorem gap9 (n : ℕ) (hn : 1 ≤ n) :
    1 < |f (xseq n) - f (xseq' n)| := by
  rw [gap6 n hn]
  exact gap7 n hn

/-- Source: `proof_gap/exercise_797/10.txt`. -/
theorem gap10 : ¬UniformContinuousOn f (Set.Ioo (0 : ℝ) 1) := by
  intro huc
  obtain ⟨δ, hδ, hcontrol⟩ :=
    (Metric.uniformContinuousOn_iff.mp huc) (1 : ℝ) (by norm_num)
  obtain ⟨N, hN⟩ := gap5 δ hδ
  let n : ℕ := max N 1
  have hnN : N ≤ n := by
    dsimp [n]
    exact Nat.le_max_left N 1
  have hn1 : 1 ≤ n := by
    dsimp [n]
    exact Nat.le_max_right N 1
  have hdist : dist (xseq n) (xseq' n) < δ := by
    simpa only [Real.dist_eq] using hN n hnN
  have hsmall :=
    @hcontrol (xseq n) (gap1 n hn1) (xseq' n) (gap2 n hn1) hdist
  have hsmall_abs : |f (xseq n) - f (xseq' n)| < 1 := by
    simpa only [Real.dist_eq] using hsmall
  nlinarith [gap9 n hn1]

/-- Source: `proof_gap/exercise_797/11.txt`. -/
theorem gap11 : ¬UniformContinuousOn f (Set.Ioo (0 : ℝ) 1) := by
  exact gap10

end

end ProofGap.Exercise797
