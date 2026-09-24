import ProofGapLean.Prelude.Analysis
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

namespace ProofGap.Exercise2755

noncomputable section

open Filter
open scoped Topology

def f (n : ℕ) (x : ℝ) : ℝ :=
  Real.sin (n * x) / n

def g (n : ℕ) (x : ℝ) : ℝ :=
  Real.sin (x / n)

def UniformlyConvergesOn
    (u : ℕ → ℝ → ℝ) (F : ℝ → ℝ) (s : Set ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ N : ℕ, ∀ n : ℕ, N < n → ∀ x ∈ s, |u n x - F x| < ε

private theorem exercise2755_f_eventually_small :
    ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, ∀ n : ℕ, N < n → ∀ x : ℝ, |f n x| < ε := by
  intro ε hε
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / ε)
  refine ⟨N, ?_⟩
  intro n hn x
  have hNn : (N : ℝ) < (n : ℝ) := by
    exact_mod_cast hn
  have hnlarge : 1 / ε < (n : ℝ) :=
    lt_trans hN hNn
  have hnpos : 0 < (n : ℝ) :=
    lt_trans (one_div_pos.mpr hε) hnlarge
  have hone : (1 : ℝ) < (n : ℝ) * ε :=
    (div_lt_iff₀ hε).mp hnlarge
  have hinv : 1 / (n : ℝ) < ε := by
    apply (div_lt_iff₀ hnpos).2
    simpa [mul_comm] using hone
  calc
    |f n x| = |Real.sin (n * x)| / (n : ℝ) := by
      simp [f, abs_div, abs_of_pos hnpos]
    _ ≤ 1 / (n : ℝ) := by
      exact (div_le_div_iff_of_pos_right hnpos).2
        (Real.abs_sin_le_one ((n : ℝ) * x))
    _ < ε := hinv

theorem gap1 :
    ∀ x : ℝ, Tendsto (fun n : ℕ => f n x) atTop (𝓝 0) := by
  intro x
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := exercise2755_f_eventually_small ε hε
  refine ⟨N + 1, ?_⟩
  intro n hn
  have hn' : N < n :=
    Nat.lt_of_lt_of_le (Nat.lt_succ_self N) hn
  simpa [Real.dist_eq] using hN n hn' x

theorem gap2 :
    ∀ x : ℝ, (0 : ℝ) = 0 := by
  intro x
  rfl

theorem gap3 :
    ∀ x : ℝ, Tendsto (fun n : ℕ => f n x) atTop (𝓝 0) := by
  exact gap1

theorem gap4 :
    ∀ (n : ℕ) (x : ℝ), |f n x| = |Real.sin (n * x)| / n := by
  intro n x
  rw [f, abs_div, abs_of_nonneg (show (0 : ℝ) ≤ (n : ℝ) from Nat.cast_nonneg n)]

theorem gap5 :
    ∀ (n : ℕ) (x : ℝ), |Real.sin (n * x)| / n ≤ 1 / (n : ℝ) := by
  intro n x
  by_cases hn : n = 0
  · subst n
    simp
  · have hnpos : 0 < (n : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero hn
    exact
      (div_le_div_iff_of_pos_right hnpos).2
        (Real.abs_sin_le_one ((n : ℝ) * x))

theorem gap6 :
    ∀ (n : ℕ) (x : ℝ), |f n x| ≤ 1 / (n : ℝ) := by
  intro n x
  calc
    |f n x| = |Real.sin (n * x)| / (n : ℝ) := gap4 n x
    _ ≤ 1 / (n : ℝ) := gap5 n x

theorem gap7 :
    ∀ (n : ℕ) (x ε : ℝ), 0 < ε →
      1 / ε < (n : ℝ) → |f n x| < ε := by
  intro n x ε hε hn
  have hnpos : 0 < (n : ℝ) :=
    lt_trans (one_div_pos.mpr hε) hn
  have hone : (1 : ℝ) < (n : ℝ) * ε :=
    (div_lt_iff₀ hε).mp hn
  have hinv : 1 / (n : ℝ) < ε := by
    apply (div_lt_iff₀ hnpos).2
    simpa [mul_comm] using hone
  exact lt_of_le_of_lt (gap6 n x) hinv

theorem gap8 :
    ∀ (n : ℕ) (x ε : ℝ), 0 < ε →
      1 / ε < (n : ℝ) → |f n x| < ε := by
  exact gap7

theorem gap9 :
    ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, ∀ n : ℕ, N < n → ∀ x : ℝ, |f n x| < ε := by
  exact exercise2755_f_eventually_small

theorem gap10 :
    UniformlyConvergesOn f (fun _ => 0) Set.univ := by
  intro ε hε
  obtain ⟨N, hN⟩ := gap9 ε hε
  refine ⟨N, ?_⟩
  intro n hn x hx
  simpa using hN n hn x

theorem gap11 :
    ∀ x : ℝ, Tendsto (fun n : ℕ => g n x) atTop (𝓝 0) := by
  intro x
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := exists_nat_gt (|x| / ε)
  refine ⟨N + 1, ?_⟩
  intro n hn
  have hNn : N < n :=
    Nat.lt_of_lt_of_le (Nat.lt_succ_self N) hn
  have hNn_real : (N : ℝ) < (n : ℝ) := by
    exact_mod_cast hNn
  have hlarge : |x| / ε < (n : ℝ) :=
    lt_trans hN hNn_real
  have hn_nat_pos : 0 < n :=
    lt_of_lt_of_le (Nat.zero_lt_succ N) hn
  have hnpos : 0 < (n : ℝ) := by
    exact_mod_cast hn_nat_pos
  have hxmul : |x| < (n : ℝ) * ε :=
    (div_lt_iff₀ hε).mp hlarge
  have hquot : |x| / (n : ℝ) < ε := by
    apply (div_lt_iff₀ hnpos).2
    simpa [mul_comm] using hxmul
  rw [Real.dist_eq]
  simp only [sub_zero, g]
  calc
    |Real.sin (x / (n : ℝ))| ≤ |x / (n : ℝ)| := by
      exact Real.abs_sin_le_abs
    _ = |x| / (n : ℝ) := by
      rw [abs_div, abs_of_pos hnpos]
    _ < ε := hquot

theorem gap12 :
    ∀ x : ℝ, (0 : ℝ) = 0 := by
  intro x
  rfl

theorem gap13 :
    ∀ x : ℝ, Tendsto (fun n : ℕ => g n x) atTop (𝓝 0) := by
  exact gap11

theorem gap14 :
    ∀ (n : ℕ) (ε₀ : ℝ), 1 ≤ n → 0 < ε₀ → ε₀ < 1 →
      |g n (n * Real.pi / 2)| = 1 := by
  intro n ε₀ hn hε₀ hε₀_one
  have hnpos_nat : 0 < n :=
    lt_of_lt_of_le Nat.zero_lt_one hn
  have hn0 : (n : ℝ) ≠ 0 := by
    have : 0 < (n : ℝ) := by
      exact_mod_cast hnpos_nat
    exact ne_of_gt this
  have harg :
      ((n : ℝ) * Real.pi / 2) / (n : ℝ) = Real.pi / 2 := by
    calc
      ((n : ℝ) * Real.pi / 2) / (n : ℝ) =
          ((n : ℝ) / (n : ℝ)) * (Real.pi / 2) := by ring
      _ = Real.pi / 2 := by rw [div_self hn0, one_mul]
  change |Real.sin (((n : ℝ) * Real.pi / 2) / (n : ℝ))| = 1
  rw [harg, Real.sin_pi_div_two, abs_one]

theorem gap15 :
    ∀ ε₀ : ℝ, 0 < ε₀ → ε₀ < 1 → 1 > ε₀ := by
  intro ε₀ hε₀ hε₀_one
  exact hε₀_one

theorem gap16 :
    ∀ (n : ℕ) (ε₀ : ℝ), 1 ≤ n → 0 < ε₀ → ε₀ < 1 →
      |g n (n * Real.pi / 2)| > ε₀ := by
  intro n ε₀ hn hε₀ hε₀_one
  rw [gap14 n ε₀ hn hε₀ hε₀_one]
  exact hε₀_one

theorem gap17 :
    ¬ UniformlyConvergesOn g (fun _ => 0) Set.univ := by
  intro h
  rw [UniformlyConvergesOn] at h
  rcases h (1 / 2 : ℝ) (by norm_num) with ⟨N, hN⟩
  have hu := hN (N + 1) (Nat.lt_succ_self N)
    ((N + 1 : ℕ) * Real.pi / 2) (Set.mem_univ _)
  have hu' :
      |g (N + 1) ((N + 1 : ℕ) * Real.pi / 2)| < (1 / 2 : ℝ) := by
    simpa using hu
  have hl :
      (1 / 2 : ℝ) < |g (N + 1) ((N + 1 : ℕ) * Real.pi / 2)| := by
    exact gap16 (N + 1) (1 / 2 : ℝ)
      (Nat.succ_le_succ (Nat.zero_le N)) (by norm_num) (by norm_num)
  exact lt_asymm hl hu'

theorem gap18 :
    UniformlyConvergesOn f (fun _ => 0) Set.univ ∧
      ¬ UniformlyConvergesOn g (fun _ => 0) Set.univ := by
  exact ⟨gap10, gap17⟩

end

end ProofGap.Exercise2755
