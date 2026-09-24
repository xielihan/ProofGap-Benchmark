import ProofGapLean.Prelude.Analysis
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise604

noncomputable section

def paritySign (n : ℕ) : ℝ := if Even n then 1 else -1
def seq (n : ℕ) : ℝ := Real.sin (Real.pi * Real.sqrt (n ^ 2 + 1))
def shifted (n : ℕ) : ℝ :=
  paritySign n * Real.sin (Real.pi * Real.sqrt (n ^ 2 + 1) - n * Real.pi)
def rationalized (n : ℕ) : ℝ :=
  paritySign n * Real.sin (Real.pi / (Real.sqrt (n ^ 2 + 1) + n))

/-- Exercise 604, gap 1. -/
private theorem paritySign_mul_sin_sub_nat_mul_pi
    (n : ℕ) (x : ℝ) :
    paritySign n * Real.sin (x - n * Real.pi) = Real.sin x := by
  induction n with
  | zero =>
      have hzero : Even (0 : ℕ) := ⟨0, rfl⟩
      simp [paritySign, hzero]
  | succ n ih =>
      have hpar : paritySign (Nat.succ n) = -paritySign n := by
        have heven : Even (Nat.succ n) ↔ ¬ Even n := by
          simp only [Nat.even_iff]
          omega
        by_cases hn : Even n <;> simp [paritySign, hn, heven]
      have harg :
          x - (Nat.succ n : ℝ) * Real.pi =
            (x - (n : ℝ) * Real.pi) - Real.pi := by
        rw [Nat.cast_succ]
        ring
      calc
        paritySign (Nat.succ n) *
            Real.sin (x - (Nat.succ n : ℝ) * Real.pi) =
            (-paritySign n) *
              (-Real.sin (x - (n : ℝ) * Real.pi)) := by
                rw [hpar, harg, Real.sin_sub_pi]
        _ = paritySign n * Real.sin (x - (n : ℝ) * Real.pi) := by ring
        _ = Real.sin x := ih

theorem gap1 (L : ℝ) :
    Filter.Tendsto seq Filter.atTop (nhds L) ↔
      Filter.Tendsto shifted Filter.atTop (nhds L) := by
  have hfun : seq = shifted := by
    funext n
    simp only [seq, shifted]
    exact (paritySign_mul_sin_sub_nat_mul_pi n _).symm
  rw [hfun]

/-- Exercise 604, gap 2. -/
theorem gap2 (L : ℝ) :
    Filter.Tendsto shifted Filter.atTop (nhds L) ↔
      Filter.Tendsto rationalized Filter.atTop (nhds L) := by
  have hfun : shifted = rationalized := by
    funext n
    have hs :
        (Real.sqrt ((n : ℝ) ^ 2 + 1)) ^ 2 = (n : ℝ) ^ 2 + 1 :=
      Real.sq_sqrt (by positivity)
    have hden :
        Real.sqrt ((n : ℝ) ^ 2 + 1) + (n : ℝ) ≠ 0 := by
      positivity
    have hrat :
        Real.sqrt ((n : ℝ) ^ 2 + 1) - (n : ℝ) =
          1 / (Real.sqrt ((n : ℝ) ^ 2 + 1) + (n : ℝ)) := by
      apply (eq_div_iff hden).2
      nlinarith [hs]
    have harg :
        Real.pi * Real.sqrt ((n : ℝ) ^ 2 + 1) - (n : ℝ) * Real.pi =
          Real.pi / (Real.sqrt ((n : ℝ) ^ 2 + 1) + (n : ℝ)) := by
      calc
        Real.pi * Real.sqrt ((n : ℝ) ^ 2 + 1) - (n : ℝ) * Real.pi =
            Real.pi * (Real.sqrt ((n : ℝ) ^ 2 + 1) - (n : ℝ)) := by ring
        _ = Real.pi *
            (1 / (Real.sqrt ((n : ℝ) ^ 2 + 1) + (n : ℝ))) := by rw [hrat]
        _ = Real.pi /
            (Real.sqrt ((n : ℝ) ^ 2 + 1) + (n : ℝ)) := by
              simp [div_eq_mul_inv]
    simp only [shifted, rationalized]
    rw [harg]
  rw [hfun]

/-- Exercise 604, gap 3. -/
theorem gap3 : Filter.Tendsto rationalized Filter.atTop (nhds 0) := by
  have harg :
      Filter.Tendsto
        (fun n : ℕ => Real.pi /
          (Real.sqrt ((n : ℝ) ^ 2 + 1) + (n : ℝ)))
        Filter.atTop (nhds 0) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨N, hN⟩ := exists_nat_gt (Real.pi / ε)
    refine ⟨N, ?_⟩
    intro n hn
    have hNn : (N : ℝ) ≤ (n : ℝ) := Nat.cast_le.2 hn
    have hratio_pos : 0 < Real.pi / ε := div_pos Real.pi_pos hε
    have hNpos : 0 < (N : ℝ) := lt_trans hratio_pos hN
    have hnpos : 0 < (n : ℝ) := lt_of_lt_of_le hNpos hNn
    have hdenpos :
        0 < Real.sqrt ((n : ℝ) ^ 2 + 1) + (n : ℝ) :=
      add_pos_of_nonneg_of_pos (Real.sqrt_nonneg _) hnpos
    have hargpos :
        0 < Real.pi /
          (Real.sqrt ((n : ℝ) ^ 2 + 1) + (n : ℝ)) :=
      div_pos Real.pi_pos hdenpos
    have hd_ge :
        (n : ℝ) ≤ Real.sqrt ((n : ℝ) ^ 2 + 1) + (n : ℝ) := by
      nlinarith [Real.sqrt_nonneg ((n : ℝ) ^ 2 + 1)]
    have hquot_le :
        Real.pi /
            (Real.sqrt ((n : ℝ) ^ 2 + 1) + (n : ℝ)) ≤
          Real.pi / (n : ℝ) := by
      apply (div_le_div_iff₀ hdenpos hnpos).2
      exact mul_le_mul_of_nonneg_left hd_ge (le_of_lt Real.pi_pos)
    have hlarge : Real.pi / ε < (n : ℝ) := lt_of_lt_of_le hN hNn
    have hpi : Real.pi < (n : ℝ) * ε := (div_lt_iff₀ hε).1 hlarge
    have hfinal : Real.pi / (n : ℝ) < ε := by
      apply (div_lt_iff₀ hnpos).2
      simpa [mul_comm] using hpi
    calc
      dist
          (Real.pi /
            (Real.sqrt ((n : ℝ) ^ 2 + 1) + (n : ℝ))) 0 =
          Real.pi /
            (Real.sqrt ((n : ℝ) ^ 2 + 1) + (n : ℝ)) := by
        rw [Real.dist_eq, sub_zero, abs_of_pos hargpos]
      _ ≤ Real.pi / (n : ℝ) := hquot_le
      _ < ε := hfinal
  have hsin :
      Filter.Tendsto
        (fun n : ℕ => Real.sin
          (Real.pi /
            (Real.sqrt ((n : ℝ) ^ 2 + 1) + (n : ℝ))))
        Filter.atTop (nhds 0) := by
    simpa using
      (Filter.Tendsto.comp Real.continuous_sin.continuousAt harg)
  rw [Metric.tendsto_atTop] at hsin ⊢
  intro ε hε
  obtain ⟨N, hN⟩ := hsin ε hε
  refine ⟨N, ?_⟩
  intro n hn
  have hs := hN n hn
  by_cases h : Even n <;>
    simpa [rationalized, paritySign, h, Real.dist_eq] using hs

/-- Exercise 604, gap 4. -/
theorem gap4 : Filter.Tendsto seq Filter.atTop (nhds 0) := by
  exact (gap1 0).2 ((gap2 0).2 gap3)

end

end ProofGap.Exercise604
