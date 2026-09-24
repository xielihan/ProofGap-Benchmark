import ProofGapLean.Prelude.Sequences

open Filter Topology

namespace ProofGap.Exercise93

/-- Source: `proof_gap/exercise_93/1.txt`. -/
theorem gap1
    (x : ℕ → ℝ) (a : ℝ)
    (hx : Tendsto x atTop (𝓝 a)) :
    ∃ N : ℕ, 0 < N ∧ ∀ n : ℕ, N < n → |x n - a| < 1 := by
  have hball : Metric.ball a 1 ∈ 𝓝 a := Metric.ball_mem_nhds a (by norm_num)
  have hev : ∀ᶠ n : ℕ in atTop, |x n - a| < 1 := by
    filter_upwards [hx.eventually hball] with n hn
    simpa [Metric.mem_ball, Real.dist_eq, abs_sub_comm] using hn
  rcases eventually_atTop.1 hev with ⟨N, hN⟩
  exact ⟨N + 1, by omega, fun n hn => hN n (by omega)⟩

/-- Source: `proof_gap/exercise_93/2.txt`; remove the rebound N and unused ε. -/
theorem gap2
    (x : ℕ → ℝ) (a : ℝ)
    (hx : Tendsto x atTop (𝓝 a)) :
    ∃ N : ℕ, ∀ n : ℕ, N < n → |x n| < |a| + 1 := by
  rcases gap1 x a hx with ⟨N, hNpos, hN⟩
  refine ⟨N, ?_⟩
  intro n hn
  have htri : |x n| ≤ |x n - a| + |a| := by
    have := abs_add_le (x n - a) a
    convert this using 1 <;> ring
  linarith [hN n hn]

/-- Source: `proof_gap/exercise_93/3.txt`; spell out the two max bounds on M. -/
theorem gap3
    (x : ℕ → ℝ) (a M : ℝ) (N : ℕ)
    (htail : ∀ n : ℕ, N < n → |x n| < |a| + 1)
    (hfinite : ∀ k : ℕ, k ≤ N → |x k| ≤ M)
    (haM : |a| + 1 ≤ M) :
    ∀ n : ℕ, |x n| ≤ M := by
  intro n
  by_cases hn : n ≤ N
  · exact hfinite n hn
  · exact le_trans (le_of_lt (htail n (by omega))) haM

/-- Source: `proof_gap/exercise_93/4.txt`. -/
theorem gap4
    (x : ℕ → ℝ)
    (hbound : ∃ M : ℝ, ∀ n : ℕ, |x n| ≤ M) :
    Bornology.IsBounded (Set.range x) := by
  rcases hbound with ⟨M, hM⟩
  apply isBounded_iff_bddBelow_bddAbove.mpr
  constructor
  · refine ⟨-M, ?_⟩
    intro y hy
    rcases hy with ⟨n, rfl⟩
    exact (abs_le.mp (hM n)).1
  · refine ⟨M, ?_⟩
    intro y hy
    rcases hy with ⟨n, rfl⟩
    exact (abs_le.mp (hM n)).2

/-- Source: `proof_gap/exercise_93/5.txt`. -/
theorem gap5
    (x : ℕ → ℝ)
    (hbound : Bornology.IsBounded (Set.range x)) :
    Bornology.IsBounded (Set.range x) := by
  exact hbound

end ProofGap.Exercise93
