import ProofGapLean.Prelude.Sequences

open Filter Topology

namespace ProofGap.Exercise91

/-- Exercise 91, gap 1. -/
theorem gap1
    (x : ℕ → ℝ) (a : ℝ)
    (hx : Tendsto x atTop (𝓝 a)) :
    ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, ∀ n : ℕ, N < n → |x n - a| < ε := by
  intro ε hε
  have hev : ∀ᶠ n : ℕ in atTop, |x n - a| < ε := by
    have hball : Metric.ball a ε ∈ 𝓝 a := Metric.ball_mem_nhds a hε
    filter_upwards [hx.eventually hball] with n hn
    simpa [Metric.mem_ball, Real.dist_eq, abs_sub_comm] using hn
  rcases eventually_atTop.1 hev with ⟨N, hN⟩
  exact ⟨N, fun n hn => hN n (by omega)⟩

/-- Exercise 91, gap 2; remove the irrelevant ε binder. -/
theorem gap2
    (x : ℕ → ℝ) (a : ℝ) :
    ∀ n : ℕ, |(|x n| - |a|)| ≤ |x n - a| := by
  intro n
  exact abs_abs_sub_abs_le_abs_sub _ _

/-- Exercise 91, gap 3; N depends on ε. -/
theorem gap3
    (x : ℕ → ℝ) (a : ℝ)
    (hx : Tendsto x atTop (𝓝 a)) :
    ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, ∀ n : ℕ, N < n → |(|x n| - |a|)| < ε := by
  intro ε hε
  rcases gap1 x a hx ε hε with ⟨N, hN⟩
  exact ⟨N, fun n hn => lt_of_le_of_lt (gap2 x a n) (hN n hn)⟩

/-- Exercise 91, gap 4. -/
theorem gap4
    (x : ℕ → ℝ) (a : ℝ)
    (hx : Tendsto x atTop (𝓝 a)) :
    Tendsto (fun n => |x n|) atTop (𝓝 |a|) := by
  exact hx.abs

/-- Exercise 91, gap 5. -/
theorem gap5
    (x : ℕ → ℝ) (a : ℝ)
    (habs : Tendsto (fun n => |x n|) atTop (𝓝 |a|)) :
    Tendsto (fun n => |x n|) atTop (𝓝 |a|) := by
  exact habs

end ProofGap.Exercise91
