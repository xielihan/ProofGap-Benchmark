import ProofGapLean.Prelude.Sequences

open Filter Topology

namespace ProofGap.Exercise89

/-- Exercise 89, gap 1. -/
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

/-- Exercise 89, gap 2; p must be a subsequence index. -/
theorem gap2 :
    ∀ p : ℕ → ℕ, StrictMono p →
      Tendsto p atTop atTop := by
  intro p hp
  exact hp.tendsto_atTop

/-- Exercise 89, gap 3; remove ε and put N before its cutoff. -/
theorem gap3 :
    ∀ p : ℕ → ℕ, StrictMono p →
      ∀ N : ℕ, ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k → N < p k := by
  intro p hp N
  have hev : ∀ᶠ k : ℕ in atTop, N + 1 ≤ p k :=
    tendsto_atTop.1 (gap2 p hp) (N + 1)
  rcases eventually_atTop.1 hev with ⟨k₀, hk₀⟩
  exact ⟨k₀, fun k hk => by
    have := hk₀ k (by omega)
    omega⟩

/-- Exercise 89, gap 4; k₀ depends on ε. -/
theorem gap4
    (x : ℕ → ℝ) (a : ℝ) (p : ℕ → ℕ)
    (hx : Tendsto x atTop (𝓝 a))
    (hp : StrictMono p) :
    ∀ ε : ℝ, 0 < ε →
      ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k → |x (p k) - a| < ε := by
  intro ε hε
  rcases gap1 x a hx ε hε with ⟨N, hN⟩
  rcases gap3 p hp N with ⟨k₀, hk₀⟩
  exact ⟨k₀, fun k hk => hN (p k) (hk₀ k hk)⟩

/-- Exercise 89, gap 5. -/
theorem gap5
    (x : ℕ → ℝ) (a : ℝ) (p : ℕ → ℕ)
    (hx : Tendsto x atTop (𝓝 a))
    (hp : StrictMono p) :
    Tendsto (x ∘ p) atTop (𝓝 a) := by
  exact hx.comp (gap2 p hp)

/-- Exercise 89, gap 6; equality of limits is a common Tendsto value. -/
theorem gap6
    (x : ℕ → ℝ) (a : ℝ) (p : ℕ → ℕ)
    (hx : Tendsto x atTop (𝓝 a))
    (hp : StrictMono p) :
    Tendsto (x ∘ p) atTop (𝓝 a) ∧ Tendsto x atTop (𝓝 a) := by
  exact ⟨gap5 x a p hx hp, hx⟩

/-- Exercise 89, gap 7. -/
theorem gap7
    (x : ℕ → ℝ) (a : ℝ)
    (hx : Tendsto x atTop (𝓝 a)) :
    Tendsto x atTop (𝓝 a) := by
  exact hx

/-- Exercise 89, gap 8; p must be a subsequence index. -/
theorem gap8
    (x : ℕ → ℝ) (a : ℝ)
    (hx : Tendsto x atTop (𝓝 a)) :
    ∀ p : ℕ → ℕ, StrictMono p →
      Tendsto (x ∘ p) atTop (𝓝 a) := by
  intro p hp
  exact gap5 x a p hx hp

/-- Exercise 89, gap 9. -/
theorem gap9
    (x : ℕ → ℝ) (a : ℝ) (p : ℕ → ℕ)
    (hx : Tendsto x atTop (𝓝 a))
    (hp : StrictMono p) :
    (∃ l : ℝ, Tendsto (x ∘ p) atTop (𝓝 l)) ∧
      Tendsto (x ∘ p) atTop (𝓝 a) ∧ Tendsto x atTop (𝓝 a) := by
  have hsub := gap5 x a p hx hp
  exact ⟨⟨a, hsub⟩, hsub, hx⟩

end ProofGap.Exercise89
