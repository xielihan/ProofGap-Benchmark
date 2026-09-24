import ProofGapLean.Prelude.Sequences

open Filter Topology

namespace ProofGap.Exercise90

def Convergent (x : ℕ → ℝ) : Prop :=
  ∃ a : ℝ, Tendsto x atTop (𝓝 a)

/-- Exercise 90, gap 1; extract the convergent subsequence. -/
theorem gap1
    (x : ℕ → ℝ)
    (hsub : ∃ a : ℝ, ∃ p : ℕ → ℕ,
      StrictMono p ∧ Tendsto (x ∘ p) atTop (𝓝 a)) :
    ∃ p : ℕ → ℕ, ∃ a : ℝ,
      Monotone x →
      ∀ ε : ℝ, 0 < ε →
        ∃ N : ℕ, ∀ k : ℕ, N < k → |x (p k) - a| < ε := by
  rcases hsub with ⟨a, p, hp, hxp⟩
  refine ⟨p, a, fun _ ε hε => ?_⟩
  have hev : ∀ᶠ k : ℕ in atTop, |x (p k) - a| < ε := by
    have hball : Metric.ball a ε ∈ 𝓝 a := Metric.ball_mem_nhds a hε
    filter_upwards [hxp.eventually hball] with k hk
    simpa [Function.comp_apply, Metric.mem_ball, Real.dist_eq, abs_sub_comm] using hk
  rcases eventually_atTop.1 hev with ⟨N, hN⟩
  exact ⟨N, fun k hk => hN k (by omega)⟩

/-- Exercise 90, gap 2; bracket n between consecutive subsequence indices. -/
theorem gap2
    (p : ℕ → ℕ) (hp : StrictMono p) :
    ∀ N : ℕ, ∃ N' : ℕ, ∀ n : ℕ, N' < n →
      ∃ k : ℕ, N < k ∧ p k ≤ n ∧ n < p (k + 1) := by
  intro N
  refine ⟨p (N + 1), ?_⟩
  intro n hn
  have hex : ∃ j : ℕ, n < p j := by
    have hev : ∀ᶠ j : ℕ in atTop, n + 1 ≤ p j :=
      tendsto_atTop.1 hp.tendsto_atTop (n + 1)
    rcases hev.exists with ⟨j, hj⟩
    exact ⟨j, by omega⟩
  let j := Nat.find hex
  have hj : n < p j := Nat.find_spec hex
  have hjlarge : N + 1 < j := by
    by_contra hnot
    have hjle : j ≤ N + 1 := by omega
    have hpjle : p j ≤ p (N + 1) := hp.monotone hjle
    linarith
  let k := j - 1
  have hkadd : k + 1 = j := by
    dsimp [k]
    omega
  have hkN : N < k := by
    dsimp [k]
    omega
  have hpk : p k ≤ n := by
    by_contra hnot
    have hnk : n < p k := by omega
    have hklt : k < j := by
      rw [← hkadd]
      omega
    exact (Nat.find_min hex hklt) hnk
  exact ⟨k, hkN, hpk, by rwa [hkadd]⟩

/-- Exercise 90, gap 3; k is chosen after n. -/
theorem gap3
    (x : ℕ → ℝ) (p : ℕ → ℕ) (a ε : ℝ)
    (hsub : Tendsto (x ∘ p) atTop (𝓝 a))
    (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n k : ℕ, N < k → |x (p k) - a| < ε := by
  have hev : ∀ᶠ k : ℕ in atTop, |x (p k) - a| < ε := by
    have hball : Metric.ball a ε ∈ 𝓝 a := Metric.ball_mem_nhds a hε
    filter_upwards [hsub.eventually hball] with k hk
    simpa [Function.comp_apply, Metric.mem_ball, Real.dist_eq, abs_sub_comm] using hk
  rcases eventually_atTop.1 hev with ⟨N, hN⟩
  exact ⟨N, fun n k hk => hN k (by omega)⟩

/-- Exercise 90, gap 4; k+1 remains in the convergent tail. -/
theorem gap4
    (x : ℕ → ℝ) (p : ℕ → ℕ) (a ε : ℝ)
    (hsub : Tendsto (x ∘ p) atTop (𝓝 a))
    (hε : 0 < ε) :
    ∃ N : ℕ, ∀ k : ℕ, N < k → |x (p (k + 1)) - a| < ε := by
  rcases gap3 x p a ε hsub hε with ⟨N, hN⟩
  exact ⟨N, fun k hk => hN k (k + 1) (by omega)⟩

/-- Exercise 90, gap 5. -/
theorem gap5
    (x : ℕ → ℝ) (p : ℕ → ℕ)
    (hmono : Monotone x) :
    ∀ n k : ℕ, p k ≤ n → x (p k) ≤ x n := by
  intro n k h
  exact hmono h

/-- Exercise 90, gap 6. -/
theorem gap6
    (x : ℕ → ℝ) (p : ℕ → ℕ)
    (hmono : Monotone x) :
    ∀ n k : ℕ, n ≤ p (k + 1) → x n ≤ x (p (k + 1)) := by
  intro n k h
  exact hmono h

/-- Exercise 90, gap 7. -/
theorem gap7
    (x : ℕ → ℝ) (p : ℕ → ℕ)
    (hmono : Monotone x) (hp : StrictMono p) :
    ∀ k : ℕ, x (p k) ≤ x (p (k + 1)) := by
  intro k
  exact hmono (hp.monotone (by omega))

/-- Exercise 90, gap 8; the cutoff depends on ε. -/
theorem gap8
    (x : ℕ → ℝ) (a : ℝ)
    (hmono : Monotone x)
    (hsub : ∃ p : ℕ → ℕ, StrictMono p ∧ Tendsto (x ∘ p) atTop (𝓝 a)) :
    Tendsto x atTop (𝓝 a) := by
  rcases hsub with ⟨p, hp, hxp⟩
  apply Metric.tendsto_atTop.2
  intro ε hε
  rcases gap3 x p a ε hxp hε with ⟨K, hK⟩
  rcases gap2 p hp K with ⟨N, hN⟩
  refine ⟨N + 1, ?_⟩
  intro n hn
  rcases hN n (by omega) with ⟨k, hkK, hleft, hright⟩
  have hkclose := hK n k hkK
  have hksclose := hK n (k + 1) (by omega)
  have hxleft := hmono hleft
  have hxright := hmono (le_of_lt hright)
  rw [Real.dist_eq]
  rw [abs_lt] at hkclose hksclose ⊢
  constructor <;> linarith

/-- Exercise 90, gap 9. -/
theorem gap9
    (x : ℕ → ℝ)
    (hmono : Monotone x)
    (hsub : ∃ a : ℝ, ∃ p : ℕ → ℕ,
      StrictMono p ∧ Tendsto (x ∘ p) atTop (𝓝 a)) :
    ∃ a : ℝ, Tendsto x atTop (𝓝 a) := by
  rcases hsub with ⟨a, p, hp, hxp⟩
  exact ⟨a, gap8 x a hmono ⟨p, hp, hxp⟩⟩

/-- Exercise 90, gap 10. -/
theorem gap10
    (x : ℕ → ℝ)
    (hmono : Antitone x)
    (hsub : ∃ a : ℝ, ∃ p : ℕ → ℕ,
      StrictMono p ∧ Tendsto (x ∘ p) atTop (𝓝 a)) :
    Convergent x := by
  rcases hsub with ⟨a, p, hp, hxp⟩
  have hnegmono : Monotone (fun n => -x n) := by
    intro n m hnm
    exact neg_le_neg (hmono hnm)
  have hnegsub :
      Tendsto ((fun n => -x n) ∘ p) atTop (𝓝 (-a)) := by
    exact hxp.neg
  have hneg := gap8 (fun n => -x n) (-a) hnegmono ⟨p, hp, hnegsub⟩
  refine ⟨a, ?_⟩
  simpa using hneg.neg

/-- Exercise 90, gap 11. -/
theorem gap11
    (x : ℕ → ℝ)
    (hmono : Monotone x ∨ Antitone x)
    (hsub : ∃ a : ℝ, ∃ p : ℕ → ℕ,
      StrictMono p ∧ Tendsto (x ∘ p) atTop (𝓝 a)) :
    Convergent x := by
  rcases hmono with hmono | hanti
  · exact gap9 x hmono hsub
  · exact gap10 x hanti hsub

/-- Exercise 90, gap 12. -/
theorem gap12
    (x : ℕ → ℝ)
    (hconv : Convergent x) :
    Convergent x := by
  exact hconv

end ProofGap.Exercise90
