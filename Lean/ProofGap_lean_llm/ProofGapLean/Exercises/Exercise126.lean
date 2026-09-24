import ProofGapLean.Prelude.Sequences

open Filter

namespace ProofGap.Exercise126

private theorem exists_abs_gt_of_not_bounded
    (s : Set ℝ) (hs : ¬ Bornology.IsBounded s) (R : ℝ) :
    ∃ y ∈ s, R < |y| := by
  by_contra h
  push_neg at h
  apply hs
  apply (Metric.isBounded_iff_subset_closedBall 0).2
  refine ⟨R, ?_⟩
  intro y hy
  simpa [Real.dist_eq] using h y hy

private theorem tail_not_bounded
    (x : ℕ → ℝ) (hunbounded : ¬ Bornology.IsBounded (Set.range x))
    (N : ℕ) :
    ¬ Bornology.IsBounded (x '' {n : ℕ | N < n}) := by
  intro htail
  have hfin : Bornology.IsBounded (x '' Set.Iic N) :=
    ((Set.finite_Iic N).image x).isBounded
  apply hunbounded
  apply (htail.union hfin).subset
  rintro y ⟨n, rfl⟩
  by_cases hn : N < n
  · exact Or.inl ⟨n, hn, rfl⟩
  · exact Or.inr ⟨n, Nat.le_of_not_gt hn, rfl⟩

private theorem exists_tail_abs_gt
    (x : ℕ → ℝ) (hunbounded : ¬ Bornology.IsBounded (Set.range x))
    (N : ℕ) (R : ℝ) :
    ∃ j : ℕ, N < j ∧ R < |x j| := by
  rcases exists_abs_gt_of_not_bounded
      (x '' {n : ℕ | N < n}) (tail_not_bounded x hunbounded N) R with
    ⟨y, ⟨j, hj, rfl⟩, hy⟩
  exact ⟨j, hj, hy⟩

/-- Exercise 126, gap 1. -/
theorem gap1
    (x : ℕ → ℝ)
    (hunbounded : ¬ Bornology.IsBounded (Set.range x)) :
    ∃ p : ℕ → ℕ, 0 < p 1 ∧ |x (p 1)| > 1 := by
  rcases exists_tail_abs_gt x hunbounded 0 1 with ⟨j, hj, hlarge⟩
  exact ⟨fun _ => j, hj, hlarge⟩

/-- Exercise 126, gap 2. -/
theorem gap2
    (x : ℕ → ℝ)
    (hunbounded : ¬ Bornology.IsBounded (Set.range x)) :
    ∃ p : ℕ → ℕ, ∀ k : ℕ,
      ¬ Bornology.IsBounded (x '' {n : ℕ | p k < n}) := by
  exact ⟨id, fun k => tail_not_bounded x hunbounded k⟩

/-- Exercise 126, gap 3; remove the rebound p and k. -/
theorem gap3
    (x : ℕ → ℝ) (p : ℕ → ℕ)
    (htail : ∀ k : ℕ,
      ¬ Bornology.IsBounded (x '' {n : ℕ | p k < n})) :
    ∀ k : ℕ, ∃ j : ℕ,
      p k < j ∧ |x j| > (k : ℝ) + 1 := by
  intro k
  rcases exists_abs_gt_of_not_bounded
      (x '' {n : ℕ | p k < n}) (htail k) ((k : ℝ) + 1) with
    ⟨y, ⟨j, hj, rfl⟩, hy⟩
  exact ⟨j, hj, hy⟩

/-- Exercise 126, gap 4. -/
theorem gap4
    (p : ℕ → ℕ)
    (hp : StrictMono p) :
    StrictMono p := by
  exact hp

/-- Exercise 126, gap 5. -/
theorem gap5
    (x : ℕ → ℝ) (p : ℕ → ℕ)
    (hlarge : ∀ k : ℕ, 0 < k → |x (p k)| > k) :
    ∀ k : ℕ, 0 < k → |x (p k)| > k := by
  exact hlarge

/-- Exercise 126, gap 6; only absolute values must tend to +∞. -/
theorem gap6
    (x : ℕ → ℝ) (p : ℕ → ℕ)
    (hlarge : ∀ k : ℕ, 0 < k → |x (p k)| > k) :
    Tendsto (fun k => |x (p k)|) atTop (atTop : Filter ℝ) := by
  apply tendsto_atTop.2
  intro B
  have hcast :
      Tendsto (fun k : ℕ => (k : ℝ)) atTop (atTop : Filter ℝ) :=
    tendsto_natCast_atTop_atTop
  filter_upwards [tendsto_atTop.1 hcast B, eventually_ge_atTop 1] with k hkB hk
  exact hkB.trans (le_of_lt (hlarge k (by omega)))

/-- Exercise 126, gap 7; repair the false signed conclusion. -/
theorem gap7
    (x : ℕ → ℝ)
    (hunbounded : ¬ Bornology.IsBounded (Set.range x)) :
    ∃ p : ℕ → ℕ, StrictMono p ∧
      Tendsto (fun k => |x (p k)|) atTop (atTop : Filter ℝ) := by
  let next : ℕ → ℕ → ℕ := fun k N =>
    Classical.choose (exists_tail_abs_gt x hunbounded N ((k : ℝ) + 1))
  have next_spec (k N : ℕ) :
      N < next k N ∧ (k : ℝ) + 1 < |x (next k N)| :=
    Classical.choose_spec
      (exists_tail_abs_gt x hunbounded N ((k : ℝ) + 1))
  let p : ℕ → ℕ := fun k =>
    Nat.rec 0 (fun k previous => next k previous) k
  have p_succ (k : ℕ) : p (k + 1) = next k (p k) := by
    simp [p]
  have hp : StrictMono p := strictMono_nat_of_lt_succ fun k => by
    rw [p_succ]
    exact (next_spec k (p k)).1
  have hlarge : ∀ k : ℕ, 0 < k → |x (p k)| > k := by
    intro k hk
    obtain ⟨t, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
    rw [p_succ]
    exact_mod_cast (next_spec t (p t)).2
  exact ⟨p, hp, gap6 x p hlarge⟩

end ProofGap.Exercise126
