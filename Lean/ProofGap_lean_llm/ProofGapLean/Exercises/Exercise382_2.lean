import ProofGapLean.Prelude.Sequences

namespace ProofGap.Exercise382_2

noncomputable section

def BoundedOn (f : ℝ → ℝ) (s : Set ℝ) : Prop :=
  ∃ M : ℝ, ∀ x ∈ s, |f x| ≤ M

def LocallyBoundedOnClosed (f : ℝ → ℝ) (a b : ℝ) : Prop :=
  ∀ x₀ ∈ Set.Icc a b, ∃ δ : ℝ, 0 < δ ∧
    BoundedOn f (Set.Ioo (x₀ - δ) (x₀ + δ) ∩ Set.Icc a b)

/-- Source: `proof_gap/exercise_382_2/1.txt`; use absolute values, since unboundedness may be above or below. -/
theorem gap1 (f : ℝ → ℝ) (a b : ℝ)
    (hnot : ¬BoundedOn f (Set.Icc a b)) :
    ∃ u : ℕ → ℝ,
      (∀ n, u n ∈ Set.Icc a b) ∧
        ∀ M : ℝ, ∃ N : ℕ, ∀ n ≥ N, M < |f (u n)| := by
  classical
  have hunbounded :
      ∀ M : ℝ, ∃ x : ℝ, x ∈ Set.Icc a b ∧ M < |f x| := by
    intro M
    by_contra hM
    apply hnot
    refine ⟨M, ?_⟩
    intro x hx
    exact le_of_not_gt (fun hlt => hM ⟨x, hx, hlt⟩)
  choose u hu_mem hu_large using
    fun n : ℕ => hunbounded (n : ℝ)
  refine ⟨u, hu_mem, ?_⟩
  intro M
  obtain ⟨N, hMN⟩ := exists_nat_gt M
  refine ⟨N, ?_⟩
  intro n hn
  calc
    M < (N : ℝ) := hMN
    _ ≤ (n : ℝ) := (Nat.cast_le).2 hn
    _ < |f (u n)| := hu_large n

/-- Source: `proof_gap/exercise_382_2/2.txt`; retain one sequence and one convergent subsequence on the fixed interval. -/
theorem gap2 (f : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b)
    (hnot : ¬BoundedOn f (Set.Icc a b)) :
    ∃ u : ℕ → ℝ, ∃ p : ℕ → ℕ, ∃ x₀ ∈ Set.Icc a b,
      StrictMono p ∧
        (∀ n, u n ∈ Set.Icc a b) ∧
          Filter.Tendsto (fun k => u (p k)) Filter.atTop (nhds x₀) := by
  classical
  obtain ⟨u, hu, hlarge⟩ := gap1 f a b hnot
  obtain ⟨x₀, hx₀, p, hp, ht⟩ :=
    isCompact_Icc.isSeqCompact hu
  refine ⟨u, p, x₀, hx₀, hp, hu, ?_⟩
  simpa only [Function.comp_apply] using ht

/-- Source: `proof_gap/exercise_382_2/3.txt`; keep `a,b` fixed instead of rebinding them under the existential. -/
theorem gap3 (f : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b)
    (hlocal : LocallyBoundedOnClosed f a b)
    (hnot : ¬BoundedOn f (Set.Icc a b)) :
    ∃ x₀ ∈ Set.Icc a b, ∀ δ > 0,
      ¬BoundedOn f (Set.Ioo (x₀ - δ) (x₀ + δ) ∩ Set.Icc a b) := by
  classical
  obtain ⟨u, hu, hlarge⟩ := gap1 f a b hnot
  obtain ⟨x₀, hx₀, p, hp, ht'⟩ :=
    isCompact_Icc.isSeqCompact hu
  have ht :
      Filter.Tendsto (fun k => u (p k)) Filter.atTop (nhds x₀) := by
    simpa only [Function.comp_apply] using ht'
  refine ⟨x₀, hx₀, ?_⟩
  intro δ hδ hbounded
  obtain ⟨M, hM⟩ := hbounded
  obtain ⟨N, hN⟩ := hlarge M
  have hnear :
      ∀ᶠ k in Filter.atTop,
        u (p k) ∈ Set.Ioo (x₀ - δ) (x₀ + δ) :=
    ht.eventually
      (Ioo_mem_nhds
        (sub_lt_self x₀ hδ)
        (lt_add_of_pos_right x₀ hδ))
  obtain ⟨K, hK⟩ := Filter.eventually_atTop.1 hnear
  let k : ℕ := max K N
  have hKk : K ≤ k := le_max_left K N
  have hNk : N ≤ k := le_max_right K N
  have hk_near : u (p k) ∈ Set.Ioo (x₀ - δ) (x₀ + δ) :=
    hK k hKk
  have hNpk : N ≤ p k :=
    hNk.trans (hp.id_le k)
  have hupper : |f (u (p k))| ≤ M :=
    hM (u (p k)) ⟨hk_near, hu (p k)⟩
  have hlower : M < |f (u (p k))| := hN (p k) hNpk
  exact (not_lt_of_ge hupper) hlower

/-- Source: `proof_gap/exercise_382_2/4.txt`. -/
theorem gap4 (f : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b)
    (hlocal : LocallyBoundedOnClosed f a b) :
    ¬BoundedOn f (Set.Icc a b) → False := by
  intro hnot
  obtain ⟨x₀, hx₀, hbad⟩ :=
    gap3 f a b hab hlocal hnot
  obtain ⟨δ, hδ, hbounded⟩ := hlocal x₀ hx₀
  exact hbad δ hδ hbounded

/-- Source: `proof_gap/exercise_382_2/5.txt`. -/
theorem gap5 (f : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b)
    (hlocal : LocallyBoundedOnClosed f a b) :
    BoundedOn f (Set.Icc a b) := by
  exact Classical.byContradiction (gap4 f a b hab hlocal)

end

end ProofGap.Exercise382_2
