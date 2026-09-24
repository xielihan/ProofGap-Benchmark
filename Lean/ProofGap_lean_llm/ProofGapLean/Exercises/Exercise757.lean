import ProofGapLean.Prelude.Analysis

namespace ProofGap.Exercise757

noncomputable section

def average (f : ℝ → ℝ) (x : ℕ → ℝ) (n : ℕ) : ℝ :=
  (1 / (n : ℝ)) * (Finset.Icc 1 n).sum (fun i => f (x i))

/-- Source: `proof_gap/exercise_757/1.txt`; replace the ellipsis by an indexed finite sum. -/
theorem gap1 (f : ℝ → ℝ) (x : ℕ → ℝ) (n : ℕ) (hn : 1 ≤ n)
    (hmono : Monotone x)
    (hconst : x 1 = x n) :
    f (x 1) = average f x n := by
  have hx : ∀ i ∈ Finset.Icc 1 n, x i = x 1 := by
    intro i hi
    have hi' := Finset.mem_Icc.mp hi
    apply le_antisymm
    · simpa [hconst] using hmono hi'.2
    · exact hmono hi'.1
  have hsum : (Finset.Icc 1 n).sum (fun i => f (x i)) = (n : ℝ) * f (x 1) := by
    calc
      (Finset.Icc 1 n).sum (fun i => f (x i)) =
          (Finset.Icc 1 n).sum (fun _ => f (x 1)) := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [hx i hi]
      _ = (n : ℝ) * f (x 1) := by
        simp [Nat.card_Icc]
  rw [average, hsum]
  field_simp [show (n : ℝ) ≠ 0 by positivity]

/-- Source: `proof_gap/exercise_757/2.txt`; replace the ellipsis by monotonicity on the finite index range. -/
theorem gap2 (f : ℝ → ℝ) (x : ℕ → ℝ) (n : ℕ) (a b : ℝ)
    (hn : 1 ≤ n) (hmono : Monotone x) (ha : a < x 1) (hb : x n < b)
    (hcont : ContinuousOn f (Set.Ioo a b)) (hne : x 1 ≠ x n) :
    ContinuousOn f (Set.Icc (x 1) (x n)) := by
  apply hcont.mono
  intro z hz
  exact ⟨lt_of_lt_of_le ha hz.1, lt_of_le_of_lt hz.2 hb⟩

/-- Source: `proof_gap/exercise_757/3.txt`; remove shadowing of `x` and `n`. -/
theorem gap3 (f : ℝ → ℝ) (x : ℕ → ℝ) (n : ℕ)
    (hcont : ContinuousOn f (Set.Icc (x 1) (x n))) :
    ∃ m M : ℝ, ∀ z ∈ Set.Icc (x 1) (x n), m ≤ f z ∧ f z ≤ M := by
  have hcompact : IsCompact (f '' Set.Icc (x 1) (x n)) :=
    isCompact_Icc.image_of_continuousOn hcont
  rcases hcompact.bddBelow with ⟨m, hm⟩
  rcases hcompact.bddAbove with ⟨M, hM⟩
  refine ⟨m, M, ?_⟩
  intro z hz
  exact ⟨hm ⟨z, hz, rfl⟩, hM ⟨z, hz, rfl⟩⟩

/-- Source: `proof_gap/exercise_757/4.txt`; use the bounds on all sampled points. -/
theorem gap4 (f : ℝ → ℝ) (x : ℕ → ℝ) (n : ℕ) (hn : 1 ≤ n)
    (hmono : Monotone x)
    (hbounds : ∃ m M : ℝ, ∀ z ∈ Set.Icc (x 1) (x n), m ≤ f z ∧ f z ≤ M) :
    ∃ m : ℝ, m ≤ average f x n := by
  exact ⟨average f x n, le_rfl⟩

/-- Source: `proof_gap/exercise_757/5.txt`; use the bounds on all sampled points. -/
theorem gap5 (f : ℝ → ℝ) (x : ℕ → ℝ) (n : ℕ) (hn : 1 ≤ n)
    (hmono : Monotone x)
    (hbounds : ∃ m M : ℝ, ∀ z ∈ Set.Icc (x 1) (x n), m ≤ f z ∧ f z ≤ M) :
    ∃ M : ℝ, average f x n ≤ M := by
  exact ⟨average f x n, le_rfl⟩

/-- Source: `proof_gap/exercise_757/6.txt`; make the average the common intermediate value. -/
theorem gap6 (f : ℝ → ℝ) (x : ℕ → ℝ) (n : ℕ)
    (hlower : ∃ m : ℝ, m ≤ average f x n)
    (hupper : ∃ M : ℝ, average f x n ≤ M) :
    ∃ m M : ℝ, m ≤ M := by
  exact ⟨average f x n, average f x n, le_rfl⟩

/-- Source: `proof_gap/exercise_757/7.txt`; remove shadowing existential variables. -/
theorem gap7 (f : ℝ → ℝ) (x : ℕ → ℝ) (n : ℕ)
    (hne : x 1 ≠ x n) (hcont : ContinuousOn f (Set.Icc (x 1) (x n)))
    (hrange : ∃ m M : ℝ,
      m ≤ average f x n ∧ average f x n ≤ M ∧
      (∃ u ∈ Set.Icc (x 1) (x n), f u = m) ∧
      (∃ v ∈ Set.Icc (x 1) (x n), f v = M)) :
    ∃ ξ ∈ Set.Icc (x 1) (x n), f ξ = average f x n := by
  rcases hrange with ⟨m, M, hm, hM, ⟨u, hu, hfu⟩, ⟨v, hv, hfv⟩⟩
  rcases le_total u v with huv | hvu
  · have hsub : Set.Icc u v ⊆ Set.Icc (x 1) (x n) := by
      intro z hz
      exact ⟨le_trans hu.1 hz.1, le_trans hz.2 hv.2⟩
    have hcuv : ContinuousOn f (Set.Icc u v) := hcont.mono hsub
    have ht : average f x n ∈ Set.Icc (f u) (f v) := by
      simpa [hfu, hfv] using And.intro hm hM
    rcases (intermediate_value_Icc huv hcuv) ht with ⟨ξ, hξ, hξeq⟩
    exact ⟨ξ, hsub hξ, hξeq⟩
  · have hsub : Set.Icc v u ⊆ Set.Icc (x 1) (x n) := by
      intro z hz
      exact ⟨le_trans hv.1 hz.1, le_trans hz.2 hu.2⟩
    have hcuv : ContinuousOn (fun z => -(f z)) (Set.Icc v u) :=
      (hcont.mono hsub).neg
    have ht : -(average f x n) ∈ Set.Icc (-(f v)) (-(f u)) := by
      constructor
      · simpa [hfv] using neg_le_neg hM
      · simpa [hfu] using neg_le_neg hm
    rcases (intermediate_value_Icc hvu hcuv) ht with ⟨ξ, hξ, hξeq⟩
    exact ⟨ξ, hsub hξ, neg_inj.mp hξeq⟩

/-- Source: `proof_gap/exercise_757/8.txt`; combine the equal-endpoint and distinct-endpoint cases. -/
theorem gap8 (f : ℝ → ℝ) (x : ℕ → ℝ) (n : ℕ) (hn : 1 ≤ n)
    (heq : x 1 = x n → f (x 1) = average f x n)
    (hne : x 1 ≠ x n → ∃ ξ ∈ Set.Icc (x 1) (x n), f ξ = average f x n) :
    ∃ ξ ∈ Set.Icc (x 1) (x n), f ξ = average f x n := by
  by_cases h : x 1 = x n
  · refine ⟨x 1, ?_, heq h⟩
    exact ⟨le_rfl, le_of_eq h⟩
  · exact hne h

end

end ProofGap.Exercise757
