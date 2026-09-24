import ProofGapLean.Prelude.Sequences

namespace ProofGap.Exercise751

noncomputable section

def BoundedOn (f : ℝ → ℝ) (s : Set ℝ) : Prop :=
  ∃ C : ℝ, ∀ x ∈ s, |f x| ≤ C

/-- Source: `proof_gap/exercise_751/1.txt`; remove shadowing of `a` and `X`. -/
theorem gap1 (f : ℝ → ℝ) (a A : ℝ)
    (hlim : Filter.Tendsto f Filter.atTop (nhds A)) :
    ∃ X > a, ∀ x > X, |f x| < |A| + 1 := by
  have hA_mem : A ∈ Set.Ioo (-(|A| + 1)) (|A| + 1) := by
    constructor
    · exact lt_of_lt_of_le
        (neg_lt_neg (lt_add_of_pos_right |A| zero_lt_one))
        (neg_abs_le A)
    · exact lt_of_le_of_lt (le_abs_self A)
        (lt_add_of_pos_right |A| zero_lt_one)
  have hnhds : Set.Ioo (-(|A| + 1)) (|A| + 1) ∈ nhds A :=
    IsOpen.mem_nhds isOpen_Ioo hA_mem
  have hev : ∀ᶠ x in Filter.atTop,
      f x ∈ Set.Ioo (-(|A| + 1)) (|A| + 1) :=
    hlim.eventually hnhds
  rcases Filter.eventually_atTop.1 hev with ⟨X₀, hX₀⟩
  refine ⟨max a X₀ + 1, ?_, ?_⟩
  · exact lt_of_le_of_lt (le_max_left a X₀)
      (lt_add_of_pos_right (max a X₀) zero_lt_one)
  · intro x hx
    apply (abs_lt).2
    apply hX₀ x
    exact le_of_lt (lt_of_le_of_lt (le_max_right a X₀)
      (lt_trans (lt_add_of_pos_right (max a X₀) zero_lt_one) hx))

/-- Source: `proof_gap/exercise_751/2.txt`. -/
theorem gap2 (f : ℝ → ℝ) (a : ℝ) (hcont : ContinuousOn f (Set.Ici a)) :
    ∀ X, BoundedOn f (Set.Icc a X) := by
  intro X
  by_cases haX : a ≤ X
  · have hf : ContinuousOn f (Set.Icc a X) := by
      apply hcont.mono
      intro x hx
      exact hx.1
    have hb : BddAbove ((fun x : ℝ => |f x|) '' Set.Icc a X) :=
      isCompact_Icc.bddAbove_image hf.abs
    rcases hb with ⟨C, hC⟩
    refine ⟨C, ?_⟩
    intro x hx
    exact hC ⟨x, hx, rfl⟩
  · refine ⟨0, ?_⟩
    intro x hx
    exact (haX (hx.1.trans hx.2)).elim

/-- Source: `proof_gap/exercise_751/3.txt`; bind a fixed compact interval. -/
theorem gap3 (f : ℝ → ℝ) (a X : ℝ) (hbounded : BoundedOn f (Set.Icc a X)) :
    ∃ M₁ : ℝ, ∀ x ∈ Set.Icc a X, |f x| ≤ M₁ := by
  exact hbounded

/-- Source: `proof_gap/exercise_751/4.txt`; bind the cutoff and local bound. -/
theorem gap4 (f : ℝ → ℝ) (a A X M₁ : ℝ)
    (htail : ∀ x > X, |f x| < |A| + 1)
    (hcompact : ∀ x ∈ Set.Icc a X, |f x| < M₁) :
    ∀ x ∈ Set.Ici a, |f x| < max (|A| + 1) M₁ := by
  intro x hxa
  by_cases hx : x ≤ X
  · exact lt_of_lt_of_le (hcompact x ⟨hxa, hx⟩)
      (le_max_right (|A| + 1) M₁)
  · exact lt_of_lt_of_le (htail x (lt_of_not_ge hx))
      (le_max_left (|A| + 1) M₁)

/-- Source: `proof_gap/exercise_751/5.txt`. -/
theorem gap5 (f : ℝ → ℝ) (a M : ℝ)
    (hM : ∀ x ∈ Set.Ici a, |f x| < M) :
    BoundedOn f (Set.Ici a) := by
  refine ⟨M, ?_⟩
  intro x hx
  exact le_of_lt (hM x hx)

/-- Source: `proof_gap/exercise_751/6.txt`. -/
theorem gap6 (f : ℝ → ℝ) (a : ℝ) (hcont : ContinuousOn f (Set.Ici a))
    (hconv : ∃ A, Filter.Tendsto f Filter.atTop (nhds A)) :
    BoundedOn f (Set.Ici a) := by
  rcases hconv with ⟨A, hA⟩
  rcases gap1 f a A hA with ⟨X, hXa, htail⟩
  rcases gap2 f a hcont X with ⟨C, hC⟩
  have hcompact : ∀ x ∈ Set.Icc a X, |f x| < C + 1 := by
    intro x hx
    exact lt_of_le_of_lt (hC x hx)
      (lt_add_of_pos_right C zero_lt_one)
  have hall : ∀ x ∈ Set.Ici a, |f x| < max (|A| + 1) (C + 1) :=
    gap4 f a A X (C + 1) htail hcompact
  exact gap5 f a (max (|A| + 1) (C + 1)) hall

end

end ProofGap.Exercise751
