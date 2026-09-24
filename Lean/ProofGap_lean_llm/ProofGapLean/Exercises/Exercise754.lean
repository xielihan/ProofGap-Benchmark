import ProofGapLean.Prelude.Sequences

namespace ProofGap.Exercise754

noncomputable section

/-- Source: `proof_gap/exercise_754/1.txt`. -/
theorem gap1 (f : ℝ → ℝ) (x₀ : ℝ) (hf : Monotone f) :
    ∀ x < x₀, f x ≤ f x₀ := by
  intro x hx
  exact hf hx.le

/-- Source: `proof_gap/exercise_754/2.txt`; express the left limit by `nhdsWithin`. -/
theorem gap2 (f : ℝ → ℝ) (x₀ L₁ : ℝ) (hf : Monotone f)
    (hlim : Filter.Tendsto f (nhdsWithin x₀ (Set.Iio x₀)) (nhds L₁)) :
    L₁ ≤ f x₀ := by
  apply le_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin] with x hx
  exact hf hx.le

/-- Source: `proof_gap/exercise_754/3.txt`; bind both one-sided limits. -/
theorem gap3 (f : ℝ → ℝ) (x₀ : ℝ) (hf : Monotone f)
    (hbounded : ∃ C : ℝ, ∀ x, |f x| ≤ C) :
    ∃ L₁ L₂ : ℝ,
      Filter.Tendsto f (nhdsWithin x₀ (Set.Iio x₀)) (nhds L₁) ∧
      Filter.Tendsto f (nhdsWithin x₀ (Set.Ioi x₀)) (nhds L₂) := by
  rcases hbounded with ⟨C, hC⟩
  have hAbove : BddAbove (f '' Set.Iio x₀) := by
    refine ⟨C, ?_⟩
    rintro y ⟨x, hx, rfl⟩
    exact (le_abs_self (f x)).trans (hC x)
  have hBelow : BddBelow (f '' Set.Ioi x₀) := by
    refine ⟨-C, ?_⟩
    rintro y ⟨x, hx, rfl⟩
    exact neg_le_of_abs_le (hC x)
  have hLeftNonempty : (f '' Set.Iio x₀).Nonempty := by
    refine ⟨f (x₀ - 1), x₀ - 1, sub_lt_self x₀ zero_lt_one, rfl⟩
  have hRightNonempty : (f '' Set.Ioi x₀).Nonempty := by
    refine ⟨f (x₀ + 1), x₀ + 1, lt_add_of_pos_right x₀ zero_lt_one, rfl⟩
  refine ⟨sSup (f '' Set.Iio x₀), sInf (f '' Set.Ioi x₀), ?_, ?_⟩
  · refine tendsto_order.2 ⟨?_, ?_⟩
    · intro a ha
      have hex : ∃ z ∈ f '' Set.Iio x₀, a < z := by
        by_contra hn
        have hall : ∀ z ∈ f '' Set.Iio x₀, z ≤ a := by
          intro z hz
          exact le_of_not_gt (fun hza => hn ⟨z, hz, hza⟩)
        exact (not_le_of_gt ha) (csSup_le hLeftNonempty hall)
      rcases hex with ⟨z, ⟨y, hy, rfl⟩, hay⟩
      filter_upwards [mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hy)] with x hx
      exact hay.trans_le (hf hx.le)
    · intro b hb
      filter_upwards [self_mem_nhdsWithin] with x hx
      exact (le_csSup hAbove ⟨x, hx, rfl⟩).trans_lt hb
  · refine tendsto_order.2 ⟨?_, ?_⟩
    · intro a ha
      filter_upwards [self_mem_nhdsWithin] with x hx
      exact ha.trans_le (csInf_le hBelow ⟨x, hx, rfl⟩)
    · intro b hb
      have hex : ∃ z ∈ f '' Set.Ioi x₀, z < b := by
        by_contra hn
        have hall : ∀ z ∈ f '' Set.Ioi x₀, b ≤ z := by
          intro z hz
          exact le_of_not_gt (fun hzb => hn ⟨z, hz, hzb⟩)
        exact (not_le_of_gt hb) (le_csInf hRightNonempty hall)
      rcases hex with ⟨z, ⟨y, hy, rfl⟩, hfy⟩
      filter_upwards [mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hy)] with x hx
      exact (hf hx.le).trans_lt hfy

/-- Source: `proof_gap/exercise_754/4.txt`. -/
theorem gap4 (f : ℝ → ℝ) (x₀ : ℝ)
    (hlim : ∃ L₁ L₂ : ℝ,
      Filter.Tendsto f (nhdsWithin x₀ (Set.Iio x₀)) (nhds L₁) ∧
      Filter.Tendsto f (nhdsWithin x₀ (Set.Ioi x₀)) (nhds L₂)) :
    ∃ L₁ L₂ : ℝ,
      Filter.Tendsto f (nhdsWithin x₀ (Set.Iio x₀)) (nhds L₁) ∧
      Filter.Tendsto f (nhdsWithin x₀ (Set.Ioi x₀)) (nhds L₂) := by
  exact hlim

end

end ProofGap.Exercise754
