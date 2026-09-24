import ProofGapLean.Prelude.Discrete
import Mathlib.Tactic.Linarith

namespace ProofGap.Exercise396

noncomputable section

def f (x : ℝ) : ℝ := x - Int.floor x
def rangeOnUnit : Set ℝ :=
  {y | ∃ x ∈ Set.Icc (0 : ℝ) 1, y = f x}

/-- Exercise 396, gap 1. -/
theorem gap1 : sInf rangeOnUnit = 0 := by
  have hbelow : BddBelow rangeOnUnit := by
    refine ⟨0, ?_⟩
    intro y hy
    rcases hy with ⟨x, hx, rfl⟩
    exact sub_nonneg.mpr (Int.floor_le x)
  have hzero : 0 ∈ rangeOnUnit := by
    change ∃ x ∈ Set.Icc (0 : ℝ) 1, 0 = f x
    exact ⟨0, ⟨le_rfl, zero_le_one⟩, by simp [f]⟩
  apply le_antisymm
  · exact csInf_le hbelow hzero
  · apply le_csInf
    · exact ⟨0, hzero⟩
    · intro y hy
      rcases hy with ⟨x, hx, rfl⟩
      exact sub_nonneg.mpr (Int.floor_le x)

/-- Exercise 396, gap 2; `1` is the supremum but is not attained. -/
theorem gap2 : sSup rangeOnUnit = 1 := by
  have hzero : 0 ∈ rangeOnUnit := by
    change ∃ x ∈ Set.Icc (0 : ℝ) 1, 0 = f x
    exact ⟨0, ⟨le_rfl, zero_le_one⟩, by simp [f]⟩
  have hne : rangeOnUnit.Nonempty := ⟨0, hzero⟩
  have hub : BddAbove rangeOnUnit := by
    refine ⟨1, ?_⟩
    intro y hy
    rcases hy with ⟨x, hx, rfl⟩
    apply le_of_lt
    rw [f, sub_lt_iff_lt_add]
    simpa [add_comm] using Int.lt_floor_add_one x
  apply le_antisymm
  · apply csSup_le hne
    intro y hy
    rcases hy with ⟨x, hx, rfl⟩
    apply le_of_lt
    rw [f, sub_lt_iff_lt_add]
    simpa [add_comm] using Int.lt_floor_add_one x
  · by_contra h
    have hsup_lt : sSup rangeOnUnit < 1 := lt_of_not_ge h
    have hzero_le_sup : 0 ≤ sSup rangeOnUnit := le_csSup hub hzero
    let x : ℝ := (sSup rangeOnUnit + 1) / 2
    have hx0 : 0 ≤ x := by
      dsimp [x]
      linarith
    have hxlt : x < 1 := by
      dsimp [x]
      linarith
    have hfloor : Int.floor x = 0 := by
      rw [Int.floor_eq_iff]
      constructor
      · simpa using hx0
      · simpa using hxlt
    have hxmem : x ∈ rangeOnUnit := by
      change ∃ y ∈ Set.Icc (0 : ℝ) 1, x = f y
      refine ⟨x, ⟨hx0, le_of_lt hxlt⟩, ?_⟩
      simp [f, hfloor]
    have hx_le_sup : x ≤ sSup rangeOnUnit := le_csSup hub hxmem
    dsimp [x] at hx_le_sup
    linarith

end

end ProofGap.Exercise396
