import ProofGapLean.Prelude.Sequences
import Mathlib.Tactic.Linarith

namespace ProofGap.Exercise745

noncomputable section

def IsRational (x : ℝ) : Prop := ∃ q : ℚ, (q : ℝ) = x

def folded (u : ℝ) : ℝ := if 0 < u ∧ u ≤ 1 then u else 2 - u

noncomputable def selector (x : ℝ) : ℝ := by
  classical
  exact if IsRational x then x else 2 - x

/-- Exercise 745, gap 1; repair the implication scope. -/
theorem gap1 (x : ℝ) : IsRational x → ∃ u : ℝ, u = x := by
  intro _
  exact ⟨x, rfl⟩

/-- Exercise 745, gap 2; repair the implication scope. -/
theorem gap2 (x : ℝ) (hx : 0 < x) : IsRational x → ∃ u : ℝ, 0 < u := by
  intro _
  exact ⟨x, hx⟩

/-- Exercise 745, gap 3; repair the implication scope. -/
theorem gap3 (x : ℝ) (hx : x < 1) : IsRational x → ∃ u : ℝ, u < 1 := by
  intro _
  exact ⟨x, hx⟩

/-- Exercise 745, gap 4; use the intended witness `u=x`. -/
theorem gap4 (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1) :
    IsRational x → ∃ u : ℝ, u = x ∧ folded u = x := by
  intro _
  refine ⟨x, rfl, ?_⟩
  simp [folded, hx0, le_of_lt hx1]

/-- Exercise 745, gap 5; repair the implication scope. -/
theorem gap5 (x : ℝ) : ¬ IsRational x → ∃ u : ℝ, u = 2 - x := by
  intro _
  exact ⟨2 - x, rfl⟩

/-- Exercise 745, gap 6; use the intended witness `u=2-x`. -/
theorem gap6 (x : ℝ) (hx : x < 1) :
    ¬ IsRational x → ∃ u : ℝ, u = 2 - x ∧ 1 < u := by
  intro _
  refine ⟨2 - x, rfl, ?_⟩
  linarith

/-- Exercise 745, gap 7; use the intended witness `u=2-x`. -/
theorem gap7 (x : ℝ) (hx : 0 < x) :
    ¬ IsRational x → ∃ u : ℝ, u = 2 - x ∧ u < 2 := by
  intro _
  refine ⟨2 - x, rfl, ?_⟩
  linarith

/-- Exercise 745, gap 8; use the intended witness `u=2-x`. -/
theorem gap8 (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1) :
    ¬ IsRational x → ∃ u : ℝ, u = 2 - x ∧ folded u = 2 - u := by
  intro _
  refine ⟨2 - x, rfl, ?_⟩
  have hu : ¬ (0 < 2 - x ∧ 2 - x ≤ 1) := by
    intro h
    linarith [h.2]
  unfold folded
  rw [if_neg hu]

/-- Exercise 745, gap 9; use the intended witness `u=2-x`. -/
theorem gap9 (x : ℝ) :
    ¬ IsRational x → ∃ u : ℝ, u = 2 - x ∧ 2 - u = x := by
  intro _
  refine ⟨2 - x, rfl, ?_⟩
  linarith

/-- Exercise 745, gap 10; use the intended witness `u=2-x`. -/
theorem gap10 (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1) :
    ¬ IsRational x → ∃ u : ℝ, u = 2 - x ∧ folded u = x := by
  intro h
  rcases gap8 x hx0 hx1 h with ⟨u, hu, hfold⟩
  refine ⟨u, hu, ?_⟩
  calc
    folded u = 2 - u := hfold
    _ = x := by linarith [hu]

/-- Exercise 745, gap 11. -/
theorem gap11 (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1) :
    folded (selector x) = x := by
  classical
  by_cases h : IsRational x
  · rcases gap4 x hx0 hx1 h with ⟨u, hu, hfold⟩
    simpa [selector, h, hu] using hfold
  · rcases gap10 x hx0 hx1 h with ⟨u, hu, hfold⟩
    simpa [selector, h, hu] using hfold

/-- Exercise 745, gap 12; retain the source's strict domain `0<x<1`. -/
theorem gap12 : ContinuousOn (folded ∘ selector) (Set.Ioo 0 1) := by
  refine continuous_id.continuousOn.congr ?_
  intro x hx
  simpa only [Function.comp_apply, id_eq] using gap11 x hx.1 hx.2

end

end ProofGap.Exercise745
