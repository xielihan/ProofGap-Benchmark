import ProofGapLean.Prelude.Sequences
import Mathlib.Tactic.Linarith

namespace ProofGap.Exercise745

noncomputable section

def IsRational (x : ℝ) : Prop := ∃ q : ℚ, (q : ℝ) = x

def folded (u : ℝ) : ℝ := if 0 < u ∧ u ≤ 1 then u else 2 - u

noncomputable def selector (x : ℝ) : ℝ := by
  classical
  exact if IsRational x then x else 2 - x

/-- Source: `proof_gap/exercise_745/1.txt`; repair the implication scope. -/
theorem gap1 (x : ℝ) : IsRational x → ∃ u : ℝ, u = x := by
  intro _
  exact ⟨x, rfl⟩

/-- Source: `proof_gap/exercise_745/2.txt`; repair the implication scope. -/
theorem gap2 (x : ℝ) (hx : 0 < x) : IsRational x → ∃ u : ℝ, 0 < u := by
  intro _
  exact ⟨x, hx⟩

/-- Source: `proof_gap/exercise_745/3.txt`; repair the implication scope. -/
theorem gap3 (x : ℝ) (hx : x < 1) : IsRational x → ∃ u : ℝ, u < 1 := by
  intro _
  exact ⟨x, hx⟩

/-- Source: `proof_gap/exercise_745/4.txt`; use the intended witness `u=x`. -/
theorem gap4 (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1) :
    IsRational x → ∃ u : ℝ, u = x ∧ folded u = x := by
  intro _
  refine ⟨x, rfl, ?_⟩
  simp [folded, hx0, le_of_lt hx1]

/-- Source: `proof_gap/exercise_745/5.txt`; repair the implication scope. -/
theorem gap5 (x : ℝ) : ¬ IsRational x → ∃ u : ℝ, u = 2 - x := by
  intro _
  exact ⟨2 - x, rfl⟩

/-- Source: `proof_gap/exercise_745/6.txt`; use the intended witness `u=2-x`. -/
theorem gap6 (x : ℝ) (hx : x < 1) :
    ¬ IsRational x → ∃ u : ℝ, u = 2 - x ∧ 1 < u := by
  intro _
  refine ⟨2 - x, rfl, ?_⟩
  linarith

/-- Source: `proof_gap/exercise_745/7.txt`; use the intended witness `u=2-x`. -/
theorem gap7 (x : ℝ) (hx : 0 < x) :
    ¬ IsRational x → ∃ u : ℝ, u = 2 - x ∧ u < 2 := by
  intro _
  refine ⟨2 - x, rfl, ?_⟩
  linarith

/-- Source: `proof_gap/exercise_745/8.txt`; use the intended witness `u=2-x`. -/
theorem gap8 (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1) :
    ¬ IsRational x → ∃ u : ℝ, u = 2 - x ∧ folded u = 2 - u := by
  intro _
  refine ⟨2 - x, rfl, ?_⟩
  have hu : ¬ (0 < 2 - x ∧ 2 - x ≤ 1) := by
    intro h
    linarith [h.2]
  unfold folded
  rw [if_neg hu]

/-- Source: `proof_gap/exercise_745/9.txt`; use the intended witness `u=2-x`. -/
theorem gap9 (x : ℝ) :
    ¬ IsRational x → ∃ u : ℝ, u = 2 - x ∧ 2 - u = x := by
  intro _
  refine ⟨2 - x, rfl, ?_⟩
  linarith

/-- Source: `proof_gap/exercise_745/10.txt`; use the intended witness `u=2-x`. -/
theorem gap10 (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1) :
    ¬ IsRational x → ∃ u : ℝ, u = 2 - x ∧ folded u = x := by
  intro h
  rcases gap8 x hx0 hx1 h with ⟨u, hu, hfold⟩
  refine ⟨u, hu, ?_⟩
  calc
    folded u = 2 - u := hfold
    _ = x := by linarith [hu]

/-- Source: `proof_gap/exercise_745/11.txt`. -/
theorem gap11 (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1) :
    folded (selector x) = x := by
  classical
  by_cases h : IsRational x
  · rcases gap4 x hx0 hx1 h with ⟨u, hu, hfold⟩
    simpa [selector, h, hu] using hfold
  · rcases gap10 x hx0 hx1 h with ⟨u, hu, hfold⟩
    simpa [selector, h, hu] using hfold

/-- Source: `proof_gap/exercise_745/12.txt`; retain the source's strict domain `0<x<1`. -/
theorem gap12 : ContinuousOn (folded ∘ selector) (Set.Ioo 0 1) := by
  refine continuous_id.continuousOn.congr ?_
  intro x hx
  simpa only [Function.comp_apply, id_eq] using gap11 x hx.1 hx.2

end

end ProofGap.Exercise745
