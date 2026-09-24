import ProofGapLean.Prelude.Discrete
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

namespace ProofGap.Exercise395

noncomputable section

def f (x : ℝ) : ℝ := Int.floor x
def openRange : Set ℤ := {y | ∃ x ∈ Set.Ioo (0 : ℝ) 2, y = f x}
def closedRange : Set ℤ := {y | ∃ x ∈ Set.Icc (0 : ℝ) 2, y = f x}

/-- Exercise 395, gap 1. -/
private lemma int_eq_floor_of_eq_f {y : ℤ} {x : ℝ}
    (h : (y : ℝ) = f x) : y = Int.floor x := by
  have h' := congrArg Int.floor h
  simpa [f] using h'

theorem gap1 : sInf openRange = 0 := by
  have hzero : (0 : ℤ) ∈ openRange := by
    change ∃ x ∈ Set.Ioo (0 : ℝ) 2, (0 : ℤ) = f x
    refine ⟨(1 / 2 : ℝ), by norm_num, ?_⟩
    norm_num [f]
  have hlower : ∀ y ∈ openRange, (0 : ℤ) ≤ y := by
    intro y hy
    change ∃ x ∈ Set.Ioo (0 : ℝ) 2, (y : ℝ) = f x at hy
    rcases hy with ⟨x, hx, hxy⟩
    rw [int_eq_floor_of_eq_f hxy]
    apply (Int.le_floor).2
    simpa using (le_of_lt hx.1)
  apply le_antisymm
  · exact csInf_le ⟨0, hlower⟩ hzero
  · exact le_csInf ⟨0, hzero⟩ hlower

/-- Exercise 395, gap 2. -/
theorem gap2 : sSup openRange = 1 := by
  have hone : (1 : ℤ) ∈ openRange := by
    change ∃ x ∈ Set.Ioo (0 : ℝ) 2, (1 : ℤ) = f x
    refine ⟨(3 / 2 : ℝ), by norm_num, ?_⟩
    norm_num [f]
  have hupper : ∀ y ∈ openRange, y ≤ (1 : ℤ) := by
    intro y hy
    change ∃ x ∈ Set.Ioo (0 : ℝ) 2, (y : ℝ) = f x at hy
    rcases hy with ⟨x, hx, hxy⟩
    rw [int_eq_floor_of_eq_f hxy]
    have hlt : Int.floor x < (2 : ℤ) := (Int.floor_lt).2 hx.2
    omega
  apply le_antisymm
  · exact csSup_le ⟨1, hone⟩ hupper
  · exact le_csSup ⟨1, hupper⟩ hone

/-- Exercise 395, gap 3. -/
theorem gap3 : sInf closedRange = 0 := by
  have hzero : (0 : ℤ) ∈ closedRange := by
    change ∃ x ∈ Set.Icc (0 : ℝ) 2, (0 : ℤ) = f x
    refine ⟨(0 : ℝ), by norm_num, ?_⟩
    norm_num [f]
  have hlower : ∀ y ∈ closedRange, (0 : ℤ) ≤ y := by
    intro y hy
    change ∃ x ∈ Set.Icc (0 : ℝ) 2, (y : ℝ) = f x at hy
    rcases hy with ⟨x, hx, hxy⟩
    rw [int_eq_floor_of_eq_f hxy]
    apply (Int.le_floor).2
    simpa using hx.1
  apply le_antisymm
  · exact csInf_le ⟨0, hlower⟩ hzero
  · exact le_csInf ⟨0, hzero⟩ hlower

/-- Exercise 395, gap 4. -/
theorem gap4 : sSup closedRange = 2 := by
  have htwo : (2 : ℤ) ∈ closedRange := by
    change ∃ x ∈ Set.Icc (0 : ℝ) 2, (2 : ℤ) = f x
    refine ⟨(2 : ℝ), by norm_num, ?_⟩
    norm_num [f]
  have hupper : ∀ y ∈ closedRange, y ≤ (2 : ℤ) := by
    intro y hy
    change ∃ x ∈ Set.Icc (0 : ℝ) 2, (y : ℝ) = f x at hy
    rcases hy with ⟨x, hx, hxy⟩
    rw [int_eq_floor_of_eq_f hxy]
    have hx3 : x < (3 : ℝ) := lt_of_le_of_lt hx.2 (by norm_num)
    have hlt : Int.floor x < (3 : ℤ) := (Int.floor_lt).2 hx3
    omega
  apply le_antisymm
  · exact csSup_le ⟨2, htwo⟩ hupper
  · exact le_csSup ⟨2, hupper⟩ htwo

end

end ProofGap.Exercise395
