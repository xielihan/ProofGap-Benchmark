import ProofGapLean.Prelude.Sequences
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp

namespace ProofGap.Exercise391

noncomputable section

def f (x : ℝ) : ℝ := x + 1 / x
def rangeOnPositive : Set ℝ :=
  {y | ∃ x ∈ Set.Ioi (0 : ℝ), y = f x}

/-- Source: `proof_gap/exercise_391/1.txt`; restore the positive domain. -/
theorem gap1 : ∀ x : ℝ, 0 < x → 2 ≤ x + 1 / x := by
  intro x hx
  have hquad : 2 * x ≤ x ^ 2 + 1 := by
    nlinarith [sq_nonneg (x - 1)]
  calc
    2 ≤ (x ^ 2 + 1) / x := (le_div_iff₀ hx).2 hquad
    _ = x + 1 / x := by
      field_simp [ne_of_gt hx]

/-- Source: `proof_gap/exercise_391/2.txt`. -/
theorem gap2 : sInf rangeOnPositive = f 1 := by
  have hone : f 1 ∈ rangeOnPositive := by
    refine ⟨1, ?_, rfl⟩
    norm_num
  have hlower : ∀ y ∈ rangeOnPositive, f 1 ≤ y := by
    intro y hy
    rcases hy with ⟨x, hx, rfl⟩
    have hfx : 2 ≤ f x := by
      change 2 ≤ x + 1 / x
      exact gap1 x hx
    calc
      f 1 = 2 := by norm_num [f]
      _ ≤ f x := hfx
  have hbdd : BddBelow rangeOnPositive := ⟨f 1, hlower⟩
  exact le_antisymm (csInf_le hbdd hone)
    (le_csInf ⟨f 1, hone⟩ hlower)

/-- Source: `proof_gap/exercise_391/3.txt`. -/
theorem gap3 : f 1 = 2 := by
  norm_num [f]

/-- Source: `proof_gap/exercise_391/4.txt`. -/
theorem gap4 : sInf rangeOnPositive = 2 := by
  calc
    sInf rangeOnPositive = f 1 := gap2
    _ = 2 := gap3

/-- Source: `proof_gap/exercise_391/5.txt`. -/
theorem gap5 : Filter.Tendsto f Filter.atTop Filter.atTop := by
  refine Filter.tendsto_atTop.2 ?_
  intro b
  refine Filter.eventually_atTop.2 ⟨max b 1, ?_⟩
  intro x hx
  have hbx : b ≤ x := le_trans (le_max_left b 1) hx
  have hxpos : 0 < x :=
    lt_of_lt_of_le (by norm_num) (le_trans (le_max_right b 1) hx)
  change b ≤ x + 1 / x
  exact hbx.trans
    (le_add_of_nonneg_right (le_of_lt (one_div_pos.mpr hxpos)))

/-- Source: `proof_gap/exercise_391/6.txt`; the extended value `+∞` is represented by unboundedness above. -/
theorem gap6 : ¬BddAbove rangeOnPositive := by
  intro h
  rcases h with ⟨M, hM⟩
  let x : ℝ := max (M + 1) 1
  have hxone : (1 : ℝ) ≤ x := by
    dsimp [x]
    exact le_max_right _ _
  have hx : 0 < x := lt_of_lt_of_le zero_lt_one hxone
  have hMx : M < x := by
    dsimp [x]
    exact lt_of_lt_of_le (by linarith) (le_max_left _ _)
  have hmem : f x ∈ rangeOnPositive := ⟨x, hx, rfl⟩
  have hupper : f x ≤ M := hM hmem
  have hxle : x ≤ f x := by
    rw [f]
    exact le_add_of_nonneg_right (le_of_lt (one_div_pos.mpr hx))
  exact (not_lt_of_ge hupper) (hMx.trans_le hxle)

end

end ProofGap.Exercise391
