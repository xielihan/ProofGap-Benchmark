import ProofGapLean.Prelude.Analysis
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise773

noncomputable section

def y (x : ℝ) : ℝ := 1 + Real.sin x

theorem gap1 (x : ℝ) (hx : x ∈ Set.Ioo 0 (2 * Real.pi)) : -1 ≤ Real.sin x := by
  exact Real.neg_one_le_sin x
theorem gap2 (x : ℝ) (hx : x ∈ Set.Ioo 0 (2 * Real.pi)) : Real.sin x ≤ 1 := by
  exact Real.sin_le_one x
theorem gap3 (x : ℝ) (hx : x ∈ Set.Ioo 0 (2 * Real.pi)) : (-1 : ℝ) ≤ 1 := by
  linarith
theorem gap4 (x : ℝ) (hx : x ∈ Set.Ioo 0 (2 * Real.pi)) : 0 ≤ y x := by
  unfold y
  linarith [gap1 x hx]
theorem gap5 (x : ℝ) (hx : x ∈ Set.Ioo 0 (2 * Real.pi)) : y x ≤ 2 := by
  unfold y
  linarith [gap2 x hx]
theorem gap6 (x : ℝ) (hx : x ∈ Set.Ioo 0 (2 * Real.pi)) : (0 : ℝ) ≤ 2 := by
  linarith
theorem gap7 : y (Real.pi / 2) = 2 := by
  unfold y
  rw [Real.sin_pi_div_two]
  ring
theorem gap8 : y (3 * Real.pi / 2) = 0 := by
  unfold y
  rw [show 3 * Real.pi / 2 = Real.pi / 2 + Real.pi by ring]
  rw [Real.sin_add, Real.sin_pi_div_two, Real.cos_pi, Real.sin_pi]
  ring
theorem gap9 : ContinuousOn y (Set.Icc (Real.pi / 2) (3 * Real.pi / 2)) := by
  exact (continuous_const.add Real.continuous_sin).continuousOn
theorem gap10 (v : ℝ) (hv : v ∈ Set.Icc 0 2) :
    ∃ x ∈ Set.Icc (Real.pi / 2) (3 * Real.pi / 2), v = y x := by
  have hab : Real.pi / 2 ≤ 3 * Real.pi / 2 := by
    linarith [Real.pi_pos]
  have hv' : v ∈ Set.Icc (y (3 * Real.pi / 2)) (y (Real.pi / 2)) := by
    simpa only [gap7, gap8] using hv
  rcases intermediate_value_Icc' (f := y) hab gap9 hv' with ⟨x, hx, hxy⟩
  exact ⟨x, hx, hxy.symm⟩
theorem gap11 : {v | ∃ x ∈ Set.Ioo 0 (2 * Real.pi), v = y x} = Set.Icc 0 2 := by
  ext v
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨gap4 x hx, gap5 x hx⟩
  · intro hv
    rcases gap10 v hv with ⟨x, hx, hvx⟩
    refine ⟨x, ?_, hvx⟩
    constructor
    · linarith [hx.1, Real.pi_pos]
    · linarith [hx.2, Real.pi_pos]
theorem gap12 : {v | ∃ x ∈ Set.Ioo 0 (2 * Real.pi), v = y x} = Set.Icc 0 2 := by
  exact gap11

end
end ProofGap.Exercise773
