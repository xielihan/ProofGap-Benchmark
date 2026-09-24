import ProofGapLean.Prelude.Elementary

namespace ProofGap.Exercise233_7

noncomputable section

def f (x : ℝ) : ℝ := Real.tan (Real.sqrt x)

/-- Source: `proof_gap/exercise_233_7/1.txt`. -/
theorem gap1 : ¬∃ T : ℝ, 0 < T ∧ Function.Periodic f T := by
  rintro ⟨T, hT, hper⟩
  let x : ℝ := min (T / 2) ((Real.pi / 4) ^ 2)
  have hx_pos : 0 < x := by
    dsimp [x]
    apply lt_min
    · linarith
    · positivity
  have hx_le_halfT : x ≤ T / 2 := by
    dsimp [x]
    exact min_le_left _ _
  have hx_le_cap : x ≤ (Real.pi / 4) ^ 2 := by
    dsimp [x]
    exact min_le_right _ _
  have hx_lt_T : x < T := by
    linarith
  have hneg : x - T ≤ 0 := by
    linarith
  have hzero : f (x - T) = 0 := by
    simp [f, Real.sqrt_eq_zero_of_nonpos hneg]
  have hfx : f x = 0 := by
    calc
      f x = f ((x - T) + T) := by rw [sub_add_cancel]
      _ = f (x - T) := hper (x - T)
      _ = 0 := hzero
  have hsqrt_pos : 0 < Real.sqrt x := Real.sqrt_pos.2 hx_pos
  have hsqrt_sq : (Real.sqrt x) ^ 2 = x :=
    Real.sq_sqrt (le_of_lt hx_pos)
  have hsqrt_le : Real.sqrt x ≤ Real.pi / 4 := by
    nlinarith [Real.sqrt_nonneg x, hsqrt_sq, hx_le_cap, Real.pi_pos]
  have hsqrt_lt : Real.sqrt x < Real.pi / 2 := by
    nlinarith [Real.pi_pos]
  have hfx_pos : 0 < f x := by
    exact Real.tan_pos_of_pos_of_lt_pi_div_two hsqrt_pos hsqrt_lt
  exact (ne_of_gt hfx_pos) hfx

/-- Source: `proof_gap/exercise_233_7/2.txt`. -/
theorem gap2 : {T : ℝ | 0 < T ∧ Function.Periodic f T} = ∅ := by
  apply Set.Subset.antisymm
  · intro T hT
    exact (gap1 ⟨T, hT⟩).elim
  · exact Set.empty_subset _

end

end ProofGap.Exercise233_7
