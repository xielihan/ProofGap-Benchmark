import ProofGapLean.Prelude.Elementary

namespace ProofGap.Exercise230

noncomputable section

def y (x : ℝ) : ℝ :=
  if x < 1 then x else if x ≤ 4 then x ^ 2 else Real.rpow 2 x

def inverse (t : ℝ) : ℝ :=
  if t < 1 then t else if t ≤ 16 then Real.sqrt t else Real.log t / Real.log 2

/-- Source: `proof_gap/exercise_230/1.txt`; make the inverse a function and bind its argument to y(x). -/
theorem gap1 : ∀ x, inverse (y x) = x := by
  intro x
  by_cases hx : x < 1
  · simp [y, inverse, hx]
  · have hx1 : 1 ≤ x := le_of_not_gt hx
    have hx0 : 0 ≤ x := le_trans (by norm_num) hx1
    by_cases hx4 : x ≤ 4
    · have hlower : 1 ≤ x ^ 2 := by
        nlinarith
      have hupper : x ^ 2 ≤ 16 := by
        nlinarith
      rw [y, if_neg hx, if_pos hx4, inverse,
        if_neg (not_lt_of_ge hlower), if_pos hupper]
      exact Real.sqrt_sq hx0
    · have hx4' : (4 : ℝ) < x := lt_of_not_ge hx4
      have hp : Real.rpow 2 (4 : ℝ) < Real.rpow 2 x :=
        Real.rpow_lt_rpow_of_exponent_lt (by norm_num) hx4'
      have hfour : Real.rpow 2 (4 : ℝ) = 16 := by
        norm_num
      rw [hfour] at hp
      have hone : 1 ≤ Real.rpow 2 x :=
        le_trans (by norm_num) (le_of_lt hp)
      have hnotle : ¬ Real.rpow 2 x ≤ 16 := not_le_of_gt hp
      rw [y, if_neg hx, if_neg hx4, inverse,
        if_neg (not_lt_of_ge hone), if_neg hnotle]
      change Real.log ((2 : ℝ) ^ (x : ℝ)) / Real.log 2 = x
      rw [Real.log_rpow (by norm_num : (0 : ℝ) < 2)]
      field_simp [ne_of_gt (Real.log_pos (by norm_num : (1 : ℝ) < 2))]

end

end ProofGap.Exercise230
