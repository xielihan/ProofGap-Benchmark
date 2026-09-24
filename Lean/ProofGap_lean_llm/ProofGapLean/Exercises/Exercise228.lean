import ProofGapLean.Prelude.Elementary

namespace ProofGap.Exercise228

noncomputable section

def y (x : ℝ) : ℝ := (Real.exp x - Real.exp (-x)) / 2
def arcsinh (t : ℝ) : ℝ := Real.log (t + Real.sqrt (1 + t ^ 2))

/-- Exercise 228, gap 1. -/
theorem gap1 : ∀ x, 2 * y x = Real.exp x - Real.exp (-x) := by
  intro x
  unfold y
  ring

/-- Exercise 228, gap 2. -/
theorem gap2 : ∀ x,
    (Real.exp x) ^ 2 - 2 * y x * Real.exp x - 1 = 0 := by
  intro x
  calc
    (Real.exp x) ^ 2 - 2 * y x * Real.exp x - 1 =
        (Real.exp x) ^ 2 -
          (Real.exp x - Real.exp (-x)) * Real.exp x - 1 := by
      rw [gap1 x]
    _ = Real.exp (-x) * Real.exp x - 1 := by ring
    _ = Real.exp (-x + x) - 1 := by rw [Real.exp_add]
    _ = 0 := by norm_num

/-- Exercise 228, gap 3. -/
theorem gap3 : ∀ x, x = arcsinh (y x) := by
  intro x
  unfold arcsinh
  have hprod : Real.exp (-x) * Real.exp x = 1 := by
    rw [← Real.exp_add]
    norm_num
  have harg : 0 ≤ 1 + (y x) ^ 2 := by positivity
  have hsquare : (Real.sqrt (1 + (y x) ^ 2)) ^ 2 = 1 + (y x) ^ 2 :=
    Real.sq_sqrt harg
  have hc_nonneg :
      0 ≤ (Real.exp x + Real.exp (-x)) / 2 := by
    positivity
  have hcsquare :
      ((Real.exp x + Real.exp (-x)) / 2) ^ 2 = 1 + (y x) ^ 2 := by
    unfold y
    nlinarith [hprod]
  have hsqrt :
      Real.sqrt (1 + (y x) ^ 2) =
        (Real.exp x + Real.exp (-x)) / 2 := by
    nlinarith [Real.sqrt_nonneg (1 + (y x) ^ 2), hsquare,
      hc_nonneg, hcsquare]
  rw [hsqrt]
  unfold y
  rw [show
    (Real.exp x - Real.exp (-x)) / 2 +
        (Real.exp x + Real.exp (-x)) / 2 = Real.exp x by ring]
  rw [Real.log_exp]

/-- Exercise 228, gap 4. -/
theorem gap4 : ∀ x,
    arcsinh (y x) = Real.log (y x + Real.sqrt (1 + (y x) ^ 2)) := by
  intro x
  rfl

/-- Exercise 228, gap 5. -/
theorem gap5 : ∀ x,
    x = Real.log (y x + Real.sqrt (1 + (y x) ^ 2)) := by
  intro x
  calc
    x = arcsinh (y x) := gap3 x
    _ = Real.log (y x + Real.sqrt (1 + (y x) ^ 2)) := gap4 x

end

end ProofGap.Exercise228
