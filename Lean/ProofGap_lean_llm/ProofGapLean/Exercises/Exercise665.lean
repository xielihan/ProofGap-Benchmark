import ProofGapLean.Prelude.Elementary
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

namespace ProofGap.Exercise665

noncomputable section

def δ (n : ℕ) : ℝ := Real.rpow 10 (-((n : ℝ) + 1))
def tolerance (n : ℕ) : ℝ := Real.rpow 10 (-(n : ℝ))
def lower (n : ℕ) : ℝ := 100 * (1 - δ n) ^ 2
def upper (n : ℕ) : ℝ := 100 * (1 + δ n) ^ 2

/-- Exercise 665, gap 1. -/
private theorem delta_closed_form (n : ℕ) :
    δ n = ((10 : ℝ) ^ (n + 1))⁻¹ := by
  unfold δ
  rw [show (n : ℝ) + 1 = ((n + 1 : ℕ) : ℝ) by norm_num]
  calc
    Real.rpow 10 (-((n + 1 : ℕ) : ℝ)) =
        (Real.rpow 10 ((n + 1 : ℕ) : ℝ))⁻¹ := by
      exact Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 10) ((n + 1 : ℕ) : ℝ)
    _ = ((10 : ℝ) ^ (n + 1))⁻¹ := by
      have hp : Real.rpow (10 : ℝ) ((n + 1 : ℕ) : ℝ) =
          (10 : ℝ) ^ (n + 1) := by
        exact Real.rpow_natCast (10 : ℝ) (n + 1)
      rw [hp]

theorem gap1 (n : ℕ) (x : ℝ)
    (h : 10 * (1 - δ n) < Real.sqrt x ∧
      Real.sqrt x < 10 * (1 + δ n)) :
    |Real.sqrt x - 10| < tolerance n := by
  have ht : tolerance n = ((10 : ℝ) ^ n)⁻¹ := by
    unfold tolerance
    calc
      Real.rpow 10 (-(n : ℝ)) = (Real.rpow 10 (n : ℝ))⁻¹ := by
        exact Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 10) (n : ℝ)
      _ = ((10 : ℝ) ^ n)⁻¹ := by
        have hp : Real.rpow (10 : ℝ) (n : ℝ) = (10 : ℝ) ^ n := by
          exact Real.rpow_natCast (10 : ℝ) n
        rw [hp]
  have hscale : 10 * δ n = tolerance n := by
    rw [delta_closed_form, ht, pow_succ]
    field_simp
  rw [abs_lt]
  constructor <;> linarith [h.1, h.2, hscale]

/-- Exercise 665, gap 2; include nonnegativity needed to pass from squared bounds to square-root bounds. -/
theorem gap2 (n : ℕ) (x : ℝ) (hx : 0 ≤ x)
    (h : lower n < x ∧ x < upper n) :
    10 * (1 - δ n) < Real.sqrt x ∧
      Real.sqrt x < 10 * (1 + δ n) := by
  rcases h with ⟨hl, hu⟩
  have hn : 0 ≤ (n : ℝ) := by positivity
  have hexp : -((n : ℝ) + 1) < 0 := by linarith
  have hdlt : δ n < 1 := by
    unfold δ
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) hexp
  have hdpos : 0 < δ n := by
    rw [delta_closed_form]
    positivity
  have hs0 : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
  have hs2 : (Real.sqrt x) ^ 2 = x := Real.sq_sqrt hx
  constructor
  · by_contra hnot
    have hle : Real.sqrt x ≤ 10 * (1 - δ n) := le_of_not_gt hnot
    have ha0 : 0 ≤ 10 * (1 - δ n) := by nlinarith
    have hminus : 0 ≤ 10 * (1 - δ n) - Real.sqrt x := by linarith
    have hplus : 0 ≤ 10 * (1 - δ n) + Real.sqrt x := by linarith
    have hp := mul_nonneg hminus hplus
    unfold lower at hl
    nlinarith [hp]
  · by_contra hnot
    have hle : 10 * (1 + δ n) ≤ Real.sqrt x := le_of_not_gt hnot
    have hb0 : 0 ≤ 10 * (1 + δ n) := by nlinarith
    have hminus : 0 ≤ Real.sqrt x - 10 * (1 + δ n) := by linarith
    have hplus : 0 ≤ Real.sqrt x + 10 * (1 + δ n) := by linarith
    have hp := mul_nonneg hminus hplus
    unfold upper at hu
    nlinarith [hp]

/-- Exercise 665, gap 3. -/
theorem gap3 (n : ℕ) (x : ℝ) (hx : 0 ≤ x)
    (h : lower n < x ∧ x < upper n) :
    |Real.sqrt x - 10| < tolerance n := by
  exact gap1 n x (gap2 n x hx h)

/-- Exercise 665, gap 4; add the omitted interval premise. -/
theorem gap4 (x : ℝ) (h : lower 0 < x ∧ x < upper 0) :
    (81 : ℝ) < x := by
  have hl := h.1
  norm_num [lower, delta_closed_form] at hl
  exact hl

/-- Exercise 665, gap 5; add the omitted interval premise. -/
theorem gap5 (x : ℝ) (h : lower 0 < x ∧ x < upper 0) :
    x < (121 : ℝ) := by
  have hu := h.2
  norm_num [upper, delta_closed_form] at hu
  exact hu

/-- Exercise 665, gap 6. -/
theorem gap6 : (81 : ℝ) < 121 := by
  norm_num

/-- Exercise 665, gap 7; add the omitted interval premise. -/
theorem gap7 (x : ℝ) (h : lower 1 < x ∧ x < upper 1) :
    (98.01 : ℝ) < x := by
  have hl := h.1
  norm_num [lower, delta_closed_form] at hl
  convert hl using 1 <;> norm_num

/-- Exercise 665, gap 8; add the omitted interval premise. -/
theorem gap8 (x : ℝ) (h : lower 1 < x ∧ x < upper 1) :
    x < (102.01 : ℝ) := by
  have hu := h.2
  norm_num [upper, delta_closed_form] at hu
  convert hu using 1 <;> norm_num

/-- Exercise 665, gap 9. -/
theorem gap9 : (98.01 : ℝ) < 102.01 := by
  norm_num

/-- Exercise 665, gap 10; correct the source typo `98.8001` to `99.8001` and add the interval premise. -/
theorem gap10 (x : ℝ) (h : lower 2 < x ∧ x < upper 2) :
    (99.8001 : ℝ) < x := by
  have hl := h.1
  norm_num [lower, delta_closed_form] at hl
  convert hl using 1 <;> norm_num

/-- Exercise 665, gap 11; add the omitted interval premise. -/
theorem gap11 (x : ℝ) (h : lower 2 < x ∧ x < upper 2) :
    x < (100.2001 : ℝ) := by
  have hu := h.2
  norm_num [upper, delta_closed_form] at hu
  convert hu using 1 <;> norm_num

/-- Exercise 665, gap 12; correct the same lower-endpoint typo. -/
theorem gap12 : (99.8001 : ℝ) < 100.2001 := by
  norm_num

/-- Exercise 665, gap 13; add the omitted interval premise. -/
theorem gap13 (x : ℝ) (h : lower 3 < x ∧ x < upper 3) :
    (99.980001 : ℝ) < x := by
  have hl := h.1
  norm_num [lower, delta_closed_form] at hl
  convert hl using 1 <;> norm_num

/-- Exercise 665, gap 14; add the omitted interval premise. -/
theorem gap14 (x : ℝ) (h : lower 3 < x ∧ x < upper 3) :
    x < (100.020001 : ℝ) := by
  have hu := h.2
  norm_num [upper, delta_closed_form] at hu
  convert hu using 1 <;> norm_num

/-- Exercise 665, gap 15. -/
theorem gap15 : (99.980001 : ℝ) < 100.020001 := by
  norm_num

end

end ProofGap.Exercise665
