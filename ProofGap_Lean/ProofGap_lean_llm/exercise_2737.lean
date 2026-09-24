import Mathlib

open Filter
open scoped Topology BigOperators

namespace Exercise2737

def ConvergentSeriesInt (f : ℤ → ℂ) : Prop := Summable f
def ConvergentSeriesNat0 (f : ℕ → ℂ) : Prop := Summable f
def ConvergentSeriesNat1 (f : ℕ → ℂ) : Prop := Summable fun n => f (n + 1)

/-- GAP 1: convergence of the nonnegative part at `x₁`. -/
theorem proof_gap_exercise_2737_1 (a : ℤ → ℂ) (x1 x2 : ℂ)
    (hx1 : 0 < ‖x1‖) (h12 : ‖x1‖ < ‖x2‖)
    (hc1 : ConvergentSeriesInt fun n => a n * x1 ^ n)
    (hc2 : ConvergentSeriesInt fun n => a n * x2 ^ n) :
    ConvergentSeriesNat0 fun n : ℕ => a n * x1 ^ n := by
  sorry

/-- GAP 2: convergence of the negative part at `x₁`. -/
theorem proof_gap_exercise_2737_2 (a : ℤ → ℂ) (x1 x2 : ℂ)
    (hx1 : 0 < ‖x1‖) (h12 : ‖x1‖ < ‖x2‖)
    (hc1 : ConvergentSeriesInt fun n => a n * x1 ^ n)
    (hc2 : ConvergentSeriesInt fun n => a n * x2 ^ n)
    (hpos1 : ConvergentSeriesNat0 fun n : ℕ => a n * x1 ^ n) :
    ConvergentSeriesNat1 fun n : ℕ => a (-(n : ℤ)) * x1 ^ (-(n : ℤ)) := by
  sorry

/-- GAP 3: convergence of the nonnegative part at `x₂`. -/
theorem proof_gap_exercise_2737_3 (a : ℤ → ℂ) (x1 x2 : ℂ)
    (hx1 : 0 < ‖x1‖) (h12 : ‖x1‖ < ‖x2‖)
    (hc1 : ConvergentSeriesInt fun n => a n * x1 ^ n)
    (hc2 : ConvergentSeriesInt fun n => a n * x2 ^ n)
    (hpos1 : ConvergentSeriesNat0 fun n : ℕ => a n * x1 ^ n)
    (hneg1 : ConvergentSeriesNat1 fun n : ℕ => a (-(n : ℤ)) * x1 ^ (-(n : ℤ))) :
    ConvergentSeriesNat0 fun n : ℕ => a n * x2 ^ n := by
  sorry

/-- GAP 4: convergence of the negative part at `x₂`. -/
theorem proof_gap_exercise_2737_4 (a : ℤ → ℂ) (x1 x2 : ℂ)
    (hx1 : 0 < ‖x1‖) (h12 : ‖x1‖ < ‖x2‖)
    (hc1 : ConvergentSeriesInt fun n => a n * x1 ^ n)
    (hc2 : ConvergentSeriesInt fun n => a n * x2 ^ n)
    (hpos1 : ConvergentSeriesNat0 fun n : ℕ => a n * x1 ^ n)
    (hneg1 : ConvergentSeriesNat1 fun n : ℕ => a (-(n : ℤ)) * x1 ^ (-(n : ℤ)))
    (hpos2 : ConvergentSeriesNat0 fun n : ℕ => a n * x2 ^ n) :
    ConvergentSeriesNat1 fun n : ℕ => a (-(n : ℤ)) * x2 ^ (-(n : ℤ)) := by
  sorry

/-- GAP 5: power series converges inside the circle determined by `x₂`. -/
theorem proof_gap_exercise_2737_5 (a : ℤ → ℂ) (x1 x2 : ℂ)
    (hpos2 : ConvergentSeriesNat0 fun n : ℕ => a n * x2 ^ n) :
    ∀ x : ℂ, ‖x1‖ < ‖x‖ ∧ ‖x‖ < ‖x2‖ →
      ConvergentSeriesNat0 fun n : ℕ => a n * x ^ n := by
  sorry

/-- GAP 6: translate annulus condition to reciprocals. -/
theorem proof_gap_exercise_2737_6 (a : ℤ → ℂ) (x1 x2 : ℂ)
    (hx1 : 0 < ‖x1‖) :
    ∀ x : ℂ, ‖x1‖ < ‖x‖ ∧ ‖x‖ < ‖x2‖ → ‖(1 / x : ℂ)‖ < ‖(1 / x1 : ℂ)‖ := by
  sorry

/-- GAP 7: negative part converges by applying power-series convergence to `1/x`. -/
theorem proof_gap_exercise_2737_7 (a : ℤ → ℂ) (x1 x2 : ℂ)
    (hneg1 : ConvergentSeriesNat1 fun n : ℕ => a (-(n : ℤ)) * x1 ^ (-(n : ℤ)))
    (hrecip : ∀ x : ℂ, ‖x1‖ < ‖x‖ ∧ ‖x‖ < ‖x2‖ →
      ‖(1 / x : ℂ)‖ < ‖(1 / x1 : ℂ)‖) :
    ∀ x : ℂ, ‖x1‖ < ‖x‖ ∧ ‖x‖ < ‖x2‖ →
      ConvergentSeriesNat1 fun n : ℕ => a (-(n : ℤ)) * x ^ (-(n : ℤ)) := by
  sorry

/-- GAP 8: positive and negative parts imply convergence of the Laurent series. -/
theorem proof_gap_exercise_2737_8 (a : ℤ → ℂ) (x1 x2 : ℂ)
    (hpos : ∀ x : ℂ, ‖x1‖ < ‖x‖ ∧ ‖x‖ < ‖x2‖ →
      ConvergentSeriesNat0 fun n : ℕ => a n * x ^ n)
    (hneg : ∀ x : ℂ, ‖x1‖ < ‖x‖ ∧ ‖x‖ < ‖x2‖ →
      ConvergentSeriesNat1 fun n : ℕ => a (-(n : ℤ)) * x ^ (-(n : ℤ))) :
    ∀ x : ℂ, ‖x1‖ < ‖x‖ ∧ ‖x‖ < ‖x2‖ →
      ConvergentSeriesInt fun n : ℤ => a n * x ^ n := by
  sorry

/-- GAP 9: restatement of Laurent convergence on the annulus. -/
theorem proof_gap_exercise_2737_9 (a : ℤ → ℂ) (x1 x2 : ℂ)
    (hlaur : ∀ x : ℂ, ‖x1‖ < ‖x‖ ∧ ‖x‖ < ‖x2‖ →
      ConvergentSeriesInt fun n : ℤ => a n * x ^ n) :
    ∀ x : ℂ, ‖x1‖ < ‖x‖ ∧ ‖x‖ < ‖x2‖ →
      ConvergentSeriesInt fun n : ℤ => a n * x ^ n := by
  sorry

/-- GAP 10: final restatement of the theorem conclusion. -/
theorem proof_gap_exercise_2737_10 (a : ℤ → ℂ) (x1 x2 : ℂ)
    (hlaur : ∀ x : ℂ, ‖x1‖ < ‖x‖ ∧ ‖x‖ < ‖x2‖ →
      ConvergentSeriesInt fun n : ℤ => a n * x ^ n) :
    ∀ x : ℂ, ‖x1‖ < ‖x‖ ∧ ‖x‖ < ‖x2‖ →
      ConvergentSeriesInt fun n : ℤ => a n * x ^ n := by
  sorry

end Exercise2737
