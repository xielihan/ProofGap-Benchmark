import ProofGapLean.Prelude.Analysis
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise2858

noncomputable section

def geometricTerm (x : ℝ) (n : ℕ) : ℝ :=
  x ^ n

def negativeDoubleTerm (x : ℝ) (n : ℕ) : ℝ :=
  (-2 : ℝ) ^ n * x ^ n

def combinedTerm (x : ℝ) (n : ℕ) : ℝ :=
  (1 - (-2 : ℝ) ^ n) * x ^ n

theorem gap1 :
    ∀ x : ℝ, x ≠ 1 → x ≠ -(1 / 2 : ℝ) →
      x / (1 + x - 2 * x ^ 2) =
        (1 / 3 : ℝ) * (1 / (1 - x) - 1 / (1 + 2 * x)) := by
  intro x hx1 hxhalf
  have h1 : 1 - x ≠ 0 := by
    exact sub_ne_zero.mpr (Ne.symm hx1)
  have h2 : 1 + 2 * x ≠ 0 := by
    intro h
    apply hxhalf
    linarith
  have h2' : 1 + x * 2 ≠ 0 := by
    simpa [mul_comm] using h2
  have hfactor : 1 + x - 2 * x ^ 2 = (1 - x) * (1 + x * 2) := by
    ring
  rw [hfactor]
  field_simp [h1, h2, h2']
  <;> ring

theorem gap2
    (hpartial :
      ∀ x : ℝ, x ≠ 1 → x ≠ -(1 / 2 : ℝ) →
        x / (1 + x - 2 * x ^ 2) =
          (1 / 3 : ℝ) * (1 / (1 - x) - 1 / (1 + 2 * x))) :
    ∀ x : ℝ, |x| < 1 / 2 →
      (1 / 3 : ℝ) * (1 / (1 - x) - 1 / (1 + 2 * x)) =
        (1 / 3 : ℝ) *
          ((∑' n, geometricTerm x n) - (∑' n, negativeDoubleTerm x n)) := by
  intro x hx
  have hxnorm : ‖x‖ < 1 := by
    rw [Real.norm_eq_abs]
    linarith
  have hnegNorm : ‖(-2 : ℝ) * x‖ < 1 := by
    rw [Real.norm_eq_abs, abs_mul]
    have htwo : |(-2 : ℝ)| = 2 := by norm_num
    rw [htwo]
    linarith
  have hgeom : (∑' n, geometricTerm x n) = 1 / (1 - x) := by
    calc
      (∑' n, geometricTerm x n) = (1 - x)⁻¹ := by
        simpa only [geometricTerm] using
          (tsum_geometric_of_norm_lt_one hxnorm)
      _ = 1 / (1 - x) := by simp only [one_div]
  have hneg : (∑' n, negativeDoubleTerm x n) = 1 / (1 + 2 * x) := by
    calc
      (∑' n, negativeDoubleTerm x n) =
          ∑' n : ℕ, ((-2 : ℝ) * x) ^ n := by
        apply tsum_congr
        intro n
        simp only [negativeDoubleTerm, mul_pow]
      _ = (1 - ((-2 : ℝ) * x))⁻¹ :=
        tsum_geometric_of_norm_lt_one hnegNorm
      _ = 1 / (1 + 2 * x) := by
        rw [one_div]
        congr 1
        ring
  rw [hgeom, hneg]

theorem gap3
    (hpartial :
      ∀ x : ℝ, x ≠ 1 → x ≠ -(1 / 2 : ℝ) →
        x / (1 + x - 2 * x ^ 2) =
          (1 / 3 : ℝ) * (1 / (1 - x) - 1 / (1 + 2 * x)))
    (hgeometric :
      ∀ x : ℝ, |x| < 1 / 2 →
        (1 / 3 : ℝ) * (1 / (1 - x) - 1 / (1 + 2 * x)) =
          (1 / 3 : ℝ) *
            ((∑' n, geometricTerm x n) - (∑' n, negativeDoubleTerm x n))) :
    ∀ x : ℝ, |x| < 1 / 2 →
      (1 / 3 : ℝ) *
          ((∑' n, geometricTerm x n) - (∑' n, negativeDoubleTerm x n)) =
        (1 / 3 : ℝ) * (∑' n, combinedTerm x n) := by
  intro x hx
  have hxnorm : ‖x‖ < 1 := by
    rw [Real.norm_eq_abs]
    linarith
  have hnegNorm : ‖(-2 : ℝ) * x‖ < 1 := by
    rw [Real.norm_eq_abs, abs_mul]
    have htwo : |(-2 : ℝ)| = 2 := by norm_num
    rw [htwo]
    linarith
  have hsgeom : Summable (geometricTerm x) := by
    simpa only [geometricTerm] using
      (summable_geometric_of_norm_lt_one hxnorm)
  have hsneg : Summable (negativeDoubleTerm x) := by
    simpa only [negativeDoubleTerm, mul_pow] using
      (summable_geometric_of_norm_lt_one hnegNorm)
  have hcombined :
      HasSum (combinedTerm x)
        ((∑' n, geometricTerm x n) - (∑' n, negativeDoubleTerm x n)) := by
    refine (hsgeom.hasSum.sub hsneg.hasSum).congr ?_
    intro n
    simp only [combinedTerm, geometricTerm, negativeDoubleTerm]
    ring
  rw [hcombined.tsum_eq]

theorem gap4
    (hpartial :
      ∀ x : ℝ, x ≠ 1 → x ≠ -(1 / 2 : ℝ) →
        x / (1 + x - 2 * x ^ 2) =
          (1 / 3 : ℝ) * (1 / (1 - x) - 1 / (1 + 2 * x)))
    (hgeometric :
      ∀ x : ℝ, |x| < 1 / 2 →
        (1 / 3 : ℝ) * (1 / (1 - x) - 1 / (1 + 2 * x)) =
          (1 / 3 : ℝ) *
            ((∑' n, geometricTerm x n) - (∑' n, negativeDoubleTerm x n)))
    (hcombine :
      ∀ x : ℝ, |x| < 1 / 2 →
        (1 / 3 : ℝ) *
            ((∑' n, geometricTerm x n) - (∑' n, negativeDoubleTerm x n)) =
          (1 / 3 : ℝ) * (∑' n, combinedTerm x n)) :
    ∀ x : ℝ, |x| < 1 / 2 →
      x / (1 + x - 2 * x ^ 2) =
        (1 / 3 : ℝ) * (∑' n, combinedTerm x n) := by
  intro x hx
  have hx1 : x ≠ 1 := by
    intro h
    subst x
    norm_num at hx
  have hxhalf : x ≠ -(1 / 2 : ℝ) := by
    intro h
    subst x
    norm_num at hx
  calc
    x / (1 + x - 2 * x ^ 2) =
        (1 / 3 : ℝ) * (1 / (1 - x) - 1 / (1 + 2 * x)) :=
      hpartial x hx1 hxhalf
    _ = (1 / 3 : ℝ) *
          ((∑' n, geometricTerm x n) - (∑' n, negativeDoubleTerm x n)) :=
      hgeometric x hx
    _ = (1 / 3 : ℝ) * (∑' n, combinedTerm x n) :=
      hcombine x hx

end

end ProofGap.Exercise2858
