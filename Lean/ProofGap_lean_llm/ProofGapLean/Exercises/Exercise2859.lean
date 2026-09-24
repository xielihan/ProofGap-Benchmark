import ProofGapLean.Prelude.Analysis
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise2859

noncomputable section

def unitGeometricTerm (x : ℝ) (n : ℕ) : ℝ :=
  x ^ n

def sixthGeometricTerm (x : ℝ) (n : ℕ) : ℝ :=
  (-(1 / 6 : ℝ)) ^ n * x ^ n

def combinedTerm (x : ℝ) (n : ℕ) : ℝ :=
  (1 + (-1 : ℝ) ^ n / (6 : ℝ) ^ n) * x ^ n

theorem gap1 :
    ∀ x : ℝ, x ≠ 1 → x ≠ -6 →
      (12 - 5 * x) / (6 - 5 * x - x ^ 2) =
        1 / (1 - x) + 6 / (6 + x) := by
  intro x hx1 hx6
  have h1 : 1 - x ≠ 0 := by
    intro h
    apply hx1
    linarith
  have h6 : 6 + x ≠ 0 := by
    intro h
    apply hx6
    linarith
  have hfactor : 6 - 5 * x - x ^ 2 = (1 - x) * (6 + x) := by
    ring
  rw [hfactor]
  field_simp [h1, h6] <;> ring

theorem gap2
    (hpartial :
      ∀ x : ℝ, x ≠ 1 → x ≠ -6 →
        (12 - 5 * x) / (6 - 5 * x - x ^ 2) =
          1 / (1 - x) + 6 / (6 + x)) :
    ∀ x : ℝ, x ≠ 1 → x ≠ -6 →
      1 / (1 - x) + 6 / (6 + x) =
        1 / (1 - x) + 1 / (1 + x / 6) := by
  intro x hx1 hx6
  have h6 : 6 + x ≠ 0 := by
    intro h
    apply hx6
    linarith
  have hscaled : 1 + x / 6 = (6 + x) / 6 := by
    ring
  rw [hscaled]
  field_simp [h6] <;> ring

theorem gap3
    (hpartial :
      ∀ x : ℝ, x ≠ 1 → x ≠ -6 →
        (12 - 5 * x) / (6 - 5 * x - x ^ 2) =
          1 / (1 - x) + 6 / (6 + x))
    (hrewrite :
      ∀ x : ℝ, x ≠ 1 → x ≠ -6 →
        1 / (1 - x) + 6 / (6 + x) =
          1 / (1 - x) + 1 / (1 + x / 6)) :
    ∀ x : ℝ, |x| < 1 →
      1 / (1 - x) + 1 / (1 + x / 6) =
        (∑' n, unitGeometricTerm x n) + (∑' n, sixthGeometricTerm x n) := by
  intro x hx
  have hxnorm : ‖x‖ < 1 := by
    simpa only [Real.norm_eq_abs] using hx
  have hratio : ‖(-(1 / 6 : ℝ)) * x‖ < 1 := by
    rw [Real.norm_eq_abs, abs_mul]
    norm_num
    nlinarith [abs_nonneg x]
  have hsum1 : ∑' n : ℕ, x ^ n = (1 - x)⁻¹ :=
    (hasSum_geometric_of_norm_lt_one hxnorm).tsum_eq
  have hsum6 :
      ∑' n : ℕ, ((-(1 / 6 : ℝ)) * x) ^ n =
        (1 - (-(1 / 6 : ℝ)) * x)⁻¹ :=
    (hasSum_geometric_of_norm_lt_one hratio).tsum_eq
  simp only [unitGeometricTerm, sixthGeometricTerm]
  have hterms :
      (fun n : ℕ => (-(1 / 6 : ℝ)) ^ n * x ^ n) =
        (fun n : ℕ => ((-(1 / 6 : ℝ)) * x) ^ n) := by
    funext n
    exact (mul_pow _ _ n).symm
  rw [hterms, hsum1, hsum6]
  rw [show 1 + x / 6 = 1 - (-(1 / 6 : ℝ)) * x by ring]
  simp only [one_div]

theorem gap4
    (hgeometric :
      ∀ x : ℝ, |x| < 1 →
        1 / (1 - x) + 1 / (1 + x / 6) =
          (∑' n, unitGeometricTerm x n) + (∑' n, sixthGeometricTerm x n)) :
    ∀ x : ℝ, |x| < 1 →
      (∑' n, unitGeometricTerm x n) + (∑' n, sixthGeometricTerm x n) =
        ∑' n, combinedTerm x n := by
  intro x hx
  have hxnorm : ‖x‖ < 1 := by
    simpa only [Real.norm_eq_abs] using hx
  have hratio : ‖(-(1 / 6 : ℝ)) * x‖ < 1 := by
    rw [Real.norm_eq_abs, abs_mul]
    norm_num
    nlinarith [abs_nonneg x]
  have hunit : Summable (fun n : ℕ => unitGeometricTerm x n) := by
    simpa only [unitGeometricTerm] using
      (hasSum_geometric_of_norm_lt_one hxnorm).summable
  have hsixth : Summable (fun n : ℕ => sixthGeometricTerm x n) := by
    simpa only [sixthGeometricTerm, mul_pow] using
      (hasSum_geometric_of_norm_lt_one hratio).summable
  rw [← hunit.tsum_add hsixth]
  refine tsum_congr (fun n => ?_)
  unfold unitGeometricTerm sixthGeometricTerm combinedTerm
  have hpow :
      (-(1 / 6 : ℝ)) ^ n = (-1 : ℝ) ^ n / (6 : ℝ) ^ n := by
    rw [show -(1 / 6 : ℝ) = (-1 : ℝ) / 6 by ring, div_pow]
  rw [hpow]
  ring

theorem gap5
    (hpartial :
      ∀ x : ℝ, x ≠ 1 → x ≠ -6 →
        (12 - 5 * x) / (6 - 5 * x - x ^ 2) =
          1 / (1 - x) + 6 / (6 + x))
    (hgeometric :
      ∀ x : ℝ, |x| < 1 →
        1 / (1 - x) + 1 / (1 + x / 6) =
          (∑' n, unitGeometricTerm x n) + (∑' n, sixthGeometricTerm x n))
    (hcombine :
      ∀ x : ℝ, |x| < 1 →
        (∑' n, unitGeometricTerm x n) + (∑' n, sixthGeometricTerm x n) =
          ∑' n, combinedTerm x n) :
    ∀ x : ℝ, |x| < 1 →
      (12 - 5 * x) / (6 - 5 * x - x ^ 2) = ∑' n, combinedTerm x n := by
  intro x hx
  have hx1 : x ≠ 1 := by
    intro h
    rw [h] at hx
    norm_num at hx
  have hx6 : x ≠ -6 := by
    intro h
    rw [h] at hx
    norm_num at hx
  calc
    (12 - 5 * x) / (6 - 5 * x - x ^ 2) =
        1 / (1 - x) + 6 / (6 + x) := hpartial x hx1 hx6
    _ = 1 / (1 - x) + 1 / (1 + x / 6) :=
      gap2 hpartial x hx1 hx6
    _ = (∑' n, unitGeometricTerm x n) +
        (∑' n, sixthGeometricTerm x n) := hgeometric x hx
    _ = ∑' n, combinedTerm x n := hcombine x hx

end

end ProofGap.Exercise2859
