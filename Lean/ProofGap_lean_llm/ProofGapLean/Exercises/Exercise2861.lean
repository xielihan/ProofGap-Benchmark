import ProofGapLean.Prelude.Analysis
import Mathlib.Topology.Algebra.InfiniteSum.Basic

namespace ProofGap.Exercise2861

noncomputable section

def positiveRoot : ℝ :=
  (Real.sqrt 5 - 1) / 2

def negativeRoot : ℝ :=
  -(Real.sqrt 5 + 1) / 2

def reciprocalCoefficientTerm (x : ℝ) (n : ℕ) : ℝ :=
  ((2 / (Real.sqrt 5 - 1)) ^ (n + 1) +
      (-1 : ℝ) ^ n * (2 / (Real.sqrt 5 + 1)) ^ (n + 1)) *
    x ^ n

def fibonacciCoefficientTerm (x : ℝ) (n : ℕ) : ℝ :=
  (((Real.sqrt 5 + 1) / 2) ^ (n + 1) +
      (-1 : ℝ) ^ n * ((Real.sqrt 5 - 1) / 2) ^ (n + 1)) *
    x ^ n

private theorem sqrtFive_pos : 0 < Real.sqrt 5 :=
  Real.sqrt_pos.2 (by norm_num)

private theorem sqrtFive_sq : (Real.sqrt 5) ^ 2 = 5 :=
  Real.sq_sqrt (by norm_num)

private theorem sqrtFive_ne_zero : Real.sqrt 5 ≠ 0 :=
  ne_of_gt sqrtFive_pos

private theorem sqrtFive_sub_one_ne_zero : Real.sqrt 5 - 1 ≠ 0 := by
  nlinarith [sqrtFive_sq, Real.sqrt_nonneg 5]

private theorem sqrtFive_add_one_ne_zero : Real.sqrt 5 + 1 ≠ 0 := by
  positivity

theorem gap1 :
    ∀ x : ℝ,
      1 / (1 - x - x ^ 2) = 1 / ((5 / 4 : ℝ) - (x + 1 / 2) ^ 2) := by
  intro x
  congr 1
  ring

theorem gap2
    (hcomplete :
      ∀ x : ℝ,
        1 / (1 - x - x ^ 2) = 1 / ((5 / 4 : ℝ) - (x + 1 / 2) ^ 2)) :
    ∀ x : ℝ, x ≠ positiveRoot → x ≠ negativeRoot →
      1 / ((5 / 4 : ℝ) - (x + 1 / 2) ^ 2) =
        1 / Real.sqrt 5 *
          (1 / (Real.sqrt 5 / 2 - (x + 1 / 2)) +
            1 / (Real.sqrt 5 / 2 + x + 1 / 2)) := by
  intro x hxpos hxneg
  have hleft : Real.sqrt 5 / 2 - (x + 1 / 2) ≠ 0 := by
    intro h
    apply hxpos
    unfold positiveRoot
    linarith
  have hright : Real.sqrt 5 / 2 + x + 1 / 2 ≠ 0 := by
    intro h
    apply hxneg
    unfold negativeRoot
    linarith
  let A : ℝ := Real.sqrt 5 / 2 - (x + 1 / 2)
  let B : ℝ := Real.sqrt 5 / 2 + x + 1 / 2
  have hA : A ≠ 0 := by simpa [A] using hleft
  have hB : B ≠ 0 := by simpa [B] using hright
  have hfactor :
      (5 / 4 : ℝ) - (x + 1 / 2) ^ 2 =
        A * B := by
    dsimp [A, B]
    nlinarith [sqrtFive_sq]
  rw [hfactor]
  change
    1 / (A * B) =
      1 / Real.sqrt 5 * (1 / A + 1 / B)
  field_simp [sqrtFive_ne_zero, hA, hB]
  dsimp [A, B]
  ring

theorem gap3
    (hcomplete :
      ∀ x : ℝ,
        1 / (1 - x - x ^ 2) = 1 / ((5 / 4 : ℝ) - (x + 1 / 2) ^ 2))
    (hpartial :
      ∀ x : ℝ, x ≠ positiveRoot → x ≠ negativeRoot →
        1 / ((5 / 4 : ℝ) - (x + 1 / 2) ^ 2) =
          1 / Real.sqrt 5 *
            (1 / (Real.sqrt 5 / 2 - (x + 1 / 2)) +
              1 / (Real.sqrt 5 / 2 + x + 1 / 2))) :
    ∀ x : ℝ, x ≠ positiveRoot → x ≠ negativeRoot →
      1 / (1 - x - x ^ 2) =
        1 / Real.sqrt 5 *
          (1 / (Real.sqrt 5 / 2 - (x + 1 / 2)) +
            1 / (Real.sqrt 5 / 2 + x + 1 / 2)) := by
  intro x hxpos hxneg
  exact (hcomplete x).trans (hpartial x hxpos hxneg)

theorem gap4
    (hpartial :
      ∀ x : ℝ, x ≠ positiveRoot → x ≠ negativeRoot →
        1 / (1 - x - x ^ 2) =
          1 / Real.sqrt 5 *
            (1 / (Real.sqrt 5 / 2 - (x + 1 / 2)) +
              1 / (Real.sqrt 5 / 2 + x + 1 / 2))) :
    ∀ x : ℝ, x ≠ positiveRoot → x ≠ negativeRoot →
      1 / (1 - x - x ^ 2) =
        1 / Real.sqrt 5 *
          (2 / (Real.sqrt 5 - 1) *
              (1 - 2 / (Real.sqrt 5 - 1) * x)⁻¹ +
            2 / (Real.sqrt 5 + 1) *
              (1 + 2 / (Real.sqrt 5 + 1) * x)⁻¹) := by
  intro x hxpos hxneg
  rw [hpartial x hxpos hxneg]
  have hleft : Real.sqrt 5 / 2 - (x + 1 / 2) ≠ 0 := by
    intro h
    apply hxpos
    unfold positiveRoot
    linarith
  have hright : Real.sqrt 5 / 2 + x + 1 / 2 ≠ 0 := by
    intro h
    apply hxneg
    unfold negativeRoot
    linarith
  have hgeomLeft :
      1 - 2 / (Real.sqrt 5 - 1) * x ≠ 0 := by
    intro h
    apply hxpos
    unfold positiveRoot
    field_simp [sqrtFive_sub_one_ne_zero] at h ⊢
    linarith
  have hgeomRight :
      1 + 2 / (Real.sqrt 5 + 1) * x ≠ 0 := by
    intro h
    apply hxneg
    unfold negativeRoot
    field_simp [sqrtFive_add_one_ne_zero] at h ⊢
    linarith
  field_simp [sqrtFive_ne_zero, sqrtFive_sub_one_ne_zero,
    sqrtFive_add_one_ne_zero, hleft, hright, hgeomLeft, hgeomRight]
  <;> ring

theorem gap5
    (hgeometricForm :
      ∀ x : ℝ, x ≠ positiveRoot → x ≠ negativeRoot →
        1 / (1 - x - x ^ 2) =
          1 / Real.sqrt 5 *
            (2 / (Real.sqrt 5 - 1) *
                (1 - 2 / (Real.sqrt 5 - 1) * x)⁻¹ +
              2 / (Real.sqrt 5 + 1) *
                (1 + 2 / (Real.sqrt 5 + 1) * x)⁻¹)) :
    ∀ x : ℝ, |x| < positiveRoot →
      1 / (1 - x - x ^ 2) =
        1 / Real.sqrt 5 * (∑' n, reciprocalCoefficientTerm x n) := by
  intro x hx
  have hsqrt_gt_one : 1 < Real.sqrt 5 := by
    nlinarith [sqrtFive_sq, Real.sqrt_nonneg 5]
  have hsqrt_lt_three : Real.sqrt 5 < 3 := by
    nlinarith [sqrtFive_sq, Real.sqrt_nonneg 5]
  have hroot_pos : 0 < positiveRoot := by
    unfold positiveRoot
    linarith
  have hroot_lt_one : positiveRoot < 1 := by
    unfold positiveRoot
    linarith
  have hbounds : -positiveRoot < x ∧ x < positiveRoot :=
    (abs_lt.mp hx)
  have hxpos : x ≠ positiveRoot :=
    ne_of_lt hbounds.2
  have hxneg : x ≠ negativeRoot := by
    have hneg_lt : negativeRoot < -positiveRoot := by
      unfold negativeRoot positiveRoot
      linarith
    exact ne_of_gt (hneg_lt.trans hbounds.1)
  rw [hgeometricForm x hxpos hxneg]
  let p : ℝ := 2 / (Real.sqrt 5 - 1)
  let r : ℝ := 2 / (Real.sqrt 5 + 1)
  have hp_pos : 0 < p := by
    dsimp [p]
    exact div_pos (by norm_num) (sub_pos.mpr hsqrt_gt_one)
  have hr_pos : 0 < r := by
    dsimp [r]
    positivity
  have hp_eq : p = 1 / positiveRoot := by
    unfold p positiveRoot
    field_simp [sqrtFive_sub_one_ne_zero]
  have hr_eq : r = positiveRoot := by
    unfold r positiveRoot
    field_simp [sqrtFive_add_one_ne_zero]
    nlinarith [sqrtFive_sq]
  have hpx : ‖p * x‖ < 1 := by
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos hp_pos, hp_eq]
    calc
      1 / positiveRoot * |x| = |x| / positiveRoot := by ring
      _ < 1 := (div_lt_one hroot_pos).2 hx
  have hrx : ‖(-r) * x‖ < 1 := by
    rw [Real.norm_eq_abs, abs_mul, abs_neg, abs_of_pos hr_pos, hr_eq]
    have hfirst :
        positiveRoot * |x| < positiveRoot * positiveRoot :=
      mul_lt_mul_of_pos_left hx hroot_pos
    have hprod :
        0 < (1 - positiveRoot) * (1 + positiveRoot) :=
      mul_pos (sub_pos.mpr hroot_lt_one) (by linarith)
    have hsecond : positiveRoot * positiveRoot < 1 := by
      nlinarith
    exact hfirst.trans hsecond
  have hs1 :
      HasSum
        (fun n : ℕ => p * (p * x) ^ n)
        (p * (1 - p * x)⁻¹) :=
    (hasSum_geometric_of_norm_lt_one hpx).mul_left p
  have hs2 :
      HasSum
        (fun n : ℕ => r * ((-r) * x) ^ n)
        (r * (1 + r * x)⁻¹) := by
    convert
      (hasSum_geometric_of_norm_lt_one hrx).mul_left r using 1
    ring
  have hseries :
      HasSum
        (fun n : ℕ => reciprocalCoefficientTerm x n)
        (p * (1 - p * x)⁻¹ + r * (1 + r * x)⁻¹) := by
    have hfun :
        (fun n : ℕ => reciprocalCoefficientTerm x n) =
          (fun n : ℕ => p * (p * x) ^ n + r * ((-r) * x) ^ n) := by
      funext n
      change
        (p ^ (n + 1) + (-1 : ℝ) ^ n * r ^ (n + 1)) * x ^ n =
          p * (p * x) ^ n + r * ((-r) * x) ^ n
      rw [pow_succ p n, pow_succ r n, mul_pow, mul_pow, neg_pow r n]
      ring
    rw [hfun]
    exact hs1.add hs2
  change
    1 / Real.sqrt 5 *
        (p * (1 - p * x)⁻¹ + r * (1 + r * x)⁻¹) =
      1 / Real.sqrt 5 * (∑' n, reciprocalCoefficientTerm x n)
  rw [hseries.tsum_eq]

theorem gap6
    (hseries :
      ∀ x : ℝ, |x| < positiveRoot →
        1 / (1 - x - x ^ 2) =
          1 / Real.sqrt 5 * (∑' n, reciprocalCoefficientTerm x n)) :
    ∀ x : ℝ, |x| < positiveRoot →
      1 / (1 - x - x ^ 2) =
        1 / Real.sqrt 5 * (∑' n, fibonacciCoefficientTerm x n) := by
  intro x hx
  rw [hseries x hx]
  congr 2
  funext n
  have hfirst :
      2 / (Real.sqrt 5 - 1) = (Real.sqrt 5 + 1) / 2 := by
    field_simp [sqrtFive_sub_one_ne_zero]
    nlinarith [sqrtFive_sq]
  have hsecond :
      2 / (Real.sqrt 5 + 1) = (Real.sqrt 5 - 1) / 2 := by
    field_simp [sqrtFive_add_one_ne_zero]
    nlinarith [sqrtFive_sq]
  simp only [reciprocalCoefficientTerm, fibonacciCoefficientTerm]
  rw [hfirst, hsecond]

end

end ProofGap.Exercise2861
