import ProofGapLean.Prelude.Core
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise221_4

noncomputable section

def f (a b c d x : ℝ) : ℝ := (a * x + b) / (c * x + d)

/-- Source: `proof_gap/exercise_221_4/1.txt`; exclude the pole. -/
theorem gap1 (a b c d : ℝ) : ∀ x, c * x + d ≠ 0 →
    f a b c d x = (a * x + b) / (c * x + d) := by
  intro x hx
  rfl

/-- Source: `proof_gap/exercise_221_4/2.txt`; require c≠0 and exclude the pole. -/
theorem gap2 (a b c d : ℝ) (hc : c ≠ 0) : ∀ x, c * x + d ≠ 0 →
    (a * x + b) / (c * x + d) =
      a / c + (b - a * (d / c)) / (c * x + d) := by
  intro x hx
  have hx' : x * c + d ≠ 0 := by simpa [mul_comm] using hx
  field_simp [hc, hx, hx']
  <;> ring

/-- Source: `proof_gap/exercise_221_4/3.txt`. -/
theorem gap3 (a b c d : ℝ) (hc : c ≠ 0) : ∀ x, c * x + d ≠ 0 →
    f a b c d x = a / c + (b - a * (d / c)) / (c * x + d) := by
  intro x hx
  simpa [f] using gap2 a b c d hc x hx

/-- Source: `proof_gap/exercise_221_4/4.txt`; d>0 fixes the missing denominator sign. -/
theorem gap4 (a b d : ℝ) (ha : 0 < a) (hd : 0 < d) :
    StrictMono (f a b 0 d) := by
  intro x y hxy
  simp only [f, zero_mul, zero_add]
  apply (div_lt_div_iff_of_pos_right hd).2
  nlinarith

/-- Source: `proof_gap/exercise_221_4/5.txt`; d>0 fixes the missing denominator sign. -/
theorem gap5 (a b d : ℝ) (ha : a < 0) (hd : 0 < d) :
    StrictAnti (f a b 0 d) := by
  intro x y hxy
  simp only [f, zero_mul, zero_add]
  apply (div_lt_div_iff_of_pos_right hd).2
  nlinarith

private theorem f_sub_f (a b c d x y : ℝ)
    (hx : c * x + d ≠ 0) (hy : c * y + d ≠ 0) :
    f a b c d y - f a b c d x =
      ((a * d - b * c) * (y - x)) /
        ((c * y + d) * (c * x + d)) := by
  have hx' : x * c + d ≠ 0 := by simpa [mul_comm] using hx
  have hy' : y * c + d ≠ 0 := by simpa [mul_comm] using hy
  unfold f
  field_simp [hx, hy, hx', hy']
  <;> ring

/-- Source: `proof_gap/exercise_221_4/6.txt`. -/
theorem gap6 (a b c d : ℝ) (hc : 0 < c) (h : b > a * (d / c)) :
    StrictAntiOn (f a b c d) (Set.Iio (-d / c)) := by
  intro x hx y hy hxy
  have hpole : c * (-d / c) + d = 0 := by
    field_simp [hc.ne']
    <;> ring
  have hdx : c * x + d < 0 := by
    have hmul := mul_lt_mul_of_pos_left hx hc
    nlinarith
  have hdy : c * y + d < 0 := by
    have hmul := mul_lt_mul_of_pos_left hy hc
    nlinarith
  have hratio : a * d / c < b := by
    calc
      a * d / c = a * (d / c) := by ring
      _ < b := h
  have hcoef : a * d - b * c < 0 := by
    have hcross := (div_lt_iff₀ hc).mp hratio
    linarith
  have hprod : 0 < (c * y + d) * (c * x + d) :=
    mul_pos_of_neg_of_neg hdy hdx
  have hnum : (a * d - b * c) * (y - x) < 0 :=
    mul_neg_of_neg_of_pos hcoef (sub_pos.mpr hxy)
  have hquot :
      ((a * d - b * c) * (y - x)) /
          ((c * y + d) * (c * x + d)) < 0 :=
    div_neg_of_neg_of_pos hnum hprod
  rw [← f_sub_f a b c d x y hdx.ne hdy.ne] at hquot
  linarith

/-- Source: `proof_gap/exercise_221_4/7.txt`. -/
theorem gap7 (a b c d : ℝ) (hc : 0 < c) (h : b > a * (d / c)) :
    StrictAntiOn (f a b c d) (Set.Ioi (-d / c)) := by
  intro x hx y hy hxy
  have hpole : c * (-d / c) + d = 0 := by
    field_simp [hc.ne']
    <;> ring
  have hdx : 0 < c * x + d := by
    have hmul := mul_lt_mul_of_pos_left hx hc
    nlinarith
  have hdy : 0 < c * y + d := by
    have hmul := mul_lt_mul_of_pos_left hy hc
    nlinarith
  have hratio : a * d / c < b := by
    calc
      a * d / c = a * (d / c) := by ring
      _ < b := h
  have hcoef : a * d - b * c < 0 := by
    have hcross := (div_lt_iff₀ hc).mp hratio
    linarith
  have hprod : 0 < (c * y + d) * (c * x + d) := mul_pos hdy hdx
  have hnum : (a * d - b * c) * (y - x) < 0 :=
    mul_neg_of_neg_of_pos hcoef (sub_pos.mpr hxy)
  have hquot :
      ((a * d - b * c) * (y - x)) /
          ((c * y + d) * (c * x + d)) < 0 :=
    div_neg_of_neg_of_pos hnum hprod
  rw [← f_sub_f a b c d x y hdx.ne' hdy.ne'] at hquot
  linarith

/-- Source: `proof_gap/exercise_221_4/8.txt`. -/
theorem gap8 (a b c d : ℝ) (hc : 0 < c) (h : b < a * d / c) :
    StrictMonoOn (f a b c d) (Set.Iio (-d / c)) := by
  intro x hx y hy hxy
  have hpole : c * (-d / c) + d = 0 := by
    field_simp [hc.ne']
    <;> ring
  have hdx : c * x + d < 0 := by
    have hmul := mul_lt_mul_of_pos_left hx hc
    nlinarith
  have hdy : c * y + d < 0 := by
    have hmul := mul_lt_mul_of_pos_left hy hc
    nlinarith
  have hcoef : 0 < a * d - b * c := by
    have hcross := (lt_div_iff₀ hc).mp h
    linarith
  have hprod : 0 < (c * y + d) * (c * x + d) :=
    mul_pos_of_neg_of_neg hdy hdx
  have hnum : 0 < (a * d - b * c) * (y - x) :=
    mul_pos hcoef (sub_pos.mpr hxy)
  have hquot :
      0 < ((a * d - b * c) * (y - x)) /
          ((c * y + d) * (c * x + d)) :=
    div_pos hnum hprod
  rw [← f_sub_f a b c d x y hdx.ne hdy.ne] at hquot
  linarith

/-- Source: `proof_gap/exercise_221_4/9.txt`. -/
theorem gap9 (a b c d : ℝ) (hc : 0 < c) (h : b < a * d / c) :
    StrictMonoOn (f a b c d) (Set.Ioi (-d / c)) := by
  intro x hx y hy hxy
  have hpole : c * (-d / c) + d = 0 := by
    field_simp [hc.ne']
    <;> ring
  have hdx : 0 < c * x + d := by
    have hmul := mul_lt_mul_of_pos_left hx hc
    nlinarith
  have hdy : 0 < c * y + d := by
    have hmul := mul_lt_mul_of_pos_left hy hc
    nlinarith
  have hcoef : 0 < a * d - b * c := by
    have hcross := (lt_div_iff₀ hc).mp h
    linarith
  have hprod : 0 < (c * y + d) * (c * x + d) := mul_pos hdy hdx
  have hnum : 0 < (a * d - b * c) * (y - x) :=
    mul_pos hcoef (sub_pos.mpr hxy)
  have hquot :
      0 < ((a * d - b * c) * (y - x)) /
          ((c * y + d) * (c * x + d)) :=
    div_pos hnum hprod
  rw [← f_sub_f a b c d x y hdx.ne' hdy.ne'] at hquot
  linarith

end

end ProofGap.Exercise221_4
