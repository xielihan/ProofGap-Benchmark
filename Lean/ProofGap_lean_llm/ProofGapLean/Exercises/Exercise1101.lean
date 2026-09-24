import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

namespace ProofGap.Exercise1101

noncomputable section

def Approx (x y ε : ℝ) : Prop := |x - y| < ε

private lemma pi_d4_bounds :
    (31415 / 10000 : ℝ) < Real.pi ∧ Real.pi < (31416 / 10000 : ℝ) := by
  constructor
  · nlinarith [Real.pi_gt_d4]
  · nlinarith [Real.pi_lt_d4]

private lemma sqrt_three_bounds :
    (173205 / 100000 : ℝ) < Real.sqrt 3 ∧
      Real.sqrt 3 < (173206 / 100000 : ℝ) := by
  have hs0 : 0 ≤ Real.sqrt (3 : ℝ) := Real.sqrt_nonneg 3
  have hs2 : (Real.sqrt (3 : ℝ)) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  constructor <;> nlinarith

private lemma cos_five_pi_div_six :
    Real.cos (5 * Real.pi / 6) = -Real.sqrt 3 / 2 := by
  rw [show 5 * Real.pi / 6 = Real.pi - Real.pi / 6 by ring,
    Real.cos_sub, Real.cos_pi, Real.sin_pi, Real.cos_pi_div_six]
  ring

private lemma sin_five_pi_div_six :
    Real.sin (5 * Real.pi / 6) = 1 / 2 := by
  rw [show 5 * Real.pi / 6 = Real.pi - Real.pi / 6 by ring,
    Real.sin_sub, Real.sin_pi, Real.cos_pi, Real.sin_pi_div_six]
  ring

private lemma cos_151_formula :
    Real.cos (151 * Real.pi / 180) =
      -Real.sqrt 3 / 2 - Real.pi / 360 +
        Real.sqrt 3 / 2 * (1 - Real.cos (Real.pi / 180)) +
        (Real.pi / 180 - Real.sin (Real.pi / 180)) / 2 := by
  rw [show 151 * Real.pi / 180 = 5 * Real.pi / 6 + Real.pi / 180 by ring,
    Real.cos_add, cos_five_pi_div_six, sin_five_pi_div_six]
  ring

private lemma small_angle_bounds :
    0 ≤ 1 - Real.cos (Real.pi / 180) ∧
      1 - Real.cos (Real.pi / 180) < (153 / 1000000 : ℝ) ∧
      0 ≤ Real.pi / 180 - Real.sin (Real.pi / 180) ∧
      Real.pi / 180 - Real.sin (Real.pi / 180) < (3 / 1000000 : ℝ) := by
  let h : ℝ := Real.pi / 180
  have hh0 : 0 ≤ h := by
    dsimp [h]
    positivity
  have hhpos : 0 < h := by
    dsimp [h]
    positivity
  have hh : h < (1746 / 100000 : ℝ) := by
    rcases pi_d4_bounds with ⟨_, hp⟩
    dsimp [h]
    nlinarith
  have habs : |h| ≤ 1 := by
    rw [abs_of_nonneg hh0]
    nlinarith
  have hu0 : 0 ≤ 1 - Real.cos h :=
    sub_nonneg.mpr (Real.cos_le_one h)
  have hsum : 0 < (1746 / 100000 : ℝ) + h := by
    nlinarith
  have hprod : 0 <
      ((1746 / 100000 : ℝ) - h) * ((1746 / 100000 : ℝ) + h) :=
    mul_pos (sub_pos.mpr hh) hsum
  have hh2sharp : h ^ 2 < (1746 / 100000 : ℝ) ^ 2 := by
    nlinarith [hprod]
  have hh2 : h ^ 2 < (1 / 3000 : ℝ) := by
    nlinarith [hh2sharp]
  have hh2sum : 0 < (1 / 3000 : ℝ) + h ^ 2 := by
    nlinarith [sq_nonneg h]
  have hh4prod : 0 <
      ((1 / 3000 : ℝ) - h ^ 2) * ((1 / 3000 : ℝ) + h ^ 2) :=
    mul_pos (sub_pos.mpr hh2) hh2sum
  have hh4 : h ^ 4 < (1 / 3000 : ℝ) ^ 2 := by
    nlinarith [hh4prod]
  have hcosb := Real.cos_bound habs
  rw [abs_of_nonneg hh0] at hcosb
  have hcoslo :
      -(h ^ 4 * (5 / 96 : ℝ)) ≤ Real.cos h - (1 - h ^ 2 / 2) :=
    (abs_le.mp hcosb).1
  have hu : 1 - Real.cos h < (153 / 1000000 : ℝ) := by
    nlinarith [hcoslo, hh2sharp, hh4]
  have hv0 : 0 ≤ h - Real.sin h :=
    sub_nonneg.mpr (Real.sin_le hh0)
  have hsinb := Real.sin_bound habs
  rw [abs_of_nonneg hh0] at hsinb
  have hsinlo :
      -(h ^ 4 * (5 / 96 : ℝ)) ≤
        Real.sin h - (h - h ^ 3 / 6) :=
    (abs_le.mp hsinb).1
  have hh20 : h < (1 / 50 : ℝ) := by
    nlinarith
  have hh3a : h ^ 2 * h < (1 / 3000 : ℝ) * h :=
    mul_lt_mul_of_pos_right hh2 hhpos
  have hh3b : (1 / 3000 : ℝ) * h <
      (1 / 3000 : ℝ) * (1 / 50 : ℝ) :=
    mul_lt_mul_of_pos_left hh20 (by norm_num)
  have hh3 : h ^ 3 < (1 / 150000 : ℝ) := by
    nlinarith [hh3a, hh3b]
  have hv : h - Real.sin h < (3 / 1000000 : ℝ) := by
    nlinarith [hsinlo, hh3, hh4]
  dsimp [h] at hu0 hu hv0 hv ⊢
  exact ⟨hu0, hu, hv0, hv⟩

private lemma cos_correction_bounds :
    0 ≤ Real.sqrt 3 / 2 * (1 - Real.cos (Real.pi / 180)) +
        (Real.pi / 180 - Real.sin (Real.pi / 180)) / 2 ∧
      Real.sqrt 3 / 2 * (1 - Real.cos (Real.pi / 180)) +
        (Real.pi / 180 - Real.sin (Real.pi / 180)) / 2 <
          (135 / 1000000 : ℝ) := by
  rcases sqrt_three_bounds with ⟨hs_lo, hs_hi⟩
  rcases small_angle_bounds with ⟨hu0, hu, hv0, hv⟩
  have hspos : 0 < Real.sqrt 3 / 2 := by
    nlinarith
  have hp0 : 0 ≤ Real.sqrt 3 / 2 *
      (1 - Real.cos (Real.pi / 180)) :=
    mul_nonneg (le_of_lt hspos) hu0
  have hp1 : Real.sqrt 3 / 2 *
      (1 - Real.cos (Real.pi / 180)) <
        Real.sqrt 3 / 2 * (153 / 1000000 : ℝ) :=
    mul_lt_mul_of_pos_left hu hspos
  have hsh : Real.sqrt 3 / 2 < (173206 / 100000 : ℝ) / 2 := by
    nlinarith
  have hp2 : Real.sqrt 3 / 2 * (153 / 1000000 : ℝ) <
      ((173206 / 100000 : ℝ) / 2) * (153 / 1000000 : ℝ) :=
    mul_lt_mul_of_pos_right hsh (by norm_num)
  constructor
  · nlinarith
  · nlinarith

private lemma arctan_105_formula :
    Real.arctan (105 / 100 : ℝ) =
      Real.arctan 1 + Real.arctan (1 / 41 : ℝ) := by
  have h := Real.arctan_add (x := (1 : ℝ)) (y := (1 / 41 : ℝ)) (by norm_num)
  convert h.symm using 1 <;> norm_num

private lemma arctan_one_over_41_bounds :
    (243 / 10000 : ℝ) < Real.arctan (1 / 41 : ℝ) ∧
      Real.arctan (1 / 41 : ℝ) < (1 / 40 : ℝ) := by
  let q : ℝ := 243 / 10000
  have hqpos : 0 < q := by norm_num [q]
  have hqabs : |q| ≤ 1 := by
    rw [abs_of_pos hqpos]
    norm_num [q]
  have hcosb := Real.cos_bound hqabs
  rw [abs_of_nonneg (le_of_lt hqpos)] at hcosb
  have hcoslo :
      -(q ^ 4 * (5 / 96 : ℝ)) ≤ Real.cos q - (1 - q ^ 2 / 2) :=
    (abs_le.mp hcosb).1
  have hcospos : 0 < Real.cos q := by
    dsimp [q] at hcoslo ⊢
    nlinarith
  have hsin : Real.sin q < q := Real.sin_lt hqpos
  have hqcos : q < (1 / 41 : ℝ) * Real.cos q := by
    dsimp [q] at hcoslo ⊢
    nlinarith
  have htan : Real.tan q < (1 / 41 : ℝ) := by
    rw [Real.tan_eq_sin_div_cos]
    apply (div_lt_iff₀ hcospos).2
    exact lt_trans hsin hqcos
  have hqlo : -(Real.pi / 2) < q := by
    dsimp [q]
    nlinarith [Real.pi_gt_three]
  have hqhi : q < Real.pi / 2 := by
    dsimp [q]
    nlinarith [Real.pi_gt_three]
  have hlo : Real.arctan (Real.tan q) < Real.arctan (1 / 41 : ℝ) :=
    Real.arctan_strictMono htan
  rw [Real.arctan_tan hqlo hqhi] at hlo
  let r : ℝ := 1 / 40
  have hrpos : 0 < r := by norm_num [r]
  have hrabs : |r| ≤ 1 := by
    rw [abs_of_pos hrpos]
    norm_num [r]
  have hrcosb := Real.cos_bound hrabs
  rw [abs_of_nonneg (le_of_lt hrpos)] at hrcosb
  have hrcoslo :
      -(r ^ 4 * (5 / 96 : ℝ)) ≤ Real.cos r - (1 - r ^ 2 / 2) :=
    (abs_le.mp hrcosb).1
  have hrcospos : 0 < Real.cos r := by
    dsimp [r] at hrcoslo ⊢
    nlinarith
  have hrsinb := Real.sin_bound hrabs
  rw [abs_of_nonneg (le_of_lt hrpos)] at hrsinb
  have hrsinlo :
      -(r ^ 4 * (5 / 96 : ℝ)) ≤
        Real.sin r - (r - r ^ 3 / 6) :=
    (abs_le.mp hrsinb).1
  have hrsin : (1 / 41 : ℝ) < Real.sin r := by
    dsimp [r] at hrsinlo ⊢
    nlinarith
  have hrtan : (1 / 41 : ℝ) < Real.tan r := by
    rw [Real.tan_eq_sin_div_cos]
    apply (lt_div_iff₀ hrcospos).2
    nlinarith [Real.cos_le_one r]
  have hrlo : -(Real.pi / 2) < r := by
    dsimp [r]
    nlinarith [Real.pi_gt_three]
  have hrhi : r < Real.pi / 2 := by
    dsimp [r]
    nlinarith [Real.pi_gt_three]
  have hu : Real.arctan (1 / 41 : ℝ) < Real.arctan (Real.tan r) :=
    Real.arctan_strictMono hrtan
  rw [Real.arctan_tan hrlo hrhi] at hu
  constructor
  · simpa [q] using hlo
  · simpa [r] using hu

theorem gap1 :
    Approx (Real.cos (151 * Real.pi / 180))
      (Real.cos (5 * Real.pi / 6) -
        Real.sin (5 * Real.pi / 6) * (Real.pi / 180))
      (2 / 10000 : ℝ) := by
  unfold Approx
  rw [cos_151_formula, cos_five_pi_div_six, sin_five_pi_div_six]
  rcases cos_correction_bounds with ⟨hc0, hc⟩
  rw [abs_lt]
  constructor <;> nlinarith

theorem gap2 :
    Approx
      (Real.cos (5 * Real.pi / 6) -
        Real.sin (5 * Real.pi / 6) * (Real.pi / 180))
      (-(8748 / 10000 : ℝ)) (1 / 10000 : ℝ) := by
  unfold Approx
  rw [cos_five_pi_div_six, sin_five_pi_div_six]
  rcases pi_d4_bounds with ⟨hpi_lo, hpi_hi⟩
  rcases sqrt_three_bounds with ⟨hs_lo, hs_hi⟩
  rw [abs_lt]
  constructor <;> nlinarith

theorem gap3 :
    Approx (Real.cos (151 * Real.pi / 180))
      (-(8748 / 10000 : ℝ)) (2 / 10000 : ℝ) := by
  unfold Approx
  rw [cos_151_formula]
  rcases pi_d4_bounds with ⟨hpi_lo, hpi_hi⟩
  rcases sqrt_three_bounds with ⟨hs_lo, hs_hi⟩
  rcases cos_correction_bounds with ⟨hc0, hc⟩
  rw [abs_lt]
  constructor <;> nlinarith

theorem gap4 :
    Approx (Real.arctan (105 / 100 : ℝ))
      (Real.arctan 1 + (5 / 100 : ℝ) * (1 / 2 : ℝ))
      (1 / 1000 : ℝ) := by
  unfold Approx
  rw [arctan_105_formula]
  rcases arctan_one_over_41_bounds with ⟨ht_lo, ht_hi⟩
  rw [abs_lt]
  constructor <;> nlinarith

theorem gap5 :
    Approx
      (Real.arctan 1 + (5 / 100 : ℝ) * (1 / 2 : ℝ))
      (8104 / 10000 : ℝ) (1 / 10000 : ℝ) := by
  unfold Approx
  rw [Real.arctan_one]
  rcases pi_d4_bounds with ⟨hpi_lo, hpi_hi⟩
  rw [abs_lt]
  constructor <;> nlinarith

theorem gap6 :
    Approx (Real.arctan (105 / 100 : ℝ))
      (8104 / 10000 : ℝ) (1 / 1000 : ℝ) := by
  unfold Approx
  rw [arctan_105_formula, Real.arctan_one]
  rcases pi_d4_bounds with ⟨hpi_lo, hpi_hi⟩
  rcases arctan_one_over_41_bounds with ⟨ht_lo, ht_hi⟩
  rw [abs_lt]
  constructor <;> nlinarith

end

end ProofGap.Exercise1101
