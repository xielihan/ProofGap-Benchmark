import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Filter.AtTopBot.Tendsto

namespace ProofGap.Exercise2738

noncomputable section

open Filter

def positiveTerm (x : ℝ) (n : ℕ) : ℝ :=
  (n : ℝ) / 2 ^ n * x ^ n

def negativeTerm (x : ℝ) (n : ℕ) : ℝ :=
  -((n : ℝ) / 2 ^ n) / x ^ n

def Splus (x : ℝ) : ℝ :=
  ∑' n : ℕ, positiveTerm x (n + 1)

def Sminus (x : ℝ) : ℝ :=
  ∑' n : ℕ, negativeTerm x (n + 1)

def LaurentSummableAt (x : ℝ) : Prop :=
  Summable (fun n : ℕ => positiveTerm x (n + 1)) ∧
    Summable (fun n : ℕ => negativeTerm x (n + 1))

def LaurentValue (x : ℝ) : ℝ :=
  Splus x + Sminus x

private theorem summable_linear_geometric_iff (r : ℝ) :
    Summable (fun n : ℕ => ((n + 1 : ℕ) : ℝ) * r ^ (n + 1)) ↔ |r| < 1 := by
  constructor
  · intro hsum
    by_contra hnot
    have hr : 1 ≤ |r| := le_of_not_gt hnot
    have hcast : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
    have hlarge : Tendsto
        (fun n : ℕ => ‖((n + 1 : ℕ) : ℝ) * r ^ (n + 1)‖) atTop atTop := by
      refine tendsto_atTop_mono' atTop ?_ hcast
      filter_upwards with n
      rw [Real.norm_eq_abs, abs_mul, abs_pow,
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((n + 1 : ℕ) : ℝ))]
      have hp : 1 ≤ |r| ^ (n + 1) := one_le_pow₀ hr
      nlinarith [show (0 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) by positivity]
    have hzero : Tendsto
        (fun n : ℕ => ‖((n + 1 : ℕ) : ℝ) * r ^ (n + 1)‖)
        atTop (nhds 0) := by
      simpa [Function.comp_def] using tendsto_norm.comp hsum.tendsto_atTop_zero
    exact not_tendsto_nhds_of_tendsto_atTop hlarge 0 hzero
  · intro hr
    have hs := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1
      (by simpa [Real.norm_eq_abs] using hr)
    simpa using
      (summable_nat_add_iff
        (f := fun n : ℕ => (n : ℝ) ^ 1 * r ^ n) 1).mpr hs

private theorem positiveTerm_series_eq (x : ℝ) :
    (fun n : ℕ => positiveTerm x (n + 1)) =
      fun n : ℕ => ((n + 1 : ℕ) : ℝ) * (x / 2) ^ (n + 1) := by
  funext n
  unfold positiveTerm
  rw [div_pow]
  push_cast
  ring

private theorem negativeTerm_series_eq (x : ℝ) :
    (fun n : ℕ => negativeTerm x (n + 1)) =
      fun n : ℕ => -(((n + 1 : ℕ) : ℝ) * (1 / (2 * x)) ^ (n + 1)) := by
  funext n
  unfold negativeTerm
  rw [div_pow, mul_pow]
  push_cast
  ring

private theorem splus_formula (x : ℝ) (hx : |x| < 2) :
    Splus x = 2 * x / (2 - x) ^ 2 := by
  let r : ℝ := x / 2
  have hr : ‖r‖ < 1 := by
    dsimp [r]
    rw [abs_div]
    norm_num
    linarith
  have hs : Summable (fun n : ℕ => (n : ℝ) * r ^ n) :=
    (summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 hr).congr
      (fun n => by simp)
  have hshift :
      (∑' n : ℕ, ((n + 1 : ℕ) : ℝ) * r ^ (n + 1)) =
        ∑' n : ℕ, (n : ℝ) * r ^ n := by
    simpa using hs.sum_add_tsum_nat_add 1
  have hx2 : 2 - x ≠ 0 := by
    intro h
    have : x = 2 := by linarith
    subst x
    norm_num at hx
  unfold Splus
  rw [positiveTerm_series_eq]
  rw [hshift, tsum_coe_mul_geometric_of_norm_lt_one hr]
  dsimp [r]
  field_simp [hx2]

private theorem first_shift_eq (x : ℝ) (hx : |x| < 2) :
    (∑' n : ℕ, ((n + 1 : ℕ) : ℝ) / 2 ^ (n + 2) * x ^ (n + 2)) =
      (x / 2) * Splus x := by
  have hs : Summable (fun n : ℕ => positiveTerm x (n + 1)) := by
    rw [positiveTerm_series_eq, summable_linear_geometric_iff]
    rw [abs_div]
    norm_num
    linarith
  unfold Splus
  rw [← hs.tsum_mul_left]
  apply tsum_congr
  intro n
  unfold positiveTerm
  push_cast
  field_simp
  ring

private theorem geometric_shift_sum (x : ℝ) (hx : |x| < 2) :
    (∑' n : ℕ, (x / 2) ^ (n + 1)) = x / (2 - x) := by
  have hr : ‖x / 2‖ < 1 := by
    rw [Real.norm_eq_abs, abs_div]
    norm_num
    linarith
  have hsum := tsum_geometric_of_norm_lt_one hr
  have hs := summable_geometric_of_norm_lt_one hr
  have hshift : (∑' n : ℕ, (x / 2) ^ (n + 1)) =
      (∑' n : ℕ, (x / 2) ^ n) - 1 := geom_series_succ (x / 2) hr
  rw [hshift, hsum]
  have hx2 : 2 - x ≠ 0 := by
    intro h
    have : x = 2 := by linarith
    subst x
    norm_num at hx
  field_simp [hx2]
  ring

theorem gap1 (x : ℝ) :
    Summable (fun n : ℕ => positiveTerm x (n + 1)) ↔ |x| < 2 := by
  rw [positiveTerm_series_eq, summable_linear_geometric_iff]
  rw [abs_div]
  norm_num
  constructor <;> intro h <;> linarith

theorem gap2 (x : ℝ) :
    Summable (fun n : ℕ => negativeTerm x (n + 1)) ↔
      x = 0 ∨ 1 / 2 < |x| := by
  rw [negativeTerm_series_eq]
  have hneg : Summable
      (fun n : ℕ => -(((n + 1 : ℕ) : ℝ) * (1 / (2 * x)) ^ (n + 1))) ↔
      Summable (fun n : ℕ => ((n + 1 : ℕ) : ℝ) * (1 / (2 * x)) ^ (n + 1)) := by
    constructor
    · intro h
      simpa using h.neg
    · intro h
      exact h.neg
  rw [hneg, summable_linear_geometric_iff]
  by_cases hx : x = 0
  · simp [hx]
  · have hxabs : 0 < |x| := abs_pos.mpr hx
    simp only [hx, false_or]
    rw [abs_div, abs_mul]
    norm_num [abs_of_pos hxabs]
    rw [mul_comm, ← div_eq_mul_inv, div_lt_one hxabs]

theorem gap3 (x : ℝ) :
    LaurentSummableAt x ↔ x = 0 ∨ (1 / 2 < |x| ∧ |x| < 2) := by
  unfold LaurentSummableAt
  rw [gap1, gap2]
  constructor
  · rintro ⟨hx2, hx0 | hx1⟩
    · exact Or.inl hx0
    · exact Or.inr ⟨hx1, hx2⟩
  · rintro (hx0 | ⟨hx1, hx2⟩)
    · subst x
      norm_num
    · exact ⟨hx2, Or.inr hx1⟩

theorem gap4 (x : ℝ) (hx₁ : 1 / 2 < |x|) (hx₂ : |x| < 2) :
    Sminus x = -Splus (1 / x) := by
  have hx0 : x ≠ 0 := by
    intro h
    subst x
    norm_num at hx₁
  unfold Sminus Splus
  rw [← tsum_neg]
  apply tsum_congr
  intro n
  unfold negativeTerm positiveTerm
  simp only [one_div]
  rw [inv_pow]
  field_simp [hx0]

theorem gap5 (x : ℝ) (hx : |x| < 2) :
    Splus x =
      (∑' n : ℕ, ((n + 1 : ℕ) : ℝ) / 2 ^ (n + 2) * x ^ (n + 2)) +
      (∑' n : ℕ, (x / 2) ^ (n + 1)) := by
  rw [first_shift_eq x hx, geometric_shift_sum x hx, splus_formula x hx]
  have hx2 : 2 - x ≠ 0 := by
    intro h
    have : x = 2 := by linarith
    subst x
    norm_num at hx
  field_simp [hx2]
  ring

theorem gap6 (x : ℝ) (hx : |x| < 2) :
    (∑' n : ℕ, ((n + 1 : ℕ) : ℝ) / 2 ^ (n + 2) * x ^ (n + 2)) =
      (x / 2) * Splus x := by
  exact first_shift_eq x hx

theorem gap7 (x : ℝ) (hx : |x| < 2) :
    Splus x = (x / 2) * Splus x + ∑' n : ℕ, (x / 2) ^ (n + 1) := by
  calc
    Splus x =
        (∑' n : ℕ, ((n + 1 : ℕ) : ℝ) / 2 ^ (n + 2) * x ^ (n + 2)) +
          (∑' n : ℕ, (x / 2) ^ (n + 1)) := gap5 x hx
    _ = (x / 2) * Splus x + ∑' n : ℕ, (x / 2) ^ (n + 1) := by
      rw [gap6 x hx]

theorem gap8 (x : ℝ) (hx : |x| < 2) :
    Splus x = (x / 2) * Splus x + x / (2 - x) := by
  calc
    Splus x = (x / 2) * Splus x +
        ∑' n : ℕ, (x / 2) ^ (n + 1) := gap7 x hx
    _ = (x / 2) * Splus x + x / (2 - x) := by
      rw [geometric_shift_sum x hx]

theorem gap9 (x : ℝ) (hx : |x| < 2) :
    Splus x = 2 * x / (2 - x) ^ 2 := by
  exact splus_formula x hx

theorem gap10 (x : ℝ) (hx : 1 / 2 < |x|) :
    Sminus x = -(2 * x) / (2 * x - 1) ^ 2 := by
  have hx0 : x ≠ 0 := by
    intro h
    subst x
    norm_num at hx
  have hinv : |1 / x| < 2 := by
    rw [abs_div]
    norm_num [abs_of_pos (abs_pos.mpr hx0)]
    rw [inv_eq_one_div]
    exact (div_lt_iff₀ (abs_pos.mpr hx0)).2 (by linarith)
  have hrel : Sminus x = -Splus (1 / x) := by
    unfold Sminus Splus
    rw [← tsum_neg]
    apply tsum_congr
    intro n
    unfold negativeTerm positiveTerm
    simp only [one_div]
    rw [inv_pow]
    field_simp [hx0]
  rw [hrel, gap9 (1 / x) hinv]
  have hden : 2 * x - 1 ≠ 0 := by
    intro h
    have : x = 1 / 2 := by linarith
    subst x
    norm_num at hx
  field_simp [hx0, hden]

theorem gap11 (x : ℝ) (hx₁ : 1 / 2 < |x|) (hx₂ : |x| < 2) :
    LaurentValue x = Splus x + Sminus x := by
  rfl

theorem gap12 (x : ℝ) (hx₁ : 1 / 2 < |x|) (hx₂ : |x| < 2) :
    Splus x + Sminus x =
      2 * x * (1 / (2 - x) ^ 2 - 1 / (2 * x - 1) ^ 2) := by
  rw [gap9 x hx₂, gap10 x hx₁]
  ring

theorem gap13 (x : ℝ) (hx₁ : 1 / 2 < |x|) (hx₂ : |x| < 2) :
    2 * x * (1 / (2 - x) ^ 2 - 1 / (2 * x - 1) ^ 2) =
      6 * x * (x ^ 2 - 1) / ((2 - x) ^ 2 * (2 * x - 1) ^ 2) := by
  have hx2 : 2 - x ≠ 0 := by
    intro h
    have : x = 2 := by linarith
    subst x
    norm_num at hx₂
  have hden : 2 * x - 1 ≠ 0 := by
    intro h
    have : x = 1 / 2 := by linarith
    subst x
    norm_num at hx₁
  field_simp [hx2, hden]
  ring

theorem gap14 (x : ℝ) (hx₁ : 1 / 2 < |x|) (hx₂ : |x| < 2) :
    LaurentValue x =
      6 * x * (x ^ 2 - 1) / ((2 - x) ^ 2 * (2 * x - 1) ^ 2) := by
  rw [gap11 x hx₁ hx₂, gap12 x hx₁ hx₂, gap13 x hx₁ hx₂]

end

end ProofGap.Exercise2738
