import ProofGapLean.Prelude.Analysis
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise786_3

noncomputable section

def signedCbrt (x : ℝ) : ℝ :=
  Real.sign x * Real.rpow |x| (1 / 3 : ℝ)

private theorem cube_le_cube_iff_of_nonneg {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    a ^ 3 ≤ b ^ 3 ↔ a ≤ b := by
  constructor
  · intro hc
    by_contra hab
    have hba : b < a := lt_of_not_ge hab
    have ha_pos : 0 < a := lt_of_le_of_lt hb hba
    have ha_sq : 0 < a ^ 2 := pow_pos ha_pos 2
    have hfactor : 0 < a ^ 2 + a * b + b ^ 2 := by
      nlinarith [ha_sq, mul_nonneg ha hb, sq_nonneg b]
    have hprod : 0 < (a - b) * (a ^ 2 + a * b + b ^ 2) :=
      mul_pos (sub_pos.mpr hba) hfactor
    have hid : a ^ 3 - b ^ 3 =
        (a - b) * (a ^ 2 + a * b + b ^ 2) := by ring
    nlinarith
  · intro hab
    have hfactor : 0 ≤ b ^ 2 + b * a + a ^ 2 :=
      add_nonneg
        (add_nonneg (sq_nonneg b) (mul_nonneg hb ha))
        (sq_nonneg a)
    have hprod : 0 ≤ (b - a) * (b ^ 2 + b * a + a ^ 2) :=
      mul_nonneg (sub_nonneg.mpr hab) hfactor
    have hid : b ^ 3 - a ^ 3 =
        (b - a) * (b ^ 2 + b * a + a ^ 2) := by ring
    nlinarith

private theorem nonneg_rpow_one_third_cubed (x : ℝ) (hx : 0 ≤ x) :
    (Real.rpow x (1 / 3 : ℝ)) ^ 3 = x := by
  calc
    (Real.rpow x (1 / 3 : ℝ)) ^ 3 =
        Real.rpow (Real.rpow x (1 / 3 : ℝ)) (3 : ℝ) :=
      (Real.rpow_natCast (Real.rpow x (1 / 3 : ℝ)) 3).symm
    _ = Real.rpow x ((1 / 3 : ℝ) * 3) :=
      (Real.rpow_mul hx (1 / 3 : ℝ) (3 : ℝ)).symm
    _ = Real.rpow x 1 := by norm_num
    _ = x := Real.rpow_one x

private theorem nonneg_cbrt_nonneg (x : ℝ) (hx : 0 ≤ x) :
    0 ≤ Real.cbrt x := by
  simpa [Real.cbrt] using (Real.rpow_nonneg hx (3 : ℝ)⁻¹)

private theorem nonneg_cbrt_cubed (x : ℝ) (hx : 0 ≤ x) :
    (Real.cbrt x) ^ 3 = x := by
  simpa [Real.cbrt, one_div] using nonneg_rpow_one_third_cubed x hx

private theorem signedCbrt_cubed (x : ℝ) :
    (signedCbrt x) ^ 3 = x := by
  rw [signedCbrt, mul_pow,
    nonneg_rpow_one_third_cubed |x| (abs_nonneg x)]
  rcases lt_trichotomy x 0 with hx | hx | hx
  · have hxne : x ≠ 0 := ne_of_lt hx
    have hxnp : ¬ 0 < x := not_lt.mpr hx.le
    have hs : Real.sign x = -1 := by
      simp [Real.sign, hx, hxne, hxnp]
    rw [hs, abs_of_neg hx]
    ring
  · subst x
    norm_num [Real.sign]
  · have hxne : x ≠ 0 := ne_of_gt hx
    have hxn : ¬ x < 0 := not_lt.mpr hx.le
    have hs : Real.sign x = 1 := by
      simp [Real.sign, hx, hxne, hxn]
    rw [hs, abs_of_pos hx]
    ring

theorem gap1 (y₁ y₂ : ℝ) (h : y₁ ≠ y₂) :
    |y₁ - y₂| = |(y₁ ^ 3 - y₂ ^ 3) / (y₁ ^ 2 + y₁ * y₂ + y₂ ^ 2)| := by
  have hden : y₁ ^ 2 + y₁ * y₂ + y₂ ^ 2 ≠ 0 := by
    intro hzero
    apply h
    nlinarith [sq_nonneg (y₁ + y₂), sq_nonneg (y₁ - y₂)]
  rw [show y₁ ^ 3 - y₂ ^ 3 =
      (y₁ - y₂) * (y₁ ^ 2 + y₁ * y₂ + y₂ ^ 2) by ring]
  simp [hden]
theorem gap2 (y₁ y₂ : ℝ) :
    |(y₁ ^ 3 - y₂ ^ 3) / (y₁ ^ 2 + y₁ * y₂ + y₂ ^ 2)| =
      |(y₁ ^ 3 - y₂ ^ 3) / ((3 / 4 : ℝ) * (y₁ + y₂) ^ 2 +
        (1 / 4 : ℝ) * (y₁ - y₂) ^ 2)| := by
  have hden :
      y₁ ^ 2 + y₁ * y₂ + y₂ ^ 2 =
        (3 / 4 : ℝ) * (y₁ + y₂) ^ 2 +
          (1 / 4 : ℝ) * (y₁ - y₂) ^ 2 := by
    ring
  rw [hden]
theorem gap3 (y₁ y₂ : ℝ) (h : y₁ ≠ y₂) :
    |(y₁ ^ 3 - y₂ ^ 3) / ((3 / 4 : ℝ) * (y₁ + y₂) ^ 2 +
      (1 / 4 : ℝ) * (y₁ - y₂) ^ 2)| ≤
      |y₁ ^ 3 - y₂ ^ 3| / ((1 / 4 : ℝ) * |y₁ - y₂| ^ 2) := by
  have habs : 0 < |y₁ - y₂| := abs_pos.mpr (sub_ne_zero.mpr h)
  have hD : 0 < (1 / 4 : ℝ) * |y₁ - y₂| ^ 2 :=
    mul_pos (by norm_num) (pow_pos habs 2)
  have hA : 0 ≤
      (3 / 4 : ℝ) * (y₁ + y₂) ^ 2 +
        (1 / 4 : ℝ) * (y₁ - y₂) ^ 2 :=
    add_nonneg
      (mul_nonneg (by norm_num) (sq_nonneg (y₁ + y₂)))
      (mul_nonneg (by norm_num) (sq_nonneg (y₁ - y₂)))
  have hDA :
      (1 / 4 : ℝ) * |y₁ - y₂| ^ 2 ≤
        (3 / 4 : ℝ) * (y₁ + y₂) ^ 2 +
          (1 / 4 : ℝ) * (y₁ - y₂) ^ 2 := by
    rw [sq_abs]
    nlinarith [sq_nonneg (y₁ + y₂)]
  have hApos : 0 <
      (3 / 4 : ℝ) * (y₁ + y₂) ^ 2 +
        (1 / 4 : ℝ) * (y₁ - y₂) ^ 2 :=
    lt_of_lt_of_le hD hDA
  rw [abs_div, abs_of_nonneg hA]
  apply (le_div_iff₀ hD).2
  calc
    |y₁ ^ 3 - y₂ ^ 3| /
          ((3 / 4 : ℝ) * (y₁ + y₂) ^ 2 +
            (1 / 4 : ℝ) * (y₁ - y₂) ^ 2) *
        ((1 / 4 : ℝ) * |y₁ - y₂| ^ 2) ≤
      |y₁ ^ 3 - y₂ ^ 3| /
          ((3 / 4 : ℝ) * (y₁ + y₂) ^ 2 +
            (1 / 4 : ℝ) * (y₁ - y₂) ^ 2) *
        ((3 / 4 : ℝ) * (y₁ + y₂) ^ 2 +
          (1 / 4 : ℝ) * (y₁ - y₂) ^ 2) :=
      mul_le_mul_of_nonneg_left hDA (div_nonneg (abs_nonneg _) hA)
    _ = |y₁ ^ 3 - y₂ ^ 3| := by
      exact div_mul_cancel₀ _ (ne_of_gt hApos)
theorem gap4 (y₁ y₂ : ℝ) (h : y₁ ≠ y₂) :
    |y₁ - y₂| ≤ |y₁ ^ 3 - y₂ ^ 3| / ((1 / 4 : ℝ) * |y₁ - y₂| ^ 2) := by
  calc
    |y₁ - y₂| =
        |(y₁ ^ 3 - y₂ ^ 3) /
          (y₁ ^ 2 + y₁ * y₂ + y₂ ^ 2)| := gap1 y₁ y₂ h
    _ = |(y₁ ^ 3 - y₂ ^ 3) /
          ((3 / 4 : ℝ) * (y₁ + y₂) ^ 2 +
            (1 / 4 : ℝ) * (y₁ - y₂) ^ 2)| := gap2 y₁ y₂
    _ ≤ |y₁ ^ 3 - y₂ ^ 3| /
          ((1 / 4 : ℝ) * |y₁ - y₂| ^ 2) := gap3 y₁ y₂ h
theorem gap5 (y₁ y₂ : ℝ) :
    (1 / 4 : ℝ) * |y₁ - y₂| ^ 3 ≤ |y₁ ^ 3 - y₂ ^ 3| := by
  by_cases h : y₁ = y₂
  · subst y₂
    norm_num
  · have habs : 0 < |y₁ - y₂| := abs_pos.mpr (sub_ne_zero.mpr h)
    have hden : 0 < (1 / 4 : ℝ) * |y₁ - y₂| ^ 2 :=
      mul_pos (by norm_num) (pow_pos habs 2)
    calc
      (1 / 4 : ℝ) * |y₁ - y₂| ^ 3 =
          |y₁ - y₂| * ((1 / 4 : ℝ) * |y₁ - y₂| ^ 2) := by ring
      _ ≤ |y₁ ^ 3 - y₂ ^ 3| :=
        (le_div_iff₀ hden).mp (gap4 y₁ y₂ h)
theorem gap6 (x₁ x₂ y₁ y₂ : ℝ) (h₁ : y₁ ^ 3 = x₁) (h₂ : y₂ ^ 3 = x₂) :
    |y₁ ^ 3 - y₂ ^ 3| = |x₁ - x₂| := by
  simpa [h₁, h₂]
theorem gap7 (x₁ x₂ y₁ y₂ : ℝ) (h₁ : y₁ ^ 3 = x₁) (h₂ : y₂ ^ 3 = x₂) :
    (1 / 4 : ℝ) * |y₁ - y₂| ^ 3 ≤ |x₁ - x₂| := by
  calc
    (1 / 4 : ℝ) * |y₁ - y₂| ^ 3 ≤
        |y₁ ^ 3 - y₂ ^ 3| := gap5 y₁ y₂
    _ = |x₁ - x₂| := gap6 x₁ x₂ y₁ y₂ h₁ h₂
theorem gap8 (x₁ x₂ y₁ y₂ : ℝ) (h₁ : y₁ ^ 3 = x₁) (h₂ : y₂ ^ 3 = x₂) :
    |y₁ - y₂| ≤ Real.cbrt (4 * |x₁ - x₂|) := by
  have hd : 0 ≤ |y₁ - y₂| := abs_nonneg _
  have harg : 0 ≤ 4 * |x₁ - x₂| :=
    mul_nonneg (by norm_num) (abs_nonneg _)
  have hz : 0 ≤ Real.cbrt (4 * |x₁ - x₂|) :=
    nonneg_cbrt_nonneg _ harg
  have hcbrt : (Real.cbrt (4 * |x₁ - x₂|)) ^ 3 =
      4 * |x₁ - x₂| := nonneg_cbrt_cubed _ harg
  apply (cube_le_cube_iff_of_nonneg hd hz).mp
  rw [hcbrt]
  have hg := gap7 x₁ x₂ y₁ y₂ h₁ h₂
  nlinarith
theorem gap9 (x₁ x₂ y₁ y₂ ε : ℝ) (hε : 0 < ε)
    (hxy : |y₁ - y₂| ≤ Real.cbrt (4 * |x₁ - x₂|))
    (h : 4 * |x₁ - x₂| < ε ^ 3) : |y₁ - y₂| < ε := by
  have harg : 0 ≤ 4 * |x₁ - x₂| :=
    mul_nonneg (by norm_num) (abs_nonneg _)
  have hz : 0 ≤ Real.cbrt (4 * |x₁ - x₂|) :=
    nonneg_cbrt_nonneg _ harg
  have hcbrt : (Real.cbrt (4 * |x₁ - x₂|)) ^ 3 =
      4 * |x₁ - x₂| := nonneg_cbrt_cubed _ harg
  have hzlt : Real.cbrt (4 * |x₁ - x₂|) < ε := by
    by_contra hn
    have hez : ε ≤ Real.cbrt (4 * |x₁ - x₂|) := le_of_not_gt hn
    have hcubes : ε ^ 3 ≤ (Real.cbrt (4 * |x₁ - x₂|)) ^ 3 :=
      (cube_le_cube_iff_of_nonneg hε.le hz).mpr hez
    rw [hcbrt] at hcubes
    linarith
  exact lt_of_le_of_lt hxy hzlt
theorem gap10 (x₁ x₂ ε : ℝ) (hε : 0 < ε)
    (h : |x₁ - x₂| < ε ^ 3 / 4) : 4 * |x₁ - x₂| < ε ^ 3 := by
  nlinarith
theorem gap11 (x₁ x₂ y₁ y₂ ε : ℝ) (hε : 0 < ε)
    (h₁ : y₁ ^ 3 = x₁) (h₂ : y₂ ^ 3 = x₂)
    (h : |x₁ - x₂| < ε ^ 3 / 4) : |y₁ - y₂| < ε := by
  exact gap9 x₁ x₂ y₁ y₂ ε hε
    (gap8 x₁ x₂ y₁ y₂ h₁ h₂)
    (gap10 x₁ x₂ ε hε h)
theorem gap12 (ε δ x₁ x₂ : ℝ) (hε : 0 < ε) (hδ : 0 < δ)
    (hδ' : δ ≤ ε ^ 3 / 4) (hx : |x₁ - x₂| < δ) :
    |signedCbrt x₁ - signedCbrt x₂| < ε := by
  have hlt : |x₁ - x₂| < ε ^ 3 / 4 := lt_of_lt_of_le hx hδ'
  have h₁ : (signedCbrt x₁) ^ 3 = x₁ := signedCbrt_cubed x₁
  have h₂ : (signedCbrt x₂) ^ 3 = x₂ := signedCbrt_cubed x₂
  exact gap11 x₁ x₂ (signedCbrt x₁) (signedCbrt x₂) ε hε h₁ h₂ hlt
theorem gap13 (δ : ℝ) (hδ : 0 < δ) (hδ' : δ ≤ (0.001 : ℝ) ^ 3 / 4)
    (x₁ x₂ : ℝ) (hx : |x₁ - x₂| < δ) :
    |signedCbrt x₁ - signedCbrt x₂| < 0.001 := by
  exact gap12 (0.001 : ℝ) δ x₁ x₂ (by norm_num) hδ hδ' hx
theorem gap14 (ε : ℝ) (hε : 0 < ε) :
    ∃ δ > 0, ∀ x₁ x₂ : ℝ, x₁ ∈ Set.Icc (-10 : ℝ) 10 →
      x₂ ∈ Set.Icc (-10 : ℝ) 10 →
      |x₁ - x₂| < δ → |signedCbrt x₁ - signedCbrt x₂| < ε := by
  have hδ : 0 < ε ^ 3 / 4 := div_pos (pow_pos hε 3) (by norm_num)
  refine ⟨ε ^ 3 / 4, hδ, ?_⟩
  intro x₁ x₂ hx₁ hx₂ hx
  exact gap12 ε (ε ^ 3 / 4) x₁ x₂ hε hδ le_rfl hx

end
end ProofGap.Exercise786_3
