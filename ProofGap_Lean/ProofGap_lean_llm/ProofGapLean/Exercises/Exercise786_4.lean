import ProofGapLean.Prelude.Elementary
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise786_4

noncomputable section

def cubeRoot (x : ℝ) : ℝ := Real.sign x * Real.rpow |x| (1 / 3 : ℝ)
def Modulus (δ ε : ℝ) : Prop :=
  ∀ x₁ ∈ Set.Icc (-10 : ℝ) 10, ∀ x₂ ∈ Set.Icc (-10 : ℝ) 10,
    |x₁ - x₂| < δ → |cubeRoot x₁ - cubeRoot x₂| < ε

private theorem cubeRoot_facts (x : ℝ) :
    cubeRoot x ^ 3 = x ∧ (0 ≤ x → 0 ≤ cubeRoot x) := by
  have hpow (t : ℝ) (ht : 0 ≤ t) :
      Real.rpow t (1 / 3 : ℝ) ^ 3 = t := by
    have hnat :
        Real.rpow (Real.rpow t (1 / 3 : ℝ)) (3 : ℝ) =
          Real.rpow t (1 / 3 : ℝ) ^ 3 := by
      exact Real.rpow_natCast (Real.rpow t (1 / 3 : ℝ)) 3
    calc
      Real.rpow t (1 / 3 : ℝ) ^ 3 =
          Real.rpow (Real.rpow t (1 / 3 : ℝ)) (3 : ℝ) := hnat.symm
      _ = Real.rpow t ((1 / 3 : ℝ) * 3) := (Real.rpow_mul ht _ _).symm
      _ = t := by norm_num
  rcases lt_trichotomy x 0 with hx | hx | hx
  · have hs : Real.sign x = -1 := by
      simp [Real.sign, hx]
    have hform : cubeRoot x = -Real.rpow (-x) (1 / 3 : ℝ) := by
      rw [cubeRoot, hs, abs_of_neg hx]
      ring
    constructor
    · rw [hform]
      nlinarith [hpow (-x) (by linarith)]
    · intro hx0
      linarith
  · subst x
    simp [cubeRoot, Real.sign]
  · have hxn : ¬x < 0 := not_lt_of_ge (le_of_lt hx)
    have hs : Real.sign x = 1 := by
      simp [Real.sign, hx, hxn]
    have hform : cubeRoot x = Real.rpow x (1 / 3 : ℝ) := by
      rw [cubeRoot, hs, abs_of_pos hx]
      ring
    constructor
    · rw [hform]
      exact hpow x (le_of_lt hx)
    · intro _
      rw [hform]
      exact (Real.rpow_pos_of_pos hx _).le

theorem gap1 (y₁ y₂ : ℝ) (hne : y₁ ≠ y₂) :
    |y₁ - y₂| = |(y₁ ^ 3 - y₂ ^ 3) / (y₁ ^ 2 + y₁ * y₂ + y₂ ^ 2)| := by
  have hsub : y₁ - y₂ ≠ 0 := sub_ne_zero.mpr hne
  have hden : y₁ ^ 2 + y₁ * y₂ + y₂ ^ 2 ≠ 0 := by
    intro hz
    have hs : 0 ≤ (y₁ + y₂) ^ 2 := sq_nonneg (y₁ + y₂)
    have hd : 0 ≤ (y₁ - y₂) ^ 2 := sq_nonneg (y₁ - y₂)
    have hid :
        y₁ ^ 2 + y₁ * y₂ + y₂ ^ 2 =
          (3 / 4 : ℝ) * (y₁ + y₂) ^ 2 + (1 / 4 : ℝ) * (y₁ - y₂) ^ 2 := by
      ring
    rw [hid] at hz
    have hzero : y₁ - y₂ = 0 := by
      nlinarith
    exact hsub hzero
  have hfactor :
      y₁ ^ 3 - y₂ ^ 3 =
        (y₁ - y₂) * (y₁ ^ 2 + y₁ * y₂ + y₂ ^ 2) := by
    ring
  rw [hfactor]
  simp [hden]
theorem gap2 (y₁ y₂ : ℝ) (hne : y₁ ≠ y₂) :
    |(y₁ ^ 3 - y₂ ^ 3) / (y₁ ^ 2 + y₁ * y₂ + y₂ ^ 2)| =
      |(y₁ ^ 3 - y₂ ^ 3) /
        ((3 / 4 : ℝ) * (y₁ + y₂) ^ 2 + (1 / 4 : ℝ) * (y₁ - y₂) ^ 2)| := by
  have hden :
      y₁ ^ 2 + y₁ * y₂ + y₂ ^ 2 =
        (3 / 4 : ℝ) * (y₁ + y₂) ^ 2 + (1 / 4 : ℝ) * (y₁ - y₂) ^ 2 := by
    ring
  rw [hden]
theorem gap3 (y₁ y₂ : ℝ) (hne : y₁ ≠ y₂) :
    |(y₁ ^ 3 - y₂ ^ 3) /
        ((3 / 4 : ℝ) * (y₁ + y₂) ^ 2 + (1 / 4 : ℝ) * (y₁ - y₂) ^ 2)| ≤
      |y₁ ^ 3 - y₂ ^ 3| / ((1 / 4 : ℝ) * |y₁ - y₂| ^ 2) := by
  have habs : 0 < |y₁ - y₂| := abs_pos.mpr (sub_ne_zero.mpr hne)
  have hcpos : 0 < (1 / 4 : ℝ) * |y₁ - y₂| ^ 2 :=
    mul_pos (by norm_num) (pow_pos habs 2)
  have hcD :
      (1 / 4 : ℝ) * |y₁ - y₂| ^ 2 ≤
        (3 / 4 : ℝ) * (y₁ + y₂) ^ 2 + (1 / 4 : ℝ) * (y₁ - y₂) ^ 2 := by
    rw [sq_abs]
    nlinarith [sq_nonneg (y₁ + y₂)]
  have hDpos :
      0 < (3 / 4 : ℝ) * (y₁ + y₂) ^ 2 + (1 / 4 : ℝ) * (y₁ - y₂) ^ 2 :=
    lt_of_lt_of_le hcpos hcD
  rw [abs_div, abs_of_pos hDpos]
  apply (div_le_div_iff₀ hDpos hcpos).2
  exact mul_le_mul_of_nonneg_left hcD (abs_nonneg (y₁ ^ 3 - y₂ ^ 3))
theorem gap4 (y₁ y₂ : ℝ) (hne : y₁ ≠ y₂) :
    |y₁ - y₂| ≤ |y₁ ^ 3 - y₂ ^ 3| / ((1 / 4 : ℝ) * |y₁ - y₂| ^ 2) := by
  calc
    |y₁ - y₂| =
        |(y₁ ^ 3 - y₂ ^ 3) / (y₁ ^ 2 + y₁ * y₂ + y₂ ^ 2)| :=
      gap1 y₁ y₂ hne
    _ =
        |(y₁ ^ 3 - y₂ ^ 3) /
          ((3 / 4 : ℝ) * (y₁ + y₂) ^ 2 + (1 / 4 : ℝ) * (y₁ - y₂) ^ 2)| :=
      gap2 y₁ y₂ hne
    _ ≤ |y₁ ^ 3 - y₂ ^ 3| / ((1 / 4 : ℝ) * |y₁ - y₂| ^ 2) :=
      gap3 y₁ y₂ hne
theorem gap5 (y₁ y₂ : ℝ) :
    (1 / 4 : ℝ) * |y₁ - y₂| ^ 3 ≤ |y₁ ^ 3 - y₂ ^ 3| := by
  by_cases hne : y₁ ≠ y₂
  · have habs : 0 < |y₁ - y₂| := abs_pos.mpr (sub_ne_zero.mpr hne)
    have hden : 0 < (1 / 4 : ℝ) * |y₁ - y₂| ^ 2 :=
      mul_pos (by norm_num) (pow_pos habs 2)
    have hm :
        |y₁ - y₂| * ((1 / 4 : ℝ) * |y₁ - y₂| ^ 2) ≤
          |y₁ ^ 3 - y₂ ^ 3| :=
      (le_div_iff₀ hden).mp (gap4 y₁ y₂ hne)
    calc
      (1 / 4 : ℝ) * |y₁ - y₂| ^ 3 =
          |y₁ - y₂| * ((1 / 4 : ℝ) * |y₁ - y₂| ^ 2) := by ring
      _ ≤ |y₁ ^ 3 - y₂ ^ 3| := hm
  · have heq : y₁ = y₂ := not_ne_iff.mp hne
    simp [heq]

/-- Restore the omitted equations `xᵢ=yᵢ³`. -/
theorem gap6 (y₁ y₂ x₁ x₂ : ℝ) (hx₁ : x₁ = y₁ ^ 3) (hx₂ : x₂ = y₂ ^ 3) :
    |y₁ ^ 3 - y₂ ^ 3| = |x₁ - x₂| := by
  simp [hx₁, hx₂]
theorem gap7 (y₁ y₂ x₁ x₂ : ℝ) (hx₁ : x₁ = y₁ ^ 3) (hx₂ : x₂ = y₂ ^ 3) :
    (1 / 4 : ℝ) * |y₁ - y₂| ^ 3 ≤ |x₁ - x₂| := by
  calc
    (1 / 4 : ℝ) * |y₁ - y₂| ^ 3 ≤ |y₁ ^ 3 - y₂ ^ 3| := gap5 y₁ y₂
    _ = |x₁ - x₂| := gap6 y₁ y₂ x₁ x₂ hx₁ hx₂
theorem gap8 (y₁ y₂ x₁ x₂ : ℝ)
    (h : (1 / 4 : ℝ) * |y₁ - y₂| ^ 3 ≤ |x₁ - x₂|) :
    |y₁ - y₂| ≤ cubeRoot (4 * |x₁ - x₂|) := by
  have hb : 0 ≤ 4 * |x₁ - x₂| :=
    mul_nonneg (by norm_num) (abs_nonneg (x₁ - x₂))
  have hz : 0 ≤ cubeRoot (4 * |x₁ - x₂|) :=
    (cubeRoot_facts (4 * |x₁ - x₂|)).2 hb
  have hz3 : cubeRoot (4 * |x₁ - x₂|) ^ 3 = 4 * |x₁ - x₂| :=
    (cubeRoot_facts (4 * |x₁ - x₂|)).1
  have ha : 0 ≤ |y₁ - y₂| := abs_nonneg (y₁ - y₂)
  have hcube : |y₁ - y₂| ^ 3 ≤ 4 * |x₁ - x₂| := by
    nlinarith
  by_contra hn
  have hza : cubeRoot (4 * |x₁ - x₂|) < |y₁ - y₂| := lt_of_not_ge hn
  have ha0 : 0 < |y₁ - y₂| := lt_of_le_of_lt hz hza
  have hcross :
      0 ≤ |y₁ - y₂| * cubeRoot (4 * |x₁ - x₂|) :=
    mul_nonneg ha hz
  have hq :
      0 < |y₁ - y₂| ^ 2 +
          |y₁ - y₂| * cubeRoot (4 * |x₁ - x₂|) +
          cubeRoot (4 * |x₁ - x₂|) ^ 2 := by
    nlinarith [pow_pos ha0 2, sq_nonneg (cubeRoot (4 * |x₁ - x₂|))]
  have hp :
      0 < (|y₁ - y₂| - cubeRoot (4 * |x₁ - x₂|)) *
          (|y₁ - y₂| ^ 2 +
            |y₁ - y₂| * cubeRoot (4 * |x₁ - x₂|) +
            cubeRoot (4 * |x₁ - x₂|) ^ 2) :=
    mul_pos (sub_pos.mpr hza) hq
  have hid :
      |y₁ - y₂| ^ 3 - cubeRoot (4 * |x₁ - x₂|) ^ 3 =
        (|y₁ - y₂| - cubeRoot (4 * |x₁ - x₂|)) *
          (|y₁ - y₂| ^ 2 +
            |y₁ - y₂| * cubeRoot (4 * |x₁ - x₂|) +
            cubeRoot (4 * |x₁ - x₂|) ^ 2) := by
    ring
  nlinarith

/-- Add the missing bound from gap 8. -/
theorem gap9 (x₁ x₂ y₁ y₂ ε : ℝ) (hε : 0 < ε)
    (hy : |y₁ - y₂| ≤ cubeRoot (4 * |x₁ - x₂|))
    (hx : 4 * |x₁ - x₂| < ε ^ 3) : |y₁ - y₂| < ε := by
  have hb : 0 ≤ 4 * |x₁ - x₂| :=
    mul_nonneg (by norm_num) (abs_nonneg (x₁ - x₂))
  have hz : 0 ≤ cubeRoot (4 * |x₁ - x₂|) :=
    (cubeRoot_facts (4 * |x₁ - x₂|)).2 hb
  have hz3 : cubeRoot (4 * |x₁ - x₂|) ^ 3 = 4 * |x₁ - x₂| :=
    (cubeRoot_facts (4 * |x₁ - x₂|)).1
  have hzlt : cubeRoot (4 * |x₁ - x₂|) < ε := by
    by_contra hn
    have hez : ε ≤ cubeRoot (4 * |x₁ - x₂|) := le_of_not_gt hn
    have he0 : 0 ≤ ε := le_of_lt hε
    have hcross : 0 ≤ cubeRoot (4 * |x₁ - x₂|) * ε :=
      mul_nonneg hz he0
    have hq :
        0 ≤ cubeRoot (4 * |x₁ - x₂|) ^ 2 +
            cubeRoot (4 * |x₁ - x₂|) * ε + ε ^ 2 := by
      nlinarith [sq_nonneg (cubeRoot (4 * |x₁ - x₂|)), sq_nonneg ε]
    have hp :
        0 ≤ (cubeRoot (4 * |x₁ - x₂|) - ε) *
            (cubeRoot (4 * |x₁ - x₂|) ^ 2 +
              cubeRoot (4 * |x₁ - x₂|) * ε + ε ^ 2) :=
      mul_nonneg (sub_nonneg.mpr hez) hq
    have hid :
        cubeRoot (4 * |x₁ - x₂|) ^ 3 - ε ^ 3 =
          (cubeRoot (4 * |x₁ - x₂|) - ε) *
            (cubeRoot (4 * |x₁ - x₂|) ^ 2 +
              cubeRoot (4 * |x₁ - x₂|) * ε + ε ^ 2) := by
      ring
    nlinarith
  exact lt_of_le_of_lt hy hzlt
theorem gap10 (x₁ x₂ ε : ℝ) (hε : 0 < ε)
    (hx : |x₁ - x₂| < ε ^ 3 / 4) : 4 * |x₁ - x₂| < ε ^ 3 := by
  nlinarith

/-- Restore `xᵢ=yᵢ³`. -/
theorem gap11 (x₁ x₂ y₁ y₂ ε : ℝ) (hε : 0 < ε)
    (hx₁ : x₁ = y₁ ^ 3) (hx₂ : x₂ = y₂ ^ 3)
    (hx : |x₁ - x₂| < ε ^ 3 / 4) : |y₁ - y₂| < ε := by
  have hbound :
      (1 / 4 : ℝ) * |y₁ - y₂| ^ 3 ≤ |x₁ - x₂| :=
    gap7 y₁ y₂ x₁ x₂ hx₁ hx₂
  have hyroot : |y₁ - y₂| ≤ cubeRoot (4 * |x₁ - x₂|) :=
    gap8 y₁ y₂ x₁ x₂ hbound
  have hxcube : 4 * |x₁ - x₂| < ε ^ 3 :=
    gap10 x₁ x₂ ε hε hx
  exact gap9 x₁ x₂ y₁ y₂ ε hε hyroot hxcube
theorem gap12 (δ ε x₁ x₂ : ℝ) (hδ0 : 0 < δ)
    (hδ : δ < ε ^ 3 / 4) (hmod : Modulus δ ε)
    (hx : |x₁ - x₂| < δ) (hx₁ : x₁ ∈ Set.Icc (-10 : ℝ) 10)
    (hx₂ : x₂ ∈ Set.Icc (-10 : ℝ) 10) :
    |cubeRoot x₁ - cubeRoot x₂| < ε := by
  exact hmod x₁ hx₁ x₂ hx₂ hx

/-- Reverse the false necessity claim to its valid sufficient direction. -/
theorem gap13 (δ ε : ℝ) (hε0 : 0 < ε) (hδ0 : 0 < δ)
    (hδ : δ < ε ^ 3 / 4) : Modulus δ ε := by
  intro x₁ hx₁ x₂ hx₂ hxx
  have hx : |x₁ - x₂| < ε ^ 3 / 4 := lt_trans hxx hδ
  exact gap11 x₁ x₂ (cubeRoot x₁) (cubeRoot x₂) ε hε0
    (cubeRoot_facts x₁).1.symm (cubeRoot_facts x₂).1.symm hx

/-- The source biconditional is not a sharp characterization; retain sufficiency. -/
theorem gap14 (δ ε : ℝ) :
    δ ∈ {d : ℝ | 0 < d ∧ d < ε ^ 3 / 4 ∧ ε ≤ 1} → Modulus δ ε := by
  rintro ⟨hδ0, hδ, hε1⟩
  have hq : 0 < ε ^ 3 / 4 := lt_trans hδ0 hδ
  have he3 : 0 < ε ^ 3 := by
    nlinarith
  have hε0 : 0 < ε := by
    by_contra hn
    have he : ε ≤ 0 := le_of_not_gt hn
    have hm : ε * ε ^ 2 ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg he (sq_nonneg ε)
    have hid : ε ^ 3 = ε * ε ^ 2 := by ring
    nlinarith
  exact gap13 δ ε hε0 hδ0 hδ

end

end ProofGap.Exercise786_4
