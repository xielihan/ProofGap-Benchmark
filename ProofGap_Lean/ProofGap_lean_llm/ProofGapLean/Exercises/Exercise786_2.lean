import ProofGapLean.Prelude.Elementary
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise786_2

noncomputable section

noncomputable def signedCbrt (x : ℝ) : ℝ :=
  if 0 ≤ x then Real.rpow x (1 / 3 : ℝ)
  else -Real.rpow (-x) (1 / 3 : ℝ)

def UCCondition (δ ε : ℝ) : Prop :=
  ∀ x₁ ∈ Set.Icc (-10 : ℝ) 10, ∀ x₂ ∈ Set.Icc (-10 : ℝ) 10,
    |x₁ - x₂| < δ → |signedCbrt x₁ - signedCbrt x₂| < ε

/-- Exercise 786_2, gap 1; discard the unrelated repeated uniform-continuity premise. -/
private theorem rpow_one_third_cubed (x : ℝ) (hx : 0 ≤ x) :
    Real.rpow x (1 / 3 : ℝ) ^ 3 = x := by
  calc
    Real.rpow x (1 / 3 : ℝ) ^ 3 =
        Real.rpow (Real.rpow x (1 / 3 : ℝ)) (↑(3 : ℕ) : ℝ) := by
      exact (Real.rpow_natCast (Real.rpow x (1 / 3 : ℝ)) 3).symm
    _ = Real.rpow x ((1 / 3 : ℝ) * 3) := by
      exact (Real.rpow_mul hx (1 / 3 : ℝ) (3 : ℝ)).symm
    _ = x := by
      norm_num

private theorem signedCbrt_cubed (x : ℝ) : signedCbrt x ^ 3 = x := by
  unfold signedCbrt
  split_ifs with hx
  · exact rpow_one_third_cubed x hx
  · have hnx : 0 ≤ -x := by linarith
    have hr := rpow_one_third_cubed (-x) hnx
    nlinarith

private theorem cbrt_eq_rpow_of_nonneg (x : ℝ) (hx : 0 ≤ x) :
    Real.cbrt x = Real.rpow x (1 / 3 : ℝ) := by
  by_cases hx0 : x = 0
  · subst x
    norm_num [Real.cbrt]
  · have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
    simp [Real.cbrt, hx, hxpos, one_div]

theorem gap1 (y₁ y₂ : ℝ) (hne : y₁ ≠ y₂) :
    |y₁ - y₂| =
      |(y₁ ^ 3 - y₂ ^ 3) / (y₁ ^ 2 + y₁ * y₂ + y₂ ^ 2)| := by
  have hden : y₁ ^ 2 + y₁ * y₂ + y₂ ^ 2 ≠ 0 := by
    intro hz
    apply hne
    nlinarith [sq_nonneg (y₁ + y₂), sq_nonneg (y₁ - y₂)]
  have hfactor :
      y₁ ^ 3 - y₂ ^ 3 =
        (y₁ - y₂) * (y₁ ^ 2 + y₁ * y₂ + y₂ ^ 2) := by
    ring
  have hquot :
      (y₁ ^ 3 - y₂ ^ 3) / (y₁ ^ 2 + y₁ * y₂ + y₂ ^ 2) = y₁ - y₂ :=
    (div_eq_iff hden).2 hfactor
  rw [hquot]

/-- Exercise 786_2, gap 2. -/
theorem gap2 (y₁ y₂ : ℝ) :
    |(y₁ ^ 3 - y₂ ^ 3) / (y₁ ^ 2 + y₁ * y₂ + y₂ ^ 2)| =
      |(y₁ ^ 3 - y₂ ^ 3) /
        ((3 / 4 : ℝ) * (y₁ + y₂) ^ 2 + (1 / 4 : ℝ) * (y₁ - y₂) ^ 2)| := by
  have hden :
      y₁ ^ 2 + y₁ * y₂ + y₂ ^ 2 =
        (3 / 4 : ℝ) * (y₁ + y₂) ^ 2 + (1 / 4 : ℝ) * (y₁ - y₂) ^ 2 := by
    ring
  rw [hden]

/-- Exercise 786_2, gap 3; retain the needed nonzero difference. -/
theorem gap3 (y₁ y₂ : ℝ) (hne : y₁ ≠ y₂) :
    |(y₁ ^ 3 - y₂ ^ 3) /
        ((3 / 4 : ℝ) * (y₁ + y₂) ^ 2 + (1 / 4 : ℝ) * (y₁ - y₂) ^ 2)| ≤
      |y₁ ^ 3 - y₂ ^ 3| / ((1 / 4 : ℝ) * |y₁ - y₂| ^ 2) := by
  have habs : 0 < |y₁ - y₂| := abs_pos.mpr (sub_ne_zero.mpr hne)
  have hB : 0 < (1 / 4 : ℝ) * |y₁ - y₂| ^ 2 :=
    mul_pos (by norm_num) (pow_pos habs 2)
  have hle :
      (1 / 4 : ℝ) * |y₁ - y₂| ^ 2 ≤
        (3 / 4 : ℝ) * (y₁ + y₂) ^ 2 + (1 / 4 : ℝ) * (y₁ - y₂) ^ 2 := by
    rw [sq_abs]
    nlinarith [sq_nonneg (y₁ + y₂)]
  have hA :
      0 < (3 / 4 : ℝ) * (y₁ + y₂) ^ 2 + (1 / 4 : ℝ) * (y₁ - y₂) ^ 2 :=
    lt_of_lt_of_le hB hle
  rw [abs_div, abs_of_pos hA]
  apply (le_div_iff₀ hB).2
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ hA).2
  exact mul_le_mul_of_nonneg_left hle (abs_nonneg _)

/-- Exercise 786_2, gap 4. -/
theorem gap4 (y₁ y₂ : ℝ) (hne : y₁ ≠ y₂) :
    |y₁ - y₂| ≤
      |y₁ ^ 3 - y₂ ^ 3| / ((1 / 4 : ℝ) * |y₁ - y₂| ^ 2) := by
  calc
    |y₁ - y₂| =
        |(y₁ ^ 3 - y₂ ^ 3) / (y₁ ^ 2 + y₁ * y₂ + y₂ ^ 2)| :=
      gap1 y₁ y₂ hne
    _ =
        |(y₁ ^ 3 - y₂ ^ 3) /
          ((3 / 4 : ℝ) * (y₁ + y₂) ^ 2 + (1 / 4 : ℝ) * (y₁ - y₂) ^ 2)| :=
      gap2 y₁ y₂
    _ ≤ |y₁ ^ 3 - y₂ ^ 3| / ((1 / 4 : ℝ) * |y₁ - y₂| ^ 2) :=
      gap3 y₁ y₂ hne

/-- Exercise 786_2, gap 5; remove the irrelevant repeated premise. -/
theorem gap5 (y₁ y₂ : ℝ) :
    (1 / 4 : ℝ) * |y₁ - y₂| ^ 3 ≤ |y₁ ^ 3 - y₂ ^ 3| := by
  by_cases hne : y₁ ≠ y₂
  · have habs : 0 < |y₁ - y₂| := abs_pos.mpr (sub_ne_zero.mpr hne)
    have hden : 0 < (1 / 4 : ℝ) * |y₁ - y₂| ^ 2 :=
      mul_pos (by norm_num) (pow_pos habs 2)
    have hmul :
        |y₁ - y₂| * ((1 / 4 : ℝ) * |y₁ - y₂| ^ 2) ≤
          |y₁ ^ 3 - y₂ ^ 3| :=
      (le_div_iff₀ hden).1 (gap4 y₁ y₂ hne)
    calc
      (1 / 4 : ℝ) * |y₁ - y₂| ^ 3 =
          |y₁ - y₂| * ((1 / 4 : ℝ) * |y₁ - y₂| ^ 2) := by ring
      _ ≤ |y₁ ^ 3 - y₂ ^ 3| := hmul
  · have heq : y₁ = y₂ := by simpa only [not_ne_iff] using hne
    subst y₂
    norm_num

/-- Exercise 786_2, gap 6; add the omitted cube-root relations. -/
theorem gap6 (y₁ y₂ x₁ x₂ : ℝ) (hy₁ : y₁ ^ 3 = x₁) (hy₂ : y₂ ^ 3 = x₂) :
    |y₁ ^ 3 - y₂ ^ 3| = |x₁ - x₂| := by
  simp only [hy₁, hy₂]

/-- Exercise 786_2, gap 7; add the omitted cube-root relations. -/
theorem gap7 (y₁ y₂ x₁ x₂ : ℝ) (hy₁ : y₁ ^ 3 = x₁) (hy₂ : y₂ ^ 3 = x₂) :
    (1 / 4 : ℝ) * |y₁ - y₂| ^ 3 ≤ |x₁ - x₂| := by
  calc
    (1 / 4 : ℝ) * |y₁ - y₂| ^ 3 ≤ |y₁ ^ 3 - y₂ ^ 3| := gap5 y₁ y₂
    _ = |x₁ - x₂| := gap6 y₁ y₂ x₁ x₂ hy₁ hy₂

/-- Exercise 786_2, gap 8; add the omitted cube-root relations. -/
theorem gap8 (y₁ y₂ x₁ x₂ : ℝ) (hy₁ : y₁ ^ 3 = x₁) (hy₂ : y₂ ^ 3 = x₂) :
    |y₁ - y₂| ≤ Real.cbrt (4 * |x₁ - x₂|) := by
  have hpow : |y₁ - y₂| ^ 3 ≤ 4 * |x₁ - x₂| := by
    nlinarith [gap7 y₁ y₂ x₁ x₂ hy₁ hy₂]
  have harg : 0 ≤ 4 * |x₁ - x₂| :=
    mul_nonneg (by norm_num) (abs_nonneg _)
  let r := Real.rpow (4 * |x₁ - x₂|) (1 / 3 : ℝ)
  have hrcube : r ^ 3 = 4 * |x₁ - x₂| := by
    dsimp [r]
    exact rpow_one_third_cubed (4 * |x₁ - x₂|) harg
  have hrnonneg : 0 ≤ r := by
    by_contra hnonneg
    have hrneg : r < 0 := lt_of_not_ge hnonneg
    have hrsq : 0 < r * r := mul_pos_of_neg_of_neg hrneg hrneg
    have hrcubeneg : r ^ 3 < 0 := by
      calc
        r ^ 3 = (r * r) * r := by ring
        _ < 0 := mul_neg_of_pos_of_neg hrsq hrneg
    rw [hrcube] at hrcubeneg
    exact (not_lt_of_ge harg) hrcubeneg
  have hbound : |y₁ - y₂| ≤ r := by
    by_contra hle
    have hra : r < |y₁ - y₂| := lt_of_not_ge hle
    have ha : 0 < |y₁ - y₂| := lt_of_le_of_lt hrnonneg hra
    have hquad :
        0 < |y₁ - y₂| ^ 2 + |y₁ - y₂| * r + r ^ 2 := by
      nlinarith [sq_nonneg r]
    have hprod :
        0 < (|y₁ - y₂| - r) *
          (|y₁ - y₂| ^ 2 + |y₁ - y₂| * r + r ^ 2) :=
      mul_pos (sub_pos.mpr hra) hquad
    nlinarith
  rw [cbrt_eq_rpow_of_nonneg (4 * |x₁ - x₂|) harg]
  exact hbound

/-- Exercise 786_2, gap 9; add the omitted cube-root relations. -/
theorem gap9 (y₁ y₂ x₁ x₂ ε : ℝ) (hε : 0 < ε)
    (hy₁ : y₁ ^ 3 = x₁) (hy₂ : y₂ ^ 3 = x₂)
    (hδ : 4 * |x₁ - x₂| < ε ^ 3) :
    |y₁ - y₂| < ε := by
  have hpow : |y₁ - y₂| ^ 3 < ε ^ 3 := by
    nlinarith [gap7 y₁ y₂ x₁ x₂ hy₁ hy₂]
  by_contra hlt
  have hεa : ε ≤ |y₁ - y₂| := le_of_not_gt hlt
  have ha2 : 0 ≤ |y₁ - y₂| ^ 2 := sq_nonneg _
  have haε : 0 ≤ |y₁ - y₂| * ε :=
    mul_nonneg (abs_nonneg _) hε.le
  have hε2 : 0 < ε ^ 2 := pow_pos hε 2
  have hquad :
      0 < |y₁ - y₂| ^ 2 + |y₁ - y₂| * ε + ε ^ 2 := by
    nlinarith
  have hprod :
      0 ≤ (|y₁ - y₂| - ε) *
          (|y₁ - y₂| ^ 2 + |y₁ - y₂| * ε + ε ^ 2) :=
    mul_nonneg (sub_nonneg.mpr hεa) hquad.le
  nlinarith

/-- Exercise 786_2, gap 10. -/
theorem gap10 (x₁ x₂ ε : ℝ) (hε : 0 < ε)
    (hδ : |x₁ - x₂| < ε ^ 3 / 4) :
    4 * |x₁ - x₂| < ε ^ 3 := by
  nlinarith

/-- Exercise 786_2, gap 11; bind `yᵢ` as the cube roots of `xᵢ`. -/
theorem gap11 (x₁ x₂ ε : ℝ) (hε : 0 < ε)
    (hδ : |x₁ - x₂| < ε ^ 3 / 4) :
    |signedCbrt x₁ - signedCbrt x₂| < ε := by
  exact gap9 (signedCbrt x₁) (signedCbrt x₂) x₁ x₂ ε hε
    (signedCbrt_cubed x₁) (signedCbrt_cubed x₂)
    (gap10 x₁ x₂ ε hε hδ)

/-- Exercise 786_2, gap 12; remove vacuous duplicated quantifiers. -/
theorem gap12 (δ ε : ℝ) (hδ0 : 0 < δ) (hδε : δ < ε ^ 3 / 4) :
    UCCondition δ ε := by
  have hε3 : 0 < ε ^ 3 := by
    nlinarith
  have hε : 0 < ε := by
    by_contra hpos
    have hnonpos : ε ≤ 0 := le_of_not_gt hpos
    have hcube_nonpos : ε * ε ^ 2 ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hnonpos (sq_nonneg ε)
    nlinarith
  unfold UCCondition
  intro x₁ hx₁ x₂ hx₂ hdist
  exact gap11 x₁ x₂ ε hε (lt_trans hdist hδε)

/-- Exercise 786_2, gap 13; reverse the source's false necessity claim to the sufficient bound. -/
theorem gap13 (δ : ℝ) (hδ0 : 0 < δ) (hδ : δ < 2.5 * 10 ^ (-4 : ℤ)) :
    UCCondition δ 0.1 := by
  apply gap12 δ 0.1 hδ0
  norm_num at hδ ⊢
  exact hδ

/-- Exercise 786_2, gap 14; replace the false biconditional by the valid sufficient-condition inclusion. -/
theorem gap14 :
    {δ : ℝ | 0 < δ ∧ δ < 2.5 * 10 ^ (-4 : ℤ)} ⊆
      {δ : ℝ | UCCondition δ 0.1} := by
  intro δ hδ
  exact gap13 δ hδ.1 hδ.2

end

end ProofGap.Exercise786_2
