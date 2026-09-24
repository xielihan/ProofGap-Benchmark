import ProofGapLean.Prelude.Elementary
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise786_1

noncomputable section

def cubeRoot (x : ℝ) : ℝ :=
  Real.sign x * Real.rpow |x| (1 / 3 : ℝ)

def Modulus (δ ε : ℝ) : Prop :=
  ∀ x₁ ∈ Set.Icc (-10 : ℝ) 10, ∀ x₂ ∈ Set.Icc (-10 : ℝ) 10,
    |x₁ - x₂| < δ → |cubeRoot x₁ - cubeRoot x₂| < ε

/-- Exercise 786_1, gap 1; use a signed real cube root and
bind `yᵢ³=xᵢ` explicitly. -/
private theorem oneThirdRpow_cube (x : ℝ) (hx : 0 ≤ x) :
    Real.rpow x (1 / 3 : ℝ) ^ 3 = x := by
  have hm := Real.rpow_mul hx (1 / 3 : ℝ) (3 : ℝ)
  have hpow :
      Real.rpow (Real.rpow x (1 / 3 : ℝ)) (3 : ℝ) =
        Real.rpow x (1 / 3 : ℝ) ^ 3 := by
    norm_num [Real.rpow_natCast]
  calc
    Real.rpow x (1 / 3 : ℝ) ^ 3 =
        Real.rpow (Real.rpow x (1 / 3 : ℝ)) (3 : ℝ) := hpow.symm
    _ = Real.rpow x ((1 / 3 : ℝ) * (3 : ℝ)) := hm.symm
    _ = x := by norm_num

private theorem signedCubeRoot_eq_rpow_of_nonneg (x : ℝ) (hx : 0 ≤ x) :
    cubeRoot x = Real.rpow x (1 / 3 : ℝ) := by
  rcases eq_or_lt_of_le hx with h | h
  · subst x
    norm_num [cubeRoot]
  · unfold cubeRoot
    rw [Real.sign_of_pos h, abs_of_pos h]
    norm_num

private theorem signedCubeRoot_nonneg (x : ℝ) (hx : 0 ≤ x) :
    0 ≤ cubeRoot x := by
  rw [signedCubeRoot_eq_rpow_of_nonneg x hx]
  exact Real.rpow_nonneg hx _

private theorem signedCubeRoot_cube_of_nonneg (x : ℝ) (hx : 0 ≤ x) :
    cubeRoot x ^ 3 = x := by
  rw [signedCubeRoot_eq_rpow_of_nonneg x hx]
  exact oneThirdRpow_cube x hx

private theorem signedCubeRoot_cube (x : ℝ) : cubeRoot x ^ 3 = x := by
  rcases lt_or_ge x 0 with hx | hx
  · have hc : cubeRoot x = -Real.rpow |x| (1 / 3 : ℝ) := by
      unfold cubeRoot
      rw [Real.sign_of_neg hx]
      ring
    have hr := oneThirdRpow_cube |x| (abs_nonneg x)
    rw [hc]
    calc
      (-Real.rpow |x| (1 / 3 : ℝ)) ^ 3 =
          -(Real.rpow |x| (1 / 3 : ℝ) ^ 3) := by ring
      _ = -|x| := by rw [hr]
      _ = x := by rw [abs_of_neg hx]; ring
  · exact signedCubeRoot_cube_of_nonneg x hx

private theorem cube_le_cube_of_nonneg {a b : ℝ} (ha : 0 ≤ a)
    (hab : a ≤ b) : a ^ 3 ≤ b ^ 3 := by
  have hb : 0 ≤ b := le_trans ha hab
  have hq : 0 ≤ b ^ 2 + b * a + a ^ 2 :=
    add_nonneg (add_nonneg (sq_nonneg b) (mul_nonneg hb ha)) (sq_nonneg a)
  have hp : 0 ≤ (b - a) * (b ^ 2 + b * a + a ^ 2) :=
    mul_nonneg (sub_nonneg.mpr hab) hq
  nlinarith [hp]

private theorem cube_lt_cube_of_nonneg {a b : ℝ} (ha : 0 ≤ a)
    (hab : a < b) : a ^ 3 < b ^ 3 := by
  have hb : 0 < b := lt_of_le_of_lt ha hab
  have hq : 0 < b ^ 2 + b * a + a ^ 2 := by
    have hb2 : 0 < b ^ 2 := sq_pos_of_ne_zero hb.ne'
    have hba : 0 ≤ b * a := mul_nonneg hb.le ha
    nlinarith [sq_nonneg a]
  have hp : 0 < (b - a) * (b ^ 2 + b * a + a ^ 2) :=
    mul_pos (sub_pos.mpr hab) hq
  nlinarith [hp]

private theorem nonneg_le_of_cube_le {a b : ℝ} (ha : 0 ≤ a)
    (hb : 0 ≤ b) (h : a ^ 3 ≤ b ^ 3) : a ≤ b := by
  by_contra hab
  have hba : b < a := lt_of_not_ge hab
  have hrev : b ^ 3 < a ^ 3 := cube_lt_cube_of_nonneg hb hba
  linarith

private theorem nonneg_lt_of_cube_lt {a b : ℝ} (ha : 0 ≤ a)
    (hb : 0 ≤ b) (h : a ^ 3 < b ^ 3) : a < b := by
  by_contra hab
  have hba : b ≤ a := le_of_not_gt hab
  have hrev : b ^ 3 ≤ a ^ 3 := cube_le_cube_of_nonneg hb hba
  linarith

theorem gap1 (y₁ y₂ : ℝ) (hne : y₁ ≠ y₂) :
    |y₁ - y₂| =
      |(y₁ ^ 3 - y₂ ^ 3) / (y₁ ^ 2 + y₁ * y₂ + y₂ ^ 2)| := by
  have hsq : 0 < (y₁ - y₂) ^ 2 :=
    sq_pos_of_ne_zero (sub_ne_zero.mpr hne)
  have hdenpos : 0 < y₁ ^ 2 + y₁ * y₂ + y₂ ^ 2 := by
    nlinarith [sq_nonneg (y₁ + y₂), hsq]
  have hden : y₁ ^ 2 + y₁ * y₂ + y₂ ^ 2 ≠ 0 := ne_of_gt hdenpos
  apply congrArg (fun z : ℝ => |z|)
  apply (eq_div_iff hden).2
  ring

/-- Exercise 786_1, gap 2. -/
theorem gap2 (y₁ y₂ : ℝ) (hne : y₁ ≠ y₂) :
    |(y₁ ^ 3 - y₂ ^ 3) / (y₁ ^ 2 + y₁ * y₂ + y₂ ^ 2)| =
      |(y₁ ^ 3 - y₂ ^ 3) /
        ((3 / 4 : ℝ) * (y₁ + y₂) ^ 2 + (1 / 4 : ℝ) * (y₁ - y₂) ^ 2)| := by
  have hden :
      y₁ ^ 2 + y₁ * y₂ + y₂ ^ 2 =
        (3 / 4 : ℝ) * (y₁ + y₂) ^ 2 +
          (1 / 4 : ℝ) * (y₁ - y₂) ^ 2 := by
    ring
  rw [hden]

/-- Exercise 786_1, gap 3. -/
theorem gap3 (y₁ y₂ : ℝ) (hne : y₁ ≠ y₂) :
    |(y₁ ^ 3 - y₂ ^ 3) /
        ((3 / 4 : ℝ) * (y₁ + y₂) ^ 2 + (1 / 4 : ℝ) * (y₁ - y₂) ^ 2)| ≤
      |y₁ ^ 3 - y₂ ^ 3| / ((1 / 4 : ℝ) * |y₁ - y₂| ^ 2) := by
  have hsq : 0 < (y₁ - y₂) ^ 2 :=
    sq_pos_of_ne_zero (sub_ne_zero.mpr hne)
  have habssq : 0 < |y₁ - y₂| ^ 2 :=
    sq_pos_of_ne_zero (abs_ne_zero.mpr (sub_ne_zero.mpr hne))
  have hsmall : 0 < (1 / 4 : ℝ) * |y₁ - y₂| ^ 2 := by
    nlinarith
  have hlarge :
      0 < (3 / 4 : ℝ) * (y₁ + y₂) ^ 2 +
        (1 / 4 : ℝ) * (y₁ - y₂) ^ 2 := by
    nlinarith [sq_nonneg (y₁ + y₂), hsq]
  have hden :
      (1 / 4 : ℝ) * |y₁ - y₂| ^ 2 ≤
        (3 / 4 : ℝ) * (y₁ + y₂) ^ 2 +
          (1 / 4 : ℝ) * (y₁ - y₂) ^ 2 := by
    rw [sq_abs]
    nlinarith [sq_nonneg (y₁ + y₂)]
  rw [abs_div, abs_of_pos hlarge]
  apply (div_le_div_iff₀ hlarge hsmall).2
  exact mul_le_mul_of_nonneg_left hden (abs_nonneg _)

/-- Exercise 786_1, gap 4. -/
theorem gap4 (y₁ y₂ : ℝ) (hne : y₁ ≠ y₂) :
    |y₁ - y₂| ≤
      |y₁ ^ 3 - y₂ ^ 3| / ((1 / 4 : ℝ) * |y₁ - y₂| ^ 2) := by
  calc
    |y₁ - y₂| =
        |(y₁ ^ 3 - y₂ ^ 3) /
          (y₁ ^ 2 + y₁ * y₂ + y₂ ^ 2)| := gap1 y₁ y₂ hne
    _ =
        |(y₁ ^ 3 - y₂ ^ 3) /
          ((3 / 4 : ℝ) * (y₁ + y₂) ^ 2 +
            (1 / 4 : ℝ) * (y₁ - y₂) ^ 2)| := gap2 y₁ y₂ hne
    _ ≤ |y₁ ^ 3 - y₂ ^ 3| /
          ((1 / 4 : ℝ) * |y₁ - y₂| ^ 2) := gap3 y₁ y₂ hne

/-- Exercise 786_1, gap 5. -/
theorem gap5 (y₁ y₂ : ℝ) :
    (1 / 4 : ℝ) * |y₁ - y₂| ^ 3 ≤ |y₁ ^ 3 - y₂ ^ 3| := by
  by_cases hne : y₁ ≠ y₂
  · have hden : 0 < (1 / 4 : ℝ) * |y₁ - y₂| ^ 2 := by
      have habs : 0 < |y₁ - y₂| := abs_pos.mpr (sub_ne_zero.mpr hne)
      positivity
    have hm := (le_div_iff₀ hden).mp (gap4 y₁ y₂ hne)
    calc
      (1 / 4 : ℝ) * |y₁ - y₂| ^ 3 =
          |y₁ - y₂| * ((1 / 4 : ℝ) * |y₁ - y₂| ^ 2) := by ring
      _ ≤ |y₁ ^ 3 - y₂ ^ 3| := hm
  · have heq : y₁ = y₂ := by
      by_contra h
      exact hne h
    subst y₂
    simp

/-- Exercise 786_1, gap 6; restore `xᵢ=yᵢ³`. -/
theorem gap6 (y₁ y₂ x₁ x₂ : ℝ) (hx₁ : x₁ = y₁ ^ 3)
    (hx₂ : x₂ = y₂ ^ 3) :
    |y₁ ^ 3 - y₂ ^ 3| = |x₁ - x₂| := by
  rw [hx₁, hx₂]

/-- Exercise 786_1, gap 7; restore `xᵢ=yᵢ³`. -/
theorem gap7 (y₁ y₂ x₁ x₂ : ℝ) (hx₁ : x₁ = y₁ ^ 3)
    (hx₂ : x₂ = y₂ ^ 3) :
    (1 / 4 : ℝ) * |y₁ - y₂| ^ 3 ≤ |x₁ - x₂| := by
  calc
    (1 / 4 : ℝ) * |y₁ - y₂| ^ 3 ≤
        |y₁ ^ 3 - y₂ ^ 3| := gap5 y₁ y₂
    _ = |x₁ - x₂| := gap6 y₁ y₂ x₁ x₂ hx₁ hx₂

/-- Exercise 786_1, gap 8; use a cube root rather than the
ambiguous `sqrtn`. -/
theorem gap8 (y₁ y₂ x₁ x₂ : ℝ)
    (h : (1 / 4 : ℝ) * |y₁ - y₂| ^ 3 ≤ |x₁ - x₂|) :
    |y₁ - y₂| ≤ cubeRoot (4 * |x₁ - x₂|) := by
  let a : ℝ := |y₁ - y₂|
  let z : ℝ := 4 * |x₁ - x₂|
  have ha : 0 ≤ a := by
    exact abs_nonneg _
  have hz : 0 ≤ z := by
    dsimp [z]
    positivity
  have ha3 : a ^ 3 ≤ z := by
    dsimp [a, z]
    nlinarith
  have hc0 : 0 ≤ cubeRoot z := signedCubeRoot_nonneg z hz
  have hc3 : cubeRoot z ^ 3 = z := signedCubeRoot_cube_of_nonneg z hz
  have hcubed : a ^ 3 ≤ cubeRoot z ^ 3 := by
    calc
      a ^ 3 ≤ z := ha3
      _ = cubeRoot z ^ 3 := hc3.symm
  have hac : a ≤ cubeRoot z :=
    nonneg_le_of_cube_le ha hc0 hcubed
  simpa [a, z] using hac

/-- Exercise 786_1, gap 9; add the bound obtained in gap 8. -/
theorem gap9 (x₁ x₂ y₁ y₂ ε : ℝ) (hε : 0 < ε)
    (hy : |y₁ - y₂| ≤ cubeRoot (4 * |x₁ - x₂|))
    (hx : 4 * |x₁ - x₂| < ε ^ 3) :
    |y₁ - y₂| < ε := by
  let z : ℝ := 4 * |x₁ - x₂|
  have hz : 0 ≤ z := by
    dsimp [z]
    positivity
  have hc0 : 0 ≤ cubeRoot z := signedCubeRoot_nonneg z hz
  have hc3 : cubeRoot z ^ 3 = z := signedCubeRoot_cube_of_nonneg z hz
  have hcube : cubeRoot z ^ 3 < ε ^ 3 := by
    calc
      cubeRoot z ^ 3 = z := hc3
      _ < ε ^ 3 := by simpa [z] using hx
  have hcε : cubeRoot z < ε :=
    nonneg_lt_of_cube_lt hc0 hε.le hcube
  have hy' : |y₁ - y₂| ≤ cubeRoot z := by
    simpa [z] using hy
  linarith

/-- Exercise 786_1, gap 10. -/
theorem gap10 (x₁ x₂ ε : ℝ) (hε : 0 < ε)
    (hx : |x₁ - x₂| < ε ^ 3 / 4) :
    4 * |x₁ - x₂| < ε ^ 3 := by
  nlinarith

/-- Exercise 786_1, gap 11; restore `yᵢ³=xᵢ`. -/
theorem gap11 (x₁ x₂ y₁ y₂ ε : ℝ) (hε : 0 < ε)
    (hx₁ : x₁ = y₁ ^ 3) (hx₂ : x₂ = y₂ ^ 3)
    (hx : |x₁ - x₂| < ε ^ 3 / 4) :
    |y₁ - y₂| < ε := by
  have hbase : (1 / 4 : ℝ) * |y₁ - y₂| ^ 3 ≤ |x₁ - x₂| :=
    gap7 y₁ y₂ x₁ x₂ hx₁ hx₂
  have hy : |y₁ - y₂| ≤ cubeRoot (4 * |x₁ - x₂|) :=
    gap8 y₁ y₂ x₁ x₂ hbase
  have hcube : 4 * |x₁ - x₂| < ε ^ 3 :=
    gap10 x₁ x₂ ε hε hx
  exact gap9 x₁ x₂ y₁ y₂ ε hε hy hcube

/-- Exercise 786_1, gap 12. -/
theorem gap12 (δ ε x₁ x₂ : ℝ) (hδ0 : 0 < δ)
    (hδ : δ < ε ^ 3 / 4) (hmod : Modulus δ ε)
    (hx : |x₁ - x₂| < δ)
    (hx₁ : x₁ ∈ Set.Icc (-10 : ℝ) 10)
    (hx₂ : x₂ ∈ Set.Icc (-10 : ℝ) 10) :
    |cubeRoot x₁ - cubeRoot x₂| < ε := by
  exact hmod x₁ hx₁ x₂ hx₂ hx

/-- Exercise 786_1, gap 13; reverse the false necessity
claim and state the sufficient modulus for `ε=1`. -/
theorem gap13 (δ : ℝ) (hδ0 : 0 < δ) (hδ : δ < (1 : ℝ) / 4) :
    Modulus δ 1 := by
  intro x₁ hx₁ x₂ hx₂ hx
  have hdist : |x₁ - x₂| < (1 : ℝ) ^ 3 / 4 := by
    calc
      |x₁ - x₂| < δ := hx
      _ < (1 : ℝ) / 4 := hδ
      _ = (1 : ℝ) ^ 3 / 4 := by norm_num
  exact gap11 x₁ x₂ (cubeRoot x₁) (cubeRoot x₂) (1 : ℝ)
    (by norm_num) (signedCubeRoot_cube x₁).symm
    (signedCubeRoot_cube x₂).symm hdist

/-- Exercise 786_1, gap 14; the claimed biconditional is
not a sharp characterization, so retain its sufficient direction. -/
theorem gap14 (δ : ℝ) :
    δ ∈ {d : ℝ | 0 < d ∧ d < (1 : ℝ) / 4} → Modulus δ 1 := by
  intro hδ
  exact gap13 δ hδ.1 hδ.2

end

end ProofGap.Exercise786_1
