import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp

namespace ProofGap.Exercise802

noncomputable section

def δ₁ (ε : ℝ) : ℝ := ε / 5
def δ₂ (ε : ℝ) : ℝ := ε / 8
def δ₃ (ε : ℝ) : ℝ := 0.01 * ε
def δ₄ (ε : ℝ) : ℝ := ε ^ 2
def δ₅ (ε : ℝ) : ℝ := ε / 3
def δ₆ (ε : ℝ) : ℝ := min (ε / 3) (ε ^ 2 / (3 + ε))
def oscillatory (x : ℝ) : ℝ := x * Real.sin (1 / x)

/-- Source: `proof_gap/exercise_802/1.txt`. -/
private theorem trig_difference_bounds (x y : ℝ) :
    |Real.sin x - Real.sin y| ≤ |x - y| ∧
      |Real.cos x - Real.cos y| ≤ |x - y| := by
  let u : ℝ := (x + y) / 2
  let v : ℝ := (x - y) / 2
  have hx : x = u + v := by
    dsimp [u, v]
    ring
  have hy : y = u - v := by
    dsimp [u, v]
    ring
  have hsinid : Real.sin x - Real.sin y = 2 * Real.cos u * Real.sin v := by
    rw [hx, hy, Real.sin_add, Real.sin_sub]
    ring
  have hcosid : Real.cos x - Real.cos y = -2 * Real.sin u * Real.sin v := by
    rw [hx, hy, Real.cos_add, Real.cos_sub]
    ring
  have hcosu : |Real.cos u| ≤ 1 := by
    rw [abs_le]
    exact ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩
  have hsinu : |Real.sin u| ≤ 1 := by
    rw [abs_le]
    exact ⟨Real.neg_one_le_sin _, Real.sin_le_one _⟩
  have hsinv : |Real.sin v| ≤ |v| := by
    exact Real.abs_sin_le_abs
  have hv : 2 * |v| = |x - y| := by
    dsimp [v]
    rw [abs_div]
    norm_num
    ring
  constructor
  · rw [hsinid]
    calc
      |2 * Real.cos u * Real.sin v| =
          2 * |Real.cos u| * |Real.sin v| := by
        rw [abs_mul, abs_mul]
        norm_num
      _ ≤ 2 * |Real.sin v| := by
        simpa only [mul_one] using
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hcosu (by norm_num : (0 : ℝ) ≤ 2))
            (abs_nonneg (Real.sin v))
      _ ≤ 2 * |v| :=
        mul_le_mul_of_nonneg_left hsinv (by norm_num)
      _ = |x - y| := hv
  · rw [hcosid]
    calc
      |-2 * Real.sin u * Real.sin v| =
          2 * |Real.sin u| * |Real.sin v| := by
        rw [abs_mul, abs_mul]
        norm_num
      _ ≤ 2 * |Real.sin v| := by
        simpa only [mul_one] using
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hsinu (by norm_num : (0 : ℝ) ≤ 2))
            (abs_nonneg (Real.sin v))
      _ ≤ 2 * |v| :=
        mul_le_mul_of_nonneg_left hsinv (by norm_num)
      _ = |x - y| := hv

theorem gap1 (x₁ x₂ : ℝ) :
    |5 * x₁ - 3 - (5 * x₂ - 3)| = 5 * |x₁ - x₂| := by
  calc
    |5 * x₁ - 3 - (5 * x₂ - 3)| = |5 * (x₁ - x₂)| := by
      congr 1
      ring
    _ = |5| * |x₁ - x₂| := abs_mul _ _
    _ = 5 * |x₁ - x₂| := by norm_num

/-- Source: `proof_gap/exercise_802/2.txt`. -/
theorem gap2 (ε : ℝ) : δ₁ ε = ε / 5 := by
  rfl

/-- Source: `proof_gap/exercise_802/3.txt`. -/
theorem gap3 (x₁ x₂ : ℝ) :
    |x₁ ^ 2 - 2 * x₁ - 1 - (x₂ ^ 2 - 2 * x₂ - 1)| =
      |x₁ - x₂| * |x₁ + x₂ - 2| := by
  calc
    |x₁ ^ 2 - 2 * x₁ - 1 - (x₂ ^ 2 - 2 * x₂ - 1)| =
        |(x₁ - x₂) * (x₁ + x₂ - 2)| := by
      congr 1
      ring
    _ = |x₁ - x₂| * |x₁ + x₂ - 2| := abs_mul _ _

/-- Source: `proof_gap/exercise_802/4.txt`; add the omitted domain
`[-1,5]`, on which the constant `8` is valid. -/
theorem gap4 (x₁ x₂ : ℝ) (hx₁ : x₁ ∈ Set.Icc (-1 : ℝ) 5)
    (hx₂ : x₂ ∈ Set.Icc (-1 : ℝ) 5) :
    |x₁ + x₂ - 2| ≤ 8 := by
  rcases hx₁ with ⟨hx₁l, hx₁u⟩
  rcases hx₂ with ⟨hx₂l, hx₂u⟩
  rw [abs_le]
  constructor <;> linarith

/-- Source: `proof_gap/exercise_802/5.txt`. -/
theorem gap5 (ε : ℝ) : δ₂ ε = ε / 8 := by
  rfl

/-- Source: `proof_gap/exercise_802/6.txt`; add nonzero hypotheses and put an
absolute value around the product in the denominator. -/
theorem gap6 (x₁ x₂ : ℝ) (hx₁ : x₁ ≠ 0) (hx₂ : x₂ ≠ 0) :
    |1 / x₁ - 1 / x₂| = |x₁ - x₂| / |x₁ * x₂| := by
  have hfrac : 1 / x₁ - 1 / x₂ = (x₂ - x₁) / (x₁ * x₂) := by
    field_simp [hx₁, hx₂]
  calc
    |1 / x₁ - 1 / x₂| = |(x₂ - x₁) / (x₁ * x₂)| := by rw [hfrac]
    _ = |x₂ - x₁| / |x₁ * x₂| := by rw [abs_div]
    _ = |x₁ - x₂| / |x₁ * x₂| := by rw [abs_sub_comm x₂ x₁]

/-- Source: `proof_gap/exercise_802/7.txt`; add the omitted lower bounds
`xᵢ≥0.1`. -/
theorem gap7 (x₁ x₂ : ℝ) (hx₁ : (0.1 : ℝ) ≤ x₁)
    (hx₂ : (0.1 : ℝ) ≤ x₂) :
    |x₁ - x₂| / |x₁ * x₂| ≤ |x₁ - x₂| / 0.01 := by
  have hx₁0 : 0 ≤ x₁ := by linarith
  have hx₂0 : 0 ≤ x₂ := by linarith
  have hp : (0.01 : ℝ) ≤ x₁ * x₂ := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hx₁) (sub_nonneg.mpr hx₂)]
  have hp0 : 0 < x₁ * x₂ := by nlinarith
  rw [abs_of_nonneg (mul_nonneg hx₁0 hx₂0)]
  exact div_le_div_of_nonneg_left (abs_nonneg _) (by norm_num) hp

/-- Source: `proof_gap/exercise_802/8.txt`; add the reciprocal-function
domain. -/
theorem gap8 (x₁ x₂ : ℝ) (hx₁ : (0.1 : ℝ) ≤ x₁)
    (hx₂ : (0.1 : ℝ) ≤ x₂) :
    |1 / x₁ - 1 / x₂| ≤ |x₁ - x₂| / 0.01 := by
  have hx₁ne : x₁ ≠ 0 := ne_of_gt (by linarith)
  have hx₂ne : x₂ ≠ 0 := ne_of_gt (by linarith)
  calc
    |1 / x₁ - 1 / x₂| = |x₁ - x₂| / |x₁ * x₂| :=
      gap6 x₁ x₂ hx₁ne hx₂ne
    _ ≤ |x₁ - x₂| / 0.01 := gap7 x₁ x₂ hx₁ hx₂

/-- Source: `proof_gap/exercise_802/9.txt`. -/
theorem gap9 (ε : ℝ) : δ₃ ε = 0.01 * ε := by
  rfl

/-- Source: `proof_gap/exercise_802/10.txt`. -/
theorem gap10 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (a + b) ≤ Real.sqrt a + Real.sqrt b := by
  have hab : 0 ≤ a + b := add_nonneg ha hb
  have hsa : Real.sqrt a ^ 2 = a := Real.sq_sqrt ha
  have hsb : Real.sqrt b ^ 2 = b := Real.sq_sqrt hb
  have hsab : Real.sqrt (a + b) ^ 2 = a + b := Real.sq_sqrt hab
  have hprod : 0 ≤ Real.sqrt a * Real.sqrt b :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  by_contra h
  have hlt : Real.sqrt a + Real.sqrt b < Real.sqrt (a + b) :=
    lt_of_not_ge h
  have hsum : 0 ≤ Real.sqrt a + Real.sqrt b :=
    add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hcpos : 0 < Real.sqrt (a + b) := lt_of_le_of_lt hsum hlt
  have hfactor :
      0 < (Real.sqrt (a + b) - (Real.sqrt a + Real.sqrt b)) *
        (Real.sqrt (a + b) + (Real.sqrt a + Real.sqrt b)) :=
    mul_pos (sub_pos.mpr hlt) (add_pos_of_pos_of_nonneg hcpos hsum)
  nlinarith

/-- Source: `proof_gap/exercise_802/11.txt`. -/
theorem gap11 (ε : ℝ) : δ₄ ε = ε ^ 2 := by
  rfl

/-- Source: `proof_gap/exercise_802/12.txt`. -/
theorem gap12 (ε x₁ x₂ : ℝ) (hε : 0 < ε) (hx₁ : 0 ≤ x₁)
    (hx₂ : 0 ≤ x₂) (hd : |x₁ - x₂| < δ₄ ε) :
    Real.sqrt x₁ < Real.sqrt (x₂ + δ₄ ε) := by
  have hδ : 0 ≤ δ₄ ε := by
    unfold δ₄
    exact sq_nonneg ε
  have hdiff : x₁ - x₂ ≤ |x₁ - x₂| := le_abs_self _
  have hlt : x₁ < x₂ + δ₄ ε := by linarith
  have hsum : 0 ≤ x₂ + δ₄ ε := add_nonneg hx₂ hδ
  have hs₁ : Real.sqrt x₁ ^ 2 = x₁ := Real.sq_sqrt hx₁
  have hs₂ : Real.sqrt (x₂ + δ₄ ε) ^ 2 = x₂ + δ₄ ε :=
    Real.sq_sqrt hsum
  by_contra h
  have hrev : Real.sqrt (x₂ + δ₄ ε) ≤ Real.sqrt x₁ := le_of_not_gt h
  have hprod :
      0 ≤ (Real.sqrt x₁ - Real.sqrt (x₂ + δ₄ ε)) *
        (Real.sqrt x₁ + Real.sqrt (x₂ + δ₄ ε)) :=
    mul_nonneg (sub_nonneg.mpr hrev)
      (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  nlinarith

/-- Source: `proof_gap/exercise_802/13.txt`. -/
theorem gap13 (ε x₂ : ℝ) (hε : 0 < ε) (hx₂ : 0 ≤ x₂) :
    Real.sqrt (x₂ + δ₄ ε) ≤
      Real.sqrt x₂ + Real.sqrt (δ₄ ε) := by
  apply gap10 x₂ (δ₄ ε) hx₂
  unfold δ₄
  exact sq_nonneg ε

/-- Source: `proof_gap/exercise_802/14.txt`; add `ε>0`, needed for
`sqrt(ε²)=ε`. -/
theorem gap14 (ε x₂ : ℝ) (hε : 0 < ε) :
    Real.sqrt x₂ + Real.sqrt (δ₄ ε) = Real.sqrt x₂ + ε := by
  simp [δ₄, Real.sqrt_sq_eq_abs, abs_of_pos hε]

/-- Source: `proof_gap/exercise_802/15.txt`. -/
theorem gap15 (ε x₁ x₂ : ℝ) (hε : 0 < ε) (hx₁ : 0 ≤ x₁)
    (hx₂ : 0 ≤ x₂) (hd : |x₁ - x₂| < δ₄ ε) :
    Real.sqrt x₁ < Real.sqrt x₂ + ε := by
  calc
    Real.sqrt x₁ < Real.sqrt (x₂ + δ₄ ε) :=
      gap12 ε x₁ x₂ hε hx₁ hx₂ hd
    _ ≤ Real.sqrt x₂ + Real.sqrt (δ₄ ε) :=
      gap13 ε x₂ hε hx₂
    _ = Real.sqrt x₂ + ε := gap14 ε x₂ hε

/-- Source: `proof_gap/exercise_802/16.txt`. -/
theorem gap16 (ε x₁ x₂ : ℝ) (hε : 0 < ε) (hx₁ : 0 ≤ x₁)
    (hx₂ : 0 ≤ x₂) (hd : |x₁ - x₂| < δ₄ ε) :
    Real.sqrt x₂ < Real.sqrt (x₁ + δ₄ ε) := by
  apply gap12 ε x₂ x₁ hε hx₂ hx₁
  rw [abs_sub_comm]
  exact hd

/-- Source: `proof_gap/exercise_802/17.txt`. -/
theorem gap17 (ε x₁ : ℝ) (hε : 0 < ε) (hx₁ : 0 ≤ x₁) :
    Real.sqrt (x₁ + δ₄ ε) ≤
      Real.sqrt x₁ + Real.sqrt (δ₄ ε) := by
  exact gap13 ε x₁ hε hx₁

/-- Source: `proof_gap/exercise_802/18.txt`; add `ε>0`. -/
theorem gap18 (ε x₁ : ℝ) (hε : 0 < ε) :
    Real.sqrt x₁ + Real.sqrt (δ₄ ε) = Real.sqrt x₁ + ε := by
  exact gap14 ε x₁ hε

/-- Source: `proof_gap/exercise_802/19.txt`. -/
theorem gap19 (ε x₁ x₂ : ℝ) (hε : 0 < ε) (hx₁ : 0 ≤ x₁)
    (hx₂ : 0 ≤ x₂) (hd : |x₁ - x₂| < δ₄ ε) :
    Real.sqrt x₂ < Real.sqrt x₁ + ε := by
  apply gap15 ε x₂ x₁ hε hx₂ hx₁
  rw [abs_sub_comm]
  exact hd

/-- Source: `proof_gap/exercise_802/20.txt`. -/
theorem gap20 (ε x₁ x₂ : ℝ) (hε : 0 < ε) (hx₁ : 0 ≤ x₁)
    (hx₂ : 0 ≤ x₂) (hd : |x₁ - x₂| < δ₄ ε) :
    |Real.sqrt x₁ - Real.sqrt x₂| < ε := by
  rw [abs_lt]
  constructor
  · have h := gap19 ε x₁ x₂ hε hx₁ hx₂ hd
    linarith
  · have h := gap15 ε x₁ x₂ hε hx₁ hx₂ hd
    linarith

/-- Source: `proof_gap/exercise_802/21.txt`. -/
theorem gap21 (x₁ x₂ : ℝ) :
    |2 * Real.sin x₁ - Real.cos x₁ -
        (2 * Real.sin x₂ - Real.cos x₂)| ≤
      2 * |Real.sin x₁ - Real.sin x₂| +
        |Real.cos x₁ - Real.cos x₂| := by
  have hrewrite :
      2 * Real.sin x₁ - Real.cos x₁ -
          (2 * Real.sin x₂ - Real.cos x₂) =
        2 * (Real.sin x₁ - Real.sin x₂) +
          -(Real.cos x₁ - Real.cos x₂) := by
    ring
  rw [hrewrite]
  calc
    |2 * (Real.sin x₁ - Real.sin x₂) +
        -(Real.cos x₁ - Real.cos x₂)| ≤
        |2 * (Real.sin x₁ - Real.sin x₂)| +
          |-(Real.cos x₁ - Real.cos x₂)| := by
      simpa [Real.norm_eq_abs] using
        norm_add_le (2 * (Real.sin x₁ - Real.sin x₂))
          (-(Real.cos x₁ - Real.cos x₂))
    _ = 2 * |Real.sin x₁ - Real.sin x₂| +
        |Real.cos x₁ - Real.cos x₂| := by
      rw [abs_mul, abs_neg]
      norm_num

/-- Source: `proof_gap/exercise_802/22.txt`. -/
theorem gap22 (x₁ x₂ : ℝ) :
    2 * |Real.sin x₁ - Real.sin x₂| +
        |Real.cos x₁ - Real.cos x₂| ≤
      3 * |x₁ - x₂| := by
  rcases trig_difference_bounds x₁ x₂ with ⟨hs, hc⟩
  linarith

/-- Source: `proof_gap/exercise_802/23.txt`. -/
theorem gap23 (x₁ x₂ : ℝ) :
    |2 * Real.sin x₁ - Real.cos x₁ -
        (2 * Real.sin x₂ - Real.cos x₂)| ≤
      3 * |x₁ - x₂| := by
  exact le_trans (gap21 x₁ x₂) (gap22 x₁ x₂)

/-- Source: `proof_gap/exercise_802/24.txt`. -/
theorem gap24 (ε : ℝ) : δ₅ ε = ε / 3 := by
  rfl

/-- Source: `proof_gap/exercise_802/25.txt`. -/
theorem gap25 (ε : ℝ) :
    δ₆ ε = min (ε / 3) (ε ^ 2 / (3 + ε)) := by
  rfl

/-- Source: `proof_gap/exercise_802/26.txt`; the source's coefficient used
`1/x₂` in the wrong order; use the smaller endpoint `x₁`. -/
theorem gap26 (ε x₁ x₂ : ℝ) (hε : 0 < ε)
    (hx₁ : x₁ ∈ Set.Icc (ε / 3) Real.pi)
    (hx₂ : x₂ ∈ Set.Icc (ε / 3) Real.pi) (hord : x₁ ≤ x₂) :
    |oscillatory x₁ - oscillatory x₂| ≤
      (1 / x₁ + 1) * |x₁ - x₂| := by
  have hx₁pos : 0 < x₁ := by
    rcases hx₁ with ⟨hx₁l, hx₁u⟩
    nlinarith
  have hx₂pos : 0 < x₂ := by
    rcases hx₂ with ⟨hx₂l, hx₂u⟩
    nlinarith
  have hx₁ne : x₁ ≠ 0 := ne_of_gt hx₁pos
  have hx₂ne : x₂ ≠ 0 := ne_of_gt hx₂pos
  have hsone : |Real.sin (1 / x₁)| ≤ 1 := by
    rw [abs_le]
    exact ⟨Real.neg_one_le_sin _, Real.sin_le_one _⟩
  have hslip :
      |Real.sin (1 / x₁) - Real.sin (1 / x₂)| ≤
        |1 / x₁ - 1 / x₂| :=
    (trig_difference_bounds (1 / x₁) (1 / x₂)).1
  have hrec := gap6 x₁ x₂ hx₁ne hx₂ne
  unfold oscillatory
  have hrewrite :
      x₁ * Real.sin (1 / x₁) - x₂ * Real.sin (1 / x₂) =
        (x₁ - x₂) * Real.sin (1 / x₁) +
          x₂ * (Real.sin (1 / x₁) - Real.sin (1 / x₂)) := by
    ring
  rw [hrewrite]
  calc
    |(x₁ - x₂) * Real.sin (1 / x₁) +
        x₂ * (Real.sin (1 / x₁) - Real.sin (1 / x₂))| ≤
        |(x₁ - x₂) * Real.sin (1 / x₁)| +
          |x₂ * (Real.sin (1 / x₁) - Real.sin (1 / x₂))| := by
      simpa [Real.norm_eq_abs] using
        norm_add_le
          ((x₁ - x₂) * Real.sin (1 / x₁))
          (x₂ * (Real.sin (1 / x₁) - Real.sin (1 / x₂)))
    _ = |x₁ - x₂| * |Real.sin (1 / x₁)| +
        |x₂| * |Real.sin (1 / x₁) - Real.sin (1 / x₂)| := by
      rw [abs_mul, abs_mul]
    _ ≤ |x₁ - x₂| * 1 + |x₂| * |1 / x₁ - 1 / x₂| :=
      add_le_add
        (mul_le_mul_of_nonneg_left hsone (abs_nonneg _))
        (mul_le_mul_of_nonneg_left hslip (abs_nonneg _))
    _ = (1 / x₁ + 1) * |x₁ - x₂| := by
      rw [hrec, abs_of_pos hx₂pos, abs_mul, abs_of_pos hx₁pos,
        abs_of_pos hx₂pos]
      field_simp [hx₁ne, hx₂ne]
      ring

/-- Source: `proof_gap/exercise_802/27.txt`; use `x₁`, matching the corrected
Lipschitz coefficient. -/
theorem gap27 (ε x₁ x₂ : ℝ) (hε : 0 < ε)
    (hx₁ : x₁ ∈ Set.Icc (ε / 3) Real.pi)
    (hx₂ : x₂ ∈ Set.Icc (ε / 3) Real.pi) :
    (1 / x₁ + 1) * |x₁ - x₂| ≤
      (3 + ε) / ε * |x₁ - x₂| := by
  have hx₁pos : 0 < x₁ := by
    rcases hx₁ with ⟨hx₁l, hx₁u⟩
    nlinarith
  have hrec : 1 / x₁ ≤ 3 / ε := by
    apply (div_le_div_iff₀ hx₁pos hε).2
    nlinarith [hx₁.1]
  have heq : (3 + ε) / ε = 3 / ε + 1 := by
    field_simp [ne_of_gt hε]
  have hcoef : 1 / x₁ + 1 ≤ (3 + ε) / ε := by
    rw [heq]
    linarith
  exact mul_le_mul_of_nonneg_right hcoef (abs_nonneg _)

/-- Source: `proof_gap/exercise_802/28.txt`; use the corrected coefficient. -/
theorem gap28 (ε x₁ x₂ : ℝ) (hε : 0 < ε)
    (hx₁ : x₁ ∈ Set.Icc (ε / 3) Real.pi)
    (hx₂ : x₂ ∈ Set.Icc (ε / 3) Real.pi) (hord : x₁ ≤ x₂) :
    |oscillatory x₁ - oscillatory x₂| ≤
      (3 + ε) / ε * |x₁ - x₂| := by
  exact le_trans (gap26 ε x₁ x₂ hε hx₁ hx₂ hord)
    (gap27 ε x₁ x₂ hε hx₁ hx₂)

/-- Source: `proof_gap/exercise_802/29.txt`. -/
theorem gap29 (ε x₁ x₂ : ℝ) (hε : 0 < ε)
    (hx₁ : x₁ ∈ Set.Icc (0 : ℝ) Real.pi)
    (hx₂ : x₂ ∈ Set.Icc (0 : ℝ) Real.pi)
    (hd : |x₁ - x₂| < δ₆ ε) (hord : x₁ < x₂)
    (hlarge : ε / 3 ≤ x₁) :
    |oscillatory x₁ - oscillatory x₂| < ε := by
  have hx₁' : x₁ ∈ Set.Icc (ε / 3) Real.pi := ⟨hlarge, hx₁.2⟩
  have hx₂' : x₂ ∈ Set.Icc (ε / 3) Real.pi :=
    ⟨le_trans hlarge (le_of_lt hord), hx₂.2⟩
  have hlip := gap28 ε x₁ x₂ hε hx₁' hx₂' (le_of_lt hord)
  have hmin : δ₆ ε ≤ ε ^ 2 / (3 + ε) := by
    unfold δ₆
    exact min_le_right _ _
  have hdist : |x₁ - x₂| < ε ^ 2 / (3 + ε) :=
    lt_of_lt_of_le hd hmin
  have hden : 0 < 3 + ε := by linarith
  have hscaled : |x₁ - x₂| * (3 + ε) < ε ^ 2 :=
    (lt_div_iff₀ hden).1 hdist
  have hid :
      (3 + ε) / ε * |x₁ - x₂| =
        ((3 + ε) * |x₁ - x₂|) / ε := by
    field_simp [ne_of_gt hε]
  have hfinal : (3 + ε) / ε * |x₁ - x₂| < ε := by
    rw [hid]
    apply (div_lt_iff₀ hε).2
    nlinarith
  exact lt_of_le_of_lt hlip hfinal

/-- Source: `proof_gap/exercise_802/30.txt`. -/
theorem gap30 (ε x₁ x₂ : ℝ) (hε : 0 < ε)
    (hd : |x₁ - x₂| < δ₆ ε) (hord : x₁ < x₂)
    (hx₁ : 0 ≤ x₁) (hsmall : x₁ < ε / 3) :
    x₂ < δ₆ ε + ε / 3 := by
  have hdiff : x₂ - x₁ < δ₆ ε := by
    rw [abs_of_neg (sub_neg.mpr hord)] at hd
    linarith
  linarith

/-- Source: `proof_gap/exercise_802/31.txt`. -/
theorem gap31 (ε : ℝ) (hε : 0 < ε) :
    δ₆ ε + ε / 3 ≤ 2 * ε / 3 := by
  have hmin : δ₆ ε ≤ ε / 3 := by
    unfold δ₆
    exact min_le_left _ _
  linarith

/-- Source: `proof_gap/exercise_802/32.txt`. -/
theorem gap32 (ε x₁ x₂ : ℝ) (hε : 0 < ε)
    (hd : |x₁ - x₂| < δ₆ ε) (hord : x₁ < x₂)
    (hx₁ : 0 ≤ x₁) (hsmall : x₁ < ε / 3) :
    x₂ < 2 * ε / 3 := by
  have h₁ := gap30 ε x₁ x₂ hε hd hord hx₁ hsmall
  have h₂ := gap31 ε hε
  linarith

/-- Source: `proof_gap/exercise_802/33.txt`. -/
theorem gap33 (x₁ x₂ : ℝ) :
    |oscillatory x₁ - oscillatory x₂| ≤ |x₁| + |x₂| := by
  have h₁ : |oscillatory x₁| ≤ |x₁| := by
    unfold oscillatory
    rw [abs_mul]
    have hs : |Real.sin (1 / x₁)| ≤ 1 := by
      rw [abs_le]
      exact ⟨Real.neg_one_le_sin _, Real.sin_le_one _⟩
    calc
      |x₁| * |Real.sin (1 / x₁)| ≤ |x₁| * 1 :=
        mul_le_mul_of_nonneg_left hs (abs_nonneg _)
      _ = |x₁| := mul_one _
  have h₂ : |oscillatory x₂| ≤ |x₂| := by
    unfold oscillatory
    rw [abs_mul]
    have hs : |Real.sin (1 / x₂)| ≤ 1 := by
      rw [abs_le]
      exact ⟨Real.neg_one_le_sin _, Real.sin_le_one _⟩
    calc
      |x₂| * |Real.sin (1 / x₂)| ≤ |x₂| * 1 :=
        mul_le_mul_of_nonneg_left hs (abs_nonneg _)
      _ = |x₂| := mul_one _
  calc
    |oscillatory x₁ - oscillatory x₂| =
        |oscillatory x₁ + -oscillatory x₂| := by rw [sub_eq_add_neg]
    _ ≤ |oscillatory x₁| + |-oscillatory x₂| := by
      simpa [Real.norm_eq_abs] using
        norm_add_le (oscillatory x₁) (-oscillatory x₂)
    _ = |oscillatory x₁| + |oscillatory x₂| := by rw [abs_neg]
    _ ≤ |x₁| + |x₂| := add_le_add h₁ h₂

/-- Source: `proof_gap/exercise_802/34.txt`. -/
theorem gap34 (ε x₁ x₂ : ℝ) (hε : 0 < ε)
    (hx₁ : 0 ≤ x₁) (hx₁' : x₁ < ε / 3)
    (hx₂ : 0 ≤ x₂) (hx₂' : x₂ < 2 * ε / 3) :
    |x₁| + |x₂| < ε := by
  rw [abs_of_nonneg hx₁, abs_of_nonneg hx₂]
  linarith

/-- Source: `proof_gap/exercise_802/35.txt`. -/
theorem gap35 (ε x₁ x₂ : ℝ) (hε : 0 < ε)
    (hd : |x₁ - x₂| < δ₆ ε) (hord : x₁ < x₂)
    (hx₁ : 0 ≤ x₁) (hsmall : x₁ < ε / 3) :
    |oscillatory x₁ - oscillatory x₂| < ε := by
  have hx₂0 : 0 ≤ x₂ := le_trans hx₁ (le_of_lt hord)
  have hx₂lt := gap32 ε x₁ x₂ hε hd hord hx₁ hsmall
  exact lt_of_le_of_lt (gap33 x₁ x₂)
    (gap34 ε x₁ x₂ hε hx₁ hsmall hx₂0 hx₂lt)

/-- Source: `proof_gap/exercise_802/36.txt`. -/
theorem gap36 (x₂ : ℝ) :
    |(0 : ℝ) - oscillatory x₂| ≤ |x₂| := by
  unfold oscillatory
  rw [zero_sub, abs_neg, abs_mul]
  have hs : |Real.sin (1 / x₂)| ≤ 1 := by
    rw [abs_le]
    exact ⟨Real.neg_one_le_sin _, Real.sin_le_one _⟩
  calc
    |x₂| * |Real.sin (1 / x₂)| ≤ |x₂| * 1 :=
      mul_le_mul_of_nonneg_left hs (abs_nonneg _)
    _ = |x₂| := mul_one _

/-- Source: `proof_gap/exercise_802/37.txt`. -/
theorem gap37 (ε x₁ x₂ : ℝ) (hε : 0 < ε)
    (hd : |x₁ - x₂| < δ₆ ε) (hord : x₁ < x₂) (hx₁ : x₁ = 0) :
    |x₂| < 2 * ε / 3 := by
  subst x₁
  have hx₂lt := gap32 ε 0 x₂ hε hd hord (le_refl 0) (by nlinarith)
  simpa [abs_of_pos hord] using hx₂lt

/-- Source: `proof_gap/exercise_802/38.txt`. -/
theorem gap38 (ε : ℝ) (hε : 0 < ε) : 2 * ε / 3 < ε := by
  nlinarith

/-- Source: `proof_gap/exercise_802/39.txt`. -/
theorem gap39 (ε x₁ x₂ : ℝ) (hε : 0 < ε)
    (hd : |x₁ - x₂| < δ₆ ε) (hord : x₁ < x₂) (hx₁ : x₁ = 0) :
    |(0 : ℝ) - oscillatory x₂| < ε := by
  have h₁ := gap36 x₂
  have h₂ := gap37 ε x₁ x₂ hε hd hord hx₁
  have h₃ := gap38 ε hε
  exact lt_of_le_of_lt h₁ (lt_trans h₂ h₃)

/-- Source: `proof_gap/exercise_802/40.txt`. -/
theorem gap40 (ε : ℝ) :
    (δ₁ ε, δ₂ ε, δ₃ ε, δ₄ ε, δ₅ ε, δ₆ ε) =
      (ε / 5, ε / 8, 0.01 * ε, ε ^ 2, ε / 3,
        min (ε / 3) (ε ^ 2 / (3 + ε))) := by
  rfl

end

end ProofGap.Exercise802
