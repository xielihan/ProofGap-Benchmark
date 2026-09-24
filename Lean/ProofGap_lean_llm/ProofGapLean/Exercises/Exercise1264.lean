import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv

namespace ProofGap.Exercise1264

noncomputable section

def firstExpr (x : ℝ) : ℝ :=
  2 * Real.arctan x + Real.arcsin (2 * x / (1 + x ^ 2))

def secondExpr (x : ℝ) : ℝ :=
  3 * Real.arccos x - Real.arccos (3 * x - 4 * x ^ 3)

def firstRawDerivative (x : ℝ) : ℝ :=
  2 / (1 + x ^ 2) +
    1 / Real.sqrt (1 - 4 * x ^ 2 / (1 + x ^ 2) ^ 2) *
      (2 * (1 + x ^ 2) - 4 * x ^ 2) / (1 + x ^ 2) ^ 2

def secondRawDerivative (x : ℝ) : ℝ :=
  -3 / Real.sqrt (1 - x ^ 2) +
    1 / Real.sqrt (1 - (3 * x - 4 * x ^ 3) ^ 2) * (3 - 12 * x ^ 2)

private lemma sin_two_arctan (x : ℝ) :
    Real.sin (2 * Real.arctan x) = 2 * x / (1 + x ^ 2) := by
  have hspos : 0 < Real.sqrt (1 + x ^ 2) := Real.sqrt_pos.2 (by positivity)
  have hs2 : Real.sqrt (1 + x ^ 2) ^ 2 = 1 + x ^ 2 :=
    Real.sq_sqrt (by positivity)
  rw [Real.sin_two_mul, Real.sin_arctan, Real.cos_arctan]
  calc
    2 * (x / Real.sqrt (1 + x ^ 2)) *
        (1 / Real.sqrt (1 + x ^ 2)) =
        2 * x / Real.sqrt (1 + x ^ 2) ^ 2 := by
      field_simp [ne_of_gt hspos]
    _ = 2 * x / (1 + x ^ 2) := by rw [hs2]

private lemma firstExpr_pos (x : ℝ) (hx : 1 < x) :
    firstExpr x = Real.pi := by
  have hatan_lo : Real.pi / 4 < Real.arctan x := by
    rw [← Real.arctan_one]
    exact Real.arctan_lt_arctan hx
  have hatan_hi : Real.arctan x < Real.pi / 2 :=
    Real.arctan_lt_pi_div_two x
  let y := Real.pi - 2 * Real.arctan x
  have hylo : -(Real.pi / 2) ≤ y := by
    dsimp [y]
    linarith [Real.pi_pos]
  have hyhi : y ≤ Real.pi / 2 := by
    dsimp [y]
    linarith
  have harg :
      2 * x / (1 + x ^ 2) = Real.sin y := by
    dsimp [y]
    rw [Real.sin_pi_sub]
    exact (sin_two_arctan x).symm
  unfold firstExpr
  rw [harg, Real.arcsin_sin hylo hyhi]
  dsimp [y]
  ring

private lemma firstExpr_neg (x : ℝ) (hx : x < -1) :
    firstExpr x = -Real.pi := by
  have hatan_hi : Real.arctan x < -(Real.pi / 4) := by
    have h := Real.arctan_lt_arctan hx
    simpa [Real.arctan_neg, Real.arctan_one] using h
  have hatan_lo : -(Real.pi / 2) < Real.arctan x :=
    Real.neg_pi_div_two_lt_arctan x
  let y := -Real.pi - 2 * Real.arctan x
  have hylo : -(Real.pi / 2) ≤ y := by
    dsimp [y]
    linarith
  have hyhi : y ≤ Real.pi / 2 := by
    dsimp [y]
    linarith [Real.pi_pos]
  have harg :
      2 * x / (1 + x ^ 2) = Real.sin y := by
    dsimp [y]
    rw [show -Real.pi - 2 * Real.arctan x =
      -(2 * Real.arctan x + Real.pi) by ring,
      Real.sin_neg, Real.sin_add_pi, neg_neg]
    exact (sin_two_arctan x).symm
  unfold firstExpr
  rw [harg, Real.arcsin_sin hylo hyhi]
  dsimp [y]
  ring

private lemma deriv_firstExpr_zero (x : ℝ) (hx : 1 < |x|) :
    deriv firstExpr x = 0 := by
  by_cases hxnonneg : 0 ≤ x
  · have hxgt : 1 < x := by
      rwa [abs_of_nonneg hxnonneg] at hx
    have hev : firstExpr =ᶠ[nhds x] fun _ => Real.pi := by
      filter_upwards [IsOpen.mem_nhds isOpen_Ioi hxgt] with z hz
      exact firstExpr_pos z hz
    simpa using Filter.EventuallyEq.deriv_eq hev
  · have hxneg : x < 0 := lt_of_not_ge hxnonneg
    have hxlt : x < -1 := by
      rw [abs_of_neg hxneg] at hx
      linarith
    have hev : firstExpr =ᶠ[nhds x] fun _ => -Real.pi := by
      filter_upwards [IsOpen.mem_nhds isOpen_Iio hxlt] with z hz
      exact firstExpr_neg z hz
    simpa using Filter.EventuallyEq.deriv_eq hev

private lemma firstRawDerivative_zero (x : ℝ) (hx : 1 < |x|) :
    firstRawDerivative x = 0 := by
  have hxsq : 1 < x ^ 2 := by
    nlinarith [sq_abs x]
  have hdenpos : 0 < 1 + x ^ 2 := by positivity
  have hrad :
      1 - 4 * x ^ 2 / (1 + x ^ 2) ^ 2 =
        ((x ^ 2 - 1) / (1 + x ^ 2)) ^ 2 := by
    field_simp [ne_of_gt hdenpos]
    ring
  have hsqrt :
      Real.sqrt (1 - 4 * x ^ 2 / (1 + x ^ 2) ^ 2) =
        (x ^ 2 - 1) / (1 + x ^ 2) := by
    rw [hrad, Real.sqrt_sq_eq_abs,
      abs_of_pos (div_pos (sub_pos.mpr hxsq) hdenpos)]
  unfold firstRawDerivative
  rw [hsqrt]
  field_simp [ne_of_gt hdenpos, ne_of_gt (sub_pos.mpr hxsq)]
  ring

private lemma arccos_half :
    Real.arccos (1 / 2 : ℝ) = Real.pi / 3 := by
  rw [← Real.cos_pi_div_three]
  exact Real.arccos_cos (by positivity) (by linarith [Real.pi_pos])

private lemma arccos_neg_half :
    Real.arccos (-1 / 2 : ℝ) = 2 * Real.pi / 3 := by
  have hcos : Real.cos (2 * Real.pi / 3) = (-1 / 2 : ℝ) := by
    rw [show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 by ring,
      Real.cos_pi_sub, Real.cos_pi_div_three]
    ring
  rw [← hcos]
  exact Real.arccos_cos (by positivity) (by linarith [Real.pi_pos])

private lemma secondExpr_eq_pi (x : ℝ) (hx : |x| < 1 / 2) :
    secondExpr x = Real.pi := by
  have hxb := abs_lt.mp hx
  have hxlo : (-1 / 2 : ℝ) < x := by linarith [hxb.1]
  have hxhi : x < (1 / 2 : ℝ) := hxb.2
  have hxlower : (-1 : ℝ) ≤ x := by linarith
  have hxupper : x ≤ (1 : ℝ) := by linarith
  let θ := Real.arccos x
  have hθlo : Real.pi / 3 < θ := by
    have h := Real.arccos_lt_arccos hxlower hxhi (by norm_num)
    dsimp [θ]
    calc
      Real.pi / 3 = Real.arccos (1 / 2 : ℝ) := arccos_half.symm
      _ < Real.arccos x := h
  have hθhi : θ < 2 * Real.pi / 3 := by
    have h := Real.arccos_lt_arccos (x := (-1 / 2 : ℝ))
      (y := x) (by norm_num) hxlo hxupper
    simpa [θ, arccos_neg_half] using h
  let z := 3 * θ - Real.pi
  have hzlo : 0 ≤ z := by
    dsimp [z]
    linarith
  have hzhi : z ≤ Real.pi := by
    dsimp [z]
    linarith
  have hcosθ : Real.cos θ = x := by
    dsimp [θ]
    exact Real.cos_arccos hxlower hxupper
  have hcos3 :
      Real.cos (3 * θ) = 4 * x ^ 3 - 3 * x := by
    rw [Real.cos_three_mul, hcosθ]
  have harg :
      3 * x - 4 * x ^ 3 = Real.cos z := by
    dsimp [z]
    rw [Real.cos_sub_pi, hcos3]
    ring
  unfold secondExpr
  rw [harg, Real.arccos_cos hzlo hzhi]
  dsimp [z]
  ring

private lemma deriv_secondExpr_zero (x : ℝ) (hx : |x| < 1 / 2) :
    deriv secondExpr x = 0 := by
  have hxmem : x ∈ Set.Ioo (-1 / 2 : ℝ) (1 / 2 : ℝ) :=
    ⟨by linarith [(abs_lt.mp hx).1], (abs_lt.mp hx).2⟩
  have hev : secondExpr =ᶠ[nhds x] fun _ => Real.pi := by
    filter_upwards [IsOpen.mem_nhds isOpen_Ioo hxmem] with z hz
    exact secondExpr_eq_pi z (abs_lt.mpr
      ⟨by linarith [hz.1], hz.2⟩)
  simpa using Filter.EventuallyEq.deriv_eq hev

private lemma secondRawDerivative_zero (x : ℝ) (hx : |x| < 1 / 2) :
    secondRawDerivative x = 0 := by
  have hxsq : x ^ 2 < 1 / 4 := by
    nlinarith [abs_nonneg x, sq_abs x]
  have hA : 0 < 1 - x ^ 2 := by linarith
  have hB : 0 < 1 - 4 * x ^ 2 := by linarith
  have hB' : 1 - x ^ 2 * 4 ≠ 0 := by nlinarith
  have hrad :
      1 - (3 * x - 4 * x ^ 3) ^ 2 =
        (1 - x ^ 2) * (1 - 4 * x ^ 2) ^ 2 := by ring
  have hsqrt :
      Real.sqrt (1 - (3 * x - 4 * x ^ 3) ^ 2) =
        Real.sqrt (1 - x ^ 2) * (1 - 4 * x ^ 2) := by
    rw [hrad, Real.sqrt_mul (le_of_lt hA), Real.sqrt_sq_eq_abs,
      abs_of_pos hB]
  have hsA : 0 < Real.sqrt (1 - x ^ 2) := Real.sqrt_pos.2 hA
  unfold secondRawDerivative
  rw [hsqrt]
  rw [show 3 - 12 * x ^ 2 = 3 * (1 - 4 * x ^ 2) by ring]
  field_simp [ne_of_gt hsA, ne_of_gt hB, hB']
  ring

theorem gap1 (x : ℝ) (hx : 1 < |x|) :
    deriv firstExpr x = firstRawDerivative x := by
  rw [deriv_firstExpr_zero x hx, firstRawDerivative_zero x hx]

theorem gap2 (x : ℝ) (hx : 1 < |x|) :
    firstRawDerivative x = 0 := by
  exact firstRawDerivative_zero x hx

theorem gap3 (x : ℝ) (hx : 1 < |x|) :
    deriv firstExpr x = 0 := by
  exact deriv_firstExpr_zero x hx

theorem gap4 :
    ∃ C₁, ∀ x, 1 < x → firstExpr x = C₁ := by
  exact ⟨Real.pi, firstExpr_pos⟩

theorem gap5 :
    ∃ C₂, ∀ x, x < -1 → firstExpr x = C₂ := by
  exact ⟨-Real.pi, firstExpr_neg⟩

theorem gap6 :
    ∃ C₁ : ℝ, C₁ = Real.pi := by
  exact ⟨Real.pi, rfl⟩

theorem gap7 :
    ∃ C₂ : ℝ, C₂ = -Real.pi := by
  exact ⟨-Real.pi, rfl⟩

theorem gap8 (x : ℝ) (hx : 1 < |x|) :
    firstExpr x = if 1 < x then Real.pi else -Real.pi := by
  by_cases hpos : 1 < x
  · rw [if_pos hpos]
    exact firstExpr_pos x hpos
  · rw [if_neg hpos]
    have hxneg : x < 0 := by
      by_contra hn
      have hxnonneg : 0 ≤ x := le_of_not_gt hn
      rw [abs_of_nonneg hxnonneg] at hx
      linarith
    have hxlt : x < -1 := by
      rw [abs_of_neg hxneg] at hx
      linarith
    exact firstExpr_neg x hxlt

theorem gap9 (x : ℝ) (hx : 1 < |x|) :
    firstExpr x = Real.pi * Real.sign x := by
  by_cases hxpos : 0 < x
  · rw [Real.sign_of_pos hxpos, mul_one]
    exact firstExpr_pos x (by
      rw [abs_of_pos hxpos] at hx
      exact hx)
  · have hxneg : x < 0 := by
      rcases lt_or_eq_of_le (le_of_not_gt hxpos) with h | rfl
      · exact h
      · norm_num at hx
    rw [Real.sign_of_neg hxneg, mul_neg, mul_one]
    exact firstExpr_neg x (by
      rw [abs_of_neg hxneg] at hx
      linarith)

theorem gap10 (x : ℝ) (hx : |x| < 1 / 2) :
    deriv secondExpr x = secondRawDerivative x := by
  rw [deriv_secondExpr_zero x hx, secondRawDerivative_zero x hx]

theorem gap11 (x : ℝ) (hx : |x| < 1 / 2) :
    secondRawDerivative x = 0 := by
  exact secondRawDerivative_zero x hx

theorem gap12 (x : ℝ) (hx : |x| < 1 / 2) :
    deriv secondExpr x = 0 := by
  exact deriv_secondExpr_zero x hx

theorem gap13 :
    ∃ C, ∀ x, |x| < 1 / 2 → secondExpr x = C := by
  exact ⟨Real.pi, secondExpr_eq_pi⟩

theorem gap14 :
    ∃ C : ℝ, C = Real.pi := by
  exact ⟨Real.pi, rfl⟩

theorem gap15 (x : ℝ) (hx : |x| < 1 / 2) :
    secondExpr x = Real.pi := by
  exact secondExpr_eq_pi x hx

theorem gap16 (x : ℝ) (hx : |x| < 1 / 2) :
    secondExpr x = Real.pi := by
  exact gap15 x hx

theorem gap17 :
    (∀ x, 1 < |x| → firstExpr x = Real.pi * Real.sign x) ∧
      (∀ x, |x| < 1 / 2 → secondExpr x = Real.pi) := by
  exact ⟨gap9, gap15⟩

end

end ProofGap.Exercise1264
