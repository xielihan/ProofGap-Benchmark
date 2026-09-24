import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1100

noncomputable section

def Approx (x y ε : ℝ) : Prop := |x - y| < ε

private theorem pi_numeric_bounds :
    (157 / 50 : ℝ) < Real.pi ∧
      Real.pi < (3927 / 1250 : ℝ) := by
  constructor
  · have hpi := Real.pi_gt_d4
    norm_num at hpi ⊢
    nlinarith
  · have hpi := Real.pi_lt_d4
    norm_num at hpi ⊢
    exact hpi

private theorem sqrt_three_numeric_bounds :
    (433 / 250 : ℝ) < Real.sqrt 3 ∧
      Real.sqrt 3 < (17321 / 10000 : ℝ) := by
  let s : ℝ := Real.sqrt 3
  have hs0 : 0 ≤ s := by
    dsimp [s]
    exact Real.sqrt_nonneg 3
  have hs_sq : s ^ 2 = 3 := by
    dsimp [s]
    simpa using Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  constructor
  · nlinarith [sq_nonneg (s - (433 / 250 : ℝ))]
  · nlinarith [sq_nonneg (s - (17321 / 10000 : ℝ))]

private theorem pi_sqrt_three_product_bounds :
    (1359 / 250 : ℝ) < Real.pi * Real.sqrt 3 ∧
      Real.pi * Real.sqrt 3 < (3402 / 625 : ℝ) := by
  rcases pi_numeric_bounds with ⟨hpilo, hpiup⟩
  rcases sqrt_three_numeric_bounds with ⟨hslo, hsup⟩
  have hspos : 0 < Real.sqrt 3 := by positivity
  constructor
  · have h1 : 0 < (Real.pi - (157 / 50 : ℝ)) * Real.sqrt 3 :=
      mul_pos (sub_pos.mpr hpilo) hspos
    have h2 :
        0 < (157 / 50 : ℝ) * (Real.sqrt 3 - (433 / 250 : ℝ)) :=
      mul_pos (by norm_num) (sub_pos.mpr hslo)
    nlinarith
  · have h1 :
        0 < ((3927 / 1250 : ℝ) - Real.pi) * Real.sqrt 3 :=
      mul_pos (sub_pos.mpr hpiup) hspos
    have h2 :
        0 < (3927 / 1250 : ℝ) *
          ((17321 / 10000 : ℝ) - Real.sqrt 3) :=
      mul_pos (by norm_num) (sub_pos.mpr hsup)
    nlinarith

private theorem decimal_linearization_signed :
    -(1 / 50000 : ℝ) <
        (Real.sin (Real.pi / 6) -
          Real.pi / 180 * Real.cos (Real.pi / 6)) -
          (4849 / 10000 : ℝ) ∧
      (Real.sin (Real.pi / 6) -
          Real.pi / 180 * Real.cos (Real.pi / 6)) -
          (4849 / 10000 : ℝ) < 0 := by
  have hsina : Real.sin (Real.pi / 6) = (1 / 2 : ℝ) := by
    simpa using Real.sin_pi_div_six
  have hcosa : Real.cos (Real.pi / 6) = Real.sqrt 3 / 2 := by
    simpa using Real.cos_pi_div_six
  have herr :
      (Real.sin (Real.pi / 6) -
          Real.pi / 180 * Real.cos (Real.pi / 6)) -
          (4849 / 10000 : ℝ) =
        (151 / 10000 : ℝ) - Real.pi * Real.sqrt 3 / 360 := by
    rw [hsina, hcosa]
    ring
  rcases pi_sqrt_three_product_bounds with ⟨hlo, hup⟩
  rw [herr]
  constructor <;> nlinarith

private theorem sin_linearization_error
    (a h : ℝ)
    (hsina : Real.sin a = (1 / 2 : ℝ))
    (hhpos : 0 < h)
    (hhpi2 : h < Real.pi / 2)
    (hhhalf : h ≤ (1 / 2 : ℝ))
    (hca0 : 0 ≤ Real.cos a)
    (hcale : Real.cos a ≤ 1) :
    -(h ^ 2 / 4) ≤
        Real.sin (a - h) - (Real.sin a - h * Real.cos a) ∧
      Real.sin (a - h) - (Real.sin a - h * Real.cos a) ≤ 0 := by
  have hh0 : 0 ≤ h := le_of_lt hhpos
  have hnegpi2 : -(Real.pi / 2) < h := by
    nlinarith [Real.pi_pos]
  have hcospos : 0 < Real.cos h :=
    Real.cos_pos_of_mem_Ioo ⟨hnegpi2, hhpi2⟩
  have htan : h ≤ Real.tan h :=
    le_of_lt (Real.lt_tan hhpos hhpi2)
  have hmulcos : h * Real.cos h ≤ Real.sin h := by
    rw [Real.tan_eq_sin_div_cos] at htan
    exact (le_div_iff₀ hcospos).mp htan
  have hsinle : Real.sin h ≤ h := Real.sin_le hh0
  have hq0 : 0 ≤ 1 - Real.cos h := by
    nlinarith [Real.cos_le_one h]
  have hqbound : 1 - Real.cos h ≤ h ^ 2 / 2 := by
    have hc : 1 - h ^ 2 / 2 ≤ Real.cos h :=
      Real.one_sub_sq_div_two_le_cos
    nlinarith
  have hr0 : 0 ≤ h - Real.sin h := by
    nlinarith
  have hrle : h - Real.sin h ≤ h * (1 - Real.cos h) := by
    nlinarith [hmulcos]
  have hcar0 : 0 ≤ Real.cos a * (h - Real.sin h) :=
    mul_nonneg hca0 hr0
  have hcarle :
      Real.cos a * (h - Real.sin h) ≤ h * (1 - Real.cos h) := by
    have h1 :
        Real.cos a * (h - Real.sin h) ≤ 1 * (h - Real.sin h) :=
      mul_le_mul_of_nonneg_right hcale hr0
    nlinarith [h1, hrle]
  have hcarhalf :
      Real.cos a * (h - Real.sin h) ≤
        (1 / 2 : ℝ) * (1 - Real.cos h) := by
    have h1 :
        h * (1 - Real.cos h) ≤
          (1 / 2 : ℝ) * (1 - Real.cos h) :=
      mul_le_mul_of_nonneg_right hhhalf hq0
    exact hcarle.trans h1
  let d : ℝ := Real.sin (a - h) - (Real.sin a - h * Real.cos a)
  have hdform :
      d = -(1 / 2 : ℝ) * (1 - Real.cos h) +
        Real.cos a * (h - Real.sin h) := by
    dsimp [d]
    rw [Real.sin_sub, hsina]
    ring
  have hdle : d ≤ 0 := by
    rw [hdform]
    nlinarith [hcarhalf]
  have hdneg : -d ≤ (1 / 2 : ℝ) * (1 - Real.cos h) := by
    rw [hdform]
    nlinarith [hcar0]
  have hqscaled :
      (1 / 2 : ℝ) * (1 - Real.cos h) ≤ h ^ 2 / 4 := by
    nlinarith [hqbound]
  have hdlower : -(h ^ 2 / 4) ≤ d := by
    nlinarith [hdneg, hqscaled]
  exact ⟨hdlower, hdle⟩

private theorem target_linearization_signed :
    -(1 / 12500 : ℝ) <
        Real.sin (29 * Real.pi / 180) -
          (Real.sin (Real.pi / 6) -
            Real.pi / 180 * Real.cos (Real.pi / 6)) ∧
      Real.sin (29 * Real.pi / 180) -
          (Real.sin (Real.pi / 6) -
            Real.pi / 180 * Real.cos (Real.pi / 6)) ≤ 0 := by
  let a : ℝ := Real.pi / 6
  let h : ℝ := Real.pi / 180
  rcases pi_numeric_bounds with ⟨_, hpiup⟩
  have hhpos : 0 < h := by
    dsimp [h]
    positivity
  have hhup : h < (7 / 400 : ℝ) := by
    dsimp [h]
    nlinarith [hpiup]
  have hhpi2 : h < Real.pi / 2 := by
    dsimp [h]
    nlinarith [Real.pi_pos]
  have hhhalf : h ≤ (1 / 2 : ℝ) := by
    nlinarith [hhup]
  have hsina : Real.sin a = (1 / 2 : ℝ) := by
    dsimp [a]
    simpa using Real.sin_pi_div_six
  have hcosa : Real.cos a = Real.sqrt 3 / 2 := by
    dsimp [a]
    simpa using Real.cos_pi_div_six
  have hca0 : 0 ≤ Real.cos a := by
    rw [hcosa]
    positivity
  have hcale : Real.cos a ≤ 1 := Real.cos_le_one a
  have hb :=
    sin_linearization_error a h hsina hhpos hhpi2 hhhalf hca0 hcale
  have hsq : h ^ 2 < (7 / 400 : ℝ) ^ 2 := by
    have hm :
        0 < ((7 / 400 : ℝ) - h) * ((7 / 400 : ℝ) + h) :=
      mul_pos (sub_pos.mpr hhup) (by nlinarith [hhpos])
    nlinarith
  have herrlt : h ^ 2 / 4 < (1 / 12500 : ℝ) := by
    nlinarith [hsq]
  have hangle : 29 * Real.pi / 180 = a - h := by
    dsimp [a, h]
    ring
  rw [hangle]
  change
    -(1 / 12500 : ℝ) <
        Real.sin (a - h) - (Real.sin a - h * Real.cos a) ∧
      Real.sin (a - h) - (Real.sin a - h * Real.cos a) ≤ 0
  constructor
  · nlinarith [hb.1, herrlt]
  · exact hb.2

theorem gap1 :
    Approx (Real.sin (29 * Real.pi / 180))
      (Real.sin (Real.pi / 6) -
        Real.pi / 180 * Real.cos (Real.pi / 6))
      (1 / 10000 : ℝ) := by
  unfold Approx
  have h := target_linearization_signed
  rw [abs_lt]
  constructor
  · nlinarith [h.1]
  · nlinarith [h.2]

theorem gap2 :
    Approx
      (Real.sin (Real.pi / 6) -
        Real.pi / 180 * Real.cos (Real.pi / 6))
      (4849 / 10000 : ℝ) (1 / 10000 : ℝ) := by
  unfold Approx
  have h := decimal_linearization_signed
  rw [abs_lt]
  constructor
  · nlinarith [h.1]
  · nlinarith [h.2]

theorem gap3 :
    Approx (Real.sin (29 * Real.pi / 180))
      (4849 / 10000 : ℝ) (1 / 10000 : ℝ) := by
  unfold Approx
  have ht := target_linearization_signed
  have hd := decimal_linearization_signed
  have hsum :
      Real.sin (29 * Real.pi / 180) - (4849 / 10000 : ℝ) =
        (Real.sin (29 * Real.pi / 180) -
          (Real.sin (Real.pi / 6) -
            Real.pi / 180 * Real.cos (Real.pi / 6))) +
        ((Real.sin (Real.pi / 6) -
            Real.pi / 180 * Real.cos (Real.pi / 6)) -
          (4849 / 10000 : ℝ)) := by
    ring
  rw [hsum, abs_lt]
  constructor
  · nlinarith [ht.1, hd.1]
  · nlinarith [ht.2, hd.2]

end

end ProofGap.Exercise1100
