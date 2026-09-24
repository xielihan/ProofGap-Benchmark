import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Real.Pi.Bounds

namespace ProofGap.Exercise3124

noncomputable section

open Finset

def degreeSin (x : ℝ) : ℝ :=
  Real.sin (x * Real.pi / 180)

def FitsAnchors (a b : ℝ) : Prop :=
  30 * a + 27000 * b = 1 / 2 ∧
    90 * a + 729000 * b = 1

def cubicModel (x : ℝ) : ℝ :=
  5 * x / 288 * (1 - (x / 150) ^ 2)

def Within (actual rounded tolerance : ℝ) : Prop :=
  |actual - rounded| ≤ tolerance

private lemma real_sin_bound_12 {x : ℝ} (hx : |x| ≤ 2) :
    |Real.sin x -
      (x - x ^ 3 / 6 + x ^ 5 / 120 - x ^ 7 / 5040 +
        x ^ 9 / 362880 - x ^ 11 / 39916800)| ≤
      |x| ^ 12 * (1 / 239500800 : ℝ) := by
  have hc : ‖(x : ℂ)‖ ≤ 2 := by simpa using hx
  have hsmallNeg : ‖-(x : ℂ) * Complex.I‖ / (12 : ℕ).succ ≤ (1 / 2 : ℝ) := by
    simp only [norm_mul, norm_neg, Complex.norm_real, Complex.norm_I]
    norm_num at hc ⊢
    linarith
  have hsmallPos : ‖(x : ℂ) * Complex.I‖ / (12 : ℕ).succ ≤ (1 / 2 : ℝ) := by
    simp only [norm_mul, Complex.norm_real, Complex.norm_I]
    norm_num at hc ⊢
    linarith
  have hneg := Complex.exp_bound' (x := -(x : ℂ) * Complex.I)
    (n := 12) hsmallNeg
  have hpos := Complex.exp_bound' (x := (x : ℂ) * Complex.I)
    (n := 12) hsmallPos
  have hcomplex :
      ‖Complex.sin (x : ℂ) -
        ((x : ℂ) - (x : ℂ) ^ 3 / 6 + (x : ℂ) ^ 5 / 120 -
          (x : ℂ) ^ 7 / 5040 + (x : ℂ) ^ 9 / 362880 -
          (x : ℂ) ^ 11 / 39916800)‖ ≤
        ‖(x : ℂ)‖ ^ 12 * (1 / 239500800 : ℝ) := by
    calc
      _ =
          ‖(Complex.exp (-(x : ℂ) * Complex.I) -
              ∑ m ∈ range 12, (-(x : ℂ) * Complex.I) ^ m / m.factorial) *
                Complex.I / 2 -
            (Complex.exp ((x : ℂ) * Complex.I) -
              ∑ m ∈ range 12, ((x : ℂ) * Complex.I) ^ m / m.factorial) *
                Complex.I / 2‖ := by
          simp [Complex.sin, field, Finset.sum_range_succ, Nat.factorial]
          grind [Complex.I_sq]
      _ ≤
          ‖Complex.exp (-(x : ℂ) * Complex.I) -
              ∑ m ∈ range 12, (-(x : ℂ) * Complex.I) ^ m / m.factorial‖ / 2 +
            ‖Complex.exp ((x : ℂ) * Complex.I) -
              ∑ m ∈ range 12, ((x : ℂ) * Complex.I) ^ m / m.factorial‖ / 2 := by
          grw [norm_sub_le]
          simp
      _ ≤
          (‖-(x : ℂ) * Complex.I‖ ^ 12 / Nat.factorial 12 * 2) / 2 +
            (‖(x : ℂ) * Complex.I‖ ^ 12 / Nat.factorial 12 * 2) / 2 := by
          grw [hneg, hpos]
      _ = _ := by norm_num; ring
  convert hcomplex using 1 <;> norm_cast

private lemma sin_interval_12 {t l u : ℝ}
    (hl : 0 ≤ l) (hlt : l < t) (htu : t < u) (hu : u ≤ 2) :
    l - u ^ 3 / 6 + l ^ 5 / 120 - u ^ 7 / 5040 +
          l ^ 9 / 362880 - u ^ 11 / 39916800 -
          u ^ 12 * (1 / 239500800 : ℝ) < Real.sin t ∧
      Real.sin t <
        u - l ^ 3 / 6 + u ^ 5 / 120 - l ^ 7 / 5040 +
          u ^ 9 / 362880 - l ^ 11 / 39916800 +
          u ^ 12 * (1 / 239500800 : ℝ) := by
  have ht0 : 0 ≤ t := le_trans hl (le_of_lt hlt)
  have ht2 : |t| ≤ 2 := by
    rw [abs_of_nonneg ht0]
    exact (le_of_lt htu).trans hu
  have hs := real_sin_bound_12 ht2
  rw [abs_of_nonneg ht0, abs_le] at hs
  have h3lo : l ^ 3 < t ^ 3 := by gcongr
  have h3hi : t ^ 3 < u ^ 3 := by gcongr
  have h5lo : l ^ 5 < t ^ 5 := by gcongr
  have h5hi : t ^ 5 < u ^ 5 := by gcongr
  have h7lo : l ^ 7 < t ^ 7 := by gcongr
  have h7hi : t ^ 7 < u ^ 7 := by gcongr
  have h9lo : l ^ 9 < t ^ 9 := by gcongr
  have h9hi : t ^ 9 < u ^ 9 := by gcongr
  have h11lo : l ^ 11 < t ^ 11 := by gcongr
  have h11hi : t ^ 11 < u ^ 11 := by gcongr
  have h12 : t ^ 12 < u ^ 12 := by gcongr
  constructor <;> nlinarith [hs.1, hs.2]

private lemma sin_between_cubic_quintic {t : ℝ} (ht0 : 0 ≤ t) (ht2 : t ≤ 2) :
    t - t ^ 3 / 6 + t ^ 5 / 120 - t ^ 7 / 5040 ≤ Real.sin t ∧
      Real.sin t ≤ t - t ^ 3 / 6 + t ^ 5 / 120 := by
  have hs := real_sin_bound_12 (x := t) (by
    rw [abs_of_nonneg ht0]
    exact ht2)
  rw [abs_of_nonneg ht0, abs_le] at hs
  have h75 : t ^ 7 ≤ 4 * t ^ 5 := by
    calc
      t ^ 7 = t ^ 5 * t ^ 2 := by ring
      _ ≤ t ^ 5 * 2 ^ 2 := by gcongr
      _ = 4 * t ^ 5 := by ring
  have h115 : t ^ 11 ≤ 64 * t ^ 5 := by
    calc
      t ^ 11 = t ^ 5 * t ^ 6 := by ring
      _ ≤ t ^ 5 * 2 ^ 6 := by gcongr
      _ = 64 * t ^ 5 := by ring
  have h125 : t ^ 12 ≤ 128 * t ^ 5 := by
    calc
      t ^ 12 = t ^ 5 * t ^ 7 := by ring
      _ ≤ t ^ 5 * 2 ^ 7 := by gcongr
      _ = 128 * t ^ 5 := by ring
  have h97 : t ^ 9 ≤ 4 * t ^ 7 := by
    calc
      t ^ 9 = t ^ 7 * t ^ 2 := by ring
      _ ≤ t ^ 7 * 2 ^ 2 := by gcongr
      _ = 4 * t ^ 7 := by ring
  have h127 : t ^ 12 ≤ 32 * t ^ 7 := by
    calc
      t ^ 12 = t ^ 7 * t ^ 5 := by ring
      _ ≤ t ^ 7 * 2 ^ 5 := by gcongr
      _ = 32 * t ^ 7 := by ring
  have h119 : t ^ 11 ≤ 4 * t ^ 9 := by
    calc
      t ^ 11 = t ^ 9 * t ^ 2 := by ring
      _ ≤ t ^ 9 * 2 ^ 2 := by gcongr
      _ = 4 * t ^ 9 := by ring
  have h129 : t ^ 12 ≤ 8 * t ^ 9 := by
    calc
      t ^ 12 = t ^ 9 * t ^ 3 := by ring
      _ ≤ t ^ 9 * 2 ^ 3 := by gcongr
      _ = 8 * t ^ 9 := by ring
  constructor <;> nlinarith [hs.1, hs.2, h75, h115, h125, h97, h127,
    h119, h129,
    pow_nonneg ht0 5, pow_nonneg ht0 7, pow_nonneg ht0 9,
    pow_nonneg ht0 11, pow_nonneg ht0 12]

private theorem sin20_bound : |Real.sin (Real.pi / 9) - 0.3420| ≤ 0.00005 := by
  have hs := sin_interval_12
    (t := Real.pi / 9)
    (l := (3490658503988659 / 10000000000000000 : ℝ))
    (u := (34906585039886592 / 100000000000000000 : ℝ))
    (by norm_num)
    (by nlinarith [Real.pi_gt_d20])
    (by nlinarith [Real.pi_lt_d20])
    (by norm_num)
  rw [abs_le]
  constructor <;> norm_num at hs ⊢ <;> linarith

private theorem sin40_bound : |Real.sin (2 * Real.pi / 9) - 0.6428| ≤ 0.00005 := by
  have hs := sin_interval_12
    (t := 2 * Real.pi / 9)
    (l := (6981317007977318 / 10000000000000000 : ℝ))
    (u := (69813170079773184 / 100000000000000000 : ℝ))
    (by norm_num)
    (by nlinarith [Real.pi_gt_d20])
    (by nlinarith [Real.pi_lt_d20])
    (by norm_num)
  rw [abs_le]
  constructor <;> norm_num at hs ⊢ <;> linarith

private theorem sin80_bound : |Real.sin (4 * Real.pi / 9) - 0.9848| ≤ 0.00005 := by
  have hs := sin_interval_12
    (t := 4 * Real.pi / 9)
    (l := (13962634015954636 / 10000000000000000 : ℝ))
    (u := (13962634015954637 / 10000000000000000 : ℝ))
    (by norm_num)
    (by nlinarith [Real.pi_gt_d20])
    (by nlinarith [Real.pi_lt_d20])
    (by norm_num)
  rw [abs_le]
  constructor <;> norm_num at hs ⊢ <;> linarith

private theorem uniform_cubic_bound :
    ∀ x ∈ Set.Icc (0 : ℝ) 90,
      |degreeSin x - cubicModel x| ≤ 0.02 := by
  intro x hx
  let t : ℝ := x * Real.pi / 180
  have ht0 : 0 ≤ t := by
    dsimp [t]
    exact div_nonneg (mul_nonneg hx.1 Real.pi_pos.le) (by norm_num)
  have htpi : t ≤ Real.pi / 2 := by
    dsimp [t]
    calc
      x * Real.pi / 180 ≤ 90 * Real.pi / 180 := by
        gcongr
        exact hx.2
      _ = Real.pi / 2 := by ring
  have ht2 : t ≤ 2 := by
    nlinarith [Real.pi_lt_four]
  have hs := sin_between_cubic_quintic ht0 ht2
  have hmodel :
      cubicModel x = 25 / (8 * Real.pi) * t -
        9 / (2 * Real.pi ^ 3) * t ^ 3 := by
    dsimp [cubicModel, t]
    field_simp [Real.pi_ne_zero]
    ring
  have hAlo : (9947 / 10000 : ℝ) < 25 / (8 * Real.pi) := by
    rw [lt_div_iff₀ (by positivity)]
    nlinarith [Real.pi_lt_d4]
  have hAhi : 25 / (8 * Real.pi) < (9948 / 10000 : ℝ) := by
    rw [div_lt_iff₀ (by positivity)]
    nlinarith [Real.pi_gt_d4]
  have hp3lo : (3.1415 : ℝ) ^ 3 < Real.pi ^ 3 := by
    gcongr
    exact Real.pi_gt_d4
  have hp3hi : Real.pi ^ 3 < (3.1416 : ℝ) ^ 3 := by
    gcongr
    exact Real.pi_lt_d4
  have hBlo : (145 / 1000 : ℝ) < 9 / (2 * Real.pi ^ 3) := by
    rw [lt_div_iff₀ (by positivity)]
    norm_num at hp3hi ⊢
    nlinarith
  have hBhi : 9 / (2 * Real.pi ^ 3) < (146 / 1000 : ℝ) := by
    rw [div_lt_iff₀ (by positivity)]
    norm_num at hp3lo ⊢
    nlinarith
  have hz0 : 0 ≤ t ^ 2 := sq_nonneg t
  have hzhi : t ^ 2 ≤ (5 / 2 : ℝ) := by
    nlinarith [sq_nonneg (Real.pi / 2 - t), Real.pi_gt_d4,
      Real.pi_lt_d4]
  have hzsq : (t ^ 2) ^ 2 ≤ (5 / 2 : ℝ) * t ^ 2 := by
    nlinarith [mul_nonneg hz0 (sub_nonneg.mpr hzhi)]
  have hqlo :
      -(1 / 100 : ℝ) ≤
        (1 - 25 / (8 * Real.pi)) +
          (9 / (2 * Real.pi ^ 3) - 1 / 6) * t ^ 2 +
          (t ^ 2) ^ 2 / 120 - (t ^ 2) ^ 3 / 5040 := by
    have hz3 : (t ^ 2) ^ 3 ≤ (5 / 2 : ℝ) * (t ^ 2) ^ 2 := by
      nlinarith [mul_nonneg (sq_nonneg (t ^ 2)) (sub_nonneg.mpr hzhi)]
    have hsq : 0 ≤ (t ^ 2 - 11 / 8) ^ 2 := sq_nonneg _
    nlinarith
  have hqhi :
      (1 - 25 / (8 * Real.pi)) +
          (9 / (2 * Real.pi ^ 3) - 1 / 6) * t ^ 2 +
          (t ^ 2) ^ 2 / 120 ≤ (58 / 10000 : ℝ) := by
    nlinarith
  have hloMul :
      -(1 / 50 : ℝ) ≤
        t * ((1 - 25 / (8 * Real.pi)) +
          (9 / (2 * Real.pi ^ 3) - 1 / 6) * t ^ 2 +
          (t ^ 2) ^ 2 / 120 - (t ^ 2) ^ 3 / 5040) := by
    have hm := mul_nonneg ht0 (sub_nonneg.mpr hqlo)
    nlinarith
  have hhiMul :
      t * ((1 - 25 / (8 * Real.pi)) +
          (9 / (2 * Real.pi ^ 3) - 1 / 6) * t ^ 2 +
          (t ^ 2) ^ 2 / 120) ≤ (1 / 50 : ℝ) := by
    have hm := mul_nonneg ht0 (sub_nonneg.mpr hqhi)
    nlinarith
  rw [degreeSin, hmodel, abs_le]
  constructor
  · nlinarith [hs.1]
  · nlinarith [hs.2]

theorem gap1 :
    ∃ a b : ℝ, FitsAnchors a b := by
  refine ⟨5 / 288, -(5 / 288) * (1 / 150) ^ 2, ?_⟩
  norm_num [FitsAnchors] <;> ring

theorem gap2 :
    ∃ a b : ℝ, FitsAnchors a b := by
  exact gap1

theorem gap3 :
    ∃ a b : ℝ, FitsAnchors a b ∧ a = 5 / 288 := by
  refine ⟨5 / 288, -(5 / 288) * (1 / 150) ^ 2, ?_, rfl⟩
  norm_num [FitsAnchors] <;> ring

theorem gap4 :
    ∃ a b : ℝ,
      FitsAnchors a b ∧ b = -(5 / 288) * (1 / 150) ^ 2 := by
  refine ⟨5 / 288, -(5 / 288) * (1 / 150) ^ 2, ?_, rfl⟩
  norm_num [FitsAnchors] <;> ring

theorem gap5 :
    ∀ x ∈ Set.Icc (0 : ℝ) 90,
      Within (degreeSin x) (cubicModel x) 0.02 := by
  exact uniform_cubic_bound

theorem gap6 : Within (cubicModel 20) 0.341 0.0005 := by
  norm_num [Within, cubicModel, abs_le] <;> ring

theorem gap7 : Within (cubicModel 40) 0.645 0.0005 := by
  norm_num [Within, cubicModel, abs_le] <;> ring

theorem gap8 : Within (cubicModel 80) 0.994 0.0005 := by
  norm_num [Within, cubicModel, abs_le] <;> ring

theorem gap9 : Within (degreeSin 20) 0.3420 0.00005 := by
  change |Real.sin (20 * Real.pi / 180) - 0.3420| ≤ 0.00005
  convert sin20_bound using 1
  congr 2
  ring

theorem gap10 : Within (degreeSin 40) 0.6428 0.00005 := by
  change |Real.sin (40 * Real.pi / 180) - 0.6428| ≤ 0.00005
  convert sin40_bound using 1
  congr 2
  ring

theorem gap11 : Within (degreeSin 80) 0.9848 0.00005 := by
  change |Real.sin (80 * Real.pi / 180) - 0.9848| ≤ 0.00005
  convert sin80_bound using 1
  congr 2
  ring

end

end ProofGap.Exercise3124
