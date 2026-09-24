import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

namespace ProofGap.Exercise1396_5

noncomputable section

def Approx (x y ε : ℝ) : Prop := |x - y| < ε
def x : ℝ := Real.pi / 10
def sinPartial : ℝ := x - x ^ 3 / (Nat.factorial 3 : ℝ) +
  x ^ 5 / (Nat.factorial 5 : ℝ)
def remainder : ℝ := |Real.sin x - sinPartial|
def remainderBound : ℝ := x ^ 7 / (Nat.factorial 7 : ℝ)

private theorem positive_quadratic_root_bounds {s : ℝ}
    (hs : 0 < s) (hq : 4 * s ^ 2 + 2 * s - 1 = 0) :
    (30901699437 / 100000000000 : ℝ) < s ∧
    s < (30901699438 / 100000000000 : ℝ) := by
  constructor
  · by_contra h
    have hle : s ≤ (30901699437 / 100000000000 : ℝ) := le_of_not_gt h
    have hmul :
        0 ≤ ((30901699437 / 100000000000 : ℝ) - s) *
          ((30901699437 / 100000000000 : ℝ) + s) :=
      mul_nonneg (sub_nonneg.mpr hle)
        (add_nonneg (by norm_num) (le_of_lt hs))
    nlinarith only [hq, hmul]
  · by_contra h
    have hle : (30901699438 / 100000000000 : ℝ) ≤ s := le_of_not_gt h
    have hcq :
        0 < 4 * (30901699438 / 100000000000 : ℝ) ^ 2 +
          2 * (30901699438 / 100000000000 : ℝ) - 1 := by
      norm_num
    have hfactor :
        0 ≤ (s - (30901699438 / 100000000000 : ℝ)) *
          (4 * (s + (30901699438 / 100000000000 : ℝ)) + 2) := by
      apply mul_nonneg (sub_nonneg.mpr hle)
      positivity
    have hmono :
        4 * (30901699438 / 100000000000 : ℝ) ^ 2 +
            2 * (30901699438 / 100000000000 : ℝ) - 1 ≤
          4 * s ^ 2 + 2 * s - 1 := by
      calc
        4 * (30901699438 / 100000000000 : ℝ) ^ 2 +
              2 * (30901699438 / 100000000000 : ℝ) - 1 ≤
            (4 * (30901699438 / 100000000000 : ℝ) ^ 2 +
              2 * (30901699438 / 100000000000 : ℝ) - 1) +
              (s - (30901699438 / 100000000000 : ℝ)) *
                (4 * (s + (30901699438 / 100000000000 : ℝ)) + 2) :=
          le_add_of_nonneg_right hfactor
        _ = 4 * s ^ 2 + 2 * s - 1 := by ring
    rw [hq] at hmono
    exact (not_lt_of_ge hmono) hcq

private theorem numerical_bounds :
    (30901705421 / 100000000000 : ℝ) < sinPartial ∧
    sinPartial < (30901705423 / 100000000000 : ℝ) ∧
    (30901699437 / 100000000000 : ℝ) < Real.sin x ∧
    Real.sin x < (30901699438 / 100000000000 : ℝ) ∧
    (599 / 10000000000 : ℝ) < remainderBound ∧
    remainderBound < (601 / 10000000000 : ℝ) := by
  set_option maxHeartbeats 2000000 in
    let a : ℝ := 314159265358 / 100000000000
    let b : ℝ := 314159265359 / 100000000000
    have ha : 0 < a := by norm_num [a]
    have hb : 0 < b := by norm_num [b]
    have hpL : a < Real.pi := by
      dsimp [a]
      nlinarith only [Real.pi_gt_d20]
    have hpU : Real.pi < b := by
      dsimp [b]
      nlinarith only [Real.pi_lt_d20]
    have h3l : a ^ 3 < Real.pi ^ 3 := by
      have h : 0 < (Real.pi - a) *
          (Real.pi ^ 2 + Real.pi * a + a ^ 2) :=
        mul_pos (sub_pos.mpr hpL) (by positivity)
      nlinarith only [h]
    have h3u : Real.pi ^ 3 < b ^ 3 := by
      have h : 0 < (b - Real.pi) *
          (b ^ 2 + b * Real.pi + Real.pi ^ 2) :=
        mul_pos (sub_pos.mpr hpU) (by positivity)
      nlinarith only [h]
    have h5l : a ^ 5 < Real.pi ^ 5 := by
      have h : 0 < (Real.pi - a) *
          (Real.pi ^ 4 + Real.pi ^ 3 * a + Real.pi ^ 2 * a ^ 2 +
            Real.pi * a ^ 3 + a ^ 4) :=
        mul_pos (sub_pos.mpr hpL) (by positivity)
      nlinarith only [h]
    have h5u : Real.pi ^ 5 < b ^ 5 := by
      have h : 0 < (b - Real.pi) *
          (b ^ 4 + b ^ 3 * Real.pi + b ^ 2 * Real.pi ^ 2 +
            b * Real.pi ^ 3 + Real.pi ^ 4) :=
        mul_pos (sub_pos.mpr hpU) (by positivity)
      nlinarith only [h]
    have h7l : a ^ 7 < Real.pi ^ 7 := by
      have h : 0 < (Real.pi - a) *
          (Real.pi ^ 6 + Real.pi ^ 5 * a + Real.pi ^ 4 * a ^ 2 +
            Real.pi ^ 3 * a ^ 3 + Real.pi ^ 2 * a ^ 4 +
            Real.pi * a ^ 5 + a ^ 6) :=
        mul_pos (sub_pos.mpr hpL) (by positivity)
      nlinarith only [h]
    have h7u : Real.pi ^ 7 < b ^ 7 := by
      have h : 0 < (b - Real.pi) *
          (b ^ 6 + b ^ 5 * Real.pi + b ^ 4 * Real.pi ^ 2 +
            b ^ 3 * Real.pi ^ 3 + b ^ 2 * Real.pi ^ 4 +
            b * Real.pi ^ 5 + Real.pi ^ 6) :=
        mul_pos (sub_pos.mpr hpU) (by positivity)
      nlinarith only [h]
    norm_num [a, b] at hpL hpU h3l h3u h5l h5u h7l h7u
    have hpartial :
        (30901705421 / 100000000000 : ℝ) < sinPartial ∧
        sinPartial < (30901705423 / 100000000000 : ℝ) := by
      constructor
      · norm_num [sinPartial, x] <;>
          nlinarith only [hpL, hpU, h3l, h3u, h5l, h5u]
      · norm_num [sinPartial, x] <;>
          nlinarith only [hpL, hpU, h3l, h3u, h5l, h5u]
    have hs2 :
        Real.sin (2 * x) = 2 * Real.sin x * Real.cos x := by
      rw [show (2 : ℝ) * x = x + x by ring, Real.sin_add]
      ring
    have hc2 :
        Real.cos (2 * x) = Real.cos x ^ 2 - Real.sin x ^ 2 := by
      rw [show (2 : ℝ) * x = x + x by ring, Real.cos_add]
      ring
    have hs4 :
        Real.sin (4 * x) =
          4 * Real.sin x * Real.cos x *
            (Real.cos x ^ 2 - Real.sin x ^ 2) := by
      calc
        Real.sin (4 * x) = Real.sin (2 * x + 2 * x) := by
          congr 1
          ring
        _ = 4 * Real.sin x * Real.cos x *
            (Real.cos x ^ 2 - Real.sin x ^ 2) := by
          rw [Real.sin_add, hs2, hc2]
          ring
    have hc4 :
        Real.cos (4 * x) =
          Real.cos x ^ 4 - 6 * Real.sin x ^ 2 * Real.cos x ^ 2 +
            Real.sin x ^ 4 := by
      calc
        Real.cos (4 * x) = Real.cos (2 * x + 2 * x) := by
          congr 1
          ring
        _ = Real.cos x ^ 4 - 6 * Real.sin x ^ 2 * Real.cos x ^ 2 +
            Real.sin x ^ 4 := by
          rw [Real.cos_add, hs2, hc2]
          ring
    have hfive :
        Real.sin (5 * x) =
          5 * Real.sin x * Real.cos x ^ 4 -
            10 * Real.sin x ^ 3 * Real.cos x ^ 2 + Real.sin x ^ 5 := by
      calc
        Real.sin (5 * x) = Real.sin (4 * x + x) := by
          congr 1
          ring
        _ = 5 * Real.sin x * Real.cos x ^ 4 -
            10 * Real.sin x ^ 3 * Real.cos x ^ 2 + Real.sin x ^ 5 := by
          rw [Real.sin_add, hs4, hc4]
          ring
    have hc_sq : Real.cos x ^ 2 = 1 - Real.sin x ^ 2 := by
      nlinarith only [Real.sin_sq_add_cos_sq x]
    have hc_four : Real.cos x ^ 4 = (1 - Real.sin x ^ 2) ^ 2 := by
      calc
        Real.cos x ^ 4 = (Real.cos x ^ 2) ^ 2 := by ring
        _ = (1 - Real.sin x ^ 2) ^ 2 := by rw [hc_sq]
    have hpoly :
        Real.sin (5 * x) =
          16 * Real.sin x ^ 5 - 20 * Real.sin x ^ 3 + 5 * Real.sin x := by
      calc
        Real.sin (5 * x) =
            5 * Real.sin x * Real.cos x ^ 4 -
              10 * Real.sin x ^ 3 * Real.cos x ^ 2 + Real.sin x ^ 5 := hfive
        _ = 16 * Real.sin x ^ 5 - 20 * Real.sin x ^ 3 +
            5 * Real.sin x := by
          rw [hc_four, hc_sq]
          ring
    have hx5 : 5 * x = Real.pi / 2 := by
      dsimp [x]
      ring
    have hsin5 : Real.sin (5 * x) = 1 := by
      rw [hx5, Real.sin_pi_div_two]
    have hxpos : 0 < x := by
      dsimp [x]
      nlinarith only [Real.pi_pos]
    have hxltpi : x < Real.pi := by
      dsimp [x]
      nlinarith only [Real.pi_pos]
    have hspos : 0 < Real.sin x :=
      Real.sin_pos_of_pos_of_lt_pi hxpos hxltpi
    have hxlt : x < 1 := by
      dsimp [x]
      nlinarith only [Real.pi_lt_d20]
    have hslt : Real.sin x < 1 := by
      have hab : |Real.sin x| ≤ |x| := Real.abs_sin_le_abs
      rw [abs_of_pos hxpos] at hab
      calc
        Real.sin x ≤ |Real.sin x| := le_abs_self (Real.sin x)
        _ ≤ x := hab
        _ < 1 := hxlt
    have heq :
        16 * Real.sin x ^ 5 - 20 * Real.sin x ^ 3 +
            5 * Real.sin x - 1 = 0 := by
      linarith only [hpoly, hsin5]
    have hid :
        16 * Real.sin x ^ 5 - 20 * Real.sin x ^ 3 +
            5 * Real.sin x - 1 =
          (Real.sin x - 1) *
            (4 * Real.sin x ^ 2 + 2 * Real.sin x - 1) ^ 2 := by
      ring
    have hprod :
        (Real.sin x - 1) *
            (4 * Real.sin x ^ 2 + 2 * Real.sin x - 1) ^ 2 = 0 := by
      rw [← hid]
      exact heq
    have hquad : 4 * Real.sin x ^ 2 + 2 * Real.sin x - 1 = 0 := by
      rcases mul_eq_zero.mp hprod with hsone | hsq
      · nlinarith only [hsone, hslt]
      · nlinarith only [hsq,
          sq_nonneg (4 * Real.sin x ^ 2 + 2 * Real.sin x - 1)]
    have hsine := positive_quadratic_root_bounds hspos hquad
    have hbound :
        (599 / 10000000000 : ℝ) < remainderBound ∧
        remainderBound < (601 / 10000000000 : ℝ) := by
      constructor
      · norm_num [remainderBound, x] <;> nlinarith only [h7l, h7u]
      · norm_num [remainderBound, x] <;> nlinarith only [h7l, h7u]
    exact
      ⟨hpartial.1, hpartial.2, hsine.1, hsine.2,
        hbound.1, hbound.2⟩

theorem gap1 : Approx (Real.sin x) sinPartial (7 / 100000000 : ℝ) := by
  rcases numerical_bounds with ⟨hpl, hpu, hsl, hsu, hrl, hru⟩
  simp only [Approx, abs_lt]
  constructor <;> norm_num <;> linarith
theorem gap2 : Approx sinPartial 0.309017 (6 / 100000000 : ℝ) := by
  rcases numerical_bounds with ⟨hpl, hpu, hsl, hsu, hrl, hru⟩
  simp only [Approx, abs_lt]
  constructor <;> norm_num <;> linarith
theorem gap3 : Approx (Real.sin x) 0.309017 (1 / 100000000 : ℝ) := by
  rcases numerical_bounds with ⟨hpl, hpu, hsl, hsu, hrl, hru⟩
  simp only [Approx, abs_lt]
  constructor <;> norm_num <;> linarith
theorem gap4 : ∃ Δ : ℝ, Δ = remainder ∧ Δ < remainderBound := by
  rcases numerical_bounds with ⟨hpl, hpu, hsl, hsu, hrl, hru⟩
  refine ⟨remainder, rfl, ?_⟩
  rw [remainder, abs_of_nonpos (by linarith)]
  linarith
theorem gap5 :
    Approx remainderBound (6 * 10 ^ (-8 : ℤ)) (1 / 1000000000 : ℝ) := by
  rcases numerical_bounds with ⟨hpl, hpu, hsl, hsu, hrl, hru⟩
  simp only [Approx, abs_lt]
  constructor <;> norm_num <;> linarith

end
end ProofGap.Exercise1396_5
