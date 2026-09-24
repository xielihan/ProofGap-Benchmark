import ProofGapLean.Prelude.Elementary
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

namespace ProofGap.Exercise3123

noncomputable section

def lagrangeSqrtModel (x : ℝ) : ℝ :=
  ((x - 25) * (x - 100)) / ((-24 : ℝ) * (-99)) +
    ((x - 1) * (x - 100)) / (24 * (-75 : ℝ)) * 5 +
    ((x - 1) * (x - 25)) / (99 * 75 : ℝ) * 10

def decimalSqrtModel (x : ℝ) : ℝ :=
  0.808 + 0.193 * x - 0.00101 * x ^ 2

def Within (actual rounded tolerance : ℝ) : Prop :=
  |actual - rounded| ≤ tolerance

/--
Exercise 3123, gap 1; replace global informal `≈`
by an explicit error bound on the interpolation interval.
-/
private theorem lagrange_error_bound {x : ℝ}
    (hx : x ∈ Set.Icc (1 : ℝ) 100) :
    |Real.sqrt x - lagrangeSqrtModel x| ≤ 106 / 99 := by
  rcases hx with ⟨hx1, hx100⟩
  have hx0 : 0 ≤ x := by linarith
  let t : ℝ := Real.sqrt x
  have ht0 : 0 ≤ t := by
    dsimp [t]
    exact Real.sqrt_nonneg x
  have ht_sq : t ^ 2 = x := by
    dsimp [t]
    exact Real.sq_sqrt hx0
  have ht1 : 1 ≤ t := by
    nlinarith [sq_nonneg (t - 1)]
  have ht10 : t ≤ 10 := by
    nlinarith [sq_nonneg (t - 10)]
  have hmodel :
      lagrangeSqrtModel x = (800 + 191 * x - x ^ 2) / 990 := by
    unfold lagrangeSqrtModel
    ring
  have herr :
      Real.sqrt x - lagrangeSqrtModel x =
        ((t + 16) * (t - 1) * (t - 5) * (t - 10)) / 990 := by
    change t - lagrangeSqrtModel x = _
    rw [hmodel, ← ht_sq]
    ring
  rw [herr]
  by_cases ht5 : t ≤ 5
  · have hp_nonneg :
        0 ≤ (t + 16) * (t - 1) * (t - 5) * (t - 10) := by
      have hfirst : 0 ≤ (t + 16) * (t - 1) :=
        mul_nonneg (by linarith) (by linarith)
      have hthree : (t + 16) * (t - 1) * (t - 5) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hfirst (by linarith)
      exact mul_nonneg_of_nonpos_of_nonpos hthree (by linarith)
    have hA0 : 0 ≤ (t + 16) * (10 - t) :=
      mul_nonneg (by linarith) (by linarith)
    have hB0 : 0 ≤ (t - 1) * (5 - t) :=
      mul_nonneg (by linarith) (by linarith)
    have hA : (t + 16) * (10 - t) ≤ 189 := by
      calc
        (t + 16) * (10 - t) ≤ 21 * (10 - t) :=
          mul_le_mul_of_nonneg_right (by linarith) (by linarith)
        _ ≤ 21 * 9 := mul_le_mul_of_nonneg_left (by linarith) (by norm_num)
        _ = 189 := by norm_num
    have hB : (t - 1) * (5 - t) ≤ 4 := by
      nlinarith [sq_nonneg (t - 3)]
    have hp_le :
        (t + 16) * (t - 1) * (t - 5) * (t - 10) ≤ 1060 := by
      calc
        (t + 16) * (t - 1) * (t - 5) * (t - 10) =
            ((t + 16) * (10 - t)) * ((t - 1) * (5 - t)) := by ring
        _ ≤ 189 * ((t - 1) * (5 - t)) :=
          mul_le_mul_of_nonneg_right hA hB0
        _ ≤ 189 * 4 := mul_le_mul_of_nonneg_left hB (by norm_num)
        _ ≤ 1060 := by norm_num
    have hfrac :
        0 ≤ ((t + 16) * (t - 1) * (t - 5) * (t - 10)) / 990 :=
      div_nonneg hp_nonneg (by norm_num)
    rw [abs_of_nonneg hfrac]
    nlinarith
  · have ht5' : 5 ≤ t := by linarith
    have hmiddle0 : 0 ≤ (t - 5) * (10 - t) :=
      mul_nonneg (by linarith) (by linarith)
    have hright :
        (t + 16) * (t - 1) * (t - 5) * (10 - t) ≤ 1060 := by
      by_cases h7 : t ≤ 7
      · have hocert : 0 ≤ (7 - t) * (7 + t + 15) :=
          mul_nonneg (by linarith) (by linarith)
        have houter : (t + 16) * (t - 1) ≤ 138 := by
          nlinarith [hocert]
        have hmcert : 0 ≤ (t - 7) * (t - 8) :=
          mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)
        have hmiddle : (t - 5) * (10 - t) ≤ 6 := by
          nlinarith [hmcert]
        calc
          (t + 16) * (t - 1) * (t - 5) * (10 - t) =
              ((t + 16) * (t - 1)) * ((t - 5) * (10 - t)) := by ring
          _ ≤ 138 * ((t - 5) * (10 - t)) :=
            mul_le_mul_of_nonneg_right houter hmiddle0
          _ ≤ 138 * 6 := mul_le_mul_of_nonneg_left hmiddle (by norm_num)
          _ ≤ 1060 := by norm_num
      · by_cases h8 : t ≤ 8
        · have hocert : 0 ≤ (8 - t) * (8 + t + 15) :=
            mul_nonneg (by linarith) (by linarith)
          have houter : (t + 16) * (t - 1) ≤ 168 := by
            nlinarith [hocert]
          have hmiddle : (t - 5) * (10 - t) ≤ (25 / 4 : ℝ) := by
            nlinarith [sq_nonneg (t - 15 / 2)]
          calc
            (t + 16) * (t - 1) * (t - 5) * (10 - t) =
                ((t + 16) * (t - 1)) * ((t - 5) * (10 - t)) := by ring
            _ ≤ 168 * ((t - 5) * (10 - t)) :=
              mul_le_mul_of_nonneg_right houter hmiddle0
            _ ≤ 168 * (25 / 4) :=
              mul_le_mul_of_nonneg_left hmiddle (by norm_num)
            _ ≤ 1060 := by norm_num
        · by_cases h33 : t ≤ (33 / 4 : ℝ)
          · have hocert :
                0 ≤ ((33 / 4 : ℝ) - t) * ((33 / 4 : ℝ) + t + 15) :=
              mul_nonneg (by linarith) (by linarith)
            have houter :
                (t + 16) * (t - 1) ≤ (2813 / 16 : ℝ) := by
              nlinarith [hocert]
            have hmcert : 0 ≤ (t - 7) * (t - 8) :=
              mul_nonneg (by linarith) (by linarith)
            have hmiddle : (t - 5) * (10 - t) ≤ 6 := by
              nlinarith [hmcert]
            calc
              (t + 16) * (t - 1) * (t - 5) * (10 - t) =
                  ((t + 16) * (t - 1)) * ((t - 5) * (10 - t)) := by ring
              _ ≤ (2813 / 16) * ((t - 5) * (10 - t)) :=
                mul_le_mul_of_nonneg_right houter hmiddle0
              _ ≤ (2813 / 16) * 6 :=
                mul_le_mul_of_nonneg_left hmiddle (by norm_num)
              _ ≤ 1060 := by norm_num
          · by_cases h17 : t ≤ (17 / 2 : ℝ)
            · have hocert :
                  0 ≤ ((17 / 2 : ℝ) - t) * ((17 / 2 : ℝ) + t + 15) :=
                mul_nonneg (by linarith) (by linarith)
              have houter :
                  (t + 16) * (t - 1) ≤ (735 / 4 : ℝ) := by
                nlinarith [hocert]
              have hmcert :
                  0 ≤ (t - 33 / 4) * (t + 33 / 4 - 15) :=
                mul_nonneg (by linarith) (by linarith)
              have hmiddle :
                  (t - 5) * (10 - t) ≤ (91 / 16 : ℝ) := by
                nlinarith [hmcert]
              calc
                (t + 16) * (t - 1) * (t - 5) * (10 - t) =
                    ((t + 16) * (t - 1)) * ((t - 5) * (10 - t)) := by ring
                _ ≤ (735 / 4) * ((t - 5) * (10 - t)) :=
                  mul_le_mul_of_nonneg_right houter hmiddle0
                _ ≤ (735 / 4) * (91 / 16) :=
                  mul_le_mul_of_nonneg_left hmiddle (by norm_num)
                _ ≤ 1060 := by norm_num
            · by_cases h9 : t ≤ 9
              · have hocert : 0 ≤ (9 - t) * (9 + t + 15) :=
                  mul_nonneg (by linarith) (by linarith)
                have houter : (t + 16) * (t - 1) ≤ 200 := by
                  nlinarith [hocert]
                have hmcert :
                    0 ≤ (t - 17 / 2) * (t + 17 / 2 - 15) :=
                  mul_nonneg (by linarith) (by linarith)
                have hmiddle :
                    (t - 5) * (10 - t) ≤ (21 / 4 : ℝ) := by
                  nlinarith [hmcert]
                calc
                  (t + 16) * (t - 1) * (t - 5) * (10 - t) =
                      ((t + 16) * (t - 1)) * ((t - 5) * (10 - t)) := by ring
                  _ ≤ 200 * ((t - 5) * (10 - t)) :=
                    mul_le_mul_of_nonneg_right houter hmiddle0
                  _ ≤ 200 * (21 / 4) :=
                    mul_le_mul_of_nonneg_left hmiddle (by norm_num)
                  _ ≤ 1060 := by norm_num
              · have hocert : 0 ≤ (10 - t) * (10 + t + 15) :=
                  mul_nonneg (by linarith) (by linarith)
                have houter : (t + 16) * (t - 1) ≤ 234 := by
                  nlinarith [hocert]
                have hmcert : 0 ≤ (t - 9) * (t + 9 - 15) :=
                  mul_nonneg (by linarith) (by linarith)
                have hmiddle : (t - 5) * (10 - t) ≤ 4 := by
                  nlinarith [hmcert]
                calc
                  (t + 16) * (t - 1) * (t - 5) * (10 - t) =
                      ((t + 16) * (t - 1)) * ((t - 5) * (10 - t)) := by ring
                  _ ≤ 234 * ((t - 5) * (10 - t)) :=
                    mul_le_mul_of_nonneg_right houter hmiddle0
                  _ ≤ 234 * 4 :=
                    mul_le_mul_of_nonneg_left hmiddle (by norm_num)
                  _ ≤ 1060 := by norm_num
    have hp_nonpos :
        (t + 16) * (t - 1) * (t - 5) * (t - 10) ≤ 0 := by
      have hthree : 0 ≤ (t + 16) * (t - 1) * (t - 5) :=
        mul_nonneg
          (mul_nonneg (by linarith) (by linarith))
          (by linarith)
      exact mul_nonpos_of_nonneg_of_nonpos hthree (by linarith)
    have hp_ge :
        -1060 ≤ (t + 16) * (t - 1) * (t - 5) * (t - 10) := by
      calc
        -1060 ≤ -((t + 16) * (t - 1) * (t - 5) * (10 - t)) :=
          neg_le_neg hright
        _ = (t + 16) * (t - 1) * (t - 5) * (t - 10) := by ring
    have hfrac :
        ((t + 16) * (t - 1) * (t - 5) * (t - 10)) / 990 ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg hp_nonpos (by norm_num)
    rw [abs_of_nonpos hfrac]
    nlinarith

theorem gap1 :
    ∀ x ∈ Set.Icc (1 : ℝ) 100,
      Within (Real.sqrt x) (lagrangeSqrtModel x) (11 / 10) := by
  intro x hx
  unfold Within
  exact (lagrange_error_bound hx).trans (by norm_num)

/--
Exercise 3123, gap 2; the rounded-coefficient model
is also restricted to the data interval with a quantitative error.
-/
theorem gap2 :
    ∀ x ∈ Set.Icc (1 : ℝ) 100,
      Within (Real.sqrt x) (decimalSqrtModel x) (11 / 10) := by
  intro x hx
  unfold Within
  have hlag := lagrange_error_bound hx
  have hx0 : 0 ≤ x := by
    exact le_trans (by norm_num) hx.1
  have hxsq : x ^ 2 ≤ 10000 := by
    have hprod : 0 ≤ (100 - x) * (100 + x) :=
      mul_nonneg (by linarith [hx.2]) (by linarith)
    nlinarith
  have hdiff_eq :
      lagrangeSqrtModel x - decimalSqrtModel x =
        1 / 12375 - 7 * x / 99000 - x ^ 2 / 9900000 := by
    unfold lagrangeSqrtModel decimalSqrtModel
    ring
  have hdiff :
      |lagrangeSqrtModel x - decimalSqrtModel x| ≤ 1 / 100 := by
    rw [hdiff_eq, abs_le]
    constructor <;> nlinarith [sq_nonneg x]
  calc
    |Real.sqrt x - decimalSqrtModel x| =
        |(Real.sqrt x - lagrangeSqrtModel x) +
          (lagrangeSqrtModel x - decimalSqrtModel x)| := by ring
    _ ≤ |Real.sqrt x - lagrangeSqrtModel x| +
          |lagrangeSqrtModel x - decimalSqrtModel x| := abs_add_le _ _
    _ ≤ 106 / 99 + 1 / 100 := add_le_add hlag hdiff
    _ ≤ 11 / 10 := by norm_num

/-- Exercise 3123, gap 3; evaluate the model, not a free `y`. -/
theorem gap3 :
    Within (decimalSqrtModel 4) 1.564 0.0005 := by
  norm_num [Within, decimalSqrtModel]

/-- Exercise 3123, gap 4; evaluate the model, not a free `y`. -/
theorem gap4 :
    Within (decimalSqrtModel 9) 2.463 0.0005 := by
  norm_num [Within, decimalSqrtModel]

/-- Exercise 3123, gap 5; evaluate the model, not a free `y`. -/
theorem gap5 :
    Within (decimalSqrtModel 16) 3.637 0.0005 := by
  norm_num [Within, decimalSqrtModel]

/-- Exercise 3123, gap 6; evaluate the model, not a free `y`. -/
theorem gap6 :
    Within (decimalSqrtModel 36) 6.447 0.0005 := by
  norm_num [Within, decimalSqrtModel]

end

end ProofGap.Exercise3123
