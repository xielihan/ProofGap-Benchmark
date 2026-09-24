import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.DerivativeTest

namespace ProofGap.Exercise1431

noncomputable section

def y (x : ℝ) : ℝ := x * (x - 1) ^ 2 * (x - 2) ^ 3

def r₁ : ℝ := (5 - Real.sqrt 13) / 6
def r₂ : ℝ := (5 + Real.sqrt 13) / 6
def Approx (a b ε : ℝ) : Prop := |a - b| < ε

private theorem sqrt13_sq : (Real.sqrt 13) ^ 2 = 13 := by
  norm_num

private theorem sqrt13_lower : (3.6 : ℝ) < Real.sqrt 13 := by
  nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 13),
    Real.sqrt_nonneg 13]

private theorem sqrt13_upper : Real.sqrt 13 < (3.61 : ℝ) := by
  nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 13),
    Real.sqrt_nonneg 13]

private theorem root_order :
    r₁ < 1 ∧ 1 < r₂ ∧ r₂ < 2 := by
  unfold r₁ r₂
  constructor
  · nlinarith [sqrt13_lower]
  constructor <;> nlinarith [sqrt13_lower, sqrt13_upper]

private theorem quadratic_factor (x : ℝ) :
    6 * x ^ 2 - 10 * x + 2 = 6 * (x - r₁) * (x - r₂) := by
  unfold r₁ r₂
  have hs := sqrt13_sq
  nlinarith

theorem gap1 (x : ℝ) :
    deriv y x = (x - 1) * (x - 2) ^ 2 * (6 * x ^ 2 - 10 * x + 2) := by
  have hx1 : HasDerivAt (fun z : ℝ => z - 1) 1 x := by
    exact (hasDerivAt_id x).sub_const 1
  have hx2 : HasDerivAt (fun z : ℝ => z - 2) 1 x := by
    exact (hasDerivAt_id x).sub_const 2
  unfold y
  convert
    (((hasDerivAt_id x).mul (hx1.fun_pow 2)).mul
      (hx2.fun_pow 3)).deriv using 1 <;>
    simp only [id_eq, Pi.mul_apply, Pi.pow_apply] <;> ring

theorem gap2 (x : ℝ) (hx : x ∈ ({1, 2, r₁, r₂} : Set ℝ)) :
    deriv y x = 0 := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · rw [gap1]
    norm_num
  · rw [gap1]
    norm_num
  · rw [gap1, quadratic_factor]
    ring
  · rw [gap1, quadratic_factor]
    ring

theorem gap3 (x : ℝ) (hx : x < r₁) : deriv y x < 0 := by
  rw [gap1, quadratic_factor]
  have hr₁1 := root_order.1
  have hr₁r₂ : r₁ < r₂ := lt_trans root_order.1 root_order.2.1
  have hx1 : x - 1 < 0 := by linarith
  have hx2 : x - 2 ≠ 0 := by linarith [root_order.2.2]
  have hq : 0 < 6 * (x - r₁) * (x - r₂) := by
    exact mul_pos_of_neg_of_neg
      (mul_neg_of_pos_of_neg (by norm_num) (by linarith))
      (by linarith)
  exact mul_neg_of_neg_of_pos
    (mul_neg_of_neg_of_pos hx1 (sq_pos_of_ne_zero hx2))
    hq

theorem gap4 (x : ℝ) (h₁ : r₁ < x) (h₂ : x < 1) :
    0 < deriv y x := by
  rw [gap1, quadratic_factor]
  have hx2 : x - 2 ≠ 0 := by linarith [root_order.2.2]
  have hq : 6 * (x - r₁) * (x - r₂) < 0 := by
    exact mul_neg_of_pos_of_neg
      (mul_pos (by norm_num) (by linarith))
      (by linarith [root_order.2.1])
  exact mul_pos_of_neg_of_neg
    (mul_neg_of_neg_of_pos (by linarith) (sq_pos_of_ne_zero hx2))
    hq

theorem gap5 (x : ℝ) (h₁ : 1 < x) (h₂ : x < r₂) :
    deriv y x < 0 := by
  rw [gap1, quadratic_factor]
  have hx2 : x - 2 ≠ 0 := by linarith [root_order.2.2]
  have hq : 6 * (x - r₁) * (x - r₂) < 0 := by
    exact mul_neg_of_pos_of_neg
      (mul_pos (by norm_num) (by linarith [root_order.1]))
      (by linarith)
  exact mul_neg_of_pos_of_neg
    (mul_pos (by linarith) (sq_pos_of_ne_zero hx2))
    hq

theorem gap6 (x : ℝ) (h₁ : r₂ < x) (h₂ : x < 2) :
    0 < deriv y x := by
  rw [gap1, quadratic_factor]
  have hr := root_order
  exact mul_pos
    (mul_pos (by linarith [hr.2.1])
      (sq_pos_of_ne_zero (by linarith)))
    (mul_pos (mul_pos (by norm_num) (by linarith [hr.1, hr.2.1]))
      (by linarith))

theorem gap7 (x : ℝ) (hx : 2 < x) : 0 < deriv y x := by
  rw [gap1, quadratic_factor]
  exact mul_pos
    (mul_pos (by linarith) (sq_pos_of_ne_zero (by linarith)))
    (mul_pos (mul_pos (by norm_num)
      (by linarith [root_order.1, root_order.2.1]))
      (by linarith [root_order.2.2]))

theorem gap8 : IsLocalMin y r₁ := by
  have hcont : Continuous y := by
    unfold y
    exact ((continuous_id.mul
      ((continuous_id.sub continuous_const).pow 2)).mul
      ((continuous_id.sub continuous_const).pow 3))
  apply isLocalMin_of_deriv_Ioo
    (a := r₁ - 1) (b := r₁) (c := (1 : ℝ))
    (by linarith) root_order.1 hcont.continuousAt
  · intro x hx
    exact
      (differentiableAt_of_deriv_ne_zero
        (gap3 x hx.2).ne).differentiableWithinAt
  · intro x hx
    exact
      (differentiableAt_of_deriv_ne_zero
        (gap4 x hx.1 hx.2).ne').differentiableWithinAt
  · intro x hx
    exact le_of_lt (gap3 x hx.2)
  · intro x hx
    exact le_of_lt (gap4 x hx.1 hx.2)

theorem gap9 : Approx (y r₁) (-0.76) 0.01 := by
  have hy :
      y r₁ = -(143 * Real.sqrt 13 + 587) / 1458 := by
    unfold y r₁
    calc
      (5 - Real.sqrt 13) / 6 *
            ((5 - Real.sqrt 13) / 6 - 1) ^ 2 *
            ((5 - Real.sqrt 13) / 6 - 2) ^ 3 =
          -(143 * Real.sqrt 13 + 587) / 1458 +
            (((Real.sqrt 13) ^ 2 - 13) *
              ((Real.sqrt 13) ^ 4 + 18 * (Real.sqrt 13) ^ 3 +
                88 * (Real.sqrt 13) ^ 2 - 58 * Real.sqrt 13 - 1313)) /
              46656 := by ring
      _ = -(143 * Real.sqrt 13 + 587) / 1458 := by
        rw [sqrt13_sq]
        ring
  unfold Approx
  rw [hy, abs_lt]
  constructor <;> nlinarith [sqrt13_lower, sqrt13_upper]

theorem gap10 : IsLocalMax y 1 := by
  have hcont : Continuous y := by
    unfold y
    exact ((continuous_id.mul
      ((continuous_id.sub continuous_const).pow 2)).mul
      ((continuous_id.sub continuous_const).pow 3))
  apply isLocalMax_of_deriv_Ioo
    (a := r₁) (b := (1 : ℝ)) (c := r₂)
    root_order.1 root_order.2.1 hcont.continuousAt
  · intro x hx
    exact
      (differentiableAt_of_deriv_ne_zero
        (gap4 x hx.1 hx.2).ne').differentiableWithinAt
  · intro x hx
    exact
      (differentiableAt_of_deriv_ne_zero
        (gap5 x hx.1 hx.2).ne).differentiableWithinAt
  · intro x hx
    exact le_of_lt (gap4 x hx.1 hx.2)
  · intro x hx
    exact le_of_lt (gap5 x hx.1 hx.2)

theorem gap11 : y 1 = 0 := by
  norm_num [y]

theorem gap12 : IsLocalMin y r₂ := by
  have hcont : Continuous y := by
    unfold y
    exact ((continuous_id.mul
      ((continuous_id.sub continuous_const).pow 2)).mul
      ((continuous_id.sub continuous_const).pow 3))
  apply isLocalMin_of_deriv_Ioo
    (a := (1 : ℝ)) (b := r₂) (c := (2 : ℝ))
    root_order.2.1 root_order.2.2 hcont.continuousAt
  · intro x hx
    exact
      (differentiableAt_of_deriv_ne_zero
        (gap5 x hx.1 hx.2).ne).differentiableWithinAt
  · intro x hx
    exact
      (differentiableAt_of_deriv_ne_zero
        (gap6 x hx.1 hx.2).ne').differentiableWithinAt
  · intro x hx
    exact le_of_lt (gap5 x hx.1 hx.2)
  · intro x hx
    exact le_of_lt (gap6 x hx.1 hx.2)

theorem gap13 : Approx (y r₂) (-0.05) 0.01 := by
  have hy :
      y r₂ = (143 * Real.sqrt 13 - 587) / 1458 := by
    unfold y r₂
    calc
      (5 + Real.sqrt 13) / 6 *
            ((5 + Real.sqrt 13) / 6 - 1) ^ 2 *
            ((5 + Real.sqrt 13) / 6 - 2) ^ 3 =
          (143 * Real.sqrt 13 - 587) / 1458 +
            (((Real.sqrt 13) ^ 2 - 13) *
              ((Real.sqrt 13) ^ 4 - 18 * (Real.sqrt 13) ^ 3 +
                88 * (Real.sqrt 13) ^ 2 + 58 * Real.sqrt 13 - 1313)) /
              46656 := by ring
      _ = (143 * Real.sqrt 13 - 587) / 1458 := by
        rw [sqrt13_sq]
        ring
  unfold Approx
  rw [hy, abs_lt]
  constructor <;> nlinarith [sqrt13_lower, sqrt13_upper]

theorem gap14 : ¬ IsLocalMax y 2 := by
  have htwo : y 2 = 0 := by norm_num [y]
  intro hmax
  change {z : ℝ | y z ≤ y 2} ∈ nhds (2 : ℝ) at hmax
  rcases Metric.mem_nhds_iff.mp hmax with ⟨ε, hε, hball⟩
  let d : ℝ := min (ε / 2) (1 / 2)
  have hd : 0 < d := by
    dsimp [d]
    exact lt_min (by linarith) (by norm_num)
  have hdε : d < ε :=
    lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hdball : 2 + d ∈ Metric.ball (2 : ℝ) ε := by
    rw [Metric.mem_ball, Real.dist_eq]
    simpa [abs_of_pos hd] using hdε
  have hle : y (2 + d) ≤ y 2 := hball hdball
  have hpos : 0 < y (2 + d) := by
    unfold y
    have hcube : 0 < (2 + d - 2) ^ 3 := by
      convert pow_pos hd 3 using 1 <;> ring
    exact mul_pos
      (mul_pos (by linarith)
        (sq_pos_of_ne_zero (by linarith)))
      hcube
  rw [htwo] at hle
  linarith

theorem gap15 : ¬ IsLocalMin y 2 := by
  have htwo : y 2 = 0 := by norm_num [y]
  intro hmin
  change {z : ℝ | y 2 ≤ y z} ∈ nhds (2 : ℝ) at hmin
  rcases Metric.mem_nhds_iff.mp hmin with ⟨ε, hε, hball⟩
  let d : ℝ := min (ε / 2) (1 / 2)
  have hd : 0 < d := by
    dsimp [d]
    exact lt_min (by linarith) (by norm_num)
  have hdε : d < ε :=
    lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hdhalf : d ≤ (1 : ℝ) / 2 := min_le_right _ _
  have hdball : 2 - d ∈ Metric.ball (2 : ℝ) ε := by
    rw [Metric.mem_ball, Real.dist_eq]
    have habs : |(2 - d) - 2| = d := by
      rw [show (2 - d) - 2 = -d by ring, abs_neg, abs_of_pos hd]
    rw [habs]
    exact hdε
  have hle : y 2 ≤ y (2 - d) := hball hdball
  have hneg : y (2 - d) < 0 := by
    unfold y
    exact mul_neg_of_pos_of_neg
      (mul_pos (by linarith)
        (sq_pos_of_ne_zero (by linarith)))
      (Odd.pow_neg (show Odd 3 by exact ⟨1, rfl⟩) (by linarith))
  rw [htwo] at hle
  linarith

end
end ProofGap.Exercise1431
