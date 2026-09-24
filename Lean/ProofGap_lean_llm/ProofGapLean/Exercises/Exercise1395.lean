import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Tactic.Positivity

namespace ProofGap.Exercise1395

noncomputable section

def approximationError (x : ℝ) : ℝ :=
  |Real.cos x - (1 - x ^ 2 / 2)|

def tolerance : ℝ := 0.0001
def certifiedRadius : ℝ := 0.2213

private theorem sin_cubic_lower (t : ℝ) (ht : 0 ≤ t) :
    t - t ^ 3 / 6 ≤ Real.sin t := by
  let f : ℝ → ℝ := fun u => Real.sin u - u + u ^ 3 / 6
  have hfderiv (u : ℝ) :
      HasDerivAt f (Real.cos u - 1 + u ^ 2 / 2) u := by
    dsimp [f]
    convert ((Real.hasDerivAt_sin u).sub (hasDerivAt_id u)).add
      (((hasDerivAt_id u).pow 3).div_const 6) using 1 <;>
      simp [id] <;> ring
  have hdiff : Differentiable ℝ f := fun u => (hfderiv u).differentiableAt
  have hmono : Monotone f :=
    monotone_of_deriv_nonneg hdiff (fun u => by
      rw [(hfderiv u).deriv]
      have hu := Real.one_sub_sq_div_two_le_cos (x := u)
      linarith)
  have h := hmono ht
  simp [f] at h
  linarith

theorem gap1 (x : ℝ) :
    approximationError x ≤ |x| ^ 4 / (Nat.factorial 4 : ℝ) := by
  have hlower : 1 - x ^ 2 / 2 ≤ Real.cos x :=
    Real.one_sub_sq_div_two_le_cos (x := x)
  have herr_nonneg : 0 ≤ Real.cos x - (1 - x ^ 2 / 2) :=
    sub_nonneg.mpr hlower
  have hx4 : 0 ≤ x ^ 4 := by
    nlinarith [sq_nonneg (x ^ 2)]
  have habs4 : |x| ^ 4 = x ^ 4 := by
    calc
      |x| ^ 4 = |x ^ 4| := (abs_pow x 4).symm
      _ = x ^ 4 := abs_of_nonneg hx4
  have hupper : Real.cos x ≤ 1 - x ^ 2 / 2 + x ^ 4 / 24 := by
    by_cases hlarge : 12 ≤ x ^ 2
    · have hcos : Real.cos x ≤ 1 := Real.cos_le_one x
      have hprod : 0 ≤ x ^ 2 * (x ^ 2 - 12) :=
        mul_nonneg (sq_nonneg x) (sub_nonneg.mpr hlarge)
      nlinarith
    · have hsmall : x ^ 2 < 12 := lt_of_not_ge hlarge
      let t : ℝ := |x| / 2
      have ht : 0 ≤ t := by
        dsimp [t]
        positivity
      have habs2 : |x| ^ 2 = x ^ 2 := by
        calc
          |x| ^ 2 = |x ^ 2| := (abs_pow x 2).symm
          _ = x ^ 2 := abs_of_nonneg (sq_nonneg x)
      have hxt2 : x ^ 2 = 4 * t ^ 2 := by
        calc
          x ^ 2 = |x| ^ 2 := habs2.symm
          _ = 4 * t ^ 2 := by
            dsimp [t]
            ring
      have hxt4 : x ^ 4 = 16 * t ^ 4 := by
        calc
          x ^ 4 = |x| ^ 4 := habs4.symm
          _ = 16 * t ^ 4 := by
            dsimp [t]
            ring
      have ht2 : t ^ 2 < 3 := by
        nlinarith
      have hsin : t - t ^ 3 / 6 ≤ Real.sin t :=
        sin_cubic_lower t ht
      have hbase : 0 ≤ t - t ^ 3 / 6 := by
        have hfactor : 0 ≤ 1 - t ^ 2 / 6 := by
          nlinarith
        have hp := mul_nonneg ht hfactor
        nlinarith
      have hsinnonneg : 0 ≤ Real.sin t := le_trans hbase hsin
      have hsquare : (t - t ^ 3 / 6) ^ 2 ≤ Real.sin t ^ 2 := by
        have hp := mul_nonneg (sub_nonneg.mpr hsin)
          (add_nonneg hsinnonneg hbase)
        nlinarith
      have hcosform : Real.cos x = 1 - 2 * Real.sin t ^ 2 := by
        calc
          Real.cos x = Real.cos |x| := (Real.cos_abs x).symm
          _ = Real.cos (2 * t) := by
            congr 1
            dsimp [t]
            ring
          _ = Real.cos t ^ 2 - Real.sin t ^ 2 := Real.cos_two_mul' t
          _ = 1 - 2 * Real.sin t ^ 2 := by
            nlinarith [Real.sin_sq_add_cos_sq t]
      rw [hcosform, hxt2, hxt4]
      nlinarith [hsquare, sq_nonneg (t ^ 3)]
  rw [approximationError, abs_of_nonneg herr_nonneg, habs4]
  norm_num [Nat.factorial]
  linarith

theorem gap2 (x : ℝ)
    (hx : |x| ^ 4 / (Nat.factorial 4 : ℝ) < tolerance) :
    approximationError x < tolerance := by
  exact lt_of_le_of_lt (gap1 x) hx

theorem gap3 (x : ℝ)
    (hx : |x| ^ 4 / (Nat.factorial 4 : ℝ) < tolerance) :
    approximationError x < tolerance := by
  exact gap2 x hx

theorem gap4 (x : ℝ) (hx : |x| < certifiedRadius) :
    approximationError x < tolerance := by
  apply gap2 x
  have ha : 0 ≤ |x| := abs_nonneg x
  have hb : 0 < certifiedRadius := by
    norm_num [certifiedRadius]
  have hprod :
      0 < (certifiedRadius - |x|) * (certifiedRadius + |x|) :=
    mul_pos (sub_pos.mpr hx) (add_pos_of_pos_of_nonneg hb ha)
  have hsq : |x| ^ 2 < certifiedRadius ^ 2 := by
    nlinarith [hprod]
  have hsum_sq : 0 < certifiedRadius ^ 2 + |x| ^ 2 :=
    add_pos_of_pos_of_nonneg (pow_pos hb 2) (sq_nonneg |x|)
  have hprod_sq :
      0 < (certifiedRadius ^ 2 - |x| ^ 2) *
        (certifiedRadius ^ 2 + |x| ^ 2) :=
    mul_pos (sub_pos.mpr hsq) hsum_sq
  have hfour : |x| ^ 4 < certifiedRadius ^ 4 := by
    nlinarith [hprod_sq]
  calc
    |x| ^ 4 / (Nat.factorial 4 : ℝ) <
        certifiedRadius ^ 4 / (Nat.factorial 4 : ℝ) :=
      div_lt_div_of_pos_right hfour (by norm_num)
    _ < tolerance := by
      norm_num [certifiedRadius, tolerance, Nat.factorial]

theorem gap5 (x : ℝ)
    (hx : x ∈ {y : ℝ | |y| < certifiedRadius}) :
    approximationError x < tolerance := by
  exact gap4 x hx

end

end ProofGap.Exercise1395
