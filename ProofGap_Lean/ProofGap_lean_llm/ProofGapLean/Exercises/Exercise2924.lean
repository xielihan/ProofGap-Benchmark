import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Analysis.Calculus.Deriv.Basic

namespace ProofGap.Exercise2924

noncomputable section

open scoped BigOperators

def angle : ℝ :=
  Real.pi / 180

def cosineTerm (n : ℕ) : ℝ :=
  (-1 : ℝ) ^ n * angle ^ (2 * n) /
    (Nat.factorial (2 * n) : ℝ)

def cosinePartial (m : ℕ) : ℝ :=
  ∑ n ∈ Finset.range m, cosineTerm n

def cosineRemainder : ℝ :=
  Real.cos angle - cosinePartial 2

def Approx (x y ε : ℝ) : Prop :=
  |x - y| < ε

private theorem cosinePartial_two :
    cosinePartial 2 = 1 - angle ^ 2 / 2 := by
  norm_num [cosinePartial, cosineTerm, Finset.sum_range_succ] <;> ring_nf

private theorem Real.abs_sin_sub_id_le (x : ℝ) :
    |Real.sin x - x| ≤ |x| ^ 3 / 6 := by
  have hnonneg : ∀ y : ℝ, 0 ≤ y →
      |Real.sin y - y| ≤ |y| ^ 3 / 6 := by
    intro y hy
    let f : ℝ → ℝ := fun z => Real.sin z - z + z ^ 3 / 6
    have hfderiv (z : ℝ) :
        HasDerivAt f (Real.cos z - 1 + z ^ 2 / 2) z := by
      dsimp [f]
      convert
        ((Real.hasDerivAt_sin z).sub (hasDerivAt_id z)).add
          (((hasDerivAt_id z).pow 3).div_const 6) using 1 <;>
        norm_num <;> ring
    have hfdiff : Differentiable ℝ f := by
      intro z
      exact (hfderiv z).differentiableAt
    have hfmono : Monotone f := by
      apply monotone_of_deriv_nonneg hfdiff
      intro z
      rw [(hfderiv z).deriv]
      nlinarith [Real.one_sub_sq_div_two_le_cos (x := z)]
    have hm : f 0 ≤ f y := hfmono hy
    have hsin_lower : y - y ^ 3 / 6 ≤ Real.sin y := by
      dsimp [f] at hm
      norm_num at hm
      linarith
    have hsin_upper : Real.sin y ≤ y := by
      calc
        Real.sin y ≤ |Real.sin y| := le_abs_self _
        _ ≤ |y| := Real.abs_sin_le_abs
        _ = y := abs_of_nonneg hy
    rw [abs_of_nonpos (sub_nonpos.mpr hsin_upper), abs_of_nonneg hy]
    linarith
  by_cases hx : 0 ≤ x
  · exact hnonneg x hx
  · have hneg : 0 ≤ -x := neg_nonneg.mpr (le_of_not_ge hx)
    have h := hnonneg (-x) hneg
    have heq : Real.sin (-x) - (-x) = -(Real.sin x - x) := by
      rw [Real.sin_neg]
      ring
    rw [heq, abs_neg] at h
    simpa only [abs_neg] using h

theorem gap1 :
    Real.cos angle = ∑' n : ℕ, cosineTerm n := by
  simpa [cosineTerm, mul_comm, mul_left_comm, mul_assoc] using
    (Real.hasSum_cos angle).tsum_eq.symm

theorem gap2 :
    |cosineRemainder| <
      (1 / (Nat.factorial 4 : ℝ)) * angle ^ 4 := by
  let t : ℝ := angle / 2
  have hx : angle = 2 * t := by
    dsimp [t]
    ring
  have hxpos : 0 < angle := by
    unfold angle
    positivity
  have ht : 0 < t := by
    dsimp [t]
    positivity
  have htlt : t < 1 := by
    dsimp [t, angle]
    nlinarith [Real.pi_lt_four]
  have ht2prod : 0 < (1 - t) * (1 + t) :=
    mul_pos (sub_pos.mpr htlt) (by nlinarith)
  have ht2 : t ^ 2 < 1 := by
    nlinarith [ht2prod]
  have ht3prod : 0 < t * (1 - t ^ 2) :=
    mul_pos ht (sub_pos.mpr ht2)
  have ht3 : t ^ 3 < t := by
    nlinarith [ht3prod]
  have hs_err : |Real.sin t - t| ≤ t ^ 3 / 6 := by
    simpa [abs_of_pos ht] using Real.abs_sin_sub_id_le t
  have hs_lower : t - t ^ 3 / 6 ≤ Real.sin t := by
    have hneg := neg_le_of_abs_le hs_err
    linarith
  let a : ℝ := t - t ^ 3 / 6
  have ha : 0 < a := by
    dsimp [a]
    nlinarith [ht3]
  have hs_nonneg : 0 ≤ Real.sin t :=
    le_trans (le_of_lt ha) hs_lower
  have hp : 0 ≤ (Real.sin t - a) * (Real.sin t + a) :=
    mul_nonneg (sub_nonneg.mpr hs_lower)
      (add_nonneg hs_nonneg (le_of_lt ha))
  have ht6 : 0 < t ^ 6 := pow_pos ht 6
  have hs_sq : t ^ 2 - t ^ 4 / 3 < Real.sin t ^ 2 := by
    dsimp [a] at hp
    nlinarith [hp, ht6]
  have hcosid : Real.cos angle = 1 - 2 * Real.sin t ^ 2 := by
    calc
      Real.cos angle = Real.cos (2 * t) := congrArg Real.cos hx
      _ = 1 - 2 * Real.sin t ^ 2 := by
        nlinarith [Real.cos_two_mul t, Real.sin_sq_add_cos_sq t]
  have hupper :
      Real.cos angle - (1 - angle ^ 2 / 2) < angle ^ 4 / 24 := by
    calc
      Real.cos angle - (1 - angle ^ 2 / 2) =
          2 * t ^ 2 - 2 * Real.sin t ^ 2 := by
            rw [hcosid, hx]
            ring
      _ < angle ^ 4 / 24 := by
            rw [hx]
            nlinarith [hs_sq]
  have hlower : 1 - angle ^ 2 / 2 ≤ Real.cos angle := by
    exact Real.one_sub_sq_div_two_le_cos (x := angle)
  have hr_nonneg : 0 ≤ cosineRemainder := by
    rw [cosineRemainder, cosinePartial_two]
    linarith
  have hr_lt : cosineRemainder < angle ^ 4 / 24 := by
    rw [cosineRemainder, cosinePartial_two]
    exact hupper
  rw [abs_of_nonneg hr_nonneg]
  norm_num [Nat.factorial]
  nlinarith [hr_lt]

theorem gap3 :
    (1 / (Nat.factorial 4 : ℝ)) * angle ^ 4 <
      (1 / 10 ^ 6 : ℝ) := by
  have hxpos : 0 < angle := by
    unfold angle
    positivity
  have hxlt : angle < (1 / 45 : ℝ) := by
    unfold angle
    nlinarith [Real.pi_lt_four]
  have ha : 0 < (1 / 45 : ℝ) := by norm_num
  have hp2 :
      0 < ((1 / 45 : ℝ) - angle) * ((1 / 45 : ℝ) + angle) :=
    mul_pos (sub_pos.mpr hxlt) (add_pos ha hxpos)
  have hx2 : angle ^ 2 < (1 / 45 : ℝ) ^ 2 := by
    nlinarith [hp2]
  have hp4 :
      0 < ((1 / 45 : ℝ) ^ 2 - angle ^ 2) *
        ((1 / 45 : ℝ) ^ 2 + angle ^ 2) :=
    mul_pos (sub_pos.mpr hx2)
      (add_pos (pow_pos ha 2) (pow_pos hxpos 2))
  have hx4 : angle ^ 4 < (1 / 45 : ℝ) ^ 4 := by
    nlinarith [hp4]
  have hnum : (1 / 45 : ℝ) ^ 4 / 24 < 1 / 10 ^ 6 := by
    norm_num
  norm_num [Nat.factorial]
  nlinarith [hx4, hnum]

theorem gap4 :
    |cosineRemainder| < (1 / 10 ^ 6 : ℝ) := by
  linarith [gap2, gap3]

theorem gap5 :
    Approx (Real.cos angle) (999848 / 1000000 : ℝ)
      (1 / 10 ^ 6 : ℝ) := by
  let q : ℝ := 999848 / 1000000
  have hxpos : 0 < angle := by
    unfold angle
    positivity
  have hxlt : angle < (1 / 45 : ℝ) := by
    unfold angle
    nlinarith [Real.pi_lt_four]
  have ha : 0 < (1 / 45 : ℝ) := by norm_num
  have hp2 :
      0 < ((1 / 45 : ℝ) - angle) * ((1 / 45 : ℝ) + angle) :=
    mul_pos (sub_pos.mpr hxlt) (add_pos ha hxpos)
  have hx2 : angle ^ 2 < (1 / 45 : ℝ) ^ 2 := by
    nlinarith [hp2]
  have hp4 :
      0 < ((1 / 45 : ℝ) ^ 2 - angle ^ 2) *
        ((1 / 45 : ℝ) ^ 2 + angle ^ 2) :=
    mul_pos (sub_pos.mpr hx2)
      (add_pos (pow_pos ha 2) (pow_pos hxpos 2))
  have hx4 : angle ^ 4 < (1 / 45 : ℝ) ^ 4 := by
    nlinarith [hp4]
  have hcoef :
      (1 / (Nat.factorial 4 : ℝ)) * angle ^ 4 <
        (1 / 50000000 : ℝ) := by
    have hnum : (1 / 45 : ℝ) ^ 4 / 24 < (1 / 50000000 : ℝ) := by
      norm_num
    norm_num [Nat.factorial]
    nlinarith [hx4, hnum]
  have hrem_abs : |cosineRemainder| < (1 / 50000000 : ℝ) := by
    nlinarith [gap2, hcoef]
  have hrem_lt : cosineRemainder < (1 / 50000000 : ℝ) :=
    lt_of_le_of_lt (le_abs_self cosineRemainder) hrem_abs
  have hpi_lower : (157 / 50 : ℝ) < Real.pi := by
    nlinarith [Real.pi_gt_d20]
  have hpi_upper : Real.pi < (22 / 7 : ℝ) := by
    nlinarith [Real.pi_lt_d20]
  have hlower_prod :
      0 < (Real.pi - (157 / 50 : ℝ)) *
        (Real.pi + (157 / 50 : ℝ)) :=
    mul_pos (sub_pos.mpr hpi_lower) (by positivity)
  have hpi2_lower : (157 / 50 : ℝ) ^ 2 < Real.pi ^ 2 := by
    nlinarith [hlower_prod]
  have hupper_prod :
      0 < ((22 / 7 : ℝ) - Real.pi) *
        ((22 / 7 : ℝ) + Real.pi) :=
    mul_pos (sub_pos.mpr hpi_upper) (by positivity)
  have hpi2_upper : Real.pi ^ 2 < (22 / 7 : ℝ) ^ 2 := by
    nlinarith [hupper_prod]
  have hdiff_lower :
      (1 / 50000000 : ℝ) < q - cosinePartial 2 := by
    rw [cosinePartial_two]
    dsimp [q]
    unfold angle
    norm_num at hpi2_lower ⊢
    nlinarith [hpi2_lower]
  have hdiff_upper :
      q - cosinePartial 2 < (1 / 10 ^ 6 : ℝ) := by
    rw [cosinePartial_two]
    dsimp [q]
    unfold angle
    norm_num at hpi2_upper ⊢
    nlinarith [hpi2_upper]
  have hr_nonneg : 0 ≤ cosineRemainder := by
    rw [cosineRemainder, cosinePartial_two]
    linarith [Real.one_sub_sq_div_two_le_cos (x := angle)]
  have hrelation :
      q - Real.cos angle =
        (q - cosinePartial 2) - cosineRemainder := by
    rw [cosineRemainder]
    ring
  have hrem_lt_diff : cosineRemainder < q - cosinePartial 2 :=
    lt_trans hrem_lt hdiff_lower
  have hqcos_pos : 0 < q - Real.cos angle := by
    rw [hrelation]
    exact sub_pos.mpr hrem_lt_diff
  have hqcos_upper :
      q - Real.cos angle < (1 / 10 ^ 6 : ℝ) := by
    rw [hrelation]
    linarith [hdiff_upper, hr_nonneg]
  unfold Approx
  change |Real.cos angle - q| < (1 / 10 ^ 6 : ℝ)
  rw [abs_of_neg (by linarith [hqcos_pos])]
  linarith

end

end ProofGap.Exercise2924
