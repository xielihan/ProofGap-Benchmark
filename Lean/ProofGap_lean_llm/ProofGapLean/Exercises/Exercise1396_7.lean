import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Basic

namespace ProofGap.Exercise1396_7

noncomputable section

def Approx (x y ε : ℝ) : Prop := |x - y| < ε
def atanPartial (x : ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range n, (-1 : ℝ) ^ k * x ^ (2 * k + 1) / (2 * k + 1)
def remainder : ℝ := |Real.arctan 0.8 - atanPartial 0.8 20|
def remainderBound : ℝ := (1 / 41 : ℝ) * 0.8 ^ 41

private theorem arctan_point_eight_estimates :
    (0 ≤ Real.arctan 0.8 - atanPartial 0.8 20 ∧
      Real.arctan 0.8 - atanPartial 0.8 20 < 0.8 ^ 41 / 41) ∧
    (0 ≤ Real.arctan 0.8 - atanPartial 0.8 30 ∧
      Real.arctan 0.8 - atanPartial 0.8 30 < 0.8 ^ 61 / 61) := by
  set_option maxHeartbeats 2000000 in
  set_option maxRecDepth 4096 in
    have hpartial (n : ℕ) (t : ℝ) :
        HasDerivAt (fun z : ℝ => atanPartial z n)
          (∑ k ∈ Finset.range n, (-1 : ℝ) ^ k * t ^ (2 * k)) t := by
      unfold atanPartial
      have hs :
          HasDerivAt
            (∑ k ∈ Finset.range n,
              (fun z : ℝ =>
                (-1 : ℝ) ^ k * z ^ (2 * k + 1) / (2 * k + 1)))
            (∑ k ∈ Finset.range n, (-1 : ℝ) ^ k * t ^ (2 * k)) t := by
        apply HasDerivAt.sum
        intro k hk
        convert ((((hasDerivAt_id t).pow (2 * k + 1)).const_mul
          ((-1 : ℝ) ^ k)).div_const (((2 * k + 1 : ℕ) : ℝ))) using 1 <;>
          simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_mul] <;>
          field_simp <;>
          simp [id_eq, pow_succ, Nat.mul_comm, Nat.add_comm, mul_comm,
            mul_left_comm, mul_assoc]
      have hfun :
          (∑ k ∈ Finset.range n,
            (fun z : ℝ =>
              (-1 : ℝ) ^ k * z ^ (2 * k + 1) / (2 * k + 1))) =
            (fun z : ℝ =>
              ∑ k ∈ Finset.range n,
                (-1 : ℝ) ^ k * z ^ (2 * k + 1) / (2 * k + 1)) := by
        funext z
        simp only [Finset.sum_apply]
      rw [← hfun]
      exact hs
    have he20 (t : ℝ) :
        HasDerivAt (fun z : ℝ => Real.arctan z - atanPartial z 20)
          (t ^ 40 / (1 + t ^ 2)) t := by
      have hden : 1 + t ^ 2 ≠ 0 := by nlinarith [sq_nonneg t]
      convert (Real.hasDerivAt_arctan t).sub (hpartial 20 t) using 1 <;>
        norm_num [Finset.sum_range_succ] <;>
        field_simp [hden] <;> ring
    have he30 (t : ℝ) :
        HasDerivAt (fun z : ℝ => Real.arctan z - atanPartial z 30)
          (t ^ 60 / (1 + t ^ 2)) t := by
      have hden : 1 + t ^ 2 ≠ 0 := by nlinarith [sq_nonneg t]
      convert (Real.hasDerivAt_arctan t).sub (hpartial 30 t) using 1 <;>
        norm_num [Finset.sum_range_succ] <;>
        field_simp [hden] <;> ring
    have hpow20 (t : ℝ) :
        HasDerivAt (fun z : ℝ => z ^ 41 / 41) (t ^ 40) t := by
      convert ((hasDerivAt_id t).pow 41).div_const 41 using 1 <;> norm_num
    have hpow30 (t : ℝ) :
        HasDerivAt (fun z : ℝ => z ^ 61 / 61) (t ^ 60) t := by
      convert ((hasDerivAt_id t).pow 61).div_const 61 using 1 <;> norm_num
    have hq20 (t : ℝ) :
        HasDerivAt
          (fun z : ℝ => z ^ 41 / 41 -
            (Real.arctan z - atanPartial z 20))
          (t ^ 40 - t ^ 40 / (1 + t ^ 2)) t :=
      (hpow20 t).sub (he20 t)
    have hq30 (t : ℝ) :
        HasDerivAt
          (fun z : ℝ => z ^ 61 / 61 -
            (Real.arctan z - atanPartial z 30))
          (t ^ 60 - t ^ 60 / (1 + t ^ 2)) t :=
      (hpow30 t).sub (he30 t)
    have hcomp20 (t : ℝ) :
        HasDerivAt
          (fun z : ℝ => z ^ 43 / (43 * (1 + (0.8 : ℝ) ^ 2)))
          (t ^ 42 / (1 + (0.8 : ℝ) ^ 2)) t := by
      convert ((hasDerivAt_id t).pow 43).div_const
        (43 * (1 + (0.8 : ℝ) ^ 2)) using 1 <;> norm_num <;> ring
    have hcomp30 (t : ℝ) :
        HasDerivAt
          (fun z : ℝ => z ^ 63 / (63 * (1 + (0.8 : ℝ) ^ 2)))
          (t ^ 62 / (1 + (0.8 : ℝ) ^ 2)) t := by
      convert ((hasDerivAt_id t).pow 63).div_const
        (63 * (1 + (0.8 : ℝ) ^ 2)) using 1 <;> norm_num <;> ring
    have hr20 (t : ℝ) :
        HasDerivAt
          (fun z : ℝ =>
            (z ^ 41 / 41 - (Real.arctan z - atanPartial z 20)) -
              z ^ 43 / (43 * (1 + (0.8 : ℝ) ^ 2)))
          ((t ^ 40 - t ^ 40 / (1 + t ^ 2)) -
            t ^ 42 / (1 + (0.8 : ℝ) ^ 2)) t :=
      (hq20 t).sub (hcomp20 t)
    have hr30 (t : ℝ) :
        HasDerivAt
          (fun z : ℝ =>
            (z ^ 61 / 61 - (Real.arctan z - atanPartial z 30)) -
              z ^ 63 / (63 * (1 + (0.8 : ℝ) ^ 2)))
          ((t ^ 60 - t ^ 60 / (1 + t ^ 2)) -
            t ^ 62 / (1 + (0.8 : ℝ) ^ 2)) t :=
      (hq30 t).sub (hcomp30 t)
    have rise (f : ℝ → ℝ) (hf : ∀ t, DifferentiableAt ℝ f t)
        (hd : ∀ t ∈ Set.Ioo (0 : ℝ) 0.8, 0 ≤ deriv f t) :
        f 0 ≤ f 0.8 := by
      have hc : ContinuousOn f (Set.Icc (0 : ℝ) 0.8) :=
        fun t ht => (hf t).continuousAt.continuousWithinAt
      have hm : MonotoneOn f (Set.Icc (0 : ℝ) 0.8) :=
        monotoneOn_of_deriv_nonneg (convex_Icc (0 : ℝ) 0.8) hc
          (fun t ht => (hf t).differentiableWithinAt) (by
            intro t ht
            apply hd t
            simpa only [interior_Icc] using ht)
      exact hm (by norm_num) (by norm_num) (by norm_num)
    have hlo20raw := rise
      (fun z : ℝ => Real.arctan z - atanPartial z 20)
      (fun t => (he20 t).differentiableAt) (by
        intro t ht
        rw [(he20 t).deriv]
        positivity)
    have he20zero : Real.arctan 0 - atanPartial 0 20 = 0 := by
      norm_num [atanPartial]
    change Real.arctan 0 - atanPartial 0 20 ≤
      Real.arctan 0.8 - atanPartial 0.8 20 at hlo20raw
    rw [he20zero] at hlo20raw
    have hlo30raw := rise
      (fun z : ℝ => Real.arctan z - atanPartial z 30)
      (fun t => (he30 t).differentiableAt) (by
        intro t ht
        rw [(he30 t).deriv]
        positivity)
    have he30zero : Real.arctan 0 - atanPartial 0 30 = 0 := by
      norm_num [atanPartial]
    change Real.arctan 0 - atanPartial 0 30 ≤
      Real.arctan 0.8 - atanPartial 0.8 30 at hlo30raw
    rw [he30zero] at hlo30raw
    have hup20raw := rise
      (fun z : ℝ =>
        (z ^ 41 / 41 - (Real.arctan z - atanPartial z 20)) -
          z ^ 43 / (43 * (1 + (0.8 : ℝ) ^ 2)))
      (fun t => (hr20 t).differentiableAt) (by
        intro t ht
        rw [(hr20 t).deriv]
        have hden : 0 < 1 + t ^ 2 := by nlinarith [sq_nonneg t]
        have hden8 : 0 < 1 + (0.8 : ℝ) ^ 2 := by norm_num
        have hqident :
            t ^ 40 - t ^ 40 / (1 + t ^ 2) =
              t ^ 42 / (1 + t ^ 2) := by
          field_simp [ne_of_gt hden]
          ring
        rw [hqident]
        have hfactor : 0 ≤ (0.8 - t) * (0.8 + t) :=
          mul_nonneg (by linarith [ht.2]) (by linarith [ht.1])
        have hdiff : 0 ≤ (0.8 : ℝ) ^ 2 - t ^ 2 := by
          nlinarith
        have hid :
            t ^ 42 / (1 + t ^ 2) -
                t ^ 42 / (1 + (0.8 : ℝ) ^ 2) =
              t ^ 42 * ((0.8 : ℝ) ^ 2 - t ^ 2) /
                ((1 + t ^ 2) * (1 + (0.8 : ℝ) ^ 2)) := by
          field_simp [ne_of_gt hden, ne_of_gt hden8]
          ring
        rw [hid]
        exact div_nonneg (mul_nonneg (by positivity) hdiff)
          (le_of_lt (mul_pos hden hden8)))
    have hr20zero :
        ((0 : ℝ) ^ 41 / 41 - (Real.arctan 0 - atanPartial 0 20)) -
            (0 : ℝ) ^ 43 / (43 * (1 + (0.8 : ℝ) ^ 2)) = 0 := by
      norm_num [atanPartial]
    change
      ((0 : ℝ) ^ 41 / 41 - (Real.arctan 0 - atanPartial 0 20)) -
          (0 : ℝ) ^ 43 / (43 * (1 + (0.8 : ℝ) ^ 2)) ≤
      ((0.8 : ℝ) ^ 41 / 41 -
          (Real.arctan 0.8 - atanPartial 0.8 20)) -
        (0.8 : ℝ) ^ 43 / (43 * (1 + (0.8 : ℝ) ^ 2)) at hup20raw
    rw [hr20zero] at hup20raw
    have hc20pos :
        0 < (0.8 : ℝ) ^ 43 / (43 * (1 + (0.8 : ℝ) ^ 2)) := by
      positivity
    have hup20 : Real.arctan 0.8 - atanPartial 0.8 20 <
        0.8 ^ 41 / 41 := by
      linarith
    have hup30raw := rise
      (fun z : ℝ =>
        (z ^ 61 / 61 - (Real.arctan z - atanPartial z 30)) -
          z ^ 63 / (63 * (1 + (0.8 : ℝ) ^ 2)))
      (fun t => (hr30 t).differentiableAt) (by
        intro t ht
        rw [(hr30 t).deriv]
        have hden : 0 < 1 + t ^ 2 := by nlinarith [sq_nonneg t]
        have hden8 : 0 < 1 + (0.8 : ℝ) ^ 2 := by norm_num
        have hqident :
            t ^ 60 - t ^ 60 / (1 + t ^ 2) =
              t ^ 62 / (1 + t ^ 2) := by
          field_simp [ne_of_gt hden]
          ring
        rw [hqident]
        have hfactor : 0 ≤ (0.8 - t) * (0.8 + t) :=
          mul_nonneg (by linarith [ht.2]) (by linarith [ht.1])
        have hdiff : 0 ≤ (0.8 : ℝ) ^ 2 - t ^ 2 := by
          nlinarith
        have hid :
            t ^ 62 / (1 + t ^ 2) -
                t ^ 62 / (1 + (0.8 : ℝ) ^ 2) =
              t ^ 62 * ((0.8 : ℝ) ^ 2 - t ^ 2) /
                ((1 + t ^ 2) * (1 + (0.8 : ℝ) ^ 2)) := by
          field_simp [ne_of_gt hden, ne_of_gt hden8]
          ring
        rw [hid]
        exact div_nonneg (mul_nonneg (by positivity) hdiff)
          (le_of_lt (mul_pos hden hden8)))
    have hr30zero :
        ((0 : ℝ) ^ 61 / 61 - (Real.arctan 0 - atanPartial 0 30)) -
            (0 : ℝ) ^ 63 / (63 * (1 + (0.8 : ℝ) ^ 2)) = 0 := by
      norm_num [atanPartial]
    change
      ((0 : ℝ) ^ 61 / 61 - (Real.arctan 0 - atanPartial 0 30)) -
          (0 : ℝ) ^ 63 / (63 * (1 + (0.8 : ℝ) ^ 2)) ≤
      ((0.8 : ℝ) ^ 61 / 61 -
          (Real.arctan 0.8 - atanPartial 0.8 30)) -
        (0.8 : ℝ) ^ 63 / (63 * (1 + (0.8 : ℝ) ^ 2)) at hup30raw
    rw [hr30zero] at hup30raw
    have hc30pos :
        0 < (0.8 : ℝ) ^ 63 / (63 * (1 + (0.8 : ℝ) ^ 2)) := by
      positivity
    have hup30 : Real.arctan 0.8 - atanPartial 0.8 30 <
        0.8 ^ 61 / 61 := by
      linarith
    exact ⟨⟨hlo20raw, hup20⟩, ⟨hlo30raw, hup30⟩⟩

theorem gap1 :
    Approx (Real.arctan 0.8) (atanPartial 0.8 20)
      (26 / 10000000 : ℝ) := by
  rcases arctan_point_eight_estimates with ⟨h20, h30⟩
  unfold Approx
  rw [abs_of_nonneg h20.1]
  exact lt_trans h20.2 (by norm_num)
theorem gap2 :
    Approx (atanPartial 0.8 20) 0.67474 (7 / 1000000 : ℝ) := by
  set_option maxRecDepth 4096 in
    norm_num [Approx, atanPartial, Finset.sum_range_succ, abs_lt]
theorem gap3 :
    Approx (Real.arctan 0.8) 0.67474 (1 / 1000000 : ℝ) := by
  set_option maxRecDepth 4096 in
    rcases arctan_point_eight_estimates with ⟨h20, h30⟩
    unfold Approx
    rw [abs_lt]
    norm_num [atanPartial, Finset.sum_range_succ] at h30 ⊢
    constructor <;> linarith [h30.1, h30.2]
theorem gap4 : ∃ Δ : ℝ, Δ = remainder ∧ Δ < remainderBound := by
  rcases arctan_point_eight_estimates with ⟨h20, h30⟩
  refine ⟨remainder, rfl, ?_⟩
  unfold remainder remainderBound
  rw [abs_of_nonneg h20.1]
  simpa [div_eq_mul_inv, mul_comm] using h20.2
theorem gap5 :
    Approx remainderBound (2.6 * 10 ^ (-6 : ℤ))
      (1 / 100000000 : ℝ) := by
  norm_num [Approx, remainderBound, abs_lt]

end
end ProofGap.Exercise1396_7
