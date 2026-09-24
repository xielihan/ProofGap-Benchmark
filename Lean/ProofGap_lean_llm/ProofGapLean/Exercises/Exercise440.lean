import ProofGapLean.Prelude.Analysis
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise440

noncomputable section

def original (x : ℝ) : ℝ :=
  (Real.sqrt (x + 13) - 2 * Real.sqrt (x + 1)) / (x ^ 2 - 9)
def rationalized (x : ℝ) : ℝ :=
  ((Real.sqrt (x + 13) - 2 * Real.sqrt (x + 1)) *
      (Real.sqrt (x + 13) + 2 * Real.sqrt (x + 1))) /
    ((x + 3) * (x - 3) *
      (Real.sqrt (x + 13) + 2 * Real.sqrt (x + 1)))
def factored (x : ℝ) : ℝ :=
  (-3 * (x - 3)) /
    ((x - 3) * (x + 3) * (Real.sqrt (x + 13) + 2 * Real.sqrt (x + 1)))
def cancelled (x : ℝ) : ℝ :=
  -3 / ((x + 3) * (Real.sqrt (x + 13) + 2 * Real.sqrt (x + 1)))
def HasLimitAt (f : ℝ → ℝ) (a L : ℝ) : Prop :=
  Filter.Tendsto f (nhdsWithin a ({a} : Set ℝ)ᶜ) (nhds L)

/-- Source: `proof_gap/exercise_440/1.txt`. -/
private lemma near_three_gt_two :
    ∀ᶠ x : ℝ in nhdsWithin (3 : ℝ) ({3} : Set ℝ)ᶜ, 2 < x := by
  exact
    (eventually_gt_nhds (show (2 : ℝ) < 3 by norm_num)).filter_mono
      inf_le_left

theorem gap1 : HasLimitAt original 3 (-1 / 16) ↔
    HasLimitAt rationalized 3 (-1 / 16) := by
  unfold HasLimitAt
  refine Filter.tendsto_congr' ?_
  filter_upwards [near_three_gt_two, self_mem_nhdsWithin] with x hx hxmem
  have hx3 : x ≠ 3 := by
    simpa using hxmem
  have hxm3 : x - 3 ≠ 0 := sub_ne_zero.mpr hx3
  have hxp3 : x + 3 ≠ 0 := by
    linarith
  have hc :
      Real.sqrt (x + 13) + 2 * Real.sqrt (x + 1) ≠ 0 := by
    have hs13 : 0 < Real.sqrt (x + 13) :=
      Real.sqrt_pos.2 (by linarith)
    have hs1 : 0 ≤ Real.sqrt (x + 1) := Real.sqrt_nonneg _
    nlinarith
  have hfactor : x ^ 2 - 9 = (x + 3) * (x - 3) := by
    ring
  have hD : (x + 3) * (x - 3) ≠ 0 :=
    mul_ne_zero hxp3 hxm3
  simp only [original, rationalized]
  rw [hfactor]
  apply (div_eq_div_iff hD (mul_ne_zero hD hc)).2
  ring

/-- Source: `proof_gap/exercise_440/2.txt`. -/
theorem gap2 : HasLimitAt original 3 (-1 / 16) ↔
    HasLimitAt factored 3 (-1 / 16) := by
  calc
    HasLimitAt original 3 (-1 / 16) ↔
        HasLimitAt rationalized 3 (-1 / 16) := gap1
    _ ↔ HasLimitAt factored 3 (-1 / 16) := by
      unfold HasLimitAt
      refine Filter.tendsto_congr' ?_
      filter_upwards [near_three_gt_two] with x hx
      have h13 : 0 ≤ x + 13 := by linarith
      have h1 : 0 ≤ x + 1 := by linarith
      have hs13 : (Real.sqrt (x + 13)) ^ 2 = x + 13 :=
        Real.sq_sqrt h13
      have hs1 : (Real.sqrt (x + 1)) ^ 2 = x + 1 :=
        Real.sq_sqrt h1
      have hnum :
          (Real.sqrt (x + 13) - 2 * Real.sqrt (x + 1)) *
              (Real.sqrt (x + 13) + 2 * Real.sqrt (x + 1)) =
            -3 * (x - 3) := by
        nlinarith [hs13, hs1]
      simp only [rationalized, factored]
      rw [hnum, mul_comm (x + 3) (x - 3)]

/-- Source: `proof_gap/exercise_440/3.txt`. -/
theorem gap3 : HasLimitAt factored 3 (-1 / 16) ↔
    HasLimitAt cancelled 3 (-1 / 16) := by
  unfold HasLimitAt
  refine Filter.tendsto_congr' ?_
  filter_upwards [self_mem_nhdsWithin] with x hxmem
  have hx3 : x ≠ 3 := by
    simpa using hxmem
  have hxm3 : x - 3 ≠ 0 := sub_ne_zero.mpr hx3
  by_cases hq :
      (x + 3) *
          (Real.sqrt (x + 13) + 2 * Real.sqrt (x + 1)) = 0
  · simp only [factored, cancelled]
    rw [show
      (x - 3) * (x + 3) *
          (Real.sqrt (x + 13) + 2 * Real.sqrt (x + 1)) =
        (x - 3) *
          ((x + 3) *
            (Real.sqrt (x + 13) + 2 * Real.sqrt (x + 1))) by ring,
      hq]
    simp
  · have hden :
        (x - 3) * (x + 3) *
            (Real.sqrt (x + 13) + 2 * Real.sqrt (x + 1)) ≠ 0 := by
      rw [show
        (x - 3) * (x + 3) *
            (Real.sqrt (x + 13) + 2 * Real.sqrt (x + 1)) =
          (x - 3) *
            ((x + 3) *
              (Real.sqrt (x + 13) + 2 * Real.sqrt (x + 1))) by ring]
      exact mul_ne_zero hxm3 hq
    simp only [factored, cancelled]
    apply (div_eq_div_iff hden hq).2
    ring

/-- Source: `proof_gap/exercise_440/4.txt`. -/
theorem gap4 : HasLimitAt cancelled 3 (-1 / 16) := by
  unfold HasLimitAt
  have hs16 : Real.sqrt (16 : ℝ) = 4 := by
    have hsq : (Real.sqrt (16 : ℝ)) ^ 2 = 16 :=
      Real.sq_sqrt (by norm_num)
    have hnonneg : 0 ≤ Real.sqrt (16 : ℝ) := Real.sqrt_nonneg _
    nlinarith
  have hs4 : Real.sqrt (4 : ℝ) = 2 := by
    have hsq : (Real.sqrt (4 : ℝ)) ^ 2 = 4 :=
      Real.sq_sqrt (by norm_num)
    have hnonneg : 0 ≤ Real.sqrt (4 : ℝ) := Real.sqrt_nonneg _
    nlinarith
  have hcont : ContinuousAt cancelled 3 := by
    unfold cancelled
    have hnum : ContinuousAt (fun _ : ℝ => (-3 : ℝ)) 3 :=
      continuousAt_const
    have hx3 : ContinuousAt (fun x : ℝ => x + 3) 3 :=
      continuousAt_id.add continuousAt_const
    have hx13 : ContinuousAt (fun x : ℝ => x + 13) 3 :=
      continuousAt_id.add continuousAt_const
    have hx1 : ContinuousAt (fun x : ℝ => x + 1) 3 :=
      continuousAt_id.add continuousAt_const
    have hs13 : ContinuousAt (fun x : ℝ => Real.sqrt (x + 13)) 3 :=
      hx13.sqrt
    have hs1 : ContinuousAt (fun x : ℝ => Real.sqrt (x + 1)) 3 :=
      hx1.sqrt
    have htwos1 :
        ContinuousAt (fun x : ℝ => 2 * Real.sqrt (x + 1)) 3 :=
      continuousAt_const.mul hs1
    have hden : ContinuousAt
        (fun x : ℝ =>
          (x + 3) *
            (Real.sqrt (x + 13) + 2 * Real.sqrt (x + 1))) 3 :=
      hx3.mul (hs13.add htwos1)
    apply hnum.div hden
    norm_num [hs16, hs4]
  have hvalue : cancelled 3 = (-1 / 16 : ℝ) := by
    norm_num [cancelled, hs16, hs4]
  rw [← hvalue]
  exact hcont.tendsto.mono_left inf_le_left

/-- Source: `proof_gap/exercise_440/5.txt`. -/
theorem gap5 : HasLimitAt original 3 (-1 / 16) := by
  exact gap2.mpr (gap3.mpr gap4)

end

end ProofGap.Exercise440
