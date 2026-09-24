import ProofGapLean.Prelude.Analysis
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise476

noncomputable section

def original (x : ℝ) : ℝ :=
  (Real.sin (5 * x) - Real.sin (3 * x)) / Real.sin x
def transformed (x : ℝ) : ℝ :=
  2 * Real.cos (4 * x) * Real.sin x / Real.sin x
def cancelled (x : ℝ) : ℝ := 2 * Real.cos (4 * x)
def HasLimitAtZero (f : ℝ → ℝ) (L : ℝ) : Prop :=
  Filter.Tendsto f (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds L)

/-- Exercise 476, gap 1. -/
theorem gap1 (L : ℝ) :
    HasLimitAtZero original L ↔ HasLimitAtZero transformed L := by
  have hfun : original = transformed := by
    funext x
    unfold original transformed
    rw [show 5 * x = 4 * x + x by ring]
    rw [Real.sin_add]
    rw [show 3 * x = 4 * x - x by ring]
    rw [Real.sin_sub]
    ring
  rw [hfun]

/-- Exercise 476, gap 2. -/
theorem gap2 (L : ℝ) :
    HasLimitAtZero transformed L ↔ HasLimitAtZero cancelled L := by
  have hsmall :
      ∀ᶠ x : ℝ in nhdsWithin 0 ({0} : Set ℝ)ᶜ,
        x ∈ Set.Ioo (-Real.pi) Real.pi := by
    exact Filter.Eventually.filter_mono inf_le_left
      (Ioo_mem_nhds (by linarith [Real.pi_pos]) Real.pi_pos)
  have hpunctured :
      ∀ᶠ x : ℝ in nhdsWithin 0 ({0} : Set ℝ)ᶜ,
        x ∈ ({0} : Set ℝ)ᶜ :=
    self_mem_nhdsWithin
  have h_event :
      transformed =ᶠ[nhdsWithin 0 ({0} : Set ℝ)ᶜ] cancelled := by
    filter_upwards [hsmall, hpunctured] with x hx hxc
    have hx0 : x ≠ 0 := by
      simpa using hxc
    have hsx : Real.sin x ≠ 0 := by
      rcases lt_or_gt_of_ne hx0 with hxneg | hxpos
      · have hnegpos : 0 < -x := neg_pos.mpr hxneg
        have hneglt : -x < Real.pi := by
          linarith [hx.1]
        have hsneg : Real.sin (-x) ≠ 0 :=
          ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hnegpos hneglt)
        simpa using hsneg
      · exact ne_of_gt
          (Real.sin_pos_of_pos_of_lt_pi hxpos hx.2)
    simp [transformed, cancelled, hsx]
  constructor
  · intro ht
    exact ht.congr' h_event
  · intro hc
    exact hc.congr' h_event.symm

/-- Exercise 476, gap 3. -/
theorem gap3 : HasLimitAtZero cancelled 2 := by
  have hcont : Continuous cancelled := by
    unfold cancelled
    exact continuous_const.mul
      (Real.continuous_cos.comp (continuous_const.mul continuous_id))
  have ht : Filter.Tendsto cancelled (nhds 0) (nhds (cancelled 0)) :=
    hcont.continuousAt
  have hc0 : cancelled 0 = 2 := by
    norm_num [cancelled]
  rw [hc0] at ht
  unfold HasLimitAtZero
  exact ht.mono_left inf_le_left

/-- Exercise 476, gap 4. -/
theorem gap4 : HasLimitAtZero original 2 := by
  exact (gap1 2).2 ((gap2 2).2 gap3)

end

end ProofGap.Exercise476
