import ProofGapLean.Prelude.Analysis
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

namespace ProofGap.Exercise445

noncomputable section

def original (x : ℝ) : ℝ :=
  (Real.sqrt (1 - 2 * x - x ^ 2) - (1 + x)) / x
def rationalized (x : ℝ) : ℝ :=
  -2 * (2 + x) / (Real.sqrt (1 - 2 * x - x ^ 2) + 1 + x)
def HasLimitAt (f : ℝ → ℝ) (a L : ℝ) : Prop :=
  Filter.Tendsto f (nhdsWithin a ({a} : Set ℝ)ᶜ) (nhds L)

/-- Exercise 445, gap 1. -/
private theorem original_eventuallyEq_rationalized :
    original =ᶠ[nhdsWithin (0 : ℝ) ({0} : Set ℝ)ᶜ] rationalized := by
  have hlim : Filter.Tendsto (fun x : ℝ => x)
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 0) := by
    exact continuousAt_id.tendsto.mono_left inf_le_left
  have hlo : ∀ᶠ x in nhdsWithin (0 : ℝ) ({0} : Set ℝ)ᶜ,
      -(1 : ℝ) / 4 < x :=
    (tendsto_order.1 hlim).1 _ (by norm_num)
  have hhi : ∀ᶠ x in nhdsWithin (0 : ℝ) ({0} : Set ℝ)ᶜ,
      x < (1 : ℝ) / 4 :=
    (tendsto_order.1 hlim).2 _ (by norm_num)
  filter_upwards [self_mem_nhdsWithin, hlo, hhi] with x hxmem hxlo hxhi
  have hx : x ≠ 0 := by
    simpa using hxmem
  have hprod :
      0 < (x + (1 : ℝ) / 4) * ((1 : ℝ) / 4 - x) :=
    mul_pos (by linarith) (by linarith)
  have hsq : x ^ 2 < (1 : ℝ) / 16 := by
    nlinarith
  have hrad : 0 ≤ 1 - 2 * x - x ^ 2 := by
    nlinarith
  have hsqrt := Real.sq_sqrt hrad
  have hden :
      0 < Real.sqrt (1 - 2 * x - x ^ 2) + 1 + x := by
    nlinarith [Real.sqrt_nonneg (1 - 2 * x - x ^ 2)]
  unfold original rationalized
  apply (div_eq_div_iff hx (ne_of_gt hden)).2
  nlinarith [hsqrt]

theorem gap1 : HasLimitAt original 0 (-2) ↔ HasLimitAt rationalized 0 (-2) := by
  unfold HasLimitAt
  constructor
  · intro h
    exact h.congr' original_eventuallyEq_rationalized
  · intro h
    exact h.congr' original_eventuallyEq_rationalized.symm

/-- Exercise 445, gap 2. -/
theorem gap2 : HasLimitAt original 0 (-2) ↔ HasLimitAt rationalized 0 (-2) := by
  exact gap1

/-- Exercise 445, gap 3. -/
theorem gap3 : HasLimitAt rationalized 0 (-2) := by
  unfold HasLimitAt
  have hnum : ContinuousAt (fun x : ℝ => -2 * (2 + x)) 0 :=
    continuousAt_const.mul (continuousAt_const.add continuousAt_id)
  have hrad : ContinuousAt (fun x : ℝ => 1 - 2 * x - x ^ 2) 0 :=
    (continuousAt_const.sub (continuousAt_const.mul continuousAt_id)).sub
      (continuousAt_id.pow 2)
  have hden : ContinuousAt
      (fun x : ℝ => Real.sqrt (1 - 2 * x - x ^ 2) + 1 + x) 0 :=
    (hrad.sqrt.add continuousAt_const).add continuousAt_id
  have hcont : ContinuousAt rationalized 0 := by
    unfold rationalized
    exact hnum.div hden (by norm_num)
  have hr0 : rationalized 0 = (-2 : ℝ) := by
    norm_num [rationalized]
  rw [← hr0]
  exact hcont.tendsto.mono_left inf_le_left

/-- Exercise 445, gap 4. -/
theorem gap4 : HasLimitAt original 0 (-2) := by
  exact gap1.mpr gap3

end

end ProofGap.Exercise445
