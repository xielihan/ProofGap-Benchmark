import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise443

noncomputable section

def cbrt (x : ℝ) : ℝ := Real.rpow x (1 / 3 : ℝ)
def original (x : ℝ) : ℝ := (Real.sqrt (9 + 2 * x) - 5) / (cbrt x - 2)
def cancelled (x : ℝ) : ℝ :=
  2 * (cbrt (x ^ 2) + 2 * cbrt x + 4) / (Real.sqrt (9 + 2 * x) + 5)
def HasLimitAt (f : ℝ → ℝ) (a L : ℝ) : Prop :=
  Filter.Tendsto f (nhdsWithin a ({a} : Set ℝ)ᶜ) (nhds L)

private theorem cbrt_spec (x : ℝ) (hx : 0 ≤ x) :
    cbrt x ^ 3 = x ∧ cbrt (x ^ 2) = cbrt x ^ 2 := by
  constructor
  · unfold cbrt
    calc
      Real.rpow x (1 / 3 : ℝ) ^ (3 : ℕ) =
          Real.rpow (Real.rpow x (1 / 3 : ℝ)) (3 : ℝ) :=
        (Real.rpow_natCast _ 3).symm
      _ = Real.rpow x ((1 / 3 : ℝ) * 3) :=
        (Real.rpow_mul hx (1 / 3 : ℝ) 3).symm
      _ = x := by norm_num
  · unfold cbrt
    calc
      Real.rpow (x ^ 2) (1 / 3 : ℝ) =
          Real.rpow (x * x) (1 / 3 : ℝ) := by rw [pow_two]
      _ = Real.rpow x (1 / 3 : ℝ) * Real.rpow x (1 / 3 : ℝ) :=
        Real.mul_rpow hx hx
      _ = Real.rpow x (1 / 3 : ℝ) ^ 2 := by rw [pow_two]

private theorem hasLimitAtCongr {f g : ℝ → ℝ} {a L : ℝ}
    (hfg : f =ᶠ[nhdsWithin a ({a} : Set ℝ)ᶜ] g) :
    HasLimitAt f a L ↔ HasLimitAt g a L := by
  unfold HasLimitAt
  exact ⟨fun hf => hf.congr' hfg, fun hg => hg.congr' hfg.symm⟩

/-- Exercise 443, gap 1. -/
theorem gap1 : HasLimitAt original 8 (12 / 5) ↔
    HasLimitAt cancelled 8 (12 / 5) := by
  apply hasLimitAtCongr
  have hnear :
      ∀ᶠ x : ℝ in nhdsWithin (8 : ℝ) ({8} : Set ℝ)ᶜ,
        x ∈ Set.Ioo (7 : ℝ) 9 :=
    mem_nhdsWithin_of_mem_nhds (isOpen_Ioo.mem_nhds (by norm_num))
  filter_upwards [hnear, self_mem_nhdsWithin] with x hx hxmem
  have hxne : x ≠ 8 := by simpa using hxmem
  have hx0 : 0 ≤ x := by linarith [hx.1]
  have hs := cbrt_spec x hx0
  have harg : 0 ≤ 9 + 2 * x := by linarith [hx.1]
  have hsqrt : (Real.sqrt (9 + 2 * x)) ^ 2 = 9 + 2 * x :=
    Real.sq_sqrt harg
  have hcden : cbrt x - 2 ≠ 0 := by
    intro h
    have hc : cbrt x = 2 := sub_eq_zero.mp h
    rw [hc] at hs
    norm_num at hs
    exact hxne hs.1.symm
  have hsden : Real.sqrt (9 + 2 * x) + 5 ≠ 0 := by positivity
  unfold original cancelled
  rw [hs.2]
  apply (div_eq_div_iff hcden hsden).2
  have hleft :
      (Real.sqrt (9 + 2 * x) - 5) *
          (Real.sqrt (9 + 2 * x) + 5) = 2 * (x - 8) := by
    nlinarith
  have hright :
      (cbrt x - 2) * (cbrt x ^ 2 + 2 * cbrt x + 4) =
        x - 8 := by
    calc
      (cbrt x - 2) * (cbrt x ^ 2 + 2 * cbrt x + 4) =
          cbrt x ^ 3 - 8 := by ring
      _ = x - 8 := by rw [hs.1]
  rw [hleft]
  nlinarith

/-- Exercise 443, gap 2. -/
theorem gap2 : HasLimitAt original 8 (12 / 5) ↔
    HasLimitAt cancelled 8 (12 / 5) := by
  exact gap1

/-- Exercise 443, gap 3. -/
theorem gap3 : HasLimitAt cancelled 8 (12 / 5) := by
  have hs8 := cbrt_spec (8 : ℝ) (by norm_num)
  have hc8 : cbrt 8 = 2 := by
    have hcube := hs8.1
    have hnonneg : 0 ≤ cbrt 8 := by
      unfold cbrt
      exact Real.rpow_nonneg (by norm_num) _
    nlinarith [sq_nonneg (cbrt 8 + 2)]
  have hc64 : cbrt 64 = 4 := by
    have h := hs8.2
    norm_num [hc8] at h
    exact h
  have hsqrt25 : Real.sqrt 25 = 5 := by
    have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 25 by norm_num)
    have hn := Real.sqrt_nonneg (25 : ℝ)
    nlinarith
  have hcbrt : Continuous cbrt := by
    unfold cbrt
    change Continuous (fun x : ℝ => x ^ (1 / 3 : ℝ))
    exact Real.continuous_rpow_const (by norm_num)
  have hc : ContinuousAt (fun x : ℝ => cbrt x) 8 :=
    hcbrt.continuousAt
  have hc2 : ContinuousAt (fun x : ℝ => cbrt (x ^ 2)) 8 := by
    have ht : Filter.Tendsto
        (cbrt ∘ fun x : ℝ => x ^ 2)
        (nhds 8) (nhds (cbrt ((8 : ℝ) ^ 2))) :=
      Filter.Tendsto.comp hcbrt.continuousAt (continuousAt_id.pow 2)
    simpa only [Function.comp_apply] using ht
  have hnum : ContinuousAt
      (fun x : ℝ => 2 * (cbrt (x ^ 2) + 2 * cbrt x + 4)) 8 :=
    continuousAt_const.mul
      ((hc2.add (continuousAt_const.mul hc)).add continuousAt_const)
  have harg : ContinuousAt (fun x : ℝ => 9 + 2 * x) 8 :=
    continuousAt_const.add (continuousAt_const.mul continuousAt_id)
  have hden : ContinuousAt
      (fun x : ℝ => Real.sqrt (9 + 2 * x) + 5) 8 :=
    (Real.continuous_sqrt.continuousAt.comp harg).add continuousAt_const
  have hdenne : Real.sqrt (9 + 2 * (8 : ℝ)) + 5 ≠ 0 := by
    norm_num [hsqrt25]
  have hcont : ContinuousAt cancelled 8 := by
    unfold cancelled
    exact hnum.div hden hdenne
  have hvalue : cancelled 8 = (12 / 5 : ℝ) := by
    norm_num [cancelled, hc8, hc64, hsqrt25]
  unfold HasLimitAt
  rw [← hvalue]
  exact hcont.tendsto.mono_left inf_le_left

/-- Exercise 443, gap 4. -/
theorem gap4 : HasLimitAt original 8 (12 / 5) := by
  exact gap1.mpr gap3

end

end ProofGap.Exercise443
