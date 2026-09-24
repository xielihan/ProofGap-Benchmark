import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

namespace ProofGap.Exercise502

noncomputable section

def original (x : ℝ) : ℝ :=
  Real.sqrt (1 - Real.cos (x ^ 2)) / (1 - Real.cos x)
def halfAngle (x : ℝ) : ℝ :=
  Real.sqrt 2 * Real.sin (x ^ 2 / 2) / (2 * Real.sin (x / 2) ^ 2)
def normalized (x : ℝ) : ℝ :=
  Real.sqrt 2 * (Real.sin (x ^ 2 / 2) / (x ^ 2 / 2)) *
    ((x / 2) / Real.sin (x / 2)) ^ 2
def HasLimitAtZero (f : ℝ → ℝ) (L : ℝ) : Prop :=
  Filter.Tendsto f (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds L)

/-- Exercise 502, gap 1. -/
private theorem sqHalfTendstoPunctured :
    Filter.Tendsto (fun x : ℝ => x ^ 2 / 2)
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ)
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) := by
  refine (tendsto_nhdsWithin_iff).2 ⟨?_, ?_⟩
  · have hid : ContinuousAt (fun x : ℝ => x) (0 : ℝ) := continuousAt_id
    have hfull :
        Filter.Tendsto (fun x : ℝ => x ^ 2 / 2) (nhds 0) (nhds 0) := by
      simpa using ((hid.pow 2).div_const (2 : ℝ)).tendsto
    exact hfull.mono_left inf_le_left
  · filter_upwards [self_mem_nhdsWithin] with x hx
    have hx0 : x ≠ 0 := by simpa using hx
    exact div_ne_zero (pow_ne_zero 2 hx0) (by norm_num)

private theorem divTwoTendstoPunctured :
    Filter.Tendsto (fun x : ℝ => x / 2)
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ)
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) := by
  refine (tendsto_nhdsWithin_iff).2 ⟨?_, ?_⟩
  · have hid : ContinuousAt (fun x : ℝ => x) (0 : ℝ) := continuousAt_id
    have hfull :
        Filter.Tendsto (fun x : ℝ => x / 2) (nhds 0) (nhds 0) := by
      simpa using (hid.div_const (2 : ℝ)).tendsto
    exact hfull.mono_left inf_le_left
  · filter_upwards [self_mem_nhdsWithin] with x hx
    have hx0 : x ≠ 0 := by simpa using hx
    exact div_ne_zero hx0 (by norm_num)

private theorem sinDivTendstoPunctured :
    Filter.Tendsto (fun x : ℝ => Real.sin x / x)
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1) := by
  have hsincAt : ContinuousAt Real.sinc (0 : ℝ) :=
    Real.continuous_sinc.continuousAt
  have hsincSelf :
      Filter.Tendsto Real.sinc (nhds 0) (nhds (Real.sinc 0)) :=
    hsincAt
  have hsincFull : Filter.Tendsto Real.sinc (nhds 0) (nhds 1) := by
    simpa [Real.sinc] using hsincSelf
  have hsinc :
      Filter.Tendsto Real.sinc (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1) :=
    hsincFull.mono_left inf_le_left
  refine (Filter.tendsto_congr' ?_).2 hsinc
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hx0 : x ≠ 0 := by simpa using hx
  simp [Real.sinc, hx0]

private theorem divSinTendstoPunctured :
    Filter.Tendsto (fun x : ℝ => (x / 2) / Real.sin (x / 2))
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1) := by
  have hbase :
      Filter.Tendsto (fun x : ℝ => x / Real.sin x)
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1) := by
    simpa only [inv_div, inv_one] using
      sinDivTendstoPunctured.inv₀ (by norm_num : (1 : ℝ) ≠ 0)
  exact hbase.comp divTwoTendstoPunctured

private theorem originalEventuallyEqHalfAngle :
    original =ᶠ[nhdsWithin 0 ({0} : Set ℝ)ᶜ] halfAngle := by
  have hto :
      Filter.Tendsto (fun x : ℝ => x ^ 2 / 2)
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 0) :=
    sqHalfTendstoPunctured.mono_right inf_le_left
  have hlt :
      ∀ᶠ x in nhdsWithin 0 ({0} : Set ℝ)ᶜ, x ^ 2 / 2 < Real.pi :=
    hto.eventually (isOpen_Iio.mem_nhds Real.pi_pos)
  filter_upwards [hlt] with x hx
  have hs : 0 ≤ Real.sin (x ^ 2 / 2) :=
    Real.sin_nonneg_of_nonneg_of_le_pi
      (div_nonneg (sq_nonneg x) (by norm_num)) (le_of_lt hx)
  have hcosnum :
      Real.cos (x ^ 2) = 2 * Real.cos (x ^ 2 / 2) ^ 2 - 1 := by
    convert Real.cos_two_mul (x ^ 2 / 2) using 1 <;> ring_nf
  have hcosden :
      Real.cos x = 2 * Real.cos (x / 2) ^ 2 - 1 := by
    convert Real.cos_two_mul (x / 2) using 1 <;> ring_nf
  have hnum :
      1 - Real.cos (x ^ 2) = 2 * Real.sin (x ^ 2 / 2) ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq (x ^ 2 / 2)]
  have hden :
      1 - Real.cos x = 2 * Real.sin (x / 2) ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq (x / 2)]
  unfold original halfAngle
  rw [hnum, hden, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2),
    Real.sqrt_sq_eq_abs, abs_of_nonneg hs]

private theorem halfAngleEventuallyEqNormalized :
    halfAngle =ᶠ[nhdsWithin 0 ({0} : Set ℝ)ᶜ] normalized := by
  have hpos :
      ∀ᶠ x in nhdsWithin 0 ({0} : Set ℝ)ᶜ,
        0 < (x / 2) / Real.sin (x / 2) :=
    divSinTendstoPunctured.eventually
      (isOpen_Ioi.mem_nhds (by norm_num : (1 : ℝ) ∈ Set.Ioi 0))
  filter_upwards [self_mem_nhdsWithin, hpos] with x hx hratio
  have hx0 : x ≠ 0 := by simpa using hx
  have hs0 : Real.sin (x / 2) ≠ 0 := by
    intro hs
    simp [hs] at hratio
  unfold halfAngle normalized
  field_simp [hx0, hs0]

theorem gap1 (L : ℝ) :
    HasLimitAtZero original L ↔ HasLimitAtZero halfAngle L := by
  unfold HasLimitAtZero
  exact Filter.tendsto_congr' originalEventuallyEqHalfAngle

/-- Exercise 502, gap 2. -/
theorem gap2 (L : ℝ) :
    HasLimitAtZero original L ↔ HasLimitAtZero normalized L := by
  refine (gap1 L).trans ?_
  unfold HasLimitAtZero
  exact Filter.tendsto_congr' halfAngleEventuallyEqNormalized

/-- Exercise 502, gap 3. -/
theorem gap3 : HasLimitAtZero normalized (Real.sqrt 2) := by
  unfold HasLimitAtZero
  have hsin :
      Filter.Tendsto (fun x : ℝ => Real.sin (x ^ 2 / 2) / (x ^ 2 / 2))
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1) :=
    sinDivTendstoPunctured.comp sqHalfTendstoPunctured
  have hc :
      Filter.Tendsto (fun _ : ℝ => Real.sqrt 2)
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds (Real.sqrt 2)) :=
    tendsto_const_nhds
  simpa [normalized] using
    ((hc.mul hsin).mul (divSinTendstoPunctured.pow 2))

/-- Exercise 502, gap 4. -/
theorem gap4 : HasLimitAtZero original (Real.sqrt 2) := by
  exact (gap2 (Real.sqrt 2)).2 gap3

end

end ProofGap.Exercise502
