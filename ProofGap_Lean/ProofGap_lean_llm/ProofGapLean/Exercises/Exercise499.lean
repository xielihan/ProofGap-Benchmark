import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

namespace ProofGap.Exercise499

noncomputable section

def original (x : ℝ) : ℝ :=
  (Real.sqrt (1 + Real.tan x) - Real.sqrt (1 + Real.sin x)) / x ^ 3
def rationalized (x : ℝ) : ℝ :=
  (Real.tan x - Real.sin x) /
    (x ^ 3 * (Real.sqrt (1 + Real.tan x) + Real.sqrt (1 + Real.sin x)))
def expanded (x : ℝ) : ℝ :=
  (Real.sin x * (1 - Real.cos x)) /
    (x ^ 3 * Real.cos x *
      (Real.sqrt (1 + Real.tan x) + Real.sqrt (1 + Real.sin x)))
def normalized (x : ℝ) : ℝ :=
  (Real.sin x / x) *
    ((2 * Real.sin (x / 2) ^ 2) / (4 * (x / 2) ^ 2)) *
    (1 / (Real.cos x *
      (Real.sqrt (1 + Real.tan x) + Real.sqrt (1 + Real.sin x))))
def HasLimitAtZero (f : ℝ → ℝ) (L : ℝ) : Prop :=
  Filter.Tendsto f (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds L)

/-- Exercise 499, gap 1. -/
private theorem transformations_eventually :
    ∀ᶠ x in nhdsWithin 0 ({0} : Set ℝ)ᶜ,
      original x = rationalized x ∧
      rationalized x = expanded x ∧
      expanded x = normalized x := by
  have hsin0 : Filter.Tendsto Real.sin (nhds 0) (nhds 0) := by
    have h :=
      (Real.continuous_sin.continuousAt : ContinuousAt Real.sin (0 : ℝ))
    change Filter.Tendsto Real.sin (nhds 0) (nhds (Real.sin 0)) at h
    simpa using h
  have hcos0 : Filter.Tendsto Real.cos (nhds 0) (nhds 1) := by
    have h :=
      (Real.continuous_cos.continuousAt : ContinuousAt Real.cos (0 : ℝ))
    change Filter.Tendsto Real.cos (nhds 0) (nhds (Real.cos 0)) at h
    simpa using h
  have htan_div : Filter.Tendsto (Real.sin / Real.cos)
      (nhds 0) (nhds 0) := by
    simpa only [zero_div] using
      hsin0.div hcos0 (by norm_num : (1 : ℝ) ≠ 0)
  have htan0 : Filter.Tendsto Real.tan (nhds 0) (nhds 0) := by
    refine htan_div.congr' ?_
    filter_upwards with x
    simpa only [Pi.div_apply] using (Real.tan_eq_sin_div_cos x).symm
  have htan_gt_nhds : ∀ᶠ x in nhds 0, -1 < Real.tan x := by
    have hm : Set.Ioi (-1 : ℝ) ∈ nhds (0 : ℝ) :=
      Ioi_mem_nhds (by norm_num)
    simpa only [Set.mem_Ioi] using htan0.eventually hm
  have hsin_gt_nhds : ∀ᶠ x in nhds 0, -1 < Real.sin x := by
    have hm : Set.Ioi (-1 : ℝ) ∈ nhds (0 : ℝ) :=
      Ioi_mem_nhds (by norm_num)
    simpa only [Set.mem_Ioi] using hsin0.eventually hm
  have hcos_pos_nhds : ∀ᶠ x in nhds 0, 0 < Real.cos x := by
    have hm : Set.Ioi (0 : ℝ) ∈ nhds (1 : ℝ) :=
      Ioi_mem_nhds (by norm_num)
    simpa only [Set.mem_Ioi] using hcos0.eventually hm
  have htan_gt : ∀ᶠ x in nhdsWithin 0 ({0} : Set ℝ)ᶜ,
      -1 < Real.tan x :=
    (show nhdsWithin 0 ({0} : Set ℝ)ᶜ ≤ nhds 0 from inf_le_left)
      htan_gt_nhds
  have hsin_gt : ∀ᶠ x in nhdsWithin 0 ({0} : Set ℝ)ᶜ,
      -1 < Real.sin x :=
    (show nhdsWithin 0 ({0} : Set ℝ)ᶜ ≤ nhds 0 from inf_le_left)
      hsin_gt_nhds
  have hcos_pos : ∀ᶠ x in nhdsWithin 0 ({0} : Set ℝ)ᶜ,
      0 < Real.cos x :=
    (show nhdsWithin 0 ({0} : Set ℝ)ᶜ ≤ nhds 0 from inf_le_left)
      hcos_pos_nhds
  have hpunc : ∀ᶠ x in nhdsWithin 0 ({0} : Set ℝ)ᶜ, x ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    simpa using hx
  filter_upwards [hpunc, htan_gt, hsin_gt, hcos_pos] with x hx ht hs hc
  have htan_nonneg : 0 ≤ 1 + Real.tan x := by linarith
  have hsin_nonneg : 0 ≤ 1 + Real.sin x := by linarith
  have hsq_tan := Real.sq_sqrt htan_nonneg
  have hsq_sin := Real.sq_sqrt hsin_nonneg
  have hsqrt_sin_pos : 0 < Real.sqrt (1 + Real.sin x) :=
    Real.sqrt_pos.2 (by linarith)
  have hsum :
      Real.sqrt (1 + Real.tan x) + Real.sqrt (1 + Real.sin x) ≠ 0 :=
    ne_of_gt
      (add_pos_of_nonneg_of_pos (Real.sqrt_nonneg _) hsqrt_sin_pos)
  have hcos_ne : Real.cos x ≠ 0 := ne_of_gt hc
  have hrat :
      (Real.sqrt (1 + Real.tan x) - Real.sqrt (1 + Real.sin x)) *
          (Real.sqrt (1 + Real.tan x) + Real.sqrt (1 + Real.sin x)) =
        Real.tan x - Real.sin x := by
    nlinarith [hsq_tan, hsq_sin]
  have htan_diff :
      Real.tan x - Real.sin x =
        Real.sin x * (1 - Real.cos x) / Real.cos x := by
    rw [Real.tan_eq_sin_div_cos]
    field_simp [hcos_ne] <;> ring
  have hcos_half :
      Real.cos x = 2 * Real.cos (x / 2) ^ 2 - 1 := by
    calc
      Real.cos x = Real.cos (2 * (x / 2)) := by congr 1 <;> ring
      _ = 2 * Real.cos (x / 2) ^ 2 - 1 := Real.cos_two_mul (x / 2)
  have htrig :
      1 - Real.cos x = 2 * Real.sin (x / 2) ^ 2 := by
    rw [hcos_half]
    nlinarith [Real.sin_sq_add_cos_sq (x / 2)]
  refine ⟨?_, ?_, ?_⟩
  · unfold original rationalized
    rw [← hrat]
    field_simp [hx, hsum] <;> ring
  · unfold rationalized expanded
    rw [htan_diff]
    field_simp [hx, hcos_ne, hsum] <;> ring
  · unfold expanded normalized
    rw [htrig]
    field_simp [hx, hcos_ne, hsum] <;> ring

theorem gap1 (L : ℝ) :
    HasLimitAtZero original L ↔ HasLimitAtZero rationalized L := by
  unfold HasLimitAtZero
  have heq : Filter.EventuallyEq
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) original rationalized :=
    transformations_eventually.mono (fun _ h => h.1)
  constructor
  · intro h
    exact h.congr' heq
  · intro h
    exact h.congr' heq.symm

/-- Exercise 499, gap 2. -/
theorem gap2 (L : ℝ) :
    HasLimitAtZero original L ↔ HasLimitAtZero expanded L := by
  unfold HasLimitAtZero
  have heq : Filter.EventuallyEq
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) original expanded :=
    transformations_eventually.mono (fun _ h => h.1.trans h.2.1)
  constructor
  · intro h
    exact h.congr' heq
  · intro h
    exact h.congr' heq.symm

/-- Exercise 499, gap 3. -/
theorem gap3 (L : ℝ) :
    HasLimitAtZero original L ↔ HasLimitAtZero normalized L := by
  unfold HasLimitAtZero
  have heq : Filter.EventuallyEq
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) original normalized :=
    transformations_eventually.mono
      (fun _ h => (h.1.trans h.2.1).trans h.2.2)
  constructor
  · intro h
    exact h.congr' heq
  · intro h
    exact h.congr' heq.symm

/-- Exercise 499, gap 4. -/
theorem gap4 : HasLimitAtZero normalized (1 / 4) := by
  unfold HasLimitAtZero normalized
  have hto0 : Filter.Tendsto (fun x : ℝ => x)
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 0) :=
    Filter.tendsto_id.mono_right inf_le_left
  have hsin : Filter.Tendsto (fun x : ℝ => Real.sin x / x)
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1) := by
    have h := (Real.hasDerivAt_sin (0 : ℝ)).tendsto_slope_zero
    simpa [div_eq_mul_inv, mul_comm] using h
  have hscale : Filter.Tendsto (fun x : ℝ => x / 2)
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ)
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · simpa using hto0.div_const (2 : ℝ)
    · filter_upwards [self_mem_nhdsWithin] with x hx
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hx ⊢
      exact div_ne_zero hx (by norm_num)
  have hsinhalf : Filter.Tendsto
      (fun x : ℝ => Real.sin (x / 2) / (x / 2))
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1) :=
    hsin.comp hscale
  have hhalf_const : Filter.Tendsto (fun _ : ℝ => (1 / 2 : ℝ))
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds (1 / 2)) :=
    tendsto_const_nhds
  have hsecond_form : Filter.Tendsto
      (fun x : ℝ => (1 / 2 : ℝ) *
        (Real.sin (x / 2) / (x / 2)) ^ 2)
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds (1 / 2)) := by
    convert hhalf_const.mul (hsinhalf.pow 2) using 1 <;> norm_num
  have hsecond : Filter.Tendsto
      (fun x : ℝ =>
        (2 * Real.sin (x / 2) ^ 2) / (4 * (x / 2) ^ 2))
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds (1 / 2)) := by
    refine hsecond_form.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hx0 : x ≠ 0 := by simpa using hx
    have hy0 : x / 2 ≠ 0 := div_ne_zero hx0 (by norm_num)
    field_simp [hy0] <;> ring
  have hone : Filter.Tendsto (fun _ : ℝ => (1 : ℝ))
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1) :=
    tendsto_const_nhds
  have hsin_at : Filter.Tendsto Real.sin (nhds 0) (nhds 0) := by
    have h :=
      (Real.continuous_sin.continuousAt : ContinuousAt Real.sin (0 : ℝ))
    change Filter.Tendsto Real.sin (nhds 0) (nhds (Real.sin 0)) at h
    simpa using h
  have hsin0 : Filter.Tendsto Real.sin
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 0) :=
    hsin_at.comp hto0
  have hcos_at : Filter.Tendsto Real.cos (nhds 0) (nhds 1) := by
    have h :=
      (Real.continuous_cos.continuousAt : ContinuousAt Real.cos (0 : ℝ))
    change Filter.Tendsto Real.cos (nhds 0) (nhds (Real.cos 0)) at h
    simpa using h
  have hcos1 : Filter.Tendsto Real.cos
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1) :=
    hcos_at.comp hto0
  have htan_div : Filter.Tendsto (Real.sin / Real.cos)
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 0) := by
    simpa only [zero_div] using
      hsin0.div hcos1 (by norm_num : (1 : ℝ) ≠ 0)
  have htan0 : Filter.Tendsto Real.tan
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 0) := by
    refine htan_div.congr' ?_
    filter_upwards with x
    simpa only [Pi.div_apply] using (Real.tan_eq_sin_div_cos x).symm
  have hone_tan : Filter.Tendsto (fun x : ℝ => 1 + Real.tan x)
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1) := by
    convert hone.add htan0 using 1 <;> norm_num
  have hone_sin : Filter.Tendsto (fun x : ℝ => 1 + Real.sin x)
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1) := by
    convert hone.add hsin0 using 1 <;> norm_num
  have hsqrt_at : Filter.Tendsto Real.sqrt (nhds 1) (nhds 1) := by
    have h :=
      (Real.continuous_sqrt.continuousAt : ContinuousAt Real.sqrt (1 : ℝ))
    change Filter.Tendsto Real.sqrt (nhds 1) (nhds (Real.sqrt 1)) at h
    simpa using h
  have hsqrt_tan : Filter.Tendsto
      (fun x : ℝ => Real.sqrt (1 + Real.tan x))
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1) :=
    hsqrt_at.comp hone_tan
  have hsqrt_sin : Filter.Tendsto
      (fun x : ℝ => Real.sqrt (1 + Real.sin x))
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1) :=
    hsqrt_at.comp hone_sin
  have hden : Filter.Tendsto
      (fun x : ℝ => Real.cos x *
        (Real.sqrt (1 + Real.tan x) + Real.sqrt (1 + Real.sin x)))
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 2) := by
    convert hcos1.mul (hsqrt_tan.add hsqrt_sin) using 1 <;> norm_num
  have hthird : Filter.Tendsto
      (fun x : ℝ => 1 / (Real.cos x *
        (Real.sqrt (1 + Real.tan x) + Real.sqrt (1 + Real.sin x))))
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds (1 / 2)) := by
    exact hone.div hden (by norm_num : (2 : ℝ) ≠ 0)
  convert (hsin.mul hsecond).mul hthird using 1 <;> norm_num

/-- Exercise 499, gap 5. -/
theorem gap5 : HasLimitAtZero original (1 / 4) := by
  exact (gap3 (1 / 4)).2 gap4

end

end ProofGap.Exercise499
