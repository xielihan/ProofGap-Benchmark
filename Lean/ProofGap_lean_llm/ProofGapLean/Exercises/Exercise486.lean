import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise486

noncomputable section

def sec (x : ℝ) : ℝ := 1 / Real.cos x
def original (a x : ℝ) : ℝ := (sec x - sec a) / (x - a)
def transformed (a x : ℝ) : ℝ :=
  (Real.cos a - Real.cos x) / ((x - a) * Real.cos x * Real.cos a)
def factored (a x : ℝ) : ℝ :=
  (Real.sin ((x + a) / 2) / (Real.cos x * Real.cos a)) *
    (Real.sin ((x - a) / 2) / ((x - a) / 2))
def HasLimitAt (f : ℝ → ℝ) (a L : ℝ) : Prop :=
  Filter.Tendsto f (nhdsWithin a ({a} : Set ℝ)ᶜ) (nhds L)

/-- Exercise 486, gap 1; require `cos a≠0`. -/
private theorem secant_eventually_cos_ne (a : ℝ) (ha : Real.cos a ≠ 0) :
    ∀ᶠ x in nhdsWithin a ({a} : Set ℝ)ᶜ, Real.cos x ≠ 0 :=
  (Real.continuous_cos.continuousAt.eventually_ne ha).filter_mono inf_le_left

private theorem sin_div_tendsto_one :
    Filter.Tendsto (fun x : ℝ => Real.sin x / x)
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1) := by
  simpa [div_eq_mul_inv, mul_comm] using
    (Real.hasDerivAt_sin 0).tendsto_slope_zero

theorem gap1 (a : ℝ) (ha : Real.cos a ≠ 0) (L : ℝ) :
    HasLimitAt (original a) a L ↔ HasLimitAt (transformed a) a L := by
  unfold HasLimitAt
  apply Filter.tendsto_congr'
  filter_upwards [self_mem_nhdsWithin, secant_eventually_cos_ne a ha] with x hxa hcx
  have hne : x ≠ a := by
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hxa
  unfold original transformed sec
  field_simp [ha, hcx, hne]

/-- Exercise 486, gap 2; require `cos a≠0`. -/
theorem gap2 (a : ℝ) (ha : Real.cos a ≠ 0) (L : ℝ) :
    HasLimitAt (transformed a) a L ↔ HasLimitAt (factored a) a L := by
  unfold HasLimitAt
  apply Filter.tendsto_congr'
  filter_upwards [self_mem_nhdsWithin, secant_eventually_cos_ne a ha] with x hxa hcx
  have hne : x ≠ a := by
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hxa
  have ha' :
      (x + a) / 2 - (x - a) / 2 = a := by
    ring
  have hx' :
      (x + a) / 2 + (x - a) / 2 = x := by
    ring
  have htrig :
      Real.cos a - Real.cos x =
        2 * Real.sin ((x + a) / 2) * Real.sin ((x - a) / 2) := by
    calc
      Real.cos a - Real.cos x =
          Real.cos ((x + a) / 2 - (x - a) / 2) -
            Real.cos ((x + a) / 2 + (x - a) / 2) := by
              rw [ha', hx']
      _ = 2 * Real.sin ((x + a) / 2) * Real.sin ((x - a) / 2) := by
        rw [Real.cos_sub, Real.cos_add]
        ring
  unfold transformed factored
  rw [htrig]
  field_simp [ha, hcx, hne]

/-- Exercise 486, gap 3; require `cos a≠0`. -/
theorem gap3 (a : ℝ) (ha : Real.cos a ≠ 0) (L : ℝ) :
    HasLimitAt (original a) a L ↔ HasLimitAt (factored a) a L := by
  exact (gap1 a ha L).trans (gap2 a ha L)

/-- Exercise 486, gap 4; require `cos a≠0`. -/
theorem gap4 (a : ℝ) (ha : Real.cos a ≠ 0) :
    HasLimitAt (original a) a (Real.sin a / Real.cos a ^ 2) := by
  apply (gap3 a ha (Real.sin a / Real.cos a ^ 2)).2
  unfold HasLimitAt
  have hnum_cont :
      ContinuousAt (fun x : ℝ => Real.sin ((x + a) / (2 : ℝ))) a := by
    simpa only [Function.comp_apply] using
      Real.continuous_sin.continuousAt.comp
        ((continuousAt_id.add continuousAt_const).div_const (2 : ℝ))
  have hfirst_cont :
      ContinuousAt
        (fun x : ℝ =>
          Real.sin ((x + a) / 2) / (Real.cos x * Real.cos a)) a := by
    exact hnum_cont.div
      (Real.continuous_cos.continuousAt.mul continuousAt_const)
      (mul_ne_zero ha ha)
  have hfirst :
      Filter.Tendsto
        (fun x : ℝ =>
          Real.sin ((x + a) / 2) / (Real.cos x * Real.cos a))
        (nhdsWithin a ({a} : Set ℝ)ᶜ)
        (nhds (Real.sin a / Real.cos a ^ 2)) := by
    simpa only [show (a + a) / (2 : ℝ) = a by ring, pow_two] using
      (hfirst_cont.tendsto).mono_left inf_le_left
  have harg_cont :
      ContinuousAt (fun x : ℝ => (x - a) / (2 : ℝ)) a :=
    (continuousAt_id.sub continuousAt_const).div_const (2 : ℝ)
  have harg :
      Filter.Tendsto (fun x : ℝ => (x - a) / (2 : ℝ))
        (nhdsWithin a ({a} : Set ℝ)ᶜ)
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · simpa using (harg_cont.tendsto).mono_left inf_le_left
    · filter_upwards [self_mem_nhdsWithin] with x hx
      have hxne : x ≠ a := by
        simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hx
      simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using
        div_ne_zero (sub_ne_zero.mpr hxne) (by norm_num : (2 : ℝ) ≠ 0)
  have hsecond :
      Filter.Tendsto
        (fun x : ℝ =>
          Real.sin ((x - a) / 2) / ((x - a) / 2))
        (nhdsWithin a ({a} : Set ℝ)ᶜ) (nhds 1) := by
    simpa only [Function.comp_apply] using
      sin_div_tendsto_one.comp harg
  simpa only [factored, mul_one] using hfirst.mul hsecond

end

end ProofGap.Exercise486
