import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise515

noncomputable section

def original (a x : ℝ) : ℝ := Real.rpow ((x + a) / (x - a)) x
def rewritten (a x : ℝ) : ℝ :=
  Real.rpow (1 + 1 / ((x - a) / (2 * a)))
    (((x - a) / (2 * a)) * (2 * a) + a)
def HasLimitAtPosInfinity (f : ℝ → ℝ) (L : ℝ) : Prop :=
  Filter.Tendsto f Filter.atTop (nhds L)

/-- Exercise 515, gap 1; exclude the zero parameter used in the substitution. -/
private theorem original_limit_of_ne_zero (a : ℝ) (ha : a ≠ 0) :
    HasLimitAtPosInfinity (original a) (Real.exp (2 * a)) := by
  unfold HasLimitAtPosInfinity
  have hsub :
      Filter.Tendsto (fun x : ℝ => x - a) Filter.atTop Filter.atTop := by
    refine Filter.tendsto_atTop.2 ?_
    intro b
    filter_upwards [Filter.eventually_ge_atTop (b + a)] with x hx
    linarith
  have hinv0 :
      Filter.Tendsto (fun x : ℝ => x⁻¹) Filter.atTop (nhds 0) :=
    tendsto_inv_atTop_zero
  have hinv :
      Filter.Tendsto (fun x : ℝ => (x - a)⁻¹) Filter.atTop (nhds 0) :=
    hinv0.comp hsub
  have hc2a :
      Filter.Tendsto (fun _ : ℝ => 2 * a) Filter.atTop (nhds (2 * a)) :=
    tendsto_const_nhds
  have hz :
      Filter.Tendsto (fun x : ℝ => 2 * a / (x - a))
        Filter.atTop (nhds 0) := by
    simpa [div_eq_mul_inv] using hc2a.mul hinv
  have hc1 :
      Filter.Tendsto (fun _ : ℝ => (1 : ℝ)) Filter.atTop (nhds 1) :=
    tendsto_const_nhds
  have hq :
      Filter.Tendsto (fun x : ℝ => 1 + 2 * a / (x - a))
        Filter.atTop (nhds 1) := by
    simpa using hc1.add hz
  have hden : ∀ᶠ x : ℝ in Filter.atTop, x - a ≠ 0 := by
    filter_upwards [Filter.eventually_gt_atTop a] with x hx
    exact sub_ne_zero.mpr (ne_of_gt hx)
  have hz_ne :
      ∀ᶠ x : ℝ in Filter.atTop, 2 * a / (x - a) ≠ 0 := by
    filter_upwards [hden] with x hx
    exact div_ne_zero (mul_ne_zero (by norm_num) ha) hx
  have hz' :
      Filter.Tendsto (fun x : ℝ => 2 * a / (x - a))
        Filter.atTop (nhdsWithin (0 : ℝ) (({0} : Set ℝ)ᶜ)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨hz, ?_⟩
    filter_upwards [hz_ne] with x hx
    simpa using hx
  have hslope0 :
      Filter.Tendsto
        (fun z : ℝ => (Real.log (1 + z) - Real.log 1) / z)
        (nhdsWithin (0 : ℝ) (({0} : Set ℝ)ᶜ)) (nhds 1) := by
    simpa [div_eq_mul_inv, mul_comm] using
      (Real.hasDerivAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto_slope_zero
  have hslope :
      Filter.Tendsto
        (fun x : ℝ =>
          (Real.log (1 + 2 * a / (x - a)) - Real.log 1) /
            (2 * a / (x - a)))
        Filter.atTop (nhds 1) :=
    hslope0.comp hz'
  have hc2aa :
      Filter.Tendsto (fun _ : ℝ => 2 * a * a)
        Filter.atTop (nhds (2 * a * a)) :=
    tendsto_const_nhds
  have hcorr :
      Filter.Tendsto (fun x : ℝ => (2 * a * a) * (x - a)⁻¹)
        Filter.atTop (nhds 0) := by
    simpa using hc2aa.mul hinv
  have hw0 :
      Filter.Tendsto
        (fun x : ℝ => 2 * a + (2 * a * a) * (x - a)⁻¹)
        Filter.atTop (nhds (2 * a)) := by
    simpa using hc2a.add hcorr
  have hw :
      Filter.Tendsto (fun x : ℝ => (2 * a / (x - a)) * x)
        Filter.atTop (nhds (2 * a)) := by
    refine hw0.congr' ?_
    filter_upwards [hden] with x hx
    field_simp [hx] <;> ring
  have hp :
      Filter.Tendsto
        (fun x : ℝ =>
          ((Real.log (1 + 2 * a / (x - a)) - Real.log 1) /
              (2 * a / (x - a))) *
            ((2 * a / (x - a)) * x))
        Filter.atTop (nhds (2 * a)) := by
    simpa using hslope.mul hw
  have hlogx :
      Filter.Tendsto
        (fun x : ℝ => Real.log (1 + 2 * a / (x - a)) * x)
        Filter.atTop (nhds (2 * a)) := by
    refine hp.congr' ?_
    filter_upwards [hden] with x hx
    have hz0 : 2 * a / (x - a) ≠ 0 :=
      div_ne_zero (mul_ne_zero (by norm_num) ha) hx
    rw [Real.log_one, sub_zero]
    field_simp [hz0] <;> ring
  have hecont : ContinuousAt Real.exp (2 * a) :=
    Real.continuous_exp.continuousAt
  have hexp :
      Filter.Tendsto
        (fun x : ℝ => Real.exp (Real.log (1 + 2 * a / (x - a)) * x))
        Filter.atTop (nhds (Real.exp (2 * a))) :=
    hecont.tendsto.comp hlogx
  have hqpos :
      ∀ᶠ x : ℝ in Filter.atTop, 0 < 1 + 2 * a / (x - a) := by
    have hnear : ∀ᶠ y : ℝ in nhds 1, 0 < y :=
      Ioi_mem_nhds (by norm_num)
    exact hq.eventually hnear
  have hrpowq :
      Filter.Tendsto
        (fun x : ℝ => Real.rpow (1 + 2 * a / (x - a)) x)
        Filter.atTop (nhds (Real.exp (2 * a))) := by
    refine hexp.congr' ?_
    filter_upwards [hqpos] with x hx
    exact (Real.rpow_def_of_pos hx x).symm
  refine hrpowq.congr' ?_
  filter_upwards [hden] with x hx
  unfold original
  apply congrArg (fun y : ℝ => Real.rpow y x)
  field_simp [hx] <;> ring

theorem gap1 (a x : ℝ) (ha : a ≠ 0) (hxa : x ≠ a) :
    original a x = rewritten a x := by
  unfold original rewritten
  apply congrArg₂ Real.rpow
  · field_simp [ha, sub_ne_zero.mpr hxa] <;> ring
  · field_simp [ha] <;> ring

/-- Exercise 515, gap 2; exclude `a=0` in the displayed substitution. -/
theorem gap2 (a : ℝ) (ha : a ≠ 0) (L : ℝ) :
    HasLimitAtPosInfinity (original a) L ↔
      HasLimitAtPosInfinity (rewritten a) L := by
  unfold HasLimitAtPosInfinity
  have heq : original a =ᶠ[Filter.atTop] rewritten a := by
    filter_upwards [Filter.eventually_gt_atTop a] with x hx
    exact gap1 a x ha (ne_of_gt hx)
  exact ⟨fun h => h.congr' heq, fun h => h.congr' heq.symm⟩

/-- Exercise 515, gap 3; exclude `a=0` in the displayed substitution. -/
theorem gap3 (a : ℝ) (ha : a ≠ 0) :
    HasLimitAtPosInfinity (rewritten a) (Real.exp (2 * a)) := by
  exact (gap2 a ha (Real.exp (2 * a))).mp
    (original_limit_of_ne_zero a ha)

/-- Exercise 515, gap 4; the final limit also covers `a=0`. -/
theorem gap4 (a : ℝ) :
    HasLimitAtPosInfinity (original a) (Real.exp (2 * a)) := by
  by_cases ha : a = 0
  · subst a
    have hconst :
        Filter.Tendsto (fun _ : ℝ => (1 : ℝ)) Filter.atTop (nhds 1) :=
      tendsto_const_nhds
    have hlim :
        Filter.Tendsto (original 0) Filter.atTop (nhds 1) := by
      refine hconst.congr' ?_
      filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with x hx
      simp [original, ne_of_gt hx]
    simpa using hlim
  · exact original_limit_of_ne_zero a ha

end

end ProofGap.Exercise515
