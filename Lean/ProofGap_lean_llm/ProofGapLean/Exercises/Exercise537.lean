import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise537

noncomputable section

def lg (x : ℝ) : ℝ := Real.logb 10 x
def original (x h : ℝ) : ℝ := (lg (x + h) + lg (x - h) - 2 * lg x) / h ^ 2
def combined (x h : ℝ) : ℝ := (lg (x ^ 2 - h ^ 2) - lg (x ^ 2)) / h ^ 2
def exponentialForm (x h : ℝ) : ℝ :=
  -(1 / x ^ 2) * lg (Real.rpow (1 - h ^ 2 / x ^ 2) (-x ^ 2 / h ^ 2))
def HasLimitAtZero (f : ℝ → ℝ) (L : ℝ) : Prop :=
  Filter.Tendsto f (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds L)

/-- Source: `proof_gap/exercise_537/1.txt`. -/
private theorem eventually_valid537 (x : ℝ) (hx : 0 < x) :
    ∀ᶠ h in nhdsWithin 0 ({0} : Set ℝ)ᶜ,
      0 < x + h ∧ 0 < x - h ∧ h ≠ 0 := by
  have hzero :
      Filter.Tendsto (fun h : ℝ => h)
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 0) :=
    (continuousAt_id :
      ContinuousAt (fun h : ℝ => h) 0).mono_left inf_le_left
  have hplus :
      Filter.Tendsto (fun h : ℝ => x + h)
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds x) := by
    simpa using tendsto_const_nhds.add hzero
  have hminus :
      Filter.Tendsto (fun h : ℝ => x - h)
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds x) := by
    simpa using tendsto_const_nhds.sub hzero
  have hp : ∀ᶠ h in nhdsWithin 0 ({0} : Set ℝ)ᶜ, 0 < x + h := by
    simpa only [Set.mem_Ioi] using
      hplus.eventually (isOpen_Ioi.mem_nhds hx)
  have hm : ∀ᶠ h in nhdsWithin 0 ({0} : Set ℝ)ᶜ, 0 < x - h := by
    simpa only [Set.mem_Ioi] using
      hminus.eventually (isOpen_Ioi.mem_nhds hx)
  filter_upwards [hp, hm, eventually_mem_nhdsWithin] with h hp hm hmem
  refine ⟨hp, hm, ?_⟩
  simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hmem

theorem gap1 (x : ℝ) (hx : 0 < x) (L : ℝ) :
    HasLimitAtZero (original x) L ↔ HasLimitAtZero (combined x) L := by
  have heq :
      original x =ᶠ[nhdsWithin 0 ({0} : Set ℝ)ᶜ] combined x := by
    filter_upwards [eventually_valid537 x hx] with h hh
    have hp : 0 < x + h := hh.1
    have hm : 0 < x - h := hh.2.1
    have hfactor : x ^ 2 - h ^ 2 = (x + h) * (x - h) := by ring
    have hsquare : x ^ 2 = x * x := by ring
    simp only [original, combined, lg, Real.logb]
    rw [hfactor, hsquare, Real.log_mul hp.ne' hm.ne',
      Real.log_mul hx.ne' hx.ne']
    ring
  unfold HasLimitAtZero
  exact Filter.tendsto_congr' heq

/-- Source: `proof_gap/exercise_537/2.txt`. -/
theorem gap2 (x : ℝ) (hx : 0 < x) (L : ℝ) :
    HasLimitAtZero (combined x) L ↔ HasLimitAtZero (exponentialForm x) L := by
  have hx0 : x ≠ 0 := ne_of_gt hx
  have hx2 : 0 < x ^ 2 := pow_pos hx 2
  have hlog10 : Real.log (10 : ℝ) ≠ 0 :=
    ne_of_gt (Real.log_pos (by norm_num))
  have heq :
      combined x =ᶠ[nhdsWithin 0 ({0} : Set ℝ)ᶜ] exponentialForm x := by
    filter_upwards [eventually_valid537 x hx] with h hh
    have hp : 0 < x + h := hh.1
    have hm : 0 < x - h := hh.2.1
    have hh0 : h ≠ 0 := hh.2.2
    have hd : 0 < x ^ 2 - h ^ 2 := by
      have hprod := mul_pos hp hm
      nlinarith
    have hbase :
        1 - h ^ 2 / x ^ 2 = (x ^ 2 - h ^ 2) / x ^ 2 := by
      field_simp [hx0]
    have hb : 0 < 1 - h ^ 2 / x ^ 2 := by
      rw [hbase]
      exact div_pos hd hx2
    have hrpow :
        Real.rpow (1 - h ^ 2 / x ^ 2) (-x ^ 2 / h ^ 2) =
          Real.exp
            (Real.log (1 - h ^ 2 / x ^ 2) * (-x ^ 2 / h ^ 2)) := by
      change
        (1 - h ^ 2 / x ^ 2) ^ (-x ^ 2 / h ^ 2) =
          Real.exp
            (Real.log (1 - h ^ 2 / x ^ 2) * (-x ^ 2 / h ^ 2))
      rw [Real.rpow_def_of_pos hb]
    simp only [combined, exponentialForm, lg, Real.logb]
    rw [hrpow, Real.log_exp, hbase,
      Real.log_div hd.ne' hx2.ne']
    field_simp [hx0, hh0, hlog10]
  unfold HasLimitAtZero
  exact Filter.tendsto_congr' heq

/-- Source: `proof_gap/exercise_537/3.txt`. -/
theorem gap3 (x : ℝ) (hx : 0 < x) :
    HasLimitAtZero (exponentialForm x) (-(1 / x ^ 2) * lg (Real.exp 1)) := by
  apply (gap2 x hx (-(1 / x ^ 2) * lg (Real.exp 1))).mp
  unfold HasLimitAtZero
  have hlog10 : Real.log (10 : ℝ) ≠ 0 :=
    ne_of_gt (Real.log_pos (by norm_num))
  have hzero :
      Filter.Tendsto (fun h : ℝ => h)
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 0) :=
    (continuousAt_id :
      ContinuousAt (fun h : ℝ => h) 0).mono_left inf_le_left
  have ht :
      Filter.Tendsto (fun h : ℝ => -(h ^ 2))
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ)
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · simpa using (hzero.pow 2).neg
    · filter_upwards [eventually_valid537 x hx] with h hh
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      exact neg_ne_zero.mpr (pow_ne_zero 2 hh.2.2)
  have hslope :
      Filter.Tendsto
        (fun t : ℝ =>
          t⁻¹ • (Real.log (x ^ 2 + t) - Real.log (x ^ 2)))
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ)
        (nhds (x ^ 2)⁻¹) :=
    (Real.hasDerivAt_log (pow_ne_zero 2 (ne_of_gt hx))).tendsto_slope_zero
  have hscaled :
      Filter.Tendsto
        (fun h : ℝ =>
          (-(1 / Real.log 10)) *
            ((-(h ^ 2))⁻¹ *
              (Real.log (x ^ 2 - h ^ 2) - Real.log (x ^ 2))))
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ)
        (nhds ((-(1 / Real.log 10)) * (x ^ 2)⁻¹)) := by
    simpa only [Function.comp_apply, smul_eq_mul, sub_eq_add_neg] using
      (tendsto_const_nhds.mul (hslope.comp ht))
  have htarget :
      (-(1 / Real.log 10)) * (x ^ 2)⁻¹ =
        -(1 / x ^ 2) * lg (Real.exp 1) := by
    simp only [lg, Real.logb, Real.log_exp]
    ring
  rw [htarget] at hscaled
  have heq :
      (fun h : ℝ =>
        (-(1 / Real.log 10)) *
          ((-(h ^ 2))⁻¹ *
            (Real.log (x ^ 2 - h ^ 2) - Real.log (x ^ 2))))
        =ᶠ[nhdsWithin 0 ({0} : Set ℝ)ᶜ] combined x := by
    filter_upwards [eventually_valid537 x hx] with h hh
    have hh0 : h ≠ 0 := hh.2.2
    simp only [combined, lg, Real.logb]
    field_simp [hh0, hlog10] <;> ring
  exact (Filter.tendsto_congr' heq).mp hscaled

/-- Source: `proof_gap/exercise_537/4.txt`. -/
theorem gap4 (x : ℝ) (hx : 0 < x) :
    HasLimitAtZero (combined x) (-(1 / x ^ 2) * lg (Real.exp 1)) := by
  exact
    (gap2 x hx (-(1 / x ^ 2) * lg (Real.exp 1))).mpr (gap3 x hx)

end

end ProofGap.Exercise537
