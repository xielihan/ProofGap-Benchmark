import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise586

noncomputable section

def original (x : ℝ) : ℝ :=
  Real.log ((1 + x) / (1 - x)) /
    (Real.arctan (1 + x) - Real.arctan (1 - x))
def normalized (x : ℝ) : ℝ :=
  (Real.log (1 + 2 * x / (1 - x)) / (2 * x / (1 - x))) *
    ((2 * x / (2 - x ^ 2)) / Real.arctan (2 * x / (2 - x ^ 2))) *
    ((2 - x ^ 2) / (1 - x))
def HasLimitAtZero (f : ℝ → ℝ) (L : ℝ) : Prop :=
  Filter.Tendsto f (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds L)

/-- Source: `proof_gap/exercise_586/1.txt`. -/
private theorem eventually_abs_lt_one :
    Filter.Eventually (fun x : ℝ => |x| < 1)
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) := by
  have hid0 :
      Filter.Tendsto (fun x : ℝ => x) (nhds 0) (nhds 0) :=
    continuousAt_id
  have hid :
      Filter.Tendsto (fun x : ℝ => x)
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 0) :=
    hid0.mono_left inf_le_left
  have h :
      Filter.Eventually (fun x : ℝ => x ∈ Metric.ball (0 : ℝ) 1)
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) :=
    hid.eventually (Metric.ball_mem_nhds (0 : ℝ) (by norm_num))
  simpa [Metric.mem_ball, Real.dist_eq] using h

private theorem tendsto_punctured_zero {f : ℝ → ℝ}
    (h : Filter.Tendsto f (nhds 0) (nhds 0))
    (hne : Filter.Eventually (fun x : ℝ => f x ≠ 0)
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ)) :
    Filter.Tendsto f
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ)
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) := by
  rw [tendsto_nhdsWithin_iff]
  exact ⟨h.mono_left inf_le_left, by
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hne⟩

private theorem tendsto_log_one_plus_div_self :
    Filter.Tendsto (fun x : ℝ => Real.log (1 + x) / x)
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1) := by
  have hinner : HasDerivAt (fun x : ℝ => 1 + x) 1 0 := by
    simpa using
      ((hasDerivAt_const (x := (0 : ℝ)) (c := (1 : ℝ))).add
        (hasDerivAt_id (0 : ℝ)))
  have hlog : HasDerivAt Real.log 1 (1 + (0 : ℝ)) := by
    convert Real.hasDerivAt_log (by norm_num : (1 : ℝ) ≠ 0) using 1 <;>
      norm_num
  have hderiv : HasDerivAt (fun x : ℝ => Real.log (1 + x)) 1 0 := by
    simpa [Function.comp_def] using hlog.comp 0 hinner
  simpa [Real.log_one, div_eq_mul_inv, mul_comm] using
    hderiv.tendsto_slope_zero

private theorem tendsto_self_div_arctan :
    Filter.Tendsto (fun x : ℝ => x / Real.arctan x)
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1) := by
  have hderiv : HasDerivAt Real.arctan 1 0 := by
    simpa using Real.hasDerivAt_arctan 0
  have hdiv :
      Filter.Tendsto (fun x : ℝ => Real.arctan x / x)
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1) := by
    simpa [Real.arctan_zero, div_eq_mul_inv, mul_comm] using
      hderiv.tendsto_slope_zero
  convert hdiv.inv₀ (by norm_num : (1 : ℝ) ≠ 0) using 1 <;>
    simp only [inv_div, inv_one]

theorem gap1 (L : ℝ) :
    HasLimitAtZero original L ↔ HasLimitAtZero normalized L := by
  unfold HasLimitAtZero
  have heq :
      Filter.EventuallyEq (nhdsWithin 0 ({0} : Set ℝ)ᶜ) original normalized := by
    filter_upwards [eventually_abs_lt_one, self_mem_nhdsWithin] with x habs hxmem
    have hx0 : x ≠ 0 := by
      simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hxmem
    rcases abs_lt.mp habs with ⟨hxneg, hxpos⟩
    have hprod : 0 < (1 - x) * (1 + x) :=
      mul_pos (sub_pos.mpr hxpos) (by linarith)
    have hsquare : x ^ 2 < 1 := by
      nlinarith
    have hx1 : 1 - x ≠ 0 := by
      nlinarith
    have htwo : 2 - x ^ 2 ≠ 0 := by
      nlinarith
    have hu0 : 2 * x / (1 - x) ≠ 0 :=
      div_ne_zero (mul_ne_zero (by norm_num) hx0) hx1
    have hv0 : 2 * x / (2 - x ^ 2) ≠ 0 :=
      div_ne_zero (mul_ne_zero (by norm_num) hx0) htwo
    have hatan0 : Real.arctan (2 * x / (2 - x ^ 2)) ≠ 0 := by
      intro hzero
      apply hv0
      calc
        2 * x / (2 - x ^ 2) =
            Real.tan (Real.arctan (2 * x / (2 - x ^ 2))) :=
          (Real.tan_arctan (2 * x / (2 - x ^ 2))).symm
        _ = 0 := by simp [hzero]
    have hratio :
        1 + 2 * x / (1 - x) = (1 + x) / (1 - x) := by
      field_simp [hx1] <;> ring
    have hadd : (1 + x) * (-(1 - x)) < 1 := by
      nlinarith
    have harg :
        ((1 + x) + (-(1 - x))) /
            (1 - (1 + x) * (-(1 - x))) =
          2 * x / (2 - x ^ 2) := by
      congr 1 <;> ring
    have hatan :
        Real.arctan (1 + x) - Real.arctan (1 - x) =
          Real.arctan (2 * x / (2 - x ^ 2)) := by
      have h := Real.arctan_add hadd
      rw [harg] at h
      rw [Real.arctan_neg] at h
      simpa [sub_eq_add_neg] using h
    dsimp [original, normalized]
    rw [hratio, hatan]
    field_simp [hu0, hv0, hatan0, hx1, htwo] <;> ring
  constructor
  · intro horiginal
    exact horiginal.congr' heq
  · intro hnormalized
    exact hnormalized.congr' heq.symm

/-- Source: `proof_gap/exercise_586/2.txt`. -/
theorem gap2 : HasLimitAtZero normalized 2 := by
  unfold HasLimitAtZero
  have hid :
      Filter.Tendsto (fun x : ℝ => x) (nhds 0) (nhds 0) :=
    continuousAt_id
  have hnum :
      Filter.Tendsto (fun x : ℝ => 2 * x) (nhds 0) (nhds 0) := by
    simpa using
      ((tendsto_const_nhds : Filter.Tendsto (fun _ : ℝ => (2 : ℝ)) (nhds 0) (nhds 2)).mul hid)
  have hu_den :
      Filter.Tendsto (fun x : ℝ => 1 - x) (nhds 0) (nhds 1) := by
    simpa using
      ((tendsto_const_nhds : Filter.Tendsto (fun _ : ℝ => (1 : ℝ)) (nhds 0) (nhds 1)).sub hid)
  have hu_nhds :
      Filter.Tendsto (fun x : ℝ => 2 * x / (1 - x)) (nhds 0) (nhds 0) := by
    simpa using hnum.div hu_den (by norm_num : (1 : ℝ) ≠ 0)
  have hu_ne :
      Filter.Eventually (fun x : ℝ => 2 * x / (1 - x) ≠ 0)
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) := by
    filter_upwards [eventually_abs_lt_one, self_mem_nhdsWithin] with x habs hxmem
    have hx0 : x ≠ 0 := by
      simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hxmem
    have hxpos := (abs_lt.mp habs).2
    have hx1 : 1 - x ≠ 0 := by
      nlinarith
    exact div_ne_zero (mul_ne_zero (by norm_num) hx0) hx1
  have hu :
      Filter.Tendsto (fun x : ℝ => 2 * x / (1 - x))
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ)
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) :=
    tendsto_punctured_zero hu_nhds hu_ne
  have hsq :
      Filter.Tendsto (fun x : ℝ => x ^ 2) (nhds 0) (nhds 0) := by
    simpa using hid.pow 2
  have hv_den :
      Filter.Tendsto (fun x : ℝ => 2 - x ^ 2) (nhds 0) (nhds 2) := by
    simpa using
      ((tendsto_const_nhds : Filter.Tendsto (fun _ : ℝ => (2 : ℝ)) (nhds 0) (nhds 2)).sub hsq)
  have hv_nhds :
      Filter.Tendsto (fun x : ℝ => 2 * x / (2 - x ^ 2))
        (nhds 0) (nhds 0) := by
    simpa using hnum.div hv_den (by norm_num : (2 : ℝ) ≠ 0)
  have hv_ne :
      Filter.Eventually (fun x : ℝ => 2 * x / (2 - x ^ 2) ≠ 0)
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) := by
    filter_upwards [eventually_abs_lt_one, self_mem_nhdsWithin] with x habs hxmem
    have hx0 : x ≠ 0 := by
      simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hxmem
    rcases abs_lt.mp habs with ⟨hxneg, hxpos⟩
    have hprod : 0 < (1 - x) * (1 + x) :=
      mul_pos (sub_pos.mpr hxpos) (by linarith)
    have hsquare : x ^ 2 < 1 := by
      nlinarith
    have htwo : 2 - x ^ 2 ≠ 0 := by
      nlinarith
    exact div_ne_zero (mul_ne_zero (by norm_num) hx0) htwo
  have hv :
      Filter.Tendsto (fun x : ℝ => 2 * x / (2 - x ^ 2))
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ)
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) :=
    tendsto_punctured_zero hv_nhds hv_ne
  have hw_nhds :
      Filter.Tendsto (fun x : ℝ => (2 - x ^ 2) / (1 - x))
        (nhds 0) (nhds 2) := by
    simpa using hv_den.div hu_den (by norm_num : (1 : ℝ) ≠ 0)
  have hw :
      Filter.Tendsto (fun x : ℝ => (2 - x ^ 2) / (1 - x))
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 2) :=
    hw_nhds.mono_left inf_le_left
  have hlog := tendsto_log_one_plus_div_self.comp hu
  have hatan := tendsto_self_div_arctan.comp hv
  simpa [normalized] using (hlog.mul hatan).mul hw

/-- Source: `proof_gap/exercise_586/3.txt`. -/
theorem gap3 : HasLimitAtZero original 2 := by
  exact (gap1 2).mpr gap2

end

end ProofGap.Exercise586
