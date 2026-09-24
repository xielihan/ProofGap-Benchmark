import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise567

noncomputable section

def original (x : ℝ) : ℝ :=
  Real.log (1 + x * Real.exp x) /
    Real.log (x + Real.sqrt (1 + x ^ 2))
def expanded (x : ℝ) : ℝ :=
  ((Real.log (1 + x * Real.exp x) / (x * Real.exp x)) * x * Real.exp x) /
  ((1 / 2 : ℝ) * Real.log (1 + x ^ 2) +
    (Real.log (1 + x / Real.sqrt (1 + x ^ 2)) /
      (x / Real.sqrt (1 + x ^ 2))) *
    (x / Real.sqrt (1 + x ^ 2)))
def reduced (x : ℝ) : ℝ :=
  (x * Real.exp x) / (x / Real.sqrt (1 + x ^ 2))
def cancelled (x : ℝ) : ℝ := Real.exp x * Real.sqrt (1 + x ^ 2)
def HasLimitAtZero (f : ℝ → ℝ) (L : ℝ) : Prop :=
  Filter.Tendsto f (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds L)

/-- Source: `proof_gap/exercise_567/1.txt`. -/
private theorem logRatio_comp_at_zero
    (g : ℝ → ℝ)
    (hg : Filter.Tendsto g
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 0))
    (hne : ∀ᶠ x in nhdsWithin 0 ({0} : Set ℝ)ᶜ, g x ≠ 0) :
    Filter.Tendsto (fun x => Real.log (1 + g x) / g x)
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1) := by
  have hinner : HasDerivAt (fun z : ℝ => 1 + z) 1 0 := by
    simpa using
      (hasDerivAt_const (0 : ℝ) (1 : ℝ)).add
        (hasDerivAt_id (𝕜 := ℝ) 0)
  have hlog : HasDerivAt Real.log 1 (1 + (0 : ℝ)) := by
    simpa using
      (Real.hasDerivAt_log (by norm_num : (1 : ℝ) ≠ 0))
  have hd : HasDerivAt (fun z : ℝ => Real.log (1 + z)) 1 0 := by
    simpa [Function.comp_def] using hlog.comp 0 hinner
  have hs := hasDerivAt_iff_tendsto_slope.mp hd
  change Filter.Tendsto
      (fun z : ℝ => (z - 0)⁻¹ •
        (Real.log (1 + z) - Real.log (1 + 0)))
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1) at hs
  have hs' :
      Filter.Tendsto (fun z : ℝ => z⁻¹ * Real.log (1 + z))
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1) := by
    simpa only [sub_zero, add_zero, Real.log_one, smul_eq_mul] using hs
  have hbase :
      Filter.Tendsto (fun z : ℝ => Real.log (1 + z) / z)
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1) := by
    have heq :
        (fun z : ℝ => Real.log (1 + z) / z) =
          (fun z : ℝ => z⁻¹ * Real.log (1 + z)) := by
      funext z
      simp only [div_eq_mul_inv, mul_comm]
    rw [heq]
    exact hs'
  have hg' :
      Filter.Tendsto g
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ)
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · exact hg
    · filter_upwards [hne] with x hx
      simpa using hx
  simpa only [Function.comp_apply] using hbase.comp hg'

private theorem cancelled_limit_at_zero :
    HasLimitAtZero cancelled 1 := by
  unfold HasLimitAtZero
  have h : ContinuousAt cancelled 0 := by
    unfold cancelled
    fun_prop
  simpa [cancelled] using h.mono_left inf_le_left

private theorem reduced_eq_cancelled_ne_zero :
    reduced =ᶠ[nhdsWithin 0 ({0} : Set ℝ)ᶜ] cancelled := by
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hx0 : x ≠ 0 := by simpa using hx
  have hs : 0 < 1 + x ^ 2 := by nlinarith [sq_nonneg x]
  have hr : 0 < Real.sqrt (1 + x ^ 2) := Real.sqrt_pos.2 hs
  unfold reduced cancelled
  field_simp [hx0, hr.ne']

private theorem expanded_limit_at_zero :
    HasLimitAtZero expanded 1 := by
  unfold HasLimitAtZero
  have hx_ne : ∀ᶠ x : ℝ in nhdsWithin 0 ({0} : Set ℝ)ᶜ, x ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    simpa using hx
  have hxlim :
      Filter.Tendsto (fun x : ℝ => x)
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 0) := by
    exact continuousAt_id.mono_left inf_le_left
  have ht0 :
      Filter.Tendsto (fun x : ℝ => x * Real.exp x)
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 0) := by
    have hc : ContinuousAt (fun x : ℝ => x * Real.exp x) 0 := by
      fun_prop
    simpa using hc.mono_left inf_le_left
  have ht_ne :
      ∀ᶠ x : ℝ in nhdsWithin 0 ({0} : Set ℝ)ᶜ,
        x * Real.exp x ≠ 0 := by
    filter_upwards [hx_ne] with x hx
    exact mul_ne_zero hx (Real.exp_ne_zero x)
  have hr0 :
      Filter.Tendsto (fun x : ℝ => Real.sqrt (1 + x ^ 2))
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1) := by
    have hc : ContinuousAt (fun x : ℝ => Real.sqrt (1 + x ^ 2)) 0 := by
      fun_prop
    simpa using hc.mono_left inf_le_left
  have hu0 :
      Filter.Tendsto
        (fun x : ℝ => x / Real.sqrt (1 + x ^ 2))
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 0) := by
    have hden : ContinuousAt (fun x : ℝ => Real.sqrt (1 + x ^ 2)) 0 := by
      fun_prop
    have hc : ContinuousAt
        (fun x : ℝ => x / Real.sqrt (1 + x ^ 2)) 0 :=
      continuousAt_id.div hden (by norm_num)
    simpa using hc.mono_left inf_le_left
  have hu_ne :
      ∀ᶠ x : ℝ in nhdsWithin 0 ({0} : Set ℝ)ᶜ,
        x / Real.sqrt (1 + x ^ 2) ≠ 0 := by
    filter_upwards [hx_ne] with x hx
    have hs : 0 < 1 + x ^ 2 := by nlinarith [sq_nonneg x]
    have hr : 0 < Real.sqrt (1 + x ^ 2) := Real.sqrt_pos.2 hs
    exact div_ne_zero hx hr.ne'
  have hv0 :
      Filter.Tendsto (fun x : ℝ => x ^ 2)
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 0) := by
    have hc : ContinuousAt (fun x : ℝ => x ^ 2) 0 := by
      fun_prop
    simpa using hc.mono_left inf_le_left
  have hv_ne :
      ∀ᶠ x : ℝ in nhdsWithin 0 ({0} : Set ℝ)ᶜ, x ^ 2 ≠ 0 := by
    filter_upwards [hx_ne] with x hx
    exact pow_ne_zero 2 hx
  have hA :
      Filter.Tendsto
        (fun x : ℝ =>
          Real.log (1 + x * Real.exp x) / (x * Real.exp x))
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1) :=
    logRatio_comp_at_zero (fun x : ℝ => x * Real.exp x) ht0 ht_ne
  have hB :
      Filter.Tendsto
        (fun x : ℝ =>
          Real.log (1 + x / Real.sqrt (1 + x ^ 2)) /
            (x / Real.sqrt (1 + x ^ 2)))
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1) :=
    logRatio_comp_at_zero
      (fun x : ℝ => x / Real.sqrt (1 + x ^ 2)) hu0 hu_ne
  have hD :
      Filter.Tendsto
        (fun x : ℝ => Real.log (1 + x ^ 2) / (x ^ 2))
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1) :=
    logRatio_comp_at_zero (fun x : ℝ => x ^ 2) hv0 hv_ne
  have hhalf :
      Filter.Tendsto (fun _ : ℝ => (1 / 2 : ℝ))
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds (1 / 2 : ℝ)) :=
    tendsto_const_nhds
  have hErhs :
      Filter.Tendsto
        (fun x : ℝ =>
          (1 / 2 : ℝ) * (Real.log (1 + x ^ 2) / (x ^ 2)) *
            (x * Real.sqrt (1 + x ^ 2)))
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 0) := by
    have h := (hhalf.mul hD).mul (hxlim.mul hr0)
    simpa using h
  have hEeq :
      (fun x : ℝ =>
          ((1 / 2 : ℝ) * Real.log (1 + x ^ 2)) /
            (x / Real.sqrt (1 + x ^ 2))) =ᶠ[
        nhdsWithin 0 ({0} : Set ℝ)ᶜ]
      (fun x : ℝ =>
          (1 / 2 : ℝ) * (Real.log (1 + x ^ 2) / (x ^ 2)) *
            (x * Real.sqrt (1 + x ^ 2))) := by
    filter_upwards [hx_ne] with x hx
    have hs : 0 < 1 + x ^ 2 := by nlinarith [sq_nonneg x]
    have hr : 0 < Real.sqrt (1 + x ^ 2) := Real.sqrt_pos.2 hs
    field_simp [hx, hr.ne']
    <;> ring
  have hE :
      Filter.Tendsto
        (fun x : ℝ =>
          ((1 / 2 : ℝ) * Real.log (1 + x ^ 2)) /
            (x / Real.sqrt (1 + x ^ 2)))
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 0) :=
    hErhs.congr' hEeq.symm
  have hred : HasLimitAtZero reduced 1 :=
    cancelled_limit_at_zero.congr' reduced_eq_cancelled_ne_zero.symm
  have hsum :
      Filter.Tendsto
        (fun x : ℝ =>
          ((1 / 2 : ℝ) * Real.log (1 + x ^ 2)) /
              (x / Real.sqrt (1 + x ^ 2)) +
            Real.log (1 + x / Real.sqrt (1 + x ^ 2)) /
              (x / Real.sqrt (1 + x ^ 2)))
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1) := by
    convert hE.add hB using 1 <;> norm_num
  have hsum_pos :
      ∀ᶠ x : ℝ in nhdsWithin 0 ({0} : Set ℝ)ᶜ,
        0 <
          ((1 / 2 : ℝ) * Real.log (1 + x ^ 2)) /
              (x / Real.sqrt (1 + x ^ 2)) +
            Real.log (1 + x / Real.sqrt (1 + x ^ 2)) /
              (x / Real.sqrt (1 + x ^ 2)) := by
    have hm := hsum (Ioi_mem_nhds (show (0 : ℝ) < 1 by norm_num))
    simpa using hm
  have hmain :
      Filter.Tendsto
        (fun x : ℝ =>
          (Real.log (1 + x * Real.exp x) / (x * Real.exp x)) * reduced x /
            (((1 / 2 : ℝ) * Real.log (1 + x ^ 2)) /
                (x / Real.sqrt (1 + x ^ 2)) +
              Real.log (1 + x / Real.sqrt (1 + x ^ 2)) /
                (x / Real.sqrt (1 + x ^ 2))))
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1) := by
    convert (hA.mul hred).div hsum (by norm_num : (1 : ℝ) ≠ 0) using 1
    <;> norm_num
  have heq :
      expanded =ᶠ[nhdsWithin 0 ({0} : Set ℝ)ᶜ]
        (fun x : ℝ =>
          (Real.log (1 + x * Real.exp x) / (x * Real.exp x)) * reduced x /
            (((1 / 2 : ℝ) * Real.log (1 + x ^ 2)) /
                (x / Real.sqrt (1 + x ^ 2)) +
              Real.log (1 + x / Real.sqrt (1 + x ^ 2)) /
                (x / Real.sqrt (1 + x ^ 2)))) := by
    filter_upwards [hx_ne, hsum_pos] with x hx hpos
    have hs : 0 < 1 + x ^ 2 := by nlinarith [sq_nonneg x]
    have hr : 0 < Real.sqrt (1 + x ^ 2) := Real.sqrt_pos.2 hs
    have ht : x * Real.exp x ≠ 0 :=
      mul_ne_zero hx (Real.exp_ne_zero x)
    have hu : x / Real.sqrt (1 + x ^ 2) ≠ 0 :=
      div_ne_zero hx hr.ne'
    have hsumne :
        ((1 / 2 : ℝ) * Real.log (1 + x ^ 2)) /
              (x / Real.sqrt (1 + x ^ 2)) +
            Real.log (1 + x / Real.sqrt (1 + x ^ 2)) /
              (x / Real.sqrt (1 + x ^ 2)) ≠ 0 :=
      ne_of_gt hpos
    have hden :
        (1 / 2 : ℝ) * Real.log (1 + x ^ 2) +
              (Real.log (1 + x / Real.sqrt (1 + x ^ 2)) /
                (x / Real.sqrt (1 + x ^ 2))) *
                (x / Real.sqrt (1 + x ^ 2)) =
          (x / Real.sqrt (1 + x ^ 2)) *
            (((1 / 2 : ℝ) * Real.log (1 + x ^ 2)) /
                (x / Real.sqrt (1 + x ^ 2)) +
              Real.log (1 + x / Real.sqrt (1 + x ^ 2)) /
                (x / Real.sqrt (1 + x ^ 2))) := by
      field_simp [hu]
      <;> ring
    have hdenne :
        (1 / 2 : ℝ) * Real.log (1 + x ^ 2) +
              (Real.log (1 + x / Real.sqrt (1 + x ^ 2)) /
                (x / Real.sqrt (1 + x ^ 2))) *
                (x / Real.sqrt (1 + x ^ 2)) ≠ 0 := by
      rw [hden]
      exact mul_ne_zero hu hsumne
    unfold expanded reduced
    field_simp [ht, hu, hsumne, hdenne, hx, hr.ne']
    <;> ring
  exact hmain.congr' heq.symm

theorem gap1 (L : ℝ) :
    HasLimitAtZero original L ↔ HasLimitAtZero expanded L := by
  have heq :
      original =ᶠ[nhdsWithin 0 ({0} : Set ℝ)ᶜ] expanded := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hx0 : x ≠ 0 := by simpa using hx
    have hs : 0 < 1 + x ^ 2 := by nlinarith [sq_nonneg x]
    have hr : 0 < Real.sqrt (1 + x ^ 2) := Real.sqrt_pos.2 hs
    have hsq : (Real.sqrt (1 + x ^ 2)) ^ 2 = 1 + x ^ 2 :=
      Real.sq_sqrt (le_of_lt hs)
    have hxp : 0 < x + Real.sqrt (1 + x ^ 2) := by
      nlinarith [Real.sqrt_nonneg (1 + x ^ 2)]
    have hone : 0 < 1 + x / Real.sqrt (1 + x ^ 2) := by
      have hid :
          1 + x / Real.sqrt (1 + x ^ 2) =
            (Real.sqrt (1 + x ^ 2) + x) / Real.sqrt (1 + x ^ 2) := by
        field_simp [hr.ne']
      rw [hid]
      exact div_pos (by linarith) hr
    have harg :
        x + Real.sqrt (1 + x ^ 2) =
          Real.sqrt (1 + x ^ 2) *
            (1 + x / Real.sqrt (1 + x ^ 2)) := by
      field_simp [hr.ne']
      <;> ring
    have hrr :
        Real.sqrt (1 + x ^ 2) * Real.sqrt (1 + x ^ 2) = 1 + x ^ 2 := by
      nlinarith
    have hlogr :
        Real.log (Real.sqrt (1 + x ^ 2)) =
          (1 / 2 : ℝ) * Real.log (1 + x ^ 2) := by
      have hm := Real.log_mul hr.ne' hr.ne'
      rw [hrr] at hm
      nlinarith
    have ht : x * Real.exp x ≠ 0 :=
      mul_ne_zero hx0 (Real.exp_ne_zero x)
    have hu : x / Real.sqrt (1 + x ^ 2) ≠ 0 :=
      div_ne_zero hx0 hr.ne'
    have hnum :
        (Real.log (1 + x * Real.exp x) / (x * Real.exp x)) * x * Real.exp x =
          Real.log (1 + x * Real.exp x) := by
      field_simp [ht]
    have hsecond :
        (Real.log (1 + x / Real.sqrt (1 + x ^ 2)) /
            (x / Real.sqrt (1 + x ^ 2))) *
            (x / Real.sqrt (1 + x ^ 2)) =
          Real.log (1 + x / Real.sqrt (1 + x ^ 2)) := by
      field_simp [hu]
    have hden :
        Real.log (x + Real.sqrt (1 + x ^ 2)) =
          (1 / 2 : ℝ) * Real.log (1 + x ^ 2) +
            (Real.log (1 + x / Real.sqrt (1 + x ^ 2)) /
                (x / Real.sqrt (1 + x ^ 2))) *
              (x / Real.sqrt (1 + x ^ 2)) := by
      calc
        Real.log (x + Real.sqrt (1 + x ^ 2)) =
            Real.log
              (Real.sqrt (1 + x ^ 2) *
                (1 + x / Real.sqrt (1 + x ^ 2))) := by rw [harg]
        _ = Real.log (Real.sqrt (1 + x ^ 2)) +
              Real.log (1 + x / Real.sqrt (1 + x ^ 2)) :=
          Real.log_mul hr.ne' hone.ne'
        _ = (1 / 2 : ℝ) * Real.log (1 + x ^ 2) +
              Real.log (1 + x / Real.sqrt (1 + x ^ 2)) := by rw [hlogr]
        _ = _ := by rw [hsecond]
    unfold original expanded
    rw [hnum, hden]
  constructor
  · intro h
    exact h.congr' heq
  · intro h
    exact h.congr' heq.symm

/-- Source: `proof_gap/exercise_567/2.txt`. -/
theorem gap2 (L : ℝ) :
    HasLimitAtZero expanded L ↔ HasLimitAtZero reduced L := by
  have hexp : HasLimitAtZero expanded 1 := expanded_limit_at_zero
  have hred : HasLimitAtZero reduced 1 := by
    exact cancelled_limit_at_zero.congr' reduced_eq_cancelled_ne_zero.symm
  constructor
  · intro h
    have hL : L = 1 := tendsto_nhds_unique h hexp
    simpa [hL] using hred
  · intro h
    have hL : L = 1 := tendsto_nhds_unique h hred
    simpa [hL] using hexp

/-- Source: `proof_gap/exercise_567/3.txt`. -/
theorem gap3 (L : ℝ) :
    HasLimitAtZero reduced L ↔ HasLimitAtZero cancelled L := by
  constructor
  · intro h
    exact h.congr' reduced_eq_cancelled_ne_zero
  · intro h
    exact h.congr' reduced_eq_cancelled_ne_zero.symm

/-- Source: `proof_gap/exercise_567/4.txt`. -/
theorem gap4 : HasLimitAtZero cancelled 1 := by
  exact cancelled_limit_at_zero

/-- Source: `proof_gap/exercise_567/5.txt`. -/
theorem gap5 : HasLimitAtZero original 1 := by
  exact (gap1 1).mpr ((gap2 1).mpr ((gap3 1).mpr gap4))

end

end ProofGap.Exercise567
