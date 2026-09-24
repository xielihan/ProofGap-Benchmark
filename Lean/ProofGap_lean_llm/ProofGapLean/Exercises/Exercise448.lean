import ProofGapLean.Prelude.Analysis
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise448

noncomputable section

def cbrt (x : ℝ) : ℝ := Real.rpow x (1 / 3 : ℝ)
def original (x : ℝ) : ℝ :=
  (Real.sqrt (1 + x) - Real.sqrt (1 - x)) /
    (cbrt (1 + x) - cbrt (1 - x))
def cancelled (x : ℝ) : ℝ :=
  (cbrt ((1 + x) ^ 2) + cbrt (1 - x ^ 2) + cbrt ((1 - x) ^ 2)) /
    (Real.sqrt (1 + x) + Real.sqrt (1 - x))
def HasLimitAt (f : ℝ → ℝ) (a L : ℝ) : Prop :=
  Filter.Tendsto f (nhdsWithin a ({a} : Set ℝ)ᶜ) (nhds L)

/-- Source: `proof_gap/exercise_448/1.txt`. -/
private theorem original_eventuallyEq_cancelled :
    original =ᶠ[nhdsWithin 0 ({0} : Set ℝ)ᶜ] cancelled := by
  have hcub : ∀ {y : ℝ}, 0 ≤ y → cbrt y ^ 3 = y := by
    intro y hy
    rcases hy.eq_or_lt with rfl | hy
    · norm_num [cbrt]
    · have hr : Real.rpow y (1 / 3 : ℝ) =
          Real.exp (Real.log y * (1 / 3 : ℝ)) := by
        simpa only using
          (Real.rpow_def_of_pos hy (1 / 3 : ℝ))
      unfold cbrt
      calc
        Real.rpow y (1 / 3 : ℝ) ^ 3 =
            Real.exp (Real.log y * (1 / 3 : ℝ)) ^ 3 := by rw [hr]
        _ = Real.exp (Real.log y) := by
          rw [pow_three, ← Real.exp_add, ← Real.exp_add]
          congr 1
          ring
        _ = y := Real.exp_log hy
  have hmul : ∀ {a b : ℝ}, 0 ≤ a → 0 ≤ b →
      cbrt (a * b) = cbrt a * cbrt b := by
    intro a b ha hb
    unfold cbrt
    exact Real.mul_rpow ha hb
  filter_upwards [
    Filter.Eventually.filter_mono inf_le_left
      (Metric.ball_mem_nhds (0 : ℝ) zero_lt_one),
    self_mem_nhdsWithin
  ] with x hx hmem
  have hxabs : |x| < 1 := by
    simpa [Real.dist_eq] using hx
  have hxne : x ≠ 0 := by
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hmem
  have habs := abs_lt.mp hxabs
  have hp : 0 < 1 + x := by linarith [habs.1]
  have hm : 0 < 1 - x := by linarith [habs.2]
  have ha2 : Real.sqrt (1 + x) ^ 2 = 1 + x :=
    Real.sq_sqrt hp.le
  have hb2 : Real.sqrt (1 - x) ^ 2 = 1 - x :=
    Real.sq_sqrt hm.le
  have hpc : cbrt (1 + x) ^ 3 = 1 + x := hcub hp.le
  have hqc : cbrt (1 - x) ^ 3 = 1 - x := hcub hm.le
  have hroot : Real.sqrt (1 + x) + Real.sqrt (1 - x) ≠ 0 := by
    exact ne_of_gt (add_pos (Real.sqrt_pos.2 hp) (Real.sqrt_pos.2 hm))
  have hcube : cbrt (1 + x) - cbrt (1 - x) ≠ 0 := by
    intro hzero
    have heq : cbrt (1 + x) = cbrt (1 - x) := sub_eq_zero.mp hzero
    have hxzero : x = 0 := by
      rw [heq] at hpc
      nlinarith [hpc, hqc]
    exact hxne hxzero
  have hsqplus : cbrt ((1 + x) ^ 2) = cbrt (1 + x) ^ 2 := by
    calc
      cbrt ((1 + x) ^ 2) = cbrt ((1 + x) * (1 + x)) := by
        congr 1 <;> ring
      _ = cbrt (1 + x) * cbrt (1 + x) := hmul hp.le hp.le
      _ = cbrt (1 + x) ^ 2 := by ring
  have hsqminus : cbrt ((1 - x) ^ 2) = cbrt (1 - x) ^ 2 := by
    calc
      cbrt ((1 - x) ^ 2) = cbrt ((1 - x) * (1 - x)) := by
        congr 1 <;> ring
      _ = cbrt (1 - x) * cbrt (1 - x) := hmul hm.le hm.le
      _ = cbrt (1 - x) ^ 2 := by ring
  have hmiddle : cbrt (1 - x ^ 2) = cbrt (1 + x) * cbrt (1 - x) := by
    calc
      cbrt (1 - x ^ 2) = cbrt ((1 + x) * (1 - x)) := by
        congr 1 <;> ring
      _ = cbrt (1 + x) * cbrt (1 - x) := hmul hp.le hm.le
  unfold original cancelled
  rw [hsqplus, hmiddle, hsqminus]
  apply (div_eq_div_iff hcube hroot).2
  calc
    (Real.sqrt (1 + x) - Real.sqrt (1 - x)) *
        (Real.sqrt (1 + x) + Real.sqrt (1 - x)) = 2 * x := by
          nlinarith [ha2, hb2]
    _ = cbrt (1 + x) ^ 3 - cbrt (1 - x) ^ 3 := by
          rw [hpc, hqc]
          ring
    _ = (cbrt (1 + x) ^ 2 + cbrt (1 + x) * cbrt (1 - x) +
          cbrt (1 - x) ^ 2) *
          (cbrt (1 + x) - cbrt (1 - x)) := by ring

theorem gap1 : HasLimitAt original 0 (3 / 2) ↔
    HasLimitAt cancelled 0 (3 / 2) := by
  unfold HasLimitAt
  exact Filter.tendsto_congr' original_eventuallyEq_cancelled

/-- Source: `proof_gap/exercise_448/2.txt`. -/
theorem gap2 : HasLimitAt original 0 (3 / 2) ↔
    HasLimitAt cancelled 0 (3 / 2) := by
  exact gap1

/-- Source: `proof_gap/exercise_448/3.txt`. -/
theorem gap3 : HasLimitAt cancelled 0 (3 / 2) := by
  let smooth : ℝ → ℝ := fun x =>
    (Real.exp (Real.log ((1 + x) ^ 2) * (1 / 3 : ℝ)) +
        Real.exp (Real.log (1 - x ^ 2) * (1 / 3 : ℝ)) +
        Real.exp (Real.log ((1 - x) ^ 2) * (1 / 3 : ℝ))) /
      (Real.sqrt (1 + x) + Real.sqrt (1 - x))
  have heq : cancelled =ᶠ[nhds 0] smooth := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) zero_lt_one] with x hx
    have hxabs : |x| < 1 := by
      simpa [Real.dist_eq] using hx
    have habs := abs_lt.mp hxabs
    have hp : 0 < 1 + x := by linarith [habs.1]
    have hm : 0 < 1 - x := by linarith [habs.2]
    have hp2 : 0 < (1 + x) ^ 2 := pow_pos hp 2
    have hm2 : 0 < (1 - x) ^ 2 := pow_pos hm 2
    have hmid : 0 < 1 - x ^ 2 := by
      nlinarith [mul_pos hp hm]
    have hrplus : ((1 + x) ^ 2) ^ (1 / 3 : ℝ) =
        Real.exp (Real.log ((1 + x) ^ 2) * (1 / 3 : ℝ)) := by
      change Real.rpow ((1 + x) ^ 2) (1 / 3 : ℝ) = _
      simpa only using
        (Real.rpow_def_of_pos hp2 (1 / 3 : ℝ))
    have hrmid : (1 - x ^ 2) ^ (1 / 3 : ℝ) =
        Real.exp (Real.log (1 - x ^ 2) * (1 / 3 : ℝ)) := by
      change Real.rpow (1 - x ^ 2) (1 / 3 : ℝ) = _
      simpa only using
        (Real.rpow_def_of_pos hmid (1 / 3 : ℝ))
    have hrminus : ((1 - x) ^ 2) ^ (1 / 3 : ℝ) =
        Real.exp (Real.log ((1 - x) ^ 2) * (1 / 3 : ℝ)) := by
      change Real.rpow ((1 - x) ^ 2) (1 / 3 : ℝ) = _
      simpa only using
        (Real.rpow_def_of_pos hm2 (1 / 3 : ℝ))
    dsimp [smooth, cancelled, cbrt]
    rw [hrplus, hrmid, hrminus]
  have hs : ContinuousAt smooth 0 := by
    dsimp [smooth]
    fun_prop (disch := norm_num)
  have hv : smooth 0 = (3 / 2 : ℝ) := by
    norm_num [smooth]
  have heq' : cancelled =ᶠ[nhdsWithin 0 ({0} : Set ℝ)ᶜ] smooth :=
    Filter.Eventually.filter_mono inf_le_left heq
  unfold HasLimitAt
  rw [Filter.tendsto_congr' heq']
  rw [← hv]
  exact hs.tendsto.mono_left inf_le_left

/-- Source: `proof_gap/exercise_448/4.txt`. -/
theorem gap4 : HasLimitAt original 0 (3 / 2) := by
  exact gap1.mpr gap3

end

end ProofGap.Exercise448
