import ProofGapLean.Prelude.Analysis
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise439

noncomputable section

def original (a x : ℝ) : ℝ :=
  (Real.sqrt x - Real.sqrt a + Real.sqrt (x - a)) /
    Real.sqrt (x ^ 2 - a ^ 2)
def rationalized (a x : ℝ) : ℝ :=
  (Real.sqrt (x - a) * (Real.sqrt (x - a) + Real.sqrt x + Real.sqrt a)) /
    (Real.sqrt (x - a) * Real.sqrt (x + a) * (Real.sqrt x + Real.sqrt a))
def cancelled (a x : ℝ) : ℝ :=
  (Real.sqrt (x - a) + Real.sqrt x + Real.sqrt a) /
    (Real.sqrt (x + a) * (Real.sqrt x + Real.sqrt a))
def HasRightLimitAt (f : ℝ → ℝ) (a L : ℝ) : Prop :=
  Filter.Tendsto f (nhdsWithin a (Set.Ioi a)) (nhds L)

/-- Source: `proof_gap/exercise_439/1.txt`; the square-root domain makes this a right-hand limit. -/
private theorem equivalent_forms_of_lt (a x : ℝ) (ha : 0 < a) (hx : a < x) :
    original a x = rationalized a x ∧
      rationalized a x = cancelled a x := by
  have hxm : 0 < x - a := sub_pos.mpr hx
  have hxpos : 0 < x := lt_trans ha hx
  have hxp : 0 < x + a := add_pos hxpos ha
  have hsd : Real.sqrt (x - a) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hxm)
  have hsp : Real.sqrt (x + a) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hxp)
  have hsum : Real.sqrt x + Real.sqrt a ≠ 0 := by
    positivity
  have hsx_sq : (Real.sqrt x) ^ 2 = x :=
    Real.sq_sqrt (le_of_lt hxpos)
  have hsa_sq : (Real.sqrt a) ^ 2 = a :=
    Real.sq_sqrt (le_of_lt ha)
  have hsd_sq : (Real.sqrt (x - a)) ^ 2 = x - a :=
    Real.sq_sqrt (le_of_lt hxm)
  have hsqrt_factor :
      Real.sqrt (x ^ 2 - a ^ 2) =
        Real.sqrt (x - a) * Real.sqrt (x + a) := by
    rw [show x ^ 2 - a ^ 2 = (x - a) * (x + a) by ring]
    rw [Real.sqrt_mul (le_of_lt hxm)]
  have hnum :
      (Real.sqrt x - Real.sqrt a + Real.sqrt (x - a)) *
          (Real.sqrt x + Real.sqrt a) =
        Real.sqrt (x - a) *
          (Real.sqrt (x - a) + Real.sqrt x + Real.sqrt a) := by
    nlinarith [hsx_sq, hsa_sq, hsd_sq]
  constructor
  · unfold original rationalized
    rw [hsqrt_factor, ← hnum]
    field_simp [hsd, hsp, hsum]
  · unfold rationalized cancelled
    field_simp [hsd, hsp, hsum]

theorem gap1 (a : ℝ) (ha : 0 < a) :
    HasRightLimitAt (original a) a (1 / Real.sqrt (2 * a)) ↔
      HasRightLimitAt (rationalized a) a (1 / Real.sqrt (2 * a)) := by
  unfold HasRightLimitAt
  have hEq :
      original a =ᶠ[nhdsWithin a (Set.Ioi a)] rationalized a := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact (equivalent_forms_of_lt a x ha hx).1
  exact Filter.tendsto_congr' hEq

/-- Source: `proof_gap/exercise_439/2.txt`; use the right-hand domain. -/
theorem gap2 (a : ℝ) (ha : 0 < a) :
    HasRightLimitAt (original a) a (1 / Real.sqrt (2 * a)) ↔
      HasRightLimitAt (rationalized a) a (1 / Real.sqrt (2 * a)) := by
  exact gap1 a ha

/-- Source: `proof_gap/exercise_439/3.txt`; use the right-hand domain. -/
theorem gap3 (a : ℝ) (ha : 0 < a) :
    HasRightLimitAt (rationalized a) a (1 / Real.sqrt (2 * a)) ↔
      HasRightLimitAt (cancelled a) a (1 / Real.sqrt (2 * a)) := by
  unfold HasRightLimitAt
  have hEq :
      rationalized a =ᶠ[nhdsWithin a (Set.Ioi a)] cancelled a := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact (equivalent_forms_of_lt a x ha hx).2
  exact Filter.tendsto_congr' hEq

/-- Source: `proof_gap/exercise_439/4.txt`; use the right-hand domain. -/
theorem gap4 (a : ℝ) (ha : 0 < a) :
    HasRightLimitAt (cancelled a) a (1 / Real.sqrt (2 * a)) := by
  have hsqrt_sub :
      ContinuousAt (fun x : ℝ => Real.sqrt (x - a)) a :=
    (Real.continuous_sqrt.comp (continuous_id.sub continuous_const)).continuousAt
  have hsqrt_id :
      ContinuousAt (fun x : ℝ => Real.sqrt x) a :=
    Real.continuous_sqrt.continuousAt
  have hsqrt_add :
      ContinuousAt (fun x : ℝ => Real.sqrt (x + a)) a :=
    (Real.continuous_sqrt.comp (continuous_id.add continuous_const)).continuousAt
  have hnum :
      ContinuousAt
        (fun x : ℝ => Real.sqrt (x - a) + Real.sqrt x + Real.sqrt a) a :=
    (hsqrt_sub.add hsqrt_id).add continuousAt_const
  have hden :
      ContinuousAt
        (fun x : ℝ => Real.sqrt (x + a) * (Real.sqrt x + Real.sqrt a)) a :=
    hsqrt_add.mul (hsqrt_id.add continuousAt_const)
  have hcont : ContinuousAt (cancelled a) a := by
    unfold cancelled
    exact hnum.div hden (by
      dsimp
      positivity)
  have hvalue : cancelled a a = 1 / Real.sqrt (2 * a) := by
    unfold cancelled
    rw [sub_self, Real.sqrt_zero]
    rw [show a + a = 2 * a by ring]
    have hroot_two_a : Real.sqrt (2 * a) ≠ 0 := by
      positivity
    have hsuma : Real.sqrt a + Real.sqrt a ≠ 0 := by
      positivity
    field_simp [hroot_two_a, hsuma] <;> ring
  unfold HasRightLimitAt
  have ht :
      Filter.Tendsto (cancelled a) (nhdsWithin a (Set.Ioi a))
        (nhds (cancelled a a)) :=
    hcont.continuousWithinAt
  simpa only [hvalue] using ht

/-- Source: `proof_gap/exercise_439/5.txt`; use the right-hand domain. -/
theorem gap5 (a : ℝ) (ha : 0 < a) :
    HasRightLimitAt (original a) a (1 / Real.sqrt (2 * a)) := by
  exact (gap1 a ha).2 ((gap3 a ha).2 (gap4 a ha))

end

end ProofGap.Exercise439
