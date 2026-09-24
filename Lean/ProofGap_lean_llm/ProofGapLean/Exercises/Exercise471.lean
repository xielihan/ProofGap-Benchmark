import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise471

noncomputable section

def original (x : ℝ) : ℝ := Real.sin (5 * x) / x
def normalized (x : ℝ) : ℝ := Real.sin (5 * x) / (5 * x)
def HasLimitAtZero (f : ℝ → ℝ) (L : ℝ) : Prop :=
  Filter.Tendsto f (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds L)

/-- Source: `proof_gap/exercise_471/1.txt`. -/
theorem gap1 (L : ℝ) :
    HasLimitAtZero original L ↔
      HasLimitAtZero (fun x => 5 * normalized x) L := by
  unfold HasLimitAtZero
  have hEq :
      Filter.EventuallyEq (nhdsWithin 0 ({0} : Set ℝ)ᶜ)
        original (fun x => 5 * normalized x) := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hx0 : x ≠ 0 := by
      simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hx
    change Real.sin (5 * x) / x =
      5 * (Real.sin (5 * x) / (5 * x))
    field_simp [hx0] <;> ring_nf
  constructor
  · exact Filter.Tendsto.congr' hEq
  · exact Filter.Tendsto.congr' hEq.symm

/-- Source: `proof_gap/exercise_471/2.txt`. -/
theorem gap2 : HasLimitAtZero (fun x => 5 * normalized x) (5 * 1) := by
  have hscale :
      Filter.Tendsto (fun x : ℝ => 5 * x)
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ)
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have hcontinuous :
          ContinuousAt ((fun _ : ℝ => (5 : ℝ)) * fun x : ℝ => x) 0 :=
        continuousAt_const.mul continuousAt_id
      change Filter.Tendsto (fun x : ℝ => 5 * x)
        (nhds 0) (nhds (5 * 0)) at hcontinuous
      have hfull :
          Filter.Tendsto (fun x : ℝ => 5 * x) (nhds 0) (nhds 0) := by
        simpa only [mul_zero] using hcontinuous
      exact hfull.mono_left inf_le_left
    · filter_upwards [self_mem_nhdsWithin] with x hx
      simpa only [Set.mem_compl_iff, Set.mem_singleton_iff, mul_eq_zero,
        OfNat.ofNat_ne_zero, false_or] using hx
  have hsin :
      Filter.Tendsto (fun y : ℝ => Real.sin y / y)
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1) := by
    simpa [div_eq_mul_inv, mul_comm] using
      (Real.hasDerivAt_sin 0).tendsto_slope_zero
  have hnorm : HasLimitAtZero normalized 1 := by
    unfold HasLimitAtZero normalized
    simpa [Function.comp_def] using hsin.comp hscale
  unfold HasLimitAtZero at hnorm ⊢
  have hconst :
      Filter.Tendsto (fun _ : ℝ => (5 : ℝ))
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 5) :=
    tendsto_const_nhds
  simpa using hconst.mul hnorm

/-- Source: `proof_gap/exercise_471/3.txt`. -/
theorem gap3 : (5 : ℝ) * 1 = 5 := by
  simp

/-- Source: `proof_gap/exercise_471/4.txt`. -/
theorem gap4 : HasLimitAtZero (fun x => 5 * normalized x) 5 := by
  simpa using gap2

end

end ProofGap.Exercise471
