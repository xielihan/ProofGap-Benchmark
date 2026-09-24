import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise495

noncomputable section

def original (x : ℝ) : ℝ :=
  Real.sin (x - Real.pi / 3) / (1 - 2 * Real.cos x)
def shifted (y : ℝ) : ℝ :=
  Real.sin y / (1 - Real.cos y + Real.sqrt 3 * Real.sin y)
def normalized (y : ℝ) : ℝ :=
  (Real.sin y / y) /
    ((Real.sin (y / 2) / (y / 2)) * Real.sin (y / 2) +
      Real.sqrt 3 * (Real.sin y / y))
def HasLimitAt (f : ℝ → ℝ) (a L : ℝ) : Prop :=
  Filter.Tendsto f (nhdsWithin a ({a} : Set ℝ)ᶜ) (nhds L)

/-- Source: `proof_gap/exercise_495/1.txt`; bind `y=x-π/3`. -/
theorem gap1 (L : ℝ) :
    HasLimitAt original (Real.pi / 3) L ↔ HasLimitAt shifted 0 L := by
  have hfun (y : ℝ) :
      original (y + Real.pi / 3) = shifted y := by
    unfold original shifted
    rw [show y + Real.pi / 3 - Real.pi / 3 = y by ring]
    rw [Real.cos_add, Real.cos_pi_div_three, Real.sin_pi_div_three]
    congr 1 <;> ring
  have hfun' (x : ℝ) :
      shifted (x - Real.pi / 3) = original x := by
    simpa using (hfun (x - Real.pi / 3)).symm
  have h_add :
      Filter.Tendsto (fun y : ℝ => y + Real.pi / 3)
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ)
        (nhdsWithin (Real.pi / 3) ({Real.pi / 3} : Set ℝ)ᶜ) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · have hc : ContinuousAt (fun y : ℝ => y + Real.pi / 3) 0 :=
        continuousAt_id.add continuousAt_const
      simpa using
        (hc.tendsto.mono_left
          (show nhdsWithin 0 ({0} : Set ℝ)ᶜ ≤ nhds 0 from inf_le_left))
    · filter_upwards [self_mem_nhdsWithin] with y hy
      simpa using hy
  have h_sub :
      Filter.Tendsto (fun x : ℝ => x - Real.pi / 3)
        (nhdsWithin (Real.pi / 3) ({Real.pi / 3} : Set ℝ)ᶜ)
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · have hc : ContinuousAt (fun x : ℝ => x - Real.pi / 3) (Real.pi / 3) :=
        continuousAt_id.sub continuousAt_const
      simpa using
        (hc.tendsto.mono_left
          (show nhdsWithin (Real.pi / 3) ({Real.pi / 3} : Set ℝ)ᶜ ≤
              nhds (Real.pi / 3) from inf_le_left))
    · filter_upwards [self_mem_nhdsWithin] with x hx
      change x - Real.pi / 3 ≠ 0
      intro hzero
      have hx' : x ≠ Real.pi / 3 := by
        simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hx
      exact hx' (sub_eq_zero.mp hzero)
  unfold HasLimitAt
  constructor
  · intro h
    have hc :
        Filter.Tendsto (fun y : ℝ => original (y + Real.pi / 3))
          (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds L) := by
      simpa only [Function.comp_apply] using h.comp h_add
    exact hc.congr' (Filter.Eventually.of_forall hfun)
  · intro h
    have hc :
        Filter.Tendsto (fun x : ℝ => shifted (x - Real.pi / 3))
          (nhdsWithin (Real.pi / 3) ({Real.pi / 3} : Set ℝ)ᶜ) (nhds L) := by
      simpa only [Function.comp_apply] using h.comp h_sub
    exact hc.congr' (Filter.Eventually.of_forall hfun')

/-- Source: `proof_gap/exercise_495/2.txt`. -/
theorem gap2 (L : ℝ) :
    HasLimitAt shifted 0 L ↔ HasLimitAt normalized 0 L := by
  have heq (y : ℝ) (hy : y ≠ 0) : shifted y = normalized y := by
    unfold shifted normalized
    have htrig : 1 - Real.cos y = 2 * Real.sin (y / 2) ^ 2 := by
      have hs := Real.sin_sq_add_cos_sq (y / 2)
      have hc := Real.cos_two_mul (y / 2)
      rw [show 2 * (y / 2) = y by ring] at hc
      nlinarith
    have hden :
        (Real.sin (y / 2) / (y / 2)) * Real.sin (y / 2) +
            Real.sqrt 3 * (Real.sin y / y) =
          (1 - Real.cos y + Real.sqrt 3 * Real.sin y) / y := by
      rw [htrig]
      field_simp [hy]
    rw [hden]
    by_cases hd : 1 - Real.cos y + Real.sqrt 3 * Real.sin y = 0
    · simp [hd]
    · field_simp [hy, hd]
  unfold HasLimitAt
  constructor
  · intro h
    apply h.congr'
    filter_upwards [self_mem_nhdsWithin] with y hy
    have hy' : y ≠ 0 := by
      simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hy
    exact heq y hy'
  · intro h
    apply h.congr'
    filter_upwards [self_mem_nhdsWithin] with y hy
    have hy' : y ≠ 0 := by
      simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hy
    exact (heq y hy').symm

/-- Source: `proof_gap/exercise_495/3.txt`. -/
theorem gap3 : HasLimitAt normalized 0 (1 / Real.sqrt 3) := by
  have hsin :
      Filter.Tendsto (fun y : ℝ => Real.sin y / y)
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1) := by
    simpa [div_eq_mul_inv, mul_comm] using
      (Real.hasDerivAt_sin 0).tendsto_slope_zero
  have hhalf_full :
      Filter.Tendsto (fun y : ℝ => y / 2) (nhds 0) (nhds 0) := by
    have hc : ContinuousAt (fun y : ℝ => y / 2) 0 :=
      continuousAt_id.div_const 2
    simpa using hc.tendsto
  have hhalf_arg :
      Filter.Tendsto (fun y : ℝ => y / 2)
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ)
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · exact hhalf_full.mono_left inf_le_left
    · filter_upwards [self_mem_nhdsWithin] with y hy
      change y / 2 ≠ 0
      apply div_ne_zero
      · simpa using hy
      · norm_num
  have hhalf_ratio :
      Filter.Tendsto (fun y : ℝ => Real.sin (y / 2) / (y / 2))
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1) := by
    simpa only [Function.comp_apply] using hsin.comp hhalf_arg
  have hsin_half :
      Filter.Tendsto (fun y : ℝ => Real.sin (y / 2))
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 0) := by
    have hfull :
        Filter.Tendsto (fun y : ℝ => Real.sin (y / 2))
          (nhds 0) (nhds 0) := by
      simpa only [Function.comp_apply, Real.sin_zero] using
        Real.continuous_sin.continuousAt.tendsto.comp hhalf_full
    exact hfull.mono_left inf_le_left
  have hsqrt :
      Filter.Tendsto (fun _ : ℝ => Real.sqrt 3)
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds (Real.sqrt 3)) :=
    tendsto_const_nhds
  have hsqrt_ne : Real.sqrt 3 ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  have hden :
      Filter.Tendsto
        (fun y : ℝ =>
          (Real.sin (y / 2) / (y / 2)) * Real.sin (y / 2) +
            Real.sqrt 3 * (Real.sin y / y))
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds (Real.sqrt 3)) := by
    simpa using (hhalf_ratio.mul hsin_half).add (hsqrt.mul hsin)
  have hquot :
      Filter.Tendsto normalized
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds (1 / Real.sqrt 3)) := by
    simpa [normalized] using hsin.div hden hsqrt_ne
  exact hquot

/-- Source: `proof_gap/exercise_495/4.txt`. -/
theorem gap4 : HasLimitAt original (Real.pi / 3) (1 / Real.sqrt 3) := by
  exact (gap1 (1 / Real.sqrt 3)).2 ((gap2 (1 / Real.sqrt 3)).2 gap3)

end

end ProofGap.Exercise495
