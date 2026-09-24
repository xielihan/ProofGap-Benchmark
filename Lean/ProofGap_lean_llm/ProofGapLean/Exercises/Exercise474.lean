import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise474

noncomputable section

def original (x : ℝ) : ℝ := (1 - Real.cos x) / x ^ 2
def halfAngle (x : ℝ) : ℝ := 2 * Real.sin (x / 2) ^ 2 / x ^ 2
def normalized (x : ℝ) : ℝ :=
  (1 / 2 : ℝ) * (Real.sin (x / 2) / (x / 2)) ^ 2
def HasLimitAtZero (f : ℝ → ℝ) (L : ℝ) : Prop :=
  Filter.Tendsto f (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds L)

/-- Source: `proof_gap/exercise_474/1.txt`. -/
theorem gap1 (x : ℝ) : 1 - Real.cos x = 2 * Real.sin (x / 2) ^ 2 := by
  have hx : x / 2 + x / 2 = x := by ring
  calc
    1 - Real.cos x = 1 - Real.cos (x / 2 + x / 2) := by rw [hx]
    _ = 2 * Real.sin (x / 2) ^ 2 := by
      rw [Real.cos_add]
      nlinarith [Real.sin_sq_add_cos_sq (x / 2)]

/-- Source: `proof_gap/exercise_474/2.txt`. -/
theorem gap2 (L : ℝ) :
    HasLimitAtZero original L ↔ HasLimitAtZero halfAngle L := by
  have hfun : original = halfAngle := by
    funext x
    unfold original halfAngle
    rw [gap1]
  rw [hfun]

/-- Source: `proof_gap/exercise_474/3.txt`. -/
theorem gap3 (L : ℝ) :
    HasLimitAtZero halfAngle L ↔ HasLimitAtZero normalized L := by
  unfold HasLimitAtZero
  have heq :
      halfAngle =ᶠ[nhdsWithin 0 ({0} : Set ℝ)ᶜ] normalized := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hx0 : x ≠ 0 := by simpa using hx
    unfold halfAngle normalized
    field_simp [hx0]
  constructor
  · intro h
    exact h.congr' heq
  · intro h
    exact h.congr' heq.symm

/-- Source: `proof_gap/exercise_474/4.txt`. -/
theorem gap4 : HasLimitAtZero normalized (1 / 2) := by
  unfold HasLimitAtZero
  have hscale :
      Filter.Tendsto (fun x : ℝ => x / 2)
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ)
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · simpa using
        ((continuousAt_id.div_const (2 : ℝ)).mono_left
          (show nhdsWithin 0 ({0} : Set ℝ)ᶜ ≤ nhds 0 from inf_le_left))
    · filter_upwards [self_mem_nhdsWithin] with x hx
      have hx0 : x ≠ 0 := by simpa using hx
      have htwo : (2 : ℝ) ≠ 0 := by norm_num
      simpa using div_ne_zero hx0 htwo
  have hsin :
      Filter.Tendsto (fun y : ℝ => Real.sin y / y)
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1) := by
    have h := (Real.hasDerivAt_sin 0).tendsto_slope_zero
    simpa [div_eq_mul_inv, mul_comm] using h
  have hratio :
      Filter.Tendsto (fun x : ℝ => Real.sin (x / 2) / (x / 2))
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1) :=
    hsin.comp hscale
  have hhalf :
      Filter.Tendsto (fun _ : ℝ => (1 / 2 : ℝ))
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds (1 / 2 : ℝ)) :=
    tendsto_const_nhds
  change Filter.Tendsto
    (fun x : ℝ => (1 / 2 : ℝ) * (Real.sin (x / 2) / (x / 2)) ^ 2)
    (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds (1 / 2 : ℝ))
  simpa only [one_pow, mul_one] using hhalf.mul (hratio.pow 2)

/-- Source: `proof_gap/exercise_474/5.txt`. -/
theorem gap5 : HasLimitAtZero halfAngle (1 / 2) := by
  exact (gap3 (1 / 2)).mpr gap4

end

end ProofGap.Exercise474
