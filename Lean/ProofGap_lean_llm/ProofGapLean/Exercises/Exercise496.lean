import ProofGapLean.Prelude.Analysis
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise496

noncomputable section

def original (x : ℝ) : ℝ :=
  (Real.tan x ^ 3 - 3 * Real.tan x) / Real.cos (x + Real.pi / 6)
def expanded (x : ℝ) : ℝ :=
  (Real.tan x * ((Real.sin x ^ 2 - 3 * Real.cos x ^ 2) / Real.cos x ^ 2)) /
    (Real.sqrt 3 / 2 * Real.cos x - 1 / 2 * Real.sin x)
def cancelled (x : ℝ) : ℝ :=
  (Real.tan x * (Real.sin x + Real.sqrt 3 * Real.cos x)) /
    (-(1 / 2 : ℝ) * Real.cos x ^ 2)
def HasLimitAt (f : ℝ → ℝ) (a L : ℝ) : Prop :=
  Filter.Tendsto f (nhdsWithin a ({a} : Set ℝ)ᶜ) (nhds L)

/-- Source: `proof_gap/exercise_496/1.txt`. -/
private theorem expanded_eventuallyEq_cancelled :
    expanded =ᶠ[nhdsWithin (Real.pi / 3)
      ({Real.pi / 3} : Set ℝ)ᶜ] cancelled := by
  have hI_nhds :
      Set.Ioo (0 : ℝ) (2 * Real.pi / 3) ∈ nhds (Real.pi / 3) := by
    apply isOpen_Ioo.mem_nhds
    constructor <;> nlinarith [Real.pi_pos]
  have hI :
      ∀ᶠ x in nhdsWithin (Real.pi / 3)
        ({Real.pi / 3} : Set ℝ)ᶜ,
        x ∈ Set.Ioo (0 : ℝ) (2 * Real.pi / 3) :=
    mem_nhdsWithin_of_mem_nhds hI_nhds
  filter_upwards [hI, self_mem_nhdsWithin] with x hxI hxcomp
  have hxa : x ≠ Real.pi / 3 := by
    simpa using hxcomp
  have hy : x + Real.pi / 6 ∈ Set.Icc (0 : ℝ) Real.pi := by
    constructor <;> nlinarith [hxI.1, hxI.2, Real.pi_pos]
  have hp : Real.pi / 2 ∈ Set.Icc (0 : ℝ) Real.pi := by
    constructor <;> nlinarith [Real.pi_pos]
  have hcosadd : Real.cos (x + Real.pi / 6) ≠ 0 := by
    intro hz
    have heq :
        Real.cos (x + Real.pi / 6) = Real.cos (Real.pi / 2) := by
      rw [Real.cos_pi_div_two]
      exact hz
    have harg : x + Real.pi / 6 = Real.pi / 2 :=
      Real.strictAntiOn_cos.injOn hy hp heq
    apply hxa
    nlinarith
  have hd :
      Real.sqrt 3 / 2 * Real.cos x - 1 / 2 * Real.sin x ≠ 0 := by
    intro hz
    apply hcosadd
    rw [Real.cos_add, Real.cos_pi_div_six, Real.sin_pi_div_six]
    simpa [mul_comm] using hz
  unfold expanded cancelled
  have hsqrt : Real.sqrt (3 : ℝ) ^ 2 = 3 :=
    Real.sq_sqrt (by norm_num)
  have hfactor :
      Real.sin x ^ 2 - 3 * Real.cos x ^ 2 =
        (Real.sin x - Real.sqrt 3 * Real.cos x) *
          (Real.sin x + Real.sqrt 3 * Real.cos x) := by
    calc
      Real.sin x ^ 2 - 3 * Real.cos x ^ 2 =
          Real.sin x ^ 2 - Real.sqrt 3 ^ 2 * Real.cos x ^ 2 := by
            rw [hsqrt]
      _ = (Real.sin x - Real.sqrt 3 * Real.cos x) *
            (Real.sin x + Real.sqrt 3 * Real.cos x) := by ring
  have hdeneq :
      Real.sqrt 3 / 2 * Real.cos x - 1 / 2 * Real.sin x =
        -(1 / 2 : ℝ) *
          (Real.sin x - Real.sqrt 3 * Real.cos x) := by
    ring
  have hf : Real.sin x - Real.sqrt 3 * Real.cos x ≠ 0 := by
    intro hf
    apply hd
    rw [hdeneq, hf]
    ring
  have hf' : Real.sin x - Real.cos x * Real.sqrt 3 ≠ 0 := by
    simpa [mul_comm] using hf
  rw [hfactor, hdeneq]
  by_cases hc : Real.cos x = 0
  · simp [hc]
  · field_simp [hc, hf, hf'] <;> ring_nf

theorem gap1 (L : ℝ) :
    HasLimitAt original (Real.pi / 3) L ↔ HasLimitAt expanded (Real.pi / 3) L := by
  have heq : original = expanded := by
    funext x
    have hnum :
        (Real.sin x / Real.cos x) ^ 3 - 3 * (Real.sin x / Real.cos x) =
          (Real.sin x / Real.cos x) *
            ((Real.sin x ^ 2 - 3 * Real.cos x ^ 2) / Real.cos x ^ 2) := by
      by_cases hc : Real.cos x = 0
      · simp [hc]
      · field_simp [hc]
        <;> ring
    unfold original expanded
    rw [Real.tan_eq_sin_div_cos, Real.cos_add,
      Real.cos_pi_div_six, Real.sin_pi_div_six]
    have hden :
        Real.cos x * (Real.sqrt 3 / 2) - Real.sin x * (1 / 2) =
          Real.sqrt 3 / 2 * Real.cos x - 1 / 2 * Real.sin x := by
      ring
    rw [hden]
    exact congrArg
      (fun z : ℝ =>
        z / (Real.sqrt 3 / 2 * Real.cos x - 1 / 2 * Real.sin x)) hnum
  rw [heq]

/-- Source: `proof_gap/exercise_496/2.txt`. -/
theorem gap2 (L : ℝ) :
    HasLimitAt expanded (Real.pi / 3) L ↔ HasLimitAt cancelled (Real.pi / 3) L := by
  unfold HasLimitAt Filter.Tendsto
  rw [Filter.map_congr expanded_eventuallyEq_cancelled]

/-- Source: `proof_gap/exercise_496/3.txt`. -/
theorem gap3 : HasLimitAt cancelled (Real.pi / 3) (-24) := by
  have hc : Real.cos (Real.pi / 3) ≠ 0 := by
    rw [Real.cos_pi_div_three]
    norm_num
  have hden :
      -(1 / 2 : ℝ) * Real.cos (Real.pi / 3) ^ 2 ≠ 0 := by
    rw [Real.cos_pi_div_three]
    norm_num
  have hs :
      ContinuousAt (fun x : ℝ => Real.sin x) (Real.pi / 3) :=
    Real.continuous_sin.continuousAt
  have hcos :
      ContinuousAt (fun x : ℝ => Real.cos x) (Real.pi / 3) :=
    Real.continuous_cos.continuousAt
  have ht :
      ContinuousAt (fun x : ℝ => Real.tan x) (Real.pi / 3) := by
    simpa only [Real.tan_eq_sin_div_cos] using hs.div hcos hc
  have hnum :
      ContinuousAt
        (fun x : ℝ =>
          Real.tan x * (Real.sin x + Real.sqrt 3 * Real.cos x))
        (Real.pi / 3) :=
    ht.mul (hs.add (continuousAt_const.mul hcos))
  have hdencont :
      ContinuousAt
        (fun x : ℝ => -(1 / 2 : ℝ) * Real.cos x ^ 2)
        (Real.pi / 3) :=
    continuousAt_const.mul (hcos.pow 2)
  have hcont : ContinuousAt cancelled (Real.pi / 3) := by
    unfold cancelled
    exact hnum.div hdencont hden
  have hval : cancelled (Real.pi / 3) = -24 := by
    have hsqrt : Real.sqrt (3 : ℝ) ^ 2 = 3 :=
      Real.sq_sqrt (by norm_num)
    unfold cancelled
    rw [Real.tan_eq_sin_div_cos, Real.sin_pi_div_three,
      Real.cos_pi_div_three]
    field_simp
    <;> nlinarith [hsqrt]
  unfold HasLimitAt
  rw [← hval]
  exact hcont.tendsto.mono_left inf_le_left

/-- Source: `proof_gap/exercise_496/4.txt`. -/
theorem gap4 : HasLimitAt original (Real.pi / 3) (-24) := by
  exact (gap1 (-24)).2 ((gap2 (-24)).2 gap3)

end

end ProofGap.Exercise496
