import ProofGapLean.Prelude.Analysis
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise475

noncomputable section

def original (x : ℝ) : ℝ :=
  (Real.tan x - Real.sin x) / Real.sin x ^ 3
def tangentExpanded (x : ℝ) : ℝ :=
  (Real.sin x / Real.cos x - Real.sin x) / Real.sin x ^ 3
def reduced (x : ℝ) : ℝ :=
  (1 - Real.cos x) / (Real.cos x * Real.sin x ^ 2)
def halfAngle (x : ℝ) : ℝ :=
  (2 * Real.sin (x / 2) ^ 2) /
    (4 * Real.sin (x / 2) ^ 2 * Real.cos (x / 2) ^ 2 * Real.cos x)
def cancelled (x : ℝ) : ℝ :=
  1 / (2 * Real.cos (x / 2) ^ 2 * Real.cos x)
def HasLimitAtZero (f : ℝ → ℝ) (L : ℝ) : Prop :=
  Filter.Tendsto f (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds L)

/-- Source: `proof_gap/exercise_475/1.txt`. -/
private theorem eventually_sin_cos_ne_zero :
    ∀ᶠ x in nhdsWithin (0 : ℝ) ({0} : Set ℝ)ᶜ,
      Real.sin x ≠ 0 ∧ Real.cos x ≠ 0 := by
  have hpi_half_lt : Real.pi / 2 < Real.pi := by
    nlinarith [Real.pi_pos]
  have hI :
      Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) ∈ nhds (0 : ℝ) :=
    isOpen_Ioo.mem_nhds
      ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  have hI' :
      Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) ∈
        nhdsWithin (0 : ℝ) ({0} : Set ℝ)ᶜ :=
    mem_nhdsWithin_of_mem_nhds hI
  filter_upwards [hI', self_mem_nhdsWithin] with x hxI hx0
  have hxne : x ≠ 0 := by
    simpa using hx0
  constructor
  · rcases lt_trichotomy x 0 with hxneg | hxeq | hxpos
    · intro hs
      have hspos : 0 < Real.sin (-x) :=
        Real.sin_pos_of_pos_of_lt_pi
          (by linarith) (by nlinarith [hxI.1, hpi_half_lt])
      rw [Real.sin_neg, hs] at hspos
      norm_num at hspos
    · exact (hxne hxeq).elim
    · exact ne_of_gt
        (Real.sin_pos_of_pos_of_lt_pi hxpos
          (by nlinarith [hxI.2, hpi_half_lt]))
  · exact ne_of_gt (Real.cos_pos_of_mem_Ioo hxI)

theorem gap1 (L : ℝ) :
    HasLimitAtZero original L ↔ HasLimitAtZero tangentExpanded L := by
  unfold HasLimitAtZero
  have hEq :
      original =ᶠ[nhdsWithin (0 : ℝ) ({0} : Set ℝ)ᶜ] tangentExpanded :=
    Filter.Eventually.of_forall (fun x => by
      simp only [original, tangentExpanded, Real.tan_eq_sin_div_cos])
  constructor
  · intro h
    exact Filter.Tendsto.congr' hEq h
  · intro h
    exact Filter.Tendsto.congr' hEq.symm h

/-- Source: `proof_gap/exercise_475/2.txt`. -/
theorem gap2 (L : ℝ) :
    HasLimitAtZero tangentExpanded L ↔ HasLimitAtZero reduced L := by
  unfold HasLimitAtZero
  have hEq :
      tangentExpanded =ᶠ[nhdsWithin (0 : ℝ) ({0} : Set ℝ)ᶜ] reduced := by
    filter_upwards [eventually_sin_cos_ne_zero] with x hx
    rcases hx with ⟨hsin, hcos⟩
    unfold tangentExpanded reduced
    field_simp [hsin, hcos] <;> ring
  constructor
  · intro h
    exact Filter.Tendsto.congr' hEq h
  · intro h
    exact Filter.Tendsto.congr' hEq.symm h

/-- Source: `proof_gap/exercise_475/3.txt`. -/
theorem gap3 (L : ℝ) :
    HasLimitAtZero reduced L ↔ HasLimitAtZero halfAngle L := by
  unfold HasLimitAtZero
  have hEq :
      reduced =ᶠ[nhdsWithin (0 : ℝ) ({0} : Set ℝ)ᶜ] halfAngle := by
    apply Filter.Eventually.of_forall
    intro x
    have hx : 2 * (x / 2) = x := by ring
    have hsin :
        Real.sin x = 2 * Real.sin (x / 2) * Real.cos (x / 2) := by
      calc
        Real.sin x = Real.sin (2 * (x / 2)) := by rw [hx]
        _ = 2 * Real.sin (x / 2) * Real.cos (x / 2) :=
          Real.sin_two_mul (x / 2)
    have hcos :
        1 - Real.cos x = 2 * Real.sin (x / 2) ^ 2 := by
      calc
        1 - Real.cos x = 1 - Real.cos (2 * (x / 2)) := by rw [hx]
        _ = 2 * Real.sin (x / 2) ^ 2 := by
          rw [Real.cos_two_mul']
          nlinarith [Real.sin_sq_add_cos_sq (x / 2)]
    unfold reduced halfAngle
    rw [hcos, hsin]
    congr 1 <;> ring
  constructor
  · intro h
    exact Filter.Tendsto.congr' hEq h
  · intro h
    exact Filter.Tendsto.congr' hEq.symm h

/-- Source: `proof_gap/exercise_475/4.txt`. -/
theorem gap4 (L : ℝ) :
    HasLimitAtZero halfAngle L ↔ HasLimitAtZero cancelled L := by
  unfold HasLimitAtZero
  have hEq :
      halfAngle =ᶠ[nhdsWithin (0 : ℝ) ({0} : Set ℝ)ᶜ] cancelled := by
    filter_upwards [eventually_sin_cos_ne_zero] with x hx
    rcases hx with ⟨hsin, hcos⟩
    have hsin_two :
        Real.sin x = 2 * Real.sin (x / 2) * Real.cos (x / 2) := by
      have hxdouble : 2 * (x / 2) = x := by ring
      calc
        Real.sin x = Real.sin (2 * (x / 2)) := by rw [hxdouble]
        _ = 2 * Real.sin (x / 2) * Real.cos (x / 2) :=
          Real.sin_two_mul (x / 2)
    have hsin_half : Real.sin (x / 2) ≠ 0 := by
      intro h
      apply hsin
      rw [hsin_two, h]
      ring
    have hcos_half : Real.cos (x / 2) ≠ 0 := by
      intro h
      apply hsin
      rw [hsin_two, h]
      ring
    unfold halfAngle cancelled
    field_simp [hsin_half, hcos_half, hcos] <;> ring
  constructor
  · intro h
    exact Filter.Tendsto.congr' hEq h
  · intro h
    exact Filter.Tendsto.congr' hEq.symm h

/-- Source: `proof_gap/exercise_475/5.txt`. -/
theorem gap5 : HasLimitAtZero cancelled (1 / 2) := by
  unfold HasLimitAtZero
  have hhalf : ContinuousAt (fun x : ℝ => x / 2) 0 := by
    exact continuousAt_id.div continuousAt_const (by norm_num)
  have hcosHalf : ContinuousAt (fun x : ℝ => Real.cos (x / 2)) 0 :=
    Real.continuous_cos.continuousAt.comp hhalf
  have hcos : ContinuousAt (fun x : ℝ => Real.cos x) 0 :=
    Real.continuous_cos.continuousAt
  have htwo : ContinuousAt (fun _ : ℝ => (2 : ℝ)) 0 :=
    continuousAt_const
  have hden : ContinuousAt
      (fun x : ℝ => 2 * Real.cos (x / 2) ^ 2 * Real.cos x) 0 :=
    (htwo.mul (hcosHalf.pow 2)).mul hcos
  have hcancelled : ContinuousAt cancelled 0 := by
    unfold cancelled
    exact continuousAt_const.div hden (by norm_num)
  have hvalue : cancelled 0 = (1 / 2 : ℝ) := by
    norm_num [cancelled]
  rw [← hvalue]
  exact hcancelled.tendsto.mono_left inf_le_left

/-- Source: `proof_gap/exercise_475/6.txt`. -/
theorem gap6 : HasLimitAtZero original (1 / 2) := by
  exact (gap1 (1 / 2)).2
    ((gap2 (1 / 2)).2
      ((gap3 (1 / 2)).2
        ((gap4 (1 / 2)).2 gap5)))

end

end ProofGap.Exercise475
