import ProofGapLean.Prelude.Elementary
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise167

noncomputable section

def lg (x : ℝ) : ℝ := Real.log x / Real.log 10
def domain : Set ℝ := {x | 0 < 1 - 2 * Real.cos x}
def y (x : ℝ) : ℝ := lg (1 - 2 * Real.cos x)
def innerValues : Set ℝ := {t | ∃ x ∈ domain, t = 1 - 2 * Real.cos x}
def valueSet : Set ℝ := {t | ∃ x ∈ domain, t = y x}

private lemma innerValues_eq_Ioc : innerValues = Set.Ioc 0 3 := by
  ext t
  constructor
  · rintro ⟨x, hxdom, rfl⟩
    have hcoslo := Real.neg_one_le_cos x
    exact ⟨hxdom, by linarith⟩
  · rintro ⟨ht0, ht3⟩
    let x := Real.arccos ((1 - t) / 2)
    have hlo : -1 ≤ (1 - t) / 2 := by linarith
    have hhi : (1 - t) / 2 ≤ 1 := by linarith
    have hcos : Real.cos x = (1 - t) / 2 := by
      exact Real.cos_arccos hlo hhi
    have hxdom : x ∈ domain := by
      change 0 < 1 - 2 * Real.cos x
      rw [hcos]
      linarith
    refine ⟨x, hxdom, ?_⟩
    rw [hcos]
    ring

/-- Source: `proof_gap/exercise_167/1.txt`. -/
theorem gap1 : ∀ x : ℝ, 0 < 1 - 2 * Real.cos x → x ∈ domain := by
  intro x hx
  exact hx

/-- Source: `proof_gap/exercise_167/2.txt`; name the set A explicitly. -/
theorem gap2 : domain = {x : ℝ | 0 < 1 - 2 * Real.cos x} := by
  rfl

/-- Source: `proof_gap/exercise_167/3.txt`; use supremum for the image set. -/
theorem gap3 : sSup innerValues = 3 := by
  rw [innerValues_eq_Ioc]
  exact csSup_Ioc (by norm_num)

/-- Source: `proof_gap/exercise_167/4.txt`; zero is the unattained infimum. -/
theorem gap4 : sInf innerValues = 0 := by
  rw [innerValues_eq_Ioc]
  exact csInf_Ioc (by norm_num)

/-- Source: `proof_gap/exercise_167/5.txt`; the lower endpoint is unbounded. -/
theorem gap5 : valueSet = Set.Iic (lg 3) := by
  ext t
  constructor
  · rintro ⟨x, hxdom, rfl⟩
    have hu0 : 0 < 1 - 2 * Real.cos x := hxdom
    have hu3 : 1 - 2 * Real.cos x ≤ 3 := by
      have hcoslo := Real.neg_one_le_cos x
      linarith
    unfold y lg
    have hlog := Real.log_le_log hu0 hu3
    have hlog10 : 0 < Real.log 10 := Real.log_pos (by norm_num)
    exact (div_le_div_iff_of_pos_right hlog10).2 hlog
  · intro ht
    let u : ℝ := Real.rpow 10 t
    have hu0 : 0 < u := Real.rpow_pos_of_pos (by norm_num) _
    have hpowlog : Real.rpow 10 (lg 3) = 3 := by
      simpa [lg, Real.logb] using
        (Real.rpow_logb (x := (3 : ℝ)) (by norm_num : (0 : ℝ) < 10)
          (by norm_num : (10 : ℝ) ≠ 1) (by norm_num : (0 : ℝ) < 3))
    have hu3 : u ≤ 3 := by
      rw [← hpowlog]
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num) ht
    have huinner : u ∈ innerValues := innerValues_eq_Ioc.symm ▸ ⟨hu0, hu3⟩
    rcases huinner with ⟨x, hxdom, hueq⟩
    refine ⟨x, hxdom, ?_⟩
    unfold y lg
    rw [← hueq]
    dsimp [u]
    rw [Real.log_rpow (by norm_num : (0 : ℝ) < 10)]
    have hlog10 : Real.log 10 ≠ 0 :=
      ne_of_gt (Real.log_pos (by norm_num))
    field_simp [hlog10]

end

end ProofGap.Exercise167
