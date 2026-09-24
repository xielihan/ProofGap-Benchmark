import ProofGapLean.Prelude.Analysis
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

open Filter Topology

namespace ProofGap.Exercise179

noncomputable section

def lg (x : ℝ) : ℝ := Real.log x / Real.log 10
def domain : Set ℝ := Set.Ioo 10 1000
def valueSet : Set ℝ := {t | ∃ x ∈ domain, t = lg x}

/-- Source: `proof_gap/exercise_179/1.txt`. -/
theorem gap1 : ContinuousOn lg domain := by
  intro x hx
  unfold lg
  apply ContinuousAt.continuousWithinAt
  exact (Real.continuousAt_log (by linarith [hx.1])).div_const _

/-- Source: `proof_gap/exercise_179/2.txt`. -/
theorem gap2 : StrictMonoOn lg domain := by
  intro a ha b hb hab
  unfold lg
  have hlog10 : 0 < Real.log 10 := Real.log_pos (by norm_num)
  apply (div_lt_div_iff_of_pos_right hlog10).2
  exact Real.log_lt_log (by linarith [ha.1]) hab

/-- Source: `proof_gap/exercise_179/3.txt`. -/
theorem gap3 : Tendsto lg (𝓝[Set.Ioi 10] 10) (𝓝 (lg 10)) := by
  unfold lg
  apply ContinuousAt.continuousWithinAt
  exact (Real.continuousAt_log (by norm_num)).div_const _

/-- Source: `proof_gap/exercise_179/4.txt`. -/
theorem gap4 : lg 10 = 1 := by
  unfold lg
  have hlog10 : Real.log 10 ≠ 0 :=
    ne_of_gt (Real.log_pos (by norm_num))
  field_simp [hlog10]

/-- Source: `proof_gap/exercise_179/5.txt`. -/
theorem gap5 : Tendsto lg (𝓝[Set.Ioi 10] 10) (𝓝 1) := by
  simpa [gap4] using gap3

/-- Source: `proof_gap/exercise_179/6.txt`. -/
theorem gap6 : Tendsto lg (𝓝[Set.Iio 1000] 1000) (𝓝 (lg 1000)) := by
  unfold lg
  apply ContinuousAt.continuousWithinAt
  exact (Real.continuousAt_log (by norm_num)).div_const _

/-- Source: `proof_gap/exercise_179/7.txt`. -/
theorem gap7 : lg 1000 = 3 := by
  unfold lg
  rw [show (1000 : ℝ) = 10 ^ 3 by norm_num, Real.log_pow]
  have hlog10 : Real.log 10 ≠ 0 :=
    ne_of_gt (Real.log_pos (by norm_num))
  field_simp [hlog10]
  norm_num

/-- Source: `proof_gap/exercise_179/8.txt`. -/
theorem gap8 : Tendsto lg (𝓝[Set.Iio 1000] 1000) (𝓝 3) := by
  simpa [gap7] using gap6

/-- Source: `proof_gap/exercise_179/9.txt`; replace the free family `E_x`. -/
theorem gap9 : valueSet = Set.Ioo 1 3 := by
  ext t
  constructor
  · rintro ⟨x, ⟨hxlo, hxhi⟩, rfl⟩
    have hlog10 : 0 < Real.log 10 := Real.log_pos (by norm_num)
    have hlo : lg 10 < lg x := by
      unfold lg
      exact (div_lt_div_iff_of_pos_right hlog10).2
        (Real.log_lt_log (by norm_num) hxlo)
    have hhi : lg x < lg 1000 := by
      unfold lg
      exact (div_lt_div_iff_of_pos_right hlog10).2
        (Real.log_lt_log (by linarith) hxhi)
    simpa [gap4, gap7] using And.intro hlo hhi
  · rintro ⟨htlo, hthi⟩
    let x : ℝ := Real.rpow 10 t
    have hxlo : 10 < x := by
      dsimp [x]
      convert Real.rpow_lt_rpow_of_exponent_lt (show (1 : ℝ) < 10 by norm_num) htlo
        using 1 <;> norm_num
    have hxhi : x < 1000 := by
      dsimp [x]
      convert Real.rpow_lt_rpow_of_exponent_lt (show (1 : ℝ) < 10 by norm_num) hthi
        using 1 <;> norm_num
    refine ⟨x, ⟨hxlo, hxhi⟩, ?_⟩
    unfold lg
    dsimp [x]
    change t = Real.log ((10 : ℝ) ^ t) / Real.log 10
    rw [Real.log_rpow (by norm_num : (0 : ℝ) < 10)]
    have hlog10 : Real.log 10 ≠ 0 :=
      ne_of_gt (Real.log_pos (by norm_num))
    field_simp [hlog10]

end

end ProofGap.Exercise179
