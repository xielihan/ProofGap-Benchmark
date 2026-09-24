import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise481

noncomputable section

def HasLimitAt (f : ℝ → ℝ) (a L : ℝ) : Prop :=
  Filter.Tendsto f (nhdsWithin a ({a} : Set ℝ)ᶜ) (nhds L)

/-- Source: `proof_gap/exercise_481/1.txt`. -/
theorem gap1 (x a : ℝ) :
    |Real.sin x - Real.sin a| =
      2 * |Real.sin ((x - a) / 2)| * |Real.cos ((x + a) / 2)| := by
  rw [Real.sin_sub_sin, abs_mul, abs_mul]
  norm_num

/-- Source: `proof_gap/exercise_481/2.txt`. -/
theorem gap2 (x a : ℝ) :
    2 * |Real.sin ((x - a) / 2)| * |Real.cos ((x + a) / 2)| ≤
      2 * |Real.sin ((x - a) / 2)| := by
  have hnonneg : 0 ≤ 2 * |Real.sin ((x - a) / 2)| := by positivity
  have h := mul_le_mul_of_nonneg_left
    (Real.abs_cos_le_one ((x + a) / 2)) hnonneg
  simpa [mul_assoc] using h

/-- Source: `proof_gap/exercise_481/3.txt`. -/
theorem gap3 (x a : ℝ) :
    2 * |Real.sin ((x - a) / 2)| ≤ |x - a| := by
  calc
    2 * |Real.sin ((x - a) / 2)| ≤ 2 * |(x - a) / 2| := by
      exact mul_le_mul_of_nonneg_left Real.abs_sin_le_abs (by norm_num)
    _ = |x - a| := by
      rw [abs_div]
      norm_num
      ring

/-- Source: `proof_gap/exercise_481/4.txt`. -/
theorem gap4 (x a : ℝ) : |Real.sin x - Real.sin a| ≤ |x - a| := by
  rw [gap1]
  exact (gap2 x a).trans (gap3 x a)

/-- Source: `proof_gap/exercise_481/5.txt`. -/
theorem gap5 (x a ε : ℝ) (hε : 0 < ε) (hxa : |x - a| < ε) :
    |Real.sin x - Real.sin a| < ε := by
  exact (gap4 x a).trans_lt hxa

/-- Source: `proof_gap/exercise_481/6.txt`. -/
theorem gap6 (x a ε : ℝ) (hε : 0 < ε) (hxa : |x - a| < ε) :
    |Real.sin x - Real.sin a| < ε := by
  exact gap5 x a ε hε hxa

/-- Source: `proof_gap/exercise_481/7.txt`; move `δ` after `ε` and before the varying point. -/
theorem gap7 (a ε : ℝ) (hε : 0 < ε) :
    ∃ δ > 0, ∀ x : ℝ, 0 < |x - a| → |x - a| < δ →
      |Real.sin x - Real.sin a| < ε := by
  refine ⟨ε, hε, ?_⟩
  intro x hxpos hx
  exact gap6 x a ε hε hx

/-- Source: `proof_gap/exercise_481/8.txt`. -/
theorem gap8 (a : ℝ) : HasLimitAt Real.sin a (Real.sin a) := by
  unfold HasLimitAt
  exact Real.continuous_sin.continuousAt.tendsto.mono_left inf_le_left

/-- Source: `proof_gap/exercise_481/9.txt`. -/
theorem gap9 (a : ℝ) : HasLimitAt Real.sin a (Real.sin a) := by
  exact gap8 a

/-- Source: `proof_gap/exercise_481/10.txt`. -/
theorem gap10 (a L : ℝ) :
    HasLimitAt Real.cos a L ↔
      HasLimitAt (fun x => Real.sin (Real.pi / 2 - x)) a L := by
  have hfun : Real.cos = fun x : ℝ => Real.sin (Real.pi / 2 - x) := by
    funext x
    exact (Real.sin_pi_div_two_sub x).symm
  rw [hfun]

/-- Source: `proof_gap/exercise_481/11.txt`. -/
theorem gap11 (a : ℝ) :
    HasLimitAt (fun x => Real.sin (Real.pi / 2 - x)) a
      (Real.sin (Real.pi / 2 - a)) := by
  unfold HasLimitAt
  have hinner : ContinuousAt (fun x : ℝ => Real.pi / 2 - x) a :=
    continuousAt_const.sub continuousAt_id
  have hcont :
      ContinuousAt (fun x : ℝ => Real.sin (Real.pi / 2 - x)) a :=
    Real.continuous_sin.continuousAt.comp hinner
  exact hcont.tendsto.mono_left inf_le_left

/-- Source: `proof_gap/exercise_481/12.txt`. -/
theorem gap12 (a : ℝ) : Real.sin (Real.pi / 2 - a) = Real.cos a := by
  exact Real.sin_pi_div_two_sub a

/-- Source: `proof_gap/exercise_481/13.txt`. -/
theorem gap13 (a : ℝ) : HasLimitAt Real.cos a (Real.cos a) := by
  unfold HasLimitAt
  exact Real.continuous_cos.continuousAt.tendsto.mono_left inf_le_left

/-- Source: `proof_gap/exercise_481/14.txt`. -/
theorem gap14 (a : ℝ) : HasLimitAt Real.cos a (Real.cos a) := by
  exact gap13 a

/-- Source: `proof_gap/exercise_481/15.txt`. -/
theorem gap15 (a L : ℝ) :
    HasLimitAt Real.tan a L ↔
      HasLimitAt (fun x => Real.sin x / Real.cos x) a L := by
  have hfun : Real.tan = fun x : ℝ => Real.sin x / Real.cos x := by
    funext x
    exact Real.tan_eq_sin_div_cos x
  rw [hfun]

/-- Source: `proof_gap/exercise_481/16.txt`; require a nonzero limiting denominator. -/
theorem gap16 (a : ℝ) (ha : Real.cos a ≠ 0) :
    HasLimitAt (fun x => Real.sin x / Real.cos x) a
      (Real.sin a / Real.cos a) := by
  unfold HasLimitAt
  exact (gap8 a).div (gap13 a) ha

/-- Source: `proof_gap/exercise_481/17.txt`. -/
theorem gap17 (a : ℝ) :
    Real.sin a / Real.cos a = Real.sin a / Real.cos a := by
  rfl

/-- Source: `proof_gap/exercise_481/18.txt`. -/
theorem gap18 (a : ℝ) : Real.sin a / Real.cos a = Real.tan a := by
  exact (Real.tan_eq_sin_div_cos a).symm

/-- Source: `proof_gap/exercise_481/19.txt`; tangent is continuous only where `cos a≠0`. -/
theorem gap19 (a : ℝ) (ha : Real.cos a ≠ 0) :
    HasLimitAt Real.tan a (Real.tan a) := by
  apply (gap15 a (Real.tan a)).mpr
  rw [← gap18 a]
  exact gap16 a ha

/-- Source: `proof_gap/exercise_481/20.txt`; tangent is continuous only where `cos a≠0`. -/
theorem gap20 (a : ℝ) (ha : Real.cos a ≠ 0) :
    HasLimitAt Real.tan a (Real.tan a) := by
  exact gap19 a ha

/-- Source: `proof_gap/exercise_481/21.txt`; retain the tangent-domain condition. -/
theorem gap21 (a : ℝ) (ha : Real.cos a ≠ 0) :
    HasLimitAt Real.sin a (Real.sin a) ∧
      HasLimitAt Real.cos a (Real.cos a) ∧
      HasLimitAt Real.tan a (Real.tan a) := by
  exact ⟨gap8 a, gap13 a, gap19 a ha⟩

end

end ProofGap.Exercise481
