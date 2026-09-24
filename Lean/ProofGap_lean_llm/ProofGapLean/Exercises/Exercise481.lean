import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise481

noncomputable section

def HasLimitAt (f : ℝ → ℝ) (a L : ℝ) : Prop :=
  Filter.Tendsto f (nhdsWithin a ({a} : Set ℝ)ᶜ) (nhds L)

/-- Exercise 481, gap 1. -/
theorem gap1 (x a : ℝ) :
    |Real.sin x - Real.sin a| =
      2 * |Real.sin ((x - a) / 2)| * |Real.cos ((x + a) / 2)| := by
  rw [Real.sin_sub_sin, abs_mul, abs_mul]
  norm_num

/-- Exercise 481, gap 2. -/
theorem gap2 (x a : ℝ) :
    2 * |Real.sin ((x - a) / 2)| * |Real.cos ((x + a) / 2)| ≤
      2 * |Real.sin ((x - a) / 2)| := by
  have hnonneg : 0 ≤ 2 * |Real.sin ((x - a) / 2)| := by positivity
  have h := mul_le_mul_of_nonneg_left
    (Real.abs_cos_le_one ((x + a) / 2)) hnonneg
  simpa [mul_assoc] using h

/-- Exercise 481, gap 3. -/
theorem gap3 (x a : ℝ) :
    2 * |Real.sin ((x - a) / 2)| ≤ |x - a| := by
  calc
    2 * |Real.sin ((x - a) / 2)| ≤ 2 * |(x - a) / 2| := by
      exact mul_le_mul_of_nonneg_left Real.abs_sin_le_abs (by norm_num)
    _ = |x - a| := by
      rw [abs_div]
      norm_num
      ring

/-- Exercise 481, gap 4. -/
theorem gap4 (x a : ℝ) : |Real.sin x - Real.sin a| ≤ |x - a| := by
  rw [gap1]
  exact (gap2 x a).trans (gap3 x a)

/-- Exercise 481, gap 5. -/
theorem gap5 (x a ε : ℝ) (hε : 0 < ε) (hxa : |x - a| < ε) :
    |Real.sin x - Real.sin a| < ε := by
  exact (gap4 x a).trans_lt hxa

/-- Exercise 481, gap 6. -/
theorem gap6 (x a ε : ℝ) (hε : 0 < ε) (hxa : |x - a| < ε) :
    |Real.sin x - Real.sin a| < ε := by
  exact gap5 x a ε hε hxa

/-- Exercise 481, gap 7; move `δ` after `ε` and before the varying point. -/
theorem gap7 (a ε : ℝ) (hε : 0 < ε) :
    ∃ δ > 0, ∀ x : ℝ, 0 < |x - a| → |x - a| < δ →
      |Real.sin x - Real.sin a| < ε := by
  refine ⟨ε, hε, ?_⟩
  intro x hxpos hx
  exact gap6 x a ε hε hx

/-- Exercise 481, gap 8. -/
theorem gap8 (a : ℝ) : HasLimitAt Real.sin a (Real.sin a) := by
  unfold HasLimitAt
  exact Real.continuous_sin.continuousAt.tendsto.mono_left inf_le_left

/-- Exercise 481, gap 9. -/
theorem gap9 (a : ℝ) : HasLimitAt Real.sin a (Real.sin a) := by
  exact gap8 a

/-- Exercise 481, gap 10. -/
theorem gap10 (a L : ℝ) :
    HasLimitAt Real.cos a L ↔
      HasLimitAt (fun x => Real.sin (Real.pi / 2 - x)) a L := by
  have hfun : Real.cos = fun x : ℝ => Real.sin (Real.pi / 2 - x) := by
    funext x
    exact (Real.sin_pi_div_two_sub x).symm
  rw [hfun]

/-- Exercise 481, gap 11. -/
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

/-- Exercise 481, gap 12. -/
theorem gap12 (a : ℝ) : Real.sin (Real.pi / 2 - a) = Real.cos a := by
  exact Real.sin_pi_div_two_sub a

/-- Exercise 481, gap 13. -/
theorem gap13 (a : ℝ) : HasLimitAt Real.cos a (Real.cos a) := by
  unfold HasLimitAt
  exact Real.continuous_cos.continuousAt.tendsto.mono_left inf_le_left

/-- Exercise 481, gap 14. -/
theorem gap14 (a : ℝ) : HasLimitAt Real.cos a (Real.cos a) := by
  exact gap13 a

/-- Exercise 481, gap 15. -/
theorem gap15 (a L : ℝ) :
    HasLimitAt Real.tan a L ↔
      HasLimitAt (fun x => Real.sin x / Real.cos x) a L := by
  have hfun : Real.tan = fun x : ℝ => Real.sin x / Real.cos x := by
    funext x
    exact Real.tan_eq_sin_div_cos x
  rw [hfun]

/-- Exercise 481, gap 16; require a nonzero limiting denominator. -/
theorem gap16 (a : ℝ) (ha : Real.cos a ≠ 0) :
    HasLimitAt (fun x => Real.sin x / Real.cos x) a
      (Real.sin a / Real.cos a) := by
  unfold HasLimitAt
  exact (gap8 a).div (gap13 a) ha

/-- Exercise 481, gap 17. -/
theorem gap17 (a : ℝ) :
    Real.sin a / Real.cos a = Real.sin a / Real.cos a := by
  rfl

/-- Exercise 481, gap 18. -/
theorem gap18 (a : ℝ) : Real.sin a / Real.cos a = Real.tan a := by
  exact (Real.tan_eq_sin_div_cos a).symm

/-- Exercise 481, gap 19; tangent is continuous only where `cos a≠0`. -/
theorem gap19 (a : ℝ) (ha : Real.cos a ≠ 0) :
    HasLimitAt Real.tan a (Real.tan a) := by
  apply (gap15 a (Real.tan a)).mpr
  rw [← gap18 a]
  exact gap16 a ha

/-- Exercise 481, gap 20; tangent is continuous only where `cos a≠0`. -/
theorem gap20 (a : ℝ) (ha : Real.cos a ≠ 0) :
    HasLimitAt Real.tan a (Real.tan a) := by
  exact gap19 a ha

/-- Exercise 481, gap 21; retain the tangent-domain condition. -/
theorem gap21 (a : ℝ) (ha : Real.cos a ≠ 0) :
    HasLimitAt Real.sin a (Real.sin a) ∧
      HasLimitAt Real.cos a (Real.cos a) ∧
      HasLimitAt Real.tan a (Real.tan a) := by
  exact ⟨gap8 a, gap13 a, gap19 a ha⟩

end

end ProofGap.Exercise481
