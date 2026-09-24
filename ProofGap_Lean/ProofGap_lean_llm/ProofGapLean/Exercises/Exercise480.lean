import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise480

noncomputable section

def original (x : ℝ) : ℝ := (1 - x) * Real.tan (Real.pi * x / 2)
def shifted (y : ℝ) : ℝ := y * (Real.cos (Real.pi * y / 2) / Real.sin (Real.pi * y / 2))
def normalized (y : ℝ) : ℝ :=
  ((Real.pi * y / 2) / Real.sin (Real.pi * y / 2)) *
    (2 / Real.pi) * Real.cos (Real.pi * y / 2)
def HasLimitAt (f : ℝ → ℝ) (a L : ℝ) : Prop :=
  Filter.Tendsto f (nhdsWithin a ({a} : Set ℝ)ᶜ) (nhds L)

/-- Exercise 480, gap 1; bind `y=1-x`. -/
private theorem tendsto_one_sub_punctured (a : ℝ) :
    Filter.Tendsto (fun x : ℝ => 1 - x)
      (nhdsWithin a (({a} : Set ℝ)ᶜ))
      (nhdsWithin (1 - a) (({1 - a} : Set ℝ)ᶜ)) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
  · exact ((continuous_const.sub continuous_id).tendsto a).mono_left inf_le_left
  · filter_upwards [self_mem_nhdsWithin] with x hx
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hx ⊢
    intro h
    apply hx
    linarith

private theorem tendsto_pi_scale_punctured :
    Filter.Tendsto (fun y : ℝ => Real.pi * y / 2)
      (nhdsWithin 0 (({0} : Set ℝ)ᶜ))
      (nhdsWithin 0 (({0} : Set ℝ)ᶜ)) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
  · simpa using
      (((continuous_const.mul continuous_id).div_const (2 : ℝ)).tendsto 0).mono_left
        inf_le_left
  · filter_upwards [self_mem_nhdsWithin] with y hy
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hy ⊢
    exact div_ne_zero (mul_ne_zero Real.pi_ne_zero hy) (by norm_num)

private theorem original_eq_shifted_one_sub (x : ℝ) :
    original x = shifted (1 - x) := by
  unfold original shifted
  rw [Real.tan_eq_sin_div_cos]
  have harg : Real.pi * (1 - x) / 2 = Real.pi / 2 - Real.pi * x / 2 := by
    ring
  rw [harg, Real.cos_pi_div_two_sub, Real.sin_pi_div_two_sub]

private theorem shifted_eq_normalized (y : ℝ) : shifted y = normalized y := by
  have hpi : (Real.pi / 2) * (2 / Real.pi) = 1 := by
    calc
      (Real.pi / 2) * (2 / Real.pi) = Real.pi / Real.pi := by ring
      _ = 1 := div_self Real.pi_ne_zero
  unfold shifted normalized
  calc
    y * (Real.cos (Real.pi * y / 2) / Real.sin (Real.pi * y / 2)) =
        ((Real.pi / 2) * (2 / Real.pi)) *
          (y * (Real.cos (Real.pi * y / 2) / Real.sin (Real.pi * y / 2))) := by
            simp [hpi]
    _ = ((Real.pi * y / 2) / Real.sin (Real.pi * y / 2)) *
          (2 / Real.pi) * Real.cos (Real.pi * y / 2) := by
            ring

theorem gap1 (L : ℝ) :
    HasLimitAt original 1 L ↔ HasLimitAt shifted 0 L := by
  unfold HasLimitAt
  have h01 :
      Filter.Tendsto (fun x : ℝ => 1 - x)
        (nhdsWithin 0 (({0} : Set ℝ)ᶜ))
        (nhdsWithin 1 (({1} : Set ℝ)ᶜ)) := by
    simpa using (tendsto_one_sub_punctured (0 : ℝ))
  have h10 :
      Filter.Tendsto (fun x : ℝ => 1 - x)
        (nhdsWithin 1 (({1} : Set ℝ)ᶜ))
        (nhdsWithin 0 (({0} : Set ℝ)ᶜ)) := by
    simpa using (tendsto_one_sub_punctured (1 : ℝ))
  constructor
  · intro h
    have hfun : shifted = fun y => original (1 - y) := by
      funext y
      rw [original_eq_shifted_one_sub]
      apply congrArg shifted
      ring
    rw [hfun]
    exact h.comp h01
  · intro h
    have hfun : original = fun x => shifted (1 - x) :=
      funext original_eq_shifted_one_sub
    rw [hfun]
    exact h.comp h10

/-- Exercise 480, gap 2. -/
theorem gap2 (L : ℝ) :
    HasLimitAt shifted 0 L ↔ HasLimitAt normalized 0 L := by
  unfold HasLimitAt
  have hfun : shifted = normalized := funext shifted_eq_normalized
  rw [hfun]

/-- Exercise 480, gap 3. -/
theorem gap3 : HasLimitAt normalized 0 (2 / Real.pi) := by
  unfold HasLimitAt
  have hscale := tendsto_pi_scale_punctured
  have hto0 :
      Filter.Tendsto (fun y : ℝ => Real.pi * y / 2)
        (nhdsWithin 0 (({0} : Set ℝ)ᶜ)) (nhds 0) :=
    hscale.mono_right inf_le_left
  have hsin_base :
      Filter.Tendsto (fun x : ℝ => x⁻¹ * Real.sin x)
        (nhdsWithin 0 (({0} : Set ℝ)ᶜ)) (nhds 1) := by
    have hderiv := (Real.hasDerivAt_sin (0 : ℝ)).tendsto_slope
    change Filter.Tendsto
      (fun x : ℝ => (x - 0)⁻¹ • (Real.sin x - Real.sin 0))
      (nhdsWithin 0 (({0} : Set ℝ)ᶜ)) (nhds (Real.cos 0)) at hderiv
    simpa only [sub_zero, Real.sin_zero, Real.cos_zero, smul_eq_mul] using hderiv
  have hsin :
      Filter.Tendsto
        (fun y : ℝ =>
          Real.sin (Real.pi * y / 2) / (Real.pi * y / 2))
        (nhdsWithin 0 (({0} : Set ℝ)ᶜ)) (nhds 1) := by
    simpa only [div_eq_mul_inv, mul_comm] using hsin_base.comp hscale
  have hratio :
      Filter.Tendsto
        (fun y : ℝ =>
          (Real.pi * y / 2) / Real.sin (Real.pi * y / 2))
        (nhdsWithin 0 (({0} : Set ℝ)ᶜ)) (nhds 1) := by
    simpa only [inv_div, inv_one] using hsin.inv₀ (by norm_num)
  have hcos :
      Filter.Tendsto (fun y : ℝ => Real.cos (Real.pi * y / 2))
        (nhdsWithin 0 (({0} : Set ℝ)ᶜ)) (nhds 1) := by
    simpa using (Real.continuous_cos.tendsto 0).comp hto0
  have hconst :
      Filter.Tendsto (fun _ : ℝ => 2 / Real.pi)
        (nhdsWithin 0 (({0} : Set ℝ)ᶜ)) (nhds (2 / Real.pi)) :=
    tendsto_const_nhds
  simpa [normalized] using ((hratio.mul hconst).mul hcos)

/-- Exercise 480, gap 4. -/
theorem gap4 : HasLimitAt original 1 (2 / Real.pi) := by
  exact (gap1 (2 / Real.pi)).2 ((gap2 (2 / Real.pi)).2 gap3)

end

end ProofGap.Exercise480
