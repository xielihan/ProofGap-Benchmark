import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Basic

namespace ProofGap.Exercise1251_1

noncomputable section

private theorem sin_secant_identity {a b : ℝ} (hab : a < b) :
    ∃ ξ ∈ Set.Icc a b,
      Real.sin a - Real.sin b = (a - b) * Real.cos ξ := by
  obtain ⟨ξ, hξ, hcos⟩ :=
    exists_hasDerivAt_eq_slope Real.sin Real.cos hab
      Real.continuous_sin.continuousOn
      (fun z _ => Real.hasDerivAt_sin z)
  have hbane : b - a ≠ 0 := sub_ne_zero.mpr (ne_of_gt hab)
  have hquot : (Real.sin b - Real.sin a) / (b - a) = Real.cos ξ := by
    simpa [slope] using hcos.symm
  have hsecant : Real.sin b - Real.sin a = Real.cos ξ * (b - a) :=
    (div_eq_iff hbane).mp hquot
  refine ⟨ξ, ⟨hξ.1.le, hξ.2.le⟩, ?_⟩
  calc
    Real.sin a - Real.sin b = -(Real.sin b - Real.sin a) := by ring
    _ = -(Real.cos ξ * (b - a)) := congrArg Neg.neg hsecant
    _ = (a - b) * Real.cos ξ := by ring

theorem gap1 (x y : ℝ) :
    ∃ ξ ∈ Set.Icc (min x y) (max x y),
      |Real.sin x - Real.sin y| = |(x - y) * Real.cos ξ| := by
  rcases lt_trichotomy x y with hxy | hxy | hyx
  · obtain ⟨ξ, hξ, heq⟩ := sin_secant_identity hxy
    refine ⟨ξ, ?_, congrArg abs heq⟩
    simpa [min_eq_left hxy.le, max_eq_right hxy.le] using hξ
  · subst y
    exact ⟨x, by simp, by simp⟩
  · obtain ⟨ξ, hξ, heq⟩ := sin_secant_identity hyx
    have heq' : Real.sin x - Real.sin y = (x - y) * Real.cos ξ := by
      calc
        Real.sin x - Real.sin y = -(Real.sin y - Real.sin x) := by ring
        _ = -((y - x) * Real.cos ξ) := congrArg Neg.neg heq
        _ = (x - y) * Real.cos ξ := by ring
    refine ⟨ξ, ?_, congrArg abs heq'⟩
    simpa [min_eq_right hyx.le, max_eq_left hyx.le] using hξ

theorem gap2 (x y : ℝ) :
    ∃ ξ ∈ Set.Icc (min x y) (max x y),
      |(x - y) * Real.cos ξ| ≤ |x - y| := by
  refine ⟨x, ⟨min_le_left x y, le_max_left x y⟩, ?_⟩
  rw [abs_mul]
  simpa only [mul_one] using
    mul_le_mul_of_nonneg_left (Real.abs_cos_le_one x) (abs_nonneg (x - y))

theorem gap3 (x y : ℝ) :
    |Real.sin x - Real.sin y| ≤ |x - y| := by
  obtain ⟨ξ, hξ, heq⟩ := gap1 x y
  rw [heq, abs_mul]
  simpa only [mul_one] using
    mul_le_mul_of_nonneg_left (Real.abs_cos_le_one ξ) (abs_nonneg (x - y))

end

end ProofGap.Exercise1251_1
