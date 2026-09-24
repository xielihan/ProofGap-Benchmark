import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Basic

namespace ProofGap.Exercise1251_3

noncomputable section

private theorem arctan_mean_value_of_lt (a b : ℝ) (hab : a < b) :
    ∃ ξ ∈ Set.Icc a b,
      |Real.arctan a - Real.arctan b| = |(a - b) / (1 + ξ ^ 2)| := by
  obtain ⟨ξ, hξ, hslope⟩ :=
    exists_hasDerivAt_eq_slope
      Real.arctan
      (fun x : ℝ => 1 / (1 + x ^ 2))
      hab
      Real.continuous_arctan.continuousOn
      (fun x _ => by simpa [one_div] using Real.hasDerivAt_arctan x)
  have hslope_eq :
      (Real.arctan b - Real.arctan a) / (b - a) =
        1 / (1 + ξ ^ 2) := hslope.symm
  have hba : b - a ≠ 0 := sub_ne_zero.mpr hab.ne'
  have hdiff :
      Real.arctan b - Real.arctan a =
        (1 / (1 + ξ ^ 2)) * (b - a) :=
    (div_eq_iff hba).mp hslope_eq
  refine ⟨ξ, ⟨hξ.1.le, hξ.2.le⟩, ?_⟩
  have hsigned :
      Real.arctan a - Real.arctan b = (a - b) / (1 + ξ ^ 2) := by
    calc
      Real.arctan a - Real.arctan b =
          -(Real.arctan b - Real.arctan a) := by ring
      _ = -((1 / (1 + ξ ^ 2)) * (b - a)) := by rw [hdiff]
      _ = (a - b) / (1 + ξ ^ 2) := by ring
  exact congrArg abs hsigned

private theorem abs_div_one_add_sq_le (x y : ℝ) :
    |x / (1 + y ^ 2)| ≤ |x| := by
  have hsq : 0 ≤ y ^ 2 := sq_nonneg y
  have hpos : 0 < 1 + y ^ 2 :=
    add_pos_of_pos_of_nonneg zero_lt_one hsq
  rw [abs_div, abs_of_pos hpos]
  exact div_le_self (abs_nonneg x) (le_add_of_nonneg_right hsq)

theorem gap1 (a b : ℝ) :
    ∃ ξ ∈ Set.Icc (min a b) (max a b),
      |Real.arctan a - Real.arctan b| = |(a - b) / (1 + ξ ^ 2)| := by
  rcases lt_trichotomy a b with hab | hab | hab
  · simpa [min_eq_left hab.le, max_eq_right hab.le] using
      arctan_mean_value_of_lt a b hab
  · subst b
    exact ⟨a, by simp, by simp⟩
  · obtain ⟨ξ, hξ, heq⟩ := arctan_mean_value_of_lt b a hab
    refine ⟨ξ, ?_, ?_⟩
    · simpa [min_eq_right hab.le, max_eq_left hab.le] using hξ
    · calc
        |Real.arctan a - Real.arctan b| =
            |Real.arctan b - Real.arctan a| := abs_sub_comm _ _
        _ = |(b - a) / (1 + ξ ^ 2)| := heq
        _ = |(a - b) / (1 + ξ ^ 2)| := by
          simp only [abs_div]
          rw [abs_sub_comm]

theorem gap2 (a b : ℝ) :
    ∃ ξ ∈ Set.Icc (min a b) (max a b),
      |(a - b) / (1 + ξ ^ 2)| ≤ |a - b| := by
  refine ⟨a, ⟨min_le_left _ _, le_max_left _ _⟩, ?_⟩
  exact abs_div_one_add_sq_le (a - b) a

theorem gap3 (a b : ℝ) :
    |Real.arctan a - Real.arctan b| ≤ |a - b| := by
  obtain ⟨ξ, hξ, heq⟩ := gap1 a b
  rw [heq]
  exact abs_div_one_add_sq_le (a - b) ξ

end

end ProofGap.Exercise1251_3
