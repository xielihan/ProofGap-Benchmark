import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Basic

namespace ProofGap.Exercise1251_4

noncomputable section

theorem gap1 (a b : ℝ) (hb : 0 < b) (hba : b < a) :
    ∃ ξ ∈ Set.Ioo b a, Real.log a - Real.log b = (a - b) / ξ := by
  have hcont : ContinuousOn Real.log (Set.Icc b a) := by
    intro x hx
    exact
      (Real.continuousAt_log
        (ne_of_gt (lt_of_lt_of_le hb hx.1))).continuousWithinAt
  have hderiv :
      ∀ x ∈ Set.Ioo b a, HasDerivAt Real.log x⁻¹ x := by
    intro x hx
    exact Real.hasDerivAt_log (ne_of_gt (lt_trans hb hx.1))
  obtain ⟨ξ, hξ, heq⟩ :=
    exists_hasDerivAt_eq_slope Real.log (fun x : ℝ => x⁻¹)
      hba hcont hderiv
  have habne : a - b ≠ 0 := sub_ne_zero.mpr (ne_of_gt hba)
  refine ⟨ξ, hξ, ?_⟩
  calc
    Real.log a - Real.log b =
        (a - b) * ((Real.log a - Real.log b) / (a - b)) := by
          field_simp [habne] <;> ring
    _ = (a - b) * ξ⁻¹ := by rw [← heq]
    _ = (a - b) / ξ := by simp only [div_eq_mul_inv]

theorem gap2 (a b : ℝ) (hb : 0 < b) (hba : b < a) :
    0 < b := by
  exact hb

theorem gap3 (a b : ℝ) (hb : 0 < b) (hba : b < a) :
    ∃ ξ, b < ξ := by
  exact ⟨a, hba⟩

theorem gap4 (a b : ℝ) (hb : 0 < b) (hba : b < a) :
    ∃ ξ, ξ < a := by
  exact ⟨b, hba⟩

theorem gap5 (a b : ℝ) (hb : 0 < b) (hba : b < a) :
    0 < a := by
  exact lt_trans hb hba

theorem gap6 (a b : ℝ) (hb : 0 < b) (hba : b < a) :
    (a - b) / a < Real.log (a / b) := by
  have ha : 0 < a := lt_trans hb hba
  obtain ⟨ξ, hξ, hlog⟩ := gap1 a b hb hba
  have hξpos : 0 < ξ := lt_trans hb hξ.1
  have hfrac : (a - b) / a < (a - b) / ξ := by
    apply (div_lt_div_iff₀ ha hξpos).2
    exact mul_lt_mul_of_pos_left hξ.2 (sub_pos.mpr hba)
  calc
    (a - b) / a < (a - b) / ξ := hfrac
    _ = Real.log a - Real.log b := hlog.symm
    _ = Real.log (a / b) := by
      rw [Real.log_div (ne_of_gt ha) (ne_of_gt hb)]

theorem gap7 (a b : ℝ) (hb : 0 < b) (hba : b < a) :
    Real.log (a / b) < (a - b) / b := by
  have ha : 0 < a := lt_trans hb hba
  obtain ⟨ξ, hξ, hlog⟩ := gap1 a b hb hba
  have hξpos : 0 < ξ := lt_trans hb hξ.1
  have hfrac : (a - b) / ξ < (a - b) / b := by
    apply (div_lt_div_iff₀ hξpos hb).2
    exact mul_lt_mul_of_pos_left hξ.1 (sub_pos.mpr hba)
  calc
    Real.log (a / b) = Real.log a - Real.log b := by
      rw [Real.log_div (ne_of_gt ha) (ne_of_gt hb)]
    _ = (a - b) / ξ := hlog
    _ < (a - b) / b := hfrac

theorem gap8 (a b : ℝ) (hb : 0 < b) (hba : b < a) :
    (a - b) / a < (a - b) / b := by
  have ha : 0 < a := lt_trans hb hba
  apply (div_lt_div_iff₀ ha hb).2
  exact mul_lt_mul_of_pos_left hba (sub_pos.mpr hba)

theorem gap9 (a b : ℝ) (hb : 0 < b) (hba : b < a) :
    (a - b) / a < Real.log (a / b) ∧
      Real.log (a / b) < (a - b) / b := by
  exact ⟨gap6 a b hb hba, gap7 a b hb hba⟩

end

end ProofGap.Exercise1251_4
