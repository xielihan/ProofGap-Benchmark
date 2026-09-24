import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise658_5

noncomputable section

def target (x : ℝ) : ℝ := Real.log x / (1 - x) ^ 2
def model (x : ℝ) : ℝ := 1 / (x - 1)

/-- Exercise 658_5, gap 1; exclude `x=1`. -/
theorem gap1 (x : ℝ) (hx : x ≠ 1) :
    target x / model x = Real.log (1 + (x - 1)) / (x - 1) := by
  have hxm1 : x - 1 ≠ 0 := sub_ne_zero.mpr hx
  have h1mx : 1 - x ≠ 0 := sub_ne_zero.mpr hx.symm
  unfold target model
  rw [show 1 + (x - 1) = x by ring]
  field_simp [hxm1, h1mx] <;> ring

/-- Exercise 658_5, gap 2. -/
theorem gap2 :
    Filter.Tendsto (fun x : ℝ => Real.log (1 + (x - 1)) / (x - 1))
      (nhdsWithin 1 ({1} : Set ℝ)ᶜ) (nhds 1) := by
  have hs :=
    (Real.hasDerivAt_log
      (show (1 : ℝ) ≠ 0 by exact one_ne_zero)).tendsto_slope
  simp only [inv_one] at hs
  change
    Filter.Tendsto
      (fun x : ℝ => (x - 1)⁻¹ * (Real.log x - Real.log 1))
      (nhdsWithin 1 ({1} : Set ℝ)ᶜ) (nhds 1) at hs
  simpa [div_eq_mul_inv, mul_comm] using hs

/-- Exercise 658_5, gap 3. -/
theorem gap3 :
    Filter.Tendsto (fun x : ℝ => target x / model x)
      (nhdsWithin 1 ({1} : Set ℝ)ᶜ) (nhds 1) := by
  refine gap2.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with x hx
  exact (gap1 x (by simpa using hx)).symm

/-- Exercise 658_5, gap 4. -/
theorem gap4 :
    Asymptotics.IsEquivalent (nhdsWithin 1 ({1} : Set ℝ)ᶜ)
      target model := by
  change
    (fun x : ℝ => target x - model x) =o[nhdsWithin 1 ({1} : Set ℝ)ᶜ]
      model
  rw [Asymptotics.isLittleO_iff]
  intro c hc
  have hratio0 :
      Filter.Tendsto (fun x : ℝ => target x / model x - 1)
        (nhdsWithin 1 ({1} : Set ℝ)ᶜ) (nhds 0) := by
    simpa using gap3.sub_const 1
  have hnorm :
      Filter.Tendsto (fun x : ℝ => ‖target x / model x - 1‖)
        (nhdsWithin 1 ({1} : Set ℝ)ᶜ) (nhds 0) := by
    simpa only [norm_zero] using hratio0.norm
  have hsmall :
      ∀ᶠ x : ℝ in nhdsWithin 1 ({1} : Set ℝ)ᶜ,
        ‖target x / model x - 1‖ < c :=
    (tendsto_order.1 hnorm).2 c hc
  filter_upwards [hsmall, self_mem_nhdsWithin] with x hsmall hx
  have hx1 : x ≠ 1 := by simpa using hx
  have hm : model x ≠ 0 := by
    simp [model, sub_ne_zero.mpr hx1]
  have heq :
      target x - model x = (target x / model x - 1) * model x := by
    field_simp [hm] <;> ring
  rw [heq, norm_mul]
  exact mul_le_mul_of_nonneg_right hsmall.le (norm_nonneg _)

/-- Exercise 658_5, gap 5. -/
theorem gap5 :
    Asymptotics.IsBigO (nhdsWithin 1 ({1} : Set ℝ)ᶜ)
      target model := by
  exact gap4.isBigO

end

end ProofGap.Exercise658_5
