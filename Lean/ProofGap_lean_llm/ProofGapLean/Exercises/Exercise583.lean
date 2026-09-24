import ProofGapLean.Prelude.Analysis
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

namespace ProofGap.Exercise583

noncomputable section

def f (x : ℝ) : ℝ := Real.arctan ((x - 4) / (x - 2) ^ 2)
def HasLimitAtTwo (g : ℝ → ℝ) (L : ℝ) : Prop :=
  Filter.Tendsto g (nhdsWithin 2 ({2} : Set ℝ)ᶜ) (nhds L)

/-- Exercise 583, gap 1. -/
theorem gap1 : HasLimitAtTwo f (-Real.pi / 2) := by
  unfold HasLimitAtTwo
  have hid0 :
      Filter.Tendsto (fun x : ℝ => x) (nhds 2) (nhds 2) := by
    exact continuousAt_id
  have hid :
      Filter.Tendsto (fun x : ℝ => x)
        (nhdsWithin 2 ({2} : Set ℝ)ᶜ) (nhds 2) :=
    hid0.mono_left inf_le_left
  have hsq :
      Filter.Tendsto (fun x : ℝ => (x - 2) ^ 2)
        (nhdsWithin 2 ({2} : Set ℝ)ᶜ) (nhds 0) := by
    simpa using
      (hid.sub
        (tendsto_const_nhds :
          Filter.Tendsto (fun _ : ℝ => (2 : ℝ))
            (nhdsWithin 2 ({2} : Set ℝ)ᶜ) (nhds 2))).pow 2
  have hlt :
      ∀ᶠ x in nhdsWithin 2 ({2} : Set ℝ)ᶜ, x < 3 :=
    (tendsto_order.1 hid).2 3 (by norm_num)
  have hne :
      ∀ᶠ x in nhdsWithin 2 ({2} : Set ℝ)ᶜ, x ≠ 2 := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    simpa using hx
  have hinner :
      Filter.Tendsto (fun x : ℝ => (x - 4) / (x - 2) ^ 2)
        (nhdsWithin 2 ({2} : Set ℝ)ᶜ) atBot := by
    refine Filter.tendsto_atBot.2 fun b => ?_
    by_cases hb : b < 0
    · have heps : 0 < (-1 : ℝ) / b :=
        div_pos_of_neg_of_neg (by norm_num) hb
      have hsmall :
          ∀ᶠ x in nhdsWithin 2 ({2} : Set ℝ)ᶜ,
            (x - 2) ^ 2 < (-1 : ℝ) / b :=
        (tendsto_order.1 hsq).2 _ heps
      filter_upwards [hlt, hne, hsmall] with x hxlt hxne hxsmall
      have hspos : 0 < (x - 2) ^ 2 := by
        rw [pow_two]
        exact mul_self_pos.mpr (sub_ne_zero.mpr hxne)
      have hscale : b * ((-1 : ℝ) / b) = -1 := by
        field_simp [ne_of_lt hb]
      have hprod : (-1 : ℝ) < b * (x - 2) ^ 2 := by
        calc
          (-1 : ℝ) = b * ((-1 : ℝ) / b) := hscale.symm
          _ < b * (x - 2) ^ 2 := mul_lt_mul_of_neg_left hxsmall hb
      have hnum : x - 4 < (-1 : ℝ) := by linarith
      exact le_of_lt ((div_lt_iff₀ hspos).2 (lt_trans hnum hprod))
    · have hbnonneg : 0 ≤ b := le_of_not_gt hb
      filter_upwards [hlt, hne] with x hxlt hxne
      have hspos : 0 < (x - 2) ^ 2 := by
        rw [pow_two]
        exact mul_self_pos.mpr (sub_ne_zero.mpr hxne)
      have hnum : x - 4 < 0 := by linarith
      exact le_trans (le_of_lt (div_neg_of_neg_of_pos hnum hspos)) hbnonneg
  have harctan := Real.tendsto_arctan_atBot.comp hinner
  have harctan' :
      Filter.Tendsto (fun x : ℝ => Real.arctan ((x - 4) / (x - 2) ^ 2))
        (nhdsWithin 2 ({2} : Set ℝ)ᶜ) (nhds (-(Real.pi / 2))) :=
    harctan.mono_right inf_le_left
  simpa [f, neg_div] using harctan'

end

end ProofGap.Exercise583
