import ProofGapLean.Prelude.Analysis
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise584

noncomputable section

def arccot (x : ℝ) : ℝ := Real.pi / 2 - Real.arctan x
def f (x : ℝ) : ℝ := arccot (x / Real.sqrt (1 + x ^ 2))
def HasLimitAtNegInfinity (g : ℝ → ℝ) (L : ℝ) : Prop :=
  Filter.Tendsto g Filter.atBot (nhds L)

/-- Exercise 584, gap 1. -/
theorem gap1 : HasLimitAtNegInfinity f (arccot (-1)) := by
  unfold HasLimitAtNegInfinity f
  have hinv :
      Filter.Tendsto (fun x : ℝ => x⁻¹) Filter.atBot (nhds 0) :=
    tendsto_inv_atBot_zero
  have hone :
      Filter.Tendsto (fun _ : ℝ => (1 : ℝ)) Filter.atBot (nhds 1) :=
    tendsto_const_nhds
  have hbase :
      Filter.Tendsto (fun x : ℝ => 1 + (x⁻¹) ^ 2) Filter.atBot (nhds 1) := by
    simpa [pow_two] using hone.add (hinv.mul hinv)
  have hroot :
      Filter.Tendsto (fun x : ℝ => Real.sqrt (1 + (x⁻¹) ^ 2))
        Filter.atBot (nhds 1) := by
    have hs := Real.continuous_sqrt.continuousAt.tendsto.comp hbase
    simpa only [Function.comp_apply, Real.sqrt_one] using hs
  have hmodel :
      Filter.Tendsto (fun x : ℝ => -(1 / Real.sqrt (1 + (x⁻¹) ^ 2)))
        Filter.atBot (nhds (-1)) := by
    have hq := hone.div hroot (one_ne_zero : (1 : ℝ) ≠ 0)
    simpa using hq.neg
  have hneg : ∀ᶠ x : ℝ in Filter.atBot, x < 0 := by
    filter_upwards [Filter.eventually_atBot.2 ⟨(-1 : ℝ), fun x hx => hx⟩] with x hx
    exact lt_of_le_of_lt hx (by norm_num)
  have heq :
      (fun x : ℝ => x / Real.sqrt (1 + x ^ 2)) =ᶠ[Filter.atBot]
        (fun x : ℝ => -(1 / Real.sqrt (1 + (x⁻¹) ^ 2))) := by
    filter_upwards [hneg] with x hx
    have hx0 : x ≠ 0 := ne_of_lt hx
    have hfactor :
        1 + x ^ 2 = x ^ 2 * (1 + (x⁻¹) ^ 2) := by
      field_simp [hx0] <;> ring
    have hqpos : 0 < 1 + (x⁻¹) ^ 2 :=
      add_pos_of_pos_of_nonneg zero_lt_one (sq_nonneg x⁻¹)
    have hspos : 0 < Real.sqrt (1 + (x⁻¹) ^ 2) :=
      Real.sqrt_pos.2 hqpos
    rw [hfactor, Real.sqrt_mul (sq_nonneg x), Real.sqrt_sq_eq_abs,
      abs_of_neg hx]
    field_simp [hx0, ne_of_gt hspos] <;> ring
  have hinner :
      Filter.Tendsto (fun x : ℝ => x / Real.sqrt (1 + x ^ 2))
        Filter.atBot (nhds (-1)) :=
    hmodel.congr' heq.symm
  have hcont : Continuous arccot := by
    simpa only [arccot] using
      (continuous_const.sub Real.continuous_arctan :
        Continuous (fun x : ℝ => Real.pi / 2 - Real.arctan x))
  exact hcont.continuousAt.tendsto.comp hinner

/-- Exercise 584, gap 2. -/
theorem gap2 : arccot (-1) = (3 / 4 : ℝ) * Real.pi := by
  unfold arccot
  rw [Real.arctan_neg, Real.arctan_one]
  ring

/-- Exercise 584, gap 3. -/
theorem gap3 : HasLimitAtNegInfinity f ((3 / 4 : ℝ) * Real.pi) := by
  rw [← gap2]
  exact gap1

end

end ProofGap.Exercise584
