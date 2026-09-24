import ProofGapLean.Prelude.Analysis
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

namespace ProofGap.Exercise506_3

noncomputable section

def original (x : ℝ) : ℝ :=
  Real.rpow ((1 + x) / (2 + x)) ((1 - Real.sqrt x) / (1 - x))
def simplified (x : ℝ) : ℝ :=
  Real.rpow ((1 + x) / (2 + x)) (1 / (1 + Real.sqrt x))

/-- Exercise 506_3, gap 1; express equality of the two represented limits. -/
theorem gap1 (L : ℝ) :
    Filter.Tendsto original Filter.atTop (nhds L) ↔
      Filter.Tendsto simplified Filter.atTop (nhds L) := by
  have heq : original =ᶠ[Filter.atTop] simplified := by
    filter_upwards [Filter.eventually_gt_atTop (1 : ℝ)] with x hx
    unfold original simplified
    apply congrArg (Real.rpow ((1 + x) / (2 + x)))
    have hx0 : 0 ≤ x := by linarith
    have hs : (Real.sqrt x) ^ 2 = x := Real.sq_sqrt hx0
    have hleft : 1 - x ≠ 0 := by linarith
    have hright : 1 + Real.sqrt x ≠ 0 := by
      have hs0 := Real.sqrt_nonneg x
      linarith
    field_simp [hleft, hright] <;> nlinarith [hs]
  exact Filter.tendsto_congr' heq

/-- Exercise 506_3, gap 2; interpret the indeterminate notation `1^0` as its resolved value. -/
theorem gap2 :
    Filter.Tendsto simplified Filter.atTop (nhds 1) := by
  have hshift :
      Filter.Tendsto (fun x : ℝ => 2 + x) Filter.atTop Filter.atTop := by
    refine Filter.tendsto_atTop.2 ?_
    intro b
    filter_upwards [Filter.eventually_ge_atTop (b - 2)] with x hx
    linarith
  have hinv_shift :
      Filter.Tendsto (fun x : ℝ => (2 + x)⁻¹) Filter.atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp hshift
  have hbase_model :
      Filter.Tendsto (fun x : ℝ => 1 - (2 + x)⁻¹)
        Filter.atTop (nhds 1) := by
    simpa using
      ((tendsto_const_nhds :
          Filter.Tendsto (fun _ : ℝ => (1 : ℝ)) Filter.atTop (nhds 1)).sub
        hinv_shift)
  have hbase :
      Filter.Tendsto (fun x : ℝ => (1 + x) / (2 + x))
        Filter.atTop (nhds 1) := by
    refine (Filter.tendsto_congr' ?_).2 hbase_model
    filter_upwards [Filter.eventually_ge_atTop (-1 : ℝ)] with x hx
    have hd : 2 + x ≠ 0 := by linarith
    field_simp [hd] <;> linarith
  have hlog :
      Filter.Tendsto (fun x : ℝ => Real.log ((1 + x) / (2 + x)))
        Filter.atTop (nhds 0) := by
    simpa using
      ((Real.continuousAt_log (one_ne_zero : (1 : ℝ) ≠ 0)).tendsto.comp hbase)
  have hden_sqrt :
      Filter.Tendsto (fun x : ℝ => 1 + Real.sqrt x)
        Filter.atTop Filter.atTop := by
    refine Filter.tendsto_atTop.2 ?_
    intro b
    filter_upwards
      [(Filter.tendsto_atTop.1 Real.tendsto_sqrt_atTop) (b - 1)] with x hx
    linarith
  have hexponent :
      Filter.Tendsto (fun x : ℝ => 1 / (1 + Real.sqrt x))
        Filter.atTop (nhds 0) := by
    simpa [one_div] using
      (tendsto_inv_atTop_zero.comp hden_sqrt)
  have hproduct :
      Filter.Tendsto
        (fun x : ℝ =>
          Real.log ((1 + x) / (2 + x)) * (1 / (1 + Real.sqrt x)))
        Filter.atTop (nhds 0) := by
    simpa using hlog.mul hexponent
  have hexp :
      Filter.Tendsto
        (fun x : ℝ =>
          Real.exp
            (Real.log ((1 + x) / (2 + x)) *
              (1 / (1 + Real.sqrt x))))
        Filter.atTop (nhds 1) := by
    simpa using (Real.continuous_exp.tendsto 0).comp hproduct
  have hpositive :
      ∀ᶠ x : ℝ in Filter.atTop, 0 < (1 + x) / (2 + x) := by
    filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with x hx
    exact div_pos (by linarith) (by linarith)
  refine (Filter.tendsto_congr' ?_).2 hexp
  filter_upwards [hpositive] with x hx
  unfold simplified
  change
    ((1 + x) / (2 + x)) ^ (1 / (1 + Real.sqrt x) : ℝ) =
      Real.exp
        (Real.log ((1 + x) / (2 + x)) *
          (1 / (1 + Real.sqrt x)))
  exact Real.rpow_def_of_pos hx (1 / (1 + Real.sqrt x))

/-- Exercise 506_3, gap 3. -/
theorem gap3 : (1 : ℝ) ^ (0 : ℕ) = 1 := by
  rfl

/-- Exercise 506_3, gap 4. -/
theorem gap4 :
    Filter.Tendsto original Filter.atTop (nhds 1) := by
  exact (gap1 1).2 gap2

end

end ProofGap.Exercise506_3
