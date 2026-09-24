import ProofGapLean.Prelude.Analysis
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise652

noncomputable section

def r₁ (x : ℝ) : ℝ := (x ^ 2 + 10 * x + 100) / (0.001 * x ^ 3)
def r₂ (x : ℝ) : ℝ := Real.log x ^ 1000 / Real.sqrt x
def r₃ (x : ℝ) : ℝ := x ^ 10 * Real.exp x / Real.exp (2 * x)

/-- Exercise 652, gap 1. -/
theorem gap1 : Filter.Tendsto r₁ Filter.atTop (nhds 0) := by
  have hinv :
      Filter.Tendsto (fun x : ℝ => x⁻¹) Filter.atTop (nhds 0) :=
    tendsto_inv_atTop_zero
  have h2 :
      Filter.Tendsto (fun x : ℝ => (x⁻¹) ^ 2) Filter.atTop (nhds 0) := by
    simpa [pow_two] using hinv.mul hinv
  have h3 :
      Filter.Tendsto (fun x : ℝ => (x⁻¹) ^ 3) Filter.atTop (nhds 0) := by
    simpa [pow_succ] using h2.mul hinv
  have hc10 :
      Filter.Tendsto (fun _ : ℝ => (10 : ℝ)) Filter.atTop (nhds 10) :=
    tendsto_const_nhds
  have hc100 :
      Filter.Tendsto (fun _ : ℝ => (100 : ℝ)) Filter.atTop (nhds 100) :=
    tendsto_const_nhds
  have hc1000 :
      Filter.Tendsto (fun _ : ℝ => (1000 : ℝ)) Filter.atTop (nhds 1000) :=
    tendsto_const_nhds
  have hsum :
      Filter.Tendsto
        (fun x : ℝ => x⁻¹ + 10 * (x⁻¹) ^ 2 + 100 * (x⁻¹) ^ 3)
        Filter.atTop (nhds 0) := by
    simpa using ((hinv.add (hc10.mul h2)).add (hc100.mul h3))
  have hpoly :
      Filter.Tendsto
        (fun x : ℝ =>
          1000 * (x⁻¹ + 10 * (x⁻¹) ^ 2 + 100 * (x⁻¹) ^ 3))
        Filter.atTop (nhds 0) := by
    simpa using hc1000.mul hsum
  refine hpoly.congr' ?_
  filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with x hx
  norm_num [r₁]
  field_simp [ne_of_gt hx] <;> ring

/-- Exercise 652, gap 2; replace `BigEnough` by an eventual assertion. -/
theorem gap2 : ∀ᶠ x in Filter.atTop, r₁ x < 1 := by
  exact gap1.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))

/-- Exercise 652, gap 3; replace `BigEnough` by an eventual assertion. -/
theorem gap3 :
    ∀ᶠ x in Filter.atTop,
      x ^ 2 + 10 * x + 100 < (0.001 : ℝ) * x ^ 3 := by
  filter_upwards [gap2, Filter.eventually_gt_atTop (0 : ℝ)] with x h hx
  change
    (x ^ 2 + 10 * x + 100) / ((0.001 : ℝ) * x ^ 3) < 1 at h
  have hd : 0 < (0.001 : ℝ) * x ^ 3 :=
    mul_pos (by norm_num) (pow_pos hx 3)
  exact (div_lt_one hd).mp h

/-- Exercise 652, gap 4. -/
theorem gap4 : Filter.Tendsto r₂ Filter.atTop (nhds 0) := by
  have hloghalf :
      Filter.Tendsto (fun x : ℝ => Real.log x / 2)
        Filter.atTop Filter.atTop := by
    refine Filter.tendsto_atTop.2 ?_
    intro b
    filter_upwards
      [(Filter.tendsto_atTop.1 Real.tendsto_log_atTop (2 * b))] with x hx
    linarith
  have hscaled :
      Filter.Tendsto
        (fun x : ℝ =>
          (Real.log x / 2) ^ 1000 / Real.exp (Real.log x / 2))
        Filter.atTop (nhds 0) := by
    simpa [div_eq_mul_inv, ← Real.exp_neg] using
      ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1000).comp hloghalf)
  have hc :
      Filter.Tendsto (fun _ : ℝ => (2 : ℝ) ^ 1000)
        Filter.atTop (nhds ((2 : ℝ) ^ 1000)) :=
    tendsto_const_nhds
  have hmul :
      Filter.Tendsto
        (fun x : ℝ =>
          (2 : ℝ) ^ 1000 *
            ((Real.log x / 2) ^ 1000 / Real.exp (Real.log x / 2)))
        Filter.atTop (nhds 0) := by
    simpa using hc.mul hscaled
  refine hmul.congr' ?_
  filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with x hx
  have hexp_sq : Real.exp (Real.log x / 2) ^ 2 = x := by
    calc
      Real.exp (Real.log x / 2) ^ 2 =
          Real.exp (Real.log x / 2 + Real.log x / 2) := by
            rw [pow_two, ← Real.exp_add]
      _ = Real.exp (Real.log x) := by
            congr 1 <;> ring
      _ = x := Real.exp_log hx
  have hsqrt_sq : Real.sqrt x ^ 2 = x :=
    Real.sq_sqrt (le_of_lt hx)
  have hsqrt : Real.sqrt x = Real.exp (Real.log x / 2) := by
    nlinarith [Real.sqrt_nonneg x, Real.exp_pos (Real.log x / 2)]
  rw [r₂, hsqrt, div_pow]
  field_simp [Real.exp_ne_zero] <;> ring

/-- Exercise 652, gap 5; replace `BigEnough` by an eventual assertion. -/
theorem gap5 : ∀ᶠ x in Filter.atTop, r₂ x < 1 := by
  exact gap4.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))

/-- Exercise 652, gap 6; replace `BigEnough` by an eventual assertion. -/
theorem gap6 :
    ∀ᶠ x in Filter.atTop, Real.log x ^ 1000 < Real.sqrt x := by
  filter_upwards [gap5, Filter.eventually_gt_atTop (0 : ℝ)] with x h hx
  change Real.log x ^ 1000 / Real.sqrt x < 1 at h
  exact (div_lt_one (Real.sqrt_pos.2 hx)).mp h

/-- Exercise 652, gap 7. -/
theorem gap7 (x : ℝ) :
    x ^ 10 * Real.exp x / Real.exp (2 * x) = x ^ 10 / Real.exp x := by
  rw [show (2 : ℝ) * x = x + x by ring, Real.exp_add]
  field_simp [Real.exp_ne_zero] <;> ring

/-- Exercise 652, gap 8. -/
theorem gap8 :
    Filter.Tendsto (fun x : ℝ => x ^ 10 / Real.exp x)
      Filter.atTop (nhds 0) := by
  simpa [div_eq_mul_inv, ← Real.exp_neg] using
    (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 10)

/-- Exercise 652, gap 9. -/
theorem gap9 : Filter.Tendsto r₃ Filter.atTop (nhds 0) := by
  refine gap8.congr' ?_
  filter_upwards with x
  exact (gap7 x).symm

/-- Exercise 652, gap 10; replace `BigEnough` by an eventual assertion. -/
theorem gap10 : ∀ᶠ x in Filter.atTop, r₃ x < 1 := by
  exact gap9.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))

/-- Exercise 652, gap 11; replace `BigEnough` by an eventual assertion. -/
theorem gap11 :
    ∀ᶠ x in Filter.atTop, x ^ 10 * Real.exp x < Real.exp (2 * x) := by
  filter_upwards [gap10] with x h
  change x ^ 10 * Real.exp x / Real.exp (2 * x) < 1 at h
  exact (div_lt_one (Real.exp_pos (2 * x))).mp h

/-- Exercise 652, gap 12; use one common eventual threshold. -/
theorem gap12 :
    ∀ᶠ x in Filter.atTop,
      x ^ 2 + 10 * x + 100 < 0.001 * x ^ 3 ∧
      Real.log x ^ 1000 < Real.sqrt x ∧
      x ^ 10 * Real.exp x < Real.exp (2 * x) := by
  filter_upwards [gap3, gap6, gap11] with x h₁ h₂ h₃
  exact ⟨h₁, h₂, h₃⟩

end

end ProofGap.Exercise652
