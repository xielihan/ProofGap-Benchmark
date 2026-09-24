import ProofGapLean.Prelude.Analysis
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise566_2

noncomputable section

def original (x : ℝ) : ℝ :=
  Real.log (x ^ 2 + Real.exp x) / Real.log (x ^ 4 + Real.exp (2 * x))
def normalized (x : ℝ) : ℝ :=
  (1 + Real.log (1 + x ^ 2 * Real.exp (-x)) / x) /
    (2 + Real.log (1 + x ^ 4 * Real.exp (-2 * x)) / x)

/-- Source: `proof_gap/exercise_566_2/1.txt`; express equality of represented limits. -/
private theorem decay_limits :
    Filter.Tendsto (fun x : ℝ => x ^ 2 * Real.exp (-x))
      Filter.atTop (nhds 0) ∧
    Filter.Tendsto (fun x : ℝ => x ^ 4 * Real.exp (-2 * x))
      Filter.atTop (nhds 0) := by
  constructor
  · simpa using Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 2
  · have htwo :
        Filter.Tendsto (fun x : ℝ => 2 * x) Filter.atTop Filter.atTop := by
      refine Filter.tendsto_atTop.2 ?_
      intro b
      filter_upwards [Filter.eventually_ge_atTop (b / 2)] with x hx
      linarith
    have hcomp :
        Filter.Tendsto
          (fun x : ℝ => (2 * x) ^ 4 * Real.exp (-(2 * x)))
          Filter.atTop (nhds 0) := by
      simpa only [Function.comp_apply] using
        (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 4).comp htwo
    have hscaled :
        Filter.Tendsto
          (fun x : ℝ =>
            (1 / 16 : ℝ) * ((2 * x) ^ 4 * Real.exp (-(2 * x))))
          Filter.atTop (nhds ((1 / 16 : ℝ) * 0)) :=
      tendsto_const_nhds.mul hcomp
    have hfun :
        (fun x : ℝ => x ^ 4 * Real.exp (-2 * x)) =
          (fun x : ℝ =>
            (1 / 16 : ℝ) * ((2 * x) ^ 4 * Real.exp (-(2 * x)))) := by
      funext x
      rw [show -(2 * x) = -2 * x by ring]
      ring_nf
    rw [hfun]
    simpa using hscaled

theorem gap1 (L : ℝ) :
    Filter.Tendsto original Filter.atTop (nhds L) ↔
      Filter.Tendsto normalized Filter.atTop (nhds L) := by
  have heq : original =ᶠ[Filter.atTop] normalized := by
    filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with x hx
    have hx0 : x ≠ 0 := ne_of_gt hx
    have hApos : 0 < 1 + x ^ 2 * Real.exp (-x) := by
      positivity
    have hBpos : 0 < 1 + x ^ 4 * Real.exp (-2 * x) := by
      positivity
    have hcancelA : Real.exp x * Real.exp (-x) = 1 := by
      rw [← Real.exp_add]
      simp
    have hcancelB : Real.exp (2 * x) * Real.exp (-2 * x) = 1 := by
      rw [← Real.exp_add]
      convert Real.exp_zero using 1 <;> ring
    have hfactorA :
        x ^ 2 + Real.exp x =
          Real.exp x * (1 + x ^ 2 * Real.exp (-x)) := by
      symm
      calc
        Real.exp x * (1 + x ^ 2 * Real.exp (-x)) =
            Real.exp x + x ^ 2 * (Real.exp x * Real.exp (-x)) := by ring
        _ = Real.exp x + x ^ 2 := by rw [hcancelA]; ring
        _ = x ^ 2 + Real.exp x := by ring
    have hfactorB :
        x ^ 4 + Real.exp (2 * x) =
          Real.exp (2 * x) * (1 + x ^ 4 * Real.exp (-2 * x)) := by
      symm
      calc
        Real.exp (2 * x) * (1 + x ^ 4 * Real.exp (-2 * x)) =
            Real.exp (2 * x) +
              x ^ 4 * (Real.exp (2 * x) * Real.exp (-2 * x)) := by ring
        _ = Real.exp (2 * x) + x ^ 4 := by rw [hcancelB]; ring
        _ = x ^ 4 + Real.exp (2 * x) := by ring
    have hlogA :
        Real.log (x ^ 2 + Real.exp x) =
          x + Real.log (1 + x ^ 2 * Real.exp (-x)) := by
      calc
        Real.log (x ^ 2 + Real.exp x) =
            Real.log (Real.exp x * (1 + x ^ 2 * Real.exp (-x))) := by
              rw [hfactorA]
        _ = Real.log (Real.exp x) +
              Real.log (1 + x ^ 2 * Real.exp (-x)) :=
            Real.log_mul (Real.exp_ne_zero x) (ne_of_gt hApos)
        _ = x + Real.log (1 + x ^ 2 * Real.exp (-x)) := by
              rw [Real.log_exp]
    have hlogB :
        Real.log (x ^ 4 + Real.exp (2 * x)) =
          2 * x + Real.log (1 + x ^ 4 * Real.exp (-2 * x)) := by
      calc
        Real.log (x ^ 4 + Real.exp (2 * x)) =
            Real.log
              (Real.exp (2 * x) * (1 + x ^ 4 * Real.exp (-2 * x))) := by
                rw [hfactorB]
        _ = Real.log (Real.exp (2 * x)) +
              Real.log (1 + x ^ 4 * Real.exp (-2 * x)) :=
            Real.log_mul (Real.exp_ne_zero (2 * x)) (ne_of_gt hBpos)
        _ = 2 * x + Real.log (1 + x ^ 4 * Real.exp (-2 * x)) := by
              rw [Real.log_exp]
    unfold original normalized
    rw [hlogA, hlogB]
    have hnum :
        1 + Real.log (1 + x ^ 2 * Real.exp (-x)) / x =
          (x + Real.log (1 + x ^ 2 * Real.exp (-x))) / x := by
      calc
        1 + Real.log (1 + x ^ 2 * Real.exp (-x)) / x =
            x / x + Real.log (1 + x ^ 2 * Real.exp (-x)) / x := by
              rw [div_self hx0]
        _ = (x + Real.log (1 + x ^ 2 * Real.exp (-x))) / x := by
              rw [add_div]
    have hden :
        2 + Real.log (1 + x ^ 4 * Real.exp (-2 * x)) / x =
          (2 * x + Real.log (1 + x ^ 4 * Real.exp (-2 * x))) / x := by
      calc
        2 + Real.log (1 + x ^ 4 * Real.exp (-2 * x)) / x =
            (2 * x) / x +
              Real.log (1 + x ^ 4 * Real.exp (-2 * x)) / x := by
                field_simp [hx0] <;> ring
        _ = (2 * x + Real.log (1 + x ^ 4 * Real.exp (-2 * x))) / x := by
              rw [add_div]
    rw [hnum, hden]
    have hterm_nonneg : 0 ≤ x ^ 4 * Real.exp (-2 * x) := by
      positivity
    have hlog_nonneg :
        0 ≤ Real.log (1 + x ^ 4 * Real.exp (-2 * x)) := by
      apply Real.log_nonneg
      linarith
    have hdpos :
        0 < 2 * x + Real.log (1 + x ^ 4 * Real.exp (-2 * x)) := by
      linarith
    field_simp [hx0, ne_of_gt hdpos] <;> ring_nf
  constructor
  · intro h
    exact Filter.Tendsto.congr' heq h
  · intro h
    exact Filter.Tendsto.congr' heq.symm h

/-- Source: `proof_gap/exercise_566_2/2.txt`. -/
theorem gap2 :
    Filter.Tendsto normalized Filter.atTop (nhds (1 / 2 : ℝ)) := by
  have harg2 :
      Filter.Tendsto
        (fun x : ℝ => 1 + x ^ 2 * Real.exp (-x))
        Filter.atTop (nhds 1) := by
    simpa using (tendsto_const_nhds.add decay_limits.1)
  have harg4 :
      Filter.Tendsto
        (fun x : ℝ => 1 + x ^ 4 * Real.exp (-2 * x))
        Filter.atTop (nhds 1) := by
    simpa using (tendsto_const_nhds.add decay_limits.2)
  have hlog2 :
      Filter.Tendsto
        (fun x : ℝ => Real.log (1 + x ^ 2 * Real.exp (-x)))
        Filter.atTop (nhds 0) := by
    simpa using
      ((Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp harg2)
  have hlog4 :
      Filter.Tendsto
        (fun x : ℝ => Real.log (1 + x ^ 4 * Real.exp (-2 * x)))
        Filter.atTop (nhds 0) := by
    simpa using
      ((Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp harg4)
  have hinv :
      Filter.Tendsto (fun x : ℝ => x⁻¹) Filter.atTop (nhds 0) :=
    tendsto_inv_atTop_zero
  have hquot2 :
      Filter.Tendsto
        (fun x : ℝ => Real.log (1 + x ^ 2 * Real.exp (-x)) / x)
        Filter.atTop (nhds 0) := by
    simpa [div_eq_mul_inv] using hlog2.mul hinv
  have hquot4 :
      Filter.Tendsto
        (fun x : ℝ => Real.log (1 + x ^ 4 * Real.exp (-2 * x)) / x)
        Filter.atTop (nhds 0) := by
    simpa [div_eq_mul_inv] using hlog4.mul hinv
  have hnum :
      Filter.Tendsto
        (fun x : ℝ => 1 + Real.log (1 + x ^ 2 * Real.exp (-x)) / x)
        Filter.atTop (nhds 1) := by
    simpa using (tendsto_const_nhds.add hquot2)
  have hden :
      Filter.Tendsto
        (fun x : ℝ => 2 + Real.log (1 + x ^ 4 * Real.exp (-2 * x)) / x)
        Filter.atTop (nhds 2) := by
    simpa using (tendsto_const_nhds.add hquot4)
  change Filter.Tendsto
    (fun x : ℝ =>
      (1 + Real.log (1 + x ^ 2 * Real.exp (-x)) / x) /
        (2 + Real.log (1 + x ^ 4 * Real.exp (-2 * x)) / x))
    Filter.atTop (nhds (1 / 2 : ℝ))
  exact hnum.div hden (by norm_num : (2 : ℝ) ≠ 0)

/-- Source: `proof_gap/exercise_566_2/3.txt`. -/
theorem gap3 :
    Filter.Tendsto original Filter.atTop (nhds (1 / 2 : ℝ)) := by
  exact (gap1 (1 / 2 : ℝ)).mpr gap2

/-- Source: `proof_gap/exercise_566_2/4.txt`. -/
theorem gap4 :
    Filter.Tendsto (fun x : ℝ => x ^ 2 * Real.exp (-x))
      Filter.atTop (nhds 0) := by
  exact decay_limits.1

/-- Source: `proof_gap/exercise_566_2/5.txt`. -/
theorem gap5 :
    Filter.Tendsto (fun x : ℝ => x ^ 4 * Real.exp (-2 * x))
      Filter.atTop (nhds 0) := by
  exact decay_limits.2

end

end ProofGap.Exercise566_2
