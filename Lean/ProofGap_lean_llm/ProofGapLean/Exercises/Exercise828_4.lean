import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

namespace ProofGap.Exercise828_4

noncomputable section

def y (x : ℝ) : ℝ := Real.sqrt x

def quotient (x Δx : ℝ) : ℝ := (y (x + Δx) - y x) / Δx

/-- Source: `proof_gap/exercise_828_4/1.txt`; define `Δy` as the actual function increment. -/
private theorem sqrt_deriv_value (x : ℝ) (hx : 0 < x) :
    deriv y x = 1 / (2 * Real.sqrt x) := by
  change deriv (fun z : ℝ => Real.sqrt z) x = 1 / (2 * Real.sqrt x)
  have hpow :
      HasDerivAt (fun z : ℝ => z ^ (1 / 2 : ℝ))
        ((1 / 2 : ℝ) * x ^ ((1 / 2 : ℝ) - 1)) x := by
    apply Real.hasDerivAt_rpow_const
    first
    | exact ne_of_gt hx
    | exact Or.inl (ne_of_gt hx)
    | exact hx
  have hsqrt :
      HasDerivAt (fun z : ℝ => Real.sqrt z)
        ((1 / 2 : ℝ) * x ^ ((1 / 2 : ℝ) - 1)) x := by
    simpa only [Real.sqrt_eq_rpow] using hpow
  calc
    deriv (fun z : ℝ => Real.sqrt z) x =
        (1 / 2 : ℝ) * x ^ ((1 / 2 : ℝ) - 1) := hsqrt.deriv
    _ = 1 / (2 * Real.sqrt x) := by
      rw [show (1 / 2 : ℝ) - 1 = -(1 / 2 : ℝ) by norm_num]
      rw [Real.rpow_neg (le_of_lt hx)]
      rw [← Real.sqrt_eq_rpow]
      field_simp [ne_of_gt (Real.sqrt_pos.2 hx)]

theorem gap1 (x Δx Δy : ℝ) (hΔy : Δy = y (x + Δx) - y x) :
    Δy / Δx =
      (Real.sqrt (x + Δx) - Real.sqrt x) / Δx := by
  simpa [hΔy, y]

/-- Source: `proof_gap/exercise_828_4/2.txt`; add positivity and nonzero-increment hypotheses. -/
theorem gap2 (x Δx : ℝ) (hx : 0 < x) (hxsum : 0 ≤ x + Δx)
    (hΔx : Δx ≠ 0) :
    (Real.sqrt (x + Δx) - Real.sqrt x) / Δx =
      1 / (Real.sqrt (x + Δx) + Real.sqrt x) := by
  have hsum_pos :
      0 < Real.sqrt (x + Δx) + Real.sqrt x :=
    add_pos_of_nonneg_of_pos (Real.sqrt_nonneg _) (Real.sqrt_pos.2 hx)
  have hsum_ne : Real.sqrt (x + Δx) + Real.sqrt x ≠ 0 :=
    ne_of_gt hsum_pos
  field_simp [hΔx, hsum_ne]
  nlinarith [Real.sq_sqrt hxsum, Real.sq_sqrt (le_of_lt hx)]

/-- Source: `proof_gap/exercise_828_4/3.txt`; define `Δy` and add domain hypotheses. -/
theorem gap3 (x Δx Δy : ℝ) (hx : 0 < x) (hxsum : 0 ≤ x + Δx)
    (hΔx : Δx ≠ 0) (hΔy : Δy = y (x + Δx) - y x) :
    Δy / Δx = 1 / (Real.sqrt (x + Δx) + Real.sqrt x) := by
  rw [hΔy]
  simpa [y] using gap2 x Δx hx hxsum hΔx

/-- Source: `proof_gap/exercise_828_4/4.txt`; replace the undefined limit-value term by `Tendsto`. -/
theorem gap4 (x : ℝ) (hx : 0 < x) :
    Filter.Tendsto (fun Δx => 1 / (Real.sqrt (x + Δx) + Real.sqrt x))
      (nhds 0) (nhds (deriv y x)) := by
  rw [sqrt_deriv_value x hx]
  have hlin : ContinuousAt (fun Δx : ℝ => x + Δx) 0 := by
    exact continuousAt_const.add continuousAt_id
  have hsqrt :
      ContinuousAt (fun Δx : ℝ => Real.sqrt (x + Δx)) 0 := by
    simpa only [Function.comp_apply] using
      Real.continuous_sqrt.continuousAt.comp hlin
  have hdencont :
      ContinuousAt (fun Δx : ℝ => Real.sqrt (x + Δx) + Real.sqrt x) 0 :=
    hsqrt.add continuousAt_const
  have hden : Real.sqrt (x + (0 : ℝ)) + Real.sqrt x ≠ 0 := by
    rw [add_zero]
    exact ne_of_gt (add_pos (Real.sqrt_pos.2 hx) (Real.sqrt_pos.2 hx))
  have hone : ContinuousAt (fun _ : ℝ => (1 : ℝ)) 0 :=
    continuousAt_const
  have hcont :
      ContinuousAt
        (fun Δx : ℝ => 1 / (Real.sqrt (x + Δx) + Real.sqrt x)) 0 :=
    hone.div hdencont hden
  simpa only [ContinuousAt, add_zero, two_mul] using hcont

/-- Source: `proof_gap/exercise_828_4/5.txt`; add `x>0`. -/
theorem gap5 (x : ℝ) (hx : 0 < x) :
    Filter.Tendsto (fun Δx => 1 / (Real.sqrt (x + Δx) + Real.sqrt x))
      (nhds 0) (nhds (1 / (2 * Real.sqrt x))) := by
  rw [← sqrt_deriv_value x hx]
  exact gap4 x hx

/-- Source: `proof_gap/exercise_828_4/6.txt`; add the square-root differentiability domain `x>0`. -/
theorem gap6 (x : ℝ) (hx : 0 < x) :
    deriv y x = 1 / (2 * Real.sqrt x) := by
  exact sqrt_deriv_value x hx

end

end ProofGap.Exercise828_4
