import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.Filter.Prod
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Topology.Defs.Filter

namespace ProofGap.Exercise3189

noncomputable section

open Filter
open scoped Topology

def atTop₂ : Filter (ℝ × ℝ) :=
  (atTop : Filter ℝ) ×ˢ (atTop : Filter ℝ)

def ratioBase (x y : ℝ) : ℝ :=
  x * y / (x ^ 2 + y ^ 2)

def target (p : ℝ × ℝ) : ℝ :=
  Real.rpow (ratioBase p.1 p.2) (p.1 ^ 2)

def upperBound (x : ℝ) : ℝ :=
  Real.rpow (1 / 2 : ℝ) (x ^ 2)

/--
Exercise 3189, gap 1; use real exponentiation on
the positive-base domain.
-/
theorem gap1 :
    ∀ x y : ℝ, 0 < x → 0 < y →
      0 ≤ Real.rpow (ratioBase x y) (x ^ 2) := by
  intro x y hx hy
  apply Real.rpow_nonneg
  unfold ratioBase
  positivity

/-- Exercise 3189, gap 2; AM-GM and monotonicity of `rpow`. -/
theorem gap2 :
    ∀ x y : ℝ, 0 < x → 0 < y →
      Real.rpow (ratioBase x y) (x ^ 2) ≤ upperBound x := by
  intro x y hx hy
  unfold ratioBase upperBound
  have hden : 0 < x ^ 2 + y ^ 2 := by
    positivity
  apply Real.rpow_le_rpow
  · positivity
  · apply (div_le_iff₀ hden).2
    nlinarith [sq_nonneg (x - y)]
  · positivity

/-- Exercise 3189, gap 3; positivity of the upper bound. -/
theorem gap3 :
    ∀ x : ℝ, 0 ≤ upperBound x := by
  intro x
  unfold upperBound
  apply Real.rpow_nonneg
  norm_num

/-- Exercise 3189, gap 4; one-variable exponential decay. -/
theorem gap4 :
    Tendsto upperBound atTop (𝓝 0) := by
  have hsquare : Tendsto (fun x : ℝ => x ^ 2) atTop atTop := by
    rw [tendsto_atTop]
    intro b
    filter_upwards [eventually_ge_atTop (max b 1)] with x hx
    have hxb : b ≤ x := le_trans (le_max_left _ _) hx
    have hx1 : 1 ≤ x := le_trans (le_max_right _ _) hx
    nlinarith
  have hlog : Real.log (1 / 2 : ℝ) < 0 := by
    apply Real.log_neg
    · norm_num
    · norm_num
  have hinner :
      Tendsto (fun x : ℝ => Real.log (1 / 2 : ℝ) * x ^ 2) atTop atBot := by
    rw [tendsto_atBot]
    intro b
    have hc : 0 < -Real.log (1 / 2 : ℝ) := neg_pos.mpr hlog
    have hevent :
        ∀ᶠ x in atTop,
          (-b) / (-Real.log (1 / 2 : ℝ)) ≤ x ^ 2 :=
      hsquare.eventually
        (eventually_ge_atTop ((-b) / (-Real.log (1 / 2 : ℝ))))
    filter_upwards [hevent] with x hx
    have hmul :
        -b ≤ x ^ 2 * (-Real.log (1 / 2 : ℝ)) :=
      (div_le_iff₀ hc).1 hx
    nlinarith
  have hhalf : 0 < (1 / 2 : ℝ) := by norm_num
  have hfun :
      upperBound =
        Real.exp ∘ (fun x : ℝ => Real.log (1 / 2 : ℝ) * x ^ 2) := by
    funext x
    change Real.rpow (1 / 2 : ℝ) (x ^ 2) =
      Real.exp (Real.log (1 / 2 : ℝ) * x ^ 2)
    exact Real.rpow_def_of_pos hhalf (x ^ 2)
  rw [hfun]
  exact Real.tendsto_exp_atBot.comp hinner

/--
Exercise 3189, gap 5; on the `(∞,∞)` filter the
base is eventually positive, so the `rpow` squeeze is valid.
-/
theorem gap5 :
    Tendsto target atTop₂ (𝓝 0) := by
  have hfst : Tendsto (fun p : ℝ × ℝ => p.1) atTop₂ atTop := by
    unfold atTop₂
    exact tendsto_fst
  have hsnd : Tendsto (fun p : ℝ × ℝ => p.2) atTop₂ atTop := by
    unfold atTop₂
    exact tendsto_snd
  have hxpos : ∀ᶠ p in atTop₂, 0 < p.1 :=
    hfst.eventually (eventually_gt_atTop 0)
  have hypos : ∀ᶠ p in atTop₂, 0 < p.2 :=
    hsnd.eventually (eventually_gt_atTop 0)
  have hupper :
      Tendsto (fun p : ℝ × ℝ => upperBound p.1) atTop₂ (𝓝 0) := by
    simpa [Function.comp_def] using gap4.comp hfst
  refine squeeze_zero' ?_ ?_ hupper
  · filter_upwards [hxpos, hypos] with p hp hq
    simpa [target] using gap1 p.1 p.2 hp hq
  · filter_upwards [hxpos, hypos] with p hp hq
    simpa [target] using gap2 p.1 p.2 hp hq

end

end ProofGap.Exercise3189
