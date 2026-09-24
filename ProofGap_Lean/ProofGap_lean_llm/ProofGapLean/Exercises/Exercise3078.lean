import ProofGapLean.Prelude.Analysis
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Summable

namespace ProofGap.Exercise3078

noncomputable section

open Filter
open scoped BigOperators Topology

def p (c x : ℝ) (n : ℕ) : ℝ :=
  (1 - x / (c + n)) * Real.exp (x / (n : ℝ))

def firstApproximation (c x : ℝ) (n : ℕ) : ℝ :=
  1 - x / (c + n) + x / (n : ℝ) -
    x ^ 2 / ((n : ℝ) * (c + n))

def simplifiedApproximation (c x : ℝ) (n : ℕ) : ℝ :=
  1 - (x ^ 2 - c * x) / ((n : ℝ) * (c + n))

def inverseSquare (n : ℕ) : ℝ :=
  1 / (n : ℝ) ^ 2

def SummableFromOne (f : ℕ → ℝ) : Prop :=
  Summable (fun k : ℕ => f (k + 1))

def partialProduct (c x : ℝ) (n : ℕ) : ℝ :=
  ∏ i ∈ Finset.Icc 1 n, p c x i

def ConvergentProduct (c x : ℝ) : Prop :=
  ∃ P : ℝ, Tendsto (partialProduct c x) atTop (𝓝 P)

private theorem exp_linear_remainder_isBigO :
    (fun t : ℝ => Real.exp t - (1 + t)) =O[𝓝 0]
      (fun t : ℝ => t ^ 2) := by
  simpa [Finset.sum_range_succ] using
    (Real.exp_sub_sum_range_isBigO_pow 2)

private theorem div_nat_tendsto_zero (x : ℝ) :
    Tendsto (fun n : ℕ => x / (n : ℝ)) atTop (𝓝 0) :=
  tendsto_natCast_atTop_atTop.const_div_atTop x

private theorem exp_div_remainder_isBigO (x : ℝ) :
    (fun n : ℕ => Real.exp (x / (n : ℝ)) - (1 + x / (n : ℝ)))
      =O[atTop] inverseSquare := by
  have hc := exp_linear_remainder_isBigO.comp_tendsto
    (div_nat_tendsto_zero x)
  have htarget :
      (fun t : ℝ => t ^ 2) ∘ (fun n : ℕ => x / (n : ℝ)) =ᶠ[atTop]
        (fun n => x ^ 2 * inverseSquare n) :=
    Eventually.of_forall fun n => by
      simp only [Function.comp_apply]
      unfold inverseSquare
      rw [div_pow]
      ring
  have hscaled :
      (fun n : ℕ => Real.exp (x / (n : ℝ)) - (1 + x / (n : ℝ)))
        =O[atTop] (fun n => x ^ 2 * inverseSquare n) :=
    hc.congr' (Eventually.of_forall fun _ => rfl) htarget
  exact hscaled.trans
    (Asymptotics.isBigO_const_mul_self (x ^ 2) inverseSquare atTop)

private theorem coefficient_isBigO (c x : ℝ) :
    (fun n : ℕ => 1 - x / (c + (n : ℝ))) =O[atTop]
      (fun _ : ℕ => (1 : ℝ)) := by
  have hden : Tendsto (fun n : ℕ => c + (n : ℝ)) atTop atTop := by
    convert tendsto_atTop_add_const_right atTop c
      tendsto_natCast_atTop_atTop using 1
    ext n
    simp [add_comm]
  have hzero : Tendsto (fun n : ℕ => x / (c + (n : ℝ))) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hden
  have hlim : Tendsto (fun n : ℕ => 1 - x / (c + (n : ℝ)))
      atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.sub hzero
  exact hlim.isBigO_one ℝ

private theorem inv_shift_isBigO (c : ℝ) (hc : 0 < c) :
    (fun n : ℕ => 1 / (c + (n : ℝ))) =O[atTop]
      (fun n : ℕ => 1 / (n : ℝ)) := by
  have hden : Tendsto (fun n : ℕ => c + (n : ℝ)) atTop atTop := by
    convert tendsto_atTop_add_const_right atTop c
      tendsto_natCast_atTop_atTop using 1
    ext n
    simp [add_comm]
  have hzero : Tendsto (fun n : ℕ => c / (c + (n : ℝ))) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hden
  have hratio : Tendsto (fun n : ℕ => (n : ℝ) / (c + (n : ℝ)))
      atTop (𝓝 1) := by
    have h : Tendsto (fun n : ℕ => 1 - c / (c + (n : ℝ)))
        atTop (𝓝 (1 - 0)) := tendsto_const_nhds.sub hzero
    rw [show (fun n : ℕ => (n : ℝ) / (c + (n : ℝ))) =
        (fun n : ℕ => 1 - c / (c + (n : ℝ))) by
      funext n
      have hcn : c + (n : ℝ) ≠ 0 := by positivity
      field_simp [hcn]
      ring]
    simpa using h
  have hO := (hratio.isBigO_one ℝ).mul
    (Asymptotics.isBigO_refl (fun n : ℕ => 1 / (n : ℝ)) atTop)
  apply hO.congr'
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : (n : ℝ) ≠ 0 := by positivity
    have hcn : c + (n : ℝ) ≠ 0 := by positivity
    field_simp [hn0, hcn]
  · exact Eventually.of_forall fun _ => by ring

private theorem simplified_sub_one_isBigO (c : ℝ) (hc : 0 < c) (x : ℝ) :
    (fun n : ℕ => simplifiedApproximation c x n - 1) =O[atTop]
      inverseSquare := by
  have hprod :=
    (Asymptotics.isBigO_refl (fun n : ℕ => 1 / (n : ℝ)) atTop).mul
      (inv_shift_isBigO c hc)
  have hconst :=
    Asymptotics.isBigO_const_mul_self (-(x ^ 2 - c * x))
      (fun n : ℕ => 1 / (n : ℝ) * (1 / (c + (n : ℝ)))) atTop
  have h := hconst.trans hprod
  apply h.congr'
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : (n : ℝ) ≠ 0 := by positivity
    have hcn : c + (n : ℝ) ≠ 0 := by positivity
    unfold simplifiedApproximation
    field_simp [hn0, hcn]
    ring
  · exact Eventually.of_forall fun n => by
      unfold inverseSquare
      ring

private theorem inverseSquare_summable : Summable inverseSquare := by
  unfold inverseSquare
  exact Real.summable_one_div_nat_pow.mpr (by norm_num)

private theorem partialProduct_eq_range (c x : ℝ) (n : ℕ) :
    partialProduct c x n =
      ∏ k ∈ Finset.range n, (1 + (p c x (k + 1) - 1)) := by
  induction n with
  | zero =>
      simp [partialProduct]
  | succ n ih =>
      rw [partialProduct, Finset.prod_Icc_succ_top (by omega)]
      change partialProduct c x n * p c x (n + 1) = _
      rw [Finset.prod_range_succ, ih]
      ring

/--
Exercise 3078, gap 1; correct the exponential sign to
match the displayed cancellation and formalize the big-O remainder.
-/
theorem gap1 (c : ℝ) (hc : 0 < c) :
    ∀ x : ℝ,
      ((fun n => p c x n - firstApproximation c x n) =O[atTop]
        inverseSquare) := by
  intro x
  have h := (coefficient_isBigO c x).mul (exp_div_remainder_isBigO x)
  have h' :
      (fun n : ℕ =>
        (1 - x / (c + (n : ℝ))) *
          (Real.exp (x / (n : ℝ)) - (1 + x / (n : ℝ))))
        =O[atTop] inverseSquare := by
    simpa only [one_mul] using h
  apply h'.congr'
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : (n : ℝ) ≠ 0 := by positivity
    have hcn : c + (n : ℝ) ≠ 0 := by positivity
    unfold p firstApproximation
    field_simp [hn0, hcn]
    ring
  · exact Eventually.of_forall fun _ => rfl

/-- Exercise 3078, gap 2; formalize the simplified remainder. -/
theorem gap2 (c : ℝ) (hc : 0 < c) :
    ∀ x : ℝ,
      ((fun n => p c x n - simplifiedApproximation c x n) =O[atTop]
        inverseSquare) := by
  intro x
  apply (gap1 c hc x).congr'
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : (n : ℝ) ≠ 0 := by positivity
    have hcn : c + (n : ℝ) ≠ 0 := by positivity
    unfold firstApproximation simplifiedApproximation
    field_simp [hn0, hcn]
    ring
  · exact Eventually.of_forall fun _ => rfl

/-- Exercise 3078, gap 3; bind `x` and state the function-level big-O. -/
theorem gap3 (c : ℝ) (hc : 0 < c) :
    ∀ x : ℝ, ((fun n => p c x n - 1) =O[atTop] inverseSquare) := by
  intro x
  have h := (gap2 c hc x).add (simplified_sub_one_isBigO c hc x)
  apply h.congr'
  · exact Eventually.of_forall fun n => by ring
  · exact Eventually.of_forall fun _ => by ring

private theorem p_sub_one_summable (c : ℝ) (hc : 0 < c) (x : ℝ) :
    Summable (fun n : ℕ => p c x n - 1) :=
  summable_of_isBigO_nat inverseSquare_summable (gap3 c hc x)

/-- Exercise 3078, gap 4; retain the positive parameter domain. -/
theorem gap4 (c : ℝ) (hc : 0 < c) :
    ∀ x : ℝ, SummableFromOne (fun n => Real.log (p c x n)) := by
  intro x
  unfold SummableFromOne
  have hs : Summable (fun k : ℕ => p c x (k + 1) - 1) :=
    (p_sub_one_summable c hc x).comp_injective Nat.succ_injective
  simpa only [add_sub_cancel] using
    Real.summable_log_one_add_of_summable hs

/--
Exercise 3078, gap 5; convergence applies to the cutoff
sequence of partial products and may have value zero.
-/
theorem gap5 (c : ℝ) (hc : 0 < c) :
    ∀ x : ℝ, ConvergentProduct c x := by
  intro x
  unfold ConvergentProduct
  have hs : Summable (fun k : ℕ => p c x (k + 1) - 1) :=
    (p_sub_one_summable c hc x).comp_injective Nat.succ_injective
  have hm : Multipliable (fun k : ℕ => 1 + (p c x (k + 1) - 1)) :=
    Real.multipliable_one_add_of_summable hs
  refine ⟨∏' k : ℕ, (1 + (p c x (k + 1) - 1)), ?_⟩
  apply hm.hasProd.tendsto_prod_nat.congr'
  exact Eventually.of_forall fun n => (partialProduct_eq_range c x n).symm

end

end ProofGap.Exercise3078
