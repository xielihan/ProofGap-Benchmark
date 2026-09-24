import ProofGapLean.Prelude.Analysis
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.PSeries

namespace ProofGap.Exercise3077

noncomputable section

open Filter
open scoped BigOperators Topology

def p (x : ℝ) (n : ℕ) : ℝ :=
  (1 + x / (n : ℝ)) * Real.exp (-x / (n : ℝ))

def alpha (x : ℝ) (n : ℕ) : ℝ :=
  p x n - 1

def secondOrderTerm (x : ℝ) (n : ℕ) : ℝ :=
  -(x ^ 2 / (2 * (n : ℝ) ^ 2))

def remainder (x : ℝ) (n : ℕ) : ℝ :=
  alpha x n - secondOrderTerm x n

def inverseSquare (n : ℕ) : ℝ :=
  1 / (n : ℝ) ^ 2

def SummableFromOne (f : ℕ → ℝ) : Prop :=
  Summable (fun k : ℕ => f (k + 1))

def partialProduct (x : ℝ) (n : ℕ) : ℝ :=
  ∏ i ∈ Finset.Icc 1 n, p x i

def ConvergentProduct (x : ℝ) : Prop :=
  ∃ P : ℝ, Tendsto (partialProduct x) atTop (𝓝 P)

private theorem exp_neg_linear_remainder_isBigO :
    (fun t : ℝ => Real.exp (-t) - (1 - t)) =O[𝓝 0]
      (fun t : ℝ => t ^ 2) := by
  have hn :
      Tendsto (fun t : ℝ => -t) (𝓝 0) (𝓝 0) := by
    simpa using
      (tendsto_id.neg :
        Tendsto (fun t : ℝ => -t) (𝓝 0) (𝓝 (-0)))
  have h :=
    (Real.exp_sub_sum_range_isBigO_pow 2).comp_tendsto hn
  simpa [Function.comp_def, Finset.sum_range_succ] using h

private theorem one_add_mul_exp_neg_sub_one_isBigO :
    (fun t : ℝ => (1 + t) * Real.exp (-t) - 1) =O[𝓝 0]
      (fun t : ℝ => t ^ 2) := by
  have ha :
      (fun t : ℝ => 1 + t) =O[𝓝 0] (fun _t : ℝ => (1 : ℝ)) := by
    exact (show Tendsto (fun t : ℝ => 1 + t) (𝓝 0) (𝓝 1) by
      simpa using
        (tendsto_const_nhds.add tendsto_id :
          Tendsto (fun t : ℝ => 1 + t) (𝓝 0) (𝓝 (1 + 0)))).isBigO_one ℝ
  have hp :
      (fun t : ℝ =>
        (1 + t) * (Real.exp (-t) - (1 - t))) =O[𝓝 0]
          (fun t : ℝ => t ^ 2) := by
    simpa only [one_mul] using
      ha.mul exp_neg_linear_remainder_isBigO
  have hs :=
    hp.sub (Asymptotics.isBigO_refl (fun t : ℝ => t ^ 2) (𝓝 0))
  apply hs.congr'
  · exact Eventually.of_forall fun t => by ring
  · exact Eventually.of_forall fun t => by ring

private theorem div_nat_tendsto_zero (x : ℝ) :
    Tendsto (fun n : ℕ => x / (n : ℝ)) atTop (𝓝 0) :=
  tendsto_natCast_atTop_atTop.const_div_atTop x

private theorem alpha_isBigO (x : ℝ) :
    alpha x =O[atTop] inverseSquare := by
  have hc :=
    one_add_mul_exp_neg_sub_one_isBigO.comp_tendsto
      (div_nat_tendsto_zero x)
  have hsource :
      (fun t : ℝ => (1 + t) * Real.exp (-t) - 1) ∘
          (fun n : ℕ => x / (n : ℝ)) =ᶠ[atTop]
        alpha x :=
    Eventually.of_forall fun n => by
      simp only [Function.comp_apply]
      unfold alpha p
      congr 2
      ring
  have htarget :
      (fun t : ℝ => t ^ 2) ∘ (fun n : ℕ => x / (n : ℝ)) =ᶠ[atTop]
        (fun n => x ^ 2 * inverseSquare n) :=
    Eventually.of_forall fun n => by
      simp only [Function.comp_apply]
      unfold inverseSquare
      rw [div_pow]
      ring
  have hscaled :
      alpha x =O[atTop] (fun n => x ^ 2 * inverseSquare n) :=
    hc.congr' hsource htarget
  exact hscaled.trans
    (Asymptotics.isBigO_const_mul_self (x ^ 2) inverseSquare atTop)

private theorem secondOrder_isBigO (x : ℝ) :
    secondOrderTerm x =O[atTop] inverseSquare := by
  have h :=
    Asymptotics.isBigO_const_mul_self (-(x ^ 2 / 2)) inverseSquare atTop
  apply h.congr'
  · filter_upwards [eventually_ge_atTop 1] with n hn
    unfold secondOrderTerm inverseSquare
    have hn0 : (n : ℝ) ≠ 0 := by positivity
    field_simp
  · exact Eventually.of_forall fun _ => rfl

private theorem inverseSquare_summable :
    Summable inverseSquare := by
  unfold inverseSquare
  exact Real.summable_one_div_nat_pow.mpr (by norm_num)

private theorem alpha_summable (x : ℝ) :
    Summable (alpha x) :=
  summable_of_isBigO_nat inverseSquare_summable (alpha_isBigO x)

private theorem partialProduct_eq_range (x : ℝ) (n : ℕ) :
    partialProduct x n =
      ∏ k ∈ Finset.range n, (1 + alpha x (k + 1)) := by
  induction n with
  | zero =>
      simp [partialProduct]
  | succ n ih =>
      rw [partialProduct, Finset.prod_Icc_succ_top (by omega)]
      change partialProduct x n * p x (n + 1) = _
      rw [Finset.prod_range_succ, ih]
      unfold alpha
      ring

/--
Exercise 3077, gap 1; make the missing `x` argument explicit
and formalize the additive `O(1/n²)` remainder.
-/
theorem gap1 :
    ∀ x : ℝ,
      ((fun n => p x n - (1 + secondOrderTerm x n)) =O[atTop]
        inverseSquare) := by
  intro x
  have h := (alpha_isBigO x).sub (secondOrder_isBigO x)
  apply h.congr'
  · exact Eventually.of_forall fun n => by
      unfold alpha
      ring
  · exact Eventually.of_forall fun _ => rfl

/--
Exercise 3077, gap 2; make `alpha` depend on `x` and
formalize its remainder.
-/
theorem gap2 :
    ∀ x : ℝ,
      ((fun n => alpha x n - secondOrderTerm x n) =O[atTop]
        inverseSquare) := by
  intro x
  exact (alpha_isBigO x).sub (secondOrder_isBigO x)

/-- Exercise 3077, gap 3; strict negativity needs `x ≠ 0` and `n ≥ 1`. -/
theorem gap3 :
    ∀ x : ℝ, x ≠ 0 → ∀ n : ℕ, 1 ≤ n → alpha x n < 0 := by
  intro x hx n hn
  let t : ℝ := x / (n : ℝ)
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have ht : t ≠ 0 := div_ne_zero hx hn0
  have hlt : 1 + t < Real.exp t := by
    simpa [add_comm] using Real.add_one_lt_exp ht
  have hmul := mul_lt_mul_of_pos_right hlt (Real.exp_pos (-t))
  have hexp : Real.exp t * Real.exp (-t) = 1 := by
    rw [← Real.exp_add]
    norm_num
  unfold alpha p
  rw [show -x / (n : ℝ) = -t by
    dsimp [t]
    ring]
  change (1 + t) * Real.exp (-t) - 1 < 0
  rw [hexp] at hmul
  linarith

/--
Exercise 3077, gap 4; replace the `bigO` summand and
unspecified lower cutoff by the actual remainder and a sum from one.
-/
theorem gap4 :
    ∀ x : ℝ,
      SummableFromOne (fun n => secondOrderTerm x n + remainder x n) := by
  intro x
  unfold SummableFromOne
  have hs :
      Summable (fun k : ℕ => alpha x (k + 1)) :=
    (alpha_summable x).comp_injective Nat.succ_injective
  apply hs.congr
  intro k
  unfold remainder
  ring

/-- Exercise 3077, gap 5. -/
theorem gap5 :
    ∀ x : ℝ, SummableFromOne (alpha x) := by
  intro x
  unfold SummableFromOne
  exact (alpha_summable x).comp_injective Nat.succ_injective

/--
Exercise 3077, gap 6; convergence applies to the partial
product sequence indexed by its cutoff.
-/
theorem gap6 :
    ∀ x : ℝ, ConvergentProduct x := by
  intro x
  unfold ConvergentProduct
  have ha :
      Summable (fun k : ℕ => alpha x (k + 1)) :=
    (alpha_summable x).comp_injective Nat.succ_injective
  have hm :
      Multipliable (fun k : ℕ => 1 + alpha x (k + 1)) :=
    Real.multipliable_one_add_of_summable ha
  refine ⟨∏' k : ℕ, (1 + alpha x (k + 1)), ?_⟩
  apply hm.hasProd.tendsto_prod_nat.congr'
  exact Eventually.of_forall fun n =>
    (partialProduct_eq_range x n).symm

end

end ProofGap.Exercise3077
