import ProofGapLean.Prelude.Analysis
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Neighborhoods
import Mathlib.Tactic.Positivity
import Mathlib.Analysis.SpecificLimits.Normed

open scoped BigOperators

namespace ProofGap.Exercise2585

noncomputable section

def factor (k : ℕ) : ℝ :=
  Real.sqrt 2 - Real.rpow 2 (1 / (2 * (k : ℝ) + 1))

def productTerm (n : ℕ) : ℝ :=
  ∏ j ∈ Finset.range n, factor (j + 1)

def quotient (n : ℕ) : ℝ :=
  productTerm (n + 1) / productTerm n

def nextFactor (n : ℕ) : ℝ := factor (n + 1)

private theorem productTerm_pos_aux (n : ℕ) : 0 < productTerm n := by
  unfold productTerm
  refine Finset.prod_pos ?_
  intro j hj
  unfold factor
  apply sub_pos.mpr
  simp only [Nat.cast_add, Nat.cast_one]
  have hj_nonneg : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
  have hden : (0 : ℝ) < 2 * ((j : ℝ) + 1) + 1 := by positivity
  have hexponent :
      (1 : ℝ) / (2 * ((j : ℝ) + 1) + 1) < 1 / 2 := by
    apply (div_lt_div_iff₀ hden (by norm_num : (0 : ℝ) < 2)).2
    nlinarith
  have htwo : (0 : ℝ) < 2 := by norm_num
  have hlog : 0 < Real.log (2 : ℝ) :=
    Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have hsqrt :
      Real.sqrt 2 = Real.exp (Real.log 2 * ((1 : ℝ) / 2)) := by
    rw [Real.sqrt_eq_rpow]
    change (2 : ℝ) ^ ((1 : ℝ) / 2) =
      Real.exp (Real.log 2 * ((1 : ℝ) / 2))
    rw [Real.rpow_def_of_pos htwo]
  have hpow :
      Real.rpow 2 (1 / (2 * ((j : ℝ) + 1) + 1)) =
        Real.exp (Real.log 2 * (1 / (2 * ((j : ℝ) + 1) + 1))) := by
    change (2 : ℝ) ^ (1 / (2 * ((j : ℝ) + 1) + 1)) =
      Real.exp (Real.log 2 * (1 / (2 * ((j : ℝ) + 1) + 1)))
    rw [Real.rpow_def_of_pos htwo]
  rw [hsqrt, hpow]
  exact Real.exp_lt_exp.mpr
    (mul_lt_mul_of_pos_left hexponent hlog)

theorem gap1
    (a : ℕ → ℝ)
    (ha : ∀ n, a n = productTerm n) :
    ∀ L : ℝ, Tendsto (fun n => a (n + 1) / a n) atTop (nhds L) ↔
      Tendsto nextFactor atTop (nhds L) := by
  have hpoint : (fun n => a (n + 1) / a n) = nextFactor := by
    funext n
    rw [ha (n + 1), ha n]
    have hrec : productTerm (n + 1) = productTerm n * factor (n + 1) := by
      simp [productTerm, Finset.prod_range_succ]
    rw [hrec]
    unfold nextFactor
    apply (div_eq_iff (ne_of_gt (productTerm_pos_aux n))).2
    exact mul_comm _ _
  rw [hpoint]
  intro L
  rfl

theorem gap2 :
    Tendsto nextFactor atTop (nhds (Real.sqrt 2 - 1)) := by
  have hcast : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hden :
      Tendsto (fun n : ℕ => 2 * ((n + 1 : ℕ) : ℝ) + 1) atTop atTop := by
    refine Filter.tendsto_atTop.2 (fun b : ℝ => ?_)
    have hb : ∀ᶠ n : ℕ in atTop, b ≤ (n : ℝ) :=
      Filter.tendsto_atTop.1 hcast b
    filter_upwards [hb] with n hn
    simp only [Nat.cast_add, Nat.cast_one]
    have hn_nonneg : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    nlinarith
  have hinv0 : Tendsto (fun x : ℝ => x⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero
  have hone :
      Tendsto (fun n : ℕ => 1 / (2 * ((n + 1 : ℕ) : ℝ) + 1))
        atTop (nhds 0) := by
    simpa only [one_div] using hinv0.comp hden
  have hlogmul :
      Tendsto
        (fun n : ℕ => Real.log 2 * (1 / (2 * ((n + 1 : ℕ) : ℝ) + 1)))
        atTop (nhds (Real.log 2 * 0)) :=
    tendsto_const_nhds.mul hone
  have hexp :
      Tendsto
        (fun n : ℕ =>
          Real.exp (Real.log 2 * (1 / (2 * ((n + 1 : ℕ) : ℝ) + 1))))
        atTop (nhds (Real.exp (Real.log 2 * 0))) :=
    Real.continuous_exp.continuousAt.tendsto.comp hlogmul
  have htwo : (0 : ℝ) < 2 := by norm_num
  have hfun :
      (fun n : ℕ => Real.rpow 2 (1 / (2 * ((n + 1 : ℕ) : ℝ) + 1))) =
        (fun n : ℕ =>
          Real.exp (Real.log 2 * (1 / (2 * ((n + 1 : ℕ) : ℝ) + 1)))) := by
    funext n
    change (2 : ℝ) ^ (1 / (2 * ((n + 1 : ℕ) : ℝ) + 1)) =
      Real.exp (Real.log 2 * (1 / (2 * ((n + 1 : ℕ) : ℝ) + 1)))
    rw [Real.rpow_def_of_pos htwo]
  have hpow :
      Tendsto
        (fun n : ℕ => Real.rpow 2 (1 / (2 * ((n + 1 : ℕ) : ℝ) + 1)))
        atTop (nhds 1) := by
    rw [hfun]
    simpa only [mul_zero, Real.exp_zero] using hexp
  have hsqrt :
      Tendsto (fun _ : ℕ => Real.sqrt 2) atTop (nhds (Real.sqrt 2)) :=
    tendsto_const_nhds
  simpa only [nextFactor, factor] using hsqrt.sub hpow

theorem gap3 :
    Real.sqrt 2 - 1 < 1 := by
  nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]

theorem gap4
    (a : ℕ → ℝ)
    (ha : ∀ n, a n = productTerm n)
    (hquotient : ∀ L : ℝ,
      Tendsto (fun n => a (n + 1) / a n) atTop (nhds L) ↔
        Tendsto nextFactor atTop (nhds L))
    (hfactor : Tendsto nextFactor atTop (nhds (Real.sqrt 2 - 1)))
    (hlt : Real.sqrt 2 - 1 < 1) :
    Tendsto (fun n => a (n + 1) / a n) atTop
        (nhds (Real.sqrt 2 - 1)) ∧
      Real.sqrt 2 - 1 < 1 := by
  exact ⟨(hquotient (Real.sqrt 2 - 1)).2 hfactor, hlt⟩

theorem gap5
    (a : ℕ → ℝ)
    (ha : ∀ n, a n = productTerm n)
    (hratio : Tendsto (fun n => a (n + 1) / a n) atTop
        (nhds (Real.sqrt 2 - 1)) ∧
      Real.sqrt 2 - 1 < 1) :
    Summable productTerm := by
  have hlim :
      Tendsto (fun n => productTerm (n + 1) / productTerm n) atTop
        (nhds (Real.sqrt 2 - 1)) := by
    simpa only [ha] using hratio.1
  let r : ℝ := ((Real.sqrt 2 - 1) + 1) / 2
  have hqr : Real.sqrt 2 - 1 < r := by
    dsimp [r]
    nlinarith [hratio.2]
  have hr1 : r < 1 := by
    dsimp [r]
    nlinarith [hratio.2]
  have hevent :
      ∀ᶠ n : ℕ in atTop, productTerm (n + 1) / productTerm n < r :=
    (tendsto_order.1 hlim).2 r hqr
  refine summable_of_ratio_norm_eventually_le hr1 ?_
  filter_upwards [hevent] with n hn
  have hmul : productTerm (n + 1) < r * productTerm n :=
    (div_lt_iff₀ (productTerm_pos_aux n)).mp hn
  simpa only [Real.norm_eq_abs,
    abs_of_pos (productTerm_pos_aux (n + 1)),
    abs_of_pos (productTerm_pos_aux n)] using hmul.le

theorem gap6
    (hsum : Summable productTerm) :
    Summable productTerm := by
  exact hsum

end

end ProofGap.Exercise2585
