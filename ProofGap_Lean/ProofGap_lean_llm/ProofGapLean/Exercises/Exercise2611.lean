import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.PSeries

namespace ProofGap.Exercise2611

noncomputable section

open Filter

def nthRoot (n : ℕ) (a : ℝ) : ℝ :=
  Real.rpow a (1 / (n : ℝ))

def logBase (b x : ℝ) : ℝ :=
  Real.log x / Real.log b

def term (a b : ℝ) (n : ℕ) : ℝ :=
  logBase (Real.rpow b n) (1 + nthRoot n a / n)

def model (a b : ℝ) (n : ℕ) : ℝ :=
  (1 / Real.log b) * nthRoot n a / (n : ℝ) ^ 2

def comparison (n : ℕ) : ℝ := 1 / (n : ℝ) ^ 2

def converges (a b : ℝ) : Prop :=
  Summable (fun n : ℕ => term a b (n + 1))

private theorem inv_succ_tendsto :
    Tendsto (fun n : ℕ => 1 / (n + 1 : ℝ)) atTop (nhds 0) := by
  have hcast : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
  simpa [one_div, Nat.cast_add, Nat.cast_one] using
    tendsto_inv_atTop_zero.comp hcast

private theorem nthRoot_succ_tendsto (a : ℝ) (ha : 0 < a) :
    Tendsto (fun n : ℕ => nthRoot (n + 1) a) atTop (nhds 1) := by
  have h := (Real.continuousAt_const_rpow ha.ne').tendsto.comp inv_succ_tendsto
  simpa [nthRoot] using h

private theorem log_one_plus_div_tendsto :
    Tendsto (fun x : ℝ => Real.log (1 + x) / x)
      (nhdsWithin 0 (Set.compl {0})) (nhds 1) := by
  have hd : HasDerivAt Real.log 1 1 := by
    simpa using Real.hasDerivAt_log one_ne_zero
  have h := hd.tendsto_slope_zero
  convert h using 1 <;> simp [div_eq_mul_inv, mul_comm]

theorem gap1 (a b : ℝ) (n : ℕ)
    (ha : 0 < a) (hb : 0 < b) (hb1 : b ≠ 1) (hn : 1 ≤ n) :
    term a b n =
      Real.log (1 + nthRoot n a / n) / ((n : ℝ) * Real.log b) := by
  unfold term logBase
  have hlog : Real.log (Real.rpow b (n : ℝ)) =
      (n : ℝ) * Real.log b := by
    change Real.log (b ^ (n : ℝ)) = (n : ℝ) * Real.log b
    exact Real.log_rpow hb _
  rw [hlog]

theorem gap2 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hb1 : b ≠ 1) :
    Asymptotics.IsEquivalent atTop
      (fun n : ℕ => term a b (n + 1))
      (fun n : ℕ => model a b (n + 1)) := by
  have hxzero : Tendsto (fun n : ℕ =>
      nthRoot (n + 1) a / (n + 1 : ℝ)) atTop (nhds 0) := by
    have h := (nthRoot_succ_tendsto a ha).mul inv_succ_tendsto
    simpa [div_eq_mul_inv] using h
  have hx : Tendsto (fun n : ℕ =>
      nthRoot (n + 1) a / (n + 1 : ℝ))
      atTop (nhdsWithin 0 (Set.compl {0})) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · exact hxzero
    · exact Filter.Eventually.of_forall (fun n =>
        div_ne_zero (Real.rpow_pos_of_pos ha _).ne' (by positivity))
  have hratio := log_one_plus_div_tendsto.comp hx
  apply Asymptotics.isEquivalent_of_tendsto_one
  apply hratio.congr'
  filter_upwards [] with n
  simp only [Function.comp_apply, Pi.div_apply]
  rw [gap1 a b (n + 1) ha hb hb1 (by omega)]
  unfold model
  have hm : (0 : ℝ) < (n + 1 : ℕ) := by positivity
  have hr : nthRoot (n + 1) a ≠ 0 :=
    (Real.rpow_pos_of_pos ha _).ne'
  have hlog : Real.log b ≠ 0 :=
    Real.log_ne_zero_of_pos_of_ne_one hb hb1
  push_cast
  field_simp [hm.ne', hr, hlog]

theorem gap3 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hb1 : b ≠ 1) :
    Asymptotics.IsBigO atTop
      (fun n : ℕ => model a b (n + 1))
      (fun n : ℕ => comparison (n + 1)) := by
  have hcoef : Tendsto (fun n : ℕ =>
      (1 / Real.log b) * nthRoot (n + 1) a) atTop
      (nhds (1 / Real.log b)) := by
    simpa using tendsto_const_nhds.mul (nthRoot_succ_tendsto a ha)
  have hratio : Tendsto (fun n : ℕ =>
      model a b (n + 1) / comparison (n + 1)) atTop
      (nhds (1 / Real.log b)) := by
    apply hcoef.congr'
    filter_upwards [] with n
    unfold model comparison
    have hm : (0 : ℝ) < (n + 1 : ℕ) := by positivity
    field_simp [hm.ne']
  refine Asymptotics.isBigO_of_div_tendsto_nhds
    (f := fun n : ℕ => model a b (n + 1))
    (g := fun n : ℕ => comparison (n + 1)) ?_
    (1 / Real.log b) ?_
  · exact Filter.Eventually.of_forall (fun n hzero =>
      False.elim ((show comparison (n + 1) ≠ 0 by
        unfold comparison
        positivity) hzero))
  · simpa only [Pi.div_apply] using hratio

theorem gap4 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hb1 : b ≠ 1) :
    converges a b := by
  have hcomparison : Summable (fun n : ℕ => comparison (n + 1)) := by
    have hall : Summable (fun n : ℕ => comparison n) := by
      unfold comparison
      simpa [one_div] using
        (Real.summable_nat_pow_inv (p := 2)).2 (by norm_num)
    exact (summable_nat_add_iff 1).mpr hall
  unfold converges
  exact summable_of_isBigO_nat hcomparison
    ((gap2 a b ha hb hb1).isBigO.trans (gap3 a b ha hb hb1))

theorem gap5 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hb1 : b ≠ 1) :
    Summable (fun n : ℕ => term a b (n + 1)) := by
  exact gap4 a b ha hb hb1

end

end ProofGap.Exercise2611
