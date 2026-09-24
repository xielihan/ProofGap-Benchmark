import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr
import Lean.Elab.Tactic.Omega
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Neighborhoods
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Basic

namespace ProofGap.Exercise2725

noncomputable section

open Filter

def term (x : ℝ) (n : ℕ) : ℝ :=
  (x * (x + n) / n) ^ n

def factoredTerm (x : ℝ) (n : ℕ) : ℝ :=
  x ^ n * (1 + x / n) ^ n

def rootMagnitude (x : ℝ) (n : ℕ) : ℝ :=
  Real.rpow |term x n| (1 / (n : ℝ))

private theorem tendsto_succ_index :
    Tendsto (fun n : ℕ => n + 1) atTop atTop := by
  refine tendsto_atTop.2 (fun b => ?_)
  filter_upwards [eventually_ge_atTop b] with n hn
  omega

private theorem tendsto_abs_factor (x : ℝ) :
    Tendsto (fun n : ℕ => |x| * |1 + x / ((n + 1 : ℕ) : ℝ)|)
      atTop (nhds |x|) := by
  have hden : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp tendsto_succ_index
  have hdiv : Tendsto (fun n : ℕ => x / ((n + 1 : ℕ) : ℝ))
      atTop (nhds 0) := by
    simpa using tendsto_const_nhds.div_atTop hden
  have hone : Tendsto (fun n : ℕ => 1 + x / ((n + 1 : ℕ) : ℝ))
      atTop (nhds 1) := by
    simpa using tendsto_const_nhds.add hdiv
  have habs : Tendsto (fun n : ℕ => |1 + x / ((n + 1 : ℕ) : ℝ)|)
      atTop (nhds 1) := by
    simpa using (continuous_abs.tendsto (1 : ℝ)).comp hone
  simpa using tendsto_const_nhds.mul habs

private theorem tendsto_one_add_div_pow_exp_fixed (a : ℝ) (ha : a ≠ 0) :
    Tendsto
      (fun n : ℕ => (1 + a / ((n + 1 : ℕ) : ℝ)) ^ (n + 1))
      atTop (nhds (Real.exp a)) := by
  have hden : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp tendsto_succ_index
  have hz : Tendsto (fun n : ℕ => a / ((n + 1 : ℕ) : ℝ))
      atTop (nhds 0) := by
    simpa using tendsto_const_nhds.div_atTop hden
  have hzWithin : Tendsto (fun n : ℕ => a / ((n + 1 : ℕ) : ℝ))
      atTop (nhdsWithin 0 ({0}ᶜ : Set ℝ)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨hz, ?_⟩
    filter_upwards [] with n
    have hn : (((n + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    exact div_ne_zero ha hn
  have hinner : HasDerivAt (fun z : ℝ => 1 + z) 1 0 := by
    simpa using
      ((hasDerivAt_const (x := (0 : ℝ)) (1 : ℝ)).add (hasDerivAt_id 0))
  have houter : HasDerivAt Real.log (1 + (0 : ℝ))⁻¹ (1 + (0 : ℝ)) :=
    Real.hasDerivAt_log (by norm_num)
  have hd : HasDerivAt (fun z : ℝ => Real.log (1 + z)) 1 0 := by
    have hcomp := houter.comp (0 : ℝ) hinner
    simpa [Function.comp_def] using hcomp
  have hslope : Tendsto (slope (fun z : ℝ => Real.log (1 + z)) 0)
      (nhdsWithin 0 ({0}ᶜ : Set ℝ)) (nhds 1) :=
    (hasDerivAt_iff_tendsto_slope).mp hd
  have hslope_formula (z : ℝ) :
      slope (fun w : ℝ => Real.log (1 + w)) 0 z =
        Real.log (1 + z) / z := by
    simp [slope, div_eq_mul_inv, mul_comm]
  have hratio : Tendsto
      (fun n : ℕ =>
        Real.log (1 + a / ((n + 1 : ℕ) : ℝ)) /
          (a / ((n + 1 : ℕ) : ℝ)))
      atTop (nhds 1) := by
    have hcomp := hslope.comp hzWithin
    simpa only [Function.comp_def, hslope_formula] using hcomp
  have harg : Tendsto
      (fun n : ℕ =>
        ((n + 1 : ℕ) : ℝ) *
          Real.log (1 + a / ((n + 1 : ℕ) : ℝ)))
      atTop (nhds a) := by
    have hfun :
        (fun n : ℕ =>
          ((n + 1 : ℕ) : ℝ) *
            Real.log (1 + a / ((n + 1 : ℕ) : ℝ))) =
        (fun n : ℕ =>
          a * (Real.log (1 + a / ((n + 1 : ℕ) : ℝ)) /
            (a / ((n + 1 : ℕ) : ℝ)))) := by
      funext n
      have hn : (((n + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
      field_simp [ha, hn]
    rw [hfun]
    simpa using tendsto_const_nhds.mul hratio
  have hbase : Tendsto
      (fun n : ℕ => 1 + a / ((n + 1 : ℕ) : ℝ)) atTop (nhds 1) := by
    simpa using tendsto_const_nhds.add hz
  have hpos : ∀ᶠ n : ℕ in atTop,
      0 < 1 + a / ((n + 1 : ℕ) : ℝ) :=
    hbase.eventually (Ioi_mem_nhds (by norm_num : (0 : ℝ) < 1))
  have hexp : Tendsto
      (fun n : ℕ => Real.exp
        (((n + 1 : ℕ) : ℝ) *
          Real.log (1 + a / ((n + 1 : ℕ) : ℝ))))
      atTop (nhds (Real.exp a)) :=
    (Real.continuous_exp.tendsto a).comp harg
  have hevent :
      (fun n : ℕ => (1 + a / ((n + 1 : ℕ) : ℝ)) ^ (n + 1)) =ᶠ[atTop]
        (fun n : ℕ => Real.exp
          (((n + 1 : ℕ) : ℝ) *
            Real.log (1 + a / ((n + 1 : ℕ) : ℝ)))) := by
    filter_upwards [hpos] with n hn
    rw [Real.exp_nat_mul, Real.exp_log hn]
  exact (tendsto_congr' hevent).2 hexp

theorem gap1 (x : ℝ) :
    ∀ n : ℕ, 1 ≤ n → term x n = factoredTerm x n := by
  intro n hn
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  unfold term factoredTerm
  rw [← mul_pow]
  congr 1
  field_simp
  <;> ring

theorem gap2 (x : ℝ) (hx : 1 < |x|) :
    Tendsto (fun n : ℕ => |term x (n + 1)|) atTop atTop := by
  let c : ℝ := (1 + |x|) / 2
  have hc1 : 1 < c := by
    dsimp [c]
    linarith
  have hcx : c < |x| := by
    dsimp [c]
    linarith
  have hbase : Tendsto
      (fun n : ℕ => |x| * |1 + x / ((n + 1 : ℕ) : ℝ)|)
      atTop (nhds |x|) := tendsto_abs_factor x
  have hevent : ∀ᶠ n : ℕ in atTop,
      c < |x| * |1 + x / ((n + 1 : ℕ) : ℝ)| :=
    hbase.eventually (Ioi_mem_nhds hcx)
  have hpow : Tendsto (fun n : ℕ => c ^ (n + 1)) atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt hc1).comp tendsto_succ_index
  refine tendsto_atTop.2 (fun A => ?_)
  have hA : ∀ᶠ n : ℕ in atTop, A ≤ c ^ (n + 1) :=
    hpow.eventually (eventually_ge_atTop A)
  filter_upwards [hevent, hA] with n hn hAn
  have hterm :
      |term x (n + 1)| =
        (|x| * |1 + x / ((n + 1 : ℕ) : ℝ)|) ^ (n + 1) := by
    rw [gap1 x (n + 1) (by omega)]
    simp only [factoredTerm, abs_mul, abs_pow]
    rw [← mul_pow]
  rw [hterm]
  calc
    A ≤ c ^ (n + 1) := hAn
    _ ≤ (|x| * |1 + x / ((n + 1 : ℕ) : ℝ)|) ^ (n + 1) := by
      gcongr

theorem gap3 (x : ℝ) (hx : 1 < |x|) :
    ¬ Summable (fun n : ℕ => term x (n + 1)) := by
  intro hs
  have hz : Tendsto (fun n : ℕ => term x (n + 1)) atTop (nhds 0) :=
    hs.tendsto_atTop_zero
  have habs : Tendsto (fun n : ℕ => |term x (n + 1)|) atTop (nhds 0) := by
    simpa only [abs_zero] using (continuous_abs.tendsto (0 : ℝ)).comp hz
  have hlt : ∀ᶠ n : ℕ in atTop, |term x (n + 1)| < 1 :=
    habs.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
  have hge : ∀ᶠ n : ℕ in atTop, 1 ≤ |term x (n + 1)| :=
    (gap2 x hx).eventually (eventually_ge_atTop (1 : ℝ))
  have hbad : ∀ᶠ n : ℕ in atTop, False := by
    filter_upwards [hlt, hge] with n hnlt hnge
    linarith
  rcases hbad.exists with ⟨n, hn⟩
  exact hn

theorem gap4 (x : ℝ) (hx : |x| = 1) :
    Tendsto (fun n : ℕ => |term x (n + 1)|) atTop
      (nhds (if x = 1 then Real.exp 1 else Real.exp (-1))) := by
  rcases (abs_eq (by norm_num : (0 : ℝ) ≤ 1)).mp hx with hx | hx
  · subst x
    have hfun :
        (fun n : ℕ => |term (1 : ℝ) (n + 1)|) =
          (fun n : ℕ => (1 + (1 : ℝ) / ((n + 1 : ℕ) : ℝ)) ^ (n + 1)) := by
      funext n
      have hp : 0 ≤ 1 + (1 : ℝ) / ((n + 1 : ℕ) : ℝ) := by positivity
      rw [gap1 (1 : ℝ) (n + 1) (by omega)]
      simp only [factoredTerm, abs_mul, abs_pow, abs_one, one_pow, one_mul]
      rw [abs_of_nonneg hp]
    rw [hfun]
    simpa using tendsto_one_add_div_pow_exp_fixed (1 : ℝ) (by norm_num)
  · subst x
    have hfun :
        (fun n : ℕ => |term (-1 : ℝ) (n + 1)|) =
          (fun n : ℕ => (1 + (-1 : ℝ) / ((n + 1 : ℕ) : ℝ)) ^ (n + 1)) := by
      funext n
      have hm : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
        norm_num [Nat.cast_add, Nat.cast_one]
      have hden : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := lt_of_lt_of_le (by norm_num) hm
      have hfrac : (1 : ℝ) / ((n + 1 : ℕ) : ℝ) ≤ 1 :=
        (div_le_one hden).2 hm
      have hp : 0 ≤ 1 + (-1 : ℝ) / ((n + 1 : ℕ) : ℝ) := by
        rw [neg_div]
        linarith
      rw [gap1 (-1 : ℝ) (n + 1) (by omega)]
      simp only [factoredTerm, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
      rw [abs_of_nonneg hp]
    rw [hfun]
    have hne : (-1 : ℝ) ≠ 1 := by norm_num
    simpa [hne] using
      tendsto_one_add_div_pow_exp_fixed (-1 : ℝ) (by norm_num)

theorem gap5 (x : ℝ) (hx : |x| = 1) :
    ¬ Tendsto (fun n : ℕ => term x (n + 1)) atTop (nhds 0) := by
  intro hzero
  have habszero : Tendsto (fun n : ℕ => |term x (n + 1)|) atTop (nhds 0) := by
    simpa only [abs_zero] using
      (continuous_abs.tendsto (0 : ℝ)).comp hzero
  have heq : (if x = 1 then Real.exp 1 else Real.exp (-1)) = 0 :=
    tendsto_nhds_unique (gap4 x hx) habszero
  split_ifs at heq <;> exact Real.exp_ne_zero _ heq

theorem gap6 (x : ℝ) (hx : |x| = 1) :
    ¬ Summable (fun n : ℕ => term x (n + 1)) := by
  intro hs
  exact gap5 x hx hs.tendsto_atTop_zero

theorem gap7 (x : ℝ) :
    ∀ n : ℕ, 1 ≤ n →
      rootMagnitude x n = |x| * |1 + x / n| := by
  intro n hn
  unfold rootMagnitude
  rw [gap1 x n hn]
  simp only [factoredTerm, abs_mul, abs_pow]
  rw [← mul_pow]
  let a : ℝ := |x| * |1 + x / (n : ℝ)|
  change Real.rpow (a ^ n) (1 / (n : ℝ)) = a
  have ha : 0 ≤ a := by
    dsimp [a]
    positivity
  have hnNat : n ≠ 0 := Nat.ne_of_gt hn
  simpa [one_div] using
    (Real.pow_rpow_inv_natCast ha hnNat)

theorem gap8 (x : ℝ) :
    Tendsto (fun n : ℕ => |x| * |1 + x / ((n + 1 : ℕ) : ℝ)|)
      atTop (nhds |x|) := by
  exact tendsto_abs_factor x

theorem gap9 (x : ℝ) (hx : |x| < 1) :
    |x| < 1 := by
  exact hx

theorem gap10 (x : ℝ) :
    Tendsto (fun n : ℕ => rootMagnitude x (n + 1)) atTop (nhds |x|) := by
  have hfun :
      (fun n : ℕ => rootMagnitude x (n + 1)) =
        (fun n : ℕ => |x| * |1 + x / ((n + 1 : ℕ) : ℝ)|) := by
    funext n
    exact gap7 x (n + 1) (by omega)
  rw [hfun]
  exact gap8 x

theorem gap11 (x : ℝ) (hx : |x| < 1) :
    Summable (fun n : ℕ => |term x (n + 1)|) := by
  let c : ℝ := (|x| + 1) / 2
  have hxc : |x| < c := by
    dsimp [c]
    linarith
  have hc1 : c < 1 := by
    dsimp [c]
    linarith
  have hc0 : 0 ≤ c := by
    dsimp [c]
    positivity
  have hevent : ∀ᶠ n : ℕ in atTop,
      |x| * |1 + x / ((n + 1 : ℕ) : ℝ)| < c :=
    (tendsto_abs_factor x).eventually (Iio_mem_nhds hxc)
  have hevent' : ∀ᶠ n : ℕ in cofinite,
      |x| * |1 + x / ((n + 1 : ℕ) : ℝ)| < c := by
    simpa only [Nat.cofinite_eq_atTop] using hevent
  have hcnorm : ‖c‖ < 1 := by
    simpa [Real.norm_eq_abs, abs_of_nonneg hc0] using hc1
  have hgeom : Summable (fun n : ℕ => c ^ n) :=
    summable_geometric_of_norm_lt_one hcnorm
  have hgeom' : Summable (fun n : ℕ => c ^ (n + 1)) := by
    simpa [pow_succ, mul_comm] using hgeom.mul_left c
  refine Summable.of_norm_bounded_eventually hgeom' ?_
  filter_upwards [hevent'] with n hn
  have hterm :
      |term x (n + 1)| =
        (|x| * |1 + x / ((n + 1 : ℕ) : ℝ)|) ^ (n + 1) := by
    rw [gap1 x (n + 1) (by omega)]
    simp only [factoredTerm, abs_mul, abs_pow]
    rw [← mul_pow]
  simp only [Real.norm_eq_abs, abs_abs, abs_pow, abs_of_nonneg hc0]
  rw [hterm]
  gcongr

theorem gap12 (x : ℝ) :
    |x| < 1 ↔ Summable (fun n : ℕ => term x (n + 1)) := by
  constructor
  · intro hx
    have habs : Summable (fun n : ℕ => ‖term x (n + 1)‖) := by
      simpa [Real.norm_eq_abs] using gap11 x hx
    exact habs.of_norm
  · intro hs
    by_contra hlt
    have hge : 1 ≤ |x| := le_of_not_gt hlt
    rcases hge.eq_or_lt with heq | hgt
    · exact gap6 x heq.symm hs
    · exact gap3 x hgt hs

end

end ProofGap.Exercise2725
