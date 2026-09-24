import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.LHopital
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

namespace ProofGap.Exercise2836

noncomputable section

open Filter
open scoped BigOperators Topology

def coefficient (n : ℕ) : ℝ :=
  (1 + 1 / (n : ℝ)) ^ (-(n : ℤ) ^ 2)

def term (n : ℕ) (x : ℝ) : ℝ :=
  coefficient n * Real.exp (-(n : ℝ) * x)

def powerTerm (n : ℕ) (q : ℝ) : ℝ :=
  coefficient n * q ^ n

def SeriesConvergesAt (x : ℝ) : Prop :=
  Summable (fun k : ℕ => term (k + 1) x)

def boundaryTerm (n : ℕ) : ℝ :=
  coefficient n * Real.exp n

private theorem coefficient_pos (n : ℕ) : 0 < coefficient n := by
  unfold coefficient
  apply zpow_pos
  positivity

private theorem coefficient_as_pow (n : ℕ) :
    coefficient n =
      ((1 + 1 / (n : ℝ)) ^ (-(n : ℤ))) ^ n := by
  unfold coefficient
  calc
    (1 + 1 / (n : ℝ)) ^ (-(n : ℤ) ^ 2) =
        (1 + 1 / (n : ℝ)) ^ ((-(n : ℤ)) * (n : ℤ)) := by
      congr 1
      ring
    _ = ((1 + 1 / (n : ℝ)) ^ (-(n : ℤ))) ^ (n : ℤ) :=
      zpow_mul _ _ _
    _ = ((1 + 1 / (n : ℝ)) ^ (-(n : ℤ))) ^ n := by
      rw [zpow_natCast]

private theorem coefficient_root (n : ℕ) :
    Real.rpow |coefficient (n + 1)|
        (1 / (((n + 1 : ℕ) : ℝ))) =
      (1 + 1 / (((n + 1 : ℕ) : ℝ))) ^ (-(n + 1 : ℤ)) := by
  let m := n + 1
  have hm : m ≠ 0 := by omega
  have hbase : 0 < 1 + 1 / (m : ℝ) := by positivity
  have hroot : 0 ≤ (1 + 1 / (m : ℝ)) ^ (-(m : ℤ)) :=
    (zpow_pos hbase _).le
  rw [abs_of_pos (coefficient_pos m), coefficient_as_pow]
  simpa [m, one_div] using Real.pow_rpow_inv_natCast hroot hm

private theorem denominator_tendsto :
    Tendsto
      (fun n : ℕ =>
        (1 + 1 / (((n + 1 : ℕ) : ℝ))) ^ (n + 1))
      atTop (𝓝 (Real.exp 1)) := by
  convert (Real.tendsto_one_add_div_pow_exp 1).comp
    (tendsto_add_atTop_nat 1) using 1

private theorem rootQuotient_tendsto (x : ℝ) :
    Tendsto
      (fun n : ℕ =>
        Real.exp (-x) /
          (1 + 1 / (((n + 1 : ℕ) : ℝ))) ^ (n + 1))
      atTop (𝓝 (Real.exp (-x) / Real.exp 1)) :=
  tendsto_const_nhds.div denominator_tendsto (Real.exp_ne_zero _)

private theorem term_abs_eq (n : ℕ) (hn : n ≠ 0) (x : ℝ) :
    |term n x| =
      (Real.exp (-x) / (1 + 1 / (n : ℝ)) ^ n) ^ n := by
  have hbase : 0 < 1 + 1 / (n : ℝ) := by
    have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
    positivity
  rw [abs_of_pos (by unfold term; exact mul_pos (coefficient_pos n) (Real.exp_pos _))]
  unfold term
  rw [coefficient_as_pow, zpow_neg, zpow_natCast]
  have hexp : Real.exp (-(n : ℝ) * x) = Real.exp (-x) ^ n := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [hexp, ← mul_pow]
  congr 1
  rw [div_eq_mul_inv]
  ring

private theorem boundaryTerm_eq_exp (n : ℕ) (hn : n ≠ 0) :
    boundaryTerm n =
      Real.exp
        (-(((n : ℝ) ^ 2) * Real.log (1 + 1 / (n : ℝ)) - (n : ℝ))) := by
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hbase : 0 < 1 + 1 / (n : ℝ) := by positivity
  unfold boundaryTerm coefficient
  rw [zpow_neg]
  have hsq : (n : ℤ) ^ 2 = ((n ^ 2 : ℕ) : ℤ) := by norm_num
  rw [hsq, zpow_natCast]
  have hpow :
      (1 + 1 / (n : ℝ)) ^ (n ^ 2) =
        Real.exp (Real.log (1 + 1 / (n : ℝ)) * ((n ^ 2 : ℕ) : ℝ)) := by
    rw [← Real.rpow_natCast, Real.rpow_def_of_pos hbase]
  rw [hpow, ← Real.exp_neg, ← Real.exp_add]
  congr 1
  push_cast
  ring

private theorem boundaryTerm_succ_tendsto :
    Tendsto (fun n : ℕ => boundaryTerm (n + 1)) atTop
      (𝓝 (Real.exp (1 / 2))) := by
  have hlog :
      Tendsto
        (fun t : ℝ => (Real.log (1 + t) - t) / t ^ 2)
        (𝓝[>] 0) (𝓝 (-1 / 2)) := by
    have hi : Tendsto (fun t : ℝ => t) (𝓝[>] 0) (𝓝 0) :=
      tendsto_id.mono_left inf_le_left
    have hone : Tendsto (fun t : ℝ => 1 + t) (𝓝[>] 0) (𝓝 1) := by
      convert tendsto_const_nhds.add hi using 1 <;> norm_num
    have hnum :
        Tendsto (fun t : ℝ => Real.log (1 + t) - t) (𝓝[>] 0) (𝓝 0) := by
      have hlog1 :=
        (Real.hasDerivAt_log (by norm_num : (1 : ℝ) ≠ 0)).continuousAt.tendsto.comp hone
      convert hlog1.sub hi using 1 <;> norm_num
    have hden : Tendsto (fun t : ℝ => t ^ 2) (𝓝[>] 0) (𝓝 0) := by
      convert hi.pow 2 using 1 <;> norm_num
    have hderiv :
        Tendsto
          (fun t : ℝ => (1 / (1 + t) - 1) / (2 * t))
          (𝓝[>] 0) (𝓝 (-1 / 2)) := by
      have heq :
          (fun t : ℝ => (1 / (1 + t) - 1) / (2 * t)) =ᶠ[𝓝[>] 0]
            fun t : ℝ => -1 / (2 * (1 + t)) := by
        filter_upwards [self_mem_nhdsWithin] with t ht
        have ht0 : t ≠ 0 := ne_of_gt ht
        have ht1 : 1 + t ≠ 0 := by
          have htpos : 0 < t := ht
          nlinarith
        field_simp [ht0, ht1] <;> ring
      rw [tendsto_congr' heq]
      have hdenlim :
          Tendsto (fun t : ℝ => 2 * (1 + t)) (𝓝[>] 0) (𝓝 2) := by
        convert tendsto_const_nhds.mul hone using 1 <;> norm_num
      convert tendsto_const_nhds.div hdenlim
        (by norm_num : (2 : ℝ) ≠ 0) using 1 <;> norm_num
    have hfd :
        ∀ᶠ t : ℝ in 𝓝[>] 0,
          HasDerivAt (fun t : ℝ => Real.log (1 + t) - t)
            (1 / (1 + t) - 1) t := by
      filter_upwards [self_mem_nhdsWithin] with t ht
      have ht1 : 1 + t ≠ 0 := by
        have htpos : 0 < t := ht
        nlinarith
      simpa [Function.comp_def, one_div] using
        (((Real.hasDerivAt_log ht1).comp t
          ((hasDerivAt_id t).const_add 1)).sub (hasDerivAt_id t))
    have hgd :
        ∀ᶠ t : ℝ in 𝓝[>] 0,
          HasDerivAt (fun t : ℝ => t ^ 2) (2 * t) t := by
      filter_upwards with t
      simpa using (hasDerivAt_id t).pow 2
    have hne : ∀ᶠ t : ℝ in 𝓝[>] 0, 2 * t ≠ 0 := by
      filter_upwards [self_mem_nhdsWithin] with t ht
      exact mul_ne_zero (by norm_num) (ne_of_gt ht)
    exact HasDerivAt.lhopital_zero_nhdsGT hfd hgd hne hnum hden hderiv
  have hnadd : Tendsto (fun n : ℕ => n + 1) atTop atTop :=
    (tendsto_add_atTop_iff_nat 1).2 tendsto_id
  have hcast :
      Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hnadd
  have ht_nhds :
      Tendsto (fun n : ℕ => 1 / ((n + 1 : ℕ) : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hcast
  have ht :
      Tendsto (fun n : ℕ => 1 / ((n + 1 : ℕ) : ℝ)) atTop (𝓝[>] 0) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · exact ht_nhds
    · exact Filter.Eventually.of_forall (fun n => by
        change 0 < 1 / ((n + 1 : ℕ) : ℝ)
        positivity)
  have hexponent :
      Tendsto
        (fun n : ℕ =>
          (((n + 1 : ℕ) : ℝ) ^ 2) *
              Real.log (1 + 1 / ((n + 1 : ℕ) : ℝ)) -
            ((n + 1 : ℕ) : ℝ))
        atTop (𝓝 (-1 / 2)) := by
    convert hlog.comp ht using 1
    funext n
    have hn : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
    change
      (((n + 1 : ℕ) : ℝ) ^ 2) *
            Real.log (1 + 1 / ((n + 1 : ℕ) : ℝ)) -
          ((n + 1 : ℕ) : ℝ) =
        (Real.log (1 + 1 / ((n + 1 : ℕ) : ℝ)) -
            1 / ((n + 1 : ℕ) : ℝ)) /
          (1 / ((n + 1 : ℕ) : ℝ)) ^ 2
    field_simp [hn.ne'] <;> ring
  have hnegative :
      Tendsto
        (fun n : ℕ =>
          -((((n + 1 : ℕ) : ℝ) ^ 2 *
              Real.log (1 + 1 / ((n + 1 : ℕ) : ℝ))) -
            ((n + 1 : ℕ) : ℝ)))
        atTop (𝓝 (1 / 2)) := by
    convert hexponent.neg using 1 <;> ring
  have hexp := (Real.continuous_exp.tendsto (1 / 2)).comp hnegative
  convert hexp using 1
  funext n
  rw [boundaryTerm_eq_exp (n + 1) (by omega)]
  rfl

theorem gap1 :
    ∀ x : ℝ,
      (fun k : ℕ => term (k + 1) x) =
        fun k : ℕ => powerTerm (k + 1) (Real.exp (-x)) := by
  intro x
  funext k
  unfold term powerTerm
  congr 1
  rw [← Real.exp_nat_mul]
  congr 1
  push_cast
  ring

theorem gap2 :
    Tendsto
      (fun n : ℕ =>
        Real.rpow |coefficient (n + 1)|
          (1 / (((n + 1 : ℕ) : ℝ))))
      atTop (𝓝 (Real.exp (-1))) ↔
        Tendsto
          (fun n : ℕ =>
            (1 + 1 / (((n + 1 : ℕ) : ℝ))) ^ (-(n + 1 : ℤ)))
          atTop (𝓝 (Real.exp (-1))) := by
  have heq :
      (fun n : ℕ =>
        Real.rpow |coefficient (n + 1)|
          (1 / (((n + 1 : ℕ) : ℝ)))) =
        fun n : ℕ =>
          (1 + 1 / (((n + 1 : ℕ) : ℝ))) ^ (-(n + 1 : ℤ)) := by
    funext n
    exact coefficient_root n
  rw [heq]

theorem gap3 :
    Tendsto
      (fun n : ℕ => (1 + 1 / (((n + 1 : ℕ) : ℝ))) ^ (-(n + 1 : ℤ)))
      atTop (𝓝 (Real.exp (-1))) := by
  have hpow := (Real.tendsto_one_add_div_pow_exp 1).comp
    (tendsto_add_atTop_nat 1)
  have hinv := hpow.inv₀ (Real.exp_ne_zero 1)
  rw [Real.exp_neg]
  refine hinv.congr' ?_
  filter_upwards [] with n
  rw [zpow_neg]
  simp only [Function.comp_apply]
  congr 1

theorem gap4 :
    Tendsto
      (fun n : ℕ =>
        Real.rpow |coefficient (n + 1)|
          (1 / (((n + 1 : ℕ) : ℝ))))
      atTop (𝓝 (Real.exp (-1))) := by
  exact (gap2).2 gap3

theorem gap5 :
    ∀ x : ℝ, |Real.exp (-x)| < Real.exp 1 ↔ -1 < x := by
  intro x
  rw [abs_of_pos (Real.exp_pos _), Real.exp_lt_exp]
  constructor <;> intro h <;> linarith

theorem gap6 :
    ∀ x : ℝ, -1 < x →
      Summable (fun k : ℕ => |term (k + 1) x|) := by
  intro x hx
  let q : ℝ := Real.exp (-x) / Real.exp 1
  let r : ℝ := (q + 1) / 2
  have hq0 : 0 < q := by dsimp [q]; positivity
  have hq1 : q < 1 := by
    dsimp [q]
    rw [div_lt_one (Real.exp_pos 1), Real.exp_lt_exp]
    linarith
  have hqr : q < r := by dsimp [r]; linarith
  have hr1 : r < 1 := by dsimp [r]; linarith
  have hr0 : 0 ≤ r := by dsimp [r]; linarith
  have hev :
      ∀ᶠ n : ℕ in atTop,
        Real.exp (-x) /
            (1 + 1 / (((n + 1 : ℕ) : ℝ))) ^ (n + 1) ≤ r :=
    (rootQuotient_tendsto x).eventually_le_const hqr
  have hgeo : Summable (fun n : ℕ => r ^ (n + 1)) := by
    have hs := summable_geometric_of_norm_lt_one
      (show ‖r‖ < 1 by
        simpa [Real.norm_eq_abs, abs_of_nonneg hr0] using hr1)
    simpa [pow_succ, mul_comm] using hs.mul_left r
  apply hgeo.of_norm_bounded_eventually_nat
  filter_upwards [hev] with n hn
  rw [Real.norm_eq_abs, abs_of_nonneg (abs_nonneg _),
    term_abs_eq (n + 1) (by omega)]
  gcongr

theorem gap7 :
    ∀ x : ℝ, x < -1 → ¬ SeriesConvergesAt x := by
  intro x hx hsum
  let q : ℝ := Real.exp (-x) / Real.exp 1
  have hq : 1 < q := by
    dsimp [q]
    rw [one_lt_div (Real.exp_pos 1), Real.exp_lt_exp]
    linarith
  have hev :
      ∀ᶠ n : ℕ in atTop,
        1 < Real.exp (-x) /
          (1 + 1 / (((n + 1 : ℕ) : ℝ))) ^ (n + 1) :=
    (rootQuotient_tendsto x).eventually_const_lt hq
  have hnorm :
      Tendsto (fun n : ℕ => ‖term (n + 1) x‖) atTop (𝓝 (0 : ℝ)) := by
    simpa using hsum.tendsto_atTop_zero.norm
  have hsmall : ∀ᶠ n : ℕ in atTop, ‖term (n + 1) x‖ < 1 :=
    hnorm.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  rcases (hev.and hsmall).exists with ⟨n, hn, hs⟩
  have hterm : 1 < |term (n + 1) x| := by
    rw [term_abs_eq (n + 1) (by omega)]
    exact one_lt_pow₀ hn (by omega)
  rw [Real.norm_eq_abs] at hs
  linarith

theorem gap8 :
    (fun n : ℕ => boundaryTerm (n + 1)) =
      fun n : ℕ =>
        (Real.exp 1 /
          (1 + 1 / (((n + 1 : ℕ) : ℝ))) ^ (n + 1)) ^ (n + 1) := by
  funext n
  let m := n + 1
  have hz :
      (1 + 1 / (m : ℝ)) ^ (-(m : ℤ)) =
        ((1 + 1 / (m : ℝ)) ^ m)⁻¹ := by
    rw [zpow_neg, zpow_natCast]
  have he : Real.exp (m : ℝ) = Real.exp 1 ^ m := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  change boundaryTerm m =
    (Real.exp 1 / (1 + 1 / (m : ℝ)) ^ m) ^ m
  unfold boundaryTerm
  rw [coefficient_as_pow, hz, he, ← mul_pow]
  congr 1
  rw [div_eq_mul_inv]
  ring

theorem gap9 :
    Tendsto (fun n : ℕ => boundaryTerm (n + 1))
      atTop (𝓝 (Real.exp (1 / 2))) := by
  exact boundaryTerm_succ_tendsto

theorem gap10 :
    Real.exp (1 / 2) ≠ 0 := by
  exact Real.exp_ne_zero _

theorem gap11 :
    ¬ Tendsto (fun n : ℕ => boundaryTerm (n + 1)) atTop (𝓝 0) := by
  intro hzero
  exact gap10 (tendsto_nhds_unique gap9 hzero)

theorem gap12 :
    ¬ Summable (fun n : ℕ => boundaryTerm (n + 1)) := by
  intro hsum
  exact gap11 hsum.tendsto_atTop_zero

theorem gap13 :
    ∀ x : ℝ, x ∈ Set.Ioi (-1 : ℝ) ↔ SeriesConvergesAt x := by
  intro x
  change -1 < x ↔ SeriesConvergesAt x
  constructor
  · intro hx
    unfold SeriesConvergesAt
    exact (gap6 x hx).of_abs
  · intro hsum
    by_contra hnot
    have hle : x ≤ -1 := le_of_not_gt hnot
    rcases hle.eq_or_lt with heq | hlt
    · have hx : x = -1 := heq
      subst x
      apply gap12
      unfold SeriesConvergesAt at hsum
      simpa [term, boundaryTerm] using hsum
    · exact (gap7 x hlt) hsum

end

end ProofGap.Exercise2836
