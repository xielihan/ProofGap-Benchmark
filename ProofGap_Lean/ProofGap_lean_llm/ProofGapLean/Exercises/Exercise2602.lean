import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.PSeries

namespace ProofGap.Exercise2602

noncomputable section

open Filter
open scoped BigOperators

def denominator (q : ℝ) (n : ℕ) : ℝ :=
  ∏ k ∈ Finset.range (n + 1), (q + k)

def term (p q : ℝ) (n : ℕ) : ℝ :=
  (Nat.factorial n : ℝ) * Real.rpow n (-p) / denominator q n

def converges (p q : ℝ) : Prop :=
  Summable (fun n : ℕ => term p q (n + 1))

def ratioRaabe (a : ℕ → ℝ) (n : ℕ) : ℝ :=
  n * (a n / a (n + 1) - 1)

def explicitRaabe (p q : ℝ) (n : ℕ) : ℝ :=
  n * (Real.rpow (1 + 1 / (n : ℝ)) p * (1 + q / (n + 1 : ℝ)) - 1)

def localQuotient (p q x : ℝ) : ℝ :=
  (Real.rpow (1 + x) p * (1 + q * x / (1 + x)) - 1) / x

private theorem denominator_pos (q : ℝ) (hq : 0 < q) (n : ℕ) :
    0 < denominator q n := by
  unfold denominator
  apply Finset.prod_pos
  intro k hk
  have hk0 : (0 : ℝ) ≤ k := by positivity
  linarith

private theorem term_nonneg (p q : ℝ) (hq : 0 < q) (n : ℕ) :
    0 ≤ term p q n := by
  unfold term
  exact div_nonneg
    (mul_nonneg (by positivity) (Real.rpow_nonneg (by positivity) _))
    (denominator_pos q hq n).le

private theorem term_eq_gammaSeq (p q : ℝ) (n : ℕ) (hn : 1 ≤ n) :
    term p q n = Real.GammaSeq q n * Real.rpow n (-(p + q)) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hpow : Real.rpow n q * Real.rpow n (-(p + q)) =
      Real.rpow n (-p) := by
    calc
      Real.rpow n q * Real.rpow n (-(p + q)) =
          Real.rpow n (q + -(p + q)) :=
        (Real.rpow_add hnpos q (-(p + q))).symm
      _ = Real.rpow n (-p) := by congr 1; ring
  unfold term denominator Real.GammaSeq
  change (Nat.factorial n : ℝ) * Real.rpow n (-p) /
      (Finset.prod (Finset.range (n + 1)) (fun k => q + k)) =
    (Real.rpow n q * (Nat.factorial n : ℝ) /
      (Finset.prod (Finset.range (n + 1)) (fun k => q + k))) *
        Real.rpow n (-(p + q))
  rw [div_mul_eq_mul_div]
  rw [show Real.rpow n q * (Nat.factorial n : ℝ) * Real.rpow n (-(p + q)) =
      (Nat.factorial n : ℝ) *
        (Real.rpow n q * Real.rpow n (-(p + q))) by ring]
  rw [hpow]

private theorem summable_term_of_one_lt_add (p q : ℝ) (hq : 0 < q)
    (hpq : 1 < p + q) : Summable (term p q) := by
  let e : ℝ := -(p + q)
  let C : ℝ := Real.Gamma q + 1
  have hGammaPos : 0 < Real.Gamma q := Real.Gamma_pos_of_pos hq
  have hCPos : 0 < C := by dsimp [C]; linarith
  have hpseries : Summable (fun n : ℕ => Real.rpow (n : ℝ) e) :=
    Real.summable_nat_rpow.mpr (by dsimp [e]; linarith)
  have hmajorant : Summable (fun n : ℕ => C * Real.rpow (n : ℝ) e) :=
    hpseries.mul_left C
  have hupper : ∀ᶠ n : ℕ in atTop, Real.GammaSeq q n < C :=
    (tendsto_order.1 (Real.GammaSeq_tendsto_Gamma q)).2 C
      (by dsimp [C]; linarith)
  apply Summable.of_norm_bounded_eventually hmajorant
  rw [Nat.cofinite_eq_atTop]
  filter_upwards [hupper, Filter.eventually_ge_atTop 1] with n hnGamma hn
  rw [Real.norm_eq_abs, abs_of_nonneg (term_nonneg p q hq n),
    term_eq_gammaSeq p q n hn]
  exact mul_le_mul_of_nonneg_right hnGamma.le
    (Real.rpow_nonneg (by positivity) _)

private theorem one_lt_add_of_summable (p q : ℝ) (hq : 0 < q)
    (hsum : Summable (term p q)) : 1 < p + q := by
  let e : ℝ := -(p + q)
  let c : ℝ := Real.Gamma q / 2
  have hGammaPos : 0 < Real.Gamma q := Real.Gamma_pos_of_pos hq
  have hcPos : 0 < c := by dsimp [c]; positivity
  have hlower : ∀ᶠ n : ℕ in atTop, c < Real.GammaSeq q n :=
    (tendsto_order.1 (Real.GammaSeq_tendsto_Gamma q)).1 c
      (by dsimp [c]; linarith)
  have hscaled : Summable (fun n : ℕ => (1 / c) * term p q n) :=
    hsum.mul_left (1 / c)
  have hpseries : Summable (fun n : ℕ => Real.rpow (n : ℝ) e) := by
    apply Summable.of_norm_bounded_eventually hscaled
    rw [Nat.cofinite_eq_atTop]
    filter_upwards [hlower, Filter.eventually_ge_atTop 1] with n hnGamma hn
    have hrpowNonneg : 0 ≤ Real.rpow (n : ℝ) e :=
      Real.rpow_nonneg (by positivity) _
    rw [Real.norm_eq_abs, abs_of_nonneg hrpowNonneg,
      term_eq_gammaSeq p q n hn]
    calc
      Real.rpow (n : ℝ) e = (1 / c) * (c * Real.rpow (n : ℝ) e) := by
        field_simp [hcPos.ne']
      _ ≤ (1 / c) * (Real.GammaSeq q n * Real.rpow (n : ℝ) e) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hnGamma.le hrpowNonneg) (by positivity)
  have hexponent := Real.summable_nat_rpow.mp hpseries
  dsimp [e] at hexponent
  linarith

theorem gap1 (p q : ℝ) (n : ℕ) (hp : 0 < p) (hq : 0 < q) (hn : 1 ≤ n) :
    term p q n / term p q (n + 1) =
      Real.rpow ((n + 1 : ℝ) / n) p * (1 + q / (n + 1 : ℝ)) := by
  have hnpos : (0 : ℝ) < n := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hn1pos : (0 : ℝ) < n + 1 := by positivity
  have hden : denominator q n ≠ 0 := (denominator_pos q hq n).ne'
  have hdenrec : denominator q (n + 1) =
      denominator q n * (q + (n + 1 : ℝ)) := by
    unfold denominator
    rw [Finset.prod_range_succ]
    norm_num
  have hpowN : Real.rpow n p ≠ 0 := (Real.rpow_pos_of_pos hnpos p).ne'
  have hpowN1 : Real.rpow (n + 1 : ℝ) p ≠ 0 :=
    (Real.rpow_pos_of_pos hn1pos p).ne'
  have hnegN : Real.rpow n (-p) = 1 / Real.rpow n p := by
    convert Real.rpow_sub hnpos 0 p using 1 <;> simp
  have hnegN1 : Real.rpow (n + 1 : ℝ) (-p) =
      1 / Real.rpow (n + 1 : ℝ) p := by
    convert Real.rpow_sub hn1pos 0 p using 1 <;> simp
  have hrpowDiv : Real.rpow ((n + 1 : ℝ) / n) p =
      Real.rpow (n + 1 : ℝ) p / Real.rpow n p :=
    Real.div_rpow hn1pos.le hnpos.le p
  unfold term
  rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, hdenrec,
    hnegN, hnegN1, hrpowDiv]
  field_simp [hden, hpowN, hpowN1]
  ring

theorem gap2 (p q : ℝ) (a : ℕ → ℝ)
    (hp : 0 < p) (hq : 0 < q)
    (ha : ∀ n ≥ 1, a n = term p q n) (n : ℕ) (hn : 1 ≤ n) :
    ratioRaabe a n = explicitRaabe p q n := by
  have hnpos : (0 : ℝ) < n := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hbase : ((n + 1 : ℝ) / n) = 1 + 1 / (n : ℝ) := by
    field_simp [hnpos.ne']
  unfold ratioRaabe explicitRaabe
  rw [ha n hn, ha (n + 1) (by omega), gap1 p q n hp hq hn, hbase]

theorem gap3 (p q L : ℝ)
    (hlocal :
      Tendsto (localQuotient p q) (nhdsWithin 0 (Set.Ioi 0)) (nhds L)) :
    Tendsto (fun n : ℕ => explicitRaabe p q (n + 1)) atTop (nhds L) := by
  have hcast : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
  have hinvZero : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1))
      atTop (nhds 0) := by
    simpa [one_div] using tendsto_inv_atTop_zero.comp hcast
  have hinvWithin : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1))
      atTop (nhdsWithin 0 (Set.Ioi 0)) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · exact hinvZero
    · exact Filter.Eventually.of_forall (fun n => by
        simp only [Set.mem_Ioi]
        positivity)
  apply (hlocal.comp hinvWithin).congr'
  filter_upwards [] with n
  unfold localQuotient explicitRaabe
  norm_num [Nat.cast_add, Nat.cast_one]
  have hnpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hn2pos : (0 : ℝ) < (n : ℝ) + 2 := by positivity
  field_simp [hnpos.ne', hn2pos.ne']

theorem gap4 (p q : ℝ) :
    Tendsto (localQuotient p q) (nhdsWithin 0 (Set.Ioi 0)) (nhds (p + q)) := by
  have hpowQuot : Tendsto (fun x : ℝ =>
      (Real.rpow (1 + x) p - 1) / x)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds p) := by
    have hd : HasDerivAt (fun y : ℝ => Real.rpow y p) p 1 := by
      convert Real.hasDerivAt_rpow_const (x := (1 : ℝ)) (p := p)
        (Or.inl one_ne_zero) using 1 <;> norm_num
    convert hd.tendsto_slope_zero_right using 1
    funext x
    simp [div_eq_mul_inv, mul_comm]
  have hfactor : Tendsto (fun x : ℝ => 1 + q * x / (1 + x))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
    have h : ContinuousAt (fun x : ℝ => 1 + q * x / (1 + x)) 0 := by
      fun_prop (disch := norm_num)
    convert h.tendsto.mono_left inf_le_left using 1 <;> norm_num
  have hqpart : Tendsto (fun x : ℝ => q / (1 + x))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds q) := by
    have h : ContinuousAt (fun x : ℝ => q / (1 + x)) 0 := by
      fun_prop (disch := norm_num)
    convert h.tendsto.mono_left inf_le_left using 1 <;> norm_num
  have hsum : Tendsto (fun x : ℝ =>
      ((Real.rpow (1 + x) p - 1) / x) * (1 + q * x / (1 + x)) +
        q / (1 + x)) (nhdsWithin 0 (Set.Ioi 0)) (nhds (p + q)) := by
    simpa using hpowQuot.mul hfactor |>.add hqpart
  apply hsum.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hxpos : 0 < x := by simpa only [Set.mem_Ioi] using hx
  have hx0 : x ≠ 0 := hxpos.ne'
  have hx1 : 1 + x ≠ 0 := by linarith
  unfold localQuotient
  field_simp [hx0, hx1]
  ring

theorem gap5 (p q : ℝ) (a : ℕ → ℝ)
    (hp : 0 < p) (hq : 0 < q)
    (ha : ∀ n ≥ 1, a n = term p q n) :
    Tendsto (fun n : ℕ => ratioRaabe a (n + 1)) atTop (nhds (p + q)) := by
  apply (gap3 p q (p + q) (gap4 p q)).congr'
  filter_upwards [] with n
  exact (gap2 p q a hp hq ha (n + 1) (by omega)).symm

theorem gap6 (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (h : 1 < p + q) :
    converges p q := by
  unfold converges
  exact (summable_nat_add_iff 1).mpr (summable_term_of_one_lt_add p q hq h)

theorem gap7 (p q : ℝ) (hp : 0 < p) (hq : 0 < q) :
    converges p q ↔ 1 < p + q := by
  constructor
  · intro hconv
    unfold converges at hconv
    exact one_lt_add_of_summable p q hq ((summable_nat_add_iff 1).mp hconv)
  · exact gap6 p q hp hq

end

end ProofGap.Exercise2602
