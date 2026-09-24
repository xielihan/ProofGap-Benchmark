import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.PSeries

namespace ProofGap.Exercise2603

noncomputable section

open Filter
open scoped BigOperators

def risingProduct (p : ℝ) (n : ℕ) : ℝ :=
  ∏ k ∈ Finset.range n, (p + k)

def term (p q : ℝ) (n : ℕ) : ℝ :=
  risingProduct p n / (Nat.factorial n : ℝ) / Real.rpow n q

def converges (p q : ℝ) : Prop :=
  Summable (fun n : ℕ => term p q (n + 1))

def ratioRaabe (a : ℕ → ℝ) (n : ℕ) : ℝ :=
  n * (a n / a (n + 1) - 1)

def explicitRaabe (p q : ℝ) (n : ℕ) : ℝ :=
  n * (Real.rpow (1 + 1 / (n : ℝ)) q * ((n + 1 : ℝ) / (p + n)) - 1)

def localQuotient (p q x : ℝ) : ℝ :=
  (Real.rpow (1 + x) (q + 1) / (1 + p * x) - 1) / x

private def coefficient (p : ℝ) (n : ℕ) : ℝ :=
  ((n : ℝ) / (p + n)) * (1 / Real.GammaSeq p n)

private theorem risingProduct_pos (p : ℝ) (hp : 0 < p) (n : ℕ) :
    0 < risingProduct p n := by
  unfold risingProduct
  apply Finset.prod_pos
  intro k hk
  have hk0 : (0 : ℝ) ≤ k := by positivity
  linarith

private theorem term_nonneg (p q : ℝ) (hp : 0 < p) (n : ℕ) :
    0 ≤ term p q n := by
  unfold term
  exact div_nonneg
    (div_nonneg (risingProduct_pos p hp n).le (by positivity))
    (Real.rpow_nonneg (by positivity) _)

private theorem term_eq_coefficient (p q : ℝ) (n : ℕ)
    (hp : 0 < p) (hn : 1 ≤ n) :
    term p q n = coefficient p n * Real.rpow n (p - q - 1) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hpnpos : 0 < p + (n : ℝ) := add_pos hp hnpos
  have hprod : risingProduct p (n + 1) =
      risingProduct p n * (p + (n : ℝ)) := by
    unfold risingProduct
    rw [Finset.prod_range_succ]
  have hprodNe : risingProduct p n ≠ 0 := (risingProduct_pos p hp n).ne'
  have hfacNe : (Nat.factorial n : ℝ) ≠ 0 := by positivity
  have hrpowPNe : Real.rpow n p ≠ 0 := (Real.rpow_pos_of_pos hnpos p).ne'
  have hrpowQNe : Real.rpow n q ≠ 0 := (Real.rpow_pos_of_pos hnpos q).ne'
  have hrpowOne : Real.rpow n 1 = (n : ℝ) := by
    simpa using Real.rpow_natCast (n : ℝ) 1
  have hmul : (n : ℝ) * Real.rpow n (p - q - 1) =
      Real.rpow n (1 + (p - q - 1)) := by
    calc
      (n : ℝ) * Real.rpow n (p - q - 1) =
          Real.rpow n 1 * Real.rpow n (p - q - 1) := by rw [hrpowOne]
      _ = Real.rpow n (1 + (p - q - 1)) :=
        (Real.rpow_add hnpos 1 (p - q - 1)).symm
  have hnegQ : Real.rpow n (-q) = 1 / Real.rpow n q := by
    convert Real.rpow_sub hnpos 0 q using 1 <;> simp
  have hpow : (n : ℝ) * Real.rpow n (p - q - 1) / Real.rpow n p =
      1 / Real.rpow n q := by
    rw [hmul]
    calc
      Real.rpow n (1 + (p - q - 1)) / Real.rpow n p =
          Real.rpow n ((1 + (p - q - 1)) - p) :=
        (Real.rpow_sub hnpos (1 + (p - q - 1)) p).symm
      _ = Real.rpow n (-q) := by congr 1; ring
      _ = 1 / Real.rpow n q := hnegQ
  unfold term coefficient
  change risingProduct p n / (Nat.factorial n : ℝ) / Real.rpow n q =
    ((n : ℝ) / (p + n) *
      (1 / (Real.rpow n p * (Nat.factorial n : ℝ) /
        (Finset.prod (Finset.range (n + 1)) (fun j => p + j))))) *
      Real.rpow n (p - q - 1)
  rw [show (Finset.prod (Finset.range (n + 1)) (fun j => p + j)) =
    risingProduct p (n + 1) by rfl, hprod]
  field_simp [hpnpos.ne', hprodNe, hfacNe, hrpowPNe, hrpowQNe] at hpow
  field_simp [hpnpos.ne', hprodNe, hfacNe, hrpowPNe, hrpowQNe]
  nlinarith

private theorem coefficient_tendsto (p : ℝ) (hp : 0 < p) :
    Tendsto (coefficient p) atTop (nhds (1 / Real.Gamma p)) := by
  have hdenAtTop : Tendsto (fun n : ℕ => (n : ℝ) + p) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
  have hsmall : Tendsto (fun n : ℕ => p / ((n : ℝ) + p))
      atTop (nhds 0) := tendsto_const_nhds.div_atTop hdenAtTop
  have hratio : Tendsto (fun n : ℕ => (n : ℝ) / (p + n))
      atTop (nhds 1) := by
    have hsub : Tendsto (fun n : ℕ => 1 - p / ((n : ℝ) + p))
        atTop (nhds 1) := by
      simpa using tendsto_const_nhds.sub hsmall
    apply hsub.congr'
    filter_upwards [] with n
    have hpos : 0 < p + (n : ℝ) := by positivity
    field_simp [hpos.ne']
    ring
  have hGammaNe : Real.Gamma p ≠ 0 := (Real.Gamma_pos_of_pos hp).ne'
  have hInvGamma : Tendsto (fun n : ℕ => 1 / Real.GammaSeq p n)
      atTop (nhds (1 / Real.Gamma p)) :=
    tendsto_const_nhds.div (Real.GammaSeq_tendsto_Gamma p) hGammaNe
  unfold coefficient
  simpa using hratio.mul hInvGamma

private theorem summable_term_of_lt (p q : ℝ) (hp : 0 < p) (hpq : p < q) :
    Summable (term p q) := by
  let e : ℝ := p - q - 1
  let C : ℝ := 1 / Real.Gamma p + 1
  have hlimitPos : 0 < 1 / Real.Gamma p :=
    one_div_pos.mpr (Real.Gamma_pos_of_pos hp)
  have hCPos : 0 < C := by dsimp [C]; linarith
  have hpseries : Summable (fun n : ℕ => Real.rpow (n : ℝ) e) :=
    Real.summable_nat_rpow.mpr (by dsimp [e]; linarith)
  have hmajorant : Summable (fun n : ℕ => C * Real.rpow (n : ℝ) e) :=
    hpseries.mul_left C
  have hupper : ∀ᶠ n : ℕ in atTop, coefficient p n < C :=
    (tendsto_order.1 (coefficient_tendsto p hp)).2 C
      (by dsimp [C]; linarith)
  apply Summable.of_norm_bounded_eventually hmajorant
  rw [Nat.cofinite_eq_atTop]
  filter_upwards [hupper, Filter.eventually_ge_atTop 1] with n hnCoeff hn
  rw [Real.norm_eq_abs, abs_of_nonneg (term_nonneg p q hp n),
    term_eq_coefficient p q n hp hn]
  exact mul_le_mul_of_nonneg_right hnCoeff.le
    (Real.rpow_nonneg (by positivity) _)

private theorem lt_of_summable_term (p q : ℝ) (hp : 0 < p)
    (hsum : Summable (term p q)) : p < q := by
  let e : ℝ := p - q - 1
  let c : ℝ := (1 / Real.Gamma p) / 2
  have hlimitPos : 0 < 1 / Real.Gamma p :=
    one_div_pos.mpr (Real.Gamma_pos_of_pos hp)
  have hcPos : 0 < c := by dsimp [c]; positivity
  have hlower : ∀ᶠ n : ℕ in atTop, c < coefficient p n :=
    (tendsto_order.1 (coefficient_tendsto p hp)).1 c
      (by dsimp [c]; linarith)
  have hscaled : Summable (fun n : ℕ => (1 / c) * term p q n) :=
    hsum.mul_left (1 / c)
  have hpseries : Summable (fun n : ℕ => Real.rpow (n : ℝ) e) := by
    apply Summable.of_norm_bounded_eventually hscaled
    rw [Nat.cofinite_eq_atTop]
    filter_upwards [hlower, Filter.eventually_ge_atTop 1] with n hnCoeff hn
    have hrpowNonneg : 0 ≤ Real.rpow (n : ℝ) e :=
      Real.rpow_nonneg (by positivity) _
    rw [Real.norm_eq_abs, abs_of_nonneg hrpowNonneg,
      term_eq_coefficient p q n hp hn]
    calc
      Real.rpow (n : ℝ) e = (1 / c) * (c * Real.rpow (n : ℝ) e) := by
        field_simp [hcPos.ne']
      _ ≤ (1 / c) * (coefficient p n * Real.rpow (n : ℝ) e) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hnCoeff.le hrpowNonneg) (by positivity)
  have hexponent := Real.summable_nat_rpow.mp hpseries
  dsimp [e] at hexponent
  linarith

theorem gap1 (p q : ℝ) (n : ℕ) (hp : 0 < p) (hq : 0 < q) (hn : 1 ≤ n) :
    term p q n / term p q (n + 1) =
      Real.rpow ((n + 1 : ℝ) / n) q * ((n + 1 : ℝ) / (p + n)) := by
  have hnpos : (0 : ℝ) < n := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hn1pos : (0 : ℝ) < n + 1 := by positivity
  have hprodNe : risingProduct p n ≠ 0 := (risingProduct_pos p hp n).ne'
  have hpnNe : p + (n : ℝ) ≠ 0 := (add_pos hp hnpos).ne'
  have hprodrec : risingProduct p (n + 1) =
      risingProduct p n * (p + (n : ℝ)) := by
    unfold risingProduct
    rw [Finset.prod_range_succ]
  have hpowN : Real.rpow n q ≠ 0 := (Real.rpow_pos_of_pos hnpos q).ne'
  have hpowN1 : Real.rpow (n + 1 : ℝ) q ≠ 0 :=
    (Real.rpow_pos_of_pos hn1pos q).ne'
  have hrpowDiv : Real.rpow ((n + 1 : ℝ) / n) q =
      Real.rpow (n + 1 : ℝ) q / Real.rpow n q :=
    Real.div_rpow hn1pos.le hnpos.le q
  unfold term
  rw [hprodrec, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
    hrpowDiv]
  field_simp [hprodNe, hpnNe, hpowN, hpowN1]

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
  simp only [Function.comp_apply, Nat.cast_add, Nat.cast_one]
  have hmpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hbasepos : 0 < 1 + 1 / ((n : ℝ) + 1) := by positivity
  have hrpowOne : Real.rpow (1 + 1 / ((n : ℝ) + 1)) 1 =
      1 + 1 / ((n : ℝ) + 1) := by
    simpa using Real.rpow_natCast (1 + 1 / ((n : ℝ) + 1)) 1
  have hpow : Real.rpow (1 + 1 / ((n : ℝ) + 1)) (q + 1) =
      Real.rpow (1 + 1 / ((n : ℝ) + 1)) q *
        (1 + 1 / ((n : ℝ) + 1)) := by
    calc
      Real.rpow (1 + 1 / ((n : ℝ) + 1)) (q + 1) =
          Real.rpow (1 + 1 / ((n : ℝ) + 1)) q *
            Real.rpow (1 + 1 / ((n : ℝ) + 1)) 1 :=
        Real.rpow_add hbasepos q 1
      _ = _ := by rw [hrpowOne]
  rw [hpow]
  by_cases hden : p + (n : ℝ) + 1 = 0
  · have hpform : p = -((n : ℝ) + 1) := by linarith
    have hzero : 1 + (-((n : ℝ) + 1)) * (1 / ((n : ℝ) + 1)) = 0 := by
      field_simp [hmpos.ne']
      norm_num
    rw [hpform, hzero]
    simp
  · field_simp [hmpos.ne', hden]
    ring

theorem gap4 (p q : ℝ) :
    Tendsto (localQuotient p q) (nhdsWithin 0 (Set.Ioi 0))
      (nhds (q + 1 - p)) := by
  have hpowQuot : Tendsto (fun x : ℝ =>
      (Real.rpow (1 + x) (q + 1) - 1) / x)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (q + 1)) := by
    have hd : HasDerivAt (fun y : ℝ => Real.rpow y (q + 1)) (q + 1) 1 := by
      convert Real.hasDerivAt_rpow_const (x := (1 : ℝ)) (p := q + 1)
        (Or.inl one_ne_zero) using 1 <;> norm_num
    convert hd.tendsto_slope_zero_right using 1
    funext x
    simp [div_eq_mul_inv, mul_comm]
  have hden : Tendsto (fun x : ℝ => 1 + p * x)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
    have h : ContinuousAt (fun x : ℝ => 1 + p * x) 0 := by fun_prop
    convert h.tendsto.mono_left inf_le_left using 1 <;> norm_num
  have hinvden : Tendsto (fun x : ℝ => 1 / (1 + p * x))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
    convert tendsto_const_nhds.div hden one_ne_zero using 1 <;> norm_num
  have hpden : Tendsto (fun x : ℝ => p / (1 + p * x))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds p) := by
    convert tendsto_const_nhds.div hden one_ne_zero using 1 <;> norm_num
  have hsum : Tendsto (fun x : ℝ =>
      ((Real.rpow (1 + x) (q + 1) - 1) / x) * (1 / (1 + p * x)) -
        p / (1 + p * x)) (nhdsWithin 0 (Set.Ioi 0))
      (nhds (q + 1 - p)) := by
    simpa using hpowQuot.mul hinvden |>.sub hpden
  have hdenNe : ∀ᶠ x : ℝ in nhdsWithin 0 (Set.Ioi 0), 1 + p * x ≠ 0 :=
    hden.eventually (eventually_ne_nhds one_ne_zero)
  apply hsum.congr'
  filter_upwards [self_mem_nhdsWithin, hdenNe] with x hx hxden
  have hxpos : 0 < x := by simpa only [Set.mem_Ioi] using hx
  have hxden' : 1 + x * p ≠ 0 := by simpa [mul_comm] using hxden
  unfold localQuotient
  let A : ℝ := Real.rpow (1 + x) (q + 1)
  change ((A - 1) / x) * (1 / (1 + p * x)) - p / (1 + p * x) =
    (A / (1 + p * x) - 1) / x
  field_simp [hxpos.ne', hxden, hxden']
  ring

theorem gap5 (p q : ℝ) (a : ℕ → ℝ)
    (hp : 0 < p) (hq : 0 < q)
    (ha : ∀ n ≥ 1, a n = term p q n) :
    Tendsto (fun n : ℕ => ratioRaabe a (n + 1)) atTop
      (nhds (q + 1 - p)) := by
  apply (gap3 p q (q + 1 - p) (gap4 p q)).congr'
  filter_upwards [] with n
  exact (gap2 p q a hp hq ha (n + 1) (by omega)).symm

theorem gap6 (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (h : p < q) :
    converges p q := by
  unfold converges
  exact (summable_nat_add_iff 1).mpr (summable_term_of_lt p q hp h)

theorem gap7 (p q : ℝ) :
    q + 1 - p > 1 ↔ q > p := by constructor <;> intro h <;> linarith

theorem gap8 (p q : ℝ) (hp : 0 < p) (hq : 0 < q) :
    converges p q ↔ p < q := by
  constructor
  · intro hconv
    unfold converges at hconv
    exact lt_of_summable_term p q hp ((summable_nat_add_iff 1).mp hconv)
  · exact gap6 p q hp hq

end

end ProofGap.Exercise2603
