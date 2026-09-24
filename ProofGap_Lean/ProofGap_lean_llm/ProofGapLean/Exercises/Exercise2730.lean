import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace ProofGap.Exercise2730

noncomputable section

open Filter

def factor (x : ℝ) (k : ℕ) : ℝ :=
  2 - Real.rpow x (1 / (k : ℝ))

def term (x : ℝ) (n : ℕ) : ℝ :=
  ∏ k ∈ Finset.range n, factor x (k + 1)

def neverZero (x : ℝ) : Prop :=
  ∀ k : ℕ, 1 ≤ k → factor x k ≠ 0

def reciprocalRemainder (n : ℕ) : ℝ :=
  let z := Real.rpow (Real.exp 1) (1 / ((n + 1 : ℕ) : ℝ)) - 1
  1 / (1 - z) - (1 + z)

def exponentialRemainder (n : ℕ) : ℝ :=
  Real.rpow (Real.exp 1) (1 / ((n + 1 : ℕ) : ℝ)) -
    1 - 1 / ((n + 1 : ℕ) : ℝ)

def raabeRemainder (n : ℕ) : ℝ :=
  term (Real.exp 1) (n + 1) / term (Real.exp 1) (n + 2) -
    (1 + 1 / ((n + 2 : ℕ) : ℝ))

private theorem term_succ (x : ℝ) (n : ℕ) :
    term x (n + 1) = term x n * factor x (n + 1) := by
  simp [term, Finset.prod_range_succ]

private theorem term_ne_zero (x : ℝ) (hz : neverZero x) (n : ℕ) :
    term x n ≠ 0 := by
  rw [term, Finset.prod_ne_zero_iff]
  intro k hk
  exact hz (k + 1) (by omega)

private theorem tendsto_reciprocal_nat_add (c : ℕ) :
    Tendsto (fun n : ℕ => 1 / ((n + c : ℕ) : ℝ)) atTop (nhds 0) := by
  have htop : Tendsto (fun n : ℕ => ((n + c : ℕ) : ℝ)) atTop atTop := by
    simpa only [Nat.cast_add] using
      tendsto_natCast_atTop_atTop.atTop_add
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (c : ℝ)) atTop (nhds c))
  simpa [one_div] using htop.inv_tendsto_atTop

private theorem tendsto_rpow_slope (x : ℝ) (hx : 0 < x) :
    Tendsto (fun t : ℝ => (Real.rpow x t - 1) / t)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (Real.log x)) := by
  have hd := (hasDerivAt_id (x := (0 : ℝ))).const_rpow hx
  simpa [one_div, div_eq_mul_inv, mul_comm] using hd.tendsto_slope_zero_right

private theorem raabe_expression_tendsto (x : ℝ) (hx : 0 < x) :
    Tendsto
      (fun n : ℕ =>
        ((n + 1 : ℕ) : ℝ) *
          (Real.rpow x (1 / ((n + 2 : ℕ) : ℝ)) - 1) /
            (2 - Real.rpow x (1 / ((n + 2 : ℕ) : ℝ))))
      atTop (nhds (Real.log x)) := by
  let t : ℕ → ℝ := fun n => 1 / ((n + 2 : ℕ) : ℝ)
  have ht0 : Tendsto t atTop (nhds 0) := by
    simpa [t] using tendsto_reciprocal_nat_add 2
  have htpos : ∀ n, 0 < t n := by
    intro n
    simp [t]
    positivity
  have ht : Tendsto t atTop (nhdsWithin 0 (Set.Ioi 0)) :=
    tendsto_nhdsWithin_iff.2 ⟨ht0, Eventually.of_forall htpos⟩
  have hslope : Tendsto (fun n => (Real.rpow x (t n) - 1) / t n)
      atTop (nhds (Real.log x)) :=
    (tendsto_rpow_slope x hx).comp ht
  have hrpow : Tendsto (fun n => Real.rpow x (t n)) atTop (nhds 1) := by
    have h := tendsto_const_nhds.rpow ht0 (Or.inl hx.ne')
    simpa using h
  have hden : Tendsto (fun n => 2 - Real.rpow x (t n)) atTop (nhds 1) := by
    convert tendsto_const_nhds.sub hrpow using 1 <;> norm_num
  have hscale : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ) * t n)
      atTop (nhds 1) := by
    have h := tendsto_add_mul_div_add_mul_atTop_nhds
      (𝕜 := ℝ) 1 2 1 (d := 1) one_ne_zero
    simpa [t, div_eq_mul_inv, mul_comm, add_comm] using h
  have h := (hscale.mul hslope).div hden (by norm_num)
  have h' : Tendsto
      ((fun n => ((n + 1 : ℕ) : ℝ) * t n *
        ((Real.rpow x (t n) - 1) / t n)) /
        (fun n => 2 - Real.rpow x (t n))) atTop (nhds (Real.log x)) := by
    simpa only [one_mul, div_one] using h
  apply h'.congr'
  filter_upwards with n
  dsimp [t]
  have hn : (0 : ℝ) < ((n + 2 : ℕ) : ℝ) := by positivity
  field_simp <;> ring

private noncomputable def pTerm (p : ℝ) (n : ℕ) : ℝ :=
  1 / Real.rpow ((n + 1 : ℕ) : ℝ) p

private theorem pTerm_pos (p : ℝ) (n : ℕ) : 0 < pTerm p n := by
  simp [pTerm]
  positivity

private theorem pTerm_raabe_limit (p : ℝ) :
    Tendsto
      (fun n : ℕ => ((n + 1 : ℕ) : ℝ) *
        (pTerm p n / pTerm p (n + 1) - 1))
      atTop (nhds p) := by
  have ht0 := tendsto_reciprocal_nat_add 1
  have ht : Tendsto (fun n : ℕ => 1 / ((n + 1 : ℕ) : ℝ))
      atTop (nhdsWithin 0 (Set.Ioi 0)) :=
    tendsto_nhdsWithin_iff.2 ⟨ht0, Eventually.of_forall
      (fun n => show 0 < 1 / ((n + 1 : ℕ) : ℝ) by positivity)⟩
  have hd := ((hasDerivAt_id (0 : ℝ)).const_add 1).rpow_const
    (p := p) (Or.inl (by norm_num [id] : (1 + id (0 : ℝ)) ≠ 0))
  have hslope : Tendsto (fun t : ℝ => (Real.rpow (1 + t) p - 1) / t)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds p) := by
    simpa [one_div, div_eq_mul_inv, mul_comm, add_comm] using
      hd.tendsto_slope_zero_right
  apply (hslope.comp ht).congr'
  filter_upwards with n
  have hn1 : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  have hn2 : (0 : ℝ) < ((n + 2 : ℕ) : ℝ) := by positivity
  have hbase : ((n + 2 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ) =
      1 + 1 / ((n + 1 : ℕ) : ℝ) := by
    field_simp
    push_cast
    ring
  rw [show pTerm p n / pTerm p (n + 1) =
      Real.rpow (1 + 1 / ((n + 1 : ℕ) : ℝ)) p by
    calc
      pTerm p n / pTerm p (n + 1) =
          Real.rpow ((n + 2 : ℕ) : ℝ) p /
            Real.rpow ((n + 1 : ℕ) : ℝ) p := by
              simp only [pTerm]
              field_simp
      _ = Real.rpow (((n + 2 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ)) p :=
        (Real.div_rpow hn2.le hn1.le p).symm
      _ = Real.rpow (1 + 1 / ((n + 1 : ℕ) : ℝ)) p := by rw [hbase]]
  change (Real.rpow (1 + 1 / ((n + 1 : ℕ) : ℝ)) p - 1) /
      (1 / ((n + 1 : ℕ) : ℝ)) =
    ((n + 1 : ℕ) : ℝ) *
      (Real.rpow (1 + 1 / ((n + 1 : ℕ) : ℝ)) p - 1)
  field_simp

private theorem shifted_harmonic_not_summable :
    ¬ Summable (fun n : ℕ => 1 / ((n + 1 : ℕ) : ℝ)) := by
  intro h
  have hbase : Summable (fun n : ℕ => 1 / (n : ℝ)) :=
    (summable_nat_add_iff 1).1 (by
      simpa only [Nat.cast_add, Nat.cast_one] using h)
  exact Real.not_summable_one_div_natCast hbase

private theorem neverZero_of_lt_four (x : ℝ) (hx : 0 < x) (hx4 : x < 4)
    (hx2 : x ≠ 2) : neverZero x := by
  intro k hk hzero
  have hrpow : Real.rpow x (1 / (k : ℝ)) = 2 := by
    simp only [factor] at hzero
    linarith
  by_cases hk1 : k = 1
  · subst k
    simp at hrpow
    exact hx2 hrpow
  · have hk2 : 2 ≤ k := by omega
    have hkpos : (0 : ℝ) < (k : ℝ) := by positivity
    have hexppos : (0 : ℝ) < 1 / (k : ℝ) := by positivity
    have hbase : Real.rpow x (1 / (k : ℝ)) <
        Real.rpow 4 (1 / (k : ℝ)) :=
      Real.rpow_lt_rpow hx.le hx4 hexppos
    have hexp : (1 / (k : ℝ)) ≤ (1 / 2 : ℝ) := by
      apply (div_le_div_iff₀ hkpos (by norm_num : (0 : ℝ) < 2)).2
      norm_num
      exact_mod_cast hk2
    have hmono : Real.rpow 4 (1 / (k : ℝ)) ≤ Real.rpow 4 (1 / 2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
    have hfour : Real.rpow 4 (1 / 2 : ℝ) = 2 := by
      calc
        Real.rpow 4 (1 / 2 : ℝ) = Real.sqrt 4 := (Real.sqrt_eq_rpow 4).symm
        _ = 2 := by
          convert Real.sqrt_sq (show (0 : ℝ) ≤ 2 by norm_num) using 1 <;> norm_num
    linarith

private theorem summable_of_raabe_limit_gt_one (f : ℕ → ℝ)
    (hfpos : ∀ᶠ n in atTop, 0 < f n) {L : ℝ}
    (hlim : Tendsto
      (fun n : ℕ => ((n + 1 : ℕ) : ℝ) * (f n / f (n + 1) - 1))
      atTop (nhds L))
    (hL : 1 < L) : Summable f := by
  let p : ℝ := (1 + L) / 2
  let q : ℝ := (p + L) / 2
  have hp1 : 1 < p := by dsimp [p]; linarith
  have hpL : p < L := by dsimp [p]; linarith
  have hpq : p < q := by dsimp [q]; linarith
  have hqL : q < L := by dsimp [q]; linarith
  have hF : ∀ᶠ n in atTop,
      q < ((n + 1 : ℕ) : ℝ) * (f n / f (n + 1) - 1) :=
    (tendsto_order.1 hlim).1 q hqL
  have hP : ∀ᶠ n in atTop,
      ((n + 1 : ℕ) : ℝ) * (pTerm p n / pTerm p (n + 1) - 1) < q :=
    (tendsto_order.1 (pTerm_raabe_limit p)).2 q hpq
  have hfpos' : ∀ᶠ n in atTop, 0 < f (n + 1) :=
    (tendsto_add_atTop_nat 1).eventually hfpos
  rcases eventually_atTop.1 (hfpos.and (hfpos'.and (hP.and hF))) with ⟨N, hN⟩
  have hratio : ∀ n, N ≤ n →
      pTerm p n / pTerm p (n + 1) < f n / f (n + 1) := by
    intro n hn
    have h := hN n hn
    have hnpos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
    nlinarith
  have hquot : Antitone (fun n : ℕ => f (n + N) / pTerm p (n + N)) := by
    apply antitone_nat_of_succ_le
    intro n
    have hfnext : 0 < f (n + N + 1) := (hN (n + N) (by omega)).2.1
    have hr := hratio (n + N) (by omega)
    apply (div_le_div_iff₀ (pTerm_pos p (n + 1 + N)) (pTerm_pos p (n + N))).2
    have hcross := (div_lt_div_iff₀ (pTerm_pos p (n + N + 1)) hfnext).1 hr
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, mul_comm] using hcross.le
  let C : ℝ := f N / pTerm p N
  have hC : 0 < C := div_pos (hN N le_rfl).1 (pTerm_pos p N)
  have hbound : ∀ n : ℕ, f (n + N) ≤ C * pTerm p (n + N) := by
    intro n
    have hq := hquot (Nat.zero_le n)
    have hq' : f (n + N) / pTerm p (n + N) ≤ f N / pTerm p N := by
      simpa using hq
    dsimp [C] at hq ⊢
    exact (div_le_iff₀ (pTerm_pos p (n + N))).1 hq'
  have hg0 : Summable (fun n : ℕ => 1 / Real.rpow n p) :=
    Real.summable_one_div_nat_rpow.mpr hp1
  have hg : Summable (pTerm p) := by
    have hshift := (summable_nat_add_iff 1).2 hg0
    apply hshift.congr
    intro n
    simp [pTerm, Nat.cast_add, Nat.cast_one, one_div]
  have hgShift : Summable (fun n : ℕ => pTerm p (n + N)) :=
    (summable_nat_add_iff N).2 hg
  have hfShift : Summable (fun n : ℕ => f (n + N)) :=
    (hgShift.mul_left C).of_nonneg_of_le
      (fun n => (hN (n + N) (by omega)).1.le) hbound
  exact (summable_nat_add_iff N).1 hfShift

private theorem not_summable_of_raabe_limit_lt_one (f : ℕ → ℝ)
    (hfpos : ∀ᶠ n in atTop, 0 < f n) {L : ℝ}
    (hlim : Tendsto
      (fun n : ℕ => ((n + 1 : ℕ) : ℝ) * (f n / f (n + 1) - 1))
      atTop (nhds L))
    (hL : L < 1) : ¬ Summable f := by
  let harmonic : ℕ → ℝ := fun n => 1 / ((n + 1 : ℕ) : ℝ)
  have hF : ∀ᶠ n in atTop,
      ((n + 1 : ℕ) : ℝ) * (f n / f (n + 1) - 1) < 1 :=
    (tendsto_order.1 hlim).2 1 hL
  have hfpos' : ∀ᶠ n in atTop, 0 < f (n + 1) :=
    (tendsto_add_atTop_nat 1).eventually hfpos
  rcases eventually_atTop.1 (hfpos.and (hfpos'.and hF)) with ⟨N, hN⟩
  have hratio : ∀ n, N ≤ n →
      f n / f (n + 1) < harmonic n / harmonic (n + 1) := by
    intro n hn
    have h := (hN n hn).2.2
    have hh : ((n + 1 : ℕ) : ℝ) *
        (harmonic n / harmonic (n + 1) - 1) = 1 := by
      dsimp [harmonic]
      field_simp
      norm_num
    have hnpos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
    nlinarith
  have hquot : Monotone (fun n : ℕ => f (n + N) / harmonic (n + N)) := by
    apply monotone_nat_of_le_succ
    intro n
    have hfnext : 0 < f (n + N + 1) := (hN (n + N) (by omega)).2.1
    have hr := hratio (n + N) (by omega)
    have hhpos : ∀ k, 0 < harmonic k := by intro k; dsimp [harmonic]; positivity
    apply (div_le_div_iff₀ (hhpos (n + N)) (hhpos (n + 1 + N))).2
    have hcross := (div_lt_div_iff₀ hfnext (hhpos (n + N + 1))).1 hr
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, mul_comm] using hcross.le
  intro hsum
  let C : ℝ := f N / harmonic N
  have hC : 0 < C := by
    dsimp [C, harmonic]
    exact div_pos (hN N le_rfl).1 (by positivity)
  have hbound : ∀ n : ℕ, C * harmonic (n + N) ≤ f (n + N) := by
    intro n
    have hq := hquot (Nat.zero_le n)
    have hq' : f N / harmonic N ≤ f (n + N) / harmonic (n + N) := by
      simpa using hq
    dsimp [C] at hq ⊢
    exact (le_div_iff₀ (by dsimp [harmonic]; positivity)).1 hq'
  have hfShift : Summable (fun n : ℕ => f (n + N)) :=
    (summable_nat_add_iff N).2 hsum
  have hscaled : Summable (fun n : ℕ => C * harmonic (n + N)) :=
    hfShift.of_nonneg_of_le
      (fun n => mul_nonneg hC.le (by dsimp [harmonic]; positivity)) hbound
  have hhShift : Summable (fun n : ℕ => harmonic (n + N)) := by
    have h := hscaled.mul_left C⁻¹
    apply h.congr
    intro n
    field_simp
  have hh : Summable harmonic := (summable_nat_add_iff N).1 hhShift
  exact shifted_harmonic_not_summable (by simpa [harmonic] using hh)

private theorem exp_one_rpow (t : ℝ) :
    Real.rpow (Real.exp 1) t = Real.exp t := by
  exact Real.exp_one_rpow t

private theorem exponential_remainder_isBigO :
    Asymptotics.IsBigO atTop exponentialRemainder
      (fun n : ℕ => 1 / (((n + 1 : ℕ) : ℝ) ^ 2)) := by
  let u : ℕ → ℝ := fun n => 1 / ((n + 1 : ℕ) : ℝ)
  have hu0 : Tendsto u atTop (nhds 0) := by
    simpa [u] using tendsto_reciprocal_nat_add 1
  have hraw : Asymptotics.IsBigO atTop
      (fun n => Real.exp (u n) - (1 + u n)) (fun n => (u n) ^ 2) := by
    simpa [Function.comp_def, Finset.sum_range_succ] using
      (Real.exp_sub_sum_range_isBigO_pow 2).comp_tendsto hu0
  apply hraw.congr'
  · filter_upwards with n
    simp [exponentialRemainder, u, Real.exp_one_rpow]
    ring
  · filter_upwards with n
    dsimp [u]
    field_simp

private theorem reciprocal_remainder_isBigO :
    Asymptotics.IsBigO atTop reciprocalRemainder
      (fun n : ℕ => 1 / (((n + 1 : ℕ) : ℝ) ^ 2)) := by
  let u : ℕ → ℝ := fun n => 1 / ((n + 1 : ℕ) : ℝ)
  let z : ℕ → ℝ := fun n => Real.exp (u n) - 1
  have hu0 : Tendsto u atTop (nhds 0) := by
    simpa [u] using tendsto_reciprocal_nat_add 1
  have hz0 : Tendsto z atTop (nhds 0) := by
    have hone : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1) :=
      tendsto_const_nhds
    simpa [z] using (Real.continuous_exp.continuousAt.tendsto.comp hu0).sub hone
  have hzO : Asymptotics.IsBigO atTop z u := by
    simpa [z, u, Function.comp_def, Finset.sum_range_succ] using
      (Real.exp_sub_sum_range_isBigO_pow 1).comp_tendsto hu0
  have hinv : Tendsto (fun n => (1 - z n)⁻¹) atTop (nhds 1) := by
    have hone : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1) :=
      tendsto_const_nhds
    simpa using (hone.sub hz0).inv₀ (by norm_num : (1 : ℝ) - 0 ≠ 0)
  have hraw := (hzO.mul hzO).mul (hinv.isBigO_one ℝ)
  apply hraw.congr'
  · filter_upwards [hz0.eventually
      (Metric.ball_mem_nhds (0 : ℝ) (show (0 : ℝ) < 1 by norm_num))]
      with n hn
    have hden : 1 - z n ≠ 0 := by
      have : |z n| < 1 := by simpa [Real.dist_eq] using hn
      linarith [le_abs_self (z n)]
    change z n * z n * (1 - z n)⁻¹ = reciprocalRemainder n
    have hrepr : reciprocalRemainder n = 1 / (1 - z n) - (1 + z n) := by
      simp [reciprocalRemainder, z, u, Real.exp_one_rpow]
    rw [hrepr]
    field_simp [hden] <;> ring
  · filter_upwards with n
    dsimp [u]
    field_simp

private theorem exp_one_neverZero : neverZero (Real.exp 1) :=
  neverZero_of_lt_four (Real.exp 1) (Real.exp_pos 1)
    (Real.exp_one_lt_three.trans (by norm_num))
    (ne_of_gt Real.exp_one_gt_two)

private theorem exp_half_lt_two : Real.exp (1 / 2 : ℝ) < 2 := by
  have hsquare : Real.exp (1 / 2 : ℝ) * Real.exp (1 / 2 : ℝ) = Real.exp 1 := by
    rw [← Real.exp_add]
    congr 1
    ring
  have he4 : Real.exp 1 < 4 := Real.exp_one_lt_three.trans (by norm_num)
  by_contra h
  have htwo : (2 : ℝ) ≤ Real.exp (1 / 2 : ℝ) := le_of_not_gt h
  nlinarith [sq_nonneg (Real.exp (1 / 2 : ℝ) - 2)]

private theorem exp_one_factor_pos (k : ℕ) (hk : 2 ≤ k) :
    0 < factor (Real.exp 1) k := by
  have hkpos : (0 : ℝ) < (k : ℝ) := by positivity
  have hexp : (1 / (k : ℝ)) ≤ (1 / 2 : ℝ) := by
    apply (div_le_div_iff₀ hkpos (by norm_num : (0 : ℝ) < 2)).2
    norm_num
    exact_mod_cast hk
  rw [factor, show Real.rpow (Real.exp 1) (1 / (k : ℝ)) =
    Real.exp (1 / (k : ℝ)) from Real.exp_one_rpow _]
  exact sub_pos.2 ((Real.exp_le_exp.2 hexp).trans_lt exp_half_lt_two)

private theorem exp_one_term_neg (n : ℕ) :
    term (Real.exp 1) (n + 1) < 0 := by
  induction n with
  | zero =>
      simp [term, factor, Real.exp_one_rpow, Real.exp_one_gt_two]
  | succ n ih =>
      rw [show term (Real.exp 1) (n + 1 + 1) =
          term (Real.exp 1) (n + 1) * factor (Real.exp 1) (n + 2) by
        simpa [Nat.add_assoc] using term_succ (Real.exp 1) (n + 1)]
      exact mul_neg_of_neg_of_pos ih (exp_one_factor_pos (n + 2) (by omega))

theorem gap1 :
    ∀ n : ℕ, 1 ≤ n → term 2 n = 0 := by
  intro n hn
  rw [term]
  apply Finset.prod_eq_zero (Finset.mem_range.2 hn)
  simp [factor]

theorem gap2 :
    Summable (fun n : ℕ => |term 2 (n + 1)|) := by
  simpa [gap1 (n := _)]

theorem gap3 (x : ℝ) (hx : 0 < x) (hx2 : x ≠ 2) :
    0 < x := by
  exact hx

theorem gap4 (x : ℝ) (hx : 0 < x) :
    Tendsto (fun n : ℕ => Real.rpow x (1 / ((n + 1 : ℕ) : ℝ)))
      atTop (nhds 1) := by
  have ht := tendsto_reciprocal_nat_add 1
  have h := tendsto_const_nhds.rpow ht (Or.inl hx.ne')
  simpa using h

theorem gap5 (x : ℝ) (hx : 0 < x) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → 0 ≤ term x n * term x (n + 1) := by
  have hev : ∀ᶠ n : ℕ in atTop,
      Real.rpow x (1 / ((n + 1 : ℕ) : ℝ)) < 2 :=
    (tendsto_order.1 (gap4 x hx)).2 2 (by norm_num)
  rcases eventually_atTop.1 hev with ⟨N, hN⟩
  refine ⟨N, fun n hn => ?_⟩
  rw [term_succ]
  have hf : 0 < factor x (n + 1) := by
    rw [factor]
    exact sub_pos.2 (hN n hn)
  calc
    term x n * (term x n * factor x (n + 1)) =
        (term x n) ^ 2 * factor x (n + 1) := by ring
    _ ≥ 0 := mul_nonneg (sq_nonneg _) hf.le

theorem gap6 (x : ℝ) (hx : 0 < x) :
    Summable (fun n : ℕ => term x (n + 1)) →
      Summable (fun n : ℕ => |term x (n + 1)|) := by
  intro h
  simpa [Real.norm_eq_abs] using h.norm

theorem gap7 (x : ℝ) (hx : 0 < x) (hz : neverZero x) :
    Tendsto
      (fun n : ℕ =>
        ((n + 1 : ℕ) : ℝ) *
          (term x (n + 1) / term x (n + 2) - 1))
      atTop
      (nhds (Real.log x)) := by
  apply (raabe_expression_tendsto x hx).congr'
  filter_upwards with n
  have ht : term x (n + 1) ≠ 0 := term_ne_zero x hz (n + 1)
  have hf : factor x (n + 2) ≠ 0 := hz (n + 2) (by omega)
  rw [show term x (n + 2) = term x (n + 1) * factor x (n + 2) by
    simpa [Nat.add_assoc] using term_succ x (n + 1)]
  simp only [factor] at hf ⊢
  field_simp [hf] <;> ring

theorem gap8 (x : ℝ) (hx : 0 < x) :
    Tendsto
      (fun n : ℕ =>
        ((n + 1 : ℕ) : ℝ) *
          (Real.rpow x (1 / ((n + 2 : ℕ) : ℝ)) - 1) /
            (2 - Real.rpow x (1 / ((n + 2 : ℕ) : ℝ))))
      atTop (nhds (Real.log x)) := by
  exact raabe_expression_tendsto x hx

theorem gap9 (x : ℝ) (hx : 0 < x) (hz : neverZero x) :
    Tendsto
      (fun n : ℕ =>
        ((n + 1 : ℕ) : ℝ) *
          (term x (n + 1) / term x (n + 2) - 1))
      atTop (nhds (Real.log x)) := by
  exact gap7 x hx hz

theorem gap10 (x : ℝ) (hx : 0 < x) (hlog : 1 < Real.log x) :
    Real.exp 1 < x := by
  rw [← Real.exp_log hx]
  exact Real.exp_lt_exp.2 hlog

private theorem abs_term_raabe_limit (x : ℝ) (hx : 0 < x) (hz : neverZero x) :
    Tendsto
      (fun n : ℕ => ((n + 1 : ℕ) : ℝ) *
        (|term x (n + 1)| / |term x (n + 2)| - 1))
      atTop (nhds (Real.log x)) := by
  rcases gap5 x hx with ⟨N, hN⟩
  apply (gap7 x hx hz).congr'
  filter_upwards [eventually_ge_atTop N] with n hn
  have ha : term x (n + 1) ≠ 0 := term_ne_zero x hz (n + 1)
  have hb : term x (n + 2) ≠ 0 := term_ne_zero x hz (n + 2)
  have hp : 0 < term x (n + 1) * term x (n + 2) :=
    lt_of_le_of_ne (hN (n + 1) (by omega))
      (Ne.symm (mul_ne_zero ha hb))
  have hdiv : 0 < term x (n + 1) / term x (n + 2) :=
    (div_pos_iff.2 (mul_pos_iff.1 hp))
  rw [← abs_div, abs_of_pos hdiv]

theorem gap11 (x : ℝ) (hx : Real.exp 1 < x) :
    Summable (fun n : ℕ => |term x (n + 1)|) := by
  have hx0 : 0 < x := (Real.exp_pos 1).trans hx
  by_cases hz : neverZero x
  · have hlog : 1 < Real.log x := by
      simpa using Real.log_lt_log (Real.exp_pos 1) hx
    apply summable_of_raabe_limit_gt_one (fun n => |term x (n + 1)|)
      (Eventually.of_forall fun n => abs_pos.2 (term_ne_zero x hz (n + 1)))
      (abs_term_raabe_limit x hx0 hz) hlog
  · rw [neverZero] at hz
    push_neg at hz
    obtain ⟨k, hk, hzero⟩ := hz
    apply (summable_nat_add_iff k).1
    have hterm : ∀ n : ℕ, term x (n + k + 1) = 0 := by
      intro n
      rw [term]
      have hmem : k - 1 ∈ Finset.range (n + k + 1) := by
        simp only [Finset.mem_range]
        omega
      apply Finset.prod_eq_zero hmem
      simpa [show k - 1 + 1 = k by omega] using hzero
    simpa [hterm]

theorem gap12 (x : ℝ) (hx0 : 0 < x) (hx : x < Real.exp 1) (hx2 : x ≠ 2) :
    ¬ Summable (fun n : ℕ => term x (n + 1)) := by
  have hx4 : x < 4 := hx.trans (Real.exp_one_lt_three.trans (by norm_num))
  have hz : neverZero x := neverZero_of_lt_four x hx0 hx4 hx2
  have hlog : Real.log x < 1 := by
    simpa using Real.log_lt_log hx0 hx
  have hnabs : ¬ Summable (fun n : ℕ => |term x (n + 1)|) :=
    not_summable_of_raabe_limit_lt_one (fun n => |term x (n + 1)|)
      (Eventually.of_forall fun n => abs_pos.2 (term_ne_zero x hz (n + 1)))
      (abs_term_raabe_limit x hx0 hz) hlog
  intro hsum
  exact hnabs (by simpa [Real.norm_eq_abs] using hsum.norm)

theorem gap13 :
    ∀ n : ℕ, 1 ≤ n →
      term (Real.exp 1) (n - 1) / term (Real.exp 1) n =
        1 / (2 - Real.rpow (Real.exp 1) (1 / (n : ℝ))) := by
  intro n hn
  have hn' : n - 1 + 1 = n := by omega
  have hrec := term_succ (Real.exp 1) (n - 1)
  rw [hn'] at hrec
  rw [hrec]
  have ht : term (Real.exp 1) (n - 1) ≠ 0 :=
    term_ne_zero (Real.exp 1) exp_one_neverZero (n - 1)
  have hf : factor (Real.exp 1) n ≠ 0 := exp_one_neverZero n hn
  simp only [factor] at hf ⊢
  field_simp [hf, ht]

theorem gap14 :
    ∀ n : ℕ, 1 ≤ n →
      1 / (2 - Real.rpow (Real.exp 1) (1 / (n : ℝ))) =
        1 / (1 - (Real.rpow (Real.exp 1) (1 / (n : ℝ)) - 1)) := by
  intro n hn
  congr 1
  ring

theorem gap15 :
    Asymptotics.IsBigO atTop reciprocalRemainder
      (fun n : ℕ => 1 / (((n + 1 : ℕ) : ℝ) ^ 2)) := by
  exact reciprocal_remainder_isBigO

theorem gap16 :
    Asymptotics.IsBigO atTop raabeRemainder
      (fun n : ℕ => 1 / (((n + 1 : ℕ) : ℝ) ^ 2)) := by
  have hrec := reciprocal_remainder_isBigO.comp_tendsto
    (tendsto_add_atTop_nat 1)
  have hexp := exponential_remainder_isBigO.comp_tendsto
    (tendsto_add_atTop_nat 1)
  have hsum := hrec.add hexp
  have hbound : Asymptotics.IsBigO atTop
      ((fun n : ℕ => 1 / (((n + 1 : ℕ) : ℝ) ^ 2)) ∘ fun a => a + 1)
      (fun n : ℕ => 1 / (((n + 1 : ℕ) : ℝ) ^ 2)) := by
    apply Asymptotics.IsBigO.of_bound 1
    filter_upwards with n
    have h1 : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) ^ 2 := by positivity
    have h2 : (0 : ℝ) < ((((n + 1 : ℕ) : ℝ) + 1) ^ 2) := by positivity
    have hle : 1 / ((((n + 1 : ℕ) : ℝ) + 1) ^ 2) ≤
        1 / (((n + 1 : ℕ) : ℝ) ^ 2) := by
      apply one_div_le_one_div_of_le h1
      have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      push_cast
      nlinarith
    simpa [Function.comp_def, Real.norm_eq_abs, abs_of_pos h1, abs_of_pos h2] using hle
  apply (hsum.trans hbound).congr'
  · filter_upwards with n
    change reciprocalRemainder (n + 1) + exponentialRemainder (n + 1) =
      raabeRemainder n
    have ht : term (Real.exp 1) (n + 1) ≠ 0 :=
      term_ne_zero (Real.exp 1) exp_one_neverZero (n + 1)
    have hf : factor (Real.exp 1) (n + 2) ≠ 0 :=
      exp_one_neverZero (n + 2) (by omega)
    have hratio : term (Real.exp 1) (n + 1) /
        term (Real.exp 1) (n + 2) =
          1 / (2 - Real.rpow (Real.exp 1) (1 / ((n + 2 : ℕ) : ℝ))) := by
      rw [show term (Real.exp 1) (n + 2) =
          term (Real.exp 1) (n + 1) * factor (Real.exp 1) (n + 2) by
        simpa [Nat.add_assoc] using term_succ (Real.exp 1) (n + 1)]
      simp only [factor] at hf ⊢
      field_simp [hf, ht]
    simp only [raabeRemainder]
    rw [hratio]
    simp only [reciprocalRemainder, exponentialRemainder]
    dsimp
    simp only [factor] at hf
    field_simp [hf]
    ring
  · filter_upwards with n
    rfl

theorem gap17 :
    Asymptotics.IsBigO atTop exponentialRemainder
      (fun n : ℕ => 1 / (((n + 1 : ℕ) : ℝ) ^ 2)) := by
  exact exponential_remainder_isBigO

theorem gap18 :
    Tendsto
      (fun n : ℕ =>
        ((n + 1 : ℕ) : ℝ) *
          (term (Real.exp 1) (n + 1) / term (Real.exp 1) (n + 2) - 1))
      atTop (nhds 1) := by
  simpa using gap9 (Real.exp 1) (Real.exp_pos 1) exp_one_neverZero

theorem gap19 :
    ¬ Summable (fun n : ℕ => term (Real.exp 1) (n + 1)) := by
  let c : ℕ → ℝ := fun n => -(((n + 1 : ℕ) : ℝ) * term (Real.exp 1) (n + 1))
  let d : ℕ → ℝ := fun n => c n / c (n + 1) - 1
  let g : ℕ → ℝ := fun n => 1 / (((n + 1 : ℕ) : ℝ) ^ 2)
  let q : ℕ → ℝ := fun n => ((n + 1 : ℕ) : ℝ) / ((n + 2 : ℕ) : ℝ)
  have hcpos : ∀ n, 0 < c n := by
    intro n
    dsimp [c]
    exact neg_pos.2 (mul_neg_of_pos_of_neg (by positivity) (exp_one_term_neg n))
  have hqT : Tendsto q atTop (nhds 1) := by
    have h := tendsto_add_mul_div_add_mul_atTop_nhds
      (𝕜 := ℝ) 1 2 1 (d := 1) one_ne_zero
    simpa [q, add_comm] using h
  have hqr : Asymptotics.IsBigO atTop
      (fun n => q n * raabeRemainder n) g := by
    have h := gap16.mul (hqT.isBigO_one ℝ)
    apply h.congr'
    · filter_upwards with n
      simp [mul_comm]
    · filter_upwards with n
      simp [g]
  have hsmall : Asymptotics.IsBigO atTop
      (fun n : ℕ => 1 / (((n + 2 : ℕ) : ℝ) ^ 2)) g := by
    apply Asymptotics.IsBigO.of_bound 1
    filter_upwards with n
    have h1 : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) ^ 2 := by positivity
    have h2 : (0 : ℝ) < ((n + 2 : ℕ) : ℝ) ^ 2 := by positivity
    have hle : 1 / (((n + 2 : ℕ) : ℝ) ^ 2) ≤
        1 / (((n + 1 : ℕ) : ℝ) ^ 2) := by
      apply one_div_le_one_div_of_le h1
      have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      push_cast
      nlinarith
    simpa [g, Real.norm_eq_abs, abs_of_pos h1, abs_of_pos h2] using hle
  have hdO : Asymptotics.IsBigO atTop d g := by
    apply (hqr.sub hsmall).congr'
    · filter_upwards with n
      have ht1 : term (Real.exp 1) (n + 1) ≠ 0 :=
        term_ne_zero (Real.exp 1) exp_one_neverZero (n + 1)
      have ht2 : term (Real.exp 1) (n + 2) ≠ 0 :=
        term_ne_zero (Real.exp 1) exp_one_neverZero (n + 2)
      dsimp [d, c, q, raabeRemainder]
      field_simp [ht1, ht2]
      push_cast
      ring
    · filter_upwards with n
      rfl
  have hg0 : Summable (fun n : ℕ => 1 / ((n : ℝ) ^ 2)) :=
    Real.summable_one_div_nat_pow.mpr (by omega)
  have hg : Summable g := by
    have hshift := (summable_nat_add_iff 1).2 hg0
    apply hshift.congr
    intro n
    simp [g, Nat.cast_add, Nat.cast_one]
  have hdSum : Summable d := summable_of_isBigO_nat hg hdO
  have hdLog : Summable (fun n => Real.log (1 + d n)) :=
    Real.summable_log_one_add_of_summable hdSum
  let P : ℝ := Real.exp (∑' n : ℕ, Real.log (1 + d n))
  have hprod : HasProd (fun n => 1 + d n) P := by
    apply Real.hasProd_of_hasSum_log
    · intro n
      dsimp [d]
      convert div_pos (hcpos n) (hcpos (n + 1)) using 1 <;> ring
    · exact hdLog.hasSum
  have hPpos : 0 < P := by
    dsimp [P]
    exact Real.exp_pos _
  have htel : ∀ n : ℕ,
      ∏ i ∈ Finset.range n, (1 + d i) = c 0 / c n := by
    intro n
    induction n with
    | zero => simp [hcpos 0 |>.ne']
    | succ n ih =>
        rw [Finset.prod_range_succ, ih]
        dsimp [d]
        field_simp [(hcpos 0).ne', (hcpos n).ne', (hcpos (n + 1)).ne']
        ring
  have hratioT : Tendsto (fun n => c 0 / c n) atTop (nhds P) := by
    apply hprod.tendsto_prod_nat.congr'
    exact Eventually.of_forall htel
  have hcT : Tendsto c atTop (nhds (c 0 / P)) := by
    have hinv := hratioT.inv₀ hPpos.ne'
    have hc0 : Tendsto (fun _ : ℕ => c 0) atTop (nhds (c 0)) :=
      tendsto_const_nhds
    have h : Tendsto (fun n => c 0 * (c 0 / c n)⁻¹) atTop
        (nhds (c 0 / P)) := by
      simpa [div_eq_mul_inv] using hc0.mul hinv
    apply h.congr'
    filter_upwards with n
    field_simp [(hcpos 0).ne', (hcpos n).ne']
  have hCpos : 0 < c 0 / P := div_pos (hcpos 0) hPpos
  intro hsum
  have hneg : Summable (fun n : ℕ => -term (Real.exp 1) (n + 1)) := hsum.neg
  have hlow : ∀ᶠ n in atTop, c 0 / P / 2 < c n :=
    (tendsto_order.1 hcT).1 (c 0 / P / 2) (by linarith)
  rcases eventually_atTop.1 hlow with ⟨N, hN⟩
  have hnegShift : Summable (fun n : ℕ => -term (Real.exp 1) (n + N + 1)) := by
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      (summable_nat_add_iff N).2 hneg
  have hhShift : Summable (fun n : ℕ => 1 / (((n + N + 1 : ℕ) : ℝ))) := by
    apply (hnegShift.mul_left (2 / (c 0 / P))).of_nonneg_of_le
    · intro n
      positivity
    · intro n
      have hl := hN (n + N) (by omega)
      have hden : (0 : ℝ) < ((n + N + 1 : ℕ) : ℝ) := by positivity
      have hC : 0 < c 0 / P := hCpos
      have hA : c 0 / P / 2 <
          ((n + N + 1 : ℕ) : ℝ) *
            (-term (Real.exp 1) (n + N + 1)) := by
        have hcshift : c (n + N) = ((n + N + 1 : ℕ) : ℝ) *
            (-term (Real.exp 1) (n + N + 1)) := by
          dsimp [c]
          ring
        rw [hcshift] at hl
        exact hl
      have hscaled : 1 ≤
          (2 / (c 0 / P)) *
            (-term (Real.exp 1) (n + N + 1)) * ((n + N + 1 : ℕ) : ℝ) := by
        have hstrict : 1 <
            (2 * (((n + N + 1 : ℕ) : ℝ) *
              (-term (Real.exp 1) (n + N + 1)))) / (c 0 / P) :=
          (lt_div_iff₀ hC).2 (by nlinarith)
        calc
          1 ≤ (2 * (((n + N + 1 : ℕ) : ℝ) *
              (-term (Real.exp 1) (n + N + 1)))) / (c 0 / P) := hstrict.le
          _ = (2 / (c 0 / P)) *
              (-term (Real.exp 1) (n + N + 1)) *
                ((n + N + 1 : ℕ) : ℝ) := by
            field_simp [hC.ne'] <;> ring
      exact (div_le_iff₀ hden).2 (by
        simpa [mul_assoc, mul_comm, mul_left_comm] using hscaled)
  have hh : Summable (fun n : ℕ => 1 / ((n + 1 : ℕ) : ℝ)) := by
    apply (summable_nat_add_iff N).1
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hhShift
  exact shifted_harmonic_not_summable hh

theorem gap20 (x : ℝ) (hx : 0 < x) :
    Summable (fun n : ℕ => |term x (n + 1)|) ↔
      x = 2 ∨ Real.exp 1 < x := by
  constructor
  · intro hsum
    by_cases hx2 : x = 2
    · exact Or.inl hx2
    by_cases hxe : Real.exp 1 < x
    · exact Or.inr hxe
    have hterm : Summable (fun n : ℕ => term x (n + 1)) := by
      apply Summable.of_norm
      simpa [Real.norm_eq_abs] using hsum
    rcases lt_or_eq_of_le (le_of_not_gt hxe) with hlt | heq
    · exact (gap12 x hx hlt hx2 hterm).elim
    · subst x
      exact (gap19 hterm).elim
  · rintro (rfl | hxe)
    · exact gap2
    · exact gap11 x hxe

end

end ProofGap.Exercise2730
