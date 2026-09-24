import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

namespace ProofGap.Exercise3030

noncomputable section

open Filter
open scoped BigOperators Topology

def negativeIntegers : Set ℝ :=
  {x | ∃ m : ℕ, 1 ≤ m ∧ x = -(m : ℝ)}

def admissible (x : ℝ) : Prop := x ∉ negativeIntegers

def term (x : ℝ) (n : ℕ) : ℝ :=
  (n.factorial : ℝ) /
    ∏ k ∈ Finset.Icc 1 n, (x + (k : ℝ))

def partialSum (x : ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 n, term x k

def remainder (x : ℝ) (n : ℕ) : ℝ :=
  term x n * ((n + 1 : ℕ) : ℝ) / (x - 1)

def alpha (x : ℝ) (k : ℕ) : ℝ :=
  (1 - x) / (x + (k : ℝ))

def u (x : ℝ) (n : ℕ) : ℝ :=
  ∏ k ∈ Finset.Icc 1 n, (1 + alpha x k)

def convergenceDomain : Set ℝ :=
  {x | admissible x ∧ Summable (fun n : ℕ => term x (n + 1))}

private theorem add_nat_ne_zero (x : ℝ) (hx : admissible x)
    (k : ℕ) (hk : 1 ≤ k) : x + (k : ℝ) ≠ 0 := by
  intro hzero
  apply hx
  refine ⟨k, hk, ?_⟩
  push_cast at hzero
  linarith

private theorem partialSum_succ (x : ℝ) (n : ℕ) :
    partialSum x (n + 1) = partialSum x n + term x (n + 1) := by
  have hs : Finset.Icc 1 (n + 1) =
      insert (n + 1) (Finset.Icc 1 n) := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  rw [partialSum, partialSum, hs, Finset.sum_insert]
  · ring
  · simp

private theorem term_succ (x : ℝ) (n : ℕ) :
    term x (n + 1) = term x n * ((n + 1 : ℕ) : ℝ) /
      (x + ((n + 1 : ℕ) : ℝ)) := by
  have hs : Finset.Icc 1 (n + 1) =
      insert (n + 1) (Finset.Icc 1 n) := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  rw [term, term, hs, Finset.prod_insert]
  · rw [Nat.factorial_succ]
    push_cast
    rw [div_eq_mul_inv, div_eq_mul_inv, mul_inv_rev]
    ring
  · simp

private theorem remainder_step (x : ℝ) (hx : admissible x)
    (hx1 : x ≠ 1) (n : ℕ) :
    term x (n + 1) + remainder x (n + 1) = remainder x n := by
  rw [remainder, remainder, term_succ]
  have hd : x + ((n + 1 : ℕ) : ℝ) ≠ 0 :=
    add_nat_ne_zero x hx (n + 1) (by omega)
  have hsub : x - 1 ≠ 0 := sub_ne_zero.mpr hx1
  field_simp [hd, hsub]
  <;> norm_num [Nat.cast_add, Nat.cast_one]
  <;> ring

private theorem remainder_succ (x : ℝ) (hx1 : x ≠ 1) (n : ℕ) :
    remainder x (n + 1) = remainder x n *
      ((n + 2 : ℕ) : ℝ) / (x + ((n + 1 : ℕ) : ℝ)) := by
  rw [remainder, remainder, term_succ]
  have hsub : x - 1 ≠ 0 := sub_ne_zero.mpr hx1
  rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv]
  ring

private theorem partialSum_eq_sum_range (x : ℝ) (n : ℕ) :
    partialSum x n = ∑ k ∈ Finset.range n, term x (k + 1) := by
  induction n with
  | zero => simp [partialSum]
  | succ n ih =>
      rw [partialSum_succ, Finset.sum_range_succ, ih]

private theorem telescoping_identity (x : ℝ) (n : ℕ)
    (hx : admissible x) (hx1 : x ≠ 1) :
    1 / (x - 1) = partialSum x n + remainder x n := by
  induction n with
  | zero => simp [partialSum, remainder, term]
  | succ n ih =>
      rw [partialSum_succ]
      have hr := remainder_step x hx hx1 n
      linarith

private theorem remainder_prod (x : ℝ) (n : ℕ)
    (hx : admissible x) (hx1 : x ≠ 1) :
    remainder x n = 1 / (x - 1) *
      (∏ k ∈ Finset.Icc 1 n,
        ((k + 1 : ℕ) : ℝ) / (x + (k : ℝ))) := by
  induction n with
  | zero => simp [remainder, term]
  | succ n ih =>
      rw [remainder_succ x hx1 n, ih]
      have hd : x + ((n + 1 : ℕ) : ℝ) ≠ 0 :=
        add_nat_ne_zero x hx (n + 1) (by omega)
      have hs : Finset.Icc 1 (n + 1) =
          insert (n + 1) (Finset.Icc 1 n) := by
        ext k
        simp only [Finset.mem_Icc, Finset.mem_insert]
        omega
      rw [hs, Finset.prod_insert]
      · field_simp [hx1, hd]
      · simp

private theorem one_add_alpha_eq (x : ℝ) (k : ℕ)
    (hden : x + (k : ℝ) ≠ 0) :
    1 + alpha x k = ((k + 1 : ℕ) : ℝ) / (x + (k : ℝ)) := by
  unfold alpha
  field_simp [hden]
  push_cast
  ring

private theorem remainder_eq_u (x : ℝ) (n : ℕ)
    (hx : admissible x) (hx1 : x ≠ 1) :
    remainder x n = 1 / (x - 1) * u x n := by
  rw [remainder_prod x n hx hx1]
  apply congrArg (fun z : ℝ => 1 / (x - 1) * z)
  unfold u
  apply Finset.prod_congr rfl
  intro k hk
  apply (one_add_alpha_eq x k ?_).symm
  exact add_nat_ne_zero x hx k (Finset.mem_Icc.mp hk).1

private theorem gamma_den_eq (x : ℝ) (n : ℕ) :
    (∏ j ∈ Finset.range (n + 1), (x + (j : ℝ))) =
      x * ∏ k ∈ Finset.Icc 1 n, (x + (k : ℝ)) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.prod_range_succ, ih]
      have hs : Finset.Icc 1 (n + 1) =
          insert (n + 1) (Finset.Icc 1 n) := by
        ext k
        simp only [Finset.mem_Icc, Finset.mem_insert]
        omega
      rw [hs, Finset.prod_insert]
      · ring
      · simp

private def ratio (n : ℕ) : ℝ := ((n : ℝ) + 1) / (n : ℝ)

private def growth (x : ℝ) (n : ℕ) : ℝ := (n : ℝ) ^ (1 - x)

private def coefficient (x : ℝ) (n : ℕ) : ℝ :=
  x / (x - 1) * Real.GammaSeq x n * ratio n

private theorem remainder_eq_coefficient_mul_growth (x : ℝ) (n : ℕ)
    (hx : admissible x) (hx0 : x ≠ 0) (hx1 : x ≠ 1) (hn : 0 < n) :
    remainder x n = coefficient x n * growth x n := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hnR
  have hsub : x - 1 ≠ 0 := sub_ne_zero.mpr hx1
  have hprod : (∏ k ∈ Finset.Icc 1 n, (x + (k : ℝ))) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro k hk
    exact add_nat_ne_zero x hx k (Finset.mem_Icc.mp hk).1
  have hpow : (n : ℝ) ^ x * (n : ℝ) ^ (1 - x) = (n : ℝ) := by
    rw [← Real.rpow_add hnR]
    convert Real.rpow_one (n : ℝ) using 1 <;> ring
  unfold remainder term coefficient growth ratio Real.GammaSeq
  rw [gamma_den_eq]
  field_simp [hx0, hsub, hn0, hprod]
  norm_num [Nat.cast_add, Nat.cast_one]
  linear_combination -((n : ℝ) + 1) * hpow

private theorem admissible_of_one_lt (x : ℝ) (hx : 1 < x) : admissible x := by
  intro hneg
  rcases hneg with ⟨m, hm, rfl⟩
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  linarith

private theorem ratio_tendsto_one : Tendsto ratio atTop (𝓝 1) := by
  have hcast : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hinv : Tendsto (fun n : ℕ => ((n : ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hcast
  have hadd : Tendsto (fun n : ℕ => 1 + ((n : ℝ))⁻¹) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.add hinv
  apply hadd.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  unfold ratio
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  field_simp [hn0]

private theorem coefficient_tendsto (x : ℝ) :
    Tendsto (coefficient x) atTop
      (𝓝 (x / (x - 1) * Real.Gamma x)) := by
  have hconst : Tendsto (fun _ : ℕ => x / (x - 1)) atTop
      (𝓝 (x / (x - 1))) := tendsto_const_nhds
  have hgamma := Real.GammaSeq_tendsto_Gamma x
  have h := (hconst.mul hgamma).mul ratio_tendsto_one
  simpa [coefficient] using h

private theorem growth_tendsto_zero (x : ℝ) (hx : 1 < x) :
    Tendsto (growth x) atTop (𝓝 0) := by
  have hr := (tendsto_rpow_neg_atTop (sub_pos.mpr hx)).comp
    tendsto_natCast_atTop_atTop
  simpa [growth, show -(x - 1) = 1 - x by ring] using hr

private theorem growth_tendsto_atTop (x : ℝ) (hx : x < 1) :
    Tendsto (growth x) atTop atTop := by
  have hr := (tendsto_rpow_atTop (sub_pos.mpr hx)).comp
    tendsto_natCast_atTop_atTop
  simpa [growth] using hr

private theorem growth_nonneg (x : ℝ) (n : ℕ) : 0 ≤ growth x n := by
  exact Real.rpow_nonneg (Nat.cast_nonneg n) _

private theorem remainder_tendsto_zero_of_one_lt (x : ℝ) (hx : 1 < x) :
    Tendsto (remainder x) atTop (𝓝 0) := by
  have hadm := admissible_of_one_lt x hx
  have hx0 : x ≠ 0 := by linarith
  have hx1 : x ≠ 1 := ne_of_gt hx
  have hmul := (coefficient_tendsto x).mul (growth_tendsto_zero x hx)
  have hprod : Tendsto (fun n => coefficient x n * growth x n)
      atTop (𝓝 0) := by simpa using hmul
  apply hprod.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  exact (remainder_eq_coefficient_mul_growth x n hadm hx0 hx1 hn).symm

private theorem u_tendsto_zero_of_one_lt (x : ℝ) (hx : 1 < x) :
    Tendsto (u x) atTop (𝓝 0) := by
  have hadm := admissible_of_one_lt x hx
  have hx1 : x ≠ 1 := ne_of_gt hx
  have hmul := (tendsto_const_nhds :
      Tendsto (fun _ : ℕ => x - 1) atTop (𝓝 (x - 1))).mul
    (remainder_tendsto_zero_of_one_lt x hx)
  have hzero : (x - 1) * 0 = (0 : ℝ) := by ring
  rw [hzero] at hmul
  apply hmul.congr'
  exact Filter.Eventually.of_forall fun n => by
    change (x - 1) * remainder x n = u x n
    rw [remainder_eq_u x n hadm hx1]
    field_simp [sub_ne_zero.mpr hx1]

private theorem factor_pos_of_one_lt (x : ℝ) (hx : 1 < x)
    (k : ℕ) (hk : 1 ≤ k) : 0 < 1 + alpha x k := by
  have hdenpos : 0 < x + (k : ℝ) := by positivity
  rw [one_add_alpha_eq x k (ne_of_gt hdenpos)]
  positivity

private theorem u_pos_of_one_lt (x : ℝ) (hx : 1 < x) (n : ℕ) :
    0 < u x n := by
  unfold u
  apply Finset.prod_pos
  intro k hk
  exact factor_pos_of_one_lt x hx k (Finset.mem_Icc.mp hk).1

private theorem log_u_tendsto_atBot_of_one_lt (x : ℝ) (hx : 1 < x) :
    Tendsto (fun n => Real.log (u x n)) atTop atBot := by
  have huwithin : Tendsto (u x) atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr
      ⟨u_tendsto_zero_of_one_lt x hx,
        Filter.Eventually.of_forall (u_pos_of_one_lt x hx)⟩
  exact Real.tendsto_log_nhdsGT_zero.comp huwithin

private theorem gamma_ne_zero_of_admissible (x : ℝ)
    (hx : admissible x) (hx0 : x ≠ 0) : Real.Gamma x ≠ 0 := by
  apply Real.Gamma_ne_zero
  intro m hxm
  by_cases hm : m = 0
  · subst m
    apply hx0
    simpa using hxm
  · apply hx
    exact ⟨m, Nat.one_le_iff_ne_zero.mpr hm, hxm⟩

private theorem product_tendsto_atTop_of_coeff_pos
    {c g : ℕ → ℝ} {L : ℝ}
    (hc : Tendsto c atTop (𝓝 L)) (hL : 0 < L)
    (hg : Tendsto g atTop atTop) (hg0 : ∀ n, 0 ≤ g n) :
    Tendsto (fun n => c n * g n) atTop atTop := by
  have hcLowerStrict : ∀ᶠ n in atTop, L / 2 < c n :=
    (tendsto_order.1 hc).1 _ (by linarith)
  have hcLower : ∀ᶠ n in atTop, L / 2 ≤ c n :=
    hcLowerStrict.mono fun _ hn => hn.le
  have hlower : Tendsto (fun n => (L / 2) * g n) atTop atTop :=
    hg.const_mul_atTop (by linarith)
  refine tendsto_atTop_mono' atTop ?_ hlower
  filter_upwards [hcLower] with n hn
  exact mul_le_mul_of_nonneg_right hn (hg0 n)

private theorem remainder_tendsto_signed_of_lt_one (x : ℝ)
    (hx : admissible x) (hx1 : x < 1) :
    Tendsto (remainder x) atTop atTop ∨
      Tendsto (remainder x) atTop atBot := by
  by_cases hx0 : x = 0
  · subst x
    right
    have hcast : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
      tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
    have hneg : Tendsto (fun n : ℕ => -((n : ℝ) + 1)) atTop atBot :=
      tendsto_neg_atBot_iff.mpr hcast
    apply hneg.congr'
    filter_upwards with n
    have hterm : term 0 n = 1 := by
      induction n with
      | zero => simp [term]
      | succ n ih =>
          rw [term_succ, ih]
          have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
          norm_num [Nat.cast_add, Nat.cast_one, ne_of_gt hpos]
    rw [remainder, hterm]
    push_cast
    ring
  · have hxone : x ≠ 1 := ne_of_lt hx1
    let L : ℝ := x / (x - 1) * Real.Gamma x
    have hL0 : L ≠ 0 := by
      dsimp [L]
      exact mul_ne_zero (div_ne_zero hx0 (sub_ne_zero.mpr hxone))
        (gamma_ne_zero_of_admissible x hx hx0)
    have hc : Tendsto (coefficient x) atTop (𝓝 L) := by
      simpa [L] using coefficient_tendsto x
    have hg := growth_tendsto_atTop x hx1
    have heq : (fun n => remainder x n) =ᶠ[atTop]
        (fun n => coefficient x n * growth x n) := by
      filter_upwards [eventually_ge_atTop 1] with n hn
      exact remainder_eq_coefficient_mul_growth x n hx hx0 hxone hn
    rcases lt_or_gt_of_ne hL0 with hL | hL
    · right
      have hcneg : Tendsto (fun n => -coefficient x n) atTop (𝓝 (-L)) :=
        hc.neg
      have hpos : Tendsto (fun n => (-coefficient x n) * growth x n)
          atTop atTop :=
        product_tendsto_atTop_of_coeff_pos hcneg (neg_pos.mpr hL)
          hg (growth_nonneg x)
      have hbot : Tendsto (fun n => coefficient x n * growth x n)
          atTop atBot := by
        have hneg := tendsto_neg_atBot_iff.mpr hpos
        simpa only [neg_mul, neg_neg] using hneg
      exact hbot.congr' heq.symm
    · left
      have htop : Tendsto (fun n => coefficient x n * growth x n)
          atTop atTop :=
        product_tendsto_atTop_of_coeff_pos hc hL hg (growth_nonneg x)
      exact htop.congr' heq.symm

private theorem alpha_error_bigO (x : ℝ) :
    Asymptotics.IsBigO atTop
      (fun k : ℕ =>
        alpha x (k + 1) - (1 - x) / ((k + 1 : ℕ) : ℝ))
      (fun k : ℕ => 1 / (((k + 1 : ℕ) : ℝ) ^ 2)) := by
  rw [Asymptotics.isBigO_iff]
  refine ⟨2 * |(1 - x) * x|, ?_⟩
  have hcast : Tendsto (fun k : ℕ => (((k + 1 : ℕ) : ℝ))) atTop atTop := by
    simpa [Nat.cast_add, Nat.cast_one] using
      (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)
  filter_upwards [hcast.eventually_ge_atTop (2 * |x|)] with k hk
  let a : ℝ := ((k + 1 : ℕ) : ℝ)
  have ha : 0 < a := by dsimp [a]; positivity
  have hxa : a / 2 ≤ x + a := by
    have hxlower : -|x| ≤ x := neg_abs_le x
    dsimp [a] at hk ⊢
    nlinarith
  have hden : 0 < x + a := lt_of_lt_of_le (half_pos ha) hxa
  have heq : alpha x (k + 1) - (1 - x) / a =
      -((1 - x) * x) / ((x + a) * a) := by
    unfold alpha
    change (1 - x) / (x + a) - (1 - x) / a = _
    field_simp [ne_of_gt ha, ne_of_gt hden]
    ring
  rw [heq]
  change ‖-((1 - x) * x) / ((x + a) * a)‖ ≤
    2 * |(1 - x) * x| * ‖1 / a ^ 2‖
  simp only [Real.norm_eq_abs, abs_div, abs_neg, abs_mul,
    abs_of_pos hden, abs_of_pos ha, abs_pow]
  have hnum : 0 ≤ |(1 - x) * x| := abs_nonneg _
  have hdenprod : 0 < (x + a) * a := mul_pos hden ha
  have ha2 : 0 < a ^ 2 := sq_pos_of_pos ha
  rw [div_le_iff₀ hdenprod, div_eq_mul_inv]
  field_simp [ne_of_gt ha]
  have hfactor : 0 ≤ 2 * |(1 - x) * x| :=
    mul_nonneg (by norm_num) hnum
  have hmul := mul_le_mul_of_nonneg_left hxa hfactor
  simp only [abs_mul, abs_one, mul_one] at hmul ⊢
  convert hmul using 1 <;> ring

private theorem one_lt_of_remainder_tendsto (x τ : ℝ)
    (hx : admissible x) (hx1 : x ≠ 1)
    (hlim : Tendsto (remainder x) atTop (𝓝 τ)) : 1 < x := by
  rcases lt_or_gt_of_ne hx1 with hlt | hgt
  · rcases remainder_tendsto_signed_of_lt_one x hx hlt with htop | hbot
    · exact False.elim ((not_tendsto_nhds_of_tendsto_atTop htop τ) hlim)
    · exact False.elim ((not_tendsto_nhds_of_tendsto_atBot hbot τ) hlim)
  · exact hgt

private theorem term_nonneg_of_one_lt (x : ℝ) (hx : 1 < x) (n : ℕ) :
    0 ≤ term x n := by
  have hprod : 0 < ∏ k ∈ Finset.Icc 1 n, (x + (k : ℝ)) := by
    apply Finset.prod_pos
    intro k hk
    have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    linarith
  unfold term
  exact div_nonneg (Nat.cast_nonneg _) hprod.le

private theorem partialSum_tendsto_of_remainder_tendsto (x τ : ℝ)
    (hx : admissible x) (hx1 : x ≠ 1)
    (hlim : Tendsto (remainder x) atTop (𝓝 τ)) :
    Tendsto (partialSum x) atTop (𝓝 (1 / (x - 1) - τ)) := by
  have hconst : Tendsto (fun _ : ℕ => 1 / (x - 1)) atTop
      (𝓝 (1 / (x - 1))) := tendsto_const_nhds
  have ht := hconst.sub hlim
  apply ht.congr'
  exact Filter.Eventually.of_forall fun n => by
    have hi := telescoping_identity x n hx hx1
    linarith

private theorem hasSum_of_remainder_tendsto (x τ : ℝ)
    (hx : admissible x) (hx1 : x ≠ 1)
    (hlim : Tendsto (remainder x) atTop (𝓝 τ)) :
    HasSum (fun n : ℕ => term x (n + 1)) (1 / (x - 1) - τ) := by
  have hxgt := one_lt_of_remainder_tendsto x τ hx hx1 hlim
  have hps := partialSum_tendsto_of_remainder_tendsto x τ hx hx1 hlim
  have hrange : Tendsto
      (fun n : ℕ => ∑ k ∈ Finset.range n, term x (k + 1))
      atTop (𝓝 (1 / (x - 1) - τ)) := by
    apply hps.congr'
    exact Filter.Eventually.of_forall fun n =>
      partialSum_eq_sum_range x n
  exact (hasSum_iff_tendsto_nat_of_nonneg
    (fun n => term_nonneg_of_one_lt x hxgt (n + 1))
    (1 / (x - 1) - τ)).2 hrange

private theorem partialSum_tendsto_tsum_of_remainder_tendsto (x τ : ℝ)
    (hx : admissible x) (hx1 : x ≠ 1)
    (hlim : Tendsto (remainder x) atTop (𝓝 τ)) :
    Tendsto (partialSum x) atTop
      (𝓝 (∑' n : ℕ, term x (n + 1))) := by
  have hs := hasSum_of_remainder_tendsto x τ hx hx1 hlim
  have hcanon : Tendsto
      (fun n : ℕ => ∑ k ∈ Finset.range n, term x (k + 1))
      atTop (𝓝 (∑' n : ℕ, term x (n + 1))) :=
    hs.summable.hasSum.tendsto_sum_nat
  apply hcanon.congr'
  exact Filter.Eventually.of_forall fun n =>
    (partialSum_eq_sum_range x n).symm

private theorem not_summable_of_lt_one (x : ℝ)
    (hx : admissible x) (hx1 : x < 1) :
    ¬Summable (fun n : ℕ => term x (n + 1)) := by
  intro hs
  have hpsRange := hs.hasSum.tendsto_sum_nat
  have hps : Tendsto (partialSum x) atTop
      (𝓝 (∑' n : ℕ, term x (n + 1))) := by
    apply hpsRange.congr'
    exact Filter.Eventually.of_forall fun n =>
      (partialSum_eq_sum_range x n).symm
  have hxone : x ≠ 1 := ne_of_lt hx1
  have hconst : Tendsto (fun _ : ℕ => 1 / (x - 1)) atTop
      (𝓝 (1 / (x - 1))) := tendsto_const_nhds
  have hremRaw := hconst.sub hps
  have hrem : Tendsto (remainder x) atTop
      (𝓝 (1 / (x - 1) - ∑' n : ℕ, term x (n + 1))) := by
    apply hremRaw.congr'
    exact Filter.Eventually.of_forall fun n => by
      have hi := telescoping_identity x n hx hxone
      linarith
  rcases remainder_tendsto_signed_of_lt_one x hx hx1 with htop | hbot
  · exact (not_tendsto_nhds_of_tendsto_atTop htop _) hrem
  · exact (not_tendsto_nhds_of_tendsto_atBot hbot _) hrem

private theorem term_one (n : ℕ) : term 1 n = 1 / (((n + 1 : ℕ) : ℝ)) := by
  induction n with
  | zero => simp [term]
  | succ n ih =>
      rw [term_succ, ih]
      have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      have hn2 : (0 : ℝ) < (n : ℝ) + 2 := by positivity
      push_cast
      field_simp [ne_of_gt hn1, ne_of_gt hn2]
      ring

private theorem not_summable_term_one :
    ¬Summable (fun n : ℕ => term 1 (n + 1)) := by
  intro hs
  have htail : Summable (fun n : ℕ => 1 / (((n + 2 : ℕ) : ℝ))) :=
    hs.congr fun n => by
      convert term_one (n + 1) using 1 <;> norm_num [Nat.cast_add]
  apply Real.not_summable_one_div_natCast
  apply (summable_nat_add_iff 2).mp
  simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using htail

private theorem log_u_eq_sum (x : ℝ) (hx : 1 < x) (n : ℕ) :
    Real.log (u x n) =
      ∑ k ∈ Finset.Icc 1 n, Real.log (1 + alpha x k) := by
  unfold u
  rw [Real.log_prod]
  intro k hk
  exact ne_of_gt (factor_pos_of_one_lt x hx k (Finset.mem_Icc.mp hk).1)

private theorem series_eq_of_one_lt (x : ℝ) (hx : 1 < x) :
    (∑' n : ℕ, term x (n + 1)) = 1 / (x - 1) := by
  have hadm := admissible_of_one_lt x hx
  have hs := hasSum_of_remainder_tendsto x 0 hadm (ne_of_gt hx)
    (remainder_tendsto_zero_of_one_lt x hx)
  simpa using hs.tsum_eq

private theorem convergenceDomain_eq : convergenceDomain = Set.Ioi 1 := by
  ext x
  constructor
  · rintro ⟨hadm, hs⟩
    by_cases hxone : x = 1
    · subst x
      exact False.elim (not_summable_term_one hs)
    · rcases lt_or_gt_of_ne hxone with hlt | hgt
      · exact False.elim ((not_summable_of_lt_one x hadm hlt) hs)
      · exact hgt
  · intro hx
    have hadm := admissible_of_one_lt x hx
    exact ⟨hadm, (hasSum_of_remainder_tendsto x 0 hadm (ne_of_gt hx)
      (remainder_tendsto_zero_of_one_lt x hx)).summable⟩

theorem gap1 (x : ℝ) (hx : admissible x) :
    x ∉ negativeIntegers := by
  exact hx

theorem gap2 (x : ℝ) (n : ℕ) (hx : admissible x) (hx1 : x ≠ 1) :
    1 / (x - 1) = partialSum x n + remainder x n := by
  exact telescoping_identity x n hx hx1

theorem gap3 (x : ℝ) (hx : admissible x) (hx1 : x ≠ 1) :
    ∀ n : ℕ, remainder x n =
      term x n * ((n + 1 : ℕ) : ℝ) / (x - 1) := by
  intro n
  rfl

theorem gap4 (x : ℝ) (n : ℕ) (hx : admissible x) (hx1 : x ≠ 1) :
    term x n * ((n + 1 : ℕ) : ℝ) / (x - 1) =
      1 / (x - 1) *
        (∏ k ∈ Finset.Icc 1 n,
          ((k + 1 : ℕ) : ℝ) / (x + (k : ℝ))) := by
  change remainder x n = _
  exact remainder_prod x n hx hx1

theorem gap5 (x : ℝ) (hx : admissible x) (hx1 : x ≠ 1) :
    ∀ n : ℕ, remainder x n =
      1 / (x - 1) *
        (∏ k ∈ Finset.Icc 1 n,
          ((k + 1 : ℕ) : ℝ) / (x + (k : ℝ))) := by
  intro n
  exact remainder_prod x n hx hx1

theorem gap6 (x : ℝ) (hx : admissible x) (hx1 : x ≠ 1) :
    ∀ n : ℕ, remainder x n = 1 / (x - 1) * u x n := by
  intro n
  exact remainder_eq_u x n hx hx1

theorem gap7 (x : ℝ) :
    Asymptotics.IsBigO atTop
      (fun k : ℕ =>
        alpha x (k + 1) - (1 - x) / ((k + 1 : ℕ) : ℝ))
      (fun k : ℕ => 1 / (((k + 1 : ℕ) : ℝ) ^ 2)) := by
  exact alpha_error_bigO x

theorem gap8 (x τ : ℝ) (hx : admissible x) (hx1 : x ≠ 1)
    (hlim : Tendsto (remainder x) atTop (𝓝 τ)) :
    Tendsto (partialSum x) atTop
      (𝓝 (∑' n : ℕ, term x (n + 1))) := by
  exact partialSum_tendsto_tsum_of_remainder_tendsto x τ hx hx1 hlim

theorem gap9 (x τ : ℝ) (hx : admissible x) (hx1 : x ≠ 1)
    (hlim : Tendsto (remainder x) atTop (𝓝 τ)) :
    Tendsto (partialSum x) atTop
      (𝓝 (1 / (x - 1) - τ)) := by
  exact partialSum_tendsto_of_remainder_tendsto x τ hx hx1 hlim

theorem gap10 (x τ : ℝ) (hx : admissible x) (hx1 : x ≠ 1)
    (hlim : Tendsto (remainder x) atTop (𝓝 τ)) :
    Tendsto (fun n : ℕ => 1 / (x - 1) - remainder x n)
      atTop (𝓝 (1 / (x - 1) - τ)) := by
  exact tendsto_const_nhds.sub hlim

theorem gap11 (x τ : ℝ) (hx : admissible x) (hx1 : x ≠ 1)
    (hlim : Tendsto (remainder x) atTop (𝓝 τ)) :
    (∑' n : ℕ, term x (n + 1)) = 1 / (x - 1) - τ := by
  exact tendsto_nhds_unique
    (partialSum_tendsto_tsum_of_remainder_tendsto x τ hx hx1 hlim)
    (partialSum_tendsto_of_remainder_tendsto x τ hx hx1 hlim)

theorem gap12 (x : ℝ) (hx : 1 < x) (k : ℕ) (hk : 1 ≤ k) :
    0 < 1 + alpha x k := by
  exact factor_pos_of_one_lt x hx k hk

theorem gap13 (x : ℝ) (hx : 1 < x) (k : ℕ) (hk : 1 ≤ k) :
    1 + alpha x k < 1 := by
  have hden : 0 < x + (k : ℝ) := by positivity
  unfold alpha
  have hq : (1 - x) / (x + (k : ℝ)) < 0 :=
    div_neg_of_neg_of_pos (sub_neg.mpr hx) hden
  linarith

theorem gap14 (x : ℝ) (hx : 1 < x) : (0 : ℝ) < 1 := by
  norm_num

theorem gap15 (x : ℝ) (hx : 1 < x) (n : ℕ) :
    Real.log (u x n) =
      ∑ k ∈ Finset.Icc 1 n, Real.log (1 + alpha x k) := by
  exact log_u_eq_sum x hx n

theorem gap16 (x : ℝ) (hx : 1 < x) :
    Tendsto
      (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, Real.log (1 + alpha x k))
      atTop atBot := by
  have h := log_u_tendsto_atBot_of_one_lt x hx
  apply h.congr'
  exact Filter.Eventually.of_forall fun n => log_u_eq_sum x hx n

theorem gap17 (x : ℝ) (hx : 1 < x) :
    Tendsto (fun n : ℕ => Real.log (u x n)) atTop atBot := by
  exact log_u_tendsto_atBot_of_one_lt x hx

theorem gap18 (x : ℝ) (hx : 1 < x) :
    Tendsto (u x) atTop (𝓝 0) := by
  exact u_tendsto_zero_of_one_lt x hx

theorem gap19 (x : ℝ) (hx : 1 < x) :
    Tendsto (remainder x) atTop (𝓝 0) := by
  exact remainder_tendsto_zero_of_one_lt x hx

theorem gap20 (x : ℝ) (hx : 1 < x) :
    (∑' n : ℕ, term x (n + 1)) = 1 / (x - 1) := by
  exact series_eq_of_one_lt x hx

theorem gap21 (x : ℝ) (hx : admissible x) (hx1 : x < 1) :
    Tendsto (remainder x) atTop atTop ∨
      Tendsto (remainder x) atTop atBot := by
  exact remainder_tendsto_signed_of_lt_one x hx hx1

theorem gap22 (x : ℝ) (hx : admissible x) (hx1 : x < 1) :
    ¬Summable (fun n : ℕ => term x (n + 1)) := by
  exact not_summable_of_lt_one x hx hx1

theorem gap23 (N : ℕ) :
    partialSum 1 N =
      ∑ k ∈ Finset.Icc 1 N, (1 : ℝ) / ((k + 1 : ℕ) : ℝ) := by
  unfold partialSum
  apply Finset.sum_congr rfl
  intro k hk
  exact term_one k

theorem gap24 :
    ¬Summable (fun n : ℕ => term 1 (n + 1)) := by
  exact not_summable_term_one

theorem gap25 : convergenceDomain = Set.Ioi 1 := by
  exact convergenceDomain_eq

theorem gap26 (x : ℝ) (hx : 1 < x) :
    (∑' n : ℕ, term x (n + 1)) = 1 / (x - 1) := by
  exact series_eq_of_one_lt x hx

end

end ProofGap.Exercise3030
