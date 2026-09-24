import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Asymptotics.Theta
import Mathlib.Topology.Algebra.InfiniteSum.Basic

open Filter
open scoped Topology

private theorem seriesConverges_iff (f : ℕ → ℝ) :
    ProofGap.SeriesConverges f ↔
      ∃ l, Tendsto (fun n => ∑ i ∈ Finset.range n, f i) atTop (𝓝 l) := by
  simp only [ProofGap.SeriesConverges, Summable, HasSum,
    SummationFilter.conditional_filter_eq_map_range, tendsto_map'_iff,
    Function.comp_def]

namespace ProofGap.Exercise2681

noncomputable section

def sign (n : ℕ) : ℝ := (-1 : ℝ) ^ (n - 1)

def term (p : ℝ) (n : ℕ) : ℝ :=
  sign n / Real.rpow (Real.sqrt n + sign n) p

def leadingTerm (p : ℝ) (n : ℕ) : ℝ :=
  sign n / Real.rpow n (p / 2)

def correction (p : ℝ) (n : ℕ) : ℝ :=
  p / Real.rpow n ((p + 1) / 2)

def remainder (p : ℝ) (n : ℕ) : ℝ :=
  term p n - (leadingTerm p n - correction p n)

def comparison (q : ℝ) (n : ℕ) : ℝ :=
  1 / Real.rpow n q

def ConditionallySummable (p : ℝ) : Prop :=
  ProofGap.SeriesConverges (fun n : ℕ => term p (n + 1)) ∧
    ¬ Summable (fun n : ℕ => |term p (n + 1)|)

private theorem abs_sign (n : ℕ) : |sign n| = 1 := by
  simp [sign]

private theorem neg_one_le_sign (n : ℕ) : -1 ≤ sign n := by
  have h : |sign n| ≤ 1 := by rw [abs_sign]
  exact (abs_le.mp h).1

private theorem sqrt_add_sign_pos {n : ℕ} (hn : 1 ≤ n) :
    0 < Real.sqrt n + sign n := by
  by_cases h1 : n = 1
  · subst n
    norm_num [sign]
  · have hn2 : 2 ≤ n := by omega
    have hsqrt : (1 : ℝ) < Real.sqrt n := by
      rw [Real.lt_sqrt (by norm_num)]
      norm_num
      omega
    linarith [neg_one_le_sign n]

private theorem term_factorization (p : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    term p n = leadingTerm p n *
      Real.rpow (1 + sign n / Real.sqrt n) (-p) := by
  have hsqrt : 0 < Real.sqrt n := Real.sqrt_pos.2 (by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn))
  have hsum : 0 < Real.sqrt n + sign n := sqrt_add_sign_pos hn
  have hfactor : 0 < 1 + sign n / Real.sqrt n := by
    have heq : Real.sqrt n + sign n =
        Real.sqrt n * (1 + sign n / Real.sqrt n) := by
      field_simp
    nlinarith
  have hsplit : Real.sqrt n + sign n =
      Real.sqrt n * (1 + sign n / Real.sqrt n) := by
    field_simp
  have hsqrt_rpow : (Real.sqrt n) ^ p = (n : ℝ) ^ (p / 2) := by
    rw [Real.sqrt_eq_rpow]
    calc
      ((n : ℝ) ^ (1 / 2 : ℝ)) ^ p = (n : ℝ) ^ ((1 / 2 : ℝ) * p) :=
        (Real.rpow_mul (by positivity : (0 : ℝ) ≤ n) _ _).symm
      _ = (n : ℝ) ^ (p / 2) := by ring_nf
  unfold term leadingTerm
  change sign n / (Real.sqrt n + sign n) ^ p =
    (sign n / (n : ℝ) ^ (p / 2)) *
      (1 + sign n / Real.sqrt n) ^ (-p)
  rw [hsplit, Real.mul_rpow hsqrt.le hfactor.le, hsqrt_rpow,
    Real.rpow_neg hfactor.le]
  have hA : (n : ℝ) ^ (p / 2) ≠ 0 :=
    ne_of_gt (Real.rpow_pos_of_pos (by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)) _)
  have hB : (1 + sign n / Real.sqrt n) ^ p ≠ 0 :=
    ne_of_gt (Real.rpow_pos_of_pos hfactor _)
  field_simp

private theorem rpow_linear_remainder_isBigO (p : ℝ) :
    (fun x : ℝ => (1 + x) ^ (-p) - (1 - p * x)) =O[𝓝[Set.Ici (-1 / 2)] (0 : ℝ)]
      (fun x : ℝ => x ^ 2) := by
  let s : Set ℝ := Set.Ici (-1 / 2)
  let f : ℝ → ℝ := fun x => (1 + x) ^ (-p)
  have hs : Convex ℝ s := convex_Ici _
  have h0s : (0 : ℝ) ∈ s := by
    dsimp [s]
    norm_num
  have hf : ContDiffOn ℝ 2 f s := by
    dsimp [f]
    exact (contDiffOn_const.add contDiffOn_id).rpow_const_of_ne
      (by
        intro x hx
        simp only [id_eq]
        have hx' : (-1 / 2 : ℝ) ≤ x := by simpa [s] using hx
        linarith)
  have hsnhds : s ∈ 𝓝 (0 : ℝ) := by
    apply Filter.mem_of_superset (Ioi_mem_nhds (show (-1 / 2 : ℝ) < 0 by norm_num))
    exact Set.Ioi_subset_Ici_self
  have hd : HasDerivAt f (-p) 0 := by
    dsimp [f]
    convert ((hasDerivAt_const (x := (0 : ℝ)) (c := (1 : ℝ))).add (hasDerivAt_id 0)).rpow_const
      (p := -p) (Or.inl (by norm_num)) using 1 <;> norm_num
  have hiter1 : iteratedDerivWithin 1 f s 0 = -p := by
    rw [iteratedDerivWithin_one, derivWithin_of_mem_nhds hsnhds]
    exact hd.deriv
  have hT1 (x : ℝ) : taylorWithinEval f 1 s 0 x = 1 - p * x := by
    rw [show 1 = 0 + 1 by omega, taylorWithinEval_succ]
    simp [f, hiter1]
    ring
  have hsmall :
      (fun x => f x - taylorWithinEval f 2 s 0 x) =o[𝓝[s] (0 : ℝ)]
        (fun x : ℝ => x ^ 2) := by
    simpa [sub_zero] using (taylor_isLittleO hs h0s hf)
  have hquad :
      (fun x => taylorWithinEval f 2 s 0 x - taylorWithinEval f 1 s 0 x) =O[𝓝[s] (0 : ℝ)]
        (fun x : ℝ => x ^ 2) := by
    have hc := Asymptotics.isBigO_const_mul_self
      (((2 : ℝ)⁻¹) * iteratedDerivWithin 2 f s 0)
      (fun x : ℝ => x ^ 2) (𝓝[s] (0 : ℝ))
    convert hc using 1
    funext x
    rw [show taylorWithinEval f 2 s 0 x =
        taylorWithinEval f 1 s 0 x +
          (((2 : ℝ)⁻¹ * x ^ 2) •
            iteratedDerivWithin 2 f s 0) by
      norm_num [taylorWithinEval_succ]]
    simp [smul_eq_mul]
    ring
  have hadd := hsmall.isBigO.add hquad
  change (fun x => f x - (1 - p * x)) =O[𝓝[s] (0 : ℝ)] (fun x : ℝ => x ^ 2)
  convert hadd using 1
  funext x
  rw [hT1]
  ring

private theorem sign_sq (n : ℕ) : sign n * sign n = 1 := by
  rw [← sq]
  simp [sign, ← pow_mul]

private theorem tendsto_comparison_succ {q : ℝ} (hq : 0 < q) :
    Tendsto (fun n : ℕ => comparison q (n + 1)) atTop (𝓝 0) := by
  have hbase : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have h := (tendsto_rpow_neg_atTop hq).comp hbase
  convert h using 1
  funext n
  unfold comparison
  change 1 / (((n + 1 : ℕ) : ℝ) ^ q) = (((n + 1 : ℕ) : ℝ) ^ (-q))
  rw [Real.rpow_neg (by positivity)]
  simp [one_div]

private theorem abs_sign_div_sqrt_succ (n : ℕ) :
    |sign (n + 1) / Real.sqrt (n + 1)| = comparison (1 / 2) (n + 1) := by
  rw [abs_div, abs_sign, abs_of_nonneg (Real.sqrt_nonneg _), Real.sqrt_eq_rpow]
  simp [comparison]

private theorem tendsto_sign_div_sqrt_succ :
    Tendsto (fun n : ℕ => sign (n + 1) / Real.sqrt (n + 1)) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  convert (tendsto_comparison_succ (q := (1 / 2 : ℝ)) (by norm_num)) using 1
  funext n
  rw [Real.norm_eq_abs, abs_sign_div_sqrt_succ]

private theorem tendsto_sign_div_sqrt_succ_within :
    Tendsto (fun n : ℕ => sign (n + 1) / Real.sqrt (n + 1)) atTop
      (𝓝[Set.Ici (-1 / 2)] 0) := by
  rw [tendsto_nhdsWithin_iff]
  refine ⟨tendsto_sign_div_sqrt_succ, ?_⟩
  have hev := tendsto_sign_div_sqrt_succ.eventually
    (Metric.ball_mem_nhds (0 : ℝ) (show 0 < (1 / 2 : ℝ) by norm_num))
  filter_upwards [hev] with n hn
  rw [Real.dist_eq] at hn
  simp only [sub_zero] at hn
  change (-1 / 2 : ℝ) ≤ sign (n + 1) / Real.sqrt (n + 1)
  convert (neg_le_of_abs_le (le_of_lt hn)) using 1 <;> ring

private theorem leading_mul_linear_eq_correction (p : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    leadingTerm p n * (p * (sign n / Real.sqrt n)) = correction p n := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hsqrt : 0 < Real.sqrt n := Real.sqrt_pos.2 hnpos
  have hden : (n : ℝ) ^ (p / 2) * Real.sqrt n = (n : ℝ) ^ ((p + 1) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hnpos]
    congr 1
    ring
  unfold leadingTerm correction
  change (sign n / (n : ℝ) ^ (p / 2)) * (p * (sign n / Real.sqrt n)) =
    p / (n : ℝ) ^ ((p + 1) / 2)
  have hA : (n : ℝ) ^ (p / 2) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hnpos _)
  have hS : Real.sqrt n ≠ 0 := ne_of_gt hsqrt
  have hC : (n : ℝ) ^ ((p + 1) / 2) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hnpos _)
  field_simp
  rw [sq, sign_sq n]
  simp only [one_mul]
  calc
    p * (n : ℝ) ^ ((p + 1) / 2) =
        p * ((n : ℝ) ^ (p / 2) * Real.sqrt n) := by rw [hden]
    _ = p * (n : ℝ) ^ (p / 2) * Real.sqrt n := by ring

private theorem comparison_mul_sign_div_sqrt_sq (p : ℝ) (n : ℕ) :
    comparison (p / 2) (n + 1) *
        (sign (n + 1) / Real.sqrt (n + 1)) ^ 2 =
      comparison (p / 2 + 1) (n + 1) := by
  have hnpos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  have hsqrt : 0 < Real.sqrt (n + 1) := Real.sqrt_pos.2 (by positivity)
  have hden : (((n + 1 : ℕ) : ℝ) ^ (p / 2)) * (n + 1 : ℕ) =
      (((n + 1 : ℕ) : ℝ) ^ (p / 2 + 1)) := by
    calc
      (((n + 1 : ℕ) : ℝ) ^ (p / 2)) * ((n + 1 : ℕ) : ℝ) =
          (((n + 1 : ℕ) : ℝ) ^ (p / 2)) * (((n + 1 : ℕ) : ℝ) ^ (1 : ℝ)) := by
            rw [Real.rpow_one]
      _ = (((n + 1 : ℕ) : ℝ) ^ (p / 2 + 1)) :=
        (Real.rpow_add hnpos _ _).symm
  unfold comparison
  change (1 / (((n + 1 : ℕ) : ℝ) ^ (p / 2))) *
      (sign (n + 1) / Real.sqrt (n + 1)) ^ 2 =
    1 / (((n + 1 : ℕ) : ℝ) ^ (p / 2 + 1))
  have hA : (((n + 1 : ℕ) : ℝ) ^ (p / 2)) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hnpos _)
  have hB : (((n + 1 : ℕ) : ℝ) ^ (p / 2 + 1)) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hnpos _)
  have hS : Real.sqrt (n + 1) ≠ 0 := ne_of_gt hsqrt
  have hsqrt_sq : (Real.sqrt (n + 1)) ^ 2 = ((n + 1 : ℕ) : ℝ) :=
    by simpa only [Nat.cast_add, Nat.cast_one] using
      (Real.sq_sqrt (show 0 ≤ (((n + 1 : ℕ) : ℝ)) by positivity))
  field_simp
  rw [sq, sign_sq (n + 1), hsqrt_sq]
  simp only [one_mul]
  rw [hden]
  change (((n + 1 : ℕ) : ℝ) ^ ((p + 2) / 2)) =
    (((n + 1 : ℕ) : ℝ) ^ (p / 2 + 1))
  exact congrArg (fun e : ℝ => (((n + 1 : ℕ) : ℝ) ^ e)) (by ring)

private theorem abs_leadingTerm_eq_comparison (p : ℝ) (n : ℕ) :
    |leadingTerm p n| = comparison (p / 2) n := by
  unfold leadingTerm comparison
  rw [abs_div, abs_sign]
  rw [show |Real.rpow (n : ℝ) (p / 2)| = Real.rpow (n : ℝ) (p / 2) from
    abs_of_nonneg (by
      change 0 ≤ ((n : ℝ) ^ (p / 2))
      exact Real.rpow_nonneg (Nat.cast_nonneg n) _)]

private theorem remainder_isBigO (p : ℝ) :
    Asymptotics.IsBigO atTop
      (fun n : ℕ => remainder p (n + 1))
      (fun n : ℕ => comparison (p / 2 + 1) (n + 1)) := by
  have herr := (rpow_linear_remainder_isBigO p).comp_tendsto
    tendsto_sign_div_sqrt_succ_within
  have hleading :
      (fun n : ℕ => leadingTerm p (n + 1)) =O[atTop]
        (fun n : ℕ => comparison (p / 2) (n + 1)) := by
    refine Asymptotics.IsBigO.of_bound 1 (Eventually.of_forall ?_)
    intro n
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_leadingTerm_eq_comparison]
    have hc : 0 ≤ comparison (p / 2) (n + 1) := by
      unfold comparison
      exact div_nonneg zero_le_one (by
        change 0 ≤ ((((n + 1 : ℕ) : ℝ)) ^ (p / 2))
        exact Real.rpow_nonneg (by positivity) _)
    rw [abs_of_nonneg hc, one_mul]
  have hmul := hleading.mul herr
  refine hmul.congr ?_ ?_
  · intro n
    have hfac := term_factorization p (n := n + 1) (by omega)
    have hcorr := leading_mul_linear_eq_correction p (n := n + 1) (by omega)
    change leadingTerm p (n + 1) *
        (Real.rpow (1 + sign (n + 1) / Real.sqrt (n + 1)) (-p) -
          (1 - p * (sign (n + 1) / Real.sqrt (n + 1)))) =
      remainder p (n + 1)
    unfold remainder
    rw [hfac, ← hcorr]
    simp only [Nat.add_comm, Nat.cast_add, Nat.cast_one]
    ring
  · intro n
    exact comparison_mul_sign_div_sqrt_sq p n

private theorem summable_comparison_succ {q : ℝ} (hq : 1 < q) :
    Summable (fun n : ℕ => comparison q (n + 1)) := by
  have h := Real.summable_one_div_nat_rpow.mpr hq
  have hs := (summable_nat_add_iff
    (f := fun n : ℕ => 1 / ((n : ℝ) ^ q)) 1).2 h
  change Summable (fun n : ℕ => 1 / (((n + 1 : ℕ) : ℝ) ^ q))
  simpa only [Nat.cast_add, Nat.cast_one] using hs

private theorem not_summable_comparison_succ {q : ℝ} (hq : q ≤ 1) :
    ¬ Summable (fun n : ℕ => comparison q (n + 1)) := by
  intro hs
  have hs' : Summable (fun n : ℕ => 1 / (((n + 1 : ℕ) : ℝ) ^ q)) := by
    change Summable (fun n : ℕ => comparison q (n + 1))
    exact hs
  have hall : Summable (fun n : ℕ => 1 / ((n : ℝ) ^ q)) :=
    (summable_nat_add_iff (f := fun n : ℕ => 1 / ((n : ℝ) ^ q)) 1).1
      (by simpa only [Nat.cast_add, Nat.cast_one] using hs')
  exact (not_lt_of_ge hq) (Real.summable_one_div_nat_rpow.mp hall)

private theorem antitone_comparison_succ {q : ℝ} (hq : 0 ≤ q) :
    Antitone (fun n : ℕ => comparison q (n + 1)) := by
  intro m n hmn
  unfold comparison
  change 1 / (((n + 1 : ℕ) : ℝ) ^ q) ≤ 1 / (((m + 1 : ℕ) : ℝ) ^ q)
  apply one_div_le_one_div_of_le (Real.rpow_pos_of_pos (by positivity) _)
  apply Real.rpow_le_rpow (by positivity) _ hq
  exact_mod_cast Nat.add_le_add_right hmn 1

private theorem leadingTerm_succ_eq (p : ℝ) (n : ℕ) :
    leadingTerm p (n + 1) =
      (-1 : ℝ) ^ n * comparison (p / 2) (n + 1) := by
  unfold leadingTerm sign comparison
  rw [Nat.add_sub_cancel]
  ring

private theorem leading_seriesConverges {p : ℝ} (hp : 0 < p) :
    ProofGap.SeriesConverges (fun n : ℕ => leadingTerm p (n + 1)) := by
  have hq : 0 < p / 2 := by linarith
  obtain ⟨l, hl⟩ :=
    (antitone_comparison_succ hq.le).tendsto_alternating_series_of_tendsto_zero
      (tendsto_comparison_succ hq)
  rw [seriesConverges_iff]
  refine ⟨l, ?_⟩
  simpa only [leadingTerm_succ_eq] using hl

private theorem not_summable_abs_leading {p : ℝ} (hp : p / 2 ≤ 1) :
    ¬ Summable (fun n : ℕ => |leadingTerm p (n + 1)|) := by
  intro h
  apply not_summable_comparison_succ hp
  exact (summable_congr fun n => abs_leadingTerm_eq_comparison p (n + 1)).1 h

private theorem summable_abs_leading {p : ℝ} (hp : 1 < p / 2) :
    Summable (fun n : ℕ => |leadingTerm p (n + 1)|) := by
  apply (summable_congr fun n => abs_leadingTerm_eq_comparison p (n + 1)).2
  exact summable_comparison_succ hp

private theorem tendsto_term_factor (p : ℝ) :
    Tendsto
      (fun n : ℕ => Real.rpow
        (1 + sign (n + 1) / Real.sqrt (n + 1)) (-p))
      atTop (𝓝 1) := by
  have hbase : Tendsto
      (fun n : ℕ => 1 + sign (n + 1) / Real.sqrt (n + 1)) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.add tendsto_sign_div_sqrt_succ
  have hc := (Real.continuousAt_rpow_const (1 : ℝ) (-p)
    (Or.inl one_ne_zero)).tendsto.comp hbase
  convert hc using 1 <;> norm_num

private theorem term_isTheta_leading (p : ℝ) :
    (fun n : ℕ => leadingTerm p (n + 1)) =Θ[atTop]
      (fun n : ℕ => term p (n + 1)) := by
  have hratio : Tendsto
      (fun n : ℕ => term p (n + 1) / leadingTerm p (n + 1))
      atTop (𝓝 1) := by
    convert tendsto_term_factor p using 1
    funext n
    have hfac := term_factorization p (n := n + 1) (by omega)
    have hsign : sign (n + 1) ≠ 0 := by simp [sign]
    have hden : Real.rpow (n + 1 : ℕ) (p / 2) ≠ 0 :=
      ne_of_gt (Real.rpow_pos_of_pos (by positivity) _)
    have hlead : leadingTerm p (n + 1) ≠ 0 := by
      unfold leadingTerm
      exact div_ne_zero hsign hden
    rw [hfac]
    field_simp
    simp only [Nat.cast_add, Nat.cast_one]
  exact Asymptotics.isTheta_of_div_tendsto_nhds_ne_zero hratio one_ne_zero

private theorem not_summable_term_of_half_le_one {p : ℝ} (hp : p / 2 ≤ 1) :
    ¬ Summable (fun n : ℕ => term p (n + 1)) := by
  intro ht
  have hl : Summable (fun n : ℕ => leadingTerm p (n + 1)) :=
    summable_of_isBigO_nat ht (term_isTheta_leading p).1
  exact not_summable_abs_leading hp (by
    simpa only [Real.norm_eq_abs] using hl.norm)

private theorem summable_correction {p : ℝ} (hp : 1 < p) :
    Summable (fun n : ℕ => correction p (n + 1)) := by
  have hq : 1 < (p + 1) / 2 := by linarith
  have h := (summable_comparison_succ hq).mul_left p
  apply (summable_congr fun n => ?_).1 h
  unfold correction comparison
  ring

private theorem summable_remainder {p : ℝ} (hp : 0 < p) :
    Summable (fun n : ℕ => remainder p (n + 1)) := by
  exact summable_of_isBigO_nat (summable_comparison_succ (by linarith))
    (remainder_isBigO p)

private theorem term_seriesConverges {p : ℝ} (hp : 1 < p) :
    ProofGap.SeriesConverges (fun n : ℕ => term p (n + 1)) := by
  have hl := leading_seriesConverges (lt_trans zero_lt_one hp)
  change Summable (fun n : ℕ => leadingTerm p (n + 1))
    (SummationFilter.conditional ℕ) at hl
  have hc : Summable (fun n : ℕ => correction p (n + 1))
      (SummationFilter.conditional ℕ) :=
    (summable_correction hp).mono_filter SummationFilter.le_atTop
  have hr : Summable (fun n : ℕ => remainder p (n + 1))
      (SummationFilter.conditional ℕ) :=
    (summable_remainder (lt_trans zero_lt_one hp)).mono_filter SummationFilter.le_atTop
  change Summable (fun n : ℕ => term p (n + 1)) (SummationFilter.conditional ℕ)
  have hsum := hr.add (hl.sub hc)
  apply (summable_congr fun n => ?_).1 hsum
  unfold remainder
  ring

private theorem summable_abs_term {p : ℝ} (hp : 2 < p) :
    Summable (fun n : ℕ => |term p (n + 1)|) := by
  have hla := summable_abs_leading (p := p) (by linarith)
  have hl : Summable (fun n : ℕ => leadingTerm p (n + 1)) := by
    apply Summable.of_norm
    simpa only [Real.norm_eq_abs] using hla
  have hc := summable_correction (lt_trans one_lt_two hp)
  have hr := summable_remainder (lt_trans zero_lt_two hp)
  have hterm : Summable (fun n : ℕ => term p (n + 1)) := by
    have hsum := hr.add (hl.sub hc)
    apply (summable_congr fun n => ?_).1 hsum
    unfold remainder
    ring
  simpa only [Real.norm_eq_abs] using hterm.norm

private theorem not_summable_abs_term {p : ℝ} (hp : p / 2 ≤ 1) :
    ¬ Summable (fun n : ℕ => |term p (n + 1)|) := by
  intro h
  apply not_summable_term_of_half_le_one hp
  apply Summable.of_norm
  simpa only [Real.norm_eq_abs] using h

private theorem not_summable_correction {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1) :
    ¬ Summable (fun n : ℕ => correction p (n + 1)) := by
  intro hc
  have hs := hc.mul_left p⁻¹
  have hcomp : Summable (fun n : ℕ => comparison ((p + 1) / 2) (n + 1)) := by
    apply (summable_congr fun n => ?_).1 hs
    unfold correction comparison
    field_simp
  exact not_summable_comparison_succ (by linarith) hcomp

theorem gap1 :
    ∀ p : ℝ, ∀ n : ℕ, 1 ≤ n →
      term p n = leadingTerm p n *
        Real.rpow (1 + sign n / Real.sqrt n) (-p) := by
  intro p n hn
  exact term_factorization p hn

theorem gap2 :
    ∀ p : ℝ,
      Asymptotics.IsBigO atTop
        (fun n : ℕ => remainder p (n + 1))
        (fun n : ℕ => comparison (p / 2 + 1) (n + 1)) := by
  exact remainder_isBigO

theorem gap3 :
    ∀ p : ℝ,
      Asymptotics.IsBigO atTop
        (fun n : ℕ =>
          term p (n + 1) -
            (leadingTerm p (n + 1) - correction p (n + 1)))
        (fun n : ℕ => comparison (p / 2 + 1) (n + 1)) := by
  intro p
  simpa only [remainder] using remainder_isBigO p

theorem gap4 :
    ∀ p : ℝ, 2 < p →
      Summable (fun n : ℕ => |term p (n + 1)|) := by
  intro p hp
  exact summable_abs_term hp

theorem gap5 :
    ∀ p : ℝ, p ≤ 0 →
      ¬ Summable (fun n : ℕ => term p (n + 1)) := by
  intro p hp
  exact not_summable_term_of_half_le_one (by linarith)

theorem gap6 :
    ∀ p : ℝ, 1 < p → p ≤ 2 →
      (ProofGap.SeriesConverges (fun n : ℕ => leadingTerm p (n + 1)) ∧
        ¬ Summable (fun n : ℕ => |leadingTerm p (n + 1)|)) := by
  intro p hp hp2
  exact ⟨leading_seriesConverges (lt_trans zero_lt_one hp),
    not_summable_abs_leading (by linarith)⟩

theorem gap7 :
    ∀ p : ℝ, 1 < p → p ≤ 2 →
      Summable (fun n : ℕ => correction p (n + 1)) := by
  intro p hp _
  exact summable_correction hp

theorem gap8 :
    ∀ p : ℝ, 1 < p → p ≤ 2 →
      Summable (fun n : ℕ => comparison (p / 2 + 1) (n + 1)) := by
  intro p hp _
  exact summable_comparison_succ (by linarith)

theorem gap9 :
    ∀ p : ℝ, 1 < p → p ≤ 2 → ConditionallySummable p := by
  intro p hp hp2
  exact ⟨term_seriesConverges hp, not_summable_abs_term (by linarith)⟩

theorem gap10 :
    ∀ p : ℝ, 0 < p → p ≤ 1 →
      ProofGap.SeriesConverges (fun n : ℕ => leadingTerm p (n + 1)) := by
  intro p hp _
  exact leading_seriesConverges hp

theorem gap11 :
    ∀ p : ℝ, 0 < p → p ≤ 1 →
      Summable (fun n : ℕ => remainder p (n + 1)) := by
  intro p hp _
  exact summable_remainder hp

theorem gap12 :
    ∀ p : ℝ, 0 < p → p ≤ 1 →
      ¬ Summable (fun n : ℕ => correction p (n + 1)) := by
  intro p hp hp1
  exact not_summable_correction hp hp1

theorem gap13 :
    ∀ p : ℝ, 0 < p → p ≤ 1 →
      ¬ Summable (fun n : ℕ => term p (n + 1)) := by
  intro p _ hp1
  exact not_summable_term_of_half_le_one (by linarith)

end

end ProofGap.Exercise2681


