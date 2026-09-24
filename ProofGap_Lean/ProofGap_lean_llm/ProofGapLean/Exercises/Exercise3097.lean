import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Topology.Algebra.InfiniteSum.Basic

namespace ProofGap.Exercise3097

noncomputable section

open Filter
open scoped Topology

def reciprocalPower (s : ℝ) (n : ℕ) : ℝ :=
  1 / Real.rpow (n : ℝ) s

def q (s : ℝ) (n : ℕ) : ℝ :=
  if n % 3 = 2 then (1 - reciprocalPower s n) ^ 2
  else 1 + reciprocalPower s n

def qDeviation (s : ℝ) (n : ℕ) : ℝ :=
  q s n - 1

def alphaStar (s : ℝ) (n : ℕ) : ℝ :=
  if n = 0 then 0
  else
    let k := (n - 1) / 4
    if (n - 1) % 4 = 0 then reciprocalPower s (1 + 3 * k)
    else if (n - 1) % 4 = 1 then -reciprocalPower s (2 + 3 * k)
    else if (n - 1) % 4 = 2 then -reciprocalPower s (2 + 3 * k)
    else reciprocalPower s (3 + 3 * k)

def p (s : ℝ) (n : ℕ) : ℝ :=
  1 + alphaStar s n

def beta (s : ℝ) (k : ℕ) : ℝ :=
  reciprocalPower s (1 + 3 * k) -
    2 * reciprocalPower s (2 + 3 * k) +
    reciprocalPower s (3 + 3 * k)

def betaBound (s : ℝ) (k : ℕ) : ℝ :=
  2 * s * (s + 1) / Real.rpow (3 * (k : ℝ) + 1) (s + 2)

def SummableFromOne (f : ℕ → ℝ) : Prop :=
  Summable (fun k : ℕ => f (k + 1)) (SummationFilter.conditional ℕ)

def AbsolutelySummableFromOne (f : ℕ → ℝ) : Prop :=
  SummableFromOne (fun n => |f n|)

def ConditionallySummableFromOne (f : ℕ → ℝ) : Prop :=
  SummableFromOne f ∧ ¬AbsolutelySummableFromOne f

private theorem summable_conditional_iff {u : ℕ → ℝ} :
    Summable u (SummationFilter.conditional ℕ) ↔
      ∃ l : ℝ,
        Tendsto (fun n : ℕ => ∑ k ∈ Finset.range n, u k) atTop (𝓝 l) := by
  simp only [Summable, HasSum, SummationFilter.conditional_filter_eq_map_range,
    Filter.tendsto_map'_iff]
  constructor
  · rintro ⟨l, hl⟩
    exact ⟨l, by simpa [Function.comp_def] using hl⟩
  · rintro ⟨l, hl⟩
    exact ⟨l, by simpa [Function.comp_def] using hl⟩

private theorem tendsto_zero_of_summable_conditional {u : ℕ → ℝ}
    (hu : Summable u (SummationFilter.conditional ℕ)) :
    Tendsto u atTop (𝓝 0) := by
  rcases summable_conditional_iff.mp hu with ⟨l, hl⟩
  have hdiff := (hl.comp (Filter.tendsto_add_atTop_nat 1)).sub hl
  simpa [Finset.sum_range_succ] using hdiff

private theorem summable_of_nonneg_conditional {u : ℕ → ℝ}
    (hu0 : ∀ n, 0 ≤ u n)
    (hu : Summable u (SummationFilter.conditional ℕ)) : Summable u := by
  rw [summable_iff_not_tendsto_nat_atTop_of_nonneg hu0]
  intro htop
  rcases summable_conditional_iff.mp hu with ⟨l, hl⟩
  obtain ⟨n, hn, hn'⟩ :=
    ((tendsto_atTop.1 htop (l + 1)).and
      (hl.eventually_lt_const (lt_add_one l))).exists
  linarith

private theorem summable_conditional_nat_add {u : ℕ → ℝ}
    (hu : Summable u (SummationFilter.conditional ℕ)) (N : ℕ) :
    Summable (fun n : ℕ => u (n + N)) (SummationFilter.conditional ℕ) := by
  rcases summable_conditional_iff.mp hu with ⟨l, hl⟩
  apply summable_conditional_iff.mpr
  refine ⟨l - ∑ k ∈ Finset.range N, u k, ?_⟩
  have hshift := hl.comp (Filter.tendsto_add_atTop_nat N)
  convert hshift.sub tendsto_const_nhds using 1
  funext n
  simp only [Function.comp_apply]
  rw [show (∑ k ∈ Finset.range n, u (k + N)) =
      ∑ k ∈ Finset.range n, u (N + k) by
    apply Finset.sum_congr rfl
    intro k hk
    rw [Nat.add_comm]]
  rw [Nat.add_comm n N, Finset.sum_range_add]
  ring

private theorem tendsto_of_tendsto_four_residue {F : ℕ → ℝ} {l : ℝ}
    (h0 : Tendsto (fun k : ℕ => F (4 * k)) atTop (𝓝 l))
    (h1 : Tendsto (fun k : ℕ => F (4 * k + 1)) atTop (𝓝 l))
    (h2 : Tendsto (fun k : ℕ => F (4 * k + 2)) atTop (𝓝 l))
    (h3 : Tendsto (fun k : ℕ => F (4 * k + 3)) atTop (𝓝 l)) :
    Tendsto F atTop (𝓝 l) := by
  rw [Metric.tendsto_atTop] at h0 h1 h2 h3 ⊢
  intro ε hε
  obtain ⟨N0, hN0⟩ := h0 ε hε
  obtain ⟨N1, hN1⟩ := h1 ε hε
  obtain ⟨N2, hN2⟩ := h2 ε hε
  obtain ⟨N3, hN3⟩ := h3 ε hε
  let N : ℕ := max N0 (max N1 (max N2 N3))
  refine ⟨4 * N, fun n hn => ?_⟩
  have hmod : n % 4 < 4 := Nat.mod_lt n (by omega)
  have hdiv := Nat.mod_add_div n 4
  have hnEq : n = 4 * (n / 4) + n % 4 := by omega
  have hk : N ≤ n / 4 := by omega
  have hk0 : N0 ≤ n / 4 := by dsimp [N] at hk; omega
  have hk1 : N1 ≤ n / 4 := by dsimp [N] at hk; omega
  have hk2 : N2 ≤ n / 4 := by dsimp [N] at hk; omega
  have hk3 : N3 ≤ n / 4 := by dsimp [N] at hk; omega
  interval_cases hcase : n % 4
  · have hnform : n = 4 * (n / 4) := by omega
    rw [hnform]
    exact hN0 (n / 4) hk0
  · have hnform : n = 4 * (n / 4) + 1 := by omega
    rw [hnform]
    exact hN1 (n / 4) hk1
  · have hnform : n = 4 * (n / 4) + 2 := by omega
    rw [hnform]
    exact hN2 (n / 4) hk2
  · have hnform : n = 4 * (n / 4) + 3 := by omega
    rw [hnform]
    exact hN3 (n / 4) hk3

private theorem tendsto_of_tendsto_three_residue {F : ℕ → ℝ} {l : ℝ}
    (h0 : Tendsto (fun k : ℕ => F (3 * k)) atTop (𝓝 l))
    (h1 : Tendsto (fun k : ℕ => F (3 * k + 1)) atTop (𝓝 l))
    (h2 : Tendsto (fun k : ℕ => F (3 * k + 2)) atTop (𝓝 l)) :
    Tendsto F atTop (𝓝 l) := by
  rw [Metric.tendsto_atTop] at h0 h1 h2 ⊢
  intro ε hε
  obtain ⟨N0, hN0⟩ := h0 ε hε
  obtain ⟨N1, hN1⟩ := h1 ε hε
  obtain ⟨N2, hN2⟩ := h2 ε hε
  let N : ℕ := max N0 (max N1 N2)
  refine ⟨3 * N, fun n hn => ?_⟩
  have hmod : n % 3 < 3 := Nat.mod_lt n (by omega)
  have hdiv := Nat.mod_add_div n 3
  have hnEq : n = 3 * (n / 3) + n % 3 := by omega
  have hk : N ≤ n / 3 := by omega
  have hk0 : N0 ≤ n / 3 := by dsimp [N] at hk; omega
  have hk1 : N1 ≤ n / 3 := by dsimp [N] at hk; omega
  have hk2 : N2 ≤ n / 3 := by dsimp [N] at hk; omega
  interval_cases hcase : n % 3
  · have hnform : n = 3 * (n / 3) := by omega
    rw [hnform]
    exact hN0 (n / 3) hk0
  · have hnform : n = 3 * (n / 3) + 1 := by omega
    rw [hnform]
    exact hN1 (n / 3) hk1
  · have hnform : n = 3 * (n / 3) + 2 := by omega
    rw [hnform]
    exact hN2 (n / 3) hk2

private theorem reciprocalPower_linear_tendsto_zero (s : ℝ) (hs : 0 < s)
    (c d : ℕ) (hc : 1 ≤ c) (hd : 1 ≤ d) :
    Tendsto (fun k : ℕ => reciprocalPower s (c + d * k)) atTop (𝓝 0) := by
  have hindex : Tendsto (fun k : ℕ => c + d * k) atTop atTop := by
    rw [Filter.tendsto_atTop]
    intro N
    filter_upwards [Filter.eventually_ge_atTop N] with k hk
    exact hk.trans ((Nat.le_mul_of_pos_left k hd).trans
      (Nat.le_add_left (d * k) c))
  have hcast :
      Tendsto (fun k : ℕ => ((c + d * k : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hindex
  have hr := tendsto_rpow_neg_atTop hs
  convert hr.comp hcast using 1
  funext k
  simpa [reciprocalPower, one_div] using
    (Real.rpow_neg (Nat.cast_nonneg (c + d * k)) s).symm

private lemma reciprocalPower_eq_rpow_neg (s : ℝ) {n : ℕ} (hn : n ≠ 0) :
    reciprocalPower s n = Real.rpow (n : ℝ) (-s) := by
  simpa [reciprocalPower, one_div] using
    (Real.rpow_neg (Nat.cast_nonneg n) s).symm

private lemma reciprocalPower_pos (s : ℝ) {n : ℕ} (hn : n ≠ 0) :
    0 < reciprocalPower s n := by
  rw [reciprocalPower]
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (Nat.pos_of_ne_zero hn)
  exact div_pos zero_lt_one (Real.rpow_pos_of_pos hnpos s)

private lemma reciprocalPower_le_one (s : ℝ) (hs : 0 ≤ s) {n : ℕ} (hn : n ≠ 0) :
    reciprocalPower s n ≤ 1 := by
  rw [reciprocalPower]
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hn)
  rw [one_div]
  have hpow : 1 ≤ Real.rpow (n : ℝ) s := Real.one_le_rpow hn1 hs
  exact (inv_le_one₀ (zero_lt_one.trans_le hpow)).2 hpow

private lemma q_three_mul_add_one_ge_two (s : ℝ) (hs : s ≤ 0) (k : ℕ) :
    2 ≤ q s (3 * k + 1) := by
  have hn1 : (1 : ℝ) ≤ (3 * k + 1 : ℕ) := by
    exact_mod_cast (by omega : 1 ≤ 3 * k + 1)
  have hpowpos : 0 < Real.rpow ((3 * k + 1 : ℕ) : ℝ) s :=
    Real.rpow_pos_of_pos (zero_lt_one.trans_le hn1) s
  have hpowle : Real.rpow ((3 * k + 1 : ℕ) : ℝ) s ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hn1 hs
  have hr : 1 ≤ reciprocalPower s (3 * k + 1) := by
    rw [reciprocalPower]
    exact (one_le_div hpowpos).2 hpowle
  simp [q]
  linarith

private lemma strictConvexOn_rpow_neg (s : ℝ) (hs : 0 < s) :
    StrictConvexOn ℝ (Set.Ioi 0) (fun x : ℝ => Real.rpow x (-s)) := by
  apply strictConvexOn_of_deriv2_pos' (convex_Ioi 0)
  · intro x hx
    exact (Real.continuousAt_rpow_const x (-s) (Or.inl hx.ne')).continuousWithinAt
  · intro x hx
    rw [show (deriv^[2] (fun y : ℝ => Real.rpow y (-s))) x =
        (descPochhammer ℝ 2).eval (-s) * Real.rpow x (-s - (2 : ℕ)) from
      Real.iter_deriv_rpow_const (-s) x 2]
    norm_num [descPochhammer_succ_eval]
    have hxpos : 0 < x := hx
    have hrpos : 0 < Real.rpow x (-s - 2) := Real.rpow_pos_of_pos hxpos _
    have hneg2 : -s - 1 < 0 := by linarith
    exact mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hs hneg2) hrpos

private lemma rpow_second_diff_le (s a : ℝ) (hs : 0 < s) (ha : 0 < a) :
    Real.rpow a (-s) - 2 * Real.rpow (a + 1) (-s) + Real.rpow (a + 2) (-s) ≤
      2 * s * (s + 1) * Real.rpow a (-s - 2) := by
  let f : ℝ → ℝ := fun x => Real.rpow x (-s)
  let f' : ℝ → ℝ := fun x => (-s) * Real.rpow x (-s - 1)
  let f'' : ℝ → ℝ := fun x => (-s) * (-s - 1) * Real.rpow x (-s - 2)
  have hfcont (u v : ℝ) (hu : 0 < u) : ContinuousOn f (Set.Icc u v) := by
    intro x hx
    exact (Real.continuousAt_rpow_const x (-s)
      (Or.inl (ne_of_gt (hu.trans_le hx.1)))).continuousWithinAt
  have hfderiv (u v : ℝ) (hu : 0 < u) :
      ∀ x ∈ Set.Ioo u v, HasDerivAt f (f' x) x := by
    intro x hx
    dsimp [f, f']
    exact Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt (hu.trans hx.1)))
  obtain ⟨c, hc, hcEq⟩ := exists_hasDerivAt_eq_slope f f'
    (show a < a + 1 by linarith) (hfcont a (a + 1) ha) (hfderiv a (a + 1) ha)
  obtain ⟨d, hd, hdEq⟩ := exists_hasDerivAt_eq_slope f f'
    (show a + 1 < a + 2 by linarith)
    (hfcont (a + 1) (a + 2) (by linarith))
    (hfderiv (a + 1) (a + 2) (by linarith))
  have hcd : c < d := hc.2.trans hd.1
  have hfpcont : ContinuousOn f' (Set.Icc c d) := by
    intro x hx
    dsimp [f']
    exact (continuousAt_const.mul
      (Real.continuousAt_rpow_const x (-s - 1)
        (Or.inl (ne_of_gt (ha.trans (hc.1.trans_le hx.1)))))).continuousWithinAt
  have hfpderiv : ∀ x ∈ Set.Ioo c d, HasDerivAt f' (f'' x) x := by
    intro x hx
    dsimp [f', f'']
    convert (Real.hasDerivAt_rpow_const
        (x := x) (p := -s - 1)
        (Or.inl (ne_of_gt (ha.trans (hc.1.trans hx.1))))).const_mul (-s) using 1 <;>
      ring_nf
  obtain ⟨e, he, heEq⟩ := exists_hasDerivAt_eq_slope f' f'' hcd hfpcont hfpderiv
  have hdcpos : 0 < d - c := sub_pos.mpr hcd
  have hdc : d - c < 2 := by linarith [hc.1, hd.2]
  have hae : a < e := hc.1.trans he.1
  have hepos : 0 < e := ha.trans hae
  have hpow : Real.rpow e (-s - 2) ≤ Real.rpow a (-s - 2) :=
    (Real.rpow_lt_rpow_of_neg ha hae (by linarith)).le
  have hcoef : 0 < (-s) * (-s - 1) :=
    mul_pos_of_neg_of_neg (by linarith) (by linarith)
  have hsecond : f'' e ≤ s * (s + 1) * Real.rpow a (-s - 2) := by
    dsimp [f'']
    have h := mul_le_mul_of_nonneg_left hpow hcoef.le
    have hcoeffeq : (-s) * (-s - 1) = s * (s + 1) := by ring
    rw [hcoeffeq] at h
    rw [hcoeffeq]
    exact h
  have hsecond_nonneg : 0 ≤ f'' e := by
    dsimp [f'']
    exact (mul_pos hcoef (Real.rpow_pos_of_pos hepos _)).le
  have hslope : f'' e * (d - c) = f' d - f' c := by
    rw [heEq]
    field_simp
  have hdiff :
      Real.rpow a (-s) - 2 * Real.rpow (a + 1) (-s) + Real.rpow (a + 2) (-s) =
        f'' e * (d - c) := by
    dsimp [f, f'] at hcEq hdEq
    norm_num at hcEq hdEq
    rw [hslope]
    dsimp [f']
    linarith
  rw [hdiff]
  calc
    f'' e * (d - c) ≤
        (s * (s + 1) * Real.rpow a (-s - 2)) * (d - c) :=
      mul_le_mul_of_nonneg_right hsecond hdcpos.le
    _ ≤ (s * (s + 1) * Real.rpow a (-s - 2)) * 2 := by
      gcongr
      exact (mul_pos (mul_pos hs (by linarith))
        (Real.rpow_pos_of_pos ha _)).le
    _ = 2 * s * (s + 1) * Real.rpow a (-s - 2) := by ring

private lemma reciprocalPower_sq_eq (s : ℝ) {n : ℕ} (hn : n ≠ 0) :
    (reciprocalPower s n) ^ 2 = 1 / Real.rpow (n : ℝ) (2 * s) := by
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  unfold reciprocalPower
  rw [div_pow]
  norm_num
  rw [show 2 * s = s * (2 : ℕ) by norm_num; ring,
    Real.rpow_mul_natCast hn0]

private lemma alphaStar_four_mul_add_one (s : ℝ) (k : ℕ) :
    alphaStar s (4 * k + 1) = reciprocalPower s (1 + 3 * k) := by
  simp [alphaStar]

private lemma alphaStar_four_mul_add_two (s : ℝ) (k : ℕ) :
    alphaStar s (4 * k + 2) = -reciprocalPower s (2 + 3 * k) := by
  simp [alphaStar]
  congr 2
  omega

private lemma alphaStar_four_mul_add_three (s : ℝ) (k : ℕ) :
    alphaStar s (4 * k + 3) = -reciprocalPower s (2 + 3 * k) := by
  simp [alphaStar]
  congr 2
  omega

private lemma alphaStar_four_mul_add_four (s : ℝ) (k : ℕ) :
    alphaStar s (4 * k + 4) = reciprocalPower s (3 + 3 * k) := by
  simp [alphaStar]
  congr 2
  omega

private lemma not_summable_one_div_three_nat_succ :
    ¬ Summable (fun k : ℕ => 1 / (3 * ((k + 1 : ℕ) : ℝ))) := by
  have hharm : ¬ Summable (fun k : ℕ => 1 / (((k + 1 : ℕ) : ℝ))) := by
    intro h
    apply Real.not_summable_one_div_natCast
    exact (summable_nat_add_iff 1).1 (by
      simpa only [Nat.cast_add, Nat.cast_one] using h)
  intro h
  apply hharm
  have h3 := h.mul_left 3
  convert h3 using 1
  ext k
  have hkpos : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
  field_simp

private lemma harmonic_lower_reciprocalPower_sq (s : ℝ)
    (hs0 : 0 < s) (hsHalf : s ≤ 1 / 2) (k : ℕ) :
    1 / (3 * ((k + 1 : ℕ) : ℝ)) ≤
      (reciprocalPower s (1 + 3 * k)) ^ 2 := by
  let m : ℝ := ((1 + 3 * k : ℕ) : ℝ)
  have hmpos : 0 < m := by dsimp [m]; positivity
  have hm1 : 1 ≤ m := by
    dsimp [m]
    exact_mod_cast (by omega : 1 ≤ 1 + 3 * k)
  have hexp : Real.rpow m (2 * s) ≤ m := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hm1 (by linarith : 2 * s ≤ 1)
  have hmle : m ≤ 3 * ((k + 1 : ℕ) : ℝ) := by
    dsimp [m]
    norm_num
    linarith
  have hden : Real.rpow m (2 * s) ≤ 3 * ((k + 1 : ℕ) : ℝ) := hexp.trans hmle
  have hinv : 1 / (3 * ((k + 1 : ℕ) : ℝ)) ≤ 1 / Real.rpow m (2 * s) :=
    one_div_le_one_div_of_le (Real.rpow_pos_of_pos hmpos _) hden
  rw [reciprocalPower_sq_eq s (by omega : 1 + 3 * k ≠ 0)]
  simpa [m] using hinv

private lemma not_summable_reciprocalPower_sq (s : ℝ)
    (hs0 : 0 < s) (hsHalf : s ≤ 1 / 2) :
    ¬ Summable (fun k : ℕ => (reciprocalPower s (1 + 3 * k)) ^ 2) := by
  intro h
  apply not_summable_one_div_three_nat_succ
  exact Summable.of_nonneg_of_le (fun k => by positivity)
    (harmonic_lower_reciprocalPower_sq s hs0 hsHalf) h

private lemma summable_reciprocalPower_sq_linear (s : ℝ)
    (hsHalf : 1 / 2 < s) (c : ℕ) (hc : 1 ≤ c) :
    Summable (fun k : ℕ => (reciprocalPower s (c + 3 * k)) ^ 2) := by
  have hp : Summable (fun k : ℕ =>
      1 / Real.rpow ((k + 1 : ℕ) : ℝ) (2 * s)) := by
    simpa only [Function.comp_apply, Nat.succ_eq_add_one] using
      (Real.summable_one_div_nat_rpow.mpr (by linarith : 1 < 2 * s)).comp_injective
        Nat.succ_injective
  refine Summable.of_nonneg_of_le (fun k => sq_nonneg _) (fun k => ?_) hp
  have hmne : c + 3 * k ≠ 0 := by omega
  rw [reciprocalPower_sq_eq s hmne]
  have hxpos : 0 < ((k + 1 : ℕ) : ℝ) := by positivity
  have hmpos : 0 < ((c + 3 * k : ℕ) : ℝ) := by
    exact_mod_cast (by omega : 0 < c + 3 * k)
  have hbase : ((k + 1 : ℕ) : ℝ) ≤ ((c + 3 * k : ℕ) : ℝ) := by
    exact_mod_cast (by omega : k + 1 ≤ c + 3 * k)
  have hexp : 0 ≤ 2 * s := by linarith
  have hpow := Real.rpow_le_rpow hxpos.le hbase hexp
  exact one_div_le_one_div_of_le (Real.rpow_pos_of_pos hxpos _) hpow

private lemma summable_of_four_residue_classes {f : ℕ → ℝ}
    (h : ∀ r < 4, Summable (fun n : ℕ => f (4 * n + r))) : Summable f := by
  rw [Finset.sum_indicator_mod 4 f]
  change Summable (fun n => ∑ a : ZMod 4, {n : ℕ | (n : ZMod 4) = a}.indicator f n)
  apply summable_sum
  intro r hr
  rw [← ZMod.natCast_zmod_val r, summable_indicator_mod_iff_summable]
  exact h r.val r.val_lt

private lemma harmonic_lower_reciprocalPower (s : ℝ)
    (hs0 : 0 < s) (hs1 : s ≤ 1) (k : ℕ) :
    1 / (3 * ((k + 1 : ℕ) : ℝ)) ≤ reciprocalPower s (1 + 3 * k) := by
  let m : ℝ := ((1 + 3 * k : ℕ) : ℝ)
  have hmpos : 0 < m := by dsimp [m]; positivity
  have hm1 : 1 ≤ m := by
    dsimp [m]
    exact_mod_cast (by omega : 1 ≤ 1 + 3 * k)
  have hexp : Real.rpow m s ≤ m := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hm1 hs1
  have hmle : m ≤ 3 * ((k + 1 : ℕ) : ℝ) := by
    dsimp [m]
    norm_num
    linarith
  have hinv : 1 / (3 * ((k + 1 : ℕ) : ℝ)) ≤ 1 / Real.rpow m s :=
    one_div_le_one_div_of_le (Real.rpow_pos_of_pos hmpos _) (hexp.trans hmle)
  simpa [reciprocalPower, m] using hinv

private lemma not_summable_reciprocalPower (s : ℝ)
    (hs0 : 0 < s) (hs1 : s ≤ 1) :
    ¬ Summable (fun k : ℕ => reciprocalPower s (1 + 3 * k)) := by
  intro h
  apply not_summable_one_div_three_nat_succ
  exact Summable.of_nonneg_of_le (fun k => by positivity)
    (harmonic_lower_reciprocalPower s hs0 hs1) h

private lemma reciprocalPower_div_two_le_log_one_add (s : ℝ) (hs0 : 0 < s)
    {n : ℕ} (hn : n ≠ 0) :
    reciprocalPower s n / 2 ≤ Real.log (1 + reciprocalPower s n) := by
  have hrpos := reciprocalPower_pos s hn
  have hrle := reciprocalPower_le_one s hs0.le hn
  have hlower := Real.le_log_one_add_of_nonneg hrpos.le
  apply le_trans _ hlower
  rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 2)
    (by linarith : 0 < reciprocalPower s n + 2)]
  nlinarith [sq_nonneg (reciprocalPower s n)]

private theorem summable_abs_qDeviation_from_one (s : ℝ) (hs : 1 < s) :
    Summable (fun k : ℕ => |qDeviation s (k + 1)|) := by
  have hrec : Summable (fun k : ℕ => reciprocalPower s (k + 1)) := by
    simpa only [Function.comp_apply, reciprocalPower, Nat.succ_eq_add_one] using
      (Real.summable_one_div_nat_rpow.mpr hs).comp_injective Nat.succ_injective
  refine Summable.of_nonneg_of_le (fun k => abs_nonneg _) (fun k => ?_) (hrec.mul_left 2)
  have hne : k + 1 ≠ 0 := by omega
  have hrpos : 0 < reciprocalPower s (k + 1) := reciprocalPower_pos s hne
  have hrle : reciprocalPower s (k + 1) ≤ 1 :=
    reciprocalPower_le_one s (by linarith) hne
  by_cases hmod : (k + 1) % 3 = 2
  · simp only [qDeviation, q, hmod, if_pos]
    rw [abs_of_nonpos]
    · nlinarith [sq_nonneg (reciprocalPower s (k + 1))]
    · nlinarith [sq_nonneg (1 - reciprocalPower s (k + 1))]
  · simp [qDeviation, q, hmod, abs_of_pos hrpos]
    linarith

/-- Exercise 3097, gap 1; define the complete periodic sequence `q`. -/
theorem gap1 (s : ℝ) (hs : 1 < s) :
    SummableFromOne (fun n => |qDeviation s n|) := by
  unfold SummableFromOne
  exact (summable_abs_qDeviation_from_one s hs).mono_filter
    (SummationFilter.conditional ℕ).le_atTop

/-- Exercise 3097, gap 2. -/
theorem gap2 (s : ℝ) (hs : 1 < s) :
    AbsolutelySummableFromOne (fun n => Real.log (q s n)) := by
  have hdabs := summable_abs_qDeviation_from_one s hs
  have hd : Summable (fun k : ℕ => qDeviation s (k + 1)) := hdabs.of_abs
  have hlog := Real.summable_log_one_add_of_summable hd
  have hnorm := hlog.norm
  have hcond := hnorm.mono_filter (SummationFilter.conditional ℕ).le_atTop
  simpa [AbsolutelySummableFromOne, SummableFromOne, qDeviation,
    Real.norm_eq_abs] using hcond

/-- Exercise 3097, gap 3. -/
theorem gap3 (s : ℝ) (hs : s ≤ 0) :
    ¬Tendsto (q s) atTop (𝓝 1) := by
  intro hq
  have hindex : Tendsto (fun k : ℕ => 3 * k + 1) atTop atTop := by
    rw [Filter.tendsto_atTop]
    intro N
    filter_upwards [Filter.eventually_ge_atTop N] with k hk
    omega
  have hsub : Tendsto (fun k : ℕ => q s (3 * k + 1)) atTop (𝓝 1) := hq.comp hindex
  have hev : ∀ᶠ k : ℕ in atTop, q s (3 * k + 1) < 3 / 2 :=
    (tendsto_order.1 hsub).2 (3 / 2) (by norm_num)
  rcases hev.exists with ⟨k, hk⟩
  linarith [q_three_mul_add_one_ge_two s hs k]

/-- Exercise 3097, gap 4. -/
theorem gap4 (s : ℝ) (hs : s ≤ 0) :
    ¬SummableFromOne (fun n => Real.log (q s n)) := by
  intro hsum
  unfold SummableFromOne at hsum
  have hzero := tendsto_zero_of_summable_conditional hsum
  have hindex : Tendsto (fun k : ℕ => 3 * k) atTop atTop := by
    rw [Filter.tendsto_atTop]
    intro N
    filter_upwards [Filter.eventually_ge_atTop N] with k hk
    omega
  have hsubzero :
      Tendsto (fun k : ℕ => Real.log (q s (3 * k + 1))) atTop (𝓝 0) := by
    simpa only [Function.comp_apply, Nat.mul_add] using hzero.comp hindex
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hev : ∀ᶠ k : ℕ in atTop,
      Real.log (q s (3 * k + 1)) < Real.log 2 / 2 :=
    (tendsto_order.1 hsubzero).2 (Real.log 2 / 2) (by linarith)
  rcases hev.exists with ⟨k, hk⟩
  have hq := q_three_mul_add_one_ge_two s hs k
  have hlog : Real.log 2 ≤ Real.log (q s (3 * k + 1)) :=
    Real.strictMonoOn_log.monotoneOn (by norm_num)
      (lt_of_lt_of_le (by norm_num) hq) hq
  linarith

/-- Exercise 3097, gap 5; use the explicit four-term refinement. -/
theorem gap5 (s : ℝ) (hs0 : 0 < s) (hs1 : s ≤ 1) :
    ∃ a : ℕ → ℝ, a = alphaStar s ∧
      ∀ k, a (4 * k + 1) = reciprocalPower s (1 + 3 * k) := by
  exact ⟨alphaStar s, rfl, alphaStar_four_mul_add_one s⟩

/-- Exercise 3097, gap 6. -/
theorem gap6 (s : ℝ) (hs0 : 0 < s) (hs1 : s ≤ 1) :
    ∃ a : ℕ → ℝ, a = alphaStar s ∧
      ∀ k, a (4 * k + 2) = -reciprocalPower s (2 + 3 * k) := by
  exact ⟨alphaStar s, rfl, alphaStar_four_mul_add_two s⟩

/-- Exercise 3097, gap 7. -/
theorem gap7 (s : ℝ) (hs0 : 0 < s) (hs1 : s ≤ 1) :
    ∃ a : ℕ → ℝ, a = alphaStar s ∧
      ∀ k, a (4 * k + 3) = -reciprocalPower s (2 + 3 * k) := by
  exact ⟨alphaStar s, rfl, alphaStar_four_mul_add_three s⟩

/-- Exercise 3097, gap 8. -/
theorem gap8 (s : ℝ) (hs0 : 0 < s) (hs1 : s ≤ 1) :
    ∃ a : ℕ → ℝ, a = alphaStar s ∧
      ∀ k, a (4 * k + 4) = reciprocalPower s (3 + 3 * k) := by
  exact ⟨alphaStar s, rfl, alphaStar_four_mul_add_four s⟩

/-- Exercise 3097, gap 9. -/
theorem gap9 (s : ℝ) (hs0 : 0 < s) (hs1 : s ≤ 1) :
    ∀ k, 0 < beta s k := by
  intro k
  let a : ℝ := ((1 + 3 * k : ℕ) : ℝ)
  have ha : 0 < a := by dsimp [a]; positivity
  have hconv := strictConvexOn_rpow_neg s hs0
  have hsec := hconv.secant_strict_mono_aux1
    (x := a) (y := a + 1) (z := a + 2)
    ha (by linarith : 0 < a + 2) (by linarith) (by linarith)
  unfold beta
  rw [reciprocalPower_eq_rpow_neg s (by omega : 1 + 3 * k ≠ 0),
    reciprocalPower_eq_rpow_neg s (by omega : 2 + 3 * k ≠ 0),
    reciprocalPower_eq_rpow_neg s (by omega : 3 + 3 * k ≠ 0)]
  norm_num [a] at hsec ⊢
  ring_nf at hsec ⊢
  linarith

/-- Exercise 3097, gap 10; interpret all real powers by `Real.rpow`. -/
theorem gap10 (s : ℝ) (hs0 : 0 < s) (hs1 : s ≤ 1) :
    ∀ k, beta s k ≤ betaBound s k := by
  intro k
  let a : ℝ := ((1 + 3 * k : ℕ) : ℝ)
  have ha : 0 < a := by dsimp [a]; positivity
  have h := rpow_second_diff_le s a hs0 ha
  unfold beta betaBound
  rw [reciprocalPower_eq_rpow_neg s (by omega : 1 + 3 * k ≠ 0),
    reciprocalPower_eq_rpow_neg s (by omega : 2 + 3 * k ≠ 0),
    reciprocalPower_eq_rpow_neg s (by omega : 3 + 3 * k ≠ 0)]
  norm_num [a] at h ⊢
  ring_nf at h ⊢
  rw [← Real.rpow_neg (by positivity : 0 ≤ (1 : ℝ) + k * 3)]
  convert h using 1 <;> ring

/-- Exercise 3097, gap 11. -/
theorem gap11 (s : ℝ) (hs0 : 0 < s) (hs1 : s ≤ 1) :
    ∀ k, 0 < betaBound s k := by
  intro k
  unfold betaBound
  have hbase : 0 < (3 * (k : ℝ) + 1) := by positivity
  exact div_pos (mul_pos (mul_pos (by norm_num) hs0) (by linarith))
    (Real.rpow_pos_of_pos hbase (s + 2))

/-- Exercise 3097, gap 12. -/
theorem gap12 (s : ℝ) (hs0 : 0 < s) (hs1 : s ≤ 1) :
    SummableFromOne (beta s) := by
  have hp : Summable (fun k : ℕ =>
      1 / Real.rpow ((k + 1 : ℕ) : ℝ) (s + 2)) := by
    simpa only [Function.comp_apply, Nat.succ_eq_add_one] using
      (Real.summable_one_div_nat_rpow.mpr (by linarith : 1 < s + 2)).comp_injective
        Nat.succ_injective
  have hmajor := hp.mul_left (2 * s * (s + 1))
  unfold SummableFromOne
  have hstd : Summable (fun k : ℕ => beta s (k + 1)) := by
    refine Summable.of_nonneg_of_le (fun k => (gap9 s hs0 hs1 (k + 1)).le)
      (fun k => ?_) hmajor
    calc
      beta s (k + 1) ≤ betaBound s (k + 1) := gap10 s hs0 hs1 (k + 1)
      _ ≤ 2 * s * (s + 1) *
          (1 / Real.rpow ((k + 1 : ℕ) : ℝ) (s + 2)) := by
        have hxpos : 0 < ((k + 1 : ℕ) : ℝ) := by positivity
        have hbase : ((k + 1 : ℕ) : ℝ) ≤ 3 * ((k + 1 : ℕ) : ℝ) + 1 := by
          have hk0 : (0 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by positivity
          linarith
        have hpnonneg : 0 ≤ s + 2 := by linarith
        have hrpow :
            Real.rpow ((k + 1 : ℕ) : ℝ) (s + 2) ≤
              Real.rpow (3 * ((k + 1 : ℕ) : ℝ) + 1) (s + 2) :=
          Real.rpow_le_rpow hxpos.le hbase hpnonneg
        have hinv :
            1 / Real.rpow (3 * ((k + 1 : ℕ) : ℝ) + 1) (s + 2) ≤
              1 / Real.rpow ((k + 1 : ℕ) : ℝ) (s + 2) :=
          one_div_le_one_div_of_le (Real.rpow_pos_of_pos hxpos _) hrpow
        unfold betaBound
        norm_num at hinv ⊢
        exact mul_le_mul_of_nonneg_left hinv
          (mul_nonneg (mul_nonneg (by norm_num) hs0.le) (by linarith))
  exact hstd.mono_filter (SummationFilter.conditional ℕ).le_atTop

private theorem summable_beta_standard (s : ℝ) (hs0 : 0 < s) (hs1 : s ≤ 1) :
    Summable (beta s) := by
  have hp : Summable (fun k : ℕ =>
      1 / Real.rpow ((k + 1 : ℕ) : ℝ) (s + 2)) := by
    simpa only [Function.comp_apply, Nat.succ_eq_add_one] using
      (Real.summable_one_div_nat_rpow.mpr (by linarith : 1 < s + 2)).comp_injective
        Nat.succ_injective
  have hmajor := hp.mul_left (2 * s * (s + 1))
  refine Summable.of_nonneg_of_le (fun k => (gap9 s hs0 hs1 k).le)
    (fun k => ?_) hmajor
  calc
    beta s k ≤ betaBound s k := gap10 s hs0 hs1 k
    _ ≤ 2 * s * (s + 1) *
        (1 / Real.rpow ((k + 1 : ℕ) : ℝ) (s + 2)) := by
      have hxpos : 0 < ((k + 1 : ℕ) : ℝ) := by positivity
      have hbase : ((k + 1 : ℕ) : ℝ) ≤ 3 * (k : ℝ) + 1 := by
        push_cast
        linarith
      have hpnonneg : 0 ≤ s + 2 := by linarith
      have hrpow :
          Real.rpow ((k + 1 : ℕ) : ℝ) (s + 2) ≤
            Real.rpow (3 * (k : ℝ) + 1) (s + 2) :=
        Real.rpow_le_rpow hxpos.le hbase hpnonneg
      have hinv :
          1 / Real.rpow (3 * (k : ℝ) + 1) (s + 2) ≤
            1 / Real.rpow ((k + 1 : ℕ) : ℝ) (s + 2) :=
        one_div_le_one_div_of_le (Real.rpow_pos_of_pos hxpos _) hrpow
      unfold betaBound
      exact mul_le_mul_of_nonneg_left (by simpa [one_div] using hinv)
        (mul_nonneg (mul_nonneg (by norm_num) hs0.le) (by linarith))

private def alphaPartial (s : ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.range N, alphaStar s (n + 1)

private theorem alphaStar_block_sum (s : ℝ) (k : ℕ) :
    (∑ i ∈ Finset.range 4, alphaStar s (4 * k + i + 1)) = beta s k := by
  norm_num [Finset.sum_range_succ]
  rw [show 4 * k + 0 + 1 = 4 * k + 1 by omega,
    show 4 * k + 1 + 1 = 4 * k + 2 by omega,
    show 4 * k + 2 + 1 = 4 * k + 3 by omega,
    show 4 * k + 3 + 1 = 4 * k + 4 by omega,
    alphaStar_four_mul_add_one, alphaStar_four_mul_add_two,
    alphaStar_four_mul_add_three, alphaStar_four_mul_add_four]
  unfold beta
  ring

private theorem alphaPartial_four_mul (s : ℝ) (N : ℕ) :
    alphaPartial s (4 * N) = ∑ k ∈ Finset.range N, beta s k := by
  induction N with
  | zero => simp [alphaPartial]
  | succ N ih =>
      rw [show 4 * (N + 1) = 4 * N + 4 by omega]
      rw [alphaPartial, Finset.sum_range_add]
      change alphaPartial s (4 * N) +
          (∑ i ∈ Finset.range 4, alphaStar s (4 * N + i + 1)) = _
      rw [ih, alphaStar_block_sum, Finset.sum_range_succ]

private theorem alphaPartial_four_mul_add_one (s : ℝ) (k : ℕ) :
    alphaPartial s (4 * k + 1) =
      (∑ j ∈ Finset.range k, beta s j) + reciprocalPower s (1 + 3 * k) := by
  rw [alphaPartial, Finset.sum_range_succ]
  change alphaPartial s (4 * k) + alphaStar s (4 * k + 1) = _
  rw [alphaPartial_four_mul, alphaStar_four_mul_add_one]

private theorem alphaPartial_four_mul_add_two (s : ℝ) (k : ℕ) :
    alphaPartial s (4 * k + 2) =
      (∑ j ∈ Finset.range k, beta s j) + reciprocalPower s (1 + 3 * k) -
        reciprocalPower s (2 + 3 * k) := by
  rw [show 4 * k + 2 = (4 * k + 1) + 1 by omega, alphaPartial,
    Finset.sum_range_succ]
  change alphaPartial s (4 * k + 1) + alphaStar s (4 * k + 2) = _
  rw [alphaPartial_four_mul_add_one, alphaStar_four_mul_add_two]
  ring

private theorem alphaPartial_four_mul_add_three (s : ℝ) (k : ℕ) :
    alphaPartial s (4 * k + 3) =
      (∑ j ∈ Finset.range k, beta s j) + reciprocalPower s (1 + 3 * k) -
        2 * reciprocalPower s (2 + 3 * k) := by
  rw [show 4 * k + 3 = (4 * k + 2) + 1 by omega, alphaPartial,
    Finset.sum_range_succ]
  change alphaPartial s (4 * k + 2) + alphaStar s (4 * k + 3) = _
  rw [alphaPartial_four_mul_add_two, alphaStar_four_mul_add_three]
  ring

private theorem alphaStar_conditional_summable (s : ℝ) (hs0 : 0 < s) (hs1 : s ≤ 1) :
    SummableFromOne (alphaStar s) := by
  have hb := (summable_beta_standard s hs0 hs1).hasSum.tendsto_sum_nat
  let L : ℝ := ∑' k : ℕ, beta s k
  have hbL : Tendsto (fun N : ℕ => ∑ k ∈ Finset.range N, beta s k)
      atTop (𝓝 L) := by simpa [L] using hb
  have hr1 := reciprocalPower_linear_tendsto_zero s hs0 1 3 (by omega) (by omega)
  have hr2 := reciprocalPower_linear_tendsto_zero s hs0 2 3 (by omega) (by omega)
  have h0 : Tendsto (fun k : ℕ => alphaPartial s (4 * k)) atTop (𝓝 L) := by
    simpa only [alphaPartial_four_mul] using hbL
  have h1 : Tendsto (fun k : ℕ => alphaPartial s (4 * k + 1)) atTop (𝓝 L) := by
    rw [show (fun k : ℕ => alphaPartial s (4 * k + 1)) =
        (fun k => (∑ j ∈ Finset.range k, beta s j) +
          reciprocalPower s (1 + 3 * k)) by
      funext k
      exact alphaPartial_four_mul_add_one s k]
    simpa using hbL.add hr1
  have h2 : Tendsto (fun k : ℕ => alphaPartial s (4 * k + 2)) atTop (𝓝 L) := by
    rw [show (fun k : ℕ => alphaPartial s (4 * k + 2)) =
        (fun k => (∑ j ∈ Finset.range k, beta s j) +
          reciprocalPower s (1 + 3 * k) - reciprocalPower s (2 + 3 * k)) by
      funext k
      exact alphaPartial_four_mul_add_two s k]
    simpa using (hbL.add hr1).sub hr2
  have h3 : Tendsto (fun k : ℕ => alphaPartial s (4 * k + 3)) atTop (𝓝 L) := by
    rw [show (fun k : ℕ => alphaPartial s (4 * k + 3)) =
        (fun k => (∑ j ∈ Finset.range k, beta s j) +
          reciprocalPower s (1 + 3 * k) - 2 * reciprocalPower s (2 + 3 * k)) by
      funext k
      exact alphaPartial_four_mul_add_three s k]
    have h2r := hr2.const_mul 2
    simpa using (hbL.add hr1).sub h2r
  unfold SummableFromOne
  apply summable_conditional_iff.mpr
  refine ⟨L, ?_⟩
  exact tendsto_of_tendsto_four_residue h0 h1 h2 h3

private theorem alphaStar_from_one_tendsto_zero (s : ℝ) (hs0 : 0 < s) :
    Tendsto (fun k : ℕ => alphaStar s (k + 1)) atTop (𝓝 0) := by
  have hr1 := reciprocalPower_linear_tendsto_zero s hs0 1 3 (by omega) (by omega)
  have hr2 := reciprocalPower_linear_tendsto_zero s hs0 2 3 (by omega) (by omega)
  have hr3 := reciprocalPower_linear_tendsto_zero s hs0 3 3 (by omega) (by omega)
  have h0 : Tendsto (fun k : ℕ => alphaStar s (4 * k + 1)) atTop (𝓝 0) := by
    simpa only [alphaStar_four_mul_add_one] using hr1
  have h1 : Tendsto (fun k : ℕ => alphaStar s (4 * k + 2)) atTop (𝓝 0) := by
    simpa only [alphaStar_four_mul_add_two, neg_zero] using hr2.neg
  have h2 : Tendsto (fun k : ℕ => alphaStar s (4 * k + 3)) atTop (𝓝 0) := by
    simpa only [alphaStar_four_mul_add_three, neg_zero] using hr2.neg
  have h3 : Tendsto (fun k : ℕ => alphaStar s (4 * k + 4)) atTop (𝓝 0) := by
    simpa only [alphaStar_four_mul_add_four] using hr3
  exact tendsto_of_tendsto_four_residue h0 h1 h2 h3

private theorem alphaStar_sq_summable_standard (s : ℝ) (hsHalf : 1 / 2 < s) :
    Summable (fun k : ℕ => (alphaStar s (k + 1)) ^ 2) := by
  apply summable_of_four_residue_classes
  intro r hr
  interval_cases r
  · simpa only [zero_add, alphaStar_four_mul_add_one] using
      summable_reciprocalPower_sq_linear s hsHalf 1 (by omega)
  · simpa only [Nat.add_one, alphaStar_four_mul_add_two, neg_sq] using
      summable_reciprocalPower_sq_linear s hsHalf 2 (by omega)
  · simpa only [alphaStar_four_mul_add_three, neg_sq] using
      summable_reciprocalPower_sq_linear s hsHalf 2 (by omega)
  · simpa only [alphaStar_four_mul_add_four] using
      summable_reciprocalPower_sq_linear s hsHalf 3 (by omega)

private theorem abs_log_one_add_sub_self_le_sq {x : ℝ} (hx : |x| ≤ 1 / 2) :
    |Real.log (1 + x) - x| ≤ x ^ 2 := by
  have hxlt : ‖(x : ℂ)‖ < 1 := by
    simpa [Complex.norm_real, Real.norm_eq_abs] using hx.trans_lt (by norm_num)
  have hc := Complex.norm_log_one_add_sub_self_le hxlt
  have hpos : 0 < 1 + x := by
    rw [abs_le] at hx
    linarith
  have hlog : Complex.log (1 + (x : ℂ)) = (Real.log (1 + x) : ℂ) := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_add,
      ← Complex.ofReal_log hpos.le]
  rw [hlog] at hc
  simp only [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at hc
  have hone : 0 < 1 - |x| := by linarith
  have hinv : (1 - |x|)⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ hone (by norm_num : (0 : ℝ) < 2)]
    linarith
  calc
    |Real.log (1 + x) - x| ≤ |x| ^ 2 * (1 - |x|)⁻¹ / 2 := hc
    _ ≤ |x| ^ 2 * 2 / 2 := by gcongr
    _ = x ^ 2 := by rw [sq_abs]; ring

private theorem sq_div_three_le_self_sub_log_one_add {x : ℝ}
    (hx0 : 0 ≤ x) (hxHalf : x ≤ 1 / 2) :
    x ^ 2 / 3 ≤ x - Real.log (1 + x) := by
  have hxabs : |-x| < 1 := by
    rw [abs_neg, abs_of_nonneg hx0]
    linarith
  have hs0 := Real.hasSum_pow_div_log_of_abs_lt_one hxabs
  have hs := hs0.mul_left (-1 : ℝ)
  let a : ℕ → ℝ := fun n => x ^ (n + 1) / ((n + 1 : ℕ) : ℝ)
  have hseries :
      HasSum (fun n : ℕ => (-1 : ℝ) ^ n * a n) (Real.log (1 + x)) := by
    convert hs using 1
    · funext n
      dsimp [a]
      rw [neg_pow]
      push_cast
      ring
    · ring
  have ha : Antitone a := by
    apply antitone_nat_of_succ_le
    intro n
    dsimp [a]
    have hn1 : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
    have hn2 : (0 : ℝ) < ((n + 2 : ℕ) : ℝ) := by positivity
    rw [div_le_div_iff₀ hn2 hn1]
    rw [show n + 1 + 1 = n + 2 by omega, pow_succ]
    have hx1 : x ≤ 1 := by linarith
    have hp0 : 0 ≤ x ^ (n + 1) := pow_nonneg hx0 _
    have hmul := mul_le_mul_of_nonneg_left hx1 hp0
    push_cast
    nlinarith
  have hupper := ha.tendsto_le_alternating_series hseries.tendsto_sum_nat 1
  norm_num [a, Finset.sum_range_succ] at hupper
  have hcube : x ^ 3 ≤ x ^ 2 / 2 := by
    have hmul := mul_le_mul_of_nonneg_left hxHalf (sq_nonneg x)
    nlinarith
  nlinarith

private theorem log_p_remainder_summable (s : ℝ) (hsHalf : 1 / 2 < s) :
    Summable (fun k : ℕ =>
      Real.log (p s (k + 1)) - alphaStar s (k + 1)) := by
  have ha0 : Tendsto (fun k : ℕ => alphaStar s (k + 1)) atTop (𝓝 0) :=
    alphaStar_from_one_tendsto_zero s (by linarith)
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 ha0 (1 / 2) (by norm_num)
  have haSmall : ∀ᶠ k : ℕ in atTop, |alphaStar s (k + 1)| ≤ 1 / 2 := by
    filter_upwards [Filter.eventually_ge_atTop N] with k hk
    have h := hN k hk
    rw [Real.dist_eq, sub_zero] at h
    exact h.le
  apply (alphaStar_sq_summable_standard s hsHalf).of_norm_bounded_eventually
  rw [Nat.cofinite_eq_atTop]
  filter_upwards [haSmall] with k hk
  rw [Real.norm_eq_abs]
  simpa only [p] using abs_log_one_add_sub_self_le_sq hk

/-- Exercise 3097, gap 13; use one fully defined witness. -/
theorem gap13 (s : ℝ) (hs0 : 0 < s) (hs1 : s ≤ 1) :
    ∃ a : ℕ → ℝ, a = alphaStar s ∧ SummableFromOne a := by
  exact ⟨alphaStar s, rfl, alphaStar_conditional_summable s hs0 hs1⟩

/-- Exercise 3097, gap 14; simplify the duplicated implications. -/
theorem gap14 (s : ℝ) (hs0 : 0 < s) (hsHalf : s ≤ 1 / 2) :
    ∃ a : ℕ → ℝ, a = alphaStar s ∧
      ¬SummableFromOne (fun n => (a n) ^ 2) := by
  refine ⟨alphaStar s, rfl, ?_⟩
  intro hsum
  unfold SummableFromOne at hsum
  have hstd : Summable (fun k : ℕ => (alphaStar s (k + 1)) ^ 2) :=
    summable_of_nonneg_conditional (fun k => sq_nonneg _) hsum
  have hinj : Function.Injective (fun k : ℕ => 4 * k) := by
    intro a b hab
    exact Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 4) hab
  have hsub := hstd.comp_injective hinj
  apply not_summable_reciprocalPower_sq s hs0 hsHalf
  simpa only [Function.comp_def, alphaStar_four_mul_add_one] using hsub

/-- Exercise 3097, gap 15. -/
theorem gap15 (s : ℝ) (hs0 : 0 < s) (hsHalf : s ≤ 1 / 2) :
    ¬SummableFromOne (fun n => Real.log (p s n)) := by
  intro hlog
  have ha := alphaStar_conditional_summable s hs0 (by linarith)
  unfold SummableFromOne at hlog ha
  have hv : Summable (fun k : ℕ =>
      alphaStar s (k + 1) - Real.log (p s (k + 1)))
      (SummationFilter.conditional ℕ) := by
    convert (hlog.sub ha).neg using 1
    funext k
    ring
  have ha0 := alphaStar_from_one_tendsto_zero s hs0
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 ha0 (1 / 2) (by norm_num)
  have hvTail := summable_conditional_nat_add hv N
  have hnonneg : ∀ k : ℕ,
      0 ≤ alphaStar s (k + N + 1) - Real.log (p s (k + N + 1)) := by
    intro k
    have hk := hN (k + N) (by omega)
    rw [Real.dist_eq, sub_zero] at hk
    have hpos : 0 < 1 + alphaStar s (k + N + 1) := by
      rw [abs_lt] at hk
      linarith
    have hlogle := Real.log_le_sub_one_of_pos hpos
    simp only [p]
    linarith
  have hvTailStd := summable_of_nonneg_conditional hnonneg hvTail
  have hvStd : Summable (fun k : ℕ =>
      alphaStar s (k + 1) - Real.log (p s (k + 1))) :=
    (summable_nat_add_iff N).1 (by
      simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hvTailStd)
  have hinj : Function.Injective (fun k : ℕ => 4 * k) := by
    intro a b hab
    exact Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 4) hab
  have hsub0 := hvStd.comp_injective hinj
  have hsub : Summable (fun k : ℕ =>
      reciprocalPower s (1 + 3 * k) -
        Real.log (1 + reciprocalPower s (1 + 3 * k))) := by
    simpa only [Function.comp_def, p, alphaStar_four_mul_add_one] using hsub0
  have hr0 := reciprocalPower_linear_tendsto_zero s hs0 1 3 (by omega) (by omega)
  obtain ⟨M, hM⟩ := Metric.tendsto_atTop.1 hr0 (1 / 2) (by norm_num)
  have hsquareThird : Summable (fun k : ℕ =>
      (reciprocalPower s (1 + 3 * k)) ^ 2 / 3) := by
    apply hsub.of_norm_bounded_eventually
    rw [Nat.cofinite_eq_atTop]
    filter_upwards [Filter.eventually_ge_atTop M] with k hk
    have hrSmall := hM k hk
    rw [Real.dist_eq, sub_zero,
      abs_of_pos (reciprocalPower_pos s (by omega))] at hrSmall
    have hbound := sq_div_three_le_self_sub_log_one_add
      (reciprocalPower_pos s (by omega)).le hrSmall.le
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity :
      0 ≤ (reciprocalPower s (1 + 3 * k)) ^ 2 / 3)]
    exact hbound
  have hsquare := hsquareThird.mul_left 3
  apply not_summable_reciprocalPower_sq s hs0 hsHalf
  convert hsquare using 1
  funext k
  ring

/-- Exercise 3097, gap 16; simplify the duplicated implications. -/
theorem gap16 (s : ℝ) (hsHalf : 1 / 2 < s) (hs1 : s ≤ 1) :
    ∃ a : ℕ → ℝ, a = alphaStar s ∧
      SummableFromOne (fun n => (a n) ^ 2) := by
  refine ⟨alphaStar s, rfl, ?_⟩
  unfold SummableFromOne
  exact (alphaStar_sq_summable_standard s hsHalf).mono_filter
    (SummationFilter.conditional ℕ).le_atTop

/-- Exercise 3097, gap 17. -/
theorem gap17 (s : ℝ) (hsHalf : 1 / 2 < s) (hs1 : s ≤ 1) :
    SummableFromOne (fun n => Real.log (p s n)) := by
  have ha := alphaStar_conditional_summable s (by linarith) hs1
  unfold SummableFromOne at ha ⊢
  have hr := (log_p_remainder_summable s hsHalf).mono_filter
    (SummationFilter.conditional ℕ).le_atTop
  have hsum := ha.add hr
  convert hsum using 1
  funext k
  ring

private def logPPartial (s : ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.range N, Real.log (p s (n + 1))

private def logQPartial (s : ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.range N, Real.log (q s (n + 1))

private theorem q_three_mul_add_one (s : ℝ) (k : ℕ) :
    q s (3 * k + 1) = 1 + reciprocalPower s (1 + 3 * k) := by
  simp [q, show 3 * k + 1 = 1 + 3 * k by omega]

private theorem q_three_mul_add_two (s : ℝ) (k : ℕ) :
    q s (3 * k + 2) = (1 - reciprocalPower s (2 + 3 * k)) ^ 2 := by
  simp [q]
  congr 3
  omega

private theorem q_three_mul_add_three (s : ℝ) (k : ℕ) :
    q s (3 * k + 3) = 1 + reciprocalPower s (3 + 3 * k) := by
  simp [q, show 3 * k + 3 = 3 + 3 * k by omega]

private theorem log_block_q_eq_p (s : ℝ) (k : ℕ) :
    (∑ i ∈ Finset.range 3, Real.log (q s (3 * k + i + 1))) =
      ∑ i ∈ Finset.range 4, Real.log (p s (4 * k + i + 1)) := by
  norm_num [Finset.sum_range_succ]
  rw [show 3 * k + 0 + 1 = 3 * k + 1 by omega,
    show 3 * k + 1 + 1 = 3 * k + 2 by omega,
    show 3 * k + 2 + 1 = 3 * k + 3 by omega,
    show 4 * k + 0 + 1 = 4 * k + 1 by omega,
    show 4 * k + 1 + 1 = 4 * k + 2 by omega,
    show 4 * k + 2 + 1 = 4 * k + 3 by omega,
    show 4 * k + 3 + 1 = 4 * k + 4 by omega,
    q_three_mul_add_one, q_three_mul_add_two, q_three_mul_add_three,
    Real.log_pow]
  simp only [p]
  rw [alphaStar_four_mul_add_one, alphaStar_four_mul_add_two,
    alphaStar_four_mul_add_three, alphaStar_four_mul_add_four]
  norm_num
  ring

private theorem logQPartial_three_mul_eq_logPPartial_four_mul
    (s : ℝ) (N : ℕ) :
    logQPartial s (3 * N) = logPPartial s (4 * N) := by
  induction N with
  | zero => simp [logQPartial, logPPartial]
  | succ N ih =>
      rw [show 3 * (N + 1) = 3 * N + 3 by omega,
        show 4 * (N + 1) = 4 * N + 4 by omega]
      rw [logQPartial, Finset.sum_range_add,
        logPPartial, Finset.sum_range_add]
      change logQPartial s (3 * N) +
          (∑ i ∈ Finset.range 3, Real.log (q s (3 * N + i + 1))) =
        logPPartial s (4 * N) +
          (∑ i ∈ Finset.range 4, Real.log (p s (4 * N + i + 1)))
      rw [ih, log_block_q_eq_p]

private theorem log_q_from_one_tendsto_zero (s : ℝ) (hs0 : 0 < s) :
    Tendsto (fun k : ℕ => Real.log (q s (k + 1))) atTop (𝓝 0) := by
  have hr1 := reciprocalPower_linear_tendsto_zero s hs0 1 3 (by omega) (by omega)
  have hr2 := reciprocalPower_linear_tendsto_zero s hs0 2 3 (by omega) (by omega)
  have hr3 := reciprocalPower_linear_tendsto_zero s hs0 3 3 (by omega) (by omega)
  have hone : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
  have hq1 : Tendsto (fun k : ℕ => q s (3 * k + 1)) atTop (𝓝 1) := by
    rw [show (fun k : ℕ => q s (3 * k + 1)) =
        (fun k => 1 + reciprocalPower s (1 + 3 * k)) by
      funext k
      exact q_three_mul_add_one s k]
    simpa using hone.add hr1
  have hq2 : Tendsto (fun k : ℕ => q s (3 * k + 2)) atTop (𝓝 1) := by
    rw [show (fun k : ℕ => q s (3 * k + 2)) =
        (fun k => (1 - reciprocalPower s (2 + 3 * k)) ^ 2) by
      funext k
      exact q_three_mul_add_two s k]
    simpa using (hone.sub hr2).pow 2
  have hq3 : Tendsto (fun k : ℕ => q s (3 * k + 3)) atTop (𝓝 1) := by
    rw [show (fun k : ℕ => q s (3 * k + 3)) =
        (fun k => 1 + reciprocalPower s (3 + 3 * k)) by
      funext k
      exact q_three_mul_add_three s k]
    simpa using hone.add hr3
  have h1 : Tendsto (fun k : ℕ => Real.log (q s (3 * k + 1))) atTop (𝓝 0) := by
    simpa using hq1.log (by norm_num : (1 : ℝ) ≠ 0)
  have h2 : Tendsto (fun k : ℕ => Real.log (q s (3 * k + 2))) atTop (𝓝 0) := by
    simpa using hq2.log (by norm_num : (1 : ℝ) ≠ 0)
  have h3 : Tendsto (fun k : ℕ => Real.log (q s (3 * k + 3))) atTop (𝓝 0) := by
    simpa using hq3.log (by norm_num : (1 : ℝ) ≠ 0)
  exact tendsto_of_tendsto_three_residue h1 h2 h3

private theorem log_q_conditional_summable (s : ℝ) (hsHalf : 1 / 2 < s)
    (hs1 : s ≤ 1) : SummableFromOne (fun n => Real.log (q s n)) := by
  have hp := gap17 s hsHalf hs1
  unfold SummableFromOne at hp ⊢
  rcases summable_conditional_iff.mp hp with ⟨l, hl⟩
  have hindex4 : Tendsto (fun k : ℕ => 4 * k) atTop atTop := by
    rw [Filter.tendsto_atTop]
    intro N
    filter_upwards [Filter.eventually_ge_atTop N] with k hk
    omega
  have hp4 : Tendsto (fun k : ℕ => logPPartial s (4 * k)) atTop (𝓝 l) := by
    simpa only [logPPartial] using hl.comp hindex4
  have hq0 : Tendsto (fun k : ℕ => logQPartial s (3 * k)) atTop (𝓝 l) := by
    rw [show (fun k : ℕ => logQPartial s (3 * k)) =
        (fun k => logPPartial s (4 * k)) by
      funext k
      exact logQPartial_three_mul_eq_logPPartial_four_mul s k]
    exact hp4
  have hz := log_q_from_one_tendsto_zero s (by linarith)
  have hz1 :
      Tendsto (fun k : ℕ => Real.log (q s (3 * k + 1))) atTop (𝓝 0) := by
    have h := hz.comp (show Tendsto (fun k : ℕ => 3 * k) atTop atTop by
      rw [Filter.tendsto_atTop]
      intro N
      filter_upwards [Filter.eventually_ge_atTop N] with k hk
      omega)
    simpa only [Function.comp_apply, Nat.mul_add] using h
  have hz2 :
      Tendsto (fun k : ℕ => Real.log (q s (3 * k + 2))) atTop (𝓝 0) := by
    have h := hz.comp (show Tendsto (fun k : ℕ => 3 * k + 1) atTop atTop by
      rw [Filter.tendsto_atTop]
      intro N
      filter_upwards [Filter.eventually_ge_atTop N] with k hk
      omega)
    simpa only [Function.comp_apply] using h
  have hq1 : Tendsto (fun k : ℕ => logQPartial s (3 * k + 1)) atTop (𝓝 l) := by
    rw [show (fun k : ℕ => logQPartial s (3 * k + 1)) =
        (fun k => logQPartial s (3 * k) + Real.log (q s (3 * k + 1))) by
      funext k
      rw [logQPartial, Finset.sum_range_succ]
      change logQPartial s (3 * k) + Real.log (q s (3 * k + 1)) =
        logQPartial s (3 * k) + Real.log (q s (3 * k + 1))
      rfl]
    simpa using hq0.add hz1
  have hq2 : Tendsto (fun k : ℕ => logQPartial s (3 * k + 2)) atTop (𝓝 l) := by
    rw [show (fun k : ℕ => logQPartial s (3 * k + 2)) =
        (fun k => logQPartial s (3 * k + 1) + Real.log (q s (3 * k + 2))) by
      funext k
      rw [show 3 * k + 2 = (3 * k + 1) + 1 by omega, logQPartial,
        Finset.sum_range_succ]
      change logQPartial s (3 * k + 1) + Real.log (q s (3 * k + 2)) =
        logQPartial s (3 * k + 1) + Real.log (q s (3 * k + 2))
      rfl]
    simpa using hq1.add hz2
  apply summable_conditional_iff.mpr
  exact ⟨l, tendsto_of_tendsto_three_residue hq0 hq1 hq2⟩

private theorem log_q_not_absolutely_summable (s : ℝ) (hs0 : 0 < s)
    (hs1 : s ≤ 1) :
    ¬AbsolutelySummableFromOne (fun n => Real.log (q s n)) := by
  intro habs
  unfold AbsolutelySummableFromOne SummableFromOne at habs
  have hstd : Summable (fun k : ℕ => |Real.log (q s (k + 1))|) :=
    summable_of_nonneg_conditional (fun k => abs_nonneg _) habs
  have hinj : Function.Injective (fun k : ℕ => 3 * k) := by
    intro a b hab
    exact Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 3) hab
  have hsub := hstd.comp_injective hinj
  have hlog : Summable (fun k : ℕ =>
      Real.log (1 + reciprocalPower s (1 + 3 * k))) := by
    convert hsub using 1
    funext k
    rw [Function.comp_apply, q_three_mul_add_one]
    rw [abs_of_pos]
    exact Real.log_pos (by
      have := reciprocalPower_pos s (by omega : 1 + 3 * k ≠ 0)
      linarith)
  have hscaled : Summable (fun k : ℕ => reciprocalPower s (1 + 3 * k) / 2) :=
    Summable.of_nonneg_of_le
      (fun k => (div_pos (reciprocalPower_pos s (by omega)) (by norm_num)).le)
      (fun k => reciprocalPower_div_two_le_log_one_add s hs0 (by omega)) hlog
  have htwice := hscaled.mul_left 2
  apply not_summable_reciprocalPower s hs0 hs1
  convert htwice using 1
  funext k
  ring

/-- Exercise 3097, gap 18; retain the full parameter range. -/
theorem gap18 (s : ℝ) (hsHalf : 1 / 2 < s) (hs1 : s ≤ 1) :
    ConditionallySummableFromOne (fun n => Real.log (q s n)) := by
  exact ⟨log_q_conditional_summable s hsHalf hs1,
    log_q_not_absolutely_summable s (by linarith) hs1⟩

end

end ProofGap.Exercise3097
