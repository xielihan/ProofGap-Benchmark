import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.PSeries

namespace ProofGap.Exercise2693

noncomputable section

open Filter

def term (p q : ℝ) (n : ℕ) : ℝ :=
  if Odd n then 1 / Real.rpow n p else -(1 / Real.rpow n q)

def ConditionallySummable (f : ℕ → ℝ) : Prop :=
  ProofGap.SeriesConverges f ∧
    ¬ ProofGap.SeriesConverges (fun n => |f n|)

private theorem seriesConverges_iff_tendsto_sum_range (a : ℕ → ℝ) :
    ProofGap.SeriesConverges a ↔
      ∃ l, Tendsto (fun n => ∑ i ∈ Finset.range n, a i) atTop (nhds l) := by
  unfold ProofGap.SeriesConverges Summable HasSum
  rw [SummationFilter.conditional_filter_eq_map_range]
  simp only [Filter.tendsto_map'_iff]
  rfl

private theorem seriesConverges_of_summable {a : ℕ → ℝ} (ha : Summable a) :
    ProofGap.SeriesConverges a := by
  rcases ha with ⟨l, hl⟩
  exact ⟨l, hl.mono_left SummationFilter.LeAtTop.le_atTop⟩

private theorem tendsto_two_mul :
    Tendsto (fun n : ℕ => 2 * n) atTop atTop := by
  rw [Filter.tendsto_atTop]
  intro b
  exact Filter.eventually_atTop.mpr ⟨b, by intro a ha; omega⟩

private theorem tendsto_two_mul_add_one :
    Tendsto (fun n : ℕ => 2 * n + 1) atTop atTop := by
  rw [Filter.tendsto_atTop]
  intro b
  exact Filter.eventually_atTop.mpr ⟨b, by intro a ha; omega⟩

private theorem summable_one_div_shift_iff (p : ℝ) :
    Summable (fun n : ℕ => 1 / Real.rpow (n + 1) p) ↔ 1 < p := by
  constructor
  · intro h
    apply Real.summable_one_div_nat_rpow.mp
    apply (summable_nat_add_iff
      (f := fun n : ℕ => 1 / Real.rpow n p) 1).mp
    simpa [Nat.cast_add] using h
  · intro h
    have hs := (summable_nat_add_iff
      (f := fun n : ℕ => 1 / Real.rpow n p) 1).mpr
      (Real.summable_one_div_nat_rpow.mpr h)
    simpa [Nat.cast_add] using hs

private theorem tendsto_one_div_shift_zero (p : ℝ) (hp : 0 < p) :
    Tendsto (fun n : ℕ => 1 / Real.rpow (n + 1) p) atTop (nhds 0) := by
  have hbase : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hpow : Tendsto (fun n : ℕ => Real.rpow ((n + 1 : ℕ) : ℝ) (-p))
      atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop hp).comp hbase
  convert hpow using 1
  funext n
  rw [Nat.cast_add, Nat.cast_one]
  simpa only [one_div] using
    (Real.rpow_neg (x := (n : ℝ) + 1) (by positivity) p).symm

private theorem antitone_one_div_shift (p : ℝ) (hp : 0 < p) :
    Antitone (fun n : ℕ => 1 / Real.rpow (n + 1) p) := by
  intro a b hab
  apply one_div_le_one_div_of_le (Real.rpow_pos_of_pos (by positivity) p)
  exact Real.rpow_le_rpow (by positivity)
    (by exact_mod_cast Nat.add_le_add_right hab 1) hp.le

private theorem term_same (p : ℝ) (n : ℕ) :
    term p p (n + 1) =
      (-1 : ℝ) ^ n * (1 / Real.rpow (n + 1) p) := by
  cases Nat.even_or_odd n with
  | inl he =>
      have hodd : Odd (n + 1) := he.add_one
      rw [term, if_pos hodd, he.neg_one_pow]
      simp [Nat.cast_add]
  | inr ho =>
      have heven : Even (n + 1) := ho.add_one
      have hnot : ¬ Odd (n + 1) := Nat.not_odd_iff_even.mpr heven
      rw [term, if_neg hnot, ho.neg_one_pow]
      simp [Nat.cast_add]

private theorem abs_term_same (p : ℝ) (n : ℕ) :
    |term p p (n + 1)| = 1 / Real.rpow (n + 1) p := by
  have hpos : 0 < 1 / Real.rpow ((n + 1 : ℕ) : ℝ) p :=
    one_div_pos.mpr (Real.rpow_pos_of_pos (by positivity) p)
  unfold term
  split_ifs
  · rw [abs_of_pos hpos]
    simp [Nat.cast_add]
  · rw [abs_neg, abs_of_pos hpos]
    simp [Nat.cast_add]

private theorem seriesConverges_term_same (p : ℝ) (hp : 0 < p) :
    ProofGap.SeriesConverges (fun n : ℕ => term p p (n + 1)) := by
  rw [seriesConverges_iff_tendsto_sum_range]
  rcases (antitone_one_div_shift p hp).tendsto_alternating_series_of_tendsto_zero
      (tendsto_one_div_shift_zero p hp) with ⟨l, hl⟩
  exact ⟨l, by simpa only [term_same] using hl⟩

private theorem seriesConverges_tendsto_zero {a : ℕ → ℝ}
    (ha : ProofGap.SeriesConverges a) : Tendsto a atTop (nhds 0) := by
  rw [seriesConverges_iff_tendsto_sum_range] at ha
  rcases ha with ⟨l, hl⟩
  have hshift := hl.comp (tendsto_add_atTop_nat 1)
  have hsub := hshift.sub hl
  have hsub' : Tendsto
      (fun n => (∑ i ∈ Finset.range (n + 1), a i) -
        ∑ i ∈ Finset.range n, a i) atTop (nhds 0) := by
    simpa only [Function.comp_apply, sub_self] using hsub
  convert hsub' using 1
  funext n
  rw [Finset.sum_range_succ]
  ring

private theorem seriesConverges_tail_one {a : ℕ → ℝ}
    (ha : ProofGap.SeriesConverges a) :
    ProofGap.SeriesConverges (fun n => a (n + 1)) := by
  rw [seriesConverges_iff_tendsto_sum_range] at ha ⊢
  rcases ha with ⟨l, hl⟩
  refine ⟨l - a 0, ?_⟩
  have hshift : Tendsto (fun n => ∑ i ∈ Finset.range (n + 1), a i)
      atTop (nhds l) := by
    simpa only [Function.comp_apply] using hl.comp (tendsto_add_atTop_nat 1)
  have hconst : Tendsto (fun _ : ℕ => a 0) atTop (nhds (a 0)) :=
    tendsto_const_nhds
  have hlim := hshift.sub hconst
  convert hlim using 1
  funext n
  induction n with
  | zero => simp
  | succ n ih =>
      calc
        (∑ i ∈ Finset.range (n + 1), a (i + 1)) =
            (∑ i ∈ Finset.range n, a (i + 1)) + a (n + 1) := by
          rw [Finset.sum_range_succ]
        _ = ((∑ i ∈ Finset.range (n + 1), a i) - a 0) + a (n + 1) := by
          rw [ih]
        _ = (∑ i ∈ Finset.range (n + 1 + 1), a i) - a 0 := by
          have hs : (∑ i ∈ Finset.range (n + 1 + 1), a i) =
              (∑ i ∈ Finset.range (n + 1), a i) + a (n + 1) := by
            rw [Finset.sum_range_succ]
          rw [hs]
          ring

private theorem seriesConverges_nat_add {a : ℕ → ℝ}
    (ha : ProofGap.SeriesConverges a) (N : ℕ) :
    ProofGap.SeriesConverges (fun n => a (n + N)) := by
  induction N with
  | zero => simpa using ha
  | succ N ih =>
      have h := seriesConverges_tail_one ih
      convert h using 1
      funext n
      congr 1
      omega

private theorem seriesConverges_pairs {a : ℕ → ℝ}
    (ha : ProofGap.SeriesConverges a) :
    ProofGap.SeriesConverges (fun n => a (2 * n) + a (2 * n + 1)) := by
  rw [seriesConverges_iff_tendsto_sum_range] at ha ⊢
  rcases ha with ⟨l, hl⟩
  refine ⟨l, ?_⟩
  have hlim : Tendsto (fun n => ∑ i ∈ Finset.range (2 * n), a i)
      atTop (nhds l) := by
    simpa only [Function.comp_apply] using hl.comp tendsto_two_mul
  convert hlim using 1
  funext n
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      rw [show 2 * (n + 1) = 2 * n + 1 + 1 by omega,
        Finset.sum_range_succ, Finset.sum_range_succ]
      abel

private theorem summable_of_seriesConverges_of_nonneg {a : ℕ → ℝ}
    (ha : ProofGap.SeriesConverges a) (h0 : ∀ n, 0 ≤ a n) : Summable a := by
  rw [seriesConverges_iff_tendsto_sum_range] at ha
  rcases ha with ⟨l, hl⟩
  rcases hl.bddAbove_range with ⟨c, hc⟩
  exact summable_of_sum_range_le h0 (fun n => hc ⟨n, rfl⟩)

private theorem term_pair_even (p q : ℝ) (k : ℕ) :
    term p q (2 * k + 1) + term p q (2 * k + 2) =
      1 / Real.rpow (2 * k + 1) p - 1 / Real.rpow (2 * k + 2) q := by
  have heven : Even (2 * k + 2) := by
    rw [show 2 * k + 2 = 2 * (k + 1) by omega]
    exact even_two_mul (k + 1)
  rw [term, if_pos (odd_two_mul_add_one k), term,
    if_neg (Nat.not_odd_iff_even.mpr heven)]
  norm_num [Nat.cast_add, Nat.cast_mul]
  simp only [one_div, sub_eq_add_neg]

private theorem term_pair_odd (p q : ℝ) (k : ℕ) :
    term p q (2 * k + 2) + term p q (2 * k + 3) =
      -(1 / Real.rpow (2 * k + 2) q) + 1 / Real.rpow (2 * k + 3) p := by
  have heven : Even (2 * k + 2) := by
    rw [show 2 * k + 2 = 2 * (k + 1) by omega]
    exact even_two_mul (k + 1)
  have hodd : Odd (2 * k + 3) := by
    rw [show 2 * k + 3 = 2 * (k + 1) + 1 by omega]
    exact odd_two_mul_add_one (k + 1)
  rw [term, if_neg (Nat.not_odd_iff_even.mpr heven), term, if_pos hodd]
  norm_num [Nat.cast_add, Nat.cast_mul]

private theorem abs_term_even (p q : ℝ) (k : ℕ) :
    |term p q (2 * k + 1)| = 1 / Real.rpow (2 * k + 1) p := by
  have hpos : 0 < 1 / Real.rpow ((2 * k + 1 : ℕ) : ℝ) p :=
    one_div_pos.mpr (Real.rpow_pos_of_pos (by positivity) p)
  rw [term, if_pos (odd_two_mul_add_one k), abs_of_pos hpos]
  norm_num [Nat.cast_add, Nat.cast_mul]

private theorem abs_term_odd (p q : ℝ) (k : ℕ) :
    |term p q ((2 * k + 1) + 1)| =
      1 / Real.rpow ((2 * k + 1) + 1) q := by
  have harg : (2 * k + 1) + 1 = 2 * (k + 1) := by omega
  have heven : Even ((2 * k + 1) + 1) := by
    rw [harg]
    exact even_two_mul (k + 1)
  have hpos : 0 < 1 / Real.rpow (((2 * k + 1) + 1 : ℕ) : ℝ) q :=
    one_div_pos.mpr (Real.rpow_pos_of_pos (by positivity) q)
  rw [term, if_neg (Nat.not_odd_iff_even.mpr heven), abs_neg, abs_of_pos hpos]
  norm_num [Nat.cast_add, Nat.cast_mul]

private theorem left_pseries_le_sparse (p : ℝ) (hp : 0 < p) (k : ℕ) :
    1 / Real.rpow (k + 1) p ≤
      Real.rpow 2 p * (1 / Real.rpow (2 * k + 1) p) := by
  let A : ℝ := Real.rpow ((k + 1 : ℕ) : ℝ) p
  let B : ℝ := Real.rpow ((2 * k + 1 : ℕ) : ℝ) p
  let C : ℝ := Real.rpow 2 p
  have hApos : 0 < A := by
    dsimp [A]
    exact Real.rpow_pos_of_pos (by positivity) p
  have hBpos : 0 < B := by
    dsimp [B]
    exact Real.rpow_pos_of_pos (by positivity) p
  have hbasele : (((2 * k + 1 : ℕ) : ℝ)) ≤
      2 * (((k + 1 : ℕ) : ℝ)) := by
    exact_mod_cast (show 2 * k + 1 ≤ 2 * (k + 1) by omega)
  have hpowle : B ≤ C * A := by
    dsimp [A, B, C]
    calc
      Real.rpow (((2 * k + 1 : ℕ) : ℝ)) p ≤
          Real.rpow (2 * (((k + 1 : ℕ) : ℝ))) p :=
        Real.rpow_le_rpow (by positivity) hbasele hp.le
      _ = Real.rpow 2 p * Real.rpow (((k + 1 : ℕ) : ℝ)) p :=
        Real.mul_rpow (by positivity) (by positivity)
  have hfrac : B / (A * B) ≤ (C * A) / (A * B) :=
    (div_le_div_iff_of_pos_right (mul_pos hApos hBpos)).mpr hpowle
  have hfinal : 1 / A ≤ C * (1 / B) := by
    calc
      1 / A = B / (A * B) := by field_simp
      _ ≤ (C * A) / (A * B) := hfrac
      _ = C * (1 / B) := by field_simp
  simpa [A, B, C, Nat.cast_add, Nat.cast_mul] using hfinal

private theorem not_summable_abs_of_left (p q : ℝ) (hp : 0 < p) (hcrit : p ≤ 1) :
    ¬ Summable (fun n : ℕ => |term p q (n + 1)|) := by
  intro hs
  have hsparse := hs.comp_injective (i := fun k : ℕ => 2 * k) (by
    intro a b hab
    exact Nat.mul_left_cancel (by decide : 0 < 2) hab)
  have hsparse' : Summable (fun k : ℕ => 1 / Real.rpow (2 * k + 1) p) := by
    refine hsparse.congr ?_
    intro k
    change |term p q (2 * k + 1)| = 1 / Real.rpow (2 * k + 1) p
    exact abs_term_even p q k
  have hmajor := hsparse'.mul_left (Real.rpow 2 p)
  have hshift : Summable (fun k : ℕ => 1 / Real.rpow (k + 1) p) :=
    Summable.of_nonneg_of_le (fun k =>
      (one_div_pos.mpr (Real.rpow_pos_of_pos (by positivity) p)).le)
      (left_pseries_le_sparse p hp) hmajor
  exact (not_lt_of_ge hcrit) ((summable_one_div_shift_iff p).mp hshift)

private theorem not_summable_abs_of_right (p q : ℝ) (hq : 0 < q) (hcrit : q ≤ 1) :
    ¬ Summable (fun n : ℕ => |term p q (n + 1)|) := by
  intro hs
  have hsparse := hs.comp_injective (i := fun k : ℕ => 2 * k + 1) (by
    intro a b hab
    exact Nat.mul_left_cancel (by decide : 0 < 2) (Nat.add_right_cancel hab))
  have hsparse' : Summable
      (fun k : ℕ => 1 / Real.rpow ((2 * k + 1) + 1) q) := by
    refine hsparse.congr ?_
    intro k
    change |term p q ((2 * k + 1) + 1)| =
      1 / Real.rpow ((2 * k + 1) + 1) q
    exact abs_term_odd p q k
  have hscaled := hsparse'.mul_left (Real.rpow 2 q)
  have hshift : Summable (fun k : ℕ => 1 / Real.rpow (k + 1) q) := by
    convert hscaled using 1
    funext k
    have hkpos : 0 < (k : ℝ) + 1 := by positivity
    have htwo : 0 < (2 : ℝ) := by norm_num
    rw [show (2 : ℝ) * (k : ℝ) + 1 + 1 = 2 * ((k : ℝ) + 1) by ring]
    have hmul : Real.rpow (2 * ((k : ℝ) + 1)) q =
        Real.rpow 2 q * Real.rpow ((k : ℝ) + 1) q :=
      Real.mul_rpow htwo.le hkpos.le
    rw [hmul]
    field_simp [ne_of_gt (Real.rpow_pos_of_pos htwo q),
      ne_of_gt (Real.rpow_pos_of_pos hkpos q)]
  exact (not_lt_of_ge hcrit) ((summable_one_div_shift_iff q).mp hshift)

private theorem sparse_left_not_summable (p : ℝ) (hp : 0 < p) (hcrit : p ≤ 1) :
    ¬ Summable (fun k : ℕ => 1 / Real.rpow (2 * k + 1) p) := by
  intro hsparse
  have hmajor := hsparse.mul_left (Real.rpow 2 p)
  have hshift : Summable (fun k : ℕ => 1 / Real.rpow (k + 1) p) :=
    Summable.of_nonneg_of_le (fun _ =>
      (one_div_pos.mpr (Real.rpow_pos_of_pos (by positivity) p)).le)
      (left_pseries_le_sparse p hp) hmajor
  exact (not_lt_of_ge hcrit) ((summable_one_div_shift_iff p).mp hshift)

private theorem sparse_right_not_summable (q : ℝ) (hq : 0 < q) (hcrit : q ≤ 1) :
    ¬ Summable (fun k : ℕ => 1 / Real.rpow (2 * k + 2) q) := by
  intro hsparse
  have hscaled := hsparse.mul_left (Real.rpow 2 q)
  have hshift : Summable (fun k : ℕ => 1 / Real.rpow (k + 1) q) := by
    convert hscaled using 1
    funext k
    have hkpos : 0 < (k : ℝ) + 1 := by positivity
    have htwo : 0 < (2 : ℝ) := by norm_num
    rw [show (2 : ℝ) * (k : ℝ) + 2 = 2 * ((k : ℝ) + 1) by ring]
    have hmul : Real.rpow (2 * ((k : ℝ) + 1)) q =
        Real.rpow 2 q * Real.rpow ((k : ℝ) + 1) q :=
      Real.mul_rpow htwo.le hkpos.le
    rw [hmul]
    field_simp [ne_of_gt (Real.rpow_pos_of_pos htwo q),
      ne_of_gt (Real.rpow_pos_of_pos hkpos q)]
  exact (not_lt_of_ge hcrit) ((summable_one_div_shift_iff q).mp hshift)

theorem gap1 (p q : ℝ) (hp : 1 < p) (hq : 1 < q) :
    Summable (fun n : ℕ => |term p q (n + 1)|) := by
  have hp0 : Summable (fun n : ℕ => 1 / Real.rpow (n + 1) p) :=
    (summable_one_div_shift_iff p).mpr hp
  have hq0 : Summable (fun n : ℕ => 1 / Real.rpow (n + 1) q) :=
    (summable_one_div_shift_iff q).mpr hq
  refine Summable.of_nonneg_of_le (fun n => abs_nonneg _) ?_ (hp0.add hq0)
  intro n
  unfold term
  split_ifs
  · have hnon : 0 ≤ 1 / Real.rpow ((n + 1 : ℕ) : ℝ) p :=
      (one_div_pos.mpr (Real.rpow_pos_of_pos (by positivity) p)).le
    rw [abs_of_nonneg hnon]
    simp only [Nat.cast_add, Nat.cast_one]
    exact le_add_of_nonneg_right
      (one_div_nonneg.mpr (Real.rpow_nonneg (by positivity) q))
  · have hnon : 0 ≤ 1 / Real.rpow ((n + 1 : ℕ) : ℝ) q :=
      (one_div_pos.mpr (Real.rpow_pos_of_pos (by positivity) q)).le
    rw [abs_neg, abs_of_nonneg hnon]
    simp only [Nat.cast_add, Nat.cast_one]
    exact le_add_of_nonneg_left
      (one_div_nonneg.mpr (Real.rpow_nonneg (by positivity) p))

theorem gap2 (p q : ℝ) (hp : 0 < p) (hq : 0 < q)
    (hpq : p = q) (hcrit : p ≤ 1) :
    ProofGap.SeriesConverges (fun n : ℕ => term p q (n + 1)) := by
  subst q
  exact seriesConverges_term_same p hp

theorem gap3 (p q : ℝ) (hp : 0 < p) (hq : 0 < q)
    (hpq : p = q) (hcrit : p ≤ 1) :
    ¬ Summable (fun n : ℕ => |term p q (n + 1)|) := by
  subst q
  intro hs
  have hshift : Summable (fun n : ℕ => 1 / Real.rpow (n + 1) p) := by
    simpa only [abs_term_same] using hs
  exact (not_lt_of_ge hcrit) ((summable_one_div_shift_iff p).mp hshift)

theorem gap4 (p q : ℝ) (hp : 0 < p) (hq : 0 < q)
    (hpq : p = q) (hcrit : p ≤ 1) :
    ConditionallySummable (fun n : ℕ => term p q (n + 1)) := by
  refine ⟨gap2 p q hp hq hpq hcrit, ?_⟩
  intro habs
  have habs' : Summable (fun n : ℕ => |term p q (n + 1)|) := by
    rw [seriesConverges_iff_tendsto_sum_range] at habs
    rcases habs with ⟨l, hl⟩
    have hnonneg : ∀ n, 0 ≤ |term p q (n + 1)| := fun n => abs_nonneg _
    rcases hl.bddAbove_range with ⟨c, hc⟩
    exact summable_of_sum_range_le hnonneg (fun n => hc ⟨n, rfl⟩)
  exact gap3 p q hp hq hpq hcrit habs'

theorem gap5 (p q : ℝ) (h : p ≤ 0 ∨ q ≤ 0) :
    ¬ Tendsto (fun n : ℕ => term p q (n + 1)) atTop (nhds 0) := by
  intro ht
  rcases h with hp | hq
  · have hsub := ht.comp tendsto_two_mul
    have hsmall : ∀ᶠ k : ℕ in atTop, term p q (2 * k + 1) < 1 := by
      simpa only [Nat.mul_comm] using
        hsub.eventually (Iio_mem_nhds zero_lt_one)
    rcases hsmall.exists with ⟨k, hk⟩
    have hbase : (1 : ℝ) ≤ ((2 * k + 1 : ℕ) : ℝ) := by
      exact_mod_cast (show 1 ≤ 2 * k + 1 by omega)
    have hrpos : 0 < Real.rpow ((2 * k + 1 : ℕ) : ℝ) p :=
      Real.rpow_pos_of_pos (lt_of_lt_of_le zero_lt_one hbase) p
    have hrle : Real.rpow ((2 * k + 1 : ℕ) : ℝ) p ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hbase hp
    have hone : 1 ≤ 1 / Real.rpow ((2 * k + 1 : ℕ) : ℝ) p :=
      (le_div_iff₀ hrpos).mpr (by simpa using hrle)
    have hlower : 1 ≤ term p q (2 * k + 1) := by
      rw [term, if_pos (odd_two_mul_add_one k)]
      exact hone
    linarith
  · have hsub := ht.comp tendsto_two_mul_add_one
    have hlarge : ∀ᶠ k : ℕ in atTop,
        -1 < term p q ((2 * k + 1) + 1) := by
      exact hsub.eventually (Ioi_mem_nhds neg_one_lt_zero)
    rcases hlarge.exists with ⟨k, hk⟩
    have harg : (2 * k + 1) + 1 = 2 * (k + 1) := by omega
    have heven : Even ((2 * k + 1) + 1) := by
      rw [harg]
      exact even_two_mul (k + 1)
    have hbase : (1 : ℝ) ≤ (((2 * k + 1) + 1 : ℕ) : ℝ) := by
      exact_mod_cast (show 1 ≤ (2 * k + 1) + 1 by omega)
    have hrpos : 0 < Real.rpow (((2 * k + 1) + 1 : ℕ) : ℝ) q :=
      Real.rpow_pos_of_pos (lt_of_lt_of_le zero_lt_one hbase) q
    have hrle : Real.rpow (((2 * k + 1) + 1 : ℕ) : ℝ) q ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hbase hq
    have hone : 1 ≤ 1 / Real.rpow (((2 * k + 1) + 1 : ℕ) : ℝ) q :=
      (le_div_iff₀ hrpos).mpr (by simpa using hrle)
    have hupper : term p q ((2 * k + 1) + 1) ≤ -1 := by
      rw [term, if_neg (Nat.not_odd_iff_even.mpr heven)]
      linarith
    linarith

theorem gap6 (p q : ℝ) (h : p ≤ 0 ∨ q ≤ 0) :
    ¬ ProofGap.SeriesConverges (fun n : ℕ => term p q (n + 1)) := by
  intro hs
  exact gap5 p q h (seriesConverges_tendsto_zero hs)

theorem gap7 (p q : ℝ) (hp : 0 < p) (hq : 0 < q)
    (hpq : p ≠ q) (hcrit : p ≤ 1 ∨ q ≤ 1) :
    ¬ ProofGap.SeriesConverges (fun n : ℕ => term p q (n + 1)) := by
  intro hs
  rcases lt_or_gt_of_ne hpq with hpq' | hqp'
  · have hpcrit : p ≤ 1 := hcrit.elim id (fun hqcrit => hpq'.le.trans hqcrit)
    have hbase : Tendsto (fun k : ℕ => (((2 * k + 1 : ℕ) : ℝ))) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp tendsto_two_mul_add_one
    have hpow : Tendsto (fun k : ℕ =>
        Real.rpow (((2 * k + 1 : ℕ) : ℝ)) (q - p)) atTop atTop := by
      simpa only [Function.comp_apply] using
        (tendsto_rpow_atTop (sub_pos.mpr hpq')).comp hbase
    have hev : ∀ᶠ k : ℕ in atTop,
        (2 : ℝ) ≤ Real.rpow (((2 * k + 1 : ℕ) : ℝ)) (q - p) :=
      hpow.eventually (eventually_ge_atTop 2)
    rcases Filter.eventually_atTop.mp hev with ⟨N, hN⟩
    have hpairs := seriesConverges_pairs hs
    have hpair : ProofGap.SeriesConverges (fun k : ℕ =>
        1 / Real.rpow (2 * k + 1) p - 1 / Real.rpow (2 * k + 2) q) := by
      exact hpairs.congr (fun k => by
        simpa only [Nat.add_assoc] using term_pair_even p q k)
    have htail := seriesConverges_nat_add hpair N
    have htail' : ProofGap.SeriesConverges (fun n : ℕ =>
        1 / Real.rpow (2 * ((n : ℝ) + (N : ℝ)) + 1) p -
          1 / Real.rpow (2 * ((n : ℝ) + (N : ℝ)) + 2) q) := by
      simpa [Nat.cast_add] using htail
    have hbound (n : ℕ) :
        0 ≤ (1 / Real.rpow (2 * (n + N) + 1) p -
          1 / Real.rpow (2 * (n + N) + 2) q) ∧
        (1 / 2 : ℝ) * (1 / Real.rpow (2 * (n + N) + 1) p) ≤
          (1 / Real.rpow (2 * (n + N) + 1) p -
            1 / Real.rpow (2 * (n + N) + 2) q) := by
      let X : ℝ := ((2 * (n + N) + 1 : ℕ) : ℝ)
      let Y : ℝ := ((2 * (n + N) + 2 : ℕ) : ℝ)
      have hX : 0 < X := by dsimp [X]; positivity
      have hY : 0 < Y := by dsimp [Y]; positivity
      have hXY : X ≤ Y := by dsimp [X, Y]; exact_mod_cast (by omega :
        2 * (n + N) + 1 ≤ 2 * (n + N) + 2)
      have hdom : (2 : ℝ) ≤ Real.rpow X (q - p) := by
        simpa [X] using hN (n + N) (by omega)
      have hXp : 0 < Real.rpow X p := Real.rpow_pos_of_pos hX p
      have hYq : 0 < Real.rpow Y q := Real.rpow_pos_of_pos hY q
      have hden : 2 * Real.rpow X p ≤ Real.rpow Y q := by
        calc
          2 * Real.rpow X p ≤ Real.rpow X (q - p) * Real.rpow X p :=
            mul_le_mul_of_nonneg_right hdom (Real.rpow_nonneg hX.le p)
          _ = Real.rpow X p * Real.rpow X (q - p) := by rw [mul_comm]
          _ = Real.rpow X (p + (q - p)) := (Real.rpow_add hX p (q - p)).symm
          _ = Real.rpow X q := by ring_nf
          _ ≤ Real.rpow Y q := Real.rpow_le_rpow hX.le hXY hq.le
      have hrecip : 1 / Real.rpow Y q ≤
          (1 / 2 : ℝ) * (1 / Real.rpow X p) := by
        calc
          1 / Real.rpow Y q ≤ 1 / (2 * Real.rpow X p) :=
            one_div_le_one_div_of_le (mul_pos (by norm_num) hXp) hden
          _ = (1 / 2 : ℝ) * (1 / Real.rpow X p) := by
            field_simp [ne_of_gt hXp]
      have hAinv : 0 < 1 / Real.rpow X p := one_div_pos.mpr hXp
      have hnon : 0 ≤ 1 / Real.rpow X p - 1 / Real.rpow Y q := by
        linarith
      have hhalf : (1 / 2 : ℝ) * (1 / Real.rpow X p) ≤
          1 / Real.rpow X p - 1 / Real.rpow Y q := by
        linarith
      simpa [X, Y, Nat.cast_add, Nat.cast_mul] using And.intro hnon hhalf
    have htailSum : Summable (fun n : ℕ =>
        1 / Real.rpow (2 * (n + N) + 1) p -
          1 / Real.rpow (2 * (n + N) + 2) q) :=
      summable_of_seriesConverges_of_nonneg htail' (fun n => (hbound n).1)
    have hhalfTail : Summable (fun n : ℕ =>
        (1 / 2 : ℝ) * (1 / Real.rpow (2 * (n + N) + 1) p)) :=
      Summable.of_nonneg_of_le (fun _ =>
        mul_nonneg (by norm_num) (one_div_nonneg.mpr (Real.rpow_nonneg (by positivity) p)))
        (fun n => (hbound n).2) htailSum
    have hhalf : Summable (fun k : ℕ =>
        (1 / 2 : ℝ) * (1 / Real.rpow (2 * k + 1) p)) := by
      apply (summable_nat_add_iff (f := fun k : ℕ =>
        (1 / 2 : ℝ) * (1 / Real.rpow (2 * k + 1) p)) N).mp
      simpa [Nat.cast_add] using hhalfTail
    have hsparse : Summable (fun k : ℕ => 1 / Real.rpow (2 * k + 1) p) := by
      have hscaled := hhalf.mul_left 2
      convert hscaled using 1
      funext k
      ring
    exact sparse_left_not_summable p hp hpcrit hsparse
  · have hqcrit : q ≤ 1 := hcrit.elim (fun hpcrit => hqp'.le.trans hpcrit) id
    have hbaseNat : Tendsto (fun k : ℕ => 2 * k + 2) atTop atTop := by
      rw [Filter.tendsto_atTop]
      intro b
      exact Filter.eventually_atTop.mpr ⟨b, by intro a ha; omega⟩
    have hbase : Tendsto (fun k : ℕ => (((2 * k + 2 : ℕ) : ℝ))) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp hbaseNat
    have hpow : Tendsto (fun k : ℕ =>
        Real.rpow (((2 * k + 2 : ℕ) : ℝ)) (p - q)) atTop atTop := by
      simpa only [Function.comp_apply] using
        (tendsto_rpow_atTop (sub_pos.mpr hqp')).comp hbase
    have hev : ∀ᶠ k : ℕ in atTop,
        (2 : ℝ) ≤ Real.rpow (((2 * k + 2 : ℕ) : ℝ)) (p - q) :=
      hpow.eventually (eventually_ge_atTop 2)
    rcases Filter.eventually_atTop.mp hev with ⟨N, hN⟩
    have hpairs := seriesConverges_pairs (seriesConverges_tail_one hs)
    have hpair : ProofGap.SeriesConverges (fun k : ℕ =>
        1 / Real.rpow (2 * k + 2) q - 1 / Real.rpow (2 * k + 3) p) := by
      have hneg := hpairs.neg
      exact hneg.congr (fun k => by
        have hterm := term_pair_odd p q k
        dsimp
        rw [hterm]
        norm_num [Nat.cast_add, Nat.cast_mul]
        ring)
    have htail := seriesConverges_nat_add hpair N
    have htail' : ProofGap.SeriesConverges (fun n : ℕ =>
        1 / Real.rpow (2 * ((n : ℝ) + (N : ℝ)) + 2) q -
          1 / Real.rpow (2 * ((n : ℝ) + (N : ℝ)) + 3) p) := by
      simpa [Nat.cast_add] using htail
    have hbound (n : ℕ) :
        0 ≤ (1 / Real.rpow (2 * (n + N) + 2) q -
          1 / Real.rpow (2 * (n + N) + 3) p) ∧
        (1 / 2 : ℝ) * (1 / Real.rpow (2 * (n + N) + 2) q) ≤
          (1 / Real.rpow (2 * (n + N) + 2) q -
            1 / Real.rpow (2 * (n + N) + 3) p) := by
      let X : ℝ := ((2 * (n + N) + 2 : ℕ) : ℝ)
      let Y : ℝ := ((2 * (n + N) + 3 : ℕ) : ℝ)
      have hX : 0 < X := by dsimp [X]; positivity
      have hY : 0 < Y := by dsimp [Y]; positivity
      have hXY : X ≤ Y := by dsimp [X, Y]; exact_mod_cast (by omega :
        2 * (n + N) + 2 ≤ 2 * (n + N) + 3)
      have hdom : (2 : ℝ) ≤ Real.rpow X (p - q) := by
        simpa [X] using hN (n + N) (by omega)
      have hXq : 0 < Real.rpow X q := Real.rpow_pos_of_pos hX q
      have hYp : 0 < Real.rpow Y p := Real.rpow_pos_of_pos hY p
      have hden : 2 * Real.rpow X q ≤ Real.rpow Y p := by
        calc
          2 * Real.rpow X q ≤ Real.rpow X (p - q) * Real.rpow X q :=
            mul_le_mul_of_nonneg_right hdom (Real.rpow_nonneg hX.le q)
          _ = Real.rpow X q * Real.rpow X (p - q) := by rw [mul_comm]
          _ = Real.rpow X (q + (p - q)) := (Real.rpow_add hX q (p - q)).symm
          _ = Real.rpow X p := by ring_nf
          _ ≤ Real.rpow Y p := Real.rpow_le_rpow hX.le hXY hp.le
      have hrecip : 1 / Real.rpow Y p ≤
          (1 / 2 : ℝ) * (1 / Real.rpow X q) := by
        calc
          1 / Real.rpow Y p ≤ 1 / (2 * Real.rpow X q) :=
            one_div_le_one_div_of_le (mul_pos (by norm_num) hXq) hden
          _ = (1 / 2 : ℝ) * (1 / Real.rpow X q) := by
            field_simp [ne_of_gt hXq]
      have hAinv : 0 < 1 / Real.rpow X q := one_div_pos.mpr hXq
      have hnon : 0 ≤ 1 / Real.rpow X q - 1 / Real.rpow Y p := by
        linarith
      have hhalf : (1 / 2 : ℝ) * (1 / Real.rpow X q) ≤
          1 / Real.rpow X q - 1 / Real.rpow Y p := by
        linarith
      simpa [X, Y, Nat.cast_add, Nat.cast_mul] using And.intro hnon hhalf
    have htailSum : Summable (fun n : ℕ =>
        1 / Real.rpow (2 * (n + N) + 2) q -
          1 / Real.rpow (2 * (n + N) + 3) p) :=
      summable_of_seriesConverges_of_nonneg htail' (fun n => (hbound n).1)
    have hhalfTail : Summable (fun n : ℕ =>
        (1 / 2 : ℝ) * (1 / Real.rpow (2 * (n + N) + 2) q)) :=
      Summable.of_nonneg_of_le (fun _ =>
        mul_nonneg (by norm_num) (one_div_nonneg.mpr (Real.rpow_nonneg (by positivity) q)))
        (fun n => (hbound n).2) htailSum
    have hhalf : Summable (fun k : ℕ =>
        (1 / 2 : ℝ) * (1 / Real.rpow (2 * k + 2) q)) := by
      apply (summable_nat_add_iff (f := fun k : ℕ =>
        (1 / 2 : ℝ) * (1 / Real.rpow (2 * k + 2) q)) N).mp
      simpa [Nat.cast_add] using hhalfTail
    have hsparse : Summable (fun k : ℕ => 1 / Real.rpow (2 * k + 2) q) := by
      have hscaled := hhalf.mul_left 2
      convert hscaled using 1
      funext k
      ring
    exact sparse_right_not_summable q hq hqcrit hsparse

end

end ProofGap.Exercise2693
