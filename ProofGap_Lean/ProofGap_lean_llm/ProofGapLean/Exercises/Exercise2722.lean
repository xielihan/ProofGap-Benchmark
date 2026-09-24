import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.PSeries

namespace ProofGap.Exercise2722

noncomputable section

open Filter

def noPole (x : ℝ) : Prop :=
  ∀ n : ℕ, 1 ≤ n → x + n ≠ 0

def term (p x : ℝ) (n : ℕ) : ℝ :=
  (-1 : ℝ) ^ n / Real.rpow |x + n| p

def magnitude (p x : ℝ) (n : ℕ) : ℝ :=
  1 / Real.rpow |x + n| p

def ConditionallySummable (p x : ℝ) : Prop :=
  ProofGap.SeriesConverges (fun n : ℕ => term p x (n + 1)) ∧
    ¬ ProofGap.SeriesConverges (fun n : ℕ => |term p x (n + 1)|)

private theorem abs_term_eq_magnitude (p x : ℝ) (n : ℕ) :
    |term p x n| = magnitude p x n := by
  simp [term, magnitude, abs_div, abs_of_nonneg (Real.rpow_nonneg _ _)]

private theorem summable_magnitude_iff (p x : ℝ) :
    Summable (fun n : ℕ => magnitude p x (n + 1)) ↔ 1 < p := by
  simpa [magnitude, Nat.cast_add, Nat.cast_one, add_assoc, add_comm, add_left_comm] using
    (Real.summable_one_div_nat_add_rpow (x + 1) p)

private theorem base_tendsto_atTop (x : ℝ) :
    Tendsto (fun n : ℕ => x + (n : ℝ)) atTop atTop := by
  simpa [add_comm] using
    (tendsto_natCast_atTop_atTop (R := ℝ)).atTop_add (tendsto_const_nhds (x := x))

private theorem partial_tendsto_of_seriesConverges {f : ℕ → ℝ}
    (hf : ProofGap.SeriesConverges f) :
    ∃ s : ℝ, Tendsto (fun n => ∑ i ∈ Finset.range n, f i) atTop (nhds s) := by
  unfold ProofGap.SeriesConverges at hf
  rcases hf with ⟨s, hs⟩
  refine ⟨s, ?_⟩
  rw [HasSum, SummationFilter.conditional_filter_eq_map_range] at hs
  simpa [Function.comp_def] using hs

private theorem seriesConverges_of_partial_tendsto {f : ℕ → ℝ} {s : ℝ}
    (hf : Tendsto (fun n => ∑ i ∈ Finset.range n, f i) atTop (nhds s)) :
    ProofGap.SeriesConverges f := by
  unfold ProofGap.SeriesConverges
  refine ⟨s, ?_⟩
  rw [HasSum, SummationFilter.conditional_filter_eq_map_range]
  simpa [Function.comp_def] using hf

private theorem seriesConverges_of_summable {f : ℕ → ℝ} (hf : Summable f) :
    ProofGap.SeriesConverges f :=
  seriesConverges_of_partial_tendsto hf.hasSum.tendsto_sum_nat

private theorem summable_of_seriesConverges_of_nonneg {f : ℕ → ℝ}
    (hf0 : ∀ n, 0 ≤ f n) (hf : ProofGap.SeriesConverges f) : Summable f := by
  rcases partial_tendsto_of_seriesConverges hf with ⟨s, hs⟩
  exact ⟨s, (hasSum_iff_tendsto_nat_of_nonneg hf0 s).2 hs⟩

private theorem seriesConverges_term_tendsto_zero {f : ℕ → ℝ}
    (hf : ProofGap.SeriesConverges f) : Tendsto f atTop (nhds 0) := by
  rcases partial_tendsto_of_seriesConverges hf with ⟨s, hs⟩
  have hs' := hs.comp (Filter.tendsto_add_atTop_nat 1)
  have hd := hs'.sub hs
  simpa [Finset.sum_range_succ, add_comm] using hd

private theorem seriesConverges_alternating_of_eventually_antitone
    (a : ℕ → ℝ) (ha : ∃ N : ℕ, AntitoneOn a (Set.Ici N))
    (ha0 : Tendsto a atTop (nhds 0)) :
    ProofGap.SeriesConverges (fun n => (-1 : ℝ) ^ n * a n) := by
  rcases ha with ⟨N, hN⟩
  have htailAnti : Antitone (fun n => a (N + n)) := by
    intro m n hmn
    exact hN (by simp) (by simp) (Nat.add_le_add_left hmn N)
  have htailZero : Tendsto (fun n => a (N + n)) atTop (nhds 0) := by
    have := ha0.comp (Filter.tendsto_add_atTop_nat N)
    simpa [Nat.add_comm] using this
  rcases htailAnti.tendsto_alternating_series_of_tendsto_zero htailZero with ⟨s, hs⟩
  have htail :
      Tendsto (fun n => ∑ i ∈ Finset.range n,
        (-1 : ℝ) ^ (N + i) * a (N + i)) atTop
        (nhds (((-1 : ℝ) ^ N) * s)) := by
    simpa only [Finset.mul_sum, pow_add, mul_assoc] using
      hs.const_mul ((-1 : ℝ) ^ N)
  have hshift :
      Tendsto (fun n => ∑ i ∈ Finset.range (N + n), (-1 : ℝ) ^ i * a i) atTop
        (nhds ((∑ i ∈ Finset.range N, (-1 : ℝ) ^ i * a i) +
          ((-1 : ℝ) ^ N) * s)) := by
    simpa only [Finset.sum_range_add] using
      (tendsto_const_nhds (x := ∑ i ∈ Finset.range N, (-1 : ℝ) ^ i * a i)).add htail
  have hshift' :
      Tendsto (fun n => ∑ i ∈ Finset.range (n + N), (-1 : ℝ) ^ i * a i) atTop
        (nhds ((∑ i ∈ Finset.range N, (-1 : ℝ) ^ i * a i) +
          ((-1 : ℝ) ^ N) * s)) := by
    simpa [Nat.add_comm] using hshift
  exact seriesConverges_of_partial_tendsto
    ((Filter.tendsto_add_atTop_iff_nat N).1 hshift')

theorem gap1 (p x : ℝ) (hp : 1 < p) (hx : noPole x) :
    Summable (fun n : ℕ => |term p x (n + 1)|) := by
  have hs := (summable_magnitude_iff p x).2 hp
  simpa only [abs_term_eq_magnitude] using hs

theorem gap2 (p x : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1) (hx : noPole x) :
    ∃ N : ℕ, AntitoneOn (magnitude p x) (Set.Ici N) := by
  rcases eventually_atTop.1
      ((base_tendsto_atTop x).eventually (eventually_gt_atTop (0 : ℝ))) with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro m hm n hn hmn
  have hmpos : 0 < x + (m : ℝ) := hN m hm
  have hnpos : 0 < x + (n : ℝ) := hN n hn
  have hbase : x + (m : ℝ) ≤ x + (n : ℝ) :=
    add_le_add_right (Nat.cast_le.2 hmn) x
  have hpow := Real.rpow_le_rpow hmpos.le hbase hp0.le
  simpa [magnitude, abs_of_pos hmpos, abs_of_pos hnpos] using
    (one_div_le_one_div_of_le (Real.rpow_pos_of_pos hmpos p) hpow)

theorem gap3 (p x : ℝ) (hp : 0 < p) (hx : noPole x) :
    Tendsto (fun n : ℕ => magnitude p x (n + 1)) atTop (nhds 0) := by
  have hb : Tendsto (fun n : ℕ => x + ((n + 1 : ℕ) : ℝ)) atTop atTop := by
    simpa [Function.comp_def] using
      (base_tendsto_atTop x).comp (Filter.tendsto_add_atTop_nat 1)
  have hpow : Tendsto (fun n : ℕ => (x + ((n + 1 : ℕ) : ℝ)) ^ (-p)) atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop hp).comp hb
  apply hpow.congr'
  filter_upwards [hb.eventually (eventually_gt_atTop (0 : ℝ))] with n hn
  rw [magnitude, abs_of_pos hn, Real.rpow_neg hn.le]
  simp only [one_div]
  unfold Real.rpow
  rw [Real.rpow_def]

theorem gap4 (p x : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1) (hx : noPole x) :
    ConditionallySummable p x := by
  rcases gap2 p x hp0 hp1 hx with ⟨N, hN⟩
  have ha : ∃ N : ℕ,
      AntitoneOn (fun n : ℕ => magnitude p x (n + 1)) (Set.Ici N) := by
    refine ⟨N, ?_⟩
    intro m hm n hn hmn
    apply hN
    · exact hm.trans (Nat.le_succ m)
    · exact hn.trans (Nat.le_succ n)
    · omega
  have halt := seriesConverges_alternating_of_eventually_antitone
    (fun n : ℕ => magnitude p x (n + 1)) ha (gap3 p x hp0 hx)
  have hterm : ProofGap.SeriesConverges (fun n : ℕ => term p x (n + 1)) := by
    have hneg := halt.neg
    change Summable (fun n : ℕ => term p x (n + 1)) (SummationFilter.conditional ℕ)
    convert hneg using 1
    funext n
    simp only [term, magnitude, pow_succ]
    ring
  refine ⟨hterm, ?_⟩
  intro habs
  have hmag : ProofGap.SeriesConverges (fun n : ℕ => magnitude p x (n + 1)) := by
    simpa only [abs_term_eq_magnitude] using habs
  have hs := summable_of_seriesConverges_of_nonneg
    (fun n => by
      unfold magnitude
      exact div_nonneg zero_le_one (Real.rpow_nonneg (abs_nonneg _) p) :
      ∀ n, 0 ≤ magnitude p x (n + 1)) hmag
  exact (not_lt_of_ge hp1) ((summable_magnitude_iff p x).1 hs)

theorem gap5 (p x : ℝ) (hp : p ≤ 0) (hx : noPole x) :
    ¬ Tendsto (fun n : ℕ => term p x (n + 1)) atTop (nhds 0) := by
  intro ht
  have hmag : Tendsto (fun n : ℕ => magnitude p x (n + 1)) atTop (nhds 0) := by
    simpa only [abs_zero, abs_term_eq_magnitude] using ht.abs
  have hb : Tendsto (fun n : ℕ => x + ((n + 1 : ℕ) : ℝ)) atTop atTop := by
    simpa [Function.comp_def] using
      (base_tendsto_atTop x).comp (Filter.tendsto_add_atTop_nat 1)
  have hbound : ∀ᶠ n : ℕ in atTop, 1 ≤ magnitude p x (n + 1) := by
    filter_upwards [hb.eventually (eventually_ge_atTop (1 : ℝ))] with n hn
    have hnpos : 0 < x + ((n + 1 : ℕ) : ℝ) := zero_lt_one.trans_le hn
    have hpow := Real.rpow_le_one_of_one_le_of_nonpos hn hp
    rw [magnitude, abs_of_pos hnpos]
    simpa [one_div] using
      (one_div_le_one_div_of_le (Real.rpow_pos_of_pos hnpos p) hpow)
  have hlt : ∀ᶠ n : ℕ in atTop, magnitude p x (n + 1) < 1 :=
    (tendsto_order.1 hmag).2 1 zero_lt_one
  rcases (hbound.and hlt).exists with ⟨n, hn, hn'⟩
  exact (not_lt_of_ge hn) hn'

theorem gap6 (p x : ℝ) (hp : p ≤ 0) (hx : noPole x) :
    ¬ Summable (fun n : ℕ => term p x (n + 1)) := by
  intro hs
  exact gap5 p x hp hx hs.tendsto_atTop_zero

theorem gap7 :
    {q : ℝ × ℝ |
        noPole q.2 ∧ Summable (fun n : ℕ => |term q.1 q.2 (n + 1)|)} =
      {q : ℝ × ℝ | noPole q.2 ∧ 1 < q.1} := by
  ext q
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨hq, hs⟩
    have hm : Summable (fun n : ℕ => magnitude q.1 q.2 (n + 1)) := by
      simpa only [abs_term_eq_magnitude] using hs
    exact ⟨hq, (summable_magnitude_iff q.1 q.2).1 hm⟩
  · rintro ⟨hq, hp⟩
    exact ⟨hq, gap1 q.1 q.2 hp hq⟩

theorem gap8 :
    {q : ℝ × ℝ | noPole q.2 ∧ ConditionallySummable q.1 q.2} =
      {q : ℝ × ℝ | noPole q.2 ∧ 0 < q.1 ∧ q.1 ≤ 1} := by
  ext q
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨hq, hc⟩
    have hp0 : 0 < q.1 := by
      by_contra h
      have hp : q.1 ≤ 0 := le_of_not_gt h
      exact gap5 q.1 q.2 hp hq (seriesConverges_term_tendsto_zero hc.1)
    have hp1 : q.1 ≤ 1 := by
      by_contra h
      have hp : 1 < q.1 := lt_of_not_ge h
      exact hc.2 (seriesConverges_of_summable (gap1 q.1 q.2 hp hq))
    exact ⟨hq, hp0, hp1⟩
  · rintro ⟨hq, hp0, hp1⟩
    exact ⟨hq, gap4 q.1 q.2 hp0 hp1 hq⟩

theorem gap9 :
    {q : ℝ × ℝ |
        noPole q.2 ∧ ¬ ProofGap.SeriesConverges (fun n : ℕ => term q.1 q.2 (n + 1))} =
      {q : ℝ × ℝ | noPole q.2 ∧ q.1 ≤ 0} := by
  ext q
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨hq, hdiv⟩
    have hp : q.1 ≤ 0 := by
      by_contra h
      have hp0 : 0 < q.1 := lt_of_not_ge h
      by_cases hp1 : q.1 ≤ 1
      · exact hdiv (gap4 q.1 q.2 hp0 hp1 hq).1
      · have hpgt : 1 < q.1 := lt_of_not_ge hp1
        have habs := gap1 q.1 q.2 hpgt hq
        have hnorm : Summable (fun n : ℕ => ‖term q.1 q.2 (n + 1)‖) := by
          simpa only [Real.norm_eq_abs] using habs
        exact hdiv (seriesConverges_of_summable hnorm.of_norm)
    exact ⟨hq, hp⟩
  · rintro ⟨hq, hp⟩
    refine ⟨hq, ?_⟩
    intro hconv
    exact gap5 q.1 q.2 hp hq (seriesConverges_term_tendsto_zero hconv)

end

end ProofGap.Exercise2722
