import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.PSeries

namespace ProofGap.Exercise2705

noncomputable section

open Filter
open scoped BigOperators

def blockBalance (p q k : ℕ) : ℝ :=
  (∑ i ∈ Finset.Icc 1 p,
      1 / (((p + q) * k + i : ℕ) : ℝ)) -
    (∑ j ∈ Finset.Icc 1 q,
      1 / (((p + q) * k + p + j : ℕ) : ℝ))

def periodicTerm (p q : ℕ) (n : ℕ) : ℝ :=
  if n % (p + q) < p then 1 / ((n : ℝ) + 1)
  else -(1 / ((n : ℝ) + 1))

def chunk (p k : ℕ) : ℝ :=
  ∑ i ∈ Finset.range p, 1 / (((k * p + i + 1 : ℕ) : ℝ))

private theorem seriesConverges_iff_tendsto (f : ℕ → ℝ) :
    ProofGap.SeriesConverges f ↔
      ∃ a : ℝ, Tendsto (fun n : ℕ => ∑ i ∈ Finset.range n, f i) atTop (nhds a) := by
  simp only [ProofGap.SeriesConverges, Summable, HasSum]
  rw [SummationFilter.conditional_filter_eq_map_range]
  simp only [tendsto_map'_iff]
  rfl

private theorem sum_Icc_one_eq_sum_range (f : ℕ → ℝ) (n : ℕ) :
    (∑ i ∈ Finset.Icc 1 n, f i) = ∑ i ∈ Finset.range n, f (i + 1) := by
  symm
  apply Finset.sum_bij (fun i _ => i + 1)
  · intro i hi
    simp only [Finset.mem_range] at hi
    simp only [Finset.mem_Icc]
    omega
  · intro i₁ hi₁ i₂ hi₂ h
    omega
  · intro j hj
    simp only [Finset.mem_Icc] at hj
    refine ⟨j - 1, ?_, ?_⟩
    · simp only [Finset.mem_range]
      omega
    · omega
  · intro i hi
    rfl

private theorem periodic_block_sum (p q k : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) :
    (∑ i ∈ Finset.range (p + q), periodicTerm p q ((p + q) * k + i)) =
      blockBalance p q k := by
  rw [Finset.sum_range_add]
  unfold blockBalance
  rw [sum_Icc_one_eq_sum_range, sum_Icc_one_eq_sum_range]
  congr 1
  · apply Finset.sum_congr rfl
    intro i hi
    have hip : i < p := Finset.mem_range.mp hi
    have him : i < p + q := by omega
    simp only [periodicTerm]
    rw [if_pos]
    · congr 2
      push_cast
      ring
    · simpa [Nat.add_mod, Nat.mod_eq_of_lt him]
  · calc
      (∑ j ∈ Finset.range q, periodicTerm p q ((p + q) * k + (p + j))) =
          ∑ j ∈ Finset.range q,
            -(1 / (((p + q) * k + p + (j + 1) : ℕ) : ℝ)) := by
            apply Finset.sum_congr rfl
            intro j hj
            have hjq : j < q := Finset.mem_range.mp hj
            have hrem : p + j < p + q := by omega
            simp only [periodicTerm]
            rw [if_neg]
            · congr 2
              norm_cast
              omega
            · simpa [Nat.add_mod, Nat.mod_eq_of_lt hrem]
      _ = -(∑ j ∈ Finset.range q,
            1 / (((p + q) * k + p + (j + 1) : ℕ) : ℝ)) :=
        by simp

private theorem sum_range_blocks (f : ℕ → ℝ) (m n : ℕ) :
    (∑ k ∈ Finset.range n, ∑ i ∈ Finset.range m, f (m * k + i)) =
      ∑ j ∈ Finset.range (m * n), f j := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih, Nat.mul_succ]
      have hblock :
          (∑ i ∈ Finset.range m, f (m * n + i)) =
            ∑ j ∈ Finset.Ico (m * n) (m * n + m), f j := by
        apply Finset.sum_bij (fun i _ => m * n + i)
        · intro i hi
          simp only [Finset.mem_range] at hi
          simp only [Finset.mem_Ico]
          omega
        · intro i₁ hi₁ i₂ hi₂ h
          omega
        · intro j hj
          simp only [Finset.mem_Ico] at hj
          refine ⟨j - m * n, ?_, ?_⟩
          · simp only [Finset.mem_range]
            omega
          · omega
        · intro i hi
          rfl
      rw [hblock, Finset.sum_range_add_sum_Ico]
      omega

private theorem sum_range_shift (f : ℕ → ℝ) (p n : ℕ) :
    (∑ i ∈ Finset.range n, f (i + p)) = ∑ j ∈ Finset.Ico p (p + n), f j := by
  apply Finset.sum_bij (fun i _ => i + p)
  · intro i hi
    simp only [Finset.mem_range] at hi
    simp only [Finset.mem_Ico]
    omega
  · intro i₁ hi₁ i₂ hi₂ h
    omega
  · intro j hj
    simp only [Finset.mem_Ico] at hj
    refine ⟨j - p, ?_, ?_⟩
    · simp only [Finset.mem_range]
      omega
    · omega
  · intro i hi
    rfl

private theorem seriesConverges_of_summable {f : ℕ → ℝ} (h : Summable f) :
    ProofGap.SeriesConverges f := by
  rw [seriesConverges_iff_tendsto]
  exact ⟨_, h.hasSum.tendsto_sum_nat⟩

private theorem seriesConverges_congr {f g : ℕ → ℝ} (hfg : ∀ n, f n = g n)
    (hf : ProofGap.SeriesConverges f) : ProofGap.SeriesConverges g := by
  rw [seriesConverges_iff_tendsto] at hf ⊢
  obtain ⟨a, ha⟩ := hf
  refine ⟨a, ha.congr' (Filter.Eventually.of_forall fun n => ?_)⟩
  exact Finset.sum_congr rfl fun i hi => hfg i

private theorem seriesConverges_neg {f : ℕ → ℝ} (hf : ProofGap.SeriesConverges f) :
    ProofGap.SeriesConverges (fun n => -f n) := by
  rw [seriesConverges_iff_tendsto] at hf ⊢
  obtain ⟨a, ha⟩ := hf
  refine ⟨-a, ?_⟩
  simpa using ha.neg

private theorem seriesConverges_add {f g : ℕ → ℝ}
    (hf : ProofGap.SeriesConverges f) (hg : ProofGap.SeriesConverges g) :
    ProofGap.SeriesConverges (fun n => f n + g n) := by
  rw [seriesConverges_iff_tendsto] at hf hg ⊢
  obtain ⟨a, ha⟩ := hf
  obtain ⟨b, hb⟩ := hg
  refine ⟨a + b, ?_⟩
  simpa [Finset.sum_add_distrib] using ha.add hb

private theorem seriesConverges_shift {f : ℕ → ℝ} (p : ℕ)
    (hf : ProofGap.SeriesConverges f) :
    ProofGap.SeriesConverges (fun n => f (n + p)) := by
  rw [seriesConverges_iff_tendsto] at hf ⊢
  obtain ⟨a, ha⟩ := hf
  refine ⟨a - ∑ i ∈ Finset.range p, f i, ?_⟩
  have htotal := ha.comp (tendsto_add_atTop_nat p)
  convert htotal.sub_const (∑ i ∈ Finset.range p, f i) using 1
  funext n
  simp only [Function.comp_apply]
  rw [sum_range_shift]
  apply eq_sub_of_add_eq
  simpa [Nat.add_comm, add_comm] using
    Finset.sum_range_add_sum_Ico f (show p ≤ p + n by omega)

private theorem shifted_mod_lt_iff (p q n : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) :
    (n + p) % (p + q) < p ↔ q ≤ n % (p + q) := by
  have hm0 : p + q ≠ 0 := by omega
  have hr : n % (p + q) < p + q := Nat.mod_lt n (by omega)
  have hpmod : p % (p + q) = p := Nat.mod_eq_of_lt (by omega)
  rw [Nat.add_mod, hpmod]
  by_cases hlt : n % (p + q) + p < p + q
  · rw [Nat.mod_eq_of_lt hlt]
    omega
  · have hge : p + q ≤ n % (p + q) + p := by omega
    rw [Nat.mod_eq_sub_mod hge]
    have hsub : n % (p + q) + p - (p + q) < p + q := by omega
    rw [Nat.mod_eq_of_lt hsub]
    omega

private theorem abs_swap_difference (p q n : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) :
    |periodicTerm q p n + periodicTerm p q (n + p)| =
      1 / (((n + 1 : ℕ) : ℝ)) - 1 / (((n + p + 1 : ℕ) : ℝ)) := by
  have hnonneg :
      0 ≤ 1 / (((n + 1 : ℕ) : ℝ)) - 1 / (((n + p + 1 : ℕ) : ℝ)) := by
    apply sub_nonneg.mpr
    apply one_div_le_one_div_of_le
    · positivity
    · norm_cast
      omega
  by_cases h : n % (p + q) < q
  · have hs : ¬(n + p) % (p + q) < p := by
      rw [shifted_mod_lt_iff p q n hp hq]
      omega
    have hfirst : n % (q + p) < q := by simpa [Nat.add_comm] using h
    simp only [periodicTerm]
    rw [if_pos hfirst, if_neg hs]
    rw [abs_of_nonneg]
    · push_cast
      ring
    · simpa only [Nat.cast_add, Nat.cast_one, sub_eq_add_neg] using hnonneg
  · have hr : q ≤ n % (p + q) := by omega
    have hs : (n + p) % (p + q) < p :=
      (shifted_mod_lt_iff p q n hp hq).2 hr
    have hfirst : ¬n % (q + p) < q := by simpa [Nat.add_comm] using h
    simp only [periodicTerm]
    rw [if_neg hfirst, if_pos hs]
    rw [show -(1 / ((n : ℝ) + 1)) + 1 / (((n + p : ℕ) : ℝ) + 1) =
        -(1 / ((n : ℝ) + 1) - 1 / (((n + p : ℕ) : ℝ) + 1)) by ring,
      abs_neg, abs_of_nonneg]
    · push_cast
      ring
    · simpa only [Nat.cast_add, Nat.cast_one] using hnonneg

private theorem summable_harmonic_shift_difference (p : ℕ) :
    Summable (fun n : ℕ =>
      1 / (((n + 1 : ℕ) : ℝ)) - 1 / (((n + p + 1 : ℕ) : ℝ))) := by
  let h : ℕ → ℝ := fun n => 1 / (((n + 1 : ℕ) : ℝ))
  let c : ℝ := ∑ i ∈ Finset.range p, h i
  have hnonneg : ∀ n : ℕ, 0 ≤ h n - h (n + p) := by
    intro n
    apply sub_nonneg.mpr
    apply one_div_le_one_div_of_le
    · dsimp [h]
      positivity
    · dsimp [h]
      norm_cast
      omega
  have hsum (n : ℕ) :
      (∑ i ∈ Finset.range n, (h i - h (i + p))) =
        c - ∑ i ∈ Finset.range p, h (n + i) := by
    dsimp [c]
    have hright :
        (∑ i ∈ Finset.range p, h (n + i)) = ∑ j ∈ Finset.Ico n (n + p), h j := by
      calc
        (∑ i ∈ Finset.range p, h (n + i)) = ∑ i ∈ Finset.range p, h (i + n) := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [Nat.add_comm]
        _ = ∑ j ∈ Finset.Ico n (n + p), h j := sum_range_shift h n p
    rw [Finset.sum_sub_distrib, sum_range_shift h p n, hright]
    rw [Finset.sum_Ico_eq_sub, Finset.sum_Ico_eq_sub]
    · rw [Nat.add_comm p n]
      ring
    · omega
    · omega
  have htail : Tendsto (fun n : ℕ => ∑ i ∈ Finset.range p, h (n + i)) atTop (nhds 0) := by
    have hi (i : ℕ) : Tendsto (fun n : ℕ => h (n + i)) atTop (nhds 0) := by
      dsimp [h]
      convert (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp
        (tendsto_add_atTop_nat i) using 1
      funext n
      simp only [Function.comp_apply, Nat.cast_add, Nat.cast_one]
    simpa using tendsto_finset_sum (Finset.range p) (fun i hi_mem => hi i)
  refine ⟨c, (hasSum_iff_tendsto_nat_of_nonneg hnonneg c).2 ?_⟩
  have hlim : Tendsto (fun n : ℕ => c - ∑ i ∈ Finset.range p, h (n + i)) atTop (nhds c) := by
    simpa using tendsto_const_nhds.sub htail
  convert hlim using 1
  funext n
  exact hsum n

theorem gap1 (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q)
    (hpq : q < p) :
    ∀ k : ℕ,
      blockBalance p q k > 1 / (((p + q) * k + 1 : ℕ) : ℝ) := by
  intro k
  let a := (p + q) * k
  have hpair :
      (∑ j ∈ Finset.Icc 1 q, 1 / (((a + p + j : ℕ) : ℝ))) <
        ∑ j ∈ Finset.Icc 1 q, 1 / (((a + (j + 1) : ℕ) : ℝ)) := by
    apply Finset.sum_lt_sum_of_nonempty
    · exact ⟨1, by simp [hq]⟩
    · intro j hj
      apply one_div_lt_one_div_of_lt
      · positivity
      · norm_cast
        omega
  have hshift :
      (∑ j ∈ Finset.Icc 1 q, 1 / (((a + (j + 1) : ℕ) : ℝ))) =
        ∑ i ∈ Finset.Icc 2 (q + 1), 1 / (((a + i : ℕ) : ℝ)) := by
    apply Finset.sum_bij (fun j _ => j + 1)
    · intro j hj
      simp only [Finset.mem_Icc] at hj ⊢
      omega
    · intro j₁ hj₁ j₂ hj₂ h
      omega
    · intro i hi
      simp only [Finset.mem_Icc] at hi
      refine ⟨i - 1, ?_, ?_⟩
      · simp only [Finset.mem_Icc]
        omega
      · omega
    · intro j hj
      rfl
  have hsubset : Finset.Icc 2 (q + 1) ⊆ Finset.Icc 2 p := by
    intro i hi
    simp only [Finset.mem_Icc] at hi ⊢
    omega
  have htail :
      (∑ j ∈ Finset.Icc 1 q, 1 / (((a + p + j : ℕ) : ℝ))) <
        ∑ i ∈ Finset.Icc 2 p, 1 / (((a + i : ℕ) : ℝ)) := by
    refine hpair.trans_le ?_
    rw [hshift]
    exact Finset.sum_le_sum_of_subset_of_nonneg hsubset (by intros; positivity)
  have hpos :
      (∑ i ∈ Finset.Icc 1 p, 1 / (((a + i : ℕ) : ℝ))) =
        1 / (((a + 1 : ℕ) : ℝ)) +
          ∑ i ∈ Finset.Icc 2 p, 1 / (((a + i : ℕ) : ℝ)) := by
    rw [← Finset.insert_Icc_succ_left_eq_Icc hp, Finset.sum_insert]
    · rfl
    · simp
  unfold blockBalance
  change
    (∑ i ∈ Finset.Icc 1 p, 1 / (((a + i : ℕ) : ℝ))) -
        (∑ j ∈ Finset.Icc 1 q, 1 / (((a + p + j : ℕ) : ℝ))) >
      1 / (((a + 1 : ℕ) : ℝ))
  rw [hpos]
  linarith

theorem gap2 (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) :
    ∀ k : ℕ, 0 < 1 / (((p + q) * k + 1 : ℕ) : ℝ) := by
  intro k
  positivity

theorem gap3 (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q)
    (hpq : q < p) :
    ∀ k : ℕ, 0 < blockBalance p q k := by
  intro k
  exact (gap2 p q hp hq k).trans (gap1 p q hp hq hpq k)

theorem gap4 (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) :
    ¬ ProofGap.SeriesConverges (fun k : ℕ =>
      1 / (((p + q) * k + 1 : ℕ) : ℝ)) := by
  intro h
  rw [seriesConverges_iff_tendsto] at h
  obtain ⟨a, ha⟩ := h
  have hs : Summable (fun k : ℕ =>
      1 / (((p + q) * k + 1 : ℕ) : ℝ)) := by
    refine ⟨a, (hasSum_iff_tendsto_nat_of_nonneg (fun k => ?_) a).2 ha⟩
    positivity
  letI : NeZero (p + q) := ⟨by omega⟩
  apply Real.not_summable_indicator_one_div_natCast (m := p + q) (by omega) (1 : ZMod (p + q))
  have hi := (summable_indicator_mod_iff_summable (p + q) 1
    (fun n : ℕ => 1 / (n : ℝ))).2 hs
  simpa only [Nat.cast_one] using hi

theorem gap5 (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q)
    (hpq : q < p) :
    ¬ ProofGap.SeriesConverges (blockBalance p q) := by
  intro h
  rw [seriesConverges_iff_tendsto] at h
  obtain ⟨a, ha⟩ := h
  have hs : Summable (blockBalance p q) := by
    refine ⟨a, (hasSum_iff_tendsto_nat_of_nonneg (fun k => (gap3 p q hp hq hpq k).le) a).2 ha⟩
  have hlower : Summable (fun k : ℕ =>
      1 / (((p + q) * k + 1 : ℕ) : ℝ)) :=
    hs.of_nonneg_of_le (fun k => (gap2 p q hp hq k).le)
      (fun k => (gap1 p q hp hq hpq k).le)
  apply gap4 p q hp hq
  rw [seriesConverges_iff_tendsto]
  exact ⟨_, hlower.hasSum.tendsto_sum_nat⟩

theorem gap6 (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q)
    (hpq : q < p) :
    ¬ ProofGap.SeriesConverges (periodicTerm p q) := by
  intro h
  apply gap5 p q hp hq hpq
  rw [seriesConverges_iff_tendsto] at h ⊢
  obtain ⟨a, ha⟩ := h
  refine ⟨a, ?_⟩
  have hmpos : 0 < p + q := by omega
  have hm : Tendsto (fun n : ℕ => (p + q) * n) atTop atTop :=
    (strictMono_nat_of_lt_succ fun n =>
      Nat.mul_lt_mul_of_pos_left (Nat.lt_succ_self n) hmpos).tendsto_atTop
  convert ha.comp hm using 1
  funext n
  simp only [Function.comp_apply]
  rw [← sum_range_blocks]
  apply Finset.sum_congr rfl
  intro k hk
  exact (periodic_block_sum p q k hp hq).symm

theorem gap7 (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q)
    (hpq : p < q) :
    ¬ ProofGap.SeriesConverges (periodicTerm p q) := by
  intro h
  have htail : ProofGap.SeriesConverges (fun n => periodicTerm p q (n + p)) :=
    seriesConverges_shift p h
  have hneg : ProofGap.SeriesConverges (fun n => -periodicTerm p q (n + p)) :=
    seriesConverges_neg htail
  have hdiffSummable : Summable (fun n =>
      periodicTerm q p n + periodicTerm p q (n + p)) := by
    apply Summable.of_norm
    refine (summable_harmonic_shift_difference p).congr (fun n => ?_)
    rw [Real.norm_eq_abs, abs_swap_difference p q n hp hq]
  have hdiff : ProofGap.SeriesConverges (fun n =>
      periodicTerm q p n + periodicTerm p q (n + p)) :=
    seriesConverges_of_summable hdiffSummable
  have hswap' := seriesConverges_add hneg hdiff
  have hswap : ProofGap.SeriesConverges (periodicTerm q p) :=
    seriesConverges_congr (fun n => by ring) hswap'
  exact gap6 q p hq hp hpq hswap

theorem gap8 (p : ℕ) (hp : 1 ≤ p) :
    ∀ k : ℕ, 0 < chunk p k := by
  intro k
  apply Finset.sum_pos
  · intro i hi
    positivity
  · exact ⟨0, Finset.mem_range.mpr hp⟩

theorem gap9 (p : ℕ) (hp : 1 ≤ p) :
    ∀ k : ℕ, chunk p (k + 1) < chunk p k := by
  intro k
  unfold chunk
  apply Finset.sum_lt_sum_of_nonempty
  · exact ⟨0, Finset.mem_range.mpr hp⟩
  · intro i hi
    apply one_div_lt_one_div_of_lt
    · positivity
    · norm_cast
      have hmul : k * p < (k + 1) * p :=
        Nat.mul_lt_mul_of_pos_right (Nat.lt_succ_self k) (Nat.zero_lt_of_lt hp)
      simpa [Nat.add_assoc] using Nat.add_lt_add_right hmul (i + 1)

theorem gap10 (p : ℕ) (hp : 1 ≤ p) :
    Tendsto (chunk p) atTop (nhds 0) := by
  apply squeeze_zero
  · intro k
    exact (gap8 p hp k).le
  · intro k
    unfold chunk
    calc
      (∑ i ∈ Finset.range p, 1 / (((k * p + i + 1 : ℕ) : ℝ)))
          ≤ ∑ _i ∈ Finset.range p, 1 / (((k + 1 : ℕ) : ℝ)) := by
            gcongr with i hi
            have hmul : k ≤ k * p := by
              simpa using Nat.mul_le_mul_left k hp
            omega
      _ = (p : ℝ) * (1 / (((k + 1 : ℕ) : ℝ))) := by simp
  · simpa only [Nat.cast_add, Nat.cast_one, mul_zero] using
      ((tendsto_const_nhds (x := (p : ℝ))).mul
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)))

theorem gap11 (p : ℕ) (hp : 1 ≤ p) :
    ProofGap.SeriesConverges
      (fun k : ℕ => (-1 : ℝ) ^ k * chunk p k) := by
  rw [seriesConverges_iff_tendsto]
  exact
    (antitone_nat_of_succ_le fun k => (gap9 p hp k).le).tendsto_alternating_series_of_tendsto_zero
      (gap10 p hp)

private theorem periodic_chunk_sum (p k : ℕ) (hp : 1 ≤ p) :
    (∑ i ∈ Finset.range p, periodicTerm p p (p * k + i)) =
      (-1 : ℝ) ^ k * chunk p k := by
  rcases Nat.even_or_odd' k with ⟨r, rfl | rfl⟩
  · rw [show (-1 : ℝ) ^ (2 * r) = 1 by simp]
    simp only [one_mul, chunk]
    apply Finset.sum_congr rfl
    intro i hi
    have hip : i < p := Finset.mem_range.mp hi
    have hmod : (p * (2 * r) + i) % (p + p) = i := by
      have heq : p * (2 * r) + i = (p + p) * r + i := by ring
      rw [heq]
      simpa [Nat.add_mod, Nat.mod_eq_of_lt (show i < p + p by omega)]
    simp only [periodicTerm]
    rw [if_pos]
    · congr 2
      push_cast
      ring
    · simpa [hmod] using hip
  · rw [show (-1 : ℝ) ^ (2 * r + 1) = -1 by simp [pow_succ]]
    rw [neg_one_mul]
    unfold chunk
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    have hip : i < p := Finset.mem_range.mp hi
    have hmod : (p * (2 * r + 1) + i) % (p + p) = p + i := by
      have heq : p * (2 * r + 1) + i = (p + p) * r + (p + i) := by ring
      rw [heq]
      simpa [Nat.add_mod, Nat.mod_eq_of_lt (show p + i < p + p by omega)]
    simp only [periodicTerm]
    rw [if_neg]
    · congr 2
      push_cast
      ring
    · simp [hmod]

private theorem balanced_series_of_chunk_series (p : ℕ) (hp : 1 ≤ p)
    (hchunks : ProofGap.SeriesConverges
      (fun k : ℕ => (-1 : ℝ) ^ k * chunk p k)) :
    ProofGap.SeriesConverges (periodicTerm p p) := by
  rw [seriesConverges_iff_tendsto] at hchunks ⊢
  obtain ⟨a, ha⟩ := hchunks
  have hboundary : Tendsto (fun n : ℕ =>
      ∑ i ∈ Finset.range (p * n), periodicTerm p p i) atTop (nhds a) := by
    convert ha using 1
    funext n
    rw [← sum_range_blocks]
    apply Finset.sum_congr rfl
    intro k hk
    exact periodic_chunk_sum p k hp
  let b : ℕ → ℕ := fun n => p * (n / p)
  have hbtop : Tendsto b atTop atTop := by
    have hmul : Tendsto (fun k : ℕ => p * k) atTop atTop :=
      (strictMono_nat_of_lt_succ fun k =>
        Nat.mul_lt_mul_of_pos_left (Nat.lt_succ_self k) (Nat.zero_lt_of_lt hp)).tendsto_atTop
    exact hmul.comp (Nat.tendsto_div_const_atTop (by omega))
  have hbase : Tendsto (fun n : ℕ =>
      ∑ i ∈ Finset.range (b n), periodicTerm p p i) atTop (nhds a) := by
    exact hboundary.comp (Nat.tendsto_div_const_atTop (by omega))
  have habsTerm (j : ℕ) : |periodicTerm p p j| = 1 / (((j + 1 : ℕ) : ℝ)) := by
    unfold periodicTerm
    split_ifs
    · rw [abs_of_nonneg (by positivity)]
      push_cast
      rfl
    · rw [abs_neg, abs_of_nonneg (by positivity)]
      push_cast
      rfl
  have hbound (n : ℕ) :
      |(∑ i ∈ Finset.range n, periodicTerm p p i) -
          ∑ i ∈ Finset.range (b n), periodicTerm p p i| ≤
        (p : ℝ) * (1 / (((b n + 1 : ℕ) : ℝ))) := by
    have hbn : b n ≤ n := by
      dsimp [b]
      simpa [Nat.mul_comm] using Nat.div_mul_le_self n p
    have hdiff :
        (∑ i ∈ Finset.range n, periodicTerm p p i) -
            ∑ i ∈ Finset.range (b n), periodicTerm p p i =
          ∑ i ∈ Finset.Ico (b n) n, periodicTerm p p i := by
      have hs := Finset.sum_range_add_sum_Ico (periodicTerm p p) hbn
      linarith
    rw [hdiff]
    calc
      |∑ i ∈ Finset.Ico (b n) n, periodicTerm p p i| ≤
          ∑ i ∈ Finset.Ico (b n) n, |periodicTerm p p i| :=
        Finset.abs_sum_le_sum_abs _ _
      _ = ∑ i ∈ Finset.Ico (b n) n, 1 / (((i + 1 : ℕ) : ℝ)) := by
        apply Finset.sum_congr rfl
        intro i hi
        exact habsTerm i
      _ ≤ ∑ _i ∈ Finset.Ico (b n) n, 1 / (((b n + 1 : ℕ) : ℝ)) := by
        apply Finset.sum_le_sum
        intro i hi
        apply one_div_le_one_div_of_le
        · positivity
        · norm_cast
          exact Nat.add_le_add_right (Finset.mem_Ico.mp hi).1 1
      _ = ((Finset.Ico (b n) n).card : ℝ) *
          (1 / (((b n + 1 : ℕ) : ℝ))) := by simp
      _ ≤ (p : ℝ) * (1 / (((b n + 1 : ℕ) : ℝ))) := by
        gcongr
        norm_cast
        simp only [Nat.card_Ico]
        have hdecomp := Nat.mod_add_div n p
        have hmod : n % p < p := Nat.mod_lt n (by omega)
        dsimp [b]
        omega
  have hupper : Tendsto (fun n : ℕ =>
      (p : ℝ) * (1 / (((b n + 1 : ℕ) : ℝ)))) atTop (nhds 0) := by
    have hone : Tendsto (fun n : ℕ => 1 / (((b n + 1 : ℕ) : ℝ))) atTop (nhds 0) := by
      convert (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp hbtop using 1
      funext n
      simp only [Function.comp_apply, Nat.cast_add, Nat.cast_one]
    simpa using (tendsto_const_nhds (x := (p : ℝ))).mul hone
  have habsDiff : Tendsto (fun n : ℕ =>
      |(∑ i ∈ Finset.range n, periodicTerm p p i) -
        ∑ i ∈ Finset.range (b n), periodicTerm p p i|) atTop (nhds 0) :=
    squeeze_zero (fun n => abs_nonneg _) hbound hupper
  have hdiff : Tendsto (fun n : ℕ =>
      (∑ i ∈ Finset.range n, periodicTerm p p i) -
        ∑ i ∈ Finset.range (b n), periodicTerm p p i) atTop (nhds 0) := by
    rwa [tendsto_zero_iff_abs_tendsto_zero]
  refine ⟨a, ?_⟩
  have htotal : Tendsto (fun n : ℕ =>
      (∑ i ∈ Finset.range (b n), periodicTerm p p i) +
        ((∑ i ∈ Finset.range n, periodicTerm p p i) -
          ∑ i ∈ Finset.range (b n), periodicTerm p p i)) atTop (nhds a) := by
    simpa using hbase.add hdiff
  convert htotal using 1
  funext n
  ring

theorem gap12 (p : ℕ) (hp : 1 ≤ p) :
    ProofGap.SeriesConverges (periodicTerm p p) ↔
      ProofGap.SeriesConverges
        (fun k : ℕ => (-1 : ℝ) ^ k * chunk p k) := by
  constructor
  · intro h
    rw [seriesConverges_iff_tendsto] at h ⊢
    obtain ⟨a, ha⟩ := h
    refine ⟨a, ?_⟩
    have hpTop : Tendsto (fun n : ℕ => p * n) atTop atTop :=
      (strictMono_nat_of_lt_succ fun n =>
        Nat.mul_lt_mul_of_pos_left (Nat.lt_succ_self n) (Nat.zero_lt_of_lt hp)).tendsto_atTop
    convert ha.comp hpTop using 1
    funext n
    simp only [Function.comp_apply]
    rw [← sum_range_blocks]
    apply Finset.sum_congr rfl
    intro k hk
    exact (periodic_chunk_sum p k hp).symm
  · exact balanced_series_of_chunk_series p hp

theorem gap13 (p : ℕ) (hp : 1 ≤ p) :
    ProofGap.SeriesConverges (periodicTerm p p) := by
  exact (gap12 p hp).2 (gap11 p hp)

theorem gap14 :
    ∀ p q : ℕ, 1 ≤ p → 1 ≤ q →
      ((p ≠ q → ¬ ProofGap.SeriesConverges (periodicTerm p q)) ∧
        (p = q → ProofGap.SeriesConverges (periodicTerm p q))) := by
  intro p q hp hq
  constructor
  · intro hpq
    rcases lt_or_gt_of_ne hpq with hpq' | hpq'
    · exact gap7 p q hp hq hpq'
    · exact gap6 p q hp hq hpq'
  · intro hpq
    subst q
    exact gap13 p hp

end

end ProofGap.Exercise2705
