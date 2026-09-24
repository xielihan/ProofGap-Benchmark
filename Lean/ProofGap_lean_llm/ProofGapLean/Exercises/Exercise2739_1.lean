import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.PSeries

namespace ProofGap.Exercise2739_1

noncomputable section

open Filter

def fallingFactorial (x : ℝ) (n : ℕ) : ℝ :=
  ∏ k ∈ Finset.range n, (x - k)

def term (x : ℝ) (n : ℕ) : ℝ :=
  fallingFactorial x n / n.factorial

def ConditionallySummable (x : ℝ) : Prop :=
  ProofGap.SeriesConverges (fun n : ℕ => term x (n + 1)) ∧
    ¬ ProofGap.SeriesConverges (fun n : ℕ => |term x (n + 1)|)

private def magnitude (x : ℝ) (n : ℕ) : ℝ :=
  (∏ k ∈ Finset.range n, ((k : ℝ) - x)) / n.factorial

private theorem term_eq_sign_mul_magnitude (x : ℝ) (n : ℕ) :
    term x n = (-1 : ℝ) ^ n * magnitude x n := by
  rw [term, magnitude]
  have hprod :
      fallingFactorial x n =
        (-1 : ℝ) ^ n * ∏ k ∈ Finset.range n, ((k : ℝ) - x) := by
    rw [fallingFactorial]
    calc
      (∏ k ∈ Finset.range n, (x - k)) =
          ∏ k ∈ Finset.range n, -((k : ℝ) - x) := by
            congr 1
            ext k
            ring
      _ = (-1 : ℝ) ^ n * ∏ k ∈ Finset.range n, ((k : ℝ) - x) := by
        rw [Finset.prod_neg]
        simp
  rw [hprod]
  ring

private theorem magnitude_pos (x : ℝ) (hx : x < 0) (n : ℕ) :
    0 < magnitude x n := by
  rw [magnitude]
  apply div_pos
  · apply Finset.prod_pos
    intro k hk
    have hk0 : 0 ≤ (k : ℝ) := by positivity
    linarith
  · exact_mod_cast Nat.factorial_pos n

private theorem magnitude_succ (x : ℝ) (n : ℕ) :
    magnitude x (n + 1) = magnitude x n * ((n : ℝ) - x) / (n + 1) := by
  rw [magnitude, magnitude, Finset.prod_range_succ, Nat.factorial_succ]
  push_cast
  field_simp

private theorem term_succ (x : ℝ) (n : ℕ) :
    term x (n + 1) = term x n * (x - n) / (n + 1) := by
  rw [term, term, fallingFactorial, fallingFactorial, Finset.prod_range_succ,
    Nat.factorial_succ]
  push_cast
  field_simp

private theorem abs_term_eq_magnitude (x : ℝ) (hx : x < 0) (n : ℕ) :
    |term x n| = magnitude x n := by
  rw [term_eq_sign_mul_magnitude, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
    abs_of_pos (magnitude_pos x hx n)]

private theorem magnitude_antitone (x : ℝ) (hx₁ : -1 < x) (hx₂ : x < 0) :
    Antitone (magnitude x) := by
  apply antitone_nat_of_succ_le
  intro n
  rw [magnitude_succ]
  have hmag : 0 ≤ magnitude x n := (magnitude_pos x hx₂ n).le
  have hratio : ((n : ℝ) - x) / (n + 1) ≤ 1 := by
    apply (div_le_one (by positivity)).2
    linarith
  calc
    magnitude x n * ((n : ℝ) - x) / (n + 1) =
        magnitude x n * (((n : ℝ) - x) / (n + 1)) := by ring
    _ ≤ magnitude x n := mul_le_of_le_one_right hmag hratio

private theorem magnitude_tendsto_zero (x : ℝ) (hx₁ : -1 < x) (hx₂ : x < 0) :
    Tendsto (magnitude x) atTop (nhds 0) := by
  let b : ℕ → ℝ := magnitude x
  have hbpos : ∀ n, 0 < b n := fun n ↦ magnitude_pos x hx₂ n
  have hanti : Antitone b := magnitude_antitone x hx₁ hx₂
  have hbdd : BddBelow (Set.range b) := by
    refine ⟨0, ?_⟩
    rintro y ⟨n, rfl⟩
    exact (hbpos n).le
  let L : ℝ := ⨅ n, b n
  have ht : Tendsto b atTop (nhds L) := tendsto_atTop_ciInf hanti hbdd
  have hLnonneg : 0 ≤ L := le_ciInf fun n ↦ (hbpos n).le
  have hLnotpos : ¬ 0 < L := by
    intro hLpos
    let d : ℕ → ℝ := fun n ↦ b n - b (n + 1)
    have hdnonneg : ∀ n, 0 ≤ d n := by
      intro n
      exact sub_nonneg.mpr (hanti (Nat.le_succ n))
    have hdtendsto :
        Tendsto (fun n : ℕ => ∑ i ∈ Finset.range n, d i) atTop (nhds (b 0 - L)) := by
      convert tendsto_const_nhds.sub ht using 1
      funext n
      exact Finset.sum_range_sub' b n
    have hd : Summable d :=
      ⟨b 0 - L, (hasSum_iff_tendsto_nat_of_nonneg hdnonneg _).2 hdtendsto⟩
    let c : ℝ := L * (x + 1)
    have hcpos : 0 < c := mul_pos hLpos (by linarith)
    have hcd : ∀ n : ℕ, c * (1 / ((n + 1 : ℕ) : ℝ)) ≤ d n := by
      intro n
      have hLb : L ≤ b n := ciInf_le hbdd n
      have hden : 0 < (((n + 1 : ℕ) : ℝ)) := by positivity
      have hdiff : d n = (x + 1) * b n / ((n + 1 : ℕ) : ℝ) := by
        dsimp [d, b]
        rw [magnitude_succ]
        push_cast
        field_simp
        ring
      rw [hdiff]
      rw [one_div, ← div_eq_mul_inv, div_le_div_iff_of_pos_right hden]
      have hmul := mul_le_mul_of_nonneg_right hLb (show 0 ≤ x + 1 by linarith)
      dsimp [c, b] at *
      nlinarith
    have hscaled : Summable (fun n : ℕ => c * (1 / ((n + 1 : ℕ) : ℝ))) :=
      Summable.of_nonneg_of_le (fun n ↦ mul_nonneg hcpos.le (by positivity)) hcd hd
    have hharShift : Summable (fun n : ℕ => 1 / ((n + 1 : ℕ) : ℝ)) := by
      have h := hscaled.mul_left c⁻¹
      simpa [hcpos.ne'] using h
    have hhar : Summable (fun n : ℕ => 1 / (n : ℝ)) := by
      apply (summable_nat_add_iff (f := fun n : ℕ => 1 / (n : ℝ)) 1).1
      simpa using hharShift
    exact Real.not_summable_one_div_natCast hhar
  have hL : L = 0 := le_antisymm (le_of_not_gt hLnotpos) hLnonneg
  simpa [hL] using ht

private theorem magnitude_not_summable (x : ℝ) (hx₁ : -1 < x) (hx₂ : x < 0) :
    ¬ Summable (magnitude x) := by
  intro hsum
  let b : ℕ → ℝ := magnitude x
  have hbpos : ∀ n, 0 < b n := fun n ↦ magnitude_pos x hx₂ n
  have htel : ∀ n : ℕ,
      (n : ℝ) * b n = (-x) * ∑ k ∈ Finset.range n, b k := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        rw [Finset.sum_range_succ]
        dsimp [b] at ih
        dsimp [b]
        rw [magnitude_succ]
        push_cast
        field_simp
        linear_combination ih
  have hpartial : Tendsto (fun n : ℕ => ∑ k ∈ Finset.range n, b k) atTop
      (nhds (∑' k, b k)) := hsum.hasSum.tendsto_sum_nat
  have hnb : Tendsto (fun n : ℕ => (n : ℝ) * b n) atTop
      (nhds ((-x) * ∑' k, b k)) := by
    convert tendsto_const_nhds.mul hpartial using 1
    · funext n
      exact htel n
  have htsumpos : 0 < ∑' k, b k := hsum.tsum_pos (fun n ↦ (hbpos n).le) 0 (hbpos 0)
  let C : ℝ := (-x) * ∑' k, b k
  have hCpos : 0 < C := mul_pos (neg_pos.mpr hx₂) htsumpos
  have hnbC : Tendsto (fun n : ℕ => (n : ℝ) * b n) atTop (nhds C) := by
    simpa [C] using hnb
  have hevent : ∀ᶠ n : ℕ in atTop, C / 2 < (n : ℝ) * b n :=
    hnbC.eventually (Ioi_mem_nhds (half_lt_self hCpos))
  rcases eventually_atTop.1 hevent with ⟨N, hN⟩
  let M : ℕ := max 1 N
  have hMpos : 0 < M := lt_of_lt_of_le Nat.zero_lt_one (le_max_left 1 N)
  have hbound : ∀ n : ℕ,
      (C / 2) * (1 / ((n + M : ℕ) : ℝ)) ≤ b (n + M) := by
    intro n
    have hNM : N ≤ n + M := (le_max_right 1 N).trans (Nat.le_add_left M n)
    have hk := hN (n + M) hNM
    have hkpos : 0 < (((n + M : ℕ) : ℝ)) := by
      exact_mod_cast lt_of_lt_of_le hMpos (Nat.le_add_left M n)
    have hk' : C / 2 < b (n + M) * ((n + M : ℕ) : ℝ) := by
      simpa [mul_comm] using hk
    rw [one_div, ← div_eq_mul_inv]
    exact ((div_lt_iff₀ hkpos).2 hk').le
  have hbShift : Summable (fun n : ℕ => b (n + M)) :=
    (summable_nat_add_iff (f := b) M).2 hsum
  have hscaled : Summable (fun n : ℕ => (C / 2) * (1 / ((n + M : ℕ) : ℝ))) :=
    Summable.of_nonneg_of_le (fun n ↦ mul_nonneg (by positivity) (by positivity)) hbound hbShift
  have hhalf : C / 2 ≠ 0 := (half_pos hCpos).ne'
  have hharShift : Summable (fun n : ℕ => 1 / ((n + M : ℕ) : ℝ)) := by
    have h := hscaled.mul_left (C / 2)⁻¹
    refine h.congr ?_
    intro n
    rw [← mul_assoc, inv_mul_cancel₀ hhalf, one_mul]
  have hhar : Summable (fun n : ℕ => 1 / (n : ℝ)) := by
    apply (summable_nat_add_iff (f := fun n : ℕ => 1 / (n : ℝ)) M).1
    simpa [Nat.add_comm] using hharShift
  exact Real.not_summable_one_div_natCast hhar

private theorem abs_term_summable_of_pos (x : ℝ) (hx : 0 < x) :
    Summable (fun n : ℕ => |term x n|) := by
  let b : ℕ → ℝ := fun n ↦ |term x n|
  obtain ⟨M, hM⟩ := exists_nat_gt (max 0 x)
  have hMpos : 0 < M := by
    exact_mod_cast (le_max_left 0 x).trans_lt hM
  have hxM : x < (M : ℝ) := (le_max_right 0 x).trans_lt hM
  have hrec : ∀ n : ℕ, M ≤ n →
      (n + 1 : ℝ) * b (n + 1) = ((n : ℝ) - x) * b n := by
    intro n hn
    have hxn : x < (n : ℝ) := hxM.trans_le (by exact_mod_cast hn)
    dsimp [b]
    rw [term_succ, abs_div, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < n + 1),
      abs_of_nonpos (by linarith : x - (n : ℝ) ≤ 0)]
    push_cast
    field_simp
    ring
  have htel : ∀ n : ℕ,
      x * (∑ j ∈ Finset.range n, b (j + M)) =
        (M : ℝ) * b M - ((M + n : ℕ) : ℝ) * b (M + n) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        rw [Finset.sum_range_succ, mul_add, ih]
        have hr := hrec (M + n) (Nat.le_add_right M n)
        rw [show n + M = M + n by omega, ← Nat.add_assoc M n 1]
        push_cast at hr ⊢
        linear_combination hr
  have hbound : ∀ n : ℕ,
      ∑ j ∈ Finset.range n, b (j + M) ≤ (M : ℝ) * b M / x := by
    intro n
    apply (le_div_iff₀ hx).2
    rw [mul_comm (∑ j ∈ Finset.range n, b (j + M)) x, htel]
    have hnonneg : 0 ≤ (((M + n : ℕ) : ℝ)) * b (M + n) := by
      dsimp [b]
      positivity
    linarith
  have htail : Summable (fun n : ℕ => b (n + M)) := by
    apply summable_of_sum_range_le (fun n ↦ abs_nonneg _)
    simpa [Nat.add_comm] using hbound
  exact (summable_nat_add_iff (f := b) M).1 htail

private theorem magnitude_monotone_of_le_neg_one (x : ℝ) (hx : x ≤ -1) :
    Monotone (magnitude x) := by
  apply monotone_nat_of_le_succ
  intro n
  rw [magnitude_succ, le_div_iff₀ (by positivity : (0 : ℝ) < n + 1)]
  have hmag : 0 ≤ magnitude x n := (magnitude_pos x (by linarith) n).le
  have hfac : (n : ℝ) + 1 ≤ (n : ℝ) - x := by linarith
  exact mul_le_mul_of_nonneg_left hfac hmag

private theorem abs_term_not_summable_of_le_neg_one (x : ℝ) (hx : x ≤ -1) :
    ¬ Summable (fun n : ℕ => |term x (n + 1)|) := by
  intro hsum
  have hxneg : x < 0 := by linarith
  have ht : Tendsto (fun n : ℕ => |term x (n + 1)|) atTop (nhds 0) := by
    simpa [Nat.cofinite_eq_atTop] using hsum.tendsto_cofinite_zero
  let c : ℝ := magnitude x 1
  have hcpos : 0 < c := magnitude_pos x hxneg 1
  have hevent : ∀ᶠ n : ℕ in atTop, |term x (n + 1)| < c :=
    ht.eventually (Iio_mem_nhds hcpos)
  rcases hevent.exists with ⟨n, hn⟩
  have hle : c ≤ magnitude x (n + 1) :=
    magnitude_monotone_of_le_neg_one x hx (Nat.le_add_left 1 n)
  rw [abs_term_eq_magnitude x hxneg] at hn
  exact (not_lt_of_ge hle) hn

private theorem seriesConverges_iff_summable_of_nonneg {f : ℕ → ℝ}
    (hf : ∀ n, 0 ≤ f n) : ProofGap.SeriesConverges f ↔ Summable f := by
  constructor
  · intro h
    unfold ProofGap.SeriesConverges at h
    rcases h with ⟨s, hs⟩
    have hs' : Tendsto (fun n : ℕ => ∑ i ∈ Finset.range n, f i) atTop (nhds s) := by
      simpa only [HasSum, SummationFilter.conditional_filter_eq_map_range,
        tendsto_map'_iff, Function.comp_apply] using hs
    exact ⟨s, (hasSum_iff_tendsto_nat_of_nonneg hf s).2 hs'⟩
  · intro h
    unfold ProofGap.SeriesConverges
    exact h.mono_filter (SummationFilter.conditional ℕ).le_atTop

private theorem seriesConverges_tendsto_zero {f : ℕ → ℝ}
    (h : ProofGap.SeriesConverges f) : Tendsto f atTop (nhds 0) := by
  unfold ProofGap.SeriesConverges at h
  rcases h with ⟨s, hs⟩
  have hpartial : Tendsto (fun n : ℕ => ∑ i ∈ Finset.range n, f i) atTop (nhds s) := by
    simpa only [HasSum, SummationFilter.conditional_filter_eq_map_range,
      tendsto_map'_iff, Function.comp_apply] using hs
  have hshift := hpartial.comp (tendsto_add_atTop_nat 1)
  have hdiff := hshift.sub hpartial
  convert hdiff using 1
  · funext n
    change f n = (∑ i ∈ Finset.range (n + 1), f i) - ∑ i ∈ Finset.range n, f i
    rw [Finset.sum_range_succ]
    ring
  · simp

private theorem term_series_not_converges_of_le_neg_one (x : ℝ) (hx : x ≤ -1) :
    ¬ ProofGap.SeriesConverges (fun n : ℕ => term x (n + 1)) := by
  intro hseries
  have ht : Tendsto (fun n : ℕ => |term x (n + 1)|) atTop (nhds 0) := by
    simpa using (seriesConverges_tendsto_zero hseries).abs
  let c : ℝ := magnitude x 1
  have hxneg : x < 0 := by linarith
  have hcpos : 0 < c := magnitude_pos x hxneg 1
  have hevent : ∀ᶠ n : ℕ in atTop, |term x (n + 1)| < c :=
    ht.eventually (Iio_mem_nhds hcpos)
  rcases hevent.exists with ⟨n, hn⟩
  have hle : c ≤ magnitude x (n + 1) :=
    magnitude_monotone_of_le_neg_one x hx (Nat.le_add_left 1 n)
  rw [abs_term_eq_magnitude x hxneg] at hn
  exact (not_lt_of_ge hle) hn

private theorem seriesConverges_alternating_of_antitone
    (b : ℕ → ℝ) (hb : ∀ n, 0 ≤ b n) (hanti : Antitone b)
    (ht : Tendsto b atTop (nhds 0)) :
    ProofGap.SeriesConverges (fun n : ℕ => (-1 : ℝ) ^ n * b n) := by
  let e : ℕ → ℝ := fun n ↦ b n - b (n + 1)
  have henonneg : ∀ n, 0 ≤ e n := fun n ↦ sub_nonneg.mpr (hanti (Nat.le_succ n))
  have hetendsto : Tendsto (fun n : ℕ => ∑ i ∈ Finset.range n, e i) atTop (nhds (b 0)) := by
    convert tendsto_const_nhds.sub ht using 1
    · funext n
      exact Finset.sum_range_sub' b n
    · simp
  have he : Summable e :=
    ⟨b 0, (hasSum_iff_tendsto_nat_of_nonneg henonneg _).2 hetendsto⟩
  let d : ℕ → ℝ := fun n ↦ e (2 * n)
  have hd : Summable d := by
    exact he.comp_injective (fun a b h ↦ by omega)
  let a : ℕ → ℝ := fun n ↦ (-1 : ℝ) ^ n * b n
  have hpair : ∀ n, a (2 * n) + a (2 * n + 1) = d n := by
    intro n
    dsimp [a, d, e]
    rw [pow_add]
    norm_num [pow_mul]
    ring
  have hsumEven : ∀ n,
      (∑ i ∈ Finset.range (2 * n), a i) = ∑ j ∈ Finset.range n, d j := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        rw [show 2 * (n + 1) = (2 * n + 1) + 1 by omega, Finset.sum_range_succ,
          show 2 * n + 1 = 2 * n + 1 by rfl, Finset.sum_range_succ, ih,
          Finset.sum_range_succ]
        linear_combination hpair n
  have heven : Tendsto (fun n : ℕ => ∑ i ∈ Finset.range (2 * n), a i) atTop
      (nhds (∑' n, d n)) := by
    convert hd.hasSum.tendsto_sum_nat using 1
    funext n
    exact hsumEven n
  have htwo : Tendsto (fun n : ℕ => 2 * n) atTop atTop := by
    simpa using (Filter.tendsto_id.nsmul_atTop (n := 2) (by norm_num : 0 < 2))
  have haEven : Tendsto (fun n : ℕ => a (2 * n)) atTop (nhds 0) := by
    have hbEven := ht.comp htwo
    simpa [a, pow_mul] using hbEven
  have hodd : Tendsto (fun n : ℕ => ∑ i ∈ Finset.range (2 * n + 1), a i) atTop
      (nhds (∑' n, d n)) := by
    convert heven.add haEven using 1
    · funext n
      rw [Finset.sum_range_succ]
    · simp
  have hall : Tendsto (fun n : ℕ => ∑ i ∈ Finset.range n, a i) atTop
      (nhds (∑' n, d n)) := by
    rw [Metric.tendsto_atTop] at heven hodd ⊢
    intro ε hε
    obtain ⟨Ne, hNe⟩ := heven ε hε
    obtain ⟨No, hNo⟩ := hodd ε hε
    refine ⟨2 * max Ne No, ?_⟩
    intro n hn
    obtain ⟨k, hk | hk⟩ := Nat.even_or_odd' n
    · subst n
      exact hNe k (by omega)
    · subst n
      exact hNo k (by omega)
  unfold ProofGap.SeriesConverges
  refine ⟨∑' n, d n, ?_⟩
  simpa only [HasSum, SummationFilter.conditional_filter_eq_map_range,
    tendsto_map'_iff, Function.comp_apply, a] using hall

theorem gap1 (n : ℕ) (x : ℝ) :
    fallingFactorial x n = ∏ k ∈ Finset.range n, (x - k) := by rfl

theorem gap2 (x : ℝ) (hx : 0 ≤ x) :
    Summable (fun n : ℕ => |term x (n + 1)|) := by
  rcases hx.eq_or_lt with rfl | hx
  · have hzero : (fun n : ℕ => |term 0 (n + 1)|) = fun _ ↦ 0 := by
      funext n
      rw [abs_eq_zero, term, fallingFactorial]
      apply div_eq_zero_iff.mpr
      left
      apply Finset.prod_eq_zero (i := 0)
      · simp
      · norm_num
    rw [hzero]
    exact summable_zero
  · have hall := abs_term_summable_of_pos x hx
    exact (summable_nat_add_iff (f := fun n : ℕ => |term x n|) 1).2 hall

theorem gap3 (x : ℝ) (hx₁ : -1 < x) (hx₂ : x < 0) :
    ConditionallySummable x := by
  let b : ℕ → ℝ := fun n ↦ magnitude x (n + 1)
  have hb : ∀ n, 0 ≤ b n := fun n ↦ (magnitude_pos x hx₂ (n + 1)).le
  have hbanti : Antitone b := by
    intro m n hmn
    exact magnitude_antitone x hx₁ hx₂ (Nat.add_le_add_right hmn 1)
  have hbtend : Tendsto b atTop (nhds 0) :=
    (magnitude_tendsto_zero x hx₁ hx₂).comp (tendsto_add_atTop_nat 1)
  have halt := seriesConverges_alternating_of_antitone b hb hbanti hbtend
  constructor
  · unfold ProofGap.SeriesConverges at halt ⊢
    have hneg := halt.neg
    convert hneg using 1
    funext n
    dsimp [b]
    rw [term_eq_sign_mul_magnitude, pow_succ]
    ring
  · intro habs
    have habs' : Summable (fun n : ℕ => |term x (n + 1)|) :=
      (seriesConverges_iff_summable_of_nonneg (fun n ↦ abs_nonneg _)).1 habs
    have hmagShift : Summable (fun n : ℕ => magnitude x (n + 1)) := by
      refine habs'.congr ?_
      intro n
      exact abs_term_eq_magnitude x hx₂ (n + 1)
    have hmag : Summable (magnitude x) :=
      (summable_nat_add_iff (f := magnitude x) 1).1 hmagShift
    exact magnitude_not_summable x hx₁ hx₂ hmag

theorem gap4 :
    {x : ℝ | Summable (fun n : ℕ => |term x (n + 1)|)} =
      {x : ℝ | 0 ≤ x} := by
  ext x
  simp only [Set.mem_setOf_eq]
  constructor
  · intro hsum
    by_contra hx
    have hxneg : x < 0 := lt_of_not_ge hx
    by_cases hx₁ : -1 < x
    · have hmagShift : Summable (fun n : ℕ => magnitude x (n + 1)) := by
        refine hsum.congr ?_
        intro n
        exact abs_term_eq_magnitude x hxneg (n + 1)
      have hmag : Summable (magnitude x) :=
        (summable_nat_add_iff (f := magnitude x) 1).1 hmagShift
      exact magnitude_not_summable x hx₁ hxneg hmag
    · exact abs_term_not_summable_of_le_neg_one x (le_of_not_gt hx₁) hsum
  · exact gap2 x

theorem gap5 :
    {x : ℝ | ConditionallySummable x} =
      {x : ℝ | -1 < x ∧ x < 0} := by
  ext x
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨hseries, hnotabs⟩
    have hxneg : x < 0 := by
      by_contra hx
      have hx0 : 0 ≤ x := le_of_not_gt hx
      have habs := gap2 x hx0
      have habsSeries :=
        (seriesConverges_iff_summable_of_nonneg (fun n ↦ abs_nonneg (term x (n + 1)))).2 habs
      exact hnotabs habsSeries
    have hx₁ : -1 < x := by
      by_contra hx
      exact term_series_not_converges_of_le_neg_one x (le_of_not_gt hx) hseries
    exact ⟨hx₁, hxneg⟩
  · rintro ⟨hx₁, hx₂⟩
    exact gap3 x hx₁ hx₂

end

end ProofGap.Exercise2739_1
