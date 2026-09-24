import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Analysis.PSeries

namespace ProofGap.Exercise2799_1

noncomputable section

open scoped BigOperators
open scoped Topology

def term (n : ℕ) (x : ℝ) : ℝ :=
  (-1 : ℝ) ^ n * x / ((n : ℝ) + x)

def derivativeTerm (n : ℕ) (x : ℝ) : ℝ :=
  (-1 : ℝ) ^ n * (n : ℝ) / ((n : ℝ) + x) ^ 2

def f (x : ℝ) : ℝ :=
  ∑'[SummationFilter.conditional ℕ] n : ℕ, term (n + 1) x

def IsRegularPoint (x : ℝ) : Prop :=
  ∀ k : ℕ, 1 ≤ k → x ≠ -(k : ℝ)

def seriesDomain : Set ℝ :=
  {x | ∀ k : ℕ, 1 ≤ k → (k : ℝ) + x ≠ 0}

def alternatingPartialSum (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range n, (-1 : ℝ) ^ (k + 1)

def BoundedSequence (u : ℕ → ℝ) : Prop :=
  ∃ C : ℝ, ∀ n : ℕ, |u n| ≤ C

def SeriesUniformlyConvergesOn
    (u : ℕ → ℝ → ℝ) (s : Set ℝ) (g : ℝ → ℝ) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ x ∈ s,
    |(∑ k ∈ Finset.range (n + 1), u k x) - g x| < ε

private theorem conditional_hasSum_of_tendsto {a : ℕ → ℝ} {s : ℝ}
    (h : Tendsto (fun n : ℕ => ∑ k ∈ Finset.range n, a k) atTop (𝓝 s)) :
    HasSum a s (SummationFilter.conditional ℕ) := by
  rw [HasSum, SummationFilter.conditional_filter_eq_map_range,
    Filter.tendsto_map'_iff]
  simpa [Function.comp_def] using h

private theorem conditional_summable_of_cauchySeq {a : ℕ → ℝ}
    (h : CauchySeq (fun n : ℕ => ∑ k ∈ Finset.range n, a k)) :
    Summable a (SummationFilter.conditional ℕ) := by
  obtain ⟨s, hs⟩ := cauchySeq_tendsto_of_complete h
  exact ⟨s, conditional_hasSum_of_tendsto hs⟩

private theorem conditional_tsum_tendsto {a : ℕ → ℝ}
    (h : Summable a (SummationFilter.conditional ℕ)) :
    Tendsto (fun n : ℕ => ∑ k ∈ Finset.range n, a k) atTop
      (𝓝 (∑'[SummationFilter.conditional ℕ] k : ℕ, a k)) := by
  have hs := h.hasSum
  rw [HasSum, SummationFilter.conditional_filter_eq_map_range,
    Filter.tendsto_map'_iff] at hs
  simpa [Function.comp_def] using hs

private theorem conditional_alternating_error
    (a : ℕ → ℝ) (ha : Antitone a) (ha0 : Tendsto a atTop (𝓝 0)) (n : ℕ) :
    |(∑'[SummationFilter.conditional ℕ] i : ℕ, (-1 : ℝ) ^ i * a i) -
      (∑ i ∈ Finset.range n, (-1 : ℝ) ^ i * a i)| ≤ a n := by
  have hs :
      Summable (fun i : ℕ => (-1 : ℝ) ^ i * a i)
        (SummationFilter.conditional ℕ) :=
    conditional_summable_of_cauchySeq
      (ha.cauchySeq_alternating_series_of_tendsto_zero ha0)
  have hlim := conditional_tsum_tendsto hs
  have upper := ha.alternating_series_le_tendsto hlim
  have lower := ha.tendsto_le_alternating_series hlim
  have hnonneg (k : ℕ) : 0 ≤ a k := by
    apply le_of_tendsto ha0
    filter_upwards [Filter.Ici_mem_atTop k] with m hm using ha hm
  obtain hn | hn := Nat.even_or_odd n
  · obtain ⟨k, rfl⟩ := even_iff_exists_two_mul.mp hn
    specialize upper k
    specialize lower k
    simp only [Finset.sum_range_succ, even_two, Even.mul_right, Even.neg_pow,
      one_pow, one_mul] at lower
    rw [abs_sub_le_iff]
    constructor
    · rwa [sub_le_iff_le_add, add_comm]
    · rw [sub_le_iff_le_add, add_comm]
      exact upper.trans (le_add_of_nonneg_right (hnonneg (2 * k)))
  · obtain ⟨k, rfl⟩ := odd_iff_exists_bit1.mp hn
    specialize upper (k + 1)
    specialize lower k
    rw [Nat.mul_add, Finset.sum_range_succ] at upper
    rw [abs_sub_le_iff]
    constructor
    · rw [sub_le_iff_le_add, add_comm]
      exact lower.trans (le_add_of_nonneg_right (hnonneg (2 * k + 1)))
    · simpa [Finset.sum_range_succ, add_comm, pow_add] using upper

private theorem conditional_alternating_eventual_error
    (A : ℕ → ℝ) (m n : ℕ) (hmn : m ≤ n)
    (ha : Antitone (fun j => A (m + j)))
    (ha0 : Tendsto (fun j => A (m + j)) atTop (𝓝 0)) :
    |(∑'[SummationFilter.conditional ℕ] k : ℕ,
        (-1 : ℝ) ^ (k + 1) * A k) -
      (∑ k ∈ Finset.range n, (-1 : ℝ) ^ (k + 1) * A k)| ≤ A n := by
  let a : ℕ → ℝ := fun j => A (m + j)
  let c : ℝ := (-1 : ℝ) ^ (m + 1)
  let pref : ℝ :=
    ∑ k ∈ Finset.range m, (-1 : ℝ) ^ (k + 1) * A k
  let tailSum : ℝ :=
    ∑'[SummationFilter.conditional ℕ] j : ℕ, (-1 : ℝ) ^ j * a j
  have hsTail :
      Summable (fun j : ℕ => (-1 : ℝ) ^ j * a j)
        (SummationFilter.conditional ℕ) :=
    conditional_summable_of_cauchySeq
      (ha.cauchySeq_alternating_series_of_tendsto_zero ha0)
  have htail :
      Tendsto
        (fun q => ∑ j ∈ Finset.range q, (-1 : ℝ) ^ j * a j)
        atTop (𝓝 tailSum) := by
    simpa [tailSum] using conditional_tsum_tendsto hsTail
  have hshift :
      (fun q =>
        ∑ k ∈ Finset.range (q + m), (-1 : ℝ) ^ (k + 1) * A k) =
      (fun q =>
        pref + c *
          (∑ j ∈ Finset.range q, (-1 : ℝ) ^ j * a j)) := by
    funext q
    rw [Nat.add_comm q m, Finset.sum_range_add]
    congr 1
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    simp only [a, c]
    rw [show m + j + 1 = (m + 1) + j by omega, pow_add]
    ring
  have hfull :
      Tendsto
        (fun q =>
          ∑ k ∈ Finset.range q, (-1 : ℝ) ^ (k + 1) * A k)
        atTop (𝓝 (pref + c * tailSum)) := by
    apply (Filter.tendsto_add_atTop_iff_nat m).mp
    rw [hshift]
    exact (htail.const_mul c).const_add pref
  have hfullSum :
      (∑'[SummationFilter.conditional ℕ] k : ℕ,
          (-1 : ℝ) ^ (k + 1) * A k) = pref + c * tailSum :=
    (conditional_hasSum_of_tendsto hfull).tsum_eq
  have hpartial :
      (∑ k ∈ Finset.range n, (-1 : ℝ) ^ (k + 1) * A k) =
        pref + c *
          (∑ j ∈ Finset.range (n - m), (-1 : ℝ) ^ j * a j) := by
    conv_lhs => rw [← Nat.add_sub_of_le hmn, Finset.sum_range_add]
    congr 1
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    simp only [a, c]
    rw [show m + j + 1 = (m + 1) + j by omega, pow_add]
    ring
  rw [hfullSum, hpartial]
  have herr := conditional_alternating_error a ha ha0 (n - m)
  calc
    |pref + c * tailSum -
        (pref + c *
          (∑ j ∈ Finset.range (n - m), (-1 : ℝ) ^ j * a j))| =
        |tailSum -
          (∑ j ∈ Finset.range (n - m), (-1 : ℝ) ^ j * a j)| := by
      rw [add_sub_add_left_eq_sub, ← mul_sub, abs_mul]
      simp [c]
    _ ≤ a (n - m) := herr
    _ = A n := by simp [a, Nat.add_sub_of_le hmn]

private theorem term_conditional_summable (x : ℝ) :
    Summable (fun n : ℕ => term (n + 1) x)
      (SummationFilter.conditional ℕ) := by
  by_cases hx0 : x = 0
  · subst x
    simp [term]
  obtain ⟨N, hN⟩ := exists_nat_gt |x|
  let a : ℕ → ℝ := fun n =>
    1 / ((n : ℝ) + ((N : ℝ) + 1 + x))
  let z : ℕ → ℝ := fun n => (-1 : ℝ) ^ (N + n + 1) * x
  have hbase : 0 < (N : ℝ) + 1 + x := by
    have hxlower : -x ≤ |x| := neg_le_abs x
    linarith
  have ha : Antitone a := by
    intro m n hmn
    dsimp [a]
    apply one_div_le_one_div_of_le
    · have hm0 : (0 : ℝ) ≤ (m : ℝ) := by positivity
      linarith
    · have hmnR : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmn
      linarith
  have ha0 : Tendsto a atTop (𝓝 0) := by
    dsimp [a]
    simpa [one_div, add_assoc] using
      (tendsto_inv_atTop_zero.comp
        (Filter.tendsto_atTop_add_const_right atTop
          ((N : ℝ) + 1 + x) tendsto_natCast_atTop_atTop))
  have hz : ∀ n : ℕ, ‖∑ i ∈ Finset.range n, z i‖ ≤ |x| := by
    intro n
    have hsum :
        (∑ i ∈ Finset.range n, z i) =
          (((-1 : ℝ) ^ (N + 1)) * x) *
            (∑ i ∈ Finset.range n, (-1 : ℝ) ^ i) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      dsimp [z]
      rw [show N + i + 1 = (N + 1) + i by omega, pow_add]
      ring
    rw [hsum, norm_mul]
    have hconst : ‖((-1 : ℝ) ^ (N + 1) * x)‖ = |x| := by
      simp [Real.norm_eq_abs]
    rw [hconst]
    simpa using
      (mul_le_mul_of_nonneg_left (norm_sum_neg_one_pow_le n) (abs_nonneg x))
  have hcTail :
      CauchySeq (fun n => ∑ i ∈ Finset.range n, a i • z i) :=
    ha.cauchySeq_series_mul_of_tendsto_zero_of_bounded ha0 hz
  have hcTail' :
      CauchySeq
        (fun n => ∑ i ∈ Finset.range n, term (N + i + 1) x) := by
    convert hcTail using 1
    funext n
    apply Finset.sum_congr rfl
    intro i hi
    simp [a, z, term, div_eq_mul_inv]
    push_cast
    ring
  apply conditional_summable_of_cauchySeq
  rw [← cauchySeq_shift N]
  have hshift :
      (fun n => ∑ k ∈ Finset.range (n + N), term (k + 1) x) =
        (fun n =>
          (∑ k ∈ Finset.range N, term (k + 1) x) +
            ∑ k ∈ Finset.range n, term (N + k + 1) x) := by
    funext n
    rw [Nat.add_comm n N, Finset.sum_range_add]
  rw [hshift]
  exact hcTail'.const_add

theorem gap1 (x : ℝ) (hx : IsRegularPoint x) :
    Summable (fun n : ℕ => term (n + 1) x)
      (SummationFilter.conditional ℕ) := by
  exact term_conditional_summable x

theorem gap2 (x₀ : ℝ) (hx₀ : 0 ≤ x₀) :
    ∃ β : ℝ, x₀ ∈ Set.Icc (-(1 / 2 : ℝ)) β := by
  refine ⟨x₀, ?_, le_rfl⟩
  linarith

theorem gap3 (n : ℕ) (x : ℝ) (hn : 1 ≤ n)
    (hx : x ≠ -(n : ℝ)) :
    HasDerivAt (term n) (derivativeTerm n x) x := by
  have hne : (n : ℝ) + x ≠ 0 := by
    intro h
    apply hx
    linarith
  convert
    (((hasDerivAt_const x ((-1 : ℝ) ^ n)).mul (hasDerivAt_id x)).div
      ((hasDerivAt_const x (n : ℝ)).add (hasDerivAt_id x)) hne) using 1 <;>
    simp [term, derivativeTerm] <;> ring

theorem gap4 (n : ℕ) (β : ℝ) (hn : 1 ≤ n) :
    ContinuousOn (derivativeTerm n) (Set.Icc (-(1 / 2 : ℝ)) β) := by
  intro x hx
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hpos : 0 < (n : ℝ) + x := by linarith [hx.1]
  apply ContinuousAt.continuousWithinAt
  unfold derivativeTerm
  exact continuousAt_const.div
    ((continuousAt_const.add continuousAt_id).pow 2)
    (pow_ne_zero 2 hpos.ne')

theorem gap5 (n : ℕ) (x : ℝ) (hn : 2 ≤ n)
    (hx : -(1 / 2 : ℝ) ≤ x) :
    |(n : ℝ) / ((n : ℝ) + x) ^ 2| ≤
      (n : ℝ) / ((n : ℝ) - 1) ^ 2 := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hleft : 0 < (n : ℝ) - 1 := by linarith
  have hright : 0 < (n : ℝ) + x := by linarith
  rw [abs_of_nonneg (div_nonneg (by positivity) (sq_nonneg _))]
  rw [div_le_div_iff₀ (sq_pos_of_pos hright) (sq_pos_of_pos hleft)]
  nlinarith [sq_nonneg ((n : ℝ) + x - ((n : ℝ) - 1))]

theorem gap6 :
    Tendsto
      (fun n : ℕ => ((n : ℝ) + 2) / (((n : ℝ) + 1) ^ 2))
      atTop (𝓝 0) := by
  have h := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  have hsum := h.add (h.mul h)
  convert hsum using 1
  · funext n
    have hn : (n : ℝ) + 1 ≠ 0 := by positivity
    field_simp
    ring
  · norm_num

theorem gap7 :
    BoundedSequence alternatingPartialSum := by
  refine ⟨1, fun n => ?_⟩
  have hsum :
      (∑ k ∈ Finset.range n, (-1 : ℝ) ^ (k + 1)) =
        -(∑ k ∈ Finset.range n, (-1 : ℝ) ^ k) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    rw [pow_succ]
    ring
  rw [alternatingPartialSum, hsum, abs_neg, ← Real.norm_eq_abs]
  exact norm_sum_neg_one_pow_le n

theorem gap8 (β : ℝ) (hβ : 0 ≤ β) :
    SeriesUniformlyConvergesOn
      (fun n x => derivativeTerm (n + 1) x)
      (Set.Icc 0 β)
      (fun x => ∑'[SummationFilter.conditional ℕ] n : ℕ,
        derivativeTerm (n + 1) x) := by
  intro ε hε
  obtain ⟨N₀, hN₀⟩ := Metric.tendsto_atTop.1 gap6 ε hε
  let m : ℕ := ⌈β⌉₊ + 1
  have hmβ : β < (m : ℝ) := by
    have hceil : β ≤ (⌈β⌉₊ : ℝ) := Nat.le_ceil β
    dsimp [m]
    push_cast
    linarith
  refine ⟨max N₀ m, fun n hn x hx => ?_⟩
  let A : ℕ → ℝ := fun k =>
    (((k + 1 : ℕ) : ℝ) / ((((k + 1 : ℕ) : ℝ) + x) ^ 2))
  have ha : Antitone (fun j => A (m + j)) := by
    intro i j hij
    let p : ℝ := ((m + i + 1 : ℕ) : ℝ)
    let q : ℝ := ((m + j + 1 : ℕ) : ℝ)
    have hp : 0 < p := by dsimp [p]; positivity
    have hpq : p ≤ q := by
      dsimp [p, q]
      exact_mod_cast (show m + i + 1 ≤ m + j + 1 by omega)
    have hxp : x ≤ p := by
      have hmp : (m : ℝ) ≤ p := by
        dsimp [p]
        exact_mod_cast (show m ≤ m + i + 1 by omega)
      linarith [hx.2]
    have hx0 : 0 ≤ x := hx.1
    have hq : 0 < q := hp.trans_le hpq
    have hdenp : 0 < p + x := by linarith
    have hdenq : 0 < q + x := by linarith
    have hxp2 : x ^ 2 ≤ p ^ 2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hxp) (add_nonneg hx0 hp.le)]
    have hp2q : p ^ 2 ≤ p * q := by
      nlinarith [mul_nonneg hp.le (sub_nonneg.mpr hpq)]
    have hx2pq : x ^ 2 ≤ p * q := hxp2.trans hp2q
    have hfactor : 0 ≤ (q - p) * (p * q - x ^ 2) :=
      mul_nonneg (sub_nonneg.mpr hpq) (sub_nonneg.mpr hx2pq)
    change q / (q + x) ^ 2 ≤ p / (p + x) ^ 2
    rw [div_le_div_iff₀ (sq_pos_of_pos hdenq) (sq_pos_of_pos hdenp)]
    nlinarith
  have ha0 : Tendsto (fun j => A (m + j)) atTop (𝓝 0) := by
    have hInv :
        Tendsto
          (fun j : ℕ =>
            (((j : ℝ) + ((m : ℝ) + 1 + x))⁻¹))
          atTop (𝓝 0) := by
      simpa [add_assoc] using
        (tendsto_inv_atTop_zero.comp
          (Filter.tendsto_atTop_add_const_right atTop
            ((m : ℝ) + 1 + x) tendsto_natCast_atTop_atTop))
    have hlim := hInv.sub ((hInv.mul hInv).const_mul x)
    convert hlim using 1
    · funext j
      dsimp [A]
      let D : ℝ := (j : ℝ) + ((m : ℝ) + 1 + x)
      have hD : D ≠ 0 := by
        dsimp [D]
        have hj : (0 : ℝ) ≤ (j : ℝ) := by positivity
        linarith [hmβ, hx.1]
      have hnum : ((m + j + 1 : ℕ) : ℝ) = D - x := by
        dsimp [D]
        push_cast
        ring
      rw [hnum, show D - x + x = D by ring]
      change (D - x) / D ^ 2 = D⁻¹ - x * (D⁻¹ * D⁻¹)
      field_simp [hD]
    · simp
  have hmn : m ≤ n + 1 := by omega
  have herr :=
    conditional_alternating_eventual_error A m (n + 1) hmn ha ha0
  have hmain :
      |(∑ k ∈ Finset.range (n + 1), derivativeTerm (k + 1) x) -
        (∑'[SummationFilter.conditional ℕ] k : ℕ,
          derivativeTerm (k + 1) x)| ≤ A (n + 1) := by
    rw [abs_sub_comm]
    simpa [A, derivativeTerm, div_eq_mul_inv, mul_assoc] using herr
  have hA_bound :
      A (n + 1) ≤ ((n : ℝ) + 2) / (((n : ℝ) + 1) ^ 2) := by
    have hraw := gap5 (n + 2) x (by omega) (by linarith [hx.1])
    have hAnonneg : 0 ≤ A (n + 1) := by
      dsimp [A]
      positivity
    rw [← abs_of_nonneg hAnonneg]
    convert hraw using 1 <;> push_cast <;> ring
  have hn₀ : N₀ ≤ n := (le_max_left N₀ m).trans hn
  have hsmall := hN₀ n hn₀
  have hboundSmall :
      ((n : ℝ) + 2) / (((n : ℝ) + 1) ^ 2) < ε := by
    have hqnonneg :
        0 ≤ ((n : ℝ) + 2) / (((n : ℝ) + 1) ^ 2) := by positivity
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hqnonneg] at hsmall
    exact hsmall
  exact lt_of_le_of_lt (hmain.trans hA_bound) hboundSmall

private theorem derivativeSeriesUniformlyConvergesOn_nonpositive :
    SeriesUniformlyConvergesOn
      (fun n x => derivativeTerm (n + 1) x)
      (Set.Icc (-(1 / 2 : ℝ)) 0)
      (fun x => ∑'[SummationFilter.conditional ℕ] n : ℕ,
        derivativeTerm (n + 1) x) := by
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 gap6 ε hε
  refine ⟨N, fun n hn x hx => ?_⟩
  let A : ℕ → ℝ := fun k =>
    (((k + 1 : ℕ) : ℝ) / ((((k + 1 : ℕ) : ℝ) + x) ^ 2))
  have ha : Antitone A := by
    intro i j hij
    let p : ℝ := ((i + 1 : ℕ) : ℝ)
    let q : ℝ := ((j + 1 : ℕ) : ℝ)
    have hp : 0 < p := by dsimp [p]; positivity
    have hp1 : (1 : ℝ) ≤ p := by
      dsimp [p]
      exact_mod_cast (show 1 ≤ i + 1 by omega)
    have hpq : p ≤ q := by
      dsimp [p, q]
      exact_mod_cast (show i + 1 ≤ j + 1 by omega)
    have hq : 0 < q := hp.trans_le hpq
    have hdenp : 0 < p + x := by linarith [hx.1]
    have hdenq : 0 < q + x := by linarith [hx.1]
    have hx2p2 : x ^ 2 ≤ p ^ 2 := by
      have hxp : x ≤ p := by linarith [hx.2]
      nlinarith [mul_nonneg (sub_nonneg.mpr hxp) hdenp.le]
    have hp2q : p ^ 2 ≤ p * q := by
      nlinarith [mul_nonneg hp.le (sub_nonneg.mpr hpq)]
    have hx2pq : x ^ 2 ≤ p * q := hx2p2.trans hp2q
    have hfactor : 0 ≤ (q - p) * (p * q - x ^ 2) :=
      mul_nonneg (sub_nonneg.mpr hpq) (sub_nonneg.mpr hx2pq)
    change q / (q + x) ^ 2 ≤ p / (p + x) ^ 2
    rw [div_le_div_iff₀ (sq_pos_of_pos hdenq) (sq_pos_of_pos hdenp)]
    nlinarith
  have ha0 : Tendsto A atTop (𝓝 0) := by
    have hInv :
        Tendsto (fun j : ℕ => (((j : ℝ) + (1 + x))⁻¹)) atTop (𝓝 0) := by
      simpa [add_assoc] using
        (tendsto_inv_atTop_zero.comp
          (Filter.tendsto_atTop_add_const_right atTop
            (1 + x) tendsto_natCast_atTop_atTop))
    have hlim := hInv.sub ((hInv.mul hInv).const_mul x)
    convert hlim using 1
    · funext j
      dsimp [A]
      let D : ℝ := (j : ℝ) + (1 + x)
      have hD : D ≠ 0 := by
        dsimp [D]
        have hj : (0 : ℝ) ≤ (j : ℝ) := by positivity
        linarith [hx.1]
      have hnum : ((j + 1 : ℕ) : ℝ) = D - x := by
        dsimp [D]
        push_cast
        ring
      rw [hnum, show D - x + x = D by ring]
      change (D - x) / D ^ 2 = D⁻¹ - x * (D⁻¹ * D⁻¹)
      field_simp [hD]
    · simp
  have herr :=
    conditional_alternating_eventual_error A 0 (n + 1) (by omega) (by simpa) (by simpa)
  have hmain :
      |(∑ k ∈ Finset.range (n + 1), derivativeTerm (k + 1) x) -
        (∑'[SummationFilter.conditional ℕ] k : ℕ,
          derivativeTerm (k + 1) x)| ≤ A (n + 1) := by
    rw [abs_sub_comm]
    simpa [A, derivativeTerm, div_eq_mul_inv, mul_assoc] using herr
  have hA_bound :
      A (n + 1) ≤ ((n : ℝ) + 2) / (((n : ℝ) + 1) ^ 2) := by
    have hraw := gap5 (n + 2) x (by omega) hx.1
    have hAnonneg : 0 ≤ A (n + 1) := by
      dsimp [A]
      positivity
    rw [← abs_of_nonneg hAnonneg]
    convert hraw using 1 <;> push_cast <;> ring
  have hsmall := hN n hn
  have hqnonneg :
      0 ≤ ((n : ℝ) + 2) / (((n : ℝ) + 1) ^ 2) := by positivity
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hqnonneg] at hsmall
  exact lt_of_le_of_lt (hmain.trans hA_bound) hsmall

private theorem derivativeSeriesUniformlyConvergesOn_near_nonnegative
    (β : ℝ) (hβ : 0 ≤ β) :
    SeriesUniformlyConvergesOn
      (fun n x => derivativeTerm (n + 1) x)
      (Set.Icc (-(1 / 2 : ℝ)) β)
      (fun x => ∑'[SummationFilter.conditional ℕ] n : ℕ,
        derivativeTerm (n + 1) x) := by
  intro ε hε
  obtain ⟨N₁, hN₁⟩ := gap8 β hβ ε hε
  obtain ⟨N₂, hN₂⟩ :=
    derivativeSeriesUniformlyConvergesOn_nonpositive ε hε
  refine ⟨max N₁ N₂, fun n hn x hx => ?_⟩
  by_cases hx0 : x ≤ 0
  · exact hN₂ n ((le_max_right N₁ N₂).trans hn) x ⟨hx.1, hx0⟩
  · exact hN₁ n ((le_max_left N₁ N₂).trans hn) x
      ⟨le_of_not_ge hx0, hx.2⟩

theorem gap9 (x₀ : ℝ) (hx₀ : 0 ≤ x₀) :
    DifferentiableAt ℝ f x₀ := by
  let β : ℝ := x₀ + 1
  have hβ : 0 ≤ β := by dsimp [β]; linarith
  let s : Set ℝ := Set.Ioo (-(1 / 2 : ℝ)) β
  have hxmem : x₀ ∈ s := by
    dsimp [s, β]
    constructor <;> linarith
  let F : ℕ → ℝ → ℝ := fun n y =>
    ∑ k ∈ Finset.range (n + 1), term (k + 1) y
  let F' : ℕ → ℝ → ℝ := fun n y =>
    ∑ k ∈ Finset.range (n + 1), derivativeTerm (k + 1) y
  let G' : ℝ → ℝ := fun y =>
    ∑'[SummationFilter.conditional ℕ] k : ℕ, derivativeTerm (k + 1) y
  have hu := derivativeSeriesUniformlyConvergesOn_near_nonnegative β hβ
  have hU : TendstoUniformlyOn F' G' atTop s := by
    refine Metric.tendstoUniformlyOn_iff.mpr fun ε hε => ?_
    obtain ⟨N, hN⟩ := hu ε hε
    filter_upwards [Filter.eventually_ge_atTop N] with n hn
    intro y hy
    have hbound := hN n hn y ⟨hy.1.le, hy.2.le⟩
    simpa [F', G', Real.dist_eq, abs_sub_comm] using hbound
  have hDeriv :
      ∀ᶠ n in atTop, ∀ y ∈ s, HasDerivAt (F n) (F' n y) y := by
    filter_upwards [] with n
    intro y hy
    dsimp [F, F']
    apply HasDerivAt.fun_sum
    intro k hk
    apply gap3 (k + 1) y (by omega)
    intro heq
    have hkR : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by
      exact_mod_cast (show 1 ≤ k + 1 by omega)
    dsimp [s] at hy
    have hylower := hy.1
    norm_num at hylower
    linarith
  have hConv : ∀ y ∈ s, Tendsto (fun n => F n y) atTop (𝓝 (f y)) := by
    intro y hy
    have hyreg : IsRegularPoint y := by
      intro k hk heq
      have hkR : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
      dsimp [s] at hy
      have hylower := hy.1
      norm_num at hylower
      linarith
    have hsum := conditional_tsum_tendsto (gap1 y hyreg)
    have hshift := hsum.comp (Filter.tendsto_add_atTop_nat 1)
    simpa [F, f] using hshift
  exact
    (hasDerivAt_of_tendstoUniformlyOn isOpen_Ioo hU hDeriv hConv hxmem).differentiableAt

theorem gap10 (x₀ : ℝ) (hx₀ : x₀ < 0)
    (hreg : IsRegularPoint x₀) :
    ∃ k₀ : ℕ,
      -((k₀ : ℝ) + 1) < x₀ ∧ x₀ < -(k₀ : ℝ) := by
  let k₀ : ℕ := ⌊-x₀⌋₊
  refine ⟨k₀, ?_, ?_⟩
  · have hupper := Nat.lt_floor_add_one (-x₀)
    change -((k₀ : ℝ) + 1) < x₀
    dsimp [k₀]
    linarith
  · have hnonneg : 0 ≤ -x₀ := by linarith
    have hle : (k₀ : ℝ) ≤ -x₀ := by
      dsimp [k₀]
      exact Nat.floor_le hnonneg
    have hne : (k₀ : ℝ) ≠ -x₀ := by
      intro heq
      have hkposR : (0 : ℝ) < (k₀ : ℝ) := by linarith
      have hkpos : 1 ≤ k₀ := by exact_mod_cast hkposR
      apply hreg k₀ hkpos
      linarith
    have hlt : (k₀ : ℝ) < -x₀ := lt_of_le_of_ne hle hne
    linarith

theorem gap11 (x₀ : ℝ) (k₀ : ℕ)
    (hk : -((k₀ : ℝ) + 1) < x₀) :
    ∃ α : ℝ, -((k₀ : ℝ) + 1) < α := by
  exact ⟨x₀, hk⟩

theorem gap12 (x₀ : ℝ) (k₀ : ℕ)
    (hk : -((k₀ : ℝ) + 1) < x₀) :
    ∃ α : ℝ, -((k₀ : ℝ) + 1) < α ∧ α < x₀ := by
  refine ⟨(-((k₀ : ℝ) + 1) + x₀) / 2, ?_, ?_⟩ <;> linarith

theorem gap13 (x₀ : ℝ) (k₀ : ℕ)
    (hk : x₀ < -(k₀ : ℝ)) :
    ∃ β : ℝ, x₀ < β ∧ β < -(k₀ : ℝ) := by
  refine ⟨(x₀ - (k₀ : ℝ)) / 2, ?_, ?_⟩ <;> linarith

theorem gap14 (x₀ : ℝ) (k₀ : ℕ)
    (hk : x₀ < -(k₀ : ℝ)) :
    ∃ β : ℝ, β < -(k₀ : ℝ) := by
  exact ⟨x₀, hk⟩

theorem gap15 (k₀ : ℕ) :
    -((k₀ : ℝ) + 1) < -(k₀ : ℝ) := by
  linarith

theorem gap16 (n : ℕ) (x : ℝ) (hn : 1 ≤ n)
    (hx : x ≠ -(n : ℝ)) :
    HasDerivAt (term n) (derivativeTerm n x) x := by
  exact gap3 n x hn hx

theorem gap17 (k₀ n : ℕ) (α β : ℝ) (hn : 1 ≤ n)
    (hα : -((k₀ : ℝ) + 1) < α) (hβ : β < -(k₀ : ℝ)) :
    ContinuousOn (derivativeTerm n) (Set.Icc α β) := by
  intro x hx
  have hne : (n : ℝ) + x ≠ 0 := by
    by_cases hnk : n ≤ k₀
    · have hnkR : (n : ℝ) ≤ (k₀ : ℝ) := by exact_mod_cast hnk
      have : x < -(n : ℝ) := by linarith [hx.2]
      linarith
    · have hkn : k₀ + 1 ≤ n := Nat.succ_le_iff.mpr (Nat.lt_of_not_ge hnk)
      have hknR : (k₀ : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hkn
      have : -(n : ℝ) < x := by linarith [hx.1]
      linarith
  apply ContinuousAt.continuousWithinAt
  unfold derivativeTerm
  exact continuousAt_const.div
    ((continuousAt_const.add continuousAt_id).pow 2)
    (pow_ne_zero 2 hne)

theorem gap18 (α x : ℝ) (n : ℕ) (hαx : α ≤ x) (hx : x ≤ 0)
    (hn : 2 * |α| < (n : ℝ)) :
    |(n : ℝ) / ((n : ℝ) + x) ^ 2| ≤
      1 / ((n : ℝ) - 2 * |α|) := by
  have hα0 : α ≤ 0 := hαx.trans hx
  have hxabs : |x| ≤ |α| := by
    rw [abs_of_nonpos hx, abs_of_nonpos hα0]
    linarith
  have hxlower : -|α| ≤ x := by
    rw [abs_of_nonpos hx] at hxabs
    linarith
  have hD : 0 < (n : ℝ) - 2 * |α| := by linarith
  have hNA : 0 ≤ (n : ℝ) - |α| := by
    have : 0 ≤ |α| := abs_nonneg α
    linarith
  have hNx : 0 < (n : ℝ) + x := by linarith
  have hsquares :
      ((n : ℝ) - |α|) ^ 2 ≤ ((n : ℝ) + x) ^ 2 := by
    rw [sq_le_sq₀ hNA hNx.le]
    linarith
  rw [abs_of_nonneg (div_nonneg (by positivity) (sq_nonneg _))]
  rw [div_le_div_iff₀ (sq_pos_of_pos hNx) hD]
  nlinarith [sq_nonneg |α|, hsquares]

theorem gap19 (α : ℝ) :
    Tendsto
      (fun n : ℕ => 1 / ((n : ℝ) - 2 * |α|))
      atTop (𝓝 0) := by
  simpa [one_div, sub_eq_add_neg] using
    (tendsto_inv_atTop_zero.comp
      (Filter.tendsto_atTop_add_const_right atTop (-2 * |α|)
        tendsto_natCast_atTop_atTop))

theorem gap20 :
    BoundedSequence alternatingPartialSum := by
  exact gap7

private theorem derivativeSeriesUniformlyConvergesOn_negativeCompact
    (α β : ℝ) (hβ : β < 0) :
    SeriesUniformlyConvergesOn
      (fun n x => derivativeTerm (n + 1) x)
      (Set.Icc α β)
      (fun x => ∑'[SummationFilter.conditional ℕ] n : ℕ,
        derivativeTerm (n + 1) x) := by
  intro ε hε
  obtain ⟨N₀, hN₀⟩ := Metric.tendsto_atTop.1 (gap19 α) ε hε
  obtain ⟨m, hm⟩ := exists_nat_gt (2 * |α|)
  refine ⟨max N₀ m, fun n hn x hx => ?_⟩
  have hxneg : x < 0 := hx.2.trans_lt hβ
  have hα0 : α ≤ 0 := hx.1.trans hxneg.le
  have hxabs : |x| ≤ |α| := by
    rw [abs_of_nonpos hxneg.le, abs_of_nonpos hα0]
    linarith [hx.1]
  let A : ℕ → ℝ := fun k =>
    (((k + 1 : ℕ) : ℝ) / ((((k + 1 : ℕ) : ℝ) + x) ^ 2))
  have ha : Antitone (fun j => A (m + j)) := by
    intro i j hij
    let p : ℝ := ((m + i + 1 : ℕ) : ℝ)
    let q : ℝ := ((m + j + 1 : ℕ) : ℝ)
    have hmp : (m : ℝ) ≤ p := by
      dsimp [p]
      exact_mod_cast (show m ≤ m + i + 1 by omega)
    have hpabs : |α| < p := by linarith [abs_nonneg α, hm, hmp]
    have hxabslt : |x| < p := hxabs.trans_lt hpabs
    have hxp : x < p := lt_of_abs_lt hxabslt
    have hpx : -p < x := neg_lt_of_abs_lt hxabslt
    have hp : 0 < p := (abs_nonneg α).trans_lt hpabs
    have hpq : p ≤ q := by
      dsimp [p, q]
      exact_mod_cast (show m + i + 1 ≤ m + j + 1 by omega)
    have hq : 0 < q := hp.trans_le hpq
    have hdenp : 0 < p + x := by linarith
    have hdenq : 0 < q + x := by linarith
    have hx2p2 : x ^ 2 ≤ p ^ 2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hxp.le) hdenp.le]
    have hp2q : p ^ 2 ≤ p * q := by
      nlinarith [mul_nonneg hp.le (sub_nonneg.mpr hpq)]
    have hx2pq : x ^ 2 ≤ p * q := hx2p2.trans hp2q
    have hfactor : 0 ≤ (q - p) * (p * q - x ^ 2) :=
      mul_nonneg (sub_nonneg.mpr hpq) (sub_nonneg.mpr hx2pq)
    change q / (q + x) ^ 2 ≤ p / (p + x) ^ 2
    rw [div_le_div_iff₀ (sq_pos_of_pos hdenq) (sq_pos_of_pos hdenp)]
    nlinarith
  have ha0 : Tendsto (fun j => A (m + j)) atTop (𝓝 0) := by
    have hInv :
        Tendsto
          (fun j : ℕ => (((j : ℝ) + ((m : ℝ) + 1 + x))⁻¹))
          atTop (𝓝 0) := by
      simpa [add_assoc] using
        (tendsto_inv_atTop_zero.comp
          (Filter.tendsto_atTop_add_const_right atTop
            ((m : ℝ) + 1 + x) tendsto_natCast_atTop_atTop))
    have hlim := hInv.sub ((hInv.mul hInv).const_mul x)
    convert hlim using 1
    · funext j
      dsimp [A]
      let D : ℝ := (j : ℝ) + ((m : ℝ) + 1 + x)
      have hD : D ≠ 0 := by
        dsimp [D]
        have hj : (0 : ℝ) ≤ (j : ℝ) := by positivity
        have hmcast : (m : ℝ) ≤ (m : ℝ) + 1 := by linarith
        linarith [hm, hxabs, neg_abs_le x]
      have hnum : ((m + j + 1 : ℕ) : ℝ) = D - x := by
        dsimp [D]
        push_cast
        ring
      rw [hnum, show D - x + x = D by ring]
      change (D - x) / D ^ 2 = D⁻¹ - x * (D⁻¹ * D⁻¹)
      field_simp [hD]
    · simp
  have hmn : m ≤ n + 1 := by omega
  have herr :=
    conditional_alternating_eventual_error A m (n + 1) hmn ha ha0
  have hmain :
      |(∑ k ∈ Finset.range (n + 1), derivativeTerm (k + 1) x) -
        (∑'[SummationFilter.conditional ℕ] k : ℕ,
          derivativeTerm (k + 1) x)| ≤ A (n + 1) := by
    rw [abs_sub_comm]
    simpa [A, derivativeTerm, div_eq_mul_inv, mul_assoc] using herr
  have hlarge : 2 * |α| < ((n + 2 : ℕ) : ℝ) := by
    have hmn' : m ≤ n := (le_max_right N₀ m).trans hn
    have hmnR : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmn'
    push_cast
    linarith
  have hA_bound :
      A (n + 1) ≤ 1 / (((n + 2 : ℕ) : ℝ) - 2 * |α|) := by
    have hraw := gap18 α x (n + 2) hx.1 hxneg.le hlarge
    have hAnonneg : 0 ≤ A (n + 1) := by
      dsimp [A]
      positivity
    rw [← abs_of_nonneg hAnonneg]
    convert hraw using 1 <;> push_cast <;> ring
  have hn₀ : N₀ ≤ n + 2 := by
    have : N₀ ≤ n := (le_max_left N₀ m).trans hn
    omega
  have hsmall := hN₀ (n + 2) hn₀
  have hden : 0 < ((n + 2 : ℕ) : ℝ) - 2 * |α| := by linarith
  have hqnonneg :
      0 ≤ 1 / (((n + 2 : ℕ) : ℝ) - 2 * |α|) := by positivity
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hqnonneg] at hsmall
  exact lt_of_le_of_lt (hmain.trans hA_bound) hsmall

theorem gap21 (k₀ : ℕ) (α β : ℝ)
    (hα : -((k₀ : ℝ) + 1) < α) (hβ : β < -(k₀ : ℝ)) :
    SeriesUniformlyConvergesOn
      (fun n x => derivativeTerm (n + 1) x)
      (Set.Icc α β)
      (fun x => ∑'[SummationFilter.conditional ℕ] n : ℕ,
        derivativeTerm (n + 1) x) := by
  have hk0 : (0 : ℝ) ≤ (k₀ : ℝ) := by positivity
  exact derivativeSeriesUniformlyConvergesOn_negativeCompact α β (by linarith)

theorem gap22 (x₀ : ℝ) (hx₀ : x₀ < 0)
    (hreg : IsRegularPoint x₀) :
    DifferentiableAt ℝ f x₀ := by
  obtain ⟨k₀, hkleft, hkright⟩ := gap10 x₀ hx₀ hreg
  obtain ⟨α, hkα, hαx⟩ := gap12 x₀ k₀ hkleft
  obtain ⟨β, hxβ, hβk⟩ := gap13 x₀ k₀ hkright
  let s : Set ℝ := Set.Ioo α β
  have hxmem : x₀ ∈ s := ⟨hαx, hxβ⟩
  have hregular : ∀ y ∈ s, IsRegularPoint y := by
    intro y hy k hk heq
    dsimp [s] at hy
    change α < y ∧ y < β at hy
    by_cases hkk : k ≤ k₀
    · have hkkR : (k : ℝ) ≤ (k₀ : ℝ) := by exact_mod_cast hkk
      linarith
    · have hkk' : k₀ + 1 ≤ k := Nat.succ_le_iff.mpr (Nat.lt_of_not_ge hkk)
      have hkkR : (k₀ : ℝ) + 1 ≤ (k : ℝ) := by exact_mod_cast hkk'
      linarith
  let F : ℕ → ℝ → ℝ := fun n y =>
    ∑ k ∈ Finset.range (n + 1), term (k + 1) y
  let F' : ℕ → ℝ → ℝ := fun n y =>
    ∑ k ∈ Finset.range (n + 1), derivativeTerm (k + 1) y
  let G' : ℝ → ℝ := fun y =>
    ∑'[SummationFilter.conditional ℕ] k : ℕ, derivativeTerm (k + 1) y
  have hu := gap21 k₀ α β hkα hβk
  have hU : TendstoUniformlyOn F' G' atTop s := by
    refine Metric.tendstoUniformlyOn_iff.mpr fun ε hε => ?_
    obtain ⟨N, hN⟩ := hu ε hε
    filter_upwards [Filter.eventually_ge_atTop N] with n hn
    intro y hy
    have hbound := hN n hn y ⟨hy.1.le, hy.2.le⟩
    simpa [F', G', Real.dist_eq, abs_sub_comm] using hbound
  have hDeriv :
      ∀ᶠ n in atTop, ∀ y ∈ s, HasDerivAt (F n) (F' n y) y := by
    filter_upwards [] with n
    intro y hy
    dsimp [F, F']
    apply HasDerivAt.fun_sum
    intro k hk
    exact gap3 (k + 1) y (by omega) (hregular y hy (k + 1) (by omega))
  have hConv : ∀ y ∈ s, Tendsto (fun n => F n y) atTop (𝓝 (f y)) := by
    intro y hy
    have hsum := conditional_tsum_tendsto (gap1 y (hregular y hy))
    have hshift := hsum.comp (Filter.tendsto_add_atTop_nat 1)
    simpa [F, f] using hshift
  exact
    (hasDerivAt_of_tendstoUniformlyOn isOpen_Ioo hU hDeriv hConv hxmem).differentiableAt

theorem gap23 :
    seriesDomain = {x : ℝ | IsRegularPoint x} := by
  ext x
  simp only [seriesDomain, Set.mem_setOf_eq, IsRegularPoint]
  constructor
  · intro h k hk hx
    apply h k hk
    linarith
  · intro h k hk hx
    apply h k hk
    linarith

private theorem term_not_differentiableAt_pole (k : ℕ) (hk : 1 ≤ k) :
    ¬ DifferentiableAt ℝ (term k) (-(k : ℝ)) := by
  intro hd
  let y : ℕ → ℝ := fun n => -(k : ℝ) + 1 / ((n : ℝ) + 1)
  have hy : Tendsto y atTop (𝓝 (-(k : ℝ))) := by
    have hzero := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    simpa [y] using (tendsto_const_nhds.add hzero)
  have ht := hd.continuousAt.tendsto.comp hy
  have ht0 : Tendsto (fun n => term k (y n)) atTop (𝓝 0) := by
    simpa [term] using ht
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 ht0 1 zero_lt_one
  let n : ℕ := max N 1
  have hnN : N ≤ n := le_max_left N 1
  have hn1 : 1 ≤ n := le_max_right N 1
  have hclose := hN n hnN
  have hval :
      term k (y n) =
        (-1 : ℝ) ^ k * (1 - (k : ℝ) * ((n : ℝ) + 1)) := by
    dsimp [y, term]
    have hden : (n : ℝ) + 1 ≠ 0 := by positivity
    field_simp [hden]
    ring
  have hkR : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  have hn2 : (2 : ℝ) ≤ (n : ℝ) + 1 := by linarith
  have hprod : (2 : ℝ) ≤ (k : ℝ) * ((n : ℝ) + 1) := by
    calc
      (2 : ℝ) = 1 * 2 := by ring
      _ ≤ (k : ℝ) * ((n : ℝ) + 1) :=
        mul_le_mul hkR hn2 (by norm_num) (by positivity)
  have hnonpos : 1 - (k : ℝ) * ((n : ℝ) + 1) ≤ 0 := by linarith
  have habs :
      |term k (y n)| = (k : ℝ) * ((n : ℝ) + 1) - 1 := by
    rw [hval, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
      abs_of_nonpos hnonpos]
    ring
  have hlower : 1 ≤ |term k (y n)| := by rw [habs]; linarith
  rw [Real.dist_eq, sub_zero] at hclose
  linarith

private theorem f_eq_prefix_add_tail (k : ℕ) (x : ℝ) :
    f x =
      (∑ i ∈ Finset.range k, term (i + 1) x) +
        ∑'[SummationFilter.conditional ℕ] j : ℕ, term (k + j + 1) x := by
  have hfull := conditional_tsum_tendsto (term_conditional_summable x)
  have hshift := hfull.comp (Filter.tendsto_add_atTop_nat k)
  have hrewrite :
      (fun n : ℕ =>
        ∑ i ∈ Finset.range (n + k), term (i + 1) x) =
      (fun n : ℕ =>
        (∑ i ∈ Finset.range k, term (i + 1) x) +
          ∑ j ∈ Finset.range n, term (k + j + 1) x) := by
    funext n
    rw [Nat.add_comm n k, Finset.sum_range_add]
  change
    Tendsto
      (fun n : ℕ => ∑ i ∈ Finset.range (n + k), term (i + 1) x)
      atTop (𝓝 (f x)) at hshift
  rw [hrewrite] at hshift
  let pref : ℝ := ∑ i ∈ Finset.range k, term (i + 1) x
  have htail :
      Tendsto
        (fun n : ℕ => ∑ j ∈ Finset.range n, term (k + j + 1) x)
        atTop (𝓝 (f x - pref)) := by
    have hpref :
        Tendsto (fun _ : ℕ => pref) atTop (𝓝 pref) := tendsto_const_nhds
    have hsub := hshift.sub hpref
    simpa [pref] using hsub
  have hsum := conditional_hasSum_of_tendsto htail
  have heq := hsum.tsum_eq
  rw [heq]
  simp [pref]

private theorem conditional_tail_eq_smooth (k : ℕ) (x : ℝ)
    (hx : x + (k : ℝ) + 1 ≠ 0) :
    (∑'[SummationFilter.conditional ℕ] j : ℕ, term (k + j + 1) x) =
      (-1 : ℝ) ^ k * x *
        (-1 / (x + (k : ℝ) + 1) -
          f (x + (k : ℝ) + 1) / (x + (k : ℝ) + 1)) := by
  let w : ℝ := x + (k : ℝ) + 1
  let b : ℕ → ℝ := fun j =>
    (-1 : ℝ) ^ (j + 1) / ((j : ℝ) + w)
  have hw : w ≠ 0 := by simpa [w] using hx
  have hf := conditional_tsum_tendsto (term_conditional_summable w)
  have hpartials :
      (fun n : ℕ => ∑ j ∈ Finset.range (n + 1), b j) =
      (fun n : ℕ =>
        -w⁻¹ + (-w⁻¹) *
          (∑ j ∈ Finset.range n, term (j + 1) w)) := by
    funext n
    rw [Nat.add_comm n 1, Finset.sum_range_add]
    simp only [Finset.sum_range_one]
    rw [Finset.mul_sum]
    congr 1
    · simp [b, div_eq_mul_inv]
    · apply Finset.sum_congr rfl
      intro j hj
      simp [b, term, div_eq_mul_inv, pow_succ, hw]
      have hcancel : w⁻¹ * w = 1 := inv_mul_cancel₀ hw
      calc
        -((-1 : ℝ) ^ (1 + j) * (1 + (j : ℝ) + w)⁻¹) =
            (-1 : ℝ) ^ j * ((j : ℝ) + 1 + w)⁻¹ := by
          rw [show 1 + j = j + 1 by omega, pow_succ]
          congr 1
          ring_nf
        _ = (w⁻¹ * w) *
            ((-1 : ℝ) ^ j * ((j : ℝ) + 1 + w)⁻¹) := by
          rw [hcancel]
          ring
        _ = w⁻¹ *
            ((-1 : ℝ) ^ j * w * ((j : ℝ) + 1 + w)⁻¹) := by ring
  have hb :
      Tendsto (fun n : ℕ => ∑ j ∈ Finset.range n, b j) atTop
        (𝓝 (-w⁻¹ + (-w⁻¹) * f w)) := by
    apply (Filter.tendsto_add_atTop_iff_nat 1).mp
    rw [hpartials]
    exact (hf.const_mul (-w⁻¹)).const_add (-w⁻¹)
  let c : ℝ := (-1 : ℝ) ^ k * x
  have htail :
      Tendsto
        (fun n : ℕ => ∑ j ∈ Finset.range n, term (k + j + 1) x)
        atTop (𝓝 (c * (-w⁻¹ + (-w⁻¹) * f w))) := by
    have hscaled := hb.const_mul c
    convert hscaled using 1
    funext n
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    simp [c, b, term, div_eq_mul_inv, pow_add]
    ring
  have heq := (conditional_hasSum_of_tendsto htail).tsum_eq
  rw [heq]
  simp only [c, w]
  field_simp [hx]
  ring

theorem gap24 :
    {x : ℝ | DifferentiableAt ℝ f x} =
      {x : ℝ | IsRegularPoint x} := by
  ext x
  simp only [Set.mem_setOf_eq]
  constructor
  · intro hdiff k hk hx
    subst x
    let p : ℝ := -(k : ℝ)
    let P : ℝ → ℝ := fun z =>
      ∑ i ∈ Finset.range (k - 1), term (i + 1) z
    let r : ℝ → ℝ := fun z =>
      ∑'[SummationFilter.conditional ℕ] j : ℕ, term (k + j + 1) z
    let q : ℝ → ℝ := fun z =>
      -1 / (z + (k : ℝ) + 1) -
        f (z + (k : ℝ) + 1) / (z + (k : ℝ) + 1)
    have hp : p + (k : ℝ) + 1 = 1 := by simp [p]
    have hg :
        DifferentiableAt ℝ (fun z : ℝ => z + (k : ℝ) + 1) p := by
      fun_prop
    have hfg :
        DifferentiableAt ℝ (fun z : ℝ => f (z + (k : ℝ) + 1)) p := by
      have hf1 : DifferentiableAt ℝ f 1 := gap9 1 (by norm_num)
      have hfarg : DifferentiableAt ℝ f (p + (k : ℝ) + 1) := by
        simpa [hp] using hf1
      simpa [Function.comp_def] using hfarg.comp p hg
    have hq : DifferentiableAt ℝ q p := by
      dsimp [q]
      exact
        ((differentiableAt_const (-1 : ℝ)).div hg (by simpa [hp])).sub
          (hfg.div hg (by simpa [hp]))
    have hsmooth :
        DifferentiableAt ℝ
          (fun z : ℝ => (-1 : ℝ) ^ k * z * q z) p := by
      exact
        ((differentiableAt_const ((-1 : ℝ) ^ k)).mul
          differentiableAt_id).mul hq
    have hr_eventually :
        r =ᶠ[𝓝 p] (fun z : ℝ => (-1 : ℝ) ^ k * z * q z) := by
      have hmem : Set.Ioo (p - (1 / 2 : ℝ)) (p + (1 / 2 : ℝ)) ∈ 𝓝 p :=
        Ioo_mem_nhds (by linarith) (by linarith)
      filter_upwards [hmem] with z hz
      dsimp [r, q]
      apply conditional_tail_eq_smooth k z
      rcases hz with ⟨hzl, hzu⟩
      dsimp [p] at hzl hzu
      intro hzero
      linarith
    have hr : DifferentiableAt ℝ r p :=
      hsmooth.congr_of_eventuallyEq hr_eventually
    have hP : DifferentiableAt ℝ P p := by
      have hP' :
          HasDerivAt P
            (∑ i ∈ Finset.range (k - 1), derivativeTerm (i + 1) p) p := by
        dsimp [P]
        apply HasDerivAt.fun_sum
        intro i hi
        apply gap3 (i + 1) p (by omega)
        intro heq
        have hik : i + 1 < k := by
          have := Finset.mem_range.mp hi
          omega
        have hikR : (((i + 1 : ℕ) : ℝ)) < (k : ℝ) := by exact_mod_cast hik
        dsimp [p] at heq
        linarith
      exact hP'.differentiableAt
    have hdecomp : ∀ z : ℝ, f z = P z + term k z + r z := by
      intro z
      have h := f_eq_prefix_add_tail k z
      have hk' : k - 1 + 1 = k := Nat.sub_add_cancel hk
      have hprefix :
          (∑ i ∈ Finset.range k, term (i + 1) z) =
            (∑ i ∈ Finset.range (k - 1), term (i + 1) z) + term k z := by
        conv_lhs => rw [← hk', Finset.sum_range_succ]
        simp [hk']
      rw [hprefix] at h
      simpa [P, r, add_assoc] using h
    have hrest :
        DifferentiableAt ℝ (fun z : ℝ => f z - P z - r z) p :=
      (hdiff.sub hP).sub hr
    have hterm :
        (fun z : ℝ => term k z) =ᶠ[𝓝 p]
          (fun z : ℝ => f z - P z - r z) := by
      filter_upwards [] with z
      have hz := hdecomp z
      linarith
    exact term_not_differentiableAt_pole k hk
      (hrest.congr_of_eventuallyEq hterm)
  · intro hreg
    by_cases hx0 : 0 ≤ x
    · exact gap9 x hx0
    · exact gap22 x (lt_of_not_ge hx0) hreg

end

end ProofGap.Exercise2799_1
