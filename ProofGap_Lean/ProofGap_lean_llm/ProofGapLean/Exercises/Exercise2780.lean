import ProofGapLean.Prelude.Analysis
import Mathlib.Tactic.IntervalCases

namespace ProofGap.Exercise2780

noncomputable section

open Filter
open scoped BigOperators

def coefficient (k : ℕ) : ℝ :=
  Real.cos (2 * k * Real.pi / 3)

def weight (n : ℕ) (x : ℝ) : ℝ :=
  1 / Real.sqrt ((n : ℝ) ^ 2 + x ^ 2)

def term (n : ℕ) (x : ℝ) : ℝ :=
  coefficient n * weight n x

def SeriesUniformlyConvergesOn
    (u : ℕ → ℝ → ℝ) (s : Set ℝ) (f : ℝ → ℝ) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ x ∈ s,
    |(∑ k ∈ Finset.range (n + 1), u k x) - f x| < ε

private theorem coefficient_add_three (n : ℕ) :
    coefficient (n + 3) = coefficient n := by
  unfold coefficient
  rw [show (2 : ℝ) * (n + 3 : ℕ) * Real.pi / 3 =
      2 * (n : ℝ) * Real.pi / 3 + 2 * Real.pi by push_cast; ring]
  exact Real.cos_add_two_pi _

private theorem coefficient_zero : coefficient 0 = 1 := by
  simp [coefficient]

private theorem coefficient_one : coefficient 1 = -(1 / 2 : ℝ) := by
  unfold coefficient
  rw [show (2 : ℝ) * (1 : ℕ) * Real.pi / 3 =
      Real.pi - Real.pi / 3 by norm_num; ring]
  rw [Real.cos_pi_sub, Real.cos_pi_div_three]

private theorem coefficient_two : coefficient 2 = -(1 / 2 : ℝ) := by
  unfold coefficient
  rw [show (2 : ℝ) * (2 : ℕ) * Real.pi / 3 =
      Real.pi / 3 + Real.pi by norm_num; ring]
  rw [Real.cos_add_pi, Real.cos_pi_div_three]

private theorem coefficient_block_zero (n : ℕ) :
    coefficient n + coefficient (n + 1) + coefficient (n + 2) = 0 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases hn : n < 3
      · interval_cases n
        · norm_num [coefficient_zero, coefficient_one, coefficient_two]
        · have h3 : coefficient 3 = coefficient 0 := by
            simpa using coefficient_add_three 0
          norm_num [coefficient_one, coefficient_two, h3, coefficient_zero]
        · have h3 : coefficient 3 = coefficient 0 := by
            simpa using coefficient_add_three 0
          have h4 : coefficient 4 = coefficient 1 := by
            simpa using coefficient_add_three 1
          norm_num [coefficient_two, h3, h4, coefficient_zero, coefficient_one]
      · have h0 : coefficient n = coefficient (n - 3) := by
          calc
            coefficient n = coefficient ((n - 3) + 3) := by congr 1 <;> omega
            _ = coefficient (n - 3) := coefficient_add_three _
        have h1 : coefficient (n + 1) = coefficient (n - 3 + 1) := by
          calc
            coefficient (n + 1) = coefficient ((n - 3 + 1) + 3) := by congr 1 <;> omega
            _ = coefficient (n - 3 + 1) := coefficient_add_three _
        have h2 : coefficient (n + 2) = coefficient (n - 3 + 2) := by
          calc
            coefficient (n + 2) = coefficient ((n - 3 + 2) + 3) := by congr 1 <;> omega
            _ = coefficient (n - 3 + 2) := coefficient_add_three _
        rw [h0, h1, h2]
        exact ih (n - 3) (by omega)

private theorem coefficient_prefix_add_three (n : ℕ) :
    (∑ k ∈ Finset.range (n + 3), coefficient (k + 1)) =
      ∑ k ∈ Finset.range n, coefficient (k + 1) := by
  rw [Finset.sum_range_add]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  rw [coefficient_block_zero (n + 1)]
  ring

private theorem coefficient_prefix_bound (n : ℕ) :
    |∑ k ∈ Finset.range n, coefficient (k + 1)| ≤ 1 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases hn : n < 3
      · interval_cases n <;>
          norm_num [Finset.sum_range_succ, coefficient_one, coefficient_two]
      · have hn3 : 3 ≤ n := by omega
        rw [show n = (n - 3) + 3 by omega, coefficient_prefix_add_three]
        exact ih (n - 3) (by omega)

theorem gap1 (n : ℕ) :
    |∑ k ∈ Finset.Icc 1 n, coefficient k| ≤
      1 / |Real.sin (Real.pi / 3)| := by
  have hbound : |∑ k ∈ Finset.Icc 1 n, coefficient k| ≤ 1 := by
    rw [← Finset.Ico_add_one_right_eq_Icc]
    rw [Finset.sum_Ico_eq_sum_range]
    simpa [Nat.add_comm] using coefficient_prefix_bound n
  have hsqrt : Real.sqrt 3 ≤ 2 := by nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  have hsqrt_pos : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  have hsin_pos : 0 < Real.sqrt 3 / 2 := div_pos hsqrt_pos (by norm_num)
  rw [Real.sin_pi_div_three, abs_of_pos hsin_pos]
  calc
    |∑ k ∈ Finset.Icc 1 n, coefficient k| ≤ 1 := hbound
    _ ≤ 1 / (Real.sqrt 3 / 2) := by
      apply (le_div_iff₀ hsin_pos).2
      nlinarith

theorem gap2 :
    1 / |Real.sin (Real.pi / 3)| = 2 / Real.sqrt 3 := by
  have hsqrt_pos : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  have hsin_pos : 0 < Real.sqrt 3 / 2 := div_pos hsqrt_pos (by norm_num)
  rw [Real.sin_pi_div_three, abs_of_pos hsin_pos]
  field_simp [ne_of_gt hsqrt_pos]

theorem gap3 (n : ℕ) :
    |∑ k ∈ Finset.Icc 1 n, coefficient k| ≤
      2 / Real.sqrt 3 := by
  rw [← gap2]
  exact gap1 n

private theorem weight_nonneg (n : ℕ) (x : ℝ) : 0 ≤ weight n x := by
  unfold weight
  positivity

theorem gap4 (n : ℕ) (x : ℝ) (hn : 1 ≤ n) :
    weight n x > weight (n + 1) x := by
  have hn_pos : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hrad_pos : 0 < (n : ℝ) ^ 2 + x ^ 2 := by positivity
  have hrad_lt : (n : ℝ) ^ 2 + x ^ 2 < ((n + 1 : ℕ) : ℝ) ^ 2 + x ^ 2 := by
    push_cast
    nlinarith
  unfold weight
  exact one_div_lt_one_div_of_lt (Real.sqrt_pos.2 hrad_pos)
    (Real.sqrt_lt_sqrt hrad_pos.le hrad_lt)

theorem gap5 (n : ℕ) (x : ℝ) (hn : 1 ≤ n) :
    weight n x ≤ 1 / (n : ℝ) := by
  have hn_pos : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hsqrt : (n : ℝ) ≤ Real.sqrt ((n : ℝ) ^ 2 + x ^ 2) := by
    have hrad_nonneg : 0 ≤ (n : ℝ) ^ 2 + x ^ 2 := by positivity
    nlinarith [Real.sq_sqrt hrad_nonneg, Real.sqrt_nonneg ((n : ℝ) ^ 2 + x ^ 2),
      sq_nonneg x]
  unfold weight
  exact one_div_le_one_div_of_le hn_pos hsqrt

theorem gap6 (x : ℝ) :
    Tendsto (fun n : ℕ => weight n x) atTop (nhds 0) := by
  rw [← Filter.tendsto_add_atTop_iff_nat 1]
  refine squeeze_zero (g := fun n : ℕ => 1 / ((n : ℝ) + 1))
    (fun n => weight_nonneg (n + 1) x) (fun n => ?_) ?_
  · simpa [Nat.cast_add, Nat.cast_one] using gap5 (n + 1) x (by omega)
  · simpa [Nat.cast_add, Nat.cast_one] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

private theorem coefficient_shift_sum_bound (N n : ℕ) :
    |∑ i ∈ Finset.range n, coefficient (N + 1 + i)| ≤ 2 := by
  have hadd := Finset.sum_range_add (f := fun i => coefficient (i + 1)) N n
  have heq :
      (∑ i ∈ Finset.range n, coefficient (N + 1 + i)) =
        (∑ i ∈ Finset.range (N + n), coefficient (i + 1)) -
          ∑ i ∈ Finset.range N, coefficient (i + 1) := by
    rw [hadd]
    simp only [add_sub_cancel_left]
    apply Finset.sum_congr rfl
    intro i hi
    congr 1
    omega
  rw [heq]
  calc
    |(∑ i ∈ Finset.range (N + n), coefficient (i + 1)) -
        ∑ i ∈ Finset.range N, coefficient (i + 1)| ≤
        |∑ i ∈ Finset.range (N + n), coefficient (i + 1)| +
          |∑ i ∈ Finset.range N, coefficient (i + 1)| := abs_sub _ _
    _ ≤ 1 + 1 := add_le_add (coefficient_prefix_bound _) (coefficient_prefix_bound _)
    _ = 2 := by norm_num

private theorem weight_shift_antitone (N : ℕ) (x : ℝ) :
    Antitone (fun i => weight (N + 1 + i) x) := by
  refine antitone_nat_of_succ_le (fun i => ?_)
  have h := (gap4 (N + 1 + i) x (by omega)).le
  simpa [Nat.add_assoc] using h

private theorem weight_shift_tendsto_zero (N : ℕ) (x : ℝ) :
    Tendsto (fun i => weight (N + 1 + i) x) atTop (nhds 0) := by
  have h := (gap6 x).comp (tendsto_add_atTop_nat (N + 1))
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

private theorem dirichlet_sum_bound
    (a z : ℕ → ℝ) (B : ℝ)
    (ha : ∀ i, 0 ≤ a i) (hanti : Antitone a)
    (hz : ∀ n, |∑ i ∈ Finset.range n, z i| ≤ B) (n : ℕ) :
    |∑ i ∈ Finset.range n, a i * z i| ≤ B * a 0 := by
  have hB : 0 ≤ B := by
    simpa using hz 0
  cases n with
  | zero =>
      simp only [Finset.range_zero, Finset.sum_empty, abs_zero]
      exact mul_nonneg hB (ha 0)
  | succ n =>
      have hparts :
          (∑ i ∈ Finset.range (n + 1), a i * z i) =
            a n * (∑ i ∈ Finset.range (n + 1), z i) -
              ∑ i ∈ Finset.range n,
                (a (i + 1) - a i) * (∑ j ∈ Finset.range (i + 1), z j) := by
        simpa [smul_eq_mul] using Finset.sum_range_by_parts a z (n + 1)
      have hfirst :
          |a n * (∑ i ∈ Finset.range (n + 1), z i)| ≤ a n * B := by
        rw [abs_mul, abs_of_nonneg (ha n)]
        exact mul_le_mul_of_nonneg_left (hz _) (ha n)
      have hsum :
          |∑ i ∈ Finset.range n,
              (a (i + 1) - a i) * (∑ j ∈ Finset.range (i + 1), z j)| ≤
            ∑ i ∈ Finset.range n, (a i - a (i + 1)) * B := by
        calc
          |∑ i ∈ Finset.range n,
              (a (i + 1) - a i) * (∑ j ∈ Finset.range (i + 1), z j)| ≤
              ∑ i ∈ Finset.range n,
                |(a (i + 1) - a i) * (∑ j ∈ Finset.range (i + 1), z j)| :=
            Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ i ∈ Finset.range n, (a i - a (i + 1)) * B := by
            apply Finset.sum_le_sum
            intro i hi
            have hdiff : 0 ≤ a i - a (i + 1) :=
              sub_nonneg.mpr (hanti (Nat.le_succ i))
            rw [abs_mul, abs_of_nonpos (sub_nonpos.mpr (hanti (Nat.le_succ i))), neg_sub]
            exact mul_le_mul_of_nonneg_left (hz _) hdiff
      rw [hparts]
      calc
        |a n * (∑ i ∈ Finset.range (n + 1), z i) -
            ∑ i ∈ Finset.range n,
              (a (i + 1) - a i) * (∑ j ∈ Finset.range (i + 1), z j)| ≤
            |a n * (∑ i ∈ Finset.range (n + 1), z i)| +
              |∑ i ∈ Finset.range n,
                (a (i + 1) - a i) * (∑ j ∈ Finset.range (i + 1), z j)| := abs_sub _ _
        _ ≤ a n * B + ∑ i ∈ Finset.range n, (a i - a (i + 1)) * B :=
          add_le_add hfirst hsum
        _ = B * a 0 := by
          rw [← Finset.sum_mul, Finset.sum_range_sub']
          ring

private theorem term_tail_bound (N m : ℕ) (x : ℝ) :
    |∑ i ∈ Finset.range m, term (N + 1 + i) x| ≤ 2 * weight (N + 1) x := by
  have h := dirichlet_sum_bound
    (fun i => weight (N + 1 + i) x)
    (fun i => coefficient (N + 1 + i)) 2
    (fun i => weight_nonneg _ _)
    (weight_shift_antitone N x)
    (coefficient_shift_sum_bound N) m
  simpa [term, mul_comm] using h

private theorem hasSum_conditional_iff_tendsto_range (f : ℕ → ℝ) (s : ℝ) :
    HasSum f s (SummationFilter.conditional ℕ) ↔
      Tendsto (fun n => ∑ i ∈ Finset.range n, f i) atTop (nhds s) := by
  simp only [HasSum, SummationFilter.conditional_filter_eq_map_range,
    tendsto_map'_iff]
  rfl

private theorem conditional_series_data (x : ℝ) :
    ∃ s : ℝ,
      HasSum (fun n => term (n + 1) x) s (SummationFilter.conditional ℕ) := by
  have hanti : Antitone (fun i => weight (1 + i) x) := by
    simpa only [zero_add] using weight_shift_antitone 0 x
  have htend : Tendsto (fun i => weight (1 + i) x) atTop (nhds 0) := by
    simpa only [zero_add] using weight_shift_tendsto_zero 0 x
  have hbound : ∀ n, ‖∑ i ∈ Finset.range n, coefficient (1 + i)‖ ≤ (1 : ℝ) := by
    intro n
    simpa [Nat.add_comm] using coefficient_prefix_bound n
  have hc0 : CauchySeq
      (fun n => ∑ i ∈ Finset.range n, weight (1 + i) x • coefficient (1 + i)) :=
    hanti.cauchySeq_series_mul_of_tendsto_zero_of_bounded htend hbound
  have hc : CauchySeq (fun n => ∑ i ∈ Finset.range n, term (i + 1) x) := by
    simpa [term, smul_eq_mul, mul_comm, Nat.add_comm] using hc0
  obtain ⟨s, hs⟩ := cauchySeq_tendsto_of_complete hc
  exact ⟨s, (hasSum_conditional_iff_tendsto_range _ _).2 hs⟩

private theorem term_remainder_bound (x s : ℝ)
    (hs : HasSum (fun n => term (n + 1) x) s (SummationFilter.conditional ℕ))
    (n : ℕ) :
    |(∑ i ∈ Finset.range (n + 1), term (i + 1) x) - s| ≤
      2 * weight (n + 2) x := by
  have hseries := (hasSum_conditional_iff_tendsto_range _ _).1 hs
  have htotal :
      Tendsto (fun m => ∑ i ∈ Finset.range (n + 1 + m), term (i + 1) x)
        atTop (nhds s) := by
    simpa [Nat.add_comm] using hseries.comp (tendsto_add_atTop_nat (n + 1))
  have hlim :
      Tendsto
        (fun m => |(∑ i ∈ Finset.range (n + 1), term (i + 1) x) -
          ∑ i ∈ Finset.range (n + 1 + m), term (i + 1) x|)
        atTop
        (nhds |(∑ i ∈ Finset.range (n + 1), term (i + 1) x) - s|) := by
    exact (tendsto_const_nhds.sub htotal).abs
  apply le_of_tendsto' hlim
  intro m
  have htail := term_tail_bound (n + 1) m x
  have hsplit :
      (∑ i ∈ Finset.range (n + 1 + m), term (i + 1) x) =
        (∑ i ∈ Finset.range (n + 1), term (i + 1) x) +
          ∑ i ∈ Finset.range m, term (n + 1 + i + 1) x := by
    simpa using Finset.sum_range_add (f := fun i => term (i + 1) x) (n + 1) m
  rw [hsplit]
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htail

theorem gap7 :
    SeriesUniformlyConvergesOn
      (fun n x => term (n + 1) x)
      Set.univ
      (fun x => ∑'[SummationFilter.conditional ℕ] n : ℕ, term (n + 1) x) := by
  intro ε hε
  have hmajorant :
      Tendsto (fun n : ℕ => 2 / ((n + 2 : ℕ) : ℝ)) atTop (nhds 0) := by
    simpa only [Function.comp_apply] using
      (tendsto_const_div_atTop_nhds_zero_nat (2 : ℝ)).comp (tendsto_add_atTop_nat 2)
  have hevent : ∀ᶠ n : ℕ in atTop, 2 / ((n + 2 : ℕ) : ℝ) < ε :=
    (tendsto_order.1 hmajorant).2 ε hε
  obtain ⟨N, hN⟩ := (eventually_atTop.1 hevent)
  refine ⟨N, fun n hn x hx => ?_⟩
  obtain ⟨s, hs⟩ := conditional_series_data x
  have htsum : (∑'[SummationFilter.conditional ℕ] i : ℕ, term (i + 1) x) = s :=
    hs.tsum_eq
  change |(∑ k ∈ Finset.range (n + 1), term (k + 1) x) -
    (∑'[SummationFilter.conditional ℕ] i : ℕ, term (i + 1) x)| < ε
  rw [htsum]
  refine lt_of_le_of_lt (term_remainder_bound x s hs n) ?_
  have hw := gap5 (n + 2) x (by omega)
  calc
    2 * weight (n + 2) x ≤ 2 * (1 / ((n + 2 : ℕ) : ℝ)) := by gcongr
    _ = 2 / ((n + 2 : ℕ) : ℝ) := by ring
    _ < ε := hN n hn

theorem gap8 :
    SeriesUniformlyConvergesOn
      (fun n x => term (n + 1) x)
      Set.univ
      (fun x => ∑'[SummationFilter.conditional ℕ] n : ℕ, term (n + 1) x) := by
  exact gap7

end

end ProofGap.Exercise2780
