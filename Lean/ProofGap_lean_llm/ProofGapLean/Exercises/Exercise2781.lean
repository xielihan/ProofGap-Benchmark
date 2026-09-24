import ProofGapLean.Prelude.Analysis

namespace ProofGap.Exercise2781

noncomputable section

open Filter
open scoped BigOperators

def coefficient (n : ℕ) (x : ℝ) : ℝ :=
  Real.sin x * Real.sin ((n : ℝ) * x)

def weight (n : ℕ) (x : ℝ) : ℝ :=
  1 / Real.sqrt ((n : ℝ) + x)

def term (n : ℕ) (x : ℝ) : ℝ :=
  coefficient n x * weight n x

def SeriesUniformlyConvergesOn
    (u : ℕ → ℝ → ℝ) (s : Set ℝ) (f : ℝ → ℝ) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ x ∈ s,
    |(∑ k ∈ Finset.range (n + 1), u k x) - f x| < ε

private theorem sine_product_identity (k : ℕ) (x : ℝ) :
    2 * Real.sin (x / 2) * Real.sin ((k : ℝ) * x) =
      Real.cos ((k : ℝ) * x - x / 2) - Real.cos (((k + 1 : ℕ) : ℝ) * x - x / 2) := by
  rw [show (((k + 1 : ℕ) : ℝ) * x - x / 2) =
      (k : ℝ) * x + x / 2 by push_cast; ring]
  rw [Real.cos_sub, Real.cos_add]
  ring

private theorem sine_sum_identity (n : ℕ) (x : ℝ) :
    2 * Real.sin (x / 2) *
        (∑ k ∈ Finset.Icc 1 n, Real.sin ((k : ℝ) * x)) =
      Real.cos (x / 2) - Real.cos (((n : ℝ) + 1 / 2) * x) := by
  calc
    2 * Real.sin (x / 2) *
        (∑ k ∈ Finset.Icc 1 n, Real.sin ((k : ℝ) * x)) =
        ∑ k ∈ Finset.Icc 1 n, 2 * Real.sin (x / 2) * Real.sin ((k : ℝ) * x) := by
      rw [Finset.mul_sum]
    _ = ∑ k ∈ Finset.Icc 1 n,
        (Real.cos ((k : ℝ) * x - x / 2) -
          Real.cos (((k + 1 : ℕ) : ℝ) * x - x / 2)) := by
      apply Finset.sum_congr rfl
      intro k hk
      exact sine_product_identity k x
    _ = Real.cos (x / 2) - Real.cos (((n : ℝ) + 1 / 2) * x) := by
      rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
      simp only [Nat.add_sub_cancel, Nat.add_assoc]
      let g : ℕ → ℝ := fun k => Real.cos (((1 + k : ℕ) : ℝ) * x - x / 2)
      change (∑ k ∈ Finset.range n, (g k - g (k + 1))) = _
      rw [Finset.sum_range_sub']
      simp [g]
      push_cast
      ring

theorem gap1 (m n : ℕ) (x : ℝ)
    (hx : x = 2 * (m : ℝ) * Real.pi) :
    ∑ k ∈ Finset.Icc 1 n, coefficient k x = 0 := by
  have hsin : Real.sin x = 0 := by
    rw [hx, show 2 * (m : ℝ) * Real.pi = ((2 * m : ℕ) : ℝ) * Real.pi by push_cast; ring]
    exact Real.sin_nat_mul_pi _
  simp [coefficient, hsin]

theorem gap2 (n : ℕ) (x : ℝ) :
    |∑ k ∈ Finset.Icc 1 n, coefficient k x| =
      |Real.sin x| *
        |∑ k ∈ Finset.Icc 1 n, Real.sin ((k : ℝ) * x)| := by
  simp only [coefficient, ← Finset.mul_sum, abs_mul]

theorem gap3 (n : ℕ) (x : ℝ) (hx : Real.sin (x / 2) ≠ 0) :
    |Real.sin x| *
        |∑ k ∈ Finset.Icc 1 n, Real.sin ((k : ℝ) * x)| ≤
      |Real.sin x| / |Real.sin (x / 2)| := by
  have hsin_pos : 0 < |Real.sin (x / 2)| := abs_pos.mpr hx
  have hcos (y : ℝ) : |Real.cos y| ≤ 1 := (abs_le).2 (Real.cos_mem_Icc y)
  have hprod :
      2 * |Real.sin (x / 2)| *
          |∑ k ∈ Finset.Icc 1 n, Real.sin ((k : ℝ) * x)| ≤ 2 := by
    calc
      2 * |Real.sin (x / 2)| *
          |∑ k ∈ Finset.Icc 1 n, Real.sin ((k : ℝ) * x)| =
          |2 * Real.sin (x / 2) *
            (∑ k ∈ Finset.Icc 1 n, Real.sin ((k : ℝ) * x))| := by
        rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      _ = |Real.cos (x / 2) - Real.cos (((n : ℝ) + 1 / 2) * x)| := by
        rw [sine_sum_identity]
      _ ≤ |Real.cos (x / 2)| + |Real.cos (((n : ℝ) + 1 / 2) * x)| := abs_sub _ _
      _ ≤ 1 + 1 := add_le_add (hcos _) (hcos _)
      _ = 2 := by norm_num
  have hsum :
      |∑ k ∈ Finset.Icc 1 n, Real.sin ((k : ℝ) * x)| ≤
        1 / |Real.sin (x / 2)| := by
    apply (le_div_iff₀ hsin_pos).2
    nlinarith
  exact mul_le_mul_of_nonneg_left (by simpa [one_div] using hsum) (abs_nonneg _)

theorem gap4 (x : ℝ) (hx : Real.sin (x / 2) ≠ 0) :
    |Real.sin x| / |Real.sin (x / 2)| =
      2 * |Real.cos (x / 2)| := by
  have hsin : Real.sin x = 2 * Real.sin (x / 2) * Real.cos (x / 2) := by
    nth_rewrite 1 [show x = 2 * (x / 2) by ring]
    rw [Real.sin_two_mul]
  rw [hsin, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  field_simp [abs_ne_zero.mpr hx]

theorem gap5 (x : ℝ) :
    2 * |Real.cos (x / 2)| ≤ 2 := by
  have hcos : |Real.cos (x / 2)| ≤ 1 := (abs_le).2 (Real.cos_mem_Icc _)
  nlinarith

theorem gap6 (n : ℕ) (x : ℝ) :
    |∑ k ∈ Finset.Icc 1 n, coefficient k x| ≤ 2 := by
  by_cases hx : Real.sin (x / 2) = 0
  · have hsin : Real.sin x = 0 := by
      nth_rewrite 1 [show x = 2 * (x / 2) by ring]
      rw [Real.sin_two_mul, hx]
      ring
    simp [coefficient, hsin]
  · calc
      |∑ k ∈ Finset.Icc 1 n, coefficient k x| =
          |Real.sin x| * |∑ k ∈ Finset.Icc 1 n, Real.sin ((k : ℝ) * x)| := gap2 n x
      _ ≤ |Real.sin x| / |Real.sin (x / 2)| := gap3 n x hx
      _ = 2 * |Real.cos (x / 2)| := gap4 x hx
      _ ≤ 2 := gap5 x

theorem gap7 (n : ℕ) (x : ℝ) (hx : x ∈ Set.Ici (0 : ℝ)) :
    |∑ k ∈ Finset.Icc 1 n, coefficient k x| ≤ 2 := by
  exact gap6 n x

theorem gap8 (n : ℕ) (x : ℝ) (hn : 1 ≤ n) (hx : 0 ≤ x) :
    weight n x > weight (n + 1) x := by
  have hn_pos : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hrad_pos : 0 < (n : ℝ) + x := by nlinarith
  have hrad_lt : (n : ℝ) + x < ((n + 1 : ℕ) : ℝ) + x := by
    push_cast
    linarith
  unfold weight
  exact one_div_lt_one_div_of_lt (Real.sqrt_pos.2 hrad_pos)
    (Real.sqrt_lt_sqrt hrad_pos.le hrad_lt)

theorem gap9 (n : ℕ) (x : ℝ) (hn : 1 ≤ n) (hx : 0 ≤ x) :
    weight n x ≤ 1 / Real.sqrt n := by
  have hn_pos : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hsqrt_le : Real.sqrt (n : ℝ) ≤ Real.sqrt ((n : ℝ) + x) :=
    Real.sqrt_le_sqrt (by linarith)
  unfold weight
  exact one_div_le_one_div_of_le (Real.sqrt_pos.2 hn_pos) hsqrt_le

private theorem inv_sqrt_nat_tendsto_zero :
    Tendsto (fun n : ℕ => 1 / Real.sqrt (n : ℝ)) atTop (nhds 0) := by
  have hsqrt : Tendsto (fun n : ℕ => Real.sqrt (n : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  simpa [one_div] using tendsto_inv_atTop_zero.comp hsqrt

theorem gap10 (x : ℝ) (hx : 0 ≤ x) :
    Tendsto (fun n : ℕ => weight n x) atTop (nhds 0) := by
  rw [← Filter.tendsto_add_atTop_iff_nat 1]
  refine squeeze_zero (g := fun n : ℕ => 1 / Real.sqrt ((n + 1 : ℕ) : ℝ))
    (fun n => by unfold weight; positivity) (fun n => ?_) ?_
  · exact gap9 (n + 1) x (by omega) hx
  · simpa only [Function.comp_apply] using
      inv_sqrt_nat_tendsto_zero.comp (tendsto_add_atTop_nat 1)

private theorem coefficient_prefix_bound (n : ℕ) (x : ℝ) :
    |∑ i ∈ Finset.range n, coefficient (i + 1) x| ≤ 2 := by
  have h := gap6 n x
  rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range] at h
  simpa [Nat.add_comm] using h

private theorem coefficient_shift_sum_bound (N n : ℕ) (x : ℝ) :
    |∑ i ∈ Finset.range n, coefficient (N + 1 + i) x| ≤ 4 := by
  have hadd := Finset.sum_range_add (f := fun i => coefficient (i + 1) x) N n
  have heq :
      (∑ i ∈ Finset.range n, coefficient (N + 1 + i) x) =
        (∑ i ∈ Finset.range (N + n), coefficient (i + 1) x) -
          ∑ i ∈ Finset.range N, coefficient (i + 1) x := by
    rw [hadd]
    simp only [add_sub_cancel_left]
    apply Finset.sum_congr rfl
    intro i hi
    congr 1
    omega
  rw [heq]
  calc
    |(∑ i ∈ Finset.range (N + n), coefficient (i + 1) x) -
        ∑ i ∈ Finset.range N, coefficient (i + 1) x| ≤
        |∑ i ∈ Finset.range (N + n), coefficient (i + 1) x| +
          |∑ i ∈ Finset.range N, coefficient (i + 1) x| := abs_sub _ _
    _ ≤ 2 + 2 := add_le_add (coefficient_prefix_bound _ _) (coefficient_prefix_bound _ _)
    _ = 4 := by norm_num

private theorem weight_nonneg (n : ℕ) (x : ℝ) : 0 ≤ weight n x := by
  unfold weight
  positivity

private theorem weight_shift_antitone (N : ℕ) (x : ℝ) (hx : 0 ≤ x) :
    Antitone (fun i => weight (N + 1 + i) x) := by
  refine antitone_nat_of_succ_le (fun i => ?_)
  have h := (gap8 (N + 1 + i) x (by omega) hx).le
  simpa [Nat.add_assoc] using h

private theorem weight_shift_tendsto_zero (N : ℕ) (x : ℝ) (hx : 0 ≤ x) :
    Tendsto (fun i => weight (N + 1 + i) x) atTop (nhds 0) := by
  have h := (gap10 x hx).comp (tendsto_add_atTop_nat (N + 1))
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

private theorem term_tail_bound (N m : ℕ) (x : ℝ) (hx : 0 ≤ x) :
    |∑ i ∈ Finset.range m, term (N + 1 + i) x| ≤ 4 * weight (N + 1) x := by
  have h := dirichlet_sum_bound
    (fun i => weight (N + 1 + i) x)
    (fun i => coefficient (N + 1 + i) x) 4
    (fun i => weight_nonneg _ _)
    (weight_shift_antitone N x hx)
    (fun n => coefficient_shift_sum_bound N n x) m
  simpa [term, mul_comm] using h

private theorem hasSum_conditional_iff_tendsto_range (f : ℕ → ℝ) (s : ℝ) :
    HasSum f s (SummationFilter.conditional ℕ) ↔
      Tendsto (fun n => ∑ i ∈ Finset.range n, f i) atTop (nhds s) := by
  simp only [HasSum, SummationFilter.conditional_filter_eq_map_range, tendsto_map'_iff]
  rfl

private theorem conditional_series_data (x : ℝ) (hx : 0 ≤ x) :
    ∃ s : ℝ, HasSum (fun n => term (n + 1) x) s (SummationFilter.conditional ℕ) := by
  have hanti : Antitone (fun i => weight (1 + i) x) := by
    simpa only [zero_add] using weight_shift_antitone 0 x hx
  have htend : Tendsto (fun i => weight (1 + i) x) atTop (nhds 0) := by
    simpa only [zero_add] using weight_shift_tendsto_zero 0 x hx
  have hbound : ∀ n, ‖∑ i ∈ Finset.range n, coefficient (1 + i) x‖ ≤ (2 : ℝ) := by
    intro n
    simpa [Nat.add_comm] using coefficient_prefix_bound n x
  have hc0 : CauchySeq
      (fun n => ∑ i ∈ Finset.range n, weight (1 + i) x • coefficient (1 + i) x) :=
    hanti.cauchySeq_series_mul_of_tendsto_zero_of_bounded htend hbound
  have hc : CauchySeq (fun n => ∑ i ∈ Finset.range n, term (i + 1) x) := by
    simpa [term, smul_eq_mul, mul_comm, Nat.add_comm] using hc0
  obtain ⟨s, hs⟩ := cauchySeq_tendsto_of_complete hc
  exact ⟨s, (hasSum_conditional_iff_tendsto_range _ _).2 hs⟩

private theorem term_remainder_bound (x s : ℝ) (hx : 0 ≤ x)
    (hs : HasSum (fun n => term (n + 1) x) s (SummationFilter.conditional ℕ)) (n : ℕ) :
    |(∑ i ∈ Finset.range (n + 1), term (i + 1) x) - s| ≤ 4 * weight (n + 2) x := by
  have hseries := (hasSum_conditional_iff_tendsto_range _ _).1 hs
  have htotal : Tendsto (fun m => ∑ i ∈ Finset.range (n + 1 + m), term (i + 1) x)
      atTop (nhds s) := by
    simpa [Nat.add_comm] using hseries.comp (tendsto_add_atTop_nat (n + 1))
  have hlim :
      Tendsto
        (fun m => |(∑ i ∈ Finset.range (n + 1), term (i + 1) x) -
          ∑ i ∈ Finset.range (n + 1 + m), term (i + 1) x|)
        atTop (nhds |(∑ i ∈ Finset.range (n + 1), term (i + 1) x) - s|) := by
    exact (tendsto_const_nhds.sub htotal).abs
  apply le_of_tendsto' hlim
  intro m
  have htail := term_tail_bound (n + 1) m x hx
  have hsplit :
      (∑ i ∈ Finset.range (n + 1 + m), term (i + 1) x) =
        (∑ i ∈ Finset.range (n + 1), term (i + 1) x) +
          ∑ i ∈ Finset.range m, term (n + 1 + i + 1) x := by
    simpa using Finset.sum_range_add (f := fun i => term (i + 1) x) (n + 1) m
  rw [hsplit]
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htail

private theorem four_div_sqrt_tendsto_zero :
    Tendsto (fun n : ℕ => 4 / Real.sqrt (n : ℝ)) atTop (nhds 0) := by
  simpa [div_eq_mul_inv, one_div] using
    (tendsto_const_nhds.mul inv_sqrt_nat_tendsto_zero :
      Tendsto (fun n : ℕ => (4 : ℝ) * (1 / Real.sqrt (n : ℝ))) atTop (nhds (4 * 0)))

theorem gap11 :
    SeriesUniformlyConvergesOn
      (fun n x => term (n + 1) x)
      (Set.Ici (0 : ℝ))
      (fun x => ∑'[SummationFilter.conditional ℕ] n : ℕ, term (n + 1) x) := by
  intro ε hε
  have hmajorant :
      Tendsto (fun n : ℕ => 4 / Real.sqrt ((n + 2 : ℕ) : ℝ)) atTop (nhds 0) := by
    simpa only [Function.comp_apply] using
      four_div_sqrt_tendsto_zero.comp (tendsto_add_atTop_nat 2)
  have hevent : ∀ᶠ n : ℕ in atTop, 4 / Real.sqrt ((n + 2 : ℕ) : ℝ) < ε :=
    (tendsto_order.1 hmajorant).2 ε hε
  obtain ⟨N, hN⟩ := eventually_atTop.1 hevent
  refine ⟨N, fun n hn x hx => ?_⟩
  obtain ⟨s, hs⟩ := conditional_series_data x hx
  have htsum : (∑'[SummationFilter.conditional ℕ] i : ℕ, term (i + 1) x) = s := hs.tsum_eq
  change |(∑ k ∈ Finset.range (n + 1), term (k + 1) x) -
    (∑'[SummationFilter.conditional ℕ] i : ℕ, term (i + 1) x)| < ε
  rw [htsum]
  refine lt_of_le_of_lt (term_remainder_bound x s hx hs n) ?_
  have hw := gap9 (n + 2) x (by omega) hx
  calc
    4 * weight (n + 2) x ≤ 4 * (1 / Real.sqrt ((n + 2 : ℕ) : ℝ)) := by gcongr
    _ = 4 / Real.sqrt ((n + 2 : ℕ) : ℝ) := by ring
    _ < ε := hN n hn

theorem gap12 :
    SeriesUniformlyConvergesOn
      (fun n x => term (n + 1) x)
      (Set.Ici (0 : ℝ))
      (fun x => ∑'[SummationFilter.conditional ℕ] n : ℕ, term (n + 1) x) := by
  exact gap11

end

end ProofGap.Exercise2781
