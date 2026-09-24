import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.PSeries
import Mathlib.Topology.Algebra.InfiniteSum.Basic

namespace ProofGap.Exercise2670

noncomputable section

open Filter

def sign (n : ℕ) : ℝ :=
  (-1 : ℝ) ^ n

def term (n : ℕ) : ℝ :=
  sign n / (Real.sqrt n + sign n)

def alternatingPart (n : ℕ) : ℝ :=
  sign n / Real.sqrt n

def harmonicPart (n : ℕ) : ℝ :=
  1 / n

def comparison (n : ℕ) : ℝ :=
  1 / Real.rpow n (3 / 2 : ℝ)

theorem gap1 :
    ∀ n : ℕ, 2 ≤ n →
      term n =
        alternatingPart n * (1 / (1 + sign n / Real.sqrt n)) := by
  intro n hn
  have hn0 : (0 : ℝ) < n := by
    exact_mod_cast lt_of_lt_of_le (by norm_num : 0 < 2) hn
  have hsqrt : Real.sqrt (n : ℝ) ≠ 0 := (Real.sqrt_pos.2 hn0).ne'
  rw [term, alternatingPart]
  field_simp

theorem gap2 :
    Asymptotics.IsBigO atTop
      (fun n : ℕ =>
        1 / (1 + sign (n + 2) / Real.sqrt (n + 2)) -
          (1 - sign (n + 2) / Real.sqrt (n + 2)))
      (fun n : ℕ => 1 / (n + 2 : ℝ)) := by
  apply Asymptotics.IsBigO.of_bound 4
  filter_upwards [] with n
  let m : ℕ := n + 2
  have hm_nat : 2 ≤ m := by omega
  have hm : (2 : ℝ) ≤ m := by exact_mod_cast hm_nat
  have hm0 : (0 : ℝ) < m := lt_of_lt_of_le (by norm_num) hm
  have hsqrt0 : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos.2 hm0
  have hsqrt_sq : Real.sqrt (m : ℝ) ^ 2 = m := Real.sq_sqrt (by positivity)
  have hsqrt_lower : (4 / 3 : ℝ) ≤ Real.sqrt (m : ℝ) := by
    nlinarith [sq_nonneg (Real.sqrt (m : ℝ) - 4 / 3)]
  have hinv : 1 / Real.sqrt (m : ℝ) ≤ (3 / 4 : ℝ) := by
    calc
      1 / Real.sqrt (m : ℝ) ≤ 1 / (4 / 3 : ℝ) :=
        one_div_le_one_div_of_le (by norm_num) hsqrt_lower
      _ = 3 / 4 := by norm_num
  have hsign_abs : |sign m| = 1 := by simp [sign]
  have hx_abs : |sign m / Real.sqrt (m : ℝ)| ≤ (3 / 4 : ℝ) := by
    rw [abs_div, hsign_abs, abs_of_pos hsqrt0]
    simpa using hinv
  have hden : (1 / 4 : ℝ) ≤ 1 + sign m / Real.sqrt (m : ℝ) := by
    have := neg_abs_le (sign m / Real.sqrt (m : ℝ))
    nlinarith
  have hden0 : 0 < 1 + sign m / Real.sqrt (m : ℝ) :=
    lt_of_lt_of_le (by norm_num) hden
  have hsum0 : Real.sqrt (m : ℝ) + sign m ≠ 0 := by
    intro hsum
    apply hden0.ne'
    field_simp [hsqrt0.ne']
    simpa using hsum
  have hsign_sq : sign m ^ 2 = (1 : ℝ) := by
    calc
      sign m ^ 2 = |sign m ^ 2| := (abs_of_nonneg (sq_nonneg _)).symm
      _ = |sign m| ^ 2 := by rw [abs_pow]
      _ = 1 := by rw [hsign_abs]; norm_num
  have hx_sq : (sign m / Real.sqrt (m : ℝ)) ^ 2 = 1 / (m : ℝ) := by
    rw [div_pow, hsign_sq, hsqrt_sq]
  have hid :
      1 / (1 + sign m / Real.sqrt (m : ℝ)) -
          (1 - sign m / Real.sqrt (m : ℝ)) =
        (sign m / Real.sqrt (m : ℝ)) ^ 2 /
          (1 + sign m / Real.sqrt (m : ℝ)) := by
    field_simp [hsqrt0.ne', hsum0]
    ring
  have hden_inv : 1 / (1 + sign m / Real.sqrt (m : ℝ)) ≤ 4 := by
    calc
      1 / (1 + sign m / Real.sqrt (m : ℝ)) ≤ 1 / (1 / 4 : ℝ) :=
        one_div_le_one_div_of_le (by norm_num) hden
      _ = 4 := by norm_num
  have hbound :
      |1 / (1 + sign m / Real.sqrt (m : ℝ)) -
          (1 - sign m / Real.sqrt (m : ℝ))| ≤
        4 * |1 / (m : ℝ)| := by
    rw [hid, abs_div, abs_of_nonneg (sq_nonneg _), hx_sq,
      abs_of_pos hden0, abs_of_pos (by positivity : (0 : ℝ) < 1 / (m : ℝ))]
    calc
      (1 / (m : ℝ)) / (1 + sign m / Real.sqrt (m : ℝ)) =
          (1 / (m : ℝ)) * (1 / (1 + sign m / Real.sqrt (m : ℝ))) := by ring
      _ ≤ (1 / (m : ℝ)) * 4 :=
        mul_le_mul_of_nonneg_left hden_inv (by positivity)
      _ = 4 * (1 / (m : ℝ)) := by ring
  simpa [m, Real.norm_eq_abs] using hbound

theorem gap3 :
    Asymptotics.IsBigO atTop
      (fun n : ℕ =>
        alternatingPart (n + 2) *
            (1 / (1 + sign (n + 2) / Real.sqrt (n + 2))) -
          (alternatingPart (n + 2) - harmonicPart (n + 2)))
      (fun n : ℕ => comparison (n + 2)) := by
  have hAlt : Asymptotics.IsBigO atTop
      (fun n : ℕ => alternatingPart (n + 2))
      (fun n : ℕ => 1 / Real.sqrt (n + 2)) := by
    apply Asymptotics.IsBigO.of_bound 1
    filter_upwards [] with n
    simp [alternatingPart, sign, Real.norm_eq_abs]
  have hprod := hAlt.mul gap2
  have hleft : ∀ n : ℕ,
      alternatingPart (n + 2) *
          (1 / (1 + sign (n + 2) / Real.sqrt (n + 2)) -
            (1 - sign (n + 2) / Real.sqrt (n + 2))) =
        alternatingPart (n + 2) *
            (1 / (1 + sign (n + 2) / Real.sqrt (n + 2))) -
          (alternatingPart (n + 2) - harmonicPart (n + 2)) := by
    intro n
    let m : ℕ := n + 2
    have hsqrt_sq : Real.sqrt (m : ℝ) ^ 2 = m := Real.sq_sqrt (by positivity)
    have hsign_abs : |sign m| = 1 := by simp [sign]
    have hsign_sq : sign m ^ 2 = (1 : ℝ) := by
      calc
        sign m ^ 2 = |sign m ^ 2| := (abs_of_nonneg (sq_nonneg _)).symm
        _ = |sign m| ^ 2 := by rw [abs_pow]
        _ = 1 := by rw [hsign_abs]; norm_num
    have hax :
        alternatingPart m * (sign m / Real.sqrt (m : ℝ)) = harmonicPart m := by
      unfold alternatingPart harmonicPart
      calc
        (sign m / Real.sqrt (m : ℝ)) * (sign m / Real.sqrt (m : ℝ)) =
            sign m ^ 2 / Real.sqrt (m : ℝ) ^ 2 := by ring
        _ = 1 / (m : ℝ) := by rw [hsign_sq, hsqrt_sq]
    have hcalc :
        alternatingPart m *
            (1 / (1 + sign m / Real.sqrt (m : ℝ)) -
              (1 - sign m / Real.sqrt (m : ℝ))) =
          alternatingPart m * (1 / (1 + sign m / Real.sqrt (m : ℝ))) -
            (alternatingPart m - harmonicPart m) := by
      calc
        alternatingPart m *
            (1 / (1 + sign m / Real.sqrt (m : ℝ)) -
              (1 - sign m / Real.sqrt (m : ℝ))) =
          alternatingPart m * (1 / (1 + sign m / Real.sqrt (m : ℝ))) -
            (alternatingPart m -
              alternatingPart m * (sign m / Real.sqrt (m : ℝ))) := by ring
        _ = alternatingPart m * (1 / (1 + sign m / Real.sqrt (m : ℝ))) -
            (alternatingPart m - harmonicPart m) := by rw [hax]
    simpa [m] using hcalc
  have hright : ∀ n : ℕ,
      (1 / Real.sqrt (n + 2)) * (1 / (n + 2 : ℝ)) = comparison (n + 2) := by
    intro n
    let m : ℕ := n + 2
    have hm0 : (0 : ℝ) < m := by positivity
    have hsqrt0 : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos.2 hm0
    have hrpow : Real.rpow (m : ℝ) (3 / 2 : ℝ) =
        Real.sqrt (m : ℝ) * (m : ℝ) := by
      calc
        Real.rpow (m : ℝ) (3 / 2 : ℝ) =
            Real.rpow (m : ℝ) (1 / 2 + 1 : ℝ) :=
          congrArg (Real.rpow (m : ℝ)) (by ring)
        _ = Real.rpow (m : ℝ) (1 / 2 : ℝ) * Real.rpow (m : ℝ) 1 := by
          exact Real.rpow_add hm0 (1 / 2 : ℝ) 1
        _ = Real.sqrt (m : ℝ) * Real.rpow (m : ℝ) 1 :=
          congrArg (fun x : ℝ => x * Real.rpow (m : ℝ) 1)
            (Real.sqrt_eq_rpow (m : ℝ)).symm
        _ = Real.sqrt (m : ℝ) * (m : ℝ) :=
          congrArg (fun x : ℝ => Real.sqrt (m : ℝ) * x) (Real.rpow_one (m : ℝ))
    have hcalc :
        (1 / Real.sqrt (m : ℝ)) * (1 / (m : ℝ)) = comparison m := by
      unfold comparison
      rw [hrpow]
      field_simp [hsqrt0.ne', hm0.ne']
    simpa [m] using hcalc
  exact hprod.congr hleft hright

theorem gap4 :
    Asymptotics.IsBigO atTop
      (fun n : ℕ =>
        term (n + 2) -
          (alternatingPart (n + 2) - harmonicPart (n + 2)))
      (fun n : ℕ => comparison (n + 2)) := by
  refine gap3.congr (fun n => ?_) (fun _ => rfl)
  rw [gap1 (n + 2) (by omega)]
  norm_num [Nat.cast_add]

theorem gap5 :
    ProofGap.SeriesConverges (fun n : ℕ => alternatingPart (n + 2)) := by
  let f : ℕ → ℝ := fun n => 1 / Real.sqrt (n + 2 : ℕ)
  have hfanti : Antitone f := by
    intro a b hab
    have hpos : 0 < Real.sqrt ((a + 2 : ℕ) : ℝ) := Real.sqrt_pos.2 (by positivity)
    have hle : Real.sqrt ((a + 2 : ℕ) : ℝ) ≤
        Real.sqrt ((b + 2 : ℕ) : ℝ) := by
      apply Real.sqrt_le_sqrt
      exact_mod_cast Nat.add_le_add_right hab 2
    exact one_div_le_one_div_of_le hpos hle
  have hnat : Tendsto (fun n : ℕ => n + 2) atTop atTop :=
    (tendsto_add_atTop_iff_nat 2).2 tendsto_id
  have hreal : Tendsto (fun n : ℕ => ((n + 2 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hnat
  have hsqrt : Tendsto (fun n : ℕ => Real.sqrt ((n + 2 : ℕ) : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp hreal
  have hfzero : Tendsto f atTop (nhds 0) := by
    simpa [f, one_div] using tendsto_inv_atTop_zero.comp hsqrt
  obtain ⟨l, hl⟩ := hfanti.tendsto_alternating_series_of_tendsto_zero hfzero
  rw [ProofGap.SeriesConverges]
  use l
  rw [HasSum, SummationFilter.conditional_filter_eq_map_range, tendsto_map'_iff]
  simpa [Function.comp_def, f, alternatingPart, sign, pow_add, div_eq_mul_inv] using hl

theorem gap6 :
    Summable (fun n : ℕ => comparison (n + 2)) := by
  rw [summable_nat_add_iff 2]
  unfold comparison
  exact Real.summable_one_div_nat_rpow.mpr (by norm_num)

theorem gap7 :
    ¬ Summable (fun n : ℕ => harmonicPart (n + 2)) := by
  rw [summable_nat_add_iff 2]
  unfold harmonicPart
  exact Real.not_summable_one_div_natCast

private theorem summable_conditional_of_summable {f : ℕ → ℝ} (hf : Summable f) :
    Summable f (SummationFilter.conditional ℕ) := by
  use ∑' n, f n
  have hsum := hf.hasSum
  unfold HasSum at hsum ⊢
  exact hsum.mono_left SummationFilter.le_atTop

private theorem term_not_series_convergent :
    ¬ ProofGap.SeriesConverges (fun n : ℕ => term (n + 2)) := by
  intro hterm
  rw [ProofGap.SeriesConverges] at hterm
  have hrem_unconditional :
      Summable (fun n : ℕ =>
        term (n + 2) -
          (alternatingPart (n + 2) - harmonicPart (n + 2))) := by
    apply summable_of_isBigO gap6
    simpa only [Nat.cofinite_eq_atTop] using gap4
  have hrem := summable_conditional_of_summable hrem_unconditional
  have halt := gap5
  rw [ProofGap.SeriesConverges] at halt
  have hbase :
      Summable (fun n : ℕ => alternatingPart (n + 2) - harmonicPart (n + 2))
        (SummationFilter.conditional ℕ) := by
    apply (hterm.sub hrem).congr
    intro n
    ring
  have hharm :
      Summable (fun n : ℕ => harmonicPart (n + 2))
        (SummationFilter.conditional ℕ) := by
    apply (halt.sub hbase).congr
    intro n
    ring
  have hfin := hharm.hasSum
  unfold HasSum at hfin
  rw [SummationFilter.conditional_filter_eq_map_range, tendsto_map'_iff] at hfin
  have hfin' :
      Tendsto (fun n => ∑ i ∈ Finset.range n, harmonicPart (i + 2)) atTop
        (nhds (∑'[SummationFilter.conditional ℕ] n, harmonicPart (n + 2))) := by
    simpa only [Function.comp_apply] using hfin
  have hdiv :
      Tendsto (fun n => ∑ i ∈ Finset.range n, harmonicPart (i + 2)) atTop atTop :=
    (not_summable_iff_tendsto_nat_atTop_of_nonneg (fun n => by
      unfold harmonicPart
      positivity)).mp gap7
  have hlt : ∀ᶠ n in atTop,
      (∑ i ∈ Finset.range n, harmonicPart (i + 2)) <
        (∑'[SummationFilter.conditional ℕ] n, harmonicPart (n + 2)) + 1 :=
    hfin'.eventually (Iio_mem_nhds (lt_add_one _))
  have hge : ∀ᶠ n in atTop,
      (∑'[SummationFilter.conditional ℕ] n, harmonicPart (n + 2)) + 1 ≤
        ∑ i ∈ Finset.range n, harmonicPart (i + 2) :=
    hdiv.eventually (eventually_ge_atTop _)
  obtain ⟨n, hnlt, hnge⟩ := (hlt.and hge).exists
  exact (not_lt_of_ge hnge) hnlt

theorem gap8 :
    ¬ Summable (fun n : ℕ => term (n + 2)) := by
  intro hterm
  apply term_not_series_convergent
  rw [ProofGap.SeriesConverges]
  exact summable_conditional_of_summable hterm

end

end ProofGap.Exercise2670
