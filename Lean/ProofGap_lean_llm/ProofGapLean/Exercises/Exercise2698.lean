import ProofGapLean.Prelude.Analysis
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

namespace ProofGap.Exercise2698

noncomputable section

open Filter
open scoped BigOperators

def weight (p : ℝ) (n : ℕ) : ℝ :=
  1 / Real.rpow (n + 1) p

def cosineTerm (p x : ℝ) (n : ℕ) : ℝ :=
  Real.cos (((n + 1 : ℕ) : ℝ) * x) * weight p n

def sineTerm (p x : ℝ) (n : ℕ) : ℝ :=
  Real.sin (((n + 1 : ℕ) : ℝ) * x) * weight p n

def cosinePartial (x : ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.range N, Real.cos (((n + 1 : ℕ) : ℝ) * x)

def sinePartial (x : ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.range N, Real.sin (((n + 1 : ℕ) : ℝ) * x)

def ConditionallySummable (f : ℕ → ℝ) : Prop :=
  ProofGap.SeriesConverges f ∧ ¬ Summable (fun n => |f n|)

private lemma weight_pos (p : ℝ) (n : ℕ) : 0 < weight p n := by
  unfold weight
  exact one_div_pos.mpr (Real.rpow_pos_of_pos (by positivity) p)

private lemma exp_I_ne_one_of_pos_of_lt_two_pi (x : ℝ) (hx₀ : 0 < x)
    (hx₂π : x < 2 * Real.pi) :
    Complex.exp (Complex.I * (x : ℂ)) ≠ 1 := by
  apply sub_ne_zero.mp
  rw [← norm_ne_zero_iff, Complex.norm_exp_I_mul_ofReal_sub_one]
  apply norm_ne_zero_iff.mpr
  exact mul_ne_zero (by norm_num)
    (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)).ne'

private lemma exp_I_pow_re (x : ℝ) (n : ℕ) :
    (Complex.exp (Complex.I * (x : ℂ)) ^ n).re = Real.cos ((n : ℝ) * x) := by
  rw [← Complex.exp_nat_mul]
  convert Complex.exp_ofReal_mul_I_re ((n : ℝ) * x) using 2 <;>
    push_cast <;> ring

private lemma exp_I_pow_im (x : ℝ) (n : ℕ) :
    (Complex.exp (Complex.I * (x : ℂ)) ^ n).im = Real.sin ((n : ℝ) * x) := by
  rw [← Complex.exp_nat_mul]
  convert Complex.exp_ofReal_mul_I_im ((n : ℝ) * x) using 2 <;>
    push_cast <;> ring

private lemma complex_geometric_partial_bound (q : ℂ) (hqnorm : ‖q‖ = 1)
    (hq : q ≠ 1) :
    ∀ N : ℕ, ‖∑ n ∈ Finset.range N, q ^ (n + 1)‖ ≤ 2 / ‖q - 1‖ := by
  intro N
  have hsum : (∑ n ∈ Finset.range N, q ^ (n + 1)) =
      q * ∑ n ∈ Finset.range N, q ^ n := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    exact pow_succ' q n
  rw [hsum, norm_mul, hqnorm, one_mul, geom_sum_eq hq, norm_div]
  have hden : 0 < ‖q - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hq)
  apply (div_le_div_iff_of_pos_right hden).2
  calc
    ‖q ^ N - 1‖ ≤ ‖q ^ N‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
    _ = 2 := by rw [norm_pow, hqnorm]; norm_num

private lemma cosine_partial_bound (x : ℝ) (hx₀ : 0 < x)
    (hx₂π : x < 2 * Real.pi) :
    ∃ C : ℝ, ∀ N : ℕ,
      |∑ n ∈ Finset.range N, Real.cos (((n + 1 : ℕ) : ℝ) * x)| ≤ C := by
  let q : ℂ := Complex.exp (Complex.I * (x : ℂ))
  have hqnorm : ‖q‖ = 1 := by
    simpa [q] using Complex.norm_exp_I_mul_ofReal x
  have hq : q ≠ 1 := by
    simpa [q] using exp_I_ne_one_of_pos_of_lt_two_pi x hx₀ hx₂π
  refine ⟨2 / ‖q - 1‖, fun N => ?_⟩
  calc
    |∑ n ∈ Finset.range N, Real.cos (((n + 1 : ℕ) : ℝ) * x)| =
        |(∑ n ∈ Finset.range N, q ^ (n + 1)).re| := by
          congr 1
          rw [Complex.re_sum]
          apply Finset.sum_congr rfl
          intro n hn
          simpa [q] using (exp_I_pow_re x (n + 1)).symm
    _ ≤ ‖∑ n ∈ Finset.range N, q ^ (n + 1)‖ := Complex.abs_re_le_norm _
    _ ≤ 2 / ‖q - 1‖ := complex_geometric_partial_bound q hqnorm hq N

private lemma sine_partial_bound (x : ℝ) (hx₀ : 0 < x)
    (hx₂π : x < 2 * Real.pi) :
    ∃ C : ℝ, ∀ N : ℕ,
      |∑ n ∈ Finset.range N, Real.sin (((n + 1 : ℕ) : ℝ) * x)| ≤ C := by
  let q : ℂ := Complex.exp (Complex.I * (x : ℂ))
  have hqnorm : ‖q‖ = 1 := by
    simpa [q] using Complex.norm_exp_I_mul_ofReal x
  have hq : q ≠ 1 := by
    simpa [q] using exp_I_ne_one_of_pos_of_lt_two_pi x hx₀ hx₂π
  refine ⟨2 / ‖q - 1‖, fun N => ?_⟩
  calc
    |∑ n ∈ Finset.range N, Real.sin (((n + 1 : ℕ) : ℝ) * x)| =
        |(∑ n ∈ Finset.range N, q ^ (n + 1)).im| := by
          congr 1
          rw [Complex.im_sum]
          apply Finset.sum_congr rfl
          intro n hn
          simpa [q] using (exp_I_pow_im x (n + 1)).symm
    _ ≤ ‖∑ n ∈ Finset.range N, q ^ (n + 1)‖ := Complex.abs_im_le_norm _
    _ ≤ 2 / ‖q - 1‖ := complex_geometric_partial_bound q hqnorm hq N

private lemma seriesConverges_iff_tendsto_sum_range (f : ℕ → ℝ) :
    ProofGap.SeriesConverges f ↔
      ∃ a : ℝ, Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, f n) atTop (nhds a) := by
  simp only [ProofGap.SeriesConverges, Summable, HasSum,
    SummationFilter.conditional_filter_eq_map_range, tendsto_map'_iff]
  simp [Function.comp_def]

private lemma seriesConverges_of_cauchySeq (f : ℕ → ℝ)
    (hf : CauchySeq (fun N : ℕ => ∑ n ∈ Finset.range N, f n)) :
    ProofGap.SeriesConverges f := by
  rw [seriesConverges_iff_tendsto_sum_range]
  exact cauchySeq_tendsto_of_complete hf

private lemma tendsto_zero_of_seriesConverges (f : ℕ → ℝ)
    (hf : ProofGap.SeriesConverges f) : Tendsto f atTop (nhds 0) := by
  rcases (seriesConverges_iff_tendsto_sum_range f).mp hf with ⟨a, ha⟩
  have ha' := (tendsto_add_atTop_iff_nat 1).mpr ha
  have hd := ha'.sub ha
  simpa [Finset.sum_range_succ] using hd

private lemma one_le_weight_of_nonpos (p : ℝ) (hp : p ≤ 0) (n : ℕ) :
    1 ≤ weight p n := by
  have hb : 1 ≤ (n : ℝ) + 1 := by
    have hn : 0 ≤ (n : ℝ) := by positivity
    linarith
  have hd : ((n : ℝ) + 1) ^ p ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hb hp
  have hdpos : 0 < ((n : ℝ) + 1) ^ p :=
    Real.rpow_pos_of_pos (by positivity) p
  unfold weight
  change 1 ≤ 1 / (((n : ℝ) + 1) ^ p)
  exact (one_le_div₀ hdpos).mpr hd

private lemma not_tendsto_cos_nat_add_one_zero (x : ℝ) (hx₀ : 0 < x)
    (hxπ : x < Real.pi) :
    ¬ Tendsto (fun n : ℕ => Real.cos (((n + 1 : ℕ) : ℝ) * x)) atTop (nhds 0) := by
  intro hc
  let c : ℕ → ℝ := fun n => Real.cos (((n + 1 : ℕ) : ℝ) * x)
  let s : ℕ → ℝ := fun n => Real.sin (((n + 1 : ℕ) : ℝ) * x)
  have hc' : Tendsto c atTop (nhds 0) := by simpa [c] using hc
  have hcshift := (tendsto_add_atTop_iff_nat 1).mpr hc'
  have hsinmul : Tendsto (fun n : ℕ => s n * Real.sin x) atTop (nhds 0) := by
    have h := (hc'.mul_const (Real.cos x)).sub hcshift
    convert h using 1
    · funext n
      dsimp [c, s]
      rw [show (((n + 1 + 1 : ℕ) : ℝ) * x) =
          (((n + 1 : ℕ) : ℝ) * x + x) by push_cast; ring, Real.cos_add]
      ring
    · ring
  have hsinx : Real.sin x ≠ 0 := (Real.sin_pos_of_pos_of_lt_pi hx₀ hxπ).ne'
  have hs : Tendsto s atTop (nhds 0) := by
    have h := hsinmul.div_const (Real.sin x)
    convert h using 1
    · funext n
      field_simp [hsinx]
    · simp
  have hsq := (hc'.pow 2).add (hs.pow 2)
  have hbad : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 0) := by
    convert hsq using 1
    · funext n
      simpa [c, s] using (Real.cos_sq_add_sin_sq (((n + 1 : ℕ) : ℝ) * x)).symm
    · norm_num
  have h10 : (1 : ℝ) = 0 := tendsto_nhds_unique tendsto_const_nhds hbad
  norm_num at h10

private lemma not_tendsto_sin_nat_add_one_zero (x : ℝ) (hx₀ : 0 < x)
    (hxπ : x < Real.pi) :
    ¬ Tendsto (fun n : ℕ => Real.sin (((n + 1 : ℕ) : ℝ) * x)) atTop (nhds 0) := by
  intro hs
  let c : ℕ → ℝ := fun n => Real.cos (((n + 1 : ℕ) : ℝ) * x)
  let s : ℕ → ℝ := fun n => Real.sin (((n + 1 : ℕ) : ℝ) * x)
  have hs' : Tendsto s atTop (nhds 0) := by simpa [s] using hs
  have hsshift := (tendsto_add_atTop_iff_nat 1).mpr hs'
  have hcosmul : Tendsto (fun n : ℕ => c n * Real.sin x) atTop (nhds 0) := by
    have h := hsshift.sub (hs'.mul_const (Real.cos x))
    convert h using 1
    · funext n
      dsimp [c, s]
      rw [show (((n + 1 + 1 : ℕ) : ℝ) * x) =
          (((n + 1 : ℕ) : ℝ) * x + x) by push_cast; ring, Real.sin_add]
      ring
    · ring
  have hsinx : Real.sin x ≠ 0 := (Real.sin_pos_of_pos_of_lt_pi hx₀ hxπ).ne'
  have hc : Tendsto c atTop (nhds 0) := by
    have h := hcosmul.div_const (Real.sin x)
    convert h using 1
    · funext n
      field_simp [hsinx]
    · simp
  have hsq := (hc.pow 2).add (hs'.pow 2)
  have hbad : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 0) := by
    convert hsq using 1
    · funext n
      simpa [c, s] using (Real.cos_sq_add_sin_sq (((n + 1 : ℕ) : ℝ) * x)).symm
    · norm_num
  have h10 : (1 : ℝ) = 0 := tendsto_nhds_unique tendsto_const_nhds hbad
  norm_num at h10

private lemma exists_abs_sum_range_le_of_seriesConverges (f : ℕ → ℝ)
    (hf : ProofGap.SeriesConverges f) :
    ∃ C : ℝ, ∀ N : ℕ, |∑ n ∈ Finset.range N, f n| ≤ C := by
  rcases (seriesConverges_iff_tendsto_sum_range f).mp hf with ⟨a, ha⟩
  rcases cauchySeq_bdd ha.cauchySeq with ⟨C, hCpos, hC⟩
  refine ⟨C, fun N => ?_⟩
  have h := (hC N 0).le
  simpa [Real.dist_eq] using h

private lemma summable_nonneg_of_series_lower_bound
    (a b c : ℕ → ℝ) (ha : Summable a) (ha₀ : ∀ n, 0 ≤ a n)
    (hb : ProofGap.SeriesConverges b) (hc₀ : ∀ n, 0 ≤ c n)
    (hba : ∀ n, b n + c n ≤ a n) : Summable c := by
  rcases exists_abs_sum_range_le_of_seriesConverges b hb with ⟨C, hC⟩
  apply summable_of_sum_range_le hc₀
  intro N
  have hsum : (∑ n ∈ Finset.range N, (b n + c n)) ≤
      ∑ n ∈ Finset.range N, a n :=
    Finset.sum_le_sum fun n hn => hba n
  have haN : (∑ n ∈ Finset.range N, a n) ≤ ∑' n, a n :=
    ha.sum_le_tsum (Finset.range N) (fun n hn => ha₀ n)
  have hbN : -C ≤ ∑ n ∈ Finset.range N, b n := neg_le_of_abs_le (hC N)
  calc
    (∑ n ∈ Finset.range N, c n) ≤
        (∑ n ∈ Finset.range N, a n) - (∑ n ∈ Finset.range N, b n) := by
          rw [Finset.sum_add_distrib] at hsum
          linarith
    _ ≤ (∑' n, a n) + C := by linarith

theorem gap1 (p x : ℝ) (hp : 1 < p) :
    ∀ n : ℕ, |cosineTerm p x n| ≤ weight p n := by
  intro n
  have hw : 0 ≤ weight p n := (weight_pos p n).le
  simpa [cosineTerm, abs_mul, abs_of_nonneg hw] using
    mul_le_mul_of_nonneg_right (Real.abs_cos_le_one (((n + 1 : ℕ) : ℝ) * x)) hw

theorem gap2 (p x : ℝ) (hp : 1 < p) :
    ∀ n : ℕ, |sineTerm p x n| ≤ weight p n := by
  intro n
  have hw : 0 ≤ weight p n := (weight_pos p n).le
  simpa [sineTerm, abs_mul, abs_of_nonneg hw] using
    mul_le_mul_of_nonneg_right (Real.abs_sin_le_one (((n + 1 : ℕ) : ℝ) * x)) hw

theorem gap3 (p : ℝ) (hp : 1 < p) :
    Summable (weight p) := by
  have hs : Summable (fun n : ℕ => 1 / |(n : ℝ) + 1| ^ p) :=
    (Real.summable_one_div_nat_add_rpow 1 p).mpr hp
  convert hs using 1
  funext n
  rw [weight, abs_of_pos (by positivity : 0 < (n : ℝ) + 1)]
  norm_num [Nat.cast_add, Nat.cast_one]

theorem gap4 (p x : ℝ) (hp : 1 < p) :
    Summable (fun n : ℕ => |cosineTerm p x n|) := by
  exact (gap3 p hp).of_nonneg_of_le (fun n => abs_nonneg _) (gap1 p x hp)

theorem gap5 (p x : ℝ) (hp : 1 < p) :
    Summable (fun n : ℕ => |sineTerm p x n|) := by
  exact (gap3 p hp).of_nonneg_of_le (fun n => abs_nonneg _) (gap2 p x hp)

theorem gap6 (p : ℝ) (hp₀ : 0 < p) (hp₁ : p ≤ 1) :
    Tendsto (weight p) atTop (nhds 0) := by
  have h : Tendsto (fun n : ℕ => (n : ℝ) ^ (-p)) atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop hp₀).comp tendsto_natCast_atTop_atTop
  have h' := (tendsto_add_atTop_iff_nat 1).mpr h
  convert h' using 1
  funext n
  rw [weight, Real.rpow_neg (by positivity)]
  norm_num [Nat.cast_add, Nat.cast_one, one_div]

theorem gap7 (p : ℝ) (hp₀ : 0 < p) (hp₁ : p ≤ 1) :
    Antitone (weight p) := by
  intro m n hmn
  unfold weight
  have hm : 0 ≤ ((m + 1 : ℕ) : ℝ) := by positivity
  have hmn' : ((m + 1 : ℕ) : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.add_le_add_right hmn 1
  have hr := Real.rpow_le_rpow hm hmn' hp₀.le
  simpa only [Nat.cast_add, Nat.cast_one] using
    one_div_le_one_div_of_le (Real.rpow_pos_of_pos (by positivity) p) hr

theorem gap8 (x : ℝ) (hx₀ : 0 < x) (hxπ : x < Real.pi) :
    ∃ C : ℝ, ∀ N : ℕ, |cosinePartial x N| ≤ C := by
  simpa [cosinePartial] using
    cosine_partial_bound x hx₀ (lt_trans hxπ (by linarith [Real.pi_pos]))

theorem gap9 (x : ℝ) (hx₀ : 0 < x) (hxπ : x < Real.pi) :
    ∃ C : ℝ, ∀ N : ℕ, |sinePartial x N| ≤ C := by
  simpa [sinePartial] using
    sine_partial_bound x hx₀ (lt_trans hxπ (by linarith [Real.pi_pos]))

theorem gap10 (p x : ℝ) (hp₀ : 0 < p) (hp₁ : p ≤ 1)
    (hx₀ : 0 < x) (hxπ : x < Real.pi) :
    ProofGap.SeriesConverges (cosineTerm p x) := by
  rcases gap8 x hx₀ hxπ with ⟨C, hC⟩
  have hbound : ∀ N : ℕ,
      ‖∑ n ∈ Finset.range N, Real.cos (((n + 1 : ℕ) : ℝ) * x)‖ ≤ C := by
    simpa [cosinePartial, Real.norm_eq_abs] using hC
  have hc := (gap7 p hp₀ hp₁).cauchySeq_series_mul_of_tendsto_zero_of_bounded
    (gap6 p hp₀ hp₁) hbound
  apply seriesConverges_of_cauchySeq (cosineTerm p x)
  simpa [cosineTerm, smul_eq_mul, mul_comm] using hc

theorem gap11 (p x : ℝ) (hp₀ : 0 < p) (hp₁ : p ≤ 1)
    (hx₀ : 0 < x) (hxπ : x < Real.pi) :
    ProofGap.SeriesConverges (sineTerm p x) := by
  rcases gap9 x hx₀ hxπ with ⟨C, hC⟩
  have hbound : ∀ N : ℕ,
      ‖∑ n ∈ Finset.range N, Real.sin (((n + 1 : ℕ) : ℝ) * x)‖ ≤ C := by
    simpa [sinePartial, Real.norm_eq_abs] using hC
  have hc := (gap7 p hp₀ hp₁).cauchySeq_series_mul_of_tendsto_zero_of_bounded
    (gap6 p hp₀ hp₁) hbound
  apply seriesConverges_of_cauchySeq (sineTerm p x)
  simpa [sineTerm, smul_eq_mul, mul_comm] using hc

theorem gap12 (p x : ℝ) (hp₀ : 0 < p) :
    ∀ n : ℕ,
      |cosineTerm p x n| ≥
        Real.cos (2 * (((n + 1 : ℕ) : ℝ) * x)) * weight p n / 2 +
          weight p n / 2 := by
  intro n
  let t : ℝ := ((n + 1 : ℕ) : ℝ) * x
  have hw : 0 ≤ weight p n := (weight_pos p n).le
  have hcabs : |Real.cos t| ≤ 1 := Real.abs_cos_le_one t
  have hcsq : Real.cos t ^ 2 ≤ |Real.cos t| := by
    rw [← sq_abs]
    nlinarith [abs_nonneg (Real.cos t)]
  have hmul := mul_le_mul_of_nonneg_right hcsq hw
  rw [cosineTerm, abs_mul, abs_of_nonneg hw]
  calc
    Real.cos (2 * (((n + 1 : ℕ) : ℝ) * x)) * weight p n / 2 + weight p n / 2 =
        Real.cos t ^ 2 * weight p n := by rw [Real.cos_sq]; dsimp [t]; ring
    _ ≤ |Real.cos t| * weight p n := hmul

theorem gap13 (p x : ℝ) (hp₀ : 0 < p) :
    ∀ n : ℕ,
      |sineTerm p x n| ≥
        weight p n / 2 -
          Real.cos (2 * (((n + 1 : ℕ) : ℝ) * x)) * weight p n / 2 := by
  intro n
  let t : ℝ := ((n + 1 : ℕ) : ℝ) * x
  have hw : 0 ≤ weight p n := (weight_pos p n).le
  have hsabs : |Real.sin t| ≤ 1 := Real.abs_sin_le_one t
  have hssq : Real.sin t ^ 2 ≤ |Real.sin t| := by
    rw [← sq_abs]
    nlinarith [abs_nonneg (Real.sin t)]
  have hmul := mul_le_mul_of_nonneg_right hssq hw
  rw [sineTerm, abs_mul, abs_of_nonneg hw]
  calc
    weight p n / 2 - Real.cos (2 * (((n + 1 : ℕ) : ℝ) * x)) * weight p n / 2 =
        Real.sin t ^ 2 * weight p n := by
          rw [Real.sin_sq, Real.cos_sq]
          dsimp [t]
          ring
    _ ≤ |Real.sin t| * weight p n := hmul

theorem gap14 (p : ℝ) (hp₀ : 0 < p) (hp₁ : p ≤ 1) :
    ¬ Summable (fun n : ℕ => weight p n / 2) := by
  intro hhalf
  have hw : Summable (weight p) := by
    have h := hhalf.mul_left 2
    convert h using 1
    funext n
    ring
  have hs : Summable (fun n : ℕ => 1 / |(n : ℝ) + 1| ^ p) := by
    convert hw using 1
    funext n
    rw [weight, abs_of_nonneg (by positivity : 0 ≤ (n : ℝ) + 1)]
    norm_num [Nat.cast_add, Nat.cast_one]
  exact (not_lt_of_ge hp₁) ((Real.summable_one_div_nat_add_rpow 1 p).mp hs)

theorem gap15 (p x : ℝ) (hp₀ : 0 < p) (hp₁ : p ≤ 1)
    (hx₀ : 0 < x) (hxπ : x < Real.pi) :
    ProofGap.SeriesConverges (fun n : ℕ =>
      Real.cos (2 * (((n + 1 : ℕ) : ℝ) * x)) * weight p n / 2) := by
  rcases cosine_partial_bound (2 * x) (by positivity) (by nlinarith) with ⟨C, hC⟩
  have hbound : ∀ N : ℕ,
      ‖∑ n ∈ Finset.range N, Real.cos (2 * (((n + 1 : ℕ) : ℝ) * x))‖ ≤ C := by
    intro N
    simpa [Real.norm_eq_abs, mul_assoc, mul_left_comm, mul_comm] using hC N
  have hc := (gap7 p hp₀ hp₁).cauchySeq_series_mul_of_tendsto_zero_of_bounded
    (gap6 p hp₀ hp₁) hbound
  have hs : ProofGap.SeriesConverges (fun n : ℕ =>
      Real.cos (2 * (((n + 1 : ℕ) : ℝ) * x)) * weight p n) := by
    apply seriesConverges_of_cauchySeq
    simpa [smul_eq_mul, mul_comm] using hc
  have hs' := hs.mul_right (1 / 2 : ℝ)
  simpa [div_eq_mul_inv, mul_assoc] using hs'

theorem gap16 (p x : ℝ) (hp₀ : 0 < p) (hp₁ : p ≤ 1)
    (hx₀ : 0 < x) (hxπ : x < Real.pi) :
    ¬ Summable (fun n : ℕ => |cosineTerm p x n|) := by
  intro h
  apply gap14 p hp₀ hp₁
  exact summable_nonneg_of_series_lower_bound
    (fun n : ℕ => |cosineTerm p x n|)
    (fun n : ℕ => Real.cos (2 * (((n + 1 : ℕ) : ℝ) * x)) * weight p n / 2)
    (fun n : ℕ => weight p n / 2)
    h (fun n => abs_nonneg _)
    (gap15 p x hp₀ hp₁ hx₀ hxπ) (fun n => by exact (div_nonneg (weight_pos p n).le (by norm_num)))
    (gap12 p x hp₀)

theorem gap17 (p x : ℝ) (hp₀ : 0 < p) (hp₁ : p ≤ 1)
    (hx₀ : 0 < x) (hxπ : x < Real.pi) :
    ¬ Summable (fun n : ℕ => |sineTerm p x n|) := by
  intro h
  apply gap14 p hp₀ hp₁
  have hb := (gap15 p x hp₀ hp₁ hx₀ hxπ).neg
  exact summable_nonneg_of_series_lower_bound
    (fun n : ℕ => |sineTerm p x n|)
    (fun n : ℕ => -(Real.cos (2 * (((n + 1 : ℕ) : ℝ) * x)) * weight p n / 2))
    (fun n : ℕ => weight p n / 2)
    h (fun n => abs_nonneg _) (by simpa using hb)
    (fun n => by exact (div_nonneg (weight_pos p n).le (by norm_num)))
    (fun n => by simpa [sub_eq_add_neg, add_comm] using gap13 p x hp₀ n)

theorem gap18 (p x : ℝ) (hp₀ : 0 < p) (hp₁ : p ≤ 1)
    (hx₀ : 0 < x) (hxπ : x < Real.pi) :
    ConditionallySummable (cosineTerm p x) := by
  exact ⟨gap10 p x hp₀ hp₁ hx₀ hxπ, gap16 p x hp₀ hp₁ hx₀ hxπ⟩

theorem gap19 (p x : ℝ) (hp₀ : 0 < p) (hp₁ : p ≤ 1)
    (hx₀ : 0 < x) (hxπ : x < Real.pi) :
    ConditionallySummable (sineTerm p x) := by
  exact ⟨gap11 p x hp₀ hp₁ hx₀ hxπ, gap17 p x hp₀ hp₁ hx₀ hxπ⟩

theorem gap20 (p x : ℝ) (hp : p ≤ 0)
    (hx₀ : 0 < x) (hxπ : x < Real.pi) :
    ¬ ProofGap.SeriesConverges (cosineTerm p x) := by
  intro hseries
  have ht := tendsto_zero_of_seriesConverges (cosineTerm p x) hseries
  have habs : Tendsto (fun n : ℕ => |Real.cos (((n + 1 : ℕ) : ℝ) * x)|)
      atTop (nhds 0) := by
    refine squeeze_zero (g := fun n => |cosineTerm p x n|)
      (fun n => abs_nonneg _) (fun n => ?_) ?_
    · have hw := one_le_weight_of_nonpos p hp n
      calc
        |Real.cos (((n + 1 : ℕ) : ℝ) * x)| =
            |Real.cos (((n + 1 : ℕ) : ℝ) * x)| * 1 := by ring
        _ ≤ |Real.cos (((n + 1 : ℕ) : ℝ) * x)| * weight p n :=
          mul_le_mul_of_nonneg_left hw (abs_nonneg _)
        _ = |cosineTerm p x n| := by
          rw [cosineTerm, abs_mul, abs_of_pos (weight_pos p n)]
    · simpa using ht.abs
  have hc : Tendsto (fun n : ℕ => Real.cos (((n + 1 : ℕ) : ℝ) * x))
      atTop (nhds 0) := by
    rw [tendsto_zero_iff_abs_tendsto_zero]
    exact habs
  exact not_tendsto_cos_nat_add_one_zero x hx₀ hxπ hc

theorem gap21 (p x : ℝ) (hp : p ≤ 0)
    (hx₀ : 0 < x) (hxπ : x < Real.pi) :
    ¬ ProofGap.SeriesConverges (sineTerm p x) := by
  intro hseries
  have ht := tendsto_zero_of_seriesConverges (sineTerm p x) hseries
  have habs : Tendsto (fun n : ℕ => |Real.sin (((n + 1 : ℕ) : ℝ) * x)|)
      atTop (nhds 0) := by
    refine squeeze_zero (g := fun n => |sineTerm p x n|)
      (fun n => abs_nonneg _) (fun n => ?_) ?_
    · have hw := one_le_weight_of_nonpos p hp n
      calc
        |Real.sin (((n + 1 : ℕ) : ℝ) * x)| =
            |Real.sin (((n + 1 : ℕ) : ℝ) * x)| * 1 := by ring
        _ ≤ |Real.sin (((n + 1 : ℕ) : ℝ) * x)| * weight p n :=
          mul_le_mul_of_nonneg_left hw (abs_nonneg _)
        _ = |sineTerm p x n| := by
          rw [sineTerm, abs_mul, abs_of_pos (weight_pos p n)]
    · simpa using ht.abs
  have hs : Tendsto (fun n : ℕ => Real.sin (((n + 1 : ℕ) : ℝ) * x))
      atTop (nhds 0) := by
    rw [tendsto_zero_iff_abs_tendsto_zero]
    exact habs
  exact not_tendsto_sin_nat_add_one_zero x hx₀ hxπ hs

theorem gap22 (p x : ℝ) (hx₀ : 0 < x) (hxπ : x < Real.pi) :
    0 < p ↔
      ((Summable (fun n : ℕ => |cosineTerm p x n|) ∧
          Summable (fun n : ℕ => |sineTerm p x n|)) ∨
        (ConditionallySummable (cosineTerm p x) ∧
          ConditionallySummable (sineTerm p x))) := by
  constructor
  · intro hp
    by_cases hp₁ : 1 < p
    · exact Or.inl ⟨gap4 p x hp₁, gap5 p x hp₁⟩
    · have hple : p ≤ 1 := le_of_not_gt hp₁
      exact Or.inr ⟨gap18 p x hp hple hx₀ hxπ, gap19 p x hp hple hx₀ hxπ⟩
  · rintro (habs | hcond)
    · by_contra hpnot
      have hpnon : p ≤ 0 := le_of_not_gt hpnot
      have hu : Summable (cosineTerm p x) := summable_abs_iff.mp habs.1
      have hc : ProofGap.SeriesConverges (cosineTerm p x) :=
        hu.mono_filter (SummationFilter.conditional ℕ).le_atTop
      exact gap20 p x hpnon hx₀ hxπ hc
    · by_contra hpnot
      have hpnon : p ≤ 0 := le_of_not_gt hpnot
      exact gap20 p x hpnon hx₀ hxπ hcond.1.1

end

end ProofGap.Exercise2698
