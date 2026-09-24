import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecificLimits.Normed

namespace ProofGap.Exercise2733_4

noncomputable section

open Filter

def term (x y : ℝ) (n : ℕ) : ℝ :=
  x ^ n / (n + y ^ n)

def outerModel (x y : ℝ) (n : ℕ) : ℝ :=
  |x / y| ^ n * (1 / (1 + (n : ℝ) / y ^ n))

private theorem tendsto_pow_div_linear (x : ℝ) (hx : 1 < |x|) :
    Tendsto (fun n : ℕ => |x| ^ (n + 1) / ((n + 2 : ℕ) : ℝ))
      atTop atTop := by
  have hbase : Tendsto (fun n : ℕ => (n : ℝ) ^ 1 / |x| ^ n)
      atTop (nhds 0) := tendsto_pow_const_div_const_pow_of_one_lt 1 hx
  have hshift : Tendsto
      (fun n : ℕ => ((n + 1 : ℕ) : ℝ) / |x| ^ (n + 1))
      atTop (nhds 0) := by
    simpa [Function.comp_def] using hbase.comp (tendsto_add_atTop_nat 1)
  have hinvpow : Tendsto (fun n : ℕ => 1 / |x| ^ (n + 1))
      atTop (nhds 0) := by
    have hpow := (tendsto_pow_atTop_atTop_of_one_lt hx).comp
      (tendsto_add_atTop_nat 1)
    exact tendsto_const_nhds.div_atTop hpow
  have hadd : Tendsto
      (fun n : ℕ => ((n + 1 : ℕ) : ℝ) / |x| ^ (n + 1) +
        1 / |x| ^ (n + 1)) atTop (nhds 0) := by
    simpa using hshift.add hinvpow
  have hzero : Tendsto
      (fun n : ℕ => ((n + 2 : ℕ) : ℝ) / |x| ^ (n + 1))
      atTop (nhds 0) := by
    convert hadd using 1
    funext n
    push_cast
    ring
  have hzeroGT : Tendsto
      (fun n : ℕ => ((n + 2 : ℕ) : ℝ) / |x| ^ (n + 1))
      atTop (nhdsWithin 0 (Set.Ioi 0)) := by
    rw [tendsto_nhdsWithin_iff]
    exact ⟨hzero, Filter.Eventually.of_forall (fun n => by
      change 0 < ((n + 2 : ℕ) : ℝ) / |x| ^ (n + 1)
      positivity)⟩
  have hinv := hzeroGT.inv_tendsto_nhdsGT_zero
  apply hinv.congr'
  filter_upwards with n
  change ((((n + 2 : ℕ) : ℝ) / |x| ^ (n + 1))⁻¹) =
    |x| ^ (n + 1) / ((n + 2 : ℕ) : ℝ)
  field_simp

theorem gap1 (x : ℝ) :
    ∀ n : ℕ, 1 ≤ n → term x 0 n = x ^ n / n := by
  intro n hn
  have hn0 : n ≠ 0 := by omega
  simp [term, zero_pow hn0]

theorem gap2 (x : ℝ) (hx : 1 < |x|) :
    ¬ Summable (fun n : ℕ => term x 0 (n + 1)) := by
  intro hsum
  have hzero : Tendsto (fun n : ℕ => ‖term x 0 (n + 1)‖)
      atTop (nhds 0) := by
    simpa using tendsto_norm.comp hsum.tendsto_atTop_zero
  have hlarge : Tendsto
      (fun n : ℕ => |x| ^ (n + 1) / ((n + 1 : ℕ) : ℝ)) atTop atTop := by
    have hbase : Tendsto (fun n : ℕ => |x| ^ (n + 1) / ((n + 2 : ℕ) : ℝ))
        atTop atTop := tendsto_pow_div_linear x hx
    refine tendsto_atTop_mono' atTop ?_ hbase
    filter_upwards with n
    gcongr
    norm_num
  have hnorm : Tendsto
      (fun n : ℕ => ‖term x 0 (n + 1)‖) atTop atTop := by
    apply hlarge.congr'
    filter_upwards with n
    rw [gap1 x (n + 1) (by omega), Real.norm_eq_abs, abs_div, abs_pow]
    rw [abs_of_pos (by positivity : (0 : ℝ) < ((n + 1 : ℕ) : ℝ))]
  exact not_tendsto_nhds_of_tendsto_atTop hnorm 0 hzero

theorem gap3 (x y : ℝ) (hy : 0 < y) :
    ∀ n : ℕ, 1 ≤ n → |term x y n| = |x| ^ n / (n + y ^ n) := by
  intro n hn
  have hden : 0 < (n : ℝ) + y ^ n := by positivity
  simp [term, abs_div, abs_pow, abs_of_pos hden]

theorem gap4 (x y : ℝ) (hy : 1 < y) (hxy : |x| < y) :
    ∀ n : ℕ, 1 ≤ n → |x| ^ n / (n + y ^ n) ≤ |x / y| ^ n := by
  intro n hn
  have hy0 : 0 < y := lt_trans (by norm_num) hy
  have hden : 0 < (n : ℝ) + y ^ n := by positivity
  have hypow : 0 < y ^ n := by positivity
  have hyle : y ^ n ≤ (n : ℝ) + y ^ n := by
    have hnnonneg : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  calc
    |x| ^ n / ((n : ℝ) + y ^ n) ≤ |x| ^ n / y ^ n := by
      exact div_le_div_of_nonneg_left (pow_nonneg (abs_nonneg x) n) hypow hyle
    _ = |x / y| ^ n := by
      rw [abs_div, abs_of_pos hy0, div_pow]

theorem gap5 (x y : ℝ) (hy : 1 < y) (hxy : |x| < y) :
    ∀ n : ℕ, 1 ≤ n → |term x y n| ≤ |x / y| ^ n := by
  intro n hn
  rw [gap3 x y (lt_trans (by norm_num) hy) n hn]
  exact gap4 x y hy hxy n hn

theorem gap6 (x y : ℝ) (hy : 1 < y) (hxy : |x| < y) :
    Summable (fun n : ℕ => |term x y (n + 1)|) := by
  have hy0 : 0 < y := lt_trans (by norm_num) hy
  have hratio : |x / y| < 1 := by
    rw [abs_div, abs_of_pos hy0]
    exact (div_lt_one hy0).2 hxy
  have hgeo0 : Summable (fun n : ℕ => |x / y| ^ n) :=
    summable_geometric_of_norm_lt_one (by simpa [Real.norm_eq_abs] using hratio)
  have hgeo : Summable (fun n : ℕ => |x / y| ^ (n + 1)) :=
    (summable_nat_add_iff (f := fun n : ℕ => |x / y| ^ n) 1).mpr hgeo0
  exact Summable.of_nonneg_of_le (fun n => abs_nonneg _)
    (fun n => gap5 x y hy hxy (n + 1) (by omega)) hgeo

theorem gap7 (x y : ℝ) (hy : 1 < y) :
    ∀ n : ℕ, 1 ≤ n → |term x y n| = outerModel x y n := by
  intro n hn
  have hy0 : 0 < y := lt_trans (by norm_num) hy
  rw [gap3 x y hy0 n hn]
  unfold outerModel
  rw [abs_div, abs_of_pos hy0, div_pow]
  have hyn : y ^ n ≠ 0 := pow_ne_zero _ (ne_of_gt hy0)
  field_simp [hyn]
  ring

theorem gap8 (x y : ℝ) (hy : 1 < y) (hxy : 1 ≤ |x / y|) :
    (|x / y| = 1 →
      Tendsto (fun n : ℕ => outerModel x y (n + 1)) atTop (nhds 1)) ∧
    (1 < |x / y| →
      Tendsto (fun n : ℕ => outerModel x y (n + 1)) atTop atTop) := by
  have hsmall0 : Tendsto
      (fun n : ℕ => (n : ℝ) ^ 1 / y ^ n) atTop (nhds 0) :=
    tendsto_pow_const_div_const_pow_of_one_lt 1 hy
  have hsmall : Tendsto
      (fun n : ℕ => ((n + 1 : ℕ) : ℝ) / y ^ (n + 1)) atTop (nhds 0) := by
    simpa [Function.comp_def] using hsmall0.comp (tendsto_add_atTop_nat 1)
  have hfactor : Tendsto
      (fun n : ℕ => 1 / (1 + ((n + 1 : ℕ) : ℝ) / y ^ (n + 1)))
      atTop (nhds 1) := by
    have hone : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1) :=
      tendsto_const_nhds
    have hadd : Tendsto
        (fun n : ℕ => (1 : ℝ) + ((n + 1 : ℕ) : ℝ) / y ^ (n + 1))
        atTop (nhds 1) := by simpa using hone.add hsmall
    have hinv := hadd.inv₀ (by norm_num : (1 : ℝ) ≠ 0)
    simpa [one_div] using hinv
  constructor
  · intro heq
    simpa [outerModel, heq] using hfactor
  · intro hlt
    have hpow : Tendsto (fun n : ℕ => |x / y| ^ (n + 1)) atTop atTop :=
      (tendsto_pow_atTop_atTop_of_one_lt hlt).comp (tendsto_add_atTop_nat 1)
    simpa [outerModel] using hpow.atTop_mul_pos (by norm_num : (0 : ℝ) < 1) hfactor

theorem gap9 (x y : ℝ) (hy : 1 < y) (hxy : 1 ≤ |x / y|) :
    ¬ Tendsto (fun n : ℕ => |term x y (n + 1)|) atTop (nhds 0) := by
  intro hzero
  have heq : (fun n : ℕ => |term x y (n + 1)|) =
      fun n : ℕ => outerModel x y (n + 1) := by
    funext n
    exact gap7 x y hy (n + 1) (by omega)
  rw [heq] at hzero
  rcases hxy.eq_or_lt with hratio | hratio
  · have hone := (gap8 x y hy hxy).1 hratio.symm
    have : (1 : ℝ) = 0 := tendsto_nhds_unique hone hzero
    norm_num at this
  · exact not_tendsto_nhds_of_tendsto_atTop
      ((gap8 x y hy hxy).2 hratio) 0 hzero

theorem gap10 (x y : ℝ) (hy : 1 < y) (hxy : 1 ≤ |x / y|) :
    ¬ Summable (fun n : ℕ => term x y (n + 1)) := by
  intro hsum
  apply gap9 x y hy hxy
  simpa [Real.norm_eq_abs] using tendsto_norm.comp hsum.tendsto_atTop_zero

theorem gap11 (x y : ℝ) (hx : 1 < |x|) (hy0 : 0 < y) (hy1 : y ≤ 1) :
    ∀ n : ℕ, 1 ≤ n → |term x y n| ≥ |x| ^ n / (n + 1 : ℕ) := by
  intro n hn
  rw [gap3 x y hy0 n hn]
  have hypow : y ^ n ≤ 1 := pow_le_one₀ (le_of_lt hy0) hy1
  norm_num [Nat.cast_add]
  gcongr

theorem gap12 (x : ℝ) (hx : 1 < |x|) :
    Tendsto (fun n : ℕ => |x| ^ (n + 1) / ((n + 2 : ℕ) : ℝ))
      atTop atTop := by
  exact tendsto_pow_div_linear x hx

theorem gap13 (x y : ℝ) (hx : 1 < |x|) (hy0 : 0 < y) (hy1 : y ≤ 1) :
    Tendsto (fun n : ℕ => |term x y (n + 1)|) atTop atTop := by
  refine tendsto_atTop_mono' atTop ?_ (gap12 x hx)
  filter_upwards with n
  simpa [Nat.add_assoc] using gap11 x y hx hy0 hy1 (n + 1) (by omega)

theorem gap14 (x y : ℝ) (hx : 1 < |x|) (hy0 : 0 < y) (hy1 : y ≤ 1) :
    ¬ Summable (fun n : ℕ => term x y (n + 1)) := by
  intro hsum
  have hzero : Tendsto (fun n : ℕ => |term x y (n + 1)|)
      atTop (nhds 0) := by
    simpa [Real.norm_eq_abs] using tendsto_norm.comp hsum.tendsto_atTop_zero
  exact not_tendsto_nhds_of_tendsto_atTop (gap13 x y hx hy0 hy1) 0 hzero

theorem gap15 :
    {q : ℝ × ℝ | 1 < |q.1| ∧ 0 < q.2 ∧ |q.1| < q.2} ⊆
      {q : ℝ × ℝ | Summable (fun n : ℕ => |term q.1 q.2 (n + 1)|)} := by
  rintro ⟨x, y⟩ ⟨hx, hy0, hxy⟩
  have hy : 1 < y := hx.trans hxy
  exact gap6 x y hy hxy

end

end ProofGap.Exercise2733_4
