import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

namespace ProofGap.Exercise2932_7

noncomputable section

open scoped BigOperators Interval

def cubeRoot (x : ℝ) : ℝ :=
  Real.rpow x (1 / 3 : ℝ)

def risingCoefficient (n : ℕ) : ℝ :=
  (∏ k ∈ Finset.range n, ((1 / 3 : ℝ) + (k : ℝ))) /
    (Nat.factorial n : ℝ)

def binomialTerm (n : ℕ) (x : ℝ) : ℝ :=
  risingCoefficient n * x ^ (2 * n)

def integratedTerm (n : ℕ) : ℝ :=
  risingCoefficient n * (1 / 3 : ℝ) ^ (2 * n + 1) /
    (2 * n + 1 : ℕ)

def targetIntegral : ℝ :=
  ∫ x in (0 : ℝ)..(1 / 3 : ℝ), 1 / cubeRoot (1 - x ^ 2)

def seriesValue : ℝ :=
  ∑' n : ℕ, integratedTerm n

def Approx (u v ε : ℝ) : Prop :=
  |u - v| < ε

private theorem risingCoefficient_succ (n : ℕ) :
    risingCoefficient (n + 1) =
      risingCoefficient n * ((1 / 3 : ℝ) + n) / (n + 1) := by
  unfold risingCoefficient
  rw [Finset.prod_range_succ, Nat.factorial_succ]
  push_cast
  have hf : (Nat.factorial n : ℝ) ≠ 0 := by positivity
  have hn : (n + 1 : ℝ) ≠ 0 := by positivity
  field_simp [hf, hn]

private theorem multichoose_succ_real (r : ℝ) (n : ℕ) :
    Ring.multichoose r (n + 1) =
      Ring.multichoose r n * (r + n) / (n + 1) := by
  have h0 := Ring.factorial_nsmul_multichoose_eq_ascPochhammer r n
  have h1 := Ring.factorial_nsmul_multichoose_eq_ascPochhammer r (n + 1)
  simp only [nsmul_eq_mul] at h0 h1
  rw [ascPochhammer_succ_right, Polynomial.smeval_mul,
    Polynomial.smeval_add, Polynomial.smeval_X,
    Polynomial.smeval_natCast] at h1
  rw [← h0] at h1
  rw [Nat.factorial_succ] at h1
  push_cast at h1
  norm_num [pow_one, pow_zero, nsmul_eq_mul] at h1
  have hn : (n + 1 : ℝ) ≠ 0 := by positivity
  have hf : (Nat.factorial n : ℝ) ≠ 0 := by positivity
  apply (eq_div_iff hn).2
  apply mul_left_cancel₀ hf
  calc
    (Nat.factorial n : ℝ) *
          (Ring.multichoose r (n + 1) * (n + 1)) =
        (n + 1) * (Nat.factorial n : ℝ) *
          Ring.multichoose r (n + 1) := by ring
    _ = (Nat.factorial n : ℝ) * Ring.multichoose r n *
          (r + n) := h1
    _ = (Nat.factorial n : ℝ) *
          (Ring.multichoose r n * (r + n)) := by ring

private theorem risingCoefficient_eq_multichoose (n : ℕ) :
    risingCoefficient n = Ring.multichoose (1 / 3 : ℝ) n := by
  induction n with
  | zero =>
      norm_num [risingCoefficient, Ring.multichoose_zero_right]
  | succ n ih =>
      rw [risingCoefficient_succ, multichoose_succ_real, ih]

private theorem binomialTerm_hasSum (x : ℝ) (hx : |x| < 1) :
    HasSum (fun n => binomialTerm n x)
      (Real.rpow (1 - x ^ 2) (-1 / 3 : ℝ)) := by
  have hzabs : |x ^ 2| < 1 := by
    rw [abs_of_nonneg (sq_nonneg x)]
    nlinarith [sq_abs x, abs_nonneg x]
  have hz : x ^ 2 ∈ Metric.eball (0 : ℝ) 1 := by
    rw [Metric.mem_eball, edist_dist, Real.dist_eq]
    rw [ENNReal.ofReal_lt_one, sub_zero]
    exact hzabs
  have h :=
    (Real.one_div_one_sub_rpow_hasFPowerSeriesOnBall_zero
      (1 / 3 : ℝ)).hasSum hz
  simp only [Real.rpow_eq_pow]
  convert h using 1 with n
  · funext n
    rw [FormalMultilinearSeries.ofScalars_apply_eq]
    simp only [smul_eq_mul, binomialTerm]
    rw [← Ring.multichoose_eq, ← risingCoefficient_eq_multichoose]
    rw [pow_mul]
  · have hnonneg : 0 ≤ 1 - x ^ 2 := by
      rw [abs_of_nonneg (sq_nonneg x)] at hzabs
      linarith
    simp only [zero_add, one_div]
    rw [show (-1 / 3 : ℝ) = -(1 / 3 : ℝ) by ring,
      Real.rpow_neg hnonneg]
    congr 2 <;> ring

theorem gap1 :
    ∀ x : ℝ, |x| < 1 →
      1 / cubeRoot (1 - x ^ 2) =
        Real.rpow (1 - x ^ 2) (-1 / 3 : ℝ) := by
  intro x hx
  have hnonneg : 0 ≤ 1 - x ^ 2 := by
    have hx2 : x ^ 2 < 1 := by
      nlinarith [sq_abs x, abs_nonneg x]
    linarith
  unfold cubeRoot
  rw [one_div]
  change
    (Real.rpow (1 - x ^ 2) (1 / 3 : ℝ))⁻¹ =
      Real.rpow (1 - x ^ 2) (-1 / 3 : ℝ)
  rw [show (-1 / 3 : ℝ) = -(1 / 3 : ℝ) by ring]
  exact (Real.rpow_neg hnonneg (1 / 3 : ℝ)).symm

theorem gap2 :
    ∀ x : ℝ, |x| < 1 →
      Real.rpow (1 - x ^ 2) (-1 / 3 : ℝ) =
        ∑' n : ℕ, binomialTerm n x := by
  intro x hx
  exact (binomialTerm_hasSum x hx).tsum_eq.symm

theorem gap3 :
    ∀ x : ℝ, |x| < 1 →
      1 / cubeRoot (1 - x ^ 2) =
        ∑' n : ℕ, binomialTerm n x := by
  intro x hx
  exact (gap1 x hx).trans (gap2 x hx)

private theorem risingCoefficient_nonneg (n : ℕ) :
    0 ≤ risingCoefficient n := by
  induction n with
  | zero =>
      norm_num [risingCoefficient]
  | succ n ih =>
      rw [risingCoefficient_succ]
      positivity

private theorem integral_binomialTerm (n : ℕ) :
    (∫ x in (0 : ℝ)..(1 / 3 : ℝ), binomialTerm n x) =
      integratedTerm n := by
  unfold binomialTerm integratedTerm
  rw [intervalIntegral.integral_const_mul, integral_pow]
  norm_num
  ring

private theorem norm_binomialTerm_le
    (t : ℝ) (n : ℕ) (ht : t ∈ Set.uIcc 0 (1 / 3 : ℝ)) :
    ‖binomialTerm n t‖ ≤ binomialTerm n (1 / 3 : ℝ) := by
  have habs : |t| ≤ (1 / 3 : ℝ) := by
    have hdist := Real.dist_left_le_of_mem_uIcc ht
    simpa [Real.dist_eq] using hdist
  have hc : 0 ≤ risingCoefficient n := risingCoefficient_nonneg n
  rw [Real.norm_eq_abs]
  calc
    |binomialTerm n t| =
        risingCoefficient n * |t| ^ (2 * n) := by
      simp [binomialTerm, abs_mul, abs_pow, abs_of_nonneg hc]
    _ ≤ risingCoefficient n * (1 / 3 : ℝ) ^ (2 * n) := by
      gcongr
    _ = binomialTerm n (1 / 3 : ℝ) := by
      rfl

private theorem endpoint_summable :
    Summable (fun n : ℕ => binomialTerm n (1 / 3 : ℝ)) :=
  (binomialTerm_hasSum (1 / 3 : ℝ) (by norm_num)).summable

private theorem integratedTerm_hasSum :
    HasSum integratedTerm targetIntegral := by
  unfold targetIntegral
  have h := intervalIntegral.hasSum_integral_of_dominated_convergence
    (μ := MeasureTheory.volume)
    (a := (0 : ℝ)) (b := (1 / 3 : ℝ))
    (f := fun t : ℝ => 1 / cubeRoot (1 - t ^ 2))
    (F := fun n t => binomialTerm n t)
    (fun n (_ : ℝ) => binomialTerm n (1 / 3 : ℝ))
    (fun n => by
      apply Continuous.aestronglyMeasurable
      unfold binomialTerm
      fun_prop)
    (by
      intro n
      filter_upwards with t ht
      exact norm_binomialTerm_le t n (Set.uIoc_subset_uIcc ht))
    (by
      filter_upwards with t ht
      exact endpoint_summable)
    intervalIntegrable_const
    (by
      filter_upwards with t ht
      have ht' := Set.uIoc_subset_uIcc ht
      rw [Set.uIcc_of_le (by norm_num)] at ht'
      have habs : |t| < 1 := by
        rw [abs_of_nonneg ht'.1]
        linarith [ht'.2]
      rw [gap1 t habs]
      exact binomialTerm_hasSum t habs)
  apply h.congr_fun
  intro n
  exact (integral_binomialTerm n).symm

private theorem summable_integratedTerm :
    Summable integratedTerm :=
  integratedTerm_hasSum.summable

theorem gap4 :
    targetIntegral = seriesValue := by
  unfold seriesValue
  exact integratedTerm_hasSum.tsum_eq.symm

private theorem risingCoefficient_succ_le_third (n : ℕ) :
    risingCoefficient (n + 1) ≤ (1 / 3 : ℝ) := by
  induction n with
  | zero =>
      norm_num [risingCoefficient]
  | succ n ih =>
      rw [risingCoefficient_succ]
      have hratio_nonneg :
          0 ≤ ((1 / 3 : ℝ) + (n + 1 : ℕ)) / ((n + 1 : ℕ) + 1) := by
        positivity
      have hratio_le :
          ((1 / 3 : ℝ) + (n + 1 : ℕ)) / ((n + 1 : ℕ) + 1) ≤ 1 := by
        apply (div_le_one (by positivity)).2
        push_cast
        linarith
      calc
        risingCoefficient (n + 1) *
              ((1 / 3 : ℝ) + (n + 1 : ℕ)) / ((n + 1 : ℕ) + 1) =
            risingCoefficient (n + 1) *
              (((1 / 3 : ℝ) + (n + 1 : ℕ)) / ((n + 1 : ℕ) + 1)) := by
                ring
        _ ≤ (1 / 3 : ℝ) *
              (((1 / 3 : ℝ) + (n + 1 : ℕ)) / ((n + 1 : ℕ) + 1)) :=
          mul_le_mul_of_nonneg_right ih hratio_nonneg
        _ ≤ (1 / 3 : ℝ) * 1 :=
          mul_le_mul_of_nonneg_left hratio_le (by norm_num)
        _ = (1 / 3 : ℝ) := by ring

private theorem integratedTerm_nonneg (n : ℕ) :
    0 ≤ integratedTerm n := by
  unfold integratedTerm
  exact div_nonneg
    (mul_nonneg (risingCoefficient_nonneg n) (by positivity))
    (by positivity)

private theorem tail_term_le_majorant (n : ℕ) :
    integratedTerm (n + 1) ≤
      (1 / 243 : ℝ) * (1 / 9 : ℝ) ^ n := by
  have hc := risingCoefficient_succ_le_third n
  have hp :
      0 ≤ (1 / 3 : ℝ) ^ (2 * (n + 1) + 1) := by positivity
  have hden :
      (3 : ℝ) ≤ ((2 * (n + 1) + 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 3 ≤ 2 * (n + 1) + 1 by omega)
  calc
    integratedTerm (n + 1) =
        risingCoefficient (n + 1) *
          (1 / 3 : ℝ) ^ (2 * (n + 1) + 1) /
            ((2 * (n + 1) + 1 : ℕ) : ℝ) := rfl
    _ ≤
        (1 / 3 : ℝ) *
          (1 / 3 : ℝ) ^ (2 * (n + 1) + 1) /
            ((2 * (n + 1) + 1 : ℕ) : ℝ) := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hc hp) (Nat.cast_nonneg _)
    _ ≤
        (1 / 3 : ℝ) *
          (1 / 3 : ℝ) ^ (2 * (n + 1) + 1) / 3 := by
      gcongr
    _ = (1 / 243 : ℝ) * (1 / 9 : ℝ) ^ n := by
      rw [show 2 * (n + 1) + 1 = 3 + 2 * n by omega, pow_add,
        pow_mul]
      norm_num
      ring

private theorem tail_summable :
    Summable (fun n : ℕ => integratedTerm (n + 1)) :=
  (summable_nat_add_iff 1).2 summable_integratedTerm

private theorem majorant_summable :
    Summable (fun n : ℕ =>
      (1 / 243 : ℝ) * (1 / 9 : ℝ) ^ n) :=
  (summable_geometric_of_norm_lt_one
    (by norm_num [Real.norm_eq_abs] : ‖(1 / 9 : ℝ)‖ < 1)).mul_left _

private theorem seriesValue_eq_head_add_tail :
    seriesValue =
      integratedTerm 0 + ∑' n : ℕ, integratedTerm (n + 1) := by
  unfold seriesValue
  have hsplit := summable_integratedTerm.sum_add_tsum_nat_add 1
  simpa using hsplit.symm

theorem gap5 :
    Approx seriesValue (337 / 1000 : ℝ)
      (1 / 1000 : ℝ) := by
  have htail_nonneg :
      0 ≤ ∑' n : ℕ, integratedTerm (n + 1) :=
    tsum_nonneg (fun n => integratedTerm_nonneg _)
  have htail_split := tail_summable.sum_add_tsum_nat_add 1
  have hrest_nonneg :
      0 ≤ ∑' n : ℕ, integratedTerm (n + 1 + 1) :=
    tsum_nonneg (fun n => integratedTerm_nonneg _)
  have hterm_one : integratedTerm 1 = (1 / 243 : ℝ) := by
    norm_num [integratedTerm, risingCoefficient]
  have htail_lower :
      (1 / 243 : ℝ) ≤ ∑' n : ℕ, integratedTerm (n + 1) := by
    calc
      (1 / 243 : ℝ) = integratedTerm 1 + 0 := by
        rw [hterm_one]
        ring
      _ ≤ integratedTerm 1 +
          ∑' n : ℕ, integratedTerm (n + 1 + 1) :=
        add_le_add (le_refl _) hrest_nonneg
      _ = ∑' n : ℕ, integratedTerm (n + 1) := by
        simpa using htail_split
  have htail_le :
      (∑' n : ℕ, integratedTerm (n + 1)) ≤
        ∑' n : ℕ, (1 / 243 : ℝ) * (1 / 9 : ℝ) ^ n :=
    tail_summable.tsum_le_tsum tail_term_le_majorant majorant_summable
  have hmajorant :
      (∑' n : ℕ, (1 / 243 : ℝ) * (1 / 9 : ℝ) ^ n) =
        (1 / 216 : ℝ) := by
    rw [tsum_mul_left, tsum_geometric_of_norm_lt_one
      (by norm_num [Real.norm_eq_abs] :
        ‖(1 / 9 : ℝ)‖ < 1)]
    norm_num
  rw [hmajorant] at htail_le
  have hhead : integratedTerm 0 = (1 / 3 : ℝ) := by
    norm_num [integratedTerm, risingCoefficient]
  rw [Approx, abs_lt, seriesValue_eq_head_add_tail, hhead]
  constructor <;> linarith

theorem gap6 :
    Approx targetIntegral (337 / 1000 : ℝ)
      (1 / 1000 : ℝ) := by
  rw [gap4]
  exact gap5

end

end ProofGap.Exercise2932_7
