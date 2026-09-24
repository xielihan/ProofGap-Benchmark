import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Complex.AbelLimit
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

namespace ProofGap.Exercise2909

noncomputable section

open scoped BigOperators Interval

def seriesTerm (x : ℝ) (n : ℕ) : ℝ :=
  x ^ (n + 1) / ((n + 1 : ℝ) * (n + 2 : ℝ))

def derivativeTerm (x : ℝ) (n : ℕ) : ℝ :=
  x ^ n / (n + 2 : ℝ)

def logarithmTerm (x : ℝ) (n : ℕ) : ℝ :=
  x ^ (n + 1) / (n + 1 : ℝ)

def F (x : ℝ) : ℝ :=
  ∑' n, seriesTerm x n

def closedForm (x : ℝ) : ℝ :=
  if x = 0 then 0
  else if x = -1 then 1 - 2 * Real.log 2
  else if x = 1 then 1
  else 1 + ((1 - x) / x) * Real.log (1 - x)

private theorem absLtOneOfMemUIcc {x t : ℝ} (hx : |x| < 1)
    (ht : t ∈ Set.uIcc (0 : ℝ) x) : |t| < 1 := by
  rcases Set.mem_uIcc.mp ht with h | h
  · rw [abs_of_nonneg h.1]
    exact lt_of_le_of_lt (h.2.trans (le_abs_self x)) hx
  · have hx0 : x ≤ 0 := h.1.trans h.2
    rw [abs_of_nonpos h.2, abs_of_nonpos hx0] at *
    linarith

private theorem seriesTerm_hasDerivAt (n : ℕ) (x : ℝ) :
    HasDerivAt (fun y : ℝ => seriesTerm y n) (derivativeTerm x n) x := by
  have h₁ : (n + 1 : ℝ) ≠ 0 := by positivity
  have h₂ : (n + 2 : ℝ) ≠ 0 := by positivity
  convert
    ((hasDerivAt_id x).pow (n + 1)).div_const
      ((n + 1 : ℝ) * (n + 2 : ℝ)) using 1 <;>
    simp only [seriesTerm, derivativeTerm, Nat.add_sub_cancel,
      Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, id_eq] <;>
    field_simp [h₁, h₂] <;>
    ring

private theorem F_hasDerivAt_series (x : ℝ) (hx : |x| < 1) :
    HasDerivAt F (∑' n, derivativeTerm x n) x := by
  let r : ℝ := (|x| + 1) / 2
  have hr0 : 0 < r := by
    dsimp [r]
    positivity
  have hr1 : r < 1 := by
    dsimp [r]
    linarith
  have hxr : |x| < r := by
    dsimp [r]
    linarith
  have hnorm : ‖r‖ < 1 := by
    simpa [Real.norm_eq_abs, abs_of_pos hr0] using hr1
  have hu : Summable (fun n : ℕ => r ^ n) :=
    summable_geometric_of_norm_lt_one hnorm
  have hbound :
      ∀ n y, y ∈ Set.Ioo (-r) r →
        ‖derivativeTerm y n‖ ≤ r ^ n := by
    intro n y hy
    have hay : |y| ≤ r := (abs_lt.mpr hy).le
    rw [derivativeTerm, Real.norm_eq_abs, abs_div, abs_pow,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ n + 2)]
    have hn0 : (0 : ℝ) ≤ n := by positivity
    calc
      |y| ^ n / (n + 2 : ℝ) ≤ |y| ^ n := by
        exact div_le_self (pow_nonneg (abs_nonneg y) n) (by linarith)
      _ ≤ r ^ n := pow_le_pow_left₀ (abs_nonneg y) hay n
  have hbase : Summable (fun n : ℕ => seriesTerm 0 n) := by
    simp [seriesTerm]
  have hxmem : x ∈ Set.Ioo (-r) r := abs_lt.mp hxr
  have hzero : (0 : ℝ) ∈ Set.Ioo (-r) r := by
    constructor <;> linarith
  simpa only [F] using
    (hasDerivAt_tsum_of_isPreconnected
      (g := fun n y => seriesTerm y n)
      (g' := fun n y => derivativeTerm y n)
      (u := fun n : ℕ => r ^ n)
      (t := Set.Ioo (-r) r)
      (y₀ := (0 : ℝ))
      hu isOpen_Ioo isPreconnected_Ioo
      (fun n y _ => seriesTerm_hasDerivAt n y)
      hbound hzero hbase hxmem)

private theorem logarithmTerm_hasSum (x : ℝ) (hx : |x| < 1) :
    HasSum (logarithmTerm x) (-Real.log (1 - x)) := by
  simpa only [logarithmTerm] using
    Real.hasSum_pow_div_log_of_abs_lt_one hx

private theorem logarithmTail_hasSum (x : ℝ) (hx : |x| < 1) :
    HasSum (fun n => logarithmTerm x (n + 1))
      (-Real.log (1 - x) - x) := by
  simpa [logarithmTerm] using
    ((hasSum_nat_add_iff' 1).2 (logarithmTerm_hasSum x hx))

private theorem derivativeTerm_hasSum_closed
    (x : ℝ) (hx : |x| < 1) (hx0 : x ≠ 0) :
    HasSum (derivativeTerm x)
      ((1 / x ^ 2) * (-Real.log (1 - x) - x)) := by
  have hs := (logarithmTail_hasSum x hx).mul_left (1 / x ^ 2)
  apply hs.congr_fun
  intro n
  unfold derivativeTerm logarithmTerm
  field_simp [hx0]
  push_cast
  ring

private theorem seriesTerm_hasSum_closed
    (x : ℝ) (hx : |x| < 1) (hx0 : x ≠ 0) :
    HasSum (seriesTerm x)
      (1 + ((1 - x) / x) * Real.log (1 - x)) := by
  have hlog := logarithmTerm_hasSum x hx
  have htail :=
    (logarithmTail_hasSum x hx).mul_left (1 / x)
  have hs := hlog.sub htail
  convert hs using 1
  · funext n
    unfold seriesTerm logarithmTerm
    field_simp [hx0]
    push_cast
    ring
  · field_simp [hx0]
    ring

private theorem F_eq_closed
    (x : ℝ) (hx : |x| < 1) (hx0 : x ≠ 0) :
    F x = 1 + ((1 - x) / x) * Real.log (1 - x) := by
  exact (seriesTerm_hasSum_closed x hx hx0).tsum_eq

private theorem derivativeTerm_summable (x : ℝ) (hx : |x| < 1) :
    Summable (derivativeTerm x) := by
  have hnorm : ‖|x|‖ < 1 := by
    simpa [Real.norm_eq_abs] using hx
  have hg : Summable (fun n : ℕ => |x| ^ n) :=
    summable_geometric_of_norm_lt_one hnorm
  apply hg.of_norm_bounded
  intro n
  rw [derivativeTerm, Real.norm_eq_abs, abs_div, abs_pow,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ n + 2)]
  have hn0 : (0 : ℝ) ≤ n := by positivity
  exact div_le_self (pow_nonneg (abs_nonneg x) n) (by linarith)

private theorem integral_derivativeTerm (x : ℝ) (n : ℕ) :
    (∫ t in (0 : ℝ)..x, derivativeTerm t n) =
      seriesTerm x n := by
  unfold derivativeTerm seriesTerm
  rw [intervalIntegral.integral_div, integral_pow]
  norm_num
  field_simp

private theorem norm_derivativeTerm_le
    (x t : ℝ) (n : ℕ) (ht : t ∈ Set.uIcc 0 x) :
    ‖derivativeTerm t n‖ ≤ |x| ^ n / (n + 2 : ℝ) := by
  have habs : |t| ≤ |x| := by
    simpa using Set.abs_sub_left_of_mem_uIcc ht
  rw [derivativeTerm, Real.norm_eq_abs, abs_div, abs_pow,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ n + 2)]
  gcongr

private theorem derivativeIntegral_hasSum
    (x : ℝ) (hx : |x| < 1) :
    HasSum
      (fun n : ℕ => ∫ t in (0 : ℝ)..x, derivativeTerm t n)
      (∫ t in (0 : ℝ)..x, ∑' n, derivativeTerm t n) := by
  apply intervalIntegral.hasSum_integral_of_dominated_convergence
    (fun (n : ℕ) (_ : ℝ) => |x| ^ n / (n + 2 : ℝ))
  · intro n
    apply Continuous.aestronglyMeasurable
    unfold derivativeTerm
    fun_prop
  · intro n
    filter_upwards with t ht
    exact norm_derivativeTerm_le x t n (Set.uIoc_subset_uIcc ht)
  · filter_upwards with t ht
    have hs := derivativeTerm_summable |x| (by simpa using hx)
    simpa only [derivativeTerm, abs_abs] using hs
  · exact intervalIntegrable_const
  · filter_upwards with t ht
    exact (derivativeTerm_summable t
      (absLtOneOfMemUIcc hx (Set.uIoc_subset_uIcc ht))).hasSum

private theorem F_eq_integral_deriv (x : ℝ) (hx : |x| < 1) :
    F x = ∫ t in (0 : ℝ)..x, deriv F t := by
  calc
    F x =
        ∑' n : ℕ, ∫ t in (0 : ℝ)..x, derivativeTerm t n := by
      rw [F]
      apply tsum_congr
      intro n
      exact (integral_derivativeTerm x n).symm
    _ = ∫ t in (0 : ℝ)..x, ∑' n, derivativeTerm t n :=
      (derivativeIntegral_hasSum x hx).tsum_eq
    _ = ∫ t in (0 : ℝ)..x, deriv F t := by
      apply intervalIntegral.integral_congr
      intro t ht
      exact
        (F_hasDerivAt_series t
          (absLtOneOfMemUIcc hx ht)).deriv.symm

private theorem seriesTerm_one_summable :
    Summable (seriesTerm 1) := by
  have hp :
      Summable (fun n : ℕ => 1 / ((n + 1 : ℝ) ^ 2)) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      ((summable_nat_add_iff 1).2
        (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2)))
  apply hp.of_norm_bounded
  intro n
  rw [seriesTerm, Real.norm_eq_abs, one_pow,
    abs_div, abs_one, abs_of_nonneg (by positivity :
      (0 : ℝ) ≤ (n + 1) * (n + 2))]
  have hn1 : (0 : ℝ) < n + 1 := by positivity
  have hn2 : (0 : ℝ) < n + 2 := by positivity
  exact
    one_div_le_one_div_of_le (sq_pos_of_pos hn1) (by
      nlinarith)

private theorem seriesTerm_one_hasSum :
    HasSum (seriesTerm 1) 1 := by
  apply seriesTerm_one_summable.hasSum_iff_tendsto_nat.mpr
  have hpartial (n : ℕ) :
      (∑ i ∈ Finset.range n, seriesTerm 1 i) =
        1 - 1 / (((n + 1 : ℕ) : ℝ)) := by
    calc
      (∑ i ∈ Finset.range n, seriesTerm 1 i) =
          ∑ i ∈ Finset.range n,
            (1 / (((i + 1 : ℕ) : ℝ)) -
              1 / (((i + 2 : ℕ) : ℝ))) := by
        apply Finset.sum_congr rfl
        intro i hi
        unfold seriesTerm
        norm_num
        field_simp
        ring
      _ = 1 / (((0 + 1 : ℕ) : ℝ)) -
          1 / (((n + 1 : ℕ) : ℝ)) := by
        simpa [Nat.add_assoc] using
          (Finset.sum_range_sub'
            (fun i : ℕ => 1 / (((i + 1 : ℕ) : ℝ))) n)
      _ = 1 - 1 / (((n + 1 : ℕ) : ℝ)) := by norm_num
  have hcast :
      Tendsto (fun n : ℕ => (((n + 1 : ℕ) : ℝ)))
        Filter.atTop Filter.atTop :=
    tendsto_natCast_atTop_atTop.comp (Filter.tendsto_add_atTop_nat 1)
  have hinv :
      Tendsto (fun n : ℕ => 1 / (((n + 1 : ℕ) : ℝ)))
        Filter.atTop (nhds 0) := by
    simpa only [one_div] using tendsto_inv_atTop_zero.comp hcast
  simpa only [hpartial, sub_zero] using tendsto_const_nhds.sub hinv

private theorem seriesTerm_neg_one_summable :
    Summable (seriesTerm (-1)) := by
  apply Summable.of_norm
  convert seriesTerm_one_summable using 1
  funext n
  unfold seriesTerm
  rw [Real.norm_eq_abs, abs_div, abs_pow,
    abs_of_nonneg (by positivity :
      (0 : ℝ) ≤ (n + 1) * (n + 2))]
  norm_num

private theorem seriesTerm_neg_one_hasSum :
    HasSum (seriesTerm (-1)) (1 - 2 * Real.log 2) := by
  have hpartial :
      Tendsto
        (fun n : ℕ =>
          ∑ i ∈ Finset.range n, seriesTerm (-1) i)
        Filter.atTop (nhds (∑' n, seriesTerm (-1) n)) :=
    seriesTerm_neg_one_summable.hasSum_iff_tendsto_nat.mp
      seriesTerm_neg_one_summable.hasSum
  have hAbel :=
    Real.tendsto_tsum_powerSeries_nhdsWithin_lt hpartial
  have hpower (r : ℝ) (hr : r ≠ 0) :
      (∑' n : ℕ, seriesTerm (-1) n * r ^ n) =
        (1 / r) * F (-r) := by
    rw [F, ← tsum_mul_left]
    apply tsum_congr
    intro n
    unfold seriesTerm
    rw [neg_pow]
    field_simp [hr]
    ring
  let H : ℝ → ℝ :=
    fun r =>
      (1 / r) *
        (1 + ((1 - (-r)) / (-r)) * Real.log (1 - (-r)))
  have heq :
      (fun r : ℝ =>
        ∑' n : ℕ, seriesTerm (-1) n * r ^ n) =ᶠ[
          nhdsWithin 1 (Set.Iio 1)] H := by
    filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)]
      with r hr
    rw [hpower r hr.1.ne']
    have habs : |-r| < 1 := by
      rw [abs_neg, abs_of_pos hr.1]
      exact hr.2
    rw [F_eq_closed (-r) habs (neg_ne_zero.mpr hr.1.ne')]
  have hHcont : ContinuousAt H 1 := by
    dsimp [H]
    fun_prop (disch := norm_num)
  have hH1 : H 1 = 1 - 2 * Real.log 2 := by
    norm_num [H]
    ring
  have hH :
      Tendsto H (nhdsWithin 1 (Set.Iio 1))
        (nhds (1 - 2 * Real.log 2)) := by
    rw [← hH1]
    exact hHcont.tendsto.mono_left inf_le_left
  have hpower_limit :
      Tendsto
        (fun r : ℝ =>
          ∑' n : ℕ, seriesTerm (-1) n * r ^ n)
        (nhdsWithin 1 (Set.Iio 1))
        (nhds (1 - 2 * Real.log 2)) :=
    hH.congr' heq.symm
  have hvalue :
      (∑' n, seriesTerm (-1) n) = 1 - 2 * Real.log 2 :=
    tendsto_nhds_unique hAbel hpower_limit
  rw [← hvalue]
  exact seriesTerm_neg_one_summable.hasSum

theorem gap1 :
    ∀ x : ℝ, |x| < 1 →
      deriv F x = ∑' n, derivativeTerm x n := by
  intro x hx
  exact (F_hasDerivAt_series x hx).deriv

theorem gap2 :
    ∀ x : ℝ, 0 < |x| → |x| < 1 →
      deriv F x =
        -(1 / x) + (1 / x ^ 2) * ∑' n, logarithmTerm x n := by
  intro x hx0 hx
  have hxn : x ≠ 0 := abs_pos.mp hx0
  rw [(F_hasDerivAt_series x hx).deriv,
    (derivativeTerm_hasSum_closed x hx hxn).tsum_eq,
    (logarithmTerm_hasSum x hx).tsum_eq]
  field_simp [hxn]
  ring

theorem gap3 :
    ∀ x : ℝ, 0 < |x| → |x| < 1 →
      deriv F x =
        -(1 / x) + (1 / x ^ 2) * (-Real.log (1 - x)) := by
  intro x hx0 hx
  have hxn : x ≠ 0 := abs_pos.mp hx0
  rw [(F_hasDerivAt_series x hx).deriv,
    (derivativeTerm_hasSum_closed x hx hxn).tsum_eq]
  field_simp [hxn]
  ring

theorem gap4 :
    F 0 = 0 := by
  simp [F, seriesTerm]

theorem gap5 :
    ∀ x : ℝ, |x| < 1 →
      F x = ∫ t in (0 : ℝ)..x, deriv F t := by
  intro x hx
  exact F_eq_integral_deriv x hx

theorem gap6 :
    ∀ x : ℝ, 0 < |x| → |x| < 1 →
      (∫ t in (0 : ℝ)..x, deriv F t) =
        1 + ((1 - x) / x) * Real.log (1 - x) := by
  intro x hx0 hx
  exact (F_eq_integral_deriv x hx).symm.trans
    (F_eq_closed x hx (abs_pos.mp hx0))

theorem gap7 :
    ∀ x : ℝ, 0 < |x| → |x| < 1 →
      F x = 1 + ((1 - x) / x) * Real.log (1 - x) := by
  intro x hx0 hx
  exact F_eq_closed x hx (abs_pos.mp hx0)

theorem gap8 :
    ∀ x : ℝ, |x| ≤ 1 →
      (∑' n, seriesTerm x n) = closedForm x := by
  intro x hx
  by_cases hx0 : x = 0
  · subst x
    simp [closedForm, seriesTerm]
  by_cases hxm1 : x = -1
  · subst x
    simp [closedForm, seriesTerm_neg_one_hasSum.tsum_eq]
  by_cases hx1 : x = 1
  · subst x
    rw [seriesTerm_one_hasSum.tsum_eq]
    norm_num [closedForm]
  have habs_ne : |x| ≠ 1 := by
    intro habs
    by_cases hnonneg : 0 ≤ x
    · rw [abs_of_nonneg hnonneg] at habs
      exact hx1 habs
    · have hnonpos : x ≤ 0 := le_of_not_ge hnonneg
      rw [abs_of_nonpos hnonpos] at habs
      apply hxm1
      linarith
  have hlt : |x| < 1 := lt_of_le_of_ne hx habs_ne
  rw [closedForm, if_neg hx0, if_neg hxm1, if_neg hx1]
  exact (seriesTerm_hasSum_closed x hlt hx0).tsum_eq

end

end ProofGap.Exercise2909
