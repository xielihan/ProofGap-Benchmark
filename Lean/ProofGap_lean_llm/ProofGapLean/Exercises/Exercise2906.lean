import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.Algebra.InfiniteSum.Basic

namespace ProofGap.Exercise2906

noncomputable section

open scoped BigOperators Interval

def seriesTerm (x : ℝ) (n : ℕ) : ℝ :=
  x ^ (2 * n + 1) / (2 * n + 1 : ℝ)

def derivativeTerm (x : ℝ) (n : ℕ) : ℝ :=
  x ^ (2 * n)

def F (x : ℝ) : ℝ :=
  ∑' n, seriesTerm x n

private theorem absLtOneOfMemUIcc {x t : ℝ} (hx : |x| < 1)
    (ht : t ∈ Set.uIcc (0 : ℝ) x) : |t| < 1 := by
  rcases Set.mem_uIcc.mp ht with h | h
  · rw [abs_of_nonneg h.1]
    exact lt_of_le_of_lt (h.2.trans (le_abs_self x)) hx
  · have hx0 : x ≤ 0 := h.1.trans h.2
    rw [abs_of_nonpos h.2, abs_of_nonpos hx0] at *
    linarith

private theorem derivativeTerm_hasSum (x : ℝ) (hx : |x| < 1) :
    HasSum (derivativeTerm x) (1 / (1 - x ^ 2)) := by
  have hnormx : ‖x‖ < 1 := by
    simpa [Real.norm_eq_abs] using hx
  have hnorm : ‖x ^ 2‖ < 1 := by
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg x) hnormx (by norm_num)
  convert (hasSum_geometric_of_norm_lt_one hnorm) using 1
  · funext n
    unfold derivativeTerm
    rw [pow_mul]
  · rw [one_div]

private theorem seriesTerm_hasSum_halfLog (x : ℝ) (hx : |x| < 1) :
    HasSum (seriesTerm x)
      ((1 / 2 : ℝ) * Real.log ((1 + x) / (1 - x))) := by
  have hs :=
    (Real.hasSum_log_sub_log_of_abs_lt_one hx).mul_left (1 / 2 : ℝ)
  have hI := abs_lt.mp hx
  have hplus : 1 + x ≠ 0 := by linarith
  have hminus : 1 - x ≠ 0 := by linarith
  convert hs using 1
  · funext n
    unfold seriesTerm
    ring
  · rw [Real.log_div hplus hminus]

private theorem F_eq_halfLog (x : ℝ) (hx : |x| < 1) :
    F x = (1 / 2 : ℝ) * Real.log ((1 + x) / (1 - x)) := by
  exact (seriesTerm_hasSum_halfLog x hx).tsum_eq

private theorem halfLog_hasDerivAt (x : ℝ) (hx : |x| < 1) :
    HasDerivAt
      (fun y : ℝ => (1 / 2 : ℝ) * Real.log ((1 + y) / (1 - y)))
      (1 / (1 - x ^ 2)) x := by
  have hI := abs_lt.mp hx
  simpa using
    (Real.hasDerivAt_half_log_one_add_div_one_sub_sub_sum_range
      0 hI.1 hI.2)

private theorem F_hasDerivAt (x : ℝ) (hx : |x| < 1) :
    HasDerivAt F (1 / (1 - x ^ 2)) x := by
  refine (halfLog_hasDerivAt x hx).congr_of_eventuallyEq ?_
  filter_upwards [Ioo_mem_nhds (abs_lt.mp hx).1 (abs_lt.mp hx).2]
    with y hy
  exact F_eq_halfLog y (abs_lt.mpr hy)

private theorem integral_one_div_one_sub_sq (x : ℝ) (hx : |x| < 1) :
    (∫ t in (0 : ℝ)..x, 1 / (1 - t ^ 2)) =
      (1 / 2 : ℝ) * Real.log ((1 + x) / (1 - x)) := by
  have hderiv :
      ∀ t ∈ Set.uIcc (0 : ℝ) x,
        HasDerivAt
          (fun y : ℝ =>
            (1 / 2 : ℝ) * Real.log ((1 + y) / (1 - y)))
          (1 / (1 - t ^ 2)) t := by
    intro t ht
    exact halfLog_hasDerivAt t (absLtOneOfMemUIcc hx ht)
  have hcont :
      ContinuousOn (fun t : ℝ => 1 / (1 - t ^ 2))
        (Set.uIcc (0 : ℝ) x) := by
    apply continuousOn_const.div
      (continuousOn_const.sub (continuousOn_id.pow 2))
    intro t ht
    have htlt := absLtOneOfMemUIcc hx ht
    have hsq : t ^ 2 < 1 := by
      rw [← sq_abs]
      exact pow_lt_one₀ (abs_nonneg t) htlt (by norm_num)
    simpa only [id_eq] using (ne_of_gt (sub_pos.mpr hsq))
  have hFTC :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      hderiv hcont.intervalIntegrable
  simpa using hFTC

theorem gap1 :
    ∀ x : ℝ, |x| < 1 →
      deriv F x = ∑' n, derivativeTerm x n := by
  intro x hx
  rw [(F_hasDerivAt x hx).deriv]
  exact (derivativeTerm_hasSum x hx).tsum_eq.symm

theorem gap2 :
    ∀ x : ℝ, |x| < 1 →
      (∑' n, derivativeTerm x n) = 1 / (1 - x ^ 2) := by
  intro x hx
  exact (derivativeTerm_hasSum x hx).tsum_eq

theorem gap3 :
    ∀ x : ℝ, |x| < 1 →
      deriv F x = 1 / (1 - x ^ 2) := by
  intro x hx
  exact (F_hasDerivAt x hx).deriv

theorem gap4 :
    F 0 = 0 := by
  simp [F, seriesTerm]

theorem gap5 :
    ∀ x : ℝ, |x| < 1 →
      F x = ∫ t in (0 : ℝ)..x, deriv F t := by
  intro x hx
  rw [F_eq_halfLog x hx, ← integral_one_div_one_sub_sq x hx]
  apply intervalIntegral.integral_congr
  intro t ht
  exact (F_hasDerivAt t (absLtOneOfMemUIcc hx ht)).deriv.symm

theorem gap6 :
    ∀ x : ℝ, |x| < 1 →
      F x = ∫ t in (0 : ℝ)..x, 1 / (1 - t ^ 2) := by
  intro x hx
  rw [F_eq_halfLog x hx, ← integral_one_div_one_sub_sq x hx]

theorem gap7 :
    ∀ x : ℝ, |x| < 1 →
      (∫ t in (0 : ℝ)..x, 1 / (1 - t ^ 2)) =
        (1 / 2 : ℝ) * Real.log ((1 + x) / (1 - x)) := by
  exact integral_one_div_one_sub_sq

theorem gap8 :
    ∀ x : ℝ, |x| < 1 →
      F x = (1 / 2 : ℝ) * Real.log ((1 + x) / (1 - x)) := by
  exact F_eq_halfLog

theorem gap9 :
    ∀ x : ℝ, |x| < 1 →
      (∑' n, seriesTerm x n) =
        (1 / 2 : ℝ) * Real.log ((1 + x) / (1 - x)) := by
  intro x hx
  exact (seriesTerm_hasSum_halfLog x hx).tsum_eq

end

end ProofGap.Exercise2906
