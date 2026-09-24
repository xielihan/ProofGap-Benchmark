import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Topology.Defs.Filter
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

namespace ProofGap.Exercise2191
noncomputable section

open Filter
open scoped BigOperators Interval

def q (a b : ℝ) (n : ℕ) : ℝ :=
  Real.rpow (b / a) (1 / (n : ℝ))

def sumInv (a b : ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range n,
    (a * q a b n ^ i)⁻¹ *
      (a * q a b n ^ (i + 1) - a * q a b n ^ i)

def rootDifference (a b : ℝ) (n : ℕ) : ℝ :=
  (n : ℝ) * (q a b n - 1)

theorem gap1 (a b : ℝ) (n : ℕ)
    (ha : 0 < a) (hab : a < b) (hn : 0 < n) :
    sumInv a b n =
      ∑ i ∈ Finset.range n,
        (a * q a b n ^ i)⁻¹ *
          (a * q a b n ^ (i + 1) - a * q a b n ^ i) := by
  rfl

theorem gap2 (a b : ℝ) (n : ℕ)
    (ha : 0 < a) (hab : a < b) (hn : 0 < n) :
    (∑ i ∈ Finset.range n,
        (a * q a b n ^ i)⁻¹ *
          (a * q a b n ^ (i + 1) - a * q a b n ^ i)) =
      (n : ℝ) * (q a b n - 1) := by
  have hb : 0 < b := lt_trans ha hab
  have hba : 0 < b / a := div_pos hb ha
  have hq : 0 < q a b n := by
    exact Real.rpow_pos_of_pos hba _
  calc
    (∑ i ∈ Finset.range n,
        (a * q a b n ^ i)⁻¹ *
          (a * q a b n ^ (i + 1) - a * q a b n ^ i)) =
        ∑ i ∈ Finset.range n, (q a b n - 1) := by
          apply Finset.sum_congr rfl
          intro i hi
          have hqi : a * q a b n ^ i ≠ 0 :=
            mul_ne_zero ha.ne' (pow_ne_zero i hq.ne')
          rw [pow_succ]
          calc
            (a * q a b n ^ i)⁻¹ *
                (a * (q a b n ^ i * q a b n) - a * q a b n ^ i) =
              (a * q a b n ^ i)⁻¹ *
                ((a * q a b n ^ i) * (q a b n - 1)) := by ring
            _ = q a b n - 1 := by
              rw [← mul_assoc, inv_mul_cancel₀ hqi, one_mul]
    _ = (n : ℝ) * (q a b n - 1) := by
      simp [mul_sub]

theorem gap3 (a b : ℝ) (n : ℕ)
    (ha : 0 < a) (hab : a < b) (hn : 0 < n) :
    (n : ℝ) * (q a b n - 1) =
      (n : ℝ) * (Real.rpow (b / a) (1 / (n : ℝ)) - 1) := by
  rfl

theorem gap4 (a b : ℝ) (n : ℕ)
    (ha : 0 < a) (hab : a < b) (hn : 0 < n) :
    sumInv a b n =
      (n : ℝ) * (Real.rpow (b / a) (1 / (n : ℝ)) - 1) := by
  calc
    sumInv a b n =
        ∑ i ∈ Finset.range n,
          (a * q a b n ^ i)⁻¹ *
            (a * q a b n ^ (i + 1) - a * q a b n ^ i) :=
      gap1 a b n ha hab hn
    _ = (n : ℝ) * (q a b n - 1) := gap2 a b n ha hab hn
    _ = (n : ℝ) * (Real.rpow (b / a) (1 / (n : ℝ)) - 1) :=
      gap3 a b n ha hab hn

theorem gap5 (α : ℝ) (hα : 0 < α) :
    Tendsto (fun t : ℝ => (Real.rpow α t - 1) / t)
      (nhdsWithin 0 ({0}ᶜ : Set ℝ)) (nhds (Real.log α)) := by
  have hderivExp :
      HasDerivAt (fun t : ℝ => Real.exp (Real.log α * t))
        (Real.log α) 0 := by
    simpa [Function.comp_def] using
      (Real.hasDerivAt_exp (Real.log α * 0)).comp 0
        ((hasDerivAt_id 0).const_mul (Real.log α))
  have hderiv :
      HasDerivAt (fun t : ℝ => Real.rpow α t) (Real.log α) 0 := by
    simpa [Real.rpow_def_of_pos hα] using hderivExp
  refine (hasDerivAt_iff_tendsto_slope.mp hderiv).congr' ?_
  exact Filter.Eventually.of_forall (fun t => by
    simp [slope, div_eq_mul_inv, mul_comm])

theorem gap6 (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    Tendsto (sumInv a b) atTop (nhds (Real.log (b / a))) ↔
      Tendsto (rootDifference a b) atTop (nhds (Real.log (b / a))) := by
  have heq :
      (fun n => sumInv a b n) =ᶠ[atTop]
        (fun n => rootDifference a b n) := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    simpa [rootDifference, q] using gap4 a b n ha hab hn
  exact tendsto_congr' heq

theorem gap7 (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    Tendsto (rootDifference a b) atTop (nhds (Real.log (b / a))) := by
  have hb : 0 < b := lt_trans ha hab
  have hba : 0 < b / a := div_pos hb ha
  have ht0 :
      Tendsto (fun n : ℕ => 1 / (n : ℝ)) atTop (nhds 0) := by
    simpa [one_div] using
      (tendsto_inv_atTop_zero.comp
        (tendsto_natCast_atTop_atTop :
          Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop))
  have ht :
      Tendsto (fun n : ℕ => 1 / (n : ℝ)) atTop
        (nhdsWithin 0 ({0}ᶜ : Set ℝ)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨ht0, ?_⟩
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    have hnR : (n : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
    simpa [one_div] using inv_ne_zero hnR
  have hcomp := (gap5 (b / a) hba).comp ht
  apply hcomp.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  have hnR : (n : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  have halg :
      (Real.rpow (b / a) (1 / (n : ℝ)) - 1) / (1 / (n : ℝ)) =
        (n : ℝ) * (Real.rpow (b / a) (1 / (n : ℝ)) - 1) := by
    field_simp [hnR]
  simpa [rootDifference, q] using halg

theorem gap8 (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    Tendsto (sumInv a b) atTop (nhds (Real.log (b / a))) := by
  exact (gap6 a b ha hab).mpr (gap7 a b ha hab)

theorem gap9 (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    (∫ x in a..b, 1 / x) = Real.log (b / a) := by
  have hzero : (0 : ℝ) ∉ Set.uIcc a b := by
    rw [Set.uIcc_of_le hab.le]
    exact fun h => (not_le_of_gt ha) h.1
  calc
    (∫ x in a..b, 1 / x) = Real.log b - Real.log a := by
      apply intervalIntegral.integral_eq_sub_of_hasDerivAt
      · intro x hx
        have hx0 : x ≠ 0 := by
          intro hxeq
          apply hzero
          simpa [hxeq] using hx
        simpa [one_div] using Real.hasDerivAt_log hx0
      · have hone :
            ContinuousOn (fun _ : ℝ => (1 : ℝ)) (Set.uIcc a b) :=
          continuousOn_const
        have hid :
            ContinuousOn (fun x : ℝ => x) (Set.uIcc a b) :=
          continuousOn_id
        have hcont :
            ContinuousOn (fun x : ℝ => 1 / x) (Set.uIcc a b) := by
          exact hone.div hid (fun x hx => by
            intro hxeq
            apply hzero
            simpa [hxeq] using hx)
        exact hcont.intervalIntegrable
    _ = Real.log (b / a) := by
      have hb : 0 < b := lt_trans ha hab
      rw [Real.log_div hb.ne' ha.ne']

end
end ProofGap.Exercise2191
