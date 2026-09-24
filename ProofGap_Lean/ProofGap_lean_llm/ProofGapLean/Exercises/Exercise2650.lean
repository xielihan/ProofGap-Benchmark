import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic

namespace ProofGap.Exercise2650

noncomputable section

open scoped Interval

def integrand (x : ℝ) : ℝ :=
  Real.sin x ^ 3 / (1 + x)

def u (n : ℕ) : ℝ :=
  ∫ x in (0 : ℝ)..Real.pi / n, integrand x

def majorant (n : ℕ) : ℝ :=
  (Real.pi / n) ^ 4

private theorem upper_le_pi (n : ℕ) (hn : 1 ≤ n) :
    Real.pi / n ≤ Real.pi := by
  have hnreal : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  exact div_le_self Real.pi_pos.le hnreal

private theorem integrand_nonneg_on (n : ℕ) (hn : 1 ≤ n)
    {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) (Real.pi / n)) :
    0 ≤ integrand x := by
  have hxpi : x ≤ Real.pi := hx.2.trans (upper_le_pi n hn)
  have hsin : 0 ≤ Real.sin x :=
    Real.sin_nonneg_of_nonneg_of_le_pi hx.1 hxpi
  unfold integrand
  exact div_nonneg (pow_nonneg hsin 3) (by linarith [hx.1])

private theorem continuousOn_integrand (n : ℕ) :
    ContinuousOn integrand (Set.Icc (0 : ℝ) (Real.pi / n)) := by
  intro x hx
  have hden : (1 + x : ℝ) ≠ 0 := by linarith [hx.1]
  unfold integrand
  exact ((Real.continuous_sin.continuousAt.pow 3).div
    ((continuous_const.add continuous_id).continuousAt) hden).continuousWithinAt

theorem gap1 :
    ∀ n : ℕ, 1 ≤ n → ∀ x ∈ Set.Icc (0 : ℝ) (Real.pi / n),
      integrand x ≤ x ^ 3 := by
  intro n hn x hx
  have hxpi : x ≤ Real.pi := hx.2.trans (upper_le_pi n hn)
  have hsin_nonneg : 0 ≤ Real.sin x :=
    Real.sin_nonneg_of_nonneg_of_le_pi hx.1 hxpi
  have hsin_le : Real.sin x ≤ x := Real.sin_le hx.1
  have hsin_pow : Real.sin x ^ 3 ≤ x ^ 3 := by
    gcongr
  have hden : 0 < 1 + x := by linarith [hx.1]
  rw [integrand, div_le_iff₀ hden]
  calc
    Real.sin x ^ 3 ≤ x ^ 3 := hsin_pow
    _ ≤ x ^ 3 * (1 + x) := by
      have hxpow : 0 ≤ x ^ 3 := pow_nonneg hx.1 3
      nlinarith

theorem gap2 :
    ∀ n : ℕ, 1 ≤ n → 0 ≤ u n := by
  intro n hn
  unfold u
  exact intervalIntegral.integral_nonneg (by positivity)
    (fun x hx => integrand_nonneg_on n hn hx)

theorem gap3 :
    ∀ n : ℕ, 1 ≤ n →
      u n ≤ ∫ x in (0 : ℝ)..Real.pi / n, x ^ 3 := by
  intro n hn
  have hinterval : (0 : ℝ) ≤ Real.pi / n := by positivity
  unfold u
  exact intervalIntegral.integral_mono_on hinterval
    ((continuousOn_integrand n).intervalIntegrable_of_Icc hinterval)
    ((continuous_id.pow 3).intervalIntegrable _ _)
    (fun x hx => gap1 n hn x hx)

theorem gap4 :
    ∀ n : ℕ, 1 ≤ n →
      (∫ x in (0 : ℝ)..Real.pi / n, x ^ 3) =
        majorant n / 4 ∧
      majorant n / 4 ≤ majorant n := by
  intro n hn
  constructor
  · rw [integral_pow]
    norm_num [majorant]
  · have hmajorant : 0 ≤ majorant n := by
      unfold majorant
      positivity
    nlinarith

theorem gap5 :
    ∀ n : ℕ, 0 ≤ majorant n := by
  intro n
  unfold majorant
  positivity

theorem gap6 :
    Summable (fun n : ℕ => majorant (n + 1)) := by
  have hfull : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 4) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  have hshift : Summable (fun n : ℕ => 1 / ((n + 1 : ℕ) : ℝ) ^ 4) :=
    (summable_nat_add_iff 1).mpr hfull
  have h := hshift.mul_left (Real.pi ^ 4)
  simpa [majorant, div_eq_mul_inv, mul_pow] using h

theorem gap7
    (hpos : ∀ n : ℕ, 1 ≤ n → 0 ≤ u n)
    (hbound : ∀ n : ℕ, 1 ≤ n → u n ≤ majorant n)
    (hmajorant : Summable (fun n : ℕ => majorant (n + 1))) :
    Summable (fun n : ℕ => u (n + 1)) := by
  exact hmajorant.of_nonneg_of_le
    (fun n => hpos (n + 1) (by omega))
    (fun n => hbound (n + 1) (by omega))

theorem gap8
    (hsum : Summable (fun n : ℕ => u (n + 1))) :
    Summable (fun n : ℕ => u (n + 1)) := by
  exact hsum

end

end ProofGap.Exercise2650
