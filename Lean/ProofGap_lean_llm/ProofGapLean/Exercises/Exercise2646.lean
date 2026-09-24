import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Analysis.PSeries
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Lean.Elab.Tactic.Omega

namespace ProofGap.Exercise2646

noncomputable section

open scoped Interval

def integrand (x : ℝ) : ℝ :=
  Real.sqrt x / (1 + x ^ 2)

def u (n : ℕ) : ℝ :=
  ∫ x in (0 : ℝ)..1 / n, integrand x

def majorant (n : ℕ) : ℝ :=
  Real.rpow n (-(3 / 2 : ℝ))

private theorem sqrt_one_div_nat_eq_rpow (n : ℕ) (hn : 1 ≤ n) :
    Real.sqrt (1 / (n : ℝ)) = Real.rpow n (-(1 / 2 : ℝ)) := by
  rw [Real.sqrt_eq_rpow]
  rw [Real.div_rpow (by norm_num : (0 : ℝ) ≤ 1) (Nat.cast_nonneg n)]
  rw [Real.one_rpow]
  have hneg : Real.rpow (n : ℝ) (-(1 / 2 : ℝ)) =
      (Real.rpow (n : ℝ) (1 / 2 : ℝ))⁻¹ := by
    exact Real.rpow_neg (Nat.cast_nonneg n) (1 / 2 : ℝ)
  simpa [one_div] using hneg.symm

theorem gap1 :
    ∀ n : ℕ, 1 ≤ n → 0 < u n := by
  intro n hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by
    exact_mod_cast (show 0 < n from hn)
  have hab : (0 : ℝ) < 1 / (n : ℝ) := by positivity
  have hcont : Continuous integrand := by
    unfold integrand
    exact Real.continuous_sqrt.div
      (continuous_const.add (continuous_id.pow 2))
      (fun x => by nlinarith [sq_nonneg x])
  unfold u
  refine intervalIntegral.integral_pos hab hcont.continuousOn ?_ ?_
  · intro x hx
    unfold integrand
    exact div_nonneg (Real.sqrt_nonneg x) (by nlinarith [sq_nonneg x])
  · refine ⟨1 / (n : ℝ), ⟨hab.le, le_rfl⟩, ?_⟩
    unfold integrand
    exact div_pos (Real.sqrt_pos.2 hab)
      (by nlinarith [sq_nonneg (1 / (n : ℝ))])

theorem gap2 :
    ∀ n : ℕ, 1 ≤ n →
      u n ≤ ∫ _x in (0 : ℝ)..1 / n, Real.rpow n (-(1 / 2 : ℝ)) := by
  intro n hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by
    exact_mod_cast (show 0 < n from hn)
  have hab : (0 : ℝ) < 1 / (n : ℝ) := by positivity
  have hcont : Continuous integrand := by
    unfold integrand
    exact Real.continuous_sqrt.div
      (continuous_const.add (continuous_id.pow 2))
      (fun x => by nlinarith [sq_nonneg x])
  have hconst : Continuous (fun _x : ℝ => Real.rpow n (-(1 / 2 : ℝ))) :=
    continuous_const
  unfold u
  refine intervalIntegral.integral_mono_on hab.le
    (hcont.intervalIntegrable 0 (1 / (n : ℝ)))
    (hconst.intervalIntegrable 0 (1 / (n : ℝ))) ?_
  intro x hx
  have hxn : x ≤ 1 / (n : ℝ) := hx.2
  calc
    integrand x = Real.sqrt x / (1 + x ^ 2) := rfl
    _ ≤ Real.sqrt x := div_le_self (Real.sqrt_nonneg x) (by nlinarith [sq_nonneg x])
    _ ≤ Real.sqrt (1 / (n : ℝ)) := Real.sqrt_le_sqrt hxn
    _ = Real.rpow n (-(1 / 2 : ℝ)) := sqrt_one_div_nat_eq_rpow n hn

theorem gap3 :
    ∀ n : ℕ, 1 ≤ n →
      (∫ _x in (0 : ℝ)..1 / n, Real.rpow n (-(1 / 2 : ℝ))) =
        majorant n := by
  intro n hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by
    exact_mod_cast (show 0 < n from hn)
  have hnegone : Real.rpow (n : ℝ) (-1 : ℝ) = (n : ℝ)⁻¹ := by
    have hneg : Real.rpow (n : ℝ) (-(1 : ℝ)) =
        (Real.rpow (n : ℝ) (1 : ℝ))⁻¹ := by
      exact Real.rpow_neg (Nat.cast_nonneg n) (1 : ℝ)
    simpa using hneg
  have hadd :
      Real.rpow (n : ℝ) ((-1 : ℝ) + -(1 / 2 : ℝ)) =
        Real.rpow (n : ℝ) (-1 : ℝ) * Real.rpow (n : ℝ) (-(1 / 2 : ℝ)) := by
    exact Real.rpow_add hn0 (-1 : ℝ) (-(1 / 2 : ℝ))
  calc
    (∫ _x in (0 : ℝ)..1 / n, Real.rpow n (-(1 / 2 : ℝ))) =
        (1 / (n : ℝ)) * Real.rpow n (-(1 / 2 : ℝ)) := by simp
    _ = (n : ℝ)⁻¹ * Real.rpow n (-(1 / 2 : ℝ)) := by rw [one_div]
    _ = Real.rpow n (-1 : ℝ) * Real.rpow n (-(1 / 2 : ℝ)) := by
      rw [hnegone]
    _ = Real.rpow n ((-1 : ℝ) + -(1 / 2 : ℝ)) := hadd.symm
    _ = majorant n := by
      unfold majorant
      congr 1
      norm_num

theorem gap4 :
    ∀ n : ℕ, 1 ≤ n → 0 < majorant n := by
  intro n hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by
    exact_mod_cast (show 0 < n from hn)
  unfold majorant
  exact Real.rpow_pos_of_pos hn0 _

theorem gap5 :
    Summable (fun n : ℕ => majorant (n + 1)) := by
  rw [summable_nat_add_iff 1]
  unfold majorant
  change Summable (fun n : ℕ => (n : ℝ) ^ (-(3 / 2 : ℝ)))
  exact (Real.summable_nat_rpow (p := -(3 / 2 : ℝ))).2 (by norm_num)

theorem gap6
    (hpos : ∀ n : ℕ, 1 ≤ n → 0 ≤ u n)
    (hbound : ∀ n : ℕ, 1 ≤ n → u n ≤ majorant n)
    (hmajorant : Summable (fun n : ℕ => majorant (n + 1))) :
    Summable (fun n : ℕ => u (n + 1)) := by
  apply Summable.of_nonneg_of_le
  · intro n
    exact hpos (n + 1) (by omega)
  · intro n
    exact hbound (n + 1) (by omega)
  · exact hmajorant

theorem gap7
    (hsum : Summable (fun n : ℕ => u (n + 1))) :
    Summable (fun n : ℕ => u (n + 1)) := by
  exact hsum

end

end ProofGap.Exercise2646
