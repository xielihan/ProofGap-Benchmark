import ProofGapLean.Prelude.Analysis
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Neighborhoods

namespace ProofGap.Exercise3061

noncomputable section

open Filter
open scoped BigOperators Topology

def factor (n : ℕ) : ℝ :=
  ((n : ℝ) ^ 2 - 4) / ((n : ℝ) ^ 2 - 1)

def partialProduct (n : ℕ) : ℝ :=
  ∏ i ∈ Finset.Icc 3 n, factor i

def ConvergentProduct : Prop :=
  ∃ L : ℝ, Tendsto partialProduct atTop (𝓝 L)

def HasProduct (L : ℝ) : Prop :=
  Tendsto partialProduct atTop (𝓝 L)

/-- Source: `proof_gap/exercise_3061/1.txt`; the product ellipsis is `partialProduct`. -/
theorem gap1 (P : ℕ → ℝ) (hP : ∀ n, P n = partialProduct n) :
    ∀ n, P n = partialProduct n := by
  exact hP

/-- Source: `proof_gap/exercise_3061/2.txt`; the formula is for `n ≥ 3`. -/
theorem gap2 :
    ∀ n : ℕ, 3 ≤ n →
      partialProduct n = ((n : ℝ) + 2) / (4 * ((n : ℝ) - 1)) := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base =>
      norm_num [partialProduct, factor]
  | succ n hn ih =>
      have hset :
          Finset.Icc 3 (n + 1) =
            insert (n + 1) (Finset.Icc 3 n) := by
        ext i
        simp only [Finset.mem_Icc, Finset.mem_insert]
        omega
      have hnot : n + 1 ∉ Finset.Icc 3 n := by
        simp [Finset.mem_Icc]
      have hprod :
          partialProduct (n + 1) = factor (n + 1) * partialProduct n := by
        change
          (∏ i ∈ Finset.Icc 3 (n + 1), factor i) =
            factor (n + 1) * ∏ i ∈ Finset.Icc 3 n, factor i
        rw [hset, Finset.prod_insert hnot]
      rw [hprod, ih]
      simp only [factor, Nat.cast_add, Nat.cast_one]
      have hnR : (3 : ℝ) ≤ (n : ℝ) := by
        exact_mod_cast hn
      have hx : (n : ℝ) ≠ 0 := by
        nlinarith
      have hxm1 : (n : ℝ) - 1 ≠ 0 := by
        nlinarith
      have hxp2 : (n : ℝ) + 2 ≠ 0 := by
        nlinarith
      have hsq : ((n : ℝ) + 1) ^ 2 - 1 ≠ 0 := by
        rw [show ((n : ℝ) + 1) ^ 2 - 1 = (n : ℝ) * ((n : ℝ) + 2) by ring]
        exact mul_ne_zero hx hxp2
      field_simp [hx, hxm1, hsq] <;> ring

/-- Source: `proof_gap/exercise_3061/3.txt`; retain the product's lower bound. -/
theorem gap3 (P : ℕ → ℝ) (hP : ∀ n, P n = partialProduct n) :
    ∀ n : ℕ, 3 ≤ n →
      P n = ((n : ℝ) + 2) / (4 * ((n : ℝ) - 1)) := by
  intro n hn
  rw [hP n]
  exact gap2 n hn

/-- Source: `proof_gap/exercise_3061/4.txt`. -/
theorem gap4 (P : ℕ → ℝ) (hP : ∀ n, P n = partialProduct n) :
    Tendsto P atTop (𝓝 (1 / 4 : ℝ)) := by
  have hcast :
      Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hinv :
      Tendsto (fun n : ℕ => ((n : ℝ)⁻¹)) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp hcast
  have hone :
      Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1) :=
    tendsto_const_nhds
  have htwo :
      Tendsto (fun _ : ℕ => (2 : ℝ)) atTop (nhds 2) :=
    tendsto_const_nhds
  have hfour :
      Tendsto (fun _ : ℕ => (4 : ℝ)) atTop (nhds 4) :=
    tendsto_const_nhds
  have hnum :
      Tendsto
        (fun n : ℕ => (1 : ℝ) + 2 * ((n : ℝ)⁻¹))
        atTop (nhds 1) := by
    simpa using hone.add (htwo.mul hinv)
  have hden :
      Tendsto
        (fun n : ℕ => (4 : ℝ) * (1 - ((n : ℝ)⁻¹)))
        atTop (nhds 4) := by
    simpa using hfour.mul (hone.sub hinv)
  have hquot :
      Tendsto
        (fun n : ℕ =>
          ((1 : ℝ) + 2 * ((n : ℝ)⁻¹)) /
            (4 * (1 - ((n : ℝ)⁻¹))))
        atTop (nhds (1 / 4 : ℝ)) :=
    hnum.div hden (by norm_num)
  have hnorm :
      P =ᶠ[atTop]
        (fun n : ℕ =>
          ((1 : ℝ) + 2 * ((n : ℝ)⁻¹)) /
            (4 * (1 - ((n : ℝ)⁻¹)))) := by
    filter_upwards [eventually_ge_atTop (3 : ℕ)] with n hn
    rw [gap3 P hP n hn]
    have hnR : (3 : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast hn
    have hn0 : (n : ℝ) ≠ 0 := by
      nlinarith
    have hnm1 : (n : ℝ) - 1 ≠ 0 := by
      nlinarith
    field_simp [hn0, hnm1] <;> ring
  exact hquot.congr' hnorm.symm

/-- Source: `proof_gap/exercise_3061/5.txt`. -/
theorem gap5 : ConvergentProduct := by
  refine ⟨1 / 4, ?_⟩
  apply gap4 partialProduct
  intro n
  rfl

/-- Source: `proof_gap/exercise_3061/6.txt`. -/
theorem gap6 : HasProduct (1 / 4 : ℝ) := by
  apply gap4 partialProduct
  intro n
  rfl

end

end ProofGap.Exercise3061
