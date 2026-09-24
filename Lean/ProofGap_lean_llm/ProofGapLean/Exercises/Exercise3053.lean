import ProofGapLean.Prelude.Analysis
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Neighborhoods

namespace ProofGap.Exercise3053

noncomputable section

open Filter
open scoped BigOperators Topology

def factor (n : ℕ) : ℝ :=
  1 - 2 / ((n : ℝ) * (n + 1))

def partialProduct (n : ℕ) : ℝ :=
  ∏ i ∈ Finset.Icc 2 n, factor i

def HasProduct (L : ℝ) : Prop :=
  Tendsto partialProduct atTop (𝓝 L)

theorem gap1 (P : ℕ → ℝ) (hP : ∀ n, P n = partialProduct n) :
    ∀ n, P n = partialProduct n := by
  exact hP

theorem gap2 (n : ℕ) :
    partialProduct n =
      ∏ i ∈ Finset.Icc 2 n,
        (((i : ℝ) + 2) * ((i : ℝ) - 1) / ((i : ℝ) * (i + 1))) := by
  unfold partialProduct
  apply Finset.prod_congr rfl
  intro i hi
  have hi2 : 2 ≤ i := (Finset.mem_Icc.mp hi).1
  have hi0 : (i : ℝ) ≠ 0 := by positivity
  have hi1 : (i : ℝ) + 1 ≠ 0 := by positivity
  unfold factor
  field_simp [hi0, hi1] <;> ring

theorem gap3 (n : ℕ) (hn : 1 ≤ n) :
    partialProduct n = (1 / 3 : ℝ) * ((n + 2 : ℕ) : ℝ) / (n : ℝ) := by
  induction n, hn using Nat.le_induction with
  | base =>
      norm_num [partialProduct]
  | succ n hn ih =>
      have hIcc :
          Finset.Icc 2 (n + 1) =
            insert (n + 1) (Finset.Icc 2 n) := by
        ext i
        simp only [Finset.mem_Icc, Finset.mem_insert]
        omega
      have hnot : n + 1 ∉ Finset.Icc 2 n := by
        simp
      calc
        partialProduct (n + 1) = partialProduct n * factor (n + 1) := by
          unfold partialProduct
          rw [hIcc, Finset.prod_insert hnot]
          ring
        _ = (1 / 3 : ℝ) * (((n + 1) + 2 : ℕ) : ℝ) /
              ((n + 1 : ℕ) : ℝ) := by
          have hn0 : (n : ℝ) ≠ 0 :=
            Nat.cast_ne_zero.mpr (by omega)
          have hn1 : (n : ℝ) + 1 ≠ 0 := by positivity
          have hn2 : (n : ℝ) + 2 ≠ 0 := by positivity
          rw [ih]
          unfold factor
          norm_num [Nat.cast_add, Nat.cast_one]
          field_simp [hn0, hn1, hn2] <;> ring

theorem gap4 (P : ℕ → ℝ) (hP : ∀ n, P n = partialProduct n)
    (n : ℕ) (hn : 1 ≤ n) :
    P n = (1 / 3 : ℝ) * ((n + 2 : ℕ) : ℝ) / (n : ℝ) := by
  rw [hP n]
  exact gap3 n hn

theorem gap5 :
    Tendsto partialProduct atTop (𝓝 (1 / 3 : ℝ)) := by
  have hone_div :
      Tendsto (fun n : ℕ => (1 : ℝ) / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_one_div_atTop_nhds_zero_nat
  have htwo :
      Tendsto (fun n : ℕ => (2 : ℝ) / (n : ℝ)) atTop (𝓝 0) := by
    have hconst :
        Tendsto (fun _ : ℕ => (2 : ℝ)) atTop (𝓝 2) :=
      tendsto_const_nhds
    simpa [div_eq_mul_inv] using hconst.mul hone_div
  have hone :
      Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) :=
    tendsto_const_nhds
  have hadd :
      Tendsto (fun n : ℕ => (1 : ℝ) + 2 / (n : ℝ)) atTop (𝓝 1) := by
    simpa using hone.add htwo
  have heqRatio :
      (fun n : ℕ => (((n + 2 : ℕ) : ℝ) / (n : ℝ))) =ᶠ[atTop]
        (fun n : ℕ => (1 : ℝ) + 2 / (n : ℝ)) := by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have hn0 : (n : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (by omega)
    norm_num [Nat.cast_add, Nat.cast_one]
    field_simp [hn0] <;> ring
  have hratio :
      Tendsto (fun n : ℕ => (((n + 2 : ℕ) : ℝ) / (n : ℝ)))
        atTop (𝓝 1) :=
    hadd.congr' heqRatio.symm
  have hthird :
      Tendsto (fun _ : ℕ => (1 / 3 : ℝ)) atTop (𝓝 (1 / 3 : ℝ)) :=
    tendsto_const_nhds
  have hformula :
      Tendsto
        (fun n : ℕ => (1 / 3 : ℝ) * ((n + 2 : ℕ) : ℝ) / (n : ℝ))
        atTop (𝓝 (1 / 3 : ℝ)) := by
    simpa [mul_div_assoc] using hthird.mul hratio
  have heqProduct :
      partialProduct =ᶠ[atTop]
        (fun n : ℕ => (1 / 3 : ℝ) * ((n + 2 : ℕ) : ℝ) / (n : ℝ)) := by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    exact gap3 n hn
  exact hformula.congr' heqProduct.symm

theorem gap6 : HasProduct (1 / 3 : ℝ) := by
  exact gap5

theorem gap7 : HasProduct (1 / 3 : ℝ) := by
  exact gap6

end

end ProofGap.Exercise3053
