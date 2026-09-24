import ProofGapLean.Prelude.Analysis
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Lean.Elab.Tactic.Omega
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Neighborhoods

namespace ProofGap.Exercise3051

noncomputable section

open Filter
open scoped BigOperators Topology

def factor (n : ℕ) : ℝ := 1 - 1 / (n : ℝ) ^ 2

def partialProduct (n : ℕ) : ℝ :=
  ∏ i ∈ Finset.Icc 2 n, factor i

def HasProduct (L : ℝ) : Prop :=
  Tendsto partialProduct atTop (𝓝 L)

theorem gap1 :
    ∃ P : ℕ → ℝ, ∀ n : ℕ, P n = partialProduct n := by
  exact ⟨partialProduct, fun n => rfl⟩

theorem gap2 (n : ℕ) :
    partialProduct n =
      ∏ i ∈ Finset.Icc 2 n, (1 - 1 / (i : ℝ) ^ 2) := by
  rfl

theorem gap3 (n : ℕ) (hn : 1 ≤ n) :
    partialProduct n = (1 / 2 : ℝ) * ((n + 1 : ℕ) : ℝ) / (n : ℝ) := by
  induction n with
  | zero => omega
  | succ n ih =>
      by_cases h : n = 0
      · subst n
        have hempty : Finset.Icc 2 1 = ∅ := by
          ext i
          simp
        norm_num [partialProduct, hempty]
      · have hn' : 1 ≤ n := by omega
        have hIcc :
            Finset.Icc 2 n.succ = insert n.succ (Finset.Icc 2 n) := by
          ext i
          simp only [Finset.mem_Icc, Finset.mem_insert]
          omega
        have hnot : n.succ ∉ Finset.Icc 2 n := by
          simp
        unfold partialProduct
        rw [hIcc, Finset.prod_insert hnot]
        change factor n.succ * partialProduct n = _
        rw [ih hn']
        have hn0 : (n : ℝ) ≠ 0 := by positivity
        have hx1 : (n : ℝ) + 1 ≠ 0 := by positivity
        simp only [factor, Nat.cast_succ]
        field_simp [hn0, hx1] <;> ring

theorem gap4 :
    ∃ P : ℕ → ℝ, ∀ n : ℕ, 1 ≤ n →
      P n = (1 / 2 : ℝ) * ((n + 1 : ℕ) : ℝ) / (n : ℝ) := by
  exact ⟨partialProduct, fun n hn => gap3 n hn⟩

theorem gap5 :
    Tendsto partialProduct atTop (𝓝 (1 / 2 : ℝ)) := by
  have hcast :
      Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hinv :
      Tendsto (fun n : ℕ => ((n : ℝ)⁻¹)) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hcast
  have hconst :
      Tendsto (fun _ : ℕ => (1 / 2 : ℝ)) atTop (𝓝 (1 / 2 : ℝ)) :=
    tendsto_const_nhds
  have hone :
      Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 (1 : ℝ)) :=
    tendsto_const_nhds
  have hlim :
      Tendsto (fun n : ℕ => (1 / 2 : ℝ) * (1 + (n : ℝ)⁻¹))
        atTop (𝓝 (1 / 2 : ℝ)) := by
    simpa using hconst.mul (hone.add hinv)
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  rw [gap3 n hn]
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  simp only [Nat.cast_add, Nat.cast_one]
  field_simp [hn0] <;> ring

theorem gap6 : HasProduct (1 / 2 : ℝ) := by
  simpa [HasProduct] using gap5

theorem gap7 : HasProduct (1 / 2 : ℝ) := by
  exact gap6

end

end ProofGap.Exercise3051
