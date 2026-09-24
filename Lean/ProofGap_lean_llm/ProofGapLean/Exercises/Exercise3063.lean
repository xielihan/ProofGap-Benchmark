import ProofGapLean.Prelude.Analysis
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Neighborhoods
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise3063

noncomputable section

open Filter
open scoped BigOperators Topology

def factor (n : ℕ) : ℝ :=
  ((2 * (n : ℝ) + 1) * (2 * (n : ℝ) + 7)) /
    ((2 * (n : ℝ) + 3) * (2 * (n : ℝ) + 5))

def partialProduct (n : ℕ) : ℝ :=
  ∏ i ∈ Finset.Icc 1 n, factor i

def ConvergentProduct : Prop :=
  ∃ L : ℝ, Tendsto partialProduct atTop (𝓝 L)

def HasProduct (L : ℝ) : Prop :=
  Tendsto partialProduct atTop (𝓝 L)

/-- Source: `proof_gap/exercise_3063/1.txt`; the product ellipsis is `partialProduct`. -/
theorem gap1 (P : ℕ → ℝ) (hP : ∀ n, P n = partialProduct n) :
    ∀ n, P n = partialProduct n := by
  exact hP

/-- Source: `proof_gap/exercise_3063/2.txt`. -/
theorem gap2 :
    ∀ n : ℕ,
      partialProduct n =
        (3 / 7 : ℝ) * (2 * (n : ℝ) + 7) / (2 * (n : ℝ) + 3) := by
  intro n
  induction n with
  | zero =>
      norm_num [partialProduct]
  | succ n ih =>
      change (∏ i ∈ Finset.Icc 1 (Nat.succ n), factor i) = _
      rw [Finset.prod_Icc_succ_top (Nat.succ_le_succ (Nat.zero_le n))]
      change partialProduct n * factor (Nat.succ n) = _
      rw [ih]
      simp only [factor, Nat.cast_succ]
      have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      field_simp <;> nlinarith

/-- Source: `proof_gap/exercise_3063/3.txt`. -/
theorem gap3 (P : ℕ → ℝ) (hP : ∀ n, P n = partialProduct n) :
    Tendsto P atTop (𝓝 (3 / 7 : ℝ)) := by
  have hnat :
      Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hden :
      Tendsto (fun n : ℕ => 2 * (n : ℝ) + 3) atTop atTop := by
    refine tendsto_atTop.2 ?_
    intro b
    filter_upwards [
      hnat.eventually (eventually_ge_atTop (α := ℝ) b)
    ] with n hn
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    nlinarith
  have hinv :
      Tendsto (fun n : ℕ => (2 * (n : ℝ) + 3)⁻¹) atTop (𝓝 (0 : ℝ)) :=
    (tendsto_inv_atTop_zero :
      Tendsto (fun x : ℝ => x⁻¹) atTop (𝓝 (0 : ℝ))).comp hden
  have hlim0 :
      Tendsto
        (fun n : ℕ =>
          (3 / 7 : ℝ) * (1 + 4 * (2 * (n : ℝ) + 3)⁻¹))
        atTop (𝓝 ((3 / 7 : ℝ) * (1 + 4 * 0))) :=
    tendsto_const_nhds.mul
      (tendsto_const_nhds.add (tendsto_const_nhds.mul hinv))
  have hlim :
      Tendsto
        (fun n : ℕ =>
          (3 / 7 : ℝ) * (1 + 4 * (2 * (n : ℝ) + 3)⁻¹))
        atTop (𝓝 (3 / 7 : ℝ)) := by
    convert hlim0 using 1 <;> norm_num
  refine hlim.congr' (Eventually.of_forall ?_)
  intro n
  rw [hP n, gap2 n]
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hd : 2 * (n : ℝ) + 3 ≠ 0 := by
    nlinarith
  field_simp [hd] <;> ring

/-- Source: `proof_gap/exercise_3063/4.txt`. -/
theorem gap4 : ConvergentProduct := by
  refine ⟨3 / 7, gap3 partialProduct ?_⟩
  intro n
  rfl

/-- Source: `proof_gap/exercise_3063/5.txt`. -/
theorem gap5 : HasProduct (3 / 7 : ℝ) := by
  exact gap3 partialProduct (fun n => rfl)

end

end ProofGap.Exercise3063
