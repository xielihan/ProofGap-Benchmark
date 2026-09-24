import ProofGapLean.Prelude.Analysis
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Neighborhoods

namespace ProofGap.Exercise3062

noncomputable section

open Filter
open scoped BigOperators Topology

def factor (n : ℕ) : ℝ :=
  1 + 1 / ((n : ℝ) * ((n : ℝ) + 2))

def partialProduct (n : ℕ) : ℝ :=
  ∏ i ∈ Finset.Icc 1 n, factor i

def ConvergentProduct : Prop :=
  ∃ L : ℝ, Tendsto partialProduct atTop (𝓝 L)

def HasProduct (L : ℝ) : Prop :=
  Tendsto partialProduct atTop (𝓝 L)

/-- Source: `proof_gap/exercise_3062/1.txt`; division requires `n ≥ 1`. -/
theorem gap1 :
    ∀ n : ℕ, 1 ≤ n →
      1 + 1 / ((n : ℝ) * ((n : ℝ) + 2)) =
        ((n : ℝ) + 1) ^ 2 / ((n : ℝ) * ((n : ℝ) + 2)) := by
  intro n hn
  have hnpos : (0 : ℝ) < (n : ℝ) :=
    Nat.cast_pos.mpr (by omega)
  have hn2 : (n : ℝ) + 2 ≠ 0 := by positivity
  field_simp [ne_of_gt hnpos, hn2]
  <;> ring

/-- Source: `proof_gap/exercise_3062/2.txt`; the product ellipsis is `partialProduct`. -/
theorem gap2 (P : ℕ → ℝ) (hP : ∀ n, P n = partialProduct n) :
    ∀ n, P n = partialProduct n := by
  exact hP

/-- Source: `proof_gap/exercise_3062/3.txt`; replace the telescoping ellipsis exactly. -/
theorem gap3 :
    ∀ n : ℕ,
      partialProduct n = 2 * ((n : ℝ) + 1) / ((n : ℝ) + 2) := by
  intro n
  induction n with
  | zero =>
      norm_num [partialProduct]
  | succ n ih =>
      have hIcc :
          Finset.Icc 1 (Nat.succ n) =
            insert (Nat.succ n) (Finset.Icc 1 n) := by
        ext i
        simp only [Finset.mem_Icc, Finset.mem_insert]
        omega
      have hnotmem : Nat.succ n ∉ Finset.Icc 1 n := by simp
      rw [partialProduct, hIcc, Finset.prod_insert hnotmem]
      change factor (Nat.succ n) * partialProduct n =
        2 * ((Nat.succ n : ℝ) + 1) / ((Nat.succ n : ℝ) + 2)
      rw [ih]
      rw [show factor (Nat.succ n) =
          ((Nat.succ n : ℝ) + 1) ^ 2 /
            ((Nat.succ n : ℝ) * ((Nat.succ n : ℝ) + 2)) from
        gap1 (Nat.succ n) (by omega)]
      simp only [Nat.cast_succ]
      have h1 : (n : ℝ) + 1 ≠ 0 := by positivity
      have h2 : (n : ℝ) + 2 ≠ 0 := by positivity
      have h3 : ((n : ℝ) + 1) + 2 ≠ 0 := by positivity
      field_simp [h1, h2, h3]
      <;> ring

/-- Source: `proof_gap/exercise_3062/4.txt`. -/
theorem gap4 (P : ℕ → ℝ) (hP : ∀ n, P n = partialProduct n) :
    ∀ n : ℕ, P n = 2 * ((n : ℝ) + 1) / ((n : ℝ) + 2) := by
  intro n
  rw [hP n, gap3 n]

/-- Source: `proof_gap/exercise_3062/5.txt`. -/
theorem gap5 (P : ℕ → ℝ) (hP : ∀ n, P n = partialProduct n) :
    Tendsto P atTop (𝓝 2) := by
  have htop :
      Tendsto (fun n : ℕ => (n : ℝ) + 2) atTop atTop := by
    refine tendsto_atTop.2 ?_
    intro b
    obtain ⟨N, hN⟩ := exists_nat_ge b
    refine (eventually_ge_atTop N).mono ?_
    intro n hn
    have hcast : (N : ℝ) ≤ (n : ℝ) := (Nat.cast_le).2 hn
    exact hN.trans (hcast.trans (by norm_num))
  have hinv :
      Tendsto (fun n : ℕ => (((n : ℝ) + 2)⁻¹)) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp htop
  have hform :
      ∀ n : ℕ, P n = 2 - 2 * (((n : ℝ) + 2)⁻¹) := by
    intro n
    rw [gap4 P hP n]
    have hne : (n : ℝ) + 2 ≠ 0 := by positivity
    field_simp [hne]
    <;> ring
  have hPfun :
      P = fun n : ℕ => 2 - 2 * (((n : ℝ) + 2)⁻¹) :=
    funext hform
  rw [hPfun]
  have hconst2 :
      Tendsto (fun _ : ℕ => (2 : ℝ)) atTop (𝓝 2) :=
    tendsto_const_nhds
  simpa using hconst2.sub (hconst2.mul hinv)

/-- Source: `proof_gap/exercise_3062/6.txt`. -/
theorem gap6 : ConvergentProduct := by
  refine ⟨2, ?_⟩
  exact gap5 partialProduct (fun n => rfl)

/-- Source: `proof_gap/exercise_3062/7.txt`. -/
theorem gap7 : HasProduct 2 := by
  exact gap5 partialProduct (fun n => rfl)

end

end ProofGap.Exercise3062
