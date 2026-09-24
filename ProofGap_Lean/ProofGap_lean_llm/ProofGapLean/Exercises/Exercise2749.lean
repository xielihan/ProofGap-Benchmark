import ProofGapLean.Prelude.Analysis
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Topology.Defs.Filter

namespace ProofGap.Exercise2749

noncomputable section

open Filter
open scoped Topology

def term (n : ℕ) (x : ℝ) : ℝ :=
  1 / (x + n)

def UniformlyConvergesOn
    (f : ℕ → ℝ → ℝ) (F : ℝ → ℝ) (s : Set ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ N : ℕ, ∀ n : ℕ, N < n → ∀ x ∈ s, |f n x - F x| < ε

theorem gap1 :
    ∀ x : ℝ, 0 < x →
      Tendsto (fun n : ℕ => term n x) atTop (𝓝 0) := by
  intro x hx
  have hden : Tendsto (fun n : ℕ => x + (n : ℝ)) atTop atTop := by
    refine tendsto_atTop.2 ?_
    intro b
    obtain ⟨N, hN⟩ := exists_nat_gt (b - x)
    refine (eventually_ge_atTop N).mono ?_
    intro n hn
    have hn' : (N : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast hn
    linarith
  have hinv : Tendsto (fun y : ℝ => y⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero
  simpa [term, one_div] using hinv.comp hden

theorem gap2 :
    ∀ x : ℝ, 0 < x → (0 : ℝ) = 0 := by
  intro x hx
  rfl

theorem gap3 :
    ∀ x : ℝ, 0 < x →
      Tendsto (fun n : ℕ => term n x) atTop (𝓝 0) := by
  exact gap1

theorem gap4 :
    ∀ (n : ℕ) (x : ℝ), 0 < x → |term n x| = 1 / (x + n) := by
  intro n x hx
  have hden : 0 < x + (n : ℝ) := by
    positivity
  rw [term, abs_of_pos (one_div_pos.mpr hden)]

theorem gap5 :
    ∀ (n : ℕ) (x : ℝ), 0 < n → 0 < x →
      1 / (x + n) < 1 / (n : ℝ) := by
  intro n x hn hx
  have hn' : (0 : ℝ) < (n : ℝ) := by
    exact_mod_cast hn
  have hlt : (n : ℝ) < x + (n : ℝ) := by
    linarith
  exact one_div_lt_one_div_of_lt hn' hlt

theorem gap6 :
    ∀ (n : ℕ) (x : ℝ), 0 < n → 0 < x →
      |term n x| < 1 / (n : ℝ) := by
  intro n x hn hx
  rw [gap4 n x hx]
  exact gap5 n x hn hx

theorem gap7 :
    ∀ (n : ℕ) (x ε : ℝ), 0 < n → 0 < x → 0 < ε →
      1 / (n : ℝ) < ε → |term n x| < ε := by
  intro n x ε hn hx hε hbound
  exact lt_trans (gap6 n x hn hx) hbound

theorem gap8 :
    ∀ (n : ℕ) (ε : ℝ), 0 < ε →
      1 / ε < (n : ℝ) → 1 / (n : ℝ) < ε := by
  intro n ε hε h
  have hnpos : (0 : ℝ) < (n : ℝ) :=
    lt_trans (one_div_pos.mpr hε) h
  have hmul : 1 < (n : ℝ) * ε :=
    (div_lt_iff₀ hε).mp h
  apply (div_lt_iff₀ hnpos).2
  simpa [mul_comm] using hmul

theorem gap9 :
    ∀ (n : ℕ) (x ε : ℝ), 0 < x → 0 < ε →
      1 / ε < (n : ℝ) → |term n x| < ε := by
  intro n x ε hx hε hbound
  have hnreal : (0 : ℝ) < (n : ℝ) :=
    lt_trans (one_div_pos.mpr hε) hbound
  have hn : 0 < n := by
    exact_mod_cast hnreal
  exact gap7 n x ε hn hx hε (gap8 n ε hε hbound)

theorem gap10 :
    ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, ∀ n : ℕ, N < n →
        ∀ x : ℝ, 0 < x → |term n x| < ε := by
  intro ε hε
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / ε)
  refine ⟨N, ?_⟩
  intro n hn x hx
  have hNn : (N : ℝ) < (n : ℝ) := by
    exact_mod_cast hn
  exact gap9 n x ε hx hε (lt_trans hN hNn)

theorem gap11 :
    UniformlyConvergesOn term (fun _ => 0) (Set.Ioi (0 : ℝ)) := by
  unfold UniformlyConvergesOn
  intro ε hε
  obtain ⟨N, hN⟩ := gap10 ε hε
  refine ⟨N, ?_⟩
  intro n hn x hx
  simpa only [sub_zero] using hN n hn x hx

theorem gap12 :
    UniformlyConvergesOn term (fun _ => 0) (Set.Ioi (0 : ℝ)) := by
  exact gap11

end

end ProofGap.Exercise2749
