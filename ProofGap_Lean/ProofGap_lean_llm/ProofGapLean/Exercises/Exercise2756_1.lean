import ProofGapLean.Prelude.Analysis
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Topology.Defs.Filter

namespace ProofGap.Exercise2756_1

noncomputable section

open Filter
open scoped Topology

def term (n : ℕ) (x : ℝ) : ℝ :=
  Real.arctan (n * x)

def UniformlyConvergesOn
    (f : ℕ → ℝ → ℝ) (F : ℝ → ℝ) (s : Set ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ N : ℕ, ∀ n : ℕ, N < n → ∀ x ∈ s, |f n x - F x| < ε

theorem gap1 :
    ∀ x : ℝ, 0 < x →
      Tendsto (fun n : ℕ => term n x) atTop (𝓝 (Real.pi / 2)) := by
  intro x hx
  have harg : Tendsto (fun n : ℕ => (n : ℝ) * x) atTop atTop := by
    refine tendsto_atTop.2 ?_
    intro b
    obtain ⟨N, hN⟩ := exists_nat_gt (b / x)
    filter_upwards [eventually_ge_atTop N] with n hn
    apply (div_le_iff₀ hx).mp
    exact le_trans (le_of_lt hN) ((Nat.cast_le).2 hn)
  have harctan :
      Tendsto Real.arctan atTop (𝓝 (Real.pi / 2)) :=
    Real.tendsto_arctan_atTop.mono_right inf_le_left
  simpa [term, Function.comp_def] using harctan.comp harg

theorem gap2 :
    ∀ x : ℝ, 0 < x → Real.pi / 2 = Real.pi / 2 := by
  intro x hx
  rfl

theorem gap3 :
    ∀ x : ℝ, 0 < x →
      Tendsto (fun n : ℕ => term n x) atTop (𝓝 (Real.pi / 2)) := by
  exact gap1

theorem gap4 :
    ∀ (n : ℕ) (ε₀ : ℝ), 1 ≤ n → 0 < ε₀ → ε₀ < Real.pi / 4 →
      |term n (1 / n) - Real.pi / 2| =
        |Real.arctan 1 - Real.pi / 2| := by
  intro n ε₀ hn hε₀ hε₀'
  have hnpos : 0 < n := lt_of_lt_of_le Nat.zero_lt_one hn
  have hn0 : n ≠ 0 := Nat.ne_of_gt hnpos
  simp [term, hn0]

theorem gap5 :
    ∀ ε₀ : ℝ, 0 < ε₀ → ε₀ < Real.pi / 4 →
      |Real.arctan 1 - Real.pi / 2| = Real.pi / 4 := by
  intro ε₀ hε₀ hε₀'
  rw [Real.arctan_one]
  have hnonpos : Real.pi / 4 - Real.pi / 2 ≤ 0 := by
    linarith [Real.pi_pos]
  rw [abs_of_nonpos hnonpos]
  ring

theorem gap6 :
    ∀ ε₀ : ℝ, 0 < ε₀ → ε₀ < Real.pi / 4 →
      Real.pi / 4 > ε₀ := by
  intro ε₀ hε₀ hε₀'
  exact hε₀'

theorem gap7 :
    ∀ (n : ℕ) (ε₀ : ℝ), 1 ≤ n → 0 < ε₀ → ε₀ < Real.pi / 4 →
      |term n (1 / n) - Real.pi / 2| > ε₀ := by
  intro n ε₀ hn hε₀ hε₀'
  calc
    |term n (1 / n) - Real.pi / 2| =
        |Real.arctan 1 - Real.pi / 2| := gap4 n ε₀ hn hε₀ hε₀'
    _ = Real.pi / 4 := gap5 ε₀ hε₀ hε₀'
    _ > ε₀ := gap6 ε₀ hε₀ hε₀'

theorem gap8 :
    ¬ UniformlyConvergesOn term (fun _ => Real.pi / 2) (Set.Ioi (0 : ℝ)) := by
  intro h
  unfold UniformlyConvergesOn at h
  have hεpos : 0 < Real.pi / 8 := by
    linarith [Real.pi_pos]
  have hεlt : Real.pi / 8 < Real.pi / 4 := by
    linarith [Real.pi_pos]
  obtain ⟨N, hN⟩ := h (Real.pi / 8) hεpos
  have hn1 : 1 ≤ N + 1 := Nat.succ_le_succ (Nat.zero_le N)
  have hx :
      (1 / (((N + 1 : ℕ) : ℝ))) ∈ Set.Ioi (0 : ℝ) := by
    change 0 < 1 / (((N + 1 : ℕ) : ℝ))
    positivity
  have hlt :=
    hN (N + 1) (Nat.lt_succ_self N)
      (1 / (((N + 1 : ℕ) : ℝ))) hx
  have hgt := gap7 (N + 1) (Real.pi / 8) hn1 hεpos hεlt
  linarith

theorem gap9 :
    ¬ UniformlyConvergesOn term (fun _ => Real.pi / 2) (Set.Ioi (0 : ℝ)) := by
  exact gap8

end

end ProofGap.Exercise2756_1
