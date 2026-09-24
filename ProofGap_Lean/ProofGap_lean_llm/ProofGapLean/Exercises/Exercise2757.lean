import ProofGapLean.Prelude.Analysis
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega
import Mathlib.Topology.Defs.Filter

namespace ProofGap.Exercise2757

noncomputable section

open Filter
open scoped Topology

def term (n : ℕ) (x : ℝ) : ℝ :=
  Real.exp (n * (x - 1))

def UniformlyConvergesOn
    (f : ℕ → ℝ → ℝ) (F : ℝ → ℝ) (s : Set ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ N : ℕ, ∀ n : ℕ, N < n → ∀ x ∈ s, |f n x - F x| < ε

theorem gap1 :
    ∀ x ∈ Set.Ioo (0 : ℝ) 1,
      Tendsto (fun n : ℕ => term n x) atTop (𝓝 0) := by
  intro x hx
  have hbase_nonneg : 0 ≤ Real.exp (x - 1) :=
    (Real.exp_pos (x - 1)).le
  have hbase_lt : Real.exp (x - 1) < 1 := by
    rw [Real.exp_lt_one_iff]
    exact sub_neg.mpr hx.2
  have hpow :
      Tendsto (fun n : ℕ => (Real.exp (x - 1)) ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hbase_nonneg hbase_lt
  simpa only [term, Real.exp_nat_mul] using hpow

theorem gap2 :
    ∀ x ∈ Set.Ioo (0 : ℝ) 1, (0 : ℝ) = 0 := by
  intro x hx
  rfl

theorem gap3 :
    ∀ x ∈ Set.Ioo (0 : ℝ) 1,
      Tendsto (fun n : ℕ => term n x) atTop (𝓝 0) := by
  exact gap1

theorem gap4 :
    ∀ (n : ℕ) (ε₀ : ℝ), 2 ≤ n → 0 < ε₀ → ε₀ < Real.exp (-1) →
      |term n (1 - 1 / n)| = Real.exp (n * (1 - 1 / n - 1)) := by
  intro n ε₀ hn hε₀ hε₀_lt
  simpa only [term, abs_of_pos (Real.exp_pos _)]

theorem gap5 :
    ∀ (n : ℕ) (ε₀ : ℝ), 1 ≤ n → 0 < ε₀ → ε₀ < Real.exp (-1) →
      Real.exp (n * (1 - 1 / n - 1)) = Real.exp (-1) := by
  intro n ε₀ hn hε₀ hε₀_lt
  apply Real.exp_injective
  have hn0 : (n : ℝ) ≠ 0 := by
    exact_mod_cast (show n ≠ 0 by omega)
  field_simp [hn0] <;> ring

theorem gap6 :
    ∀ ε₀ : ℝ, 0 < ε₀ → ε₀ < Real.exp (-1) → Real.exp (-1) > ε₀ := by
  intro ε₀ hε₀ hε₀_lt
  exact hε₀_lt

theorem gap7 :
    ∀ (n : ℕ) (ε₀ : ℝ), 2 ≤ n → 0 < ε₀ → ε₀ < Real.exp (-1) →
      |term n (1 - 1 / n)| > ε₀ := by
  intro n ε₀ hn hε₀ hε₀_lt
  rw [gap4 n ε₀ hn hε₀ hε₀_lt,
    gap5 n ε₀ (by omega) hε₀ hε₀_lt]
  exact gap6 ε₀ hε₀ hε₀_lt

theorem gap8 :
    ¬ UniformlyConvergesOn term (fun _ => 0) (Set.Ioo (0 : ℝ) 1) := by
  intro h
  unfold UniformlyConvergesOn at h
  let ε₀ : ℝ := Real.exp (-1) / 2
  have hε₀ : 0 < ε₀ := by
    dsimp [ε₀]
    exact half_pos (Real.exp_pos (-1))
  have hε₀_lt : ε₀ < Real.exp (-1) := by
    dsimp [ε₀]
    exact half_lt_self (Real.exp_pos (-1))
  rcases h ε₀ hε₀ with ⟨N, hN⟩
  let n : ℕ := N + 2
  have hn2 : 2 ≤ n := by
    dsimp [n]
    omega
  have hNn : N < n := by
    dsimp [n]
    omega
  have hnone : (1 : ℝ) < (n : ℝ) := by
    exact_mod_cast (show (1 : ℕ) < n by omega)
  have hnpos : (0 : ℝ) < (n : ℝ) :=
    lt_trans zero_lt_one hnone
  let x : ℝ := 1 - 1 / (n : ℝ)
  have hfrac_lt : (1 : ℝ) / (n : ℝ) < 1 :=
    (div_lt_one hnpos).2 hnone
  have hfrac_pos : 0 < (1 : ℝ) / (n : ℝ) :=
    div_pos zero_lt_one hnpos
  have hx : x ∈ Set.Ioo (0 : ℝ) 1 := by
    dsimp [x]
    constructor
    · exact sub_pos.mpr hfrac_lt
    · exact sub_lt_self 1 hfrac_pos
  have hupper : |term n x| < ε₀ := by
    simpa using hN n hNn x hx
  have hlower : |term n x| > ε₀ := by
    simpa only [x] using gap7 n ε₀ hn2 hε₀ hε₀_lt
  exact (not_lt_of_ge (le_of_lt hlower)) hupper

theorem gap9 :
    ¬ UniformlyConvergesOn term (fun _ => 0) (Set.Ioo (0 : ℝ) 1) := by
  exact gap8

end

end ProofGap.Exercise2757
