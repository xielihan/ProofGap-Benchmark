import ProofGapLean.Prelude.Analysis
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Neighborhoods

namespace ProofGap.Exercise2752

noncomputable section

open Filter
open scoped Topology

def term (n : ℕ) (x : ℝ) : ℝ :=
  (2 * n * x) / (1 + (n : ℝ) ^ 2 * x ^ 2)

def UniformlyConvergesOn
    (f : ℕ → ℝ → ℝ) (F : ℝ → ℝ) (s : Set ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ N : ℕ, ∀ n : ℕ, N < n → ∀ x ∈ s, |f n x - F x| < ε

private theorem term_tendsto_zero_of_ne {x : ℝ} (hx : x ≠ 0) :
    Tendsto (fun n : ℕ => term n x) atTop (𝓝 0) := by
  have hinv : Tendsto (fun n : ℕ => ((n : ℝ)⁻¹)) atTop (𝓝 0) := by
    exact
      (tendsto_inv_atTop_zero :
        Tendsto (fun y : ℝ => y⁻¹) atTop (𝓝 0)).comp
        tendsto_natCast_atTop_atTop
  have hnum :
      Tendsto (fun n : ℕ => (2 * x) * ((n : ℝ)⁻¹)) atTop
        (𝓝 ((2 * x) * 0)) :=
    tendsto_const_nhds.mul hinv
  have hden :
      Tendsto (fun n : ℕ => ((n : ℝ)⁻¹) ^ 2 + x ^ 2) atTop
        (𝓝 (0 ^ 2 + x ^ 2)) :=
    (hinv.pow 2).add tendsto_const_nhds
  have hden0 : 0 ^ 2 + x ^ 2 ≠ 0 := by
    simp [hx]
  have hscaled :
      Tendsto
        (fun n : ℕ =>
          ((2 * x) * ((n : ℝ)⁻¹)) /
            (((n : ℝ)⁻¹) ^ 2 + x ^ 2))
        atTop (𝓝 0) := by
    simpa using hnum.div hden hden0
  refine hscaled.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hn)
  have hx2 : 0 < x ^ 2 := by positivity
  have hden1 : 1 + (n : ℝ) ^ 2 * x ^ 2 ≠ 0 := by positivity
  have hden2 : ((n : ℝ)⁻¹) ^ 2 + x ^ 2 ≠ 0 := by positivity
  unfold term
  field_simp [hn0, hden1, hden2] <;> ring

theorem gap1 :
    ∀ x ∈ Set.Icc (0 : ℝ) 1,
      Tendsto (fun n : ℕ => term n x) atTop (𝓝 0) := by
  intro x hx
  by_cases hzero : x = 0
  · subst x
    simp [term]
  · exact term_tendsto_zero_of_ne hzero

theorem gap2 :
    ∀ x ∈ Set.Icc (0 : ℝ) 1, (0 : ℝ) = 0 := by
  intro x hx
  rfl

theorem gap3 :
    ∀ x ∈ Set.Icc (0 : ℝ) 1,
      Tendsto (fun n : ℕ => term n x) atTop (𝓝 0) := by
  exact gap1

theorem gap4 :
    ∀ (n : ℕ) (ε₀ : ℝ), 1 ≤ n → 0 < ε₀ → ε₀ < 1 →
      |term n (1 / n) - 0| = 1 := by
  intro n ε₀ hn hε₀ hε₀_one
  have hnpos : 0 < n := lt_of_lt_of_le Nat.zero_lt_one hn
  have hnR : (n : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hnpos)
  have hterm : term n (1 / (n : ℝ)) = 1 := by
    unfold term
    field_simp [hnR] <;> ring
  calc
    |term n (1 / (n : ℝ)) - 0| = |(1 : ℝ) - 0| := by rw [hterm]
    _ = 1 := by norm_num

theorem gap5 :
    ∀ ε₀ : ℝ, 0 < ε₀ → ε₀ < 1 → 1 > ε₀ := by
  intro ε₀ hε₀ hε₀_one
  exact hε₀_one

theorem gap6 :
    ∀ (n : ℕ) (ε₀ : ℝ), 1 ≤ n → 0 < ε₀ → ε₀ < 1 →
      |term n (1 / n) - 0| > ε₀ := by
  intro n ε₀ hn hε₀ hε₀_one
  rw [gap4 n ε₀ hn hε₀ hε₀_one]
  exact hε₀_one

theorem gap7 :
    ¬ UniformlyConvergesOn term (fun _ => 0) (Set.Icc (0 : ℝ) 1) := by
  intro hconv
  obtain ⟨N, hN⟩ := hconv (1 / 2 : ℝ) (by norm_num)
  let n : ℕ := N + 1
  have hNn : N < n := by
    simp [n]
  have hn : 1 ≤ n := by
    simp [n]
  have hnR_one : (1 : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast hn
  have hnR : (0 : ℝ) < (n : ℝ) := lt_of_lt_of_le zero_lt_one hnR_one
  have hxmem : 1 / (n : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · positivity
    · apply (div_le_iff₀ hnR).2
      simpa using hnR_one
  have hsmall : |term n (1 / (n : ℝ)) - 0| < (1 / 2 : ℝ) := by
    simpa using hN n hNn (1 / (n : ℝ)) hxmem
  have hlarge : |term n (1 / (n : ℝ)) - 0| > (1 / 2 : ℝ) :=
    gap6 n (1 / 2 : ℝ) hn (by norm_num) (by norm_num)
  linarith

theorem gap8 :
    ∀ x : ℝ, 1 < x →
      Tendsto (fun n : ℕ => term n x) atTop (𝓝 0) := by
  intro x hx
  apply term_tendsto_zero_of_ne
  exact ne_of_gt (lt_trans zero_lt_one hx)

theorem gap9 :
    ∀ x : ℝ, 1 < x → (0 : ℝ) = 0 := by
  intro x hx
  rfl

theorem gap10 :
    ∀ x : ℝ, 1 < x →
      Tendsto (fun n : ℕ => term n x) atTop (𝓝 0) := by
  exact gap8

theorem gap11 :
    ∀ (n : ℕ) (x : ℝ), 1 < x → |term n x| = term n x := by
  intro n x hx
  apply abs_of_nonneg
  unfold term
  positivity

theorem gap12 :
    ∀ (n : ℕ) (x : ℝ), 0 < n → 1 < x →
      term n x < (2 * n * x) / ((n : ℝ) ^ 2 * x ^ 2) := by
  intro n x hn hx
  have hnR : (0 : ℝ) < (n : ℝ) := by
    exact_mod_cast hn
  have hxR : 0 < x := lt_trans zero_lt_one hx
  apply (div_lt_div_iff₀ (by positivity) (by positivity)).2
  have hnum : 0 < 2 * (n : ℝ) * x := by positivity
  nlinarith [hnum]

theorem gap13 :
    ∀ (n : ℕ) (x : ℝ), 0 < n → 1 < x →
      (2 * n * x) / ((n : ℝ) ^ 2 * x ^ 2) < 2 / (n : ℝ) := by
  intro n x hn hx
  have hnR : (0 : ℝ) < (n : ℝ) := by
    exact_mod_cast hn
  have hxR : 0 < x := lt_trans zero_lt_one hx
  have hxsub : 0 < x - 1 := sub_pos.mpr hx
  have hden : 0 < (n : ℝ) ^ 2 * x ^ 2 := by positivity
  apply (div_lt_div_iff₀ hden hnR).2
  have hpos : 0 < 2 * (n : ℝ) ^ 2 * x * (x - 1) := by
    positivity
  nlinarith [hpos]

theorem gap14 :
    ∀ (n : ℕ) (x : ℝ), 0 < n → 1 < x →
      |term n x| < 2 / (n : ℝ) := by
  intro n x hn hx
  rw [gap11 n x hx]
  exact lt_trans (gap12 n x hn hx) (gap13 n x hn hx)

theorem gap15 :
    ∀ (n : ℕ) (x ε : ℝ), 1 < x → 0 < ε →
      2 / ε < (n : ℝ) → |term n x| < ε := by
  intro n x ε hx hε hbound
  have htwo : 0 < 2 / ε := by positivity
  have hnR : (0 : ℝ) < (n : ℝ) := lt_trans htwo hbound
  have hn : 0 < n := by
    exact_mod_cast hnR
  have hcross : 2 < (n : ℝ) * ε := (div_lt_iff₀ hε).mp hbound
  have hratio : 2 / (n : ℝ) < ε := by
    apply (div_lt_iff₀ hnR).2
    simpa [mul_comm] using hcross
  exact lt_trans (gap14 n x hn hx) hratio

theorem gap16 :
    ∀ (n : ℕ) (x ε : ℝ), 1 < x → 0 < ε →
      2 / ε < (n : ℝ) → |term n x| < ε := by
  intro n x ε hx hε hbound
  exact gap15 n x ε hx hε hbound

theorem gap17 :
    ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, ∀ n : ℕ, N < n →
        ∀ x : ℝ, 1 < x → |term n x| < ε := by
  intro ε hε
  obtain ⟨N, hN⟩ := exists_nat_gt (2 / ε)
  refine ⟨N, ?_⟩
  intro n hn x hx
  apply gap16 n x ε hx hε
  exact lt_trans hN (by exact_mod_cast hn)

theorem gap18 :
    UniformlyConvergesOn term (fun _ => 0) (Set.Ioi (1 : ℝ)) := by
  intro ε hε
  obtain ⟨N, hN⟩ := gap17 ε hε
  refine ⟨N, ?_⟩
  intro n hn x hx
  simpa using hN n hn x hx

theorem gap19 :
    ¬ UniformlyConvergesOn term (fun _ => 0) (Set.Icc (0 : ℝ) 1) ∧
      UniformlyConvergesOn term (fun _ => 0) (Set.Ioi (1 : ℝ)) := by
  exact ⟨gap7, gap18⟩

end

end ProofGap.Exercise2752
