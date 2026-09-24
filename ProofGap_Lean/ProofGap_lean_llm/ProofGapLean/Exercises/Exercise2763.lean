import ProofGapLean.Prelude.Analysis
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Neighborhoods

namespace ProofGap.Exercise2763

noncomputable section

open Filter
open scoped Topology

def term (n : ℕ) (x : ℝ) : ℝ :=
  if 0 ≤ x ∧ x ≤ 1 / (n : ℝ) then (n : ℝ) ^ 2 * x
  else if 1 / (n : ℝ) < x ∧ x < 2 / (n : ℝ) then
    (n : ℝ) ^ 2 * (2 / (n : ℝ) - x)
  else 0

def UniformlyConvergesOn
    (f : ℕ → ℝ → ℝ) (F : ℝ → ℝ) (s : Set ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ N : ℕ, ∀ n : ℕ, N < n → ∀ x ∈ s, |f n x - F x| < ε

theorem gap1 :
    ∀ n : ℕ, term n 0 = 0 := by
  intro n
  simp [term]

theorem gap2 :
    Tendsto (fun n : ℕ => term n 0) atTop (𝓝 0) := by
  simpa only [gap1] using
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))

theorem gap3 :
    ∀ x ∈ Set.Icc (0 : ℝ) 1, x ≠ 0 → 0 < x := by
  intro x hx hne
  rcases lt_or_eq_of_le hx.1 with hlt | heq
  · exact hlt
  · exact False.elim (hne heq.symm)

theorem gap4 :
    ∀ x ∈ Set.Icc (0 : ℝ) 1, x ≠ 0 →
      ∃ N : ℕ, 0 < N ∧ 2 / (N : ℝ) ≤ x := by
  intro x hx hne
  have hxpos : 0 < x := gap3 x hx hne
  obtain ⟨N, hN⟩ := exists_nat_gt (2 / x)
  have hdivpos : 0 < (2 : ℝ) / x := div_pos (by norm_num) hxpos
  have hNrealpos : 0 < (N : ℝ) := lt_trans hdivpos hN
  have hNnat : 0 < N := by exact_mod_cast hNrealpos
  have hNx : 2 < (N : ℝ) * x := (div_lt_iff₀ hxpos).mp hN
  refine ⟨N, hNnat, ?_⟩
  apply (div_le_iff₀ hNrealpos).2
  simpa [mul_comm] using (le_of_lt hNx)

theorem gap5 :
    ∀ x ∈ Set.Icc (0 : ℝ) 1, x ≠ 0 →
      ∃ N : ℕ, 0 < N ∧ 2 / (N : ℝ) ≤ x := by
  exact gap4

theorem gap6 :
    ∀ (N n : ℕ), 0 < N → N < n →
      2 / (n : ℝ) < 2 / (N : ℝ) := by
  intro N n hN hNn
  have hNreal : 0 < (N : ℝ) := by exact_mod_cast hN
  have hNnreal : (N : ℝ) < (n : ℝ) := by exact_mod_cast hNn
  have hrecip : 1 / (n : ℝ) < 1 / (N : ℝ) :=
    one_div_lt_one_div_of_lt hNreal hNnreal
  have hscaled := mul_lt_mul_of_pos_left hrecip (show (0 : ℝ) < 2 by norm_num)
  simpa [div_eq_mul_inv] using hscaled

theorem gap7 :
    ∀ x ∈ Set.Icc (0 : ℝ) 1, x ≠ 0 →
      ∃ N : ℕ, ∀ n : ℕ, N < n → 2 / (n : ℝ) < x := by
  intro x hx hne
  rcases gap4 x hx hne with ⟨N, hNpos, hNx⟩
  refine ⟨N, ?_⟩
  intro n hNn
  exact lt_of_lt_of_le (gap6 N n hNpos hNn) hNx

theorem gap8 :
    ∀ x ∈ Set.Icc (0 : ℝ) 1, x ≠ 0 →
      ∃ N : ℕ, ∀ n : ℕ, N < n → 2 / (n : ℝ) < x := by
  exact gap7

theorem gap9 :
    ∀ x ∈ Set.Icc (0 : ℝ) 1, x ≠ 0 →
      ∃ N : ℕ, ∀ n : ℕ, N < n → term n x = 0 := by
  intro x hx hne
  rcases gap7 x hx hne with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hNn
  have hlt : 2 / (n : ℝ) < x := hN n hNn
  have hnNat : 0 < n := lt_of_le_of_lt (Nat.zero_le N) hNn
  have hnReal : 0 < (n : ℝ) := by exact_mod_cast hnNat
  have honeTwo : 1 / (n : ℝ) < 2 / (n : ℝ) :=
    (div_lt_div_iff_of_pos_right hnReal).2 (by norm_num)
  unfold term
  split
  · rename_i hfirst
    exfalso
    linarith [hfirst.2, honeTwo, hlt]
  · split
    · rename_i hsecond
      exfalso
      linarith [hsecond.2, hlt]
    · rfl

theorem gap10 :
    ∀ x ∈ Set.Icc (0 : ℝ) 1, x ≠ 0 →
      Tendsto (fun n : ℕ => term n x) atTop (𝓝 0) := by
  intro x hx hne
  rcases gap9 x hx hne with ⟨N, hN⟩
  have heq : (fun n : ℕ => term n x) =ᶠ[atTop] (fun _ : ℕ => (0 : ℝ)) := by
    filter_upwards [eventually_gt_atTop N] with n hn
    exact hN n hn
  exact (tendsto_congr' heq).2 tendsto_const_nhds

theorem gap11 :
    ∀ x ∈ Set.Icc (0 : ℝ) 1,
      Tendsto (fun n : ℕ => term n x) atTop (𝓝 0) := by
  intro x hx
  by_cases hzero : x = 0
  · subst x
    exact gap2
  · exact gap10 x hx hzero

theorem gap12 :
    ∀ (n : ℕ) (ε₀ : ℝ), 1 ≤ n → 0 < ε₀ → ε₀ < 1 →
      |term n (1 / (n : ℝ) ^ 2)| = (n : ℝ) ^ 2 * (1 / (n : ℝ) ^ 2) := by
  intro n ε₀ hn hε hε1
  have hnReal : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnPos : 0 < (n : ℝ) := lt_of_lt_of_le zero_lt_one hnReal
  have hprod : 0 ≤ (n : ℝ) * ((n : ℝ) - 1) :=
    mul_nonneg hnPos.le (sub_nonneg.mpr hnReal)
  have hsq : (n : ℝ) ≤ (n : ℝ) ^ 2 := by
    nlinarith
  have hyPos : 0 < 1 / (n : ℝ) ^ 2 :=
    div_pos zero_lt_one (pow_pos hnPos 2)
  have hyNonneg : 0 ≤ 1 / (n : ℝ) ^ 2 := hyPos.le
  have hyLe : 1 / (n : ℝ) ^ 2 ≤ 1 / (n : ℝ) := by
    apply (div_le_div_iff₀ (pow_pos hnPos 2) hnPos).2
    simpa using hsq
  unfold term
  rw [if_pos ⟨hyNonneg, hyLe⟩]
  exact abs_of_nonneg (mul_nonneg (sq_nonneg (n : ℝ)) hyNonneg)

theorem gap13 :
    ∀ n : ℕ, 1 ≤ n →
      (n : ℝ) ^ 2 * (1 / (n : ℝ) ^ 2) = 1 := by
  intro n hn
  have hnNatPos : 0 < n := lt_of_lt_of_le Nat.zero_lt_one hn
  have hnPos : 0 < (n : ℝ) := by exact_mod_cast hnNatPos
  have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hnPos
  field_simp [hn0]

theorem gap14 :
    ∀ ε₀ : ℝ, 0 < ε₀ → ε₀ < 1 → 1 > ε₀ := by
  intro ε₀ hpos hlt
  exact hlt

theorem gap15 :
    ∀ (n : ℕ) (ε₀ : ℝ), 1 ≤ n → 0 < ε₀ → ε₀ < 1 →
      |term n (1 / (n : ℝ) ^ 2)| > ε₀ := by
  intro n ε₀ hn hε hε1
  rw [gap12 n ε₀ hn hε hε1, gap13 n hn]
  exact hε1

theorem gap16 :
    ¬ UniformlyConvergesOn term (fun _ => 0) (Set.Icc (0 : ℝ) 1) := by
  intro hUniform
  rcases hUniform (1 / 2 : ℝ) (by norm_num) with ⟨N, hN⟩
  have hn : 1 ≤ N + 1 := Nat.succ_le_succ (Nat.zero_le N)
  have hnReal : (1 : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := by exact_mod_cast hn
  have hnPos : 0 < ((N + 1 : ℕ) : ℝ) := lt_of_lt_of_le zero_lt_one hnReal
  have hprod : 0 ≤ ((N + 1 : ℕ) : ℝ) * (((N + 1 : ℕ) : ℝ) - 1) :=
    mul_nonneg hnPos.le (sub_nonneg.mpr hnReal)
  have hsq : (1 : ℝ) ≤ ((N + 1 : ℕ) : ℝ) ^ 2 := by
    nlinarith
  have hxPos : 0 < 1 / ((N + 1 : ℕ) : ℝ) ^ 2 :=
    div_pos zero_lt_one (pow_pos hnPos 2)
  have hxLe : 1 / ((N + 1 : ℕ) : ℝ) ^ 2 ≤ 1 := by
    apply (div_le_iff₀ (pow_pos hnPos 2)).2
    simpa using hsq
  have hxMem : 1 / ((N + 1 : ℕ) : ℝ) ^ 2 ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨hxPos.le, hxLe⟩
  have hsmall := hN (N + 1) (Nat.lt_succ_self N)
    (1 / ((N + 1 : ℕ) : ℝ) ^ 2) hxMem
  simp only [sub_zero] at hsmall
  have hlarge := gap15 (N + 1) (1 / 2 : ℝ) hn (by norm_num) (by norm_num)
  linarith

theorem gap17 :
    (∀ x ∈ Set.Icc (0 : ℝ) 1,
      Tendsto (fun n : ℕ => term n x) atTop (𝓝 0)) ∧
      ¬ UniformlyConvergesOn term (fun _ => 0) (Set.Icc (0 : ℝ) 1) := by
  exact ⟨gap11, gap16⟩

end

end ProofGap.Exercise2763
