import ProofGapLean.Prelude.Analysis
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Neighborhoods

namespace ProofGap.Exercise2753

noncomputable section

open Filter
open scoped Topology

def term (n : ℕ) (x : ℝ) : ℝ :=
  Real.sqrt (x ^ 2 + 1 / (n : ℝ) ^ 2)

def UniformlyConvergesOn
    (f : ℕ → ℝ → ℝ) (F : ℝ → ℝ) (s : Set ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ N : ℕ, ∀ n : ℕ, N < n → ∀ x ∈ s, |f n x - F x| < ε

theorem gap1 :
    ∀ x : ℝ, Tendsto (fun n : ℕ => term n x) atTop (𝓝 (abs x)) := by
  intro x
  have hn : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hinv : Tendsto (fun n : ℕ => ((n : ℝ)⁻¹)) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hn
  have hinside :
      Tendsto (fun n : ℕ => x ^ 2 + ((n : ℝ)⁻¹) ^ 2) atTop
        (𝓝 (x ^ 2 + 0 ^ 2)) :=
    (tendsto_const_nhds :
      Tendsto (fun _ : ℕ => x ^ 2) atTop (𝓝 (x ^ 2))).add (hinv.pow 2)
  have hsqrt :
      Tendsto (fun n : ℕ => Real.sqrt (x ^ 2 + ((n : ℝ)⁻¹) ^ 2)) atTop
        (𝓝 (Real.sqrt (x ^ 2 + 0 ^ 2))) :=
    Real.continuous_sqrt.continuousAt.tendsto.comp hinside
  simpa [term, one_div, Real.sqrt_sq_eq_abs] using hsqrt

theorem gap2 :
    ∀ x : ℝ, abs x = abs x := by
  intro x
  rfl

theorem gap3 :
    ∀ x : ℝ, Tendsto (fun n : ℕ => term n x) atTop (𝓝 (abs x)) := by
  exact gap1

theorem gap4 :
    ∀ (n : ℕ) (x : ℝ), 0 < n →
      |term n x - abs x| =
        (x ^ 2 + 1 / (n : ℝ) ^ 2 - x ^ 2) / (term n x + abs x) := by
  intro n x hn
  have hnR : 0 < (n : ℝ) := by
    exact_mod_cast hn
  have hqpos : 0 < 1 / (n : ℝ) ^ 2 := by
    positivity
  have hA : 0 ≤ x ^ 2 + 1 / (n : ℝ) ^ 2 := by
    positivity
  have ht_sq :
      (term n x) ^ 2 = x ^ 2 + 1 / (n : ℝ) ^ 2 := by
    unfold term
    exact Real.sq_sqrt hA
  have ht_nonneg : 0 ≤ term n x := by
    unfold term
    exact Real.sqrt_nonneg _
  have hx_sq : (abs x) ^ 2 = x ^ 2 := sq_abs x
  have hx_nonneg : 0 ≤ abs x := abs_nonneg x
  have hprod :
      (term n x - abs x) * (term n x + abs x) =
        x ^ 2 + 1 / (n : ℝ) ^ 2 - x ^ 2 := by
    calc
      (term n x - abs x) * (term n x + abs x) =
          (term n x) ^ 2 - (abs x) ^ 2 := by ring
      _ = x ^ 2 + 1 / (n : ℝ) ^ 2 - x ^ 2 := by
        rw [ht_sq, hx_sq]
  have hlt : abs x < term n x := by
    by_contra hnot
    have hsub : term n x - abs x ≤ 0 :=
      sub_nonpos.mpr (le_of_not_gt hnot)
    have hsum : 0 ≤ term n x + abs x :=
      add_nonneg ht_nonneg hx_nonneg
    have hpnonpos :
        (term n x - abs x) * (term n x + abs x) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hsub hsum
    nlinarith [hprod, hqpos]
  have hdenpos : 0 < term n x + abs x := by
    nlinarith [hx_nonneg]
  rw [abs_of_nonneg (sub_nonneg.mpr (le_of_lt hlt))]
  exact (eq_div_iff (ne_of_gt hdenpos)).2 hprod

theorem gap5 :
    ∀ (n : ℕ) (x : ℝ), 0 < n →
      (x ^ 2 + 1 / (n : ℝ) ^ 2 - x ^ 2) / (term n x + abs x) ≤
        (1 / (n : ℝ) ^ 2) / (1 / (n : ℝ)) := by
  intro n x hn
  have hnR : 0 < (n : ℝ) := by
    exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hnR
  have hy : 0 < 1 / (n : ℝ) := by
    positivity
  have hy_sq :
      (1 / (n : ℝ)) ^ 2 = 1 / (n : ℝ) ^ 2 := by
    field_simp [hn0]
  have hA : 0 ≤ x ^ 2 + 1 / (n : ℝ) ^ 2 := by
    positivity
  have ht_sq :
      (term n x) ^ 2 = x ^ 2 + 1 / (n : ℝ) ^ 2 := by
    unfold term
    exact Real.sq_sqrt hA
  have ht_nonneg : 0 ≤ term n x := by
    unfold term
    exact Real.sqrt_nonneg _
  have hdiffprod :
      (term n x - 1 / (n : ℝ)) * (term n x + 1 / (n : ℝ)) = x ^ 2 := by
    calc
      (term n x - 1 / (n : ℝ)) * (term n x + 1 / (n : ℝ)) =
          (term n x) ^ 2 - (1 / (n : ℝ)) ^ 2 := by ring
      _ = (x ^ 2 + 1 / (n : ℝ) ^ 2) - (1 / (n : ℝ)) ^ 2 := by
        rw [ht_sq]
      _ = x ^ 2 := by
        rw [hy_sq]
        ring
  have ht_ge : 1 / (n : ℝ) ≤ term n x := by
    by_contra hnot
    have hsub : term n x - 1 / (n : ℝ) < 0 :=
      sub_neg.mpr (lt_of_not_ge hnot)
    have hsum : 0 < term n x + 1 / (n : ℝ) := by
      nlinarith
    have hpneg :
        (term n x - 1 / (n : ℝ)) * (term n x + 1 / (n : ℝ)) < 0 :=
      mul_neg_of_neg_of_pos hsub hsum
    nlinarith [hdiffprod, sq_nonneg x]
  have hden_ge :
      1 / (n : ℝ) ≤ term n x + abs x := by
    nlinarith [abs_nonneg x]
  have hdenpos : 0 < term n x + abs x :=
    lt_of_lt_of_le hy hden_ge
  have hnum :
      x ^ 2 + 1 / (n : ℝ) ^ 2 - x ^ 2 = 1 / (n : ℝ) ^ 2 := by
    ring
  have hqnonneg : 0 ≤ 1 / (n : ℝ) ^ 2 := by
    positivity
  rw [hnum]
  exact (div_le_div_iff₀ hdenpos hy).2
    (mul_le_mul_of_nonneg_left hden_ge hqnonneg)

theorem gap6 :
    ∀ n : ℕ, 0 < n →
      (1 / (n : ℝ) ^ 2) / (1 / (n : ℝ)) = 1 / (n : ℝ) := by
  intro n hn
  have hnR : 0 < (n : ℝ) := by
    exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hnR
  field_simp [hn0]

theorem gap7 :
    ∀ (n : ℕ) (x : ℝ), 0 < n →
      |term n x - abs x| ≤ 1 / (n : ℝ) := by
  intro n x hn
  calc
    |term n x - abs x| =
        (x ^ 2 + 1 / (n : ℝ) ^ 2 - x ^ 2) /
          (term n x + abs x) := gap4 n x hn
    _ ≤ (1 / (n : ℝ) ^ 2) / (1 / (n : ℝ)) := gap5 n x hn
    _ = 1 / (n : ℝ) := gap6 n hn

theorem gap8 :
    ∀ (n : ℕ) (x ε : ℝ), 0 < ε →
      1 / ε < (n : ℝ) → |term n x - abs x| < ε := by
  intro n x ε hε hnε
  have hεinv : 0 < 1 / ε := by
    positivity
  have hnR : 0 < (n : ℝ) := lt_trans hεinv hnε
  have hn : 0 < n := by
    exact_mod_cast hnR
  have hprod : 1 < (n : ℝ) * ε :=
    (div_lt_iff₀ hε).1 hnε
  have hrecip : 1 / (n : ℝ) < ε := by
    apply (div_lt_iff₀ hnR).2
    simpa [mul_comm] using hprod
  exact lt_of_le_of_lt (gap7 n x hn) hrecip

theorem gap9 :
    ∀ (n : ℕ) (x ε : ℝ), 0 < ε →
      1 / ε < (n : ℝ) → |term n x - abs x| < ε := by
  exact gap8

theorem gap10 :
    ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, ∀ n : ℕ, N < n →
        ∀ x : ℝ, |term n x - abs x| < ε := by
  intro ε hε
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / ε)
  refine ⟨N, ?_⟩
  intro n hn x
  apply gap8 n x ε hε
  have hcast : (N : ℝ) < (n : ℝ) := by
    exact_mod_cast hn
  exact lt_trans hN hcast

theorem gap11 :
    UniformlyConvergesOn term abs Set.univ := by
  unfold UniformlyConvergesOn
  intro ε hε
  obtain ⟨N, hN⟩ := gap10 ε hε
  refine ⟨N, ?_⟩
  intro n hn x hx
  exact hN n hn x

theorem gap12 :
    UniformlyConvergesOn term abs Set.univ := by
  exact gap11

end

end ProofGap.Exercise2753
