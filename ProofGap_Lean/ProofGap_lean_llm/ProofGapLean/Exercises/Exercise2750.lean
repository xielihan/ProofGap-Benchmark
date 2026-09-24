import ProofGapLean.Prelude.Analysis
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise2750

noncomputable section

open Filter
open scoped Topology

def term (n : ℕ) (x : ℝ) : ℝ :=
  (n * x) / (1 + n + x)

def UniformlyConvergesOn
    (f : ℕ → ℝ → ℝ) (F : ℝ → ℝ) (s : Set ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ N : ℕ, ∀ n : ℕ, N < n → ∀ x ∈ s, |f n x - F x| < ε

private theorem term_error_lt_aux (n : ℕ) (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) (hn : 0 < n) : |term n x - x| < 2 / (n : ℝ) := by
  have hnR : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := hnR.le
  have he : 0 < (n : ℝ) + 1 := by nlinarith
  have hd : 0 < 1 + (n : ℝ) + x := by nlinarith [hx.1]
  by_cases hzero : x = 0
  · subst x
    simpa [term] using (div_pos (show (0 : ℝ) < 2 by norm_num) hnR)
  · have hxpos : 0 < x := lt_of_le_of_ne hx.1 (Ne.symm hzero)
    have hprod : 0 ≤ x * (1 - x) := mul_nonneg hx.1 (sub_nonneg.mpr hx.2)
    have hnum_le : x + x ^ 2 ≤ 2 := by nlinarith
    have hnum_nonneg : 0 ≤ x + x ^ 2 := by nlinarith [sq_nonneg x]
    have hid : term n x - x = -((x + x ^ 2) / (1 + n + x)) := by
      unfold term
      field_simp [ne_of_gt hd] <;> ring
    rw [hid, abs_neg, abs_of_nonneg (div_nonneg hnum_nonneg hd.le)]
    calc
      (x + x ^ 2) / (1 + n + x) ≤ 2 / (1 + n + x) := (div_le_div_iff_of_pos_right hd).2 hnum_le
      _ < 2 / ((n : ℝ) + 1) := by
        apply (div_lt_div_iff₀ hd he).2
        nlinarith
      _ < 2 / (n : ℝ) := by
        apply (div_lt_div_iff₀ he hnR).2
        nlinarith

theorem gap1 :
    ∀ x ∈ Set.Icc (0 : ℝ) 1,
      Tendsto (fun n : ℕ => term n x) atTop (𝓝 x) := by
  intro x hx
  apply Metric.tendsto_atTop.2
  intro ε hε
  obtain ⟨N, hN⟩ := exists_nat_gt (2 / ε)
  refine ⟨N, ?_⟩
  intro n hn
  have hncast : (N : ℝ) ≤ (n : ℝ) := (Nat.cast_le).2 hn
  have hlarge : 2 / ε < (n : ℝ) := lt_of_lt_of_le hN hncast
  have hpos : (0 : ℝ) < 2 / ε := div_pos (by norm_num) hε
  have hnR : (0 : ℝ) < (n : ℝ) := lt_trans hpos hlarge
  have hnNat : 0 < n := Nat.cast_pos.mp hnR
  have herr := term_error_lt_aux n x hx hnNat
  have hmul : 2 < (n : ℝ) * ε := (div_lt_iff₀ hε).mp hlarge
  have hquot : 2 / (n : ℝ) < ε := by
    apply (div_lt_iff₀ hnR).2
    nlinarith
  simpa [Real.dist_eq] using lt_trans herr hquot

theorem gap2 :
    ∀ x ∈ Set.Icc (0 : ℝ) 1, x = x := by
  intro x hx
  rfl

theorem gap3 :
    ∀ x ∈ Set.Icc (0 : ℝ) 1,
      Tendsto (fun n : ℕ => term n x) atTop (𝓝 x) := by
  exact gap1

theorem gap4 :
    ∀ (n : ℕ) (x : ℝ), x ∈ Set.Icc (0 : ℝ) 1 →
      |term n x - x| = |(n * x) / (1 + n + x) - x| := by
  intro n x hx
  rfl

theorem gap5 :
    ∀ (n : ℕ) (x : ℝ), x ∈ Set.Icc (0 : ℝ) 1 →
      |(n * x) / (1 + n + x) - x| =
        (x + x ^ 2) / (1 + n + x) := by
  intro n x hx
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hd : 0 < 1 + (n : ℝ) + x := by nlinarith [hx.1]
  have hnum : 0 ≤ x + x ^ 2 := by nlinarith [hx.1, sq_nonneg x]
  have hid : (n * x) / (1 + n + x) - x = -((x + x ^ 2) / (1 + n + x)) := by
    field_simp [ne_of_gt hd] <;> ring
  rw [hid, abs_neg, abs_of_nonneg (div_nonneg hnum hd.le)]

theorem gap6 :
    ∀ (n : ℕ) (x : ℝ), x ∈ Set.Icc (0 : ℝ) 1 →
      (x + x ^ 2) / (1 + n + x) < 2 / ((n : ℝ) + 1) := by
  intro n x hx
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have he : 0 < (n : ℝ) + 1 := by nlinarith
  have hd : 0 < 1 + (n : ℝ) + x := by nlinarith [hx.1]
  by_cases hzero : x = 0
  · subst x
    simpa using (div_pos (show (0 : ℝ) < 2 by norm_num) he)
  · have hxpos : 0 < x := lt_of_le_of_ne hx.1 (Ne.symm hzero)
    have hprod : 0 ≤ x * (1 - x) := mul_nonneg hx.1 (sub_nonneg.mpr hx.2)
    have hnum : x + x ^ 2 ≤ 2 := by nlinarith
    calc
      (x + x ^ 2) / (1 + n + x) ≤ 2 / (1 + n + x) := (div_le_div_iff_of_pos_right hd).2 hnum
      _ < 2 / ((n : ℝ) + 1) := by
        apply (div_lt_div_iff₀ hd he).2
        nlinarith

theorem gap7 :
    ∀ n : ℕ, 0 < n →
      2 / ((n : ℝ) + 1) < 2 / (n : ℝ) := by
  intro n hn
  have hnR : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have hnp : 0 < (n : ℝ) + 1 := by nlinarith
  apply (div_lt_div_iff₀ hnp hnR).2
  nlinarith

theorem gap8 :
    ∀ (n : ℕ) (x : ℝ), 0 < n → x ∈ Set.Icc (0 : ℝ) 1 →
      |term n x - x| < 2 / (n : ℝ) := by
  intro n x hn hx
  exact term_error_lt_aux n x hx hn

theorem gap9 :
    ∀ (n : ℕ) (x ε : ℝ), x ∈ Set.Icc (0 : ℝ) 1 → 0 < ε →
      2 / ε < (n : ℝ) → |term n x - x| < ε := by
  intro n x ε hx hε hlarge
  have hpos : (0 : ℝ) < 2 / ε := div_pos (by norm_num) hε
  have hnR : (0 : ℝ) < (n : ℝ) := lt_trans hpos hlarge
  have hnNat : 0 < n := Nat.cast_pos.mp hnR
  have herr := gap8 n x hnNat hx
  have hmul : 2 < (n : ℝ) * ε := (div_lt_iff₀ hε).mp hlarge
  have hquot : 2 / (n : ℝ) < ε := by
    apply (div_lt_iff₀ hnR).2
    nlinarith
  exact lt_trans herr hquot

theorem gap10 :
    ∀ (n : ℕ) (x ε : ℝ), x ∈ Set.Icc (0 : ℝ) 1 → 0 < ε →
      2 / ε < (n : ℝ) → |term n x - x| < ε := by
  exact gap9

theorem gap11 :
    ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, ∀ n : ℕ, N < n →
        ∀ x ∈ Set.Icc (0 : ℝ) 1, |term n x - x| < ε := by
  intro ε hε
  obtain ⟨N, hN⟩ := exists_nat_gt (2 / ε)
  refine ⟨N, ?_⟩
  intro n hn x hx
  apply gap10 n x ε hx hε
  have hncast : (N : ℝ) < (n : ℝ) := (Nat.cast_lt).2 hn
  exact lt_trans hN hncast

theorem gap12 :
    UniformlyConvergesOn term id (Set.Icc (0 : ℝ) 1) := by
  simpa [UniformlyConvergesOn] using gap11

theorem gap13 :
    UniformlyConvergesOn term id (Set.Icc (0 : ℝ) 1) := by
  exact gap12

end

end ProofGap.Exercise2750
