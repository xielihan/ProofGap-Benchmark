import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Defs.Filter

namespace ProofGap.Exercise2916

noncomputable section

open Filter
open scoped Topology

def coefficient (n : ℕ) : ℝ :=
  1 / ((n : ℝ) * 2 ^ n)

def center : ℂ :=
  1 + Complex.I

def powerSeriesTerm (z : ℂ) (n : ℕ) : ℂ :=
  (coefficient n : ℂ) * (z - center) ^ n

def SeriesConvergesAt (z : ℂ) : Prop :=
  Summable (powerSeriesTerm z)

def HasConvergenceRadius (R : ℝ) : Prop :=
  (∀ z : ℂ, ‖z - center‖ < R → SeriesConvergesAt z) ∧
    (∀ z : ℂ, R < ‖z - center‖ → ¬SeriesConvergesAt z)

private lemma norm_powerSeriesTerm_eq_of_pos
    (z : ℂ) (n : ℕ) (hn : 0 < n) :
    ‖powerSeriesTerm z n‖ = (‖z - center‖ / 2) ^ n / (n : ℝ) := by
  have hnR : 0 < (n : ℝ) := Nat.cast_pos.2 hn
  have hc : 0 < coefficient n := by
    unfold coefficient
    exact one_div_pos.mpr
      (mul_pos hnR (pow_pos (by norm_num) n))
  have hnormcoeff : ‖(coefficient n : ℂ)‖ = coefficient n := by
    simpa [Real.norm_eq_abs, abs_of_pos hc]
  rw [powerSeriesTerm, norm_mul, norm_pow, hnormcoeff]
  unfold coefficient
  rw [div_pow]
  field_simp [ne_of_gt hnR]
  <;> ring

theorem gap1 :
    Tendsto
      (fun n : ℕ => |coefficient n / coefficient (n + 1)|)
      atTop (𝓝 2) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := exists_nat_gt (2 / ε)
  refine ⟨max N 1, ?_⟩
  intro n hn
  have hnN : N ≤ n := le_trans (le_max_left N 1) hn
  have hn1 : 1 ≤ n := le_trans (le_max_right N 1) hn
  have hnposNat : 0 < n := lt_of_lt_of_le Nat.zero_lt_one hn1
  have hnpos : 0 < (n : ℝ) := Nat.cast_pos.2 hnposNat
  have hnN' : (N : ℝ) ≤ (n : ℝ) := Nat.cast_le.2 hnN
  have h2eps : 2 < (N : ℝ) * ε := (div_lt_iff₀ hε).1 hN
  have hmul : (N : ℝ) * ε ≤ (n : ℝ) * ε :=
    mul_le_mul_of_nonneg_right hnN' (le_of_lt hε)
  have hfrac : 2 / (n : ℝ) < ε := by
    apply (div_lt_iff₀ hnpos).2
    nlinarith
  have hcast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by
    norm_num
  have hformula :
      coefficient n / coefficient (n + 1) = 2 + 2 / (n : ℝ) := by
    unfold coefficient
    rw [pow_succ, hcast]
    field_simp [ne_of_gt hnpos]
    <;> ring
  have hq : 0 ≤ 2 / (n : ℝ) :=
    div_nonneg (by norm_num) (le_of_lt hnpos)
  rw [hformula, abs_of_pos (by nlinarith [hq]), Real.dist_eq]
  simpa [abs_of_nonneg hq] using hfrac

theorem gap2 :
    HasConvergenceRadius 2 := by
  constructor
  · intro z hz
    change Summable (powerSeriesTerm z)
    let q : ℝ := ‖z - center‖ / 2
    have hq0 : 0 ≤ q := by
      dsimp [q]
      exact div_nonneg (norm_nonneg _) (by norm_num)
    have hq1 : q < 1 := by
      dsimp [q]
      linarith
    have hqnorm : ‖q‖ < 1 := by
      rw [Real.norm_eq_abs, abs_of_nonneg hq0]
      exact hq1
    refine Summable.of_norm_bounded
      (summable_geometric_of_norm_lt_one hqnorm) ?_
    intro n
    by_cases hn : n = 0
    · subst n
      simp [powerSeriesTerm, coefficient]
    · have hnposNat : 0 < n := Nat.pos_of_ne_zero hn
      rw [norm_powerSeriesTerm_eq_of_pos z n hnposNat]
      have hnR : 0 < (n : ℝ) := Nat.cast_pos.2 hnposNat
      have hn1Nat : 1 ≤ n := Nat.one_le_iff_ne_zero.2 hn
      have hn1 : (1 : ℝ) ≤ (n : ℝ) := by
        simpa only [Nat.cast_one] using
          (show ((1 : ℕ) : ℝ) ≤ (n : ℝ) from Nat.cast_le.2 hn1Nat)
      have hpow : 0 ≤ q ^ n := pow_nonneg hq0 n
      apply (div_le_iff₀ hnR).2
      nlinarith
  · intro z hz hsum
    change Summable (powerSeriesTerm z) at hsum
    let d : ℝ := ‖z - center‖ / 2 - 1
    have hd : 0 < d := by
      dsimp [d]
      linarith
    have hbern : ∀ m : ℕ, 1 + (m : ℝ) * d ≤ (1 + d) ^ m := by
      intro m
      induction m with
      | zero => simp
      | succ m ih =>
          rw [pow_succ]
          have h1d : 0 ≤ (1 + d : ℝ) := by
            linarith
          have hmul :
              (1 + (m : ℝ) * d) * (1 + d) ≤
                (1 + d) ^ m * (1 + d) :=
            mul_le_mul_of_nonneg_right ih h1d
          calc
            1 + (Nat.succ m : ℝ) * d ≤
                (1 + (m : ℝ) * d) * (1 + d) := by
              rw [Nat.cast_succ]
              have hm0 : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
              have hd2 : 0 ≤ d ^ 2 := sq_nonneg d
              have hmd2 : 0 ≤ (m : ℝ) * d ^ 2 := mul_nonneg hm0 hd2
              nlinarith [hmd2]
            _ ≤ (1 + d) ^ m * (1 + d) := hmul
    have ht : Tendsto (powerSeriesTerm z) atTop (𝓝 0) :=
      hsum.tendsto_atTop_zero
    rw [Metric.tendsto_atTop] at ht
    obtain ⟨N, hN⟩ := ht d hd
    let n : ℕ := max N 1
    have hnN : N ≤ n := le_max_left N 1
    have hn1 : 1 ≤ n := le_max_right N 1
    have hnposNat : 0 < n := lt_of_lt_of_le Nat.zero_lt_one hn1
    have hnR : 0 < (n : ℝ) := Nat.cast_pos.2 hnposNat
    have hsmall : ‖powerSeriesTerm z n‖ < d := by
      simpa only [dist_zero_right] using hN n hnN
    have hlower : d ≤ (‖z - center‖ / 2) ^ n / (n : ℝ) := by
      apply (le_div_iff₀ hnR).2
      have hb := hbern n
      have heq : 1 + d = ‖z - center‖ / 2 := by
        dsimp [d]
        ring
      rw [heq] at hb
      nlinarith
    rw [norm_powerSeriesTerm_eq_of_pos z n hnposNat] at hsmall
    exact (not_lt_of_ge hlower) hsmall

theorem gap3 :
    ∀ z : ℂ, ‖z - center‖ < 2 → SeriesConvergesAt z := by
  exact gap2.1

theorem gap4 :
    ∀ x y : ℝ,
      ‖(x : ℂ) + (y : ℂ) * Complex.I - center‖ < 2 ↔
        (x - 1) ^ 2 + (y - 1) ^ 2 < (2 : ℝ) ^ 2 := by
  intro x y
  have hsquare :
      ‖(x : ℂ) + (y : ℂ) * Complex.I - center‖ ^ 2 =
        (x - 1) ^ 2 + (y - 1) ^ 2 := by
    rw [Complex.sq_norm]
    simp [Complex.normSq_apply, center]
    ring
  constructor
  · intro h
    have hn : 0 ≤ ‖(x : ℂ) + (y : ℂ) * Complex.I - center‖ :=
      norm_nonneg _
    nlinarith
  · intro h
    have hn : 0 ≤ ‖(x : ℂ) + (y : ℂ) * Complex.I - center‖ :=
      norm_nonneg _
    nlinarith

end

end ProofGap.Exercise2916
