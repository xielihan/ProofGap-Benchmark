import ProofGapLean.Prelude.Analysis
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Neighborhoods
import Mathlib.Analysis.SpecificLimits.Normed

namespace ProofGap.Exercise2748

noncomputable section

open Filter
open scoped Topology

def term (n : ℕ) (x : ℝ) : ℝ :=
  x ^ n - x ^ (2 * n)

def UniformlyConvergesOn
    (f : ℕ → ℝ → ℝ) (F : ℝ → ℝ) (s : Set ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ N : ℕ, ∀ n : ℕ, N < n → ∀ x ∈ s, |f n x - F x| < ε

private theorem NormedRing.tendsto_pow_atTop_nhds_zero_of_norm_lt_one
    {x : ℝ} (h : ‖x‖ < 1) :
    Tendsto (fun n : ℕ => x ^ n) atTop (𝓝 0) :=
  _root_.tendsto_pow_atTop_nhds_zero_of_norm_lt_one h

theorem gap1 :
    ∀ x ∈ Set.Icc (0 : ℝ) 1,
      Tendsto (fun n : ℕ => term n x) atTop (𝓝 0) := by
  intro x hx
  rcases eq_or_lt_of_le hx.2 with h | hxlt
  · subst x
    simpa [term] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
  · have hnorm : ‖x‖ < 1 := by
      simpa [Real.norm_eq_abs, abs_of_nonneg hx.1] using hxlt
    have hpow : Tendsto (fun n : ℕ => x ^ n) atTop (𝓝 0) :=
      NormedRing.tendsto_pow_atTop_nhds_zero_of_norm_lt_one hnorm
    simpa [term, two_mul, pow_add] using (hpow.sub (hpow.mul hpow))

theorem gap2 :
    ∀ x ∈ Set.Icc (0 : ℝ) 1, (0 : ℝ) = 0 := by
  simp

theorem gap3 :
    ∀ x ∈ Set.Icc (0 : ℝ) 1,
      Tendsto (fun n : ℕ => term n x) atTop (𝓝 0) := by
  exact gap1

theorem gap4 :
    ∀ (n : ℕ) (x : ℝ), x ∈ Set.Icc (0 : ℝ) 1 →
      |term n x| = x ^ n - x ^ (2 * n) := by
  intro n x hx
  have hpow_le_one : ∀ k : ℕ, x ^ k ≤ 1 := by
    intro k
    induction k with
    | zero => norm_num
    | succ k ih =>
        rw [pow_succ]
        calc
          x ^ k * x ≤ 1 * x := mul_le_mul_of_nonneg_right ih hx.1
          _ ≤ 1 := by simpa using hx.2
  have hxn0 : 0 ≤ x ^ n := pow_nonneg hx.1 n
  have hxn1 : x ^ n ≤ 1 := hpow_le_one n
  apply abs_of_nonneg
  unfold term
  rw [two_mul, pow_add]
  nlinarith

theorem gap5 :
    ∀ (n : ℕ) (ε₀ : ℝ), 1 ≤ n → 0 < ε₀ → ε₀ < 1 / 4 →
      let x := Real.rpow 2 (-(1 : ℝ) / n)
      |term n x| = 1 / 4 := by
  intro n ε₀ hn _ _
  dsimp
  have hnpos : 0 < n := lt_of_lt_of_le Nat.zero_lt_one hn
  have hnR : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hnpos
  have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hnR
  have hexp : (-(1 : ℝ) / (n : ℝ)) * (n : ℝ) = -1 := by
    simpa using (div_mul_cancel₀ (-(1 : ℝ)) hn0)
  have hbase : 0 < Real.rpow 2 (-(1 : ℝ) / (n : ℝ)) := by
    exact Real.rpow_pos_of_pos (by norm_num) _
  have hp :
      (Real.rpow 2 (-(1 : ℝ) / (n : ℝ))) ^ n = 1 / 2 := by
    calc
      (Real.rpow 2 (-(1 : ℝ) / (n : ℝ))) ^ n =
          Real.rpow (Real.rpow 2 (-(1 : ℝ) / (n : ℝ))) (n : ℝ) := by
            symm
            simpa [abs_of_pos hbase] using
              (Real.rpow_natCast
                (Real.rpow 2 (-(1 : ℝ) / (n : ℝ))) n)
      _ = Real.rpow 2 ((-(1 : ℝ) / (n : ℝ)) * (n : ℝ)) := by
            simpa only using
              (Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)
                (-(1 : ℝ) / (n : ℝ)) (n : ℝ)).symm
      _ = Real.rpow 2 (-1) := by rw [hexp]
      _ = (Real.rpow 2 (1 : ℝ))⁻¹ := by
            simpa only using
              (Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2) (1 : ℝ))
      _ = 1 / 2 := by
            have htwo : Real.rpow 2 (1 : ℝ) = 2 := by
              simpa only using (Real.rpow_one (2 : ℝ))
            rw [htwo]
            norm_num
  calc
    |term n (Real.rpow 2 (-(1 : ℝ) / (n : ℝ)))| =
        |(Real.rpow 2 (-(1 : ℝ) / (n : ℝ))) ^ n -
          (Real.rpow 2 (-(1 : ℝ) / (n : ℝ))) ^ n *
            (Real.rpow 2 (-(1 : ℝ) / (n : ℝ))) ^ n| := by
          simp only [term, two_mul, pow_add]
    _ = 1 / 4 := by rw [hp]; norm_num

theorem gap6 :
    ∀ ε₀ : ℝ, 0 < ε₀ → ε₀ < 1 / 4 → 1 / 4 > ε₀ := by
  intro ε₀ _ h
  exact h

theorem gap7 :
    ∀ (n : ℕ) (ε₀ : ℝ), 1 ≤ n → 0 < ε₀ → ε₀ < 1 / 4 →
      let x := Real.rpow 2 (-(1 : ℝ) / n)
      |term n x| > ε₀ := by
  intro n ε₀ hn hε hlt
  dsimp
  have hvalue := gap5 n ε₀ hn hε hlt
  dsimp at hvalue
  rw [hvalue]
  exact hlt

theorem gap8 :
    ¬ UniformlyConvergesOn term (fun _ => 0) (Set.Icc (0 : ℝ) 1) := by
  intro hU
  unfold UniformlyConvergesOn at hU
  rcases hU (1 / 8) (by norm_num) with ⟨N, hN⟩
  let n : ℕ := N + 1
  let x : ℝ := Real.rpow 2 (-(1 : ℝ) / (n : ℝ))
  have hnN : N < n := by
    simpa [n] using Nat.lt_succ_self N
  have hn : 1 ≤ n := by
    dsimp [n]
    exact Nat.succ_le_succ (Nat.zero_le N)
  have hnpos : 0 < n := lt_of_lt_of_le Nat.zero_lt_one hn
  have hnR : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hnpos
  have hx : x ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · dsimp [x]
      positivity
    · dsimp [x]
      apply Real.rpow_le_one_of_one_le_of_nonpos
      · norm_num
      · exact div_nonpos_of_nonpos_of_nonneg (by norm_num) hnR.le
  have hsmall : |term n x| < 1 / 8 := by
    simpa using hN n hnN x hx
  have hlarge : |term n x| > 1 / 8 := by
    simpa [x] using
      (gap7 n (1 / 8) hn (by norm_num) (by norm_num))
  exact (not_lt_of_ge hlarge.le) hsmall

theorem gap9 :
    ¬ UniformlyConvergesOn term (fun _ => 0) (Set.Icc (0 : ℝ) 1) := by
  exact gap8

end

end ProofGap.Exercise2748
