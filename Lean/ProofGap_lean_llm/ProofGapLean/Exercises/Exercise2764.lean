import ProofGapLean.Prelude.Analysis
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

namespace ProofGap.Exercise2764

noncomputable section

def approximation (n : ℕ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  (Int.floor (n * f x) : ℝ) / n

def UniformlyConvergesOn
    (u : ℕ → ℝ → ℝ) (F : ℝ → ℝ) (s : Set ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ N : ℕ, ∀ n : ℕ, N < n → ∀ x ∈ s, |u n x - F x| < ε

theorem gap1 :
    ∀ (n : ℕ) (f : ℝ → ℝ) (x : ℝ), 0 < n →
      |approximation n f x - f x| =
        (1 / (n : ℝ)) * |(Int.floor (n * f x) : ℝ) - n * f x| := by
  intro n f x hn
  have hnR : (0 : ℝ) < (n : ℝ) := by
    exact_mod_cast hn
  have hnne : (n : ℝ) ≠ 0 := ne_of_gt hnR
  unfold approximation
  have h :
      (Int.floor ((n : ℝ) * f x) : ℝ) / (n : ℝ) - f x =
        (1 / (n : ℝ)) *
          ((Int.floor ((n : ℝ) * f x) : ℝ) - (n : ℝ) * f x) := by
    field_simp [hnne] <;> ring
  rw [h, abs_mul, abs_of_pos (one_div_pos.mpr hnR)]

theorem gap2 :
    ∀ (n : ℕ) (f : ℝ → ℝ) (x : ℝ), 0 < n →
      (1 / (n : ℝ)) * |(Int.floor (n * f x) : ℝ) - n * f x| ≤
        1 / (n : ℝ) := by
  intro n f x hn
  have hnR : (0 : ℝ) < (n : ℝ) := by
    exact_mod_cast hn
  have hfloor :
      (Int.floor ((n : ℝ) * f x) : ℝ) ≤ (n : ℝ) * f x :=
    Int.floor_le _
  have hlt :
      (n : ℝ) * f x < (Int.floor ((n : ℝ) * f x) : ℝ) + 1 :=
    Int.lt_floor_add_one _
  have habs :
      |(Int.floor ((n : ℝ) * f x) : ℝ) - (n : ℝ) * f x| ≤ 1 := by
    rw [abs_of_nonpos (sub_nonpos.mpr hfloor)]
    linarith
  simpa only [mul_one] using
    (mul_le_mul_of_nonneg_left habs (le_of_lt (one_div_pos.mpr hnR)))

theorem gap3 :
    ∀ (n : ℕ) (f : ℝ → ℝ) (x : ℝ), 0 < n →
      |approximation n f x - f x| ≤ 1 / (n : ℝ) := by
  intro n f x hn
  calc
    |approximation n f x - f x| =
        (1 / (n : ℝ)) *
          |(Int.floor ((n : ℝ) * f x) : ℝ) - (n : ℝ) * f x| :=
      gap1 n f x hn
    _ ≤ 1 / (n : ℝ) := gap2 n f x hn

theorem gap4 :
    ∀ (a b : ℝ) (f : ℝ → ℝ) (ε : ℝ), 0 < ε →
      ∃ N : ℕ, ∀ n : ℕ, N < n →
        ∀ x ∈ Set.Icc a b, |approximation n f x - f x| < ε := by
  intro a b f ε hε
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / ε)
  refine ⟨N, ?_⟩
  intro n hn x hx
  have hn0 : 0 < n := lt_of_le_of_lt (Nat.zero_le N) hn
  have hnR : (0 : ℝ) < (n : ℝ) := by
    exact_mod_cast hn0
  have hNnR : (N : ℝ) < (n : ℝ) := by
    exact_mod_cast hn
  have hbound : 1 / ε < (n : ℝ) := lt_trans hN hNnR
  have hmul : 1 < (n : ℝ) * ε := (div_lt_iff₀ hε).mp hbound
  have hrecip : 1 / (n : ℝ) < ε := by
    apply (div_lt_iff₀ hnR).2
    simpa [mul_comm] using hmul
  exact lt_of_le_of_lt (gap3 n f x hn0) hrecip

theorem gap5 :
    ∀ (a b : ℝ) (f : ℝ → ℝ),
      UniformlyConvergesOn (fun n x => approximation n f x) f (Set.Icc a b) := by
  intro a b f
  simpa [UniformlyConvergesOn] using (gap4 a b f)

theorem gap6 :
    ∀ (a b : ℝ) (f : ℝ → ℝ),
      UniformlyConvergesOn (fun n x => approximation n f x) f (Set.Icc a b) := by
  exact gap5

end

end ProofGap.Exercise2764
