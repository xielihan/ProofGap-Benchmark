import ProofGapLean.Prelude.Analysis
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

namespace ProofGap.Exercise1455_2

noncomputable section

def f (x : ℝ) : ℝ := Real.sqrt x / (x + 10000)
def realDomain : Set ℝ := Set.Ioi 0
def positiveNaturals : Set ℕ := {n | 0 < n}
def g (n : ℕ) : ℝ := Real.sqrt (n : ℝ) / ((n : ℝ) + 10000)

private theorem sqrt_ten_thousand : Real.sqrt (10000 : ℝ) = 100 := by
  calc
    Real.sqrt (10000 : ℝ) = Real.sqrt ((100 : ℝ) ^ 2) := by norm_num
    _ = |(100 : ℝ)| := Real.sqrt_sq_eq_abs 100
    _ = 100 := abs_of_nonneg (by norm_num)

theorem gap1 : IsMaxOn f realDomain 10000 := by
  intro x hx
  change 0 < x at hx
  have hden : 0 < x + 10000 := by linarith
  calc
    f x = Real.sqrt x / (x + 10000) := rfl
    _ ≤ 1 / 200 := by
      apply (div_le_iff₀ hden).2
      have hsqrt : (Real.sqrt x) ^ 2 = x := Real.sq_sqrt (le_of_lt hx)
      nlinarith [sq_nonneg (Real.sqrt x - 100)]
    _ = f 10000 := by
      rw [f, sqrt_ten_thousand]
      norm_num

theorem gap2 : sSup (g '' positiveNaturals) = f 10000 := by
  have hmem : f 10000 ∈ g '' positiveNaturals := by
    refine ⟨10000, ?_, ?_⟩
    · norm_num [positiveNaturals]
    · rfl
  have hub : ∀ z ∈ g '' positiveNaturals, z ≤ f 10000 := by
    intro z hz
    rcases hz with ⟨n, hn, rfl⟩
    change 0 < n at hn
    change f (n : ℝ) ≤ f 10000
    apply gap1
    change 0 < (n : ℝ)
    exact Nat.cast_pos.mpr hn
  have hne : (g '' positiveNaturals).Nonempty := ⟨f 10000, hmem⟩
  have hbdd : BddAbove (g '' positiveNaturals) := ⟨f 10000, hub⟩
  apply le_antisymm
  · exact csSup_le hne hub
  · exact le_csSup hbdd hmem

theorem gap3 : f 10000 = 1 / 200 := by
  rw [f, sqrt_ten_thousand]
  norm_num

theorem gap4 : sSup (g '' positiveNaturals) = 1 / 200 := by
  rw [gap2, gap3]

end
end ProofGap.Exercise1455_2
