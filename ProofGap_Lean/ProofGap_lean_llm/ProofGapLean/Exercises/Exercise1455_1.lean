import ProofGapLean.Prelude.Analysis
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

namespace ProofGap.Exercise1455_1

noncomputable section

def f (x : ℝ) : ℝ := x ^ 10 / Real.rpow 2 x
def realDomain : Set ℝ := Set.Ioi 0
def positiveNaturals : Set ℕ := {n | 0 < n}
def g (n : ℕ) : ℝ := (n : ℝ) ^ 10 / Real.rpow 2 (n : ℝ)
def N : ℕ := 14
def Approx (a b ε : ℝ) : Prop := |a - b| < ε

private theorem f_le_critical {x : ℝ} (hx : 0 < x) :
    f x ≤ f (10 / Real.log 2) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have ha : 0 < 10 / Real.log 2 := div_pos (by norm_num) hlog2
  let t : ℝ := x / (10 / Real.log 2)
  have ht : 0 < t := by
    dsimp [t]
    positivity
  have hlogt := Real.log_le_sub_one_of_pos ht
  have hscaled : 10 * Real.log t ≤ 10 * (t - 1) :=
    mul_le_mul_of_nonneg_left hlogt (by norm_num)
  have hexp : Real.exp (10 * Real.log t) ≤ Real.exp (10 * (t - 1)) :=
    Real.exp_le_exp.mpr hscaled
  have hleft : Real.exp (10 * Real.log t) = t ^ 10 := by
    calc
      Real.exp (10 * Real.log t) = Real.exp (Real.log t) ^ 10 := by
        simpa using (Real.exp_nat_mul (Real.log t) 10)
      _ = t ^ 10 := by rw [Real.exp_log ht]
  have hexponent : 10 * (t - 1) = Real.log 2 * x - 10 := by
    dsimp [t]
    field_simp [ne_of_gt hlog2] <;> ring
  rw [hleft, hexponent, Real.exp_sub] at hexp
  have hcross : t ^ 10 * Real.exp 10 ≤ Real.exp (Real.log 2 * x) :=
    (le_div_iff₀ (Real.exp_pos 10)).mp hexp
  have hscaledCross :=
    mul_le_mul_of_nonneg_right hcross
      (pow_nonneg (le_of_lt ha) 10)
  have hxrel : x = t * (10 / Real.log 2) := by
    dsimp [t]
    field_simp [ne_of_gt hlog2] <;> ring
  have hxpow : x ^ 10 = t ^ 10 * (10 / Real.log 2) ^ 10 := by
    rw [hxrel, mul_pow]
  have hfinal :
      x ^ 10 * Real.exp 10 ≤
        (10 / Real.log 2) ^ 10 * Real.exp (Real.log 2 * x) := by
    rw [hxpow]
    calc
      t ^ 10 * (10 / Real.log 2) ^ 10 * Real.exp 10 =
          (t ^ 10 * Real.exp 10) * (10 / Real.log 2) ^ 10 := by ring
      _ ≤ Real.exp (Real.log 2 * x) * (10 / Real.log 2) ^ 10 := hscaledCross
      _ = (10 / Real.log 2) ^ 10 * Real.exp (Real.log 2 * x) := by ring
  have hcritexp : Real.log 2 * (10 / Real.log 2) = 10 := by
    field_simp [ne_of_gt hlog2]
  have hrpowx : Real.rpow 2 x = Real.exp (Real.log 2 * x) := by
    change (2 : ℝ) ^ x = Real.exp (Real.log 2 * x)
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hrpowcrit :
      Real.rpow 2 (10 / Real.log 2) =
        Real.exp (Real.log 2 * (10 / Real.log 2)) := by
    change (2 : ℝ) ^ (10 / Real.log 2) =
      Real.exp (Real.log 2 * (10 / Real.log 2))
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
  simp only [f]
  rw [hrpowx, hrpowcrit, hcritexp]
  exact
    (div_le_div_iff₀ (Real.exp_pos (Real.log 2 * x)) (Real.exp_pos 10)).2 hfinal

private theorem two_rpow_nat (n : ℕ) :
    Real.rpow 2 (n : ℝ) = (2 : ℝ) ^ n := by
  change (2 : ℝ) ^ (n : ℝ) = (2 : ℝ) ^ n
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
  calc
    Real.exp (Real.log 2 * (n : ℝ)) =
        Real.exp ((n : ℝ) * Real.log 2) := by
          congr 1
          ring
    _ = Real.exp (Real.log 2) ^ n := by
      simpa using (Real.exp_nat_mul (Real.log 2) n)
    _ = (2 : ℝ) ^ n := by rw [Real.exp_log (by norm_num : (0 : ℝ) < 2)]

private theorem g_decreases {n : ℕ} (hn : 15 ≤ n) :
    g (n + 1) ≤ g n := by
  have hn' : (15 : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast hn
  have hlin : 15 * ((n : ℝ) + 1) ≤ 16 * (n : ℝ) := by
    linarith
  have hp :
      (15 * ((n : ℝ) + 1)) ^ 10 ≤ (16 * (n : ℝ)) ^ 10 := by
    gcongr
  rw [mul_pow, mul_pow] at hp
  norm_num at hp
  have hpow_nonneg : 0 ≤ (n : ℝ) ^ 10 :=
    pow_nonneg (Nat.cast_nonneg n) 10
  have hnumpow : ((n : ℝ) + 1) ^ 10 ≤ 2 * (n : ℝ) ^ 10 := by
    nlinarith [hpow_nonneg]
  simp only [g]
  rw [two_rpow_nat (n + 1), two_rpow_nat n]
  simp only [Nat.cast_add, Nat.cast_one]
  have hden : (2 : ℝ) ^ (n + 1) = (2 : ℝ) ^ n * 2 := by
    exact pow_succ 2 n
  rw [hden]
  apply
    (div_le_div_iff₀
      (mul_pos (pow_pos (by norm_num : (0 : ℝ) < 2) n) (by norm_num))
      (pow_pos (by norm_num : (0 : ℝ) < 2) n)).2
  have hm :=
    mul_le_mul_of_nonneg_right hnumpow
      (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) n)
  calc
    ((n : ℝ) + 1) ^ 10 * (2 : ℝ) ^ n ≤
        (2 * (n : ℝ) ^ 10) * (2 : ℝ) ^ n := hm
    _ = (n : ℝ) ^ 10 * ((2 : ℝ) ^ n * 2) := by ring

private theorem g_le_fourteen {n : ℕ} (hn : 0 < n) :
    g n ≤ g 14 := by
  by_cases hsmall : n ≤ 14
  · interval_cases n <;>
      norm_num [g, two_rpow_nat] at hn ⊢
  · have hlarge : 15 ≤ n := by omega
    have htail : ∀ k : ℕ, g (15 + k) ≤ g 14 := by
      intro k
      induction k with
      | zero =>
          norm_num [g, two_rpow_nat]
      | succ k ih =>
          have hs : g ((15 + k) + 1) ≤ g (15 + k) :=
            g_decreases (by omega)
          simpa [Nat.add_assoc] using hs.trans ih
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hlarge
    exact htail k

private theorem supremum_g_eq :
    sSup (g '' positiveNaturals) = g 14 := by
  have hmem : g 14 ∈ g '' positiveNaturals := by
    exact ⟨14, by norm_num [positiveNaturals], rfl⟩
  have hbdd : BddAbove (g '' positiveNaturals) := by
    refine ⟨g 14, ?_⟩
    rintro y ⟨n, hn, rfl⟩
    exact g_le_fourteen hn
  apply le_antisymm
  · apply csSup_le
    · exact ⟨g 14, hmem⟩
    · rintro y ⟨n, hn, rfl⟩
      exact g_le_fourteen hn
  · exact le_csSup hbdd hmem

theorem gap1 :
    IsMaxOn f realDomain (10 / Real.log 2) := by
  intro x hx
  exact f_le_critical (show 0 < x from hx)

theorem gap2 : N = 14 := by
  rfl

theorem gap3 :
    sSup (g '' positiveNaturals) =
      max (g (N - 1)) (max (g N) (g (N + 1))) := by
  rw [supremum_g_eq]
  norm_num [N, g, two_rpow_nat]

theorem gap4 :
    sSup (g '' positiveNaturals) =
      max (g 13) (max (g 14) (g 15)) := by
  simpa [N] using gap3

theorem gap5 :
    max (g 13) (max (g 14) (g 15)) = g 14 := by
  norm_num [g, two_rpow_nat]

theorem gap6 :
    Approx (g 14) (1.77 * 10 ^ 7) (1 * 10 ^ 5) := by
  norm_num [Approx, g, two_rpow_nat, abs_lt]

theorem gap7 :
    Approx (sSup (g '' positiveNaturals)) (1.77 * 10 ^ 7)
      (1 * 10 ^ 5) := by
  rw [gap4, gap5]
  exact gap6

end
end ProofGap.Exercise1455_1
