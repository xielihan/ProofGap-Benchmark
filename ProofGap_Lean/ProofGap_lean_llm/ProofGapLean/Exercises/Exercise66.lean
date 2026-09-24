import ProofGapLean.Prelude.Full
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Data.Nat.Factorial.BigOperators

open scoped Topology

/-!
# Exercise 66

Semantic formalization of Exercise 66, gaps 1,...,5.
-/

namespace ProofGap.Exercise66

noncomputable section

def rootFactorial (n : ℕ) : ℝ :=
  Real.rpow (Nat.factorial n : ℝ) (1 / (n : ℝ))

def u (n : ℕ) : ℝ :=
  1 / rootFactorial n

def upper (n : ℕ) : ℝ :=
  Real.rpow 2 (1 / (n : ℝ)) / Real.sqrt n

private theorem pow_self_le_factorial_sq (n : ℕ) :
    (n : ℝ) ^ n ≤ (Nat.factorial n : ℝ) ^ 2 := by
  have hterm : ∀ j ∈ Finset.range n,
      (n : ℝ) ≤ ((j + 1 : ℕ) : ℝ) * ((n - j : ℕ) : ℝ) := by
    intro j hj
    have hjlt : j < n := Finset.mem_range.mp hj
    have hjle : j ≤ n := Nat.le_of_lt hjlt
    have hsub : (1 : ℝ) ≤ (n - j : ℕ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.sub_ne_zero_of_lt hjlt)
    have hsub' : (1 : ℝ) ≤ (n : ℝ) - j := by
      rw [← Nat.cast_sub hjle]
      exact hsub
    have hmul : 0 ≤ (j : ℝ) * ((n : ℝ) - j - 1) :=
      mul_nonneg (by positivity) (by linarith)
    rw [Nat.cast_sub hjle]
    push_cast
    nlinarith
  have hp := Finset.prod_le_prod
    (s := Finset.range n)
    (f := fun _ : ℕ => (n : ℝ))
    (g := fun j : ℕ => ((j + 1 : ℕ) : ℝ) * ((n - j : ℕ) : ℝ))
    (fun _ _ => by positivity) hterm
  have hfirst :
      (∏ j ∈ Finset.range n, ((j + 1 : ℕ) : ℝ)) =
        (Nat.factorial n : ℝ) := by
    exact_mod_cast Finset.prod_range_add_one_eq_factorial n
  have hsecond :
      (∏ j ∈ Finset.range n, ((n - j : ℕ) : ℝ)) =
        (∏ j ∈ Finset.range n, ((j + 1 : ℕ) : ℝ)) := by
    calc
      (∏ j ∈ Finset.range n, ((n - j : ℕ) : ℝ)) =
          ∏ j ∈ Finset.range n, ((n - 1 - j + 1 : ℕ) : ℝ) := by
            apply Finset.prod_congr rfl
            intro j hj
            norm_cast
            have hjlt : j < n := Finset.mem_range.mp hj
            omega
      _ = ∏ j ∈ Finset.range n, ((j + 1 : ℕ) : ℝ) := by
        exact Finset.prod_range_reflect (fun j => ((j + 1 : ℕ) : ℝ)) n
  rw [Finset.prod_const, Finset.card_range, Finset.prod_mul_distrib,
    hfirst, hsecond, hfirst] at hp
  simpa [pow_two] using hp

/-- Exercise 66, gap 1. -/
theorem gap1 :
    ∀ n : ℕ,
      (Nat.factorial n : ℝ) ≥
        (1 / 2 : ℝ) * Real.rpow n ((n : ℝ) / 2) := by
  intro n
  have hpow := pow_self_le_factorial_sq n
  have hn : (0 : ℝ) ≤ n := by positivity
  have hrpow : 0 ≤ Real.rpow (n : ℝ) ((n : ℝ) / 2) :=
    Real.rpow_nonneg hn _
  have hfac : 0 ≤ (Nat.factorial n : ℝ) := by positivity
  have hsquare :
      (Real.rpow (n : ℝ) ((n : ℝ) / 2)) ^ 2 = (n : ℝ) ^ n := by
    calc
      (Real.rpow (n : ℝ) ((n : ℝ) / 2)) ^ 2 =
          Real.rpow (n : ℝ) (((n : ℝ) / 2) * (2 : ℕ)) :=
        (Real.rpow_mul_natCast hn _ 2).symm
      _ = Real.rpow (n : ℝ) (n : ℝ) := by congr 1 <;> norm_num
      _ = (n : ℝ) ^ n := Real.rpow_natCast _ _
  rw [← hsquare] at hpow
  nlinarith

/-- Exercise 66, gap 2; positive `n` is restored. -/
theorem gap2
    (h1 : ∀ n : ℕ,
      (Nat.factorial n : ℝ) ≥
        (1 / 2 : ℝ) * Real.rpow n ((n : ℝ) / 2)) :
    ∀ n : ℕ, 0 < n → u n ≤ upper n := by
  intro n hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  let e : ℝ := 1 / (n : ℝ)
  let twoRoot : ℝ := Real.rpow 2 e
  have he : 0 ≤ e := by
    dsimp [e]
    positivity
  have hbase :
      0 ≤ (1 / 2 : ℝ) * Real.rpow n ((n : ℝ) / 2) := by
    exact mul_nonneg (by norm_num) (Real.rpow_nonneg hnR.le _)
  have hroot :
      Real.rpow ((1 / 2 : ℝ) * Real.rpow n ((n : ℝ) / 2)) e ≤
        rootFactorial n := by
    have hmono := Real.rpow_le_rpow hbase (h1 n) he
    simpa [rootFactorial, e] using hmono
  have hlower :
      Real.rpow ((1 / 2 : ℝ) * Real.rpow n ((n : ℝ) / 2)) e =
        Real.sqrt n / twoRoot := by
    change ((1 / 2 : ℝ) * (n : ℝ) ^ ((n : ℝ) / 2)) ^ e =
      Real.sqrt n / twoRoot
    have hexp : ((n : ℝ) / 2) * e = 1 / 2 := by
      dsimp [e]
      field_simp
    rw [Real.mul_rpow (by norm_num) (Real.rpow_nonneg hnR.le _)]
    rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num,
      Real.inv_rpow (by norm_num)]
    rw [← Real.rpow_mul hnR.le, hexp, ← Real.sqrt_eq_rpow]
    simp only [twoRoot, Real.rpow_eq_pow, div_eq_mul_inv]
    ring
  rw [hlower] at hroot
  have hsqrt : 0 < Real.sqrt n := Real.sqrt_pos.2 hnR
  have htwo : 0 < twoRoot := Real.rpow_pos_of_pos (by norm_num) _
  have hquot : 0 < Real.sqrt n / twoRoot := div_pos hsqrt htwo
  calc
    u n = 1 / rootFactorial n := rfl
    _ ≤ 1 / (Real.sqrt n / twoRoot) :=
      one_div_le_one_div_of_le hquot hroot
    _ = upper n := by
      dsimp [upper, twoRoot, e]
      field_simp

/-- Exercise 66, gap 3. -/
theorem gap3 :
    Tendsto upper atTop (𝓝 0) := by
  have hexp :
      Tendsto (fun n : ℕ => (1 : ℝ) / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_one_div_atTop_nhds_zero_nat
  have hnum :
      Tendsto (fun n : ℕ => (2 : ℝ) ^ ((1 : ℝ) / (n : ℝ)))
        atTop (𝓝 1) := by
    have h := (tendsto_const_nhds (x := (2 : ℝ))).rpow hexp
      (Or.inl (by norm_num))
    simpa using h
  have hsqrt :
      Tendsto (fun n : ℕ => Real.sqrt (n : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hquot := hnum.div_atTop hsqrt
  change Tendsto
    (fun n : ℕ => Real.rpow 2 ((1 : ℝ) / (n : ℝ)) / Real.sqrt n)
    atTop (𝓝 0)
  simpa only [Real.rpow_eq_pow, one_div] using hquot

/-- Exercise 66, gap 4. -/
theorem gap4
    (h2 : ∀ n : ℕ, 0 < n → u n ≤ upper n)
    (h3 : Tendsto upper atTop (𝓝 0)) :
    Tendsto u atTop (𝓝 0) := by
  apply squeeze_zero'
  · filter_upwards with n
    unfold u rootFactorial
    exact one_div_nonneg.mpr
      (Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ Nat.factorial n) _)
  · filter_upwards [Filter.eventually_ge_atTop (1 : ℕ)] with n hn
    exact h2 n (by omega)
  · exact h3

/-- Exercise 66, gap 5. -/
theorem gap5
    (h4 : Tendsto u atTop (𝓝 0)) :
    Tendsto u atTop (𝓝 0) := by
  exact h4

end

end ProofGap.Exercise66
