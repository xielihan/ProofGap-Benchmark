import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Data.Nat.Factorial.Basic

namespace ProofGap.Exercise3113

noncomputable section

open scoped BigOperators

def oddProduct50 : ℝ :=
  ∏ i ∈ Finset.Icc 1 50, (2 * i - 1 : ℕ)

def evenProduct50 : ℝ :=
  ∏ i ∈ Finset.Icc 1 50, (2 * i : ℕ)

def wallisRatio : ℝ :=
  oddProduct50 / evenProduct50

def LinearizedExp (A scale θ : ℝ) : Prop :=
  |A * Real.exp (θ / scale) - A * (1 + θ / scale)| ≤
    |A| * Real.exp (1 / scale) / (2 * scale ^ 2)

private lemma oddProduct50_nat :
    (∏ i ∈ Finset.Icc 1 50, (2 * i - 1 : ℕ)) =
      2725392139750729502980713245400918633290796330545803413734328823443106201171875 := by
  native_decide

private lemma evenProduct50_nat :
    (∏ i ∈ Finset.Icc 1 50, (2 * i : ℕ)) =
      34243224702511976248246432895208185975118675053719198827915654463488000000000000 := by
  native_decide

private lemma oddProduct50_real :
    (∏ i ∈ Finset.Icc 1 50, ((2 * i - 1 : ℕ) : ℝ)) =
      (2725392139750729502980713245400918633290796330545803413734328823443106201171875 : ℝ) := by
  exact_mod_cast oddProduct50_nat

private lemma evenProduct50_real :
    (∏ i ∈ Finset.Icc 1 50, ((2 * i : ℕ) : ℝ)) =
      (34243224702511976248246432895208185975118675053719198827915654463488000000000000 : ℝ) := by
  exact_mod_cast evenProduct50_nat

private lemma evenProduct50_real' :
    (∏ i ∈ Finset.Icc (1 : ℕ) 50, (2 : ℝ) * (i : ℝ)) =
      (34243224702511976248246432895208185975118675053719198827915654463488000000000000 : ℝ) := by
  simpa only [Nat.cast_mul, Nat.cast_ofNat] using evenProduct50_real

/-- Exercise 3113, gap 1. -/
theorem gap1 :
    wallisRatio =
      (Nat.factorial 100 : ℝ) /
        ((2 : ℝ) ^ 100 * (Nat.factorial 50 : ℝ) ^ 2) := by
  norm_num [wallisRatio, oddProduct50, evenProduct50,
    oddProduct50_real, evenProduct50_real', Nat.factorial]

/--
Exercise 3113, gap 2; correct the Stirling remainder
denominators and retain `0<θᵢ<1`.
-/
theorem gap2 :
    ∃ θ₁ θ₂ : ℝ,
      0 < θ₁ ∧ θ₁ < 1 ∧ 0 < θ₂ ∧ θ₂ < 1 ∧
      (Nat.factorial 100 : ℝ) /
          ((2 : ℝ) ^ 100 * (Nat.factorial 50 : ℝ) ^ 2) =
        (Real.sqrt (2 * Real.pi * 100) * (100 : ℝ) ^ 100 *
            Real.exp (-100) * Real.exp (θ₁ / 1200)) /
          ((2 : ℝ) ^ 100 * 100 * Real.pi * (50 : ℝ) ^ 100 *
            Real.exp (-100) * Real.exp (θ₂ / 300)) := by
  let R : ℝ :=
    12611418068195524166851562157 /
      158456325028528675187087900672
  let base : ℝ := Real.sqrt (2 * Real.pi * 100) / (100 * Real.pi)
  let q : ℝ := R * Real.sqrt (50 * Real.pi)
  have hR :
      (Nat.factorial 100 : ℝ) /
          ((2 : ℝ) ^ 100 * (Nat.factorial 50 : ℝ) ^ 2) = R := by
    norm_num [R, Nat.factorial]
  have hRpos : 0 < R := by
    norm_num [R]
  have hqpos : 0 < q := by
    dsimp [q]
    positivity
  have hqsq :
      q ^ 2 = R ^ 2 * (50 * Real.pi) := by
    dsimp [q]
    rw [mul_pow, Real.sq_sqrt (by positivity : 0 ≤ 50 * Real.pi)]
  have hq_lt_one : q < 1 := by
    have hsquare : q ^ 2 < 1 := by
      rw [hqsq]
      dsimp [R]
      nlinarith [Real.pi_lt_d20]
    nlinarith [sq_nonneg (q - 1)]
  have hrat : (2400 : ℝ) / 2407 < q := by
    have hsquare : ((2400 : ℝ) / 2407) ^ 2 < q ^ 2 := by
      rw [hqsq]
      dsimp [R]
      nlinarith [Real.pi_gt_d20]
    nlinarith [sq_nonneg (q - 2400 / 2407)]
  have hexpLower :
      Real.exp (-(7 / 2400 : ℝ)) < (2400 : ℝ) / 2407 := by
    rw [Real.exp_neg]
    have H := one_div_lt_one_div_of_lt
      (by norm_num : (0 : ℝ) < 2407 / 2400)
      (show (2407 : ℝ) / 2400 < Real.exp (7 / 2400) by
        simpa only [show (2407 : ℝ) / 2400 = 7 / 2400 + 1 by norm_num] using
          Real.add_one_lt_exp (by norm_num : (7 / 2400 : ℝ) ≠ 0))
    norm_num at H ⊢
    exact H
  have hlogLower : -(7 / 2400 : ℝ) < Real.log q :=
    (Real.lt_log_iff_exp_lt hqpos).2 (hexpLower.trans hrat)
  have hlogUpper : Real.log q < 1 / 2400 := by
    exact (Real.log_lt_iff_lt_exp hqpos).2
      (hq_lt_one.trans (Real.one_lt_exp_iff.mpr (by norm_num)))
  let θ₁ : ℝ := 1 / 2
  let θ₂ : ℝ := 300 * (1 / 2400 - Real.log q)
  have hθ₁ : 0 < θ₁ ∧ θ₁ < 1 := by
    dsimp [θ₁]
    norm_num
  have hθ₂ : 0 < θ₂ ∧ θ₂ < 1 := by
    dsimp [θ₂]
    constructor <;> nlinarith
  have hbaseq : base * q = R := by
    have hsqrt :
        Real.sqrt (2 * Real.pi * 100) *
            Real.sqrt (50 * Real.pi) = 100 * Real.pi := by
      rw [← Real.sqrt_mul (by positivity : 0 ≤ 2 * Real.pi * 100)]
      have hinside :
          (2 * Real.pi * 100) * (50 * Real.pi) =
            (100 * Real.pi) ^ 2 := by ring
      rw [hinside, Real.sqrt_sq_eq_abs, abs_of_pos (by positivity)]
    dsimp [base, q]
    calc
      Real.sqrt (2 * Real.pi * 100) / (100 * Real.pi) *
            (R * Real.sqrt (50 * Real.pi)) =
          R * (Real.sqrt (2 * Real.pi * 100) *
            Real.sqrt (50 * Real.pi)) / (100 * Real.pi) := by ring
      _ = R := by rw [hsqrt]; field_simp [Real.pi_ne_zero]
  have hexpquot :
      Real.exp (θ₁ / 1200) / Real.exp (θ₂ / 300) = q := by
    rw [← Real.exp_sub]
    have heq : θ₁ / 1200 - θ₂ / 300 = Real.log q := by
      dsimp [θ₁, θ₂]
      ring
    rw [heq, Real.exp_log hqpos]
  refine ⟨θ₁, θ₂, hθ₁.1, hθ₁.2, hθ₂.1, hθ₂.2, ?_⟩
  rw [hR]
  have hRHS :
      (Real.sqrt (2 * Real.pi * 100) * (100 : ℝ) ^ 100 *
            Real.exp (-100) * Real.exp (θ₁ / 1200)) /
          ((2 : ℝ) ^ 100 * 100 * Real.pi * (50 : ℝ) ^ 100 *
            Real.exp (-100) * Real.exp (θ₂ / 300)) =
        base * (Real.exp (θ₁ / 1200) / Real.exp (θ₂ / 300)) := by
    dsimp [base]
    norm_num
    field_simp [Real.pi_ne_zero, Real.exp_ne_zero]
    ring
  rw [hRHS, hexpquot, hbaseq]

/-- Exercise 3113, gap 3; bind the effective remainder and its bound. -/
theorem gap3 :
    ∃ θ : ℝ, |θ| < 1 ∧
      wallisRatio = (0.0798 : ℝ) * Real.exp (θ / 300) := by
  let q : ℝ := wallisRatio / (0.0798 : ℝ)
  have hqpos : 0 < q := by
    norm_num [q, wallisRatio, oddProduct50, evenProduct50,
      oddProduct50_real, evenProduct50_real']
  have hq_lt_one : q < 1 := by
    norm_num [q, wallisRatio, oddProduct50, evenProduct50,
      oddProduct50_real, evenProduct50_real']
  have hrat : (300 : ℝ) / 301 < q := by
    norm_num [q, wallisRatio, oddProduct50, evenProduct50,
      oddProduct50_real, evenProduct50_real']
  have hexp :
      Real.exp (-(1 / 300 : ℝ)) < (300 : ℝ) / 301 := by
    rw [Real.exp_neg]
    have H := one_div_lt_one_div_of_lt
      (by norm_num : (0 : ℝ) < 301 / 300)
      (show (301 : ℝ) / 300 < Real.exp (1 / 300) by
        simpa only [show (301 : ℝ) / 300 = 1 + 1 / 300 by norm_num] using
          (by simpa [add_comm] using
            Real.add_one_lt_exp (by norm_num : (1 / 300 : ℝ) ≠ 0)))
    norm_num at H ⊢
    exact H
  let θ : ℝ := 300 * Real.log q
  have hθlower : -1 < θ := by
    have hlog : -(1 / 300 : ℝ) < Real.log q := by
      exact (Real.lt_log_iff_exp_lt hqpos).2 (hexp.trans hrat)
    dsimp [θ]
    nlinarith
  have hθupper : θ < 1 := by
    have hlogneg : Real.log q < 0 := (Real.log_neg hqpos hq_lt_one)
    dsimp [θ]
    nlinarith
  refine ⟨θ, (abs_lt.mpr ⟨hθlower, hθupper⟩), ?_⟩
  have hqeq : Real.exp (θ / 300) = q := by
    rw [show θ / 300 = Real.log q by dsimp [θ]; ring,
      Real.exp_log hqpos]
  rw [hqeq]
  dsimp [q]
  norm_num
  field_simp

private theorem exp_linear_remainder_bound (u : ℝ)
    (hu : |u| ≤ 1 / 300) :
    |Real.exp u - 1 - u| ≤
      Real.exp (1 / 300) * u ^ 2 / 2 := by
  by_cases hu0 : u = 0
  · simp [hu0]
  rcases lt_or_gt_of_ne hu0 with huneg | hupos
  · let v := -u
    have hvpos : 0 < v := by dsimp [v]; linarith
    have hvle : v ≤ 1 / 300 := by
      have := (abs_le.mp hu).1
      dsimp [v]
      linarith
    let g : ℝ → ℝ := fun y => Real.exp (-y)
    have hgcont : ContDiff ℝ ⊤ g := by
      dsimp [g]
      fun_prop
    obtain ⟨ξ, hξ, hrem⟩ :=
      taylor_mean_remainder_lagrange_iteratedDeriv
        (f := g) (n := 1) hvpos
          (hgcont.contDiffOn.of_le (by norm_num))
    have hwithin :
        iteratedDerivWithin 1 g (Set.Icc 0 v) 0 =
          (-1 : ℝ) * Real.exp 0 := by
      rw [iteratedDerivWithin_eq_iteratedDeriv
        (uniqueDiffOn_Icc hvpos) (hgcont.contDiffAt.of_le (by norm_num))
        (Set.left_mem_Icc.mpr hvpos.le)]
      simpa [g] using
        congrFun (iteratedDeriv_exp_const_mul 1 (-1)) 0
    have htaylor :
        taylorWithinEval g 1 (Set.Icc 0 v) 0 v = 1 - v := by
      rw [taylorWithinEval_succ, taylor_within_zero_eval, hwithin]
      simp [g]
      ring
    have hiter :
        iteratedDeriv 2 g ξ = Real.exp (-ξ) := by
      simpa [g] using
        congrFun (iteratedDeriv_exp_const_mul 2 (-1)) ξ
    rw [htaylor, hiter] at hrem
    have hexple : Real.exp (-ξ) ≤ Real.exp (1 / 300) := by
      apply Real.exp_le_exp_of_le
      linarith [hξ.1, hvle]
    have hnonneg : 0 ≤ Real.exp (-ξ) * v ^ 2 / 2 := by positivity
    have huv : u = -v := by simp [v]
    rw [huv]
    have hrem' :
        Real.exp (-v) - 1 - -v =
          Real.exp (-ξ) * v ^ 2 / 2 := by
      linarith [hrem]
    rw [hrem', abs_of_nonneg hnonneg]
    have hv2 : 0 ≤ v ^ 2 := sq_nonneg v
    nlinarith [mul_le_mul_of_nonneg_right hexple hv2]
  · have hule : u ≤ 1 / 300 := (abs_le.mp hu).2
    obtain ⟨ξ, hξ, hrem⟩ :=
      taylor_mean_remainder_lagrange_iteratedDeriv
        (f := Real.exp) (n := 1) hupos Real.contDiff_exp.contDiffOn
    have hwithin :
        iteratedDerivWithin 1 Real.exp (Set.Icc 0 u) 0 =
          Real.exp 0 := by
      rw [iteratedDerivWithin_eq_iteratedDeriv
        (uniqueDiffOn_Icc hupos) Real.contDiff_exp.contDiffAt
        (Set.left_mem_Icc.mpr hupos.le)]
      simpa using
        congrFun (iteratedDeriv_exp_const_mul 1 1) 0
    have htaylor :
        taylorWithinEval Real.exp 1 (Set.Icc 0 u) 0 u = 1 + u := by
      rw [taylorWithinEval_succ, taylor_within_zero_eval, hwithin]
      norm_num
    have hiter : iteratedDeriv 2 Real.exp ξ = Real.exp ξ := by
      simpa using
        congrFun (iteratedDeriv_exp_const_mul 2 1) ξ
    rw [htaylor, hiter] at hrem
    have hexple : Real.exp ξ ≤ Real.exp (1 / 300) :=
      Real.exp_le_exp_of_le (hξ.2.le.trans hule)
    have hnonneg : 0 ≤ Real.exp ξ * u ^ 2 / 2 := by positivity
    have hrem' :
        Real.exp u - 1 - u = Real.exp ξ * u ^ 2 / 2 := by
      linarith [hrem]
    rw [hrem', abs_of_nonneg hnonneg]
    have hu2 : 0 ≤ u ^ 2 := sq_nonneg u
    nlinarith [mul_le_mul_of_nonneg_right hexple hu2]

/-- Exercise 3113, gap 4; replace informal `≈` by a Taylor error bound. -/
theorem gap4 :
    ∀ θ : ℝ, |θ| < 1 →
      LinearizedExp (0.0798 : ℝ) 300 θ := by
  intro θ hθ
  have hu : |θ / 300| ≤ 1 / 300 := by
    rw [abs_div]
    norm_num
    nlinarith [hθ]
  have hrem := exp_linear_remainder_bound (θ / 300) hu
  unfold LinearizedExp
  have hfactor :
      (0.0798 : ℝ) * Real.exp (θ / 300) -
          (0.0798 : ℝ) * (1 + θ / 300) =
        (0.0798 : ℝ) * (Real.exp (θ / 300) - 1 - θ / 300) := by
    ring
  rw [hfactor, abs_mul]
  norm_num at *
  calc
    (399 / 5000 : ℝ) * |Real.exp (θ / 300) - 1 - θ / 300|
        ≤ (399 / 5000 : ℝ) *
          (Real.exp (1 / 300) * (θ / 300) ^ 2 / 2) :=
      mul_le_mul_of_nonneg_left hrem (by norm_num)
    _ ≤ (399 / 5000 : ℝ) * Real.exp (1 / 300) / 180000 := by
      have hθb := abs_lt.mp hθ
      have hθsq : θ ^ 2 ≤ 1 := by nlinarith [sq_nonneg θ]
      have he := Real.exp_pos (1 / 300)
      nlinarith

/-- Exercise 3113, gap 5; keep the same bounded witness and both estimates. -/
theorem gap5 :
    ∃ θ : ℝ,
      |θ| < 1 ∧
      wallisRatio = (0.0798 : ℝ) * Real.exp (θ / 300) ∧
      LinearizedExp (0.0798 : ℝ) 300 θ := by
  obtain ⟨θ, hθ, hvalue⟩ := gap3
  exact ⟨θ, hθ, hvalue, gap4 θ hθ⟩

end

end ProofGap.Exercise3113
