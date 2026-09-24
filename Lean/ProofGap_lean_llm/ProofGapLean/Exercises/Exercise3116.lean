import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.EulerSineProd
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

namespace ProofGap.Exercise3116

noncomputable section

open scoped BigOperators Interval

def targetIntegral : ℝ :=
  ∫ x in (0 : ℝ)..1, (1 - x ^ 2) ^ 50

def cosineIntegral : ℝ :=
  ∫ t in (0 : ℝ)..(Real.pi / 2), Real.cos t ^ 101

def evenProduct50 : ℝ :=
  ∏ i ∈ Finset.Icc 1 50, (2 * i : ℕ)

def oddProduct51 : ℝ :=
  ∏ i ∈ Finset.Icc 0 50, (2 * i + 1 : ℕ)

def exactPrefactor : ℝ :=
  10 * Real.sqrt Real.pi / (101 * Real.sqrt 2)

def LinearizedExp (A scale θ : ℝ) : Prop :=
  |A * Real.exp (θ / scale) - A * (1 + θ / scale)| ≤
    |A| * Real.exp (1 / scale) / (2 * scale ^ 2)

/-- Source: `proof_gap/exercise_3116/1.txt`; substitution `x=sin t`. -/
theorem gap1 : targetIntegral = cosineIntegral := by
  have H :=
    integral_sin_pow_mul_cos_pow_odd
      (a := (0 : ℝ)) (b := Real.pi / 2) 0 50
  simpa [targetIntegral, cosineIntegral] using H.symm

/-- Source: `proof_gap/exercise_3116/2.txt`; Wallis integral formula. -/
theorem gap2 :
    cosineIntegral = evenProduct50 / oddProduct51 := by
  rw [cosineIntegral, EulerSine.integral_cos_pow_eq,
    show (101 : ℕ) = 2 * 50 + 1 by norm_num,
    integral_sin_pow_odd]
  norm_num [evenProduct50, oddProduct51, Finset.prod_range_succ,
    Finset.prod_Icc_succ_top]

/-- Source: `proof_gap/exercise_3116/3.txt`; convert double factorials to factorials. -/
theorem gap3 :
    evenProduct50 / oddProduct51 =
      ((2 : ℝ) ^ 100 * (Nat.factorial 50 : ℝ) ^ 2) /
        (Nat.factorial 101 : ℝ) := by
  norm_num [evenProduct50, oddProduct51, Finset.prod_Icc_succ_top,
    Nat.factorial]

/-- Source: `proof_gap/exercise_3116/4.txt`; retain both Stirling remainder bounds. -/
theorem gap4 :
    ∃ θ₁ θ₂ : ℝ,
      0 < θ₁ ∧ θ₁ < 1 ∧ 0 < θ₂ ∧ θ₂ < 1 ∧
      ((2 : ℝ) ^ 100 * (Nat.factorial 50 : ℝ) ^ 2) /
          (Nat.factorial 101 : ℝ) =
        ((2 : ℝ) ^ 100 * 100 * Real.pi * (50 : ℝ) ^ 100 *
            Real.exp (-100) * Real.exp (θ₁ / 300)) /
          (101 * Real.sqrt (2 * Real.pi * 100) * (100 : ℝ) ^ 100 *
            Real.exp (-100) * Real.exp (θ₂ / 1200)) := by
  let R : ℝ :=
    158456325028528675187087900672 /
      1273753224887747940852007777857
  let base : ℝ := 10 * Real.sqrt Real.pi / (101 * Real.sqrt 2)
  let q : ℝ := R / base
  have hR :
      ((2 : ℝ) ^ 100 * (Nat.factorial 50 : ℝ) ^ 2) /
          (Nat.factorial 101 : ℝ) = R := by
    norm_num [R, Nat.factorial]
  have hbasepos : 0 < base := by
    dsimp [base]
    positivity
  have hqpos : 0 < q := by
    dsimp [q, R]
    positivity
  have hbaseSq : base ^ 2 = 50 * Real.pi / 10201 := by
    dsimp [base]
    rw [div_pow, mul_pow, Real.sq_sqrt Real.pi_nonneg,
      mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
    ring
  have hqsq :
      q ^ 2 = R ^ 2 * 10201 / (50 * Real.pi) := by
    dsimp [q]
    rw [div_pow, hbaseSq]
    field_simp [Real.pi_ne_zero]
  have hone_lt_q : 1 < q := by
    have hsquare : 1 < q ^ 2 := by
      rw [hqsq]
      dsimp [R]
      have hp := Real.pi_lt_d20
      field_simp [Real.pi_ne_zero]
      nlinarith
    nlinarith [sq_nonneg (q - 1)]
  have hqrat : q < (2407 : ℝ) / 2400 := by
    have hsquare : q ^ 2 < ((2407 : ℝ) / 2400) ^ 2 := by
      rw [hqsq]
      dsimp [R]
      have hp := Real.pi_gt_d20
      field_simp [Real.pi_ne_zero]
      nlinarith
    nlinarith [sq_nonneg (q - 2407 / 2400)]
  have hqexp : q < Real.exp (7 / 2400) :=
    hqrat.trans (by
      simpa only [show (2407 : ℝ) / 2400 = 7 / 2400 + 1 by norm_num] using
        Real.add_one_lt_exp (by norm_num : (7 / 2400 : ℝ) ≠ 0))
  have hlogpos : 0 < Real.log q := Real.log_pos hone_lt_q
  have hlogupper : Real.log q < 7 / 2400 :=
    (Real.log_lt_iff_lt_exp hqpos).2 hqexp
  let θ : ℝ := 300 * Real.log q
  have hθ : 0 < θ ∧ θ < 7 / 8 := by
    dsimp [θ]
    constructor
    · nlinarith
    · norm_num at hlogupper ⊢
      nlinarith
  let θ₁ : ℝ := θ + 1 / 8
  let θ₂ : ℝ := 1 / 2
  have hθ₁ : 0 < θ₁ ∧ θ₁ < 1 := by
    dsimp [θ₁]
    constructor <;> nlinarith [hθ.1, hθ.2]
  have hθ₂ : 0 < θ₂ ∧ θ₂ < 1 := by
    dsimp [θ₂]
    norm_num
  have hexpquot :
      Real.exp (θ₁ / 300) / Real.exp (θ₂ / 1200) = q := by
    rw [← Real.exp_sub]
    have heq : θ₁ / 300 - θ₂ / 1200 = Real.log q := by
      dsimp [θ₁, θ₂, θ]
      ring
    rw [heq, Real.exp_log hqpos]
  have hbaseq : base * q = R := by
    dsimp [q]
    field_simp
  have hbaseOrig :
      100 * Real.pi /
          (101 * Real.sqrt (2 * Real.pi * 100)) = base := by
    have hsqrtpi : (Real.sqrt Real.pi) ^ 2 = Real.pi :=
      Real.sq_sqrt Real.pi_nonneg
    have hsqrt200 :
        Real.sqrt (2 * Real.pi * 100) =
          10 * (Real.sqrt 2 * Real.sqrt Real.pi) := by
      rw [show 2 * Real.pi * 100 = 100 * (2 * Real.pi) by ring,
        Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 100)]
      have hs100 : Real.sqrt (100 : ℝ) = 10 := by
        rw [show (100 : ℝ) = 10 ^ 2 by norm_num,
          Real.sqrt_sq_eq_abs]
        norm_num
      rw [hs100, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    dsimp [base]
    rw [hsqrt200]
    field_simp [Real.pi_ne_zero,
      Real.sqrt_ne_zero'.mpr (by positivity : (0 : ℝ) < 2),
      Real.sqrt_ne_zero'.mpr Real.pi_pos]
    nlinarith
  refine ⟨θ₁, θ₂, hθ₁.1, hθ₁.2, hθ₂.1, hθ₂.2, ?_⟩
  rw [hR]
  have hRHS :
      ((2 : ℝ) ^ 100 * 100 * Real.pi * (50 : ℝ) ^ 100 *
            Real.exp (-100) * Real.exp (θ₁ / 300)) /
          (101 * Real.sqrt (2 * Real.pi * 100) * (100 : ℝ) ^ 100 *
            Real.exp (-100) * Real.exp (θ₂ / 1200)) =
        (100 * Real.pi / (101 * Real.sqrt (2 * Real.pi * 100))) *
          (Real.exp (θ₁ / 300) / Real.exp (θ₂ / 1200)) := by
    norm_num
    field_simp [Real.pi_ne_zero, Real.exp_ne_zero,
      Real.sqrt_ne_zero'.mpr (by positivity : 0 < 2 * Real.pi * 100)]
    ring
  rw [hRHS, hbaseOrig, hexpquot, hbaseq]

/-- Source: `proof_gap/exercise_3116/5.txt`; bind the effective remainder. -/
theorem gap5 :
    ∃ θ : ℝ, |θ| < 1 ∧
      targetIntegral = exactPrefactor * Real.exp (θ / 300) := by
  obtain ⟨θ₁, θ₂, hθ₁pos, hθ₁lt, hθ₂pos, hθ₂lt, hstirling⟩ := gap4
  let θ : ℝ := θ₁ - θ₂ / 4
  have hθ : |θ| < 1 := by
    rw [abs_lt]
    dsimp [θ]
    constructor <;> nlinarith
  have hbase :
      100 * Real.pi /
          (101 * Real.sqrt (2 * Real.pi * 100)) = exactPrefactor := by
    have hsqrtpi : (Real.sqrt Real.pi) ^ 2 = Real.pi :=
      Real.sq_sqrt Real.pi_nonneg
    have hsqrt200 :
        Real.sqrt (2 * Real.pi * 100) =
          10 * (Real.sqrt 2 * Real.sqrt Real.pi) := by
      rw [show 2 * Real.pi * 100 = 100 * (2 * Real.pi) by ring,
        Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 100)]
      have hs100 : Real.sqrt (100 : ℝ) = 10 := by
        rw [show (100 : ℝ) = 10 ^ 2 by norm_num,
          Real.sqrt_sq_eq_abs]
        norm_num
      rw [hs100, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    unfold exactPrefactor
    rw [hsqrt200]
    field_simp [Real.pi_ne_zero,
      Real.sqrt_ne_zero'.mpr (by positivity : (0 : ℝ) < 2),
      Real.sqrt_ne_zero'.mpr Real.pi_pos]
    nlinarith
  have hratio :
      ((2 : ℝ) ^ 100 * (Nat.factorial 50 : ℝ) ^ 2) /
          (Nat.factorial 101 : ℝ) =
        exactPrefactor * Real.exp (θ / 300) := by
    rw [hstirling]
    have hRHS :
        ((2 : ℝ) ^ 100 * 100 * Real.pi * (50 : ℝ) ^ 100 *
              Real.exp (-100) * Real.exp (θ₁ / 300)) /
            (101 * Real.sqrt (2 * Real.pi * 100) * (100 : ℝ) ^ 100 *
              Real.exp (-100) * Real.exp (θ₂ / 1200)) =
          (100 * Real.pi / (101 * Real.sqrt (2 * Real.pi * 100))) *
            (Real.exp (θ₁ / 300) / Real.exp (θ₂ / 1200)) := by
      norm_num
      field_simp [Real.pi_ne_zero, Real.exp_ne_zero,
        Real.sqrt_ne_zero'.mpr (by positivity : 0 < 2 * Real.pi * 100)]
      ring
    rw [hRHS, hbase, ← Real.exp_sub]
    congr 2
    dsimp [θ]
    ring
  refine ⟨θ, hθ, ?_⟩
  rw [gap1, gap2, gap3]
  exact hratio

/-- Source: `proof_gap/exercise_3116/6.txt`; quantify the decimal approximation error. -/
theorem gap6 :
    ∃ θ : ℝ, |θ| < 1 ∧
      targetIntegral = (0.1241 : ℝ) * Real.exp (θ / 300) := by
  let R : ℝ :=
    158456325028528675187087900672 /
      1273753224887747940852007777857
  have hvalue : targetIntegral = R := by
    rw [gap1, gap2, gap3]
    norm_num [R, Nat.factorial]
  let q : ℝ := R / (0.1241 : ℝ)
  have hqpos : 0 < q := by
    norm_num [q, R]
  have hone_lt_q : 1 < q := by
    norm_num [q, R]
  have hqrat : q < (301 : ℝ) / 300 := by
    norm_num [q, R]
  have hqexp : q < Real.exp (1 / 300) :=
    hqrat.trans (by
      simpa [add_comm, show (301 : ℝ) / 300 = 1 / 300 + 1 by norm_num] using
        Real.add_one_lt_exp (by norm_num : (1 / 300 : ℝ) ≠ 0))
  let θ : ℝ := 300 * Real.log q
  have hθpos : 0 < θ := by
    dsimp [θ]
    have := Real.log_pos hone_lt_q
    nlinarith
  have hθupper : θ < 1 := by
    have hlog : Real.log q < 1 / 300 :=
      (Real.log_lt_iff_lt_exp hqpos).2 hqexp
    dsimp [θ]
    norm_num at hlog ⊢
    nlinarith
  refine ⟨θ, abs_lt.mpr ⟨by linarith, hθupper⟩, ?_⟩
  rw [hvalue]
  have hqeq : Real.exp (θ / 300) = q := by
    rw [show θ / 300 = Real.log q by dsimp [θ]; ring,
      Real.exp_log hqpos]
  rw [hqeq]
  dsimp [q]
  norm_num

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
      simpa [g] using congrFun (iteratedDeriv_exp_const_mul 1 (-1)) 0
    have htaylor :
        taylorWithinEval g 1 (Set.Icc 0 v) 0 v = 1 - v := by
      rw [taylorWithinEval_succ, taylor_within_zero_eval, hwithin]
      simp [g]
      ring
    have hiter :
        iteratedDeriv 2 g ξ = Real.exp (-ξ) := by
      simpa [g] using congrFun (iteratedDeriv_exp_const_mul 2 (-1)) ξ
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
      simpa using congrFun (iteratedDeriv_exp_const_mul 1 1) 0
    have htaylor :
        taylorWithinEval Real.exp 1 (Set.Icc 0 u) 0 u = 1 + u := by
      rw [taylorWithinEval_succ, taylor_within_zero_eval, hwithin]
      norm_num
    have hiter : iteratedDeriv 2 Real.exp ξ = Real.exp ξ := by
      simpa using congrFun (iteratedDeriv_exp_const_mul 2 1) ξ
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

/-- Source: `proof_gap/exercise_3116/7.txt`; replace informal `≈` by a Taylor error bound. -/
theorem gap7 :
    ∀ θ : ℝ, |θ| < 1 →
      LinearizedExp (0.1241 : ℝ) 300 θ := by
  intro θ hθ
  have hu : |θ / 300| ≤ 1 / 300 := by
    rw [abs_div]
    norm_num
    nlinarith [hθ]
  have hrem := exp_linear_remainder_bound (θ / 300) hu
  unfold LinearizedExp
  have hfactor :
      (0.1241 : ℝ) * Real.exp (θ / 300) -
          (0.1241 : ℝ) * (1 + θ / 300) =
        (0.1241 : ℝ) * (Real.exp (θ / 300) - 1 - θ / 300) := by
    ring
  rw [hfactor, abs_mul]
  norm_num at *
  calc
    (1241 / 10000 : ℝ) * |Real.exp (θ / 300) - 1 - θ / 300|
        ≤ (1241 / 10000 : ℝ) *
          (Real.exp (1 / 300) * (θ / 300) ^ 2 / 2) :=
      mul_le_mul_of_nonneg_left hrem (by norm_num)
    _ ≤ (1241 / 10000 : ℝ) * Real.exp (1 / 300) / 180000 := by
      have hθb := abs_lt.mp hθ
      have hθsq : θ ^ 2 ≤ 1 := by nlinarith [sq_nonneg θ]
      have he := Real.exp_pos (1 / 300)
      nlinarith

/-- Source: `proof_gap/exercise_3116/8.txt`; retain one witness for value and approximation. -/
theorem gap8 :
    ∃ θ : ℝ,
      |θ| < 1 ∧
      targetIntegral = (0.1241 : ℝ) * Real.exp (θ / 300) ∧
      LinearizedExp (0.1241 : ℝ) 300 θ := by
  obtain ⟨θ, hθ, hvalue⟩ := gap6
  exact ⟨θ, hθ, hvalue, gap7 θ hθ⟩

end

end ProofGap.Exercise3116
