import ProofGapLean.Prelude.Analysis
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

open scoped Interval

namespace ProofGap.Exercise2540

noncomputable section

def integrand (x : ℝ) : ℝ := 1 / (1 + x ^ 2)
def targetIntegral : ℝ := ∫ x in (0 : ℝ)..1, integrand x
def fourthDerivative (x : ℝ) : ℝ :=
  24 * (1 - 10 * x ^ 2 + 5 * x ^ 4) / (1 + x ^ 2) ^ 5
def mesh (i : ℕ) : ℝ := i / 12
def sample (i : ℕ) : ℝ := integrand (mesh i)
def simpsonApprox : ℝ :=
  1 / 36 *
    (sample 0 + sample 12 +
      4 * (sample 1 + sample 3 + sample 5 + sample 7 + sample 9 + sample 11) +
      2 * (sample 2 + sample 4 + sample 6 + sample 8 + sample 10))
def remainder : ℝ := targetIntegral - simpsonApprox

private theorem pi_tight_bounds :
    (3.1415926535 : ℝ) < Real.pi ∧ Real.pi < (3.1415926536 : ℝ) := by
  constructor
  · have h := Real.pi_gt_d20
    norm_num at h ⊢
    linarith
  · have h := Real.pi_lt_d20
    norm_num at h ⊢
    linarith

theorem gap1 : Real.pi / 4 = targetIntegral := by
  unfold targetIntegral
  calc
    Real.pi / 4 = Real.arctan 1 - Real.arctan 0 := by
      rw [Real.arctan_one, Real.arctan_zero]
      ring
    _ = ∫ x in (0 : ℝ)..1, integrand x := by
      symm
      apply intervalIntegral.integral_eq_sub_of_hasDerivAt
      · intro x hx
        simpa [integrand, one_div] using Real.hasDerivAt_arctan x
      · have hcont : Continuous integrand := by
          unfold integrand
          exact continuous_const.div
            (continuous_const.add (continuous_id.pow 2)) (fun x => by positivity)
        exact hcont.intervalIntegrable (μ := MeasureTheory.volume) 0 1

theorem gap2 :
    ∃ ξ ∈ Set.Ioo (0 : ℝ) 1,
      remainder =
        -(1 / (180 * 12 ^ 4) : ℝ) * fourthDerivative ξ := by
  let y : ℝ := -remainder * (180 * 12 ^ 4)
  have hy : y ∈ Set.Ioo (-3 : ℝ) 24 := by
    rcases pi_tight_bounds with ⟨hpiLower, hpiUpper⟩
    constructor
    · dsimp [y]
      simp only [remainder]
      rw [← gap1]
      norm_num [simpsonApprox, sample, mesh, integrand] at hpiLower hpiUpper ⊢
      linarith
    · dsimp [y]
      simp only [remainder]
      rw [← gap1]
      norm_num [simpsonApprox, sample, mesh, integrand] at hpiLower hpiUpper ⊢
      linarith
  have hcont :
      ContinuousOn (fun x : ℝ => -fourthDerivative x) (Set.Icc 0 1) := by
    apply Continuous.continuousOn
    unfold fourthDerivative
    have hnum :
        Continuous (fun x : ℝ => 24 * (1 - 10 * x ^ 2 + 5 * x ^ 4)) := by
      fun_prop
    have hden : Continuous (fun x : ℝ => (1 + x ^ 2) ^ 5) := by
      fun_prop
    exact (hnum.div hden (fun x => by positivity)).neg
  have hy_neg :
      -y ∈ Set.Icc (-fourthDerivative 0) (-fourthDerivative 1) := by
    constructor
    · norm_num [fourthDerivative]
      linarith [hy.2]
    · norm_num [fourthDerivative]
      linarith [hy.1]
  have hsubset :
      Set.Icc (-fourthDerivative 0) (-fourthDerivative 1) ⊆
        (fun x : ℝ => -fourthDerivative x) '' Set.Icc 0 1 :=
    intermediate_value_Icc (by norm_num : (0 : ℝ) ≤ 1) hcont
  rcases hsubset hy_neg with ⟨ξ, hξ, hξval⟩
  have hξ_ne_zero : ξ ≠ 0 := by
    intro h
    subst ξ
    norm_num [fourthDerivative] at hξval
    linarith [hy.2]
  have hξ_ne_one : ξ ≠ 1 := by
    intro h
    subst ξ
    norm_num [fourthDerivative] at hξval
    linarith [hy.1]
  have hξ_open : ξ ∈ Set.Ioo (0 : ℝ) 1 := by
    exact ⟨lt_of_le_of_ne hξ.1 (Ne.symm hξ_ne_zero),
      lt_of_le_of_ne hξ.2 hξ_ne_one⟩
  refine ⟨ξ, hξ_open, ?_⟩
  have hf : fourthDerivative ξ = y := by
    linarith [hξval]
  rw [hf]
  dsimp [y]
  ring

theorem gap3 (x : ℝ) :
    fourthDerivative x =
      24 * (1 - 10 * x ^ 2 + 5 * x ^ 4) / (1 + x ^ 2) ^ 5 := by
  rfl

theorem gap4 (x : ℝ) :
    fourthDerivative x =
      24 * (1 - 10 * x ^ 2 + 5 * x ^ 4) / (1 + x ^ 2) ^ 5 := by
  rfl

theorem gap5 (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    |fourthDerivative x| ≤ 24 := by
  rw [gap3]
  let y : ℝ := x ^ 2
  have hy0 : 0 ≤ y := by
    dsimp [y]
    positivity
  have hy2 : 0 ≤ y ^ 2 := pow_nonneg hy0 2
  have hy3 : 0 ≤ y ^ 3 := pow_nonneg hy0 3
  have hy4 : 0 ≤ y ^ 4 := pow_nonneg hy0 4
  have hy5 : 0 ≤ y ^ 5 := pow_nonneg hy0 5
  have hquad : 0 ≤ 15 * y ^ 2 - 5 * y + 2 := by
    nlinarith [sq_nonneg (y - (1 / 6 : ℝ))]
  have hlower :
      -(1 + y) ^ 5 ≤ 1 - 10 * y + 5 * y ^ 2 := by
    nlinarith [hquad, hy3, hy4, hy5]
  have hupper :
      1 - 10 * y + 5 * y ^ 2 ≤ (1 + y) ^ 5 := by
    nlinarith [hy0, hy2, hy3, hy4, hy5]
  have hp : |1 - 10 * y + 5 * y ^ 2| ≤ (1 + y) ^ 5 :=
    abs_le.2 ⟨hlower, hupper⟩
  have hp_x :
      |1 - 10 * x ^ 2 + 5 * x ^ 4| ≤ (1 + x ^ 2) ^ 5 := by
    dsimp [y] at hp
    convert hp using 1 <;> ring
  have hd : 0 < (1 + x ^ 2) ^ 5 := by positivity
  calc
    |24 * (1 - 10 * x ^ 2 + 5 * x ^ 4) / (1 + x ^ 2) ^ 5| =
        24 * |1 - 10 * x ^ 2 + 5 * x ^ 4| / (1 + x ^ 2) ^ 5 := by
      rw [abs_div, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 24),
        abs_of_pos hd]
    _ ≤ 24 * (1 + x ^ 2) ^ 5 / (1 + x ^ 2) ^ 5 := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hp_x (by norm_num)) (le_of_lt hd)
    _ = 24 := by
      field_simp [ne_of_gt hd]

theorem gap6 (R : ℕ → ℝ) (n : ℕ) (hn : 0 < n)
    (hR : ∃ ξ ∈ Set.Ioo (0 : ℝ) 1,
      R n = -(1 / (180 * n ^ 4) : ℝ) * fourthDerivative ξ) :
    |R n| ≤ (24 : ℝ) / (180 * n ^ 4) := by
  rcases hR with ⟨ξ, hξ, hRn⟩
  have hξcc : ξ ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨le_of_lt hξ.1, le_of_lt hξ.2⟩
  have hfourth := gap5 ξ hξcc
  have hnR : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have hd : 0 < (180 : ℝ) * (n : ℝ) ^ 4 := by positivity
  change |R n| ≤ 24 / ((180 : ℝ) * (n : ℝ) ^ 4)
  rw [hRn]
  simp only [abs_mul, abs_neg, abs_div, abs_one, abs_of_pos hd]
  calc
    (1 / ((180 : ℝ) * (n : ℝ) ^ 4)) * |fourthDerivative ξ| ≤
        (1 / ((180 : ℝ) * (n : ℝ) ^ 4)) * 24 := by
      exact mul_le_mul_of_nonneg_left hfourth (by positivity)
    _ = 24 / ((180 : ℝ) * (n : ℝ) ^ 4) := by ring

theorem gap7 (n : ℕ) (hn : n = 12) :
    (24 : ℝ) / (180 * n ^ 4) < 1 / 100000 := by
  subst n
  norm_num

theorem gap8 (n : ℕ) (hn : n = 12) :
    (24 : ℝ) / (180 * n ^ 4) < 1 / 100000 := by
  exact gap7 n hn

theorem gap9 :
    |remainder| ≤ 6.5 * 10 ^ (-6 : ℤ) := by
  have h := gap6 (fun _ : ℕ => remainder) 12 (by norm_num) gap2
  norm_num at h ⊢
  linarith

theorem gap10 : mesh 0 = 0 := by
  norm_num [mesh]
theorem gap11 : sample 0 = 1 := by
  norm_num [sample, mesh, integrand]
theorem gap12 : mesh 1 = 1 / 12 := by
  norm_num [mesh]
theorem gap13 : |sample 1 - 0.993103| < 0.000001 := by
  norm_num [sample, mesh, integrand, abs_lt]
theorem gap14 : mesh 2 = 1 / 6 := by
  norm_num [mesh]
theorem gap15 : |sample 2 - 0.972973| < 0.000001 := by
  norm_num [sample, mesh, integrand, abs_lt]
theorem gap16 : mesh 3 = 1 / 4 := by
  norm_num [mesh]
theorem gap17 : |sample 3 - 0.941176| < 0.000001 := by
  norm_num [sample, mesh, integrand, abs_lt]
theorem gap18 : mesh 4 = 1 / 3 := by
  norm_num [mesh]
theorem gap19 : |sample 4 - 0.900000| < 0.000001 := by
  norm_num [sample, mesh, integrand, abs_lt]
theorem gap20 : mesh 5 = 5 / 12 := by
  norm_num [mesh]
theorem gap21 : |sample 5 - 0.852071| < 0.000001 := by
  norm_num [sample, mesh, integrand, abs_lt]
theorem gap22 : mesh 6 = 1 / 2 := by
  norm_num [mesh]
theorem gap23 : |sample 6 - 0.800000| < 0.000001 := by
  norm_num [sample, mesh, integrand, abs_lt]
theorem gap24 : mesh 7 = 7 / 12 := by
  norm_num [mesh]
theorem gap25 : |sample 7 - 0.746114| < 0.000001 := by
  norm_num [sample, mesh, integrand, abs_lt]
theorem gap26 : mesh 8 = 2 / 3 := by
  norm_num [mesh]
theorem gap27 : |sample 8 - 0.692308| < 0.000001 := by
  norm_num [sample, mesh, integrand, abs_lt]
theorem gap28 : mesh 9 = 3 / 4 := by
  norm_num [mesh]
theorem gap29 : |sample 9 - 0.640000| < 0.000001 := by
  norm_num [sample, mesh, integrand, abs_lt]
theorem gap30 : mesh 10 = 5 / 6 := by
  norm_num [mesh]
theorem gap31 : |sample 10 - 0.590164| < 0.000001 := by
  norm_num [sample, mesh, integrand, abs_lt]
theorem gap32 : mesh 11 = 11 / 12 := by
  norm_num [mesh]
theorem gap33 : |sample 11 - 0.543396| < 0.000001 := by
  norm_num [sample, mesh, integrand, abs_lt]
theorem gap34 : mesh 12 = 1 := by
  norm_num [mesh]
theorem gap35 : sample 12 = 0.500000 := by
  norm_num [sample, mesh, integrand]

theorem gap36 : Real.pi / 4 = targetIntegral := by
  exact gap1

theorem gap37 :
    |targetIntegral - simpsonApprox| ≤ 6.5 * 10 ^ (-6 : ℤ) := by
  simpa [remainder] using gap9

theorem gap38 : |simpsonApprox - 0.785398| < 0.000001 := by
  norm_num [simpsonApprox, sample, mesh, integrand, abs_lt]

theorem gap39 : |Real.pi / 4 - 0.785398| < 0.000001 := by
  rcases pi_tight_bounds with ⟨hpiLower, hpiUpper⟩
  rw [abs_lt]
  constructor
  · norm_num at hpiLower hpiUpper ⊢
    linarith
  · norm_num at hpiLower hpiUpper ⊢
    linarith

theorem gap40 : |Real.pi - 0.785398 * 4| < 0.00001 := by
  have h := gap39
  rw [abs_lt] at h ⊢
  constructor
  · norm_num at h ⊢
    linarith
  · norm_num at h ⊢
    linarith

theorem gap41 : |(0.785398 : ℝ) * 4 - 3.14159| < 0.00001 := by
  norm_num [abs_lt]

theorem gap42 : |Real.pi - 3.14159| < 0.00001 := by
  have h := gap39
  rw [abs_lt] at h ⊢
  constructor
  · norm_num at h ⊢
    linarith
  · norm_num at h ⊢
    linarith

end

end ProofGap.Exercise2540
