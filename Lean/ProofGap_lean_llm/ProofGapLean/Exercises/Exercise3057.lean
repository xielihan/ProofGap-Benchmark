import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent

namespace ProofGap.Exercise3057

noncomputable section

open Filter
open scoped BigOperators Topology

def factor (x : ℝ) (n : ℕ) : ℝ :=
  Real.cosh (x / (2 : ℝ) ^ n)

def partialProduct (x : ℝ) (n : ℕ) : ℝ :=
  ∏ i ∈ Finset.Icc 1 n, factor x i

def normalizedSinh (x : ℝ) : ℝ :=
  if x = 0 then 1 else Real.sinh x / x

def HasProduct (x L : ℝ) : Prop :=
  Tendsto (partialProduct x) atTop (𝓝 L)

private theorem sinh_div_pow_succ (x : ℝ) (n : ℕ) :
    Real.sinh (x / (2 : ℝ) ^ n) =
      2 * Real.sinh (x / (2 : ℝ) ^ (n + 1)) *
        Real.cosh (x / (2 : ℝ) ^ (n + 1)) := by
  rw [← Real.sinh_two_mul]
  congr 1
  rw [pow_succ]
  field_simp

private theorem partialProduct_formula (x : ℝ) (n : ℕ) (hx : x ≠ 0) :
    partialProduct x n =
      Real.sinh x /
        ((2 : ℝ) ^ n * Real.sinh (x / (2 : ℝ) ^ n)) := by
  induction n with
  | zero =>
      simp [partialProduct, Real.sinh_ne_zero.mpr hx]
  | succ n ih =>
      rw [partialProduct, Finset.prod_Icc_succ_top (by omega)]
      change partialProduct x n * factor x (n + 1) = _
      rw [ih]
      unfold factor
      rw [sinh_div_pow_succ]
      have hy :
          Real.sinh (x / (2 : ℝ) ^ (n + 1)) ≠ 0 := by
        rw [Real.sinh_ne_zero]
        exact div_ne_zero hx (pow_ne_zero _ (by norm_num))
      field_simp
      ring

private theorem finite_formula_algebra (x : ℝ) (n : ℕ) (hx : x ≠ 0) :
    Real.sinh x / ((2 : ℝ) ^ n * Real.sinh (x / (2 : ℝ) ^ n)) =
      (Real.sinh x / x) *
        ((x / (2 : ℝ) ^ n) / Real.sinh (x / (2 : ℝ) ^ n)) := by
  have hp : (2 : ℝ) ^ n ≠ 0 := pow_ne_zero _ (by norm_num)
  have hy : Real.sinh (x / (2 : ℝ) ^ n) ≠ 0 := by
    rw [Real.sinh_ne_zero]
    exact div_ne_zero hx hp
  field_simp

private theorem eventually_ne_zero_punctured :
    ∀ᶠ y : ℝ in 𝓝[≠] (0 : ℝ), y ≠ 0 := by
  filter_upwards [self_mem_nhdsWithin] with y hy
  simpa using hy

private theorem sinh_div_self_tendsto_punctured :
    Tendsto (fun y : ℝ => Real.sinh y / y)
      (𝓝[≠] (0 : ℝ)) (𝓝 1) := by
  have heq :
      Asymptotics.IsEquivalent (𝓝[≠] (0 : ℝ))
        Real.sinh (fun y : ℝ => y) :=
    Real.isEquivalent_sinh.mono
      (show 𝓝[≠] (0 : ℝ) ≤ 𝓝 0 from inf_le_left)
  simpa [Function.support] using
    (Asymptotics.isEquivalent_iff_tendsto_one
      eventually_ne_zero_punctured).mp heq

private theorem self_div_sinh_tendsto_punctured :
    Tendsto (fun y : ℝ => y / Real.sinh y)
      (𝓝[≠] (0 : ℝ)) (𝓝 1) := by
  simpa [Pi.div_apply, inv_div] using
    sinh_div_self_tendsto_punctured.inv₀ (by norm_num)

private theorem reciprocal_cosh_tendsto :
    Tendsto (fun y : ℝ => 1 / Real.cosh y) (𝓝 0) (𝓝 1) := by
  have hc : Tendsto Real.cosh (𝓝 0) (𝓝 1) := by
    simpa using Real.continuous_cosh.tendsto 0
  simpa [one_div] using hc.inv₀ (by norm_num)

private theorem div_pow_tendsto_zero (x : ℝ) :
    Tendsto (fun n : ℕ => x / (2 : ℝ) ^ n) atTop (𝓝 0) := by
  have hp :
      Tendsto (fun n : ℕ => ((1 / 2 : ℝ) ^ n)) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_norm_lt_one (by norm_num)
  have hm :
      Tendsto (fun n : ℕ => x * (1 / 2 : ℝ) ^ n)
        atTop (𝓝 (x * 0)) :=
    tendsto_const_nhds.mul hp
  convert hm using 1
  · funext n
    rw [div_eq_mul_inv, ← inv_pow]
    norm_num
  · ring

private theorem div_pow_tendsto_punctured
    (x : ℝ) (hx : x ≠ 0) :
    Tendsto (fun n : ℕ => x / (2 : ℝ) ^ n)
      atTop (𝓝[≠] (0 : ℝ)) := by
  rw [tendsto_nhdsWithin_iff]
  refine ⟨div_pow_tendsto_zero x, ?_⟩
  exact Eventually.of_forall fun n => by
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    exact div_ne_zero hx (pow_ne_zero _ (by norm_num))

private theorem quotient_sequence_tendsto
    (x : ℝ) (hx : x ≠ 0) :
    Tendsto
      (fun n : ℕ =>
        (x / (2 : ℝ) ^ n) / Real.sinh (x / (2 : ℝ) ^ n))
      atTop (𝓝 1) :=
  self_div_sinh_tendsto_punctured.comp
    (div_pow_tendsto_punctured x hx)

theorem gap1 (x : ℝ) (n : ℕ) :
    partialProduct x n =
      ∏ i ∈ Finset.Icc 1 n, Real.cosh (x / (2 : ℝ) ^ i) := by
  rfl

theorem gap2 (x : ℝ) (n : ℕ) (hx : x ≠ 0) :
    partialProduct x n =
      Real.sinh x / ((2 : ℝ) ^ n * Real.sinh (x / (2 : ℝ) ^ n)) := by
  exact partialProduct_formula x n hx

theorem gap3 (x : ℝ) (n : ℕ) (hx : x ≠ 0) :
    Real.sinh x / ((2 : ℝ) ^ n * Real.sinh (x / (2 : ℝ) ^ n)) =
      (Real.sinh x / x) *
        ((x / (2 : ℝ) ^ n) / Real.sinh (x / (2 : ℝ) ^ n)) := by
  exact finite_formula_algebra x n hx

theorem gap4 (x : ℝ) (n : ℕ) (hx : x ≠ 0) :
    partialProduct x n =
      (Real.sinh x / x) *
        ((x / (2 : ℝ) ^ n) / Real.sinh (x / (2 : ℝ) ^ n)) := by
  rw [partialProduct_formula x n hx]
  exact finite_formula_algebra x n hx

theorem gap5 :
    Tendsto (fun y : ℝ => y / Real.sinh y) (𝓝[≠] (0 : ℝ)) (𝓝 1) ∧
      Tendsto (fun y : ℝ => 1 / Real.cosh y) (𝓝 0) (𝓝 1) := by
  exact ⟨self_div_sinh_tendsto_punctured, reciprocal_cosh_tendsto⟩

theorem gap6 :
    Tendsto (fun y : ℝ => 1 / Real.cosh y) (𝓝 0) (𝓝 1) := by
  exact reciprocal_cosh_tendsto

theorem gap7 :
    Tendsto (fun y : ℝ => y / Real.sinh y)
      (𝓝[≠] (0 : ℝ)) (𝓝 1) := by
  exact self_div_sinh_tendsto_punctured

theorem gap8 (x : ℝ) :
    Tendsto (partialProduct x) atTop (𝓝 (normalizedSinh x)) := by
  by_cases hx : x = 0
  · subst x
    simp only [normalizedSinh, if_pos]
    change Tendsto (fun n : ℕ => partialProduct 0 n) atTop (𝓝 1)
    simpa [partialProduct, factor] using
      (tendsto_const_nhds :
        Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1))
  · unfold normalizedSinh
    rw [if_neg hx]
    have hlim :
        Tendsto
          (fun n : ℕ =>
            (Real.sinh x / x) *
              ((x / (2 : ℝ) ^ n) /
                Real.sinh (x / (2 : ℝ) ^ n)))
          atTop (𝓝 ((Real.sinh x / x) * 1)) :=
      tendsto_const_nhds.mul (quotient_sequence_tendsto x hx)
    simpa using hlim.congr'
      (Eventually.of_forall fun n =>
        ((partialProduct_formula x n hx).trans
          (finite_formula_algebra x n hx)).symm)

theorem gap9 (x : ℝ) :
    HasProduct x (normalizedSinh x) := by
  exact gap8 x

theorem gap10 (x : ℝ) :
    HasProduct x (normalizedSinh x) := by
  exact gap9 x

end

end ProofGap.Exercise3057
