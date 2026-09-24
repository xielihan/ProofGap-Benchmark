import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Neighborhoods

namespace ProofGap.Exercise3055

noncomputable section

open Filter
open scoped BigOperators Topology

def factor (n : ℕ) : ℝ :=
  Real.cos (Real.pi / (2 : ℝ) ^ (n + 1))

def partialProduct (n : ℕ) : ℝ :=
  ∏ i ∈ Finset.Icc 1 n, factor i

def HasProduct (L : ℝ) : Prop :=
  Tendsto partialProduct atTop (𝓝 L)

private theorem one_le_two_pow (n : ℕ) : (1 : ℝ) ≤ 2 ^ n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      rw [pow_succ]
      nlinarith

private theorem sin_dyadic_pos (n : ℕ) :
    0 < Real.sin (Real.pi / (2 : ℝ) ^ (n + 1)) := by
  have hpowpos : 0 < (2 : ℝ) ^ (n + 1) := by positivity
  have hpow : (1 : ℝ) < 2 ^ (n + 1) := by
    rw [show n + 1 = Nat.succ n by omega, pow_succ]
    nlinarith [one_le_two_pow n]
  have hxpos : 0 < Real.pi / (2 : ℝ) ^ (n + 1) :=
    div_pos Real.pi_pos hpowpos
  have hxlt : Real.pi / (2 : ℝ) ^ (n + 1) < Real.pi :=
    div_lt_self Real.pi_pos hpow
  exact Real.sin_pos_of_pos_of_lt_pi hxpos hxlt

private theorem partialProduct_succ (n : ℕ) :
    partialProduct (n + 1) = partialProduct n * factor (n + 1) := by
  have hset :
      Finset.Icc 1 (n + 1) =
        insert (n + 1) (Finset.Icc 1 n) := by
    ext i
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  have hnot : n + 1 ∉ Finset.Icc 1 n := by
    simp [Finset.mem_Icc]
  unfold partialProduct
  rw [hset, Finset.prod_insert hnot]
  exact mul_comm _ _

theorem gap1 (n : ℕ) :
    partialProduct n =
      ∏ i ∈ Finset.Icc 1 n,
        Real.cos (Real.pi / (2 : ℝ) ^ (i + 1)) := by
  rfl

theorem gap2 (n : ℕ) :
    partialProduct n =
      1 / (2 * Real.sin (Real.pi / (2 : ℝ) ^ (n + 1))) *
        partialProduct n *
        (2 * Real.sin (Real.pi / (2 : ℝ) ^ (n + 1))) := by
  have hs : Real.sin (Real.pi / (2 : ℝ) ^ (n + 1)) ≠ 0 :=
    ne_of_gt (sin_dyadic_pos n)
  field_simp [hs] <;> ring

theorem gap3 (n : ℕ) :
    partialProduct n =
      Real.sin (Real.pi / 2) /
        ((2 : ℝ) ^ n * Real.sin (Real.pi / (2 : ℝ) ^ (n + 1))) := by
  induction n with
  | zero =>
      simp [partialProduct]
  | succ n ih =>
      rw [partialProduct_succ n, ih]
      unfold factor
      have hangle :
          Real.pi / (2 : ℝ) ^ (n + 1) =
            2 * (Real.pi / (2 : ℝ) ^ ((n + 1) + 1)) := by
        conv_rhs => rw [pow_succ]
        field_simp <;> ring
      have hsin :
          Real.sin (Real.pi / (2 : ℝ) ^ (n + 1)) =
            2 * Real.sin (Real.pi / (2 : ℝ) ^ ((n + 1) + 1)) *
              Real.cos (Real.pi / (2 : ℝ) ^ ((n + 1) + 1)) := by
        calc
          Real.sin (Real.pi / (2 : ℝ) ^ (n + 1)) =
              Real.sin (2 * (Real.pi / (2 : ℝ) ^ ((n + 1) + 1))) :=
            congrArg Real.sin hangle
          _ = 2 * Real.sin (Real.pi / (2 : ℝ) ^ ((n + 1) + 1)) *
                Real.cos (Real.pi / (2 : ℝ) ^ ((n + 1) + 1)) :=
            Real.sin_two_mul (Real.pi / (2 : ℝ) ^ ((n + 1) + 1))
      have hs0 : Real.sin (Real.pi / (2 : ℝ) ^ (n + 1)) ≠ 0 :=
        ne_of_gt (sin_dyadic_pos n)
      have hs1 : Real.sin (Real.pi / (2 : ℝ) ^ ((n + 1) + 1)) ≠ 0 :=
        ne_of_gt (sin_dyadic_pos (n + 1))
      field_simp [hs0, hs1]
      rw [hsin]
      simp only [pow_succ]
      ring

theorem gap4 (n : ℕ) :
    Real.sin (Real.pi / 2) /
        ((2 : ℝ) ^ n * Real.sin (Real.pi / (2 : ℝ) ^ (n + 1))) =
      ((Real.pi / (2 : ℝ) ^ (n + 1)) /
        Real.sin (Real.pi / (2 : ℝ) ^ (n + 1))) *
        (2 / Real.pi) := by
  rw [Real.sin_pi_div_two]
  have hs : Real.sin (Real.pi / (2 : ℝ) ^ (n + 1)) ≠ 0 :=
    ne_of_gt (sin_dyadic_pos n)
  have hp : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  field_simp [hs, hp]
  simp only [pow_succ]

theorem gap5 (n : ℕ) :
    partialProduct n =
      ((Real.pi / (2 : ℝ) ^ (n + 1)) /
        Real.sin (Real.pi / (2 : ℝ) ^ (n + 1))) *
        (2 / Real.pi) := by
  exact (gap3 n).trans (gap4 n)

theorem gap6 :
    Tendsto partialProduct atTop (𝓝 (2 / Real.pi)) := by
  have hxform (n : ℕ) :
      Real.pi / (2 : ℝ) ^ (n + 1) =
        (Real.pi / 2) * (1 / 2 : ℝ) ^ n := by
    change Real.pi / ((2 : ℝ) ^ n * 2) =
      (Real.pi / 2) * (1 / 2 : ℝ) ^ n
    rw [div_pow]
    simp only [one_pow]
    field_simp <;> ring
  have hgeom :
      Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_norm_lt_one (by norm_num)
  have hc :
      Tendsto (fun _ : ℕ => Real.pi / 2) atTop (𝓝 (Real.pi / 2)) :=
    tendsto_const_nhds
  have hangle :
      Tendsto (fun n : ℕ => Real.pi / (2 : ℝ) ^ (n + 1)) atTop (𝓝 0) := by
    simpa only [hxform, mul_zero] using hc.mul hgeom
  have hsinc_zero : Real.sinc 0 = 1 := by
    simp [Real.sinc]
  have hsinc :
      Tendsto
        (fun n : ℕ => Real.sinc (Real.pi / (2 : ℝ) ^ (n + 1)))
        atTop (𝓝 1) := by
    simpa only [Function.comp_apply, hsinc_zero] using
      Real.continuous_sinc.continuousAt.tendsto.comp hangle
  have hinv :
      Tendsto
        (fun n : ℕ =>
          (Real.sinc (Real.pi / (2 : ℝ) ^ (n + 1)))⁻¹)
        atTop (𝓝 1) := by
    simpa using hsinc.inv₀ (by norm_num : (1 : ℝ) ≠ 0)
  have hratio (n : ℕ) :
      (Real.pi / (2 : ℝ) ^ (n + 1)) /
          Real.sin (Real.pi / (2 : ℝ) ^ (n + 1)) =
        (Real.sinc (Real.pi / (2 : ℝ) ^ (n + 1)))⁻¹ := by
    have hxn : Real.pi / (2 : ℝ) ^ (n + 1) ≠ 0 :=
      ne_of_gt (div_pos Real.pi_pos (by positivity))
    have hsn : Real.sin (Real.pi / (2 : ℝ) ^ (n + 1)) ≠ 0 :=
      ne_of_gt (sin_dyadic_pos n)
    simp only [Real.sinc, if_neg hxn]
    field_simp [hxn, hsn] <;> ring
  have hratio_t :
      Tendsto
        (fun n : ℕ =>
          (Real.pi / (2 : ℝ) ^ (n + 1)) /
            Real.sin (Real.pi / (2 : ℝ) ^ (n + 1)))
        atTop (𝓝 1) := by
    have heq :
        (fun n : ℕ =>
          (Real.pi / (2 : ℝ) ^ (n + 1)) /
            Real.sin (Real.pi / (2 : ℝ) ^ (n + 1))) =
          (fun n : ℕ =>
            (Real.sinc (Real.pi / (2 : ℝ) ^ (n + 1)))⁻¹) := by
      funext n
      exact hratio n
    rw [heq]
    exact hinv
  have hconst :
      Tendsto (fun _ : ℕ => 2 / Real.pi) atTop (𝓝 (2 / Real.pi)) :=
    tendsto_const_nhds
  have hprod :
      partialProduct =
        (fun n : ℕ =>
          ((Real.pi / (2 : ℝ) ^ (n + 1)) /
            Real.sin (Real.pi / (2 : ℝ) ^ (n + 1))) *
              (2 / Real.pi)) := by
    funext n
    exact gap5 n
  rw [hprod]
  simpa only [one_mul] using hratio_t.mul hconst

theorem gap7 : HasProduct (2 / Real.pi) := by
  exact gap6

theorem gap8 : HasProduct (2 / Real.pi) := by
  exact gap7

end

end ProofGap.Exercise3055
