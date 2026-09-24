import ProofGapLean.Prelude.Analysis
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Neighborhoods

namespace ProofGap.Exercise2803

noncomputable section

open Filter
open scoped Interval Topology

def term (n : ℕ) (x : ℝ) : ℝ :=
  (n : ℝ) * x * Real.exp (-(n : ℝ) * x ^ 2)

def PointwiseConvergesTo
    (f : ℕ → ℝ → ℝ) (F : ℝ → ℝ) : Prop :=
  ∀ x : ℝ, Tendsto (fun n : ℕ => f n x) atTop (𝓝 (F x))

def pointwiseLimit (_ : ℝ) : ℝ := 0

def integralSeq (n : ℕ) : ℝ :=
  ∫ x in (0 : ℝ)..1, term n x

def boundarySeq (n : ℕ) : ℝ :=
  (-(1 / 2 : ℝ) * Real.exp (-(n : ℝ) * 1 ^ 2)) -
    (-(1 / 2 : ℝ) * Real.exp (-(n : ℝ) * 0 ^ 2))

def closedFormSeq (n : ℕ) : ℝ :=
  1 / 2 - 1 / 2 * Real.exp (-(n : ℝ))

theorem gap1 :
    ∀ x : ℝ, x = 0 → ∀ n : ℕ, term n x = 0 := by
  intro x hx n
  subst x
  simp [term]

theorem gap2 :
    ∀ x : ℝ, x ≠ 0 →
      Tendsto (fun n : ℕ => term n x) atTop (𝓝 0) := by
  intro x hx
  have hx2 : 0 < x ^ 2 := sq_pos_of_ne_zero hx
  have hscale :
      Tendsto (fun n : ℕ => (n : ℝ) * x ^ 2) atTop atTop := by
    refine tendsto_atTop.2 ?_
    intro b
    obtain ⟨N : ℕ, hN⟩ := exists_nat_gt (b / x ^ 2)
    filter_upwards [eventually_ge_atTop N] with n hn
    have hNn : (N : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast hn
    have hbN : b < (N : ℝ) * x ^ 2 :=
      (div_lt_iff₀ hx2).mp hN
    exact hbN.le.trans (mul_le_mul_of_nonneg_right hNn hx2.le)
  have hdecay :
      Tendsto
        (fun n : ℕ =>
          ((n : ℝ) * x ^ 2) ^ (1 : ℕ) *
            Real.exp (-((n : ℝ) * x ^ 2)))
        atTop (𝓝 0) := by
    simpa only using
      (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp hscale
  have hout :
      Tendsto
        (fun n : ℕ =>
          (1 / x) *
            (((n : ℝ) * x ^ 2) ^ (1 : ℕ) *
              Real.exp (-((n : ℝ) * x ^ 2))))
        atTop (𝓝 ((1 / x) * 0)) :=
    tendsto_const_nhds.mul hdecay
  have heq :
      (fun n : ℕ => term n x) =
        fun n : ℕ =>
          (1 / x) *
            (((n : ℝ) * x ^ 2) ^ (1 : ℕ) *
              Real.exp (-((n : ℝ) * x ^ 2))) := by
    funext n
    unfold term
    simp only [pow_one]
    rw [show -(n : ℝ) * x ^ 2 = -((n : ℝ) * x ^ 2) by ring]
    field_simp [hx]
    <;> ring
  rw [heq]
  simpa using hout

theorem gap3 :
    PointwiseConvergesTo term (fun _ => 0) := by
  intro x
  by_cases hx : x = 0
  · simpa [term, hx] using
      (tendsto_const_nhds :
        Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
  · exact gap2 x hx

theorem gap4 :
    (∫ x in (0 : ℝ)..1, pointwiseLimit x) =
      ∫ _x in (0 : ℝ)..1, (0 : ℝ) := by
  rfl

theorem gap5 :
    (∫ _x in (0 : ℝ)..1, (0 : ℝ)) = 0 := by
  simp

theorem gap6 :
    (∫ x in (0 : ℝ)..1, pointwiseLimit x) = 0 := by
  calc
    (∫ x in (0 : ℝ)..1, pointwiseLimit x) =
        ∫ _x in (0 : ℝ)..1, (0 : ℝ) := gap4
    _ = 0 := gap5

theorem gap7 :
    integralSeq =
      fun n : ℕ =>
        ∫ x in (0 : ℝ)..1,
          (n : ℝ) * x * Real.exp (-(n : ℝ) * x ^ 2) := by
  rfl

theorem gap8 :
    integralSeq = boundarySeq := by
  funext n
  unfold integralSeq boundarySeq term
  have hsquare : ∀ x : ℝ,
      HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by
    intro x
    convert (hasDerivAt_id x).mul (hasDerivAt_id x) using 1
    · funext y
      simp [pow_two]
    · simp only [id_eq]
      ring
  have hinner : ∀ x : ℝ,
      HasDerivAt (fun y : ℝ => -(n : ℝ) * y ^ 2)
        (-(n : ℝ) * (2 * x)) x := by
    intro x
    convert
      (hasDerivAt_const x (-(n : ℝ))).mul (hsquare x)
      using 1 <;> ring
  have hderiv : ∀ x : ℝ,
      HasDerivAt
        (fun y : ℝ =>
          -(1 / 2 : ℝ) * Real.exp (-(n : ℝ) * y ^ 2))
        ((n : ℝ) * x * Real.exp (-(n : ℝ) * x ^ 2)) x := by
    intro x
    have hexp :=
      (Real.hasDerivAt_exp (-(n : ℝ) * x ^ 2)).comp x (hinner x)
    convert
      (hasDerivAt_const x (-(1 / 2 : ℝ))).mul hexp
      using 1 <;> ring
  have hinnerCont :
      Continuous (fun x : ℝ => -(n : ℝ) * x ^ 2) :=
    continuous_const.mul (continuous_id.pow 2)
  have hcont :
      Continuous
        (fun x : ℝ =>
          (n : ℝ) * x * Real.exp (-(n : ℝ) * x ^ 2)) :=
    (continuous_const.mul continuous_id).mul
      (Real.continuous_exp.comp hinnerCont)
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun y : ℝ =>
      -(1 / 2 : ℝ) * Real.exp (-(n : ℝ) * y ^ 2))
    (f' := fun y : ℝ =>
      (n : ℝ) * y * Real.exp (-(n : ℝ) * y ^ 2))
    (a := 0) (b := 1)
    (fun x _hx => hderiv x)
    (hcont.intervalIntegrable 0 1)

theorem gap9 :
    boundarySeq = closedFormSeq := by
  funext n
  simp [boundarySeq, closedFormSeq]
  <;> ring

theorem gap10 :
    Tendsto closedFormSeq atTop (𝓝 (1 / 2 : ℝ)) := by
  have hneg :
      Tendsto (fun n : ℕ => -(n : ℝ)) atTop atBot := by
    refine tendsto_atBot.2 ?_
    intro b
    obtain ⟨N : ℕ, hN⟩ := exists_nat_gt (-b)
    filter_upwards [eventually_ge_atTop N] with n hn
    have hNn : (N : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast hn
    linarith
  have hexp :
      Tendsto (fun n : ℕ => Real.exp (-(n : ℝ))) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp hneg
  change Tendsto
    (fun n : ℕ =>
      (1 / 2 : ℝ) - (1 / 2 : ℝ) * Real.exp (-(n : ℝ)))
    atTop (𝓝 (1 / 2 : ℝ))
  simpa only [mul_zero, sub_zero] using
    ((tendsto_const_nhds :
        Tendsto (fun _ : ℕ => (1 / 2 : ℝ)) atTop (𝓝 (1 / 2 : ℝ))).sub
      ((tendsto_const_nhds :
          Tendsto (fun _ : ℕ => (1 / 2 : ℝ)) atTop (𝓝 (1 / 2 : ℝ))).mul
        hexp))

theorem gap11 :
    (1 / 2 : ℝ) ≠ 0 := by
  norm_num

theorem gap12 :
    ¬ Tendsto integralSeq atTop (𝓝 0) := by
  intro hint
  have hzero : Tendsto closedFormSeq atTop (𝓝 0) := by
    rw [← gap9, ← gap8]
    exact hint
  exact gap11 (tendsto_nhds_unique gap10 hzero)

theorem gap13 :
    PointwiseConvergesTo term (fun _ => 0) ∧
      ¬ Tendsto integralSeq atTop
        (𝓝 (∫ x in (0 : ℝ)..1, pointwiseLimit x)) := by
  refine ⟨gap3, ?_⟩
  rw [gap6]
  exact gap12

end

end ProofGap.Exercise2803
