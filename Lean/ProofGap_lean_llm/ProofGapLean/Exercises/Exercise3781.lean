import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise3781

noncomputable section

open Filter MeasureTheory Set
open scoped Interval Topology

def integrand (α x : ℝ) : ℝ :=
  Real.sin x /
    (Real.rpow x α * Real.rpow (Real.pi - x) α)

def F (α : ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..Real.pi, integrand α x

def UniformAtZero (α₀ α₁ : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ δ : ℝ, 0 < δ ∧
      ∀ α ∈ Set.Icc α₀ α₁, ∀ η : ℝ, 0 < η → η < δ →
        |∫ x in (0 : ℝ)..η, integrand α x| < ε

private lemma integrand_pi_sub (α x : ℝ) :
    integrand α (Real.pi - x) = integrand α x := by
  unfold integrand
  rw [Real.sin_pi_sub]
  have hsub : Real.pi - (Real.pi - x) = x := by ring
  rw [hsub, mul_comm]

private lemma half_integrals_eq (α : ℝ) :
    (∫ x in Real.pi / 2..Real.pi, integrand α x) =
      ∫ x in (0 : ℝ)..Real.pi / 2, integrand α x := by
  have hcomp :=
    intervalIntegral.integral_comp_sub_left
      (f := integrand α) (a := Real.pi / 2) (b := Real.pi) Real.pi
  rw [show Real.pi - Real.pi = (0 : ℝ) by ring,
    show Real.pi - Real.pi / 2 = Real.pi / 2 by ring] at hcomp
  simpa only [integrand_pi_sub] using hcomp

private lemma half_integrable_iff (α : ℝ) :
    IntervalIntegrable (integrand α) volume
        (Real.pi / 2) Real.pi ↔
      IntervalIntegrable (integrand α) volume 0 (Real.pi / 2) := by
  constructor
  · intro h
    have hc := h.comp_sub_left Real.pi
    convert hc.symm using 1
    · funext x
      exact (integrand_pi_sub α x).symm
    · ring
    · ring
  · intro h
    have hc := h.comp_sub_left Real.pi
    convert hc.symm using 1
    · funext x
      exact (integrand_pi_sub α x).symm
    · ring
    · ring

theorem gap1 (α : ℝ) :
    F α =
      (∫ x in (0 : ℝ)..Real.pi / 2, integrand α x) +
        ∫ x in Real.pi / 2..Real.pi, integrand α x := by
  by_cases hleft :
      IntervalIntegrable (integrand α) volume 0 (Real.pi / 2)
  · have hright :
        IntervalIntegrable (integrand α) volume
          (Real.pi / 2) Real.pi :=
      (half_integrable_iff α).2 hleft
    unfold F
    exact
      (intervalIntegral.integral_add_adjacent_intervals hleft hright).symm
  · have hright :
        ¬IntervalIntegrable (integrand α) volume
          (Real.pi / 2) Real.pi := by
      intro h
      exact hleft ((half_integrable_iff α).1 h)
    have hfull :
        ¬IntervalIntegrable (integrand α) volume 0 Real.pi := by
      intro h
      exact hleft (h.mono_set (by
        rw [uIcc_of_le Real.pi_nonneg,
          uIcc_of_le Real.pi_div_two_pos.le]
        intro x hx
        exact ⟨hx.1, hx.2.trans (by linarith [Real.pi_pos])⟩))
    rw [F, intervalIntegral.integral_undef hfull,
      intervalIntegral.integral_undef hleft,
      intervalIntegral.integral_undef hright]
    ring

theorem gap2 (α : ℝ) :
    F α =
      (∫ x in (0 : ℝ)..Real.pi / 2, integrand α x) -
        ∫ t in Real.pi / 2..0,
          Real.sin (Real.pi - t) /
            (Real.rpow (Real.pi - t) α * Real.rpow t α) := by
  rw [gap1]
  have hfun :
      (fun t : ℝ =>
        Real.sin (Real.pi - t) /
          (Real.rpow (Real.pi - t) α * Real.rpow t α)) =
        integrand α := by
    funext t
    simpa [integrand] using integrand_pi_sub α t
  rw [hfun, half_integrals_eq]
  have hsym :
      (∫ x in Real.pi / 2..(0 : ℝ), integrand α x) =
        -(∫ x in (0 : ℝ)..Real.pi / 2, integrand α x) :=
    intervalIntegral.integral_symm
      (f := integrand α) (a := 0) (b := Real.pi / 2)
  rw [hsym]
  ring

theorem gap3 (α : ℝ) :
    F α = 2 * ∫ x in (0 : ℝ)..Real.pi / 2, integrand α x := by
  rw [gap1, half_integrals_eq]
  ring

private lemma measurable_rpow_const (a : ℝ) :
    Measurable (fun x : ℝ => Real.rpow x a) := by
  apply measurable_of_continuousOn_compl_singleton 0
  exact continuousOn_id.rpow_const
    (fun x hx => Or.inl (by simpa using hx))

private lemma measurable_abs_integrand (a : ℝ) :
    Measurable
      (fun x : ℝ =>
        |Real.sin x| /
          (Real.rpow x a * Real.rpow (Real.pi - x) a)) := by
  exact
    Real.continuous_sin.abs.measurable.div
      ((measurable_rpow_const a).mul
        ((measurable_rpow_const a).comp
          (measurable_const.sub measurable_id)))

private lemma quotient_rpow_eq {x a : ℝ} (hx : 0 < x) :
    x / Real.rpow x a = Real.rpow x (1 - a) := by
  calc
    x / Real.rpow x a =
        Real.rpow x 1 / Real.rpow x a := by
          congr 1
          exact (Real.rpow_one x).symm
    _ = Real.rpow x (1 - a) :=
      (Real.rpow_sub hx 1 a).symm

private lemma reciprocal_pi_half_rpow (a : ℝ) :
    1 / Real.rpow (Real.pi / 2) a =
      Real.rpow (2 / Real.pi) a := by
  calc
    1 / Real.rpow (Real.pi / 2) a =
        (Real.rpow (Real.pi / 2) a)⁻¹ := one_div _
    _ = Real.rpow ((Real.pi / 2)⁻¹) a :=
      (Real.inv_rpow Real.pi_div_two_pos.le a).symm
    _ = Real.rpow (2 / Real.pi) a := by
      congr 1
      field_simp [Real.pi_ne_zero]

private lemma reciprocal_rpow_eq {x a : ℝ} (hx : 0 < x) :
    1 / Real.rpow x (a - 1) = Real.rpow x (1 - a) := by
  calc
    1 / Real.rpow x (a - 1) =
        (Real.rpow x (a - 1))⁻¹ := one_div _
    _ = Real.rpow x (-(a - 1)) :=
      (Real.rpow_neg hx.le (a - 1)).symm
    _ = Real.rpow x (1 - a) := by ring_nf

private lemma reciprocal_rpow_intervalIntegrable
    {a η : ℝ} (hη : 0 ≤ η) (ha2 : a < 2) :
    IntervalIntegrable
      (fun x : ℝ => 1 / Real.rpow x (a - 1))
      volume 0 η := by
  have hp :
      IntervalIntegrable (fun x : ℝ => Real.rpow x (1 - a))
        volume 0 η :=
    intervalIntegral.intervalIntegrable_rpow' (by linarith)
  apply hp.congr
  intro x hx
  by_cases hx0 : x = 0
  · subst x
    by_cases ha1 : a = 1
    · simp [ha1]
    · have h₁ : a - 1 ≠ 0 := sub_ne_zero.mpr ha1
      have h₂ : 1 - a ≠ 0 := sub_ne_zero.mpr (Ne.symm ha1)
      simp [Real.zero_rpow h₁, Real.zero_rpow h₂]
  · have hxnonneg : 0 ≤ x := by
      rw [uIoc_of_le hη] at hx
      exact hx.1.le
    exact (reciprocal_rpow_eq (hxnonneg.lt_of_ne' hx0)).symm

private lemma left_pointwise_bound
    {a η x : ℝ} (hη : 0 < η) (hη1 : η < 1)
    (ha0 : 0 < a) (hx : x ∈ Icc (0 : ℝ) η) :
    |Real.sin x| /
        (Real.rpow x a * Real.rpow (Real.pi - x) a) ≤
      Real.rpow (2 / Real.pi) a *
        (1 / Real.rpow x (a - 1)) := by
  by_cases hxzero : x = 0
  · subst x
    simp only [Real.sin_zero, abs_zero, zero_div]
    exact mul_nonneg
      (Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ 2 / Real.pi) a)
      (one_div_nonneg.mpr (Real.rpow_nonneg (le_refl 0) (a - 1)))
  have hx0 : 0 < x := hx.1.lt_of_ne' hxzero
  have hx1 : x < 1 := hx.2.trans_lt hη1
  have hpi2 : Real.pi / 2 ≤ Real.pi - x := by
    linarith [Real.two_le_pi]
  have hpiSub0 : 0 < Real.pi - x :=
    Real.pi_div_two_pos.trans_le hpi2
  have hxpow : 0 < Real.rpow x a :=
    Real.rpow_pos_of_pos hx0 a
  have hpipow : 0 < Real.rpow (Real.pi - x) a :=
    Real.rpow_pos_of_pos hpiSub0 a
  have hhalfPow : 0 < Real.rpow (Real.pi / 2) a :=
    Real.rpow_pos_of_pos Real.pi_div_two_pos a
  have hpow :
      Real.rpow (Real.pi / 2) a ≤
        Real.rpow (Real.pi - x) a :=
    Real.rpow_le_rpow Real.pi_div_two_pos.le hpi2 ha0.le
  have hsin : |Real.sin x| ≤ x := by
    simpa [abs_of_pos hx0] using
      (Real.abs_sin_le_abs : |Real.sin x| ≤ |x|)
  calc
    |Real.sin x| /
        (Real.rpow x a * Real.rpow (Real.pi - x) a) ≤
        x /
          (Real.rpow x a * Real.rpow (Real.pi - x) a) :=
      div_le_div_of_nonneg_right hsin
        (mul_nonneg hxpow.le hpipow.le)
    _ = (x / Real.rpow x a) /
          Real.rpow (Real.pi - x) a := by
      field_simp [hxpow.ne', hpipow.ne']
    _ ≤ (x / Real.rpow x a) /
          Real.rpow (Real.pi / 2) a := by
      exact div_le_div_of_nonneg_left
        (div_nonneg hx0.le hxpow.le) hhalfPow hpow
    _ = Real.rpow (2 / Real.pi) a *
          (1 / Real.rpow x (a - 1)) := by
      rw [quotient_rpow_eq hx0, reciprocal_rpow_eq hx0,
        div_eq_mul_inv, ← reciprocal_pi_half_rpow]
      ring

theorem gap4 (η α₀ α α₁ : ℝ) (hη : 0 < η) (hη1 : η < 1)
    (hα₀ : 0 < α₀) (hα₀α : α₀ ≤ α) (hαα₁ : α ≤ α₁)
    (hα₁ : α₁ < 2) :
    (∫ x in (0 : ℝ)..η, |Real.sin x| /
      (Real.rpow x α * Real.rpow (Real.pi - x) α)) ≤
        Real.rpow (2 / Real.pi) α *
          ∫ x in (0 : ℝ)..η, 1 / Real.rpow x (α - 1) := by
  have hα0 : 0 < α := hα₀.trans_le hα₀α
  have hα2 : α < 2 := hαα₁.trans_lt hα₁
  have hmajor :
      IntervalIntegrable
        (fun x : ℝ =>
          Real.rpow (2 / Real.pi) α *
            (1 / Real.rpow x (α - 1)))
        volume 0 η :=
    (reciprocal_rpow_intervalIntegrable hη.le hα2).const_mul _
  have hleft :
      IntervalIntegrable
        (fun x : ℝ =>
          |Real.sin x| /
            (Real.rpow x α * Real.rpow (Real.pi - x) α))
        volume 0 η := by
    apply hmajor.mono_fun
      (measurable_abs_integrand α).aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_uIoc] with x hx
    rw [uIoc_of_le hη.le] at hx
    have hxIcc : x ∈ Icc (0 : ℝ) η := ⟨hx.1.le, hx.2⟩
    have hpi0 : 0 ≤ Real.pi - x := by
      linarith [Real.pi_gt_three, hx.2, hη1]
    have hleft0 :
        0 ≤ |Real.sin x| /
          (Real.rpow x α * Real.rpow (Real.pi - x) α) :=
      div_nonneg (abs_nonneg _)
        (mul_nonneg (Real.rpow_nonneg hx.1.le α)
          (Real.rpow_nonneg hpi0 α))
    have hmajor0 :
        0 ≤ Real.rpow (2 / Real.pi) α *
          (1 / Real.rpow x (α - 1)) :=
      mul_nonneg
        (Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ 2 / Real.pi) α)
        (one_div_nonneg.mpr (Real.rpow_nonneg hx.1.le (α - 1)))
    change
      |(|Real.sin x| /
          (Real.rpow x α * Real.rpow (Real.pi - x) α))| ≤
        |(Real.rpow (2 / Real.pi) α *
          (1 / Real.rpow x (α - 1)))|
    rw [abs_of_nonneg hleft0, abs_of_nonneg hmajor0]
    exact left_pointwise_bound hη hη1 hα0 hxIcc
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_mono_on hη.le hleft hmajor
  intro x hx
  exact left_pointwise_bound hη hη1 hα0 hx

private lemma integral_reciprocal_rpow
    {a η : ℝ} (hη : 0 < η) (ha2 : a < 2) :
    (∫ x in (0 : ℝ)..η, 1 / Real.rpow x (a - 1)) =
      (1 / (2 - a)) * Real.rpow η (2 - a) := by
  have hcongr :
      (∫ x in (0 : ℝ)..η, 1 / Real.rpow x (a - 1)) =
        ∫ x in (0 : ℝ)..η, Real.rpow x (1 - a) := by
    apply intervalIntegral.integral_congr
    intro x hx
    have hxnonneg : 0 ≤ x := by
      rw [uIcc_of_le hη.le] at hx
      exact hx.1
    by_cases hx0 : x = 0
    · subst x
      by_cases ha1 : a = 1
      · simp [ha1]
      · have h₁ : a - 1 ≠ 0 := sub_ne_zero.mpr ha1
        have h₂ : 1 - a ≠ 0 := sub_ne_zero.mpr (Ne.symm ha1)
        simp [Real.zero_rpow h₁, Real.zero_rpow h₂]
    · exact reciprocal_rpow_eq (hxnonneg.lt_of_ne' hx0)
  rw [hcongr]
  change
    (∫ x in (0 : ℝ)..η, x ^ (1 - a)) =
      (1 / (2 - a)) * η ^ (2 - a)
  rw [integral_rpow (Or.inl (by linarith : -1 < 1 - a))]
  have hexp : 1 - a + 1 = 2 - a := by ring
  rw [hexp, Real.zero_rpow (by linarith : 2 - a ≠ 0)]
  ring

theorem gap5 (η α₀ α α₁ : ℝ) (hη : 0 < η) (hη1 : η < 1)
    (hα₀ : 0 < α₀) (hα₀α : α₀ ≤ α) (hαα₁ : α ≤ α₁)
    (hα₁ : α₁ < 2) :
    (∫ x in (0 : ℝ)..η, |Real.sin x| /
      (Real.rpow x α * Real.rpow (Real.pi - x) α)) ≤
        Real.rpow (2 / Real.pi) α₀ *
          (1 / (2 - α₁)) * Real.rpow η (2 - α₁) := by
  have hα0 : 0 < α := hα₀.trans_le hα₀α
  have hα2 : α < 2 := hαα₁.trans_lt hα₁
  have hbase0 : 0 < 2 / Real.pi := by positivity
  have hbase1 : 2 / Real.pi ≤ 1 := by
    apply (div_le_one Real.pi_pos).2
    exact Real.two_le_pi
  have hcoef :
      Real.rpow (2 / Real.pi) α ≤
        Real.rpow (2 / Real.pi) α₀ :=
    Real.rpow_le_rpow_of_exponent_ge hbase0 hbase1 hα₀α
  have hpow :
      Real.rpow η (2 - α) ≤ Real.rpow η (2 - α₁) :=
    Real.rpow_le_rpow_of_exponent_ge hη hη1.le (by linarith)
  have hinv :
      1 / (2 - α) ≤ 1 / (2 - α₁) :=
    one_div_le_one_div_of_le (by linarith) (by linarith)
  have hInt0 :
      0 ≤ ∫ x in (0 : ℝ)..η, 1 / Real.rpow x (α - 1) := by
    apply intervalIntegral.integral_nonneg hη.le
    intro x hx
    exact one_div_nonneg.mpr
      (Real.rpow_nonneg hx.1 (α - 1))
  have hIntBound :
      (∫ x in (0 : ℝ)..η, 1 / Real.rpow x (α - 1)) ≤
        (1 / (2 - α₁)) * Real.rpow η (2 - α₁) := by
    rw [integral_reciprocal_rpow hη hα2]
    exact mul_le_mul hinv hpow
      (Real.rpow_nonneg hη.le (2 - α))
      (one_div_nonneg.mpr (by linarith))
  calc
    (∫ x in (0 : ℝ)..η, |Real.sin x| /
        (Real.rpow x α * Real.rpow (Real.pi - x) α)) ≤
        Real.rpow (2 / Real.pi) α *
          ∫ x in (0 : ℝ)..η, 1 / Real.rpow x (α - 1) :=
      gap4 η α₀ α α₁ hη hη1 hα₀ hα₀α hαα₁ hα₁
    _ ≤ Real.rpow (2 / Real.pi) α₀ *
          ∫ x in (0 : ℝ)..η, 1 / Real.rpow x (α - 1) :=
      mul_le_mul_of_nonneg_right hcoef hInt0
    _ ≤ Real.rpow (2 / Real.pi) α₀ *
          ((1 / (2 - α₁)) * Real.rpow η (2 - α₁)) :=
      mul_le_mul_of_nonneg_left hIntBound
        (Real.rpow_nonneg hbase0.le α₀)
    _ = Real.rpow (2 / Real.pi) α₀ *
          (1 / (2 - α₁)) * Real.rpow η (2 - α₁) := by ring

private lemma abs_integrand_intervalIntegrable
    {a η : ℝ} (hη : 0 < η) (hη1 : η < 1)
    (ha0 : 0 < a) (ha2 : a < 2) :
    IntervalIntegrable
      (fun x : ℝ =>
        |Real.sin x| /
          (Real.rpow x a * Real.rpow (Real.pi - x) a))
      volume 0 η := by
  have hmajor :
      IntervalIntegrable
        (fun x : ℝ =>
          Real.rpow (2 / Real.pi) a *
            (1 / Real.rpow x (a - 1)))
        volume 0 η :=
    (reciprocal_rpow_intervalIntegrable hη.le ha2).const_mul _
  apply hmajor.mono_fun
    (measurable_abs_integrand a).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_uIoc] with x hx
  rw [uIoc_of_le hη.le] at hx
  have hxIcc : x ∈ Icc (0 : ℝ) η := ⟨hx.1.le, hx.2⟩
  have hpi0 : 0 ≤ Real.pi - x := by
    linarith [Real.pi_gt_three, hx.2, hη1]
  have hleft0 :
      0 ≤ |Real.sin x| /
        (Real.rpow x a * Real.rpow (Real.pi - x) a) :=
    div_nonneg (abs_nonneg _)
      (mul_nonneg (Real.rpow_nonneg hx.1.le a)
        (Real.rpow_nonneg hpi0 a))
  have hmajor0 :
      0 ≤ Real.rpow (2 / Real.pi) a *
        (1 / Real.rpow x (a - 1)) :=
    mul_nonneg
      (Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ 2 / Real.pi) a)
      (one_div_nonneg.mpr (Real.rpow_nonneg hx.1.le (a - 1)))
  change
    |(|Real.sin x| /
        (Real.rpow x a * Real.rpow (Real.pi - x) a))| ≤
      |(Real.rpow (2 / Real.pi) a *
        (1 / Real.rpow x (a - 1)))|
  rw [abs_of_nonneg hleft0, abs_of_nonneg hmajor0]
  exact left_pointwise_bound hη hη1 ha0 hxIcc

theorem gap6 (η α₀ α α₁ ε : ℝ) (hη : 0 < η) (hη1 : η < 1)
    (hα₀ : 0 < α₀) (hα₀α : α₀ ≤ α) (hαα₁ : α ≤ α₁)
    (hα₁ : α₁ < 2) (hε : 0 < ε)
    (hsmall : Real.rpow (2 / Real.pi) α₀ *
      (1 / (2 - α₁)) * Real.rpow η (2 - α₁) < ε) :
    |∫ x in (0 : ℝ)..η, integrand α x| < ε := by
  have hα0 : 0 < α := hα₀.trans_le hα₀α
  have hα2 : α < 2 := hαα₁.trans_lt hα₁
  have habsInt :=
    abs_integrand_intervalIntegrable hη hη1 hα0 hα2
  have hnorm :
      |∫ x in (0 : ℝ)..η, integrand α x| ≤
        ∫ x in (0 : ℝ)..η,
          |Real.sin x| /
            (Real.rpow x α * Real.rpow (Real.pi - x) α) := by
    rw [← Real.norm_eq_abs]
    apply intervalIntegral.norm_integral_le_of_norm_le hη.le
    · filter_upwards with x hx
      have hx0 : 0 ≤ x := hx.1.le
      have hpi0 : 0 ≤ Real.pi - x := by
        linarith [Real.pi_gt_three, hx.2, hη1]
      have hden0 :
          0 ≤ Real.rpow x α * Real.rpow (Real.pi - x) α :=
        mul_nonneg (Real.rpow_nonneg hx0 α)
          (Real.rpow_nonneg hpi0 α)
      simp only [integrand, Real.norm_eq_abs, abs_div,
        abs_of_nonneg hden0, le_refl]
    · exact habsInt
  exact hnorm.trans_lt
    ((gap5 η α₀ α α₁ hη hη1 hα₀ hα₀α hαα₁ hα₁).trans_lt
      hsmall)

theorem gap7 (α₀ α₁ : ℝ) (hα₀ : 0 < α₀)
    (hα₀α₁ : α₀ ≤ α₁) (hα₁ : α₁ < 2) :
    UniformAtZero α₀ α₁ := by
  intro ε hε
  let q : ℝ := 2 - α₁
  let C : ℝ :=
    Real.rpow (2 / Real.pi) α₀ * (1 / (2 - α₁))
  have hq : 0 < q := by
    dsimp [q]
    linarith
  have hC0 : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg
      (Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ 2 / Real.pi) α₀)
      (one_div_nonneg.mpr (by linarith))
  have hpow :
      Tendsto (fun η : ℝ => Real.rpow η q) (𝓝 0) (𝓝 0) := by
    have hc :
        ContinuousAt (fun η : ℝ => Real.rpow η q) 0 :=
      (Real.continuous_rpow_const hq.le).continuousAt
    have hz : Real.rpow (0 : ℝ) q = 0 :=
      Real.zero_rpow hq.ne'
    change
      Tendsto (fun η : ℝ => Real.rpow η q) (𝓝 0)
        (𝓝 (Real.rpow 0 q)) at hc
    rw [hz] at hc
    exact hc
  have hlim :
      Tendsto (fun η : ℝ => C * Real.rpow η q)
        (𝓝 0) (𝓝 0) := by
    simpa using tendsto_const_nhds.mul hpow
  obtain ⟨δ₀, hδ₀, hnear⟩ :=
    (Metric.tendsto_nhds_nhds.1 hlim) ε hε
  let δ : ℝ := min δ₀ 1
  have hδ : 0 < δ := by
    dsimp [δ]
    exact lt_min hδ₀ zero_lt_one
  refine ⟨δ, hδ, ?_⟩
  intro α hα η hη hηδ
  have hηδ₀ : η < δ₀ :=
    hηδ.trans_le (by
      dsimp [δ]
      exact min_le_left _ _)
  have hη1 : η < 1 :=
    hηδ.trans_le (by
      dsimp [δ]
      exact min_le_right _ _)
  have hdist : dist η 0 < δ₀ := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hη]
    exact hηδ₀
  have hs := hnear hdist
  have hsmall :
      Real.rpow (2 / Real.pi) α₀ *
          (1 / (2 - α₁)) * Real.rpow η (2 - α₁) < ε := by
    have hterm0 : 0 ≤ C * Real.rpow η q :=
      mul_nonneg hC0 (Real.rpow_nonneg hη.le q)
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hterm0] at hs
    simpa [C, q, mul_assoc] using hs
  exact gap6 η α₀ α α₁ ε hη hη1 hα₀ hα.1 hα.2 hα₁ hε
    hsmall

private lemma continuous_integrand_at {α x : ℝ}
    (hx0 : 0 < x) (hxp : x < Real.pi) :
    ContinuousAt
      (fun a : ℝ =>
        Real.sin x /
          (Real.rpow x a * Real.rpow (Real.pi - x) a)) α := by
  have hy0 : 0 < Real.pi - x := sub_pos.mpr hxp
  have hxpow : ContinuousAt (fun a : ℝ => Real.rpow x a) α :=
    continuousAt_const.rpow continuousAt_id (Or.inl hx0.ne')
  have hypow :
      ContinuousAt (fun a : ℝ => Real.rpow (Real.pi - x) a) α :=
    continuousAt_const.rpow continuousAt_id (Or.inl hy0.ne')
  apply continuousAt_const.div (hxpow.mul hypow)
  exact mul_ne_zero
    (Real.rpow_pos_of_pos hx0 α).ne'
    (Real.rpow_pos_of_pos hy0 α).ne'

private lemma continuous_integrand_on (a : ℝ) :
    ContinuousOn
      (fun x : ℝ =>
        Real.sin x /
          (Real.rpow x a * Real.rpow (Real.pi - x) a))
      (Ioo 0 Real.pi) := by
  intro x hx
  have hy0 : 0 < Real.pi - x := sub_pos.mpr hx.2
  have hxpow : ContinuousAt (fun y : ℝ => Real.rpow y a) x :=
    continuousAt_id.rpow continuousAt_const (Or.inl hx.1.ne')
  have hypow :
      ContinuousAt (fun y : ℝ => Real.rpow (Real.pi - y) a) x :=
    (continuousAt_const.sub continuousAt_id).rpow continuousAt_const
      (Or.inl hy0.ne')
  apply
    (Real.continuous_sin.continuousAt.div (hxpow.mul hypow)
      (mul_ne_zero
        (Real.rpow_pos_of_pos hx.1 a).ne'
        (Real.rpow_pos_of_pos hy0 a).ne')).continuousWithinAt

private lemma left_bound {a r x : ℝ}
    (hx0 : 0 < x) (hxp : x < Real.pi) (hx1 : x ≤ 1)
    (ha0 : 0 < a) (har : a < r) :
    ‖Real.sin x /
        (Real.rpow x a * Real.rpow (Real.pi - x) a)‖
      ≤ Real.rpow x (1 - r) := by
  have hy1 : 1 ≤ Real.pi - x := by
    linarith [Real.pi_gt_three]
  have hy0 : 0 < Real.pi - x := zero_lt_one.trans_le hy1
  have hs0 : 0 ≤ Real.sin x :=
    Real.sin_nonneg_of_nonneg_of_le_pi hx0.le hxp.le
  have hsx : Real.sin x ≤ x := Real.sin_le hx0.le
  have hxa : 0 < Real.rpow x a := Real.rpow_pos_of_pos hx0 a
  have hya : 0 < Real.rpow (Real.pi - x) a :=
    Real.rpow_pos_of_pos hy0 a
  have hden :
      0 < Real.rpow x a * Real.rpow (Real.pi - x) a :=
    mul_pos hxa hya
  rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg hs0 hden.le)]
  calc
    Real.sin x / (Real.rpow x a * Real.rpow (Real.pi - x) a)
        ≤ x / (Real.rpow x a * Real.rpow (Real.pi - x) a) :=
      div_le_div_of_nonneg_right hsx hden.le
    _ = (x / Real.rpow x a) / Real.rpow (Real.pi - x) a := by
      field_simp [hxa.ne', hya.ne']
    _ ≤ x / Real.rpow x a := by
      exact div_le_self
        (div_nonneg hx0.le hxa.le)
        (Real.one_le_rpow hy1 ha0.le)
    _ = Real.rpow x (1 - a) := quotient_rpow_eq hx0
    _ ≤ Real.rpow x (1 - r) :=
      Real.rpow_le_rpow_of_exponent_ge hx0 hx1 (by linarith)

private lemma middle_bound {a x : ℝ}
    (hx1 : 1 ≤ x) (hy1 : 1 ≤ Real.pi - x) (ha0 : 0 < a) :
    ‖Real.sin x /
        (Real.rpow x a * Real.rpow (Real.pi - x) a)‖ ≤ 1 := by
  have hxp0 : 0 ≤ Real.rpow x a :=
    Real.rpow_nonneg (zero_le_one.trans hx1) a
  have hyp0 :
      0 ≤ Real.rpow (Real.pi - x) a :=
    Real.rpow_nonneg (zero_le_one.trans hy1) a
  have hden1 :
      1 ≤ Real.rpow x a * Real.rpow (Real.pi - x) a :=
    one_le_mul_of_one_le_of_one_le
      (Real.one_le_rpow hx1 ha0.le)
      (Real.one_le_rpow hy1 ha0.le)
  rw [norm_div, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg hxp0 hyp0)]
  exact (div_le_self (abs_nonneg _) hden1).trans
    (Real.abs_sin_le_one x)

private lemma pointwise_bound {a r x : ℝ}
    (hx0 : 0 < x) (hxp : x < Real.pi)
    (ha0 : 0 < a) (har : a < r) :
    ‖Real.sin x /
        (Real.rpow x a * Real.rpow (Real.pi - x) a)‖
      ≤
        (if x ≤ 1 then Real.rpow x (1 - r)
          else if Real.pi - x ≤ 1 then
            Real.rpow (Real.pi - x) (1 - r)
          else 1) := by
  by_cases hx1 : x ≤ 1
  · rw [if_pos hx1]
    exact left_bound hx0 hxp hx1 ha0 har
  by_cases hy1 : Real.pi - x ≤ 1
  · rw [if_neg hx1, if_pos hy1]
    have hy0 : 0 < Real.pi - x := sub_pos.mpr hxp
    have hyp : Real.pi - x < Real.pi := by linarith
    have H := left_bound hy0 hyp hy1 ha0 har
    simpa [Real.sin_pi_sub, mul_comm] using H
  · rw [if_neg hx1, if_neg hy1]
    exact middle_bound (le_of_not_ge hx1) (le_of_not_ge hy1) ha0

private lemma integrable_bound {r : ℝ} (hr : r < 2) :
    IntervalIntegrable
      (fun x : ℝ =>
        if x ≤ 1 then Real.rpow x (1 - r)
        else if Real.pi - x ≤ 1 then
          Real.rpow (Real.pi - x) (1 - r)
        else 1)
      volume 0 Real.pi := by
  let b : ℝ → ℝ :=
    fun x =>
      if x ≤ 1 then Real.rpow x (1 - r)
      else if Real.pi - x ≤ 1 then
        Real.rpow (Real.pi - x) (1 - r)
      else 1
  have hp :
      IntervalIntegrable (fun x : ℝ => Real.rpow x (1 - r))
        volume 0 1 :=
    intervalIntegral.intervalIntegrable_rpow' (by linarith)
  have hleft : IntervalIntegrable b volume 0 1 := by
    apply hp.congr
    intro x hx
    rw [uIoc_of_le zero_le_one] at hx
    simp [b, hx.2]
  have hsplit : 1 ≤ Real.pi - 1 := by
    linarith [Real.two_le_pi]
  have hmiddle : IntervalIntegrable b volume 1 (Real.pi - 1) := by
    have hc :
        IntervalIntegrable (fun _ : ℝ => (1 : ℝ))
          volume 1 (Real.pi - 1) :=
      intervalIntegrable_const
    apply hc.congr
    intro x hx
    rw [uIoc_of_le hsplit] at hx
    have hx1 : ¬x ≤ 1 := not_le_of_gt hx.1
    change (1 : ℝ) = b x
    dsimp [b]
    rw [if_neg hx1]
    by_cases hy1 : Real.pi - x ≤ 1
    · have hy_ge : 1 ≤ Real.pi - x := by linarith [hx.2]
      have hy_eq : Real.pi - x = 1 := le_antisymm hy1 hy_ge
      rw [if_pos hy1, hy_eq]
      exact (Real.one_rpow (1 - r)).symm
    · rw [if_neg hy1]
  have hrightPower :
      IntervalIntegrable
        (fun x : ℝ => Real.rpow (Real.pi - x) (1 - r))
        volume (Real.pi - 1) Real.pi := by
    simpa using (hp.comp_sub_left Real.pi).symm
  have hright : IntervalIntegrable b volume (Real.pi - 1) Real.pi := by
    apply hrightPower.congr
    intro x hx
    rw [uIoc_of_le (by linarith)] at hx
    have hx1 : ¬x ≤ 1 := by
      exact not_le_of_gt (by linarith [Real.pi_gt_three, hx.1])
    have hy1 : Real.pi - x ≤ 1 := by linarith [hx.1]
    change Real.rpow (Real.pi - x) (1 - r) = b x
    dsimp [b]
    rw [if_neg hx1, if_pos hy1]
  exact hleft.trans hmiddle |>.trans hright

private theorem F_continuous_Ioo :
    ContinuousOn F (Set.Ioo (0 : ℝ) 2) := by
  intro α hα
  change 0 < α ∧ α < 2 at hα
  let q : ℝ := α / 2
  let r : ℝ := (α + 2) / 2
  have hq0 : 0 < q := by
    dsimp [q]
    linarith
  have hqα : q < α := by
    dsimp [q]
    linarith
  have hαr : α < r := by
    dsimp [r]
    linarith
  have hr2 : r < 2 := by
    dsimp [r]
    linarith
  let b : ℝ → ℝ :=
    fun x =>
      if x ≤ 1 then Real.rpow x (1 - r)
      else if Real.pi - x ≤ 1 then
        Real.rpow (Real.pi - x) (1 - r)
      else 1
  have hb : IntervalIntegrable b volume 0 Real.pi :=
    integrable_bound hr2
  have hmeas :
      ∀ᶠ a in 𝓝 α,
        AEStronglyMeasurable
          (fun x : ℝ =>
            Real.sin x /
              (Real.rpow x a * Real.rpow (Real.pi - x) a))
          (volume.restrict (Ι (0 : ℝ) Real.pi)) := by
    filter_upwards with a
    rw [uIoc_of_le Real.pi_nonneg,
      ← Measure.restrict_congr_set Ioo_ae_eq_Ioc]
    exact
      (continuous_integrand_on a).aestronglyMeasurable
        measurableSet_Ioo
  have hbound :
      ∀ᶠ a in 𝓝 α, ∀ᵐ x ∂volume,
        x ∈ Ι (0 : ℝ) Real.pi →
          ‖Real.sin x /
              (Real.rpow x a * Real.rpow (Real.pi - x) a)‖
            ≤ b x := by
    filter_upwards [Ioo_mem_nhds hqα hαr] with a ha
    filter_upwards [volume.ae_ne (0 : ℝ),
      volume.ae_ne Real.pi] with x hx0ne hxpine
    intro hx
    rw [uIoc_of_le Real.pi_nonneg] at hx
    have hx0 : 0 < x := hx.1
    have hxp : x < Real.pi := lt_of_le_of_ne hx.2 hxpine
    exact pointwise_bound hx0 hxp (hq0.trans ha.1) ha.2
  have hcont :
      ∀ᵐ x ∂volume,
        x ∈ Ι (0 : ℝ) Real.pi →
          ContinuousAt
            (fun a : ℝ =>
              Real.sin x /
                (Real.rpow x a * Real.rpow (Real.pi - x) a)) α := by
    filter_upwards [volume.ae_ne (0 : ℝ),
      volume.ae_ne Real.pi] with x hx0ne hxpine
    intro hx
    rw [uIoc_of_le Real.pi_nonneg] at hx
    exact continuous_integrand_at hx.1
      (lt_of_le_of_ne hx.2 hxpine)
  have H :=
    intervalIntegral.continuousAt_of_dominated_interval
      hmeas hbound hb hcont
  simpa [F, integrand] using H.continuousWithinAt

theorem gap8 (α₀ α₁ : ℝ) (hα₀ : 0 < α₀)
    (hα₀α₁ : α₀ ≤ α₁) (hα₁ : α₁ < 2) :
    ContinuousOn F (Set.Icc α₀ α₁) := by
  apply F_continuous_Ioo.mono
  intro α hα
  exact ⟨hα₀.trans_le hα.1, hα.2.trans_lt hα₁⟩

theorem gap9 :
    ContinuousOn F (Set.Ioo 0 2) := by
  exact F_continuous_Ioo

theorem gap10 :
    ContinuousOn F (Set.Ioo 0 2) := by
  exact gap9

end

end ProofGap.Exercise3781
