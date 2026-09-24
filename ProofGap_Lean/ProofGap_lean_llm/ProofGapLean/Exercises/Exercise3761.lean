import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Neighborhoods
import Mathlib.Topology.Algebra.Order.Field

namespace ProofGap.Exercise3761

noncomputable section

open Filter MeasureTheory
open scoped Interval

def weight (α p x : ℝ) : ℝ :=
  Real.exp (-(α * x)) / Real.rpow x p

def integrand (α p x : ℝ) : ℝ :=
  Real.exp (-(α * x)) * (Real.cos x / Real.rpow x p)

private theorem tail_integral_bound
    (α p A A₁ : ℝ) (hα : 0 ≤ α) (hp : 0 < p)
    (hA : 1 < A) (hAA₁ : A < A₁) :
    |∫ x in A..A₁, integrand α p x| ≤ 2 * weight α p A := by
  let D : ℝ → ℝ := fun x =>
    (((-α * Real.exp (-(α * x))) * Real.rpow x p) -
      Real.exp (-(α * x)) * (p * Real.rpow x (p - 1))) /
      (Real.rpow x p) ^ 2
  have hpos_of_mem : ∀ x ∈ Set.uIcc A A₁, 0 < x := by
    intro x hx
    have hx' : x ∈ Set.Icc A A₁ := by
      simpa [Set.uIcc, le_of_lt hAA₁] using hx
    exact lt_of_lt_of_le (lt_trans zero_lt_one hA) hx'.1
  have hweight_deriv : ∀ x, 0 < x → HasDerivAt (weight α p) (D x) x := by
    intro x hx
    have he : HasDerivAt (fun y : ℝ => Real.exp (-(α * y)))
        (-α * Real.exp (-(α * x))) x := by
      convert (Real.hasDerivAt_exp (-(α * x))).comp x
        (((hasDerivAt_const x α).mul (hasDerivAt_id x)).neg) using 1 <;> ring
    have hr : HasDerivAt (fun y : ℝ => Real.rpow y p)
        (p * Real.rpow x (p - 1)) x :=
      Real.hasDerivAt_rpow_const (p := p) (Or.inl hx.ne')
    simpa [weight, D] using
      he.div hr (ne_of_gt (Real.rpow_pos_of_pos hx p))
  have hD_nonpos : ∀ x, 0 < x → D x ≤ 0 := by
    intro x hx
    have hexp : 0 < Real.exp (-(α * x)) := Real.exp_pos _
    have hrp : 0 < Real.rpow x p := Real.rpow_pos_of_pos hx p
    have hrpm : 0 < Real.rpow x (p - 1) := Real.rpow_pos_of_pos hx (p - 1)
    have hfirst : (-α * Real.exp (-(α * x))) * Real.rpow x p ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hα) (le_of_lt hexp))
        (le_of_lt hrp)
    have hsecond : 0 ≤ Real.exp (-(α * x)) *
        (p * Real.rpow x (p - 1)) :=
      mul_nonneg (le_of_lt hexp) (mul_nonneg (le_of_lt hp) (le_of_lt hrpm))
    apply div_nonpos_of_nonpos_of_nonneg
    · exact sub_nonpos.mpr (hfirst.trans hsecond)
    · exact sq_nonneg _
  have hcontW : ContinuousOn (weight α p) (Set.uIcc A A₁) := by
    intro x hx
    exact (hweight_deriv x (hpos_of_mem x hx)).continuousAt.continuousWithinAt
  have hcontD : ContinuousOn D (Set.uIcc A A₁) := by
    intro x hx
    have hx0 := hpos_of_mem x hx
    have he : HasDerivAt (fun y : ℝ => Real.exp (-(α * y)))
        (-α * Real.exp (-(α * x))) x := by
      convert (Real.hasDerivAt_exp (-(α * x))).comp x
        (((hasDerivAt_const x α).mul (hasDerivAt_id x)).neg) using 1 <;> ring
    have hr : HasDerivAt (fun y : ℝ => Real.rpow y p)
        (p * Real.rpow x (p - 1)) x :=
      Real.hasDerivAt_rpow_const (p := p) (Or.inl hx0.ne')
    have hrm : HasDerivAt (fun y : ℝ => Real.rpow y (p - 1))
        ((p - 1) * Real.rpow x (p - 1 - 1)) x :=
      Real.hasDerivAt_rpow_const (p := p - 1) (Or.inl hx0.ne')
    have hcnum : ContinuousAt (fun y : ℝ =>
        ((-α * Real.exp (-(α * y))) * Real.rpow y p) -
          Real.exp (-(α * y)) * (p * Real.rpow y (p - 1))) x :=
      ((continuousAt_const.mul he.continuousAt).mul hr.continuousAt).sub
        (he.continuousAt.mul (continuousAt_const.mul hrm.continuousAt))
    have hcden : ContinuousAt (fun y : ℝ => (Real.rpow y p) ^ 2) x :=
      hr.continuousAt.pow 2
    have hden : (Real.rpow x p) ^ 2 ≠ 0 :=
      pow_ne_zero 2 (ne_of_gt (Real.rpow_pos_of_pos hx0 p))
    exact (by
      simpa [D] using (hcnum.div hcden hden).continuousWithinAt)
  have hDint : IntervalIntegrable D volume A A₁ := hcontD.intervalIntegrable
  have hWcos : IntervalIntegrable (fun x => weight α p x * Real.cos x)
      volume A A₁ :=
    (hcontW.mul Real.continuous_cos.continuousOn).intervalIntegrable
  have hDsin : IntervalIntegrable (fun x => D x * Real.sin x)
      volume A A₁ :=
    (hcontD.mul Real.continuous_sin.continuousOn).intervalIntegrable
  have hfund : (∫ x in A..A₁, D x) = weight α p A₁ - weight α p A := by
    simpa using intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x hx => hweight_deriv x (hpos_of_mem x hx)) hDint
  have hprod :
      (∫ x in A..A₁, D x * Real.sin x) +
          (∫ x in A..A₁, weight α p x * Real.cos x) =
        weight α p A₁ * Real.sin A₁ - weight α p A * Real.sin A := by
    have hsumInt : IntervalIntegrable
        (fun x => D x * Real.sin x + weight α p x * Real.cos x)
        volume A A₁ := hDsin.add hWcos
    have hFTC :
        (∫ x in A..A₁, D x * Real.sin x + weight α p x * Real.cos x) =
          weight α p A₁ * Real.sin A₁ - weight α p A * Real.sin A := by
      simpa using intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun x hx =>
          (hweight_deriv x (hpos_of_mem x hx)).mul
            (Real.hasDerivAt_sin x))
        hsumInt
    rw [intervalIntegral.integral_add hDsin hWcos] at hFTC
    exact hFTC
  have hleft : (∫ x in A..A₁, D x) ≤
      ∫ x in A..A₁, D x * Real.sin x := by
    apply intervalIntegral.integral_mono_on (le_of_lt hAA₁) hDint hDsin
    intro x hx
    have hx0 : 0 < x :=
      lt_trans zero_lt_one (lt_of_lt_of_le hA hx.1)
    have hDx := hD_nonpos x hx0
    simpa using mul_le_mul_of_nonpos_left (Real.sin_le_one x) hDx
  have hnegDint : IntervalIntegrable (fun x => -D x) volume A A₁ := hDint.neg
  have hright : (∫ x in A..A₁, D x * Real.sin x) ≤
      ∫ x in A..A₁, -D x := by
    apply intervalIntegral.integral_mono_on (le_of_lt hAA₁) hDsin hnegDint
    intro x hx
    have hx0 : 0 < x :=
      lt_trans zero_lt_one (lt_of_lt_of_le hA hx.1)
    have hDx := hD_nonpos x hx0
    have hm := mul_le_mul_of_nonpos_left (Real.neg_one_le_sin x) hDx
    simpa using hm
  have hnegfund : (∫ x in A..A₁, -D x) =
      weight α p A - weight α p A₁ := by
    rw [intervalIntegral.integral_neg]
    linarith
  have hJlo : weight α p A₁ - weight α p A ≤
      ∫ x in A..A₁, D x * Real.sin x := by linarith
  have hJhi : (∫ x in A..A₁, D x * Real.sin x) ≤
      weight α p A - weight α p A₁ := by linarith
  have hwA : 0 ≤ weight α p A := by
    exact le_of_lt (div_pos (Real.exp_pos _)
      (Real.rpow_pos_of_pos (lt_trans zero_lt_one hA) p))
  have hwA₁ : 0 ≤ weight α p A₁ := by
    exact le_of_lt (div_pos (Real.exp_pos _)
      (Real.rpow_pos_of_pos
        (lt_trans (lt_trans zero_lt_one hA) hAA₁) p))
  have hbA : |weight α p A * Real.sin A| ≤ weight α p A := by
    rw [abs_mul, abs_of_nonneg hwA]
    exact mul_le_of_le_one_right hwA (Real.abs_sin_le_one A)
  have hbA₁ : |weight α p A₁ * Real.sin A₁| ≤ weight α p A₁ := by
    rw [abs_mul, abs_of_nonneg hwA₁]
    exact mul_le_of_le_one_right hwA₁ (Real.abs_sin_le_one A₁)
  have hfun : integrand α p = fun x => weight α p x * Real.cos x := by
    funext x
    unfold integrand weight
    ring
  rw [hfun]
  apply (abs_le).2
  rcases (abs_le.1 hbA) with ⟨hbAlo, hbAhi⟩
  rcases (abs_le.1 hbA₁) with ⟨hbA₁lo, hbA₁hi⟩
  constructor <;> linarith

theorem gap1 (A : ℝ) :
    |∫ x in (1 : ℝ)..A, Real.cos x| =
      |Real.sin A - Real.sin 1| := by
  have hcos : IntervalIntegrable Real.cos volume (1 : ℝ) A :=
    Real.continuous_cos.intervalIntegrable (1 : ℝ) A
  have h : (∫ x in (1 : ℝ)..A, Real.cos x) =
      Real.sin A - Real.sin 1 := by
    simpa using intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x _ => Real.hasDerivAt_sin x) hcos
  rw [h]

theorem gap2 (A : ℝ) :
    |Real.sin A - Real.sin 1| ≤ 2 := by
  calc
    |Real.sin A - Real.sin 1| ≤ |Real.sin A| + |Real.sin 1| := abs_sub _ _
    _ ≤ 1 + 1 := add_le_add (Real.abs_sin_le_one A) (Real.abs_sin_le_one 1)
    _ = 2 := by norm_num

theorem gap3 (A : ℝ) :
    |∫ x in (1 : ℝ)..A, Real.cos x| ≤ 2 := by
  rw [gap1]
  exact gap2 A

theorem gap4 (α p : ℝ) (hα : 0 ≤ α) (hp : 0 < p) :
    AntitoneOn (weight α p) (Set.Ici 1) := by
  intro x hx y hy hxy
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hy0 : 0 < y := lt_of_lt_of_le zero_lt_one hy
  have he : Real.exp (-(α * y)) ≤ Real.exp (-(α * x)) := by
    apply Real.exp_le_exp.mpr
    exact neg_le_neg (mul_le_mul_of_nonneg_left hxy hα)
  have hr : Real.rpow x p ≤ Real.rpow y p :=
    Real.rpow_le_rpow (le_of_lt hx0) hxy (le_of_lt hp)
  have hrx : 0 < Real.rpow x p := Real.rpow_pos_of_pos hx0 p
  have hry : 0 < Real.rpow y p := Real.rpow_pos_of_pos hy0 p
  unfold weight
  apply (div_le_div_iff₀ hry hrx).2
  calc
    Real.exp (-(α * y)) * Real.rpow x p
        ≤ Real.exp (-(α * x)) * Real.rpow x p :=
      mul_le_mul_of_nonneg_right he (le_of_lt hrx)
    _ ≤ Real.exp (-(α * x)) * Real.rpow y p :=
      mul_le_mul_of_nonneg_left hr (le_of_lt (Real.exp_pos _))

theorem gap5 (α x p : ℝ) (hx : 0 < x) :
    0 < weight α p x := by
  unfold weight
  exact div_pos (Real.exp_pos _) (Real.rpow_pos_of_pos hx p)

theorem gap6 (α x p : ℝ) (hα : 0 ≤ α) (hx : 0 < x) :
    weight α p x ≤ 1 / Real.rpow x p := by
  unfold weight
  have hr : 0 < Real.rpow x p := Real.rpow_pos_of_pos hx p
  have he : Real.exp (-(α * x)) ≤ 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (neg_nonpos.mpr (mul_nonneg hα (le_of_lt hx)))
  apply (div_le_div_iff₀ hr hr).2
  exact mul_le_mul_of_nonneg_right he (le_of_lt hr)

theorem gap7 (x p : ℝ) (hx : 0 < x) :
    0 < 1 / Real.rpow x p := by
  exact one_div_pos.mpr (Real.rpow_pos_of_pos hx p)

theorem gap8 (α p : ℝ) (hα : 0 ≤ α) (hp : 0 < p) :
    Tendsto (weight α p) atTop (nhds 0) := by
  have hinner_log : Tendsto (fun z : ℝ => -(z * p)) atTop atBot := by
    refine tendsto_atBot.2 ?_
    intro b
    filter_upwards [eventually_ge_atTop ((-b) / p)] with z hz
    have hz' : -b ≤ z * p := (div_le_iff₀ hp).mp hz
    linarith
  have hinner : Tendsto (fun x : ℝ => -(Real.log x * p)) atTop atBot :=
    hinner_log.comp Real.tendsto_log_atTop
  have hexp : Tendsto (fun x : ℝ => Real.exp (-(Real.log x * p)))
      atTop (nhds 0) := Real.tendsto_exp_atBot.comp hinner
  have heq : (fun x : ℝ => 1 / Real.rpow x p) =ᶠ[atTop]
      (fun x : ℝ => Real.exp (-(Real.log x * p))) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    change 1 / (x ^ p) = Real.exp (-(Real.log x * p))
    have hrpow : (x ^ p : ℝ) = Real.exp (Real.log x * p) :=
      Real.rpow_def_of_pos hx p
    rw [hrpow]
    simpa [one_div] using (Real.exp_neg (Real.log x * p)).symm
  have hlim : Tendsto (fun x : ℝ => 1 / Real.rpow x p) atTop (nhds 0) :=
    hexp.congr' heq.symm
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hlim ?_ ?_
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    exact le_of_lt (gap5 α x p hx)
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    exact gap6 α x p hα hx

theorem gap9 (p ε : ℝ) (hp : 0 < p) (hε : 0 < ε) :
    ∃ A₀ : ℝ, 1 < A₀ ∧
      ∀ A A₁ α : ℝ, A₀ < A → A < A₁ → 0 ≤ α →
        |∫ x in A..A₁, integrand α p x| < ε := by
  have hev : ∀ᶠ x : ℝ in atTop, weight 0 p x < ε / 2 :=
    (tendsto_order.1 (gap8 0 p (le_refl 0) hp)).2 (ε / 2) (half_pos hε)
  rcases eventually_atTop.1 hev with ⟨B, hB⟩
  refine ⟨max 1 B + 1, by linarith [le_max_left (1 : ℝ) B], ?_⟩
  intro A A₁ α hA hAA₁ hα
  have hA1 : 1 < A :=
    lt_trans (by linarith [le_max_left (1 : ℝ) B]) hA
  have hAB : B ≤ A := by
    linarith [le_max_right (1 : ℝ) B]
  have hsmall : weight 0 p A < ε / 2 := hB A hAB
  have hw : weight α p A ≤ weight 0 p A := by
    have h := gap6 α A p hα (lt_trans zero_lt_one hA1)
    simpa [weight] using h
  have hbound := tail_integral_bound α p A A₁ hα hp hA1 hAA₁
  nlinarith

theorem gap10 (p ε : ℝ) (hp : 0 < p) (hε : 0 < ε) :
    ∃ A₀ : ℝ, 1 < A₀ ∧
      ∀ A A₁ α : ℝ, A₀ < A → A < A₁ → 0 ≤ α →
        |∫ x in A..A₁, integrand α p x| < ε := by
  exact gap9 p ε hp hε

end

end ProofGap.Exercise3761
