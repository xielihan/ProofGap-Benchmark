import ProofGapLean.Prelude.Analysis
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.LHopital
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Neighborhoods
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open Filter Topology
open scoped Interval

namespace ProofGap.Exercise2234

noncomputable section

def integral (x : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..x, Real.exp (t ^ 2)

def comparison (x : ℝ) : ℝ :=
  (1 / (2 * x)) * Real.exp (x ^ 2)

def derivativeRatio (x : ℝ) : ℝ :=
  Real.exp (x ^ 2) /
    (Real.exp (x ^ 2) * (1 - 1 / (2 * x ^ 2)))

def quotient (x : ℝ) : ℝ := integral x / comparison x

private theorem exercise2234_limits :
    Tendsto derivativeRatio atTop (nhds 1) ∧
      Tendsto quotient atTop (nhds 1) := by
  have hsquare : Tendsto (fun x : ℝ => x ^ 2) atTop atTop := by
    simpa using
      (tendsto_pow_atTop_atTop_of_one_lt
        (R := ℝ) (by norm_num : 1 < (2 : ℕ)))
  have hinvSquare :
      Tendsto (fun x : ℝ => (x ^ 2)⁻¹) atTop (nhds 0) := by
    exact tendsto_inv_atTop_zero.comp hsquare
  have hscaledInv :
      Tendsto (fun x : ℝ => (1 / 2 : ℝ) * (x ^ 2)⁻¹) atTop (nhds 0) := by
    convert tendsto_const_nhds.mul hinvSquare using 1 <;> norm_num
  have hsmall :
      Tendsto (fun x : ℝ => 1 / (2 * x ^ 2)) atTop (nhds 0) := by
    convert hscaledInv using 1
    ext x
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  have hden :
      Tendsto (fun x : ℝ => 1 - 1 / (2 * x ^ 2)) atTop (nhds 1) := by
    convert tendsto_const_nhds.sub hsmall using 1 <;> norm_num
  have hratio' :
      Tendsto (fun x : ℝ => 1 / (1 - 1 / (2 * x ^ 2))) atTop (nhds 1) := by
    convert tendsto_const_nhds.div hden (by norm_num : (1 : ℝ) ≠ 0) using 1 <;>
      norm_num
  have hratio : Tendsto derivativeRatio atTop (nhds 1) := by
    have heq :
        derivativeRatio = fun x : ℝ => 1 / (1 - 1 / (2 * x ^ 2)) := by
      funext x
      unfold derivativeRatio
      field_simp [Real.exp_ne_zero]
    rw [heq]
    exact hratio'
  have hcomparison : Tendsto comparison atTop atTop := by
    refine tendsto_atTop.2 ?_
    intro b
    filter_upwards [eventually_ge_atTop (max 1 (2 * b))] with x hx
    have hx1 : 1 ≤ x := le_trans (le_max_left 1 (2 * b)) hx
    have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx1
    have hb : b ≤ x / 2 := by
      have hxb : 2 * b ≤ x := le_trans (le_max_right 1 (2 * b)) hx
      linarith
    have hexp : x ^ 2 ≤ Real.exp (x ^ 2) := by
      have h := Real.add_one_le_exp (x ^ 2)
      nlinarith
    calc
      b ≤ x / 2 := hb
      _ = (1 / (2 * x)) * x ^ 2 := by field_simp
      _ ≤ (1 / (2 * x)) * Real.exp (x ^ 2) := by
        exact mul_le_mul_of_nonneg_left hexp (by positivity)
      _ = comparison x := by rfl
  have hderivs :
      ∀ᶠ x : ℝ in atTop,
        HasDerivAt integral (Real.exp (x ^ 2)) x ∧
          HasDerivAt comparison
            (Real.exp (x ^ 2) * (1 - 1 / (2 * x ^ 2))) x := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    have hxne : x ≠ 0 := ne_of_gt hx
    constructor
    · unfold integral
      have hcont : Continuous (fun t : ℝ => Real.exp (t ^ 2)) := by
        simpa only [Function.comp_apply, id_eq] using
          Real.continuous_exp.comp (continuous_id.pow 2)
      have hint :
          IntervalIntegrable (fun t : ℝ => Real.exp (t ^ 2))
            MeasureTheory.volume (0 : ℝ) x :=
        hcont.intervalIntegrable (0 : ℝ) x
      have hca :
          ContinuousAt (fun t : ℝ => Real.exp (t ^ 2)) x :=
        hcont.continuousAt
      refine intervalIntegral.integral_hasDerivAt_right hint ?_ hca
      exact hcont.stronglyMeasurable.stronglyMeasurableAtFilter
    · have hlin : HasDerivAt (fun y : ℝ => 2 * y) 2 x := by
        simpa using (hasDerivAt_const x (2 : ℝ)).mul (hasDerivAt_id x)
      have hinv :
          HasDerivAt (fun y : ℝ => 1 / (2 * y)) (-1 / (2 * x ^ 2)) x := by
        convert (hasDerivAt_const x (1 : ℝ)).div hlin (by positivity) using 1 <;>
          field_simp [hxne] <;> ring
      have hsq : HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by
        simpa [pow_two, two_mul] using
          (hasDerivAt_id x).mul (hasDerivAt_id x)
      have hexp :
          HasDerivAt (fun y : ℝ => Real.exp (y ^ 2))
            (Real.exp (x ^ 2) * (2 * x)) x := by
        simpa only [Function.comp_apply] using
          (Real.hasDerivAt_exp (x ^ 2)).comp x hsq
      unfold comparison
      convert hinv.mul hexp using 1 <;> field_simp [hxne] <;> ring
  have hinvComparison :
      Tendsto (fun x : ℝ => (comparison x)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp hcomparison
  have hconstDiv : ∀ c : ℝ,
      Tendsto (fun x : ℝ => c / comparison x) atTop (nhds 0) := by
    intro c
    have hc : Tendsto (fun _ : ℝ => c) atTop (nhds c) :=
      tendsto_const_nhds
    simpa [div_eq_mul_inv] using (hc.mul hinvComparison)
  have hclose : ∀ ε : ℝ, 0 < ε →
      ∀ᶠ x : ℝ in atTop,
        1 - ε < quotient x ∧ quotient x < 1 + ε := by
    intro ε hε
    let δ : ℝ := ε / 2
    have hδ : 0 < δ := by
      dsimp [δ]
      linarith
    have hlower :
        ∀ᶠ x : ℝ in atTop, 1 - δ < derivativeRatio x :=
      (tendsto_order.1 hratio).1 (1 - δ) (by linarith)
    have hupper :
        ∀ᶠ x : ℝ in atTop, derivativeRatio x < 1 + δ :=
      (tendsto_order.1 hratio).2 (1 + δ) (by linarith)
    have htail :
        ∀ᶠ x : ℝ in atTop,
          1 < x ∧
            HasDerivAt integral (Real.exp (x ^ 2)) x ∧
            HasDerivAt comparison
              (Real.exp (x ^ 2) * (1 - 1 / (2 * x ^ 2))) x ∧
            0 < Real.exp (x ^ 2) * (1 - 1 / (2 * x ^ 2)) ∧
            1 - δ < derivativeRatio x ∧
            derivativeRatio x < 1 + δ := by
      filter_upwards
        [eventually_gt_atTop (1 : ℝ), hderivs, hlower, hupper] with
        x hx hd hlo hup
      have hx0 : 0 < x := lt_trans zero_lt_one hx
      have hlarge : (1 : ℝ) < 2 * x ^ 2 := by
        nlinarith [sq_nonneg (x - 1)]
      have hpos : (0 : ℝ) < 2 * x ^ 2 := by positivity
      have hfrac : (1 : ℝ) / (2 * x ^ 2) < 1 :=
        (div_lt_one hpos).2 hlarge
      have hgp :
          0 < Real.exp (x ^ 2) * (1 - 1 / (2 * x ^ 2)) :=
        mul_pos (Real.exp_pos _) (sub_pos.2 hfrac)
      exact ⟨hx, hd.1, hd.2, hgp, hlo, hup⟩
    rcases (eventually_atTop.1 htail) with ⟨A, hA⟩
    have hlowData : ∀ x ∈ Set.Ici A,
        HasDerivAt
          (fun y : ℝ => integral y - (1 - δ) * comparison y)
          (Real.exp (x ^ 2) -
            (1 - δ) *
              (Real.exp (x ^ 2) * (1 - 1 / (2 * x ^ 2)))) x ∧
        0 < Real.exp (x ^ 2) -
          (1 - δ) *
            (Real.exp (x ^ 2) * (1 - 1 / (2 * x ^ 2))) := by
      intro x hx
      rcases hA x hx with ⟨_, hf, hg, hgp, hlo, _⟩
      have hlo' :
          1 - δ <
            Real.exp (x ^ 2) /
              (Real.exp (x ^ 2) * (1 - 1 / (2 * x ^ 2))) := by
        simpa only [derivativeRatio] using hlo
      have hrel :
          (1 - δ) *
              (Real.exp (x ^ 2) * (1 - 1 / (2 * x ^ 2))) <
            Real.exp (x ^ 2) :=
        (lt_div_iff₀ hgp).1 hlo'
      constructor
      · simpa using
          hf.sub ((hasDerivAt_const x (1 - δ)).mul hg)
      · linarith
    have hhighData : ∀ x ∈ Set.Ici A,
        HasDerivAt
          (fun y : ℝ => (1 + δ) * comparison y - integral y)
          ((1 + δ) *
              (Real.exp (x ^ 2) * (1 - 1 / (2 * x ^ 2))) -
            Real.exp (x ^ 2)) x ∧
        0 < (1 + δ) *
            (Real.exp (x ^ 2) * (1 - 1 / (2 * x ^ 2))) -
          Real.exp (x ^ 2) := by
      intro x hx
      rcases hA x hx with ⟨_, hf, hg, hgp, _, hup⟩
      have hup' :
          Real.exp (x ^ 2) /
              (Real.exp (x ^ 2) * (1 - 1 / (2 * x ^ 2))) <
            1 + δ := by
        simpa only [derivativeRatio] using hup
      have hrel :
          Real.exp (x ^ 2) <
            (1 + δ) *
              (Real.exp (x ^ 2) * (1 - 1 / (2 * x ^ 2))) :=
        (div_lt_iff₀ hgp).1 hup'
      constructor
      · simpa using
          ((hasDerivAt_const x (1 + δ)).mul hg).sub hf
      · linarith
    have hdiffLow : DifferentiableOn ℝ
        (fun y : ℝ => integral y - (1 - δ) * comparison y)
        (Set.Ici A) := by
      intro x hx
      exact (hlowData x hx).1.differentiableAt.differentiableWithinAt
    have hdiffHigh : DifferentiableOn ℝ
        (fun y : ℝ => (1 + δ) * comparison y - integral y)
        (Set.Ici A) := by
      intro x hx
      exact (hhighData x hx).1.differentiableAt.differentiableWithinAt
    have hderivLowOn : ∀ x ∈ Set.Ici A,
        0 < deriv
          (fun y : ℝ => integral y - (1 - δ) * comparison y) x := by
      intro x hx
      have hd := (hlowData x hx).1
      rw [hd.deriv]
      exact (hlowData x hx).2
    have hderivHighOn : ∀ x ∈ Set.Ici A,
        0 < deriv
          (fun y : ℝ => (1 + δ) * comparison y - integral y) x := by
      intro x hx
      have hd := (hhighData x hx).1
      rw [hd.deriv]
      exact (hhighData x hx).2
    have hderivLow : ∀ x ∈ interior (Set.Ici A),
        0 < deriv
          (fun y : ℝ => integral y - (1 - δ) * comparison y) x := by
      intro x hx
      exact hderivLowOn x (interior_subset hx)
    have hderivHigh : ∀ x ∈ interior (Set.Ici A),
        0 < deriv
          (fun y : ℝ => (1 + δ) * comparison y - integral y) x := by
      intro x hx
      exact hderivHighOn x (interior_subset hx)
    have hmonoLow : StrictMonoOn
        (fun y : ℝ => integral y - (1 - δ) * comparison y)
        (Set.Ici A) := by
      exact strictMonoOn_of_deriv_pos
        (convex_Ici A) hdiffLow.continuousOn hderivLow
    have hmonoHigh : StrictMonoOn
        (fun y : ℝ => (1 + δ) * comparison y - integral y)
        (Set.Ici A) := by
      exact strictMonoOn_of_deriv_pos
        (convex_Ici A) hdiffHigh.continuousOn hderivHigh
    let cLow : ℝ := integral A - (1 - δ) * comparison A
    let cHigh : ℝ := integral A - (1 + δ) * comparison A
    have hcLowLower :
        ∀ᶠ x : ℝ in atTop, -δ < cLow / comparison x :=
      (tendsto_order.1 (hconstDiv cLow)).1 (-δ) (by linarith)
    have hcHighUpper :
        ∀ᶠ x : ℝ in atTop, cHigh / comparison x < δ :=
      (tendsto_order.1 (hconstDiv cHigh)).2 δ hδ
    filter_upwards
      [eventually_gt_atTop A, hcLowLower, hcHighUpper] with
      x hx hclow hchigh
    have hxone : (1 : ℝ) < x := (hA x (le_of_lt hx)).1
    have hx0 : (0 : ℝ) < x := lt_trans zero_lt_one hxone
    have hgvalue : 0 < comparison x := by
      unfold comparison
      positivity
    have hincLow :
        integral A - (1 - δ) * comparison A <
          integral x - (1 - δ) * comparison x := by
      exact hmonoLow
        (Set.mem_Ici.mpr (le_refl A))
        (Set.mem_Ici.mpr (le_of_lt hx)) hx
    have hincHigh :
        (1 + δ) * comparison A - integral A <
          (1 + δ) * comparison x - integral x := by
      exact hmonoHigh
        (Set.mem_Ici.mpr (le_refl A))
        (Set.mem_Ici.mpr (le_of_lt hx)) hx
    have hnumLow :
        (1 - δ) * comparison x + cLow < integral x := by
      dsimp [cLow]
      linarith [hincLow]
    have hnumHigh :
        integral x < (1 + δ) * comparison x + cHigh := by
      dsimp [cHigh]
      linarith [hincHigh]
    have hqLow :
        1 - δ + cLow / comparison x < quotient x := by
      unfold quotient
      calc
        1 - δ + cLow / comparison x =
            ((1 - δ) * comparison x + cLow) / comparison x := by
              field_simp [ne_of_gt hgvalue] <;> ring
        _ < integral x / comparison x :=
          (div_lt_div_iff_of_pos_right hgvalue).2 hnumLow
    have hqHigh :
        quotient x < 1 + δ + cHigh / comparison x := by
      unfold quotient
      calc
        integral x / comparison x <
            ((1 + δ) * comparison x + cHigh) / comparison x :=
          (div_lt_div_iff_of_pos_right hgvalue).2 hnumHigh
        _ = 1 + δ + cHigh / comparison x := by
          field_simp [ne_of_gt hgvalue] <;> ring
    have hdelta : δ + δ = ε := by
      dsimp [δ]
      ring
    constructor
    · linarith [hqLow, hclow, hdelta]
    · linarith [hqHigh, hchigh, hdelta]
  have hquot : Tendsto quotient atTop (nhds 1) := by
    refine tendsto_order.2 ⟨?_, ?_⟩
    · intro a ha
      filter_upwards [hclose (1 - a) (sub_pos.mpr ha)] with x hx
      linarith [hx.1]
    · intro b hb
      filter_upwards [hclose (b - 1) (sub_pos.mpr hb)] with x hx
      linarith [hx.2]
  exact ⟨hratio, hquot⟩

theorem gap1 :
    ∀ L : ℝ, Tendsto quotient atTop (𝓝 L) ↔
      Tendsto derivativeRatio atTop (𝓝 L) := by
  intro L
  constructor
  · intro hL
    have hL_eq : L = 1 := tendsto_nhds_unique hL exercise2234_limits.2
    simpa [hL_eq] using exercise2234_limits.1
  · intro hL
    have hL_eq : L = 1 := tendsto_nhds_unique hL exercise2234_limits.1
    simpa [hL_eq] using exercise2234_limits.2

theorem gap2 :
    Tendsto derivativeRatio atTop (𝓝 1) := by
  exact exercise2234_limits.1

theorem gap3 :
    Tendsto quotient atTop (𝓝 1) := by
  exact (gap1 1).2 gap2

theorem gap4 :
    Asymptotics.IsEquivalent atTop integral comparison := by
  refine (Asymptotics.isEquivalent_iff_tendsto_one ?_).2 ?_
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    unfold comparison
    positivity
  · simpa [quotient] using gap3

theorem gap5 :
    Asymptotics.IsEquivalent atTop integral comparison := by
  exact gap4

end

end ProofGap.Exercise2234
