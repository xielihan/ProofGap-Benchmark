import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Order.Filter.Tendsto
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Neighborhoods
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise2344
noncomputable section

open Filter
open scoped Interval

def integrand (x : ℝ) : ℝ := x * Real.log x / (1 + x ^ 2) ^ 2
def auxiliaryIntegrand (x : ℝ) : ℝ := 1 / (x * (1 + x ^ 2))
def splitAuxiliaryIntegrand (x : ℝ) : ℝ := 1 / x - x / (1 + x ^ 2)

def primitive (x : ℝ) : ℝ :=
  -Real.log x / (2 * (1 + x ^ 2)) +
    (1 / 4 : ℝ) * Real.log (x ^ 2 / (1 + x ^ 2))

def FamilyOn (f : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∀ x > 0, HasDerivAt F (f x) x}

def TranslatesOn (P : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x > 0, F x = P x + C}

def FirstPartsFamily : Set (ℝ → ℝ) :=
  {F | ∃ G : ℝ → ℝ,
    (∀ x > 0, HasDerivAt G (-2 * x * Real.log x / (1 + x ^ 2) ^ 2) x) ∧
    ∀ x > 0, F x = -(1 / 2 : ℝ) * G x}

def SecondPartsFamily (g : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ G : ℝ → ℝ,
    (∀ x > 0, HasDerivAt G (g x) x) ∧
    ∀ x > 0, F x = -Real.log x / (2 * (1 + x ^ 2)) + (1 / 2 : ℝ) * G x}

def boundaryExpression (ε : ℝ) : ℝ :=
  -(ε ^ 2 / (2 * (ε ^ 2 + 1))) * Real.log ε +
    (1 / 4 : ℝ) * Real.log (ε ^ 2 + 1)

private theorem hasDerivAt_logQuotient {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun y : ℝ => Real.log y / (1 + y ^ 2))
      (auxiliaryIntegrand x - 2 * x * Real.log x / (1 + x ^ 2) ^ 2) x := by
  have hx0 : x ≠ 0 := ne_of_gt hx
  have hden : 1 + x ^ 2 ≠ 0 := by positivity
  have hlog := Real.hasDerivAt_log hx0
  have hpoly := (hasDerivAt_const x 1).add ((hasDerivAt_id x).pow 2)
  convert hlog.div hpoly hden using 1 <;>
    simp [auxiliaryIntegrand] <;>
    field_simp [hx0, hden] <;>
    ring

private def canonicalAuxiliary (x : ℝ) : ℝ :=
  Real.log x - (1 / 2 : ℝ) * Real.log (1 + x ^ 2)

private theorem hasDerivAt_canonicalAuxiliary (x : ℝ) (hx : 0 < x) :
    HasDerivAt canonicalAuxiliary (splitAuxiliaryIntegrand x) x := by
  have hx0 : x ≠ 0 := ne_of_gt hx
  have hden : 1 + x ^ 2 ≠ 0 := by positivity
  have hlog := Real.hasDerivAt_log hx0
  have hpoly := (hasDerivAt_const x 1).add ((hasDerivAt_id x).pow 2)
  have hlogden := hpoly.log hden
  change HasDerivAt
    (fun y : ℝ => Real.log y - (1 / 2 : ℝ) * Real.log (1 + y ^ 2))
    (splitAuxiliaryIntegrand x) x
  convert hlog.sub (hlogden.const_mul (1 / 2 : ℝ)) using 1 <;>
    simp [splitAuxiliaryIntegrand] <;>
    field_simp [hx0, hden] <;>
    ring

private theorem primitive_eq_secondForm {x : ℝ} (hx : 0 < x) :
    primitive x =
      -Real.log x / (2 * (1 + x ^ 2)) +
        (1 / 2 : ℝ) * canonicalAuxiliary x := by
  have hx0 : x ≠ 0 := ne_of_gt hx
  have hden : 1 + x ^ 2 ≠ 0 := by positivity
  unfold primitive
  rw [show Real.log (x ^ 2 / (1 + x ^ 2)) =
      2 * Real.log x - Real.log (1 + x ^ 2) by
    rw [Real.log_div (pow_ne_zero 2 hx0) hden, Real.log_pow]
    norm_num]
  unfold canonicalAuxiliary
  ring

private theorem continuousAt_integrand {x : ℝ} (hx : 0 < x) :
    ContinuousAt integrand x := by
  have hx0 : x ≠ 0 := ne_of_gt hx
  have hden : (1 + x ^ 2) ^ 2 ≠ 0 := by positivity
  simpa [integrand] using
    (continuousAt_id.mul (Real.continuousAt_log hx0)).div
      ((continuousAt_const.add (continuousAt_id.pow 2)).pow 2) hden

private theorem boundaryExpression_tendsto_zero :
    Tendsto boundaryExpression (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  let l := nhdsWithin (0 : ℝ) (Set.Ioi 0)
  have hx : Tendsto (fun x : ℝ => x) l (nhds 0) :=
    tendsto_id.mono_left inf_le_left
  have hsql : Tendsto (fun x : ℝ => x ^ 2 * Real.log x) l (nhds 0) := by
    have hlt : ∀ᶠ x in l, x < 1 :=
      (tendsto_order.1 hx).2 1 (by norm_num)
    have hbounds :
        ∀ᶠ x in l, -x ≤ x ^ 2 * Real.log x ∧ x ^ 2 * Real.log x ≤ 0 := by
      filter_upwards [self_mem_nhdsWithin, hlt] with x hxpos hxon
      have hxpos' : 0 < x := hxpos
      have hx0 : x ≠ 0 := ne_of_gt hxpos'
      have hlogInv : Real.log (x⁻¹) ≤ x⁻¹ - 1 :=
        Real.log_le_sub_one_of_pos (inv_pos.mpr hxpos')
      rw [Real.log_inv] at hlogInv
      have hmul := mul_le_mul_of_nonneg_left hlogInv (le_of_lt hxpos')
      rw [mul_sub, mul_inv_cancel₀ hx0, mul_one] at hmul
      have hmul' : -(x * Real.log x) ≤ 1 - x := by
        simpa only [mul_neg] using hmul
      have hnegBound : -(x * Real.log x) ≤ 1 :=
        hmul'.trans (sub_le_self 1 (le_of_lt hxpos'))
      have hbase : -1 ≤ x * Real.log x := by
        have h := neg_le_neg hnegBound
        simpa only [neg_neg] using h
      have hlower := mul_le_mul_of_nonneg_left hbase (le_of_lt hxpos')
      have hlower' : -x ≤ x ^ 2 * Real.log x := by
        convert hlower using 1 <;> ring
      have hlogNonpos : Real.log x ≤ 0 :=
        Real.log_nonpos (le_of_lt hxpos') (le_of_lt hxon)
      have hupper : x ^ 2 * Real.log x ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (sq_nonneg x) hlogNonpos
      exact ⟨hlower', hupper⟩
    have hneg : Tendsto (fun x : ℝ => -x) l (nhds 0) := by
      simpa using hx.neg
    have hzero : Tendsto (fun _ : ℝ => (0 : ℝ)) l (nhds 0) :=
      tendsto_const_nhds
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hneg hzero
      (hbounds.mono fun x h => h.1) (hbounds.mono fun x h => h.2)
  have hden : Tendsto (fun x : ℝ => 2 * (x ^ 2 + 1)) l (nhds 2) := by
    convert (tendsto_const_nhds.mul ((hx.pow 2).add tendsto_const_nhds)) using 1 <;>
      norm_num
  have hfirst :
      Tendsto (fun x : ℝ => -(x ^ 2 * Real.log x) / (2 * (x ^ 2 + 1))) l (nhds 0) := by
    convert hsql.neg.div hden (by norm_num : (2 : ℝ) ≠ 0) using 1 <;> norm_num
  have hone : Tendsto (fun x : ℝ => x ^ 2 + 1) l (nhds 1) := by
    convert (hx.pow 2).add tendsto_const_nhds using 1 <;> norm_num
  have hlog : Tendsto (fun x : ℝ => Real.log (x ^ 2 + 1)) l (nhds 0) := by
    convert (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp hone using 1 <;>
      norm_num
  have hsecond :
      Tendsto (fun x : ℝ => (1 / 4 : ℝ) * Real.log (x ^ 2 + 1)) l (nhds 0) := by
    convert tendsto_const_nhds.mul hlog using 1 <;> norm_num
  convert hfirst.add hsecond using 1
  · funext x
    simp [boundaryExpression]
    ring
  · norm_num

private theorem primitive_inv {x : ℝ} (hx : 0 < x) :
    primitive x⁻¹ = primitive x := by
  have hx0 : x ≠ 0 := ne_of_gt hx
  have hden : 1 + x ^ 2 ≠ 0 := by positivity
  have hdenInv : 1 + x⁻¹ ^ 2 ≠ 0 := by positivity
  have hlogden :
      Real.log (1 + x⁻¹ ^ 2) =
        Real.log (1 + x ^ 2) - 2 * Real.log x := by
    calc
      Real.log (1 + x⁻¹ ^ 2) =
          Real.log ((1 + x ^ 2) / x ^ 2) := by
            congr 1
            field_simp [hx0] <;> ring
      _ = Real.log (1 + x ^ 2) - Real.log (x ^ 2) := by
            rw [Real.log_div hden (pow_ne_zero 2 hx0)]
      _ = Real.log (1 + x ^ 2) - 2 * Real.log x := by
            rw [Real.log_pow]
            norm_num
  rw [primitive_eq_secondForm (inv_pos.mpr hx), primitive_eq_secondForm hx]
  unfold canonicalAuxiliary
  rw [Real.log_inv, hlogden]
  field_simp [hx0, hden, hdenInv] <;> ring

private def positiveExhaustion (n : ℕ) : Set ℝ :=
  Set.Ioc (((n : ℝ) + 1)⁻¹) ((n : ℝ) + 1)

private theorem positiveExhaustion_mono : Monotone positiveExhaustion := by
  rintro m n hmn x ⟨hxlow, hxhigh⟩
  have hmnR : (m : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast hmn
  have hsum : (m : ℝ) + 1 ≤ (n : ℝ) + 1 := by linarith
  have hmpos : 0 < (m : ℝ) + 1 := by positivity
  have hlower : (((n : ℝ) + 1)⁻¹) ≤ (((m : ℝ) + 1)⁻¹) := by
    simpa only [one_div] using one_div_le_one_div_of_le hmpos hsum
  exact ⟨lt_of_le_of_lt hlower hxlow, le_trans hxhigh hsum⟩

private theorem positiveExhaustion_iUnion :
    (⋃ n : ℕ, positiveExhaustion n) = Set.Ioi (0 : ℝ) := by
  ext x
  constructor
  · intro hx
    rcases Set.mem_iUnion.1 hx with ⟨n, hn⟩
    rcases hn with ⟨hnlow, hnhigh⟩
    have hpos : 0 < (((n : ℝ) + 1)⁻¹) := by positivity
    exact hpos.trans hnlow
  · intro hx
    have hxpos : 0 < x := hx
    obtain ⟨n, hn⟩ := exists_nat_gt (max x x⁻¹)
    have hxlt : x < (n : ℝ) :=
      lt_of_le_of_lt (le_max_left x x⁻¹) hn
    have hinvlt : x⁻¹ < (n : ℝ) :=
      lt_of_le_of_lt (le_max_right x x⁻¹) hn
    have hinvlt' : x⁻¹ < (n : ℝ) + 1 := by linarith
    have hlower : (((n : ℝ) + 1)⁻¹) < x := by
      have h := one_div_lt_one_div_of_lt (inv_pos.mpr hxpos) hinvlt'
      simpa only [one_div, inv_inv] using h
    have hupper : x ≤ (n : ℝ) + 1 := by linarith
    exact Set.mem_iUnion.2 ⟨n, hlower, hupper⟩

theorem gap1 : FamilyOn integrand = FirstPartsFamily := by
  ext F
  constructor
  · intro hF
    refine ⟨fun x => -2 * F x, ?_, ?_⟩
    · intro x hx
      convert (hF x hx).const_mul (-2) using 1 <;>
        simp [integrand] <;> ring
    · intro x hx
      ring
  · rintro ⟨G, hG, hFG⟩
    intro x hx
    have hd := (hG x hx).const_mul (-(1 / 2 : ℝ))
    have heq : F =ᶠ[nhds x] (fun y => -(1 / 2 : ℝ) * G y) := by
      filter_upwards [Ioi_mem_nhds hx] with y hy
      exact hFG y hy
    convert hd.congr_of_eventuallyEq heq using 1 <;>
      simp [integrand] <;> ring

theorem gap2 : FirstPartsFamily = SecondPartsFamily auxiliaryIntegrand := by
  ext F
  constructor
  · rintro ⟨G, hG, hFG⟩
    refine ⟨fun x => -G x + Real.log x / (1 + x ^ 2), ?_, ?_⟩
    · intro x hx
      convert (hG x hx).neg.add (hasDerivAt_logQuotient hx) using 1 <;>
        simp [auxiliaryIntegrand] <;> ring
    · intro x hx
      have hden : 1 + x ^ 2 ≠ 0 := by positivity
      rw [hFG x hx]
      field_simp [hden] <;> ring
  · rintro ⟨G, hG, hFG⟩
    refine ⟨fun x => Real.log x / (1 + x ^ 2) - G x, ?_, ?_⟩
    · intro x hx
      convert (hasDerivAt_logQuotient hx).sub (hG x hx) using 1 <;>
        simp [auxiliaryIntegrand] <;> ring
    · intro x hx
      have hden : 1 + x ^ 2 ≠ 0 := by positivity
      rw [hFG x hx]
      field_simp [hden] <;> ring

theorem gap3 : FamilyOn integrand = SecondPartsFamily auxiliaryIntegrand := by
  exact gap1.trans gap2

theorem gap4 :
    FamilyOn integrand = SecondPartsFamily splitAuxiliaryIntegrand := by
  rw [gap3]
  ext F
  constructor
  · rintro ⟨G, hG, hFG⟩
    refine ⟨G, ?_, hFG⟩
    intro x hx
    have hx0 : x ≠ 0 := ne_of_gt hx
    convert hG x hx using 1
    simp only [auxiliaryIntegrand, splitAuxiliaryIntegrand]
    field_simp [hx0] <;> ring
  · rintro ⟨G, hG, hFG⟩
    refine ⟨G, ?_, hFG⟩
    intro x hx
    have hx0 : x ≠ 0 := ne_of_gt hx
    convert hG x hx using 1
    simp only [auxiliaryIntegrand, splitAuxiliaryIntegrand]
    field_simp [hx0] <;> ring

theorem gap5 :
    SecondPartsFamily splitAuxiliaryIntegrand = TranslatesOn primitive := by
  have hprimitiveSecond : primitive ∈ SecondPartsFamily splitAuxiliaryIntegrand := by
    refine ⟨canonicalAuxiliary, hasDerivAt_canonicalAuxiliary, ?_⟩
    intro x hx
    exact primitive_eq_secondForm hx
  have hprimitiveFamily : primitive ∈ FamilyOn integrand := by
    rw [gap4]
    exact hprimitiveSecond
  ext F
  constructor
  · intro hF
    have hFFamily : F ∈ FamilyOn integrand := by
      rw [gap4]
      exact hF
    let D : ℝ → ℝ := fun x => F x - primitive x
    have hdiff : DifferentiableOn ℝ D (Set.Ioi 0) := by
      intro x hx
      exact ((hFFamily x hx).sub (hprimitiveFamily x hx)).differentiableAt.differentiableWithinAt
    have hzero : ∀ x ∈ Set.Ioi (0 : ℝ), deriv D x = 0 := by
      intro x hx
      exact ((hFFamily x hx).sub (hprimitiveFamily x hx)).deriv.trans
        (sub_self (integrand x))
    refine ⟨F 1 - primitive 1, ?_⟩
    intro x hx
    have heq := isOpen_Ioi.is_const_of_deriv_eq_zero isPreconnected_Ioi
      hdiff hzero hx (by norm_num : (1 : ℝ) ∈ Set.Ioi 0)
    dsimp [D] at heq
    linarith
  · rintro ⟨C, hFC⟩
    refine ⟨fun x => canonicalAuxiliary x + 2 * C, ?_, ?_⟩
    · intro x hx
      simpa using (hasDerivAt_canonicalAuxiliary x hx).add_const (2 * C)
    · intro x hx
      rw [hFC x hx, primitive_eq_secondForm hx]
      ring

theorem gap6 : FamilyOn integrand = TranslatesOn primitive := by
  exact gap4.trans gap5

theorem gap7 (a : ℝ) (ha : 0 < a) :
    Tendsto (fun b => ∫ x in a..b, integrand x) atTop
        (nhds (-primitive a)) ↔
      Tendsto (fun b => primitive b - primitive a) atTop
        (nhds (-primitive a)) := by
  have hp : primitive ∈ FamilyOn integrand := by
    rw [gap6]
    exact ⟨0, by simp⟩
  have heq :
      (fun b => ∫ x in a..b, integrand x) =ᶠ[atTop]
        (fun b => primitive b - primitive a) := by
    filter_upwards [eventually_gt_atTop a] with b hb
    have hb0 : 0 < b := lt_trans ha hb
    have hpos : ∀ x ∈ Set.uIcc a b, 0 < x := by
      intro x hx
      have hxab : x ∈ Set.Icc a b := by
        simpa [Set.uIcc_of_le (le_of_lt hb)] using hx
      exact lt_of_lt_of_le ha hxab.1
    have hc : ContinuousOn integrand (Set.uIcc a b) := by
      intro x hx
      have hx0 := hpos x hx
      simpa [integrand] using (continuousAt_integrand hx0).continuousWithinAt
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · intro x hx
      exact hp x (hpos x hx)
    · exact hc.intervalIntegrable
  exact tendsto_congr' heq

theorem gap8 :
    (∫ x in Set.Ioi (0 : ℝ), integrand x) = 0 ↔
      Tendsto boundaryExpression (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  constructor
  · intro _
    exact boundaryExpression_tendsto_zero
  · intro _
    by_cases hInt : MeasureTheory.IntegrableOn integrand (Set.Ioi 0)
    · have hp : primitive ∈ FamilyOn integrand := by
        rw [gap6]
        exact ⟨0, by simp⟩
      have hzero : ∀ n : ℕ,
          (∫ x in positiveExhaustion n, integrand x) = 0 := by
        intro n
        let r : ℝ := (n : ℝ) + 1
        have hr : 0 < r := by
          dsimp [r]
          positivity
        have hn : (0 : ℝ) ≤ (n : ℝ) := by positivity
        have hrone : 1 ≤ r := by
          dsimp [r]
          linarith
        have hinvleone : r⁻¹ ≤ (1 : ℝ) := by
          simpa only [one_div, inv_one] using
            (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hrone)
        have hle : r⁻¹ ≤ r := hinvleone.trans hrone
        have hpos : ∀ x ∈ Set.uIcc r⁻¹ r, 0 < x := by
          intro x hx
          have hxIcc : x ∈ Set.Icc r⁻¹ r := by
            simpa [Set.uIcc_of_le hle] using hx
          exact (inv_pos.mpr hr).trans_le hxIcc.1
        have hc : ContinuousOn integrand (Set.uIcc r⁻¹ r) := by
          intro x hx
          exact (continuousAt_integrand (hpos x hx)).continuousWithinAt
        have hinterval :
            (∫ x in r⁻¹..r, integrand x) = primitive r - primitive r⁻¹ := by
          apply intervalIntegral.integral_eq_sub_of_hasDerivAt
          · intro x hx
            exact hp x (hpos x hx)
          · exact hc.intervalIntegrable
        rw [intervalIntegral.integral_of_le hle] at hinterval
        change (∫ x in Set.Ioc r⁻¹ r, integrand x) = 0
        calc
          (∫ x in Set.Ioc r⁻¹ r, integrand x) = primitive r - primitive r⁻¹ := hinterval
          _ = 0 := by rw [primitive_inv hr]; ring
      have ht :
          Tendsto
            (fun n : ℕ => ∫ x in positiveExhaustion n, integrand x)
            atTop
            (nhds (∫ x in (⋃ n : ℕ, positiveExhaustion n), integrand x)) := by
        apply MeasureTheory.tendsto_setIntegral_of_monotone
        all_goals
          first
          | exact positiveExhaustion_mono
          | exact fun _ => measurableSet_Ioc
          | simpa only [positiveExhaustion_iUnion] using hInt
      rw [positiveExhaustion_iUnion] at ht
      have ht0 :
          Tendsto (fun _ : ℕ => (0 : ℝ)) atTop
            (nhds (∫ x in Set.Ioi (0 : ℝ), integrand x)) := by
        simpa only [hzero] using ht
      exact tendsto_nhds_unique ht0 tendsto_const_nhds
    · exact MeasureTheory.integral_undef hInt

theorem gap9 :
    Tendsto boundaryExpression (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  exact boundaryExpression_tendsto_zero

theorem gap10 :
    (∫ x in Set.Ioi (0 : ℝ), integrand x) = 0 := by
  exact gap8.mpr gap9

end
end ProofGap.Exercise2344
