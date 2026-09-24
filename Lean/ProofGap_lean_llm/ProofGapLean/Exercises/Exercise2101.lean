import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Topology.Defs.Filter
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise2101
noncomputable section

def Regular (U : Set ℝ) (a b : ℝ) : Prop :=
  IsOpen U ∧ IsPreconnected U ∧ ∀ x ∈ U, 0 < x + a ∧ 0 < x + b

def sourceIntegrand (a b x : ℝ) :=
  Real.log (Real.rpow (x + a) (x + a) * Real.rpow (x + b) (x + b)) /
    ((x + a) * (x + b))
def firstTerm (a b x : ℝ) := Real.log (x + a) / (x + b)
def secondTerm (a b x : ℝ) := Real.log (x + b) / (x + a)
def firstDifferentialTerm (a b x : ℝ) :=
  Real.log (x + a) * deriv (fun y : ℝ => Real.log (y + b)) x
def secondDifferentialTerm (a b x : ℝ) :=
  Real.log (x + b) * deriv (fun y : ℝ => Real.log (y + a)) x
def productPrimitive (a b x : ℝ) := Real.log (x + a) * Real.log (x + b)

def Family (U : Set ℝ) (f : ℝ → ℝ) :=
  {F : ℝ → ℝ | ∀ x ∈ U, HasDerivAt F (f x) x}
def SumFamily (U : Set ℝ) (f g : ℝ → ℝ) :=
  {F : ℝ → ℝ | ∃ A ∈ Family U f, ∃ B ∈ Family U g,
    ∀ x ∈ U, F x = A x + B x}
def ByPartsFamily (U : Set ℝ) (a b : ℝ) :=
  {F : ℝ → ℝ | ∃ A ∈ Family U (firstDifferentialTerm a b), ∃ C : ℝ,
    ∀ x ∈ U, F x = productPrimitive a b x - A x + C}
def Translates (U : Set ℝ) (p : ℝ → ℝ) :=
  {F : ℝ → ℝ | ∃ C : ℝ, ∀ x ∈ U, F x = p x + C}

private theorem source_eq_terms (a b x : ℝ)
    (hxa : 0 < x + a) (hxb : 0 < x + b) :
    sourceIntegrand a b x = firstTerm a b x + secondTerm a b x := by
  have hra : 0 < Real.rpow (x + a) (x + a) :=
    Real.rpow_pos_of_pos hxa _
  have hrb : 0 < Real.rpow (x + b) (x + b) :=
    Real.rpow_pos_of_pos hxb _
  have hloga :
      Real.log (Real.rpow (x + a) (x + a)) =
        (x + a) * Real.log (x + a) := by
    change Real.log ((x + a) ^ (x + a : ℝ)) =
      (x + a) * Real.log (x + a)
    rw [Real.rpow_def_of_pos hxa, Real.log_exp]
    ring
  have hlogb :
      Real.log (Real.rpow (x + b) (x + b)) =
        (x + b) * Real.log (x + b) := by
    change Real.log ((x + b) ^ (x + b : ℝ)) =
      (x + b) * Real.log (x + b)
    rw [Real.rpow_def_of_pos hxb, Real.log_exp]
    ring
  rw [sourceIntegrand, firstTerm, secondTerm,
    Real.log_mul hra.ne' hrb.ne', hloga, hlogb]
  field_simp [hxa.ne', hxb.ne']
  <;> ring

private theorem shiftedLog_hasDeriv (c x : ℝ) (h : 0 < x + c) :
    HasDerivAt (fun y : ℝ => Real.log (y + c)) ((x + c)⁻¹) x := by
  have hlog : HasDerivAt Real.log ((x + c)⁻¹) (x + c) :=
    Real.hasDerivAt_log h.ne'
  have hshift : HasDerivAt (fun y : ℝ => y + c) 1 x :=
    (hasDerivAt_id x).add_const c
  simpa [Function.comp_def] using hlog.comp x hshift

private theorem continuousOn_firstTerm (U : Set ℝ) (a b : ℝ)
    (hU : Regular U a b) : ContinuousOn (firstTerm a b) U := by
  intro x hx
  have hla : ContinuousAt (fun y : ℝ => Real.log (y + a)) x :=
    (shiftedLog_hasDeriv a x (hU.2.2 x hx).1).continuousAt
  have hcb : ContinuousAt (fun y : ℝ => y + b) x :=
    continuousAt_id.add continuousAt_const
  have hxb : x + b ≠ 0 := (hU.2.2 x hx).2.ne'
  simpa [firstTerm] using (hla.div hcb hxb).continuousWithinAt

private theorem stronglyMeasurable_firstTerm (a b : ℝ) :
    MeasureTheory.StronglyMeasurable (firstTerm a b) := by
  have hma : Measurable (fun x : ℝ => x + a) :=
    measurable_id.add measurable_const
  have hmb : Measurable (fun x : ℝ => x + b) :=
    measurable_id.add measurable_const
  have hm : Measurable (fun x : ℝ => Real.log (x + a) / (x + b)) :=
    (Real.measurable_log.comp hma).div hmb
  simpa [firstTerm] using hm.stronglyMeasurable

private theorem exists_family_of_continuousOn {U : Set ℝ} {f : ℝ → ℝ}
    (hopen : IsOpen U) (hconn : IsPreconnected U)
    (hf : ContinuousOn f U)
    (hsm : MeasureTheory.StronglyMeasurable f) :
    ∃ A, A ∈ Family U f := by
  by_cases hne : U.Nonempty
  · rcases hne with ⟨c, hc⟩
    refine ⟨fun x => ∫ t in c..x, f t, ?_⟩
    intro x hx
    have hsegment : Set.uIcc c x ⊆ U := by
      rcases le_total c x with hcx | hxc
      · rw [Set.uIcc_of_le hcx]
        exact hconn.ordConnected.out hc hx
      · rw [Set.uIcc_of_ge hxc]
        exact hconn.ordConnected.out hx hc
    have hcontinuous : ContinuousAt f x :=
      hf.continuousAt (hopen.mem_nhds hx)
    have hmeas :
        StronglyMeasurableAtFilter f (nhds x) MeasureTheory.volume :=
      hsm.stronglyMeasurableAtFilter
    exact intervalIntegral.integral_hasDerivAt_right
      ((hf.mono hsegment).intervalIntegrable)
      hmeas
      hcontinuous
  · refine ⟨0, ?_⟩
    intro x hx
    exact False.elim (hne ⟨x, hx⟩)

private theorem hasDerivAt_congr_on_open {U : Set ℝ}
    (hopen : IsOpen U) {F G : ℝ → ℝ} {f x : ℝ}
    (hx : x ∈ U) (hFG : ∀ y ∈ U, F y = G y)
    (hG : HasDerivAt G f x) : HasDerivAt F f x := by
  apply hG.congr_of_eventuallyEq
  filter_upwards [hopen.mem_nhds hx] with y hy
  exact hFG y hy

private theorem family_congr_on {U : Set ℝ} {f g : ℝ → ℝ}
    (hfg : ∀ x ∈ U, f x = g x) : Family U f = Family U g := by
  ext F
  simp only [Family, Set.mem_setOf_eq]
  constructor
  · intro hF x hx
    simpa [hfg x hx] using hF x hx
  · intro hF x hx
    simpa [hfg x hx] using hF x hx

private theorem firstTerm_eq_firstDifferentialTerm (a b x : ℝ)
    (hxb : 0 < x + b) :
    firstTerm a b x = firstDifferentialTerm a b x := by
  have hd := shiftedLog_hasDeriv b x hxb
  simp [firstTerm, firstDifferentialTerm, hd.deriv, div_eq_mul_inv]

private theorem secondTerm_eq_secondDifferentialTerm (a b x : ℝ)
    (hxa : 0 < x + a) :
    secondTerm a b x = secondDifferentialTerm a b x := by
  have hd := shiftedLog_hasDeriv a x hxa
  simp [secondTerm, secondDifferentialTerm, hd.deriv, div_eq_mul_inv]

private theorem product_hasDeriv_terms (a b x : ℝ)
    (hxa : 0 < x + a) (hxb : 0 < x + b) :
    HasDerivAt (productPrimitive a b)
      (firstDifferentialTerm a b x + secondDifferentialTerm a b x) x := by
  have hda := shiftedLog_hasDeriv a x hxa
  have hdb := shiftedLog_hasDeriv b x hxb
  have hp := hda.mul hdb
  convert hp using 1 <;>
    simp [productPrimitive, firstDifferentialTerm, secondDifferentialTerm,
      hda.deriv, hdb.deriv] <;> ring

private theorem product_hasDeriv_source (a b x : ℝ)
    (hxa : 0 < x + a) (hxb : 0 < x + b) :
    HasDerivAt (productPrimitive a b) (sourceIntegrand a b x) x := by
  have hp := product_hasDeriv_terms a b x hxa hxb
  rw [source_eq_terms a b x hxa hxb]
  rw [firstTerm_eq_firstDifferentialTerm a b x hxb,
    secondTerm_eq_secondDifferentialTerm a b x hxa]
  exact hp

theorem gap1 (U : Set ℝ) (a b : ℝ) (hU : Regular U a b) :
    Family U (sourceIntegrand a b) =
      SumFamily U (firstTerm a b) (secondTerm a b) := by
  ext F
  simp only [Family, SumFamily, Set.mem_setOf_eq]
  constructor
  · intro hF
    obtain ⟨A, hA⟩ :=
      exists_family_of_continuousOn (U := U) (f := firstTerm a b)
        hU.1 hU.2.1
        (continuousOn_firstTerm U a b hU)
        (stronglyMeasurable_firstTerm a b)
    refine ⟨A, hA, fun y => F y - A y, ?_, ?_⟩
    · intro x hx
      have hd := (hF x hx).sub (hA x hx)
      have heq := source_eq_terms a b x
        (hU.2.2 x hx).1 (hU.2.2 x hx).2
      convert hd using 1 <;> simp [heq]
    · intro x hx
      ring
  · rintro ⟨A, hA, B, hB, hF⟩ x hx
    have hd := (hA x hx).add (hB x hx)
    have heq := source_eq_terms a b x
      (hU.2.2 x hx).1 (hU.2.2 x hx).2
    rw [heq]
    exact hasDerivAt_congr_on_open hU.1 hx hF hd

theorem gap2 (U : Set ℝ) (a b : ℝ) (hU : Regular U a b) :
    Family U (sourceIntegrand a b) =
      SumFamily U (firstDifferentialTerm a b) (secondDifferentialTerm a b) := by
  have hfirst :
      Family U (firstTerm a b) = Family U (firstDifferentialTerm a b) :=
    family_congr_on fun x hx =>
      firstTerm_eq_firstDifferentialTerm a b x (hU.2.2 x hx).2
  have hsecond :
      Family U (secondTerm a b) = Family U (secondDifferentialTerm a b) :=
    family_congr_on fun x hx =>
      secondTerm_eq_secondDifferentialTerm a b x (hU.2.2 x hx).1
  rw [gap1 U a b hU]
  unfold SumFamily
  rw [hfirst, hsecond]

theorem gap3 (U : Set ℝ) (a b : ℝ) (hU : Regular U a b) :
    Family U (secondDifferentialTerm a b) = ByPartsFamily U a b := by
  ext F
  simp only [Family, ByPartsFamily, Set.mem_setOf_eq]
  constructor
  · intro hF
    refine ⟨fun y => productPrimitive a b y - F y, ?_, 0, ?_⟩
    · intro x hx
      have hp := product_hasDeriv_terms a b x
        (hU.2.2 x hx).1 (hU.2.2 x hx).2
      have hd := hp.sub (hF x hx)
      convert hd using 1 <;> simp <;> ring
    · intro x hx
      ring
  · rintro ⟨A, hA, C, hF⟩ x hx
    have hp := product_hasDeriv_terms a b x
      (hU.2.2 x hx).1 (hU.2.2 x hx).2
    have hd := (hp.sub (hA x hx)).add_const C
    have hd' :
        HasDerivAt (fun y => productPrimitive a b y - A y + C)
          (secondDifferentialTerm a b x) x := by
      convert hd using 1 <;> ring
    exact hasDerivAt_congr_on_open hU.1 hx hF hd'

theorem gap4 (U : Set ℝ) (a b : ℝ) (hU : Regular U a b) :
    Family U (sourceIntegrand a b) =
      Translates U (productPrimitive a b) := by
  ext F
  simp only [Family, Translates, Set.mem_setOf_eq]
  constructor
  · intro hF
    by_cases hne : U.Nonempty
    · rcases hne with ⟨c, hc⟩
      refine ⟨F c - productPrimitive a b c, ?_⟩
      intro x hx
      have hdiff :
          DifferentiableOn ℝ (fun y => F y - productPrimitive a b y) U := by
        intro y hy
        exact ((hF y hy).differentiableAt.sub
          (product_hasDeriv_source a b y
            (hU.2.2 y hy).1 (hU.2.2 y hy).2).differentiableAt).differentiableWithinAt
      have hzero :
          ∀ y ∈ U, deriv (fun z => F z - productPrimitive a b z) y = 0 := by
        intro y hy
        have hd := (hF y hy).sub
          (product_hasDeriv_source a b y
            (hU.2.2 y hy).1 (hU.2.2 y hy).2)
        simpa using hd.deriv
      have hconst :
          F x - productPrimitive a b x =
            F c - productPrimitive a b c :=
        hU.1.is_const_of_deriv_eq_zero hU.2.1 hdiff hzero hx hc
      calc
        F x = productPrimitive a b x +
            (F x - productPrimitive a b x) := by ring
        _ = productPrimitive a b x +
            (F c - productPrimitive a b c) := by rw [hconst]
    · refine ⟨0, ?_⟩
      intro x hx
      exact False.elim (hne ⟨x, hx⟩)
  · rintro ⟨C, hF⟩ x hx
    have hp := product_hasDeriv_source a b x
      (hU.2.2 x hx).1 (hU.2.2 x hx).2
    exact hasDerivAt_congr_on_open hU.1 hx hF (hp.add_const C)

end
end ProofGap.Exercise2101
