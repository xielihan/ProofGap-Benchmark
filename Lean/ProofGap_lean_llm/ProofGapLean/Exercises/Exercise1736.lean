import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Neighborhoods
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise1736

noncomputable section

def domain : Set ℝ := Set.Ioi (Real.sqrt 2)
def original (x : ℝ) : ℝ := 1 / ((x ^ 2 - 2) * (x ^ 2 + 3))
def partialFractions (x : ℝ) : ℝ :=
  (1 / 5) * (1 / (x ^ 2 - 2) - 1 / (x ^ 2 + 3))
def primitive (x : ℝ) : ℝ :=
  (1 / (10 * Real.sqrt 2)) *
      Real.log |(x - Real.sqrt 2) / (x + Real.sqrt 2)| -
    (1 / (5 * Real.sqrt 3)) * Real.arctan (x / Real.sqrt 3)
def AntiderivativesOn (g : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | DifferentiableOn ℝ F domain ∧ ∀ x ∈ domain, deriv F x = g x}
def PrimitiveFamily (p : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x ∈ domain, F x = p x + C}

private theorem primitive_hasDerivAt {x : ℝ} (hx : x ∈ domain) :
    HasDerivAt primitive (partialFractions x) x := by
  change Real.sqrt 2 < x at hx
  have hs2pos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hs3pos : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  have hs2ne : Real.sqrt 2 ≠ 0 := ne_of_gt hs2pos
  have hs3ne : Real.sqrt 3 ≠ 0 := ne_of_gt hs3pos
  have hs2sq : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs3sq : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hxmpos : 0 < x - Real.sqrt 2 := sub_pos.mpr hx
  have hxppos : 0 < x + Real.sqrt 2 := by nlinarith
  have hxmne : x - Real.sqrt 2 ≠ 0 := ne_of_gt hxmpos
  have hxpne : x + Real.sqrt 2 ≠ 0 := ne_of_gt hxppos
  have hqpos : 0 < (x - Real.sqrt 2) / (x + Real.sqrt 2) :=
    div_pos hxmpos hxppos
  have hqne : (x - Real.sqrt 2) / (x + Real.sqrt 2) ≠ 0 := ne_of_gt hqpos
  have hx2 : 2 < x ^ 2 := by nlinarith
  have hpoly2ne : x ^ 2 - 2 ≠ 0 := ne_of_gt (sub_pos.mpr hx2)
  have hpoly3ne : x ^ 2 + 3 ≠ 0 := by nlinarith [sq_nonneg x]
  have hquot0 :=
    ((hasDerivAt_id x).sub_const (Real.sqrt 2)).div
      ((hasDerivAt_id x).add_const (Real.sqrt 2)) hxpne
  simp only [id_eq] at hquot0
  have hquot :
      HasDerivAt
        (fun y => (y - Real.sqrt 2) / (y + Real.sqrt 2))
        (2 * Real.sqrt 2 / (x + Real.sqrt 2) ^ 2) x := by
    convert hquot0 using 1 <;> ring
  have habs :
      HasDerivAt
        (fun y => |(y - Real.sqrt 2) / (y + Real.sqrt 2)|)
        (2 * Real.sqrt 2 / (x + Real.sqrt 2) ^ 2) x := by
    simpa [Function.comp_def, hqpos] using
      ((hasDerivAt_abs hqne).comp x hquot)
  have hlog0 :
      HasDerivAt
        (fun y => Real.log |(y - Real.sqrt 2) / (y + Real.sqrt 2)|)
        (|(x - Real.sqrt 2) / (x + Real.sqrt 2)|⁻¹ *
          (2 * Real.sqrt 2 / (x + Real.sqrt 2) ^ 2)) x := by
    simpa [Function.comp_def] using
      ((Real.hasDerivAt_log (abs_ne_zero.mpr hqne)).comp x habs)
  have hlog :
      HasDerivAt
        (fun y => Real.log |(y - Real.sqrt 2) / (y + Real.sqrt 2)|)
        (2 * Real.sqrt 2 / (x ^ 2 - 2)) x := by
    convert hlog0 using 1
    rw [abs_of_pos hqpos]
    field_simp [hxmne, hxpne, hpoly2ne]
    nlinarith [hs2sq]
  have harg := (hasDerivAt_id x).div_const (Real.sqrt 3)
  have hatan0 := (Real.hasDerivAt_arctan (x / Real.sqrt 3)).comp x harg
  have hatan :
      HasDerivAt (fun y => Real.arctan (y / Real.sqrt 3))
        (Real.sqrt 3 / (x ^ 2 + 3)) x := by
    convert hatan0 using 1
    field_simp [hs3ne, hpoly3ne] <;> nlinarith [hs3sq]
  have hcombined :=
    (hlog.const_mul (1 / (10 * Real.sqrt 2))).sub
      (hatan.const_mul (1 / (5 * Real.sqrt 3)))
  unfold primitive
  convert hcombined using 1
  unfold partialFractions
  field_simp [hs2ne, hs3ne, hpoly2ne, hpoly3ne] <;>
    nlinarith [hs2sq, hs3sq]

theorem gap1 : AntiderivativesOn original = AntiderivativesOn partialFractions := by
  apply Set.ext
  intro F
  simp only [AntiderivativesOn, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hF, hderiv⟩
    refine ⟨hF, ?_⟩
    intro x hx
    rw [hderiv x hx]
    unfold original partialFractions
    have hsqrt : Real.sqrt 2 < x := hx
    have hsqrt_nonneg : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
    have hsqrt_sq : (Real.sqrt 2) ^ 2 = 2 := by norm_num
    have hx2 : 2 < x ^ 2 := by nlinarith
    have hne1 : x ^ 2 - 2 ≠ 0 := ne_of_gt (sub_pos.mpr hx2)
    have hne2 : x ^ 2 + 3 ≠ 0 := by nlinarith
    field_simp
    ring
  · rintro ⟨hF, hderiv⟩
    refine ⟨hF, ?_⟩
    intro x hx
    rw [hderiv x hx]
    unfold original partialFractions
    have hsqrt : Real.sqrt 2 < x := hx
    have hsqrt_nonneg : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
    have hsqrt_sq : (Real.sqrt 2) ^ 2 = 2 := by norm_num
    have hx2 : 2 < x ^ 2 := by nlinarith
    have hne1 : x ^ 2 - 2 ≠ 0 := ne_of_gt (sub_pos.mpr hx2)
    have hne2 : x ^ 2 + 3 ≠ 0 := by nlinarith
    field_simp
    ring

theorem gap2 : AntiderivativesOn partialFractions = PrimitiveFamily primitive := by
  apply Set.ext
  intro F
  simp only [AntiderivativesOn, PrimitiveFamily, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hF, hderiv⟩
    have hpDiff : DifferentiableOn ℝ primitive domain := by
      intro x hx
      exact (primitive_hasDerivAt hx).differentiableAt.differentiableWithinAt
    have hdiff : DifferentiableOn ℝ (fun y => F y - primitive y) domain :=
      hF.sub hpDiff
    have hzero : ∀ x ∈ domain, deriv (fun y => F y - primitive y) x = 0 := by
      intro x hx
      have hFat : DifferentiableAt ℝ F x :=
        (hF x hx).differentiableAt (isOpen_Ioi.mem_nhds hx)
      have hpat : DifferentiableAt ℝ primitive x :=
        (primitive_hasDerivAt hx).differentiableAt
      change deriv (F - primitive) x = 0
      rw [deriv_sub hFat hpat, hderiv x hx, (primitive_hasDerivAt hx).deriv]
      ring
    let x₀ : ℝ := Real.sqrt 2 + 1
    have hx₀ : x₀ ∈ domain := by
      dsimp [x₀, domain]
      norm_num
    refine ⟨F x₀ - primitive x₀, ?_⟩
    intro x hx
    have hc : F x - primitive x = F x₀ - primitive x₀ :=
      isOpen_Ioi.is_const_of_deriv_eq_zero isPreconnected_Ioi hdiff hzero hx hx₀
    linarith
  · rintro ⟨C, hEq⟩
    have hpcDiff : DifferentiableOn ℝ (fun y => primitive y + C) domain := by
      intro x hx
      exact ((primitive_hasDerivAt hx).add_const C).differentiableAt.differentiableWithinAt
    have hFDiff : DifferentiableOn ℝ F domain :=
      hpcDiff.congr (fun x hx => hEq x hx)
    refine ⟨hFDiff, ?_⟩
    intro x hx
    have hevent : F =ᶠ[nhds x] (fun y => primitive y + C) :=
      Filter.mem_of_superset (isOpen_Ioi.mem_nhds hx) (fun y hy => hEq y hy)
    calc
      deriv F x = deriv (fun y => primitive y + C) x := hevent.deriv_eq
      _ = partialFractions x := ((primitive_hasDerivAt hx).add_const C).deriv

theorem gap3 : AntiderivativesOn original = PrimitiveFamily primitive := by
  exact gap1.trans gap2

end
end ProofGap.Exercise1736
