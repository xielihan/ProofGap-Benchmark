import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Topology.Neighborhoods
import Mathlib.Topology.Order.OrderClosed

namespace ProofGap.Exercise1838

noncomputable section

def branch : Set ℝ := Set.Ioo (-1 / 3 : ℝ) 1
def integrand (x : ℝ) := 1 / (3 * x ^ 2 - 2 * x - 1)
def monicIntegrand (x : ℝ) := 1 / (x ^ 2 - (2 / 3) * x - 1 / 3)
def shiftedIntegrand (x : ℝ) :=
  1 / ((x - 1 / 3) ^ 2 - (2 / 3) ^ 2) *
    deriv (fun t : ℝ => t - 1 / 3) x
def primitiveRaw (x : ℝ) :=
  -(1 / 3 : ℝ) * (3 / 4 : ℝ) *
    Real.log |((2 / 3 : ℝ) + x - 1 / 3) /
      ((2 / 3 : ℝ) - (x - 1 / 3))|
def primitive (x : ℝ) :=
  (1 / 4 : ℝ) * Real.log |(x - 1) / (3 * x + 1)|
def AntiderivativesOn (f : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∀ x ∈ branch, HasDerivAt F (f x) x}
def ThirdFamily (f : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ G ∈ AntiderivativesOn f,
    ∀ x ∈ branch, F x = (1 / 3 : ℝ) * G x}
def PrimitiveFamily (p : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x ∈ branch, F x = p x + C}

private theorem integrand_eq_third (x : ℝ) :
    integrand x = (1 / 3 : ℝ) * monicIntegrand x := by
  unfold integrand monicIntegrand
  rw [show 3 * x ^ 2 - 2 * x - 1 =
      3 * (x ^ 2 - (2 / 3 : ℝ) * x - 1 / 3) by ring]
  simp only [one_div, mul_inv_rev]
  norm_num
  ring

private theorem shifted_eq_monic (x : ℝ) :
    shiftedIntegrand x = monicIntegrand x := by
  unfold shiftedIntegrand monicIntegrand
  rw [show deriv (fun t : ℝ => t - 1 / 3) x = 1 by
    exact ((hasDerivAt_id x).sub_const (1 / 3 : ℝ)).deriv]
  rw [show (x - 1 / 3) ^ 2 - (2 / 3 : ℝ) ^ 2 =
      x ^ 2 - (2 / 3 : ℝ) * x - 1 / 3 by ring]
  simp

private theorem hasDerivAt_of_eqOn_branch
    {F H : ℝ → ℝ} {d x : ℝ} (hx : x ∈ branch)
    (hEq : ∀ y ∈ branch, F y = H y) (hH : HasDerivAt H d x) :
    HasDerivAt F d x := by
  apply hH.congr_of_eventuallyEq
  filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
  exact hEq y hy

private theorem eq_at_zero_of_hasDerivAt_zero (h : ℝ → ℝ)
    (hh : ∀ x ∈ branch, HasDerivAt h 0 x) :
    ∀ x ∈ branch, h x = h 0 := by
  intro x hx
  by_cases hx0 : x = 0
  · simp [hx0]
  rcases lt_or_gt_of_ne hx0 with hneg | hpos
  · have hcont : ContinuousOn h (Set.Icc x 0) := by
      intro y hy
      exact (hh y ⟨by linarith [hx.1, hy.1], by linarith [hy.2]⟩).continuousAt.continuousWithinAt
    have hdiff : DifferentiableOn ℝ h (Set.Ioo x 0) := by
      intro y hy
      exact (hh y ⟨by linarith [hx.1, hy.1], by linarith [hy.2]⟩).differentiableAt.differentiableWithinAt
    obtain ⟨c, hc, hcSlope⟩ := exists_deriv_eq_slope h hneg hcont hdiff
    have hcZero : deriv h c = 0 :=
      (hh c ⟨by linarith [hx.1, hc.1], by linarith [hc.2]⟩).deriv
    have hslope : (h 0 - h x) / (0 - x) = 0 := hcSlope.symm.trans hcZero
    have hnum : h 0 - h x = 0 :=
      (div_eq_zero_iff.mp hslope).resolve_right (by linarith)
    linarith
  · have hcont : ContinuousOn h (Set.Icc 0 x) := by
      intro y hy
      exact (hh y ⟨by linarith [hy.1], by linarith [hx.2, hy.2]⟩).continuousAt.continuousWithinAt
    have hdiff : DifferentiableOn ℝ h (Set.Ioo 0 x) := by
      intro y hy
      exact (hh y ⟨by linarith [hy.1], by linarith [hx.2, hy.2]⟩).differentiableAt.differentiableWithinAt
    obtain ⟨c, hc, hcSlope⟩ := exists_deriv_eq_slope h hpos hcont hdiff
    have hcZero : deriv h c = 0 :=
      (hh c ⟨by linarith [hc.1], by linarith [hx.2, hc.2]⟩).deriv
    have hslope : (h x - h 0) / (x - 0) = 0 := hcSlope.symm.trans hcZero
    have hnum : h x - h 0 = 0 :=
      (div_eq_zero_iff.mp hslope).resolve_right (by linarith)
    linarith

private theorem antiderivatives_eq_primitiveFamily {f p : ℝ → ℝ}
    (hp : ∀ x ∈ branch, HasDerivAt p (f x) x) :
    AntiderivativesOn f = PrimitiveFamily p := by
  ext F
  simp only [AntiderivativesOn, PrimitiveFamily, Set.mem_setOf_eq]
  constructor
  · intro hF
    refine ⟨F 0 - p 0, ?_⟩
    have hz : ∀ y ∈ branch, HasDerivAt (fun z => F z - p z) 0 y := by
      intro y hy
      simpa using (hF y hy).sub (hp y hy)
    intro x hx
    have hc := eq_at_zero_of_hasDerivAt_zero (fun z => F z - p z) hz x hx
    linarith
  · rintro ⟨C, hC⟩
    intro x hx
    have hd : HasDerivAt (fun y => p y + C) (f x) x := (hp x hx).add_const C
    exact hasDerivAt_of_eqOn_branch hx (fun y hy => hC y hy) hd

private theorem primitiveRaw_hasDerivAt (x : ℝ) (hx : x ∈ branch) :
    HasDerivAt primitiveRaw (integrand x) x := by
  have hnpos : 0 < (2 / 3 : ℝ) + x - 1 / 3 := by
    linarith [hx.1]
  have hdpos : 0 < (2 / 3 : ℝ) - (x - 1 / 3) := by
    linarith [hx.2]
  have hnne : (2 / 3 : ℝ) + x - 1 / 3 ≠ 0 := ne_of_gt hnpos
  have hdne : (2 / 3 : ℝ) - (x - 1 / 3) ≠ 0 := ne_of_gt hdpos
  have hn : HasDerivAt (fun t : ℝ => (2 / 3 : ℝ) + t - 1 / 3) 1 x := by
    simpa using (((hasDerivAt_id x).const_add (2 / 3 : ℝ)).sub_const (1 / 3 : ℝ))
  have hd : HasDerivAt (fun t : ℝ => (2 / 3 : ℝ) - (t - 1 / 3)) (-1) x := by
    simpa using ((hasDerivAt_const x (2 / 3 : ℝ)).sub
      ((hasDerivAt_id x).sub_const (1 / 3 : ℝ)))
  have hscaled := ((hn.log hnne).sub (hd.log hdne)).const_mul (-(1 / 4 : ℝ))
  have hevN : ∀ᶠ y in nhds x, 0 < (2 / 3 : ℝ) + y - 1 / 3 :=
    hn.continuousAt.eventually (isOpen_Ioi.mem_nhds hnpos)
  have hevD : ∀ᶠ y in nhds x, 0 < (2 / 3 : ℝ) - (y - 1 / 3) :=
    hd.continuousAt.eventually (isOpen_Ioi.mem_nhds hdpos)
  have hevEq : primitiveRaw =ᶠ[nhds x]
      (fun y : ℝ => (-(1 / 4 : ℝ)) *
        (Real.log ((2 / 3 : ℝ) + y - 1 / 3) -
          Real.log ((2 / 3 : ℝ) - (y - 1 / 3)))) := by
    filter_upwards [hevN, hevD] with y hyN hyD
    unfold primitiveRaw
    rw [abs_of_pos (div_pos hyN hyD)]
    rw [Real.log_div (ne_of_gt hyN) (ne_of_gt hyD)]
    ring
  have hraw : HasDerivAt primitiveRaw
      ((-(1 / 4 : ℝ)) *
        (1 / ((2 / 3 : ℝ) + x - 1 / 3) -
          (-1) / ((2 / 3 : ℝ) - (x - 1 / 3)))) x := by
    exact hscaled.congr_of_eventuallyEq hevEq
  have hAne : 3 * x + 1 ≠ 0 := by
    linarith [hx.1]
  have hxmne : x - 1 ≠ 0 := by
    linarith [hx.2]
  have hBone : 1 - x ≠ 0 := by
    linarith [hx.2]
  have hval :
      (-(1 / 4 : ℝ)) *
          (1 / ((2 / 3 : ℝ) + x - 1 / 3) -
            (-1) / ((2 / 3 : ℝ) - (x - 1 / 3))) =
        integrand x := by
    unfold integrand
    rw [show (2 / 3 : ℝ) + x - 1 / 3 = (3 * x + 1) / 3 by ring]
    rw [show (2 / 3 : ℝ) - (x - 1 / 3) = 1 - x by ring]
    rw [show 3 * x ^ 2 - 2 * x - 1 = (3 * x + 1) * (x - 1) by ring]
    field_simp [hAne, hxmne, hBone]
    <;> ring
  rw [← hval]
  exact hraw

private theorem primitiveRaw_eq_primitive_add (x : ℝ) (hx : x ∈ branch) :
    primitiveRaw x = primitive x + (1 / 4 : ℝ) * Real.log 3 := by
  have hnpos : 0 < x + 1 / 3 := by linarith [hx.1]
  have hdpos : 0 < 1 - x := by linarith [hx.2]
  have h3pos : 0 < 3 * x + 1 := by linarith [hx.1]
  have hnne : x + 1 / 3 ≠ 0 := ne_of_gt hnpos
  have hdne : 1 - x ≠ 0 := ne_of_gt hdpos
  have h3ne : 3 * x + 1 ≠ 0 := ne_of_gt h3pos
  unfold primitiveRaw primitive
  rw [show (2 / 3 : ℝ) + x - 1 / 3 = x + 1 / 3 by ring]
  rw [show (2 / 3 : ℝ) - (x - 1 / 3) = 1 - x by ring]
  rw [abs_of_pos (div_pos hnpos hdpos)]
  rw [abs_of_neg (div_neg_of_neg_of_pos (by linarith [hx.2]) h3pos)]
  rw [show -((x - 1) / (3 * x + 1)) = (1 - x) / (3 * x + 1) by ring]
  rw [Real.log_div hnne hdne, Real.log_div hdne h3ne]
  rw [show 3 * x + 1 = 3 * (x + 1 / 3) by ring]
  rw [Real.log_mul (by norm_num : (3 : ℝ) ≠ 0) hnne]
  ring

theorem gap1 :
    AntiderivativesOn integrand = ThirdFamily monicIntegrand := by
  ext F
  simp only [AntiderivativesOn, ThirdFamily, Set.mem_setOf_eq]
  constructor
  · intro hF
    refine ⟨fun y => 3 * F y, ?_, ?_⟩
    · intro x hx
      have hd := (hF x hx).const_mul (3 : ℝ)
      rw [integrand_eq_third] at hd
      convert hd using 1 <;> ring
    · intro x hx
      ring
  · rintro ⟨G, hG, hFG⟩
    intro x hx
    have hd : HasDerivAt (fun y => (1 / 3 : ℝ) * G y) (integrand x) x := by
      rw [integrand_eq_third]
      exact (hG x hx).const_mul (1 / 3 : ℝ)
    exact hasDerivAt_of_eqOn_branch hx (fun y hy => hFG y hy) hd
theorem gap2 :
    ThirdFamily monicIntegrand = ThirdFamily shiftedIntegrand := by
  have h : monicIntegrand = shiftedIntegrand := by
    funext x
    exact (shifted_eq_monic x).symm
  rw [h]
theorem gap3 :
    AntiderivativesOn integrand = ThirdFamily shiftedIntegrand := by
  exact gap1.trans gap2
theorem gap4 :
    AntiderivativesOn integrand = PrimitiveFamily primitiveRaw := by
  apply antiderivatives_eq_primitiveFamily
  intro x hx
  exact primitiveRaw_hasDerivAt x hx
theorem gap5 :
    PrimitiveFamily primitiveRaw = PrimitiveFamily primitive := by
  ext F
  simp only [PrimitiveFamily, Set.mem_setOf_eq]
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨(1 / 4 : ℝ) * Real.log 3 + C, ?_⟩
    intro x hx
    rw [hC x hx, primitiveRaw_eq_primitive_add x hx]
    ring
  · rintro ⟨C, hC⟩
    refine ⟨C - (1 / 4 : ℝ) * Real.log 3, ?_⟩
    intro x hx
    rw [hC x hx, primitiveRaw_eq_primitive_add x hx]
    ring
theorem gap6 :
    AntiderivativesOn integrand = PrimitiveFamily primitive := by
  exact gap4.trans gap5

end
end ProofGap.Exercise1838
