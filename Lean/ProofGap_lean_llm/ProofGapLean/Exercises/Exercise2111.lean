import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Defs.Filter
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise2111
noncomputable section

def domain : Set ℝ := Set.Ioo (-1) 1
def integrand (x : ℝ) :=
  Real.arccos x / (Real.sqrt (1 - x ^ 2)) ^ 3
def differentialForm (x : ℝ) :=
  Real.arccos x * deriv (fun y : ℝ => y / Real.sqrt (1 - y ^ 2)) x
def residual (x : ℝ) := x / (1 - x ^ 2)
def primitive (x : ℝ) :=
  x * Real.arccos x / Real.sqrt (1 - x ^ 2) -
    Real.log (Real.sqrt (1 - x ^ 2))

def Family (f : ℝ → ℝ) :=
  {F : ℝ → ℝ | ∀ x ∈ domain, HasDerivAt F (f x) x}
def ByPartsFamily :=
  {F : ℝ → ℝ | ∃ A ∈ Family residual, ∀ x ∈ domain,
    F x = x * Real.arccos x / Real.sqrt (1 - x ^ 2) + A x}
def Translates (p : ℝ → ℝ) :=
  {F : ℝ → ℝ | ∃ C : ℝ, ∀ x ∈ domain, F x = p x + C}

private theorem one_sub_sq_pos {x : ℝ} (hx : x ∈ domain) : 0 < 1 - x ^ 2 := by
  have hxi : x ∈ Set.Ioo (-1 : ℝ) 1 := by
    simpa [domain] using hx
  have hleft : 0 < 1 + x := by linarith [hxi.1]
  have hright : 0 < 1 - x := sub_pos.mpr hxi.2
  nlinarith [mul_pos hleft hright]

private theorem hasDerivAt_sqrtOneSubSq {x : ℝ} (hx : x ∈ domain) :
    HasDerivAt (fun y : ℝ => Real.sqrt (1 - y ^ 2))
      (-x / Real.sqrt (1 - x ^ 2)) x := by
  have hp : 0 < 1 - x ^ 2 := one_sub_sq_pos hx
  have hspos : 0 < Real.sqrt (1 - x ^ 2) := Real.sqrt_pos.2 hp
  have hi : HasDerivAt (fun y : ℝ => 1 - y ^ 2) (-2 * x) x := by
    convert (hasDerivAt_const x (1 : ℝ)).sub ((hasDerivAt_id x).pow 2) using 1 <;>
      simp only [id_eq] <;> ring
  have hs := (Real.hasDerivAt_sqrt (ne_of_gt hp)).comp x hi
  have hder :
      1 / (2 * Real.sqrt (1 - x ^ 2)) * (-2 * x) =
        -x / Real.sqrt (1 - x ^ 2) := by
    field_simp [ne_of_gt hspos] <;> ring
  simpa only [Function.comp_apply, hder] using hs

private theorem hasDerivAt_quotient {x : ℝ} (hx : x ∈ domain) :
    HasDerivAt (fun y : ℝ => y / Real.sqrt (1 - y ^ 2))
      (1 / (Real.sqrt (1 - x ^ 2)) ^ 3) x := by
  have hp : 0 < 1 - x ^ 2 := one_sub_sq_pos hx
  have hspos : 0 < Real.sqrt (1 - x ^ 2) := Real.sqrt_pos.2 hp
  have hsq : (Real.sqrt (1 - x ^ 2)) ^ 2 = 1 - x ^ 2 :=
    Real.sq_sqrt (le_of_lt hp)
  have hs := hasDerivAt_sqrtOneSubSq hx
  have hraw := (hasDerivAt_id x).div hs (ne_of_gt hspos)
  have hder :
      (1 * Real.sqrt (1 - x ^ 2) -
          x * (-x / Real.sqrt (1 - x ^ 2))) /
          (Real.sqrt (1 - x ^ 2)) ^ 2 =
        1 / (Real.sqrt (1 - x ^ 2)) ^ 3 := by
    field_simp [ne_of_gt hspos] <;> nlinarith [hsq]
  simpa only [id_eq, hder] using hraw

private theorem integrand_eq_differentialForm {x : ℝ} (hx : x ∈ domain) :
    integrand x = differentialForm x := by
  have hg := hasDerivAt_quotient hx
  simp only [integrand, differentialForm]
  rw [hg.deriv]
  simp only [div_eq_mul_inv, one_mul]

private theorem hasDerivAt_boundaryTerm {x : ℝ} (hx : x ∈ domain) :
    HasDerivAt
      (fun y : ℝ => y * Real.arccos y / Real.sqrt (1 - y ^ 2))
      (differentialForm x - residual x) x := by
  have hp : 0 < 1 - x ^ 2 := one_sub_sq_pos hx
  have hspos : 0 < Real.sqrt (1 - x ^ 2) := Real.sqrt_pos.2 hp
  have hsq : (Real.sqrt (1 - x ^ 2)) ^ 2 = 1 - x ^ 2 :=
    Real.sq_sqrt (le_of_lt hp)
  have hres :
      residual x = x / (Real.sqrt (1 - x ^ 2)) ^ 2 := by
    unfold residual
    rw [hsq]
  have hxi : x ∈ Set.Ioo (-1 : ℝ) 1 := by
    simpa [domain] using hx
  have hg := hasDerivAt_quotient hx
  have ha := Real.hasDerivAt_arccos (ne_of_gt hxi.1) (ne_of_lt hxi.2)
  convert hg.mul ha using 1
  · funext y
    change y * Real.arccos y / Real.sqrt (1 - y ^ 2) =
      (y / Real.sqrt (1 - y ^ 2)) * Real.arccos y
    ring
  · simp only [differentialForm, hg.deriv, hres]
    field_simp [ne_of_gt hspos] <;> ring

private theorem hasDerivAt_logPrimitive {x : ℝ} (hx : x ∈ domain) :
    HasDerivAt (fun y : ℝ => -Real.log (Real.sqrt (1 - y ^ 2)))
      (residual x) x := by
  have hp : 0 < 1 - x ^ 2 := one_sub_sq_pos hx
  have hspos : 0 < Real.sqrt (1 - x ^ 2) := Real.sqrt_pos.2 hp
  have hsq : (Real.sqrt (1 - x ^ 2)) ^ 2 = 1 - x ^ 2 :=
    Real.sq_sqrt (le_of_lt hp)
  have hres :
      residual x = x / (Real.sqrt (1 - x ^ 2)) ^ 2 := by
    unfold residual
    rw [hsq]
  have hs := hasDerivAt_sqrtOneSubSq hx
  have hraw := ((Real.hasDerivAt_log (ne_of_gt hspos)).comp x hs).neg
  have hder :
      -((Real.sqrt (1 - x ^ 2))⁻¹ *
          (-x / Real.sqrt (1 - x ^ 2))) = residual x := by
    rw [hres]
    field_simp [ne_of_gt hspos] <;> ring
  simpa only [Function.comp_apply, hder] using hraw

private theorem constant_on_domain_of_hasDerivAt_zero
    (f : ℝ → ℝ) (hf : ∀ x ∈ domain, HasDerivAt f 0 x)
    {x : ℝ} (hx : x ∈ domain) : f x = f 0 := by
  have hdiff : DifferentiableOn ℝ f (Set.Ioo (-1 : ℝ) 1) := by
    intro y hy
    exact (hf y (by simpa [domain] using hy)).differentiableAt.differentiableWithinAt
  have hzero : ∀ y ∈ Set.Ioo (-1 : ℝ) 1, deriv f y = 0 := by
    intro y hy
    exact (hf y (by simpa [domain] using hy)).deriv
  have hx' : x ∈ Set.Ioo (-1 : ℝ) 1 := by
    simpa [domain] using hx
  have h0 : (0 : ℝ) ∈ Set.Ioo (-1 : ℝ) 1 := by norm_num
  exact isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo hdiff hzero hx' h0

theorem gap1 : Family integrand = Family differentialForm := by
  ext F
  simp only [Family, Set.mem_setOf_eq]
  constructor
  · intro h x hx
    rw [← integrand_eq_differentialForm hx]
    exact h x hx
  · intro h x hx
    rw [integrand_eq_differentialForm hx]
    exact h x hx
theorem gap2 : Family differentialForm = ByPartsFamily := by
  ext F
  simp only [Family, ByPartsFamily, Set.mem_setOf_eq]
  constructor
  · intro hF
    refine ⟨fun y => F y - y * Real.arccos y / Real.sqrt (1 - y ^ 2), ?_, ?_⟩
    · intro x hx
      convert (hF x hx).sub (hasDerivAt_boundaryTerm hx) using 1 <;> ring
    · intro x hx
      ring
  · rintro ⟨A, hA, hFA⟩
    intro x hx
    have hd : HasDerivAt
        (fun y => y * Real.arccos y / Real.sqrt (1 - y ^ 2) + A y)
        (differentialForm x) x := by
      convert (hasDerivAt_boundaryTerm hx).add (hA x hx) using 1 <;> ring
    have hxi : x ∈ Set.Ioo (-1 : ℝ) 1 := by
      simpa [domain] using hx
    have hev :
        (fun y => y * Real.arccos y / Real.sqrt (1 - y ^ 2) + A y) =ᶠ[nhds x] F := by
      filter_upwards [Ioo_mem_nhds hxi.1 hxi.2] with y hy
      exact (hFA y (by simpa [domain] using hy)).symm
    exact hd.congr_of_eventuallyEq hev.symm
theorem gap3 : ByPartsFamily = Translates primitive := by
  ext F
  simp only [ByPartsFamily, Translates, Family, Set.mem_setOf_eq]
  constructor
  · rintro ⟨A, hA, hFA⟩
    have hzero : ∀ x ∈ domain,
        HasDerivAt
          (fun y => A y - (-Real.log (Real.sqrt (1 - y ^ 2)))) 0 x := by
      intro x hx
      convert (hA x hx).sub (hasDerivAt_logPrimitive hx) using 1 <;> ring
    refine ⟨A 0 - (-Real.log (Real.sqrt (1 - (0 : ℝ) ^ 2))), ?_⟩
    intro x hx
    have hc := constant_on_domain_of_hasDerivAt_zero
      (fun y => A y - (-Real.log (Real.sqrt (1 - y ^ 2)))) hzero hx
    have hc' :
        A x - (-Real.log (Real.sqrt (1 - x ^ 2))) =
          A 0 - (-Real.log (Real.sqrt (1 - (0 : ℝ) ^ 2))) := by
      simpa only using hc
    have hAx :
        A x = -Real.log (Real.sqrt (1 - x ^ 2)) +
          (A 0 - (-Real.log (Real.sqrt (1 - (0 : ℝ) ^ 2)))) := by
      calc
        A x = (A x - (-Real.log (Real.sqrt (1 - x ^ 2)))) +
            (-Real.log (Real.sqrt (1 - x ^ 2))) := by ring
        _ = (A 0 - (-Real.log (Real.sqrt (1 - (0 : ℝ) ^ 2)))) +
            (-Real.log (Real.sqrt (1 - x ^ 2))) := by
              exact congrArg
                (fun z : ℝ => z + (-Real.log (Real.sqrt (1 - x ^ 2)))) hc'
        _ = -Real.log (Real.sqrt (1 - x ^ 2)) +
            (A 0 - (-Real.log (Real.sqrt (1 - (0 : ℝ) ^ 2)))) := by ring
    rw [hFA x hx, hAx]
    simp only [primitive]
    ring
  · rintro ⟨C, hF⟩
    refine ⟨fun y => -Real.log (Real.sqrt (1 - y ^ 2)) + C, ?_, ?_⟩
    · intro x hx
      simpa using (hasDerivAt_logPrimitive hx).add_const C
    · intro x hx
      rw [hF x hx]
      simp only [primitive]
      ring
theorem gap4 : Family integrand = Translates primitive := by
  calc
    Family integrand = Family differentialForm := gap1
    _ = ByPartsFamily := gap2
    _ = Translates primitive := gap3

end
end ProofGap.Exercise2111
