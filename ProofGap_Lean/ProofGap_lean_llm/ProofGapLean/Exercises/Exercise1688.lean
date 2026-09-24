import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Topology.Neighborhoods
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise1688

noncomputable section

def integrand (x : ℝ) : ℝ := 1 / Real.sqrt (x * (1 - x))
def primitive (x : ℝ) : ℝ := 2 * Real.arcsin (Real.sqrt x)
def domain : Set ℝ := Set.Ioo 0 1

def IsAntiderivativeOn (F f : ℝ → ℝ) (s : Set ℝ) : Prop :=
  ∀ x ∈ s, HasDerivAt F (f x) x
def Family (f : ℝ → ℝ) (s : Set ℝ) : Set (ℝ → ℝ) :=
  {F | IsAntiderivativeOn F f s}
def Translates (P : ℝ → ℝ) (s : Set ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C, ∀ x ∈ s, F x = P x + C}

theorem gap1 (x : ℝ) (hx : 0 < x * (1 - x)) :
    x ∈ domain := by
  change 0 < x ∧ x < 1
  constructor <;> nlinarith

theorem gap2 (x : ℝ) (hx : x ∈ domain) :
    integrand x =
      2 * deriv Real.sqrt x / Real.sqrt (1 - (Real.sqrt x) ^ 2) := by
  rcases hx with ⟨hx0, hx1⟩
  unfold integrand
  have hxne : x ≠ 0 := ne_of_gt hx0
  have hsqrt : Real.sqrt x ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hx0)
  have hone : 0 < 1 - x := sub_pos.2 hx1
  have hsqrt_one : Real.sqrt (1 - x) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hone)
  have hsq : (Real.sqrt x) ^ 2 = x :=
    Real.sq_sqrt (le_of_lt hx0)
  have hderiv : deriv Real.sqrt x = 1 / (2 * Real.sqrt x) :=
    (Real.hasDerivAt_sqrt hxne).deriv
  have hprod : Real.sqrt (x * (1 - x)) =
      Real.sqrt x * Real.sqrt (1 - x) := by
    rw [Real.sqrt_mul (le_of_lt hx0)]
  rw [hderiv, hsq, hprod]
  field_simp

theorem gap3 (x : ℝ) (hx : x ∈ domain) :
    HasDerivAt primitive (integrand x) x := by
  rcases hx with ⟨hx0, hx1⟩
  have hsq : (Real.sqrt x) ^ 2 = x :=
    Real.sq_sqrt (le_of_lt hx0)
  have hsqrt0 : 0 < Real.sqrt x := Real.sqrt_pos.2 hx0
  have hsqrt_nonneg : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
  have hsqrt1 : Real.sqrt x < 1 := by
    nlinarith
  have hsqrt_deriv : HasDerivAt Real.sqrt
      (1 / (2 * Real.sqrt x)) x := by
    simpa using Real.hasDerivAt_sqrt (ne_of_gt hx0)
  have harcsin_deriv : HasDerivAt Real.arcsin
      (1 / Real.sqrt (1 - (Real.sqrt x) ^ 2)) (Real.sqrt x) := by
    simpa using Real.hasDerivAt_arcsin
      (ne_of_gt (show (-1 : ℝ) < Real.sqrt x by linarith))
      (ne_of_lt hsqrt1)
  have hcomp := harcsin_deriv.comp x hsqrt_deriv
  have hcoef :
      2 * ((1 / Real.sqrt (1 - (Real.sqrt x) ^ 2)) *
        (1 / (2 * Real.sqrt x))) = integrand x := by
    rw [gap2 x ⟨hx0, hx1⟩,
      (Real.hasDerivAt_sqrt (ne_of_gt hx0)).deriv]
    ring
  have hscaled := hcomp.const_mul 2
  rw [hcoef] at hscaled
  simpa [primitive, Function.comp_def] using hscaled

theorem gap4 :
    Family integrand domain = Translates primitive domain := by
  apply Set.ext
  intro F
  constructor
  · intro hF
    change IsAntiderivativeOn F integrand domain at hF
    change ∃ C, ∀ x ∈ domain, F x = primitive x + C
    refine ⟨F (1 / 2) - primitive (1 / 2), ?_⟩
    intro x hx
    have hxI : x ∈ Set.Ioo (0 : ℝ) 1 := by
      simpa [domain] using hx
    have hhalfI : (1 / 2 : ℝ) ∈ Set.Ioo (0 : ℝ) 1 := by
      norm_num
    have hdiff : DifferentiableOn ℝ (fun z => F z - primitive z)
        (Set.Ioo (0 : ℝ) 1) := by
      intro y hy
      have hyDom : y ∈ domain := by
        simpa [domain] using hy
      exact ((hF y hyDom).sub (gap3 y hyDom)).differentiableAt.differentiableWithinAt
    have hzero : ∀ y ∈ Set.Ioo (0 : ℝ) 1,
        deriv (fun z => F z - primitive z) y = 0 := by
      intro y hy
      have hyDom : y ∈ domain := by
        simpa [domain] using hy
      simpa using ((hF y hyDom).sub (gap3 y hyDom)).deriv
    have heq : F x - primitive x =
        F (1 / 2) - primitive (1 / 2) := by
      exact isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo
        hdiff hzero hxI hhalfI
    linarith
  · rintro ⟨C, hC⟩
    change IsAntiderivativeOn F integrand domain
    intro x hx
    have hopen : IsOpen domain := by
      simpa [domain] using
        (isOpen_Ioo : IsOpen (Set.Ioo (0 : ℝ) 1))
    have hmem : ∀ᶠ y in nhds x, y ∈ domain := hopen.mem_nhds hx
    have hlocal : ∀ᶠ y in nhds x, F y = primitive y + C :=
      hmem.mono (fun y hy => hC y hy)
    have hprimitive : HasDerivAt (fun y => primitive y + C)
        (integrand x) x := by
      simpa [add_comm] using (gap3 x hx).const_add C
    exact hprimitive.congr_of_eventuallyEq hlocal

end

end ProofGap.Exercise1688
