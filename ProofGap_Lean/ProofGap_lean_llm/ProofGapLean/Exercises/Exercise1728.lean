import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Topology.Neighborhoods
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise1728

noncomputable section

def domain : Set ℝ := Set.Ioi (-1)
def original (x : ℝ) : ℝ := x ^ 5 / (x + 1)
def expanded (x : ℝ) : ℝ :=
  x ^ 4 - x ^ 3 + x ^ 2 - x + 1 - 1 / (x + 1)
def primitive (x : ℝ) : ℝ :=
  (1 / 5) * x ^ 5 - (1 / 4) * x ^ 4 + (1 / 3) * x ^ 3 -
    (1 / 2) * x ^ 2 + x - Real.log |1 + x|
def AntiderivativesOn (g : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | DifferentiableOn ℝ F domain ∧ ∀ x ∈ domain, deriv F x = g x}
def PrimitiveFamily (p : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x ∈ domain, F x = p x + C}

private theorem primitive_hasDerivAt {x : ℝ} (hx : x ∈ domain) :
    HasDerivAt primitive (expanded x) x := by
  have hxpos : 0 < 1 + x := by
    simp only [domain, Set.mem_Ioi] at hx
    linarith
  have hxne : 1 + x ≠ 0 := ne_of_gt hxpos
  have hlog :
      HasDerivAt (fun y : ℝ => Real.log (1 + y)) (1 / (1 + x)) x := by
    convert
      (Real.hasDerivAt_log hxne).comp x
        ((hasDerivAt_const x (1 : ℝ)).add (hasDerivAt_id x)) using 1 <;>
      ring
  have h5 := ((hasDerivAt_id x).pow 5).const_mul (1 / 5 : ℝ)
  have h4 := ((hasDerivAt_id x).pow 4).const_mul (1 / 4 : ℝ)
  have h3 := ((hasDerivAt_id x).pow 3).const_mul (1 / 3 : ℝ)
  have h2 := ((hasDerivAt_id x).pow 2).const_mul (1 / 2 : ℝ)
  have hcalc :
      HasDerivAt
        (fun y : ℝ =>
          (1 / 5) * y ^ 5 - (1 / 4) * y ^ 4 + (1 / 3) * y ^ 3 -
            (1 / 2) * y ^ 2 + y - Real.log (1 + y))
        (expanded x) x := by
    convert
      (((((h5.sub h4).add h3).sub h2).add (hasDerivAt_id x)).sub hlog) using 1 <;>
      norm_num [expanded] <;>
      ring
  have hevent :
      primitive =ᶠ[nhds x]
        (fun y : ℝ =>
          (1 / 5) * y ^ 5 - (1 / 4) * y ^ 4 + (1 / 3) * y ^ 3 -
            (1 / 2) * y ^ 2 + y - Real.log (1 + y)) := by
    filter_upwards [isOpen_Ioi.mem_nhds hx] with y hy
    have hypos : 0 < 1 + y := by
      simp only [Set.mem_Ioi] at hy
      linarith
    simpa only [primitive, abs_of_pos hypos]
  exact hcalc.congr_of_eventuallyEq hevent

theorem gap1 : AntiderivativesOn original = AntiderivativesOn expanded := by
  have hfun : ∀ x ∈ domain, original x = expanded x := by
    intro x hx
    simp only [domain, Set.mem_Ioi] at hx
    have hne : x + 1 ≠ 0 := by linarith
    unfold original expanded
    field_simp [hne]
    ring
  apply Set.ext
  intro F
  change
    (DifferentiableOn ℝ F domain ∧ ∀ x ∈ domain, deriv F x = original x) ↔
      (DifferentiableOn ℝ F domain ∧ ∀ x ∈ domain, deriv F x = expanded x)
  constructor
  · rintro ⟨hDiff, hDer⟩
    refine ⟨hDiff, ?_⟩
    intro x hx
    simpa only [hfun x hx] using hDer x hx
  · rintro ⟨hDiff, hDer⟩
    refine ⟨hDiff, ?_⟩
    intro x hx
    simpa only [hfun x hx] using hDer x hx

theorem gap2 : AntiderivativesOn expanded = PrimitiveFamily primitive := by
  apply Set.ext
  intro F
  change
    (DifferentiableOn ℝ F domain ∧ ∀ x ∈ domain, deriv F x = expanded x) ↔
      (∃ C : ℝ, ∀ x ∈ domain, F x = primitive x + C)
  have hpDiff : DifferentiableOn ℝ primitive domain := by
    intro x hx
    exact (primitive_hasDerivAt hx).differentiableAt.differentiableWithinAt
  constructor
  · rintro ⟨hDiff, hDer⟩
    have hHDiff :
        DifferentiableOn ℝ (fun x => F x - primitive x) domain :=
      hDiff.sub hpDiff
    have hHDer :
        ∀ x ∈ domain, deriv (fun y => F y - primitive y) x = 0 := by
      intro x hx
      have hFat : DifferentiableAt ℝ F x :=
        (hDiff x hx).differentiableAt (isOpen_Ioi.mem_nhds hx)
      simpa only [hDer x hx, sub_self] using
        (hFat.hasDerivAt.sub (primitive_hasDerivAt hx)).deriv
    have hopen : IsOpen domain := by
      rw [domain]
      exact isOpen_Ioi
    have hconn : IsPreconnected domain := by
      rw [domain]
      exact isPreconnected_Ioi
    have hconst :
        ∀ x ∈ domain, ∀ y ∈ domain,
          F x - primitive x = F y - primitive y := by
      intro x hx y hy
      exact hopen.is_const_of_deriv_eq_zero hconn hHDiff hHDer hx hy
    have hzero : (0 : ℝ) ∈ domain := by norm_num [domain]
    refine ⟨F 0 - primitive 0, ?_⟩
    intro x hx
    have heq : F x - primitive x = F 0 - primitive 0 :=
      hconst x hx 0 hzero
    linarith
  · rintro ⟨C, hF⟩
    have hopen : IsOpen domain := by
      unfold domain
      exact isOpen_Ioi
    have hAt : ∀ x ∈ domain, HasDerivAt F (expanded x) x := by
      intro x hx
      have hevent : F =ᶠ[nhds x] (fun y => primitive y + C) := by
        filter_upwards [hopen.mem_nhds hx] with y hy
        exact hF y hy
      have hsum :
          HasDerivAt (fun y => primitive y + C) (expanded x) x := by
        convert
          (primitive_hasDerivAt hx).add (hasDerivAt_const x C) using 1 <;> ring
      exact hsum.congr_of_eventuallyEq hevent
    refine ⟨?_, ?_⟩
    · intro x hx
      exact (hAt x hx).differentiableAt.differentiableWithinAt
    · intro x hx
      exact (hAt x hx).deriv

theorem gap3 : AntiderivativesOn original = PrimitiveFamily primitive := by
  exact gap1.trans gap2

end
end ProofGap.Exercise1728
