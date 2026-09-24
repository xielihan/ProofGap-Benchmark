import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Topology.Neighborhoods
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise1640

noncomputable section

def domain : Set ℝ := Set.Ioo (-1) 1
def original (x : ℝ) : ℝ := x ^ 2 / (1 - x ^ 2)
def simple (x : ℝ) : ℝ := -1 + 1 / (1 - x ^ 2)
def primitive (x : ℝ) : ℝ :=
  -x + (1 / 2) * Real.log |(1 + x) / (1 - x)|
def AntiderivativesOn (g : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | DifferentiableOn ℝ F domain ∧ ∀ x ∈ domain, deriv F x = g x}
def PrimitiveFamily (p : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x ∈ domain, F x = p x + C}

private theorem primitive_hasDerivAt (x : ℝ) (hx : x ∈ domain) :
    HasDerivAt primitive (simple x) x := by
  unfold domain at hx
  have hxp : 0 < 1 + x := by linarith [hx.1]
  have hxm : 0 < 1 - x := by linarith [hx.2]
  have hxpne : 1 + x ≠ 0 := ne_of_gt hxp
  have hxmne : 1 - x ≠ 0 := ne_of_gt hxm
  have hp :
      HasDerivAt (fun y : ℝ => Real.log (1 + y)) (1 / (1 + x)) x := by
    simpa [one_div] using
      (((hasDerivAt_const x 1).add (hasDerivAt_id x)).log hxpne)
  have hm :
      HasDerivAt (fun y : ℝ => Real.log (1 - y)) (-1 / (1 - x)) x := by
    simpa [one_div] using
      (((hasDerivAt_const x 1).sub (hasDerivAt_id x)).log hxmne)
  have hraw :
      HasDerivAt
        (fun y : ℝ =>
          -y + (1 / 2) * (Real.log (1 + y) - Real.log (1 - y)))
        (simple x) x := by
    convert
      (hasDerivAt_id x).neg.add
        ((hasDerivAt_const x (1 / 2)).mul (hp.sub hm)) using 1
    unfold simple
    have hsq : 0 < 1 - x ^ 2 := by nlinarith [hx.1, hx.2]
    field_simp [hxpne, hxmne, ne_of_gt hsq]
    ring
  apply hraw.congr_of_eventuallyEq
  filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
  unfold primitive
  have hyp : 0 < 1 + y := by linarith [hy.1]
  have hym : 0 < 1 - y := by linarith [hy.2]
  rw [abs_of_pos (div_pos hyp hym),
    Real.log_div (ne_of_gt hyp) (ne_of_gt hym)]

theorem gap1 : AntiderivativesOn original = AntiderivativesOn simple := by
  apply Set.ext
  intro F
  simp only [AntiderivativesOn, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hF, hderiv⟩
    refine ⟨hF, ?_⟩
    intro x hx
    rw [hderiv x hx]
    unfold original simple
    have hxlt : x < 1 := hx.2
    have hxgt : -1 < x := hx.1
    have hne : 1 - x ^ 2 ≠ 0 := by
      have hpos : 0 < 1 - x ^ 2 := by nlinarith
      exact ne_of_gt hpos
    field_simp
    ring
  · rintro ⟨hF, hderiv⟩
    refine ⟨hF, ?_⟩
    intro x hx
    rw [hderiv x hx]
    unfold original simple
    have hxlt : x < 1 := hx.2
    have hxgt : -1 < x := hx.1
    have hne : 1 - x ^ 2 ≠ 0 := by
      have hpos : 0 < 1 - x ^ 2 := by nlinarith
      exact ne_of_gt hpos
    field_simp
    ring

theorem gap2 : AntiderivativesOn simple = PrimitiveFamily primitive := by
  apply Set.ext
  intro F
  simp only [AntiderivativesOn, PrimitiveFamily, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hFdiff, hFderiv⟩
    have hzero : ∀ x ∈ domain, deriv (fun y => F y - primitive y) x = 0 := by
      intro x hx
      have hFat : DifferentiableAt ℝ F x :=
        (hFdiff x hx).differentiableAt (isOpen_Ioo.mem_nhds hx)
      have hPat : DifferentiableAt ℝ primitive x :=
        (primitive_hasDerivAt x hx).differentiableAt
      change deriv (F - primitive) x = 0
      rw [deriv_sub hFat hPat, hFderiv x hx,
        (primitive_hasDerivAt x hx).deriv]
      ring
    refine ⟨F 0 - primitive 0, ?_⟩
    intro x hx
    have h0 : (0 : ℝ) ∈ domain := by
      constructor <;> norm_num [domain]
    have hconst :=
      isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo
        (fun y hy =>
          (hFdiff y hy).sub
            (primitive_hasDerivAt y hy).differentiableAt.differentiableWithinAt)
        hzero hx h0
    dsimp at hconst
    linarith
  · rintro ⟨C, hFC⟩
    have hFderiv : ∀ x ∈ domain, HasDerivAt F (simple x) x := by
      intro x hx
      have heq : F =ᶠ[nhds x] fun y => primitive y + C := by
        filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
        exact hFC y hy
      exact ((primitive_hasDerivAt x hx).add_const C).congr_of_eventuallyEq heq
    exact
      ⟨fun x hx => (hFderiv x hx).differentiableAt.differentiableWithinAt,
        fun x hx => (hFderiv x hx).deriv⟩

theorem gap3 : AntiderivativesOn original = PrimitiveFamily primitive := by
  rw [gap1, gap2]

end
end ProofGap.Exercise1640
