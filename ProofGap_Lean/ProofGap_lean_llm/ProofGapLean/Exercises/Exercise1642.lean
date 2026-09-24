import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise1642

noncomputable section

def domain : Set ℝ := Set.Ioo (-1) 1
def original (x : ℝ) : ℝ :=
  (Real.sqrt (1 + x ^ 2) + Real.sqrt (1 - x ^ 2)) /
    Real.sqrt (1 - x ^ 4)
def simple (x : ℝ) : ℝ :=
  1 / Real.sqrt (1 - x ^ 2) + 1 / Real.sqrt (1 + x ^ 2)
def primitive (x : ℝ) : ℝ :=
  Real.arcsin x + Real.log (x + Real.sqrt (1 + x ^ 2))
def AntiderivativesOn (g : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | DifferentiableOn ℝ F domain ∧ ∀ x ∈ domain, deriv F x = g x}
def PrimitiveFamily (p : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x ∈ domain, F x = p x + C}

private theorem original_eq_simple (x : ℝ) (hx : x ∈ domain) :
    original x = simple x := by
  have hx' : -1 < x ∧ x < 1 := by
    simpa [domain] using hx
  have hm : 0 < 1 - x ^ 2 := by
    nlinarith
  have hp : 0 < 1 + x ^ 2 := by
    nlinarith [sq_nonneg x]
  have hsqrt :
      Real.sqrt (1 - x ^ 4) =
        Real.sqrt (1 - x ^ 2) * Real.sqrt (1 + x ^ 2) := by
    rw [show 1 - x ^ 4 = (1 - x ^ 2) * (1 + x ^ 2) by ring]
    rw [Real.sqrt_mul (le_of_lt hm)]
  rw [original, simple, hsqrt]
  field_simp [ne_of_gt (Real.sqrt_pos.2 hm), ne_of_gt (Real.sqrt_pos.2 hp)]
  <;> ring

private theorem primitive_hasDerivAt (x : ℝ) (hx : x ∈ domain) :
    HasDerivAt primitive (simple x) x := by
  have hx' : x ∈ Set.Ioo (-1 : ℝ) 1 := by
    simpa [domain] using hx
  have hp : 0 < 1 + x ^ 2 := by
    nlinarith [sq_nonneg x]
  have hspos : 0 < Real.sqrt (1 + x ^ 2) := Real.sqrt_pos.2 hp
  have hsqrt_deriv :
      HasDerivAt (fun y : ℝ => Real.sqrt (1 + y ^ 2))
        (x / Real.sqrt (1 + x ^ 2)) x := by
    convert
      (Real.hasDerivAt_sqrt (ne_of_gt hp)).comp x
        ((hasDerivAt_const x 1).add ((hasDerivAt_id x).pow 2)) using 1 <;>
      simp only [id_eq] <;>
      field_simp [ne_of_gt hspos] <;>
      ring
  have harg : 0 < x + Real.sqrt (1 + x ^ 2) := by
    have hsquare := Real.sq_sqrt (le_of_lt hp)
    have hsnonneg := Real.sqrt_nonneg (1 + x ^ 2)
    by_contra hn
    have hle : x + Real.sqrt (1 + x ^ 2) ≤ 0 := le_of_not_gt hn
    have hxnonpos : x ≤ 0 := by linarith
    have hmul₁ : 0 ≤ x * (x + Real.sqrt (1 + x ^ 2)) :=
      mul_nonneg_of_nonpos_of_nonpos hxnonpos hle
    have hmul₂ :
        Real.sqrt (1 + x ^ 2) * (x + Real.sqrt (1 + x ^ 2)) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hsnonneg hle
    nlinarith
  have hlog_deriv :
      HasDerivAt
        (fun y : ℝ => Real.log (y + Real.sqrt (1 + y ^ 2)))
        (1 / Real.sqrt (1 + x ^ 2)) x := by
    convert
      (Real.hasDerivAt_log (ne_of_gt harg)).comp x
        ((hasDerivAt_id x).add hsqrt_deriv) using 1 <;>
      field_simp [ne_of_gt hspos, ne_of_gt harg] <;> ring
  simpa [primitive, simple, one_div] using
    (Real.hasDerivAt_arcsin (ne_of_gt hx'.1) (ne_of_lt hx'.2)).add hlog_deriv

theorem gap1 : AntiderivativesOn original = AntiderivativesOn simple := by
  apply Set.ext
  intro F
  change
    (DifferentiableOn ℝ F domain ∧ ∀ x ∈ domain, deriv F x = original x) ↔
      (DifferentiableOn ℝ F domain ∧ ∀ x ∈ domain, deriv F x = simple x)
  constructor
  · rintro ⟨hF, hder⟩
    refine ⟨hF, ?_⟩
    intro x hx
    rw [hder x hx, original_eq_simple x hx]
  · rintro ⟨hF, hder⟩
    refine ⟨hF, ?_⟩
    intro x hx
    rw [hder x hx, original_eq_simple x hx]

theorem gap2 : AntiderivativesOn simple = PrimitiveFamily primitive := by
  apply Set.ext
  intro F
  change
    (DifferentiableOn ℝ F domain ∧ ∀ x ∈ domain, deriv F x = simple x) ↔
      (∃ C : ℝ, ∀ x ∈ domain, F x = primitive x + C)
  constructor
  · rintro ⟨hFdiff, hFder⟩
    let H : ℝ → ℝ := fun x => F x - primitive x
    have hHzero : ∀ x ∈ domain, HasDerivAt H 0 x := by
      intro x hx
      have hda : DifferentiableAt ℝ F x :=
        (hFdiff x hx).differentiableAt (isOpen_Ioo.mem_nhds hx)
      have hFat : HasDerivAt F (simple x) x := by
        simpa [hFder x hx] using hda.hasDerivAt
      simpa [H] using hFat.sub (primitive_hasDerivAt x hx)
    have hHdiff : DifferentiableOn ℝ H (Set.Ioo (-1 : ℝ) 1) := by
      intro x hx
      have hxdom : x ∈ domain := by
        simpa [domain] using hx
      exact (hHzero x hxdom).differentiableAt.differentiableWithinAt
    have hHder : ∀ x ∈ Set.Ioo (-1 : ℝ) 1, deriv H x = 0 := by
      intro x hx
      have hxdom : x ∈ domain := by
        simpa [domain] using hx
      exact (hHzero x hxdom).deriv
    refine ⟨F 0 - primitive 0, ?_⟩
    intro x hx
    have hxIoo : x ∈ Set.Ioo (-1 : ℝ) 1 := by
      simpa [domain] using hx
    have hzero : (0 : ℝ) ∈ Set.Ioo (-1 : ℝ) 1 := by
      norm_num
    have heq : H x = H 0 :=
      isOpen_Ioo.is_const_of_deriv_eq_zero
        isPreconnected_Ioo hHdiff hHder hxIoo hzero
    dsimp [H] at heq
    linarith
  · rintro ⟨C, hFC⟩
    have hFat : ∀ x ∈ domain, HasDerivAt F (simple x) x := by
      intro x hx
      have hsum : HasDerivAt (fun y => primitive y + C) (simple x) x :=
        (primitive_hasDerivAt x hx).add_const C
      have hwithin : HasDerivWithinAt F (simple x) domain x := by
        apply hsum.hasDerivWithinAt.congr
        · intro y hy
          exact hFC y hy
        · exact hFC x hx
      exact hwithin.hasDerivAt (isOpen_Ioo.mem_nhds hx)
    constructor
    · intro x hx
      exact (hFat x hx).differentiableAt.differentiableWithinAt
    · intro x hx
      exact (hFat x hx).deriv

theorem gap3 : AntiderivativesOn original = PrimitiveFamily primitive := by
  rw [gap1]
  exact gap2

end
end ProofGap.Exercise1642
