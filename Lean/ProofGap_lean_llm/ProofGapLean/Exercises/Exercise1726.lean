import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.Neighborhoods
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1726

noncomputable section

def domain : Set ℝ := Set.Ioo (-Real.sqrt 2) (Real.sqrt 2)
def original (x : ℝ) : ℝ := (2 - x) ^ 2 / (2 - x ^ 2)
def expanded (x : ℝ) : ℝ := (x ^ 2 - 2 - 4 * x + 6) / (2 - x ^ 2)
def simple (x : ℝ) : ℝ := -1 - 4 * x / (2 - x ^ 2) + 6 / (2 - x ^ 2)
def primitive (x : ℝ) : ℝ :=
  -x + 2 * Real.log |2 - x ^ 2| +
    (3 / Real.sqrt 2) * Real.log |(Real.sqrt 2 + x) / (Real.sqrt 2 - x)|
def AntiderivativesOn (g : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | DifferentiableOn ℝ F domain ∧ ∀ x ∈ domain, deriv F x = g x}
def PrimitiveFamily (p : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x ∈ domain, F x = p x + C}

private theorem sqrt_two_pos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)

private theorem sqrt_two_sq : (Real.sqrt 2) ^ 2 = (2 : ℝ) :=
  Real.sq_sqrt (by norm_num)

private theorem denom_pos {x : ℝ} (hx : x ∈ domain) :
    0 < 2 - x ^ 2 := by
  have hx' : -Real.sqrt 2 < x ∧ x < Real.sqrt 2 := hx
  nlinarith [sqrt_two_sq]

private theorem original_eq_expanded (x : ℝ) :
    original x = expanded x := by
  unfold original expanded
  congr 1
  ring

private theorem expanded_eq_simple {x : ℝ} (hx : x ∈ domain) :
    expanded x = simple x := by
  have hdne : 2 - x ^ 2 ≠ 0 := ne_of_gt (denom_pos hx)
  unfold expanded simple
  field_simp [hdne]
  ring

private theorem original_eq_simple {x : ℝ} (hx : x ∈ domain) :
    original x = simple x :=
  (original_eq_expanded x).trans (expanded_eq_simple hx)

private theorem primitive_hasDerivAt {x : ℝ} (hx : x ∈ domain) :
    HasDerivAt primitive (simple x) x := by
  have hsne : Real.sqrt 2 ≠ 0 := ne_of_gt sqrt_two_pos
  have hdpos : 0 < 2 - x ^ 2 := denom_pos hx
  have hdne : 2 - x ^ 2 ≠ 0 := ne_of_gt hdpos
  have hleft : 0 < Real.sqrt 2 + x := by
    have hx' : -Real.sqrt 2 < x := hx.1
    linarith
  have hright : 0 < Real.sqrt 2 - x := by
    have hx' : x < Real.sqrt 2 := hx.2
    linarith
  have hinner : HasDerivAt (fun y : ℝ => 2 - y ^ 2) (-2 * x) x := by
    convert (hasDerivAt_const x 2).sub ((hasDerivAt_id x).pow 2) using 1 <;>
      simp only [id_eq] <;>
      ring
  have hlogdRaw :=
    (Real.hasDerivAt_log hdne).comp x hinner
  have hlogd :
      HasDerivAt (fun y : ℝ => Real.log |2 - y ^ 2|)
        (-2 * x / (2 - x ^ 2)) x := by
    convert hlogdRaw using 1
    · funext y
      simp only [Function.comp_apply, Real.log_abs]
    · ring
  have hnum :
      HasDerivAt (fun y : ℝ => Real.sqrt 2 + y) 1 x := by
    simpa using (hasDerivAt_const x (Real.sqrt 2)).add (hasDerivAt_id x)
  have hden :
      HasDerivAt (fun y : ℝ => Real.sqrt 2 - y) (-1) x := by
    simpa using (hasDerivAt_const x (Real.sqrt 2)).sub (hasDerivAt_id x)
  have hquot :=
    hnum.div hden (ne_of_gt hright)
  have hqne :
      (Real.sqrt 2 + x) / (Real.sqrt 2 - x) ≠ 0 :=
    div_ne_zero (ne_of_gt hleft) (ne_of_gt hright)
  have hlogqRaw :=
    (Real.hasDerivAt_log hqne).comp x hquot
  have hlogq :
      HasDerivAt
        (fun y : ℝ =>
          Real.log |(Real.sqrt 2 + y) / (Real.sqrt 2 - y)|)
        (2 * Real.sqrt 2 / (2 - x ^ 2)) x := by
    convert hlogqRaw using 1
    · funext y
      simp only [Function.comp_apply, Pi.div_apply, Real.log_abs]
    · field_simp [ne_of_gt hleft, ne_of_gt hright, hdne]
      nlinarith [sqrt_two_sq]
  have hraw :=
    (((hasDerivAt_id x).neg.add (hlogd.const_mul 2)).add
      (hlogq.const_mul (3 / Real.sqrt 2)))
  unfold primitive
  convert hraw using 1
  unfold simple
  field_simp [hsne, hdne]
  ring

theorem gap1 : AntiderivativesOn original = AntiderivativesOn expanded := by
  ext F
  simp only [AntiderivativesOn, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hF, hderiv⟩
    exact ⟨hF, fun x hx => (hderiv x hx).trans (original_eq_expanded x)⟩
  · rintro ⟨hF, hderiv⟩
    exact ⟨hF, fun x hx => (hderiv x hx).trans (original_eq_expanded x).symm⟩

theorem gap2 : AntiderivativesOn expanded = AntiderivativesOn simple := by
  ext F
  simp only [AntiderivativesOn, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hF, hderiv⟩
    exact ⟨hF, fun x hx => (hderiv x hx).trans (expanded_eq_simple hx)⟩
  · rintro ⟨hF, hderiv⟩
    exact ⟨hF, fun x hx => (hderiv x hx).trans (expanded_eq_simple hx).symm⟩

theorem gap3 : AntiderivativesOn original = AntiderivativesOn simple := by
  exact gap1.trans gap2

theorem gap4 : AntiderivativesOn original = PrimitiveFamily primitive := by
  ext F
  simp only [AntiderivativesOn, PrimitiveFamily, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hFdiff, hFderiv⟩
    let H : ℝ → ℝ := fun x => F x - primitive x
    have hHzero : ∀ x ∈ domain, HasDerivAt H 0 x := by
      intro x hx
      have hFat : DifferentiableAt ℝ F x :=
        (hFdiff x hx).differentiableAt (isOpen_Ioo.mem_nhds hx)
      have hFder : HasDerivAt F (simple x) x := by
        rw [← original_eq_simple hx]
        simpa only [hFderiv x hx] using hFat.hasDerivAt
      simpa [H] using hFder.sub (primitive_hasDerivAt hx)
    have hHdiff : DifferentiableOn ℝ H domain := by
      intro x hx
      exact (hHzero x hx).differentiableAt.differentiableWithinAt
    have hHderiv : ∀ x ∈ domain, deriv H x = 0 := by
      intro x hx
      exact (hHzero x hx).deriv
    refine ⟨F 0 - primitive 0, ?_⟩
    intro x hx
    have hzero : (0 : ℝ) ∈ domain := by
      exact ⟨by linarith [sqrt_two_pos], sqrt_two_pos⟩
    have hc : H x = H 0 :=
      isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo
        hHdiff hHderiv hx hzero
    dsimp [H] at hc
    linarith
  · rintro ⟨C, hFC⟩
    have hFat : ∀ x ∈ domain, HasDerivAt F (original x) x := by
      intro x hx
      have hsum :
          HasDerivAt (fun y => primitive y + C) (original x) x := by
        rw [original_eq_simple hx]
        exact (primitive_hasDerivAt hx).add_const C
      have hevent : F =ᶠ[nhds x] fun y => primitive y + C := by
        filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
        exact hFC y hy
      exact hsum.congr_of_eventuallyEq hevent
    constructor
    · intro x hx
      exact (hFat x hx).differentiableAt.differentiableWithinAt
    · intro x hx
      exact (hFat x hx).deriv

end
end ProofGap.Exercise1726
