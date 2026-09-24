import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.Neighborhoods
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1643

noncomputable section

def domain : Set ℝ := Set.Ioi 1
def original (x : ℝ) : ℝ :=
  (Real.sqrt (x ^ 2 + 1) - Real.sqrt (x ^ 2 - 1)) /
    Real.sqrt (x ^ 4 - 1)
def simple (x : ℝ) : ℝ :=
  1 / Real.sqrt (x ^ 2 - 1) - 1 / Real.sqrt (x ^ 2 + 1)
def primitive (x : ℝ) : ℝ :=
  Real.log |(x + Real.sqrt (x ^ 2 - 1)) /
    (x + Real.sqrt (x ^ 2 + 1))|
def AntiderivativesOn (g : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | DifferentiableOn ℝ F domain ∧ ∀ x ∈ domain, deriv F x = g x}
def PrimitiveFamily (p : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x ∈ domain, F x = p x + C}

private theorem domain_isOpen : IsOpen domain := by
  simpa [domain] using (isOpen_Ioi : IsOpen (Set.Ioi (1 : ℝ)))

private theorem original_eq_simple {x : ℝ} (hx : x ∈ domain) :
    original x = simple x := by
  have hxpos : 1 < x := hx
  have hm : 0 < x ^ 2 - 1 := by nlinarith
  have hp : 0 < x ^ 2 + 1 := by nlinarith [sq_nonneg x]
  have hsqrt :
      Real.sqrt (x ^ 4 - 1) =
        Real.sqrt (x ^ 2 - 1) * Real.sqrt (x ^ 2 + 1) := by
    rw [show x ^ 4 - 1 = (x ^ 2 - 1) * (x ^ 2 + 1) by ring]
    rw [Real.sqrt_mul (le_of_lt hm)]
  rw [original, simple, hsqrt]
  field_simp [ne_of_gt (Real.sqrt_pos.2 hm), ne_of_gt (Real.sqrt_pos.2 hp)]
  <;> ring

private def expandedPrimitive (x : ℝ) : ℝ :=
  Real.log (x + Real.sqrt (x ^ 2 - 1)) -
    Real.log (x + Real.sqrt (x ^ 2 + 1))

private theorem primitive_eq_expanded {x : ℝ} (hx : x ∈ domain) :
    primitive x = expandedPrimitive x := by
  have hxpos : 1 < x := hx
  have hm : 0 < x ^ 2 - 1 := by nlinarith
  have hp : 0 < x ^ 2 + 1 := by nlinarith [sq_nonneg x]
  have hargm : 0 < x + Real.sqrt (x ^ 2 - 1) := by
    nlinarith [Real.sqrt_nonneg (x ^ 2 - 1)]
  have hargp : 0 < x + Real.sqrt (x ^ 2 + 1) := by
    nlinarith [Real.sqrt_nonneg (x ^ 2 + 1)]
  unfold primitive expandedPrimitive
  rw [Real.log_abs, Real.log_div (ne_of_gt hargm) (ne_of_gt hargp)]

private theorem primitive_hasDerivAt {x : ℝ} (hx : x ∈ domain) :
    HasDerivAt primitive (simple x) x := by
  have hxpos : 1 < x := hx
  have hm : 0 < x ^ 2 - 1 := by nlinarith
  have hp : 0 < x ^ 2 + 1 := by nlinarith [sq_nonneg x]
  have hsm : 0 < Real.sqrt (x ^ 2 - 1) := Real.sqrt_pos.2 hm
  have hsp : 0 < Real.sqrt (x ^ 2 + 1) := Real.sqrt_pos.2 hp
  have hargm : 0 < x + Real.sqrt (x ^ 2 - 1) := by
    nlinarith [Real.sqrt_nonneg (x ^ 2 - 1)]
  have hargp : 0 < x + Real.sqrt (x ^ 2 + 1) := by
    nlinarith [Real.sqrt_nonneg (x ^ 2 + 1)]
  have hsm_deriv :
      HasDerivAt (fun y : ℝ => Real.sqrt (y ^ 2 - 1))
        (x / Real.sqrt (x ^ 2 - 1)) x := by
    convert
      (Real.hasDerivAt_sqrt (ne_of_gt hm)).comp x
        (((hasDerivAt_id x).pow 2).sub (hasDerivAt_const x 1)) using 1 <;>
      simp only [id_eq] <;>
      field_simp [ne_of_gt hsm] <;>
      ring
  have hsp_deriv :
      HasDerivAt (fun y : ℝ => Real.sqrt (y ^ 2 + 1))
        (x / Real.sqrt (x ^ 2 + 1)) x := by
    convert
      (Real.hasDerivAt_sqrt (ne_of_gt hp)).comp x
        (((hasDerivAt_id x).pow 2).add (hasDerivAt_const x 1)) using 1 <;>
      simp only [id_eq] <;>
      field_simp [ne_of_gt hsp] <;>
      ring
  have hlogm :
      HasDerivAt (fun y : ℝ => Real.log (y + Real.sqrt (y ^ 2 - 1)))
        (1 / Real.sqrt (x ^ 2 - 1)) x := by
    convert
      (Real.hasDerivAt_log (ne_of_gt hargm)).comp x
        ((hasDerivAt_id x).add hsm_deriv) using 1 <;>
      field_simp [ne_of_gt hsm, ne_of_gt hargm] <;>
      nlinarith [Real.sq_sqrt hm.le]
  have hlogp :
      HasDerivAt (fun y : ℝ => Real.log (y + Real.sqrt (y ^ 2 + 1)))
        (1 / Real.sqrt (x ^ 2 + 1)) x := by
    convert
      (Real.hasDerivAt_log (ne_of_gt hargp)).comp x
        ((hasDerivAt_id x).add hsp_deriv) using 1 <;>
      field_simp [ne_of_gt hsp, ne_of_gt hargp] <;>
      nlinarith [Real.sq_sqrt hp.le]
  have hexp : HasDerivAt expandedPrimitive (simple x) x := by
    simpa [expandedPrimitive, simple] using hlogm.sub hlogp
  have heq : primitive =ᶠ[nhds x] expandedPrimitive := by
    filter_upwards [domain_isOpen.mem_nhds hx] with y hy
    exact primitive_eq_expanded hy
  exact hexp.congr_of_eventuallyEq heq

theorem gap1 : AntiderivativesOn original = AntiderivativesOn simple := by
  ext F
  simp only [AntiderivativesOn, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hF, hderiv⟩
    exact ⟨hF, fun x hx => (hderiv x hx).trans (original_eq_simple hx)⟩
  · rintro ⟨hF, hderiv⟩
    exact ⟨hF, fun x hx => (hderiv x hx).trans (original_eq_simple hx).symm⟩

theorem gap2 : AntiderivativesOn simple = PrimitiveFamily primitive := by
  ext F
  simp only [AntiderivativesOn, PrimitiveFamily, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hFdiff, hFderiv⟩
    let H : ℝ → ℝ := fun x => F x - primitive x
    have hHdiff : DifferentiableOn ℝ H domain := by
      intro x hx
      have hFat : DifferentiableAt ℝ F x :=
        (hFdiff x hx).differentiableAt (domain_isOpen.mem_nhds hx)
      exact (hFat.sub (primitive_hasDerivAt hx).differentiableAt).differentiableWithinAt
    have hHzero : ∀ x ∈ domain, deriv H x = 0 := by
      intro x hx
      have hFat : DifferentiableAt ℝ F x :=
        (hFdiff x hx).differentiableAt (domain_isOpen.mem_nhds hx)
      have hd : HasDerivAt H (deriv F x - simple x) x := by
        simpa [H] using hFat.hasDerivAt.sub (primitive_hasDerivAt hx)
      rw [hFderiv x hx] at hd
      simpa using hd.deriv
    have hpre : IsPreconnected domain := by
      exact (convex_Ioi (1 : ℝ)).isPreconnected
    refine ⟨F 2 - primitive 2, ?_⟩
    intro x hx
    have htwo : (2 : ℝ) ∈ domain := by norm_num [domain]
    have hc : H x = H 2 :=
      domain_isOpen.is_const_of_deriv_eq_zero hpre hHdiff hHzero hx htwo
    dsimp [H] at hc
    linarith
  · rintro ⟨C, hFC⟩
    have hpDiff : DifferentiableOn ℝ (fun x => primitive x + C) domain := by
      intro x hx
      exact ((primitive_hasDerivAt hx).add_const C).differentiableAt.differentiableWithinAt
    refine ⟨hpDiff.congr (fun x hx => hFC x hx), ?_⟩
    intro x hx
    have hevent : F =ᶠ[nhds x] fun y => primitive y + C := by
      filter_upwards [domain_isOpen.mem_nhds hx] with y hy
      exact hFC y hy
    rw [hevent.deriv_eq]
    exact ((primitive_hasDerivAt hx).add_const C).deriv

theorem gap3 : AntiderivativesOn original = PrimitiveFamily primitive := by
  exact gap1.trans gap2

end
end ProofGap.Exercise1643
