import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Neighborhoods
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

namespace ProofGap.Exercise1826

noncomputable section

def branch : Set ℝ := Set.Ioi 0
def integrand (x : ℝ) := Real.sin (Real.log x)
def residual₁ (x : ℝ) :=
  x * Real.cos (Real.log x) * (1 / x)
def boundary₁ (x : ℝ) := x * Real.sin (Real.log x)
def boundary₂ (x : ℝ) :=
  boundary₁ x - x * Real.cos (Real.log x)
def primitive (x : ℝ) :=
  x / 2 * (Real.sin (Real.log x) - Real.cos (Real.log x))
def AntiderivativesOn (f : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∀ x ∈ branch, HasDerivAt F (f x) x}
def FirstByPartsFamily : Set (ℝ → ℝ) :=
  {F | ∃ G ∈ AntiderivativesOn residual₁,
    ∀ x ∈ branch, F x = boundary₁ x - G x}
def RecurrenceFamily : Set (ℝ → ℝ) :=
  {F | ∃ G ∈ AntiderivativesOn integrand,
    ∀ x ∈ branch, F x = boundary₂ x - G x}
def PrimitiveFamily : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x ∈ branch, F x = primitive x + C}

private theorem deriv_congr_on_branch
    (x : ℝ) (hx : x ∈ branch) {f g : ℝ → ℝ} {f' : ℝ}
    (hfg : ∀ y ∈ branch, f y = g y) (hg : HasDerivAt g f' x) :
    HasDerivAt f f' x := by
  have hx' : x ∈ Set.Ioi (0 : ℝ) := by
    simpa [branch] using hx
  have hnhds : branch ∈ nhds x := by
    simpa [branch] using (isOpen_Ioi.mem_nhds hx')
  have heq : f =ᶠ[nhds x] g :=
    Filter.mem_of_superset hnhds (fun y hy => hfg y hy)
  exact hg.congr_of_eventuallyEq heq

private theorem hasDerivAt_boundary₁ (x : ℝ) (hx : x ∈ branch) :
    HasDerivAt boundary₁ (integrand x + residual₁ x) x := by
  have hx0 : x ≠ 0 := by
    exact ne_of_gt (by simpa [branch] using hx)
  have hlog : HasDerivAt Real.log (1 / x) x := by
    simpa [one_div] using Real.hasDerivAt_log hx0
  simpa [boundary₁, integrand, residual₁, mul_assoc] using
    (hasDerivAt_id x).mul
      ((Real.hasDerivAt_sin (Real.log x)).comp x hlog)

private theorem hasDerivAt_cosine_boundary (x : ℝ) (hx : x ∈ branch) :
    HasDerivAt (fun y => y * Real.cos (Real.log y))
      (residual₁ x - integrand x) x := by
  have hx0 : x ≠ 0 := by
    exact ne_of_gt (by simpa [branch] using hx)
  have hlog : HasDerivAt Real.log (1 / x) x := by
    simpa [one_div] using Real.hasDerivAt_log hx0
  have hcos : HasDerivAt (fun y => Real.cos (Real.log y))
      (-Real.sin (Real.log x) * (1 / x)) x := by
    simpa using (Real.hasDerivAt_cos (Real.log x)).comp x hlog
  have hraw : HasDerivAt (fun y => y * Real.cos (Real.log y))
      (1 * Real.cos (Real.log x) +
        x * (-Real.sin (Real.log x) * (1 / x))) x :=
    (hasDerivAt_id x).mul hcos
  have hres : residual₁ x = Real.cos (Real.log x) := by
    calc
      residual₁ x = Real.cos (Real.log x) * (x * (1 / x)) := by
        unfold residual₁
        ring
      _ = Real.cos (Real.log x) := by
        simp [hx0]
  convert hraw using 1
  rw [hres]
  unfold integrand
  field_simp [hx0] <;> ring

private theorem hasDerivAt_boundary₂ (x : ℝ) (hx : x ∈ branch) :
    HasDerivAt boundary₂ (2 * integrand x) x := by
  unfold boundary₂
  convert (hasDerivAt_boundary₁ x hx).sub
    (hasDerivAt_cosine_boundary x hx) using 1 <;> ring

private theorem hasDerivAt_primitive (x : ℝ) (hx : x ∈ branch) :
    HasDerivAt primitive (integrand x) x := by
  have hfun : primitive = fun y => (1 / 2 : ℝ) * boundary₂ y := by
    funext y
    simp [primitive, boundary₂, boundary₁]
    ring
  rw [hfun]
  convert (hasDerivAt_boundary₂ x hx).const_mul (1 / 2 : ℝ) using 1 <;> ring

theorem gap1 :
    AntiderivativesOn integrand = FirstByPartsFamily := by
  ext F
  change
    (∀ x ∈ branch, HasDerivAt F (integrand x) x) ↔
      ∃ G, (∀ x ∈ branch, HasDerivAt G (residual₁ x) x) ∧
        ∀ x ∈ branch, F x = boundary₁ x - G x
  constructor
  · intro hF
    refine ⟨fun y => boundary₁ y - F y, ?_, ?_⟩
    · intro x hx
      convert (hasDerivAt_boundary₁ x hx).sub (hF x hx) using 1 <;> ring
    · intro x hx
      ring
  · rintro ⟨G, hG, hFG⟩
    intro x hx
    have hd :
        HasDerivAt (fun y => boundary₁ y - G y) (integrand x) x := by
      convert (hasDerivAt_boundary₁ x hx).sub (hG x hx) using 1 <;> ring
    exact deriv_congr_on_branch x hx (fun y hy => hFG y hy) hd
theorem gap2 :
    FirstByPartsFamily = RecurrenceFamily := by
  ext F
  change
    (∃ G, (∀ x ∈ branch, HasDerivAt G (residual₁ x) x) ∧
      ∀ x ∈ branch, F x = boundary₁ x - G x) ↔
    ∃ H, (∀ x ∈ branch, HasDerivAt H (integrand x) x) ∧
      ∀ x ∈ branch, F x = boundary₂ x - H x
  constructor
  · rintro ⟨G, hG, hFG⟩
    refine ⟨fun y => G y - y * Real.cos (Real.log y), ?_, ?_⟩
    · intro x hx
      convert (hG x hx).sub (hasDerivAt_cosine_boundary x hx) using 1 <;> ring
    · intro x hx
      calc
        F x = boundary₁ x - G x := hFG x hx
        _ = boundary₂ x - (G x - x * Real.cos (Real.log x)) := by
          unfold boundary₂
          ring
  · rintro ⟨H, hH, hFH⟩
    refine ⟨fun y => y * Real.cos (Real.log y) + H y, ?_, ?_⟩
    · intro x hx
      convert (hasDerivAt_cosine_boundary x hx).add (hH x hx) using 1 <;> ring
    · intro x hx
      calc
        F x = boundary₂ x - H x := hFH x hx
        _ = boundary₁ x - (x * Real.cos (Real.log x) + H x) := by
          unfold boundary₂
          ring
theorem gap3 :
    AntiderivativesOn integrand = RecurrenceFamily := by
  calc
    AntiderivativesOn integrand = FirstByPartsFamily := gap1
    _ = RecurrenceFamily := gap2
theorem gap4 :
    AntiderivativesOn integrand = PrimitiveFamily := by
  ext F
  change
    (∀ x ∈ branch, HasDerivAt F (integrand x) x) ↔
      ∃ C : ℝ, ∀ x ∈ branch, F x = primitive x + C
  constructor
  · intro hF
    let D : ℝ → ℝ := fun y => F y - primitive y
    have hD : ∀ x ∈ branch, HasDerivAt D 0 x := by
      intro x hx
      dsimp [D]
      convert (hF x hx).sub (hasDerivAt_primitive x hx) using 1 <;> ring
    have hDdiff : DifferentiableOn ℝ D branch := by
      intro x hx
      exact (hD x hx).differentiableAt.differentiableWithinAt
    have hDderiv : ∀ x ∈ branch, deriv D x = 0 := by
      intro x hx
      exact (hD x hx).deriv
    have h1 : (1 : ℝ) ∈ branch := by
      norm_num [branch]
    refine ⟨F 1 - primitive 1, ?_⟩
    intro x hx
    have hc : D x = D 1 :=
      (isOpen_Ioi : IsOpen (Set.Ioi (0 : ℝ))).is_const_of_deriv_eq_zero
        (convex_Ioi (0 : ℝ)).isPreconnected hDdiff hDderiv hx h1
    dsimp [D] at hc
    linarith
  · rintro ⟨C, hFC⟩
    intro x hx
    have hd : HasDerivAt (fun y => primitive y + C) (integrand x) x :=
      (hasDerivAt_primitive x hx).add_const C
    exact deriv_congr_on_branch x hx (fun y hy => hFC y hy) hd

end
end ProofGap.Exercise1826
