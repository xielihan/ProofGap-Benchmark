import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Neighborhoods
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise1926

noncomputable section

def t (x : ℝ) := Real.sqrt x
def positiveBranch : Set ℝ := {x | 0 < x}
def AntiderivativesOn (s : Set ℝ) (f : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∀ x ∈ s, HasDerivAt F (f x) x}
def PrimitiveFamilyOn (s : Set ℝ) (p : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x ∈ s, F x = p x + C}
def integrand (x : ℝ) := 1 / (1 + Real.sqrt x)
def transformed₁ (x : ℝ) := t x / (1 + t x) * deriv t x
def transformed₂ (x : ℝ) := (1 - 1 / (1 + t x)) * deriv t x
def ScaledFamily (p : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ G ∈ AntiderivativesOn positiveBranch p,
    ∀ x ∈ positiveBranch, F x = 2 * G x}
def primitiveT (x : ℝ) := 2 * (t x - Real.log (1 + t x))
def primitiveSqrt (x : ℝ) :=
  2 * Real.sqrt x - 2 * Real.log (1 + Real.sqrt x)

private theorem positiveBranch_isOpen : IsOpen positiveBranch := by
  simpa [positiveBranch] using (isOpen_Ioi : IsOpen (Set.Ioi (0 : ℝ)))

private theorem primitiveT_hasDerivAt (x : ℝ) (hx : x ∈ positiveBranch) :
    HasDerivAt primitiveT (integrand x) x := by
  have hxpos : 0 < x := by
    simpa [positiveBranch] using hx
  have htpos : 0 < t x := by
    simpa [t] using (Real.sqrt_pos.2 hxpos)
  have hs : HasDerivAt t ((2 * t x)⁻¹) x := by
    simpa [t] using Real.hasDerivAt_sqrt (ne_of_gt hxpos)
  have hinner : HasDerivAt (fun y => 1 + t y) ((2 * t x)⁻¹) x := by
    exact hs.const_add 1
  have hlog : HasDerivAt (fun y => Real.log (1 + t y))
      ((1 + t x)⁻¹ * (2 * t x)⁻¹) x := by
    simpa using
      (Real.hasDerivAt_log
        (ne_of_gt (show 0 < 1 + t x by positivity))).comp x hinner
  have hraw := (hs.sub hlog).const_mul 2
  have hcoef :
      2 * ((2 * t x)⁻¹ - (1 + t x)⁻¹ * (2 * t x)⁻¹) = integrand x := by
    simp only [integrand]
    change 2 * ((2 * t x)⁻¹ - (1 + t x)⁻¹ * (2 * t x)⁻¹) =
      1 / (1 + t x)
    field_simp [ne_of_gt htpos, ne_of_gt (show 0 < 1 + t x by positivity)]
    ring
  simpa only [primitiveT, hcoef] using hraw

private theorem hasDerivAt_zero_eq {f : ℝ → ℝ}
    (hf : ∀ x, HasDerivAt f 0 x) (x y : ℝ) : f x = f y := by
  have hdiff : Differentiable ℝ f := fun z => (hf z).differentiableAt
  have hderiv : ∀ z, deriv f z = 0 := fun z => (hf z).deriv
  exact is_const_of_deriv_eq_zero hdiff hderiv x y

theorem gap1 (x : ℝ) (hx : 0 ≤ x) :
    x = t x ^ 2 := by
  simpa [t] using (Real.sq_sqrt hx).symm
theorem gap2 (x : ℝ) (hx : 0 < x) :
    1 = 2 * t x * deriv t x := by
  have htpos : 0 < t x := by
    simpa [t] using (Real.sqrt_pos.2 hx)
  have hs : HasDerivAt t ((2 * t x)⁻¹) x := by
    simpa [t] using Real.hasDerivAt_sqrt (ne_of_gt hx)
  rw [hs.deriv]
  field_simp [ne_of_gt htpos]
theorem gap3 :
    AntiderivativesOn positiveBranch integrand = ScaledFamily transformed₁ := by
  apply Set.ext
  intro F
  constructor
  · intro hF
    change ∀ x ∈ positiveBranch, HasDerivAt F (integrand x) x at hF
    change ∃ G ∈ AntiderivativesOn positiveBranch transformed₁,
      ∀ x ∈ positiveBranch, F x = 2 * G x
    refine ⟨fun y => (1 / 2 : ℝ) * F y, ?_, ?_⟩
    · change ∀ x ∈ positiveBranch,
        HasDerivAt (fun y => (1 / 2 : ℝ) * F y) (transformed₁ x) x
      intro x hx
      have htd : t x * deriv t x = (1 / 2 : ℝ) := by
        nlinarith [gap2 x hx]
      have hcoef : (1 / 2 : ℝ) * integrand x = transformed₁ x := by
        simp only [integrand, transformed₁]
        change (1 / 2 : ℝ) * (1 / (1 + t x)) =
          t x / (1 + t x) * deriv t x
        rw [← htd]
        ring
      simpa only [hcoef] using (hF x hx).const_mul (1 / 2 : ℝ)
    · intro x hx
      ring
  · intro hscaled
    change ∃ G ∈ AntiderivativesOn positiveBranch transformed₁,
      ∀ x ∈ positiveBranch, F x = 2 * G x at hscaled
    rcases hscaled with ⟨G, hG, hFG⟩
    change ∀ x ∈ positiveBranch, HasDerivAt G (transformed₁ x) x at hG
    change ∀ x ∈ positiveBranch, HasDerivAt F (integrand x) x
    intro x hx
    have htd : t x * deriv t x = (1 / 2 : ℝ) := by
      nlinarith [gap2 x hx]
    have hhalf : (1 / 2 : ℝ) * integrand x = transformed₁ x := by
      simp only [integrand, transformed₁]
      change (1 / 2 : ℝ) * (1 / (1 + t x)) =
        t x / (1 + t x) * deriv t x
      rw [← htd]
      ring
    have hcoef : 2 * transformed₁ x = integrand x := by
      rw [← hhalf]
      ring
    have hd : HasDerivAt (fun y => 2 * G y) (integrand x) x := by
      simpa only [hcoef] using (hG x hx).const_mul 2
    have heq : F =ᶠ[nhds x] fun y => 2 * G y := by
      filter_upwards [positiveBranch_isOpen.mem_nhds hx] with y hy
      exact hFG y hy
    exact hd.congr_of_eventuallyEq heq
theorem gap4 :
    ScaledFamily transformed₁ = ScaledFamily transformed₂ := by
  apply Set.ext
  intro F
  constructor
  · intro hF
    change ∃ G ∈ AntiderivativesOn positiveBranch transformed₁,
      ∀ x ∈ positiveBranch, F x = 2 * G x at hF
    rcases hF with ⟨G, hG, hFG⟩
    change ∃ G ∈ AntiderivativesOn positiveBranch transformed₂,
      ∀ x ∈ positiveBranch, F x = 2 * G x
    refine ⟨G, ?_, hFG⟩
    change ∀ x ∈ positiveBranch, HasDerivAt G (transformed₂ x) x
    intro x hx
    have heq : transformed₁ x = transformed₂ x := by
      have htpos : 0 < t x := by
        simpa [positiveBranch, t] using (Real.sqrt_pos.2 hx)
      simp only [transformed₁, transformed₂]
      field_simp [ne_of_gt (show 0 < 1 + t x by positivity)]
      ring
    simpa only [heq] using hG x hx
  · intro hF
    change ∃ G ∈ AntiderivativesOn positiveBranch transformed₂,
      ∀ x ∈ positiveBranch, F x = 2 * G x at hF
    rcases hF with ⟨G, hG, hFG⟩
    change ∃ G ∈ AntiderivativesOn positiveBranch transformed₁,
      ∀ x ∈ positiveBranch, F x = 2 * G x
    refine ⟨G, ?_, hFG⟩
    change ∀ x ∈ positiveBranch, HasDerivAt G (transformed₁ x) x
    intro x hx
    have heq : transformed₁ x = transformed₂ x := by
      have htpos : 0 < t x := by
        simpa [positiveBranch, t] using (Real.sqrt_pos.2 hx)
      simp only [transformed₁, transformed₂]
      field_simp [ne_of_gt (show 0 < 1 + t x by positivity)]
      ring
    simpa only [heq] using hG x hx
theorem gap5 :
    AntiderivativesOn positiveBranch integrand = ScaledFamily transformed₂ := by
  exact gap3.trans gap4
theorem gap6 :
    AntiderivativesOn positiveBranch integrand =
      PrimitiveFamilyOn positiveBranch primitiveT := by
  apply Set.ext
  intro F
  constructor
  · intro hF
    change ∀ x ∈ positiveBranch, HasDerivAt F (integrand x) x at hF
    change ∃ C : ℝ, ∀ x ∈ positiveBranch, F x = primitiveT x + C
    refine ⟨F 1 - primitiveT 1, ?_⟩
    intro x hx
    have hxpos : 0 < x := by
      simpa [positiveBranch] using hx
    let H : ℝ → ℝ := fun y => F (Real.exp y) - primitiveT (Real.exp y)
    have hH : ∀ y, HasDerivAt H 0 y := by
      intro y
      have hy : Real.exp y ∈ positiveBranch := by
        change 0 < Real.exp y
        exact Real.exp_pos y
      have hFcomp := (hF (Real.exp y) hy).comp y (Real.hasDerivAt_exp y)
      have hPcomp := (primitiveT_hasDerivAt (Real.exp y) hy).comp y
        (Real.hasDerivAt_exp y)
      change HasDerivAt (fun z => F (Real.exp z) - primitiveT (Real.exp z)) 0 y
      simpa using hFcomp.sub hPcomp
    have hc : H (Real.log x) = H 0 :=
      hasDerivAt_zero_eq hH (Real.log x) 0
    dsimp [H] at hc
    rw [Real.exp_log hxpos] at hc
    norm_num at hc
    linarith
  · rintro ⟨C, hFC⟩
    change ∀ x ∈ positiveBranch, HasDerivAt F (integrand x) x
    intro x hx
    have hd : HasDerivAt (fun y => primitiveT y + C) (integrand x) x :=
      (primitiveT_hasDerivAt x hx).add_const C
    have heq : F =ᶠ[nhds x] fun y => primitiveT y + C := by
      filter_upwards [positiveBranch_isOpen.mem_nhds hx] with y hy
      exact hFC y hy
    exact hd.congr_of_eventuallyEq heq
theorem gap7 :
    PrimitiveFamilyOn positiveBranch primitiveT =
      PrimitiveFamilyOn positiveBranch primitiveSqrt := by
  have hp : primitiveT = primitiveSqrt := by
    funext x
    simp only [primitiveT, primitiveSqrt, t]
    ring
  rw [hp]
theorem gap8 :
    AntiderivativesOn positiveBranch integrand =
      PrimitiveFamilyOn positiveBranch primitiveSqrt := by
  exact gap6.trans gap7

end
end ProofGap.Exercise1926
