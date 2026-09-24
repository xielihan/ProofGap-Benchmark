import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Neighborhoods
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise1822

noncomputable section

def branch : Set ℝ := Set.Ioi 0
def t (x : ℝ) := Real.sqrt x
def integrand (x : ℝ) := Real.exp (t x)
def substitutedIntegrand (x : ℝ) := t x * Real.exp (t x) * deriv t x
def expChainIntegrand (x : ℝ) := t x * deriv (fun y => Real.exp (t y)) x
def residual (x : ℝ) := Real.exp (t x) * deriv t x
def boundary (x : ℝ) := 2 * t x * Real.exp (t x)
def primitiveT (x : ℝ) := boundary x - 2 * Real.exp (t x)
def primitive (x : ℝ) :=
  2 * (Real.sqrt x - 1) * Real.exp (Real.sqrt x)
def AntiderivativesOn (f : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∀ x ∈ branch, HasDerivAt F (f x) x}
def TwiceFamily (f : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ G ∈ AntiderivativesOn f, ∀ x ∈ branch, F x = 2 * G x}
def ByPartsFamily : Set (ℝ → ℝ) :=
  {F | ∃ G ∈ AntiderivativesOn residual,
    ∀ x ∈ branch, F x = boundary x - 2 * G x}
def PrimitiveTFamily : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x ∈ branch, F x = primitiveT x + C}
def PrimitiveFamily : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x ∈ branch, F x = primitive x + C}

private theorem hasDerivAt_t (x : ℝ) (hx : x ∈ branch) :
    HasDerivAt t (1 / (2 * Real.sqrt x)) x := by
  have hx0 : 0 < x := by simpa [branch] using hx
  simpa [t] using Real.hasDerivAt_sqrt (ne_of_gt hx0)

private theorem hasDerivAt_exp_t (x : ℝ) (hx : x ∈ branch) :
    HasDerivAt (fun y : ℝ => Real.exp (t y))
      (Real.exp (t x) * deriv t x) x := by
  have h := (Real.hasDerivAt_exp (t x)).comp x (hasDerivAt_t x hx)
  simpa only [Function.comp_apply, (hasDerivAt_t x hx).deriv] using h

private theorem two_mul_substituted_eq_integrand
    (x : ℝ) (hx : x ∈ branch) :
    2 * substitutedIntegrand x = integrand x := by
  have hx0 : 0 < x := by simpa [branch] using hx
  have hs : Real.sqrt x ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hx0)
  rw [substitutedIntegrand, integrand, (hasDerivAt_t x hx).deriv]
  dsimp [t]
  field_simp [hs]

private theorem substitutedIntegrand_eq_expChainIntegrand
    (x : ℝ) (hx : x ∈ branch) :
    substitutedIntegrand x = expChainIntegrand x := by
  unfold substitutedIntegrand expChainIntegrand
  rw [(hasDerivAt_exp_t x hx).deriv]
  ring

private theorem hasDerivAt_t_mul_exp_t
    (x : ℝ) (hx : x ∈ branch) :
    HasDerivAt (fun y => t y * Real.exp (t y))
      (residual x + expChainIntegrand x) x := by
  have ht : deriv t x = 1 / (2 * Real.sqrt x) :=
    (hasDerivAt_t x hx).deriv
  have ht' : HasDerivAt t (deriv t x) x := by
    simpa only [ht] using hasDerivAt_t x hx
  have h := ht'.mul (hasDerivAt_exp_t x hx)
  convert h using 1
  unfold residual expChainIntegrand
  rw [(hasDerivAt_exp_t x hx).deriv]
  ring

private theorem residual_antiderivative_eq_exp_add_const
    {G : ℝ → ℝ} (hG : G ∈ AntiderivativesOn residual) :
    ∃ C : ℝ, ∀ x ∈ branch, G x = Real.exp (t x) + C := by
  let D : ℝ → ℝ := fun x => G x - Real.exp (t x)
  have hD : ∀ x ∈ branch, HasDerivAt D 0 x := by
    intro x hx
    have h := (hG x hx).sub (hasDerivAt_exp_t x hx)
    simpa [D, residual] using h
  have hconst : ∀ x ∈ branch, ∀ y ∈ branch, D x = D y := by
    intro x hx y hy
    have hx0 : 0 < x := by simpa [branch] using hx
    have hy0 : 0 < y := by simpa [branch] using hy
    let b : ℝ := max x y + 1
    have hxb : x < b := by
      dsimp [b]
      linarith [le_max_left x y]
    have hyb : y < b := by
      dsimp [b]
      linarith [le_max_right x y]
    have hdiff : DifferentiableOn ℝ D (Set.Ioo 0 b) := by
      intro z hz
      exact (hD z (by simpa [branch] using hz.1)).differentiableAt.differentiableWithinAt
    have hzero : ∀ z ∈ Set.Ioo 0 b, deriv D z = 0 := by
      intro z hz
      exact (hD z (by simpa [branch] using hz.1)).deriv
    have hc : ∀ u ∈ Set.Ioo 0 b, ∀ v ∈ Set.Ioo 0 b, D u = D v := by
      intro u hu v hv
      exact isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo hdiff hzero hu hv
    exact hc x ⟨hx0, hxb⟩ y ⟨hy0, hyb⟩
  refine ⟨D 1, ?_⟩
  intro x hx
  have h1 : (1 : ℝ) ∈ branch := by norm_num [branch]
  have hc := hconst x hx 1 h1
  dsimp [D] at hc ⊢
  linarith

theorem gap1 (x : ℝ) (hx : x ∈ branch) :
    x = (t x) ^ 2 := by
  have hx0 : 0 ≤ x := le_of_lt (by simpa [branch] using hx)
  simpa [t] using (Real.sq_sqrt hx0).symm
theorem gap2 (x : ℝ) (hx : x ∈ branch) :
    deriv (fun y : ℝ => y) x = 2 * t x * deriv t x := by
  have hx0 : 0 < x := by simpa [branch] using hx
  have hs : Real.sqrt x ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hx0)
  have hid : deriv (fun y : ℝ => y) x = 1 :=
    (hasDerivAt_id x).deriv
  have ht : deriv t x = 1 / (2 * Real.sqrt x) :=
    (hasDerivAt_t x hx).deriv
  rw [hid, ht]
  dsimp [t]
  field_simp [hs]
theorem gap3 :
    AntiderivativesOn integrand = TwiceFamily substitutedIntegrand := by
  ext F
  constructor
  · intro hF
    refine ⟨fun y => (1 / 2 : ℝ) * F y, ?_, ?_⟩
    · intro x hx
      have hs : substitutedIntegrand x =
          (1 / 2 : ℝ) * integrand x := by
        nlinarith [two_mul_substituted_eq_integrand x hx]
      simpa only [hs] using (hF x hx).const_mul (1 / 2 : ℝ)
    · intro x hx
      ring
  · rintro ⟨G, hG, hFG⟩
    intro x hx
    have hder : HasDerivAt (fun y => 2 * G y) (integrand x) x := by
      simpa only [two_mul_substituted_eq_integrand x hx] using
        (hG x hx).const_mul 2
    have hnear : F =ᶠ[nhds x] fun y => 2 * G y := by
      have hb : branch ∈ nhds x := by
        change Set.Ioi 0 ∈ nhds x
        exact isOpen_Ioi.mem_nhds (by simpa [branch] using hx)
      filter_upwards [hb] with y hy
      exact hFG y hy
    exact hder.congr_of_eventuallyEq hnear
theorem gap4 :
    TwiceFamily substitutedIntegrand = TwiceFamily expChainIntegrand := by
  ext F
  constructor
  · rintro ⟨G, hG, hFG⟩
    refine ⟨G, ?_, hFG⟩
    intro x hx
    have heq := substitutedIntegrand_eq_expChainIntegrand x hx
    simpa only [← heq] using hG x hx
  · rintro ⟨G, hG, hFG⟩
    refine ⟨G, ?_, hFG⟩
    intro x hx
    have heq := substitutedIntegrand_eq_expChainIntegrand x hx
    simpa only [heq] using hG x hx
theorem gap5 :
    TwiceFamily expChainIntegrand = ByPartsFamily := by
  ext F
  constructor
  · rintro ⟨G, hG, hFG⟩
    refine ⟨fun y => t y * Real.exp (t y) - G y, ?_, ?_⟩
    · intro x hx
      have h := (hasDerivAt_t_mul_exp_t x hx).sub (hG x hx)
      convert h using 1
      ring
    · intro x hx
      rw [hFG x hx]
      unfold boundary
      ring
  · rintro ⟨G, hG, hFG⟩
    refine ⟨fun y => t y * Real.exp (t y) - G y, ?_, ?_⟩
    · intro x hx
      have h := (hasDerivAt_t_mul_exp_t x hx).sub (hG x hx)
      convert h using 1
      ring
    · intro x hx
      rw [hFG x hx]
      unfold boundary
      ring
theorem gap6 :
    ByPartsFamily = PrimitiveTFamily := by
  ext F
  constructor
  · rintro ⟨G, hG, hFG⟩
    obtain ⟨C, hC⟩ := residual_antiderivative_eq_exp_add_const hG
    refine ⟨-2 * C, ?_⟩
    intro x hx
    rw [hFG x hx, hC x hx]
    unfold primitiveT
    ring
  · rintro ⟨C, hF⟩
    refine ⟨fun y => Real.exp (t y) - C / 2, ?_, ?_⟩
    · intro x hx
      simpa [residual] using
        (hasDerivAt_exp_t x hx).sub_const (C / 2)
    · intro x hx
      rw [hF x hx]
      unfold primitiveT
      ring
theorem gap7 :
    PrimitiveTFamily = PrimitiveFamily := by
  ext F
  constructor
  · rintro ⟨C, hF⟩
    refine ⟨C, ?_⟩
    intro x hx
    rw [hF x hx]
    simp only [primitiveT, primitive, boundary, t]
    ring
  · rintro ⟨C, hF⟩
    refine ⟨C, ?_⟩
    intro x hx
    rw [hF x hx]
    simp only [primitiveT, primitive, boundary, t]
    ring
theorem gap8 :
    AntiderivativesOn integrand = PrimitiveFamily := by
  calc
    AntiderivativesOn integrand = TwiceFamily substitutedIntegrand := gap3
    _ = TwiceFamily expChainIntegrand := gap4
    _ = ByPartsFamily := gap5
    _ = PrimitiveTFamily := gap6
    _ = PrimitiveFamily := gap7

end
end ProofGap.Exercise1822
