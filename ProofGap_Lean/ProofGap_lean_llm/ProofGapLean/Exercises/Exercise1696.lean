import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Topology.Neighborhoods
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1696

noncomputable section

def branch : Set ℝ := Set.Ioo (-Real.pi / 2) (Real.pi / 2)
def integrand (x : ℝ) :=
  Real.sin x / Real.sqrt ((Real.cos x) ^ 3)
def substitutedIntegrand (x : ℝ) :=
  -(Real.rpow (Real.cos x) (-3 / 2 : ℝ) * deriv Real.cos x)
def primitive (x : ℝ) := 2 / Real.sqrt (Real.cos x)
def AntiderivativesOn (f : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∀ x ∈ branch, HasDerivAt F (f x) x}
def PrimitiveFamily (p : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x ∈ branch, F x = p x + C}

private lemma sqrt_cube_eq_mul_sqrt {a : ℝ} (ha : 0 ≤ a) :
    Real.sqrt (a ^ 3) = a * Real.sqrt a := by
  have hcube : 0 ≤ a ^ 3 := pow_nonneg ha 3
  have hleft_sq : (Real.sqrt (a ^ 3)) ^ 2 = a ^ 3 :=
    Real.sq_sqrt hcube
  have hright_sq : (a * Real.sqrt a) ^ 2 = a ^ 3 := by
    rw [mul_pow, Real.sq_sqrt ha]
    ring
  have hleft_nonneg : 0 ≤ Real.sqrt (a ^ 3) := Real.sqrt_nonneg _
  have hright_nonneg : 0 ≤ a * Real.sqrt a :=
    mul_nonneg ha (Real.sqrt_nonneg _)
  nlinarith

private lemma rpow_neg_three_halves_eq_inv_sqrt_cube {a : ℝ} (ha : 0 < a) :
    Real.rpow a (-3 / 2 : ℝ) = (Real.sqrt (a ^ 3))⁻¹ := by
  calc
    Real.rpow a (-3 / 2 : ℝ) =
        Real.exp (Real.log a * (-3 / 2 : ℝ)) := by
      simpa only using
        ((Real.rpow_def_of_pos ha) (-3 / 2 : ℝ))
    _ = (Real.sqrt (a ^ 3))⁻¹ := by
      rw [sqrt_cube_eq_mul_sqrt (le_of_lt ha)]
      let L : ℝ := Real.log a * (-3 / 2 : ℝ)
      have hpow : Real.exp L ^ 2 * a ^ 3 = 1 := by
        calc
          Real.exp L ^ 2 * a ^ 3 =
              Real.exp L ^ 2 * Real.exp (Real.log a) ^ 3 := by
            rw [Real.exp_log ha]
          _ = Real.exp
              (L + L + Real.log a + Real.log a + Real.log a) := by
            simp only [pow_succ, Real.exp_add]
            ring
          _ = Real.exp 0 := by
            congr 1
            dsimp [L]
            ring
          _ = 1 := by simp
      have hsqrt_sq : (Real.sqrt a) ^ 2 = a :=
        Real.sq_sqrt (le_of_lt ha)
      have hproduct_sq :
          (Real.exp L * (a * Real.sqrt a)) ^ 2 = 1 := by
        calc
          (Real.exp L * (a * Real.sqrt a)) ^ 2 =
              Real.exp L ^ 2 * a ^ 3 := by
            rw [mul_pow, mul_pow, hsqrt_sq]
            ring
          _ = 1 := hpow
      have hproduct_pos : 0 < Real.exp L * (a * Real.sqrt a) :=
        mul_pos (Real.exp_pos _) (mul_pos ha (Real.sqrt_pos.2 ha))
      have hproduct : Real.exp L * (a * Real.sqrt a) = 1 := by
        nlinarith
      have hden : a * Real.sqrt a ≠ 0 :=
        ne_of_gt (mul_pos ha (Real.sqrt_pos.2 ha))
      change Real.exp L = (a * Real.sqrt a)⁻¹
      rw [← one_div]
      exact (eq_div_iff hden).2 hproduct

private lemma integrand_eq_substitutedIntegrand (x : ℝ) (hx : x ∈ branch) :
    integrand x = substitutedIntegrand x := by
  have hx' : x ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    change -Real.pi / 2 < x ∧ x < Real.pi / 2 at hx
    constructor
    · nlinarith [hx.1]
    · exact hx.2
  have hcos : 0 < Real.cos x := Real.cos_pos_of_mem_Ioo hx'
  have hderiv : deriv Real.cos x = -Real.sin x :=
    (Real.hasDerivAt_cos x).deriv
  have hrpow := rpow_neg_three_halves_eq_inv_sqrt_cube hcos
  unfold integrand substitutedIntegrand
  rw [hderiv, hrpow]
  simp only [div_eq_mul_inv]
  ring

private lemma hasDerivAt_primitive_integrand (x : ℝ) (hx : x ∈ branch) :
    HasDerivAt primitive (integrand x) x := by
  have hx' : x ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    change -Real.pi / 2 < x ∧ x < Real.pi / 2 at hx
    constructor
    · nlinarith [hx.1]
    · exact hx.2
  have hcos : 0 < Real.cos x := Real.cos_pos_of_mem_Ioo hx'
  have hsqrt_pos : 0 < Real.sqrt (Real.cos x) := Real.sqrt_pos.2 hcos
  have hsqrt_ne : Real.sqrt (Real.cos x) ≠ 0 := ne_of_gt hsqrt_pos
  have hsqrt :
      HasDerivAt (fun y : ℝ => Real.sqrt (Real.cos y))
        ((1 / (2 * Real.sqrt (Real.cos x))) * (-Real.sin x)) x := by
    simpa only [Function.comp_apply] using
      (Real.hasDerivAt_sqrt (ne_of_gt hcos)).comp x
        (Real.hasDerivAt_cos x)
  have hraw :
      HasDerivAt primitive
        (2 *
          (-((1 / (2 * Real.sqrt (Real.cos x))) * (-Real.sin x)) /
            (Real.sqrt (Real.cos x)) ^ 2)) x := by
    simpa only [primitive, div_eq_mul_inv] using
      (hsqrt.inv hsqrt_ne).const_mul 2
  apply hraw.congr_deriv
  have hsquare : (Real.sqrt (Real.cos x)) ^ 2 = Real.cos x :=
    Real.sq_sqrt (le_of_lt hcos)
  have hcube := sqrt_cube_eq_mul_sqrt (le_of_lt hcos)
  unfold integrand
  rw [hcube, hsquare]
  field_simp [hsqrt_ne, ne_of_gt hcos]
  <;> ring

private lemma hasDerivAt_primitive_substitutedIntegrand
    (x : ℝ) (hx : x ∈ branch) :
    HasDerivAt primitive (substitutedIntegrand x) x :=
  (hasDerivAt_primitive_integrand x hx).congr_deriv
    (integrand_eq_substitutedIntegrand x hx)

private lemma eq_at_zero_of_hasDerivAt_zero_on_branch
    (g : ℝ → ℝ)
    (hg : ∀ x ∈ branch, HasDerivAt g 0 x) :
    ∀ x ∈ branch, g x = g 0 := by
  have hzero : (0 : ℝ) ∈ branch := by
    change -Real.pi / 2 < 0 ∧ 0 < Real.pi / 2
    constructor <;> nlinarith [Real.pi_pos]
  have hopen : IsOpen branch := by
    simpa [branch] using
      (isOpen_Ioo : IsOpen (Set.Ioo (-Real.pi / 2) (Real.pi / 2)))
  have hconvex : Convex ℝ branch := by
    rw [branch]
    exact convex_Ioo (-Real.pi / 2) (Real.pi / 2)
  have hpreconnected : IsPreconnected branch :=
    hconvex.isPreconnected
  have hdiff : DifferentiableOn ℝ g branch := by
    intro x hx
    exact (hg x hx).differentiableAt.differentiableWithinAt
  have hderiv : ∀ x ∈ branch, deriv g x = 0 := by
    intro x hx
    exact (hg x hx).deriv
  intro x hx
  exact hopen.is_const_of_deriv_eq_zero hpreconnected hdiff hderiv hx hzero

theorem gap1 :
    AntiderivativesOn integrand = AntiderivativesOn substitutedIntegrand := by
  apply Set.ext
  intro F
  change
    (∀ x ∈ branch, HasDerivAt F (integrand x) x) ↔
      ∀ x ∈ branch, HasDerivAt F (substitutedIntegrand x) x
  constructor
  · intro h x hx
    exact (h x hx).congr_deriv (integrand_eq_substitutedIntegrand x hx)
  · intro h x hx
    exact (h x hx).congr_deriv (integrand_eq_substitutedIntegrand x hx).symm
theorem gap2 :
    AntiderivativesOn substitutedIntegrand = PrimitiveFamily primitive := by
  apply Set.ext
  intro F
  change
    (∀ x ∈ branch, HasDerivAt F (substitutedIntegrand x) x) ↔
      ∃ C : ℝ, ∀ x ∈ branch, F x = primitive x + C
  constructor
  · intro hF
    have hz :
        ∀ x ∈ branch,
          HasDerivAt (fun y => F y - primitive y) 0 x := by
      intro x hx
      simpa using
        (hF x hx).sub (hasDerivAt_primitive_substitutedIntegrand x hx)
    refine ⟨F 0 - primitive 0, ?_⟩
    intro x hx
    have hc := eq_at_zero_of_hasDerivAt_zero_on_branch
      (fun y => F y - primitive y) hz x hx
    dsimp at hc
    linarith
  · rintro ⟨C, hC⟩ x hx
    have hp := hasDerivAt_primitive_substitutedIntegrand x hx
    have hc : HasDerivAt (fun _ : ℝ => C) 0 x :=
      hasDerivAt_const (x := x) (c := C)
    have hpc :
        HasDerivAt (primitive + fun _ : ℝ => C)
          (substitutedIntegrand x) x := by
      simpa only [add_zero] using hp.add hc
    have hopen : IsOpen branch := by
      simpa [branch] using
        (isOpen_Ioo : IsOpen (Set.Ioo (-Real.pi / 2) (Real.pi / 2)))
    have heq : F =ᶠ[nhds x] (primitive + fun _ : ℝ => C) :=
      Filter.mem_of_superset (hopen.mem_nhds hx) (by
        intro y hy
        simpa only [Pi.add_apply] using hC y hy)
    exact hpc.congr_of_eventuallyEq heq
theorem gap3 :
    AntiderivativesOn integrand = PrimitiveFamily primitive := by
  exact gap1.trans gap2

end
end ProofGap.Exercise1696
