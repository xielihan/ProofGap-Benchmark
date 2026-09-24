import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Topology.Neighborhoods
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise1701

noncomputable section

def branch : Set ℝ := Set.Ioo 0 (Real.pi / 2)
def cot (x : ℝ) := Real.cos x / Real.sin x
def integrand (x : ℝ) :=
  1 / ((Real.sin x) ^ 2 * Real.rpow (cot x) (1 / 4 : ℝ))
def substitutedIntegrand (x : ℝ) :=
  -(Real.rpow (cot x) (-1 / 4 : ℝ) * deriv cot x)
def primitive (x : ℝ) :=
  -(4 / 3 : ℝ) * Real.rpow (cot x) (3 / 4 : ℝ)
def AntiderivativesOn (f : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∀ x ∈ branch, HasDerivAt F (f x) x}
def PrimitiveFamily (p : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x ∈ branch, F x = p x + C}

private theorem branch_sin_pos {x : ℝ} (hx : x ∈ branch) : 0 < Real.sin x := by
  apply Real.sin_pos_of_pos_of_lt_pi hx.1
  nlinarith [hx.2, Real.pi_pos]

private theorem branch_cos_pos {x : ℝ} (hx : x ∈ branch) : 0 < Real.cos x := by
  apply Real.cos_pos_of_mem_Ioo
  constructor <;> nlinarith [hx.1, hx.2, Real.pi_pos]

private theorem branch_cot_pos {x : ℝ} (hx : x ∈ branch) : 0 < cot x := by
  exact div_pos (branch_cos_pos hx) (branch_sin_pos hx)

private theorem cot_hasDerivAt {x : ℝ} (hx : x ∈ branch) :
    HasDerivAt cot (-1 / (Real.sin x) ^ 2) x := by
  have hs : Real.sin x ≠ 0 := (branch_sin_pos hx).ne'
  have hquot := (Real.hasDerivAt_cos x).div (Real.hasDerivAt_sin x) hs
  have hcoeff :
      ((-Real.sin x) * Real.sin x - Real.cos x * Real.cos x) /
          (Real.sin x) ^ 2 =
        -1 / (Real.sin x) ^ 2 := by
    congr 1
    nlinarith [Real.sin_sq_add_cos_sq x]
  simpa only [cot, hcoeff] using hquot

private theorem integrand_eq_substituted {x : ℝ} (hx : x ∈ branch) :
    integrand x = substitutedIntegrand x := by
  have hs := branch_sin_pos hx
  have hc := branch_cot_pos hx
  have hd : deriv cot x = -1 / (Real.sin x) ^ 2 :=
    (cot_hasDerivAt hx).deriv
  have hp : 0 < Real.rpow (cot x) (1 / 4 : ℝ) :=
    Real.rpow_pos_of_pos hc _
  have hrpow :
      Real.rpow (cot x) (-1 / 4 : ℝ) =
        (Real.rpow (cot x) (1 / 4 : ℝ))⁻¹ := by
    rw [show (-1 / 4 : ℝ) = -(1 / 4 : ℝ) by ring]
    exact Real.rpow_neg (le_of_lt hc) _
  unfold integrand substitutedIntegrand
  rw [hd, hrpow]
  field_simp [hs.ne', hp.ne']

private theorem primitive_hasDerivAt {x : ℝ} (hx : x ∈ branch) :
    HasDerivAt primitive (substitutedIntegrand x) x := by
  have hc := branch_cot_pos hx
  have hcot := cot_hasDerivAt hx
  have hbase :
      HasDerivAt (fun t : ℝ => Real.rpow t (3 / 4 : ℝ))
        ((3 / 4 : ℝ) * Real.rpow (cot x) ((3 / 4 : ℝ) - 1)) (cot x) := by
    convert Real.hasDerivAt_rpow_const (Or.inl hc.ne') using 1 <;> ring
  have hpow := hbase.comp x hcot
  have hd : deriv cot x = -1 / (Real.sin x) ^ 2 := hcot.deriv
  convert hpow.const_mul (-(4 / 3 : ℝ)) using 1 <;>
    norm_num [primitive, substitutedIntegrand, hd] <;> ring

theorem gap1 :
    AntiderivativesOn integrand = AntiderivativesOn substitutedIntegrand := by
  ext F
  change
    (∀ x ∈ branch, HasDerivAt F (integrand x) x) ↔
      ∀ x ∈ branch, HasDerivAt F (substitutedIntegrand x) x
  constructor
  · intro h x hx
    simpa only [integrand_eq_substituted hx] using h x hx
  · intro h x hx
    simpa only [integrand_eq_substituted hx] using h x hx
theorem gap2 :
    AntiderivativesOn substitutedIntegrand = PrimitiveFamily primitive := by
  ext F
  change
    (∀ x ∈ branch, HasDerivAt F (substitutedIntegrand x) x) ↔
      ∃ C : ℝ, ∀ x ∈ branch, F x = primitive x + C
  constructor
  · intro hF
    let x₀ : ℝ := Real.pi / 4
    have hx₀ : x₀ ∈ branch := by
      change 0 < Real.pi / 4 ∧ Real.pi / 4 < Real.pi / 2
      constructor <;> nlinarith [Real.pi_pos]
    have hzero :
        ∀ x ∈ branch,
          HasDerivAt (fun y => F y - primitive y) 0 x := by
      intro x hx
      convert (hF x hx).sub (primitive_hasDerivAt hx) using 1 <;> ring
    have hdiff :
        DifferentiableOn ℝ (fun y => F y - primitive y) branch := by
      intro x hx
      exact (hzero x hx).differentiableAt.differentiableWithinAt
    have hderiv :
        ∀ x ∈ branch, deriv (fun y => F y - primitive y) x = 0 := by
      intro x hx
      exact (hzero x hx).deriv
    refine ⟨F x₀ - primitive x₀, ?_⟩
    intro x hx
    have heq :=
      isOpen_Ioo.is_const_of_deriv_eq_zero
        (convex_Ioo (0 : ℝ) (Real.pi / 2)).isPreconnected hdiff hderiv
        (x := x) (y := x₀) hx hx₀
    linarith
  · rintro ⟨C, hF⟩ x hx
    have hopen : IsOpen branch := isOpen_Ioo
    have hevent :
        F =ᶠ[nhds x] (fun y => primitive y + C) := by
      filter_upwards [hopen.mem_nhds hx] with y hy
      exact hF y hy
    exact ((primitive_hasDerivAt hx).add_const C).congr_of_eventuallyEq hevent
theorem gap3 :
    AntiderivativesOn integrand = PrimitiveFamily primitive := by
  calc
    AntiderivativesOn integrand = AntiderivativesOn substitutedIntegrand := gap1
    _ = PrimitiveFamily primitive := gap2

end
end ProofGap.Exercise1701
