import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise2030
noncomputable section

def branch : Set ℝ := Set.Ioo (-(Real.pi / 2)) (Real.pi / 2)
def integrand (a b x : ℝ) :=
  1 / (a ^ 2 * Real.sin x ^ 2 + b ^ 2 * Real.cos x ^ 2)
def transformed (a b x : ℝ) :=
  1 / (a ^ 2 * Real.tan x ^ 2 + b ^ 2) * deriv Real.tan x
def primitive (a b x : ℝ) :=
  1 / (a * b) * Real.arctan (a * Real.tan x / b)
def Family (f : ℝ → ℝ) :=
  {F : ℝ → ℝ | ∀ x ∈ branch, HasDerivAt F (f x) x}
def Translates (p : ℝ → ℝ) :=
  {F : ℝ → ℝ | ∃ C, ∀ x ∈ branch, F x = p x + C}

theorem gap1 (a b x : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (hx : x ∈ branch) :
    integrand a b x = transformed a b x := by
  have hcos : Real.cos x ≠ 0 :=
    ne_of_gt (Real.cos_pos_of_mem_Ioo (by simpa only [branch] using hx))
  have hleft :
      a ^ 2 * Real.sin x ^ 2 + b ^ 2 * Real.cos x ^ 2 ≠ 0 := by
    positivity
  have hright :
      a ^ 2 * (Real.sin x / Real.cos x) ^ 2 + b ^ 2 ≠ 0 := by
    positivity
  unfold integrand transformed
  rw [(Real.hasDerivAt_tan hcos).deriv, Real.tan_eq_sin_div_cos]
  field_simp [hcos, hleft, hright] <;> ring
theorem gap2 (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) :
    Family (integrand a b) = Translates (primitive a b) := by
  have hprimitive : ∀ x ∈ branch,
      HasDerivAt (primitive a b) (integrand a b x) x := by
    intro x hx
    have hcos : Real.cos x ≠ 0 :=
      ne_of_gt (Real.cos_pos_of_mem_Ioo (by simpa only [branch] using hx))
    have htan : HasDerivAt Real.tan (1 / Real.cos x ^ 2) x :=
      Real.hasDerivAt_tan hcos
    have hinner :
        HasDerivAt (fun y => a * Real.tan y / b)
          (a * (1 / Real.cos x ^ 2) / b) x := by
      simpa only using (htan.const_mul a).div_const b
    have harctan :
        HasDerivAt (fun y => Real.arctan (a * Real.tan y / b))
          (1 / (1 + (a * Real.tan x / b) ^ 2) *
            (a * (1 / Real.cos x ^ 2) / b)) x := by
      exact (Real.hasDerivAt_arctan (a * Real.tan x / b)).comp x hinner
    have houter :
        HasDerivAt
          (fun y => 1 / (a * b) * Real.arctan (a * Real.tan y / b))
          (1 / (a * b) *
            (1 / (1 + (a * Real.tan x / b) ^ 2) *
              (a * (1 / Real.cos x ^ 2) / b))) x := by
      simpa only using harctan.const_mul (1 / (a * b))
    have hden : a ^ 2 * Real.tan x ^ 2 + b ^ 2 ≠ 0 := by
      positivity
    have harcden : 1 + (a * Real.tan x / b) ^ 2 ≠ 0 := by
      positivity
    have hcoef :
        1 / (a * b) *
            (1 / (1 + (a * Real.tan x / b) ^ 2) *
              (a * (1 / Real.cos x ^ 2) / b)) =
          transformed a b x := by
      unfold transformed
      rw [htan.deriv]
      field_simp [ha, hb, hcos, hden, harcden] <;> ring
    rw [hcoef, ← gap1 a b x ha hb hx] at houter
    simpa only [primitive] using houter
  ext F
  constructor
  · intro hF
    change ∀ x ∈ branch, HasDerivAt F (integrand a b x) x at hF
    change ∃ C, ∀ x ∈ branch, F x = primitive a b x + C
    let D : ℝ → ℝ := fun y => F y - primitive a b y
    have hD : ∀ x ∈ branch, HasDerivAt D 0 x := by
      intro x hx
      simpa only [D, sub_self] using (hF x hx).sub (hprimitive x hx)
    have hdiff : DifferentiableOn ℝ D branch := by
      intro x hx
      exact (hD x hx).differentiableAt.differentiableWithinAt
    have hderiv : ∀ x ∈ branch, deriv D x = 0 := by
      intro x hx
      exact (hD x hx).deriv
    have hzero : (0 : ℝ) ∈ branch := by
      change -(Real.pi / 2) < 0 ∧ 0 < Real.pi / 2
      constructor <;> linarith [Real.pi_pos]
    refine ⟨D 0, ?_⟩
    intro x hx
    have hconst : D x = D 0 :=
      isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo
        hdiff hderiv hx hzero
    dsimp only [D] at hconst ⊢
    linarith
  · intro hF
    change (∃ C, ∀ x ∈ branch, F x = primitive a b x + C) at hF
    change ∀ x ∈ branch, HasDerivAt F (integrand a b x) x
    rcases hF with ⟨C, hC⟩
    intro x hx
    have hpc :
        HasDerivAt (fun y => primitive a b y + C) (integrand a b x) x :=
      (hprimitive x hx).add_const C
    apply hpc.congr_of_eventuallyEq
    filter_upwards [isOpen_Ioo.mem_nhds (by simpa only [branch] using hx)] with y hy
    exact hC y (by simpa only [branch] using hy)

end
end ProofGap.Exercise2030
