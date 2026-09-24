import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Defs.Filter
import Mathlib.Tactic.Positivity
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise2029
noncomputable section

def branch : Set ℝ := Set.Ioo (-(Real.pi / 2)) (Real.pi / 2)
def integrand (x : ℝ) := Real.sin x ^ 2 / (1 + Real.sin x ^ 2)
def remainder (x : ℝ) := 1 / (1 + Real.sin x ^ 2)
def firstTanRemainder (x : ℝ) :=
  1 / (1 / Real.cos x ^ 2 + Real.tan x ^ 2) * deriv Real.tan x
def secondTanRemainder (x : ℝ) :=
  1 / (1 + 2 * Real.tan x ^ 2) * deriv Real.tan x
def primitive (x : ℝ) :=
  x - 1 / Real.sqrt 2 * Real.arctan (Real.sqrt 2 * Real.tan x)
def Family (f : ℝ → ℝ) :=
  {F : ℝ → ℝ | ∀ x ∈ branch, HasDerivAt F (f x) x}
def Translates (p : ℝ → ℝ) :=
  {F : ℝ → ℝ | ∃ C, ∀ x ∈ branch, F x = p x + C}

theorem gap1 (x : ℝ) : integrand x = 1 - remainder x := by
  unfold integrand remainder
  have hden : 1 + Real.sin x ^ 2 ≠ 0 := by positivity
  field_simp [hden] <;> ring
theorem gap2 (x : ℝ) (hx : x ∈ branch) :
    integrand x = 1 - firstTanRemainder x := by
  have hx' : x ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    simpa [branch] using hx
  have hcospos : 0 < Real.cos x := Real.cos_pos_of_mem_Ioo hx'
  have hcos : Real.cos x ≠ 0 := hcospos.ne'
  have hderiv : deriv Real.tan x = 1 / Real.cos x ^ 2 :=
    (Real.hasDerivAt_tan hcos).deriv
  have hbase : 1 + Real.sin x ^ 2 ≠ 0 := by positivity
  have hfirst : firstTanRemainder x = remainder x := by
    dsimp [firstTanRemainder, remainder]
    rw [hderiv, Real.tan_eq_sin_div_cos]
    have hdeneq :
        1 / Real.cos x ^ 2 + (Real.sin x / Real.cos x) ^ 2 =
          (1 + Real.sin x ^ 2) / Real.cos x ^ 2 := by
      field_simp [hcos] <;> ring
    rw [hdeneq]
    field_simp [hcos, hbase] <;> ring
  rw [gap1, hfirst]
theorem gap3 (x : ℝ) (hx : x ∈ branch) :
    integrand x = 1 - secondTanRemainder x := by
  have hx' : x ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    simpa [branch] using hx
  have hcospos : 0 < Real.cos x := Real.cos_pos_of_mem_Ioo hx'
  have hcos : Real.cos x ≠ 0 := hcospos.ne'
  have hderiv : deriv Real.tan x = 1 / Real.cos x ^ 2 :=
    (Real.hasDerivAt_tan hcos).deriv
  have hbase : 1 + Real.sin x ^ 2 ≠ 0 := by positivity
  have hsecond : secondTanRemainder x = remainder x := by
    dsimp [secondTanRemainder, remainder]
    rw [hderiv, Real.tan_eq_sin_div_cos]
    have hdeneq :
        1 + 2 * (Real.sin x / Real.cos x) ^ 2 =
          (1 + Real.sin x ^ 2) / Real.cos x ^ 2 := by
      field_simp [hcos]
      nlinarith [Real.sin_sq_add_cos_sq x]
    rw [hdeneq]
    field_simp [hcos, hbase] <;> ring
  rw [gap1, hsecond]
theorem gap4 : Family integrand = Translates primitive := by
  have hopen : IsOpen branch := by
    simpa [branch] using (isOpen_Ioo : IsOpen (Set.Ioo (-(Real.pi / 2)) (Real.pi / 2)))
  have hpre : IsPreconnected branch := by
    simpa [branch] using
      (isPreconnected_Ioo : IsPreconnected (Set.Ioo (-(Real.pi / 2)) (Real.pi / 2)))
  have hprimitive : ∀ x ∈ branch, HasDerivAt primitive (integrand x) x := by
    intro x hx
    have hx' : x ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
      simpa [branch] using hx
    have hcospos : 0 < Real.cos x := Real.cos_pos_of_mem_Ioo hx'
    have hcos : Real.cos x ≠ 0 := hcospos.ne'
    have hsqrt : Real.sqrt 2 ≠ 0 :=
      (Real.sqrt_pos.2 (by norm_num)).ne'
    have hsqrt_sq : Real.sqrt 2 ^ 2 = 2 :=
      Real.sq_sqrt (by norm_num)
    have hpow : (Real.sqrt 2 * Real.tan x) ^ 2 = 2 * Real.tan x ^ 2 := by
      calc
        (Real.sqrt 2 * Real.tan x) ^ 2 =
            Real.sqrt 2 ^ 2 * Real.tan x ^ 2 := by ring
        _ = 2 * Real.tan x ^ 2 := by rw [hsqrt_sq]
    have hden : 1 + 2 * Real.tan x ^ 2 ≠ 0 := by positivity
    have hscale :
        1 / Real.sqrt 2 *
            (1 / (1 + (Real.sqrt 2 * Real.tan x) ^ 2) *
              (Real.sqrt 2 * (1 / Real.cos x ^ 2))) =
          secondTanRemainder x := by
      dsimp [secondTanRemainder]
      rw [(Real.hasDerivAt_tan hcos).deriv, hpow]
      field_simp [hsqrt, hden, hcos] <;> ring
    have hraw0 :=
      (hasDerivAt_id x).sub
        (((Real.hasDerivAt_arctan (Real.sqrt 2 * Real.tan x)).comp x
          ((Real.hasDerivAt_tan hcos).const_mul (Real.sqrt 2))).const_mul
            (1 / Real.sqrt 2))
    simp only [Function.comp_apply] at hraw0
    have hfun :
        ((id : ℝ → ℝ) - fun y : ℝ =>
          1 / Real.sqrt 2 * Real.arctan (Real.sqrt 2 * Real.tan y)) =
          primitive := by
      funext y
      rfl
    rw [hfun] at hraw0
    have hraw : HasDerivAt primitive
        (1 - 1 / Real.sqrt 2 *
          (1 / (1 + (Real.sqrt 2 * Real.tan x) ^ 2) *
            (Real.sqrt 2 * (1 / Real.cos x ^ 2)))) x := by
      simpa using hraw0
    rw [hscale] at hraw
    rw [← gap3 x hx] at hraw
    exact hraw
  apply Set.ext
  intro F
  constructor
  · intro hF
    change ∀ x ∈ branch, HasDerivAt F (integrand x) x at hF
    change ∃ C, ∀ x ∈ branch, F x = primitive x + C
    have hzero : (0 : ℝ) ∈ branch := by
      rw [branch]
      constructor <;> nlinarith [Real.pi_pos]
    have hgdiff : DifferentiableOn ℝ (fun y => F y - primitive y) branch := by
      intro y hy
      simpa using
        (((hF y hy).sub (hprimitive y hy)).differentiableAt.differentiableWithinAt)
    have hgderiv : ∀ y ∈ branch, deriv (fun z => F z - primitive z) y = 0 := by
      intro y hy
      simpa using (((hF y hy).sub (hprimitive y hy)).deriv)
    refine ⟨F 0 - primitive 0, ?_⟩
    intro x hx
    have heq : F x - primitive x = F 0 - primitive 0 :=
      hopen.is_const_of_deriv_eq_zero hpre hgdiff hgderiv hx hzero
    linarith
  · intro hF
    change ∃ C, ∀ x ∈ branch, F x = primitive x + C at hF
    change ∀ x ∈ branch, HasDerivAt F (integrand x) x
    obtain ⟨C, hC⟩ := hF
    intro x hx
    have hpc : HasDerivAt (fun y => primitive y + C) (integrand x) x :=
      (hprimitive x hx).add_const C
    have heq : F =ᶠ[nhds x] (fun y => primitive y + C) := by
      filter_upwards [hopen.mem_nhds hx] with y hy
      exact hC y hy
    exact hpc.congr_of_eventuallyEq heq

end
end ProofGap.Exercise2029
