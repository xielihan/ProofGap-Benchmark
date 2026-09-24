import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise1707

noncomputable section

def branch : Set ℝ := Set.univ
def integrand (x : ℝ) :=
  Real.sinh x * Real.cosh x /
    Real.sqrt ((Real.sinh x) ^ 4 + (Real.cosh x) ^ 4)
def doubledCosh (x : ℝ) := Real.cosh (2 * x)
def substitutedIntegrand (x : ℝ) :=
  ((1 / 4 : ℝ) * deriv doubledCosh x) /
    ((1 / Real.sqrt 2) * Real.sqrt (1 + (Real.cosh (2 * x)) ^ 2))
def primitive₁ (x : ℝ) :=
  1 / (2 * Real.sqrt 2) *
    Real.log
      (Real.cosh (2 * x) + Real.sqrt (1 + (Real.cosh (2 * x)) ^ 2))
def primitive₂ (x : ℝ) :=
  1 / (2 * Real.sqrt 2) *
    Real.log
      (Real.cosh (2 * x) / Real.sqrt 2 +
        Real.sqrt ((Real.sinh x) ^ 4 + (Real.cosh x) ^ 4))
def AntiderivativesOn (f : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∀ x ∈ branch, HasDerivAt F (f x) x}
def PrimitiveFamily (p : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x ∈ branch, F x = p x + C}

private theorem sqrt_div_two (a : ℝ) (ha : 0 ≤ a) :
    Real.sqrt (a / 2) = (1 / Real.sqrt 2) * Real.sqrt a := by
  have hrpos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hr2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hu : 0 ≤ Real.sqrt (a / 2) := Real.sqrt_nonneg _
  have hv : 0 ≤ Real.sqrt a := Real.sqrt_nonneg _
  have hu2 : (Real.sqrt (a / 2)) ^ 2 = a / 2 :=
    Real.sq_sqrt (div_nonneg ha (by norm_num))
  have hv2 : (Real.sqrt a) ^ 2 = a := Real.sq_sqrt ha
  have hp : 0 ≤ Real.sqrt 2 * Real.sqrt (a / 2) :=
    mul_nonneg hrpos.le hu
  have hs :
      (Real.sqrt 2 * Real.sqrt (a / 2)) ^ 2 = (Real.sqrt a) ^ 2 := by
    rw [mul_pow, hr2, hu2, hv2]
    ring
  have heq : Real.sqrt 2 * Real.sqrt (a / 2) = Real.sqrt a := by
    nlinarith
  have hh : Real.sqrt (a / 2) = Real.sqrt a / Real.sqrt 2 :=
    (eq_div_iff hrpos.ne').2 (by simpa [mul_comm] using heq)
  simpa [div_eq_mul_inv, mul_comm] using hh

private theorem hasDerivAt_doubledCosh (x : ℝ) :
    HasDerivAt doubledCosh (2 * Real.sinh (2 * x)) x := by
  unfold doubledCosh
  convert (Real.hasDerivAt_cosh (2 * x)).comp x
    ((hasDerivAt_const x 2).mul (hasDerivAt_id x)) using 1 <;> ring

private theorem hasDerivAt_primitive₁ (x : ℝ) :
    HasDerivAt primitive₁ (substitutedIntegrand x) x := by
  have hc : HasDerivAt (fun y : ℝ => Real.cosh (2 * y))
      (2 * Real.sinh (2 * x)) x := hasDerivAt_doubledCosh x
  have hi : HasDerivAt
      (fun y : ℝ => 1 + (Real.cosh (2 * y)) ^ 2)
      (4 * Real.cosh (2 * x) * Real.sinh (2 * x)) x := by
    convert (hc.pow 2).const_add 1 using 1 <;> ring
  have hs : HasDerivAt
      (fun y : ℝ => Real.sqrt (1 + (Real.cosh (2 * y)) ^ 2))
      ((4 * Real.cosh (2 * x) * Real.sinh (2 * x)) /
        (2 * Real.sqrt (1 + (Real.cosh (2 * x)) ^ 2))) x := by
    convert (Real.hasDerivAt_sqrt (by positivity :
      1 + (Real.cosh (2 * x)) ^ 2 ≠ 0)).comp x hi using 1 <;> ring
  have hsum : HasDerivAt
      (fun y : ℝ => Real.cosh (2 * y) +
        Real.sqrt (1 + (Real.cosh (2 * y)) ^ 2))
      (2 * Real.sinh (2 * x) +
        (4 * Real.cosh (2 * x) * Real.sinh (2 * x)) /
          (2 * Real.sqrt (1 + (Real.cosh (2 * x)) ^ 2))) x := by
    simpa only [Pi.add_apply] using hc.add hs
  have hvpos : 0 < Real.sqrt (1 + (Real.cosh (2 * x)) ^ 2) :=
    Real.sqrt_pos.2 (by positivity)
  have hargpos :
      0 < Real.cosh (2 * x) +
        Real.sqrt (1 + (Real.cosh (2 * x)) ^ 2) :=
    add_pos (Real.cosh_pos _) hvpos
  have hlog : HasDerivAt
      (fun y : ℝ => Real.log
        (Real.cosh (2 * y) +
          Real.sqrt (1 + (Real.cosh (2 * y)) ^ 2)))
      ((2 * Real.sinh (2 * x) +
          (4 * Real.cosh (2 * x) * Real.sinh (2 * x)) /
            (2 * Real.sqrt (1 + (Real.cosh (2 * x)) ^ 2))) /
        (Real.cosh (2 * x) +
          Real.sqrt (1 + (Real.cosh (2 * x)) ^ 2))) x := by
    simpa only [Pi.add_apply, div_eq_mul_inv, mul_comm] using
      (Real.hasDerivAt_log hargpos.ne').comp x hsum
  have hlog' : HasDerivAt
      (fun y : ℝ => Real.log
        (Real.cosh (2 * y) +
          Real.sqrt (1 + (Real.cosh (2 * y)) ^ 2)))
      (2 * Real.sinh (2 * x) /
        Real.sqrt (1 + (Real.cosh (2 * x)) ^ 2)) x := by
    convert hlog using 1
    field_simp [hvpos.ne', hargpos.ne']
    ring
  unfold primitive₁
  have hp := hlog'.const_mul (1 / (2 * Real.sqrt 2))
  have hrpos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hr2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hcoef : 1 / (2 * Real.sqrt 2) = Real.sqrt 2 / 4 := by
    field_simp [hrpos.ne']
    nlinarith [hr2]
  have hinv : 1 / Real.sqrt 2 = Real.sqrt 2 / 2 := by
    field_simp [hrpos.ne']
    nlinarith [hr2]
  convert hp using 1
  unfold substitutedIntegrand
  rw [(hasDerivAt_doubledCosh x).deriv, hcoef, hinv]
  field_simp [hrpos.ne', hvpos.ne']
  ring_nf
  rw [hr2]

private theorem constant_of_hasDerivAt_zero
    (g : ℝ → ℝ) (hg : ∀ x : ℝ, HasDerivAt g 0 x) (x : ℝ) :
    g x = g 0 := by
  have hdiff : Differentiable ℝ g := fun y => (hg y).differentiableAt
  have hderiv : ∀ y : ℝ, deriv g y = 0 := fun y => (hg y).deriv
  exact is_const_of_deriv_eq_zero hdiff hderiv x 0

theorem gap1 (x : ℝ) :
    (Real.sinh x) ^ 4 + (Real.cosh x) ^ 4 =
      ((Real.sinh x) ^ 2 + (Real.cosh x) ^ 2) ^ 2 -
        2 * (Real.sinh x) ^ 2 * (Real.cosh x) ^ 2 := by
  ring
theorem gap2 (x : ℝ) :
    ((Real.sinh x) ^ 2 + (Real.cosh x) ^ 2) ^ 2 -
        2 * (Real.sinh x) ^ 2 * (Real.cosh x) ^ 2 =
      (Real.cosh (2 * x)) ^ 2 - (1 / 2 : ℝ) * (Real.sinh (2 * x)) ^ 2 := by
  rw [show 2 * x = x + x by ring, Real.cosh_add, Real.sinh_add]
  ring
theorem gap3 (x : ℝ) :
    (Real.cosh (2 * x)) ^ 2 - (1 / 2 : ℝ) * (Real.sinh (2 * x)) ^ 2 =
      (1 + (Real.cosh (2 * x)) ^ 2) / 2 := by
  nlinarith [Real.cosh_sq_sub_sinh_sq (2 * x)]
theorem gap4 (x : ℝ) :
    (Real.sinh x) ^ 4 + (Real.cosh x) ^ 4 =
      (1 + (Real.cosh (2 * x)) ^ 2) / 2 := by
  calc
    (Real.sinh x) ^ 4 + (Real.cosh x) ^ 4 =
        ((Real.sinh x) ^ 2 + (Real.cosh x) ^ 2) ^ 2 -
          2 * (Real.sinh x) ^ 2 * (Real.cosh x) ^ 2 := gap1 x
    _ = (Real.cosh (2 * x)) ^ 2 -
          (1 / 2 : ℝ) * (Real.sinh (2 * x)) ^ 2 := gap2 x
    _ = (1 + (Real.cosh (2 * x)) ^ 2) / 2 := gap3 x
theorem gap5 :
    AntiderivativesOn integrand =
      AntiderivativesOn substitutedIntegrand := by
  apply congrArg AntiderivativesOn
  funext x
  have hsqrt := congrArg Real.sqrt (gap4 x)
  rw [sqrt_div_two (1 + (Real.cosh (2 * x)) ^ 2) (by positivity)] at hsqrt
  have hsinh : Real.sinh (2 * x) = 2 * Real.sinh x * Real.cosh x := by
    rw [show 2 * x = x + x by ring, Real.sinh_add]
    ring
  unfold integrand substitutedIntegrand
  rw [(hasDerivAt_doubledCosh x).deriv, hsinh, hsqrt]
  ring
theorem gap6 :
    AntiderivativesOn substitutedIntegrand = PrimitiveFamily primitive₁ := by
  ext F
  simp only [AntiderivativesOn, PrimitiveFamily, Set.mem_setOf_eq]
  constructor
  · intro hF
    refine ⟨F 0 - primitive₁ 0, ?_⟩
    intro x hx
    have hz : ∀ y : ℝ, HasDerivAt (fun z => F z - primitive₁ z) 0 y := by
      intro y
      convert (hF y (by simp [branch])).sub (hasDerivAt_primitive₁ y) using 1
      ring
    have hc := constant_of_hasDerivAt_zero
      (fun z => F z - primitive₁ z) hz x
    change F x - primitive₁ x = F 0 - primitive₁ 0 at hc
    linarith
  · rintro ⟨C, hC⟩
    have hfun : F = fun x => primitive₁ x + C := by
      funext x
      exact hC x (by simp [branch])
    intro x hx
    rw [hfun]
    simpa only [add_comm] using (hasDerivAt_primitive₁ x).const_add C
theorem gap7 :
    AntiderivativesOn integrand = PrimitiveFamily primitive₁ := by
  rw [gap5, gap6]
theorem gap8 :
    AntiderivativesOn integrand = PrimitiveFamily primitive₂ := by
  rw [gap7]
  have hrel : ∀ x : ℝ,
      primitive₂ x = primitive₁ x -
        1 / (2 * Real.sqrt 2) * Real.log (Real.sqrt 2) := by
    intro x
    have hsqrt := congrArg Real.sqrt (gap4 x)
    rw [sqrt_div_two (1 + (Real.cosh (2 * x)) ^ 2) (by positivity)] at hsqrt
    have harg :
        Real.cosh (2 * x) / Real.sqrt 2 +
            (1 / Real.sqrt 2) *
              Real.sqrt (1 + (Real.cosh (2 * x)) ^ 2) =
          (Real.cosh (2 * x) +
              Real.sqrt (1 + (Real.cosh (2 * x)) ^ 2)) /
            Real.sqrt 2 := by
      ring
    have hrpos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
    have hvpos : 0 < Real.sqrt (1 + (Real.cosh (2 * x)) ^ 2) :=
      Real.sqrt_pos.2 (by positivity)
    have hargpos :
        0 < Real.cosh (2 * x) +
          Real.sqrt (1 + (Real.cosh (2 * x)) ^ 2) :=
      add_pos (Real.cosh_pos _) hvpos
    unfold primitive₁ primitive₂
    rw [hsqrt, harg, Real.log_div hargpos.ne' hrpos.ne']
    ring
  ext F
  simp only [PrimitiveFamily, Set.mem_setOf_eq]
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨C + 1 / (2 * Real.sqrt 2) * Real.log (Real.sqrt 2), ?_⟩
    intro x hx
    rw [hC x hx, hrel x]
    ring
  · rintro ⟨C, hC⟩
    refine ⟨C - 1 / (2 * Real.sqrt 2) * Real.log (Real.sqrt 2), ?_⟩
    intro x hx
    rw [hC x hx, hrel x]
    ring

end
end ProofGap.Exercise1707
