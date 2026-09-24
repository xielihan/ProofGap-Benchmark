import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise2102
noncomputable section

def asinhForm (x : ℝ) := Real.log (x + Real.sqrt (1 + x ^ 2))
def integrand (x : ℝ) := asinhForm x ^ 2
def auxiliary₁ (x : ℝ) := x / Real.sqrt (1 + x ^ 2) * asinhForm x
def auxiliary₂ (x : ℝ) :=
  asinhForm x * deriv (fun y : ℝ => Real.sqrt (1 + y ^ 2)) x
def primitive (x : ℝ) :=
  x * asinhForm x ^ 2 -
    2 * Real.sqrt (1 + x ^ 2) * asinhForm x + 2 * x

def Family (f : ℝ → ℝ) :=
  {F : ℝ → ℝ | ∀ x, HasDerivAt F (f x) x}
def ByPartsFamily (f : ℝ → ℝ) :=
  {F : ℝ → ℝ | ∃ A ∈ Family f,
    ∀ x, F x = x * asinhForm x ^ 2 - 2 * A x}
def ExpandedFamily :=
  {F : ℝ → ℝ | ∃ A ∈ Family (fun _ => (1 : ℝ)),
    ∀ x, F x =
      x * asinhForm x ^ 2 -
        2 * Real.sqrt (1 + x ^ 2) * asinhForm x + 2 * A x}
def Translates (p : ℝ → ℝ) :=
  {F : ℝ → ℝ | ∃ C : ℝ, ∀ x, F x = p x + C}

private theorem one_add_sq_pos (x : ℝ) : 0 < 1 + x ^ 2 := by
  nlinarith [sq_nonneg x]

private theorem sqrt_one_add_sq_pos (x : ℝ) :
    0 < Real.sqrt (1 + x ^ 2) := by
  exact Real.sqrt_pos.2 (one_add_sq_pos x)

private theorem add_sqrt_one_add_sq_pos (x : ℝ) :
    0 < x + Real.sqrt (1 + x ^ 2) := by
  have hb := one_add_sq_pos x
  have hs0 := Real.sqrt_nonneg (1 + x ^ 2)
  have hs2 := Real.sq_sqrt (le_of_lt hb)
  by_contra h
  have hsum : x + Real.sqrt (1 + x ^ 2) ≤ 0 := le_of_not_gt h
  have hx : x ≤ 0 := by linarith
  have hp₁ : 0 ≤ x * (x + Real.sqrt (1 + x ^ 2)) :=
    mul_nonneg_of_nonpos_of_nonpos hx hsum
  have hp₂ : Real.sqrt (1 + x ^ 2) *
      (x + Real.sqrt (1 + x ^ 2)) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hs0 hsum
  nlinarith

private theorem hasDerivAt_sqrt_one_add_sq (x : ℝ) :
    HasDerivAt (fun y : ℝ => Real.sqrt (1 + y ^ 2))
      (x / Real.sqrt (1 + x ^ 2)) x := by
  have hb := one_add_sq_pos x
  have hs := sqrt_one_add_sq_pos x
  have hpoly : HasDerivAt (fun y : ℝ => 1 + y ^ 2) (2 * x) x := by
    convert
      ((hasDerivAt_const x (1 : ℝ)).add ((hasDerivAt_id x).pow 2)) using 1 <;>
      simp [mul_comm]
  have hraw :
      HasDerivAt (fun y : ℝ => Real.sqrt (1 + y ^ 2))
        ((1 / (2 * Real.sqrt (1 + x ^ 2))) * (2 * x)) x := by
    simpa only [Function.comp_apply] using
      ((Real.hasDerivAt_sqrt (ne_of_gt hb)).comp x hpoly)
  convert hraw using 1
  field_simp [ne_of_gt hs] <;> ring

private theorem hasDerivAt_asinhForm (x : ℝ) :
    HasDerivAt asinhForm (1 / Real.sqrt (1 + x ^ 2)) x := by
  have hs := sqrt_one_add_sq_pos x
  have hz := add_sqrt_one_add_sq_pos x
  have hinner :
      HasDerivAt (fun y : ℝ => y + Real.sqrt (1 + y ^ 2))
        (1 + x / Real.sqrt (1 + x ^ 2)) x :=
    (hasDerivAt_id x).add (hasDerivAt_sqrt_one_add_sq x)
  have hraw :
      HasDerivAt
        (fun y : ℝ => Real.log (y + Real.sqrt (1 + y ^ 2)))
        ((1 / (x + Real.sqrt (1 + x ^ 2))) *
          (1 + x / Real.sqrt (1 + x ^ 2))) x := by
    simpa only [Function.comp_apply, one_div] using
      ((Real.hasDerivAt_log (ne_of_gt hz)).comp x hinner)
  unfold asinhForm
  convert hraw using 1
  field_simp [ne_of_gt hs, ne_of_gt hz] <;> ring

private theorem hasDerivAt_sqrt_mul_asinh (x : ℝ) :
    HasDerivAt
      (fun y : ℝ => Real.sqrt (1 + y ^ 2) * asinhForm y)
      (auxiliary₁ x + 1) x := by
  have hraw := (hasDerivAt_sqrt_one_add_sq x).mul (hasDerivAt_asinhForm x)
  convert hraw using 1
  simp only [auxiliary₁]
  field_simp [ne_of_gt (sqrt_one_add_sq_pos x)] <;> ring

private theorem hasDerivAt_x_asinh_sq (x : ℝ) :
    HasDerivAt (fun y : ℝ => y * asinhForm y ^ 2)
      (integrand x + 2 * auxiliary₁ x) x := by
  have hraw :
      HasDerivAt (fun y : ℝ => y * asinhForm y ^ 2)
        (asinhForm x ^ 2 +
          x * (2 * asinhForm x * (1 / Real.sqrt (1 + x ^ 2)))) x := by
    simpa using (hasDerivAt_id x).mul ((hasDerivAt_asinhForm x).pow 2)
  convert hraw using 1
  simp only [integrand, auxiliary₁]
  field_simp [ne_of_gt (sqrt_one_add_sq_pos x)] <;> ring

theorem gap1 : Family integrand = ByPartsFamily auxiliary₁ := by
  apply Set.ext
  intro F
  constructor
  · intro hF
    refine ⟨fun x => (x * asinhForm x ^ 2 - F x) / 2, ?_, ?_⟩
    · intro x
      have hd := ((hasDerivAt_x_asinh_sq x).sub (hF x)).div_const 2
      convert hd using 1 <;> ring
    · intro x
      ring
  · rintro ⟨A, hA, hEq⟩
    intro x
    have htwoA := (hasDerivAt_const x (2 : ℝ)).mul (hA x)
    have hd := (hasDerivAt_x_asinh_sq x).sub htwoA
    have hF_eq : F = fun y => y * asinhForm y ^ 2 - 2 * A y :=
      funext fun y => hEq y
    rw [hF_eq]
    convert hd using 1 <;> ring
theorem gap2 : Family integrand = ByPartsFamily auxiliary₂ := by
  have haux : auxiliary₂ = auxiliary₁ := by
    funext x
    have hd := (hasDerivAt_sqrt_one_add_sq x).deriv
    simp only [auxiliary₂, auxiliary₁]
    rw [hd]
    ring
  rw [haux]
  exact gap1
theorem gap3 : Family integrand = ExpandedFamily := by
  rw [gap1]
  apply Set.ext
  intro F
  constructor
  · rintro ⟨A, hA, hEq⟩
    refine ⟨fun x => Real.sqrt (1 + x ^ 2) * asinhForm x - A x, ?_, ?_⟩
    · intro x
      convert (hasDerivAt_sqrt_mul_asinh x).sub (hA x) using 1 <;> ring
    · intro x
      rw [hEq x]
      ring
  · rintro ⟨B, hB, hEq⟩
    refine ⟨fun x => Real.sqrt (1 + x ^ 2) * asinhForm x - B x, ?_, ?_⟩
    · intro x
      convert (hasDerivAt_sqrt_mul_asinh x).sub (hB x) using 1 <;> ring
    · intro x
      rw [hEq x]
      ring
theorem gap4 : Family integrand = Translates primitive := by
  rw [gap3]
  apply Set.ext
  intro F
  constructor
  · rintro ⟨A, hA, hEq⟩
    have hzero : ∀ x, HasDerivAt (fun y : ℝ => A y - y) 0 x := by
      intro x
      convert (hA x).sub (hasDerivAt_id x) using 1 <;> ring
    have hdiff : Differentiable ℝ (fun y : ℝ => A y - y) :=
      fun x => (hzero x).differentiableAt
    have hderiv : ∀ x, deriv (fun y : ℝ => A y - y) x = 0 :=
      fun x => (hzero x).deriv
    refine ⟨2 * A 0, ?_⟩
    intro x
    have hc : (fun y : ℝ => A y - y) x = (fun y : ℝ => A y - y) 0 :=
      is_const_of_deriv_eq_zero hdiff hderiv x 0
    have hAx : A x = x + A 0 := by
      dsimp at hc
      linarith
    rw [hEq x]
    simp only [primitive]
    rw [hAx]
    ring
  · rintro ⟨C, hEq⟩
    refine ⟨fun x => x + C / 2, ?_, ?_⟩
    · intro x
      convert (hasDerivAt_id x).add (hasDerivAt_const x (C / 2)) using 1 <;> ring
    · intro x
      rw [hEq x]
      simp only [primitive]
      ring

end
end ProofGap.Exercise2102
