import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise2003

noncomputable section

def branch : Set ℝ := {x | Real.sin x ≠ 0 ∧ Real.cos x ≠ 0}
def originalIntegrand (x : ℝ) :=
  1 / (Real.sin x * Real.cos x ^ 4)
def identityIntegrand (x : ℝ) :=
  (Real.sin x ^ 2 + Real.cos x ^ 2) /
    (Real.sin x * Real.cos x ^ 4)
def firstPart (x : ℝ) := Real.sin x / Real.cos x ^ 4
def secondPart (x : ℝ) := 1 / (Real.sin x * Real.cos x ^ 2)
def d₁ (x : ℝ) := deriv Real.cos x / Real.cos x ^ 4
def d₂ (x : ℝ) := Real.sin x / Real.cos x ^ 2
def d₃ (x : ℝ) := 1 / Real.sin x
def residual (x : ℝ) := deriv Real.cos x / Real.cos x ^ 2
def primitive (x : ℝ) :=
  1 / (3 * Real.cos x ^ 3) + 1 / Real.cos x +
    Real.log |Real.tan (x / 2)|
def Antiderivatives (f : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∀ x ∈ branch, HasDerivAt F (f x) x}
def SplitFamily : Set (ℝ → ℝ) :=
  {F | ∃ G ∈ Antiderivatives firstPart,
    ∃ H ∈ Antiderivatives secondPart,
      ∀ x ∈ branch, F x = G x + H x}
def ThreeTermFamily : Set (ℝ → ℝ) :=
  {F | ∃ G ∈ Antiderivatives d₁,
    ∃ H ∈ Antiderivatives d₂,
    ∃ K ∈ Antiderivatives d₃,
      ∀ x ∈ branch, F x = -G x + H x + K x}
def ReducedFamily : Set (ℝ → ℝ) :=
  {F | ∃ G ∈ Antiderivatives residual,
    ∀ x ∈ branch,
      F x =
        1 / (3 * Real.cos x ^ 3) - G x +
          Real.log |Real.tan (x / 2)|}
def ComponentwisePrimitiveFamily : Set (ℝ → ℝ) :=
  {F | ∃ K : ℝ → ℝ,
    (∀ x ∈ branch, F x = primitive x + K x) ∧
    (∀ x ∈ branch, HasDerivAt K 0 x)}

private theorem branch_isOpen : IsOpen branch := by
  have hs : IsOpen (Real.sin ⁻¹' ({0} : Set ℝ)ᶜ) :=
    isClosed_singleton.isOpen_compl.preimage Real.continuous_sin
  have hc : IsOpen (Real.cos ⁻¹' ({0} : Set ℝ)ᶜ) :=
    isClosed_singleton.isOpen_compl.preimage Real.continuous_cos
  simpa [branch] using hs.inter hc

private theorem hasDerivAt_congr_on_branch
    {F G : ℝ → ℝ} {d x : ℝ} (hx : x ∈ branch)
    (hFG : ∀ y ∈ branch, F y = G y) (hG : HasDerivAt G d x) :
    HasDerivAt F d x := by
  apply hG.congr_of_eventuallyEq
  filter_upwards [branch_isOpen.mem_nhds hx] with y hy
  exact hFG y hy

private theorem identity_eq_original (x : ℝ) (hx : x ∈ branch) :
    identityIntegrand x = originalIntegrand x := by
  unfold identityIntegrand originalIntegrand
  rw [Real.sin_sq_add_cos_sq]

private theorem identity_eq_split (x : ℝ) (hx : x ∈ branch) :
    identityIntegrand x = firstPart x + secondPart x := by
  rcases hx with ⟨hs, hc⟩
  unfold identityIntegrand firstPart secondPart
  field_simp [hs, hc]

private theorem original_eq_components (x : ℝ) (hx : x ∈ branch) :
    originalIntegrand x = firstPart x + d₂ x + d₃ x := by
  rcases hx with ⟨hs, hc⟩
  unfold originalIntegrand firstPart d₂ d₃
  have htrig := Real.sin_sq_add_cos_sq x
  field_simp [hs, hc]
  ring_nf
  nlinarith

private theorem d₁_eq_neg_firstPart (x : ℝ) :
    d₁ x = -firstPart x := by
  unfold d₁ firstPart
  rw [(Real.hasDerivAt_cos x).deriv]
  ring

private theorem residual_eq_neg_d₂ (x : ℝ) :
    residual x = -d₂ x := by
  unfold residual d₂
  rw [(Real.hasDerivAt_cos x).deriv]
  ring

private theorem hasDerivAt_firstPrimitive (x : ℝ) (hc : Real.cos x ≠ 0) :
    HasDerivAt (fun y : ℝ => 1 / (3 * Real.cos y ^ 3)) (firstPart x) x := by
  have h :=
    (hasDerivAt_const x (1 : ℝ)).div
      ((hasDerivAt_const x (3 : ℝ)).mul ((Real.hasDerivAt_cos x).pow 3))
      (mul_ne_zero (by norm_num) (pow_ne_zero 3 hc))
  convert h using 1 <;> simp [firstPart] <;> field_simp [hc] <;> ring

private theorem hasDerivAt_d₁Primitive (x : ℝ) (hc : Real.cos x ≠ 0) :
    HasDerivAt (fun y : ℝ => -(1 / (3 * Real.cos y ^ 3))) (d₁ x) x := by
  have h := (hasDerivAt_firstPrimitive x hc).neg
  convert h using 1
  exact d₁_eq_neg_firstPart x

private theorem hasDerivAt_d₂Primitive (x : ℝ) (hc : Real.cos x ≠ 0) :
    HasDerivAt (fun y : ℝ => 1 / Real.cos y) (d₂ x) x := by
  have h := (hasDerivAt_const x (1 : ℝ)).div (Real.hasDerivAt_cos x) hc
  convert h using 1 <;> unfold d₂ <;> field_simp [hc] <;> ring

private theorem hasDerivAt_d₃Primitive (x : ℝ) (hx : x ∈ branch) :
    HasDerivAt (fun y : ℝ => Real.log |Real.tan (y / 2)|) (d₃ x) x := by
  rcases hx with ⟨hs, hc⟩
  have hsin_half : Real.sin (x / 2) ≠ 0 := by
    intro h
    apply hs
    rw [show x = 2 * (x / 2) by ring, Real.sin_two_mul, h]
    ring
  have hcos_half : Real.cos (x / 2) ≠ 0 := by
    intro h
    apply hs
    rw [show x = 2 * (x / 2) by ring, Real.sin_two_mul, h]
    ring
  have htan : Real.tan (x / 2) ≠ 0 := by
    rw [Real.tan_eq_sin_div_cos]
    exact div_ne_zero hsin_half hcos_half
  have ht :
      HasDerivAt (fun y : ℝ => Real.tan (y / 2))
        ((1 / Real.cos (x / 2) ^ 2) * (1 / 2)) x := by
    simpa only [Function.comp_apply] using
      (Real.hasDerivAt_tan hcos_half).comp x
        ((hasDerivAt_id x).div_const 2)
  have hl := ht.log htan
  have hlabs :
      HasDerivAt (fun y : ℝ => Real.log |Real.tan (y / 2)|)
        (((1 / Real.cos (x / 2) ^ 2) * (1 / 2)) / Real.tan (x / 2)) x := by
    simpa only [Real.log_abs] using hl
  have hsin_double :
      Real.sin x = 2 * Real.sin (x / 2) * Real.cos (x / 2) := by
    calc
      Real.sin x = Real.sin (2 * (x / 2)) :=
        congrArg Real.sin (by ring)
      _ = 2 * Real.sin (x / 2) * Real.cos (x / 2) :=
        Real.sin_two_mul (x / 2)
  convert hlabs using 1
  unfold d₃
  rw [Real.tan_eq_sin_div_cos, hsin_double]
  field_simp [hsin_half, hcos_half]
  <;> ring

private theorem hasDerivAt_primitive (x : ℝ) (hx : x ∈ branch) :
    HasDerivAt primitive (originalIntegrand x) x := by
  have h :=
    ((hasDerivAt_firstPrimitive x hx.2).add (hasDerivAt_d₂Primitive x hx.2)).add
      (hasDerivAt_d₃Primitive x hx)
  convert h using 1
  exact original_eq_components x hx

private theorem antiderivatives_original_eq_reduced :
    Antiderivatives originalIntegrand = ReducedFamily := by
  ext F
  change
    (∀ x ∈ branch, HasDerivAt F (originalIntegrand x) x) ↔
      ∃ G, (∀ x ∈ branch, HasDerivAt G (residual x) x) ∧
        ∀ x ∈ branch,
          F x = 1 / (3 * Real.cos x ^ 3) - G x +
            Real.log |Real.tan (x / 2)|
  constructor
  · intro hF
    refine ⟨(fun y =>
      1 / (3 * Real.cos y ^ 3) + Real.log |Real.tan (y / 2)| - F y), ?_, ?_⟩
    · intro x hx
      have h :=
        ((hasDerivAt_firstPrimitive x hx.2).add (hasDerivAt_d₃Primitive x hx)).sub
          (hF x hx)
      convert h using 1
      rw [original_eq_components x hx, residual_eq_neg_d₂ x]
      ring
    · intro x hx
      ring
  · rintro ⟨G, hG, hEq⟩
    intro x hx
    have h :=
      ((hasDerivAt_firstPrimitive x hx.2).sub (hG x hx)).add
        (hasDerivAt_d₃Primitive x hx)
    have h' :
        HasDerivAt
          (fun y => 1 / (3 * Real.cos y ^ 3) - G y +
            Real.log |Real.tan (y / 2)|)
          (originalIntegrand x) x := by
      convert h using 1
      rw [residual_eq_neg_d₂ x, original_eq_components x hx]
      ring
    exact hasDerivAt_congr_on_branch hx hEq h'

theorem gap1 :
    Antiderivatives originalIntegrand =
      Antiderivatives identityIntegrand := by
  ext F
  change
    (∀ x ∈ branch, HasDerivAt F (originalIntegrand x) x) ↔
      ∀ x ∈ branch, HasDerivAt F (identityIntegrand x) x
  constructor
  · intro hF x hx
    simpa only [identity_eq_original x hx] using hF x hx
  · intro hF x hx
    simpa only [identity_eq_original x hx] using hF x hx
theorem gap2 :
    Antiderivatives identityIntegrand = SplitFamily := by
  ext F
  change
    (∀ x ∈ branch, HasDerivAt F (identityIntegrand x) x) ↔
      ∃ G, (∀ x ∈ branch, HasDerivAt G (firstPart x) x) ∧
        ∃ H, (∀ x ∈ branch, HasDerivAt H (secondPart x) x) ∧
          ∀ x ∈ branch, F x = G x + H x
  constructor
  · intro hF
    refine ⟨(fun y => 1 / (3 * Real.cos y ^ 3)), ?_,
      (fun y => F y - 1 / (3 * Real.cos y ^ 3)), ?_, ?_⟩
    · intro x hx
      exact hasDerivAt_firstPrimitive x hx.2
    · intro x hx
      have h := (hF x hx).sub (hasDerivAt_firstPrimitive x hx.2)
      convert h using 1
      rw [identity_eq_split x hx]
      ring
    · intro x hx
      ring
  · rintro ⟨G, hG, H, hH, hEq⟩
    intro x hx
    have hsum := (hG x hx).add (hH x hx)
    have hsum' :
        HasDerivAt (fun y => G y + H y) (identityIntegrand x) x := by
      convert hsum using 1
      rw [identity_eq_split x hx]
    exact hasDerivAt_congr_on_branch hx hEq hsum'
theorem gap3 :
    Antiderivatives originalIntegrand = SplitFamily := by
  exact gap1.trans gap2
theorem gap4 :
    Antiderivatives originalIntegrand = ThreeTermFamily := by
  ext F
  change
    (∀ x ∈ branch, HasDerivAt F (originalIntegrand x) x) ↔
      ∃ G, (∀ x ∈ branch, HasDerivAt G (d₁ x) x) ∧
        ∃ H, (∀ x ∈ branch, HasDerivAt H (d₂ x) x) ∧
          ∃ K, (∀ x ∈ branch, HasDerivAt K (d₃ x) x) ∧
            ∀ x ∈ branch, F x = -G x + H x + K x
  constructor
  · intro hF
    refine ⟨(fun y => -(1 / (3 * Real.cos y ^ 3))), ?_,
      (fun y => 1 / Real.cos y), ?_,
      (fun y => F y + (-(1 / (3 * Real.cos y ^ 3))) - 1 / Real.cos y), ?_, ?_⟩
    · intro x hx
      exact hasDerivAt_d₁Primitive x hx.2
    · intro x hx
      exact hasDerivAt_d₂Primitive x hx.2
    · intro x hx
      have h := ((hF x hx).add (hasDerivAt_d₁Primitive x hx.2)).sub
        (hasDerivAt_d₂Primitive x hx.2)
      convert h using 1
      rw [original_eq_components x hx, d₁_eq_neg_firstPart x]
      ring
    · intro x hx
      ring
  · rintro ⟨G, hG, H, hH, K, hK, hEq⟩
    intro x hx
    have hsum := ((hG x hx).neg.add (hH x hx)).add (hK x hx)
    have hsum' :
        HasDerivAt (fun y => -G y + H y + K y) (originalIntegrand x) x := by
      convert hsum using 1
      rw [d₁_eq_neg_firstPart x, original_eq_components x hx]
      ring
    exact hasDerivAt_congr_on_branch hx hEq hsum'
theorem gap5 :
    ThreeTermFamily = ReducedFamily := by
  calc
    ThreeTermFamily = Antiderivatives originalIntegrand := gap4.symm
    _ = ReducedFamily := antiderivatives_original_eq_reduced
theorem gap6 :
    Antiderivatives originalIntegrand = ReducedFamily := by
  exact antiderivatives_original_eq_reduced
theorem gap7 :
    Antiderivatives originalIntegrand =
      ComponentwisePrimitiveFamily := by
  ext F
  change
    (∀ x ∈ branch, HasDerivAt F (originalIntegrand x) x) ↔
      ∃ K : ℝ → ℝ,
        (∀ x ∈ branch, F x = primitive x + K x) ∧
          ∀ x ∈ branch, HasDerivAt K 0 x
  constructor
  · intro hF
    refine ⟨(fun y => F y - primitive y), ?_, ?_⟩
    · intro x hx
      ring
    · intro x hx
      have h := (hF x hx).sub (hasDerivAt_primitive x hx)
      convert h using 1
      ring
  · rintro ⟨K, hEq, hK⟩
    intro x hx
    have hsum := (hasDerivAt_primitive x hx).add (hK x hx)
    have hsum' :
        HasDerivAt (fun y => primitive y + K y) (originalIntegrand x) x := by
      convert hsum using 1
      ring
    exact hasDerivAt_congr_on_branch hx hEq hsum'

end
end ProofGap.Exercise2003
