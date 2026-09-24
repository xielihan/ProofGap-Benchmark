import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise1801

noncomputable section

def branch : Set ℝ := Set.univ
def sinh3 (x : ℝ) := Real.sinh (3 * x)
def cosh3 (x : ℝ) := Real.cosh (3 * x)
def integrand (x : ℝ) := x ^ 3 * cosh3 x
def scaledDerivativeIntegrand (x : ℝ) := (1 / 3 : ℝ) * x ^ 3 * deriv sinh3 x
def residual₁ (x : ℝ) := x ^ 2 * sinh3 x
def residual₂ (x : ℝ) := x * cosh3 x
def residual₃ (x : ℝ) := sinh3 x
def rawResidual₂ (x : ℝ) := x ^ 2 * deriv cosh3 x
def rawResidual₃ (x : ℝ) := x * deriv sinh3 x
def boundary₁ (x : ℝ) := (1 / 3 : ℝ) * x ^ 3 * sinh3 x
def boundary₂ (x : ℝ) :=
  boundary₁ x - (1 / 3 : ℝ) * x ^ 2 * cosh3 x
def boundary₃ (x : ℝ) :=
  boundary₂ x + (2 / 9 : ℝ) * x * sinh3 x
def primitive (x : ℝ) :=
  (x ^ 3 / 3 + 2 * x / 9) * sinh3 x -
    (x ^ 2 / 3 + 2 / 27) * cosh3 x
def AntiderivativesOn (f : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∀ x ∈ branch, HasDerivAt F (f x) x}
def ByPartsFamily (b : ℝ → ℝ) (c : ℝ) (r : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ G ∈ AntiderivativesOn r, ∀ x ∈ branch, F x = b x + c * G x}
def PrimitiveFamily : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x ∈ branch, F x = primitive x + C}

private theorem hasDerivAt_sinh3 (x : ℝ) :
    HasDerivAt sinh3 (3 * cosh3 x) x := by
  unfold sinh3 cosh3
  convert (Real.hasDerivAt_sinh (3 * x)).comp x
    ((hasDerivAt_id x).const_mul 3) using 1 <;> ring

private theorem hasDerivAt_cosh3 (x : ℝ) :
    HasDerivAt cosh3 (3 * sinh3 x) x := by
  unfold sinh3 cosh3
  convert (Real.hasDerivAt_cosh (3 * x)).comp x
    ((hasDerivAt_id x).const_mul 3) using 1 <;> ring

private theorem scaledDerivativeIntegrand_eq_integrand (x : ℝ) :
    scaledDerivativeIntegrand x = integrand x := by
  unfold scaledDerivativeIntegrand integrand
  rw [(hasDerivAt_sinh3 x).deriv]
  ring

private theorem rawResidual₂_eq (x : ℝ) :
    rawResidual₂ x = 3 * residual₁ x := by
  unfold rawResidual₂ residual₁
  rw [(hasDerivAt_cosh3 x).deriv]
  ring

private theorem rawResidual₃_eq (x : ℝ) :
    rawResidual₃ x = 3 * residual₂ x := by
  unfold rawResidual₃ residual₂
  rw [(hasDerivAt_sinh3 x).deriv]
  ring

private theorem hasDerivAt_boundary₁ (x : ℝ) :
    HasDerivAt boundary₁ (integrand x + residual₁ x) x := by
  unfold boundary₁ integrand residual₁
  convert ((hasDerivAt_id x).pow 3).mul (hasDerivAt_sinh3 x) |>.const_mul (1 / 3 : ℝ) using 1 <;>
    simp only [Pi.pow_apply, Pi.mul_apply, id_eq] <;> ring

private theorem hasDerivAt_boundary₂ (x : ℝ) :
    HasDerivAt boundary₂ (integrand x - (2 / 3 : ℝ) * residual₂ x) x := by
  unfold boundary₂
  convert (hasDerivAt_boundary₁ x).sub
    ((((hasDerivAt_id x).pow 2).mul
      (hasDerivAt_cosh3 x)).const_mul (1 / 3 : ℝ)) using 1
  · funext y
    simp only [Pi.pow_apply, Pi.mul_apply, Pi.sub_apply, id_eq]
    ring
  · norm_num [integrand, residual₁, residual₂] <;> ring

private theorem hasDerivAt_boundary₃ (x : ℝ) :
    HasDerivAt boundary₃ (integrand x + (2 / 9 : ℝ) * residual₃ x) x := by
  unfold boundary₃
  convert (hasDerivAt_boundary₂ x).add
    ((((hasDerivAt_id x).mul
      (hasDerivAt_sinh3 x)).const_mul (2 / 9 : ℝ))) using 1
  · funext y
    simp only [Pi.mul_apply, Pi.add_apply, id_eq]
    ring
  · norm_num [integrand, residual₂, residual₃] <;> ring

private theorem primitive_eq_boundary₃ (x : ℝ) :
    primitive x = boundary₃ x - (2 / 27 : ℝ) * cosh3 x := by
  unfold primitive boundary₃ boundary₂ boundary₁
  ring

private theorem hasDerivAt_primitive (x : ℝ) :
    HasDerivAt primitive (integrand x) x := by
  have hfun : primitive = fun y => boundary₃ y - (2 / 27 : ℝ) * cosh3 y := by
    funext y
    exact primitive_eq_boundary₃ y
  rw [hfun]
  convert (hasDerivAt_boundary₃ x).sub
    ((hasDerivAt_cosh3 x).const_mul (2 / 27 : ℝ)) using 1 <;>
    unfold residual₃ <;> ring

private theorem antiderivativesOn_eq_byPartsFamily
    (f b r : ℝ → ℝ) (c : ℝ) (hc : c ≠ 0)
    (hb : ∀ x, HasDerivAt b (f x - c * r x) x) :
    AntiderivativesOn f = ByPartsFamily b c r := by
  apply Set.ext
  intro F
  simp only [AntiderivativesOn, ByPartsFamily, Set.mem_setOf_eq]
  constructor
  · intro hF
    let G : ℝ → ℝ := fun y => (1 / c) * (F y - b y)
    refine ⟨G, ?_, ?_⟩
    · intro x hx
      dsimp [G]
      convert ((hF x hx).sub (hb x)).const_mul (1 / c) using 1 <;>
        field_simp [hc] <;> ring
    · intro x hx
      dsimp [G]
      field_simp [hc]
      ring
  · rintro ⟨G, hG, hFG⟩
    have hfun : F = fun y => b y + c * G y := by
      funext y
      exact hFG y (by simp [branch])
    rw [hfun]
    intro x hx
    convert (hb x).add ((hG x hx).const_mul c) using 1 <;> ring

private theorem hasDerivAt_zero_is_constant (D : ℝ → ℝ)
    (hD : ∀ x, HasDerivAt D 0 x) : ∀ x, D x = D 0 := by
  have hdiff : Differentiable ℝ D := fun x => (hD x).differentiableAt
  have hderiv : ∀ x, deriv D x = 0 := fun x => (hD x).deriv
  intro x
  exact is_const_of_deriv_eq_zero hdiff hderiv x 0

theorem gap1 :
    AntiderivativesOn integrand =
      AntiderivativesOn scaledDerivativeIntegrand := by
  apply Set.ext
  intro F
  constructor
  · intro h x hx
    simpa only [scaledDerivativeIntegrand_eq_integrand] using h x hx
  · intro h x hx
    simpa only [scaledDerivativeIntegrand_eq_integrand] using h x hx
theorem gap2 :
    AntiderivativesOn scaledDerivativeIntegrand =
      ByPartsFamily boundary₁ (-1) residual₁ := by
  apply antiderivativesOn_eq_byPartsFamily
  · norm_num
  · intro x
    simpa only [scaledDerivativeIntegrand_eq_integrand, neg_one_mul,
      sub_neg_eq_add] using hasDerivAt_boundary₁ x
theorem gap3 :
    AntiderivativesOn integrand =
      ByPartsFamily boundary₁ (-1) residual₁ := by
  exact gap1.trans gap2
theorem gap4 :
    AntiderivativesOn integrand =
      ByPartsFamily boundary₁ (-1 / 3) rawResidual₂ := by
  apply antiderivativesOn_eq_byPartsFamily
  · norm_num
  · intro x
    convert hasDerivAt_boundary₁ x using 1
    rw [rawResidual₂_eq]
    ring
theorem gap5 :
    ByPartsFamily boundary₁ (-1 / 3) rawResidual₂ =
      ByPartsFamily boundary₂ (2 / 3) residual₂ := by
  calc
    ByPartsFamily boundary₁ (-1 / 3) rawResidual₂ =
        AntiderivativesOn integrand := gap4.symm
    _ = ByPartsFamily boundary₂ (2 / 3) residual₂ := by
      apply antiderivativesOn_eq_byPartsFamily
      · norm_num
      · intro x
        exact hasDerivAt_boundary₂ x
theorem gap6 :
    AntiderivativesOn integrand =
      ByPartsFamily boundary₂ (2 / 3) residual₂ := by
  exact gap4.trans gap5
theorem gap7 :
    AntiderivativesOn integrand =
      ByPartsFamily boundary₂ (2 / 9) rawResidual₃ := by
  apply antiderivativesOn_eq_byPartsFamily
  · norm_num
  · intro x
    convert hasDerivAt_boundary₂ x using 1
    rw [rawResidual₃_eq]
    ring
theorem gap8 :
    ByPartsFamily boundary₂ (2 / 9) rawResidual₃ =
      ByPartsFamily boundary₃ (-2 / 9) residual₃ := by
  calc
    ByPartsFamily boundary₂ (2 / 9) rawResidual₃ =
        AntiderivativesOn integrand := gap7.symm
    _ = ByPartsFamily boundary₃ (-2 / 9) residual₃ := by
      apply antiderivativesOn_eq_byPartsFamily
      · norm_num
      · intro x
        convert hasDerivAt_boundary₃ x using 1 <;> ring
theorem gap9 :
    AntiderivativesOn integrand =
      ByPartsFamily boundary₃ (-2 / 9) residual₃ := by
  exact gap7.trans gap8
theorem gap10 :
    AntiderivativesOn integrand = PrimitiveFamily := by
  apply Set.ext
  intro F
  simp only [AntiderivativesOn, PrimitiveFamily, Set.mem_setOf_eq]
  constructor
  · intro hF
    let D : ℝ → ℝ := fun y => F y - primitive y
    have hD : ∀ x, HasDerivAt D 0 x := by
      intro x
      dsimp [D]
      convert (hF x (by simp [branch])).sub (hasDerivAt_primitive x) using 1 <;> ring
    have hconst : ∀ x, D x = D 0 := hasDerivAt_zero_is_constant D hD
    refine ⟨D 0, ?_⟩
    intro x hx
    dsimp [D] at hconst ⊢
    linarith [hconst x]
  · rintro ⟨C, hFC⟩
    have hfun : F = fun y => primitive y + C := by
      funext y
      exact hFC y (by simp [branch])
    rw [hfun]
    intro x hx
    exact (hasDerivAt_primitive x).add_const C

end
end ProofGap.Exercise1801
