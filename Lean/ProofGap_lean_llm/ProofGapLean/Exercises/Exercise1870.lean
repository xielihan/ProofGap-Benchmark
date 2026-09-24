import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.MeanValue

open Set Real

namespace ProofGap.Exercise1870

noncomputable section

def integrand (x : ℝ) : ℝ := x ^ 4 / (x ^ 4 + 5 * x ^ 2 + 4)

def divisionRewrite (x : ℝ) : ℝ :=
  1 - (5 * x ^ 2 + 4) / ((x ^ 2 + 1) * (x ^ 2 + 4))

def partialFractionRewrite (x : ℝ) : ℝ :=
  1 + 1 / (3 * (x ^ 2 + 1)) - 16 / (3 * (x ^ 2 + 4))

def antiderivatives (g : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | Differentiable ℝ F ∧ ∀ x, deriv F x = g x}

def primitiveFamily (p : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, F = fun x => p x + C}

def primitive (x : ℝ) : ℝ :=
  x + (1 / 3 : ℝ) * Real.arctan x -
    (8 / 3 : ℝ) * Real.arctan (x / 2)

def coefficientIdentity (A₁ B₁ A₂ B₂ : ℝ) : Prop :=
  ∀ x, -(5 * x ^ 2 + 4) =
    (A₁ * x + B₁) * (x ^ 2 + 4) + (A₂ * x + B₂) * (x ^ 2 + 1)

private theorem integrand_eq_partialFractionRewrite (x : ℝ) :
    integrand x = partialFractionRewrite x := by
  unfold integrand partialFractionRewrite
  have hfac : x ^ 4 + 5 * x ^ 2 + 4 = (x ^ 2 + 1) * (x ^ 2 + 4) := by
    ring
  rw [hfac]
  have h1 : x ^ 2 + 1 ≠ 0 := by
    nlinarith [sq_nonneg x]
  have h4 : x ^ 2 + 4 ≠ 0 := by
    nlinarith [sq_nonneg x]
  field_simp [h1, h4] <;> ring

private theorem primitive_hasDerivAt (x : ℝ) :
    HasDerivAt primitive (integrand x) x := by
  have hhalf : 1 + (x / 2) ^ 2 ≠ 0 := by
    nlinarith [sq_nonneg (x / 2)]
  have h1 : x ^ 2 + 1 ≠ 0 := by
    nlinarith [sq_nonneg x]
  have h4 : x ^ 2 + 4 ≠ 0 := by
    nlinarith [sq_nonneg x]
  have hraw :=
    ((hasDerivAt_id x).add
      ((Real.hasDerivAt_arctan x).const_mul (1 / 3 : ℝ))).sub
      (((Real.hasDerivAt_arctan (x / 2)).comp x
        ((hasDerivAt_id x).div_const 2)).const_mul (8 / 3 : ℝ))
  have hpf : HasDerivAt primitive (partialFractionRewrite x) x := by
    unfold primitive
    convert hraw using 1 <;> try rfl
    unfold partialFractionRewrite
    field_simp [hhalf, h1, h4] <;> ring
  simpa only [integrand_eq_partialFractionRewrite] using hpf

theorem gap1 : ∀ x, integrand x = divisionRewrite x := by
  intro x
  unfold integrand divisionRewrite
  have hfac : x ^ 4 + 5 * x ^ 2 + 4 = (x ^ 2 + 1) * (x ^ 2 + 4) := by
    ring
  rw [hfac]
  have h1 : x ^ 2 + 1 ≠ 0 := by
    nlinarith [sq_nonneg x]
  have h4 : x ^ 2 + 4 ≠ 0 := by
    nlinarith [sq_nonneg x]
  field_simp [h1, h4] <;> ring

theorem gap2 :
    ∃ A₁ B₁ A₂ B₂ : ℝ, ∀ x,
      -(5 * x ^ 2 + 4) / ((x ^ 2 + 1) * (x ^ 2 + 4)) =
        (A₁ * x + B₁) / (x ^ 2 + 1) +
          (A₂ * x + B₂) / (x ^ 2 + 4) := by
  refine ⟨0, (1 / 3 : ℝ), 0, -(16 / 3 : ℝ), ?_⟩
  intro x
  have h1 : x ^ 2 + 1 ≠ 0 := by
    nlinarith [sq_nonneg x]
  have h4 : x ^ 2 + 4 ≠ 0 := by
    nlinarith [sq_nonneg x]
  field_simp [h1, h4] <;> ring

theorem gap3 : ∃ A₁ B₁ A₂ B₂ : ℝ, coefficientIdentity A₁ B₁ A₂ B₂ := by
  refine ⟨0, (1 / 3 : ℝ), 0, -(16 / 3 : ℝ), ?_⟩
  unfold coefficientIdentity
  intro x
  ring

theorem gap4 (A₁ B₁ A₂ B₂ : ℝ) (h : coefficientIdentity A₁ B₁ A₂ B₂) :
    A₁ + A₂ = 0 := by
  unfold coefficientIdentity at h
  have hp1 := h 1
  have hm1 := h (-1)
  have hp2 := h 2
  have hm2 := h (-2)
  norm_num at hp1 hm1 hp2 hm2
  linarith

theorem gap5 (A₁ B₁ A₂ B₂ : ℝ) (h : coefficientIdentity A₁ B₁ A₂ B₂) :
    B₁ + B₂ = -5 := by
  unfold coefficientIdentity at h
  have h0 := h 0
  have hp1 := h 1
  have hm1 := h (-1)
  norm_num at h0 hp1 hm1
  linarith

theorem gap6 (A₁ B₁ A₂ B₂ : ℝ) (h : coefficientIdentity A₁ B₁ A₂ B₂) :
    4 * A₁ + A₂ = 0 := by
  unfold coefficientIdentity at h
  have hp1 := h 1
  have hm1 := h (-1)
  have hp2 := h 2
  have hm2 := h (-2)
  norm_num at hp1 hm1 hp2 hm2
  linarith

theorem gap7 (A₁ B₁ A₂ B₂ : ℝ) (h : coefficientIdentity A₁ B₁ A₂ B₂) :
    4 * B₁ + B₂ = -4 := by
  unfold coefficientIdentity at h
  have h0 := h 0
  norm_num at h0
  linarith

theorem gap8 (A₁ A₂ : ℝ) (h1 : A₁ + A₂ = 0) (h2 : 4 * A₁ + A₂ = 0) :
    A₁ = 0 := by
  linarith

theorem gap9 (B₁ B₂ : ℝ) (h1 : B₁ + B₂ = -5) (h2 : 4 * B₁ + B₂ = -4) :
    B₁ = (1 / 3 : ℝ) := by
  linarith

theorem gap10 (A₁ A₂ : ℝ) (h1 : A₁ + A₂ = 0) (h2 : 4 * A₁ + A₂ = 0) :
    A₂ = 0 := by
  linarith

theorem gap11 (B₁ B₂ : ℝ) (h1 : B₁ + B₂ = -5) (h2 : 4 * B₁ + B₂ = -4) :
    B₂ = -(16 / 3 : ℝ) := by
  linarith

theorem gap12 :
    antiderivatives integrand = antiderivatives partialFractionRewrite := by
  apply Set.ext
  intro F
  simp only [antiderivatives, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hF, hder⟩
    exact ⟨hF, fun x => (hder x).trans (integrand_eq_partialFractionRewrite x)⟩
  · rintro ⟨hF, hder⟩
    exact ⟨hF, fun x => (hder x).trans (integrand_eq_partialFractionRewrite x).symm⟩

theorem gap13 : antiderivatives integrand = primitiveFamily primitive := by
  apply Set.ext
  intro F
  simp only [antiderivatives, primitiveFamily, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hF, hder⟩
    let d : ℝ → ℝ := fun x => F x - primitive x
    have hd : ∀ x, HasDerivAt d 0 x := by
      intro x
      dsimp [d]
      simpa [hder x] using
        ((hF x).hasDerivAt.sub (primitive_hasDerivAt x))
    have hDifferentiable : Differentiable ℝ d :=
      fun x => (hd x).differentiableAt
    refine ⟨d 0, ?_⟩
    funext x
    have hx : d x = d 0 :=
      is_const_of_deriv_eq_zero hDifferentiable (fun z => (hd z).deriv) x 0
    dsimp [d] at hx ⊢
    linarith
  · rintro ⟨C, rfl⟩
    exact
      ⟨fun x => ((primitive_hasDerivAt x).add_const C).differentiableAt,
        fun x => ((primitive_hasDerivAt x).add_const C).deriv⟩

end

end ProofGap.Exercise1870
