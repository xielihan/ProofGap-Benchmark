import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

open Set Real

namespace ProofGap.Exercise1876

noncomputable section

def denominator (x : ℝ) : ℝ := (x ^ 2 + 1) * (x ^ 2 + 4)

def integrand (x : ℝ) : ℝ := (x ^ 2 + 5 * x + 4) / denominator x

def partialFractions (x : ℝ) : ℝ :=
  ((5 / 3 : ℝ) * x + 1) / (x ^ 2 + 1) -
    ((5 / 3 : ℝ) * x) / (x ^ 2 + 4)

def antiderivatives (g : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | Differentiable ℝ F ∧ ∀ x, deriv F x = g x}

def primitiveFamily (p : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, F = fun x => p x + C}

def primitive (x : ℝ) : ℝ :=
  (5 / 6 : ℝ) * Real.log ((x ^ 2 + 1) / (x ^ 2 + 4)) +
    Real.arctan x

def sumFamily₁ : Set (ℝ → ℝ) :=
  {F | ∃ G H : ℝ → ℝ,
    Differentiable ℝ G ∧ (∀ x, deriv G x = (x ^ 2 + 4) / denominator x) ∧
    Differentiable ℝ H ∧ (∀ x, deriv H x = x / denominator x) ∧
    F = fun x => G x + 5 * H x}

def sumFamily₂ : Set (ℝ → ℝ) :=
  {F | ∃ G H : ℝ → ℝ,
    Differentiable ℝ G ∧ (∀ x, deriv G x = 1 / (x ^ 2 + 1)) ∧
    Differentiable ℝ H ∧ (∀ x, deriv H x = 2 * x / denominator x) ∧
    F = fun x => G x + (5 / 2 : ℝ) * H x}

def sumFamily₃ : Set (ℝ → ℝ) :=
  {F | ∃ H : ℝ → ℝ,
    Differentiable ℝ H ∧
      (∀ x, deriv H x =
        (1 / (x ^ 2 + 1) - 1 / (x ^ 2 + 4)) * (2 * x)) ∧
    F = fun x => Real.arctan x + (5 / 6 : ℝ) * H x}

private theorem quadratic_ne (x : ℝ) :
    x ^ 2 + 1 ≠ 0 ∧ x ^ 2 + 4 ≠ 0 := by
  constructor <;> nlinarith [sq_nonneg x]

private theorem primitive_hasDerivAt (x : ℝ) :
    HasDerivAt primitive (integrand x) x := by
  rcases quadratic_ne x with ⟨h1, h4⟩
  have ha : HasDerivAt (fun y : ℝ => y ^ 2 + 1) (2 * x) x := by
    simpa [id, mul_comm] using (((hasDerivAt_id x).pow 2).add_const 1)
  have hb : HasDerivAt (fun y : ℝ => y ^ 2 + 4) (2 * x) x := by
    simpa [id, mul_comm] using (((hasDerivAt_id x).pow 2).add_const 4)
  have hfun : primitive = fun y =>
      (5 / 6 : ℝ) *
        (Real.log (y ^ 2 + 1) - Real.log (y ^ 2 + 4)) +
      Real.arctan y := by
    funext y
    unfold primitive
    rw [Real.log_div (quadratic_ne y).1 (quadratic_ne y).2]
  rw [hfun]
  have h :=
    (((ha.log h1).sub (hb.log h4)).const_mul (5 / 6 : ℝ)).add
      (Real.hasDerivAt_arctan x)
  convert h using 1
  unfold integrand denominator
  field_simp [h1, h4] <;> ring

theorem gap1 :
    ∃ A B C D : ℝ, ∀ x,
      integrand x = (A * x + B) / (x ^ 2 + 1) +
        (C * x + D) / (x ^ 2 + 4) := by
  refine ⟨5 / 3, 1, -(5 / 3), 0, ?_⟩
  intro x
  rcases quadratic_ne x with ⟨h1, h4⟩
  unfold integrand denominator
  field_simp [h1, h4] <;> ring

theorem gap2 :
    ∃ A B C D : ℝ, ∀ x, x ^ 2 + 5 * x + 4 =
      (A * x + B) * (x ^ 2 + 4) + (C * x + D) * (x ^ 2 + 1) := by
  refine ⟨5 / 3, 1, -(5 / 3), 0, ?_⟩
  intro x
  ring

theorem gap3 : ∃ A C : ℝ, A + C = 0 := by
  exact ⟨0, 0, by norm_num⟩

theorem gap4 : ∃ B D : ℝ, B + D = 1 := by
  exact ⟨1, 0, by norm_num⟩

theorem gap5 : ∃ A C : ℝ, 4 * A + C = 5 := by
  exact ⟨1, 1, by norm_num⟩

theorem gap6 : ∃ B D : ℝ, 4 * B + D = 4 := by
  exact ⟨1, 0, by norm_num⟩

theorem gap7 : ∃ A : ℝ, A = (5 / 3 : ℝ) := by
  exact ⟨5 / 3, rfl⟩

theorem gap8 : ∃ B : ℝ, B = 1 := by
  exact ⟨1, rfl⟩

theorem gap9 : ∃ C : ℝ, C = -(5 / 3 : ℝ) := by
  exact ⟨-(5 / 3), rfl⟩

theorem gap10 : ∃ D : ℝ, D = 0 := by
  exact ⟨0, rfl⟩

theorem gap11 :
    antiderivatives integrand = antiderivatives partialFractions := by
  have h : integrand = partialFractions := by
    funext x
    rcases quadratic_ne x with ⟨h1, h4⟩
    unfold integrand partialFractions denominator
    field_simp [h1, h4] <;> ring
  exact congrArg antiderivatives h

theorem gap12 : antiderivatives integrand = primitiveFamily primitive := by
  ext F
  simp only [antiderivatives, primitiveFamily, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hF, hF'⟩
    have hsubDiff : Differentiable ℝ (fun x => F x - primitive x) := by
      intro x
      exact
        (hF.differentiableAt.hasDerivAt.sub
          (primitive_hasDerivAt x)).differentiableAt
    have hsubDeriv : ∀ x, deriv (fun y => F y - primitive y) x = 0 := by
      intro x
      have hd :=
        (hF.differentiableAt.hasDerivAt.sub
          (primitive_hasDerivAt x)).deriv
      calc
        deriv (fun y => F y - primitive y) x = deriv F x - integrand x := hd
        _ = 0 := by rw [hF' x]; ring
    refine ⟨F 0 - primitive 0, funext fun x => ?_⟩
    have hconst : F x - primitive x = F 0 - primitive 0 := by
      rcases lt_trichotomy x 0 with hx | hx | hx
      · obtain ⟨c, hcI, hc⟩ :=
          exists_deriv_eq_slope (fun y => F y - primitive y) hx
            hsubDiff.continuous.continuousOn hsubDiff.differentiableOn
        rw [hsubDeriv c] at hc
        have hne : (0 : ℝ) - x ≠ 0 := by linarith
        field_simp [hne] at hc
        linarith
      · simpa [hx]
      · obtain ⟨c, hcI, hc⟩ :=
          exists_deriv_eq_slope (fun y => F y - primitive y) hx
            hsubDiff.continuous.continuousOn hsubDiff.differentiableOn
        rw [hsubDeriv c] at hc
        have hne : x - (0 : ℝ) ≠ 0 := by linarith
        field_simp [hne] at hc
        linarith
    linarith
  · rintro ⟨C, rfl⟩
    constructor
    · intro x
      exact ((primitive_hasDerivAt x).add_const C).differentiableAt
    · intro x
      exact ((primitive_hasDerivAt x).add_const C).deriv

theorem gap13 : antiderivatives integrand = sumFamily₁ := by
  ext F
  simp only [antiderivatives, sumFamily₁, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hF, hF'⟩
    refine ⟨Real.arctan, fun x => (1 / 5 : ℝ) * (F x - Real.arctan x), ?_, ?_, ?_, ?_, ?_⟩
    · intro x
      exact (Real.hasDerivAt_arctan x).differentiableAt
    · intro x
      rw [(Real.hasDerivAt_arctan x).deriv]
      rcases quadratic_ne x with ⟨h1, h4⟩
      unfold denominator
      field_simp [h1, h4] <;> ring
    · intro x
      exact
        ((hF.differentiableAt.hasDerivAt.sub
          (Real.hasDerivAt_arctan x)).const_mul (1 / 5 : ℝ)).differentiableAt
    · intro x
      have hd :=
        ((hF.differentiableAt.hasDerivAt.sub
          (Real.hasDerivAt_arctan x)).const_mul (1 / 5 : ℝ)).deriv
      calc
        deriv (fun y => (1 / 5 : ℝ) * (F y - Real.arctan y)) x =
            (1 / 5 : ℝ) * (deriv F x - 1 / (1 + x ^ 2)) := by
          simpa only [Pi.sub_apply] using hd
        _ = x / denominator x := by
          rw [hF' x]
          rcases quadratic_ne x with ⟨h1, h4⟩
          unfold integrand denominator
          field_simp [h1, h4] <;> ring
    · funext x
      ring
  · rintro ⟨G, H, hG, hG', hH, hH', rfl⟩
    constructor
    · intro x
      exact
        (hG.differentiableAt.hasDerivAt.add
          (hH.differentiableAt.hasDerivAt.const_mul 5)).differentiableAt
    · intro x
      have hGx : HasDerivAt G (deriv G x) x :=
        hG.differentiableAt.hasDerivAt
      have hHx : HasDerivAt H (deriv H x) x :=
        hH.differentiableAt.hasDerivAt
      have hd :
          deriv (fun y => G y + 5 * H y) x =
            deriv G x + 5 * deriv H x := by
        simpa only [Pi.add_apply] using (hGx.add (hHx.const_mul 5)).deriv
      rw [hd, hG' x, hH' x]
      rcases quadratic_ne x with ⟨h1, h4⟩
      unfold integrand denominator
      field_simp [h1, h4] <;> ring

theorem gap14 : antiderivatives integrand = sumFamily₂ := by
  ext F
  simp only [antiderivatives, sumFamily₂, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hF, hF'⟩
    refine ⟨Real.arctan, fun x => (2 / 5 : ℝ) * (F x - Real.arctan x), ?_, ?_, ?_, ?_, ?_⟩
    · intro x
      exact (Real.hasDerivAt_arctan x).differentiableAt
    · intro x
      simpa only [add_comm] using (Real.hasDerivAt_arctan x).deriv
    · intro x
      exact
        ((hF.differentiableAt.hasDerivAt.sub
          (Real.hasDerivAt_arctan x)).const_mul (2 / 5 : ℝ)).differentiableAt
    · intro x
      have hd :=
        ((hF.differentiableAt.hasDerivAt.sub
          (Real.hasDerivAt_arctan x)).const_mul (2 / 5 : ℝ)).deriv
      calc
        deriv (fun y => (2 / 5 : ℝ) * (F y - Real.arctan y)) x =
            (2 / 5 : ℝ) * (deriv F x - 1 / (1 + x ^ 2)) := by
          simpa only [Pi.sub_apply] using hd
        _ = 2 * x / denominator x := by
          rw [hF' x]
          rcases quadratic_ne x with ⟨h1, h4⟩
          unfold integrand denominator
          field_simp [h1, h4] <;> ring
    · funext x
      ring
  · rintro ⟨G, H, hG, hG', hH, hH', rfl⟩
    constructor
    · intro x
      exact
        (hG.differentiableAt.hasDerivAt.add
          (hH.differentiableAt.hasDerivAt.const_mul (5 / 2 : ℝ))).differentiableAt
    · intro x
      have hGx : HasDerivAt G (deriv G x) x :=
        hG.differentiableAt.hasDerivAt
      have hHx : HasDerivAt H (deriv H x) x :=
        hH.differentiableAt.hasDerivAt
      have hd :
          deriv (fun y => G y + (5 / 2 : ℝ) * H y) x =
            deriv G x + (5 / 2 : ℝ) * deriv H x := by
        simpa only [Pi.add_apply] using
          (hGx.add (hHx.const_mul (5 / 2 : ℝ))).deriv
      rw [hd, hG' x, hH' x]
      rcases quadratic_ne x with ⟨h1, h4⟩
      unfold integrand denominator
      field_simp [h1, h4] <;> ring

theorem gap15 : antiderivatives integrand = sumFamily₃ := by
  ext F
  simp only [antiderivatives, sumFamily₃, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hF, hF'⟩
    refine ⟨fun x => (6 / 5 : ℝ) * (F x - Real.arctan x), ?_, ?_, ?_⟩
    · intro x
      exact
        ((hF.differentiableAt.hasDerivAt.sub
          (Real.hasDerivAt_arctan x)).const_mul (6 / 5 : ℝ)).differentiableAt
    · intro x
      have hd :=
        ((hF.differentiableAt.hasDerivAt.sub
          (Real.hasDerivAt_arctan x)).const_mul (6 / 5 : ℝ)).deriv
      calc
        deriv (fun y => (6 / 5 : ℝ) * (F y - Real.arctan y)) x =
            (6 / 5 : ℝ) * (deriv F x - 1 / (1 + x ^ 2)) := by
          simpa only [Pi.sub_apply] using hd
        _ = (1 / (x ^ 2 + 1) - 1 / (x ^ 2 + 4)) * (2 * x) := by
          rw [hF' x]
          rcases quadratic_ne x with ⟨h1, h4⟩
          unfold integrand denominator
          field_simp [h1, h4] <;> ring
    · funext x
      ring
  · rintro ⟨H, hH, hH', rfl⟩
    constructor
    · intro x
      exact
        ((Real.hasDerivAt_arctan x).add
          (hH.differentiableAt.hasDerivAt.const_mul (5 / 6 : ℝ))).differentiableAt
    · intro x
      have hd :=
        ((Real.hasDerivAt_arctan x).add
          (hH.differentiableAt.hasDerivAt.const_mul (5 / 6 : ℝ))).deriv
      calc
        deriv (fun y => Real.arctan y + (5 / 6 : ℝ) * H y) x =
            1 / (1 + x ^ 2) + (5 / 6 : ℝ) * deriv H x := by
          simpa only [Pi.add_apply] using hd
        _ = integrand x := by
          rw [hH' x]
          rcases quadratic_ne x with ⟨h1, h4⟩
          unfold integrand denominator
          field_simp [h1, h4] <;> ring

theorem gap16 :
    antiderivatives integrand =
      primitiveFamily (fun x =>
        Real.arctan x + (5 / 6 : ℝ) *
          Real.log ((x ^ 2 + 1) / (x ^ 2 + 4))) := by
  have hp : primitive = fun x =>
      Real.arctan x + (5 / 6 : ℝ) *
        Real.log ((x ^ 2 + 1) / (x ^ 2 + 4)) := by
    funext x
    unfold primitive
    ring
  calc
    antiderivatives integrand = primitiveFamily primitive := gap12
    _ = primitiveFamily (fun x =>
        Real.arctan x + (5 / 6 : ℝ) *
          Real.log ((x ^ 2 + 1) / (x ^ 2 + 4))) := by rw [hp]

end

end ProofGap.Exercise1876
