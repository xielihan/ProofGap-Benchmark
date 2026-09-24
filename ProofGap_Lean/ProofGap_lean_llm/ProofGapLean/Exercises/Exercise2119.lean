import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise2119
noncomputable section

def integrand (x : ℝ) := Real.sinh x * Real.sinh (2 * x) * Real.sinh (3 * x)
def firstReduced (x : ℝ) :=
  (1 / 2 : ℝ) * (Real.cosh (4 * x) - Real.cosh (2 * x)) * Real.sinh (2 * x)
def term₁ (x : ℝ) := Real.cosh (4 * x) * Real.sinh (2 * x)
def term₂ (x : ℝ) := Real.cosh (2 * x) * Real.sinh (2 * x)
def finalReduced₁ (x : ℝ) := Real.sinh (6 * x) - Real.sinh (2 * x)
def finalReduced₂ (x : ℝ) := Real.sinh (4 * x)
def primitive (x : ℝ) :=
  (1 / 24 : ℝ) * Real.cosh (6 * x) -
    (1 / 16 : ℝ) * Real.cosh (4 * x) -
    (1 / 8 : ℝ) * Real.cosh (2 * x)

def Family (f : ℝ → ℝ) :=
  {F : ℝ → ℝ | ∀ x, HasDerivAt F (f x) x}
def DifferenceFamily (c₁ c₂ : ℝ) (f g : ℝ → ℝ) :=
  {F : ℝ → ℝ | ∃ A ∈ Family f, ∃ B ∈ Family g,
    ∀ x, F x = c₁ * A x - c₂ * B x}
def Translates (p : ℝ → ℝ) :=
  {F : ℝ → ℝ | ∃ C : ℝ, ∀ x, F x = p x + C}

theorem gap1 : Family integrand = Family firstReduced := by
  have hident : ∀ x : ℝ, integrand x = firstReduced x := by
    intro x
    dsimp [integrand, firstReduced]
    have h4 : 4 * x = 3 * x + x := by ring
    have h2 : 2 * x = 3 * x - x := by ring
    rw [h4, h2, Real.cosh_add, Real.cosh_sub]
    ring
  apply Set.ext
  intro F
  simp only [Family, Set.mem_setOf_eq]
  constructor
  · intro h x
    rw [← hident x]
    exact h x
  · intro h x
    rw [hident x]
    exact h x
theorem gap2 : Family firstReduced = DifferenceFamily (1 / 2) (1 / 2) term₁ term₂ := by
  let B₀ : ℝ → ℝ := fun y => (1 / 8 : ℝ) * Real.cosh (4 * y)
  have hB₀ : ∀ x, HasDerivAt B₀ (term₂ x) x := by
    intro x
    have hd :=
      ((Real.hasDerivAt_cosh (4 * x)).comp x
        ((hasDerivAt_id x).const_mul 4)).const_mul (1 / 8 : ℝ)
    change HasDerivAt B₀ (term₂ x) x
    convert hd using 1
    dsimp [term₂]
    have h4 : 4 * x = 2 * x + 2 * x := by ring
    rw [h4, Real.sinh_add]
    ring
  apply Set.ext
  intro F
  simp only [DifferenceFamily, Family, Set.mem_setOf_eq]
  constructor
  · intro hF
    refine ⟨fun y => 2 * F y + B₀ y, ?_, B₀, hB₀, ?_⟩
    · intro x
      convert ((hF x).const_mul 2).add (hB₀ x) using 1
      dsimp [firstReduced, term₁, term₂]
      ring
    · intro x
      dsimp only
      ring
  · rintro ⟨A, hA, B, hB, hF⟩
    have hfun : F = fun y => (1 / 2 : ℝ) * A y - (1 / 2 : ℝ) * B y :=
      funext hF
    intro x
    rw [hfun]
    convert ((hA x).const_mul (1 / 2 : ℝ)).sub
      ((hB x).const_mul (1 / 2 : ℝ)) using 1
    dsimp [firstReduced, term₁, term₂]
    ring
theorem gap3 : Family integrand = DifferenceFamily (1 / 2) (1 / 2) term₁ term₂ := by
  exact gap1.trans gap2
theorem gap4 :
    Family integrand = DifferenceFamily (1 / 4) (1 / 4) finalReduced₁ finalReduced₂ := by
  have h₁ : ∀ x : ℝ, finalReduced₁ x = 2 * term₁ x := by
    intro x
    dsimp [finalReduced₁, term₁]
    calc
      Real.sinh (6 * x) - Real.sinh (2 * x) =
          Real.sinh (4 * x + 2 * x) - Real.sinh (4 * x - 2 * x) := by
            congr 1 <;> ring
      _ = 2 * (Real.cosh (4 * x) * Real.sinh (2 * x)) := by
            rw [Real.sinh_add, Real.sinh_sub]
            ring
  have h₂ : ∀ x : ℝ, finalReduced₂ x = 2 * term₂ x := by
    intro x
    dsimp [finalReduced₂, term₂]
    calc
      Real.sinh (4 * x) = Real.sinh (2 * x + 2 * x) := by
        congr 1
        ring
      _ = 2 * (Real.cosh (2 * x) * Real.sinh (2 * x)) := by
        rw [Real.sinh_add]
        ring
  rw [gap3]
  apply Set.ext
  intro F
  simp only [DifferenceFamily, Family, Set.mem_setOf_eq]
  constructor
  · rintro ⟨A, hA, B, hB, hF⟩
    refine ⟨fun y => 2 * A y, ?_, fun y => 2 * B y, ?_, ?_⟩
    · intro x
      convert (hA x).const_mul 2 using 1
      rw [h₁ x]
    · intro x
      convert (hB x).const_mul 2 using 1
      rw [h₂ x]
    · intro x
      rw [hF x]
      ring
  · rintro ⟨A, hA, B, hB, hF⟩
    refine ⟨fun y => (1 / 2 : ℝ) * A y, ?_,
      fun y => (1 / 2 : ℝ) * B y, ?_, ?_⟩
    · intro x
      convert (hA x).const_mul (1 / 2 : ℝ) using 1
      rw [h₁ x]
      ring
    · intro x
      convert (hB x).const_mul (1 / 2 : ℝ) using 1
      rw [h₂ x]
      ring
    · intro x
      rw [hF x]
      ring
theorem gap5 :
    DifferenceFamily (1 / 4) (1 / 4) finalReduced₁ finalReduced₂ =
      Translates primitive := by
  have hident : ∀ x : ℝ,
      integrand x = (1 / 4 : ℝ) * (finalReduced₁ x - finalReduced₂ x) := by
    intro x
    have hi : integrand x = firstReduced x := by
      dsimp [integrand, firstReduced]
      have h4 : 4 * x = 3 * x + x := by ring
      have h2 : 2 * x = 3 * x - x := by ring
      rw [h4, h2, Real.cosh_add, Real.cosh_sub]
      ring
    have h₁ : finalReduced₁ x = 2 * term₁ x := by
      dsimp [finalReduced₁, term₁]
      calc
        Real.sinh (6 * x) - Real.sinh (2 * x) =
            Real.sinh (4 * x + 2 * x) - Real.sinh (4 * x - 2 * x) := by
              congr 1 <;> ring
        _ = 2 * (Real.cosh (4 * x) * Real.sinh (2 * x)) := by
              rw [Real.sinh_add, Real.sinh_sub]
              ring
    have h₂ : finalReduced₂ x = 2 * term₂ x := by
      dsimp [finalReduced₂, term₂]
      calc
        Real.sinh (4 * x) = Real.sinh (2 * x + 2 * x) := by
          congr 1
          ring
        _ = 2 * (Real.cosh (2 * x) * Real.sinh (2 * x)) := by
          rw [Real.sinh_add]
          ring
    calc
      integrand x = firstReduced x := hi
      _ = (1 / 2 : ℝ) * (term₁ x - term₂ x) := by
        dsimp [firstReduced, term₁, term₂]
        ring
      _ = (1 / 4 : ℝ) * (finalReduced₁ x - finalReduced₂ x) := by
        rw [h₁, h₂]
        ring
  have hprim : ∀ x, HasDerivAt primitive (integrand x) x := by
    intro x
    have hcosh (n : ℝ) :
        HasDerivAt (fun y : ℝ => Real.cosh (n * y))
          (n * Real.sinh (n * x)) x := by
      convert (Real.hasDerivAt_cosh (n * x)).comp x
        ((hasDerivAt_id x).const_mul n) using 1 <;> ring
    have hd : HasDerivAt primitive
        ((1 / 24 : ℝ) * (6 * Real.sinh (6 * x)) -
          (1 / 16 : ℝ) * (4 * Real.sinh (4 * x)) -
          (1 / 8 : ℝ) * (2 * Real.sinh (2 * x))) x := by
      unfold primitive
      convert (((hcosh 6).const_mul (1 / 24 : ℝ)).sub
        ((hcosh 4).const_mul (1 / 16 : ℝ))).sub
        ((hcosh 2).const_mul (1 / 8 : ℝ)) using 1 <;> ring
    convert hd using 1
    rw [hident x]
    dsimp [finalReduced₁, finalReduced₂]
    ring
  rw [← gap4]
  apply Set.ext
  intro F
  simp only [Family, Translates, Set.mem_setOf_eq]
  constructor
  · intro hF
    have hzero : ∀ x,
        HasDerivAt (fun y => F y - primitive y) 0 x := by
      intro x
      convert (hF x).sub (hprim x) using 1 <;> ring
    have hdiff : Differentiable ℝ (fun y => F y - primitive y) :=
      fun x => (hzero x).differentiableAt
    have hderiv : ∀ x, deriv (fun y => F y - primitive y) x = 0 :=
      fun x => (hzero x).deriv
    refine ⟨F 0 - primitive 0, ?_⟩
    intro x
    have hc : F x - primitive x = F 0 - primitive 0 :=
      is_const_of_deriv_eq_zero hdiff hderiv x 0
    calc
      F x = primitive x + (F x - primitive x) := by ring
      _ = primitive x + (F 0 - primitive 0) := by rw [hc]
  · rintro ⟨C, hF⟩
    have hfun : F = fun y => primitive y + C := funext hF
    intro x
    rw [hfun]
    exact (hprim x).add_const C
theorem gap6 : Family integrand = Translates primitive := by
  exact gap4.trans gap5

end
end ProofGap.Exercise2119
