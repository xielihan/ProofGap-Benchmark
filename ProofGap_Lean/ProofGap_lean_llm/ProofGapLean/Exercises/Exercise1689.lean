import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise1689

noncomputable section

def inner (x : ℝ) : ℝ := -x ^ 2
def integrand (x : ℝ) : ℝ := x * Real.exp (inner x)
def primitive (x : ℝ) : ℝ := -(1 / 2 : ℝ) * Real.exp (inner x)

def IsAntiderivativeOn (F f : ℝ → ℝ) (s : Set ℝ) : Prop :=
  ∀ x ∈ s, HasDerivAt F (f x) x
def Family (f : ℝ → ℝ) (s : Set ℝ) : Set (ℝ → ℝ) :=
  {F | IsAntiderivativeOn F f s}
def Translates (P : ℝ → ℝ) (s : Set ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C, ∀ x ∈ s, F x = P x + C}

private theorem inner_hasDerivAt (x : ℝ) :
    HasDerivAt inner (-x + -x) x := by
  have hinner : inner = (-(id * id) : ℝ → ℝ) := by
    funext y
    simp [inner, pow_two]
  rw [hinner]
  convert ((hasDerivAt_id x).mul (hasDerivAt_id x)).neg using 1 <;>
    (simp only [id]; ring)

theorem gap1 (x : ℝ) :
    integrand x = -(1 / 2 : ℝ) * Real.exp (inner x) * deriv inner x := by
  rw [(inner_hasDerivAt x).deriv]
  simp only [integrand]
  ring

theorem gap2 (x : ℝ) :
    HasDerivAt primitive (integrand x) x := by
  have hexp :
      HasDerivAt (fun y : ℝ => Real.exp (inner y))
        (Real.exp (inner x) * (-x + -x)) x :=
    (Real.hasDerivAt_exp (inner x)).comp x (inner_hasDerivAt x)
  change
    HasDerivAt (fun y : ℝ => -(1 / 2 : ℝ) * Real.exp (inner y))
      (x * Real.exp (inner x)) x
  convert hexp.const_mul (-(1 / 2 : ℝ)) using 1 <;> ring

theorem gap3 :
    Family integrand Set.univ = Translates primitive Set.univ := by
  ext F
  change
    (∀ x ∈ Set.univ, HasDerivAt F (integrand x) x) ↔
      ∃ C, ∀ x ∈ Set.univ, F x = primitive x + C
  constructor
  · intro hF
    let D : ℝ → ℝ := fun y => F y - primitive y
    have hD : ∀ y : ℝ, HasDerivAt D 0 y := by
      intro y
      simpa only [D, sub_self] using
        (hF y (Set.mem_univ y)).sub (gap2 y)
    have hdiff : Differentiable ℝ D := by
      intro y
      exact (hD y).differentiableAt
    have hderiv : ∀ y : ℝ, deriv D y = 0 := by
      intro y
      exact (hD y).deriv
    refine ⟨F 0 - primitive 0, ?_⟩
    intro x hx
    have heq : D x = D 0 :=
      is_const_of_deriv_eq_zero hdiff hderiv x 0
    dsimp [D] at heq
    linarith
  · rintro ⟨C, hC⟩
    have hfun : F = fun y => primitive y + C := by
      funext y
      exact hC y (Set.mem_univ y)
    intro x hx
    rw [hfun]
    exact (gap2 x).add_const C

end

end ProofGap.Exercise1689
