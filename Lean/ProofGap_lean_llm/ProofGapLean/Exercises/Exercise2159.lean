import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise2159

noncomputable section

def arccot (x : ℝ) := Real.pi / 2 - Real.arctan x
def Antiderivatives (f : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∀ x, HasDerivAt F (f x) x}
def PrimitiveFamily (p : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x, F x = p x + C}
def integrand (x : ℝ) := x * (1 + x ^ 2) * arccot x
def InitialFamily : Set (ℝ → ℝ) :=
  {F | ∃ G : ℝ → ℝ,
    (∀ x,
      HasDerivAt G
        (arccot x * deriv (fun y : ℝ => (1 + y ^ 2) ^ 2) x) x) ∧
    ∀ x, F x = 1 / 4 * G x}
def ByPartsFamily : Set (ℝ → ℝ) :=
  {F | ∃ G ∈ Antiderivatives (fun x => 1 + x ^ 2),
    ∀ x,
      F x = 1 / 4 * (1 + x ^ 2) ^ 2 * arccot x + 1 / 4 * G x}
def primitive (x : ℝ) :=
  1 / 4 * (1 + x ^ 2) ^ 2 * arccot x + x / 4 + x ^ 3 / 12

private theorem hasDerivAt_arccot (x : ℝ) :
    HasDerivAt arccot (-(1 / (1 + x ^ 2))) x := by
  simpa [arccot] using
    ((hasDerivAt_const (x := x) (Real.pi / 2)).sub
      (Real.hasDerivAt_arctan x))

private theorem hasDerivAt_quartic (x : ℝ) :
    HasDerivAt (fun y : ℝ => (1 + y ^ 2) ^ 2)
      (4 * x * (1 + x ^ 2)) x := by
  convert
    (((hasDerivAt_const (x := x) (1 : ℝ)).add
      ((hasDerivAt_id x).pow 2)).pow 2) using 1 <;>
    simp only [Pi.add_apply, Pi.pow_apply, id_eq] <;> ring

private theorem deriv_quartic (x : ℝ) :
    deriv (fun y : ℝ => (1 + y ^ 2) ^ 2) x =
      4 * x * (1 + x ^ 2) := by
  exact (hasDerivAt_quartic x).deriv

private theorem hasDerivAt_mainTerm (x : ℝ) :
    HasDerivAt
      (fun y : ℝ => (1 + y ^ 2) ^ 2 * arccot y)
      (4 * x * (1 + x ^ 2) * arccot x - (1 + x ^ 2)) x := by
  have hne : 1 + x ^ 2 ≠ 0 := by
    nlinarith [sq_nonneg x]
  convert (hasDerivAt_quartic x).mul (hasDerivAt_arccot x) using 1
  field_simp [hne]
  <;> ring

private theorem hasDerivAt_primitive (x : ℝ) :
    HasDerivAt primitive (integrand x) x := by
  unfold primitive integrand
  convert
    (((hasDerivAt_mainTerm x).const_mul (1 / 4 : ℝ)).add
      ((hasDerivAt_id x).const_mul (1 / 4 : ℝ))).add
      (((hasDerivAt_id x).pow 3).const_mul (1 / 12 : ℝ))
    using 1
  · funext y
    simp only [Pi.add_apply, Pi.pow_apply, id_eq]
    ring
  · simp only [Pi.add_apply, Pi.pow_apply, id_eq]
    ring

theorem gap1 :
    Antiderivatives integrand = InitialFamily := by
  ext F
  change
    (∀ x, HasDerivAt F (integrand x) x) ↔
      ∃ G : ℝ → ℝ,
        (∀ x,
          HasDerivAt G
            (arccot x * deriv (fun y : ℝ => (1 + y ^ 2) ^ 2) x) x) ∧
        ∀ x, F x = 1 / 4 * G x
  constructor
  · intro hF
    refine ⟨fun y => 4 * F y, ?_, ?_⟩
    · intro x
      convert (hF x).const_mul (4 : ℝ) using 1
      rw [deriv_quartic]
      unfold integrand
      ring
    · intro x
      ring
  · rintro ⟨G, hG, hFG⟩
    have hEq : F = fun y => (1 / 4 : ℝ) * G y := by
      funext y
      exact hFG y
    intro x
    rw [hEq]
    convert (hG x).const_mul (1 / 4 : ℝ) using 1
    rw [deriv_quartic]
    unfold integrand
    ring
theorem gap2 :
    InitialFamily = ByPartsFamily := by
  ext F
  change
    (∃ H : ℝ → ℝ,
        (∀ x,
          HasDerivAt H
            (arccot x * deriv (fun y : ℝ => (1 + y ^ 2) ^ 2) x) x) ∧
        ∀ x, F x = 1 / 4 * H x) ↔
      ∃ G : ℝ → ℝ,
        (∀ x, HasDerivAt G (1 + x ^ 2) x) ∧
        ∀ x,
          F x =
            1 / 4 * (1 + x ^ 2) ^ 2 * arccot x + 1 / 4 * G x
  constructor
  · rintro ⟨H, hH, hFH⟩
    refine
      ⟨fun y => H y - (1 + y ^ 2) ^ 2 * arccot y, ?_, ?_⟩
    · intro x
      have hH' :
          HasDerivAt H (4 * x * (1 + x ^ 2) * arccot x) x := by
        convert hH x using 1
        rw [deriv_quartic]
        ring
      convert hH'.sub (hasDerivAt_mainTerm x) using 1 <;> ring
    · intro x
      rw [hFH x]
      ring
  · rintro ⟨G, hG, hFG⟩
    refine
      ⟨fun y => (1 + y ^ 2) ^ 2 * arccot y + G y, ?_, ?_⟩
    · intro x
      convert (hasDerivAt_mainTerm x).add (hG x) using 1
      rw [deriv_quartic]
      ring
    · intro x
      rw [hFG x]
      ring
theorem gap3 :
    Antiderivatives integrand = ByPartsFamily := by
  exact gap1.trans gap2
theorem gap4 :
    Antiderivatives integrand = PrimitiveFamily primitive := by
  ext F
  change
    (∀ x, HasDerivAt F (integrand x) x) ↔
      ∃ C : ℝ, ∀ x, F x = primitive x + C
  constructor
  · intro hF
    let D : ℝ → ℝ := fun y => F y - primitive y
    have hD : ∀ x, HasDerivAt D 0 x := by
      intro x
      dsimp [D]
      convert (hF x).sub (hasDerivAt_primitive x) using 1 <;> ring
    have hdiff : Differentiable ℝ D := by
      intro x
      exact (hD x).differentiableAt
    have hderiv : ∀ x, deriv D x = 0 := by
      intro x
      exact (hD x).deriv
    refine ⟨D 0, ?_⟩
    intro x
    have hc : D x = D 0 :=
      is_const_of_deriv_eq_zero hdiff hderiv x 0
    dsimp [D] at hc ⊢
    linarith
  · rintro ⟨C, hFC⟩
    have hEq : F = fun y => primitive y + C := by
      funext y
      exact hFC y
    subst F
    intro x
    exact (hasDerivAt_primitive x).add_const C

end
end ProofGap.Exercise2159
