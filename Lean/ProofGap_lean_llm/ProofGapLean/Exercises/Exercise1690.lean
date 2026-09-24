import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise1690

noncomputable section

def inner (x : ℝ) : ℝ := 2 + Real.exp x
def integrand (x : ℝ) : ℝ := Real.exp x / inner x
def primitive (x : ℝ) : ℝ := Real.log (inner x)

def IsAntiderivativeOn (F f : ℝ → ℝ) (s : Set ℝ) : Prop :=
  ∀ x ∈ s, HasDerivAt F (f x) x
def Family (f : ℝ → ℝ) (s : Set ℝ) : Set (ℝ → ℝ) :=
  {F | IsAntiderivativeOn F f s}
def Translates (P : ℝ → ℝ) (s : Set ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C, ∀ x ∈ s, F x = P x + C}

private theorem inner_hasDerivAt (x : ℝ) :
    HasDerivAt inner (Real.exp x) x := by
  have h := (hasDerivAt_const x (2 : ℝ)).add (Real.hasDerivAt_exp x)
  change HasDerivAt (fun y : ℝ => 2 + Real.exp y) (0 + Real.exp x) x at h
  change HasDerivAt (fun y : ℝ => 2 + Real.exp y) (Real.exp x) x
  simpa only [zero_add] using h

private theorem derivative_zero_eq {f : ℝ → ℝ}
    (h : ∀ x, HasDerivAt f 0 x) {x y : ℝ} : f x = f y := by
  have hdiff : Differentiable ℝ f := fun z => (h z).differentiableAt
  have hderiv : ∀ z, deriv f z = 0 := fun z => (h z).deriv
  exact is_const_of_deriv_eq_zero hdiff hderiv x y

theorem gap1 (x : ℝ) :
    integrand x = deriv inner x / inner x := by
  have hd : deriv inner x = Real.exp x := (inner_hasDerivAt x).deriv
  rw [hd]
  rfl

theorem gap2 (x : ℝ) :
    HasDerivAt primitive (integrand x) x := by
  have hne : inner x ≠ 0 := by
    have hpos : 0 < inner x := by
      dsimp [inner]
      positivity
    exact ne_of_gt hpos
  simpa [primitive, integrand] using (inner_hasDerivAt x).log hne

theorem gap3 :
    Family integrand Set.univ = Translates primitive Set.univ := by
  ext F
  constructor
  · intro hF
    change (∀ x ∈ Set.univ, HasDerivAt F (integrand x) x) at hF
    change ∃ C, ∀ x ∈ Set.univ, F x = primitive x + C
    let D : ℝ → ℝ := fun x => F x - primitive x
    have hD : ∀ x, HasDerivAt D 0 x := by
      intro x
      simpa [D] using (hF x (Set.mem_univ x)).sub (gap2 x)
    refine ⟨D 0, ?_⟩
    intro x hx
    have hc : D x = D 0 := derivative_zero_eq hD
    dsimp [D] at hc ⊢
    linarith
  · rintro ⟨C, hC⟩
    change ∀ x ∈ Set.univ, HasDerivAt F (integrand x) x
    intro x hx
    have hFC : F = fun y => primitive y + C := by
      funext y
      exact hC y (Set.mem_univ y)
    rw [hFC]
    exact (gap2 x).add_const C

end

end ProofGap.Exercise1690
