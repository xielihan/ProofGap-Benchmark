import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1920

noncomputable section

def branch : Set ℝ := Set.univ
def integrand (x : ℝ) := (x ^ 4 + 1) / (x ^ 6 + 1)
def rewrittenIntegrand (x : ℝ) :=
  (x ^ 4 - x ^ 2 + 1 + x ^ 2) / (x ^ 6 + 1)
def firstPart (x : ℝ) :=
  (x ^ 4 - x ^ 2 + 1) / ((x ^ 2 + 1) * (x ^ 4 - x ^ 2 + 1))
def secondPart (x : ℝ) := x ^ 2 / (x ^ 6 + 1)
def atanIntegrand (x : ℝ) := 1 / (x ^ 2 + 1)
def cubicAtanIntegrand (x : ℝ) :=
  1 / ((x ^ 3) ^ 2 + 1) * deriv (fun t : ℝ => t ^ 3) x
def primitive (x : ℝ) :=
  Real.arctan x + (1 / 3 : ℝ) * Real.arctan (x ^ 3)
def AntiderivativesOn (f : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∀ x ∈ branch, HasDerivAt F (f x) x}
def SplitFamily (f g : ℝ → ℝ) (c d : ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ G ∈ AntiderivativesOn f, ∃ H ∈ AntiderivativesOn g,
    ∀ x ∈ branch, F x = c * G x + d * H x}
def PrimitiveFamily : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x ∈ branch, F x = primitive x + C}

private theorem hasDerivAt_cube (x : ℝ) :
    HasDerivAt (fun t : ℝ => t ^ 3) (3 * x ^ 2) x := by
  simpa using (hasDerivAt_id x).pow 3

private theorem rewrittenIntegrand_eq_parts (x : ℝ) :
    rewrittenIntegrand x = firstPart x + secondPart x := by
  have hfactor :
      x ^ 6 + 1 = (x ^ 2 + 1) * (x ^ 4 - x ^ 2 + 1) := by
    ring
  unfold rewrittenIntegrand firstPart secondPart
  rw [hfactor]
  ring

private theorem firstPart_eq_atanIntegrand (x : ℝ) :
    firstPart x = atanIntegrand x := by
  have h1 : x ^ 2 + 1 ≠ 0 := by
    nlinarith [sq_nonneg x]
  have hq : x ^ 4 - x ^ 2 + 1 ≠ 0 := by
    nlinarith [sq_nonneg (x ^ 2 - (1 / 2 : ℝ))]
  have hprod :
      (x ^ 2 + 1) * (x ^ 4 - x ^ 2 + 1) ≠ 0 :=
    mul_ne_zero h1 hq
  unfold firstPart atanIntegrand
  apply (div_eq_iff hprod).2
  field_simp [h1] <;> ring

private theorem secondPart_eq_cubicAtanIntegrand (x : ℝ) :
    secondPart x = (1 / 3 : ℝ) * cubicAtanIntegrand x := by
  have hp := hasDerivAt_cube x
  have h6 : x ^ 6 + 1 ≠ 0 := by
    nlinarith [sq_nonneg (x ^ 3)]
  have hc : (x ^ 3) ^ 2 + 1 ≠ 0 := by
    nlinarith [sq_nonneg (x ^ 3)]
  unfold secondPart cubicAtanIntegrand
  rw [hp.deriv]
  field_simp [h6, hc]

private theorem integrand_eq_atan_parts (x : ℝ) :
    integrand x = atanIntegrand x + (1 / 3 : ℝ) * cubicAtanIntegrand x := by
  calc
    integrand x = rewrittenIntegrand x := by
      unfold integrand rewrittenIntegrand
      ring
    _ = firstPart x + secondPart x := rewrittenIntegrand_eq_parts x
    _ = atanIntegrand x + (1 / 3 : ℝ) * cubicAtanIntegrand x := by
      rw [firstPart_eq_atanIntegrand, secondPart_eq_cubicAtanIntegrand]

private theorem hasDerivAt_atanIntegrand (x : ℝ) :
    HasDerivAt Real.arctan (atanIntegrand x) x := by
  simpa [atanIntegrand, one_div, add_comm] using Real.hasDerivAt_arctan x

private theorem hasDerivAt_cubicArctan (x : ℝ) :
    HasDerivAt (fun t : ℝ => Real.arctan (t ^ 3))
      (cubicAtanIntegrand x) x := by
  have hp := hasDerivAt_cube x
  have h := (Real.hasDerivAt_arctan (x ^ 3)).comp x hp
  simpa [cubicAtanIntegrand, hp.deriv, one_div, add_comm] using h

private theorem hasDerivAt_primitive (x : ℝ) :
    HasDerivAt primitive (integrand x) x := by
  have h := (hasDerivAt_atanIntegrand x).add
    ((hasDerivAt_cubicArctan x).const_mul (1 / 3 : ℝ))
  have hv := integrand_eq_atan_parts x
  simpa only [primitive, hv] using h

private theorem antiderivatives_eq_split_of_sum
    (f g h Q : ℝ → ℝ) (d : ℝ)
    (hfg : ∀ x, f x = g x + d * h x)
    (hQ : ∀ x, HasDerivAt Q (h x) x) :
    AntiderivativesOn f = SplitFamily g h 1 d := by
  ext F
  constructor
  · intro hF
    let G : ℝ → ℝ := fun y => F y - d * Q y
    refine ⟨G, ?_, Q, ?_, ?_⟩
    · intro x hx
      have hd := (hF x hx).sub ((hQ x).const_mul d)
      have heq : f x - d * h x = g x := by
        rw [hfg x]
        ring
      simpa only [G, heq] using hd
    · intro x hx
      exact hQ x
    · intro x hx
      simp only [G]
      ring
  · rintro ⟨G, hG, H, hH, hEq⟩
    have hFEq : F = fun y => G y + d * H y := by
      funext y
      simpa using hEq y (by simp [branch])
    rw [hFEq]
    intro x hx
    have hd := (hG x hx).add ((hH x hx).const_mul d)
    simpa only [hfg x] using hd

private theorem antiderivativesOn_integrand_eq_primitiveFamily :
    AntiderivativesOn integrand = PrimitiveFamily := by
  ext F
  constructor
  · intro hF
    let D : ℝ → ℝ := fun x => F x - primitive x
    have hD : ∀ x, HasDerivAt D 0 x := by
      intro x
      have hd := (hF x (by simp [branch])).sub (hasDerivAt_primitive x)
      simpa only [D, sub_self] using hd
    have hdiff : Differentiable ℝ D := fun x => (hD x).differentiableAt
    have hconst : ∀ x y : ℝ, D x = D y :=
      is_const_of_deriv_eq_zero hdiff (fun x => (hD x).deriv)
    let C : ℝ := D 0
    refine ⟨C, ?_⟩
    intro x hx
    have hc : D x = C := hconst x 0
    dsimp only [D] at hc
    linarith
  · rintro ⟨C, hC⟩
    have hFEq : F = fun x => primitive x + C := by
      funext x
      exact hC x (by simp [branch])
    rw [hFEq]
    intro x hx
    exact (hasDerivAt_primitive x).add_const C

theorem gap1 :
    AntiderivativesOn integrand = AntiderivativesOn rewrittenIntegrand := by
  apply congrArg AntiderivativesOn
  funext x
  unfold integrand rewrittenIntegrand
  ring
theorem gap2 :
    AntiderivativesOn rewrittenIntegrand =
      SplitFamily firstPart secondPart 1 1 := by
  apply antiderivatives_eq_split_of_sum
    rewrittenIntegrand firstPart secondPart
    (fun x : ℝ => (1 / 3 : ℝ) * Real.arctan (x ^ 3)) 1
  · intro x
    simpa using rewrittenIntegrand_eq_parts x
  · intro x
    have h := (hasDerivAt_cubicArctan x).const_mul (1 / 3 : ℝ)
    simpa only [secondPart_eq_cubicAtanIntegrand x] using h
theorem gap3 :
    AntiderivativesOn integrand =
      SplitFamily firstPart secondPart 1 1 := by
  calc
    AntiderivativesOn integrand = AntiderivativesOn rewrittenIntegrand := gap1
    _ = SplitFamily firstPart secondPart 1 1 := gap2
theorem gap4 :
    AntiderivativesOn integrand =
      SplitFamily atanIntegrand cubicAtanIntegrand 1 (1 / 3) := by
  apply antiderivatives_eq_split_of_sum
    integrand atanIntegrand cubicAtanIntegrand
    (fun x : ℝ => Real.arctan (x ^ 3)) (1 / 3 : ℝ)
  · exact integrand_eq_atan_parts
  · exact hasDerivAt_cubicArctan
theorem gap5 :
    SplitFamily atanIntegrand cubicAtanIntegrand 1 (1 / 3) =
      PrimitiveFamily := by
  calc
    SplitFamily atanIntegrand cubicAtanIntegrand 1 (1 / 3) =
        AntiderivativesOn integrand := gap4.symm
    _ = PrimitiveFamily := antiderivativesOn_integrand_eq_primitiveFamily
theorem gap6 :
    AntiderivativesOn integrand = PrimitiveFamily := by
  exact antiderivativesOn_integrand_eq_primitiveFamily

end
end ProofGap.Exercise1920
