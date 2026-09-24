import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1678

noncomputable section

def inner (x : ℝ) : ℝ := x ^ 2
def integrand (x : ℝ) : ℝ := x / (4 + x ^ 4)
def primitive (x : ℝ) : ℝ := (1 / 4 : ℝ) * Real.arctan (x ^ 2 / 2)

def IsAntiderivativeOn (F f : ℝ → ℝ) (s : Set ℝ) : Prop :=
  ∀ x ∈ s, HasDerivAt F (f x) x
def Family (f : ℝ → ℝ) (s : Set ℝ) : Set (ℝ → ℝ) :=
  {F | IsAntiderivativeOn F f s}
def Translates (P : ℝ → ℝ) (s : Set ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C, ∀ x ∈ s, F x = P x + C}

private theorem isConst_of_deriv_eq_zero
    {G : ℝ → ℝ}
    (hGdiff : Differentiable ℝ G)
    (hGderiv : ∀ x, deriv G x = 0) :
    ∀ x y : ℝ, G x = G y := by
  exact is_const_of_deriv_eq_zero hGdiff hGderiv

theorem gap1 (x : ℝ) :
    integrand x = (1 / 2 : ℝ) * deriv inner x / (2 ^ 2 + inner x ^ 2) := by
  have hid : HasDerivAt (fun y : ℝ => y) 1 x := hasDerivAt_id x
  have hsq : HasDerivAt (fun y : ℝ => y * y) (x + x) x := by
    simpa using hid.mul hid
  have hfun : (fun y : ℝ => y * y) = inner := by
    funext y
    simp [inner, pow_two]
  have hinner : HasDerivAt inner (2 * x) x := by
    rw [← hfun]
    simpa [two_mul] using hsq
  rw [hinner.deriv]
  unfold integrand inner
  ring

theorem gap2 (x : ℝ) :
    HasDerivAt primitive (integrand x) x := by
  have hu : HasDerivAt (fun y : ℝ => y ^ 2 / 2) x x := by
    simpa using ((hasDerivAt_id x).pow 2).div_const 2
  have ha := (Real.hasDerivAt_arctan (x ^ 2 / 2)).comp x hu
  have h₁ : 4 + x ^ 4 ≠ 0 := by positivity
  have h₂ : 1 + (x ^ 2 / 2) ^ 2 ≠ 0 := by positivity
  have hp : HasDerivAt
      (fun y : ℝ => (1 / 4 : ℝ) * Real.arctan (y ^ 2 / 2))
      ((1 / 4 : ℝ) * (1 / (1 + (x ^ 2 / 2) ^ 2) * x)) x := by
    simpa [Function.comp_def] using ha.const_mul (1 / 4 : ℝ)
  have hcoeff :
      (1 / 4 : ℝ) * (1 / (1 + (x ^ 2 / 2) ^ 2) * x) = integrand x := by
    unfold integrand
    field_simp [h₁, h₂] <;> ring
  rw [← hcoeff]
  change HasDerivAt
    (fun y : ℝ => (1 / 4 : ℝ) * Real.arctan (y ^ 2 / 2))
    ((1 / 4 : ℝ) * (1 / (1 + (x ^ 2 / 2) ^ 2) * x)) x
  exact hp

theorem gap3 :
    Family integrand Set.univ = Translates primitive Set.univ := by
  ext F
  constructor
  · intro hF
    change IsAntiderivativeOn F integrand Set.univ at hF
    change ∃ C, ∀ x ∈ Set.univ, F x = primitive x + C
    let G : ℝ → ℝ := fun x => F x - primitive x
    have hG : ∀ x, HasDerivAt G 0 x := by
      intro x
      simpa [G] using (hF x (Set.mem_univ x)).sub (gap2 x)
    have hGdiff : Differentiable ℝ G := fun x => (hG x).differentiableAt
    have hGderiv : ∀ x, deriv G x = 0 := fun x => (hG x).deriv
    have hconst : ∀ x y : ℝ, G x = G y :=
      isConst_of_deriv_eq_zero hGdiff hGderiv
    refine ⟨F 0 - primitive 0, ?_⟩
    intro x hx
    have h := hconst x 0
    dsimp [G] at h
    calc
      F x = primitive x + (F x - primitive x) := by ring
      _ = primitive x + (F 0 - primitive 0) := by rw [h]
  · intro hF
    change ∃ C, ∀ x ∈ Set.univ, F x = primitive x + C at hF
    change IsAntiderivativeOn F integrand Set.univ
    rcases hF with ⟨C, hC⟩
    have hEq : F = fun y => primitive y + C := by
      funext y
      exact hC y (Set.mem_univ y)
    intro x hx
    rw [hEq]
    exact (gap2 x).add_const C

end

end ProofGap.Exercise1678
