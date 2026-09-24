import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

namespace ProofGap.Exercise1772

noncomputable section

def subst (x : ℝ) : ℝ := Real.cos x ^ 2
def integrand (x : ℝ) : ℝ :=
  Real.sin x * Real.cos x ^ 3 / (1 + Real.cos x ^ 2)
def intermediate (x : ℝ) : ℝ :=
  -(1 / 2 : ℝ) * subst x + (1 / 2 : ℝ) * Real.log (1 + subst x)
def primitive (x : ℝ) : ℝ :=
  -(1 / 2 : ℝ) * Real.cos x ^ 2 +
    (1 / 2 : ℝ) * Real.log (1 + Real.cos x ^ 2)
def IsAntiderivative (F f : ℝ → ℝ) : Prop := ∀ x, HasDerivAt F (f x) x
def Family (f : ℝ → ℝ) : Set (ℝ → ℝ) := {F | IsAntiderivative F f}
def Translates (P : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C, ∀ x, F x = P x + C}

private theorem subst_hasDerivAt (x : ℝ) :
    HasDerivAt subst (-2 * Real.sin x * Real.cos x) x := by
  convert (Real.hasDerivAt_cos x).pow 2 using 1 <;>
    simp [subst] <;> ring

theorem gap1 (x : ℝ) :
    Real.sin x * Real.cos x = -(1 / 2 : ℝ) * deriv subst x := by
  have h := subst_hasDerivAt x
  rw [h.deriv]
  ring

theorem gap2 (x : ℝ) :
    integrand x =
      -(1 / 2 : ℝ) * (subst x / (1 + subst x)) * deriv subst x := by
  calc
    integrand x =
        (Real.sin x * Real.cos x) *
          (subst x / (1 + subst x)) := by
      unfold integrand subst
      ring
    _ = (-(1 / 2 : ℝ) * deriv subst x) *
          (subst x / (1 + subst x)) := by
      rw [gap1 x]
    _ = -(1 / 2 : ℝ) * (subst x / (1 + subst x)) *
          deriv subst x := by
      ring

theorem gap3 (x : ℝ) :
    subst x / (1 + subst x) = 1 - 1 / (1 + subst x) := by
  have hpos : 0 < 1 + subst x := by
    unfold subst
    nlinarith [sq_nonneg (Real.cos x)]
  have hne : 1 + subst x ≠ 0 := ne_of_gt hpos
  field_simp [hne] <;> ring

theorem gap4 (x : ℝ) :
    HasDerivAt intermediate (integrand x) x := by
  have hs0 := subst_hasDerivAt x
  have hs : HasDerivAt subst (deriv subst x) x := by
    rw [hs0.deriv]
    exact hs0
  have hinner0 := (hasDerivAt_const x (1 : ℝ)).add hs
  change HasDerivAt (fun y : ℝ => 1 + subst y)
    (0 + deriv subst x) x at hinner0
  have hinner :
      HasDerivAt (fun y : ℝ => 1 + subst y) (deriv subst x) x := by
    simpa only [zero_add] using hinner0
  have hpos : 0 < 1 + subst x := by
    unfold subst
    nlinarith [sq_nonneg (Real.cos x)]
  have hlog :
      HasDerivAt (fun y : ℝ => Real.log (1 + subst y))
        (deriv subst x / (1 + subst x)) x := by
    simpa [Function.comp_def, div_eq_mul_inv, mul_comm] using
      (Real.hasDerivAt_log hpos.ne').comp x hinner
  have hint0 :=
    (hs.const_mul (-(1 / 2 : ℝ))).add
      (hlog.const_mul (1 / 2 : ℝ))
  change HasDerivAt intermediate
    (-(1 / 2 : ℝ) * deriv subst x +
      (1 / 2 : ℝ) * (deriv subst x / (1 + subst x))) x at hint0
  have hv :
      -(1 / 2 : ℝ) * deriv subst x +
          (1 / 2 : ℝ) * (deriv subst x / (1 + subst x)) =
        integrand x := by
    rw [gap2 x, gap3 x]
    ring
  rw [← hv]
  exact hint0

theorem gap5 (x : ℝ) :
    intermediate x = primitive x := by
  rfl

theorem gap6 :
    Family integrand = Translates primitive := by
  have hip : intermediate = primitive := funext gap5
  have hp : ∀ x, HasDerivAt primitive (integrand x) x := by
    intro x
    rw [← hip]
    exact gap4 x
  ext F
  change IsAntiderivative F integrand ↔
    ∃ C, ∀ x, F x = primitive x + C
  constructor
  · intro hF
    change ∀ x, HasDerivAt F (integrand x) x at hF
    let G : ℝ → ℝ := fun y => F y - primitive y
    have hG : ∀ y, HasDerivAt G 0 y := by
      intro y
      simpa [G] using (hF y).sub (hp y)
    have hGdiff : Differentiable ℝ G :=
      fun y => (hG y).differentiableAt
    have hGderiv : ∀ y, deriv G y = 0 :=
      fun y => (hG y).deriv
    have hconst : ∀ y z : ℝ, G y = G z :=
      is_const_of_deriv_eq_zero hGdiff hGderiv
    refine ⟨G 0, ?_⟩
    intro x
    have hx := hconst x 0
    dsimp [G] at hx ⊢
    linarith
  · rintro ⟨C, hC⟩
    change ∀ x, HasDerivAt F (integrand x) x
    have hfun : F = fun y => primitive y + C := funext hC
    intro x
    have hadd :
        HasDerivAt (fun y => primitive y + C) (integrand x) x :=
      (hp x).add_const C
    rw [← hfun] at hadd
    exact hadd

end

end ProofGap.Exercise1772
