import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.MeanValue

open Set Real

namespace ProofGap.Exercise1849

noncomputable section

def integrand (x : ℝ) : ℝ := 1 / Real.sqrt (2 * x ^ 2 - x + 2)

def completedSquareIntegrand (x : ℝ) : ℝ :=
  (1 / Real.sqrt 2) /
    Real.sqrt ((x - 1 / 4 : ℝ) ^ 2 + 15 / 16)

def antiderivatives (g : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | Differentiable ℝ F ∧ ∀ x, deriv F x = g x}

def primitiveFamily (p : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, F = fun x => p x + C}

def primitive (x : ℝ) : ℝ :=
  (1 / Real.sqrt 2) *
    Real.log (x - 1 / 4 +
      Real.sqrt ((x - 1 / 4 : ℝ) ^ 2 + 15 / 16))

private theorem integrand_eq_completedSquareIntegrand :
    integrand = completedSquareIntegrand := by
  funext x
  unfold integrand completedSquareIntegrand
  rw [show 2 * x ^ 2 - x + 2 =
      2 * ((x - 1 / 4 : ℝ) ^ 2 + 15 / 16) by ring]
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  ring

private theorem primitive_hasDerivAt (x : ℝ) :
    HasDerivAt primitive (completedSquareIntegrand x) x := by
  have hu : HasDerivAt (fun y : ℝ => y - 1 / 4) 1 x := by
    convert (hasDerivAt_id x).sub_const (1 / 4) using 1 <;> ring
  have hqpos : 0 < (x - 1 / 4 : ℝ) ^ 2 + 15 / 16 := by
    nlinarith [sq_nonneg (x - 1 / 4)]
  have hq : HasDerivAt
      (fun y : ℝ => (y - 1 / 4) ^ 2 + 15 / 16)
      (2 * (x - 1 / 4)) x := by
    convert (hu.pow 2).add_const (15 / 16) using 1 <;> ring
  have hs :=
    (Real.hasDerivAt_sqrt (ne_of_gt hqpos)).comp x hq
  have hspos : 0 < Real.sqrt ((x - 1 / 4 : ℝ) ^ 2 + 15 / 16) :=
    Real.sqrt_pos.2 hqpos
  have hssq :
      Real.sqrt ((x - 1 / 4 : ℝ) ^ 2 + 15 / 16) ^ 2 =
        (x - 1 / 4 : ℝ) ^ 2 + 15 / 16 :=
    Real.sq_sqrt (le_of_lt hqpos)
  have hhpos :
      0 < x - 1 / 4 +
        Real.sqrt ((x - 1 / 4 : ℝ) ^ 2 + 15 / 16) := by
    by_contra hn
    have hle :
        x - 1 / 4 +
          Real.sqrt ((x - 1 / 4 : ℝ) ^ 2 + 15 / 16) ≤ 0 :=
      le_of_not_gt hn
    have hm :
        0 ≤ (x - 1 / 4 : ℝ) ^ 2 -
          Real.sqrt ((x - 1 / 4 : ℝ) ^ 2 + 15 / 16) ^ 2 := by
      have hp := mul_nonneg
        (neg_nonneg.mpr hle)
        (by linarith [Real.sqrt_nonneg ((x - 1 / 4 : ℝ) ^ 2 + 15 / 16)] :
          0 ≤ Real.sqrt ((x - 1 / 4 : ℝ) ^ 2 + 15 / 16) - (x - 1 / 4))
      nlinarith
    nlinarith
  have hlog :=
    (Real.hasDerivAt_log (ne_of_gt hhpos)).comp x (hu.add hs)
  have hsne :
      Real.sqrt ((x - 1 / 4 : ℝ) ^ 2 + 15 / 16) ≠ 0 :=
    ne_of_gt hspos
  have hhne :
      x - 1 / 4 + Real.sqrt ((x - 1 / 4 : ℝ) ^ 2 + 15 / 16) ≠ 0 :=
    ne_of_gt hhpos
  have hinner :
      1 +
          1 / (2 * Real.sqrt ((x - 1 / 4 : ℝ) ^ 2 + 15 / 16)) *
            (2 * (x - 1 / 4)) =
        (x - 1 / 4 +
          Real.sqrt ((x - 1 / 4 : ℝ) ^ 2 + 15 / 16)) /
          Real.sqrt ((x - 1 / 4 : ℝ) ^ 2 + 15 / 16) := by
    field_simp [hsne]
    <;> ring
  have hcoef :
      (x - 1 / 4 +
          Real.sqrt ((x - 1 / 4 : ℝ) ^ 2 + 15 / 16))⁻¹ *
          (1 +
            1 / (2 * Real.sqrt ((x - 1 / 4 : ℝ) ^ 2 + 15 / 16)) *
              (2 * (x - 1 / 4))) =
        1 / Real.sqrt ((x - 1 / 4 : ℝ) ^ 2 + 15 / 16) := by
    rw [hinner]
    calc
      (x - 1 / 4 +
          Real.sqrt ((x - 1 / 4 : ℝ) ^ 2 + 15 / 16))⁻¹ *
          ((x - 1 / 4 +
            Real.sqrt ((x - 1 / 4 : ℝ) ^ 2 + 15 / 16)) /
            Real.sqrt ((x - 1 / 4 : ℝ) ^ 2 + 15 / 16)) =
        ((x - 1 / 4 +
            Real.sqrt ((x - 1 / 4 : ℝ) ^ 2 + 15 / 16))⁻¹ *
          (x - 1 / 4 +
            Real.sqrt ((x - 1 / 4 : ℝ) ^ 2 + 15 / 16))) /
          Real.sqrt ((x - 1 / 4 : ℝ) ^ 2 + 15 / 16) := by ring
      _ = 1 / Real.sqrt ((x - 1 / 4 : ℝ) ^ 2 + 15 / 16) := by
        rw [inv_mul_cancel₀ hhne]
  rw [hcoef] at hlog
  have hlog' : HasDerivAt
      (fun y : ℝ => Real.log
        (y - 1 / 4 +
          Real.sqrt ((y - 1 / 4 : ℝ) ^ 2 + 15 / 16)))
      (1 / Real.sqrt ((x - 1 / 4 : ℝ) ^ 2 + 15 / 16)) x := by
    simpa only [Function.comp_apply, Pi.add_apply] using hlog
  change HasDerivAt
    (fun y : ℝ => (1 / Real.sqrt 2) *
      Real.log (y - 1 / 4 +
        Real.sqrt ((y - 1 / 4 : ℝ) ^ 2 + 15 / 16)))
    ((1 / Real.sqrt 2) /
      Real.sqrt ((x - 1 / 4 : ℝ) ^ 2 + 15 / 16)) x
  simpa only [div_eq_mul_inv, one_mul] using
    hlog'.const_mul (1 / Real.sqrt 2)

private theorem primitive_differentiable : Differentiable ℝ primitive := by
  intro x
  exact (primitive_hasDerivAt x).differentiableAt

private theorem eq_add_const_of_same_deriv
    {F : ℝ → ℝ}
    (hF : Differentiable ℝ F)
    (hderiv : ∀ x, deriv F x = completedSquareIntegrand x) :
    ∃ C : ℝ, F = fun x => primitive x + C := by
  let H : ℝ → ℝ := fun x => F x - primitive x
  have hHdiff : Differentiable ℝ H :=
    hF.sub primitive_differentiable
  have hHderiv : ∀ x, deriv H x = 0 := by
    intro x
    change deriv (fun y => F y - primitive y) x = 0
    calc
      deriv (fun y => F y - primitive y) x =
          deriv F x - deriv primitive x := by
        simpa only [Pi.sub_apply] using
          deriv_sub (hF x) (primitive_differentiable x)
      _ = 0 := by
        rw [hderiv x, (primitive_hasDerivAt x).deriv]
        ring
  refine ⟨H 0, funext fun x => ?_⟩
  have hx : H x = H 0 :=
    is_const_of_deriv_eq_zero hHdiff hHderiv x 0
  dsimp [H] at hx ⊢
  linarith

theorem gap1 :
    antiderivatives integrand = antiderivatives completedSquareIntegrand := by
  ext F
  simp only [antiderivatives]
  rw [integrand_eq_completedSquareIntegrand]

theorem gap2 :
    antiderivatives completedSquareIntegrand = primitiveFamily primitive := by
  ext F
  constructor
  · rintro ⟨hF, hderiv⟩
    change ∃ C : ℝ, F = fun x => primitive x + C
    exact eq_add_const_of_same_deriv hF hderiv
  · rintro ⟨C, rfl⟩
    constructor
    · exact primitive_differentiable.add (differentiable_const C)
    · intro x
      simpa using ((primitive_hasDerivAt x).add_const C).deriv

theorem gap3 : antiderivatives integrand = primitiveFamily primitive := by
  rw [gap1, gap2]

end

end ProofGap.Exercise1849
