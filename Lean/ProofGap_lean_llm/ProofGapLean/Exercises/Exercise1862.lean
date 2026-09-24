import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.MeanValue

open Set Real

namespace ProofGap.Exercise1862

noncomputable section

def integrand (x : ℝ) : ℝ := Real.sqrt (x ^ 2 + x + 2)

def completedSquareIntegrand (x : ℝ) : ℝ :=
  Real.sqrt (7 / 4 + (x + 1 / 2) ^ 2)

def antiderivatives (g : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | Differentiable ℝ F ∧ ∀ x, deriv F x = g x}

def primitiveFamily (p : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, F = fun x => p x + C}

def primitive (x : ℝ) : ℝ :=
  ((2 * x + 1) / 4) * Real.sqrt (x ^ 2 + x + 2) +
    (7 / 8 : ℝ) *
      Real.log (x + 1 / 2 + Real.sqrt (x ^ 2 + x + 2))

private theorem primitive_hasDerivAt (x : ℝ) :
    HasDerivAt primitive (integrand x) x := by
  have hq : 0 < x ^ 2 + x + 2 := by
    nlinarith [sq_nonneg (x + 1 / 2)]
  let s : ℝ := Real.sqrt (x ^ 2 + x + 2)
  have hs : 0 < s := by
    dsimp [s]
    exact Real.sqrt_pos.2 hq
  have hs_sq : s ^ 2 = x ^ 2 + x + 2 := by
    dsimp [s]
    exact Real.sq_sqrt hq.le
  have hpoly :
      HasDerivAt (fun y : ℝ => y ^ 2 + y + 2) (2 * x + 1) x := by
    convert ((((hasDerivAt_id x).pow 2).add (hasDerivAt_id x)).add_const 2) using 1 <;>
      simp [id_eq] <;> ring
  have hsqrt :
      HasDerivAt (fun y : ℝ => Real.sqrt (y ^ 2 + y + 2))
        ((1 / (2 * s)) * (2 * x + 1)) x := by
    exact (Real.hasDerivAt_sqrt hq.ne').comp x hpoly
  have hcoef :
      HasDerivAt (fun y : ℝ => (2 * y + 1) / 4) (1 / 2) x := by
    convert ((((hasDerivAt_id x).const_mul 2).add_const 1).div_const 4) using 1 <;>
      norm_num
  have hshift :
      HasDerivAt (fun y : ℝ => y + 1 / 2) 1 x :=
    (hasDerivAt_id x).add_const (1 / 2)
  have hinside_ne : x + 1 / 2 + s ≠ 0 := by
    intro h
    nlinarith [hs_sq]
  have hlog0 :
      HasDerivAt
        (fun y : ℝ => Real.log (y + 1 / 2 + Real.sqrt (y ^ 2 + y + 2)))
        ((x + 1 / 2 + s)⁻¹ *
          (1 + (1 / (2 * s)) * (2 * x + 1))) x := by
    exact (Real.hasDerivAt_log hinside_ne).comp x (hshift.add hsqrt)
  have hnum :
      1 + (1 / (2 * s)) * (2 * x + 1) =
        (x + 1 / 2 + s) * (1 / s) := by
    field_simp [hs.ne'] <;> ring
  have hlog_coeff :
      (x + 1 / 2 + s)⁻¹ *
          (1 + (1 / (2 * s)) * (2 * x + 1)) =
        1 / s := by
    rw [hnum, ← mul_assoc, inv_mul_cancel₀ hinside_ne, one_mul]
  rw [hlog_coeff] at hlog0
  have hlog :
      HasDerivAt
        (fun y : ℝ => Real.log (y + 1 / 2 + Real.sqrt (y ^ 2 + y + 2)))
        (1 / s) x := hlog0
  have hraw :
      HasDerivAt primitive
        ((1 / 2) * s +
          ((2 * x + 1) / 4) * ((1 / (2 * s)) * (2 * x + 1)) +
          (7 / 8) * (1 / s)) x := by
    simpa only [primitive] using
      (hcoef.mul hsqrt).add (hlog.const_mul (7 / 8))
  have hid :
      4 * s ^ 2 + (2 * x + 1) ^ 2 + 7 = 8 * s ^ 2 := by
    nlinarith [hs_sq]
  have hderiv :
      (1 / 2) * s +
          ((2 * x + 1) / 4) * ((1 / (2 * s)) * (2 * x + 1)) +
          (7 / 8) * (1 / s) = s := by
    calc
      _ = (4 * s ^ 2 + (2 * x + 1) ^ 2 + 7) / (8 * s) := by
        field_simp [hs.ne'] <;> ring
      _ = s := by
        rw [hid]
        field_simp [hs.ne'] <;> ring
  rw [hderiv] at hraw
  simpa [s, integrand] using hraw

theorem gap1 :
    antiderivatives integrand = antiderivatives completedSquareIntegrand := by
  apply congrArg antiderivatives
  funext x
  unfold integrand completedSquareIntegrand
  congr 1
  ring

theorem gap2 : antiderivatives integrand = primitiveFamily primitive := by
  ext F
  constructor
  · rintro ⟨hF, hFderiv⟩
    let D : ℝ → ℝ := fun x => F x - primitive x
    have hD' : ∀ x, HasDerivAt D 0 x := by
      intro x
      simpa [D, hFderiv x] using
        ((hF x).hasDerivAt.sub (primitive_hasDerivAt x))
    have hD : Differentiable ℝ D :=
      fun x => (hD' x).differentiableAt
    have hDderiv : ∀ x, deriv D x = 0 :=
      fun x => (hD' x).deriv
    refine ⟨F 0 - primitive 0, ?_⟩
    funext x
    have hx : D x = D 0 :=
      is_const_of_deriv_eq_zero hD hDderiv x 0
    dsimp [D] at hx ⊢
    linarith
  · rintro ⟨C, rfl⟩
    constructor
    · intro x
      exact (primitive_hasDerivAt x).differentiableAt.add
        ((differentiable_const C) x)
    · intro x
      exact ((primitive_hasDerivAt x).add_const C).deriv

end

end ProofGap.Exercise1862
