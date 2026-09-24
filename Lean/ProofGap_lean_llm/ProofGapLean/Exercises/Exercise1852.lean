import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.MeanValue

open Set Real

namespace ProofGap.Exercise1852

noncomputable section

def integrand (x : ℝ) : ℝ := (x + 1) / Real.sqrt (x ^ 2 + x + 1)

def splitIntegrand (x : ℝ) : ℝ :=
  (2 * x + 1) / (2 * Real.sqrt (x ^ 2 + x + 1)) +
    1 / (2 * Real.sqrt (x ^ 2 + x + 1))

def antiderivatives (g : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | Differentiable ℝ F ∧ ∀ x, deriv F x = g x}

def primitiveFamily (p : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, F = fun x => p x + C}

def primitive (x : ℝ) : ℝ :=
  Real.sqrt (x ^ 2 + x + 1) +
    (1 / 2 : ℝ) *
      Real.log (x + 1 / 2 + Real.sqrt (x ^ 2 + x + 1))

private theorem primitive_hasDerivAt (x : ℝ) :
    HasDerivAt primitive (splitIntegrand x) x := by
  have hq : 0 < x ^ 2 + x + 1 := by
    nlinarith [sq_nonneg (x + 1 / 2)]
  have hspos : 0 < Real.sqrt (x ^ 2 + x + 1) := Real.sqrt_pos.2 hq
  have hsq : (Real.sqrt (x ^ 2 + x + 1)) ^ 2 = x ^ 2 + x + 1 :=
    Real.sq_sqrt hq.le
  have hu : 0 < x + 1 / 2 + Real.sqrt (x ^ 2 + x + 1) := by
    have hprod :
        (Real.sqrt (x ^ 2 + x + 1) + (x + 1 / 2)) *
            (Real.sqrt (x ^ 2 + x + 1) - (x + 1 / 2)) = (3 / 4 : ℝ) := by
      nlinarith [hsq]
    by_contra hn
    have hleft : Real.sqrt (x ^ 2 + x + 1) + (x + 1 / 2) ≤ 0 := by
      nlinarith [le_of_not_gt hn]
    have hright : 0 < Real.sqrt (x ^ 2 + x + 1) - (x + 1 / 2) := by
      nlinarith [hspos]
    have hmul := mul_nonpos_of_nonpos_of_nonneg hleft hright.le
    nlinarith [hprod]
  have hpoly :
      HasDerivAt (fun y : ℝ => y ^ 2 + y + 1) (2 * x + 1) x := by
    convert
      (((hasDerivAt_id x).mul (hasDerivAt_id x)).add
        (hasDerivAt_id x)).add_const (1 : ℝ) using 1
    · funext y
      dsimp
      ring
    · dsimp
      ring
  have hsqrt :
      HasDerivAt
        (fun y : ℝ => Real.sqrt (y ^ 2 + y + 1))
        ((2 * x + 1) / (2 * Real.sqrt (x ^ 2 + x + 1))) x := by
    convert (Real.hasDerivAt_sqrt (ne_of_gt hq)).comp x hpoly using 1 <;>
      simp [div_eq_mul_inv, mul_comm]
  have huDeriv :
      HasDerivAt
        (fun y : ℝ => y + 1 / 2 + Real.sqrt (y ^ 2 + y + 1))
        (1 + (2 * x + 1) / (2 * Real.sqrt (x ^ 2 + x + 1))) x := by
    convert
      ((hasDerivAt_id x).add_const (1 / 2 : ℝ)).add hsqrt using 1 <;> ring
  have hlog :
      HasDerivAt
        (fun y : ℝ =>
          Real.log (y + 1 / 2 + Real.sqrt (y ^ 2 + y + 1)))
        ((1 + (2 * x + 1) / (2 * Real.sqrt (x ^ 2 + x + 1))) /
          (x + 1 / 2 + Real.sqrt (x ^ 2 + x + 1))) x := by
    convert (Real.hasDerivAt_log (ne_of_gt hu)).comp x huDeriv using 1 <;>
      simp [div_eq_mul_inv, mul_comm]
  have hraw :
      HasDerivAt primitive
        ((2 * x + 1) / (2 * Real.sqrt (x ^ 2 + x + 1)) +
          (1 / 2 : ℝ) *
            ((1 + (2 * x + 1) / (2 * Real.sqrt (x ^ 2 + x + 1))) /
              (x + 1 / 2 + Real.sqrt (x ^ 2 + x + 1)))) x := by
    convert hsqrt.add (hlog.const_mul (1 / 2 : ℝ)) using 1
  have hnum :
      1 + (2 * x + 1) / (2 * Real.sqrt (x ^ 2 + x + 1)) =
        (x + 1 / 2 + Real.sqrt (x ^ 2 + x + 1)) /
          Real.sqrt (x ^ 2 + x + 1) := by
    let s : ℝ := Real.sqrt (x ^ 2 + x + 1)
    have hs : 0 < s := by
      simpa [s] using hspos
    change 1 + (2 * x + 1) / (2 * s) = (x + 1 / 2 + s) / s
    field_simp [ne_of_gt hs] <;> ring
  have hlogFactor :
      (1 + (2 * x + 1) / (2 * Real.sqrt (x ^ 2 + x + 1))) /
          (x + 1 / 2 + Real.sqrt (x ^ 2 + x + 1)) =
        1 / Real.sqrt (x ^ 2 + x + 1) := by
    rw [hnum]
    apply (div_eq_iff (ne_of_gt hu)).2
    ring
  convert hraw using 1
  unfold splitIntegrand
  rw [hlogFactor]
  field_simp [ne_of_gt hspos] <;> ring

theorem gap1 : antiderivatives integrand = antiderivatives splitIntegrand := by
  have h : integrand = splitIntegrand := by
    funext x
    unfold integrand splitIntegrand
    ring
  rw [h]

theorem gap2 :
    antiderivatives splitIntegrand = primitiveFamily primitive := by
  ext F
  simp only [antiderivatives, primitiveFamily, mem_setOf_eq]
  constructor
  · rintro ⟨hF, hder⟩
    have hGder : ∀ x, HasDerivAt (fun y => F y - primitive y) 0 x := by
      intro x
      simpa [hder x] using
        ((hF x).hasDerivAt.sub (primitive_hasDerivAt x))
    have hG : Differentiable ℝ (fun y => F y - primitive y) :=
      fun x => (hGder x).differentiableAt
    have hconst :=
      is_const_of_deriv_eq_zero hG (fun x => (hGder x).deriv)
    refine ⟨F 0 - primitive 0, funext ?_⟩
    intro x
    have hx := hconst x 0
    linarith
  · rintro ⟨C, rfl⟩
    constructor
    · exact fun x => ((primitive_hasDerivAt x).add_const C).differentiableAt
    · exact fun x => ((primitive_hasDerivAt x).add_const C).deriv

theorem gap3 : antiderivatives integrand = primitiveFamily primitive := by
  exact gap1.trans gap2

end

end ProofGap.Exercise1852
