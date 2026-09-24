import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1796

noncomputable section

def integrand (x : ℝ) : ℝ := x ^ 2 * Real.exp (-2 * x)
def primitive (x : ℝ) : ℝ :=
  -(1 / 2 : ℝ) * Real.exp (-2 * x) * (x ^ 2 + x + 1 / 2)
def IsAntiderivative (F f : ℝ → ℝ) : Prop := ∀ x, HasDerivAt F (f x) x
def Family (f : ℝ → ℝ) : Set (ℝ → ℝ) := {F | IsAntiderivative F f}
def Translates (P : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C, ∀ x, F x = P x + C}

private theorem isConst_of_deriv_eq_zero {f : ℝ → ℝ}
    (h : ∀ x, HasDerivAt f 0 x) : ∀ x y, f x = f y := by
  have hf : Differentiable ℝ f := fun x => (h x).differentiableAt
  have hd : ∀ x, deriv f x = 0 := fun x => (h x).deriv
  have hc := is_const_of_deriv_eq_zero hf hd
  intro x y
  exact @hc x y

theorem gap1 (x : ℝ) :
    HasDerivAt (fun y => Real.exp (-2 * y))
      (-2 * Real.exp (-2 * x)) x := by
  convert
    (Real.hasDerivAt_exp (-2 * x)).comp x
      ((hasDerivAt_id x).const_mul (-2 : ℝ)) using 1 <;> ring

theorem gap2 (x : ℝ) :
    HasDerivAt
      (fun y => -(1 / 2 : ℝ) * y ^ 2 * Real.exp (-2 * y))
      (integrand x - x * Real.exp (-2 * x)) x := by
  have hsquare : HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by
    convert (hasDerivAt_id x).mul (hasDerivAt_id x) using 1
    · funext y
      simp only [Pi.mul_apply, id, pow_two]
    · simp only [id]
      ring
  have hscaled :
      HasDerivAt (fun y : ℝ => -(1 / 2 : ℝ) * y ^ 2) (-x) x := by
    convert hsquare.const_mul (-(1 / 2 : ℝ)) using 1 <;> ring
  unfold integrand
  convert hscaled.mul (gap1 x) using 1 <;> ring

theorem gap3 (x : ℝ) :
    HasDerivAt
      (fun y => -(1 / 2 : ℝ) * y * Real.exp (-2 * y))
      (x * Real.exp (-2 * x) - (1 / 2 : ℝ) * Real.exp (-2 * x)) x := by
  convert
    (((hasDerivAt_id x).const_mul (-(1 / 2 : ℝ))).mul (gap1 x))
      using 1
  all_goals
    try simp only [id]
    ring_nf

theorem gap4 (x : ℝ) :
    HasDerivAt
      (fun y =>
        -(1 / 2 : ℝ) * y ^ 2 * Real.exp (-2 * y) -
          (1 / 2 : ℝ) * y * Real.exp (-2 * y))
      (integrand x - (1 / 2 : ℝ) * Real.exp (-2 * x)) x := by
  convert (gap2 x).add (gap3 x) using 1
  · funext y
    simp only [Pi.add_apply]
    ring
  · simp only [integrand]
    ring

theorem gap5 (x : ℝ) :
    HasDerivAt primitive (integrand x) x := by
  convert
    (gap4 x).add ((gap1 x).const_mul (-(1 / 4 : ℝ))) using 1
  · funext y
    simp only [Pi.add_apply, primitive]
    ring
  · simp only [integrand]
    ring

theorem gap6 :
    Family integrand = Translates primitive := by
  ext F
  change IsAntiderivative F integrand ↔ ∃ C, ∀ x, F x = primitive x + C
  constructor
  · intro hF
    have hzero : ∀ x, HasDerivAt (fun y => F y - primitive y) 0 x := by
      intro x
      convert (hF x).sub (gap5 x) using 1 <;> ring
    have hconst := isConst_of_deriv_eq_zero hzero
    refine ⟨F 0 - primitive 0, ?_⟩
    intro x
    have hx : F x - primitive x = F 0 - primitive 0 := hconst x 0
    calc
      F x = primitive x + (F x - primitive x) := by ring
      _ = primitive x + (F 0 - primitive 0) := by rw [hx]
  · rintro ⟨C, hC⟩
    intro x
    have hEq : F = fun y => primitive y + C := funext hC
    rw [hEq]
    exact (gap5 x).add_const C

end

end ProofGap.Exercise1796
