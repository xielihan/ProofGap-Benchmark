import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Topology.Neighborhoods
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1174

noncomputable section

def nthDeriv : ℕ → (ℝ → ℝ) → ℝ → ℝ
  | 0, f => f
  | n + 1, f => deriv (nthDeriv n f)

def y (x : ℝ) : ℝ := Real.exp x * Real.log x
def differential (n : ℕ) (f : ℝ → ℝ) (x dx : ℝ) : ℝ :=
  nthDeriv n f x * dx ^ n

def fourthCoeff (x : ℝ) : ℝ :=
  Real.exp x *
    (Real.log x + 4 / x - 6 / x ^ 2 + 8 / x ^ 3 - 6 / x ^ 4)

private def firstForm (x : ℝ) : ℝ :=
  Real.exp x * (Real.log x + 1 / x)

private def secondForm (x : ℝ) : ℝ :=
  Real.exp x * (Real.log x + 2 / x - 1 / x ^ 2)

private def thirdForm (x : ℝ) : ℝ :=
  Real.exp x * (Real.log x + 3 / x - 3 / x ^ 2 + 2 / x ^ 3)

private theorem nthDeriv_four_y {x : ℝ} (hx : 0 < x) :
    nthDeriv 4 y x = fourthCoeff x := by
  have h1 : ∀ z : ℝ, 0 < z → deriv y z = firstForm z := by
    intro z hz
    have hz0 : z ≠ 0 := ne_of_gt hz
    convert ((Real.hasDerivAt_exp z).mul (Real.hasDerivAt_log hz0)).deriv using 1 <;>
      simp [y, firstForm] <;>
      field_simp [hz0] <;>
      ring
  have h2 : ∀ z : ℝ, 0 < z → deriv (deriv y) z = secondForm z := by
    intro z hz
    have hz0 : z ≠ 0 := ne_of_gt hz
    have heq : deriv y =ᶠ[nhds z] firstForm :=
      (eventually_gt_nhds hz).mono (fun w hw => h1 w hw)
    have hd : deriv firstForm z = secondForm z := by
      convert ((Real.hasDerivAt_exp z).mul
        ((Real.hasDerivAt_log hz0).add
          ((hasDerivAt_const (x := z) (1 : ℝ)).div
            (hasDerivAt_id z) hz0))).deriv using 1 <;>
        simp [firstForm, secondForm] <;>
        field_simp [hz0] <;>
        ring
    calc
      deriv (deriv y) z = deriv firstForm z := heq.deriv_eq
      _ = secondForm z := hd
  have h3 : ∀ z : ℝ, 0 < z → deriv (deriv (deriv y)) z = thirdForm z := by
    intro z hz
    have hz0 : z ≠ 0 := ne_of_gt hz
    have heq : deriv (deriv y) =ᶠ[nhds z] secondForm :=
      (eventually_gt_nhds hz).mono (fun w hw => h2 w hw)
    have hd : deriv secondForm z = thirdForm z := by
      convert ((Real.hasDerivAt_exp z).mul
        (((Real.hasDerivAt_log hz0).add
          ((hasDerivAt_const (x := z) (2 : ℝ)).div
            (hasDerivAt_id z) hz0)).sub
          ((hasDerivAt_const (x := z) (1 : ℝ)).div
            ((hasDerivAt_id z).pow 2) (pow_ne_zero 2 hz0)))).deriv using 1 <;>
        simp [secondForm, thirdForm] <;>
        field_simp [hz0] <;>
        ring
    calc
      deriv (deriv (deriv y)) z = deriv secondForm z := heq.deriv_eq
      _ = thirdForm z := hd
  have h4 : ∀ z : ℝ, 0 < z →
      deriv (deriv (deriv (deriv y))) z = fourthCoeff z := by
    intro z hz
    have hz0 : z ≠ 0 := ne_of_gt hz
    have heq : deriv (deriv (deriv y)) =ᶠ[nhds z] thirdForm :=
      (eventually_gt_nhds hz).mono (fun w hw => h3 w hw)
    have hd : deriv thirdForm z = fourthCoeff z := by
      convert ((Real.hasDerivAt_exp z).mul
        ((((Real.hasDerivAt_log hz0).add
          ((hasDerivAt_const (x := z) (3 : ℝ)).div
            (hasDerivAt_id z) hz0)).sub
          ((hasDerivAt_const (x := z) (3 : ℝ)).div
            ((hasDerivAt_id z).pow 2) (pow_ne_zero 2 hz0))).add
          ((hasDerivAt_const (x := z) (2 : ℝ)).div
            ((hasDerivAt_id z).pow 3) (pow_ne_zero 3 hz0)))).deriv using 1 <;>
        simp [thirdForm, fourthCoeff] <;>
        field_simp [hz0] <;>
        ring
    calc
      deriv (deriv (deriv (deriv y))) z = deriv thirdForm z := heq.deriv_eq
      _ = fourthCoeff z := hd
  simpa [nthDeriv] using h4 x hx

theorem gap1 (x dx : ℝ) (hx : 0 < x) :
    differential 4 y x dx = nthDeriv 4 y x * dx ^ 4 := by
  rfl

theorem gap2 (x dx : ℝ) (hx : 0 < x) :
    nthDeriv 4 y x * dx ^ 4 =
      fourthCoeff x * dx ^ 4 := by
  rw [nthDeriv_four_y hx]

theorem gap3 (x dx : ℝ) (hx : 0 < x) :
    differential 4 y x dx = fourthCoeff x * dx ^ 4 := by
  calc
    differential 4 y x dx = nthDeriv 4 y x * dx ^ 4 := gap1 x dx hx
    _ = fourthCoeff x * dx ^ 4 := gap2 x dx hx

end

end ProofGap.Exercise1174
