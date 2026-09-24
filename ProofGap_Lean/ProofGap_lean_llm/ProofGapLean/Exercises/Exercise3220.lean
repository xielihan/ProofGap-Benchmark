import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Defs.Filter

namespace ProofGap.Exercise3220

noncomputable section

def u (x y : ℝ) : ℝ :=
  Real.rpow x y

def partialX (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => f t y) x

def partialY (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => f x t) y

def secondXX (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => partialX f t y) x

def secondYY (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => partialY f x t) y

def mixedXY (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => partialX f x t) y

private theorem hasDerivAt_rpow_exponent_pos (x y : ℝ) (hx : 0 < x) :
    HasDerivAt (fun t : ℝ => Real.rpow x t)
      (Real.rpow x y * Real.log x) y := by
  have hfun :
      (fun t : ℝ => Real.rpow x t) =
        (fun t : ℝ => Real.exp (t * Real.log x)) := by
    funext t
    simpa [mul_comm] using Real.rpow_def_of_pos hx t
  rw [hfun]
  simpa [Real.rpow_def_of_pos hx y, mul_comm] using
    ((Real.hasDerivAt_exp (y * Real.log x)).comp y
      ((hasDerivAt_id y).mul_const (Real.log x)))

theorem gap1 :
    ∀ x y : ℝ, u x y = Real.rpow x y := by
  intro x y
  rfl

theorem gap2 :
    ∀ x y : ℝ, 0 < x →
      Real.rpow x y = Real.exp (y * Real.log x) := by
  intro x y hx
  simpa [mul_comm] using Real.rpow_def_of_pos hx y

theorem gap3 :
    ∀ x y : ℝ, 0 < x →
      u x y = Real.exp (y * Real.log x) := by
  intro x y hx
  simpa [u] using gap2 x y hx

theorem gap4 :
    ∀ x y : ℝ, 0 < x →
      partialX u x y = y * Real.rpow x (y - 1) := by
  intro x y hx
  unfold partialX u
  exact
    (Real.hasDerivAt_rpow_const (p := y)
      (Or.inl (ne_of_gt hx))).deriv

theorem gap5 :
    ∀ x y : ℝ, 0 < x →
      partialY u x y =
        Real.exp (y * Real.log x) * Real.log x := by
  intro x y hx
  change deriv (fun t : ℝ => Real.rpow x t) y = _
  rw [← gap2 x y hx]
  exact (hasDerivAt_rpow_exponent_pos x y hx).deriv

theorem gap6 :
    ∀ y x : ℝ, 0 < x →
      Real.exp (y * Real.log x) * Real.log x =
        Real.rpow x y * Real.log x := by
  intro y x hx
  rw [gap2 x y hx]

theorem gap7 :
    ∀ x y : ℝ, 0 < x →
      partialY u x y = Real.rpow x y * Real.log x := by
  intro x y hx
  calc
    partialY u x y =
        Real.exp (y * Real.log x) * Real.log x := gap5 x y hx
    _ = Real.rpow x y * Real.log x := gap6 y x hx

theorem gap8 :
    ∀ x y : ℝ, 0 < x →
      secondXX u x y =
        y * (y - 1) * Real.rpow x (y - 2) := by
  intro x y hx
  unfold secondXX
  have heq :
      (fun t : ℝ => partialX u t y) =ᶠ[nhds x]
        (fun t : ℝ => y * Real.rpow t (y - 1)) := by
    filter_upwards [Ioi_mem_nhds hx] with t ht
    exact gap4 t y ht
  have hd0 :=
    (Real.hasDerivAt_rpow_const (p := y - 1)
      (Or.inl (ne_of_gt hx))).const_mul y
  have hexp : y - 1 - 1 = y - 2 := by
    ring
  rw [hexp] at hd0
  have hd :
      HasDerivAt (fun t : ℝ => y * Real.rpow t (y - 1))
        (y * (y - 1) * Real.rpow x (y - 2)) x := by
    simpa only [mul_assoc] using hd0
  calc
    deriv (fun t : ℝ => partialX u t y) x =
        deriv (fun t : ℝ => y * Real.rpow t (y - 1)) x := heq.deriv_eq
    _ = y * (y - 1) * Real.rpow x (y - 2) := hd.deriv

theorem gap9 :
    ∀ x y : ℝ, 0 < x →
      secondYY u x y =
        Real.rpow x y * Real.log x ^ 2 := by
  intro x y hx
  unfold secondYY
  have hfun :
      (fun t : ℝ => partialY u x t) =
        (fun t : ℝ => Real.rpow x t * Real.log x) := by
    funext t
    exact gap7 x t hx
  rw [hfun]
  simpa [pow_two, mul_assoc] using
    ((hasDerivAt_rpow_exponent_pos x y hx).mul_const
      (Real.log x)).deriv

theorem gap10 :
    ∀ x y : ℝ, 0 < x →
      mixedXY u x y =
        Real.rpow x (y - 1) +
          y * Real.rpow x (y - 1) * Real.log x := by
  intro x y hx
  unfold mixedXY
  have hfun :
      (fun t : ℝ => partialX u x t) =
        (fun t : ℝ => t * Real.rpow x (t - 1)) := by
    funext t
    exact gap4 x t hx
  rw [hfun]
  have hp :
      HasDerivAt (fun t : ℝ => Real.rpow x (t - 1))
        (Real.rpow x (y - 1) * Real.log x) y := by
    simpa using
      ((hasDerivAt_rpow_exponent_pos x (y - 1) hx).comp y
        ((hasDerivAt_id y).sub_const 1))
  simpa only [one_mul, mul_one, mul_assoc] using
    ((hasDerivAt_id y).mul hp).deriv

theorem gap11 :
    ∀ x y : ℝ, 0 < x →
      Real.rpow x (y - 1) +
          y * Real.rpow x (y - 1) * Real.log x =
        Real.rpow x (y - 1) * (1 + y * Real.log x) := by
  intro x y hx
  ring

theorem gap12 :
    ∀ x y : ℝ, 0 < x →
      mixedXY u x y =
        Real.rpow x (y - 1) * (1 + y * Real.log x) := by
  intro x y hx
  calc
    mixedXY u x y =
        Real.rpow x (y - 1) +
          y * Real.rpow x (y - 1) * Real.log x := gap10 x y hx
    _ = Real.rpow x (y - 1) * (1 + y * Real.log x) :=
      gap11 x y hx

end

end ProofGap.Exercise3220
