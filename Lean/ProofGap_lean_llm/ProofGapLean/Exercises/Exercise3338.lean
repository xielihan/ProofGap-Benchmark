import ProofGapLean.Prelude.Core
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Comp

namespace ProofGap.Exercise3338

noncomputable section

def secondDeriv (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  deriv (deriv f) x

def z (φ ψ : ℝ → ℝ) (x y : ℝ) : ℝ :=
  φ (x + y) + ψ (x - y)

def partialX (g : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun s => g s y) x

def partialY (g : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun s => g x s) y

def partialXX (g : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun s => partialX g s y) x

def partialYY (g : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun s => partialY g x s) y

theorem gap1 (φ ψ : ℝ → ℝ)
    (hφ : ContDiff ℝ 2 φ) (hψ : ContDiff ℝ 2 ψ) :
    ∀ x y,
      partialX (z φ ψ) x y = deriv φ (x + y) + deriv ψ (x - y) := by
  intro x y
  have hφd : Differentiable ℝ φ := hφ.differentiable (by decide)
  have hψd : Differentiable ℝ ψ := hψ.differentiable (by decide)
  have hleft :=
    hφd.differentiableAt.hasDerivAt.comp x
      ((hasDerivAt_id x).add_const y)
  have hright :=
    hψd.differentiableAt.hasDerivAt.comp x
      ((hasDerivAt_id x).sub_const y)
  unfold partialX z
  simpa [Function.comp_apply] using (hleft.add hright).deriv

theorem gap2 (φ ψ : ℝ → ℝ)
    (hφ : ContDiff ℝ 2 φ) (hψ : ContDiff ℝ 2 ψ) :
    ∀ x y,
      partialY (z φ ψ) x y = deriv φ (x + y) - deriv ψ (x - y) := by
  intro x y
  have hφd : Differentiable ℝ φ := hφ.differentiable (by decide)
  have hψd : Differentiable ℝ ψ := hψ.differentiable (by decide)
  have hleft :=
    hφd.differentiableAt.hasDerivAt.comp y
      ((hasDerivAt_id y).const_add x)
  have hright :=
    hψd.differentiableAt.hasDerivAt.comp y
      (HasDerivAt.const_sub x (hasDerivAt_id y))
  unfold partialY z
  convert (hleft.add hright).deriv using 1
  all_goals simp [sub_eq_add_neg]

theorem gap3 (φ ψ : ℝ → ℝ)
    (hφ : ContDiff ℝ 2 φ) (hψ : ContDiff ℝ 2 ψ) :
    ∀ x y,
      partialXX (z φ ψ) x y =
        secondDeriv φ (x + y) + secondDeriv ψ (x - y) := by
  intro x y
  have hφ1 : ContDiff ℝ 1 (deriv φ) := by exact hφ.deriv'
  have hψ1 : ContDiff ℝ 1 (deriv ψ) := by exact hψ.deriv'
  have hφd : Differentiable ℝ (deriv φ) :=
    hφ1.differentiable (by decide)
  have hψd : Differentiable ℝ (deriv ψ) :=
    hψ1.differentiable (by decide)
  have hleft :=
    hφd.differentiableAt.hasDerivAt.comp x
      ((hasDerivAt_id x).add_const y)
  have hright :=
    hψd.differentiableAt.hasDerivAt.comp x
      ((hasDerivAt_id x).sub_const y)
  unfold partialXX
  rw [show (fun s => partialX (z φ ψ) s y) =
      fun s => deriv φ (s + y) + deriv ψ (s - y) by
    funext s
    exact gap1 φ ψ hφ hψ s y]
  unfold secondDeriv
  simpa [Function.comp_apply] using (hleft.add hright).deriv

theorem gap4 (φ ψ : ℝ → ℝ)
    (hφ : ContDiff ℝ 2 φ) (hψ : ContDiff ℝ 2 ψ) :
    ∀ x y,
      partialYY (z φ ψ) x y =
        secondDeriv φ (x + y) + secondDeriv ψ (x - y) := by
  intro x y
  have hφ1 : ContDiff ℝ 1 (deriv φ) := by exact hφ.deriv'
  have hψ1 : ContDiff ℝ 1 (deriv ψ) := by exact hψ.deriv'
  have hφd : Differentiable ℝ (deriv φ) :=
    hφ1.differentiable (by decide)
  have hψd : Differentiable ℝ (deriv ψ) :=
    hψ1.differentiable (by decide)
  have hleft :=
    hφd.differentiableAt.hasDerivAt.comp y
      ((hasDerivAt_id y).const_add x)
  have hright :=
    hψd.differentiableAt.hasDerivAt.comp y
      (HasDerivAt.const_sub x (hasDerivAt_id y))
  unfold partialYY
  rw [show (fun s => partialY (z φ ψ) x s) =
      fun s => deriv φ (x + s) - deriv ψ (x - s) by
    funext s
    exact gap2 φ ψ hφ hψ x s]
  unfold secondDeriv
  convert (hleft.sub hright).deriv using 1
  all_goals simp [sub_eq_add_neg]

theorem gap5 (φ ψ : ℝ → ℝ)
    (hφ : ContDiff ℝ 2 φ) (hψ : ContDiff ℝ 2 ψ) :
    ∀ x y, partialXX (z φ ψ) x y = partialYY (z φ ψ) x y := by
  intro x y
  exact (gap3 φ ψ hφ hψ x y).trans (gap4 φ ψ hφ hψ x y).symm

theorem gap6 (φ ψ : ℝ → ℝ)
    (hφ : ContDiff ℝ 2 φ) (hψ : ContDiff ℝ 2 ψ) :
    ∀ x y, partialXX (z φ ψ) x y = partialYY (z φ ψ) x y := by
  exact gap5 φ ψ hφ hψ

end

end ProofGap.Exercise3338
