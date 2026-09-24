import ProofGapLean.Prelude.Core
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul

namespace ProofGap.Exercise3326

noncomputable section

def secondDeriv (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  deriv (deriv f) x

def u (a : ℝ) (φ ψ : ℝ → ℝ) (x t : ℝ) : ℝ :=
  φ (x - a * t) + ψ (x + a * t)

def partialX (g : ℝ → ℝ → ℝ) (x t : ℝ) : ℝ :=
  deriv (fun s => g s t) x

def partialXX (g : ℝ → ℝ → ℝ) (x t : ℝ) : ℝ :=
  deriv (fun s => partialX g s t) x

def partialT (g : ℝ → ℝ → ℝ) (x t : ℝ) : ℝ :=
  deriv (fun s => g x s) t

def partialTT (g : ℝ → ℝ → ℝ) (x t : ℝ) : ℝ :=
  deriv (fun s => partialT g x s) t

private lemma partialT_formula3326 (a : ℝ) (φ ψ : ℝ → ℝ)
    (hφ : ContDiff ℝ 2 φ) (hψ : ContDiff ℝ 2 ψ) (x t : ℝ) :
    partialT (u a φ ψ) x t =
      -a * deriv φ (x - a * t) + a * deriv ψ (x + a * t) := by
  have hφ1 : Differentiable ℝ φ := hφ.differentiable (by decide)
  have hψ1 : Differentiable ℝ ψ := hψ.differentiable (by decide)
  have hminus : HasDerivAt (fun s : ℝ => x - a * s) (-a) t := by
    convert (hasDerivAt_const t x).sub
      ((hasDerivAt_id t).const_mul a) using 1 <;> ring
  have hplus : HasDerivAt (fun s : ℝ => x + a * s) a t := by
    convert (hasDerivAt_const t x).add
      ((hasDerivAt_id t).const_mul a) using 1 <;> ring
  have hleft := hφ1.differentiableAt.hasDerivAt.comp t hminus
  have hright := hψ1.differentiableAt.hasDerivAt.comp t hplus
  unfold partialT u
  convert (hleft.add hright).deriv using 1 <;> ring

private lemma partialX_formula3326 (a : ℝ) (φ ψ : ℝ → ℝ)
    (hφ : ContDiff ℝ 2 φ) (hψ : ContDiff ℝ 2 ψ) (x t : ℝ) :
    partialX (u a φ ψ) x t =
      deriv φ (x - a * t) + deriv ψ (x + a * t) := by
  have hφ1 : Differentiable ℝ φ := hφ.differentiable (by decide)
  have hψ1 : Differentiable ℝ ψ := hψ.differentiable (by decide)
  have hminus : HasDerivAt (fun s : ℝ => s - a * t) 1 x := by
    convert (hasDerivAt_id x).sub (hasDerivAt_const x (a * t)) using 1 <;>
      ring
  have hplus : HasDerivAt (fun s : ℝ => s + a * t) 1 x := by
    convert (hasDerivAt_id x).add (hasDerivAt_const x (a * t)) using 1 <;>
      ring
  have hleft := hφ1.differentiableAt.hasDerivAt.comp x hminus
  have hright := hψ1.differentiableAt.hasDerivAt.comp x hplus
  unfold partialX u
  convert (hleft.add hright).deriv using 1 <;> ring

theorem gap1 (a : ℝ) (φ ψ : ℝ → ℝ)
    (hφ : ContDiff ℝ 2 φ) (hψ : ContDiff ℝ 2 ψ) :
    ∀ x t,
      partialTT (u a φ ψ) x t =
        a ^ 2 * secondDeriv φ (x - a * t) +
          a ^ 2 * secondDeriv ψ (x + a * t) := by
  intro x t
  have hφd : ContDiff ℝ 1 (deriv φ) := hφ.deriv'
  have hψd : ContDiff ℝ 1 (deriv ψ) := hψ.deriv'
  have hminus : HasDerivAt (fun s : ℝ => x - a * s) (-a) t := by
    convert (hasDerivAt_const t x).sub
      ((hasDerivAt_id t).const_mul a) using 1 <;> ring
  have hplus : HasDerivAt (fun s : ℝ => x + a * s) a t := by
    convert (hasDerivAt_const t x).add
      ((hasDerivAt_id t).const_mul a) using 1 <;> ring
  have hleft :=
    hφd.differentiable (by decide) |>.differentiableAt.hasDerivAt.comp t hminus
  have hright :=
    hψd.differentiable (by decide) |>.differentiableAt.hasDerivAt.comp t hplus
  unfold partialTT
  rw [show (fun s => partialT (u a φ ψ) x s) =
      fun s => -a * deriv φ (x - a * s) +
        a * deriv ψ (x + a * s) by
    funext s
    exact partialT_formula3326 a φ ψ hφ hψ x s]
  convert ((hleft.const_mul (-a)).add
    (hright.const_mul a)).deriv using 1
  · unfold secondDeriv
    ring

theorem gap2 (a : ℝ) (φ ψ : ℝ → ℝ)
    (hφ : ContDiff ℝ 2 φ) (hψ : ContDiff ℝ 2 ψ) :
    ∀ x t,
      partialXX (u a φ ψ) x t =
        secondDeriv φ (x - a * t) +
          secondDeriv ψ (x + a * t) := by
  intro x t
  have hφd : ContDiff ℝ 1 (deriv φ) := hφ.deriv'
  have hψd : ContDiff ℝ 1 (deriv ψ) := hψ.deriv'
  have hminus : HasDerivAt (fun s : ℝ => s - a * t) 1 x := by
    convert (hasDerivAt_id x).sub (hasDerivAt_const x (a * t)) using 1 <;>
      ring
  have hplus : HasDerivAt (fun s : ℝ => s + a * t) 1 x := by
    convert (hasDerivAt_id x).add (hasDerivAt_const x (a * t)) using 1 <;>
      ring
  have hleft :=
    hφd.differentiable (by decide) |>.differentiableAt.hasDerivAt.comp x hminus
  have hright :=
    hψd.differentiable (by decide) |>.differentiableAt.hasDerivAt.comp x hplus
  unfold partialXX
  rw [show (fun s => partialX (u a φ ψ) s t) =
      fun s => deriv φ (s - a * t) + deriv ψ (s + a * t) by
    funext s
    exact partialX_formula3326 a φ ψ hφ hψ s t]
  convert (hleft.add hright).deriv using 1 <;>
    unfold secondDeriv <;> ring

theorem gap3 (a : ℝ) (φ ψ : ℝ → ℝ)
    (hφ : ContDiff ℝ 2 φ) (hψ : ContDiff ℝ 2 ψ) :
    ∀ x t,
      partialTT (u a φ ψ) x t =
        a ^ 2 * partialXX (u a φ ψ) x t := by
  intro x t
  rw [gap1 a φ ψ hφ hψ x t, gap2 a φ ψ hφ hψ x t]
  ring

theorem gap4 (a : ℝ) (φ ψ : ℝ → ℝ)
    (hφ : ContDiff ℝ 2 φ) (hψ : ContDiff ℝ 2 ψ) :
    ∀ x t,
      partialTT (u a φ ψ) x t =
        a ^ 2 * partialXX (u a φ ψ) x t := by
  exact gap3 a φ ψ hφ hψ

end

end ProofGap.Exercise3326
