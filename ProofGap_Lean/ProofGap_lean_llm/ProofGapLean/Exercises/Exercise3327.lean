import ProofGapLean.Prelude.Core
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul

namespace ProofGap.Exercise3327

noncomputable section

def secondDeriv (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  deriv (deriv f) x

def u (φ ψ : ℝ → ℝ) (x y : ℝ) : ℝ :=
  x * φ (x + y) + y * ψ (x + y)

def partialX (g : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun s => g s y) x

def partialY (g : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun s => g x s) y

def partialXX (g : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun s => partialX g s y) x

def partialXY (g : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun s => partialX g x s) y

def partialYY (g : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun s => partialY g x s) y

private theorem hasDerivAt_add_right
    (f : ℝ → ℝ) (hf : Differentiable ℝ f) (x c : ℝ) :
    HasDerivAt (fun s => f (s + c)) (deriv f (x + c)) x := by
  simpa [Function.comp_def] using
    hf.differentiableAt.hasDerivAt.comp x
      ((hasDerivAt_id x).add_const c)

private theorem hasDerivAt_add_left
    (f : ℝ → ℝ) (hf : Differentiable ℝ f) (c x : ℝ) :
    HasDerivAt (fun s => f (c + s)) (deriv f (c + x)) x := by
  simpa [Function.comp_def] using
    hf.differentiableAt.hasDerivAt.comp x
      ((hasDerivAt_const x c).add (hasDerivAt_id x))

theorem gap1 (φ ψ : ℝ → ℝ)
    (hφ : ContDiff ℝ 2 φ) (hψ : ContDiff ℝ 2 ψ) :
    ∀ x y,
      partialX (u φ ψ) x y =
        φ (x + y) + y * deriv ψ (x + y) + x * deriv φ (x + y) := by
  intro x y
  have hφs := hasDerivAt_add_right φ
    (hφ.differentiable (by decide)) x y
  have hψs := hasDerivAt_add_right ψ
    (hψ.differentiable (by decide)) x y
  have h :=
    ((hasDerivAt_id x).mul hφs).add
      ((hasDerivAt_const x y).mul hψs)
  unfold partialX u
  convert h.deriv using 1 <;> simp [id] <;> ring

theorem gap2 (φ ψ : ℝ → ℝ)
    (hφ : ContDiff ℝ 2 φ) (hψ : ContDiff ℝ 2 ψ) :
    ∀ x y,
      partialY (u φ ψ) x y =
        x * deriv φ (x + y) + ψ (x + y) + y * deriv ψ (x + y) := by
  intro x y
  have hφs := hasDerivAt_add_left φ
    (hφ.differentiable (by decide)) x y
  have hψs := hasDerivAt_add_left ψ
    (hψ.differentiable (by decide)) x y
  have h :=
    ((hasDerivAt_const y x).mul hφs).add
      ((hasDerivAt_id y).mul hψs)
  unfold partialY u
  convert h.deriv using 1 <;> simp [id] <;> ring

theorem gap3 (φ ψ : ℝ → ℝ)
    (hφ : ContDiff ℝ 2 φ) (hψ : ContDiff ℝ 2 ψ) :
    ∀ x y,
      partialXX (u φ ψ) x y =
        2 * deriv φ (x + y) + y * secondDeriv ψ (x + y) +
          x * secondDeriv φ (x + y) := by
  intro x y
  unfold partialXX
  rw [show (fun s => partialX (u φ ψ) s y) =
      fun s =>
        φ (s + y) + y * deriv ψ (s + y) + s * deriv φ (s + y) by
    funext s
    exact gap1 φ ψ hφ hψ s y]
  have hφs := hasDerivAt_add_right φ
    (hφ.differentiable (by decide)) x y
  have hψ2s := hasDerivAt_add_right (deriv ψ)
    hψ.differentiable_deriv_two x y
  have hφ2s := hasDerivAt_add_right (deriv φ)
    hφ.differentiable_deriv_two x y
  have h :=
    (hφs.add ((hasDerivAt_const x y).mul hψ2s)).add
      ((hasDerivAt_id x).mul hφ2s)
  convert h.deriv using 1 <;> simp [secondDeriv, id] <;> ring

theorem gap4 (φ ψ : ℝ → ℝ)
    (hφ : ContDiff ℝ 2 φ) (hψ : ContDiff ℝ 2 ψ) :
    ∀ x y,
      partialXY (u φ ψ) x y =
        deriv φ (x + y) + deriv ψ (x + y) +
          y * secondDeriv ψ (x + y) +
          x * secondDeriv φ (x + y) := by
  intro x y
  unfold partialXY
  rw [show (fun s => partialX (u φ ψ) x s) =
      fun s =>
        φ (x + s) + s * deriv ψ (x + s) + x * deriv φ (x + s) by
    funext s
    exact gap1 φ ψ hφ hψ x s]
  have hφs := hasDerivAt_add_left φ
    (hφ.differentiable (by decide)) x y
  have hψ2s := hasDerivAt_add_left (deriv ψ)
    hψ.differentiable_deriv_two x y
  have hφ2s := hasDerivAt_add_left (deriv φ)
    hφ.differentiable_deriv_two x y
  have h :=
    (hφs.add ((hasDerivAt_id y).mul hψ2s)).add
      ((hasDerivAt_const y x).mul hφ2s)
  convert h.deriv using 1 <;> simp [secondDeriv, id] <;> ring

theorem gap5 (φ ψ : ℝ → ℝ)
    (hφ : ContDiff ℝ 2 φ) (hψ : ContDiff ℝ 2 ψ) :
    ∀ x y,
      partialYY (u φ ψ) x y =
        x * secondDeriv φ (x + y) + 2 * deriv ψ (x + y) +
          y * secondDeriv ψ (x + y) := by
  intro x y
  unfold partialYY
  rw [show (fun s => partialY (u φ ψ) x s) =
      fun s =>
        x * deriv φ (x + s) + ψ (x + s) + s * deriv ψ (x + s) by
    funext s
    exact gap2 φ ψ hφ hψ x s]
  have hφ2s := hasDerivAt_add_left (deriv φ)
    hφ.differentiable_deriv_two x y
  have hψs := hasDerivAt_add_left ψ
    (hψ.differentiable (by decide)) x y
  have hψ2s := hasDerivAt_add_left (deriv ψ)
    hψ.differentiable_deriv_two x y
  have h :=
    (((hasDerivAt_const y x).mul hφ2s).add hψs).add
      ((hasDerivAt_id y).mul hψ2s)
  convert h.deriv using 1 <;> simp [secondDeriv, id] <;> ring

theorem gap6 (φ ψ : ℝ → ℝ)
    (hφ : ContDiff ℝ 2 φ) (hψ : ContDiff ℝ 2 ψ) :
    ∀ x y,
      partialXX (u φ ψ) x y - 2 * partialXY (u φ ψ) x y +
        partialYY (u φ ψ) x y = 0 := by
  intro x y
  rw [gap3 φ ψ hφ hψ x y, gap4 φ ψ hφ hψ x y,
    gap5 φ ψ hφ hψ x y]
  ring

theorem gap7 (φ ψ : ℝ → ℝ)
    (hφ : ContDiff ℝ 2 φ) (hψ : ContDiff ℝ 2 ψ) :
    ∀ x y,
      partialXX (u φ ψ) x y - 2 * partialXY (u φ ψ) x y +
        partialYY (u φ ψ) x y = 0 := by
  exact gap6 φ ψ hφ hψ

end

end ProofGap.Exercise3327
