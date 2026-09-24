import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul

namespace ProofGap.Exercise3267

noncomputable section

def t (x y z : ℝ) : ℝ := x * y * z

def u (f : ℝ → ℝ) (x y z : ℝ) : ℝ :=
  f (t x y z)

def iterDeriv (n : ℕ) (f : ℝ → ℝ) : ℝ → ℝ :=
  (deriv^[n]) f

def partialX (g : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  deriv (fun s => g s y z) x

def partialXY (g : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  deriv (fun s => partialX g x s z) y

def partialXYZ (g : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  deriv (fun s => partialXY g x y s) z

def expandedThird (f : ℝ → ℝ) (x y z : ℝ) : ℝ :=
  x ^ 2 * y ^ 2 * z ^ 2 * iterDeriv 3 f (t x y z) +
    2 * x * y * z * iterDeriv 2 f (t x y z) +
    iterDeriv 1 f (t x y z) +
    x * y * z * iterDeriv 2 f (t x y z)

def combinedThird (f : ℝ → ℝ) (x y z : ℝ) : ℝ :=
  x ^ 2 * y ^ 2 * z ^ 2 * iterDeriv 3 f (t x y z) +
    3 * x * y * z * iterDeriv 2 f (t x y z) +
    iterDeriv 1 f (t x y z)

def F (f : ℝ → ℝ) (s : ℝ) : ℝ :=
  s ^ 2 * iterDeriv 3 f s + 3 * s * iterDeriv 2 f s + iterDeriv 1 f s

theorem gap1 (f : ℝ → ℝ) (hf : ContDiff ℝ 3 f) (x y z : ℝ) :
    partialX (u f) x y z =
      y * z * iterDeriv 1 f (t x y z) := by
  have hf1 : Differentiable ℝ f :=
    hf.differentiable (by decide)
  have ht :
      HasDerivAt (fun s : ℝ => t s y z) (y * z) x := by
    simpa [t, mul_assoc] using
      ((hasDerivAt_id x).mul_const y).mul_const z
  have hc :=
    (hf1.differentiableAt.hasDerivAt.comp x ht).deriv
  unfold partialX u
  simpa [iterDeriv, mul_comm] using hc

theorem gap2 (f : ℝ → ℝ) (hf : ContDiff ℝ 3 f) (x y z : ℝ) :
    partialXY (u f) x y z =
      y * z * iterDeriv 2 f (t x y z) * x * z +
        z * iterDeriv 1 f (t x y z) := by
  have hdf : ContDiff ℝ 2 (deriv f) := by
    exact hf.deriv'
  have ht :
      HasDerivAt (fun s : ℝ => t x s z) (x * z) y := by
    simpa [t, mul_assoc] using
      HasDerivAt.const_mul x ((hasDerivAt_id y).mul_const z)
  have hcomp :=
    (hdf.differentiable (by decide)).differentiableAt.hasDerivAt.comp y ht
  have hprod :=
    ((hasDerivAt_id y).mul_const z).mul hcomp
  unfold partialXY
  rw [show (fun s => partialX (u f) x s z) =
      fun s => s * z * iterDeriv 1 f (t x s z) by
    funext s
    exact gap1 f hf x s z]
  have hd := hprod.deriv
  have hsource :
      ((fun s : ℝ => id s * z) *
          (deriv f ∘ fun s => t x s z)) =
        (fun s => s * z * iterDeriv 1 f (t x s z)) := by
    funext s
    simp [iterDeriv]
  rw [hsource] at hd
  simp only [Function.comp_apply] at hd
  rw [hd]
  simp [iterDeriv]
  ring

theorem gap3 (f : ℝ → ℝ) (hf : ContDiff ℝ 3 f) (x y z : ℝ) :
    partialXYZ (u f) x y z = expandedThird f x y z := by
  have hdf : ContDiff ℝ 2 (deriv f) := by
    exact hf.deriv'
  have hddf : ContDiff ℝ 1 (deriv (deriv f)) := by
    exact hdf.deriv'
  have ht :
      HasDerivAt (fun s : ℝ => t x y s) (x * y) z := by
    simpa [t, mul_assoc] using
      HasDerivAt.const_mul (x * y) (hasDerivAt_id z)
  have hd2comp :=
    (hddf.differentiable (by decide)).differentiableAt.hasDerivAt.comp z ht
  have hd1comp :=
    (hdf.differentiable (by decide)).differentiableAt.hasDerivAt.comp z ht
  have hfirst :=
    ((((HasDerivAt.const_mul y (hasDerivAt_id z)).mul hd2comp).mul_const x).mul
      (hasDerivAt_id z))
  have hsecond :=
    (hasDerivAt_id z).mul hd1comp
  have hsum := hfirst.add hsecond
  unfold partialXYZ
  rw [show (fun s => partialXY (u f) x y s) =
      fun s =>
        y * s * iterDeriv 2 f (t x y s) * x * s +
          s * iterDeriv 1 f (t x y s) by
    funext s
    exact gap2 f hf x y s]
  unfold expandedThird
  convert hsum.deriv using 1
  all_goals
    simp [iterDeriv, Function.comp_apply]
    ring

theorem gap4 (f : ℝ → ℝ) (x y z : ℝ) :
    expandedThird f x y z = combinedThird f x y z := by
  unfold expandedThird combinedThird
  ring

theorem gap5 (f : ℝ → ℝ) (hf : ContDiff ℝ 3 f) (x y z : ℝ) :
    partialXYZ (u f) x y z = combinedThird f x y z := by
  exact (gap3 f hf x y z).trans (gap4 f x y z)

theorem gap6 (f : ℝ → ℝ) (hf : ContDiff ℝ 3 f) (x y z : ℝ) :
    partialXYZ (u f) x y z = F f (t x y z) := by
  rw [gap5 f hf x y z]
  unfold combinedThird F t
  ring

theorem gap7 (f : ℝ → ℝ) (x y z : ℝ) :
    ∃ G : ℝ → ℝ, G = F f ∧
      combinedThird f x y z = G (t x y z) := by
  refine ⟨F f, rfl, ?_⟩
  unfold combinedThird F t
  ring

theorem gap8 (f : ℝ → ℝ) (hf : ContDiff ℝ 3 f) (x y z : ℝ) :
    ∃ G : ℝ → ℝ, G = F f ∧
      partialXYZ (u f) x y z = G (t x y z) := by
  exact ⟨F f, rfl, gap6 f hf x y z⟩

theorem gap9 (f : ℝ → ℝ) (hf : ContDiff ℝ 3 f) :
    ∃ t' : ℝ → ℝ → ℝ → ℝ, ∃ G : ℝ → ℝ,
      t' = t ∧ G = F f ∧
        ∀ x y z,
          partialXYZ (u f) x y z = G (t' x y z) ∧
            t' x y z = x * y * z := by
  refine ⟨t, F f, rfl, rfl, ?_⟩
  intro x y z
  exact ⟨gap6 f hf x y z, rfl⟩

end

end ProofGap.Exercise3267
