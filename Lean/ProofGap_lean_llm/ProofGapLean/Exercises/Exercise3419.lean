import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Prod

namespace ProofGap.Exercise3419

noncomputable section

def partial1 (f : ℝ → ℝ → ℝ → ℝ → ℝ) (x y z t : ℝ) : ℝ :=
  deriv (fun s => f s y z t) x

def partial2 (f : ℝ → ℝ → ℝ → ℝ → ℝ) (x y z t : ℝ) : ℝ :=
  deriv (fun s => f x s z t) y

def partial3 (f : ℝ → ℝ → ℝ → ℝ → ℝ) (x y z t : ℝ) : ℝ :=
  deriv (fun s => f x y s t) z

def partial4 (f : ℝ → ℝ → ℝ → ℝ → ℝ) (x y z t : ℝ) : ℝ :=
  deriv (fun s => f x y z s) t

def partialX (u : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun s => u s y) x

def partialY (u : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun s => u x s) y

def differential (u : ℝ → ℝ → ℝ) (x y dx dy : ℝ) : ℝ :=
  partialX u x y * dx + partialY u x y * dy

def implicitDifferential (f : ℝ → ℝ → ℝ → ℝ → ℝ)
    (z t : ℝ → ℝ → ℝ) (x y dx dy : ℝ) : ℝ :=
  partial1 f x y (z x y) (t x y) * dx +
    partial2 f x y (z x y) (t x y) * dy +
    partial3 f x y (z x y) (t x y) * differential z x y dx dy +
    partial4 f x y (z x y) (t x y) * differential t x y dx dy

def jacobian13 (f g : ℝ → ℝ → ℝ → ℝ → ℝ)
    (x y z t : ℝ) : ℝ :=
  partial1 f x y z t * partial4 g x y z t -
    partial4 f x y z t * partial1 g x y z t

def jacobian23 (f g : ℝ → ℝ → ℝ → ℝ → ℝ)
    (x y z t : ℝ) : ℝ :=
  partial2 f x y z t * partial4 g x y z t -
    partial4 f x y z t * partial2 g x y z t

def jacobian34 (f g : ℝ → ℝ → ℝ → ℝ → ℝ)
    (x y z t : ℝ) : ℝ :=
  partial3 f x y z t * partial4 g x y z t -
    partial4 f x y z t * partial3 g x y z t

private theorem implicitDifferential_vanishes
    (f : ℝ → ℝ → ℝ → ℝ → ℝ) (z t : ℝ → ℝ → ℝ)
    (hEq : ∀ x y, f x y (z x y) (t x y) = 0)
    (hf : Differentiable ℝ
      (fun p : ℝ × (ℝ × (ℝ × ℝ)) => f p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hz : Differentiable ℝ (Function.uncurry z))
    (ht : Differentiable ℝ (Function.uncurry t)) :
    ∀ x y dx dy, implicitDifferential f z t x y dx dy = 0 := by
  intro x y dx dy
  let F : ℝ × (ℝ × (ℝ × ℝ)) → ℝ :=
    fun p => f p.1 p.2.1 p.2.2.1 p.2.2.2
  let p : ℝ × (ℝ × (ℝ × ℝ)) :=
    (x, (y, (z x y, t x y)))
  let L : (ℝ × (ℝ × (ℝ × ℝ))) →L[ℝ] ℝ := fderiv ℝ F p
  have hF : Differentiable ℝ F := by
    simpa [F] using hf
  have hxyX : DifferentiableAt ℝ (fun s : ℝ => (s, y)) x := by
    exact differentiableAt_id.prodMk
      (differentiableAt_const (x := x) (c := y))
  have hxyY : DifferentiableAt ℝ (fun s : ℝ => (x, s)) y := by
    exact (differentiableAt_const (x := y) (c := x)).prodMk
      differentiableAt_id
  have hzXDiff : DifferentiableAt ℝ (fun s : ℝ => z s y) x := by
    simpa [Function.comp_def, Function.uncurry] using
      (hz (x, y)).comp x hxyX
  have htXDiff : DifferentiableAt ℝ (fun s : ℝ => t s y) x := by
    simpa [Function.comp_def, Function.uncurry] using
      (ht (x, y)).comp x hxyX
  have hzYDiff : DifferentiableAt ℝ (fun s : ℝ => z x s) y := by
    simpa [Function.comp_def, Function.uncurry] using
      (hz (x, y)).comp y hxyY
  have htYDiff : DifferentiableAt ℝ (fun s : ℝ => t x s) y := by
    simpa [Function.comp_def, Function.uncurry] using
      (ht (x, y)).comp y hxyY
  have hzX : HasDerivAt (fun s : ℝ => z s y) (partialX z x y) x := by
    simpa [partialX] using hzXDiff.hasDerivAt
  have htX : HasDerivAt (fun s : ℝ => t s y) (partialX t x y) x := by
    simpa [partialX] using htXDiff.hasDerivAt
  have hzY : HasDerivAt (fun s : ℝ => z x s) (partialY z x y) y := by
    simpa [partialY] using hzYDiff.hasDerivAt
  have htY : HasDerivAt (fun s : ℝ => t x s) (partialY t x y) y := by
    simpa [partialY] using htYDiff.hasDerivAt
  have hqX :=
    (hasDerivAt_id x).hasFDerivAt.prodMk
      ((hasDerivAt_const (x := x) (c := y)).hasFDerivAt.prodMk
        (hzX.hasFDerivAt.prodMk htX.hasFDerivAt))
  have hqY :=
    (hasDerivAt_const (x := y) (c := x)).hasFDerivAt.prodMk
      ((hasDerivAt_id y).hasFDerivAt.prodMk
        (hzY.hasFDerivAt.prodMk htY.hasFDerivAt))
  have htotalX :
      HasDerivAt (fun s : ℝ => f s y (z s y) (t s y))
        (L (1, (0, (partialX z x y, partialX t x y)))) x := by
    simpa [F, p, L, Function.comp_def] using
      ((hF p).hasFDerivAt.comp x hqX).hasDerivAt
  have htotalY :
      HasDerivAt (fun s : ℝ => f x s (z x s) (t x s))
        (L (0, (1, (partialY z x y, partialY t x y)))) y := by
    simpa [F, p, L, Function.comp_def] using
      ((hF p).hasFDerivAt.comp y hqY).hasDerivAt
  have hq1 :=
    (hasDerivAt_id x).hasFDerivAt.prodMk
      ((hasDerivAt_const (x := x) (c := y)).hasFDerivAt.prodMk
        ((hasDerivAt_const (x := x) (c := z x y)).hasFDerivAt.prodMk
          (hasDerivAt_const (x := x) (c := t x y)).hasFDerivAt))
  have hq2 :=
    (hasDerivAt_const (x := y) (c := x)).hasFDerivAt.prodMk
      ((hasDerivAt_id y).hasFDerivAt.prodMk
        ((hasDerivAt_const (x := y) (c := z x y)).hasFDerivAt.prodMk
          (hasDerivAt_const (x := y) (c := t x y)).hasFDerivAt))
  have hq3 :=
    (hasDerivAt_const (x := z x y) (c := x)).hasFDerivAt.prodMk
      ((hasDerivAt_const (x := z x y) (c := y)).hasFDerivAt.prodMk
        ((hasDerivAt_id (z x y)).hasFDerivAt.prodMk
          (hasDerivAt_const (x := z x y) (c := t x y)).hasFDerivAt))
  have hq4 :=
    (hasDerivAt_const (x := t x y) (c := x)).hasFDerivAt.prodMk
      ((hasDerivAt_const (x := t x y) (c := y)).hasFDerivAt.prodMk
        ((hasDerivAt_const (x := t x y) (c := z x y)).hasFDerivAt.prodMk
          (hasDerivAt_id (t x y)).hasFDerivAt))
  have hf1 :
      partial1 f x y (z x y) (t x y) = L (1, (0, (0, 0))) := by
    unfold partial1
    simpa [F, p, L, Function.comp_def] using
      ((hF p).hasFDerivAt.comp x hq1).hasDerivAt.deriv
  have hf2 :
      partial2 f x y (z x y) (t x y) = L (0, (1, (0, 0))) := by
    unfold partial2
    simpa [F, p, L, Function.comp_def] using
      ((hF p).hasFDerivAt.comp y hq2).hasDerivAt.deriv
  have hf3 :
      partial3 f x y (z x y) (t x y) = L (0, (0, (1, 0))) := by
    unfold partial3
    simpa [F, p, L, Function.comp_def] using
      ((hF p).hasFDerivAt.comp (z x y) hq3).hasDerivAt.deriv
  have hf4 :
      partial4 f x y (z x y) (t x y) = L (0, (0, (0, 1))) := by
    unfold partial4
    simpa [F, p, L, Function.comp_def] using
      ((hF p).hasFDerivAt.comp (t x y) hq4).hasDerivAt.deriv
  have hzeroXDeriv : deriv (fun s : ℝ => f s y (z s y) (t s y)) x = 0 := by
    have heq : (fun s : ℝ => f s y (z s y) (t s y)) = fun _ : ℝ => 0 := by
      funext s
      exact hEq s y
    rw [heq]
    simpa using (hasDerivAt_const (x := x) (c := (0 : ℝ))).deriv
  have hzeroYDeriv : deriv (fun s : ℝ => f x s (z x s) (t x s)) y = 0 := by
    have heq : (fun s : ℝ => f x s (z x s) (t x s)) = fun _ : ℝ => 0 := by
      funext s
      exact hEq x s
    rw [heq]
    simpa using (hasDerivAt_const (x := y) (c := (0 : ℝ))).deriv
  have hzeroX :
      L (1, (0, (partialX z x y, partialX t x y))) = 0 := by
    rw [← htotalX.deriv]
    exact hzeroXDeriv
  have hzeroY :
      L (0, (1, (partialY z x y, partialY t x y))) = 0 := by
    rw [← htotalY.deriv]
    exact hzeroYDeriv
  have hvecX :
      ((1, (0, (partialX z x y, partialX t x y))) :
        ℝ × (ℝ × (ℝ × ℝ))) =
        ((1, (0, (0, 0))) : ℝ × (ℝ × (ℝ × ℝ))) +
          partialX z x y •
            ((0, (0, (1, 0))) : ℝ × (ℝ × (ℝ × ℝ))) +
          partialX t x y •
            ((0, (0, (0, 1))) : ℝ × (ℝ × (ℝ × ℝ))) := by
    ext <;> simp
  have hvecY :
      ((0, (1, (partialY z x y, partialY t x y))) :
        ℝ × (ℝ × (ℝ × ℝ))) =
        ((0, (1, (0, 0))) : ℝ × (ℝ × (ℝ × ℝ))) +
          partialY z x y •
            ((0, (0, (1, 0))) : ℝ × (ℝ × (ℝ × ℝ))) +
          partialY t x y •
            ((0, (0, (0, 1))) : ℝ × (ℝ × (ℝ × ℝ))) := by
    ext <;> simp
  rw [hvecX] at hzeroX
  rw [hvecY] at hzeroY
  simp only [map_add, map_smul] at hzeroX hzeroY
  have hx0 :
      partial1 f x y (z x y) (t x y) +
          partial3 f x y (z x y) (t x y) * partialX z x y +
          partial4 f x y (z x y) (t x y) * partialX t x y = 0 := by
    rw [hf1, hf3, hf4]
    simpa [smul_eq_mul, mul_comm] using hzeroX
  have hy0 :
      partial2 f x y (z x y) (t x y) +
          partial3 f x y (z x y) (t x y) * partialY z x y +
          partial4 f x y (z x y) (t x y) * partialY t x y = 0 := by
    rw [hf2, hf3, hf4]
    simpa [smul_eq_mul, mul_comm] using hzeroY
  simp only [implicitDifferential, differential]
  linear_combination dx * hx0 + dy * hy0

theorem gap1 (f : ℝ → ℝ → ℝ → ℝ → ℝ) (z t : ℝ → ℝ → ℝ)
    (hEq : ∀ x y, f x y (z x y) (t x y) = 0)
    (hf : Differentiable ℝ
      (fun p : ℝ × (ℝ × (ℝ × ℝ)) => f p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hz : Differentiable ℝ (Function.uncurry z))
    (ht : Differentiable ℝ (Function.uncurry t)) :
    ∀ x y dx dy, implicitDifferential f z t x y dx dy = 0 := by
  exact implicitDifferential_vanishes f z t hEq hf hz ht

theorem gap2 (g : ℝ → ℝ → ℝ → ℝ → ℝ) (z t : ℝ → ℝ → ℝ)
    (hEq : ∀ x y, g x y (z x y) (t x y) = 0)
    (hg : Differentiable ℝ
      (fun p : ℝ × (ℝ × (ℝ × ℝ)) => g p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hz : Differentiable ℝ (Function.uncurry z))
    (ht : Differentiable ℝ (Function.uncurry t)) :
    ∀ x y dx dy, implicitDifferential g z t x y dx dy = 0 := by
  exact implicitDifferential_vanishes g z t hEq hg hz ht

theorem gap3 (f g : ℝ → ℝ → ℝ → ℝ → ℝ)
    (z t : ℝ → ℝ → ℝ)
    (hF : ∀ x y dx dy, implicitDifferential f z t x y dx dy = 0)
    (hG : ∀ x y dx dy, implicitDifferential g z t x y dx dy = 0)
    (hDet : ∀ x y, jacobian34 f g x y (z x y) (t x y) ≠ 0) :
    ∀ x y dx dy,
      differential z x y dx dy =
        (partial4 f x y (z x y) (t x y) *
            (partial1 g x y (z x y) (t x y) * dx +
              partial2 g x y (z x y) (t x y) * dy) -
          partial4 g x y (z x y) (t x y) *
            (partial1 f x y (z x y) (t x y) * dx +
              partial2 f x y (z x y) (t x y) * dy)) /
          jacobian34 f g x y (z x y) (t x y) := by
  intro x y dx dy
  have hf0 := hF x y dx dy
  have hg0 := hG x y dx dy
  simp only [implicitDifferential] at hf0 hg0
  apply (eq_div_iff (hDet x y)).2
  unfold jacobian34
  linear_combination
    (partial4 g x y (z x y) (t x y)) * hf0 -
      (partial4 f x y (z x y) (t x y)) * hg0

theorem gap4 (f g : ℝ → ℝ → ℝ → ℝ → ℝ)
    (z t : ℝ → ℝ → ℝ) :
    ∀ x y dx dy,
      (partial4 f x y (z x y) (t x y) *
            (partial1 g x y (z x y) (t x y) * dx +
              partial2 g x y (z x y) (t x y) * dy) -
          partial4 g x y (z x y) (t x y) *
            (partial1 f x y (z x y) (t x y) * dx +
              partial2 f x y (z x y) (t x y) * dy)) /
          jacobian34 f g x y (z x y) (t x y) =
        ((partial4 f x y (z x y) (t x y) *
              partial1 g x y (z x y) (t x y) -
            partial4 g x y (z x y) (t x y) *
              partial1 f x y (z x y) (t x y)) * dx +
          (partial4 f x y (z x y) (t x y) *
              partial2 g x y (z x y) (t x y) -
            partial4 g x y (z x y) (t x y) *
              partial2 f x y (z x y) (t x y)) * dy) /
          jacobian34 f g x y (z x y) (t x y) := by
  intro x y dx dy
  ring

theorem gap5 (f g : ℝ → ℝ → ℝ → ℝ → ℝ)
    (z t : ℝ → ℝ → ℝ)
    (hSolved :
      ∀ x y dx dy,
        differential z x y dx dy =
          (partial4 f x y (z x y) (t x y) *
                (partial1 g x y (z x y) (t x y) * dx +
                  partial2 g x y (z x y) (t x y) * dy) -
              partial4 g x y (z x y) (t x y) *
                (partial1 f x y (z x y) (t x y) * dx +
                  partial2 f x y (z x y) (t x y) * dy)) /
            jacobian34 f g x y (z x y) (t x y))
    (hCollect :
      ∀ x y dx dy,
        (partial4 f x y (z x y) (t x y) *
              (partial1 g x y (z x y) (t x y) * dx +
                partial2 g x y (z x y) (t x y) * dy) -
            partial4 g x y (z x y) (t x y) *
              (partial1 f x y (z x y) (t x y) * dx +
                partial2 f x y (z x y) (t x y) * dy)) /
            jacobian34 f g x y (z x y) (t x y) =
          ((partial4 f x y (z x y) (t x y) *
                partial1 g x y (z x y) (t x y) -
              partial4 g x y (z x y) (t x y) *
                partial1 f x y (z x y) (t x y)) * dx +
            (partial4 f x y (z x y) (t x y) *
                partial2 g x y (z x y) (t x y) -
              partial4 g x y (z x y) (t x y) *
                partial2 f x y (z x y) (t x y)) * dy) /
            jacobian34 f g x y (z x y) (t x y)) :
    ∀ x y dx dy,
      differential z x y dx dy =
        ((partial4 f x y (z x y) (t x y) *
              partial1 g x y (z x y) (t x y) -
            partial4 g x y (z x y) (t x y) *
              partial1 f x y (z x y) (t x y)) * dx +
          (partial4 f x y (z x y) (t x y) *
              partial2 g x y (z x y) (t x y) -
            partial4 g x y (z x y) (t x y) *
              partial2 f x y (z x y) (t x y)) * dy) /
          jacobian34 f g x y (z x y) (t x y) := by
  intro x y dx dy
  exact (hSolved x y dx dy).trans (hCollect x y dx dy)

theorem gap6 (f g : ℝ → ℝ → ℝ → ℝ → ℝ)
    (z t : ℝ → ℝ → ℝ)
    (hJacobianForm :
      ∀ x y dx dy,
        differential z x y dx dy =
          ((partial4 f x y (z x y) (t x y) *
                partial1 g x y (z x y) (t x y) -
              partial4 g x y (z x y) (t x y) *
                partial1 f x y (z x y) (t x y)) * dx +
            (partial4 f x y (z x y) (t x y) *
                partial2 g x y (z x y) (t x y) -
              partial4 g x y (z x y) (t x y) *
                partial2 f x y (z x y) (t x y)) * dy) /
            jacobian34 f g x y (z x y) (t x y)) :
    ∀ x y dx dy,
      differential z x y dx dy =
        -(jacobian13 f g x y (z x y) (t x y) * dx +
            jacobian23 f g x y (z x y) (t x y) * dy) /
          jacobian34 f g x y (z x y) (t x y) := by
  intro x y dx dy
  rw [hJacobianForm x y dx dy]
  unfold jacobian13 jacobian23
  ring

end

end ProofGap.Exercise3419
