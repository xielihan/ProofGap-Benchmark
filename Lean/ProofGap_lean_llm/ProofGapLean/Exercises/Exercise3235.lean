import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.Ring
import Mathlib.Topology.Defs.Filter

namespace ProofGap.Exercise3235

noncomputable section

def u (m n x y : ℝ) : ℝ :=
  Real.rpow x m * Real.rpow y n

def admissible (x y : ℝ) : Prop :=
  0 < x ∧ 0 < y

def partialX (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => f t y) x

def partialY (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => f x t) y

def partialXX (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => partialX f t y) x

def partialXY (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => partialX f x t) y

def partialYY (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => partialY f x t) y

def differential (f : ℝ → ℝ → ℝ) (x y dx dy : ℝ) : ℝ :=
  partialX f x y * dx + partialY f x y * dy

def secondDifferential (f : ℝ → ℝ → ℝ) (x y dx dy : ℝ) : ℝ :=
  partialXX f x y * dx ^ 2 +
    2 * partialXY f x y * dx * dy +
    partialYY f x y * dy ^ 2

def firstFactored (m n x y dx dy : ℝ) : ℝ :=
  Real.rpow x (m - 1) * Real.rpow y (n - 1) *
    (m * y * dx + n * x * dy)

def secondExpanded (m n x y dx dy : ℝ) : ℝ :=
  m * (m - 1) * Real.rpow x (m - 2) * Real.rpow y n * dx ^ 2 +
    2 * m * n * Real.rpow x (m - 1) * Real.rpow y (n - 1) *
      dx * dy +
    n * (n - 1) * Real.rpow x m * Real.rpow y (n - 2) * dy ^ 2

def secondFactored (m n x y dx dy : ℝ) : ℝ :=
  Real.rpow x (m - 2) * Real.rpow y (n - 2) *
    (m * (m - 1) * y ^ 2 * dx ^ 2 +
      2 * m * n * x * y * dx * dy +
      n * (n - 1) * x ^ 2 * dy ^ 2)

private lemma rpow_shift_one (a x : ℝ) (hx : 0 < x) :
    Real.rpow x a = Real.rpow x (a - 1) * x := by
  calc
    Real.rpow x a = Real.rpow x ((a - 1) + 1) := by
      congr 1
      ring
    _ = Real.rpow x (a - 1) * Real.rpow x 1 := by
      simpa using (Real.rpow_add hx (a - 1) 1)
    _ = Real.rpow x (a - 1) * x := by simp

private lemma rpow_shift_from_sub_one (a x : ℝ) (hx : 0 < x) :
    Real.rpow x (a - 1) = Real.rpow x (a - 2) * x := by
  convert rpow_shift_one (a - 1) x hx using 1 <;> ring

private lemma rpow_shift_two (a x : ℝ) (hx : 0 < x) :
    Real.rpow x a = Real.rpow x (a - 2) * x ^ 2 := by
  rw [rpow_shift_one a x hx, rpow_shift_from_sub_one a x hx]
  ring

private lemma partialX_u (m n x y : ℝ) (hx : 0 < x) :
    partialX (u m n) x y =
      m * Real.rpow x (m - 1) * Real.rpow y n := by
  simpa [partialX, u] using
    ((Real.hasDerivAt_rpow_const (p := m)
      (Or.inl (ne_of_gt hx))).mul_const (Real.rpow y n)).deriv

private lemma partialY_u (m n x y : ℝ) (hy : 0 < y) :
    partialY (u m n) x y =
      Real.rpow x m * (n * Real.rpow y (n - 1)) := by
  simpa [partialY, u] using
    ((Real.hasDerivAt_rpow_const (p := n)
      (Or.inl (ne_of_gt hy))).const_mul (Real.rpow x m)).deriv

private lemma partialXX_u (m n x y : ℝ) (hx : 0 < x) :
    partialXX (u m n) x y =
      m * (m - 1) * Real.rpow x (m - 2) * Real.rpow y n := by
  have heq :
      (fun t => partialX (u m n) t y) =ᶠ[nhds x]
        (fun t => m * Real.rpow t (m - 1) * Real.rpow y n) := by
    filter_upwards [Ioi_mem_nhds hx] with t ht
    exact partialX_u m n t y ht
  unfold partialXX
  calc
    deriv (fun t => partialX (u m n) t y) x =
        deriv (fun t => m * Real.rpow t (m - 1) * Real.rpow y n) x :=
      heq.deriv_eq
    _ = m * ((m - 1) * Real.rpow x (m - 1 - 1)) * Real.rpow y n := by
      simpa using
        (((Real.hasDerivAt_rpow_const (p := m - 1)
          (Or.inl (ne_of_gt hx))).const_mul m).mul_const
            (Real.rpow y n)).deriv
    _ = m * (m - 1) * Real.rpow x (m - 2) * Real.rpow y n := by
      rw [show m - 1 - 1 = m - 2 by ring]
      ring

private lemma partialXY_u (m n x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    partialXY (u m n) x y =
      m * n * Real.rpow x (m - 1) * Real.rpow y (n - 1) := by
  have hfun :
      (fun t => partialX (u m n) x t) =
        (fun t => m * Real.rpow x (m - 1) * Real.rpow t n) := by
    funext t
    exact partialX_u m n x t hx
  unfold partialXY
  rw [hfun]
  calc
    deriv (fun t => m * Real.rpow x (m - 1) * Real.rpow t n) y =
        (m * Real.rpow x (m - 1)) *
          (n * Real.rpow y (n - 1)) := by
      simpa using
        ((Real.hasDerivAt_rpow_const (p := n)
          (Or.inl (ne_of_gt hy))).const_mul
            (m * Real.rpow x (m - 1))).deriv
    _ = m * n * Real.rpow x (m - 1) * Real.rpow y (n - 1) := by
      ring

private lemma partialYY_u (m n x y : ℝ) (hy : 0 < y) :
    partialYY (u m n) x y =
      n * (n - 1) * Real.rpow x m * Real.rpow y (n - 2) := by
  have heq :
      (fun t => partialY (u m n) x t) =ᶠ[nhds y]
        (fun t => Real.rpow x m * (n * Real.rpow t (n - 1))) := by
    filter_upwards [Ioi_mem_nhds hy] with t ht
    exact partialY_u m n x t ht
  unfold partialYY
  calc
    deriv (fun t => partialY (u m n) x t) y =
        deriv (fun t => Real.rpow x m * (n * Real.rpow t (n - 1))) y :=
      heq.deriv_eq
    _ = Real.rpow x m *
        (n * ((n - 1) * Real.rpow y (n - 1 - 1))) := by
      simpa using
        (((Real.hasDerivAt_rpow_const (p := n - 1)
          (Or.inl (ne_of_gt hy))).const_mul n).const_mul
            (Real.rpow x m)).deriv
    _ = n * (n - 1) * Real.rpow x m * Real.rpow y (n - 2) := by
      rw [show n - 1 - 1 = n - 2 by ring]
      ring

theorem gap1 :
    ∀ m n x y dx dy : ℝ, admissible x y →
      differential (u m n) x y dx dy =
        firstFactored m n x y dx dy := by
  intro m n x y dx dy hxy
  rcases hxy with ⟨hx, hy⟩
  unfold differential firstFactored
  rw [partialX_u m n x y hx, partialY_u m n x y hy]
  rw [rpow_shift_one m x hx, rpow_shift_one n y hy]
  ring

theorem gap2 :
    ∀ m n x y dx dy : ℝ, admissible x y →
      secondDifferential (u m n) x y dx dy =
        secondExpanded m n x y dx dy := by
  intro m n x y dx dy hxy
  rcases hxy with ⟨hx, hy⟩
  unfold secondDifferential secondExpanded
  rw [partialXX_u m n x y hx, partialXY_u m n x y hx hy,
    partialYY_u m n x y hy]
  ring

theorem gap3 :
    ∀ m n x y dx dy : ℝ, admissible x y →
      secondExpanded m n x y dx dy =
        secondFactored m n x y dx dy := by
  intro m n x y dx dy hxy
  rcases hxy with ⟨hx, hy⟩
  unfold secondExpanded secondFactored
  rw [rpow_shift_two m x hx, rpow_shift_two n y hy]
  rw [rpow_shift_from_sub_one m x hx, rpow_shift_from_sub_one n y hy]
  ring

theorem gap4 :
    ∀ m n x y dx dy : ℝ, admissible x y →
      secondDifferential (u m n) x y dx dy =
        secondFactored m n x y dx dy := by
  intro m n x y dx dy hxy
  calc
    secondDifferential (u m n) x y dx dy =
        secondExpanded m n x y dx dy := gap2 m n x y dx dy hxy
    _ = secondFactored m n x y dx dy := gap3 m n x y dx dy hxy

end

end ProofGap.Exercise3235
