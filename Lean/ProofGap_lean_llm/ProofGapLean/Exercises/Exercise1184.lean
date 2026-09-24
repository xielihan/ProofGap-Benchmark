import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Topology.Neighborhoods
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

namespace ProofGap.Exercise1184

noncomputable section

def iterDeriv (k : ℕ) (f : ℝ → ℝ) : ℝ → ℝ :=
  (deriv^[k]) f

def pow (x n : ℝ) : ℝ := Real.rpow x n

def y (n C₁ C₂ x : ℝ) : ℝ :=
  pow x n * (C₁ * Real.cos (Real.log x) + C₂ * Real.sin (Real.log x))

def A (C₁ C₂ x : ℝ) : ℝ :=
  C₁ * Real.cos (Real.log x) + C₂ * Real.sin (Real.log x)

def B (C₁ C₂ x : ℝ) : ℝ :=
  C₂ * Real.cos (Real.log x) - C₁ * Real.sin (Real.log x)

def expandedODE (n C₁ C₂ x : ℝ) : ℝ :=
  pow x n * ((n ^ 2 - n - 1) * A C₁ C₂ x + (2 * n - 1) * B C₁ C₂ x) +
    (1 - 2 * n) * pow x n * (n * A C₁ C₂ x + B C₁ C₂ x) +
    (1 + n ^ 2) * pow x n * A C₁ C₂ x

private theorem rpow_shift (n x : ℝ) (hx : 0 < x) :
    x * pow x (n - 1) = pow x n := by
  unfold pow
  have h_one : Real.rpow x (1 : ℝ) = x := by
    exact Real.rpow_one x
  have h_add :
      Real.rpow x (1 + (n - 1)) =
        Real.rpow x 1 * Real.rpow x (n - 1) := by
    apply Real.rpow_add hx
  calc
    x * Real.rpow x (n - 1) =
        Real.rpow x 1 * Real.rpow x (n - 1) := by
      rw [h_one]
    _ = Real.rpow x (1 + (n - 1)) := h_add.symm
    _ = Real.rpow x n := by
      congr 1
      ring

private theorem hasDerivAt_pow (n x : ℝ) (hx : 0 < x) :
    HasDerivAt (fun t : ℝ => pow t n) (n * pow x (n - 1)) x := by
  unfold pow
  exact Real.hasDerivAt_rpow_const (p := n) (Or.inl hx.ne')

private theorem hasDerivAt_AB (C₁ C₂ x : ℝ) (hx : 0 < x) :
    HasDerivAt (A C₁ C₂) (x⁻¹ * B C₁ C₂ x) x ∧
      HasDerivAt (B C₁ C₂) (-x⁻¹ * A C₁ C₂ x) x := by
  constructor
  · unfold A B
    have hc :=
      (Real.hasDerivAt_cos (Real.log x)).comp x (Real.hasDerivAt_log hx.ne')
    have hs :=
      (Real.hasDerivAt_sin (Real.log x)).comp x (Real.hasDerivAt_log hx.ne')
    convert (hc.const_mul C₁).add (hs.const_mul C₂) using 1 <;> ring
  · unfold A B
    have hc :=
      (Real.hasDerivAt_cos (Real.log x)).comp x (Real.hasDerivAt_log hx.ne')
    have hs :=
      (Real.hasDerivAt_sin (Real.log x)).comp x (Real.hasDerivAt_log hx.ne')
    convert (hc.const_mul C₂).sub (hs.const_mul C₁) using 1 <;> ring

theorem gap1 (n C₁ C₂ x : ℝ) (hx : 0 < x) :
    iterDeriv 1 (y n C₁ C₂) x =
      n * pow x (n - 1) * A C₁ C₂ x + pow x (n - 1) * B C₁ C₂ x := by
  have hp := hasDerivAt_pow n x hx
  have hab := hasDerivAt_AB C₁ C₂ x hx
  have hshift := rpow_shift n x hx
  change deriv (fun t : ℝ => pow t n * A C₁ C₂ t) x = _
  have hd := (hp.mul hab.1).deriv
  convert hd using 1
  rw [← hshift]
  field_simp [hx.ne'] <;> ring

theorem gap2 (n C₁ C₂ x : ℝ) (hx : 0 < x) :
    iterDeriv 2 (y n C₁ C₂) x =
      pow x (n - 2) *
        ((n ^ 2 - n - 1) * A C₁ C₂ x + (2 * n - 1) * B C₁ C₂ x) := by
  have hp := hasDerivAt_pow (n - 1) x hx
  have hab := hasDerivAt_AB C₁ C₂ x hx
  have hs : x * pow x (n - 2) = pow x (n - 1) := by
    convert rpow_shift (n - 1) x hx using 1 <;> ring
  have hg₀ := ((hp.mul hab.1).const_mul n).add (hp.mul hab.2)
  have hg :
      HasDerivAt
        (fun t : ℝ =>
          n * pow t (n - 1) * A C₁ C₂ t + pow t (n - 1) * B C₁ C₂ t)
        (pow x (n - 2) *
          ((n ^ 2 - n - 1) * A C₁ C₂ x + (2 * n - 1) * B C₁ C₂ x)) x := by
    convert hg₀ using 1
    · funext t
      change
        n * pow t (n - 1) * A C₁ C₂ t + pow t (n - 1) * B C₁ C₂ t =
          n * (pow t (n - 1) * A C₁ C₂ t) + pow t (n - 1) * B C₁ C₂ t
      ring
    · rw [show n - 1 - 1 = n - 2 by ring]
      simp only [← hs]
      field_simp [hx.ne'] <;> ring
  have hd :
      HasDerivAt (fun t : ℝ => deriv (y n C₁ C₂) t)
        (pow x (n - 2) *
          ((n ^ 2 - n - 1) * A C₁ C₂ x + (2 * n - 1) * B C₁ C₂ x)) x := by
    apply hg.congr_of_eventuallyEq
    filter_upwards [eventually_gt_nhds hx] with t ht
    simpa [iterDeriv] using gap1 n C₁ C₂ t ht
  simpa [iterDeriv] using hd.deriv

theorem gap3 (n C₁ C₂ x : ℝ) (hx : 0 < x) :
    x ^ 2 * iterDeriv 2 (y n C₁ C₂) x +
        (1 - 2 * n) * x * iterDeriv 1 (y n C₁ C₂) x +
        (1 + n ^ 2) * y n C₁ C₂ x =
      expandedODE n C₁ C₂ x := by
  have hs1 := rpow_shift n x hx
  have hs2 : x * pow x (n - 2) = pow x (n - 1) := by
    convert rpow_shift (n - 1) x hx using 1 <;> ring
  rw [gap2 n C₁ C₂ x hx, gap1 n C₁ C₂ x hx]
  unfold expandedODE y A
  simp only [← hs1, ← hs2]
  ring

theorem gap4 (n C₁ C₂ x : ℝ) (hx : 0 < x) :
    expandedODE n C₁ C₂ x = 0 := by
  unfold expandedODE
  ring

theorem gap5 (n C₁ C₂ x : ℝ) (hx : 0 < x) :
    x ^ 2 * iterDeriv 2 (y n C₁ C₂) x +
      (1 - 2 * n) * x * iterDeriv 1 (y n C₁ C₂) x +
      (1 + n ^ 2) * y n C₁ C₂ x = 0 := by
  rw [gap3 n C₁ C₂ x hx]
  exact gap4 n C₁ C₂ x hx

theorem gap6 (n C₁ C₂ x : ℝ) (hx : 0 < x) :
    x ^ 2 * iterDeriv 2 (y n C₁ C₂) x +
      (1 - 2 * n) * x * iterDeriv 1 (y n C₁ C₂) x +
      (1 + n ^ 2) * y n C₁ C₂ x = 0 := by
  exact gap5 n C₁ C₂ x hx

end

end ProofGap.Exercise1184
