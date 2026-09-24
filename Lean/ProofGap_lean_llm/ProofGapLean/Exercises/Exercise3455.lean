import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.Calculus.Deriv.Basic

namespace ProofGap.Exercise3455

noncomputable section

def d1 (f : ℝ → ℝ) (t : ℝ) : ℝ :=
  deriv f t

def regular (r : ℝ → ℝ) (t : ℝ) : Prop :=
  r t ≠ 0

def radialCramer (k : ℝ) (r φ : ℝ → ℝ) (t : ℝ) : ℝ :=
  1 / r t *
    (r t * Real.cos (φ t) *
        (r t * Real.sin (φ t) + k * (r t) ^ 3 * Real.cos (φ t)) -
      (-r t * Real.sin (φ t)) *
        (-r t * Real.cos (φ t) + k * (r t) ^ 3 * Real.sin (φ t)))

def angularCramer (k : ℝ) (r φ : ℝ → ℝ) (t : ℝ) : ℝ :=
  1 / r t *
    (Real.cos (φ t) *
        (-r t * Real.cos (φ t) + k * (r t) ^ 3 * Real.sin (φ t)) -
      Real.sin (φ t) *
        (r t * Real.sin (φ t) + k * (r t) ^ 3 * Real.cos (φ t)))

private theorem polarDerivCos (r φ : ℝ → ℝ)
    (hr : ContDiff ℝ 1 r) (hφ : ContDiff ℝ 1 φ) :
    ∀ t,
      d1 (fun s => r s * Real.cos (φ s)) t =
        Real.cos (φ t) * d1 r t -
          r t * Real.sin (φ t) * d1 φ t := by
  intro t
  have hrAt : HasDerivAt r (d1 r t) t :=
    (hr.differentiable one_ne_zero).differentiableAt.hasDerivAt
  have hφAt : HasDerivAt φ (d1 φ t) t :=
    (hφ.differentiable one_ne_zero).differentiableAt.hasDerivAt
  have h := hrAt.mul ((Real.hasDerivAt_cos (φ t)).comp t hφAt)
  convert h.deriv using 1 <;>
    simp only [d1, Function.comp_apply] <;> ring

private theorem polarDerivSin (r φ : ℝ → ℝ)
    (hr : ContDiff ℝ 1 r) (hφ : ContDiff ℝ 1 φ) :
    ∀ t,
      d1 (fun s => r s * Real.sin (φ s)) t =
        Real.sin (φ t) * d1 r t +
          r t * Real.cos (φ t) * d1 φ t := by
  intro t
  have hrAt : HasDerivAt r (d1 r t) t :=
    (hr.differentiable one_ne_zero).differentiableAt.hasDerivAt
  have hφAt : HasDerivAt φ (d1 φ t) t :=
    (hφ.differentiable one_ne_zero).differentiableAt.hasDerivAt
  have h := hrAt.mul ((Real.hasDerivAt_sin (φ t)).comp t hφAt)
  convert h.deriv using 1 <;>
    simp only [d1, Function.comp_apply] <;> ring

theorem gap1 (k : ℝ) (x y r φ : ℝ → ℝ)
    (hXODE :
      ∀ t,
        d1 x t = y t + k * x t * ((x t) ^ 2 + (y t) ^ 2))
    (hX : ∀ t, x t = r t * Real.cos (φ t))
    (hY : ∀ t, y t = r t * Real.sin (φ t))
    (hr : ContDiff ℝ 1 r)
    (hφ : ContDiff ℝ 1 φ) :
    ∀ t,
      Real.cos (φ t) * d1 r t -
          r t * Real.sin (φ t) * d1 φ t =
        r t * Real.sin (φ t) +
          k * (r t) ^ 3 * Real.cos (φ t) := by
  intro t
  have hx_eq : x = fun s => r s * Real.cos (φ s) := funext hX
  have htrig : Real.cos (φ t) ^ 2 + Real.sin (φ t) ^ 2 = 1 := by
    simpa [add_comm] using Real.sin_sq_add_cos_sq (φ t)
  have hnorm :
      (r t * Real.cos (φ t)) ^ 2 + (r t * Real.sin (φ t)) ^ 2 =
        (r t) ^ 2 := by
    calc
      (r t * Real.cos (φ t)) ^ 2 + (r t * Real.sin (φ t)) ^ 2 =
          (r t) ^ 2 * (Real.cos (φ t) ^ 2 + Real.sin (φ t) ^ 2) := by ring
      _ = (r t) ^ 2 := by rw [htrig]; ring
  have h := hXODE t
  rw [hx_eq, polarDerivCos r φ hr hφ t, hY t, hnorm] at h
  calc
    Real.cos (φ t) * d1 r t - r t * Real.sin (φ t) * d1 φ t =
        r t * Real.sin (φ t) +
          k * (r t * Real.cos (φ t)) * (r t) ^ 2 := h
    _ = r t * Real.sin (φ t) + k * (r t) ^ 3 * Real.cos (φ t) := by ring

theorem gap2 (k : ℝ) (x y r φ : ℝ → ℝ)
    (hYODE :
      ∀ t,
        d1 y t = -x t + k * y t * ((x t) ^ 2 + (y t) ^ 2))
    (hX : ∀ t, x t = r t * Real.cos (φ t))
    (hY : ∀ t, y t = r t * Real.sin (φ t))
    (hr : ContDiff ℝ 1 r)
    (hφ : ContDiff ℝ 1 φ) :
    ∀ t,
      Real.sin (φ t) * d1 r t +
          r t * Real.cos (φ t) * d1 φ t =
        -r t * Real.cos (φ t) +
          k * (r t) ^ 3 * Real.sin (φ t) := by
  intro t
  have hy_eq : y = fun s => r s * Real.sin (φ s) := funext hY
  have htrig : Real.cos (φ t) ^ 2 + Real.sin (φ t) ^ 2 = 1 := by
    simpa [add_comm] using Real.sin_sq_add_cos_sq (φ t)
  have hnorm :
      (r t * Real.cos (φ t)) ^ 2 + (r t * Real.sin (φ t)) ^ 2 =
        (r t) ^ 2 := by
    calc
      (r t * Real.cos (φ t)) ^ 2 + (r t * Real.sin (φ t)) ^ 2 =
          (r t) ^ 2 * (Real.cos (φ t) ^ 2 + Real.sin (φ t) ^ 2) := by ring
      _ = (r t) ^ 2 := by rw [htrig]; ring
  have h := hYODE t
  rw [hy_eq, polarDerivSin r φ hr hφ t, hX t, hnorm] at h
  calc
    Real.sin (φ t) * d1 r t + r t * Real.cos (φ t) * d1 φ t =
        -(r t * Real.cos (φ t)) +
          k * (r t * Real.sin (φ t)) * (r t) ^ 2 := h
    _ = -r t * Real.cos (φ t) + k * (r t) ^ 3 * Real.sin (φ t) := by ring

theorem gap3 (k : ℝ) (r φ : ℝ → ℝ)
    (hXEquation :
      ∀ t,
        Real.cos (φ t) * d1 r t -
            r t * Real.sin (φ t) * d1 φ t =
          r t * Real.sin (φ t) +
            k * (r t) ^ 3 * Real.cos (φ t))
    (hYEquation :
      ∀ t,
        Real.sin (φ t) * d1 r t +
            r t * Real.cos (φ t) * d1 φ t =
          -r t * Real.cos (φ t) +
            k * (r t) ^ 3 * Real.sin (φ t)) :
    ∀ t, regular r t →
      d1 r t = radialCramer k r φ t := by
  intro t ht
  change r t ≠ 0 at ht
  unfold radialCramer
  rw [← hXEquation t, ← hYEquation t]
  have htrig : Real.cos (φ t) ^ 2 + Real.sin (φ t) ^ 2 = 1 := by
    simpa [add_comm] using Real.sin_sq_add_cos_sq (φ t)
  have hnum :
      r t * Real.cos (φ t) *
            (Real.cos (φ t) * d1 r t -
              r t * Real.sin (φ t) * d1 φ t) -
          (-r t * Real.sin (φ t)) *
            (Real.sin (φ t) * d1 r t +
              r t * Real.cos (φ t) * d1 φ t) =
        r t * d1 r t := by
    calc
      _ = r t * d1 r t *
          (Real.cos (φ t) ^ 2 + Real.sin (φ t) ^ 2) := by ring
      _ = r t * d1 r t := by rw [htrig]; ring
  rw [hnum]
  field_simp [ht]

theorem gap4 (k : ℝ) (r φ : ℝ → ℝ) :
    ∀ t, regular r t →
      radialCramer k r φ t = k * (r t) ^ 3 := by
  intro t ht
  change r t ≠ 0 at ht
  unfold radialCramer
  have htrig : Real.cos (φ t) ^ 2 + Real.sin (φ t) ^ 2 = 1 := by
    simpa [add_comm] using Real.sin_sq_add_cos_sq (φ t)
  have hnum :
      r t * Real.cos (φ t) *
            (r t * Real.sin (φ t) +
              k * (r t) ^ 3 * Real.cos (φ t)) -
          (-r t * Real.sin (φ t)) *
            (-r t * Real.cos (φ t) +
              k * (r t) ^ 3 * Real.sin (φ t)) =
        r t * (k * (r t) ^ 3) := by
    calc
      _ = k * (r t) ^ 4 *
          (Real.cos (φ t) ^ 2 + Real.sin (φ t) ^ 2) := by ring
      _ = k * (r t) ^ 4 := by rw [htrig]; ring
      _ = r t * (k * (r t) ^ 3) := by ring
  rw [hnum]
  field_simp [ht]

theorem gap5 (k : ℝ) (r φ : ℝ → ℝ)
    (hCramer :
      ∀ t, regular r t →
        d1 r t = radialCramer k r φ t)
    (hSimplify :
      ∀ t, regular r t →
        radialCramer k r φ t = k * (r t) ^ 3) :
    ∀ t, regular r t →
      d1 r t = k * (r t) ^ 3 := by
  intro t ht
  calc
    d1 r t = radialCramer k r φ t := hCramer t ht
    _ = k * (r t) ^ 3 := hSimplify t ht

theorem gap6 (k : ℝ) (r φ : ℝ → ℝ)
    (hXEquation :
      ∀ t,
        Real.cos (φ t) * d1 r t -
            r t * Real.sin (φ t) * d1 φ t =
          r t * Real.sin (φ t) +
            k * (r t) ^ 3 * Real.cos (φ t))
    (hYEquation :
      ∀ t,
        Real.sin (φ t) * d1 r t +
            r t * Real.cos (φ t) * d1 φ t =
          -r t * Real.cos (φ t) +
            k * (r t) ^ 3 * Real.sin (φ t)) :
    ∀ t, regular r t →
      d1 φ t = angularCramer k r φ t := by
  intro t ht
  change r t ≠ 0 at ht
  unfold angularCramer
  rw [← hYEquation t, ← hXEquation t]
  have htrig : Real.cos (φ t) ^ 2 + Real.sin (φ t) ^ 2 = 1 := by
    simpa [add_comm] using Real.sin_sq_add_cos_sq (φ t)
  have hnum :
      Real.cos (φ t) *
            (Real.sin (φ t) * d1 r t +
              r t * Real.cos (φ t) * d1 φ t) -
          Real.sin (φ t) *
            (Real.cos (φ t) * d1 r t -
              r t * Real.sin (φ t) * d1 φ t) =
        r t * d1 φ t := by
    calc
      _ = r t * d1 φ t *
          (Real.cos (φ t) ^ 2 + Real.sin (φ t) ^ 2) := by ring
      _ = r t * d1 φ t := by rw [htrig]; ring
  rw [hnum]
  field_simp [ht]

theorem gap7 (k : ℝ) (r φ : ℝ → ℝ) :
    ∀ t, regular r t →
      angularCramer k r φ t = -1 := by
  intro t ht
  change r t ≠ 0 at ht
  unfold angularCramer
  have htrig : Real.cos (φ t) ^ 2 + Real.sin (φ t) ^ 2 = 1 := by
    simpa [add_comm] using Real.sin_sq_add_cos_sq (φ t)
  have hnum :
      Real.cos (φ t) *
            (-r t * Real.cos (φ t) +
              k * (r t) ^ 3 * Real.sin (φ t)) -
          Real.sin (φ t) *
            (r t * Real.sin (φ t) +
              k * (r t) ^ 3 * Real.cos (φ t)) =
        r t * (-1) := by
    calc
      _ = -r t *
          (Real.cos (φ t) ^ 2 + Real.sin (φ t) ^ 2) := by ring
      _ = r t * (-1) := by rw [htrig]; ring
  rw [hnum]
  field_simp [ht]

theorem gap8 (k : ℝ) (r φ : ℝ → ℝ)
    (hCramer :
      ∀ t, regular r t →
        d1 φ t = angularCramer k r φ t)
    (hSimplify :
      ∀ t, regular r t →
        angularCramer k r φ t = -1) :
    ∀ t, regular r t →
      d1 φ t = -1 := by
  intro t ht
  calc
    d1 φ t = angularCramer k r φ t := hCramer t ht
    _ = -1 := hSimplify t ht

end

end ProofGap.Exercise3455
