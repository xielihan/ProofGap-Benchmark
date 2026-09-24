import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Topology.Defs.Filter

namespace ProofGap.Exercise3447

noncomputable section

def d1 (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  deriv f x

def d2 (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  deriv (deriv f) x

def regular (y : ℝ → ℝ) (x : ℝ) : Prop :=
  x ≠ 0 ∧ y x ≠ 0

def ScaleInvariantZero (F : ℝ → ℝ → ℝ → ℝ) : Prop :=
  ∀ c a b d, c ≠ 0 →
    (F (c * a) (c * b) (c * d) = 0 ↔ F a b d = 0)

theorem gap1 (u y : ℝ → ℝ)
    (hDefinition :
      ∀ x, regular y x →
        u x = x * d1 y x / y x) :
    ∀ x, regular y x →
      d1 y x = y x * u x / x := by
  intro x hx
  rw [hDefinition x hx]
  field_simp [hx.1, hx.2] <;> ring

theorem gap2 (u y : ℝ → ℝ)
    (hFirst :
      ∀ x, regular y x →
        d1 y x = y x * u x / x)
    (hu : ContDiff ℝ 1 u)
    (hy : ContDiff ℝ 2 y) :
    ∀ x, regular y x →
      d2 y x =
        (x * (d1 u x * y x + d1 y x * u x) -
            y x * u x) /
          x ^ 2 := by
  intro x hx
  have hreg : ∀ᶠ z in nhds x, regular y z := by
    filter_upwards [
      eventually_ne_nhds hx.1,
      hy.continuous.continuousAt (eventually_ne_nhds hx.2)
    ] with z hz hyz
    exact ⟨hz, hyz⟩
  have heq :
      deriv y =ᶠ[nhds x] (fun z : ℝ => y z * u z / z) := by
    filter_upwards [hreg] with z hz
    simpa only [d1] using hFirst z hz
  have huDeriv : HasDerivAt u (d1 u x) x := by
    simp only [d1]
    exact (hu.differentiable (by norm_num)).differentiableAt.hasDerivAt
  have hyDeriv : HasDerivAt y (d1 y x) x := by
    simp only [d1]
    exact (hy.differentiable (by decide)).differentiableAt.hasDerivAt
  have hquotRaw :
      HasDerivAt (fun z : ℝ => y z * u z / z)
        (((d1 y x * u x + y x * d1 u x) * x - y x * u x) /
          x ^ 2) x := by
    simpa using
      (hyDeriv.mul huDeriv).div (hasDerivAt_id x) hx.1
  have hquot :
      HasDerivAt (fun z : ℝ => y z * u z / z)
        ((x * (d1 u x * y x + d1 y x * u x) - y x * u x) /
          x ^ 2) x := by
    convert hquotRaw using 1 <;> ring
  have hlocal :
      HasDerivAt (deriv y)
        ((x * (d1 u x * y x + d1 y x * u x) - y x * u x) /
          x ^ 2) x :=
    hquot.congr_of_eventuallyEq heq
  simpa only [d2] using hlocal.deriv

theorem gap3 (u y : ℝ → ℝ)
    (hFirst :
      ∀ x, regular y x →
        d1 y x = y x * u x / x) :
    ∀ x, regular y x →
      (x * (d1 u x * y x + d1 y x * u x) -
            y x * u x) /
          x ^ 2 =
        y x * (x * d1 u x + (u x) ^ 2 - u x) /
          x ^ 2 := by
  intro x hx
  rw [hFirst x hx]
  field_simp [hx.1] <;> ring

theorem gap4 (u y : ℝ → ℝ)
    (hDifferentiate :
      ∀ x, regular y x →
        d2 y x =
          (x * (d1 u x * y x + d1 y x * u x) -
              y x * u x) /
            x ^ 2)
    (hSubstitute :
      ∀ x, regular y x →
        (x * (d1 u x * y x + d1 y x * u x) -
              y x * u x) /
            x ^ 2 =
          y x * (x * d1 u x + (u x) ^ 2 - u x) /
            x ^ 2) :
    ∀ x, regular y x →
      d2 y x =
        y x * (x * d1 u x + (u x) ^ 2 - u x) /
          x ^ 2 := by
  intro x hx
  calc
    d2 y x =
        (x * (d1 u x * y x + d1 y x * u x) - y x * u x) /
          x ^ 2 := hDifferentiate x hx
    _ = y x * (x * d1 u x + (u x) ^ 2 - u x) /
          x ^ 2 := hSubstitute x hx

theorem gap5 (u y : ℝ → ℝ)
    (hFirst :
      ∀ x, regular y x →
        d1 y x = y x * u x / x) :
    ∀ x, regular y x →
      x * d1 y x = u x * y x := by
  intro x hx
  rw [hFirst x hx]
  field_simp [hx.1] <;> ring

theorem gap6 (u y : ℝ → ℝ)
    (hSecond :
      ∀ x, regular y x →
        d2 y x =
          y x * (x * d1 u x + (u x) ^ 2 - u x) /
            x ^ 2) :
    ∀ x, regular y x →
      x ^ 2 * d2 y x =
        y x * (x * d1 u x + (u x) ^ 2 - u x) := by
  intro x hx
  rw [hSecond x hx]
  field_simp [hx.1] <;> ring

theorem gap7 (F : ℝ → ℝ → ℝ → ℝ) (u y : ℝ → ℝ)
    (hODE :
      ∀ x,
        F (x ^ 2 * d2 y x) (x * d1 y x) (y x) = 0)
    (hFirst :
      ∀ x, regular y x →
        x * d1 y x = u x * y x)
    (hSecond :
      ∀ x, regular y x →
        x ^ 2 * d2 y x =
          y x * (x * d1 u x + (u x) ^ 2 - u x))
    (hScale : ScaleInvariantZero F) :
    ∀ x, regular y x →
      F (x * d1 u x + (u x) ^ 2 - u x) (u x) 1 = 0 := by
  intro x hx
  apply
    (hScale (y x)
      (x * d1 u x + (u x) ^ 2 - u x) (u x) 1 hx.2).mp
  have h := hODE x
  rw [hSecond x hx, hFirst x hx] at h
  simpa [mul_comm] using h

end

end ProofGap.Exercise3447
