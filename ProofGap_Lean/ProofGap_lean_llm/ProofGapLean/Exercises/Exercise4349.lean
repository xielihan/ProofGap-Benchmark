import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

namespace ProofGap.Exercise4349

noncomputable section

open scoped Interval

abbrev Point3 := ℝ × (ℝ × ℝ)

def coneParam (α r φ : ℝ) : Point3 :=
  (r * Real.cos φ * Real.sin α,
    (r * Real.sin φ * Real.sin α, r * Real.cos α))

def partialR (α r φ : ℝ) : Point3 :=
  (deriv (fun s => (coneParam α s φ).1) r,
    (deriv (fun s => (coneParam α s φ).2.1) r,
      deriv (fun s => (coneParam α s φ).2.2) r))

def partialPhi (α r φ : ℝ) : Point3 :=
  (deriv (fun s => (coneParam α r s).1) φ,
    (deriv (fun s => (coneParam α r s).2.1) φ,
      deriv (fun s => (coneParam α r s).2.2) φ))

def dot3 (p q : Point3) : ℝ :=
  p.1 * q.1 + p.2.1 * q.2.1 + p.2.2 * q.2.2

def E (α r φ : ℝ) : ℝ := dot3 (partialR α r φ) (partialR α r φ)

def G (α r φ : ℝ) : ℝ :=
  dot3 (partialPhi α r φ) (partialPhi α r φ)

def F (α r φ : ℝ) : ℝ :=
  dot3 (partialR α r φ) (partialPhi α r φ)

def areaFactor (α r φ : ℝ) : ℝ :=
  Real.sqrt (E α r φ * G α r φ - F α r φ ^ 2)

def coneMoment (a α : ℝ) : ℝ :=
  ∫ φ in (0 : ℝ)..2 * Real.pi,
    ∫ r in (0 : ℝ)..a,
      r ^ 2 * Real.cos α ^ 2 * r * Real.sin α

private theorem partialR_eq (α r φ : ℝ) :
    partialR α r φ =
      (Real.cos φ * Real.sin α,
        (Real.sin φ * Real.sin α, Real.cos α)) := by
  have hx :
      deriv (fun s : ℝ => s * Real.cos φ * Real.sin α) r =
        Real.cos φ * Real.sin α := by
    simpa using
      (((hasDerivAt_id r).mul_const (Real.cos φ)).mul_const
        (Real.sin α)).deriv
  have hy :
      deriv (fun s : ℝ => s * Real.sin φ * Real.sin α) r =
        Real.sin φ * Real.sin α := by
    simpa using
      (((hasDerivAt_id r).mul_const (Real.sin φ)).mul_const
        (Real.sin α)).deriv
  have hz :
      deriv (fun s : ℝ => s * Real.cos α) r = Real.cos α := by
    simpa using ((hasDerivAt_id r).mul_const (Real.cos α)).deriv
  simp only [partialR, coneParam]
  rw [hx, hy, hz]

private theorem partialPhi_eq (α r φ : ℝ) :
    partialPhi α r φ =
      (-r * Real.sin φ * Real.sin α,
        (r * Real.cos φ * Real.sin α, 0)) := by
  have hx :
      deriv (fun s : ℝ => r * Real.cos s * Real.sin α) φ =
        -r * Real.sin φ * Real.sin α := by
    convert
      (((Real.hasDerivAt_cos φ).const_mul r).mul_const
        (Real.sin α)).deriv using 1 <;> ring
  have hy :
      deriv (fun s : ℝ => r * Real.sin s * Real.sin α) φ =
        r * Real.cos φ * Real.sin α := by
    convert
      (((Real.hasDerivAt_sin φ).const_mul r).mul_const
        (Real.sin α)).deriv using 1 <;> ring
  have hz :
      deriv (fun _ : ℝ => r * Real.cos α) φ = 0 := by
    simpa using
      (hasDerivAt_const (x := φ) (c := r * Real.cos α)).deriv
  simp only [partialPhi, coneParam]
  rw [hx, hy, hz]

theorem gap1 (α r φ : ℝ) :
    E α r φ =
      Real.cos φ ^ 2 * Real.sin α ^ 2 +
        Real.sin φ ^ 2 * Real.sin α ^ 2 +
        Real.cos α ^ 2 := by
  simp only [E, dot3, partialR_eq]
  ring

theorem gap2 (α φ : ℝ) :
    Real.cos φ ^ 2 * Real.sin α ^ 2 +
        Real.sin φ ^ 2 * Real.sin α ^ 2 +
        Real.cos α ^ 2 =
      1 := by
  calc
    Real.cos φ ^ 2 * Real.sin α ^ 2 +
          Real.sin φ ^ 2 * Real.sin α ^ 2 +
          Real.cos α ^ 2 =
        (Real.sin φ ^ 2 + Real.cos φ ^ 2) * Real.sin α ^ 2 +
          Real.cos α ^ 2 := by ring
    _ = Real.sin α ^ 2 + Real.cos α ^ 2 := by
      rw [Real.sin_sq_add_cos_sq]
      ring
    _ = 1 := Real.sin_sq_add_cos_sq α

theorem gap3 (α r φ : ℝ) :
    E α r φ = 1 := by
  calc
    E α r φ =
        Real.cos φ ^ 2 * Real.sin α ^ 2 +
          Real.sin φ ^ 2 * Real.sin α ^ 2 +
          Real.cos α ^ 2 := gap1 α r φ
    _ = 1 := gap2 α φ

theorem gap4 (α r φ : ℝ) :
    G α r φ =
      r ^ 2 * Real.cos φ ^ 2 * Real.sin α ^ 2 +
        r ^ 2 * Real.sin φ ^ 2 * Real.sin α ^ 2 := by
  simp only [G, dot3, partialPhi_eq]
  ring

theorem gap5 (α r φ : ℝ) :
    r ^ 2 * Real.cos φ ^ 2 * Real.sin α ^ 2 +
        r ^ 2 * Real.sin φ ^ 2 * Real.sin α ^ 2 =
      r ^ 2 * Real.sin α ^ 2 := by
  calc
    r ^ 2 * Real.cos φ ^ 2 * Real.sin α ^ 2 +
          r ^ 2 * Real.sin φ ^ 2 * Real.sin α ^ 2 =
        r ^ 2 * Real.sin α ^ 2 *
          (Real.sin φ ^ 2 + Real.cos φ ^ 2) := by ring
    _ = r ^ 2 * Real.sin α ^ 2 := by
      rw [Real.sin_sq_add_cos_sq]
      ring

theorem gap6 (α r φ : ℝ) :
    G α r φ = r ^ 2 * Real.sin α ^ 2 := by
  calc
    G α r φ =
        r ^ 2 * Real.cos φ ^ 2 * Real.sin α ^ 2 +
          r ^ 2 * Real.sin φ ^ 2 * Real.sin α ^ 2 := gap4 α r φ
    _ = r ^ 2 * Real.sin α ^ 2 := gap5 α r φ

theorem gap7 (α r φ : ℝ) :
    F α r φ =
      Real.cos φ * Real.sin α *
          (-r * Real.sin φ * Real.sin α) +
        Real.sin φ * Real.sin α *
          (r * Real.cos φ * Real.sin α) := by
  simp only [F, dot3, partialR_eq, partialPhi_eq]
  ring

theorem gap8 (α r φ : ℝ) :
    Real.cos φ * Real.sin α *
          (-r * Real.sin φ * Real.sin α) +
        Real.sin φ * Real.sin α *
          (r * Real.cos φ * Real.sin α) =
      0 := by
  ring

theorem gap9 (α r φ : ℝ) :
    F α r φ = 0 := by
  calc
    F α r φ =
        Real.cos φ * Real.sin α *
            (-r * Real.sin φ * Real.sin α) +
          Real.sin φ * Real.sin α *
            (r * Real.cos φ * Real.sin α) := gap7 α r φ
    _ = 0 := gap8 α r φ

theorem gap10
    (α r φ : ℝ) (hα0 : 0 < α) (hα1 : α < Real.pi / 2)
    (hr : 0 ≤ r) :
    areaFactor α r φ = r * Real.sin α := by
  have hαpi : α < Real.pi := by
    nlinarith [Real.pi_pos]
  have hsin : 0 ≤ Real.sin α :=
    le_of_lt (Real.sin_pos_of_pos_of_lt_pi hα0 hαpi)
  have hrs : 0 ≤ r * Real.sin α := mul_nonneg hr hsin
  have hsq : r ^ 2 * Real.sin α ^ 2 = (r * Real.sin α) ^ 2 := by
    ring
  unfold areaFactor
  rw [gap3, gap6, gap9, hsq]
  calc
    Real.sqrt (1 * (r * Real.sin α) ^ 2 - 0 ^ 2) =
        Real.sqrt ((r * Real.sin α) ^ 2) := by
      congr 1
      ring
    _ = |r * Real.sin α| := Real.sqrt_sq_eq_abs _
    _ = r * Real.sin α := abs_of_nonneg hrs

theorem gap11
    (a α : ℝ) (ha : 0 ≤ a)
    (hα0 : 0 < α) (hα1 : α < Real.pi / 2) :
    coneMoment a α =
      ∫ φ in (0 : ℝ)..2 * Real.pi,
        ∫ r in (0 : ℝ)..a,
          r ^ 2 * Real.cos α ^ 2 * r * Real.sin α := by
  rfl

theorem gap12
    (a α : ℝ) (ha : 0 ≤ a)
    (hα0 : 0 < α) (hα1 : α < Real.pi / 2) :
    (∫ φ in (0 : ℝ)..2 * Real.pi,
        ∫ r in (0 : ℝ)..a,
          r ^ 2 * Real.cos α ^ 2 * r * Real.sin α) =
      Real.pi * a ^ 4 / 2 *
        Real.sin α * Real.cos α ^ 2 := by
  have hderiv (x : ℝ) :
      HasDerivAt (fun t : ℝ => t ^ 4 / 4) (x ^ 3) x := by
    convert (((hasDerivAt_id x).pow 4).div_const 4) using 1 <;>
      norm_num <;> ring
  have hcont : Continuous (fun x : ℝ => x ^ 3) :=
    continuous_id.pow 3
  have hpow :
      (∫ r : ℝ in (0 : ℝ)..a, r ^ 3) = a ^ 4 / 4 := by
    calc
      (∫ r : ℝ in (0 : ℝ)..a, r ^ 3) =
          a ^ 4 / 4 - (0 : ℝ) ^ 4 / 4 := by
        exact intervalIntegral.integral_deriv_eq_sub'
          (fun t : ℝ => t ^ 4 / 4)
          (funext fun x => (hderiv x).deriv)
          (fun x _ => (hderiv x).differentiableAt)
          hcont.continuousOn
      _ = a ^ 4 / 4 := by norm_num
  have hfun :
      (fun r : ℝ =>
          r ^ 2 * Real.cos α ^ 2 * r * Real.sin α) =
        (fun r : ℝ =>
          (Real.cos α ^ 2 * Real.sin α) * r ^ 3) := by
    funext r
    ring
  have hinner :
      (∫ r in (0 : ℝ)..a,
          r ^ 2 * Real.cos α ^ 2 * r * Real.sin α) =
        (Real.cos α ^ 2 * Real.sin α) * (a ^ 4 / 4) := by
    rw [hfun, intervalIntegral.integral_const_mul, hpow]
  rw [hinner]
  norm_num [intervalIntegral.integral_const] <;> ring

theorem gap13
    (a α : ℝ) (ha : 0 ≤ a)
    (hα0 : 0 < α) (hα1 : α < Real.pi / 2) :
    coneMoment a α =
      Real.pi * a ^ 4 / 2 *
        Real.sin α * Real.cos α ^ 2 := by
  calc
    coneMoment a α =
        ∫ φ in (0 : ℝ)..2 * Real.pi,
          ∫ r in (0 : ℝ)..a,
            r ^ 2 * Real.cos α ^ 2 * r * Real.sin α :=
      gap11 a α ha hα0 hα1
    _ = Real.pi * a ^ 4 / 2 *
          Real.sin α * Real.cos α ^ 2 :=
      gap12 a α ha hα0 hα1

end

end ProofGap.Exercise4349
