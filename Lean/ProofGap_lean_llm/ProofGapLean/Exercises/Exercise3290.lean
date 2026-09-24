import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Topology.Neighborhoods
import Mathlib.Topology.Defs.Filter
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

namespace ProofGap.Exercise3290

noncomputable section

def iterDeriv (n : ℕ) (f : ℝ → ℝ) : ℝ → ℝ :=
  (deriv^[n]) f

def nthDifferential (n : ℕ) (u : ℝ → ℝ → ℝ)
    (x y dx dy : ℝ) : ℝ :=
  iterDeriv n (fun s => u (x + s * dx) (y + s * dy)) 0

def radius (x y : ℝ) : ℝ :=
  Real.sqrt (x ^ 2 + y ^ 2)

private lemma radius_sq_eq (x y : ℝ) :
    radius x y ^ 2 = x ^ 2 + y ^ 2 := by
  rw [radius, Real.sq_sqrt]
  positivity

private lemma radius_ne_zero_of_sum_sq_ne_zero
    (x y : ℝ) (h : x ^ 2 + y ^ 2 ≠ 0) :
    radius x y ≠ 0 := by
  have hnonneg : 0 ≤ x ^ 2 + y ^ 2 := by positivity
  have hpos : 0 < x ^ 2 + y ^ 2 :=
    lt_of_le_of_ne hnonneg (Ne.symm h)
  unfold radius
  exact ne_of_gt (Real.sqrt_pos.2 hpos)

private lemma hasDerivAt_line_normSq
    (x y dx dy t : ℝ) :
    HasDerivAt
      (fun s : ℝ => (x + s * dx) ^ 2 + (y + s * dy) ^ 2)
      (2 * ((x + t * dx) * dx + (y + t * dy) * dy)) t := by
  convert
    (((hasDerivAt_const t x).add
        ((hasDerivAt_id t).mul_const dx)).pow 2).add
      (((hasDerivAt_const t y).add
        ((hasDerivAt_id t).mul_const dy)).pow 2)
    using 1 <;>
    simp only [Pi.add_apply, id_eq] <;>
    ring

private lemma hasDerivAt_radius_line
    (x y dx dy t : ℝ)
    (h : (x + t * dx) ^ 2 + (y + t * dy) ^ 2 ≠ 0) :
    HasDerivAt
      (fun s : ℝ => radius (x + s * dx) (y + s * dy))
      (((x + t * dx) * dx + (y + t * dy) * dy) /
        radius (x + t * dx) (y + t * dy)) t := by
  have hr_ne :
      radius (x + t * dx) (y + t * dy) ≠ 0 :=
    radius_ne_zero_of_sum_sq_ne_zero
      (x + t * dx) (y + t * dy) h
  have hsqrt_ne :
      Real.sqrt
          ((x + t * dx) ^ 2 + (y + t * dy) ^ 2) ≠ 0 := by
    simpa [radius] using hr_ne
  have hs :=
    (Real.hasDerivAt_sqrt h).comp t
      (hasDerivAt_line_normSq x y dx dy t)
  convert hs using 1 <;>
    simp only [radius] <;>
    field_simp [hsqrt_ne]

theorem gap1 (u : ℝ → ℝ → ℝ) (f : ℝ → ℝ)
    (hu : ∀ x y, u x y = f (radius x y))
    (hf : Differentiable ℝ f)
    (x y dx dy : ℝ) (hr : x ^ 2 + y ^ 2 ≠ 0) :
    nthDifferential 1 u x y dx dy =
      deriv f (radius x y) *
        ((x * dx + y * dy) / radius x y) := by
  change
    deriv (fun s : ℝ => u (x + s * dx) (y + s * dy)) 0 =
      deriv f (radius x y) *
        ((x * dx + y * dy) / radius x y)
  have hrad :
      HasDerivAt
        (fun s : ℝ => radius (x + s * dx) (y + s * dy))
        ((x * dx + y * dy) / radius x y) 0 := by
    simpa only [zero_mul, add_zero] using
      hasDerivAt_radius_line x y dx dy 0
        (by simpa only [zero_mul, add_zero] using hr)
  have hcomp :
      HasDerivAt
        (fun s : ℝ => f (radius (x + s * dx) (y + s * dy)))
        (deriv f (radius x y) *
          ((x * dx + y * dy) / radius x y)) 0 := by
    simpa only [zero_mul, add_zero] using
      ((hf _).hasDerivAt.comp 0 hrad)
  have hu_line :
      (fun s : ℝ => u (x + s * dx) (y + s * dy)) =
        fun s : ℝ => f (radius (x + s * dx) (y + s * dy)) := by
    funext s
    exact hu _ _
  rw [hu_line]
  exact hcomp.deriv

theorem gap2 (u : ℝ → ℝ → ℝ) (f : ℝ → ℝ)
    (hu : ∀ x y, u x y = f (radius x y))
    (hf : ContDiff ℝ 2 f)
    (x y dx dy : ℝ) (hr : x ^ 2 + y ^ 2 ≠ 0) :
    nthDifferential 2 u x y dx dy =
      iterDeriv 2 f (radius x y) *
          (x * dx + y * dy) ^ 2 / (x ^ 2 + y ^ 2) +
        deriv f (radius x y) *
          (y * dx - x * dy) ^ 2 / radius x y ^ 3 := by
  change
    deriv (deriv (fun s : ℝ => u (x + s * dx) (y + s * dy))) 0 =
      deriv (deriv f) (radius x y) *
          (x * dx + y * dy) ^ 2 / (x ^ 2 + y ^ 2) +
        deriv f (radius x y) *
          (y * dx - x * dy) ^ 2 / radius x y ^ 3
  have hf_succ : ContDiff ℝ (1 + 1) f := by
    simpa only [one_add_one_eq_two] using hf
  have hf_split := contDiff_succ_iff_deriv.mp hf_succ
  have hf₁ : Differentiable ℝ f := hf_split.1
  have hdf : Differentiable ℝ (deriv f) :=
    hf_split.2.2.differentiable (by simp)
  have hr0 : radius x y ≠ 0 :=
    radius_ne_zero_of_sum_sq_ne_zero x y hr
  have hrsq : radius x y ^ 2 = x ^ 2 + y ^ 2 :=
    radius_sq_eq x y
  have hrad :
      HasDerivAt
        (fun s : ℝ => radius (x + s * dx) (y + s * dy))
        ((x * dx + y * dy) / radius x y) 0 := by
    simpa only [zero_mul, add_zero] using
      hasDerivAt_radius_line x y dx dy 0
        (by simpa only [zero_mul, add_zero] using hr)
  have hden :
      radius (x + (0 : ℝ) * dx) (y + (0 : ℝ) * dy) ≠ 0 := by
    simpa only [zero_mul, add_zero] using hr0
  have hp :
      HasDerivAt
        (fun s : ℝ =>
          (x + s * dx) * dx + (y + s * dy) * dy)
        (dx ^ 2 + dy ^ 2) 0 := by
    convert
      (((hasDerivAt_const 0 x).add
          ((hasDerivAt_id 0).mul_const dx)).mul_const dx).add
        (((hasDerivAt_const 0 y).add
          ((hasDerivAt_id 0).mul_const dy)).mul_const dy)
      using 1 <;>
      (try simp only [Pi.add_apply, id_eq]) <;>
      ring
  have hquot :
      HasDerivAt
        (fun s : ℝ =>
          ((x + s * dx) * dx + (y + s * dy) * dy) /
            radius (x + s * dx) (y + s * dy))
        (((dx ^ 2 + dy ^ 2) * radius x y -
            (x * dx + y * dy) *
              ((x * dx + y * dy) / radius x y)) /
          radius x y ^ 2) 0 := by
    simpa only [zero_mul, add_zero] using
      hp.div hrad hden
  have houter :
      HasDerivAt
        (fun s : ℝ =>
          deriv f (radius (x + s * dx) (y + s * dy)))
        (deriv (deriv f) (radius x y) *
          ((x * dx + y * dy) / radius x y)) 0 := by
    simpa only [zero_mul, add_zero] using
      ((hdf _).hasDerivAt.comp 0 hrad)
  have hraw :
      HasDerivAt
        (fun s : ℝ =>
          deriv f (radius (x + s * dx) (y + s * dy)) *
            (((x + s * dx) * dx + (y + s * dy) * dy) /
              radius (x + s * dx) (y + s * dy)))
        ((deriv (deriv f) (radius x y) *
              ((x * dx + y * dy) / radius x y)) *
            ((x * dx + y * dy) / radius x y) +
          deriv f (radius x y) *
            (((dx ^ 2 + dy ^ 2) * radius x y -
                (x * dx + y * dy) *
                  ((x * dx + y * dy) / radius x y)) /
              radius x y ^ 2)) 0 := by
    simpa only [zero_mul, add_zero] using houter.mul hquot
  have hcross :
      (dx ^ 2 + dy ^ 2) * radius x y ^ 2 -
          (x * dx + y * dy) ^ 2 =
        (y * dx - x * dy) ^ 2 := by
    rw [hrsq]
    ring
  have hcoef :
      (deriv (deriv f) (radius x y) *
              ((x * dx + y * dy) / radius x y)) *
            ((x * dx + y * dy) / radius x y) +
          deriv f (radius x y) *
            (((dx ^ 2 + dy ^ 2) * radius x y -
                (x * dx + y * dy) *
                  ((x * dx + y * dy) / radius x y)) /
              radius x y ^ 2) =
        deriv (deriv f) (radius x y) *
            (x * dx + y * dy) ^ 2 / (x ^ 2 + y ^ 2) +
          deriv f (radius x y) *
            (y * dx - x * dy) ^ 2 / radius x y ^ 3 := by
    calc
      _ = deriv (deriv f) (radius x y) *
              (x * dx + y * dy) ^ 2 / radius x y ^ 2 +
            deriv f (radius x y) *
              (((dx ^ 2 + dy ^ 2) * radius x y ^ 2 -
                  (x * dx + y * dy) ^ 2) / radius x y ^ 3) := by
            field_simp [hr0] <;> ring
      _ = deriv (deriv f) (radius x y) *
              (x * dx + y * dy) ^ 2 / radius x y ^ 2 +
            deriv f (radius x y) *
              (y * dx - x * dy) ^ 2 / radius x y ^ 3 := by
            rw [hcross]
            ring
      _ = _ := by rw [hrsq]
  have htarget :
      HasDerivAt
        (fun s : ℝ =>
          deriv f (radius (x + s * dx) (y + s * dy)) *
            (((x + s * dx) * dx + (y + s * dy) * dy) /
              radius (x + s * dx) (y + s * dy)))
        (deriv (deriv f) (radius x y) *
            (x * dx + y * dy) ^ 2 / (x ^ 2 + y ^ 2) +
          deriv f (radius x y) *
            (y * dx - x * dy) ^ 2 / radius x y ^ 3) 0 := by
    simpa only [hcoef] using hraw
  have hr_event :
      ∀ᶠ s in nhds (0 : ℝ),
        radius (x + s * dx) (y + s * dy) ≠ 0 := by
    exact hrad.continuousAt.eventually_ne hden
  have hderiv_event :
      (fun s : ℝ =>
          deriv
            (fun t : ℝ =>
              f (radius (x + t * dx) (y + t * dy))) s) =ᶠ[nhds 0]
        (fun s : ℝ =>
          deriv f (radius (x + s * dx) (y + s * dy)) *
            (((x + s * dx) * dx + (y + s * dy) * dy) /
              radius (x + s * dx) (y + s * dy))) := by
    filter_upwards [hr_event] with s hrs
    have hqne :
        (x + s * dx) ^ 2 + (y + s * dy) ^ 2 ≠ 0 := by
      intro hzero
      apply hrs
      simp only [radius, hzero, Real.sqrt_zero]
    exact
      ((hf₁ _).hasDerivAt.comp s
        (hasDerivAt_radius_line x y dx dy s hqne)).deriv
  have hsecond :
      HasDerivAt
        (fun s : ℝ =>
          deriv
            (fun t : ℝ =>
              f (radius (x + t * dx) (y + t * dy))) s)
        (deriv (deriv f) (radius x y) *
            (x * dx + y * dy) ^ 2 / (x ^ 2 + y ^ 2) +
          deriv f (radius x y) *
            (y * dx - x * dy) ^ 2 / radius x y ^ 3) 0 :=
    htarget.congr_of_eventuallyEq hderiv_event
  have hu_line :
      (fun s : ℝ => u (x + s * dx) (y + s * dy)) =
        fun s : ℝ => f (radius (x + s * dx) (y + s * dy)) := by
    funext s
    exact hu _ _
  rw [hu_line]
  exact hsecond.deriv

end

end ProofGap.Exercise3290
