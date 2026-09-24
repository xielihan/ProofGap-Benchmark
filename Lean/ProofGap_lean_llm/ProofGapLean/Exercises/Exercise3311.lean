import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Defs.Filter

namespace ProofGap.Exercise3311

noncomputable section

def radius (a b c x y z : ℝ) : ℝ :=
  Real.sqrt ((x - a) ^ 2 + (y - b) ^ 2 + (z - c) ^ 2)

def u (a b c x y z : ℝ) : ℝ :=
  1 / radius a b c x y z

def partialX (f : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  deriv (fun s => f s y z) x

def partialY (f : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  deriv (fun s => f x s z) y

def partialZ (f : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  deriv (fun s => f x y s) z

def partialXX (f : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  deriv (fun s => partialX f s y z) x

def partialYY (f : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  deriv (fun s => partialY f x s z) y

def partialZZ (f : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  deriv (fun s => partialZ f x y s) z

private theorem secondDeriv_invSqrt_sq_add
    (a d t : ℝ)
    (hr : Real.sqrt ((t - a) ^ 2 + d) ≠ 0) :
    deriv
        (fun s : ℝ =>
          deriv (fun q : ℝ => 1 / Real.sqrt ((q - a) ^ 2 + d)) s)
        t =
      -1 / (Real.sqrt ((t - a) ^ 2 + d)) ^ 3 +
        3 * (t - a) ^ 2 / (Real.sqrt ((t - a) ^ 2 + d)) ^ 5 := by
  have hRadius : ∀ s : ℝ, Real.sqrt ((s - a) ^ 2 + d) ≠ 0 →
      HasDerivAt
        (fun q : ℝ => Real.sqrt ((q - a) ^ 2 + d))
        ((s - a) / Real.sqrt ((s - a) ^ 2 + d)) s := by
    intro s hs
    have hq : (s - a) ^ 2 + d ≠ 0 := by
      intro hzero
      apply hs
      rw [hzero]
      simp
    have hinner :
        HasDerivAt (fun q : ℝ => (q - a) ^ 2 + d) (2 * (s - a)) s := by
      convert (((hasDerivAt_id s).sub_const a).pow 2).add_const d using 1 <;>
        norm_num <;> ring
    have hcomp := (Real.hasDerivAt_sqrt hq).comp s hinner
    convert hcomp using 1 <;> field_simp [hs] <;> ring
  have hInv : ∀ s : ℝ, Real.sqrt ((s - a) ^ 2 + d) ≠ 0 →
      HasDerivAt
        (fun q : ℝ => 1 / Real.sqrt ((q - a) ^ 2 + d))
        (-(s - a) / (Real.sqrt ((s - a) ^ 2 + d)) ^ 3) s := by
    intro s hs
    have h := hRadius s hs
    have hcoeff :
        -((s - a) / Real.sqrt ((s - a) ^ 2 + d)) /
            (Real.sqrt ((s - a) ^ 2 + d)) ^ 2 =
          -(s - a) / (Real.sqrt ((s - a) ^ 2 + d)) ^ 3 := by
      field_simp [hs]
    rw [← hcoeff]
    simpa only [one_div] using h.inv hs
  have hs := hRadius t hr
  have houter :
      HasDerivAt
        (fun s : ℝ =>
          -(s - a) / (Real.sqrt ((s - a) ^ 2 + d)) ^ 3)
        (-1 / (Real.sqrt ((t - a) ^ 2 + d)) ^ 3 +
          3 * (t - a) ^ 2 / (Real.sqrt ((t - a) ^ 2 + d)) ^ 5) t := by
    have hnum : HasDerivAt (fun s : ℝ => -(s - a)) (-1) t :=
      ((hasDerivAt_id t).sub_const a).neg
    have hden := hs.pow 3
    have hquot := hnum.div hden (pow_ne_zero 3 hr)
    have hcoeff :
        ((-1) * (Real.sqrt ((t - a) ^ 2 + d)) ^ 3 -
            (-(t - a)) *
              ((3 : ℝ) * (Real.sqrt ((t - a) ^ 2 + d)) ^ (3 - 1) *
                ((t - a) / Real.sqrt ((t - a) ^ 2 + d)))) /
            ((Real.sqrt ((t - a) ^ 2 + d)) ^ 3) ^ 2 =
          -1 / (Real.sqrt ((t - a) ^ 2 + d)) ^ 3 +
            3 * (t - a) ^ 2 / (Real.sqrt ((t - a) ^ 2 + d)) ^ 5 := by
      norm_num
      field_simp [hr]
      ring
    rw [← hcoeff]
    simpa only [Pi.div_apply, Pi.pow_apply] using hquot
  have heq :
      (fun s : ℝ =>
          deriv (fun q : ℝ => 1 / Real.sqrt ((q - a) ^ 2 + d)) s) =ᶠ[nhds t]
        (fun s : ℝ =>
          -(s - a) / (Real.sqrt ((s - a) ^ 2 + d)) ^ 3) := by
    filter_upwards [hs.continuousAt.eventually_ne hr] with s hs_ne
    exact (hInv s hs_ne).deriv
  rw [heq.deriv_eq]
  exact houter.deriv

theorem gap1 (a b c x y z : ℝ) (hr : radius a b c x y z ≠ 0) :
    partialXX (u a b c) x y z =
      -1 / (radius a b c x y z) ^ 3 +
        3 * (x - a) ^ 2 / (radius a b c x y z) ^ 5 := by
  have hr' :
      Real.sqrt ((x - a) ^ 2 + ((y - b) ^ 2 + (z - c) ^ 2)) ≠ 0 := by
    simpa [radius, add_assoc] using hr
  simpa [partialXX, partialX, u, radius, add_assoc] using
    (secondDeriv_invSqrt_sq_add a ((y - b) ^ 2 + (z - c) ^ 2) x hr')

theorem gap2 (a b c x y z : ℝ) (hr : radius a b c x y z ≠ 0) :
    partialYY (u a b c) x y z =
      -1 / (radius a b c x y z) ^ 3 +
        3 * (y - b) ^ 2 / (radius a b c x y z) ^ 5 := by
  have hr' :
      Real.sqrt ((y - b) ^ 2 + ((x - a) ^ 2 + (z - c) ^ 2)) ≠ 0 := by
    simpa [radius, add_comm, add_left_comm, add_assoc] using hr
  simpa [partialYY, partialY, u, radius, add_comm, add_left_comm, add_assoc] using
    (secondDeriv_invSqrt_sq_add b ((x - a) ^ 2 + (z - c) ^ 2) y hr')

theorem gap3 (a b c x y z : ℝ) (hr : radius a b c x y z ≠ 0) :
    partialZZ (u a b c) x y z =
      -1 / (radius a b c x y z) ^ 3 +
        3 * (z - c) ^ 2 / (radius a b c x y z) ^ 5 := by
  have hr' :
      Real.sqrt ((z - c) ^ 2 + ((x - a) ^ 2 + (y - b) ^ 2)) ≠ 0 := by
    simpa [radius, add_comm, add_left_comm, add_assoc] using hr
  simpa [partialZZ, partialZ, u, radius, add_comm, add_left_comm, add_assoc] using
    (secondDeriv_invSqrt_sq_add c ((x - a) ^ 2 + (y - b) ^ 2) z hr')

theorem gap4 (a b c x y z : ℝ) (hr : radius a b c x y z ≠ 0) :
    partialXX (u a b c) x y z +
      partialYY (u a b c) x y z +
      partialZZ (u a b c) x y z = 0 := by
  rw [gap1 a b c x y z hr, gap2 a b c x y z hr,
    gap3 a b c x y z hr]
  have hq :
      0 ≤ (x - a) ^ 2 + (y - b) ^ 2 + (z - c) ^ 2 :=
    add_nonneg (add_nonneg (sq_nonneg _) (sq_nonneg _)) (sq_nonneg _)
  have hrsq :
      radius a b c x y z ^ 2 =
        (x - a) ^ 2 + (y - b) ^ 2 + (z - c) ^ 2 := by
    simpa [radius] using Real.sq_sqrt hq
  field_simp [hr] <;> nlinarith [hrsq]

theorem gap5 (a b c : ℝ) :
    ∀ x y z, radius a b c x y z ≠ 0 →
      partialXX (u a b c) x y z +
        partialYY (u a b c) x y z +
        partialZZ (u a b c) x y z = 0 := by
  intro x y z hr
  exact gap4 a b c x y z hr

end

end ProofGap.Exercise3311
