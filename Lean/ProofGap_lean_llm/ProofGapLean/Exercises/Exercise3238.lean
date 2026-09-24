import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Topology.Defs.Filter

namespace ProofGap.Exercise3238

noncomputable section

def radialSq (x y : ℝ) : ℝ :=
  x ^ 2 + y ^ 2

def u (x y : ℝ) : ℝ :=
  Real.log (Real.sqrt (radialSq x y))

def admissible (x y : ℝ) : Prop :=
  0 < radialSq x y

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

def firstForm (x y dx dy : ℝ) : ℝ :=
  (x * dx + y * dy) / radialSq x y

def secondRaw (x y dx dy : ℝ) : ℝ :=
  (dx ^ 2 + dy ^ 2) / radialSq x y -
    2 * (x * dx + y * dy) ^ 2 / radialSq x y ^ 2

def secondSimplified (x y dx dy : ℝ) : ℝ :=
  ((y ^ 2 - x ^ 2) * (dx ^ 2 - dy ^ 2) -
      4 * x * y * dx * dy) /
    radialSq x y ^ 2

private theorem firstPartials_u (x y : ℝ) (h : admissible x y) :
    partialX u x y = x / radialSq x y ∧
      partialY u x y = y / radialSq x y := by
  change 0 < radialSq x y at h
  have hr : radialSq x y ≠ 0 := ne_of_gt h
  have hs : 0 < Real.sqrt (radialSq x y) := Real.sqrt_pos.2 h
  have hrx : HasDerivAt (fun t : ℝ => radialSq t y) (2 * x) x := by
    have hraw :
        HasDerivAt (id ^ 2 + fun _ : ℝ => y ^ 2) (2 * x) x := by
      simpa [id_eq] using
        (((hasDerivAt_id x).pow 2).add (hasDerivAt_const x (y ^ 2)))
    have hfun :
        (id ^ 2 + fun _ : ℝ => y ^ 2) =
          (fun t : ℝ => radialSq t y) := by
      funext t
      rfl
    rw [← hfun]
    exact hraw
  have hry : HasDerivAt (fun t : ℝ => radialSq x t) (2 * y) y := by
    have hraw :
        HasDerivAt ((fun _ : ℝ => x ^ 2) + id ^ 2) (2 * y) y := by
      simpa [id_eq] using
        ((hasDerivAt_const y (x ^ 2)).add ((hasDerivAt_id y).pow 2))
    have hfun :
        ((fun _ : ℝ => x ^ 2) + id ^ 2) =
          (fun t : ℝ => radialSq x t) := by
      funext t
      rfl
    rw [← hfun]
    exact hraw
  have hcoef (z : ℝ) :
      (Real.sqrt (radialSq x y))⁻¹ *
          ((2 * Real.sqrt (radialSq x y))⁻¹ * (2 * z)) =
        z / radialSq x y := by
    calc
      (Real.sqrt (radialSq x y))⁻¹ *
            ((2 * Real.sqrt (radialSq x y))⁻¹ * (2 * z)) =
          z / (Real.sqrt (radialSq x y)) ^ 2 := by
            field_simp [hs.ne'] <;> ring
      _ = z / radialSq x y := by
        rw [Real.sq_sqrt (le_of_lt h)]
  have huX : HasDerivAt (fun t : ℝ => u t y) (x / radialSq x y) x := by
    have hcomp :
        HasDerivAt (fun t : ℝ => u t y)
          ((Real.sqrt (radialSq x y))⁻¹ *
            ((2 * Real.sqrt (radialSq x y))⁻¹ * (2 * x))) x := by
      simpa only [u, Function.comp_apply, one_div] using
        ((Real.hasDerivAt_log hs.ne').comp x
          ((Real.hasDerivAt_sqrt hr).comp x hrx))
    simpa only [hcoef x] using hcomp
  have huY : HasDerivAt (fun t : ℝ => u x t) (y / radialSq x y) y := by
    have hcomp :
        HasDerivAt (fun t : ℝ => u x t)
          ((Real.sqrt (radialSq x y))⁻¹ *
            ((2 * Real.sqrt (radialSq x y))⁻¹ * (2 * y))) y := by
      simpa only [u, Function.comp_apply, one_div] using
        ((Real.hasDerivAt_log hs.ne').comp y
          ((Real.hasDerivAt_sqrt hr).comp y hry))
    simpa only [hcoef y] using hcomp
  constructor
  · simpa only [partialX] using huX.deriv
  · simpa only [partialY] using huY.deriv

theorem gap1 :
    ∀ x y dx dy : ℝ, admissible x y →
      differential u x y dx dy = firstForm x y dx dy := by
  intro x y dx dy h
  rcases firstPartials_u x y h with ⟨hx, hy⟩
  have hr : radialSq x y ≠ 0 := ne_of_gt h
  unfold differential firstForm
  rw [hx, hy]
  field_simp [radialSq, hr] <;> ring

theorem gap2 :
    ∀ x y dx dy : ℝ, admissible x y →
      secondDifferential u x y dx dy = secondRaw x y dx dy := by
  intro x y dx dy h
  change 0 < radialSq x y at h
  have hr : radialSq x y ≠ 0 := ne_of_gt h
  have hcX : ContinuousAt (fun t : ℝ => radialSq t y) x := by
    simpa only [radialSq] using
      (continuousAt_id.pow 2).add
        (continuousAt_const : ContinuousAt (fun _ : ℝ => y ^ 2) x)
  have hcY : ContinuousAt (fun t : ℝ => radialSq x t) y := by
    simpa only [radialSq] using
      (continuousAt_const : ContinuousAt (fun _ : ℝ => x ^ 2) y).add
        (continuousAt_id.pow 2)
  have hadmX : ∀ᶠ t in nhds x, admissible t y := by
    simpa only [admissible] using (hcX (Ioi_mem_nhds h))
  have hadmY : ∀ᶠ t in nhds y, admissible x t := by
    simpa only [admissible] using (hcY (Ioi_mem_nhds h))
  have heqX :
      (fun t : ℝ => partialX u t y) =ᶠ[nhds x]
        (fun t : ℝ => t / radialSq t y) :=
    hadmX.mono (fun t ht => (firstPartials_u t y ht).1)
  have heqXY :
      (fun t : ℝ => partialX u x t) =ᶠ[nhds y]
        (fun t : ℝ => x / radialSq x t) :=
    hadmY.mono (fun t ht => (firstPartials_u x t ht).1)
  have heqY :
      (fun t : ℝ => partialY u x t) =ᶠ[nhds y]
        (fun t : ℝ => t / radialSq x t) :=
    hadmY.mono (fun t ht => (firstPartials_u x t ht).2)
  have hdenX :
      HasDerivAt (fun t : ℝ => radialSq t y) (2 * x) x := by
    have hraw :
        HasDerivAt (id ^ 2 + fun _ : ℝ => y ^ 2) (2 * x) x := by
      simpa [id_eq] using
        (((hasDerivAt_id x).pow 2).add (hasDerivAt_const x (y ^ 2)))
    have hfun :
        (id ^ 2 + fun _ : ℝ => y ^ 2) =
          (fun t : ℝ => radialSq t y) := by
      funext t
      rfl
    rw [← hfun]
    exact hraw
  have hdenY :
      HasDerivAt (fun t : ℝ => radialSq x t) (2 * y) y := by
    have hraw :
        HasDerivAt ((fun _ : ℝ => x ^ 2) + id ^ 2) (2 * y) y := by
      simpa [id_eq] using
        ((hasDerivAt_const y (x ^ 2)).add ((hasDerivAt_id y).pow 2))
    have hfun :
        ((fun _ : ℝ => x ^ 2) + id ^ 2) =
          (fun t : ℝ => radialSq x t) := by
      funext t
      rfl
    rw [← hfun]
    exact hraw
  have hdxx :
      HasDerivAt (fun t : ℝ => t / radialSq t y)
        ((1 * radialSq x y - x * (2 * x)) / radialSq x y ^ 2) x := by
    simpa only [id_eq] using ((hasDerivAt_id x).div hdenX hr)
  have hdxy :
      HasDerivAt (fun t : ℝ => x / radialSq x t)
        ((0 * radialSq x y - x * (2 * y)) / radialSq x y ^ 2) y := by
    simpa only using ((hasDerivAt_const y x).div hdenY hr)
  have hdyy :
      HasDerivAt (fun t : ℝ => t / radialSq x t)
        ((1 * radialSq x y - y * (2 * y)) / radialSq x y ^ 2) y := by
    simpa only [id_eq] using ((hasDerivAt_id y).div hdenY hr)
  have hxx :
      partialXX u x y = (y ^ 2 - x ^ 2) / radialSq x y ^ 2 := by
    unfold partialXX
    rw [heqX.deriv_eq]
    calc
      deriv (fun t : ℝ => t / radialSq t y) x =
          (1 * radialSq x y - x * (2 * x)) / radialSq x y ^ 2 := hdxx.deriv
      _ = (y ^ 2 - x ^ 2) / radialSq x y ^ 2 := by
        unfold radialSq
        ring
  have hxy :
      partialXY u x y = -2 * x * y / radialSq x y ^ 2 := by
    unfold partialXY
    rw [heqXY.deriv_eq]
    calc
      deriv (fun t : ℝ => x / radialSq x t) y =
          (0 * radialSq x y - x * (2 * y)) / radialSq x y ^ 2 := hdxy.deriv
      _ = -2 * x * y / radialSq x y ^ 2 := by ring
  have hyy :
      partialYY u x y = (x ^ 2 - y ^ 2) / radialSq x y ^ 2 := by
    unfold partialYY
    rw [heqY.deriv_eq]
    calc
      deriv (fun t : ℝ => t / radialSq x t) y =
          (1 * radialSq x y - y * (2 * y)) / radialSq x y ^ 2 := hdyy.deriv
      _ = (x ^ 2 - y ^ 2) / radialSq x y ^ 2 := by
        unfold radialSq
        ring
  unfold secondDifferential secondRaw
  rw [hxx, hxy, hyy]
  unfold radialSq at hr ⊢
  field_simp [hr] <;> ring

theorem gap3 :
    ∀ x y dx dy : ℝ, admissible x y →
      secondRaw x y dx dy = secondSimplified x y dx dy := by
  intro x y dx dy h
  change 0 < radialSq x y at h
  have hr : radialSq x y ≠ 0 := ne_of_gt h
  unfold secondRaw secondSimplified
  unfold radialSq at hr ⊢
  field_simp [hr] <;> ring

theorem gap4 :
    ∀ x y dx dy : ℝ, admissible x y →
      secondDifferential u x y dx dy =
        secondSimplified x y dx dy := by
  intro x y dx dy h
  calc
    secondDifferential u x y dx dy = secondRaw x y dx dy :=
      gap2 x y dx dy h
    _ = secondSimplified x y dx dy := gap3 x y dx dy h

end

end ProofGap.Exercise3238
