import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Topology.Neighborhoods
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Topology.Defs.Filter

namespace ProofGap.Exercise3281_2

noncomputable section

def partialXOrder (n : ℕ) (f : ℝ → ℝ → ℝ)
    (x y : ℝ) : ℝ :=
  (deriv^[n]) (fun t => f t y) x

def partialYOrder (n : ℕ) (f : ℝ → ℝ → ℝ)
    (x y : ℝ) : ℝ :=
  (deriv^[n]) (fun t => f x t) y

def laplacian (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  partialXOrder 2 f x y + partialYOrder 2 f x y

def u (x y : ℝ) : ℝ :=
  Real.log (Real.sqrt (x ^ 2 + y ^ 2))

theorem gap1 (x y : ℝ) (hr : x ^ 2 + y ^ 2 ≠ 0) :
    partialXOrder 1 u x y = x / (x ^ 2 + y ^ 2) := by
  change
    deriv (fun t : ℝ => Real.log (Real.sqrt (t ^ 2 + y ^ 2))) x =
      x / (x ^ 2 + y ^ 2)
  have hq0 : 0 ≤ x ^ 2 + y ^ 2 :=
    add_nonneg (sq_nonneg x) (sq_nonneg y)
  have hq : 0 < x ^ 2 + y ^ 2 :=
    lt_of_le_of_ne hq0 hr.symm
  have hsne : Real.sqrt (x ^ 2 + y ^ 2) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hq)
  have hsquare :
      Real.sqrt (x ^ 2 + y ^ 2) ^ 2 = x ^ 2 + y ^ 2 :=
    Real.sq_sqrt hq0
  have hsq : HasDerivAt (fun t : ℝ => t ^ 2) (2 * x) x := by
    convert (hasDerivAt_id x).pow 2 using 1 <;> simp
  have hpoly :
      HasDerivAt (fun t : ℝ => t ^ 2 + y ^ 2) (2 * x) x :=
    hsq.add_const (y ^ 2)
  have hraw :=
    (Real.hasDerivAt_log hsne).comp x
      ((Real.hasDerivAt_sqrt hr).comp x hpoly)
  calc
    deriv (fun t : ℝ => Real.log (Real.sqrt (t ^ 2 + y ^ 2))) x =
        (Real.sqrt (x ^ 2 + y ^ 2))⁻¹ *
          (1 / (2 * Real.sqrt (x ^ 2 + y ^ 2)) * (2 * x)) := by
      simpa only [Function.comp_def] using hraw.deriv
    _ = x / Real.sqrt (x ^ 2 + y ^ 2) ^ 2 := by
      field_simp [hsne] <;> ring
    _ = x / (x ^ 2 + y ^ 2) := by
      rw [hsquare]

theorem gap2 (x y : ℝ) (hr : x ^ 2 + y ^ 2 ≠ 0) :
    partialXOrder 2 u x y =
      (y ^ 2 - x ^ 2) / (x ^ 2 + y ^ 2) ^ 2 := by
  change
    deriv (fun t : ℝ => deriv (fun s : ℝ => u s y) t) x =
      (y ^ 2 - x ^ 2) / (x ^ 2 + y ^ 2) ^ 2
  have hcont : ContinuousAt (fun t : ℝ => t ^ 2 + y ^ 2) x :=
    (continuousAt_id.pow 2).add continuousAt_const
  have hevent : ∀ᶠ t in nhds x, t ^ 2 + y ^ 2 ≠ 0 :=
    hcont.eventually_ne hr
  have hfun :
      (fun t : ℝ => deriv (fun s : ℝ => u s y) t) =ᶠ[nhds x]
        (fun t : ℝ => t / (t ^ 2 + y ^ 2)) :=
    hevent.mono (by
      intro t ht
      simpa [partialXOrder] using gap1 t y ht)
  have hsq : HasDerivAt (fun t : ℝ => t ^ 2) (2 * x) x := by
    convert (hasDerivAt_id x).pow 2 using 1 <;> simp
  have hden :
      HasDerivAt (fun t : ℝ => t ^ 2 + y ^ 2) (2 * x) x :=
    hsq.add_const (y ^ 2)
  have hquot :
      HasDerivAt (fun t : ℝ => t / (t ^ 2 + y ^ 2))
        ((1 * (x ^ 2 + y ^ 2) - x * (2 * x)) /
          (x ^ 2 + y ^ 2) ^ 2) x :=
    (hasDerivAt_id x).div hden hr
  calc
    deriv (fun t : ℝ => deriv (fun s : ℝ => u s y) t) x =
        deriv (fun t : ℝ => t / (t ^ 2 + y ^ 2)) x := hfun.deriv_eq
    _ = (1 * (x ^ 2 + y ^ 2) - x * (2 * x)) /
          (x ^ 2 + y ^ 2) ^ 2 := hquot.deriv
    _ = (y ^ 2 - x ^ 2) / (x ^ 2 + y ^ 2) ^ 2 := by
      ring

theorem gap3 (x y : ℝ) (hr : x ^ 2 + y ^ 2 ≠ 0) :
    partialYOrder 2 u x y =
      (x ^ 2 - y ^ 2) / (x ^ 2 + y ^ 2) ^ 2 := by
  change
    deriv (fun t : ℝ => deriv (fun s : ℝ => u x s) t) y =
      (x ^ 2 - y ^ 2) / (x ^ 2 + y ^ 2) ^ 2
  have hu : (fun s : ℝ => u x s) = (fun s : ℝ => u s x) := by
    funext s
    simp only [u]
    rw [add_comm]
  have hcont : ContinuousAt (fun t : ℝ => x ^ 2 + t ^ 2) y :=
    continuousAt_const.add (continuousAt_id.pow 2)
  have hevent : ∀ᶠ t in nhds y, x ^ 2 + t ^ 2 ≠ 0 :=
    hcont.eventually_ne hr
  have hfun :
      (fun t : ℝ => deriv (fun s : ℝ => u x s) t) =ᶠ[nhds y]
        (fun t : ℝ => t / (x ^ 2 + t ^ 2)) :=
    hevent.mono (by
      intro t ht
      have ht' : t ^ 2 + x ^ 2 ≠ 0 := by
        simpa [add_comm] using ht
      rw [hu]
      calc
        deriv (fun s : ℝ => u s x) t = t / (t ^ 2 + x ^ 2) := by
          simpa [partialXOrder] using gap1 t x ht'
        _ = t / (x ^ 2 + t ^ 2) := by rw [add_comm])
  have hsq : HasDerivAt (fun t : ℝ => t ^ 2) (2 * y) y := by
    convert (hasDerivAt_id y).pow 2 using 1 <;> simp
  have hden :
      HasDerivAt (fun t : ℝ => x ^ 2 + t ^ 2) (2 * y) y :=
    hsq.const_add (x ^ 2)
  have hquot :
      HasDerivAt (fun t : ℝ => t / (x ^ 2 + t ^ 2))
        ((1 * (x ^ 2 + y ^ 2) - y * (2 * y)) /
          (x ^ 2 + y ^ 2) ^ 2) y :=
    (hasDerivAt_id y).div hden hr
  calc
    deriv (fun t : ℝ => deriv (fun s : ℝ => u x s) t) y =
        deriv (fun t : ℝ => t / (x ^ 2 + t ^ 2)) y := hfun.deriv_eq
    _ = (1 * (x ^ 2 + y ^ 2) - y * (2 * y)) /
          (x ^ 2 + y ^ 2) ^ 2 := hquot.deriv
    _ = (x ^ 2 - y ^ 2) / (x ^ 2 + y ^ 2) ^ 2 := by
      ring

theorem gap4 (x y : ℝ) (hr : x ^ 2 + y ^ 2 ≠ 0) :
    laplacian u x y =
      (y ^ 2 - x ^ 2) / (x ^ 2 + y ^ 2) ^ 2 +
        (x ^ 2 - y ^ 2) / (x ^ 2 + y ^ 2) ^ 2 := by
  unfold laplacian
  rw [gap2 x y hr, gap3 x y hr]

theorem gap5 (x y : ℝ) (hr : x ^ 2 + y ^ 2 ≠ 0) :
    (y ^ 2 - x ^ 2) / (x ^ 2 + y ^ 2) ^ 2 +
        (x ^ 2 - y ^ 2) / (x ^ 2 + y ^ 2) ^ 2 = 0 := by
  ring

theorem gap6 (x y : ℝ) (hr : x ^ 2 + y ^ 2 ≠ 0) :
    laplacian u x y = 0 := by
  rw [gap4 x y hr, gap5 x y hr]

end

end ProofGap.Exercise3281_2
