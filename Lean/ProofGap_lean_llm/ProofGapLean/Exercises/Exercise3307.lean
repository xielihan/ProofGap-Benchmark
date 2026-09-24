import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Topology.Neighborhoods
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Defs.Filter

namespace ProofGap.Exercise3307

noncomputable section

def radiusSq (a b x y : ℝ) : ℝ :=
  (x - a) ^ 2 + (y - b) ^ 2

def u (a b x y : ℝ) : ℝ :=
  Real.log (Real.sqrt (radiusSq a b x y))

def partialX (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun s => f s y) x

def partialXX (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun s => partialX f s y) x

def partialYY (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun s => deriv (fun t => f x t) s) y

private theorem deriv_u_second_formula (a b x y : ℝ)
    (h : radiusSq a b x y ≠ 0) :
    deriv (fun t => u a b x t) y = (y - b) / radiusSq a b x y := by
  have hr_nonneg : 0 ≤ radiusSq a b x y := by
    unfold radiusSq
    positivity
  have hr_pos : 0 < radiusSq a b x y :=
    lt_of_le_of_ne hr_nonneg (Ne.symm h)
  have hsqrt_ne : Real.sqrt (radiusSq a b x y) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hr_pos)
  have hr : HasDerivAt (fun s : ℝ => radiusSq a b x s) (2 * (y - b)) y := by
    simpa [radiusSq] using
      (((hasDerivAt_id y).sub_const b).pow 2).const_add ((x - a) ^ 2)
  have hu : HasDerivAt (fun s : ℝ => u a b x s)
      ((Real.sqrt (radiusSq a b x y))⁻¹ *
        ((2 * Real.sqrt (radiusSq a b x y))⁻¹ * (2 * (y - b)))) y := by
    simpa [u] using
      (Real.hasDerivAt_log hsqrt_ne).comp y
        ((Real.hasDerivAt_sqrt h).comp y hr)
  rw [hu.deriv]
  field_simp [hsqrt_ne, h] <;>
    simp only [Real.sq_sqrt hr_nonneg] <;>
    ring

theorem gap1 (a b x y : ℝ) (h : radiusSq a b x y ≠ 0) :
    partialX (u a b) x y =
      (x - a) / radiusSq a b x y := by
  have hr_nonneg : 0 ≤ radiusSq a b x y := by
    unfold radiusSq
    positivity
  have hr_pos : 0 < radiusSq a b x y :=
    lt_of_le_of_ne hr_nonneg (Ne.symm h)
  have hsqrt_ne : Real.sqrt (radiusSq a b x y) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hr_pos)
  have hr : HasDerivAt (fun s : ℝ => radiusSq a b s y) (2 * (x - a)) x := by
    simpa [radiusSq] using
      (((hasDerivAt_id x).sub_const a).pow 2).add_const ((y - b) ^ 2)
  have hu : HasDerivAt (fun s : ℝ => u a b s y)
      ((Real.sqrt (radiusSq a b x y))⁻¹ *
        ((2 * Real.sqrt (radiusSq a b x y))⁻¹ * (2 * (x - a)))) x := by
    simpa [u] using
      (Real.hasDerivAt_log hsqrt_ne).comp x
        ((Real.hasDerivAt_sqrt h).comp x hr)
  unfold partialX
  rw [hu.deriv]
  field_simp [hsqrt_ne, h] <;>
    simp only [Real.sq_sqrt hr_nonneg] <;>
    ring

theorem gap2 (a b x y : ℝ) (h : radiusSq a b x y ≠ 0) :
    partialXX (u a b) x y =
      ((y - b) ^ 2 - (x - a) ^ 2) / (radiusSq a b x y) ^ 2 := by
  have hr_nonneg : 0 ≤ radiusSq a b x y := by
    unfold radiusSq
    positivity
  have hr_pos : 0 < radiusSq a b x y :=
    lt_of_le_of_ne hr_nonneg (Ne.symm h)
  have hr : HasDerivAt (fun s : ℝ => radiusSq a b s y) (2 * (x - a)) x := by
    simpa [radiusSq] using
      (((hasDerivAt_id x).sub_const a).pow 2).add_const ((y - b) ^ 2)
  have hpos : ∀ᶠ s in nhds x, 0 < radiusSq a b s y :=
    hr.continuousAt (Ioi_mem_nhds hr_pos)
  have heq :
      (fun s : ℝ => partialX (u a b) s y) =ᶠ[nhds x]
        (fun s : ℝ => (s - a) / radiusSq a b s y) :=
    hpos.mono (fun s hs => gap1 a b s y (ne_of_gt hs))
  have hn : HasDerivAt (fun s : ℝ => s - a) 1 x := by
    simpa using (hasDerivAt_id x).sub_const a
  have hquot : HasDerivAt
      (fun s : ℝ => (s - a) / radiusSq a b s y)
      ((1 * radiusSq a b x y - (x - a) * (2 * (x - a))) /
        radiusSq a b x y ^ 2) x := by
    exact hn.div hr h
  have hp : HasDerivAt
      (fun s : ℝ => partialX (u a b) s y)
      ((1 * radiusSq a b x y - (x - a) * (2 * (x - a))) /
        radiusSq a b x y ^ 2) x :=
    hquot.congr_of_eventuallyEq heq
  unfold partialXX
  rw [hp.deriv]
  field_simp [h]
  unfold radiusSq
  ring

theorem gap3 (a b x y : ℝ) (h : radiusSq a b x y ≠ 0) :
    partialYY (u a b) x y =
      ((x - a) ^ 2 - (y - b) ^ 2) / (radiusSq a b x y) ^ 2 := by
  have hr_nonneg : 0 ≤ radiusSq a b x y := by
    unfold radiusSq
    positivity
  have hr_pos : 0 < radiusSq a b x y :=
    lt_of_le_of_ne hr_nonneg (Ne.symm h)
  have hr : HasDerivAt (fun s : ℝ => radiusSq a b x s) (2 * (y - b)) y := by
    simpa [radiusSq] using
      (((hasDerivAt_id y).sub_const b).pow 2).const_add ((x - a) ^ 2)
  have hpos : ∀ᶠ s in nhds y, 0 < radiusSq a b x s :=
    hr.continuousAt (Ioi_mem_nhds hr_pos)
  have heq :
      (fun s : ℝ => deriv (fun t => u a b x t) s) =ᶠ[nhds y]
        (fun s : ℝ => (s - b) / radiusSq a b x s) :=
    hpos.mono (fun s hs =>
      deriv_u_second_formula a b x s (ne_of_gt hs))
  have hn : HasDerivAt (fun s : ℝ => s - b) 1 y := by
    simpa using (hasDerivAt_id y).sub_const b
  have hquot : HasDerivAt
      (fun s : ℝ => (s - b) / radiusSq a b x s)
      ((1 * radiusSq a b x y - (y - b) * (2 * (y - b))) /
        radiusSq a b x y ^ 2) y := by
    exact hn.div hr h
  have hp : HasDerivAt
      (fun s : ℝ => deriv (fun t => u a b x t) s)
      ((1 * radiusSq a b x y - (y - b) * (2 * (y - b))) /
        radiusSq a b x y ^ 2) y :=
    hquot.congr_of_eventuallyEq heq
  unfold partialYY
  rw [hp.deriv]
  field_simp [h]
  unfold radiusSq
  ring

theorem gap4 (a b x y : ℝ) (h : radiusSq a b x y ≠ 0) :
    partialXX (u a b) x y + partialYY (u a b) x y = 0 := by
  rw [gap2 a b x y h, gap3 a b x y h]
  ring

theorem gap5 (a b : ℝ) :
    ∀ x y, radiusSq a b x y ≠ 0 →
      partialXX (u a b) x y + partialYY (u a b) x y = 0 := by
  intro x y h
  exact gap4 a b x y h

end

end ProofGap.Exercise3307
