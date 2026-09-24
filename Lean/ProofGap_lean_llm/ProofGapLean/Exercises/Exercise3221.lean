import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Topology.Defs.Filter

namespace ProofGap.Exercise3221

noncomputable section

def u (x y : ℝ) : ℝ :=
  Real.log (x + y ^ 2)

def partialX (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => f t y) x

def partialY (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => f x t) y

def secondXX (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => partialX f t y) x

def secondYY (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => partialY f x t) y

def mixedXY (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => partialX f x t) y

private theorem hasDerivAt_const_add_sq (x y : ℝ) :
    HasDerivAt (fun t : ℝ => x + t ^ 2) (2 * y) y := by
  have hsq : HasDerivAt (fun t : ℝ => t ^ 2) (2 * y) y := by
    simpa [id, mul_comm] using ((hasDerivAt_id y).pow 2)
  simpa [add_comm] using hsq.add_const x

theorem gap1 :
    ∀ x y : ℝ, 0 < x + y ^ 2 →
      partialX u x y = 1 / (x + y ^ 2) := by
  intro x y h
  unfold partialX u
  have hinner : HasDerivAt (fun t : ℝ => t + y ^ 2) 1 x := by
    convert (hasDerivAt_id x).add (hasDerivAt_const x (y ^ 2)) using 1 <;> ring
  simpa [Function.comp_def, one_div] using
    ((Real.hasDerivAt_log (ne_of_gt h)).comp x hinner).deriv

theorem gap2 :
    ∀ x y : ℝ, 0 < x + y ^ 2 →
      partialY u x y = 2 * y / (x + y ^ 2) := by
  intro x y h
  unfold partialY u
  simpa [Function.comp_def, div_eq_mul_inv, mul_comm] using
    ((Real.hasDerivAt_log (ne_of_gt h)).comp y
      (hasDerivAt_const_add_sq x y)).deriv

theorem gap3 :
    ∀ x y : ℝ, 0 < x + y ^ 2 →
      secondXX u x y = -(1 / (x + y ^ 2) ^ 2) := by
  intro x y h
  have hc : ContinuousAt (fun t : ℝ => t + y ^ 2) x :=
    continuousAt_id.add continuousAt_const
  have hevent : ∀ᶠ t in nhds x, 0 < t + y ^ 2 := by
    exact hc.eventually (Ioi_mem_nhds h)
  have heq :
      (fun t : ℝ => partialX u t y) =ᶠ[nhds x]
        (fun t : ℝ => 1 / (t + y ^ 2)) :=
    hevent.mono (fun t ht => gap1 t y ht)
  have hinner : HasDerivAt (fun t : ℝ => t + y ^ 2) 1 x := by
    convert (hasDerivAt_id x).add (hasDerivAt_const x (y ^ 2)) using 1 <;> ring
  have hrat :
      HasDerivAt (fun t : ℝ => 1 / (t + y ^ 2))
        (-1 / (x + y ^ 2) ^ 2) x := by
    simpa only [one_div] using hinner.inv (ne_of_gt h)
  unfold secondXX
  calc
    deriv (fun t => partialX u t y) x =
        deriv (fun t : ℝ => 1 / (t + y ^ 2)) x := heq.deriv_eq
    _ = -1 / (x + y ^ 2) ^ 2 := hrat.deriv
    _ = -(1 / (x + y ^ 2) ^ 2) := by ring

theorem gap4 :
    ∀ x y : ℝ, 0 < x + y ^ 2 →
      secondYY u x y =
        2 / (x + y ^ 2) -
          (2 * y * (2 * y)) / (x + y ^ 2) ^ 2 := by
  intro x y h
  have hc : ContinuousAt (fun t : ℝ => x + t ^ 2) y :=
    continuousAt_const.add (continuousAt_id.pow 2)
  have hevent : ∀ᶠ t in nhds y, 0 < x + t ^ 2 := by
    exact hc.eventually (Ioi_mem_nhds h)
  have heq :
      (fun t : ℝ => partialY u x t) =ᶠ[nhds y]
        (fun t : ℝ => 2 * t / (x + t ^ 2)) :=
    hevent.mono (fun t ht => gap2 x t ht)
  have hnum : HasDerivAt (fun t : ℝ => 2 * t) 2 y := by
    convert (hasDerivAt_const y 2).mul (hasDerivAt_id y) using 1 <;> ring
  have hrat :
      HasDerivAt (fun t : ℝ => 2 * t / (x + t ^ 2))
        (2 / (x + y ^ 2) -
          (2 * y * (2 * y)) / (x + y ^ 2) ^ 2) y := by
    have hq := hnum.div (hasDerivAt_const_add_sq x y) (ne_of_gt h)
    convert hq using 1 <;> field_simp [ne_of_gt h] <;> ring
  unfold secondYY
  calc
    deriv (fun t => partialY u x t) y =
        deriv (fun t : ℝ => 2 * t / (x + t ^ 2)) y := heq.deriv_eq
    _ = 2 / (x + y ^ 2) -
          (2 * y * (2 * y)) / (x + y ^ 2) ^ 2 := hrat.deriv

theorem gap5 :
    ∀ x y : ℝ, 0 < x + y ^ 2 →
      2 / (x + y ^ 2) -
          (2 * y * (2 * y)) / (x + y ^ 2) ^ 2 =
        2 * (x - y ^ 2) / (x + y ^ 2) ^ 2 := by
  intro x y h
  have hn : x + y ^ 2 ≠ 0 := ne_of_gt h
  field_simp [hn] <;> ring

theorem gap6 :
    ∀ x y : ℝ, 0 < x + y ^ 2 →
      secondYY u x y =
        2 * (x - y ^ 2) / (x + y ^ 2) ^ 2 := by
  intro x y h
  calc
    secondYY u x y =
        2 / (x + y ^ 2) -
          (2 * y * (2 * y)) / (x + y ^ 2) ^ 2 := gap4 x y h
    _ = 2 * (x - y ^ 2) / (x + y ^ 2) ^ 2 := gap5 x y h

theorem gap7 :
    ∀ x y : ℝ, 0 < x + y ^ 2 →
      mixedXY u x y = -(2 * y / (x + y ^ 2) ^ 2) := by
  intro x y h
  have hc : ContinuousAt (fun t : ℝ => x + t ^ 2) y :=
    continuousAt_const.add (continuousAt_id.pow 2)
  have hevent : ∀ᶠ t in nhds y, 0 < x + t ^ 2 := by
    exact hc.eventually (Ioi_mem_nhds h)
  have heq :
      (fun t : ℝ => partialX u x t) =ᶠ[nhds y]
        (fun t : ℝ => 1 / (x + t ^ 2)) :=
    hevent.mono (fun t ht => gap1 x t ht)
  have hrat :
      HasDerivAt (fun t : ℝ => 1 / (x + t ^ 2))
        (-(2 * y) / (x + y ^ 2) ^ 2) y := by
    simpa only [one_div] using
      (hasDerivAt_const_add_sq x y).inv (ne_of_gt h)
  unfold mixedXY
  calc
    deriv (fun t => partialX u x t) y =
        deriv (fun t : ℝ => 1 / (x + t ^ 2)) y := heq.deriv_eq
    _ = -(2 * y) / (x + y ^ 2) ^ 2 := hrat.deriv
    _ = -(2 * y / (x + y ^ 2) ^ 2) := by ring

end

end ProofGap.Exercise3221
