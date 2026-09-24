import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Group.Arithmetic
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise4301

noncomputable section

open MeasureTheory
open scoped Interval

def P (x y : ℝ) : ℝ :=
  Real.exp (-(x ^ 2 + y ^ 2)) * Real.cos (2 * x * y)

def Q (x y : ℝ) : ℝ :=
  Real.exp (-(x ^ 2 + y ^ 2)) * Real.sin (2 * x * y)

def curl (x y : ℝ) : ℝ :=
  deriv (fun t => Q t y) x - deriv (fun t => P x t) y

def circle (R t : ℝ) : ℝ × ℝ :=
  (R * Real.cos t, R * Real.sin t)

def circleIntegral (R : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..2 * Real.pi,
    P (circle R t).1 (circle R t).2 *
        deriv (fun s => (circle R s).1) t +
      Q (circle R t).1 (circle R t).2 *
        deriv (fun s => (circle R s).2) t

def disk (R : ℝ) : Set (ℝ × ℝ) :=
  {z | z.1 ^ 2 + z.2 ^ 2 ≤ R ^ 2}

def curlAreaIntegral (R : ℝ) : ℝ :=
  ∫ z in disk R, curl z.1 z.2

private theorem circleIntegral_vanishes (R : ℝ) : circleIntegral R = 0 := by
  have hx (t : ℝ) :
      deriv (fun s => (circle R s).1) t = -(R * Real.sin t) := by
    simpa [circle] using ((Real.hasDerivAt_cos t).const_mul R).deriv
  have hy (t : ℝ) :
      deriv (fun s => (circle R s).2) t = R * Real.cos t := by
    simpa [circle] using ((Real.hasDerivAt_sin t).const_mul R).deriv
  unfold circleIntegral
  simp_rw [hx, hy]
  let g : ℝ → ℝ := fun t =>
    P (R * Real.cos t) (R * Real.sin t) * (-(R * Real.sin t)) +
      Q (R * Real.cos t) (R * Real.sin t) * (R * Real.cos t)
  change (∫ t in (0 : ℝ)..2 * Real.pi, g t) = 0
  have hsymm (t : ℝ) : g (2 * Real.pi - t) = -g t := by
    dsimp [g, P, Q]
    rw [Real.sin_two_pi_sub, Real.cos_two_pi_sub]
    ring_nf
    simp [Real.cos_neg, Real.sin_neg] <;> ring
  have hchange :
      (∫ t in (0 : ℝ)..2 * Real.pi, g (2 * Real.pi - t)) =
        ∫ t in (0 : ℝ)..2 * Real.pi, g t := by
    simpa using
      (intervalIntegral.integral_comp_sub_left
        (f := g) (a := (0 : ℝ)) (b := 2 * Real.pi)
        (c := 2 * Real.pi))
  have hneg :
      (∫ t in (0 : ℝ)..2 * Real.pi, g t) =
        -(∫ t in (0 : ℝ)..2 * Real.pi, g t) := by
    calc
      (∫ t in (0 : ℝ)..2 * Real.pi, g t) =
          ∫ t in (0 : ℝ)..2 * Real.pi, g (2 * Real.pi - t) := hchange.symm
      _ = ∫ t in (0 : ℝ)..2 * Real.pi, -g t := by
        apply intervalIntegral.integral_congr
        intro t _
        exact hsymm t
      _ = -(∫ t in (0 : ℝ)..2 * Real.pi, g t) := by simp
  linarith

theorem gap1 (x y : ℝ) :
    curl x y =
      Real.exp (-(x ^ 2 + y ^ 2)) *
        (-2 * x * Real.sin (2 * x * y) +
          2 * y * Real.cos (2 * x * y) -
          (-2 * y * Real.cos (2 * x * y) -
            2 * x * Real.sin (2 * x * y))) := by
  have hexpx :
      HasDerivAt (fun t : ℝ => Real.exp (-(t ^ 2 + y ^ 2)))
        (-2 * x * Real.exp (-(x ^ 2 + y ^ 2))) x := by
    convert
      (((hasDerivAt_id x).pow 2).add (hasDerivAt_const x (y ^ 2))).neg.exp
      using 1 <;> simp <;> ring
  have hsin :
      HasDerivAt (fun t : ℝ => Real.sin (2 * t * y))
        (2 * y * Real.cos (2 * x * y)) x := by
    convert (((hasDerivAt_id x).const_mul 2).mul_const y).sin using 1 <;>
      simp <;> ring
  have hQ :
      HasDerivAt (fun t : ℝ => Q t y)
        (Real.exp (-(x ^ 2 + y ^ 2)) *
          (-2 * x * Real.sin (2 * x * y) +
            2 * y * Real.cos (2 * x * y))) x := by
    unfold Q
    convert hexpx.mul hsin using 1 <;> ring
  have hexpy :
      HasDerivAt (fun t : ℝ => Real.exp (-(x ^ 2 + t ^ 2)))
        (-2 * y * Real.exp (-(x ^ 2 + y ^ 2))) y := by
    convert
      ((hasDerivAt_const y (x ^ 2)).add ((hasDerivAt_id y).pow 2)).neg.exp
      using 1 <;> simp <;> ring
  have hcos :
      HasDerivAt (fun t : ℝ => Real.cos (2 * x * t))
        (-2 * x * Real.sin (2 * x * y)) y := by
    convert ((hasDerivAt_id y).const_mul (2 * x)).cos using 1 <;>
      simp <;> ring
  have hP :
      HasDerivAt (fun t : ℝ => P x t)
        (Real.exp (-(x ^ 2 + y ^ 2)) *
          (-2 * y * Real.cos (2 * x * y) -
            2 * x * Real.sin (2 * x * y))) y := by
    unfold P
    convert hexpy.mul hcos using 1 <;> ring
  unfold curl
  rw [hQ.deriv, hP.deriv]
  ring

theorem gap2 (x y : ℝ) :
    Real.exp (-(x ^ 2 + y ^ 2)) *
        (-2 * x * Real.sin (2 * x * y) +
          2 * y * Real.cos (2 * x * y) -
          (-2 * y * Real.cos (2 * x * y) -
            2 * x * Real.sin (2 * x * y))) =
      4 * y * Real.exp (-(x ^ 2 + y ^ 2)) *
        Real.cos (2 * x * y) := by
  ring

theorem gap3 (x y : ℝ) :
    curl x y =
      4 * y * Real.exp (-(x ^ 2 + y ^ 2)) *
        Real.cos (2 * x * y) := by
  rw [gap1, gap2]

theorem gap4 (R : ℝ) :
    circleIntegral R = curlAreaIntegral R := by
  have hdisk : MeasurableSet (disk R) := by
    unfold disk
    exact
      (isClosed_le
        ((continuous_fst.pow 2).add (continuous_snd.pow 2))
        continuous_const).measurableSet
  let F : ℝ × ℝ → ℝ := fun z =>
    (disk R).indicator
      (fun w =>
        4 * w.2 * Real.exp (-(w.1 ^ 2 + w.2 ^ 2)) *
          Real.cos (2 * w.1 * w.2)) z
  let e : (ℝ × ℝ) ≃ᵐ (ℝ × ℝ) :=
    { toFun := fun z => -z
      invFun := fun z => -z
      left_inv := fun z => neg_neg z
      right_inv := fun z => neg_neg z
      measurable_toFun := continuous_neg.measurable
      measurable_invFun := continuous_neg.measurable }
  have hnegReal :
      MeasurePreserving (fun x : ℝ => -x)
        (volume : Measure ℝ) (volume : Measure ℝ) := by
    exact Measure.measurePreserving_neg (volume : Measure ℝ)
  have hmp : MeasurePreserving e := by
    simpa [e] using (hnegReal.prod hnegReal)
  have hodd (z : ℝ × ℝ) : F (-z) = -F z := by
    rcases z with ⟨x, y⟩
    by_cases h : (x, y) ∈ disk R
    · have hn : (-x, -y) ∈ disk R := by
        simpa [disk] using h
      dsimp [F]
      rw [Set.indicator_of_mem hn, Set.indicator_of_mem h]
      dsimp
      ring_nf
    · have hn : (-x, -y) ∉ disk R := by
        intro hn
        apply h
        simpa [disk] using hn
      simp [F, h, hn]
  have hpres :
      (∫ z : ℝ × ℝ, F (-z)) = ∫ z : ℝ × ℝ, F z := by
    simpa [e] using hmp.integral_comp e.measurableEmbedding F
  have harea : curlAreaIntegral R = 0 := by
    unfold curlAreaIntegral
    simp_rw [gap3]
    rw [← integral_indicator hdisk]
    change (∫ z, F z) = 0
    have hneg : (∫ z, F z) = -(∫ z, F z) := by
      calc
        (∫ z, F z) = ∫ z, F (-z) := hpres.symm
        _ = ∫ z, -F z := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall hodd
        _ = -(∫ z, F z) := integral_neg F
    linarith
  calc
    circleIntegral R = 0 := circleIntegral_vanishes R
    _ = curlAreaIntegral R := harea.symm

theorem gap5 (R : ℝ) :
    curlAreaIntegral R = 0 := by
  calc
    curlAreaIntegral R = circleIntegral R := (gap4 R).symm
    _ = 0 := circleIntegral_vanishes R

theorem gap6 (R : ℝ) :
    circleIntegral R = 0 := by
  exact circleIntegral_vanishes R

end

end ProofGap.Exercise4301
