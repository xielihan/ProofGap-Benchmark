import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

namespace ProofGap.Exercise4452

noncomputable section

open scoped Interval

abbrev Vec3 := ℝ × ℝ × ℝ

def helix (a b t : ℝ) : Vec3 :=
  (a * Real.cos t, a * Real.sin t, b * t)

def helixDerivative (a b t : ℝ) : Vec3 :=
  (-a * Real.sin t, a * Real.cos t, b)

def dot (p q : Vec3) : ℝ :=
  p.1 * q.1 + p.2.1 * q.2.1 + p.2.2 * q.2.2

def workIntegrand (a b t : ℝ) : ℝ :=
  dot (helix a b t) (helixDerivative a b t)

def work (a b : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..2 * Real.pi, workIntegrand a b t

def lineIntegral (a b : ℝ) : ℝ :=
  work a b

private theorem integral_id_basic4452 (c : ℝ) :
    (∫ t in (0 : ℝ)..c, t) = c ^ 2 / 2 := by
  have hid :
      IntervalIntegrable (fun t : ℝ => t) MeasureTheory.volume 0 c :=
    continuous_id.intervalIntegrable 0 c
  have hsub :
      IntervalIntegrable (fun t : ℝ => c - t) MeasureTheory.volume 0 c :=
    (continuous_const.sub continuous_id).intervalIntegrable 0 c
  have hsymm :
      (∫ t in (0 : ℝ)..c, c - t) =
        ∫ t in (0 : ℝ)..c, t := by
    simpa using
      (intervalIntegral.integral_comp_sub_left
        (f := fun t : ℝ => t) (a := 0) (b := c) c)
  have hadd := intervalIntegral.integral_add hid hsub
  have htwo :
      c ^ 2 =
        (∫ t in (0 : ℝ)..c, t) +
          ∫ t in (0 : ℝ)..c, c - t := by
    calc
      c ^ 2 = ∫ _t in (0 : ℝ)..c, c := by
        rw [intervalIntegral.integral_const]
        simp
        ring
      _ = ∫ t in (0 : ℝ)..c, t + (c - t) := by
        apply intervalIntegral.integral_congr
        intro t ht
        ring
      _ = (∫ t in (0 : ℝ)..c, t) +
          ∫ t in (0 : ℝ)..c, c - t := hadd
  rw [hsymm] at htwo
  linarith

theorem gap1 (a b t : ℝ) :
    helixDerivative a b t =
      (-a * Real.sin t, a * Real.cos t, b) := by
  rfl

theorem gap2 (a b t : ℝ) :
    workIntegrand a b t = b ^ 2 * t := by
  unfold workIntegrand dot helix helixDerivative
  ring

theorem gap3 (a b : ℝ) :
    work a b = ∫ t in (0 : ℝ)..2 * Real.pi, b ^ 2 * t := by
  unfold work
  apply intervalIntegral.integral_congr
  intro t ht
  exact gap2 a b t

theorem gap4 (b : ℝ) :
    (∫ t in (0 : ℝ)..2 * Real.pi, b ^ 2 * t) =
      2 * Real.pi ^ 2 * b ^ 2 := by
  rw [intervalIntegral.integral_const_mul, integral_id_basic4452]
  ring

theorem gap5 (a b : ℝ) :
    work a b = 2 * Real.pi ^ 2 * b ^ 2 := by
  rw [gap3, gap4]

theorem gap6 (a b : ℝ) :
    lineIntegral a b = 2 * Real.pi ^ 2 * b ^ 2 := by
  exact gap5 a b

end

end ProofGap.Exercise4452
