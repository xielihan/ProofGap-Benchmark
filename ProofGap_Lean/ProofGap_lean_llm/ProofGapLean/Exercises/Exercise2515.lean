import ProofGapLean.Prelude.Analysis
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul

open scoped Interval

namespace ProofGap.Exercise2515

noncomputable section

def profile (a z : ℝ) : ℝ := Real.sqrt (a ^ 2 - z ^ 2)
def surfaceDensity (a z : ℝ) : ℝ :=
  2 * Real.pi * profile a z *
    (a / Real.sqrt (a ^ 2 - z ^ 2))
def surfaceCentroidZ (a : ℝ) : ℝ :=
  (∫ z in 0..a, z * surfaceDensity a z) /
    (∫ z in 0..a, surfaceDensity a z)

private theorem sqrt_mul_div_ae (a : ℝ) (ha : 0 < a) :
    ∀ᵐ z ∂MeasureTheory.volume.restrict (Set.Ioc 0 a),
      Real.sqrt (a ^ 2 - z ^ 2) *
          (a / Real.sqrt (a ^ 2 - z ^ 2)) = a := by
  rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioc]
  have hne : ∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ), z ≠ a := by
    change MeasureTheory.volume {z : ℝ | z ≠ a}ᶜ = 0
    simpa using
      (MeasureTheory.measure_singleton
        (μ := (MeasureTheory.volume : MeasureTheory.Measure ℝ)) a)
  filter_upwards [hne] with z hza
  intro hz
  have hza_lt : z < a := lt_of_le_of_ne hz.2 hza
  have hprod : 0 < (a - z) * (a + z) := by
    exact mul_pos (sub_pos.mpr hza_lt) (by linarith [ha, hz.1])
  have hrad : 0 < a ^ 2 - z ^ 2 := by
    nlinarith [hprod]
  have hsqrt : Real.sqrt (a ^ 2 - z ^ 2) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hrad)
  field_simp [hsqrt]

theorem gap1 (ξ : ℝ) (hξ : ξ = 0) : ξ = 0 := by
  exact hξ

theorem gap2 (η : ℝ) (hη : η = 0) : η = 0 := by
  exact hη

theorem gap3 (a ζ : ℝ) (hζ : ζ = surfaceCentroidZ a) :
    ζ = (∫ z in 0..a, z * surfaceDensity a z) /
      (∫ z in 0..a, surfaceDensity a z) := by
  simpa [surfaceCentroidZ] using hζ

theorem gap4 (a ζ : ℝ) (ha : 0 < a)
    (hζ : ζ = surfaceCentroidZ a) :
    ζ =
      (∫ z in 0..a,
        2 * Real.pi * z * Real.sqrt (a ^ 2 - z ^ 2) *
          (a / Real.sqrt (a ^ 2 - z ^ 2))) /
      (∫ z in 0..a,
        2 * Real.pi * Real.sqrt (a ^ 2 - z ^ 2) *
          (a / Real.sqrt (a ^ 2 - z ^ 2))) := by
  simpa [surfaceCentroidZ, surfaceDensity, profile, mul_assoc, mul_left_comm,
    mul_comm] using hζ

theorem gap5 (a ζ : ℝ) (ha : 0 < a)
    (hζ : ζ = surfaceCentroidZ a) :
    ζ = (2 * Real.pi * a * ∫ z in 0..a, z) /
      (2 * Real.pi * a * ∫ _z in 0..a, (1 : ℝ)) := by
  have hcancel := sqrt_mul_div_ae a ha
  have hnum :
      (∫ z in 0..a,
        2 * Real.pi * z * Real.sqrt (a ^ 2 - z ^ 2) *
          (a / Real.sqrt (a ^ 2 - z ^ 2))) =
        2 * Real.pi * a * ∫ z in 0..a, z := by
    calc
      (∫ z in 0..a,
        2 * Real.pi * z * Real.sqrt (a ^ 2 - z ^ 2) *
          (a / Real.sqrt (a ^ 2 - z ^ 2))) =
          ∫ z in 0..a, (2 * Real.pi * a) * z := by
            simp only [intervalIntegral.integral_of_le ha.le]
            exact MeasureTheory.integral_congr_ae
              (hcancel.mono fun z hz => by
                calc
                  2 * Real.pi * z * Real.sqrt (a ^ 2 - z ^ 2) *
                        (a / Real.sqrt (a ^ 2 - z ^ 2)) =
                      2 * Real.pi * z *
                        (Real.sqrt (a ^ 2 - z ^ 2) *
                          (a / Real.sqrt (a ^ 2 - z ^ 2))) := by ring
                  _ = 2 * Real.pi * z * a := by rw [hz]
                  _ = (2 * Real.pi * a) * z := by ring)
      _ = 2 * Real.pi * a * ∫ z in 0..a, z := by
        rw [intervalIntegral.integral_const_mul]
  have hden :
      (∫ z in 0..a,
        2 * Real.pi * Real.sqrt (a ^ 2 - z ^ 2) *
          (a / Real.sqrt (a ^ 2 - z ^ 2))) =
        2 * Real.pi * a * ∫ _z in 0..a, (1 : ℝ) := by
    calc
      (∫ z in 0..a,
        2 * Real.pi * Real.sqrt (a ^ 2 - z ^ 2) *
          (a / Real.sqrt (a ^ 2 - z ^ 2))) =
          ∫ _z in 0..a, (2 * Real.pi * a) * (1 : ℝ) := by
            simp only [intervalIntegral.integral_of_le ha.le]
            exact MeasureTheory.integral_congr_ae
              (hcancel.mono fun z hz => by
                calc
                  2 * Real.pi * Real.sqrt (a ^ 2 - z ^ 2) *
                        (a / Real.sqrt (a ^ 2 - z ^ 2)) =
                      2 * Real.pi *
                        (Real.sqrt (a ^ 2 - z ^ 2) *
                          (a / Real.sqrt (a ^ 2 - z ^ 2))) := by ring
                  _ = 2 * Real.pi * a := by rw [hz]
                  _ = (2 * Real.pi * a) * (1 : ℝ) := by ring)
      _ = 2 * Real.pi * a * ∫ _z in 0..a, (1 : ℝ) := by
        rw [intervalIntegral.integral_const_mul]
  calc
    ζ =
        (∫ z in 0..a,
          2 * Real.pi * z * Real.sqrt (a ^ 2 - z ^ 2) *
            (a / Real.sqrt (a ^ 2 - z ^ 2))) /
        (∫ z in 0..a,
          2 * Real.pi * Real.sqrt (a ^ 2 - z ^ 2) *
            (a / Real.sqrt (a ^ 2 - z ^ 2))) := gap4 a ζ ha hζ
    _ = (2 * Real.pi * a * ∫ z in 0..a, z) /
        (2 * Real.pi * a * ∫ _z in 0..a, (1 : ℝ)) := by
          rw [hnum, hden]

theorem gap6 (a : ℝ) (ha : 0 < a) :
    (2 * Real.pi * a * ∫ z in 0..a, z) /
        (2 * Real.pi * a * ∫ _z in 0..a, (1 : ℝ)) =
      (2 * Real.pi * a * (1 / 2) * a ^ 2) /
        (2 * Real.pi * a ^ 2) := by
  have hderiv : ∀ x ∈ Set.uIcc (0 : ℝ) a,
      HasDerivAt (fun t : ℝ => t ^ 2 / 2) x x := by
    intro x _hx
    convert ((hasDerivAt_id x).mul (hasDerivAt_id x)).div_const 2 using 1 <;>
      simp [pow_two] <;> ring
  have hi_raw :
      (∫ z in 0..a, z) =
        (fun x : ℝ => x ^ 2 / 2) a -
          (fun x : ℝ => x ^ 2 / 2) 0 := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    exact continuous_id.intervalIntegrable
      (μ := MeasureTheory.volume) 0 a
  have hi : (∫ z in 0..a, z) = (1 / 2 : ℝ) * a ^ 2 := by
    calc
      (∫ z in 0..a, z) =
          (fun x : ℝ => x ^ 2 / 2) a -
            (fun x : ℝ => x ^ 2 / 2) 0 := hi_raw
      _ = (1 / 2 : ℝ) * a ^ 2 := by ring
  have hc : (∫ _z in 0..a, (1 : ℝ)) = a := by
    simp
  rw [hi, hc]
  congr 1 <;> ring

theorem gap7 (a : ℝ) (ha : 0 < a) :
    (2 * Real.pi * a * (1 / 2) * a ^ 2) /
        (2 * Real.pi * a ^ 2) =
      a / 2 := by
  have ha0 : a ≠ 0 := ne_of_gt ha
  have hpi0 : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  field_simp [ha0, hpi0] <;> ring

theorem gap8 (a ζ : ℝ) (ha : 0 < a)
    (hζ : ζ = surfaceCentroidZ a) :
    ζ = a / 2 := by
  calc
    ζ = (2 * Real.pi * a * ∫ z in 0..a, z) /
        (2 * Real.pi * a * ∫ _z in 0..a, (1 : ℝ)) := gap5 a ζ ha hζ
    _ = (2 * Real.pi * a * (1 / 2) * a ^ 2) /
        (2 * Real.pi * a ^ 2) := gap6 a ha
    _ = a / 2 := gap7 a ha

theorem gap9 (a ξ η ζ : ℝ)
    (hξ : ξ = 0) (hη : η = 0) (hζ : ζ = a / 2) :
    (ξ, η, ζ) = (0, 0, a / 2) := by
  simp [hξ, hη, hζ]

end

end ProofGap.Exercise2515
