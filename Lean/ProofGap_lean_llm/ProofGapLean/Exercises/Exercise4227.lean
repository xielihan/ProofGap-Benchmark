import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise4227

noncomputable section

open scoped Interval

def lemniscate (a : ℝ) : Set (ℝ × ℝ) :=
  {p | (p.1 ^ 2 + p.2 ^ 2) ^ 2 = a ^ 2 * (p.1 ^ 2 - p.2 ^ 2)}

def radius (a φ : ℝ) : ℝ :=
  a * Real.sqrt (Real.cos (2 * φ))

def radiusDerivative (a φ : ℝ) : ℝ :=
  -a * Real.sin (2 * φ) / Real.sqrt (Real.cos (2 * φ))

def rawPolarSpeed (a φ : ℝ) : ℝ :=
  Real.sqrt (radius a φ ^ 2 + radiusDerivative a φ ^ 2)

def polarSpeed (a φ : ℝ) : ℝ :=
  a / Real.sqrt (Real.cos (2 * φ))

def endpointPrimitive (a φ : ℝ) : ℝ :=
  -4 * a ^ 2 * Real.cos φ

def weightedLength (a : ℝ) : ℝ :=
  4 *
    ∫ φ in (0 : ℝ)..Real.pi / 4,
      radius a φ * Real.sin φ * polarSpeed a φ

theorem gap1 (a φ : ℝ) (ha : 0 < a)
    (hφ : φ ∈ Set.Icc (-Real.pi / 4) (Real.pi / 4)) :
    radius a φ ^ 2 = a ^ 2 * Real.cos (2 * φ) := by
  have hangle :
      2 * φ ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> linarith [hφ.1, hφ.2]
  have hcos : 0 ≤ Real.cos (2 * φ) :=
    Real.cos_nonneg_of_mem_Icc hangle
  unfold radius
  rw [mul_pow, Real.sq_sqrt hcos]

theorem gap2 (a φ : ℝ) :
    rawPolarSpeed a φ =
      Real.sqrt (radius a φ ^ 2 + radiusDerivative a φ ^ 2) := by
  rfl

theorem gap3 (a φ : ℝ) (ha : 0 < a)
    (hφ : φ ∈ Set.Ioo (-Real.pi / 4) (Real.pi / 4)) :
    rawPolarSpeed a φ = polarSpeed a φ := by
  have hangle :
      2 * φ ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> linarith [hφ.1, hφ.2]
  have hcos : 0 < Real.cos (2 * φ) :=
    Real.cos_pos_of_mem_Ioo hangle
  have hsqrt : 0 < Real.sqrt (Real.cos (2 * φ)) :=
    Real.sqrt_pos.2 hcos
  have hinside :
      (a * Real.sqrt (Real.cos (2 * φ))) ^ 2 +
          (-a * Real.sin (2 * φ) /
            Real.sqrt (Real.cos (2 * φ))) ^ 2 =
        (a / Real.sqrt (Real.cos (2 * φ))) ^ 2 := by
    field_simp [hsqrt.ne']
    calc
      Real.sqrt (Real.cos (2 * φ)) ^ 4 + Real.sin (2 * φ) ^ 2 =
          Real.cos (2 * φ) ^ 2 + Real.sin (2 * φ) ^ 2 := by
        rw [show Real.sqrt (Real.cos (2 * φ)) ^ 4 =
          (Real.sqrt (Real.cos (2 * φ)) ^ 2) ^ 2 by ring]
        rw [Real.sq_sqrt hcos.le]
      _ = 1 := by nlinarith [Real.sin_sq_add_cos_sq (2 * φ)]
  unfold rawPolarSpeed polarSpeed radius radiusDerivative
  rw [hinside, Real.sqrt_sq_eq_abs]
  exact abs_of_pos (div_pos ha hsqrt)

theorem gap4 (a φ : ℝ) (ha : 0 < a)
    (hφ : φ ∈ Set.Ioo (-Real.pi / 4) (Real.pi / 4)) :
    polarSpeed a φ = a / Real.sqrt (Real.cos (2 * φ)) := by
  rfl

theorem gap5 (a : ℝ) (ha : 0 < a) :
    weightedLength a =
      4 *
        ∫ φ in (0 : ℝ)..Real.pi / 4,
          a * Real.sqrt (Real.cos (2 * φ)) * Real.sin φ *
            (a / Real.sqrt (Real.cos (2 * φ))) := by
  rfl

theorem gap6 (a : ℝ) (ha : 0 < a) :
    4 *
        (∫ φ in (0 : ℝ)..Real.pi / 4,
          a * Real.sqrt (Real.cos (2 * φ)) * Real.sin φ *
            (a / Real.sqrt (Real.cos (2 * φ)))) =
      endpointPrimitive a (Real.pi / 4) - endpointPrimitive a 0 := by
  have hae :
      ∀ᵐ φ : ℝ ∂MeasureTheory.volume, φ ≠ Real.pi / 4 := by
    rw [MeasureTheory.ae_iff]
    simpa using (MeasureTheory.measure_singleton (Real.pi / 4))
  have hcancel :
      (∫ φ in (0 : ℝ)..Real.pi / 4,
        a * Real.sqrt (Real.cos (2 * φ)) * Real.sin φ *
          (a / Real.sqrt (Real.cos (2 * φ)))) =
        ∫ φ in (0 : ℝ)..Real.pi / 4, a ^ 2 * Real.sin φ := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hae] with φ hφne
    intro hφ
    rw [Set.uIoc_of_le (by linarith [Real.pi_pos] :
      (0 : ℝ) ≤ Real.pi / 4)] at hφ
    have hφlt : φ < Real.pi / 4 :=
      lt_of_le_of_ne hφ.2 hφne
    have hangle :
        2 * φ ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
      constructor <;> linarith [hφ.1, hφlt, Real.pi_pos]
    have hcos : 0 < Real.cos (2 * φ) :=
      Real.cos_pos_of_mem_Ioo hangle
    have hsqrtne : Real.sqrt (Real.cos (2 * φ)) ≠ 0 :=
      (Real.sqrt_ne_zero').2 hcos
    change
      a * Real.sqrt (Real.cos (2 * φ)) * Real.sin φ *
          (a / Real.sqrt (Real.cos (2 * φ))) =
        a ^ 2 * Real.sin φ
    field_simp [hsqrtne]
  rw [hcancel, intervalIntegral.integral_const_mul,
    integral_sin]
  unfold endpointPrimitive
  ring

theorem gap7 (a : ℝ) :
    endpointPrimitive a (Real.pi / 4) - endpointPrimitive a 0 =
      2 * a ^ 2 * (2 - Real.sqrt 2) := by
  unfold endpointPrimitive
  rw [Real.cos_pi_div_four, Real.cos_zero]
  ring

theorem gap8 (a : ℝ) (ha : 0 < a) :
    weightedLength a = 2 * a ^ 2 * (2 - Real.sqrt 2) := by
  exact (gap5 a ha).trans ((gap6 a ha).trans (gap7 a))

end

end ProofGap.Exercise4227
