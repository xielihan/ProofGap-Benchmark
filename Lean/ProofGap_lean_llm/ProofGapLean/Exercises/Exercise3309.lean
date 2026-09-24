import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise3309

noncomputable section

def heatKernel (a b x t : ℝ) : ℝ :=
  1 / (2 * a * Real.sqrt (Real.pi * t)) *
    Real.exp (-((x - b) ^ 2) / (4 * a ^ 2 * t))

def partialX (f : ℝ → ℝ → ℝ) (x t : ℝ) : ℝ :=
  deriv (fun s => f s t) x

def partialXX (f : ℝ → ℝ → ℝ) (x t : ℝ) : ℝ :=
  deriv (fun s => partialX f s t) x

def partialT (f : ℝ → ℝ → ℝ) (x t : ℝ) : ℝ :=
  deriv (fun s => f x s) t

theorem gap1 (a b : ℝ) (ha : a ≠ 0) :
    ∀ x t, 0 < t →
      partialT (heatKernel a b) x t =
        1 / (8 * a ^ 3 * t ^ 2 * Real.sqrt (Real.pi * t)) *
          Real.exp (-((x - b) ^ 2) / (4 * a ^ 2 * t)) *
          ((x - b) ^ 2 - 2 * a ^ 2 * t) := by
  intro x t ht
  have ht0 : t ≠ 0 := ne_of_gt ht
  have hpt : 0 < Real.pi * t := mul_pos Real.pi_pos ht
  have hsqrt0 : Real.sqrt (Real.pi * t) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hpt)
  have hsqrt_sq : (Real.sqrt (Real.pi * t)) ^ 2 = Real.pi * t :=
    Real.sq_sqrt (le_of_lt hpt)
  have hsqrt_sq_comm : (Real.sqrt (t * Real.pi)) ^ 2 = t * Real.pi := by
    calc
      (Real.sqrt (t * Real.pi)) ^ 2 =
          (Real.sqrt (Real.pi * t)) ^ 2 := by
            rw [mul_comm t Real.pi]
      _ = Real.pi * t := hsqrt_sq
      _ = t * Real.pi := mul_comm Real.pi t
  have hsqrtDeriv :=
    (Real.hasDerivAt_sqrt (ne_of_gt hpt)).comp t
      ((hasDerivAt_const t Real.pi).mul (hasDerivAt_id t))
  have hden0 : 2 * a * Real.sqrt (Real.pi * t) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) ha) hsqrt0
  have hdenDeriv :=
    (hasDerivAt_const t (2 * a)).mul hsqrtDeriv
  have hfracRaw :=
    (hasDerivAt_const t (1 : ℝ)).div hdenDeriv hden0
  simp [Function.comp_apply] at hfracRaw
  have hfracDeriv :
      HasDerivAt
        (fun s : ℝ => 1 / (2 * a * Real.sqrt (Real.pi * s)))
        (-1 / (4 * a * t * Real.sqrt (Real.pi * t))) t := by
    convert hfracRaw using 1
    field_simp [ha, ht0, hsqrt0] <;>
      nlinarith [hsqrt_sq, hsqrt_sq_comm]
  have htimeDen0 : 4 * a ^ 2 * t ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 2 ha)) ht0
  have htimeDenDeriv :=
    (hasDerivAt_const t (4 * a ^ 2)).mul (hasDerivAt_id t)
  have hquotRaw :=
    (hasDerivAt_const t (-((x - b) ^ 2))).div
      htimeDenDeriv htimeDen0
  simp [Function.comp_apply] at hquotRaw
  have hquotDeriv :
      HasDerivAt
        (fun s : ℝ => -((x - b) ^ 2) / (4 * a ^ 2 * s))
        ((x - b) ^ 2 / (4 * a ^ 2 * t ^ 2)) t := by
    convert hquotRaw using 1
    field_simp [ha, ht0] <;> ring
  have hExpDeriv := hquotDeriv.exp
  have hkernelDeriv := hfracDeriv.mul hExpDeriv
  unfold partialT
  change
    deriv
        (fun s : ℝ =>
          1 / (2 * a * Real.sqrt (Real.pi * s)) *
            Real.exp (-((x - b) ^ 2) / (4 * a ^ 2 * s))) t = _
  calc
    deriv
        (fun s : ℝ =>
          1 / (2 * a * Real.sqrt (Real.pi * s)) *
            Real.exp (-((x - b) ^ 2) / (4 * a ^ 2 * s))) t =
        -1 / (4 * a * t * Real.sqrt (Real.pi * t)) *
            Real.exp (-((x - b) ^ 2) / (4 * a ^ 2 * t)) +
          1 / (2 * a * Real.sqrt (Real.pi * t)) *
            (Real.exp (-((x - b) ^ 2) / (4 * a ^ 2 * t)) *
              ((x - b) ^ 2 / (4 * a ^ 2 * t ^ 2))) := by
      simpa only [Pi.mul_apply] using hkernelDeriv.deriv
    _ = _ := by
      field_simp [ha, ht0, hsqrt0] <;> ring

theorem gap2 (a b : ℝ) (ha : a ≠ 0) :
    ∀ x t, 0 < t →
      partialX (heatKernel a b) x t =
        -(x - b) / (4 * a ^ 3 * t * Real.sqrt (Real.pi * t)) *
          Real.exp (-((x - b) ^ 2) / (4 * a ^ 2 * t)) := by
  intro x t ht
  have ht0 : t ≠ 0 := ne_of_gt ht
  have hpt : 0 < Real.pi * t := mul_pos Real.pi_pos ht
  have hsqrt0 : Real.sqrt (Real.pi * t) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hpt)
  have hspaceDen0 : 4 * a ^ 2 * t ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 2 ha)) ht0
  have hsubDeriv := (hasDerivAt_id x).sub_const b
  have hnumDeriv := (hsubDeriv.pow 2).neg
  have hdenDeriv := hasDerivAt_const x (4 * a ^ 2 * t)
  have hquotRaw := hnumDeriv.div hdenDeriv hspaceDen0
  simp [Function.comp_apply] at hquotRaw
  have hquotDeriv :
      HasDerivAt
        (fun s : ℝ => -((s - b) ^ 2) / (4 * a ^ 2 * t))
        (-(x - b) / (2 * a ^ 2 * t)) x := by
    convert hquotRaw using 1
    field_simp [ha, ht0] <;> ring
  have hExpDeriv := hquotDeriv.exp
  have hprefDeriv :=
    hasDerivAt_const x (1 / (2 * a * Real.sqrt (Real.pi * t)))
  have hkernelDeriv := hprefDeriv.mul hExpDeriv
  unfold partialX
  change
    deriv
        (fun s : ℝ =>
          1 / (2 * a * Real.sqrt (Real.pi * t)) *
            Real.exp (-((s - b) ^ 2) / (4 * a ^ 2 * t))) x = _
  calc
    deriv
        (fun s : ℝ =>
          1 / (2 * a * Real.sqrt (Real.pi * t)) *
            Real.exp (-((s - b) ^ 2) / (4 * a ^ 2 * t))) x =
        0 * Real.exp (-((x - b) ^ 2) / (4 * a ^ 2 * t)) +
          1 / (2 * a * Real.sqrt (Real.pi * t)) *
            (Real.exp (-((x - b) ^ 2) / (4 * a ^ 2 * t)) *
              (-(x - b) / (2 * a ^ 2 * t))) := by
      simpa only [Pi.mul_apply] using hkernelDeriv.deriv
    _ = _ := by
      field_simp [ha, ht0, hsqrt0] <;> ring

theorem gap3 (a b : ℝ) (ha : a ≠ 0) :
    ∀ x t, 0 < t →
      partialXX (heatKernel a b) x t =
        1 / (8 * a ^ 5 * t ^ 2 * Real.sqrt (Real.pi * t)) *
          Real.exp (-((x - b) ^ 2) / (4 * a ^ 2 * t)) *
          ((x - b) ^ 2 - 2 * a ^ 2 * t) := by
  intro x t ht
  have ht0 : t ≠ 0 := ne_of_gt ht
  have hpt : 0 < Real.pi * t := mul_pos Real.pi_pos ht
  have hsqrt0 : Real.sqrt (Real.pi * t) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hpt)
  unfold partialXX
  have hfun :
      (fun s : ℝ => partialX (heatKernel a b) s t) =
        (fun s : ℝ =>
          -(s - b) / (4 * a ^ 3 * t * Real.sqrt (Real.pi * t)) *
            Real.exp (-((s - b) ^ 2) / (4 * a ^ 2 * t))) := by
    funext s
    exact gap2 a b ha s t ht
  rw [hfun]
  have hprefDen0 :
      4 * a ^ 3 * t * Real.sqrt (Real.pi * t) ≠ 0 := by
    exact
      mul_ne_zero
        (mul_ne_zero
          (mul_ne_zero (by norm_num) (pow_ne_zero 3 ha)) ht0)
        hsqrt0
  have hprefNumDeriv := ((hasDerivAt_id x).sub_const b).neg
  have hprefDenDeriv :=
    hasDerivAt_const x
      (4 * a ^ 3 * t * Real.sqrt (Real.pi * t))
  have hprefRaw := hprefNumDeriv.div hprefDenDeriv hprefDen0
  simp [Function.comp_apply] at hprefRaw
  have hprefDeriv :
      HasDerivAt
        (fun s : ℝ =>
          -(s - b) / (4 * a ^ 3 * t * Real.sqrt (Real.pi * t)))
        (-1 / (4 * a ^ 3 * t * Real.sqrt (Real.pi * t))) x := by
    convert hprefRaw using 1
    field_simp [ha, ht0, hsqrt0] <;> ring
  have hspaceDen0 : 4 * a ^ 2 * t ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 2 ha)) ht0
  have hquotNumDeriv := (((hasDerivAt_id x).sub_const b).pow 2).neg
  have hquotDenDeriv := hasDerivAt_const x (4 * a ^ 2 * t)
  have hquotRaw := hquotNumDeriv.div hquotDenDeriv hspaceDen0
  simp [Function.comp_apply] at hquotRaw
  have hquotDeriv :
      HasDerivAt
        (fun s : ℝ => -((s - b) ^ 2) / (4 * a ^ 2 * t))
        (-(x - b) / (2 * a ^ 2 * t)) x := by
    convert hquotRaw using 1
    field_simp [ha, ht0] <;> ring
  have hExpDeriv := hquotDeriv.exp
  have hsecondDeriv := hprefDeriv.mul hExpDeriv
  calc
    deriv
        (fun s : ℝ =>
          -(s - b) / (4 * a ^ 3 * t * Real.sqrt (Real.pi * t)) *
            Real.exp (-((s - b) ^ 2) / (4 * a ^ 2 * t))) x =
        -1 / (4 * a ^ 3 * t * Real.sqrt (Real.pi * t)) *
            Real.exp (-((x - b) ^ 2) / (4 * a ^ 2 * t)) +
          (-(x - b) / (4 * a ^ 3 * t * Real.sqrt (Real.pi * t))) *
            (Real.exp (-((x - b) ^ 2) / (4 * a ^ 2 * t)) *
              (-(x - b) / (2 * a ^ 2 * t))) := by
      simpa only [Pi.mul_apply] using hsecondDeriv.deriv
    _ = _ := by
      field_simp [ha, ht0, hsqrt0] <;> ring

theorem gap4 (a b : ℝ) (ha : a ≠ 0) :
    ∀ x t, 0 < t →
      partialT (heatKernel a b) x t =
        a ^ 2 * partialXX (heatKernel a b) x t := by
  intro x t ht
  have ht0 : t ≠ 0 := ne_of_gt ht
  have hpt : 0 < Real.pi * t := mul_pos Real.pi_pos ht
  have hsqrt0 : Real.sqrt (Real.pi * t) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hpt)
  rw [gap1 a b ha x t ht, gap3 a b ha x t ht]
  field_simp [ha, ht0, hsqrt0]

theorem gap5 (a b : ℝ) (ha : a ≠ 0) :
    ∀ x t, 0 < t →
      partialT (heatKernel a b) x t =
        a ^ 2 * partialXX (heatKernel a b) x t := by
  exact gap4 a b ha

end

end ProofGap.Exercise3309
