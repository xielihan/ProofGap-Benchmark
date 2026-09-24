import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise4346

noncomputable section

open scoped Interval

def paraboloidHeight (x y : ℝ) : ℝ := x ^ 2 + y ^ 2

def paraboloidSurface : Set (ℝ × (ℝ × ℝ)) :=
  {p | p.2.2 = p.1 ^ 2 + p.2.1 ^ 2 ∧ p.2.2 ≤ 1}

def graphAreaFactor (x y : ℝ) : ℝ :=
  Real.sqrt
    (1 + (deriv (fun s => paraboloidHeight s y) x) ^ 2 +
      (deriv (fun s => paraboloidHeight x s) y) ^ 2)

def polarParam (r φ : ℝ) : ℝ × (ℝ × ℝ) :=
  (r * Real.cos φ, (r * Real.sin φ, r ^ 2))

def paraboloidMoment : ℝ :=
  4 * ∫ φ in (0 : ℝ)..Real.pi / 2,
    ∫ r in (0 : ℝ)..1,
      r ^ 4 * Real.cos φ * Real.sin φ *
        Real.sqrt (1 + 4 * r ^ 2) * r

def radialMoment : ℝ :=
  2 * ∫ r in (0 : ℝ)..1,
    r ^ 5 * Real.sqrt (1 + 4 * r ^ 2)

def polynomialPrimitive (y : ℝ) : ℝ :=
  (1 / 32 : ℝ) *
    (y ^ 7 / 7 - 2 * y ^ 5 / 5 + y ^ 3 / 3)

private theorem integralEvaluations :
    radialMoment =
        polynomialPrimitive (Real.sqrt 5) - polynomialPrimitive 1 ∧
      (∫ t in (0 : ℝ)..1,
          t ^ 2 * Real.sqrt (1 + 4 * t)) =
        polynomialPrimitive (Real.sqrt 5) - polynomialPrimitive 1 ∧
      (∫ y in (1 : ℝ)..Real.sqrt 5,
          (1 / 32 : ℝ) * (y ^ 2 - 1) ^ 2 * y ^ 2) =
        polynomialPrimitive (Real.sqrt 5) - polynomialPrimitive 1 := by
  have hpoly (y : ℝ) :
      HasDerivAt polynomialPrimitive
        ((1 / 32 : ℝ) * (y ^ 2 - 1) ^ 2 * y ^ 2) y := by
    unfold polynomialPrimitive
    convert
      (((((hasDerivAt_id y).pow 7).div_const 7).sub
          ((((hasDerivAt_id y).pow 5).const_mul 2).div_const 5)).add
        (((hasDerivAt_id y).pow 3).div_const 3)).const_mul (1 / 32) using 1 <;>
      simp only [id_eq] <;> ring_nf
  have hycont : Continuous (fun y : ℝ =>
      (1 / 32 : ℝ) * (y ^ 2 - 1) ^ 2 * y ^ 2) := by
    exact
      (continuous_const.mul
        (((continuous_id.pow 2).sub continuous_const).pow 2)).mul
          (continuous_id.pow 2)
  have hyEval :
      (∫ y in (1 : ℝ)..Real.sqrt 5,
          (1 / 32 : ℝ) * (y ^ 2 - 1) ^ 2 * y ^ 2) =
        polynomialPrimitive (Real.sqrt 5) - polynomialPrimitive 1 := by
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun y hy => hpoly y)
      (hycont.intervalIntegrable 1 (Real.sqrt 5))
  have htderiv (t : ℝ) (ht : t ∈ Set.uIcc (0 : ℝ) 1) :
      HasDerivAt
        (fun s : ℝ => polynomialPrimitive (Real.sqrt (1 + 4 * s)))
        (t ^ 2 * Real.sqrt (1 + 4 * t)) t := by
    have ht0 : 0 ≤ t := by
      rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
      exact ht.1
    have harg : 0 < 1 + 4 * t := by
      nlinarith
    have hsne : Real.sqrt (1 + 4 * t) ≠ 0 :=
      ne_of_gt (Real.sqrt_pos.2 harg)
    have hlin : HasDerivAt (fun s : ℝ => 1 + 4 * s) 4 t := by
      convert (hasDerivAt_const (x := t) 1).add
        ((hasDerivAt_id t).const_mul 4) using 1 <;>
        (try simp only [id_eq]) <;> ring_nf
    have hsqrt_sq :
        Real.sqrt (1 + t * 4) ^ 2 = 1 + t * 4 := by
      exact Real.sq_sqrt (by nlinarith)
    have hsqrt_four :
        Real.sqrt (1 + t * 4) ^ 4 = (1 + t * 4) ^ 2 := by
      calc
        Real.sqrt (1 + t * 4) ^ 4 =
            (Real.sqrt (1 + t * 4) ^ 2) ^ 2 := by ring
        _ = (1 + t * 4) ^ 2 := by rw [hsqrt_sq]
    convert
      (hpoly (Real.sqrt (1 + 4 * t))).comp t
        ((Real.hasDerivAt_sqrt (ne_of_gt harg)).comp t hlin) using 1
    field_simp [hsne]
    rw [hsqrt_sq]
    ring
  have htcont : Continuous (fun t : ℝ =>
      t ^ 2 * Real.sqrt (1 + 4 * t)) := by
    exact
      (continuous_id.pow 2).mul
        (Real.continuous_sqrt.comp
          (continuous_const.add (continuous_const.mul continuous_id)))
  have htEval :
      (∫ t in (0 : ℝ)..1,
          t ^ 2 * Real.sqrt (1 + 4 * t)) =
        polynomialPrimitive (Real.sqrt 5) - polynomialPrimitive 1 := by
    convert
      (intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun t ht => htderiv t ht)
        (htcont.intervalIntegrable 0 1)) using 1 <;> norm_num
  have hrderiv (r : ℝ) (hr : r ∈ Set.uIcc (0 : ℝ) 1) :
      HasDerivAt
        (fun s : ℝ => polynomialPrimitive (Real.sqrt (1 + 4 * s ^ 2)))
        (2 * (r ^ 5 * Real.sqrt (1 + 4 * r ^ 2))) r := by
    have harg : 0 < 1 + 4 * r ^ 2 := by
      nlinarith [sq_nonneg r]
    have hsne : Real.sqrt (1 + 4 * r ^ 2) ≠ 0 :=
      ne_of_gt (Real.sqrt_pos.2 harg)
    have hquad : HasDerivAt (fun s : ℝ => 1 + 4 * s ^ 2) (8 * r) r := by
      convert (hasDerivAt_const (x := r) 1).add
        (((hasDerivAt_id r).pow 2).const_mul 4) using 1 <;>
        simp only [id_eq] <;> ring_nf
    have hsqrt_sq :
        Real.sqrt (1 + r ^ 2 * 4) ^ 2 = 1 + r ^ 2 * 4 := by
      exact Real.sq_sqrt (by nlinarith [sq_nonneg r])
    have hsqrt_four :
        Real.sqrt (1 + r ^ 2 * 4) ^ 4 = (1 + r ^ 2 * 4) ^ 2 := by
      calc
        Real.sqrt (1 + r ^ 2 * 4) ^ 4 =
            (Real.sqrt (1 + r ^ 2 * 4) ^ 2) ^ 2 := by ring
        _ = (1 + r ^ 2 * 4) ^ 2 := by rw [hsqrt_sq]
    convert
      (hpoly (Real.sqrt (1 + 4 * r ^ 2))).comp r
        ((Real.hasDerivAt_sqrt (ne_of_gt harg)).comp r hquad) using 1
    field_simp [hsne]
    rw [hsqrt_sq]
    ring
  have hrcont : Continuous (fun r : ℝ =>
      2 * (r ^ 5 * Real.sqrt (1 + 4 * r ^ 2))) := by
    exact
      continuous_const.mul
        ((continuous_id.pow 5).mul
          (Real.continuous_sqrt.comp
            (continuous_const.add
              (continuous_const.mul (continuous_id.pow 2)))))
  have hrIntEval :
      (∫ r in (0 : ℝ)..1,
          2 * (r ^ 5 * Real.sqrt (1 + 4 * r ^ 2))) =
        polynomialPrimitive (Real.sqrt 5) - polynomialPrimitive 1 := by
    convert
      (intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun r hr => hrderiv r hr)
        (hrcont.intervalIntegrable 0 1)) using 1 <;> norm_num
  have hrEval :
      radialMoment =
        polynomialPrimitive (Real.sqrt 5) - polynomialPrimitive 1 := by
    calc
      radialMoment =
          ∫ r in (0 : ℝ)..1,
            2 * (r ^ 5 * Real.sqrt (1 + 4 * r ^ 2)) := by
              unfold radialMoment
              rw [intervalIntegral.integral_const_mul]
      _ = polynomialPrimitive (Real.sqrt 5) - polynomialPrimitive 1 :=
        hrIntEval
  exact ⟨hrEval, htEval, hyEval⟩

theorem gap1 (x y : ℝ) :
    graphAreaFactor x y =
      Real.sqrt (1 + 4 * (x ^ 2 + y ^ 2)) := by
  unfold graphAreaFactor
  have hx :
      HasDerivAt (fun s : ℝ => paraboloidHeight s y) (2 * x) x := by
    unfold paraboloidHeight
    convert ((hasDerivAt_id x).pow 2).add
      (hasDerivAt_const (x := x) (y ^ 2)) using 1 <;>
      simp only [id_eq] <;> ring_nf
  have hy :
      HasDerivAt (fun s : ℝ => paraboloidHeight x s) (2 * y) y := by
    unfold paraboloidHeight
    convert (hasDerivAt_const (x := y) (x ^ 2)).add
      ((hasDerivAt_id y).pow 2) using 1 <;>
      simp only [id_eq] <;> ring_nf
  rw [hx.deriv, hy.deriv]
  congr 1
  ring

theorem gap2 :
    paraboloidMoment =
      4 * ∫ φ in (0 : ℝ)..Real.pi / 2,
        ∫ r in (0 : ℝ)..1,
          r ^ 4 * Real.cos φ * Real.sin φ *
            Real.sqrt (1 + 4 * r ^ 2) * r := by
  rfl

theorem gap3 :
    paraboloidMoment = radialMoment := by
  have hinner (φ : ℝ) :
      (∫ r in (0 : ℝ)..1,
          r ^ 4 * Real.cos φ * Real.sin φ *
            Real.sqrt (1 + 4 * r ^ 2) * r) =
        Real.cos φ * Real.sin φ *
          (∫ r in (0 : ℝ)..1,
            r ^ 5 * Real.sqrt (1 + 4 * r ^ 2)) := by
    calc
      (∫ r in (0 : ℝ)..1,
          r ^ 4 * Real.cos φ * Real.sin φ *
            Real.sqrt (1 + 4 * r ^ 2) * r) =
          ∫ r in (0 : ℝ)..1,
            (Real.cos φ * Real.sin φ) *
              (r ^ 5 * Real.sqrt (1 + 4 * r ^ 2)) := by
            apply intervalIntegral.integral_congr
            intro r hr
            ring
      _ = Real.cos φ * Real.sin φ *
          (∫ r in (0 : ℝ)..1,
            r ^ 5 * Real.sqrt (1 + 4 * r ^ 2)) := by
            rw [intervalIntegral.integral_const_mul]
  have hang :
      (∫ φ in (0 : ℝ)..Real.pi / 2,
        Real.cos φ * Real.sin φ) = (1 / 2 : ℝ) := by
    calc
      (∫ φ in (0 : ℝ)..Real.pi / 2,
        Real.cos φ * Real.sin φ) =
          Real.sin (Real.pi / 2) ^ 2 / 2 -
            Real.sin 0 ^ 2 / 2 := by
              exact intervalIntegral.integral_eq_sub_of_hasDerivAt
                (f := fun φ : ℝ => Real.sin φ ^ 2 / 2)
                (f' := fun φ : ℝ => Real.cos φ * Real.sin φ)
                (fun φ hφ => by
                  convert ((Real.hasDerivAt_sin φ).pow 2).div_const 2 using 1 <;>
                    ring)
                ((Real.continuous_cos.mul Real.continuous_sin).intervalIntegrable
                  0 (Real.pi / 2))
      _ = (1 / 2 : ℝ) := by
        rw [Real.sin_pi_div_two, Real.sin_zero]
        norm_num
  calc
    paraboloidMoment =
        4 * ∫ φ in (0 : ℝ)..Real.pi / 2,
          (Real.cos φ * Real.sin φ) *
            (∫ r in (0 : ℝ)..1,
              r ^ 5 * Real.sqrt (1 + 4 * r ^ 2)) := by
          unfold paraboloidMoment
          apply congrArg (fun z : ℝ => 4 * z)
          apply intervalIntegral.integral_congr
          intro φ hφ
          exact hinner φ
    _ = 4 * ((∫ φ in (0 : ℝ)..Real.pi / 2,
          Real.cos φ * Real.sin φ) *
            (∫ r in (0 : ℝ)..1,
              r ^ 5 * Real.sqrt (1 + 4 * r ^ 2))) := by
          rw [intervalIntegral.integral_mul_const]
    _ = radialMoment := by
          rw [hang]
          unfold radialMoment
          ring

theorem gap4 :
    radialMoment =
      ∫ t in (0 : ℝ)..1,
        t ^ 2 * Real.sqrt (1 + 4 * t) := by
  calc
    radialMoment =
        polynomialPrimitive (Real.sqrt 5) - polynomialPrimitive 1 :=
      integralEvaluations.1
    _ = ∫ t in (0 : ℝ)..1,
        t ^ 2 * Real.sqrt (1 + 4 * t) :=
      integralEvaluations.2.1.symm

theorem gap5 :
    paraboloidMoment =
      ∫ t in (0 : ℝ)..1,
        t ^ 2 * Real.sqrt (1 + 4 * t) := by
  exact gap3.trans gap4

theorem gap6 :
    paraboloidMoment =
      ∫ y in (1 : ℝ)..Real.sqrt 5,
        (1 / 32 : ℝ) * (y ^ 2 - 1) ^ 2 * y ^ 2 := by
  calc
    paraboloidMoment =
        ∫ t in (0 : ℝ)..1,
          t ^ 2 * Real.sqrt (1 + 4 * t) := gap5
    _ = polynomialPrimitive (Real.sqrt 5) - polynomialPrimitive 1 :=
      integralEvaluations.2.1
    _ = ∫ y in (1 : ℝ)..Real.sqrt 5,
        (1 / 32 : ℝ) * (y ^ 2 - 1) ^ 2 * y ^ 2 :=
      integralEvaluations.2.2.symm

theorem gap7 :
    (∫ y in (1 : ℝ)..Real.sqrt 5,
        (1 / 32 : ℝ) * (y ^ 2 - 1) ^ 2 * y ^ 2) =
      polynomialPrimitive (Real.sqrt 5) - polynomialPrimitive 1 := by
  exact integralEvaluations.2.2

theorem gap8 :
    polynomialPrimitive (Real.sqrt 5) - polynomialPrimitive 1 =
      (125 * Real.sqrt 5 - 1) / 420 := by
  have hs2 : (Real.sqrt 5) ^ 2 = (5 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  have hs3 : (Real.sqrt 5) ^ 3 = 5 * Real.sqrt 5 := by
    calc
      (Real.sqrt 5) ^ 3 = (Real.sqrt 5) ^ 2 * Real.sqrt 5 := by ring
      _ = 5 * Real.sqrt 5 := by rw [hs2]
  have hs5 : (Real.sqrt 5) ^ 5 = 25 * Real.sqrt 5 := by
    calc
      (Real.sqrt 5) ^ 5 = ((Real.sqrt 5) ^ 2) ^ 2 * Real.sqrt 5 := by ring
      _ = 25 * Real.sqrt 5 := by rw [hs2]; norm_num
  have hs7 : (Real.sqrt 5) ^ 7 = 125 * Real.sqrt 5 := by
    calc
      (Real.sqrt 5) ^ 7 = ((Real.sqrt 5) ^ 2) ^ 3 * Real.sqrt 5 := by ring
      _ = 125 * Real.sqrt 5 := by rw [hs2]; norm_num
  unfold polynomialPrimitive
  rw [hs7, hs5, hs3]
  ring

theorem gap9 :
    paraboloidMoment = (125 * Real.sqrt 5 - 1) / 420 := by
  calc
    paraboloidMoment =
        ∫ y in (1 : ℝ)..Real.sqrt 5,
          (1 / 32 : ℝ) * (y ^ 2 - 1) ^ 2 * y ^ 2 := gap6
    _ = polynomialPrimitive (Real.sqrt 5) - polynomialPrimitive 1 := gap7
    _ = (125 * Real.sqrt 5 - 1) / 420 := gap8

end

end ProofGap.Exercise4346
