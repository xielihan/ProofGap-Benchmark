import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Normed.Operator.Prod
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise4029

noncomputable section

open MeasureTheory
open scoped Interval

def originalRegion : Set (ℝ × ℝ) :=
  {p |
    0 < p.1 ∧ 0 < p.2 ∧
      1 / 2 ≤ p.1 / p.2 ^ 2 ∧ p.1 / p.2 ^ 2 ≤ 1 ∧
      1 / 2 ≤ p.2 / p.1 ^ 2 ∧ p.2 / p.1 ^ 2 ≤ 1}

def parameterRegion : Set (ℝ × ℝ) :=
  Set.Icc (1 / 2 : ℝ) 1 ×ˢ Set.Icc (1 / 2 : ℝ) 1

def volume : ℝ :=
  ∫ p in originalRegion, p.1 * p.2

def xCoord (u v : ℝ) : ℝ :=
  Real.rpow u (-1 / 3 : ℝ) * Real.rpow v (-2 / 3 : ℝ)

def yCoord (u v : ℝ) : ℝ :=
  Real.rpow u (-2 / 3 : ℝ) * Real.rpow v (-1 / 3 : ℝ)

def jacobianAbs (u v : ℝ) : ℝ :=
  1 / 3 * Real.rpow u (-2 : ℝ) * Real.rpow v (-2 : ℝ)

theorem gap1 :
    volume = ∫ p in originalRegion, p.1 * p.2 := by
  rfl

theorem gap2 (u v : ℝ) (hu : 0 < u) (hv : 0 < v) :
    xCoord u v =
      Real.rpow u (-1 / 3 : ℝ) * Real.rpow v (-2 / 3 : ℝ) := by
  rfl

theorem gap3 (u v : ℝ) (hu : 0 < u) (hv : 0 < v) :
    yCoord u v =
      Real.rpow u (-2 / 3 : ℝ) * Real.rpow v (-1 / 3 : ℝ) := by
  rfl

theorem gap4 :
    parameterRegion =
      {p |
        1 / 2 ≤ p.1 ∧ p.1 ≤ 1 ∧
          1 / 2 ≤ p.2 ∧ p.2 ≤ 1} := by
  ext p
  change
    (((1 / 2 : ℝ) ≤ p.1 ∧ p.1 ≤ 1) ∧
        ((1 / 2 : ℝ) ≤ p.2 ∧ p.2 ≤ 1)) ↔
      (1 / 2 : ℝ) ≤ p.1 ∧ p.1 ≤ 1 ∧
        (1 / 2 : ℝ) ≤ p.2 ∧ p.2 ≤ 1
  constructor
  · rintro ⟨⟨hp1l, hp1u⟩, hp2l, hp2u⟩
    exact ⟨hp1l, hp1u, hp2l, hp2u⟩
  · rintro ⟨hp1l, hp1u, hp2l, hp2u⟩
    exact ⟨⟨hp1l, hp1u⟩, hp2l, hp2u⟩

theorem gap5 (u v : ℝ) (hu : 0 < u) (hv : 0 < v) :
    jacobianAbs u v =
      1 / 3 * Real.rpow u (-2 : ℝ) * Real.rpow v (-2 : ℝ) := by
  rfl

private theorem rpow_add_eq (z α β : ℝ) (hz : 0 < z) :
    Real.rpow z α * Real.rpow z β = Real.rpow z (α + β) :=
  (Real.rpow_add hz α β).symm

private theorem rpow_sq_eq (z α : ℝ) (hz : 0 < z) :
    Real.rpow z α ^ 2 = Real.rpow z (α + α) := by
  rw [pow_two, rpow_add_eq z α α hz]

private theorem rpow_pow_eq (z α : ℝ) (n : ℕ) (hz : 0 < z) :
    Real.rpow (z ^ n) α = Real.rpow z ((n : ℝ) * α) := by
  exact (Real.rpow_natCast_mul hz.le n α).symm

private def paramMap (p : ℝ × ℝ) : ℝ × ℝ :=
  (xCoord p.1 p.2, yCoord p.1 p.2)

private def inverseMap (p : ℝ × ℝ) : ℝ × ℝ :=
  (p.1 / p.2 ^ 2, p.2 / p.1 ^ 2)

private theorem paramMap_pos (u v : ℝ) (hu : 0 < u) (hv : 0 < v) :
    0 < xCoord u v ∧ 0 < yCoord u v := by
  constructor
  · exact mul_pos (Real.rpow_pos_of_pos hu _) (Real.rpow_pos_of_pos hv _)
  · exact mul_pos (Real.rpow_pos_of_pos hu _) (Real.rpow_pos_of_pos hv _)

private theorem inverse_after_param_fst (u v : ℝ)
    (hu : 0 < u) (hv : 0 < v) :
    xCoord u v / yCoord u v ^ 2 = u := by
  have hvSq :
      Real.rpow v (-1 / 3 : ℝ) ^ 2 =
        Real.rpow v (-2 / 3 : ℝ) := by
    rw [rpow_sq_eq v (-1 / 3 : ℝ) hv]
    congr 1
    ring
  have huSq :
      Real.rpow u (-2 / 3 : ℝ) ^ 2 =
        Real.rpow u (-4 / 3 : ℝ) := by
    rw [rpow_sq_eq u (-2 / 3 : ℝ) hu]
    congr 1
    ring
  have huRel :
      u * Real.rpow u (-4 / 3 : ℝ) =
        Real.rpow u (-1 / 3 : ℝ) := by
    calc
      u * Real.rpow u (-4 / 3 : ℝ) =
          Real.rpow u 1 * Real.rpow u (-4 / 3 : ℝ) := by
            exact congrArg
              (fun z : ℝ => z * Real.rpow u (-4 / 3 : ℝ))
              (Real.rpow_one u).symm
      _ = Real.rpow u (1 + (-4 / 3 : ℝ)) :=
            rpow_add_eq u 1 (-4 / 3 : ℝ) hu
      _ = Real.rpow u (-1 / 3 : ℝ) := by congr 1 <;> ring
  have hUne : Real.rpow u (-4 / 3 : ℝ) ≠ 0 :=
    (Real.rpow_pos_of_pos hu _).ne'
  have hVne : Real.rpow v (-2 / 3 : ℝ) ≠ 0 :=
    (Real.rpow_pos_of_pos hv _).ne'
  unfold xCoord yCoord
  rw [mul_pow, huSq, hvSq]
  apply (div_eq_iff (mul_ne_zero hUne hVne)).2
  rw [← huRel]
  ring

private theorem inverse_after_param_snd (u v : ℝ)
    (hu : 0 < u) (hv : 0 < v) :
    yCoord u v / xCoord u v ^ 2 = v := by
  have huSq :
      Real.rpow u (-1 / 3 : ℝ) ^ 2 =
        Real.rpow u (-2 / 3 : ℝ) := by
    rw [rpow_sq_eq u (-1 / 3 : ℝ) hu]
    congr 1
    ring
  have hvSq :
      Real.rpow v (-2 / 3 : ℝ) ^ 2 =
        Real.rpow v (-4 / 3 : ℝ) := by
    rw [rpow_sq_eq v (-2 / 3 : ℝ) hv]
    congr 1
    ring
  have hvRel :
      v * Real.rpow v (-4 / 3 : ℝ) =
        Real.rpow v (-1 / 3 : ℝ) := by
    calc
      v * Real.rpow v (-4 / 3 : ℝ) =
          Real.rpow v 1 * Real.rpow v (-4 / 3 : ℝ) := by
            exact congrArg
              (fun z : ℝ => z * Real.rpow v (-4 / 3 : ℝ))
              (Real.rpow_one v).symm
      _ = Real.rpow v (1 + (-4 / 3 : ℝ)) :=
            rpow_add_eq v 1 (-4 / 3 : ℝ) hv
      _ = Real.rpow v (-1 / 3 : ℝ) := by congr 1 <;> ring
  have hUne : Real.rpow u (-2 / 3 : ℝ) ≠ 0 :=
    (Real.rpow_pos_of_pos hu _).ne'
  have hVne : Real.rpow v (-4 / 3 : ℝ) ≠ 0 :=
    (Real.rpow_pos_of_pos hv _).ne'
  unfold xCoord yCoord
  rw [mul_pow, huSq, hvSq]
  apply (div_eq_iff (mul_ne_zero hUne hVne)).2
  rw [← hvRel]
  ring

private theorem param_after_inverse_fst (x y : ℝ)
    (hx : 0 < x) (hy : 0 < y) :
    xCoord (x / y ^ 2) (y / x ^ 2) = x := by
  have hu : 0 < x / y ^ 2 := div_pos hx (sq_pos_of_pos hy)
  have hv : 0 < y / x ^ 2 := div_pos hy (sq_pos_of_pos hx)
  have hyPow :
      Real.rpow (y ^ 2) (-1 / 3 : ℝ) =
        Real.rpow y (-2 / 3 : ℝ) := by
    rw [rpow_pow_eq y (-1 / 3 : ℝ) 2 hy]
    congr 1
    ring
  have hxPow :
      Real.rpow (x ^ 2) (-2 / 3 : ℝ) =
        Real.rpow x (-4 / 3 : ℝ) := by
    rw [rpow_pow_eq x (-2 / 3 : ℝ) 2 hx]
    congr 1
    ring
  have hxRel :
      Real.rpow x (-1 / 3 : ℝ) =
        x * Real.rpow x (-4 / 3 : ℝ) := by
    symm
    calc
      x * Real.rpow x (-4 / 3 : ℝ) =
          Real.rpow x 1 * Real.rpow x (-4 / 3 : ℝ) := by
            exact congrArg
              (fun z : ℝ => z * Real.rpow x (-4 / 3 : ℝ))
              (Real.rpow_one x).symm
      _ = Real.rpow x (1 + (-4 / 3 : ℝ)) :=
            rpow_add_eq x 1 (-4 / 3 : ℝ) hx
      _ = Real.rpow x (-1 / 3 : ℝ) := by congr 1 <;> ring
  have hYne : Real.rpow y (-2 / 3 : ℝ) ≠ 0 :=
    (Real.rpow_pos_of_pos hy _).ne'
  have hXne : Real.rpow x (-4 / 3 : ℝ) ≠ 0 :=
    (Real.rpow_pos_of_pos hx _).ne'
  have hdivU :
      Real.rpow (x / y ^ 2) (-1 / 3 : ℝ) =
        Real.rpow x (-1 / 3 : ℝ) /
          Real.rpow (y ^ 2) (-1 / 3 : ℝ) :=
    Real.div_rpow hx.le (sq_nonneg y) _
  have hdivV :
      Real.rpow (y / x ^ 2) (-2 / 3 : ℝ) =
        Real.rpow y (-2 / 3 : ℝ) /
          Real.rpow (x ^ 2) (-2 / 3 : ℝ) :=
    Real.div_rpow hy.le (sq_nonneg x) _
  unfold xCoord
  change
    Real.rpow (x / y ^ 2) (-1 / 3 : ℝ) *
      Real.rpow (y / x ^ 2) (-2 / 3 : ℝ) = x
  rw [hdivU, hdivV, hyPow, hxPow, hxRel]
  field_simp [hYne, hXne]
  exact div_self (mul_ne_zero
    (Real.rpow_pos_of_pos hx _).ne'
    (Real.rpow_pos_of_pos hy _).ne')

private theorem param_after_inverse_snd (x y : ℝ)
    (hx : 0 < x) (hy : 0 < y) :
    yCoord (x / y ^ 2) (y / x ^ 2) = y := by
  have hxPow :
      Real.rpow (x ^ 2) (-1 / 3 : ℝ) =
        Real.rpow x (-2 / 3 : ℝ) := by
    rw [rpow_pow_eq x (-1 / 3 : ℝ) 2 hx]
    congr 1
    ring
  have hyPow :
      Real.rpow (y ^ 2) (-2 / 3 : ℝ) =
        Real.rpow y (-4 / 3 : ℝ) := by
    rw [rpow_pow_eq y (-2 / 3 : ℝ) 2 hy]
    congr 1
    ring
  have hyRel :
      Real.rpow y (-1 / 3 : ℝ) =
        y * Real.rpow y (-4 / 3 : ℝ) := by
    symm
    calc
      y * Real.rpow y (-4 / 3 : ℝ) =
          Real.rpow y 1 * Real.rpow y (-4 / 3 : ℝ) := by
            exact congrArg
              (fun z : ℝ => z * Real.rpow y (-4 / 3 : ℝ))
              (Real.rpow_one y).symm
      _ = Real.rpow y (1 + (-4 / 3 : ℝ)) :=
            rpow_add_eq y 1 (-4 / 3 : ℝ) hy
      _ = Real.rpow y (-1 / 3 : ℝ) := by congr 1 <;> ring
  have hXne : Real.rpow x (-2 / 3 : ℝ) ≠ 0 :=
    (Real.rpow_pos_of_pos hx _).ne'
  have hYne : Real.rpow y (-4 / 3 : ℝ) ≠ 0 :=
    (Real.rpow_pos_of_pos hy _).ne'
  have hdivU :
      Real.rpow (x / y ^ 2) (-2 / 3 : ℝ) =
        Real.rpow x (-2 / 3 : ℝ) /
          Real.rpow (y ^ 2) (-2 / 3 : ℝ) :=
    Real.div_rpow hx.le (sq_nonneg y) _
  have hdivV :
      Real.rpow (y / x ^ 2) (-1 / 3 : ℝ) =
        Real.rpow y (-1 / 3 : ℝ) /
          Real.rpow (x ^ 2) (-1 / 3 : ℝ) :=
    Real.div_rpow hy.le (sq_nonneg x) _
  unfold yCoord
  change
    Real.rpow (x / y ^ 2) (-2 / 3 : ℝ) *
      Real.rpow (y / x ^ 2) (-1 / 3 : ℝ) = y
  rw [hdivU, hdivV, hxPow, hyPow, hyRel]
  field_simp [hXne, hYne]
  exact div_self (mul_ne_zero
    (Real.rpow_pos_of_pos hx _).ne'
    (Real.rpow_pos_of_pos hy _).ne')

private theorem image_parameter :
    paramMap '' parameterRegion = originalRegion := by
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    have hu : 0 < q.1 := lt_of_lt_of_le (by norm_num) hq.1.1
    have hv : 0 < q.2 := lt_of_lt_of_le (by norm_num) hq.2.1
    have hpos := paramMap_pos q.1 q.2 hu hv
    change
      0 < xCoord q.1 q.2 ∧ 0 < yCoord q.1 q.2 ∧
        1 / 2 ≤ xCoord q.1 q.2 / yCoord q.1 q.2 ^ 2 ∧
        xCoord q.1 q.2 / yCoord q.1 q.2 ^ 2 ≤ 1 ∧
        1 / 2 ≤ yCoord q.1 q.2 / xCoord q.1 q.2 ^ 2 ∧
        yCoord q.1 q.2 / xCoord q.1 q.2 ^ 2 ≤ 1
    rw [inverse_after_param_fst q.1 q.2 hu hv,
      inverse_after_param_snd q.1 q.2 hu hv]
    exact ⟨hpos.1, hpos.2, hq.1.1, hq.1.2, hq.2.1, hq.2.2⟩
  · intro hp
    have hp' :
        0 < p.1 ∧ 0 < p.2 ∧
          1 / 2 ≤ p.1 / p.2 ^ 2 ∧ p.1 / p.2 ^ 2 ≤ 1 ∧
          1 / 2 ≤ p.2 / p.1 ^ 2 ∧ p.2 / p.1 ^ 2 ≤ 1 := hp
    let q : ℝ × ℝ := inverseMap p
    have hq : q ∈ parameterRegion := by
      exact ⟨⟨hp'.2.2.1, hp'.2.2.2.1⟩,
        ⟨hp'.2.2.2.2.1, hp'.2.2.2.2.2⟩⟩
    refine ⟨q, hq, ?_⟩
    apply Prod.ext
    · exact param_after_inverse_fst p.1 p.2 hp'.1 hp'.2.1
    · exact param_after_inverse_snd p.1 p.2 hp'.1 hp'.2.1

private theorem param_injOn :
    Set.InjOn paramMap parameterRegion := by
  intro p hp q hq heq
  have hp1 : 0 < p.1 := lt_of_lt_of_le (by norm_num) hp.1.1
  have hp2 : 0 < p.2 := lt_of_lt_of_le (by norm_num) hp.2.1
  have hq1 : 0 < q.1 := lt_of_lt_of_le (by norm_num) hq.1.1
  have hq2 : 0 < q.2 := lt_of_lt_of_le (by norm_num) hq.2.1
  have hfst := congrArg
    (fun z : ℝ × ℝ => z.1 / z.2 ^ 2) heq
  have hsnd := congrArg
    (fun z : ℝ × ℝ => z.2 / z.1 ^ 2) heq
  change
    xCoord p.1 p.2 / yCoord p.1 p.2 ^ 2 =
      xCoord q.1 q.2 / yCoord q.1 q.2 ^ 2 at hfst
  change
    yCoord p.1 p.2 / xCoord p.1 p.2 ^ 2 =
      yCoord q.1 q.2 / xCoord q.1 q.2 ^ 2 at hsnd
  rw [inverse_after_param_fst p.1 p.2 hp1 hp2,
    inverse_after_param_fst q.1 q.2 hq1 hq2] at hfst
  rw [inverse_after_param_snd p.1 p.2 hp1 hp2,
    inverse_after_param_snd q.1 q.2 hq1 hq2] at hsnd
  exact Prod.ext hfst hsnd

private def derivCLM (u v : ℝ) : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
  (Matrix.toLin (.finTwoProd ℝ) (.finTwoProd ℝ)
    !![
      (-1 / 3 : ℝ) * Real.rpow u (-4 / 3 : ℝ) *
        Real.rpow v (-2 / 3 : ℝ),
      (-2 / 3 : ℝ) * Real.rpow u (-1 / 3 : ℝ) *
        Real.rpow v (-5 / 3 : ℝ);
      (-2 / 3 : ℝ) * Real.rpow u (-5 / 3 : ℝ) *
        Real.rpow v (-1 / 3 : ℝ),
      (-1 / 3 : ℝ) * Real.rpow u (-2 / 3 : ℝ) *
        Real.rpow v (-4 / 3 : ℝ)
    ]).toContinuousLinearMap

private theorem derivCLM_apply (u v : ℝ) (p : ℝ × ℝ) :
    derivCLM u v p =
      (((-1 / 3 : ℝ) * Real.rpow u (-4 / 3 : ℝ) *
          Real.rpow v (-2 / 3 : ℝ)) * p.1 +
        ((-2 / 3 : ℝ) * Real.rpow u (-1 / 3 : ℝ) *
          Real.rpow v (-5 / 3 : ℝ)) * p.2,
       ((-2 / 3 : ℝ) * Real.rpow u (-5 / 3 : ℝ) *
          Real.rpow v (-1 / 3 : ℝ)) * p.1 +
        ((-1 / 3 : ℝ) * Real.rpow u (-2 / 3 : ℝ) *
          Real.rpow v (-4 / 3 : ℝ)) * p.2) := by
  unfold derivCLM
  rw [Matrix.toLin_finTwoProd_toContinuousLinearMap]
  simp

private theorem hasFDerivAt_paramMap (u v : ℝ) (hu : 0 < u) (hv : 0 < v) :
    HasFDerivAt paramMap (derivCLM u v) (u, v) := by
  let fstCLM := ContinuousLinearMap.fst ℝ ℝ ℝ
  let sndCLM := ContinuousLinearMap.snd ℝ ℝ ℝ
  have hu1 :
      HasFDerivAt (fun p : ℝ × ℝ => Real.rpow p.1 (-1 / 3 : ℝ))
        (((-1 / 3 : ℝ) * Real.rpow u (-4 / 3 : ℝ)) • fstCLM)
        (u, v) := by
    simpa [fstCLM, Function.comp_def,
      show (-1 / 3 : ℝ) - 1 = -4 / 3 by ring] using
      (Real.hasDerivAt_rpow_const
        (x := u) (p := (-1 / 3 : ℝ)) (Or.inl hu.ne')).comp_hasFDerivAt
          (u, v) (ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt
  have hu2 :
      HasFDerivAt (fun p : ℝ × ℝ => Real.rpow p.1 (-2 / 3 : ℝ))
        (((-2 / 3 : ℝ) * Real.rpow u (-5 / 3 : ℝ)) • fstCLM)
        (u, v) := by
    simpa [fstCLM, Function.comp_def,
      show (-2 / 3 : ℝ) - 1 = -5 / 3 by ring] using
      (Real.hasDerivAt_rpow_const
        (x := u) (p := (-2 / 3 : ℝ)) (Or.inl hu.ne')).comp_hasFDerivAt
          (u, v) (ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt
  have hv1 :
      HasFDerivAt (fun p : ℝ × ℝ => Real.rpow p.2 (-1 / 3 : ℝ))
        (((-1 / 3 : ℝ) * Real.rpow v (-4 / 3 : ℝ)) • sndCLM)
        (u, v) := by
    simpa [sndCLM, Function.comp_def,
      show (-1 / 3 : ℝ) - 1 = -4 / 3 by ring] using
      (Real.hasDerivAt_rpow_const
        (x := v) (p := (-1 / 3 : ℝ)) (Or.inl hv.ne')).comp_hasFDerivAt
          (u, v) (ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt
  have hv2 :
      HasFDerivAt (fun p : ℝ × ℝ => Real.rpow p.2 (-2 / 3 : ℝ))
        (((-2 / 3 : ℝ) * Real.rpow v (-5 / 3 : ℝ)) • sndCLM)
        (u, v) := by
    simpa [sndCLM, Function.comp_def,
      show (-2 / 3 : ℝ) - 1 = -5 / 3 by ring] using
      (Real.hasDerivAt_rpow_const
        (x := v) (p := (-2 / 3 : ℝ)) (Or.inl hv.ne')).comp_hasFDerivAt
          (u, v) (ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt
  have hx := hu1.mul hv2
  have hy := hu2.mul hv1
  have hxy := hx.prodMk hy
  convert hxy using 1
  · ext p <;> simp [fstCLM, sndCLM, derivCLM_apply] <;> ring

private theorem deriv_det (u v : ℝ) (hu : 0 < u) (hv : 0 < v) :
    (derivCLM u v).det =
      -(1 / 3 * Real.rpow u (-2 : ℝ) *
        Real.rpow v (-2 : ℝ)) := by
  have huA :
      Real.rpow u (-4 / 3 : ℝ) * Real.rpow u (-2 / 3 : ℝ) =
        Real.rpow u (-2 : ℝ) := by
    rw [rpow_add_eq u (-4 / 3 : ℝ) (-2 / 3 : ℝ) hu]
    congr 1
    ring
  have huB :
      Real.rpow u (-1 / 3 : ℝ) * Real.rpow u (-5 / 3 : ℝ) =
        Real.rpow u (-2 : ℝ) := by
    rw [rpow_add_eq u (-1 / 3 : ℝ) (-5 / 3 : ℝ) hu]
    congr 1
    ring
  have hvA :
      Real.rpow v (-2 / 3 : ℝ) * Real.rpow v (-4 / 3 : ℝ) =
        Real.rpow v (-2 : ℝ) := by
    rw [rpow_add_eq v (-2 / 3 : ℝ) (-4 / 3 : ℝ) hv]
    congr 1
    ring
  have hvB :
      Real.rpow v (-5 / 3 : ℝ) * Real.rpow v (-1 / 3 : ℝ) =
        Real.rpow v (-2 : ℝ) := by
    rw [rpow_add_eq v (-5 / 3 : ℝ) (-1 / 3 : ℝ) hv]
    congr 1
    ring
  unfold derivCLM
  simp only [LinearMap.det_toContinuousLinearMap, LinearMap.det_toLin,
    Matrix.det_fin_two_of]
  rw [show
      ((-1 / 3 : ℝ) * Real.rpow u (-4 / 3 : ℝ) *
          Real.rpow v (-2 / 3 : ℝ)) *
        ((-1 / 3 : ℝ) * Real.rpow u (-2 / 3 : ℝ) *
          Real.rpow v (-4 / 3 : ℝ)) =
        1 / 9 *
          (Real.rpow u (-4 / 3 : ℝ) * Real.rpow u (-2 / 3 : ℝ)) *
          (Real.rpow v (-2 / 3 : ℝ) * Real.rpow v (-4 / 3 : ℝ)) by ring,
    show
      ((-2 / 3 : ℝ) * Real.rpow u (-1 / 3 : ℝ) *
          Real.rpow v (-5 / 3 : ℝ)) *
        ((-2 / 3 : ℝ) * Real.rpow u (-5 / 3 : ℝ) *
          Real.rpow v (-1 / 3 : ℝ)) =
        4 / 9 *
          (Real.rpow u (-1 / 3 : ℝ) * Real.rpow u (-5 / 3 : ℝ)) *
          (Real.rpow v (-5 / 3 : ℝ) * Real.rpow v (-1 / 3 : ℝ)) by ring,
    huA, huB, hvA, hvB]
  ring

private theorem abs_deriv_det (u v : ℝ) (hu : 0 < u) (hv : 0 < v) :
    |(derivCLM u v).det| = jacobianAbs u v := by
  rw [deriv_det u v hu hv]
  have hnonneg :
      0 ≤ 1 / 3 * Real.rpow u (-2 : ℝ) *
        Real.rpow v (-2 : ℝ) :=
    mul_nonneg
      (mul_nonneg (by norm_num) (Real.rpow_nonneg hu.le _))
      (Real.rpow_nonneg hv.le _)
  rw [abs_neg, abs_of_nonneg hnonneg]
  rfl

private theorem transformed_integrand (u v : ℝ) (hu : 0 < u) (hv : 0 < v) :
    jacobianAbs u v *
        (xCoord u v * yCoord u v) =
      1 / 3 * Real.rpow u (-3 : ℝ) *
        Real.rpow v (-3 : ℝ) := by
  have huXY :
      Real.rpow u (-1 / 3 : ℝ) * Real.rpow u (-2 / 3 : ℝ) =
        Real.rpow u (-1 : ℝ) := by
    rw [rpow_add_eq u (-1 / 3 : ℝ) (-2 / 3 : ℝ) hu]
    congr 1
    ring
  have hvXY :
      Real.rpow v (-2 / 3 : ℝ) * Real.rpow v (-1 / 3 : ℝ) =
        Real.rpow v (-1 : ℝ) := by
    rw [rpow_add_eq v (-2 / 3 : ℝ) (-1 / 3 : ℝ) hv]
    congr 1
    ring
  have huAll :
      Real.rpow u (-2 : ℝ) * Real.rpow u (-1 : ℝ) =
        Real.rpow u (-3 : ℝ) := by
    rw [rpow_add_eq u (-2 : ℝ) (-1 : ℝ) hu]
    congr 1
    ring
  have hvAll :
      Real.rpow v (-2 : ℝ) * Real.rpow v (-1 : ℝ) =
        Real.rpow v (-3 : ℝ) := by
    rw [rpow_add_eq v (-2 : ℝ) (-1 : ℝ) hv]
    congr 1
    ring
  unfold jacobianAbs xCoord yCoord
  rw [show
      (1 / 3 * Real.rpow u (-2 : ℝ) * Real.rpow v (-2 : ℝ)) *
        ((Real.rpow u (-1 / 3 : ℝ) * Real.rpow v (-2 / 3 : ℝ)) *
          (Real.rpow u (-2 / 3 : ℝ) * Real.rpow v (-1 / 3 : ℝ))) =
        1 / 3 *
          (Real.rpow u (-2 : ℝ) *
            (Real.rpow u (-1 / 3 : ℝ) * Real.rpow u (-2 / 3 : ℝ))) *
          (Real.rpow v (-2 : ℝ) *
            (Real.rpow v (-2 / 3 : ℝ) * Real.rpow v (-1 / 3 : ℝ))) by ring,
    huXY, hvXY, huAll, hvAll]

private theorem parameter_integral_as_iterated :
    (∫ p in parameterRegion,
      Real.rpow p.1 (-3 : ℝ) * Real.rpow p.2 (-3 : ℝ)) =
      ∫ u in (1 / 2 : ℝ)..1,
        ∫ v in (1 / 2 : ℝ)..1,
          Real.rpow u (-3 : ℝ) * Real.rpow v (-3 : ℝ) := by
  let I : ℝ :=
    ∫ t in Set.Icc (1 / 2 : ℝ) 1, Real.rpow t (-3 : ℝ)
  have hset :
      (∫ p in parameterRegion,
        Real.rpow p.1 (-3 : ℝ) * Real.rpow p.2 (-3 : ℝ)) =
        I * I := by
    unfold parameterRegion I
    exact MeasureTheory.setIntegral_prod_mul
      (fun t : ℝ => Real.rpow t (-3 : ℝ))
      (fun t : ℝ => Real.rpow t (-3 : ℝ))
      (Set.Icc (1 / 2 : ℝ) 1) (Set.Icc (1 / 2 : ℝ) 1)
  have hI :
      I = ∫ t in (1 / 2 : ℝ)..1, Real.rpow t (-3 : ℝ) := by
    unfold I
    rw [← Measure.restrict_congr_set
      (Ioc_ae_eq_Icc :
        Set.Ioc (1 / 2 : ℝ) 1 =ᵐ[MeasureTheory.volume]
          Set.Icc (1 / 2 : ℝ) 1)]
    rw [← intervalIntegral.integral_of_le (by norm_num)]
  rw [hset, hI]
  calc
    (∫ u in (1 / 2 : ℝ)..1, Real.rpow u (-3 : ℝ)) *
        (∫ v in (1 / 2 : ℝ)..1, Real.rpow v (-3 : ℝ)) =
        ∫ u in (1 / 2 : ℝ)..1,
          Real.rpow u (-3 : ℝ) *
            (∫ v in (1 / 2 : ℝ)..1,
              Real.rpow v (-3 : ℝ)) := by
          rw [intervalIntegral.integral_mul_const]
    _ = ∫ u in (1 / 2 : ℝ)..1,
        ∫ v in (1 / 2 : ℝ)..1,
          Real.rpow u (-3 : ℝ) * Real.rpow v (-3 : ℝ) := by
          apply intervalIntegral.integral_congr
          intro u hu
          change
            Real.rpow u (-3 : ℝ) *
                (∫ v in (1 / 2 : ℝ)..1,
                  Real.rpow v (-3 : ℝ)) =
              ∫ v in (1 / 2 : ℝ)..1,
                Real.rpow u (-3 : ℝ) * Real.rpow v (-3 : ℝ)
          rw [intervalIntegral.integral_const_mul]

theorem gap6 :
    volume =
      1 / 3 *
        ∫ u in (1 / 2 : ℝ)..1,
          ∫ v in (1 / 2 : ℝ)..1,
            Real.rpow u (-3 : ℝ) * Real.rpow v (-3 : ℝ) := by
  letI : Measure.IsAddHaarMeasure
      (MeasureTheory.volume : Measure (ℝ × ℝ)) := by
    rw [Measure.volume_eq_prod]
    infer_instance
  have hparam : MeasurableSet parameterRegion :=
    measurableSet_Icc.prod measurableSet_Icc
  have hchange :=
    MeasureTheory.integral_image_eq_integral_abs_det_fderiv_smul
      (MeasureTheory.volume : Measure (ℝ × ℝ))
      hparam (f := paramMap)
      (f' := fun p => derivCLM p.1 p.2)
      (fun p hp => by
        have hp1 : 0 < p.1 := lt_of_lt_of_le (by norm_num) hp.1.1
        have hp2 : 0 < p.2 := lt_of_lt_of_le (by norm_num) hp.2.1
        exact (hasFDerivAt_paramMap p.1 p.2 hp1 hp2).hasFDerivWithinAt)
      param_injOn (fun p : ℝ × ℝ => p.1 * p.2)
  rw [image_parameter] at hchange
  have hpoint : ∀ p ∈ parameterRegion,
      |(derivCLM p.1 p.2).det| •
          ((paramMap p).1 * (paramMap p).2) =
        1 / 3 *
          (Real.rpow p.1 (-3 : ℝ) * Real.rpow p.2 (-3 : ℝ)) := by
    intro p hp
    have hp1 : 0 < p.1 := lt_of_lt_of_le (by norm_num) hp.1.1
    have hp2 : 0 < p.2 := lt_of_lt_of_le (by norm_num) hp.2.1
    rw [abs_deriv_det p.1 p.2 hp1 hp2]
    simp only [smul_eq_mul, paramMap, Prod.fst, Prod.snd]
    rw [transformed_integrand p.1 p.2 hp1 hp2]
    ring
  calc
    volume = ∫ p in originalRegion, p.1 * p.2 := rfl
    _ = ∫ p in parameterRegion,
        |(derivCLM p.1 p.2).det| •
          ((paramMap p).1 * (paramMap p).2) := hchange
    _ = ∫ p in parameterRegion,
        1 / 3 *
          (Real.rpow p.1 (-3 : ℝ) *
            Real.rpow p.2 (-3 : ℝ)) := by
          apply MeasureTheory.setIntegral_congr_fun hparam
          exact hpoint
    _ = 1 / 3 * ∫ p in parameterRegion,
        Real.rpow p.1 (-3 : ℝ) *
          Real.rpow p.2 (-3 : ℝ) := by
          rw [MeasureTheory.integral_const_mul]
    _ = 1 / 3 *
        ∫ u in (1 / 2 : ℝ)..1,
          ∫ v in (1 / 2 : ℝ)..1,
            Real.rpow u (-3 : ℝ) * Real.rpow v (-3 : ℝ) := by
          rw [parameter_integral_as_iterated]

theorem gap7 :
    1 / 3 *
        (∫ u in (1 / 2 : ℝ)..1,
          ∫ v in (1 / 2 : ℝ)..1,
            Real.rpow u (-3 : ℝ) * Real.rpow v (-3 : ℝ)) =
      1 / 3 *
        (∫ u in (1 / 2 : ℝ)..1, Real.rpow u (-3 : ℝ)) ^ 2 := by
  have hinner : ∀ u : ℝ,
      (∫ v in (1 / 2 : ℝ)..1,
        Real.rpow u (-3 : ℝ) * Real.rpow v (-3 : ℝ)) =
        Real.rpow u (-3 : ℝ) *
          ∫ v in (1 / 2 : ℝ)..1, Real.rpow v (-3 : ℝ) := by
    intro u
    rw [intervalIntegral.integral_const_mul]
  congr 1
  calc
    (∫ u in (1 / 2 : ℝ)..1,
      ∫ v in (1 / 2 : ℝ)..1,
        Real.rpow u (-3 : ℝ) * Real.rpow v (-3 : ℝ)) =
        ∫ u in (1 / 2 : ℝ)..1,
          Real.rpow u (-3 : ℝ) *
            (∫ v in (1 / 2 : ℝ)..1,
              Real.rpow v (-3 : ℝ)) := by
          apply intervalIntegral.integral_congr
          intro u hu
          exact hinner u
    _ = (∫ u in (1 / 2 : ℝ)..1, Real.rpow u (-3 : ℝ)) *
        (∫ v in (1 / 2 : ℝ)..1, Real.rpow v (-3 : ℝ)) := by
          rw [intervalIntegral.integral_mul_const]
    _ = _ := by ring

private theorem rpow_integral_value :
    (∫ u in (1 / 2 : ℝ)..1, Real.rpow u (-3 : ℝ)) = 3 / 2 := by
  change (∫ u in (1 / 2 : ℝ)..1, u ^ (-3 : ℝ)) = 3 / 2
  rw [integral_rpow (a := (1 / 2 : ℝ)) (b := (1 : ℝ))
    (r := (-3 : ℝ)) (Or.inr ⟨by norm_num, by
      rw [Set.uIcc_of_le (by norm_num)]
      norm_num⟩)]
  norm_num [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]

theorem gap8 :
    1 / 3 *
        (∫ u in (1 / 2 : ℝ)..1, Real.rpow u (-3 : ℝ)) ^ 2 =
      1 / 3 * (9 / 4) := by
  rw [rpow_integral_value]
  norm_num

theorem gap9 :
    1 / 3 * (9 / 4) = 3 / 4 := by
  norm_num

theorem gap10 :
    volume = 3 / 4 := by
  calc
    volume =
        1 / 3 *
          (∫ u in (1 / 2 : ℝ)..1,
            ∫ v in (1 / 2 : ℝ)..1,
              Real.rpow u (-3 : ℝ) * Real.rpow v (-3 : ℝ)) := gap6
    _ = 1 / 3 *
        (∫ u in (1 / 2 : ℝ)..1, Real.rpow u (-3 : ℝ)) ^ 2 := gap7
    _ = 1 / 3 * (9 / 4) := gap8
    _ = 3 / 4 := by norm_num

end

end ProofGap.Exercise4029
