import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp

namespace ProofGap.Exercise831

noncomputable section

def f (x : ℝ) : ℝ :=
  x + (x - 1) * Real.arcsin (Real.sqrt (x / (x + 1)))
def quotientAtOne (Δx : ℝ) : ℝ :=
  (f (1 + Δx) - f 1) / Δx

private lemma sqrt_one_div_two :
    Real.sqrt (1 / 2 : ℝ) = 1 / Real.sqrt 2 := by
  rw [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 1)]
  norm_num

theorem gap1 (x : ℝ) (hx : 0 < x) :
    deriv f x =
      1 + Real.arcsin (Real.sqrt (x / (x + 1))) +
        (x - 1) / (2 * (x + 1) * Real.sqrt x) := by
  have harcid (y : ℝ) (hy : 0 < y) :
      Real.arcsin (Real.sqrt (y / (y + 1))) =
        Real.arctan (Real.sqrt y) := by
    have hsin :
        Real.sin (Real.arctan (Real.sqrt y)) =
          Real.sqrt (y / (y + 1)) := by
      calc
        Real.sin (Real.arctan (Real.sqrt y)) =
            Real.sqrt y / Real.sqrt (1 + (Real.sqrt y) ^ 2) :=
          Real.sin_arctan (Real.sqrt y)
        _ = Real.sqrt y / Real.sqrt (y + 1) := by
          rw [Real.sq_sqrt (le_of_lt hy), add_comm]
        _ = Real.sqrt (y / (y + 1)) := by
          rw [Real.sqrt_div (le_of_lt hy)]
    calc
      Real.arcsin (Real.sqrt (y / (y + 1))) =
          Real.arcsin (Real.sin (Real.arctan (Real.sqrt y))) := by
        rw [hsin]
      _ = Real.arctan (Real.sqrt y) :=
        Real.arcsin_sin
          (le_of_lt (Real.neg_pi_div_two_lt_arctan (Real.sqrt y)))
          (le_of_lt (Real.arctan_lt_pi_div_two (Real.sqrt y)))
  have hspos : 0 < Real.sqrt x := Real.sqrt_pos.2 hx
  have hssq : (Real.sqrt x) ^ 2 = x :=
    Real.sq_sqrt (le_of_lt hx)
  have hrpowOuter :
      HasDerivAt (fun z : ℝ => z ^ (1 / 2 : ℝ))
        ((1 / 2 : ℝ) * x ^ ((1 / 2 : ℝ) - 1)) x :=
    Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt hx))
  have hhalf :
      (1 / 2 : ℝ) * x ^ ((1 / 2 : ℝ) - 1) =
        1 / (2 * Real.sqrt x) := by
    rw [show (1 / 2 : ℝ) - 1 = -(1 / 2 : ℝ) by norm_num]
    rw [Real.rpow_neg (le_of_lt hx), ← Real.sqrt_eq_rpow]
    field_simp [ne_of_gt hspos]
  rw [hhalf] at hrpowOuter
  have hsqrt :
      HasDerivAt (fun y : ℝ => Real.sqrt y)
        (1 / (2 * Real.sqrt x)) x := by
    simpa only [Real.sqrt_eq_rpow] using hrpowOuter
  have hatanOuter :
      HasDerivAt Real.arctan
        (1 / (1 + (Real.sqrt x) ^ 2)) (Real.sqrt x) :=
    Real.hasDerivAt_arctan (Real.sqrt x)
  have hatanRaw :
      HasDerivAt (fun y : ℝ => Real.arctan (Real.sqrt y))
        ((1 / (1 + (Real.sqrt x) ^ 2)) *
          (1 / (2 * Real.sqrt x))) x :=
    hatanOuter.comp x hsqrt
  have hatanCoef :
      (1 / (1 + (Real.sqrt x) ^ 2)) *
          (1 / (2 * Real.sqrt x)) =
        1 / (2 * (x + 1) * Real.sqrt x) := by
    rw [hssq]
    field_simp [ne_of_gt hspos] <;> ring
  rw [hatanCoef] at hatanRaw
  have hfg :
      f =ᶠ[nhds x]
        (fun y : ℝ => y + (y - 1) * Real.arctan (Real.sqrt y)) := by
    filter_upwards [Ioi_mem_nhds hx] with y hy
    unfold f
    rw [harcid y hy]
  have htotal :=
    (hasDerivAt_id x).add
      (((hasDerivAt_id x).sub (hasDerivAt_const x 1)).mul hatanRaw)
  have hderiv :
      deriv (fun y : ℝ => y + (y - 1) * Real.arctan (Real.sqrt y)) x =
        1 + Real.arctan (Real.sqrt x) +
          (x - 1) / (2 * (x + 1) * Real.sqrt x) := by
    convert htotal.deriv using 1 <;>
      simp only [Pi.sub_apply, id_eq, one_mul, sub_zero, div_eq_mul_inv] <;>
      ring
  calc
    deriv f x =
        deriv (fun y : ℝ => y + (y - 1) * Real.arctan (Real.sqrt y)) x :=
      Filter.EventuallyEq.deriv_eq hfg
    _ = 1 + Real.arctan (Real.sqrt x) +
          (x - 1) / (2 * (x + 1) * Real.sqrt x) := hderiv
    _ = 1 + Real.arcsin (Real.sqrt (x / (x + 1))) +
          (x - 1) / (2 * (x + 1) * Real.sqrt x) := by
      rw [harcid x hx]
theorem gap2 :
    deriv f 1 = 1 + Real.arcsin (1 / Real.sqrt 2) := by
  rw [gap1 1 (by norm_num)]
  norm_num [sqrt_one_div_two]
theorem gap3 :
    1 + Real.arcsin (1 / Real.sqrt 2) = 1 + Real.pi / 4 := by
  have hsqrtPos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hsqrtNe : Real.sqrt 2 ≠ 0 := ne_of_gt hsqrtPos
  have hrecip : 1 / Real.sqrt 2 = Real.sqrt 2 / 2 := by
    field_simp [hsqrtNe] <;>
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  rw [hrecip, ← Real.sin_pi_div_four]
  rw [Real.arcsin_sin (by linarith [Real.pi_pos])
    (by linarith [Real.pi_pos])]
theorem gap4 : deriv f 1 = 1 + Real.pi / 4 := by
  calc
    deriv f 1 = 1 + Real.arcsin (1 / Real.sqrt 2) := gap2
    _ = 1 + Real.pi / 4 := gap3
theorem gap5 (Δx : ℝ) (hΔ : Δx ≠ 0) :
    quotientAtOne Δx =
      1 + Real.arcsin (Real.sqrt ((1 + Δx) / (2 + Δx))) := by
  unfold quotientAtOne f
  have harg :
      (1 + Δx) / ((1 + Δx) + 1) = (1 + Δx) / (2 + Δx) := by
    congr 1
    ring
  rw [harg]
  field_simp [hΔ] <;> ring
theorem gap6 :
    HasDerivAt f (deriv f 1) 1 ↔
      Filter.Tendsto quotientAtOne
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds (deriv f 1)) := by
  unfold quotientAtOne
  simpa only [div_eq_mul_inv, mul_comm] using
    (hasDerivAt_iff_tendsto_slope_zero
      (f := f) (f' := deriv f 1) (x := (1 : ℝ)))
theorem gap7 :
    Filter.Tendsto quotientAtOne
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds (1 + Real.pi / 4)) ↔
    Filter.Tendsto
      (fun Δx : ℝ => 1 + Real.arcsin (Real.sqrt ((1 + Δx) / (2 + Δx))))
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds (1 + Real.pi / 4)) := by
  have heq :
      quotientAtOne =ᶠ[nhdsWithin 0 ({0} : Set ℝ)ᶜ]
        (fun Δx : ℝ =>
          1 + Real.arcsin (Real.sqrt ((1 + Δx) / (2 + Δx)))) := by
    filter_upwards [self_mem_nhdsWithin] with Δx hΔ
    apply gap5 Δx
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hΔ
  exact Filter.tendsto_congr' heq
theorem gap8 :
    Filter.Tendsto
      (fun Δx : ℝ => 1 + Real.arcsin (Real.sqrt ((1 + Δx) / (2 + Δx))))
      (nhds 0) (nhds (1 + Real.pi / 4)) := by
  have hnum : ContinuousAt (fun Δx : ℝ => 1 + Δx) 0 :=
    continuousAt_const.add continuousAt_id
  have hden : ContinuousAt (fun Δx : ℝ => 2 + Δx) 0 :=
    continuousAt_const.add continuousAt_id
  have hratio :
      ContinuousAt (fun Δx : ℝ => (1 + Δx) / (2 + Δx)) 0 :=
    hnum.div hden (by norm_num)
  have hsqrt :
      ContinuousAt
        (fun Δx : ℝ => Real.sqrt ((1 + Δx) / (2 + Δx))) 0 :=
    Real.continuous_sqrt.continuousAt.comp hratio
  have harcsin :
      ContinuousAt
        (fun Δx : ℝ =>
          Real.arcsin (Real.sqrt ((1 + Δx) / (2 + Δx)))) 0 :=
    Real.continuous_arcsin.continuousAt.comp hsqrt
  have hcont :
      ContinuousAt
        (fun Δx : ℝ =>
          1 + Real.arcsin (Real.sqrt ((1 + Δx) / (2 + Δx)))) 0 :=
    continuousAt_const.add harcsin
  have hvalue :
      (fun Δx : ℝ =>
        1 + Real.arcsin (Real.sqrt ((1 + Δx) / (2 + Δx)))) 0 =
        1 + Real.pi / 4 := by
    norm_num only [add_zero]
    rw [sqrt_one_div_two]
    exact gap3
  simpa only [hvalue] using hcont.tendsto
theorem gap9 : deriv f 1 = 1 + Real.pi / 4 := by
  exact gap4

end

end ProofGap.Exercise831
