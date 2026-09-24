import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Order.Filter.AtTopBot.Ring

namespace ProofGap.Exercise4311

noncomputable section

open MeasureTheory
open scoped Interval

def foliumParam (a t : ℝ) : ℝ × ℝ :=
  (3 * a * t / (1 + t ^ 3),
    3 * a * t ^ 2 / (1 + t ^ 3))

def foliumLoop (a : ℝ) : Set (ℝ × ℝ) :=
  foliumParam a '' Set.Ici (0 : ℝ)

def foliumOrientedArea (a : ℝ) : ℝ :=
  (1 / 2 : ℝ) *
    ∫ t in Set.Ici (0 : ℝ),
      (foliumParam a t).1 * deriv (fun s => (foliumParam a s).2) t -
        (foliumParam a t).2 * deriv (fun s => (foliumParam a s).1) t

def foliumPrimitive (a t : ℝ) : ℝ :=
  -(3 * a ^ 2 / 2) / (1 + t ^ 3)

theorem gap1 (a : ℝ) :
    foliumLoop a = foliumParam a '' Set.Ici (0 : ℝ) := by
  rfl

theorem gap2 (a t : ℝ) (ht : 0 ≤ t) :
    deriv (fun s => (foliumParam a s).1) t =
      3 * a * (1 - 2 * t ^ 3) / (1 + t ^ 3) ^ 2 := by
  have hden : 1 + t ^ 3 ≠ 0 := by positivity
  have hnum :
      HasDerivAt (fun s : ℝ => 3 * a * s) (3 * a) t := by
    convert (hasDerivAt_id t).const_mul (3 * a) using 1 <;> ring
  have hdenDeriv :
      HasDerivAt (fun s : ℝ => 1 + s ^ 3) (3 * t ^ 2) t := by
    convert (hasDerivAt_const t (1 : ℝ)).add
      ((hasDerivAt_id t).pow 3) using 1 <;> simp [id_eq] <;> ring
  unfold foliumParam
  dsimp only
  convert (hnum.div hdenDeriv hden).deriv using 1 <;>
    (try simp [id_eq]) <;>
    field_simp [hden] <;> ring

theorem gap3 (a t : ℝ) (ht : 0 ≤ t) :
    deriv (fun s => (foliumParam a s).2) t =
      3 * a * t * (2 - t ^ 3) / (1 + t ^ 3) ^ 2 := by
  have hden : 1 + t ^ 3 ≠ 0 := by positivity
  have hnum :
      HasDerivAt (fun s : ℝ => 3 * a * s ^ 2) (6 * a * t) t := by
    convert ((hasDerivAt_id t).pow 2).const_mul (3 * a) using 1 <;>
      simp [id_eq] <;> ring
  have hdenDeriv :
      HasDerivAt (fun s : ℝ => 1 + s ^ 3) (3 * t ^ 2) t := by
    convert (hasDerivAt_const t (1 : ℝ)).add
      ((hasDerivAt_id t).pow 3) using 1 <;> simp [id_eq] <;> ring
  unfold foliumParam
  dsimp only
  convert (hnum.div hdenDeriv hden).deriv using 1 <;>
    (try simp [id_eq]) <;>
    field_simp [hden] <;> ring

theorem gap4 (a t : ℝ) (ht : 0 ≤ t) :
    (foliumParam a t).1 * deriv (fun s => (foliumParam a s).2) t -
        (foliumParam a t).2 * deriv (fun s => (foliumParam a s).1) t =
      9 * a ^ 2 * t ^ 2 / (1 + t ^ 3) ^ 2 := by
  rw [gap2 a t ht, gap3 a t ht]
  unfold foliumParam
  dsimp only
  have hden : 1 + t ^ 3 ≠ 0 := by positivity
  field_simp [hden]
  ring

theorem gap5 (a : ℝ) (ha : 0 < a) :
    foliumOrientedArea a =
      9 * a ^ 2 / 2 *
        ∫ t in Set.Ici (0 : ℝ), t ^ 2 / (1 + t ^ 3) ^ 2 := by
  unfold foliumOrientedArea
  have heq :
      (fun t : ℝ =>
          (foliumParam a t).1 * deriv (fun s => (foliumParam a s).2) t -
            (foliumParam a t).2 * deriv (fun s => (foliumParam a s).1) t) =ᵐ[
        volume.restrict (Set.Ici (0 : ℝ))]
        (fun t : ℝ => 9 * a ^ 2 * (t ^ 2 / (1 + t ^ 3) ^ 2)) := by
    filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ici] with t ht
    simpa [div_eq_mul_inv, mul_assoc] using gap4 a t ht
  rw [MeasureTheory.integral_congr_ae heq]
  rw [MeasureTheory.integral_const_mul]
  ring

theorem gap6 (a : ℝ) :
    9 * a ^ 2 / 2 *
        (∫ t in Set.Ici (0 : ℝ), t ^ 2 / (1 + t ^ 3) ^ 2) =
      0 - foliumPrimitive a 0 := by
  let F : ℝ → ℝ := fun t => -(1 / 3 : ℝ) / (1 + t ^ 3)
  let g : ℝ → ℝ := fun t => t ^ 2 / (1 + t ^ 3) ^ 2
  have hderiv : ∀ t ∈ Set.Ici (0 : ℝ), HasDerivAt F (g t) t := by
    intro t ht
    have ht0 : 0 ≤ t := ht
    have hden : 1 + t ^ 3 ≠ 0 := by
      have ht3 : 0 ≤ t ^ 3 := pow_nonneg ht0 3
      nlinarith
    have hdenDeriv :
        HasDerivAt (fun s : ℝ => 1 + s ^ 3) (3 * t ^ 2) t := by
      convert (hasDerivAt_const t (1 : ℝ)).add
        ((hasDerivAt_id t).pow 3) using 1 <;> simp [id_eq] <;> ring
    dsimp only [F, g]
    convert
      (hasDerivAt_const t (-(1 / 3 : ℝ))).div hdenDeriv hden using 1 <;>
      (try simp [id_eq]) <;>
      field_simp [hden] <;> ring
  have hpos : ∀ t ∈ Set.Ioi (0 : ℝ), 0 ≤ g t := by
    intro t ht
    dsimp only [g]
    positivity
  have hpow :
      Filter.Tendsto (fun t : ℝ => t ^ 3) Filter.atTop Filter.atTop :=
    Filter.tendsto_pow_atTop (by norm_num)
  have hden :
      Filter.Tendsto (fun t : ℝ => 1 + t ^ 3) Filter.atTop Filter.atTop := by
    exact Filter.tendsto_atTop_mono' _
      (Filter.Eventually.of_forall fun t => by linarith) hpow
  have hinv :
      Filter.Tendsto (fun t : ℝ => (1 + t ^ 3)⁻¹)
        Filter.atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp hden
  have hF :
      Filter.Tendsto F Filter.atTop (nhds 0) := by
    dsimp only [F]
    simpa [div_eq_mul_inv] using
      (tendsto_const_nhds.mul hinv :
        Filter.Tendsto
          (fun t : ℝ => (-(1 / 3 : ℝ)) * (1 + t ^ 3)⁻¹)
          Filter.atTop (nhds ((-(1 / 3 : ℝ)) * 0)))
  have hIoi :
      (∫ t in Set.Ioi (0 : ℝ), g t) = 0 - F 0 :=
    MeasureTheory.integral_Ioi_of_hasDerivAt_of_nonneg' hderiv hpos hF
  have hbase :
      (∫ t in Set.Ici (0 : ℝ), t ^ 2 / (1 + t ^ 3) ^ 2) = 1 / 3 := by
    change (∫ t in Set.Ici (0 : ℝ), g t) = 1 / 3
    rw [MeasureTheory.integral_Ici_eq_integral_Ioi, hIoi]
    norm_num [F]
  rw [hbase]
  norm_num [foliumPrimitive]
  ring

theorem gap7 (a : ℝ) :
    0 - foliumPrimitive a 0 = 3 * a ^ 2 / 2 := by
  norm_num [foliumPrimitive]

theorem gap8 (a : ℝ) (ha : 0 < a) :
    foliumOrientedArea a = 3 * a ^ 2 / 2 := by
  rw [gap5 a ha, gap6 a, gap7 a]

end

end ProofGap.Exercise4311
