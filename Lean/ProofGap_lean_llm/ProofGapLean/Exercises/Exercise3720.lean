import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Order.OrderClosed

namespace ProofGap.Exercise3720

noncomputable section

open scoped Interval

def integralFunction (a b : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ y in a..b, f y * |x - y|

def splitIntegral (a b : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  (∫ y in a..x, (x - y) * f y) +
    ∫ y in x..b, (y - x) * f y

def firstDerivative (a b : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  (∫ y in a..x, f y) + ∫ y in b..x, f y

def secondDerivative (a b : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  deriv (deriv (integralFunction a b f)) x

private theorem integralFunction_forms (a b : ℝ) (f : ℝ → ℝ) (hab : a < b)
    (hf : Differentiable ℝ f) :
    (∀ x ∈ Set.Ioo a b,
      integralFunction a b f x = splitIntegral a b f x) ∧
    (∀ z : ℝ,
      splitIntegral a b f z =
        z * (∫ y in a..z, f y) - (∫ y in a..z, y * f y) +
          (z * (∫ y in b..z, f y) - (∫ y in b..z, y * f y))) ∧
    (∀ z : ℝ, z < a →
      integralFunction a b f z =
        (∫ y in a..b, y * f y) - z * (∫ y in a..b, f y)) ∧
    (∀ z : ℝ, b < z →
      integralFunction a b f z =
        z * (∫ y in a..b, f y) - (∫ y in a..b, y * f y)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx
    have hcont : Continuous (fun y : ℝ => f y * |x - y|) :=
      hf.continuous.mul ((continuous_const.sub continuous_id).abs)
    have hleft :
        (∫ y in a..x, f y * |x - y|) =
          ∫ y in a..x, (x - y) * f y := by
      apply intervalIntegral.integral_congr
      intro y hy
      have hyx : y ≤ x := by
        rcases Set.mem_uIcc.mp hy with hy | hy
        · exact hy.2
        · linarith [hx.1]
      change f y * |x - y| = (x - y) * f y
      rw [abs_of_nonneg (sub_nonneg.mpr hyx)]
      ring
    have hright :
        (∫ y in x..b, f y * |x - y|) =
          ∫ y in x..b, (y - x) * f y := by
      apply intervalIntegral.integral_congr
      intro y hy
      have hxy : x ≤ y := by
        rcases Set.mem_uIcc.mp hy with hy | hy
        · exact hy.1
        · linarith [hx.2]
      change f y * |x - y| = (y - x) * f y
      rw [abs_of_nonpos (sub_nonpos.mpr hxy)]
      ring
    unfold integralFunction splitIntegral
    calc
      (∫ y in a..b, f y * |x - y|) =
          (∫ y in a..x, f y * |x - y|) +
            ∫ y in x..b, f y * |x - y| :=
        (intervalIntegral.integral_add_adjacent_intervals
          (hcont.intervalIntegrable a x)
          (hcont.intervalIntegrable x b)).symm
      _ = (∫ y in a..x, (x - y) * f y) +
            ∫ y in x..b, (y - x) * f y := by rw [hleft, hright]
  · intro z
    have hzf_az : IntervalIntegrable (fun y : ℝ => z * f y) MeasureTheory.volume a z :=
      (continuous_const.mul hf.continuous).intervalIntegrable a z
    have hyf_az : IntervalIntegrable (fun y : ℝ => y * f y) MeasureTheory.volume a z :=
      (continuous_id.mul hf.continuous).intervalIntegrable a z
    have hfirst :
        (∫ y in a..z, (z - y) * f y) =
          z * (∫ y in a..z, f y) - (∫ y in a..z, y * f y) := by
      calc
        (∫ y in a..z, (z - y) * f y) =
            ∫ y in a..z, z * f y - y * f y := by
          apply intervalIntegral.integral_congr
          intro y hy
          change (z - y) * f y = z * f y - y * f y
          ring
        _ = (∫ y in a..z, z * f y) - (∫ y in a..z, y * f y) :=
          intervalIntegral.integral_sub hzf_az hyf_az
        _ = z * (∫ y in a..z, f y) - (∫ y in a..z, y * f y) := by
          rw [intervalIntegral.integral_const_mul]
    have hrev :
        (∫ y in z..b, (y - z) * f y) =
          ∫ y in b..z, (z - y) * f y := by
      rw [intervalIntegral.integral_symm]
      rw [← intervalIntegral.integral_neg]
      apply intervalIntegral.integral_congr
      intro y hy
      change -((y - z) * f y) = (z - y) * f y
      ring
    have hzf_bz : IntervalIntegrable (fun y : ℝ => z * f y) MeasureTheory.volume b z :=
      (continuous_const.mul hf.continuous).intervalIntegrable b z
    have hyf_bz : IntervalIntegrable (fun y : ℝ => y * f y) MeasureTheory.volume b z :=
      (continuous_id.mul hf.continuous).intervalIntegrable b z
    have hsecond :
        (∫ y in b..z, (z - y) * f y) =
          z * (∫ y in b..z, f y) - (∫ y in b..z, y * f y) := by
      calc
        (∫ y in b..z, (z - y) * f y) =
            ∫ y in b..z, z * f y - y * f y := by
          apply intervalIntegral.integral_congr
          intro y hy
          change (z - y) * f y = z * f y - y * f y
          ring
        _ = (∫ y in b..z, z * f y) - (∫ y in b..z, y * f y) :=
          intervalIntegral.integral_sub hzf_bz hyf_bz
        _ = z * (∫ y in b..z, f y) - (∫ y in b..z, y * f y) := by
          rw [intervalIntegral.integral_const_mul]
    unfold splitIntegral
    rw [hfirst, hrev, hsecond]
  · intro z hz
    have hyf : IntervalIntegrable (fun y : ℝ => y * f y) MeasureTheory.volume a b :=
      (continuous_id.mul hf.continuous).intervalIntegrable a b
    have hzf : IntervalIntegrable (fun y : ℝ => z * f y) MeasureTheory.volume a b :=
      (continuous_const.mul hf.continuous).intervalIntegrable a b
    unfold integralFunction
    calc
      (∫ y in a..b, f y * |z - y|) =
          ∫ y in a..b, y * f y - z * f y := by
        apply intervalIntegral.integral_congr
        intro y hy
        have hay : a ≤ y := by
          rcases Set.mem_uIcc.mp hy with hy | hy
          · exact hy.1
          · linarith [hab]
        change f y * |z - y| = y * f y - z * f y
        rw [abs_of_nonpos (by linarith : z - y ≤ 0)]
        ring
      _ = (∫ y in a..b, y * f y) - (∫ y in a..b, z * f y) :=
        intervalIntegral.integral_sub hyf hzf
      _ = (∫ y in a..b, y * f y) - z * (∫ y in a..b, f y) := by
        rw [intervalIntegral.integral_const_mul]
  · intro z hz
    have hzf : IntervalIntegrable (fun y : ℝ => z * f y) MeasureTheory.volume a b :=
      (continuous_const.mul hf.continuous).intervalIntegrable a b
    have hyf : IntervalIntegrable (fun y : ℝ => y * f y) MeasureTheory.volume a b :=
      (continuous_id.mul hf.continuous).intervalIntegrable a b
    unfold integralFunction
    calc
      (∫ y in a..b, f y * |z - y|) =
          ∫ y in a..b, z * f y - y * f y := by
        apply intervalIntegral.integral_congr
        intro y hy
        have hyb : y ≤ b := by
          rcases Set.mem_uIcc.mp hy with hy | hy
          · exact hy.2
          · linarith [hab]
        change f y * |z - y| = z * f y - y * f y
        rw [abs_of_nonneg (by linarith : 0 ≤ z - y)]
        ring
      _ = (∫ y in a..b, z * f y) - (∫ y in a..b, y * f y) :=
        intervalIntegral.integral_sub hzf hyf
      _ = z * (∫ y in a..b, f y) - (∫ y in a..b, y * f y) := by
        rw [intervalIntegral.integral_const_mul]

theorem gap1 (a b : ℝ) (f : ℝ → ℝ) (hab : a < b)
    (hf : Differentiable ℝ f) :
    ∀ x ∈ Set.Ioo a b,
      integralFunction a b f x = splitIntegral a b f x := by
  intro x hx
  exact (integralFunction_forms a b f hab hf).1 x hx

theorem gap2 (a b : ℝ) (f : ℝ → ℝ) (hab : a < b)
    (hf : Differentiable ℝ f) :
    ∀ x ∈ Set.Ioo a b,
      deriv (integralFunction a b f) x = firstDerivative a b f x := by
  intro x hx
  have hforms := integralFunction_forms a b f hab hf
  have heq :
      integralFunction a b f =ᶠ[nhds x]
        (fun z : ℝ =>
          z * (∫ y in a..z, f y) - (∫ y in a..z, y * f y) +
            (z * (∫ y in b..z, f y) - (∫ y in b..z, y * f y))) :=
    Filter.mem_of_superset (Ioo_mem_nhds hx.1 hx.2) (fun z hz =>
      (hforms.1 z hz).trans (hforms.2.1 z))
  have hyf_cont : Continuous (fun y : ℝ => y * f y) :=
    continuous_id.mul hf.continuous
  have hFa : HasDerivAt (fun z : ℝ => ∫ y in a..z, f y) (f x) x :=
    intervalIntegral.integral_hasDerivAt_right
      (hf.continuous.intervalIntegrable a x)
      hf.continuous.stronglyMeasurable.stronglyMeasurableAtFilter
      hf.continuous.continuousAt
  have hYa : HasDerivAt (fun z : ℝ => ∫ y in a..z, y * f y) (x * f x) x :=
    intervalIntegral.integral_hasDerivAt_right
      (hyf_cont.intervalIntegrable a x)
      hyf_cont.stronglyMeasurable.stronglyMeasurableAtFilter
      hyf_cont.continuousAt
  have hFb : HasDerivAt (fun z : ℝ => ∫ y in b..z, f y) (f x) x :=
    intervalIntegral.integral_hasDerivAt_right
      (hf.continuous.intervalIntegrable b x)
      hf.continuous.stronglyMeasurable.stronglyMeasurableAtFilter
      hf.continuous.continuousAt
  have hYb : HasDerivAt (fun z : ℝ => ∫ y in b..z, y * f y) (x * f x) x :=
    intervalIntegral.integral_hasDerivAt_right
      (hyf_cont.intervalIntegrable b x)
      hyf_cont.stronglyMeasurable.stronglyMeasurableAtFilter
      hyf_cont.continuousAt
  have hS : HasDerivAt
      (fun z : ℝ =>
        z * (∫ y in a..z, f y) - (∫ y in a..z, y * f y) +
          (z * (∫ y in b..z, f y) - (∫ y in b..z, y * f y)))
      (firstDerivative a b f x) x := by
    convert (((hasDerivAt_id x).mul hFa).sub hYa).add
      (((hasDerivAt_id x).mul hFb).sub hYb) using 1 <;>
      simp [firstDerivative] <;> ring
  calc
    deriv (integralFunction a b f) x =
        deriv
          (fun z : ℝ =>
            z * (∫ y in a..z, f y) - (∫ y in a..z, y * f y) +
              (z * (∫ y in b..z, f y) - (∫ y in b..z, y * f y))) x :=
      heq.deriv_eq
    _ = firstDerivative a b f x := hS.deriv

theorem gap3 (a b : ℝ) (f : ℝ → ℝ) (hab : a < b)
    (hf : Differentiable ℝ f) :
    ∀ x ∈ Set.Ioo a b,
      secondDerivative a b f x = f x + f x := by
  intro x hx
  have heq :
      (fun z : ℝ => deriv (integralFunction a b f) z) =ᶠ[nhds x]
        firstDerivative a b f :=
    Filter.mem_of_superset (Ioo_mem_nhds hx.1 hx.2)
      (fun z hz => gap2 a b f hab hf z hz)
  have hFa : HasDerivAt (fun z : ℝ => ∫ y in a..z, f y) (f x) x :=
    intervalIntegral.integral_hasDerivAt_right
      (hf.continuous.intervalIntegrable a x)
      hf.continuous.stronglyMeasurable.stronglyMeasurableAtFilter
      hf.continuous.continuousAt
  have hFb : HasDerivAt (fun z : ℝ => ∫ y in b..z, f y) (f x) x :=
    intervalIntegral.integral_hasDerivAt_right
      (hf.continuous.intervalIntegrable b x)
      hf.continuous.stronglyMeasurable.stronglyMeasurableAtFilter
      hf.continuous.continuousAt
  have hfirst : HasDerivAt (firstDerivative a b f) (f x + f x) x := by
    simpa [firstDerivative] using hFa.add hFb
  unfold secondDerivative
  calc
    deriv (deriv (integralFunction a b f)) x =
        deriv (firstDerivative a b f) x := heq.deriv_eq
    _ = f x + f x := hfirst.deriv

theorem gap4 (a b : ℝ) (f : ℝ → ℝ) (hab : a < b)
    (hf : Differentiable ℝ f) :
    ∀ x ∈ Set.Ioo a b, f x + f x = 2 * f x := by
  intro x hx
  ring

theorem gap5 (a b : ℝ) (f : ℝ → ℝ) (hab : a < b)
    (hf : Differentiable ℝ f) :
    ∀ x ∈ Set.Ioo a b,
      secondDerivative a b f x = 2 * f x := by
  intro x hx
  calc
    secondDerivative a b f x = f x + f x := gap3 a b f hab hf x hx
    _ = 2 * f x := gap4 a b f hab hf x hx

theorem gap6 (a b : ℝ) (f : ℝ → ℝ) (hab : a < b)
    (hf : Differentiable ℝ f) :
    ∀ x : ℝ, x < a ∨ b < x →
      secondDerivative a b f x = 0 := by
  intro x hx
  have hforms := integralFunction_forms a b f hab hf
  rcases hx with hx | hx
  · let C : ℝ := ∫ y in a..b, y * f y
    let D : ℝ := ∫ y in a..b, f y
    have hderiv :
        (fun z : ℝ => deriv (integralFunction a b f) z) =ᶠ[nhds x]
          (fun _ : ℝ => -D) :=
      Filter.mem_of_superset (Iio_mem_nhds hx) (fun z hz => by
        have heqz :
            integralFunction a b f =ᶠ[nhds z] (fun w : ℝ => C - w * D) :=
          Filter.mem_of_superset (Iio_mem_nhds hz) (fun w hw => by
            simpa [C, D] using hforms.2.2.1 w hw)
        have haff : HasDerivAt (fun w : ℝ => C - w * D) (-D) z := by
          convert (hasDerivAt_const (x := z) C).sub
            ((hasDerivAt_id z).mul_const D) using 1 <;> ring
        calc
          deriv (integralFunction a b f) z =
              deriv (fun w : ℝ => C - w * D) z := heqz.deriv_eq
          _ = -D := haff.deriv)
    unfold secondDerivative
    calc
      deriv (deriv (integralFunction a b f)) x =
          deriv (fun _ : ℝ => -D) x := hderiv.deriv_eq
      _ = 0 := (hasDerivAt_const (x := x) (-D)).deriv
  · let C : ℝ := ∫ y in a..b, y * f y
    let D : ℝ := ∫ y in a..b, f y
    have hderiv :
        (fun z : ℝ => deriv (integralFunction a b f) z) =ᶠ[nhds x]
          (fun _ : ℝ => D) :=
      Filter.mem_of_superset (Ioi_mem_nhds hx) (fun z hz => by
        have heqz :
            integralFunction a b f =ᶠ[nhds z] (fun w : ℝ => w * D - C) :=
          Filter.mem_of_superset (Ioi_mem_nhds hz) (fun w hw => by
            simpa [C, D] using hforms.2.2.2 w hw)
        have haff : HasDerivAt (fun w : ℝ => w * D - C) D z := by
          convert ((hasDerivAt_id z).mul_const D).sub
            (hasDerivAt_const (x := z) C) using 1 <;> ring
        calc
          deriv (integralFunction a b f) z =
              deriv (fun w : ℝ => w * D - C) z := heqz.deriv_eq
          _ = D := haff.deriv)
    unfold secondDerivative
    calc
      deriv (deriv (integralFunction a b f)) x =
          deriv (fun _ : ℝ => D) x := hderiv.deriv_eq
      _ = 0 := (hasDerivAt_const (x := x) D).deriv

theorem gap7 (a b : ℝ) (f : ℝ → ℝ) (hab : a < b)
    (hf : Differentiable ℝ f) :
    ∀ x : ℝ, x ≠ a → x ≠ b →
      secondDerivative a b f x =
        if x ∈ Set.Ioo a b then 2 * f x else 0 := by
  intro x hxa hxb
  by_cases hx : x ∈ Set.Ioo a b
  · rw [if_pos hx]
    exact gap5 a b f hab hf x hx
  · rw [if_neg hx]
    apply gap6 a b f hab hf x
    by_cases hleft : x < a
    · exact Or.inl hleft
    · right
      have hax : a < x :=
        lt_of_le_of_ne (le_of_not_gt hleft) (Ne.symm hxa)
      by_contra hright
      have hle : x ≤ b := le_of_not_gt hright
      have hlt : x < b := lt_of_le_of_ne hle hxb
      exact hx ⟨hax, hlt⟩

end

end ProofGap.Exercise3720
