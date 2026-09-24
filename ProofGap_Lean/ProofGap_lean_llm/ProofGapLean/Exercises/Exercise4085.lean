import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise4085

noncomputable section

open MeasureTheory
open scoped Interval

def cubeIntegral (f : ℝ → ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..1,
    ∫ y in (0 : ℝ)..1,
      ∫ z in (0 : ℝ)..x + y, f z

private theorem primitive_hasDerivAt
    (f : ℝ → ℝ) (hf : Continuous f) (a y : ℝ) :
    HasDerivAt (fun t : ℝ => ∫ z in a..t, f z) (f y) y := by
  apply intervalIntegral.integral_hasDerivAt_right
    (hf.intervalIntegrable a y)
  · exact hf.stronglyMeasurable.stronglyMeasurableAtFilter
  · exact hf.continuousAt

private theorem nested_interval_integral_eq_weighted
    (f : ℝ → ℝ) (hf : Continuous f) (a b : ℝ) :
    (∫ y in a..b, ∫ z in a..y, f z) =
      ∫ y in a..b, f y * (b - y) := by
  let F : ℝ → ℝ := fun y => ∫ z in a..y, f z
  have hF : ∀ y : ℝ, HasDerivAt F (f y) y := by
    intro y
    simpa [F] using primitive_hasDerivAt f hf a y
  have hFc : Continuous F :=
    continuous_iff_continuousAt.2 fun y => (hF y).continuousAt
  have hlin : Continuous (fun y : ℝ => b - y) :=
    continuous_const.sub continuous_id
  have hd : ∀ y : ℝ,
      HasDerivAt (fun z : ℝ => F z * (b - z))
        (f y * (b - y) - F y) y := by
    intro y
    have hsub : HasDerivAt (fun z : ℝ => b - z) (-1) y := by
      convert (hasDerivAt_const y b).sub (hasDerivAt_id y) using 1 <;> ring
    convert (hF y).mul hsub using 1 <;> ring
  have hcont : Continuous (fun y : ℝ => f y * (b - y) - F y) :=
    (hf.mul hlin).sub hFc
  have hzero :
      (∫ y in a..b, f y * (b - y) - F y) = 0 := by
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun y _ => hd y) (hcont.intervalIntegrable a b)
    simpa [F] using h
  have hw : IntervalIntegrable (fun y : ℝ => f y * (b - y)) volume a b :=
    (hf.mul hlin).intervalIntegrable a b
  have hFi : IntervalIntegrable F volume a b :=
    hFc.intervalIntegrable a b
  rw [intervalIntegral.integral_sub hw hFi] at hzero
  have heq :
      (∫ y in a..b, f y * (b - y)) = (∫ y in a..b, F y) :=
    sub_eq_zero.mp hzero
  simpa [F] using heq.symm

private theorem primitive_weighted_eq_square
    (f : ℝ → ℝ) (hf : Continuous f) (a b : ℝ) :
    (∫ y in a..b, (∫ z in a..y, f z) * (b - y)) =
      (1 / 2 : ℝ) * ∫ y in a..b, f y * (b - y) ^ 2 := by
  let F : ℝ → ℝ := fun y => ∫ z in a..y, f z
  have hF : ∀ y : ℝ, HasDerivAt F (f y) y := by
    intro y
    simpa [F] using primitive_hasDerivAt f hf a y
  have hFc : Continuous F :=
    continuous_iff_continuousAt.2 fun y => (hF y).continuousAt
  have hlin : Continuous (fun y : ℝ => b - y) :=
    continuous_const.sub continuous_id
  have hq : ∀ y : ℝ,
      HasDerivAt
        (fun z : ℝ => (1 / 2 : ℝ) * ((b - z) * (b - z)))
        (-(b - y)) y := by
    intro y
    have hs : HasDerivAt (fun z : ℝ => b - z) (-1) y := by
      convert (hasDerivAt_const y b).sub (hasDerivAt_id y) using 1 <;> ring
    convert ((hasDerivAt_const y (1 / 2 : ℝ)).mul (hs.mul hs)) using 1 <;> ring
  have hd : ∀ y : ℝ,
      HasDerivAt
        (fun z : ℝ =>
          F z * ((1 / 2 : ℝ) * ((b - z) * (b - z))))
        ((1 / 2 : ℝ) * (f y * (b - y) ^ 2) - F y * (b - y)) y := by
    intro y
    convert (hF y).mul (hq y) using 1 <;> ring
  have hhalf : Continuous
      (fun y : ℝ => (1 / 2 : ℝ) * (f y * (b - y) ^ 2)) :=
    continuous_const.mul (hf.mul (hlin.pow 2))
  have hprim : Continuous (fun y : ℝ => F y * (b - y)) :=
    hFc.mul hlin
  have hzero :
      (∫ y in a..b,
        (1 / 2 : ℝ) * (f y * (b - y) ^ 2) - F y * (b - y)) = 0 := by
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun y _ => hd y) ((hhalf.sub hprim).intervalIntegrable a b)
    simpa [F] using h
  have hhalfI : IntervalIntegrable
      (fun y : ℝ => (1 / 2 : ℝ) * (f y * (b - y) ^ 2)) volume a b :=
    hhalf.intervalIntegrable a b
  have hprimI : IntervalIntegrable
      (fun y : ℝ => F y * (b - y)) volume a b :=
    hprim.intervalIntegrable a b
  rw [intervalIntegral.integral_sub hhalfI hprimI] at hzero
  have heq := sub_eq_zero.mp hzero
  change (∫ y in a..b, F y * (b - y)) =
    (1 / 2 : ℝ) * ∫ y in a..b, f y * (b - y) ^ 2
  calc
    _ = ∫ y in a..b, (1 / 2 : ℝ) * (f y * (b - y) ^ 2) := heq.symm
    _ = _ := by rw [intervalIntegral.integral_const_mul]

private theorem tripleVolterra_eq_square_kernel
    (f : ℝ → ℝ) (hf : Continuous f) (x : ℝ) :
    (∫ xi in (0 : ℝ)..x,
      ∫ eta in (0 : ℝ)..xi,
        ∫ zeta in (0 : ℝ)..eta, f zeta) =
      (1 / 2 : ℝ) * ∫ z in (0 : ℝ)..x, f z * (x - z) ^ 2 := by
  let F : ℝ → ℝ := fun y => ∫ z in (0 : ℝ)..y, f z
  have hFc : Continuous F := by
    apply continuous_iff_continuousAt.2
    intro y
    exact (primitive_hasDerivAt f hf 0 y).continuousAt
  calc
    (∫ xi in (0 : ℝ)..x,
      ∫ eta in (0 : ℝ)..xi,
        ∫ zeta in (0 : ℝ)..eta, f zeta) =
        ∫ eta in (0 : ℝ)..x, F eta * (x - eta) := by
      exact nested_interval_integral_eq_weighted F hFc 0 x
    _ = _ := by
      simpa [F] using primitive_weighted_eq_square f hf 0 x

private theorem cubeIntegral_weighted (f : ℝ → ℝ) (hf : Continuous f) :
    cubeIntegral f =
      (1 / 2 * ∫ z in (0 : ℝ)..1, f z * (2 - z ^ 2)) +
        (1 / 2 * ∫ z in (1 : ℝ)..2, f z * (2 - z) ^ 2) := by
  let F : ℝ → ℝ := fun t => ∫ z in (0 : ℝ)..t, f z
  let G : ℝ → ℝ := fun t => ∫ y in (0 : ℝ)..t, F y
  have hFc : Continuous F := by
    apply continuous_iff_continuousAt.2
    intro y
    exact (primitive_hasDerivAt f hf 0 y).continuousAt
  have hGc : Continuous G := by
    apply continuous_iff_continuousAt.2
    intro y
    exact (primitive_hasDerivAt F hFc 0 y).continuousAt
  have hinner (x : ℝ) :
      (∫ y in (0 : ℝ)..1, F (x + y)) = G (x + 1) - G x := by
    have hshift :
        (∫ y in (0 : ℝ)..1, F (x + y)) = ∫ y in x..1 + x, F y := by
      simpa [add_comm] using
        (intervalIntegral.integral_comp_add_right F x (a := (0 : ℝ)) (b := 1))
    rw [hshift]
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (a := x) (b := 1 + x)
      (f := G) (f' := F)
      (fun y _ => by
        simpa [G] using primitive_hasDerivAt F hFc 0 y)
      (hFc.intervalIntegrable x (1 + x))
    simpa [add_comm] using h
  have hcube :
      cubeIntegral f =
        (∫ x in (0 : ℝ)..1, G (x + 1)) -
          ∫ x in (0 : ℝ)..1, G x := by
    unfold cubeIntegral
    change (∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1, F (x + y)) = _
    rw [show (∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1, F (x + y)) =
        ∫ x in (0 : ℝ)..1, (G (x + 1) - G x) by
      apply intervalIntegral.integral_congr
      intro x hx
      exact hinner x]
    have hshiftC : Continuous (fun x : ℝ => G (x + 1)) :=
      hGc.comp (continuous_id.add continuous_const)
    rw [intervalIntegral.integral_sub
      (hshiftC.intervalIntegrable 0 1)
      (hGc.intervalIntegrable 0 1)]
  have hshiftG :
      (∫ x in (0 : ℝ)..1, G (x + 1)) = ∫ x in (1 : ℝ)..2, G x := by
    calc
      (∫ x in (0 : ℝ)..1, G (x + 1)) =
          ∫ x in (0 : ℝ) + 1..1 + 1, G x :=
        intervalIntegral.integral_comp_add_right G 1
      _ = ∫ x in (1 : ℝ)..2, G x := by norm_num
  have hH (t : ℝ) :
      (∫ x in (0 : ℝ)..t, G x) =
        (1 / 2 : ℝ) * ∫ z in (0 : ℝ)..t, f z * (t - z) ^ 2 := by
    simpa [G, F] using tripleVolterra_eq_square_kernel f hf t
  have hsplitG :
      (∫ x in (1 : ℝ)..2, G x) =
        (∫ x in (0 : ℝ)..2, G x) - ∫ x in (0 : ℝ)..1, G x := by
    rw [← intervalIntegral.integral_add_adjacent_intervals
      (hGc.intervalIntegrable 0 1) (hGc.intervalIntegrable 1 2)]
    ring
  rw [hcube, hshiftG, hsplitG, hH 2, hH 1]
  have hsplit :
      (∫ z in (0 : ℝ)..2, f z * (2 - z) ^ 2) =
        (∫ z in (0 : ℝ)..1, f z * (2 - z) ^ 2) +
          ∫ z in (1 : ℝ)..2, f z * (2 - z) ^ 2 := by
    have hc : Continuous (fun z : ℝ => f z * (2 - z) ^ 2) :=
      hf.mul ((continuous_const.sub continuous_id).pow 2)
    exact (intervalIntegral.integral_add_adjacent_intervals
      (hc.intervalIntegrable (μ := volume) 0 1)
      (hc.intervalIntegrable (μ := volume) 1 2)).symm
  rw [hsplit]
  have hcombine :
      (∫ z in (0 : ℝ)..1, f z * (2 - z) ^ 2) -
          2 * ∫ z in (0 : ℝ)..1, f z * (1 - z) ^ 2 =
        ∫ z in (0 : ℝ)..1, f z * (2 - z ^ 2) := by
    rw [← intervalIntegral.integral_const_mul]
    have hc1 : Continuous (fun z : ℝ => f z * (2 - z) ^ 2) :=
      hf.mul ((continuous_const.sub continuous_id).pow 2)
    have hc2 : Continuous (fun z : ℝ =>
        (2 : ℝ) * (f z * (1 - z) ^ 2)) :=
      continuous_const.mul
        (hf.mul ((continuous_const.sub continuous_id).pow 2))
    rw [← intervalIntegral.integral_sub
      (hc1.intervalIntegrable 0 1) (hc2.intervalIntegrable 0 1)]
    apply intervalIntegral.integral_congr
    intro z hz
    ring
  rw [show
      (1 / 2 : ℝ) *
            ((∫ z in (0 : ℝ)..1, f z * (2 - z) ^ 2) +
              ∫ z in (1 : ℝ)..2, f z * (2 - z) ^ 2) -
          ((1 / 2 : ℝ) * ∫ z in (0 : ℝ)..1, f z * (1 - z) ^ 2) -
          (1 / 2 : ℝ) * ∫ z in (0 : ℝ)..1, f z * (1 - z) ^ 2 =
        (1 / 2 : ℝ) *
          ((∫ z in (0 : ℝ)..1, f z * (2 - z) ^ 2) -
            2 * ∫ z in (0 : ℝ)..1, f z * (1 - z) ^ 2) +
          (1 / 2 : ℝ) * ∫ z in (1 : ℝ)..2, f z * (2 - z) ^ 2 by ring]
  rw [hcombine]

theorem gap1 (f : ℝ → ℝ) (hf : Continuous f) :
    cubeIntegral f =
      (∫ z in (0 : ℝ)..1,
        ∫ x in z..1,
          ∫ y in (0 : ℝ)..1, f z) +
      (∫ z in (0 : ℝ)..1,
        ∫ x in (0 : ℝ)..z,
          ∫ y in z - x..1, f z) +
      ∫ z in (1 : ℝ)..2,
        ∫ x in z - 1..1,
          ∫ y in z - x..1, f z := by
  rw [cubeIntegral_weighted f hf]
  have hfirst :
      (∫ z in (0 : ℝ)..1,
        ∫ x in z..1,
          ∫ y in (0 : ℝ)..1, f z) =
      ∫ z in (0 : ℝ)..1, f z * (1 - z) := by
    apply intervalIntegral.integral_congr
    intro z hz
    simp only [intervalIntegral.integral_const, smul_eq_mul]
    ring
  have hsecond :
      (∫ z in (0 : ℝ)..1,
        ∫ x in (0 : ℝ)..z,
          ∫ y in z - x..1, f z) =
      ∫ z in (0 : ℝ)..1, f z * (z - z ^ 2 / 2) := by
    apply intervalIntegral.integral_congr
    intro z hz
    simp_rw [intervalIntegral.integral_const, smul_eq_mul]
    have hpoly :
        (∫ x in (0 : ℝ)..z, (1 - (z - x)) * f z) =
          f z * (z - z ^ 2 / 2) := by
      rw [show (fun x : ℝ => (1 - (z - x)) * f z) =
          fun x => (f z * (1 - z)) + f z * x by
        funext x
        ring]
      have hc1 : Continuous (fun _ : ℝ => f z * (1 - z)) := continuous_const
      have hc2 : Continuous (fun x : ℝ => f z * x) :=
        continuous_const.mul continuous_id
      rw [intervalIntegral.integral_add
        (hc1.intervalIntegrable 0 z) (hc2.intervalIntegrable 0 z)]
      rw [intervalIntegral.integral_const, intervalIntegral.integral_const_mul,
        integral_id]
      simp only [smul_eq_mul]
      ring
    exact hpoly
  have hthird :
      (∫ z in (1 : ℝ)..2,
        ∫ x in z - 1..1,
          ∫ y in z - x..1, f z) =
      1 / 2 * ∫ z in (1 : ℝ)..2, f z * (2 - z) ^ 2 := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro z hz
    simp_rw [intervalIntegral.integral_const, smul_eq_mul]
    rw [show (fun x : ℝ => (1 - (z - x)) * f z) =
        fun x => f z * (x - (z - 1)) by
      funext x
      ring]
    rw [intervalIntegral.integral_const_mul]
    have hlin :
        (∫ x in z - 1..1, x - (z - 1)) =
          (1 / 2 : ℝ) * (2 - z) ^ 2 := by
      have hderiv : ∀ x : ℝ,
          HasDerivAt
            (fun t : ℝ => (1 / 2 : ℝ) * (t - (z - 1)) ^ 2)
            (x - (z - 1)) x := by
        intro x
        convert
          ((hasDerivAt_id x).sub_const (z - 1)).pow 2 |>.const_mul (1 / 2 : ℝ)
          using 1 <;> simp only [id_eq] <;> ring
      have hc : Continuous (fun x : ℝ => x - (z - 1)) :=
        continuous_id.sub continuous_const
      have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun x _ => hderiv x)
        (hc.intervalIntegrable (μ := volume) (z - 1) 1)
      convert h using 1 <;> ring
    rw [hlin]
    ring
  rw [hfirst, hsecond, hthird]
  have hsum :
      (∫ z in (0 : ℝ)..1, f z * (1 - z)) +
          ∫ z in (0 : ℝ)..1, f z * (z - z ^ 2 / 2) =
        1 / 2 * ∫ z in (0 : ℝ)..1, f z * (2 - z ^ 2) := by
    have hc1 : Continuous (fun z : ℝ => f z * (1 - z)) :=
      hf.mul (continuous_const.sub continuous_id)
    have hc2 : Continuous (fun z : ℝ => f z * (z - z ^ 2 / 2)) :=
      hf.mul (continuous_id.sub ((continuous_id.pow 2).div_const 2))
    rw [← intervalIntegral.integral_add
      (hc1.intervalIntegrable 0 1) (hc2.intervalIntegrable 0 1)]
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro z hz
    ring
  rw [hsum]

theorem gap2 (f : ℝ → ℝ) (hf : Continuous f) :
    (∫ z in (0 : ℝ)..1,
        ∫ x in z..1, f z) +
      (∫ z in (0 : ℝ)..1,
        ∫ x in (0 : ℝ)..z, f z * (1 - z + x)) =
      ∫ z in (0 : ℝ)..1, f z * (1 - z ^ 2 / 2) := by
  have hfirst (z : ℝ) :
      (∫ x in z..1, f z) = f z * (1 - z) := by
    rw [intervalIntegral.integral_const]
    simp only [smul_eq_mul]
    ring
  have hsecond (z : ℝ) :
      (∫ x in (0 : ℝ)..z, f z * (1 - z + x)) =
        f z * (z - z ^ 2 / 2) := by
    rw [show (fun x : ℝ => f z * (1 - z + x)) =
        fun x => f z * (1 - z) + f z * x by
      funext x
      ring]
    have hc1 : Continuous (fun _ : ℝ => f z * (1 - z)) := continuous_const
    have hc2 : Continuous (fun x : ℝ => f z * x) :=
      continuous_const.mul continuous_id
    rw [intervalIntegral.integral_add
      (hc1.intervalIntegrable 0 z) (hc2.intervalIntegrable 0 z)]
    rw [intervalIntegral.integral_const, intervalIntegral.integral_const_mul,
      integral_id]
    simp only [smul_eq_mul]
    ring
  simp_rw [hfirst, hsecond]
  have hc1 : Continuous (fun z : ℝ => f z * (1 - z)) :=
    hf.mul (continuous_const.sub continuous_id)
  have hc2 : Continuous (fun z : ℝ => f z * (z - z ^ 2 / 2)) :=
    hf.mul (continuous_id.sub ((continuous_id.pow 2).div_const 2))
  rw [← intervalIntegral.integral_add
    (hc1.intervalIntegrable 0 1) (hc2.intervalIntegrable 0 1)]
  apply intervalIntegral.integral_congr
  intro z hz
  ring

theorem gap3 (f : ℝ → ℝ) (hf : Continuous f) :
    (∫ z in (1 : ℝ)..2,
        ∫ x in z - 1..1, f z * (1 - z + x)) =
      1 / 2 * ∫ z in (1 : ℝ)..2, f z * (z - 2) ^ 2 := by
  have hlin (z : ℝ) :
      (∫ x in z - 1..1, x - (z - 1)) =
        (1 / 2 : ℝ) * (z - 2) ^ 2 := by
    have hderiv : ∀ x : ℝ,
        HasDerivAt
          (fun t : ℝ => (1 / 2 : ℝ) * (t - (z - 1)) ^ 2)
          (x - (z - 1)) x := by
      intro x
      convert
        ((hasDerivAt_id x).sub_const (z - 1)).pow 2 |>.const_mul (1 / 2 : ℝ)
        using 1 <;> simp only [id_eq] <;> ring
    have hc : Continuous (fun x : ℝ => x - (z - 1)) :=
      continuous_id.sub continuous_const
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x _ => hderiv x)
      (hc.intervalIntegrable (μ := volume) (z - 1) 1)
    convert h using 1 <;> ring
  have hinner (z : ℝ) :
      (∫ x in z - 1..1, f z * (1 - z + x)) =
        (1 / 2 : ℝ) * (f z * (z - 2) ^ 2) := by
    rw [show (fun x : ℝ => f z * (1 - z + x)) =
        fun x => f z * (x - (z - 1)) by
      funext x
      ring]
    rw [intervalIntegral.integral_const_mul, hlin z]
    ring
  simp_rw [hinner]
  rw [intervalIntegral.integral_const_mul]

theorem gap4 (f : ℝ → ℝ) (hf : Continuous f) :
    cubeIntegral f =
      (1 / 2 * ∫ z in (0 : ℝ)..1, f z * (2 - z ^ 2)) +
        (1 / 2 * ∫ z in (1 : ℝ)..2, f z * (2 - z) ^ 2) := by
  exact cubeIntegral_weighted f hf

end

end ProofGap.Exercise4085
