import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise3997

noncomputable section

open MeasureTheory
open scoped Interval

local instance : Measure.IsAddHaarMeasure volume (G := ℝ × ℝ) :=
  Measure.prod.instIsAddHaarMeasure _ _

def region (a : ℝ) : Set (ℝ × ℝ) :=
  {p |
    a ^ 2 ≤ p.1 * p.2 ∧ p.1 * p.2 ≤ 2 * a ^ 2 ∧
      p.1 ≤ p.2 ∧ p.2 ≤ 2 * p.1 ∧
      0 < p.1 ∧ 0 < p.2}

def regionArea (a : ℝ) : ℝ :=
  ∫ _p in region a, (1 : ℝ)

def jacobianDet (v : ℝ) : ℝ :=
  1 / (2 * v)

private def rg (a : ℝ) : Set (ℝ × ℝ) :=
  region a

private def fm (z : ℝ × ℝ) : ℝ × ℝ :=
  (z.1 * z.2, z.2 / z.1)

private def fd (x y : ℝ) : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
  (Matrix.toLin (.finTwoProd ℝ) (.finTwoProd ℝ)
    !![y, x; -y / x ^ 2, 1 / x]).toContinuousLinearMap

private def rect (a : ℝ) : Set (ℝ × ℝ) :=
  Set.Icc (a ^ 2) (2 * a ^ 2) ×ˢ Set.Icc (1 : ℝ) 2

private def invm (z : ℝ × ℝ) : ℝ × ℝ :=
  (Real.exp ((Real.log z.1 - Real.log z.2) / 2),
    Real.exp ((Real.log z.1 + Real.log z.2) / 2))

private theorem fm_invm (u v : ℝ) (hu : 0 < u) (hv : 0 < v) :
    fm (invm (u, v)) = (u, v) := by
  have hxne :
      Real.exp ((Real.log u - Real.log v) / 2) ≠ 0 :=
    Real.exp_ne_zero _
  ext
  · change
      Real.exp ((Real.log u - Real.log v) / 2) *
          Real.exp ((Real.log u + Real.log v) / 2) = u
    rw [← Real.exp_add]
    calc
      Real.exp
          ((Real.log u - Real.log v) / 2 +
            (Real.log u + Real.log v) / 2) =
          Real.exp (Real.log u) := by
        congr 1
        ring
      _ = u := Real.exp_log hu
  · change
      Real.exp ((Real.log u + Real.log v) / 2) /
          Real.exp ((Real.log u - Real.log v) / 2) = v
    rw [div_eq_iff hxne]
    calc
      Real.exp ((Real.log u + Real.log v) / 2) =
          Real.exp
            (Real.log v + (Real.log u - Real.log v) / 2) := by
        congr 1
        ring
      _ =
          v * Real.exp ((Real.log u - Real.log v) / 2) := by
        rw [Real.exp_add, Real.exp_log hv]

private theorem rg_meas (a : ℝ) : MeasurableSet (rg a) := by
  unfold rg region
  exact
    (measurableSet_le measurable_const (measurable_fst.mul measurable_snd)).inter
      ((measurableSet_le (measurable_fst.mul measurable_snd) measurable_const).inter
        ((measurableSet_le measurable_fst measurable_snd).inter
          ((measurableSet_le measurable_snd (measurable_const.mul measurable_fst)).inter
            ((measurableSet_lt measurable_const measurable_fst).inter
              (measurableSet_lt measurable_const measurable_snd)))))

private theorem fm_inj (a : ℝ) : Set.InjOn fm (rg a) := by
  intro z hz w hw h
  change
    a ^ 2 ≤ z.1 * z.2 ∧ z.1 * z.2 ≤ 2 * a ^ 2 ∧
      z.1 ≤ z.2 ∧ z.2 ≤ 2 * z.1 ∧ 0 < z.1 ∧ 0 < z.2 at hz
  change
    a ^ 2 ≤ w.1 * w.2 ∧ w.1 * w.2 ≤ 2 * a ^ 2 ∧
      w.1 ≤ w.2 ∧ w.2 ≤ 2 * w.1 ∧ 0 < w.1 ∧ 0 < w.2 at hw
  have h₁ := congrArg Prod.fst h
  have h₂ := congrArg Prod.snd h
  change z.1 * z.2 = w.1 * w.2 at h₁
  change z.2 / z.1 = w.2 / w.1 at h₂
  have hz1 : z.1 ≠ 0 := hz.2.2.2.2.1.ne'
  have hw1 : w.1 ≠ 0 := hw.2.2.2.2.1.ne'
  have hsquares : z.1 ^ 2 = w.1 ^ 2 := by
    have hp :
        (z.1 * z.2) / (z.2 / z.1) =
          (w.1 * w.2) / (w.2 / w.1) := by
      rw [h₁, h₂]
    field_simp [hz1, hw1, hz.2.2.2.2.2.ne', hw.2.2.2.2.2.ne'] at hp
    nlinarith
  have hx : z.1 = w.1 := by
    nlinarith [hz.2.2.2.2.1, hw.2.2.2.2.1]
  ext
  · exact hx
  · rw [hx] at h₁
    exact (mul_left_cancel₀ hw1 h₁)

private theorem fm_image (a : ℝ) (ha : a ≠ 0) :
    fm '' rg a = rect a := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    change
      a ^ 2 ≤ w.1 * w.2 ∧ w.1 * w.2 ≤ 2 * a ^ 2 ∧
        w.1 ≤ w.2 ∧ w.2 ≤ 2 * w.1 ∧ 0 < w.1 ∧ 0 < w.2 at hw
    have hx : 0 < w.1 := hw.2.2.2.2.1
    exact
      ⟨⟨hw.1, hw.2.1⟩,
        ⟨(le_div_iff₀ hx).2 (by simpa using hw.2.2.1),
          (div_le_iff₀ hx).2 hw.2.2.2.1⟩⟩
  · intro hz
    change
      z.1 ∈ Set.Icc (a ^ 2) (2 * a ^ 2) ∧
        z.2 ∈ Set.Icc (1 : ℝ) 2 at hz
    have hu : 0 < z.1 :=
      lt_of_lt_of_le (sq_pos_of_ne_zero ha) hz.1.1
    have hv : 0 < z.2 := lt_of_lt_of_le zero_lt_one hz.2.1
    refine ⟨invm z, ?_, ?_⟩
    · have hfi : fm (invm z) = z := by
        rcases z with ⟨u, v⟩
        exact fm_invm u v hu hv
      have hxpos : 0 < (invm z).1 := Real.exp_pos _
      have hypos : 0 < (invm z).2 := Real.exp_pos _
      change
        a ^ 2 ≤ (invm z).1 * (invm z).2 ∧
          (invm z).1 * (invm z).2 ≤ 2 * a ^ 2 ∧
          (invm z).1 ≤ (invm z).2 ∧
          (invm z).2 ≤ 2 * (invm z).1 ∧
          0 < (invm z).1 ∧ 0 < (invm z).2
      have hprod := congrArg Prod.fst hfi
      have hquot := congrArg Prod.snd hfi
      change (invm z).1 * (invm z).2 = z.1 at hprod
      change (invm z).2 / (invm z).1 = z.2 at hquot
      refine ⟨?_, ?_, ?_, ?_, hxpos, hypos⟩
      · rw [hprod]
        exact hz.1.1
      · rw [hprod]
        exact hz.1.2
      · have hratio : 1 ≤ (invm z).2 / (invm z).1 := by
          rw [hquot]
          exact hz.2.1
        have := (le_div_iff₀ hxpos).1 hratio
        simpa using this
      · have hratio : (invm z).2 / (invm z).1 ≤ 2 := by
          rw [hquot]
          exact hz.2.2
        exact (div_le_iff₀ hxpos).1 hratio
    · rcases z with ⟨u, v⟩
      exact fm_invm u v hu hv

private theorem fm_deriv (x y : ℝ) (hx : x ≠ 0) :
    HasFDerivAt fm (fd x y) (x, y) := by
  have hfst :
      HasFDerivAt (fun z : ℝ × ℝ => z.1)
        (ContinuousLinearMap.fst ℝ ℝ ℝ) (x, y) :=
    hasFDerivAt_fst
  have hsnd :
      HasFDerivAt (fun z : ℝ × ℝ => z.2)
        (ContinuousLinearMap.snd ℝ ℝ ℝ) (x, y) :=
    hasFDerivAt_snd
  have hfst_inv := (hasFDerivAt_inv hx).comp (x, y) hfst
  have hp := hfst.mul hsnd
  have hq := hsnd.mul hfst_inv
  unfold fm fd
  convert hp.prodMk hq using 1 <;>
    ext <;>
    simp [Matrix.toLin_finTwoProd_toContinuousLinearMap] <;>
    field_simp [hx] <;>
    ring

private theorem fd_det (x y : ℝ) (hx : x ≠ 0) :
    (fd x y).det = 2 * (y / x) := by
  unfold fd
  rw [LinearMap.det_toContinuousLinearMap, LinearMap.det_toLin,
    Matrix.det_fin_two_of]
  field_simp [hx]
  ring

private theorem int_Icc_int {a b : ℝ} (hab : a ≤ b) (f : ℝ → ℝ) :
    (∫ x in Set.Icc a b, f x) = ∫ x in a..b, f x := by
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
    intervalIntegral.integral_of_le hab]

private theorem regionArea_nonzero (a : ℝ) (ha : a ≠ 0) :
    regionArea a =
      1 / 2 *
        ∫ u in a ^ 2..2 * a ^ 2,
          ∫ v in (1 : ℝ)..2, 1 / v := by
  unfold regionArea
  change
    (∫ _z in rg a, (1 : ℝ)) =
      1 / 2 *
        ∫ u in a ^ 2..2 * a ^ 2,
          ∫ v in (1 : ℝ)..2, 1 / v
  have hd :
      ∀ z ∈ rg a, HasFDerivWithinAt fm (fd z.1 z.2) (rg a) z := by
    intro z hz
    change
      a ^ 2 ≤ z.1 * z.2 ∧ z.1 * z.2 ≤ 2 * a ^ 2 ∧
        z.1 ≤ z.2 ∧ z.2 ≤ 2 * z.1 ∧ 0 < z.1 ∧ 0 < z.2 at hz
    exact (fm_deriv z.1 z.2 hz.2.2.2.2.1.ne').hasFDerivWithinAt
  have hc :=
    MeasureTheory.integral_image_eq_integral_abs_det_fderiv_smul
      (μ := volume) (rg_meas a) hd (fm_inj a)
      (fun z : ℝ × ℝ => 1 / (2 * z.2))
  rw [fm_image a ha] at hc
  have hrhs :
      (∫ z in rg a, |(fd z.1 z.2).det| •
          (1 / (2 * (fm z).2))) =
        ∫ _z in rg a, (1 : ℝ) := by
    apply setIntegral_congr_fun (rg_meas a)
    intro z hz
    change
      a ^ 2 ≤ z.1 * z.2 ∧ z.1 * z.2 ≤ 2 * a ^ 2 ∧
        z.1 ≤ z.2 ∧ z.2 ≤ 2 * z.1 ∧ 0 < z.1 ∧ 0 < z.2 at hz
    have hx : 0 < z.1 := hz.2.2.2.2.1
    have hy : 0 < z.2 := hz.2.2.2.2.2
    change |(fd z.1 z.2).det| * (1 / (2 * (z.2 / z.1))) = 1
    rw [fd_det z.1 z.2 hx.ne', abs_of_pos (by positivity : 0 < 2 * (z.2 / z.1))]
    field_simp
  rw [hrhs] at hc
  have hrect :
      (∫ z in rect a, 1 / (2 * z.2)) =
        1 / 2 *
          ∫ u in a ^ 2..2 * a ^ 2,
            ∫ v in (1 : ℝ)..2, 1 / v := by
    unfold rect
    rw [Measure.volume_eq_prod]
    have hp :
        (∫ z : ℝ × ℝ in
            Set.Icc (a ^ 2) (2 * a ^ 2) ×ˢ Set.Icc (1 : ℝ) 2,
            1 / (2 * z.2) ∂volume.prod volume) =
          (∫ _u in Set.Icc (a ^ 2) (2 * a ^ 2), (1 : ℝ)) *
            ∫ v in Set.Icc (1 : ℝ) 2, 1 / (2 * v) := by
      simpa only [one_mul] using
        (MeasureTheory.setIntegral_prod_mul
          (μ := volume) (ν := volume)
          (fun _u : ℝ => (1 : ℝ))
          (fun v : ℝ => 1 / (2 * v))
          (Set.Icc (a ^ 2) (2 * a ^ 2)) (Set.Icc (1 : ℝ) 2))
    rw [hp, int_Icc_int (by nlinarith [sq_nonneg a] : a ^ 2 ≤ 2 * a ^ 2),
      int_Icc_int (by norm_num : (1 : ℝ) ≤ 2)]
    rw [show (fun v : ℝ => 1 / (2 * v)) =
        fun v => (1 / 2 : ℝ) * (1 / v) by
          funext v
          ring,
      intervalIntegral.integral_const_mul]
    simp
    ring
  rw [hrect] at hc
  exact hc.symm

private theorem iteratedIntegral_eval (a : ℝ) :
    1 / 2 *
        (∫ u in a ^ 2..2 * a ^ 2,
          ∫ v in (1 : ℝ)..2, 1 / v) =
      1 / 2 * a ^ 2 * Real.log 2 := by
  have hi :
      (∫ v in (1 : ℝ)..2, 1 / v) = Real.log 2 := by
    simpa using
      (integral_one_div_of_pos (a := (1 : ℝ)) (b := 2)
        (by norm_num) (by norm_num))
  rw [hi, intervalIntegral.integral_const]
  simp only [smul_eq_mul]
  ring

private theorem regionArea_zero :
    regionArea 0 =
      1 / 2 *
        ∫ u in (0 : ℝ) ^ 2..2 * (0 : ℝ) ^ 2,
          ∫ v in (1 : ℝ)..2, 1 / v := by
  unfold regionArea
  change
    (∫ _z in rg 0, (1 : ℝ)) =
      1 / 2 *
        ∫ u in (0 : ℝ) ^ 2..2 * (0 : ℝ) ^ 2,
          ∫ v in (1 : ℝ)..2, 1 / v
  have he : rg 0 = ∅ := by
    ext z
    constructor
    · intro hz
      change
        (0 : ℝ) ^ 2 ≤ z.1 * z.2 ∧
          z.1 * z.2 ≤ 2 * (0 : ℝ) ^ 2 ∧
          z.1 ≤ z.2 ∧ z.2 ≤ 2 * z.1 ∧
          0 < z.1 ∧ 0 < z.2 at hz
      have hp : 0 < z.1 * z.2 := mul_pos hz.2.2.2.2.1 hz.2.2.2.2.2
      simp only [Set.mem_empty_iff_false]
      norm_num at hz
      linarith
    · simp
  rw [he]
  simp

theorem gap1 (a x y u v : ℝ)
    (hp : (x, y) ∈ region a) (hu : u = x * y) (hv : v = y / x) :
    a ^ 2 ≤ u := by
  change
    a ^ 2 ≤ x * y ∧ x * y ≤ 2 * a ^ 2 ∧
      x ≤ y ∧ y ≤ 2 * x ∧ 0 < x ∧ 0 < y at hp
  rw [hu]
  exact hp.1

theorem gap2 (a x y u v : ℝ)
    (hp : (x, y) ∈ region a) (hu : u = x * y) (hv : v = y / x) :
    u ≤ 2 * a ^ 2 := by
  change
    a ^ 2 ≤ x * y ∧ x * y ≤ 2 * a ^ 2 ∧
      x ≤ y ∧ y ≤ 2 * x ∧ 0 < x ∧ 0 < y at hp
  rw [hu]
  exact hp.2.1

theorem gap3 (a x y u v : ℝ)
    (hp : (x, y) ∈ region a) (hu : u = x * y) (hv : v = y / x) :
    1 ≤ v := by
  change
    a ^ 2 ≤ x * y ∧ x * y ≤ 2 * a ^ 2 ∧
      x ≤ y ∧ y ≤ 2 * x ∧ 0 < x ∧ 0 < y at hp
  rw [hv]
  exact (le_div_iff₀ hp.2.2.2.2.1).2 (by simpa using hp.2.2.1)

theorem gap4 (a x y u v : ℝ)
    (hp : (x, y) ∈ region a) (hu : u = x * y) (hv : v = y / x) :
    v ≤ 2 := by
  change
    a ^ 2 ≤ x * y ∧ x * y ≤ 2 * a ^ 2 ∧
      x ≤ y ∧ y ≤ 2 * x ∧ 0 < x ∧ 0 < y at hp
  rw [hv]
  exact (div_le_iff₀ hp.2.2.2.2.1).2 hp.2.2.2.1

theorem gap5 (v : ℝ) (hv : 1 ≤ v) :
    |jacobianDet v| = 1 / (2 * v) := by
  have hvpos : 0 < v := lt_of_lt_of_le zero_lt_one hv
  unfold jacobianDet
  rw [abs_of_pos (div_pos one_pos (mul_pos (by norm_num) hvpos))]

theorem gap6 (a : ℝ) :
    regionArea a =
      1 / 2 *
        ∫ u in a ^ 2..2 * a ^ 2,
          ∫ v in (1 : ℝ)..2, 1 / v := by
  by_cases ha : a = 0
  · subst a
    exact regionArea_zero
  · exact regionArea_nonzero a ha

theorem gap7 (a : ℝ) :
    1 / 2 *
        (∫ u in a ^ 2..2 * a ^ 2,
          ∫ v in (1 : ℝ)..2, 1 / v) =
      1 / 2 * a ^ 2 * Real.log 2 := by
  exact iteratedIntegral_eval a

theorem gap8 (a : ℝ) :
    regionArea a = 1 / 2 * a ^ 2 * Real.log 2 := by
  rw [gap6, gap7]

end

end ProofGap.Exercise3997
