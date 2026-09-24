/- Exercise 3959. -/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Normed.Operator.Prod
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise3959

noncomputable section

open MeasureTheory
open scoped Interval

def rootRegion (a : ℝ) : Set (ℝ × ℝ) :=
  {p | Real.sqrt p.1 + Real.sqrt p.2 ≤ Real.sqrt a ∧
    0 ≤ p.1 ∧ 0 ≤ p.2}

def curvedBoundary (a : ℝ) : Set (ℝ × ℝ) :=
  {p | ∃ v ∈ Set.Icc (0 : ℝ) (Real.pi / 2),
    p = (a * Real.cos v ^ 4, a * Real.sin v ^ 4)}

def parameterRegion (a : ℝ) : Set (ℝ × ℝ) :=
  Set.Icc (0 : ℝ) a ×ˢ Set.Icc (0 : ℝ) (Real.pi / 2)

def coordinateMap (u v : ℝ) : ℝ × ℝ :=
  (u * Real.cos v ^ 4, u * Real.sin v ^ 4)

def jacobianAbs (u v : ℝ) : ℝ :=
  |4 * u * Real.cos v ^ 3 * Real.sin v ^ 3|

def regionIntegral (a : ℝ) (f : ℝ → ℝ → ℝ) : ℝ :=
  ∫ p in rootRegion a, f p.1 p.2

private def auxParameterRegion (a : ℝ) : Set (ℝ × ℝ) :=
  Set.Ioc (0 : ℝ) a ×ˢ Set.Icc (0 : ℝ) 1

private def parameterMap (q : ℝ × ℝ) : ℝ × ℝ :=
  (q.1 * q.2 ^ 2, q.1 * (1 - q.2) ^ 2)

private def parameterMapFDeriv (q : ℝ × ℝ) :
    ℝ × ℝ →L[ℝ] ℝ × ℝ :=
  (Matrix.toLin (.finTwoProd ℝ) (.finTwoProd ℝ)
    !![q.2 ^ 2, 2 * q.1 * q.2;
       (1 - q.2) ^ 2, -2 * q.1 * (1 - q.2)]).toContinuousLinearMap

private theorem parameterMap_hasFDerivAt (q : ℝ × ℝ) :
    HasFDerivAt parameterMap (parameterMapFDeriv q) q := by
  unfold parameterMap parameterMapFDeriv
  rw [Matrix.toLin_finTwoProd_toContinuousLinearMap]
  have hu :
      HasFDerivAt (fun z : ℝ × ℝ => z.1)
        (ContinuousLinearMap.fst ℝ ℝ ℝ) q :=
    hasFDerivAt_fst
  have ht :
      HasFDerivAt (fun z : ℝ × ℝ => z.2)
        (ContinuousLinearMap.snd ℝ ℝ ℝ) q :=
    hasFDerivAt_snd
  have homt :
      HasFDerivAt (fun z : ℝ × ℝ => 1 - z.2)
        (-(ContinuousLinearMap.snd ℝ ℝ ℝ)) q := by
    exact ht.const_sub 1
  convert HasFDerivAt.prodMk
      (hu.mul (ht.pow 2))
      (hu.mul (homt.pow 2))
      using 2 <;>
    ext z <;>
    simp [smul_eq_mul] <;>
    ring

private theorem parameterMapFDeriv_det (q : ℝ × ℝ) :
    (parameterMapFDeriv q).det =
      -2 * q.1 * q.2 * (1 - q.2) := by
  unfold parameterMapFDeriv
  simp only [LinearMap.det_toContinuousLinearMap,
    LinearMap.det_toLin, Matrix.det_fin_two_of]
  ring

private theorem sqrt_mul_sq (u t : ℝ) (hu : 0 ≤ u) (ht : 0 ≤ t) :
    Real.sqrt (u * t ^ 2) = Real.sqrt u * t := by
  have hu_sq : Real.sqrt u ^ 2 = u :=
    Real.sq_sqrt hu
  calc
    Real.sqrt (u * t ^ 2) =
        Real.sqrt ((Real.sqrt u * t) ^ 2) := by
      congr 1
      rw [mul_pow, hu_sq]
    _ = |Real.sqrt u * t| :=
      Real.sqrt_sq_eq_abs _
    _ = Real.sqrt u * t :=
      abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) ht)

private theorem parameterMap_injOn (a : ℝ) :
    Set.InjOn parameterMap (auxParameterRegion a) := by
  rintro p hp q hq heq
  rcases hp with ⟨hp_u, hp_t⟩
  rcases hq with ⟨hq_u, hq_t⟩
  have hx := congrArg (fun z : ℝ × ℝ => Real.sqrt z.1) heq
  have hy := congrArg (fun z : ℝ × ℝ => Real.sqrt z.2) heq
  simp only [parameterMap] at hx hy
  rw [sqrt_mul_sq p.1 p.2 hp_u.1.le hp_t.1,
    sqrt_mul_sq q.1 q.2 hq_u.1.le hq_t.1] at hx
  rw [sqrt_mul_sq p.1 (1 - p.2) hp_u.1.le (sub_nonneg.mpr hp_t.2),
    sqrt_mul_sq q.1 (1 - q.2) hq_u.1.le
      (sub_nonneg.mpr hq_t.2)] at hy
  have hsqrt :
      Real.sqrt p.1 = Real.sqrt q.1 := by
    linarith
  have hu : p.1 = q.1 := by
    calc
      p.1 = Real.sqrt p.1 ^ 2 :=
        (Real.sq_sqrt hp_u.1.le).symm
      _ = Real.sqrt q.1 ^ 2 := by rw [hsqrt]
      _ = q.1 := Real.sq_sqrt hq_u.1.le
  have hsqrt_pos : 0 < Real.sqrt p.1 :=
    Real.sqrt_pos.2 hp_u.1
  have ht : p.2 = q.2 := by
    rw [← hsqrt] at hx
    exact (mul_left_cancel₀ hsqrt_pos.ne' hx)
  exact Prod.ext hu ht

private theorem parameterMap_image (a : ℝ) (ha : 0 < a) :
    parameterMap '' auxParameterRegion a =
      rootRegion a \ {((0 : ℝ), (0 : ℝ))} := by
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    rcases hq with ⟨hq_u, hq_t⟩
    have hu0 : 0 ≤ q.1 := hq_u.1.le
    have ht0 : 0 ≤ q.2 := hq_t.1
    have ht1 : q.2 ≤ 1 := hq_t.2
    have hsqrtx :
        Real.sqrt (q.1 * q.2 ^ 2) =
          Real.sqrt q.1 * q.2 :=
      sqrt_mul_sq q.1 q.2 hu0 ht0
    have hsqrty :
        Real.sqrt (q.1 * (1 - q.2) ^ 2) =
          Real.sqrt q.1 * (1 - q.2) :=
      sqrt_mul_sq q.1 (1 - q.2) hu0
        (sub_nonneg.mpr ht1)
    constructor
    · change
        Real.sqrt (q.1 * q.2 ^ 2) +
              Real.sqrt (q.1 * (1 - q.2) ^ 2) ≤
            Real.sqrt a ∧
          0 ≤ q.1 * q.2 ^ 2 ∧
          0 ≤ q.1 * (1 - q.2) ^ 2
      refine ⟨?_, mul_nonneg hu0 (sq_nonneg _),
          mul_nonneg hu0 (sq_nonneg _)⟩
      rw [hsqrtx, hsqrty]
      have hsqrt_le :
          Real.sqrt q.1 ≤ Real.sqrt a :=
        Real.sqrt_le_sqrt hq_u.2
      linarith
    · intro hz
      have hz' :
          (q.1 * q.2 ^ 2,
            q.1 * (1 - q.2) ^ 2) =
            ((0 : ℝ), (0 : ℝ)) := by
        simpa only [Set.mem_singleton_iff] using hz
      have hx := congrArg Prod.fst hz'
      have hy := congrArg Prod.snd hz'
      simp only [Prod.fst, Prod.snd] at hx hy
      have ht_sq : q.2 ^ 2 = 0 :=
        (mul_eq_zero.mp hx).resolve_left hq_u.1.ne'
      have homt_sq : (1 - q.2) ^ 2 = 0 :=
        (mul_eq_zero.mp hy).resolve_left hq_u.1.ne'
      have ht : q.2 = 0 := sq_eq_zero_iff.mp ht_sq
      have homt : 1 - q.2 = 0 := sq_eq_zero_iff.mp homt_sq
      linarith
  · rintro ⟨hp, hpne⟩
    rcases hp with ⟨hroot, hx0, hy0⟩
    have hp_ne : p ≠ ((0 : ℝ), (0 : ℝ)) := by
      simpa only [Set.mem_singleton_iff] using hpne
    let sx : ℝ := Real.sqrt p.1
    let sy : ℝ := Real.sqrt p.2
    let s : ℝ := sx + sy
    have hsx0 : 0 ≤ sx := Real.sqrt_nonneg _
    have hsy0 : 0 ≤ sy := Real.sqrt_nonneg _
    have hs0 : 0 ≤ s := add_nonneg hsx0 hsy0
    have hs_ne : s ≠ 0 := by
      intro hs
      have hsx : sx = 0 := by linarith
      have hsy : sy = 0 := by linarith
      have hx : p.1 = 0 :=
        (Real.sqrt_eq_zero hx0).mp (by simpa only [sx] using hsx)
      have hy : p.2 = 0 :=
        (Real.sqrt_eq_zero hy0).mp (by simpa only [sy] using hsy)
      apply hp_ne
      exact Prod.ext hx hy
    have hspos : 0 < s := lt_of_le_of_ne hs0 (Ne.symm hs_ne)
    let u : ℝ := s ^ 2
    let t : ℝ := sx / s
    have hu_pos : 0 < u := sq_pos_of_pos hspos
    have hu_le : u ≤ a := by
      have ha_sq : Real.sqrt a ^ 2 = a :=
        Real.sq_sqrt ha.le
      have hs_le : s ≤ Real.sqrt a := by
        simpa only [s, sx, sy] using hroot
      dsimp only [u]
      nlinarith
    have ht0 : 0 ≤ t :=
      div_nonneg hsx0 hs0
    have ht1 : t ≤ 1 := by
      apply (div_le_one hspos).2
      dsimp only [s]
      linarith
    refine ⟨(u, t), ⟨⟨hu_pos, hu_le⟩, ⟨ht0, ht1⟩⟩, ?_⟩
    have hsx_sq : sx ^ 2 = p.1 := by
      dsimp only [sx]
      exact Real.sq_sqrt hx0
    have hsy_sq : sy ^ 2 = p.2 := by
      dsimp only [sy]
      exact Real.sq_sqrt hy0
    have homt : 1 - t = sy / s := by
      dsimp only [t]
      field_simp [hs_ne]
      dsimp only [s]
      ring
    apply Prod.ext
    · change u * t ^ 2 = p.1
      dsimp only [u, t]
      field_simp [hs_ne]
      rw [hsx_sq]
    · change u * (1 - t) ^ 2 = p.2
      rw [homt]
      dsimp only [u]
      field_simp [hs_ne]
      rw [hsy_sq]

private def cosSq (v : ℝ) : ℝ :=
  Real.cos v ^ 2

private def cosSqDeriv (v : ℝ) : ℝ :=
  -2 * Real.cos v * Real.sin v

private theorem cosSq_hasDerivAt (v : ℝ) :
    HasDerivAt cosSq (cosSqDeriv v) v := by
  unfold cosSq cosSqDeriv
  convert (Real.hasDerivAt_cos v).pow 2 using 1 <;>
    ring

private theorem cosSq_antitone :
    AntitoneOn cosSq (Set.Icc (0 : ℝ) (Real.pi / 2)) := by
  intro x hx y hy hxy
  have hpi2_le_pi : Real.pi / 2 ≤ Real.pi := by
    linarith [Real.pi_pos]
  have hx_pi : x ∈ Set.Icc (0 : ℝ) Real.pi :=
    ⟨hx.1, hx.2.trans hpi2_le_pi⟩
  have hy_pi : y ∈ Set.Icc (0 : ℝ) Real.pi :=
    ⟨hy.1, hy.2.trans hpi2_le_pi⟩
  have hcos : Real.cos y ≤ Real.cos x :=
    Real.antitoneOn_cos hx_pi hy_pi hxy
  have hxcos0 : 0 ≤ Real.cos x :=
    Real.cos_nonneg_of_mem_Icc
      ⟨by linarith [hx.1, Real.pi_pos],
        hx.2⟩
  have hycos0 : 0 ≤ Real.cos y :=
    Real.cos_nonneg_of_mem_Icc
      ⟨by linarith [hy.1, Real.pi_pos],
        hy.2⟩
  unfold cosSq
  nlinarith

private theorem cosSq_image :
    cosSq '' Set.Icc (0 : ℝ) (Real.pi / 2) =
      Set.Icc (0 : ℝ) 1 := by
  ext t
  constructor
  · rintro ⟨v, hv, rfl⟩
    have hcos0 : 0 ≤ Real.cos v :=
      Real.cos_nonneg_of_mem_Icc
        ⟨by linarith [hv.1, Real.pi_pos], hv.2⟩
    change
      0 ≤ Real.cos v ^ 2 ∧ Real.cos v ^ 2 ≤ 1
    exact
      ⟨sq_nonneg _,
        by nlinarith [Real.cos_le_one v]⟩
  · intro ht
    let v : ℝ := Real.arccos (Real.sqrt t)
    have hsqrt0 : 0 ≤ Real.sqrt t :=
      Real.sqrt_nonneg _
    have hsqrt1 : Real.sqrt t ≤ 1 := by
      rw [Real.sqrt_le_one]
      exact ht.2
    have hv0 : 0 ≤ v := Real.arccos_nonneg _
    have hv1 : v ≤ Real.pi / 2 :=
      Real.arccos_le_pi_div_two.2 hsqrt0
    refine ⟨v, ⟨hv0, hv1⟩, ?_⟩
    unfold cosSq
    rw [show Real.cos v = Real.sqrt t by
      dsimp only [v]
      exact Real.cos_arccos (by linarith) hsqrt1]
    exact Real.sq_sqrt ht.1

private theorem cosine_substitution
    (u : ℝ) (f : ℝ → ℝ → ℝ) :
    (∫ t in (0 : ℝ)..1,
        2 * u * t * (1 - t) *
          f (u * t ^ 2) (u * (1 - t) ^ 2)) =
      4 * ∫ v in (0 : ℝ)..Real.pi / 2,
        u * Real.cos v ^ 3 * Real.sin v ^ 3 *
          f (u * Real.cos v ^ 4)
            (u * Real.sin v ^ 4) := by
  let G : ℝ → ℝ := fun t =>
    2 * u * t * (1 - t) *
      f (u * t ^ 2) (u * (1 - t) ^ 2)
  have hsub :=
    integral_image_eq_integral_deriv_smul_of_antitone
      (s := Set.Icc (0 : ℝ) (Real.pi / 2))
      measurableSet_Icc
      (fun v hv => (cosSq_hasDerivAt v).hasDerivWithinAt)
      cosSq_antitone G
  rw [cosSq_image] at hsub
  simp only [smul_eq_mul] at hsub
  have ht_interval :
      (∫ t in Set.Icc (0 : ℝ) 1, G t) =
        ∫ t in (0 : ℝ)..1, G t := by
    calc
      (∫ t in Set.Icc (0 : ℝ) 1, G t) =
          ∫ t in Set.Ioc (0 : ℝ) 1, G t :=
        integral_Icc_eq_integral_Ioc
      _ = ∫ t in (0 : ℝ)..1, G t :=
        (intervalIntegral.integral_of_le
          (by norm_num : (0 : ℝ) ≤ 1)).symm
  have hv_interval :
      (∫ v in Set.Icc (0 : ℝ) (Real.pi / 2),
          (-cosSqDeriv v) * G (cosSq v)) =
        ∫ v in (0 : ℝ)..Real.pi / 2,
          (-cosSqDeriv v) * G (cosSq v) := by
    calc
      (∫ v in Set.Icc (0 : ℝ) (Real.pi / 2),
          (-cosSqDeriv v) * G (cosSq v)) =
          ∫ v in Set.Ioc (0 : ℝ) (Real.pi / 2),
            (-cosSqDeriv v) * G (cosSq v) :=
        integral_Icc_eq_integral_Ioc
      _ =
          ∫ v in (0 : ℝ)..Real.pi / 2,
            (-cosSqDeriv v) * G (cosSq v) :=
        (intervalIntegral.integral_of_le
          (by positivity : (0 : ℝ) ≤ Real.pi / 2)).symm
  have hinter :
      (∫ t in (0 : ℝ)..1, G t) =
        ∫ v in (0 : ℝ)..Real.pi / 2,
          (-cosSqDeriv v) * G (cosSq v) := by
    rw [← ht_interval, ← hv_interval]
    exact hsub
  calc
    (∫ t in (0 : ℝ)..1,
        2 * u * t * (1 - t) *
          f (u * t ^ 2) (u * (1 - t) ^ 2)) =
        ∫ t in (0 : ℝ)..1, G t := rfl
    _ =
        ∫ v in (0 : ℝ)..Real.pi / 2,
          (-cosSqDeriv v) * G (cosSq v) := hinter
    _ =
        ∫ v in (0 : ℝ)..Real.pi / 2,
          4 *
            (u * Real.cos v ^ 3 * Real.sin v ^ 3 *
              f (u * Real.cos v ^ 4)
                (u * Real.sin v ^ 4)) := by
      apply intervalIntegral.integral_congr
      intro v hv
      unfold cosSqDeriv cosSq G
      change
        -(-2 * Real.cos v * Real.sin v) *
            (2 * u * Real.cos v ^ 2 *
              (1 - Real.cos v ^ 2) *
              f (u * (Real.cos v ^ 2) ^ 2)
                (u * (1 - Real.cos v ^ 2) ^ 2)) =
          4 *
            (u * Real.cos v ^ 3 * Real.sin v ^ 3 *
              f (u * Real.cos v ^ 4)
                (u * Real.sin v ^ 4))
      have htrig :
          1 - Real.cos v ^ 2 = Real.sin v ^ 2 := by
        nlinarith [Real.sin_sq_add_cos_sq v]
      rw [htrig]
      rw [show (Real.cos v ^ 2) ^ 2 =
          Real.cos v ^ 4 by ring,
        show (Real.sin v ^ 2) ^ 2 =
          Real.sin v ^ 4 by ring]
      ring
    _ =
        4 * ∫ v in (0 : ℝ)..Real.pi / 2,
          u * Real.cos v ^ 3 * Real.sin v ^ 3 *
            f (u * Real.cos v ^ 4)
              (u * Real.sin v ^ 4) := by
      simpa only using
        (intervalIntegral.integral_const_mul
          (a := (0 : ℝ)) (b := Real.pi / 2)
          (4 : ℝ)
          (fun v =>
            u * Real.cos v ^ 3 * Real.sin v ^ 3 *
              f (u * Real.cos v ^ 4)
                (u * Real.sin v ^ 4)))

private instance : Measure.IsAddHaarMeasure volume (G := ℝ × ℝ) :=
  Measure.prod.instIsAddHaarMeasure _ _

private def auxWeight (f : ℝ → ℝ → ℝ) (q : ℝ × ℝ) : ℝ :=
  2 * q.1 * q.2 * (1 - q.2) *
    f (q.1 * q.2 ^ 2) (q.1 * (1 - q.2) ^ 2)

private theorem auxWeight_integrable
    (a : ℝ) (f : ℝ → ℝ → ℝ) (ha : 0 < a)
    (hf : IntegrableOn (fun p : ℝ × ℝ => f p.1 p.2) (rootRegion a)) :
    IntegrableOn (auxWeight f) (auxParameterRegion a) := by
  let g : ℝ × ℝ → ℝ := fun p => f p.1 p.2
  have hparam_meas : MeasurableSet (auxParameterRegion a) :=
    measurableSet_Ioc.prod measurableSet_Icc
  have hderiv :
      ∀ q ∈ auxParameterRegion a,
        HasFDerivWithinAt parameterMap
          (parameterMapFDeriv q) (auxParameterRegion a) q := by
    intro q hq
    exact (parameterMap_hasFDerivAt q).hasFDerivWithinAt
  have hgf : IntegrableOn g (rootRegion a) := by
    simpa only [g] using hf
  have hparam :
      IntegrableOn
        (fun q : ℝ × ℝ =>
          |(parameterMapFDeriv q).det| •
            g (parameterMap q))
        (auxParameterRegion a) := by
    have hiff :=
      integrableOn_image_iff_integrableOn_abs_det_fderiv_smul
        (μ := volume) hparam_meas hderiv
          (parameterMap_injOn a) g
    rw [parameterMap_image a ha] at hiff
    exact hiff.mp (hgf.mono_set Set.diff_subset)
  refine hparam.congr_fun ?_ hparam_meas
  intro q hq
  rcases hq with ⟨hq_u, hq_t⟩
  change
    |(parameterMapFDeriv q).det| *
        f (q.1 * q.2 ^ 2)
          (q.1 * (1 - q.2) ^ 2) =
      auxWeight f q
  rw [parameterMapFDeriv_det]
  unfold auxWeight
  rw [show
    -2 * q.1 * q.2 * (1 - q.2) =
      -(2 * q.1 * q.2 * (1 - q.2)) by ring,
    abs_neg,
    abs_of_nonneg
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg (by norm_num) hq_u.1.le)
          hq_t.1)
        (sub_nonneg.mpr hq_t.2))]

private def angleRegion (a : ℝ) : Set (ℝ × ℝ) :=
  Set.Ioc (0 : ℝ) a ×ˢ Set.Icc (0 : ℝ) (Real.pi / 2)

private def angleToAux (q : ℝ × ℝ) : ℝ × ℝ :=
  (q.1, cosSq q.2)

private def angleToAuxFDeriv (q : ℝ × ℝ) :
    ℝ × ℝ →L[ℝ] ℝ × ℝ :=
  (Matrix.toLin (.finTwoProd ℝ) (.finTwoProd ℝ)
    !![1, 0; 0, cosSqDeriv q.2]).toContinuousLinearMap

private theorem angleToAux_hasFDerivAt (q : ℝ × ℝ) :
    HasFDerivAt angleToAux (angleToAuxFDeriv q) q := by
  unfold angleToAux angleToAuxFDeriv
  rw [Matrix.toLin_finTwoProd_toContinuousLinearMap]
  have hu :
      HasFDerivAt (fun z : ℝ × ℝ => z.1)
        (ContinuousLinearMap.fst ℝ ℝ ℝ) q :=
    hasFDerivAt_fst
  have hv :
      HasFDerivAt (fun z : ℝ × ℝ => cosSq z.2)
        ((cosSqDeriv q.2) • (ContinuousLinearMap.snd ℝ ℝ ℝ)) q := by
    convert
      (cosSq_hasDerivAt q.2).hasFDerivAt.comp q hasFDerivAt_snd
      using 1 <;>
      ext z <;>
      simp [smul_eq_mul]
  convert HasFDerivAt.prodMk hu hv using 2 <;>
    ext z <;>
    simp [smul_eq_mul] <;>
    ring

private theorem angleToAuxFDeriv_det (q : ℝ × ℝ) :
    (angleToAuxFDeriv q).det = cosSqDeriv q.2 := by
  unfold angleToAuxFDeriv
  simp only [LinearMap.det_toContinuousLinearMap,
    LinearMap.det_toLin, Matrix.det_fin_two_of]
  ring

private theorem cosSq_injOn :
    Set.InjOn cosSq (Set.Icc (0 : ℝ) (Real.pi / 2)) := by
  intro v hv w hw heq
  have hvcos0 : 0 ≤ Real.cos v :=
    Real.cos_nonneg_of_mem_Icc
      ⟨by linarith [hv.1, Real.pi_pos], hv.2⟩
  have hwcos0 : 0 ≤ Real.cos w :=
    Real.cos_nonneg_of_mem_Icc
      ⟨by linarith [hw.1, Real.pi_pos], hw.2⟩
  have hcos : Real.cos v = Real.cos w := by
    unfold cosSq at heq
    nlinarith
  apply Real.strictAntiOn_cos.injOn
  · exact ⟨hv.1, hv.2.trans (by linarith [Real.pi_pos])⟩
  · exact ⟨hw.1, hw.2.trans (by linarith [Real.pi_pos])⟩
  · exact hcos

private theorem angleToAux_injOn (a : ℝ) :
    Set.InjOn angleToAux (angleRegion a) := by
  rintro p hp q hq heq
  have hfst := congrArg Prod.fst heq
  have hsnd := congrArg Prod.snd heq
  change p.1 = q.1 at hfst
  change cosSq p.2 = cosSq q.2 at hsnd
  exact Prod.ext hfst (cosSq_injOn hp.2 hq.2 hsnd)

private theorem angleToAux_image (a : ℝ) :
    angleToAux '' angleRegion a = auxParameterRegion a := by
  ext q
  constructor
  · rintro ⟨p, hp, rfl⟩
    refine ⟨hp.1, ?_⟩
    rw [← cosSq_image]
    exact ⟨p.2, hp.2, rfl⟩
  · intro hq
    have ht : q.2 ∈ cosSq '' Set.Icc (0 : ℝ) (Real.pi / 2) := by
      rw [cosSq_image]
      exact hq.2
    rcases ht with ⟨v, hv, heq⟩
    refine ⟨(q.1, v), ⟨hq.1, hv⟩, ?_⟩
    exact Prod.ext rfl heq

private def angleWeight (f : ℝ → ℝ → ℝ) (q : ℝ × ℝ) : ℝ :=
  q.1 * Real.cos q.2 ^ 3 * Real.sin q.2 ^ 3 *
    f (q.1 * Real.cos q.2 ^ 4) (q.1 * Real.sin q.2 ^ 4)

private theorem angleWeight_integrable
    (a : ℝ) (f : ℝ → ℝ → ℝ) (ha : 0 < a)
    (hf : IntegrableOn (fun p : ℝ × ℝ => f p.1 p.2) (rootRegion a)) :
    IntegrableOn (angleWeight f) (angleRegion a) := by
  have hmeas : MeasurableSet (angleRegion a) :=
    measurableSet_Ioc.prod measurableSet_Icc
  have hderiv :
      ∀ q ∈ angleRegion a,
        HasFDerivWithinAt angleToAux
          (angleToAuxFDeriv q) (angleRegion a) q := by
    intro q hq
    exact (angleToAux_hasFDerivAt q).hasFDerivWithinAt
  have hiff :=
    integrableOn_image_iff_integrableOn_abs_det_fderiv_smul
      (μ := volume) hmeas hderiv (angleToAux_injOn a) (auxWeight f)
  rw [angleToAux_image a] at hiff
  have hweighted := hiff.mp (auxWeight_integrable a f ha hf)
  have hfour :
      IntegrableOn (fun q : ℝ × ℝ => 4 * angleWeight f q)
        (angleRegion a) := by
    refine hweighted.congr_fun ?_ hmeas
    intro q hq
    rcases hq with ⟨hq_u, hq_v⟩
    have hcos0 : 0 ≤ Real.cos q.2 :=
      Real.cos_nonneg_of_mem_Icc
        ⟨by linarith [hq_v.1, Real.pi_pos], hq_v.2⟩
    have hsin0 : 0 ≤ Real.sin q.2 :=
      Real.sin_nonneg_of_nonneg_of_le_pi hq_v.1
        (hq_v.2.trans (by linarith [Real.pi_pos]))
    have htrig :
        1 - Real.cos q.2 ^ 2 = Real.sin q.2 ^ 2 := by
      nlinarith [Real.sin_sq_add_cos_sq q.2]
    change
      |(angleToAuxFDeriv q).det| *
          auxWeight f (angleToAux q) =
        4 * angleWeight f q
    rw [angleToAuxFDeriv_det]
    unfold angleToAux cosSq cosSqDeriv auxWeight angleWeight
    simp only [Prod.fst, Prod.snd]
    rw [show
        -2 * Real.cos q.2 * Real.sin q.2 =
          -(2 * Real.cos q.2 * Real.sin q.2) by ring,
      abs_neg, abs_of_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) hcos0) hsin0), htrig]
    ring
  have hscaled := hfour.const_mul (1 / 4 : ℝ)
  apply hscaled.congr
  filter_upwards with q
  ring

private theorem regionIntegral_formula (a : ℝ) (f : ℝ → ℝ → ℝ) (ha : 0 < a)
    (hf : IntegrableOn (fun p : ℝ × ℝ => f p.1 p.2) (rootRegion a)) :
    (∫ p in rootRegion a, f p.1 p.2) =
      4 * ∫ u in (0 : ℝ)..a,
        ∫ v in (0 : ℝ)..Real.pi / 2,
          u * Real.cos v ^ 3 * Real.sin v ^ 3 *
            f (u * Real.cos v ^ 4) (u * Real.sin v ^ 4) := by
  let g : ℝ × ℝ → ℝ := fun p => f p.1 p.2
  let W : ℝ × ℝ → ℝ := fun q =>
    2 * q.1 * q.2 * (1 - q.2) *
      f (q.1 * q.2 ^ 2) (q.1 * (1 - q.2) ^ 2)
  have hparam_meas : MeasurableSet (auxParameterRegion a) :=
    measurableSet_Ioc.prod measurableSet_Icc
  have hderiv :
      ∀ q ∈ auxParameterRegion a,
        HasFDerivWithinAt parameterMap
          (parameterMapFDeriv q) (auxParameterRegion a) q := by
    intro q hq
    exact (parameterMap_hasFDerivAt q).hasFDerivWithinAt
  have horigin :
      {((0 : ℝ), (0 : ℝ))} ⊆ rootRegion a := by
    intro p hp
    simp only [Set.mem_singleton_iff] at hp
    subst p
    simp [rootRegion, Real.sqrt_nonneg]
  have hgf :
      IntegrableOn g (rootRegion a) := by
    simpa only [g] using hf
  have hremove :
      (∫ p in rootRegion a \ {((0 : ℝ), (0 : ℝ))},
          g p) =
        ∫ p in rootRegion a, g p := by
    rw [setIntegral_diff (MeasurableSet.singleton _)
      hgf horigin]
    rw [setIntegral_measure_zero g
      (Set.subsingleton_singleton.measure_zero volume), sub_zero]
  have hparam :
      IntegrableOn
        (fun q : ℝ × ℝ =>
          |(parameterMapFDeriv q).det| •
            g (parameterMap q))
        (auxParameterRegion a) := by
    have hiff :=
      integrableOn_image_iff_integrableOn_abs_det_fderiv_smul
        (μ := volume) hparam_meas hderiv
          (parameterMap_injOn a) g
    rw [parameterMap_image a ha] at hiff
    exact hiff.mp (hgf.mono_set Set.diff_subset)
  have hW :
      IntegrableOn W (auxParameterRegion a) := by
    refine hparam.congr_fun ?_ hparam_meas
    intro q hq
    rcases hq with ⟨hq_u, hq_t⟩
    change
      |(parameterMapFDeriv q).det| *
          f (q.1 * q.2 ^ 2)
            (q.1 * (1 - q.2) ^ 2) =
        2 * q.1 * q.2 * (1 - q.2) *
          f (q.1 * q.2 ^ 2)
            (q.1 * (1 - q.2) ^ 2)
    rw [parameterMapFDeriv_det]
    rw [show
      -2 * q.1 * q.2 * (1 - q.2) =
        -(2 * q.1 * q.2 * (1 - q.2)) by ring,
      abs_neg,
      abs_of_nonneg
        (mul_nonneg
          (mul_nonneg
            (mul_nonneg (by norm_num) hq_u.1.le)
            hq_t.1)
          (sub_nonneg.mpr hq_t.2))]
  have hchange :
      (∫ p in rootRegion a, g p) =
        ∫ q in auxParameterRegion a, W q := by
    calc
      (∫ p in rootRegion a, g p) =
          ∫ p in rootRegion a \
            {((0 : ℝ), (0 : ℝ))}, g p :=
        hremove.symm
      _ =
          ∫ p in parameterMap '' auxParameterRegion a,
            g p := by
        rw [parameterMap_image a ha]
      _ =
          ∫ q in auxParameterRegion a,
            |(parameterMapFDeriv q).det| •
              g (parameterMap q) :=
        integral_image_eq_integral_abs_det_fderiv_smul
          volume hparam_meas hderiv
            (parameterMap_injOn a) g
      _ = ∫ q in auxParameterRegion a, W q := by
        apply setIntegral_congr_fun hparam_meas
        intro q hq
        rcases hq with ⟨hq_u, hq_t⟩
        change
          |(parameterMapFDeriv q).det| *
              f (q.1 * q.2 ^ 2)
                (q.1 * (1 - q.2) ^ 2) =
            2 * q.1 * q.2 * (1 - q.2) *
              f (q.1 * q.2 ^ 2)
                (q.1 * (1 - q.2) ^ 2)
        rw [parameterMapFDeriv_det]
        rw [show
          -2 * q.1 * q.2 * (1 - q.2) =
            -(2 * q.1 * q.2 * (1 - q.2)) by ring,
          abs_neg,
          abs_of_nonneg
            (mul_nonneg
              (mul_nonneg
                (mul_nonneg (by norm_num) hq_u.1.le)
                hq_t.1)
              (sub_nonneg.mpr hq_t.2))]
  have hparameter_eval :
      (∫ q in auxParameterRegion a, W q) =
        ∫ u in (0 : ℝ)..a,
          ∫ t in (0 : ℝ)..1,
            2 * u * t * (1 - t) *
              f (u * t ^ 2) (u * (1 - t) ^ 2) := by
    have hfubini :
        (∫ q in auxParameterRegion a, W q) =
          ∫ u in Set.Ioc (0 : ℝ) a,
            ∫ t in Set.Icc (0 : ℝ) 1,
              W (u, t) := by
      unfold auxParameterRegion at hW ⊢
      exact setIntegral_prod _ hW
    have hinner (u : ℝ) :
        (∫ t in Set.Icc (0 : ℝ) 1, W (u, t)) =
          ∫ t in (0 : ℝ)..1,
            2 * u * t * (1 - t) *
              f (u * t ^ 2) (u * (1 - t) ^ 2) := by
      calc
        (∫ t in Set.Icc (0 : ℝ) 1, W (u, t)) =
            ∫ t in Set.Ioc (0 : ℝ) 1, W (u, t) :=
          integral_Icc_eq_integral_Ioc
        _ = ∫ t in (0 : ℝ)..1, W (u, t) :=
          (intervalIntegral.integral_of_le
            (by norm_num : (0 : ℝ) ≤ 1)).symm
        _ =
            ∫ t in (0 : ℝ)..1,
              2 * u * t * (1 - t) *
                f (u * t ^ 2) (u * (1 - t) ^ 2) := by
          rfl
    rw [hfubini]
    simp_rw [hinner]
    exact
      (intervalIntegral.integral_of_le ha.le).symm
  calc
    (∫ p in rootRegion a, f p.1 p.2) =
        ∫ p in rootRegion a, g p := rfl
    _ = ∫ q in auxParameterRegion a, W q := hchange
    _ =
        ∫ u in (0 : ℝ)..a,
          ∫ t in (0 : ℝ)..1,
            2 * u * t * (1 - t) *
              f (u * t ^ 2) (u * (1 - t) ^ 2) :=
      hparameter_eval
    _ =
        ∫ u in (0 : ℝ)..a,
          4 * ∫ v in (0 : ℝ)..Real.pi / 2,
            u * Real.cos v ^ 3 * Real.sin v ^ 3 *
              f (u * Real.cos v ^ 4)
                (u * Real.sin v ^ 4) := by
      apply intervalIntegral.integral_congr
      intro u hu
      exact cosine_substitution u f
    _ =
        4 * ∫ u in (0 : ℝ)..a,
          ∫ v in (0 : ℝ)..Real.pi / 2,
            u * Real.cos v ^ 3 * Real.sin v ^ 3 *
              f (u * Real.cos v ^ 4)
                (u * Real.sin v ^ 4) := by
      rw [intervalIntegral.integral_const_mul]

theorem gap1 (a : ℝ) (ha : 0 < a) :
    curvedBoundary a =
      {p | ∃ v ∈ Set.Icc (0 : ℝ) (Real.pi / 2),
        p = (a * Real.cos v ^ 4, a * Real.sin v ^ 4)} := by
  rfl

theorem gap2 (u v : ℝ) :
    jacobianAbs u v =
      4 * |u * Real.cos v ^ 3 * Real.sin v ^ 3| := by
  unfold jacobianAbs
  rw [show
    4 * u * Real.cos v ^ 3 * Real.sin v ^ 3 =
      4 * (u * Real.cos v ^ 3 * Real.sin v ^ 3) by ring,
    abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4)]

theorem gap3 (a : ℝ) (ha : 0 < a) :
    parameterRegion a =
      {p | 0 ≤ p.1 ∧ p.1 ≤ a ∧
        0 ≤ p.2 ∧ p.2 ≤ Real.pi / 2} := by
  ext p
  simp only [parameterRegion, Set.mem_prod, Set.mem_Icc,
    Set.mem_setOf_eq]
  tauto

theorem gap4 (a : ℝ) (f : ℝ → ℝ → ℝ) (ha : 0 < a)
    (hf : IntegrableOn (fun p : ℝ × ℝ => f p.1 p.2) (rootRegion a)) :
    regionIntegral a f =
      4 * ∫ u in (0 : ℝ)..a,
        ∫ v in (0 : ℝ)..Real.pi / 2,
          u * Real.cos v ^ 3 * Real.sin v ^ 3 *
            f (u * Real.cos v ^ 4) (u * Real.sin v ^ 4) := by
  unfold regionIntegral
  exact regionIntegral_formula a f ha hf

theorem gap5 (a : ℝ) (f : ℝ → ℝ → ℝ) (ha : 0 < a)
    (hf : IntegrableOn (fun p : ℝ × ℝ => f p.1 p.2) (rootRegion a)) :
    4 * (∫ u in (0 : ℝ)..a,
        ∫ v in (0 : ℝ)..Real.pi / 2,
          u * Real.cos v ^ 3 * Real.sin v ^ 3 *
            f (u * Real.cos v ^ 4) (u * Real.sin v ^ 4)) =
      4 * ∫ v in (0 : ℝ)..Real.pi / 2,
        ∫ u in (0 : ℝ)..a,
          u * Real.cos v ^ 3 * Real.sin v ^ 3 *
            f (u * Real.cos v ^ 4) (u * Real.sin v ^ 4) := by
  let H : ℝ × ℝ → ℝ := angleWeight f
  let su : Set ℝ := Set.Ioc (0 : ℝ) a
  let sv : Set ℝ := Set.Ioc (0 : ℝ) (Real.pi / 2)
  have hpi : (0 : ℝ) ≤ Real.pi / 2 := by positivity
  have hHlarge :
      IntegrableOn H (angleRegion a) := by
    simpa only [H] using angleWeight_integrable a f ha hf
  have hH :
      IntegrableOn H (su ×ˢ sv) :=
    hHlarge.mono_set (by
      intro q hq
      exact ⟨hq.1, Set.Ioc_subset_Icc_self hq.2⟩)
  have hprod :
      Integrable H
        ((volume.restrict su).prod (volume.restrict sv)) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
    exact hH
  have hswap :
      (∫ u, ∫ v, H (u, v) ∂volume.restrict sv
          ∂volume.restrict su) =
        ∫ v, ∫ u, H (u, v) ∂volume.restrict su
          ∂volume.restrict sv :=
    integral_integral_swap
      (f := fun u v => H (u, v)) hprod
  have hcore :
      (∫ u in su, ∫ v in sv, H (u, v)) =
        ∫ v in sv, ∫ u in su, H (u, v) := by
    exact hswap
  rw [intervalIntegral.integral_of_le ha.le,
    intervalIntegral.integral_of_le hpi]
  simp_rw [intervalIntegral.integral_of_le ha.le,
    intervalIntegral.integral_of_le hpi]
  simpa [su, sv, H, angleWeight] using congrArg (fun z : ℝ => 4 * z) hcore

theorem gap6 (a : ℝ) (f : ℝ → ℝ → ℝ) (ha : 0 < a)
    (hf : IntegrableOn (fun p : ℝ × ℝ => f p.1 p.2) (rootRegion a)) :
    regionIntegral a f =
      4 * ∫ v in (0 : ℝ)..Real.pi / 2,
        ∫ u in (0 : ℝ)..a,
          u * Real.cos v ^ 3 * Real.sin v ^ 3 *
            f (u * Real.cos v ^ 4) (u * Real.sin v ^ 4) := by
  exact (gap4 a f ha hf).trans (gap5 a f ha hf)

end

end ProofGap.Exercise3959
