import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.Data.Real.Sqrt
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise4087

noncomputable section

open MeasureTheory
open scoped Interval

def ball : Set (ℝ × ℝ × ℝ) :=
  {p | p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2 ≤ p.2.2}

def sphericalMap (r phi psi : ℝ) : ℝ × ℝ × ℝ :=
  (r * Real.cos phi * Real.cos psi,
    r * Real.sin phi * Real.cos psi,
    r * Real.sin psi)

def sphericalDomain : Set (ℝ × ℝ × ℝ) :=
  {p | 0 ≤ p.1 ∧ p.1 ≤ 2 * Real.pi ∧
    0 ≤ p.2.1 ∧ p.2.1 ≤ Real.pi / 2 ∧
    0 ≤ p.2.2 ∧ p.2.2 ≤ Real.sin p.2.1}

def sphericalJacobianAbs (r psi : ℝ) : ℝ :=
  |r ^ 2 * Real.cos psi|

def radialNormIntegral : ℝ :=
  ∫ p in ball, Real.sqrt (p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2)

private def halfBallPlane : Set (ℝ × ℝ) :=
  {q | 0 < q.1 ∧ q.1 ^ 2 + q.2 ^ 2 ≤ q.2}

private def ballPlane : Set (ℝ × ℝ) :=
  {q | q.1 ^ 2 + q.2 ^ 2 ≤ q.2}

private def planeIntegrand (q : ℝ × ℝ) : ℝ :=
  q.1 * Real.sqrt (q.1 ^ 2 + q.2 ^ 2)

private theorem ball_closed : IsClosed ball := by
  exact isClosed_le
    (((continuous_fst.pow 2).add
      ((continuous_fst.comp continuous_snd).pow 2)).add
      ((continuous_snd.comp continuous_snd).pow 2))
    (continuous_snd.comp continuous_snd)

private theorem ball_compact : IsCompact ball := by
  apply (isCompact_Icc :
    IsCompact (Set.Icc ((-1 : ℝ), ((-1 : ℝ), (-1 : ℝ)))
      ((1 : ℝ), ((1 : ℝ), (1 : ℝ))))).of_isClosed_subset ball_closed
  intro p hp
  change p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2 ≤ p.2.2 at hp
  have hzsq : p.2.2 ^ 2 ≤ p.2.2 := by
    nlinarith [sq_nonneg p.1, sq_nonneg p.2.1]
  have hz0 : 0 ≤ p.2.2 := by
    by_contra hn
    have : p.2.2 < 0 := lt_of_not_ge hn
    nlinarith [sq_nonneg p.2.2]
  have hz1 : p.2.2 ≤ 1 := by
    nlinarith [sq_nonneg (p.2.2 - 1)]
  have hx : p.1 ^ 2 ≤ 1 := by
    nlinarith [sq_nonneg p.2.1, sq_nonneg (p.2.2 - 1 / 2)]
  have hy : p.2.1 ^ 2 ≤ 1 := by
    nlinarith [sq_nonneg p.1, sq_nonneg (p.2.2 - 1 / 2)]
  constructor
  · exact ⟨by nlinarith [sq_nonneg (p.1 + 1)],
      by nlinarith [sq_nonneg (p.2.1 + 1)], by linarith⟩
  · exact ⟨by nlinarith [sq_nonneg (p.1 - 1)],
      by nlinarith [sq_nonneg (p.2.1 - 1)], hz1⟩

private theorem ballPlane_closed : IsClosed ballPlane := by
  exact isClosed_le
    ((continuous_fst.pow 2).add (continuous_snd.pow 2))
    continuous_snd

private theorem ballPlane_compact : IsCompact ballPlane := by
  apply (isCompact_Icc :
    IsCompact (Set.Icc ((-1 : ℝ), (-1 : ℝ))
      ((1 : ℝ), (1 : ℝ)))).of_isClosed_subset ballPlane_closed
  intro q hq
  change q.1 ^ 2 + q.2 ^ 2 ≤ q.2 at hq
  have hy2 : q.2 ^ 2 ≤ q.2 := by nlinarith [sq_nonneg q.1]
  have hy0 : 0 ≤ q.2 := by
    by_contra hn
    have : q.2 < 0 := lt_of_not_ge hn
    nlinarith [sq_nonneg q.2]
  have hy1 : q.2 ≤ 1 := by
    nlinarith [sq_nonneg (q.2 - 1)]
  have hx : q.1 ^ 2 ≤ 1 := by
    nlinarith [sq_nonneg (q.2 - 1 / 2)]
  exact ⟨⟨by nlinarith [sq_nonneg (q.1 + 1)], by linarith⟩,
    ⟨by nlinarith [sq_nonneg (q.1 - 1)], hy1⟩⟩

private theorem halfBallPlane_measurable : MeasurableSet halfBallPlane := by
  exact (isOpen_lt continuous_const continuous_fst).measurableSet.inter
    ballPlane_closed.measurableSet

private theorem planeIntegrand_continuous : Continuous planeIntegrand := by
  exact continuous_fst.mul
    (Real.continuous_sqrt.comp
      ((continuous_fst.pow 2).add (continuous_snd.pow 2)))

private theorem first_polar_pointwise (z : ℝ) (p : ℝ × ℝ)
    (hp : p ∈ polarCoord.target) :
    p.1 • ball.indicator
        (fun q : ℝ × ℝ × ℝ =>
          Real.sqrt (q.1 ^ 2 + q.2.1 ^ 2 + q.2.2 ^ 2))
        ((polarCoord.symm p).1, ((polarCoord.symm p).2, z)) =
      halfBallPlane.indicator planeIntegrand (p.1, z) * (1 : ℝ) := by
  rcases p with ⟨r, theta⟩
  have hr : 0 < r := hp.1
  have htrig :
      (r * Real.cos theta) ^ 2 + (r * Real.sin theta) ^ 2 = r ^ 2 := by
    calc
      _ = r ^ 2 * (Real.cos theta ^ 2 + Real.sin theta ^ 2) := by ring
      _ = r ^ 2 := by rw [Real.cos_sq_add_sin_sq]; ring
  have hmem :
      ((polarCoord.symm (r, theta)).1,
          ((polarCoord.symm (r, theta)).2, z)) ∈ ball ↔
        (r, z) ∈ halfBallPlane := by
    rw [polarCoord_symm_apply]
    simp only [ball, halfBallPlane, Set.mem_setOf_eq]
    rw [show
      (r * Real.cos theta) ^ 2 + (r * Real.sin theta) ^ 2 + z ^ 2 =
        ((r * Real.cos theta) ^ 2 + (r * Real.sin theta) ^ 2) + z ^ 2 by
      ring, htrig]
    simp [hr]
  by_cases h : (r, z) ∈ halfBallPlane
  · have h' :
        ((polarCoord.symm (r, theta)).1,
          ((polarCoord.symm (r, theta)).2, z)) ∈ ball :=
      hmem.mpr h
    rw [Set.indicator_of_mem h, Set.indicator_of_mem h']
    simp only [smul_eq_mul, planeIntegrand]
    rw [polarCoord_symm_apply]
    rw [show
      (r * Real.cos theta) ^ 2 + (r * Real.sin theta) ^ 2 + z ^ 2 =
        ((r * Real.cos theta) ^ 2 + (r * Real.sin theta) ^ 2) + z ^ 2 by
      ring, htrig]
    ring
  · have h' :
        ((polarCoord.symm (r, theta)).1,
          ((polarCoord.symm (r, theta)).2, z)) ∉ ball := by
      intro hh
      exact h (hmem.mp hh)
    rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h']
    simp

private theorem angular_full :
    (∫ theta in Set.Ioo (-Real.pi) Real.pi, (1 : ℝ)) =
      2 * Real.pi := by
  calc
    _ = ∫ theta in Set.Ioc (-Real.pi) Real.pi, (1 : ℝ) :=
      (integral_Ioc_eq_integral_Ioo
        (f := fun _ : ℝ => (1 : ℝ))).symm
    _ = ∫ theta in -Real.pi..Real.pi, (1 : ℝ) := by
      rw [intervalIntegral.integral_of_le]
      exact neg_le_self Real.pi_nonneg
    _ = 2 * Real.pi := by
      simp only [intervalIntegral.integral_const, smul_eq_mul]
      ring

private theorem radialNorm_to_plane :
    radialNormIntegral =
      (∫ q in halfBallPlane, planeIntegrand q) * (2 * Real.pi) := by
  let G : ℝ × ℝ × ℝ → ℝ := fun p =>
    Real.sqrt (p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2)
  have hG : Continuous G :=
    Real.continuous_sqrt.comp
      (((continuous_fst.pow 2).add
        ((continuous_fst.comp continuous_snd).pow 2)).add
        ((continuous_snd.comp continuous_snd).pow 2))
  have hK : Integrable (ball.indicator G) := by
    rw [integrable_indicator_iff ball_closed.measurableSet]
    exact hG.continuousOn.integrableOn_compact ball_compact
  let e :=
    (MeasurableEquiv.prodAssoc :
      ((ℝ × ℝ) × ℝ) ≃ᵐ (ℝ × (ℝ × ℝ)))
  have hK' : Integrable
      (fun q : (ℝ × ℝ) × ℝ => ball.indicator G (e q)) := by
    simpa only [Function.comp_apply] using
      (volume_preserving_prodAssoc.integrable_comp_emb
        e.measurableEmbedding).2 hK
  have hreassoc :
      (∫ q : (ℝ × ℝ) × ℝ, ball.indicator G (e q)) =
        ∫ p : ℝ × (ℝ × ℝ), ball.indicator G p :=
    volume_preserving_prodAssoc.integral_comp' (ball.indicator G)
  unfold radialNormIntegral
  rw [← integral_indicator ball_closed.measurableSet]
  change (∫ p : ℝ × (ℝ × ℝ), ball.indicator G p) = _
  rw [← hreassoc]
  have hFubini :
      (∫ q : (ℝ × ℝ) × ℝ, ball.indicator G (e q)) =
        ∫ z : ℝ, ∫ q : ℝ × ℝ, ball.indicator G (e (q, z)) := by
    exact MeasureTheory.integral_prod_symm
      (fun q : (ℝ × ℝ) × ℝ => ball.indicator G (e q)) hK'
  rw [hFubini]
  change (∫ z : ℝ, ∫ q : ℝ × ℝ,
    ball.indicator G (q.1, (q.2, z))) = _
  have hxy (z : ℝ) :
      (∫ q : ℝ × ℝ, ball.indicator G (q.1, (q.2, z))) =
        (∫ r in Set.Ioi (0 : ℝ),
            halfBallPlane.indicator planeIntegrand (r, z)) *
          (2 * Real.pi) := by
    have hp := integral_comp_polarCoord_symm
      (fun q : ℝ × ℝ => ball.indicator G (q.1, (q.2, z)))
    have hprod :
        (∫ p in polarCoord.target,
          p.1 • ball.indicator G
            ((polarCoord.symm p).1, ((polarCoord.symm p).2, z))) =
          (∫ r in Set.Ioi (0 : ℝ),
              halfBallPlane.indicator planeIntegrand (r, z)) *
            ∫ theta in Set.Ioo (-Real.pi) Real.pi, (1 : ℝ) := by
      rw [polarCoord_target]
      calc
        _ = ∫ p in Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-Real.pi) Real.pi,
            halfBallPlane.indicator planeIntegrand (p.1, z) *
              (1 : ℝ) := by
          apply setIntegral_congr_fun
            (measurableSet_Ioi.prod measurableSet_Ioo)
          intro p hp'
          simpa [G] using first_polar_pointwise z p hp'
        _ = _ := by
          exact setIntegral_prod_mul
            (fun r : ℝ => halfBallPlane.indicator planeIntegrand (r, z))
            (fun _theta : ℝ => (1 : ℝ))
            (Set.Ioi (0 : ℝ)) (Set.Ioo (-Real.pi) Real.pi)
    rw [hprod, angular_full] at hp
    exact hp.symm
  simp_rw [hxy]
  rw [integral_mul_const]
  congr 1
  rw [← integral_indicator halfBallPlane_measurable]
  have hsub : halfBallPlane ⊆ ballPlane := by
    intro q hq
    exact hq.2
  have hJint : Integrable (halfBallPlane.indicator planeIntegrand) := by
    rw [integrable_indicator_iff halfBallPlane_measurable]
    exact
      (planeIntegrand_continuous.continuousOn.integrableOn_compact
        ballPlane_compact).mono_set hsub
  have hfub :
      (∫ q : ℝ × ℝ, halfBallPlane.indicator planeIntegrand q) =
        ∫ z : ℝ, ∫ r : ℝ,
          halfBallPlane.indicator planeIntegrand (r, z) := by
    exact MeasureTheory.integral_prod_symm
      (halfBallPlane.indicator planeIntegrand) hJint
  rw [hfub]
  apply integral_congr_ae
  filter_upwards [] with z
  rw [← integral_indicator measurableSet_Ioi]
  apply integral_congr_ae
  filter_upwards [] with r
  by_cases hr : 0 < r
  · simp [Set.indicator, hr]
  · have hnot : (r, z) ∉ halfBallPlane := by
      intro h
      exact hr h.1
    simp [Set.indicator, hr, hnot]

private theorem cos_pos_iff_in_half
    {theta : ℝ} (htheta : theta ∈ Set.Ioo (-Real.pi) Real.pi) :
    0 < Real.cos theta ↔
      theta ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
  constructor
  · intro hc
    constructor
    · by_contra hn
      have hle : theta ≤ -(Real.pi / 2) := le_of_not_gt hn
      have hneg : Real.cos theta ≤ 0 := by
        rw [← Real.cos_neg theta]
        have h1 : Real.pi / 2 ≤ -theta := by linarith
        have h2 : -theta ≤ Real.pi + Real.pi / 2 := by
          linarith [htheta.1, Real.pi_pos]
        exact Real.cos_nonpos_of_pi_div_two_le_of_le h1 h2
      linarith
    · by_contra hn
      have hle : Real.pi / 2 ≤ theta := le_of_not_gt hn
      have h2 : theta ≤ Real.pi + Real.pi / 2 := by
        linarith [htheta.2, Real.pi_pos]
      have hneg := Real.cos_nonpos_of_pi_div_two_le_of_le hle h2
      linarith
  · exact Real.cos_pos_of_mem_Ioo

private theorem second_polar_pointwise (p : ℝ × ℝ)
    (hp : p ∈ polarCoord.target) :
    p.1 • halfBallPlane.indicator planeIntegrand (polarCoord.symm p) =
      (Set.Iic (Real.sin p.2)).indicator
          (fun r => r ^ 3 * Real.cos p.2) p.1 *
        (Set.Ioo (0 : ℝ) (Real.pi / 2)).indicator
          (fun _psi => (1 : ℝ)) p.2 := by
  rcases p with ⟨r, psi⟩
  have hr : 0 < r := hp.1
  have hpsi : psi ∈ Set.Ioo (-Real.pi) Real.pi := hp.2
  have htrig :
      (r * Real.cos psi) ^ 2 + (r * Real.sin psi) ^ 2 = r ^ 2 := by
    calc
      _ = r ^ 2 * (Real.cos psi ^ 2 + Real.sin psi ^ 2) := by ring
      _ = r ^ 2 := by rw [Real.cos_sq_add_sin_sq]; ring
  have hmem :
      polarCoord.symm (r, psi) ∈ halfBallPlane ↔
        r ≤ Real.sin psi ∧
          psi ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
    rw [polarCoord_symm_apply]
    simp only [halfBallPlane, Set.mem_setOf_eq]
    rw [htrig]
    have hcos :
        0 < r * Real.cos psi ↔ 0 < Real.cos psi :=
      mul_pos_iff_of_pos_left hr
    have hrad :
        r ^ 2 ≤ r * Real.sin psi ↔ r ≤ Real.sin psi := by
      constructor <;> intro h <;> nlinarith
    rw [hcos, hrad]
    constructor
    · rintro ⟨hc, hle⟩
      have hang := (cos_pos_iff_in_half hpsi).mp hc
      have hs : 0 < Real.sin psi := lt_of_lt_of_le hr hle
      have hpsi0 : 0 < psi := by
        by_contra hn
        have hnon : Real.sin psi ≤ 0 :=
          Real.sin_nonpos_of_nonpos_of_neg_pi_le
            (le_of_not_gt hn) hpsi.1.le
        linarith
      exact ⟨hle, hpsi0, hang.2⟩
    · rintro ⟨hle, hangle⟩
      exact ⟨(cos_pos_iff_in_half hpsi).mpr
          ⟨by linarith [hangle.1, Real.pi_pos], hangle.2⟩, hle⟩
  simp only [Set.indicator, hmem, Set.mem_Iic, smul_eq_mul]
  by_cases hrle : r ≤ Real.sin psi
  · by_cases hangle : psi ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)
    · simp only [hrle, hangle, and_self, if_true]
      rw [polarCoord_symm_apply]
      simp only [planeIntegrand]
      rw [htrig, Real.sqrt_sq_eq_abs, abs_of_pos hr]
      ring
    · simp [hrle, hangle]
  · simp [hrle]

private def secondParamRegion : Set (ℝ × ℝ) :=
  {p | 0 < p.1 ∧ p.1 ≤ Real.sin p.2 ∧
    p.2 ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)}

private def secondIntegrand (p : ℝ × ℝ) : ℝ :=
  p.1 ^ 3 * Real.cos p.2

private theorem secondParamRegion_measurable :
    MeasurableSet secondParamRegion := by
  simpa only [secondParamRegion, Set.setOf_and] using
    (isOpen_lt continuous_const continuous_fst).measurableSet.inter
      ((isClosed_le continuous_fst
        (Real.continuous_sin.comp continuous_snd)).measurableSet.inter
        (measurableSet_Ioo.preimage continuous_snd.measurable))

private theorem secondParamRegion_compact_support :
    secondParamRegion ⊆
      Set.Icc ((0 : ℝ), (0 : ℝ)) (1, Real.pi / 2) := by
  intro p hp
  exact ⟨⟨hp.1.le, hp.2.2.1.le⟩,
    ⟨hp.2.1.trans (Real.sin_le_one p.2), hp.2.2.2.le⟩⟩

private theorem secondIntegrand_continuous :
    Continuous secondIntegrand := by
  exact (continuous_fst.pow 3).mul
    (Real.continuous_cos.comp continuous_snd)

private theorem plane_to_second_integral :
    (∫ q in halfBallPlane, planeIntegrand q) =
      ∫ psi in (0 : ℝ)..Real.pi / 2,
        ∫ r in (0 : ℝ)..Real.sin psi,
          r ^ 3 * Real.cos psi := by
  have hp := integral_comp_polarCoord_symm
    (halfBallPlane.indicator planeIntegrand)
  rw [integral_indicator halfBallPlane_measurable] at hp
  have hpolar :
      (∫ p in polarCoord.target,
          p.1 • halfBallPlane.indicator planeIntegrand
            (polarCoord.symm p)) =
        ∫ p : ℝ × ℝ,
          secondParamRegion.indicator secondIntegrand p := by
    rw [polarCoord_target]
    calc
      _ = ∫ p in Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-Real.pi) Real.pi,
          (Set.Iic (Real.sin p.2)).indicator
              (fun r => r ^ 3 * Real.cos p.2) p.1 *
            (Set.Ioo (0 : ℝ) (Real.pi / 2)).indicator
              (fun _psi => (1 : ℝ)) p.2 := by
        apply setIntegral_congr_fun
          (measurableSet_Ioi.prod measurableSet_Ioo)
        intro p hp'
        exact second_polar_pointwise p hp'
      _ = ∫ p in Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-Real.pi) Real.pi,
          secondParamRegion.indicator secondIntegrand p := by
        apply setIntegral_congr_fun
          (measurableSet_Ioi.prod measurableSet_Ioo)
        intro p hp'
        have hr : 0 < p.1 := hp'.1
        change
          (Set.Iic (Real.sin p.2)).indicator
              (fun r => r ^ 3 * Real.cos p.2) p.1 *
            (Set.Ioo (0 : ℝ) (Real.pi / 2)).indicator
              (fun _psi => (1 : ℝ)) p.2 =
            secondParamRegion.indicator secondIntegrand p
        by_cases hrle : p.1 ≤ Real.sin p.2
        · by_cases hangle : p.2 ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)
          · have hparam : p ∈ secondParamRegion :=
              ⟨hr, hrle, hangle⟩
            rw [Set.indicator_of_mem
                (s := Set.Iic (Real.sin p.2)) hrle,
              Set.indicator_of_mem
                (s := Set.Ioo (0 : ℝ) (Real.pi / 2)) hangle,
              Set.indicator_of_mem
                (s := secondParamRegion) hparam]
            simp [secondIntegrand]
          · have hparam : p ∉ secondParamRegion := by
              intro h
              exact hangle h.2.2
            rw [Set.indicator_of_mem
                (s := Set.Iic (Real.sin p.2)) hrle,
              Set.indicator_of_notMem
                (s := Set.Ioo (0 : ℝ) (Real.pi / 2)) hangle,
              Set.indicator_of_notMem
                (s := secondParamRegion) hparam]
            simp
        · have hparam : p ∉ secondParamRegion := by
            intro h
            exact hrle h.2.1
          rw [Set.indicator_of_notMem
              (s := Set.Iic (Real.sin p.2)) hrle,
            Set.indicator_of_notMem
              (s := secondParamRegion) hparam]
          simp
      _ = ∫ p : ℝ × ℝ,
          secondParamRegion.indicator secondIntegrand p := by
        rw [← integral_indicator
          (measurableSet_Ioi.prod measurableSet_Ioo)]
        apply integral_congr_ae
        filter_upwards [] with p
        by_cases hparam : p ∈ secondParamRegion
        · have htarget :
              p ∈ Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-Real.pi) Real.pi := by
            exact ⟨hparam.1,
              ⟨by linarith [hparam.2.2.1, Real.pi_pos],
                by linarith [hparam.2.2.2, Real.pi_pos]⟩⟩
          rw [Set.indicator_of_mem htarget,
            Set.indicator_of_mem hparam]
        · rw [Set.indicator_of_notMem hparam]
          by_cases htarget :
              p ∈ Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-Real.pi) Real.pi
          · rw [Set.indicator_of_mem htarget,
              Set.indicator_of_notMem hparam]
          · rw [Set.indicator_of_notMem htarget]
  rw [hpolar] at hp
  have hparamInt :
      Integrable (secondParamRegion.indicator secondIntegrand) := by
    rw [integrable_indicator_iff secondParamRegion_measurable]
    exact
      (secondIntegrand_continuous.continuousOn.integrableOn_compact
        (isCompact_Icc :
          IsCompact
            (Set.Icc ((0 : ℝ), (0 : ℝ))
              (1, Real.pi / 2)))).mono_set
        secondParamRegion_compact_support
  have hfub :
      (∫ p : ℝ × ℝ,
          secondParamRegion.indicator secondIntegrand p) =
        ∫ psi : ℝ, ∫ r : ℝ,
          secondParamRegion.indicator secondIntegrand (r, psi) := by
    exact MeasureTheory.integral_prod_symm
      (secondParamRegion.indicator secondIntegrand) hparamInt
  rw [hfub] at hp
  have hinner (psi : ℝ) :
      (∫ r : ℝ,
          secondParamRegion.indicator secondIntegrand (r, psi)) =
        (Set.Ioo (0 : ℝ) (Real.pi / 2)).indicator
          (fun psi =>
            ∫ r in (0 : ℝ)..Real.sin psi,
              r ^ 3 * Real.cos psi) psi := by
    by_cases hangle : psi ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)
    · rw [Set.indicator_of_mem hangle]
      have hsin : 0 ≤ Real.sin psi :=
        (Real.sin_pos_of_pos_of_lt_pi hangle.1
          (by linarith [hangle.2, Real.pi_pos])).le
      rw [intervalIntegral.integral_of_le hsin]
      rw [← integral_indicator measurableSet_Ioc]
      apply integral_congr_ae
      filter_upwards [] with r
      simp [secondParamRegion, secondIntegrand, hangle.1, hangle.2,
        Set.indicator, Set.mem_Ioc]
    · rw [Set.indicator_of_notMem hangle]
      apply integral_eq_zero_of_ae
      filter_upwards [] with r
      have hnot : (r, psi) ∉ secondParamRegion := by
        intro h
        exact hangle h.2.2
      rw [Set.indicator_of_notMem hnot]
      simp
  simp_rw [hinner] at hp
  rw [integral_indicator measurableSet_Ioo] at hp
  have hangleInterval :
      (∫ psi in Set.Ioo (0 : ℝ) (Real.pi / 2),
        ∫ r in (0 : ℝ)..Real.sin psi,
          r ^ 3 * Real.cos psi) =
        ∫ psi in (0 : ℝ)..Real.pi / 2,
          ∫ r in (0 : ℝ)..Real.sin psi,
            r ^ 3 * Real.cos psi := by
    calc
      _ = ∫ psi in Set.Ioc (0 : ℝ) (Real.pi / 2),
          ∫ r in (0 : ℝ)..Real.sin psi,
            r ^ 3 * Real.cos psi :=
        (integral_Ioc_eq_integral_Ioo
          (f := fun psi : ℝ =>
            ∫ r in (0 : ℝ)..Real.sin psi,
              r ^ 3 * Real.cos psi)).symm
      _ = _ := by
        rw [intervalIntegral.integral_of_le]
        positivity
  rw [hangleInterval] at hp
  exact hp.symm

private theorem radialNorm_triple :
    radialNormIntegral =
      ∫ phi in (0 : ℝ)..2 * Real.pi,
        ∫ psi in (0 : ℝ)..Real.pi / 2,
          ∫ r in (0 : ℝ)..Real.sin psi,
            r * r ^ 2 * Real.cos psi := by
  rw [radialNorm_to_plane, plane_to_second_integral]
  rw [show (fun psi : ℝ =>
      ∫ r in (0 : ℝ)..Real.sin psi,
        r * r ^ 2 * Real.cos psi) =
      fun psi =>
        ∫ r in (0 : ℝ)..Real.sin psi,
          r ^ 3 * Real.cos psi by
    funext psi
    apply intervalIntegral.integral_congr
    intro r hr
    ring]
  rw [intervalIntegral.integral_const]
  simp only [smul_eq_mul]
  ring

private theorem radial_inner_value (psi : ℝ) :
    (∫ r in (0 : ℝ)..Real.sin psi,
      r * r ^ 2 * Real.cos psi) =
      1 / 4 * Real.sin psi ^ 4 * Real.cos psi := by
  rw [show (fun r : ℝ => r * r ^ 2 * Real.cos psi) =
      fun r => Real.cos psi * r ^ 3 by
    funext r
    ring]
  rw [intervalIntegral.integral_const_mul, integral_pow]
  norm_num
  ring

private theorem psi_sin_four_cos :
    (∫ psi in (0 : ℝ)..Real.pi / 2,
      Real.sin psi ^ 4 * Real.cos psi) = 1 / 5 := by
  have h :=
    integral_sin_pow_mul_cos_pow_odd
      (a := (0 : ℝ)) (b := Real.pi / 2) 4 0
  norm_num [Real.sin_zero, Real.sin_pi_div_two, integral_pow] at h
  simpa using h

private theorem reduced_nested_value :
    (∫ phi in (0 : ℝ)..2 * Real.pi,
      ∫ psi in (0 : ℝ)..Real.pi / 2,
        Real.sin psi ^ 4 * Real.cos psi) =
      2 * Real.pi / 5 := by
  simp_rw [psi_sin_four_cos]
  rw [intervalIntegral.integral_const]
  simp only [smul_eq_mul]
  ring

private theorem triple_nested_value :
    (∫ phi in (0 : ℝ)..2 * Real.pi,
      ∫ psi in (0 : ℝ)..Real.pi / 2,
        ∫ r in (0 : ℝ)..Real.sin psi,
          r * r ^ 2 * Real.cos psi) =
      Real.pi / 10 := by
  simp_rw [radial_inner_value]
  have hpsi :
      (∫ psi in (0 : ℝ)..Real.pi / 2,
        1 / 4 * Real.sin psi ^ 4 * Real.cos psi) = 1 / 20 := by
    rw [show (fun psi : ℝ =>
        1 / 4 * Real.sin psi ^ 4 * Real.cos psi) =
      fun psi => (1 / 4 : ℝ) *
        (Real.sin psi ^ 4 * Real.cos psi) by
      funext psi
      ring]
    rw [intervalIntegral.integral_const_mul, psi_sin_four_cos]
    norm_num
  simp_rw [hpsi]
  rw [intervalIntegral.integral_const]
  simp only [smul_eq_mul]
  ring

private theorem radialNorm_value :
    radialNormIntegral = Real.pi / 10 := by
  rw [radialNorm_triple, triple_nested_value]

theorem gap1 (r phi psi : ℝ) :
    let p := sphericalMap r phi psi
    p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2 = p.2.2 ↔
      r = 0 ∨ r = Real.sin psi := by
  dsimp only
  change
    (r * Real.cos phi * Real.cos psi) ^ 2 +
        (r * Real.sin phi * Real.cos psi) ^ 2 +
        (r * Real.sin psi) ^ 2 =
      r * Real.sin psi ↔
        r = 0 ∨ r = Real.sin psi
  have hnorm :
      (r * Real.cos phi * Real.cos psi) ^ 2 +
          (r * Real.sin phi * Real.cos psi) ^ 2 +
          (r * Real.sin psi) ^ 2 = r ^ 2 := by
    calc
      _ = r ^ 2 *
          ((Real.cos phi ^ 2 + Real.sin phi ^ 2) *
            Real.cos psi ^ 2 + Real.sin psi ^ 2) := by ring
      _ = r ^ 2 := by
        rw [Real.cos_sq_add_sin_sq, one_mul,
          Real.cos_sq_add_sin_sq]
        ring
  rw [hnorm]
  constructor
  · intro h
    have hz : r * (r - Real.sin psi) = 0 := by nlinarith
    rcases mul_eq_zero.mp hz with hr | hr
    · exact Or.inl hr
    · exact Or.inr (by linarith)
  · rintro (rfl | hr)
    · simp
    · rw [hr]
      ring

theorem gap2 :
    sphericalDomain =
      {p | 0 ≤ p.1 ∧ p.1 ≤ 2 * Real.pi ∧
        0 ≤ p.2.1 ∧ p.2.1 ≤ Real.pi / 2 ∧
        0 ≤ p.2.2 ∧ p.2.2 ≤ Real.sin p.2.1} := by
  rfl

theorem gap3 (r psi : ℝ) (hr : 0 ≤ r)
    (hpsi₀ : 0 ≤ psi) (hpsi₁ : psi ≤ Real.pi / 2) :
    sphericalJacobianAbs r psi = r ^ 2 * Real.cos psi := by
  unfold sphericalJacobianAbs
  rw [abs_of_nonneg]
  exact mul_nonneg (sq_nonneg r)
    (Real.cos_nonneg_of_mem_Icc
      ⟨by linarith [Real.pi_pos], hpsi₁⟩)

theorem gap4 :
    radialNormIntegral =
      ∫ phi in (0 : ℝ)..2 * Real.pi,
        ∫ psi in (0 : ℝ)..Real.pi / 2,
          ∫ r in (0 : ℝ)..Real.sin psi,
            r * r ^ 2 * Real.cos psi := by
  exact radialNorm_triple

theorem gap5 :
    (∫ phi in (0 : ℝ)..2 * Real.pi,
        ∫ psi in (0 : ℝ)..Real.pi / 2,
          ∫ r in (0 : ℝ)..Real.sin psi,
            r * r ^ 2 * Real.cos psi) =
      1 / 4 *
        ∫ phi in (0 : ℝ)..2 * Real.pi,
          ∫ psi in (0 : ℝ)..Real.pi / 2,
            Real.sin psi ^ 4 * Real.cos psi := by
  rw [triple_nested_value, reduced_nested_value]
  ring

theorem gap6 :
    1 / 4 *
        (∫ phi in (0 : ℝ)..2 * Real.pi,
          ∫ psi in (0 : ℝ)..Real.pi / 2,
            Real.sin psi ^ 4 * Real.cos psi) =
      Real.pi / 10 := by
  rw [reduced_nested_value]
  ring

theorem gap7 :
    radialNormIntegral = Real.pi / 10 := by
  exact radialNorm_value

end

end ProofGap.Exercise4087
