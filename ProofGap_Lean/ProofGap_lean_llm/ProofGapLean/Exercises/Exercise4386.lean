import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise4386

noncomputable section

open MeasureTheory
open scoped Interval Pointwise

abbrev Vec3 := ℝ × ℝ × ℝ
abbrev SpaceTimeField := Vec3 → ℝ → ℝ

def dot (p q : Vec3) : ℝ :=
  p.1 * q.1 + p.2.1 * q.2.1 + p.2.2 * q.2.2

def unitBall : Set Vec3 :=
  {p | p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2 ≤ 1}

def ball (t : ℝ) : Set Vec3 :=
  {p | p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2 ≤ t ^ 2}

def sphere (t : ℝ) : Set Vec3 :=
  {p | p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2 = t ^ 2}

def scalePoint (t : ℝ) (p : Vec3) : Vec3 :=
  (t * p.1, t * p.2.1, t * p.2.2)

def ballIntegral (f : SpaceTimeField) (t : ℝ) : ℝ :=
  ∫ p in ball t, f p t

def unitBallPullback (f : SpaceTimeField) (t : ℝ) : ℝ :=
  ∫ q in unitBall, |t| ^ 3 * f (scalePoint t q) t

def spatialGradient (f : SpaceTimeField) (p : Vec3) (t : ℝ) : Vec3 :=
  (deriv (fun x => f (x, p.2.1, p.2.2) t) p.1,
    deriv (fun y => f (p.1, y, p.2.2) t) p.2.1,
    deriv (fun z => f (p.1, p.2.1, z) t) p.2.2)

def timeDerivative (f : SpaceTimeField) (p : Vec3) (t : ℝ) : ℝ :=
  deriv (fun s => f p s) t

def divergence (F : Vec3 → Vec3) (p : Vec3) : ℝ :=
  deriv (fun x => (F (x, p.2.1, p.2.2)).1) p.1 +
    deriv (fun y => (F (p.1, y, p.2.2)).2.1) p.2.1 +
    deriv (fun z => (F (p.1, p.2.1, z)).2.2) p.2.2

def productVectorField (f : SpaceTimeField) (t : ℝ) (p : Vec3) : Vec3 :=
  (f p t * p.1, f p t * p.2.1, f p t * p.2.2)

def scalingDerivativeCore (f : SpaceTimeField) (t : ℝ) (q : Vec3) : ℝ :=
  t ^ 3 * dot (spatialGradient f (scalePoint t q) t) q +
    3 * t ^ 2 * f (scalePoint t q) t

def productDivergence (f : SpaceTimeField) (t : ℝ) (p : Vec3) : ℝ :=
  divergence (productVectorField f t) p

def productDivergenceVolume (f : SpaceTimeField) (t : ℝ) : ℝ :=
  ∫ p in ball t, productDivergence f t p

def timeDerivativeVolume (f : SpaceTimeField) (t : ℝ) : ℝ :=
  ∫ p in ball t, timeDerivative f p t

def sphereNormal (t : ℝ) (p : Vec3) : Vec3 :=
  (p.1 / t, p.2.1 / t, p.2.2 / t)

def sphereParam (t φ θ : ℝ) : Vec3 :=
  (t * Real.cos φ * Real.cos θ,
    t * Real.cos φ * Real.sin θ,
    t * Real.sin φ)

def sphereSurfaceIntegral (f : SpaceTimeField) (t : ℝ) : ℝ :=
  ∫ φ in -Real.pi / 2..Real.pi / 2,
    ∫ θ in (0 : ℝ)..2 * Real.pi,
      t ^ 2 * Real.cos φ * f (sphereParam t φ θ) t

def radialFlux (f : SpaceTimeField) (t : ℝ) : ℝ :=
  ∫ φ in -Real.pi / 2..Real.pi / 2,
    ∫ θ in (0 : ℝ)..2 * Real.pi,
      t ^ 2 * Real.cos φ *
        dot (productVectorField f t (sphereParam t φ θ))
          (sphereNormal t (sphereParam t φ θ))

def IsC1 (f : SpaceTimeField) : Prop :=
  ContDiff ℝ 1 (fun z : Vec3 × ℝ => f z.1 z.2)

open Set Filter
open scoped Topology

/-! The proof below derives the required moving-ball formula from two planar polar changes
of variables and a compact-interval Leibniz rule. -/

private theorem ball_closed (R : ℝ) : IsClosed (ball R) := by
  exact isClosed_le
    (((continuous_fst.pow 2).add
      ((continuous_fst.comp continuous_snd).pow 2)).add
      ((continuous_snd.comp continuous_snd).pow 2))
    continuous_const

private theorem ball_compact {R : ℝ} (hR : 0 < R) :
    IsCompact (ball R) := by
  apply (isCompact_Icc :
    IsCompact
      (Icc ((-R : ℝ), ((-R : ℝ), (-R : ℝ)))
        (R, (R, R)))).of_isClosed_subset (ball_closed R)
  intro p hp
  change p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2 ≤ R ^ 2 at hp
  have hx : p.1 ^ 2 ≤ R ^ 2 := by
    nlinarith [sq_nonneg p.2.1, sq_nonneg p.2.2]
  have hy : p.2.1 ^ 2 ≤ R ^ 2 := by
    nlinarith [sq_nonneg p.1, sq_nonneg p.2.2]
  have hz : p.2.2 ^ 2 ≤ R ^ 2 := by
    nlinarith [sq_nonneg p.1, sq_nonneg p.2.1]
  exact
    ⟨⟨by nlinarith [sq_nonneg (p.1 + R)],
        by nlinarith [sq_nonneg (p.2.1 + R)],
        by nlinarith [sq_nonneg (p.2.2 + R)]⟩,
      ⟨by nlinarith [sq_nonneg (p.1 - R)],
        by nlinarith [sq_nonneg (p.2.1 - R)],
        by nlinarith [sq_nonneg (p.2.2 - R)]⟩⟩

/- Coordinates are `(z, (ρ, θ))`. -/
private def cylindricalRegion (R : ℝ) :
    Set (ℝ × (ℝ × ℝ)) :=
  {q | 0 < q.2.1 ∧
    q.2.1 ^ 2 + q.1 ^ 2 ≤ R ^ 2 ∧
    q.2.2 ∈ Ioo (-Real.pi) Real.pi}

private def cylindricalIntegrand (g : Vec3 → ℝ)
    (q : ℝ × (ℝ × ℝ)) : ℝ :=
  q.2.1 *
    g (q.2.1 * Real.cos q.2.2,
      q.2.1 * Real.sin q.2.2,
      q.1)

private theorem cylindricalRegion_measurable (R : ℝ) :
    MeasurableSet (cylindricalRegion R) := by
  exact
    (isOpen_lt continuous_const
      (continuous_fst.comp continuous_snd)).measurableSet.inter
      ((isClosed_le
        (((continuous_fst.comp continuous_snd).pow 2).add
          (continuous_fst.pow 2))
        continuous_const).measurableSet.inter
        (measurableSet_Ioo.preimage
          (continuous_snd.comp continuous_snd).measurable))

private theorem cylindricalRegion_subset_box {R : ℝ} (hR : 0 < R) :
    cylindricalRegion R ⊆
      Icc ((-R : ℝ), ((0 : ℝ), -Real.pi))
        (R, (R, Real.pi)) := by
  intro q hq
  have hrho_sq : q.2.1 ^ 2 ≤ R ^ 2 := by
    nlinarith [hq.2.1, sq_nonneg q.1]
  have hz_sq : q.1 ^ 2 ≤ R ^ 2 := by
    nlinarith [hq.2.1, sq_nonneg q.2.1]
  exact
    ⟨⟨by nlinarith [sq_nonneg (q.1 + R)],
        hq.1.le, hq.2.2.1.le⟩,
      ⟨by nlinarith [sq_nonneg (q.1 - R)],
        by nlinarith [sq_nonneg (q.2.1 - R)],
        hq.2.2.2.le⟩⟩

private theorem cylindricalIntegrand_continuous
    {g : Vec3 → ℝ} (hg : Continuous g) :
    Continuous (cylindricalIntegrand g) := by
  unfold cylindricalIntegrand
  fun_prop

private theorem cylindrical_indicator_integrable
    {g : Vec3 → ℝ} (hg : Continuous g)
    {R : ℝ} (hR : 0 < R) :
    Integrable ((cylindricalRegion R).indicator
      (cylindricalIntegrand g)) := by
  rw [integrable_indicator_iff (cylindricalRegion_measurable R)]
  exact
    ((cylindricalIntegrand_continuous hg).continuousOn.integrableOn_compact
      (isCompact_Icc :
        IsCompact
          (Icc ((-R : ℝ), ((0 : ℝ), -Real.pi))
            (R, (R, Real.pi))))).mono_set
      (cylindricalRegion_subset_box hR)

private theorem first_polar_pointwise
    (g : Vec3 → ℝ) (R z : ℝ) (p : ℝ × ℝ)
    (hp : p ∈ polarCoord.target) :
    p.1 • (ball R).indicator g
        ((polarCoord.symm p).1, ((polarCoord.symm p).2, z)) =
      (cylindricalRegion R).indicator
        (cylindricalIntegrand g) (z, p) := by
  rcases p with ⟨ρ, θ⟩
  have hρ : 0 < ρ := hp.1
  have hθ : θ ∈ Ioo (-Real.pi) Real.pi := hp.2
  have htrig :
      (ρ * Real.cos θ) ^ 2 + (ρ * Real.sin θ) ^ 2 = ρ ^ 2 := by
    calc
      _ = ρ ^ 2 * (Real.cos θ ^ 2 + Real.sin θ ^ 2) := by ring
      _ = ρ ^ 2 := by rw [Real.cos_sq_add_sin_sq]; ring
  have hmem :
      ((polarCoord.symm (ρ, θ)).1,
          ((polarCoord.symm (ρ, θ)).2, z)) ∈ ball R ↔
        (z, (ρ, θ)) ∈ cylindricalRegion R := by
    rw [polarCoord_symm_apply]
    simp only [ball, cylindricalRegion, mem_setOf_eq]
    rw [show
      (ρ * Real.cos θ) ^ 2 +
          (ρ * Real.sin θ) ^ 2 + z ^ 2 =
        ((ρ * Real.cos θ) ^ 2 +
          (ρ * Real.sin θ) ^ 2) + z ^ 2 by ring,
      htrig]
    simp [hρ, hθ]
  by_cases h : (z, (ρ, θ)) ∈ cylindricalRegion R
  · have h' :
        ((polarCoord.symm (ρ, θ)).1,
          ((polarCoord.symm (ρ, θ)).2, z)) ∈ ball R :=
      hmem.mpr h
    rw [indicator_of_mem h, indicator_of_mem h']
    simp only [smul_eq_mul, cylindricalIntegrand]
    rw [polarCoord_symm_apply]
  · have h' :
        ((polarCoord.symm (ρ, θ)).1,
          ((polarCoord.symm (ρ, θ)).2, z)) ∉ ball R := by
      intro hh
      exact h (hmem.mp hh)
    rw [indicator_of_notMem h, indicator_of_notMem h']
    simp

private theorem ball_to_cylindrical
    (g : Vec3 → ℝ) (hg : Continuous g)
    (R : ℝ) (hR : 0 < R) :
    (∫ p in ball R, g p) =
      ∫ q in cylindricalRegion R, cylindricalIntegrand g q := by
  have hK : Integrable ((ball R).indicator g) := by
    rw [integrable_indicator_iff (ball_closed R).measurableSet]
    exact hg.continuousOn.integrableOn_compact (ball_compact hR)
  let e :=
    (MeasurableEquiv.prodAssoc :
      ((ℝ × ℝ) × ℝ) ≃ᵐ (ℝ × (ℝ × ℝ)))
  have hK' : Integrable
      (fun q : (ℝ × ℝ) × ℝ =>
        (ball R).indicator g (e q)) := by
    simpa only [Function.comp_apply] using
      (volume_preserving_prodAssoc.integrable_comp_emb
        e.measurableEmbedding).2 hK
  have hreassoc :
      (∫ q : (ℝ × ℝ) × ℝ,
          (ball R).indicator g (e q)) =
        ∫ p : ℝ × (ℝ × ℝ), (ball R).indicator g p :=
    volume_preserving_prodAssoc.integral_comp'
      ((ball R).indicator g)
  rw [← integral_indicator (ball_closed R).measurableSet]
  change (∫ p : ℝ × (ℝ × ℝ), (ball R).indicator g p) = _
  rw [← hreassoc]
  have hFubini₁ :
      (∫ q : (ℝ × ℝ) × ℝ,
          (ball R).indicator g (e q)) =
        ∫ z : ℝ, ∫ q : ℝ × ℝ,
          (ball R).indicator g (e (q, z)) := by
    exact MeasureTheory.integral_prod_symm
      (fun q : (ℝ × ℝ) × ℝ =>
        (ball R).indicator g (e q)) hK'
  rw [hFubini₁]
  change
    (∫ z : ℝ, ∫ q : ℝ × ℝ,
      (ball R).indicator g (q.1, (q.2, z))) = _
  have hxy (z : ℝ) :
      (∫ q : ℝ × ℝ,
          (ball R).indicator g (q.1, (q.2, z))) =
        ∫ p in polarCoord.target,
          (cylindricalRegion R).indicator
            (cylindricalIntegrand g) (z, p) := by
    have hp := integral_comp_polarCoord_symm
      (fun q : ℝ × ℝ =>
        (ball R).indicator g (q.1, (q.2, z)))
    calc
      _ = ∫ p in polarCoord.target,
          p.1 • (ball R).indicator g
            ((polarCoord.symm p).1,
              ((polarCoord.symm p).2, z)) := hp.symm
      _ = _ := by
        apply setIntegral_congr_fun polarCoord.open_target.measurableSet
        intro p hp'
        exact first_polar_pointwise g R z p hp'
  simp_rw [hxy]
  rw [polarCoord_target]
  have hC :=
    cylindrical_indicator_integrable hg hR
  rw [← integral_indicator (cylindricalRegion_measurable R)]
  have hFub :
      (∫ q : ℝ × (ℝ × ℝ),
          (cylindricalRegion R).indicator
            (cylindricalIntegrand g) q) =
        ∫ z : ℝ, ∫ p : ℝ × ℝ,
          (cylindricalRegion R).indicator
            (cylindricalIntegrand g) (z, p) :=
    MeasureTheory.integral_prod
      ((cylindricalRegion R).indicator
        (cylindricalIntegrand g)) hC
  rw [hFub]
  apply integral_congr_ae
  filter_upwards [] with z
  rw [← integral_indicator
    (measurableSet_Ioi.prod measurableSet_Ioo)]
  apply integral_congr_ae
  filter_upwards [] with p
  by_cases hp :
      p ∈ Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi
  · rw [indicator_of_mem hp]
  · rw [indicator_of_notMem hp]
    have hnot :
        (z, p) ∉ cylindricalRegion R := by
      intro h
      exact hp ⟨h.1, h.2.2⟩
    rw [indicator_of_notMem hnot]

private def sphericalRegion (R : ℝ) :
    Set (ℝ × (ℝ × ℝ)) :=
  {q | 0 < q.1 ∧ q.1 ≤ R ∧
    q.2.1 ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2) ∧
    q.2.2 ∈ Ioo (-Real.pi) Real.pi}

private def sphericalIntegrand (g : Vec3 → ℝ)
    (q : ℝ × (ℝ × ℝ)) : ℝ :=
  q.1 ^ 2 * Real.cos q.2.1 *
    g (sphereParam q.1 q.2.1 q.2.2)

private def angularIntegrand (g : Vec3 → ℝ)
    (r φ θ : ℝ) : ℝ :=
  r ^ 2 * Real.cos φ * g (sphereParam r φ θ)

private theorem sphericalRegion_measurable (R : ℝ) :
    MeasurableSet (sphericalRegion R) := by
  exact
    (isOpen_lt continuous_const continuous_fst).measurableSet.inter
      ((isClosed_le continuous_fst continuous_const).measurableSet.inter
        ((measurableSet_Ioo.preimage
          (continuous_fst.comp continuous_snd).measurable).inter
          (measurableSet_Ioo.preimage
            (continuous_snd.comp continuous_snd).measurable)))

private theorem sphericalRegion_subset_box {R : ℝ} :
    sphericalRegion R ⊆
      Icc ((0 : ℝ), (-(Real.pi / 2), -Real.pi))
        (R, (Real.pi / 2, Real.pi)) := by
  intro q hq
  exact
    ⟨⟨hq.1.le, hq.2.2.1.1.le, hq.2.2.2.1.le⟩,
      ⟨hq.2.1, hq.2.2.1.2.le, hq.2.2.2.2.le⟩⟩

private theorem sphericalIntegrand_continuous
    {g : Vec3 → ℝ} (hg : Continuous g) :
    Continuous (sphericalIntegrand g) := by
  unfold sphericalIntegrand sphereParam
  fun_prop

private theorem spherical_indicator_integrable
    {g : Vec3 → ℝ} (hg : Continuous g)
    {R : ℝ} :
    Integrable ((sphericalRegion R).indicator
      (sphericalIntegrand g)) := by
  rw [integrable_indicator_iff (sphericalRegion_measurable R)]
  exact
    ((sphericalIntegrand_continuous hg).continuousOn.integrableOn_compact
      (isCompact_Icc :
        IsCompact
          (Icc ((0 : ℝ), (-(Real.pi / 2), -Real.pi))
            (R, (Real.pi / 2, Real.pi))))).mono_set
      sphericalRegion_subset_box

private theorem cos_pos_iff_in_half
    {φ : ℝ} (hφ : φ ∈ Ioo (-Real.pi) Real.pi) :
    0 < Real.cos φ ↔
      φ ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
  constructor
  · intro hc
    constructor
    · by_contra hn
      have hle : φ ≤ -(Real.pi / 2) := le_of_not_gt hn
      have hneg : Real.cos φ ≤ 0 := by
        rw [← Real.cos_neg φ]
        have h1 : Real.pi / 2 ≤ -φ := by linarith
        have h2 : -φ ≤ Real.pi + Real.pi / 2 := by
          linarith [hφ.1, Real.pi_pos]
        exact Real.cos_nonpos_of_pi_div_two_le_of_le h1 h2
      linarith
    · by_contra hn
      have hle : Real.pi / 2 ≤ φ := le_of_not_gt hn
      have h2 : φ ≤ Real.pi + Real.pi / 2 := by
        linarith [hφ.2, Real.pi_pos]
      have hneg :=
        Real.cos_nonpos_of_pi_div_two_le_of_le hle h2
      linarith
  · exact Real.cos_pos_of_mem_Ioo

private theorem second_polar_pointwise
    (g : Vec3 → ℝ) (R θ : ℝ) (hR : 0 < R)
    (p : ℝ × ℝ) (hp : p ∈ polarCoord.target) :
    p.1 • (cylindricalRegion R).indicator
        (cylindricalIntegrand g)
        ((polarCoord.symm p).2,
          ((polarCoord.symm p).1, θ)) =
      (sphericalRegion R).indicator
        (sphericalIntegrand g) (p.1, (p.2, θ)) := by
  rcases p with ⟨r, φ⟩
  have hr : 0 < r := hp.1
  have hφ : φ ∈ Ioo (-Real.pi) Real.pi := hp.2
  have htrig :
      (r * Real.cos φ) ^ 2 + (r * Real.sin φ) ^ 2 =
        r ^ 2 := by
    calc
      _ = r ^ 2 *
          (Real.cos φ ^ 2 + Real.sin φ ^ 2) := by ring
      _ = r ^ 2 := by rw [Real.cos_sq_add_sin_sq]; ring
  have hrad : r ^ 2 ≤ R ^ 2 ↔ r ≤ R := by
    constructor
    · intro h
      nlinarith [sq_nonneg (r - R)]
    · intro h
      have hprod : 0 ≤ (R - r) * (R + r) :=
        mul_nonneg (sub_nonneg.mpr h)
          (add_nonneg hR.le hr.le)
      nlinarith
  have hmem :
      ((polarCoord.symm (r, φ)).2,
          ((polarCoord.symm (r, φ)).1, θ)) ∈
          cylindricalRegion R ↔
        (r, (φ, θ)) ∈ sphericalRegion R := by
    rw [polarCoord_symm_apply]
    simp only [cylindricalRegion, sphericalRegion, mem_setOf_eq]
    rw [htrig]
    have hcos :
        0 < r * Real.cos φ ↔ 0 < Real.cos φ :=
      mul_pos_iff_of_pos_left hr
    rw [hcos, hrad, cos_pos_iff_in_half hφ]
    aesop
  by_cases h : (r, (φ, θ)) ∈ sphericalRegion R
  · have h' :
        ((polarCoord.symm (r, φ)).2,
          ((polarCoord.symm (r, φ)).1, θ)) ∈
            cylindricalRegion R :=
      hmem.mpr h
    rw [indicator_of_mem h, indicator_of_mem h']
    simp only [smul_eq_mul, cylindricalIntegrand,
      sphericalIntegrand]
    rw [polarCoord_symm_apply]
    unfold sphereParam
    ring
  · have h' :
        ((polarCoord.symm (r, φ)).2,
          ((polarCoord.symm (r, φ)).1, θ)) ∉
            cylindricalRegion R := by
      intro hh
      exact h (hmem.mp hh)
    rw [indicator_of_notMem h, indicator_of_notMem h']
    simp

private theorem cylindrical_to_spherical
    (g : Vec3 → ℝ) (hg : Continuous g)
    (R : ℝ) (hR : 0 < R) :
    (∫ q in cylindricalRegion R, cylindricalIntegrand g q) =
      ∫ q in sphericalRegion R, sphericalIntegrand g q := by
  let C : ℝ × (ℝ × ℝ) → ℝ :=
    (cylindricalRegion R).indicator (cylindricalIntegrand g)
  have hC : Integrable C :=
    cylindrical_indicator_integrable hg hR
  let ea :=
    (MeasurableEquiv.prodAssoc :
      ((ℝ × ℝ) × ℝ) ≃ᵐ (ℝ × (ℝ × ℝ)))
  have hCa : Integrable
      (fun q : (ℝ × ℝ) × ℝ => C (ea q)) := by
    simpa only [Function.comp_apply] using
      (volume_preserving_prodAssoc.integrable_comp_emb
        ea.measurableEmbedding).2 hC
  have hreassocC :
      (∫ q : (ℝ × ℝ) × ℝ, C (ea q)) =
        ∫ q : ℝ × (ℝ × ℝ), C q :=
    volume_preserving_prodAssoc.integral_comp' C
  rw [← integral_indicator (cylindricalRegion_measurable R)]
  change (∫ q : ℝ × (ℝ × ℝ), C q) = _
  rw [← hreassocC]
  have hFubC :
      (∫ q : (ℝ × ℝ) × ℝ, C (ea q)) =
        ∫ θ : ℝ, ∫ q : ℝ × ℝ, C (ea (q, θ)) := by
    exact MeasureTheory.integral_prod_symm
      (fun q : (ℝ × ℝ) × ℝ => C (ea q)) hCa
  rw [hFubC]
  change
    (∫ θ : ℝ, ∫ q : ℝ × ℝ,
      C (q.1, (q.2, θ))) = _
  have hswap (θ : ℝ) :
      (∫ q : ℝ × ℝ, C (q.1, (q.2, θ))) =
        ∫ q : ℝ × ℝ, C (q.2, (q.1, θ)) := by
    exact (MeasureTheory.integral_prod_swap
      (fun q : ℝ × ℝ => C (q.1, (q.2, θ)))).symm
  simp_rw [hswap]
  have hsecond (θ : ℝ) :
      (∫ q : ℝ × ℝ, C (q.2, (q.1, θ))) =
        ∫ p in polarCoord.target,
          (sphericalRegion R).indicator
            (sphericalIntegrand g)
            (p.1, (p.2, θ)) := by
    have hp := integral_comp_polarCoord_symm
      (fun q : ℝ × ℝ => C (q.2, (q.1, θ)))
    calc
      _ = ∫ p in polarCoord.target,
          p.1 • C
            ((polarCoord.symm p).2,
              ((polarCoord.symm p).1, θ)) := hp.symm
      _ = _ := by
        apply setIntegral_congr_fun polarCoord.open_target.measurableSet
        intro p hp'
        exact second_polar_pointwise g R θ hR p hp'
  simp_rw [hsecond]
  rw [polarCoord_target]
  let S : ℝ × (ℝ × ℝ) → ℝ :=
    (sphericalRegion R).indicator (sphericalIntegrand g)
  have hS : Integrable S :=
    spherical_indicator_integrable hg
  let es :=
    (MeasurableEquiv.prodAssoc :
      ((ℝ × ℝ) × ℝ) ≃ᵐ (ℝ × (ℝ × ℝ)))
  have hSa : Integrable
      (fun q : (ℝ × ℝ) × ℝ => S (es q)) := by
    simpa only [Function.comp_apply] using
      (volume_preserving_prodAssoc.integrable_comp_emb
        es.measurableEmbedding).2 hS
  have hreassocS :
      (∫ q : (ℝ × ℝ) × ℝ, S (es q)) =
        ∫ q : ℝ × (ℝ × ℝ), S q :=
    volume_preserving_prodAssoc.integral_comp' S
  rw [← integral_indicator (sphericalRegion_measurable R)]
  change _ = ∫ q : ℝ × (ℝ × ℝ), S q
  rw [← hreassocS]
  have hFubS :
      (∫ q : (ℝ × ℝ) × ℝ, S (es q)) =
        ∫ θ : ℝ, ∫ p : ℝ × ℝ, S (es (p, θ)) := by
    exact MeasureTheory.integral_prod_symm
      (fun q : (ℝ × ℝ) × ℝ => S (es q)) hSa
  rw [hFubS]
  apply integral_congr_ae
  filter_upwards [] with θ
  rw [← integral_indicator
    (measurableSet_Ioi.prod measurableSet_Ioo)]
  apply integral_congr_ae
  filter_upwards [] with p
  change
    (Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi).indicator
        (fun p : ℝ × ℝ =>
          (sphericalRegion R).indicator
            (sphericalIntegrand g) (p.1, (p.2, θ))) p =
      (sphericalRegion R).indicator
        (sphericalIntegrand g) (p.1, (p.2, θ))
  by_cases hp :
      p ∈ Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi
  · rw [indicator_of_mem hp]
  · rw [indicator_of_notMem hp]
    have hnot :
        (p.1, (p.2, θ)) ∉ sphericalRegion R := by
      intro h
      exact hp ⟨h.1, ⟨by
        linarith [h.2.2.1.1, Real.pi_pos],
        by linarith [h.2.2.1.2, Real.pi_pos]⟩⟩
    rw [indicator_of_notMem hnot]

private theorem sphericalRegion_eq_prod (R : ℝ) :
    sphericalRegion R =
      Ioc (0 : ℝ) R ×ˢ
        (Ioo (-(Real.pi / 2)) (Real.pi / 2) ×ˢ
          Ioo (-Real.pi) Real.pi) := by
  ext q
  simp only [sphericalRegion, mem_setOf_eq, mem_prod, mem_Ioc,
    mem_Ioo]
  tauto

private theorem angularIntegrand_continuous
    {g : Vec3 → ℝ} (hg : Continuous g) (r : ℝ) :
    Continuous (fun u : ℝ × ℝ =>
      angularIntegrand g r u.1 u.2) := by
  unfold angularIntegrand sphereParam
  fun_prop

private theorem angularIntegrableOn
    {g : Vec3 → ℝ} (hg : Continuous g) (r : ℝ) :
    IntegrableOn
      (fun u : ℝ × ℝ =>
        angularIntegrand g r u.1 u.2)
      (Ioo (-(Real.pi / 2)) (Real.pi / 2) ×ˢ
        Ioo (-Real.pi) Real.pi) := by
  apply
    ((angularIntegrand_continuous hg r).continuousOn.integrableOn_compact
      ((isCompact_Icc :
        IsCompact (Icc (-(Real.pi / 2)) (Real.pi / 2))).prod
        (isCompact_Icc :
          IsCompact (Icc (-Real.pi) Real.pi)))).mono_set
  exact prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self

private theorem angular_setIntegral_prod
    {g : Vec3 → ℝ} (hg : Continuous g) (r : ℝ) :
    (∫ u in
        Ioo (-(Real.pi / 2)) (Real.pi / 2) ×ˢ
          Ioo (-Real.pi) Real.pi,
        angularIntegrand g r u.1 u.2) =
      ∫ φ in Ioo (-(Real.pi / 2)) (Real.pi / 2),
        ∫ θ in Ioo (-Real.pi) Real.pi,
          angularIntegrand g r φ θ := by
  exact MeasureTheory.setIntegral_prod
    (fun u : ℝ × ℝ =>
      angularIntegrand g r u.1 u.2)
    (angularIntegrableOn hg r)

private theorem theta_setIntegral_eq_interval
    (g : Vec3 → ℝ) (r φ : ℝ) :
    (∫ θ in Ioo (-Real.pi) Real.pi,
        angularIntegrand g r φ θ) =
      ∫ θ in -Real.pi..Real.pi,
        angularIntegrand g r φ θ := by
  calc
    _ = ∫ θ in Ioc (-Real.pi) Real.pi,
        angularIntegrand g r φ θ :=
      (integral_Ioc_eq_integral_Ioo
        (f := fun θ : ℝ =>
          angularIntegrand g r φ θ)).symm
    _ = _ := by
      rw [intervalIntegral.integral_of_le]
      exact neg_le_self Real.pi_nonneg

private theorem phi_setIntegral_eq_interval
    (g : Vec3 → ℝ) (r : ℝ) :
    (∫ φ in Ioo (-(Real.pi / 2)) (Real.pi / 2),
        ∫ θ in -Real.pi..Real.pi,
          angularIntegrand g r φ θ) =
      ∫ φ in -(Real.pi / 2)..Real.pi / 2,
        ∫ θ in -Real.pi..Real.pi,
          angularIntegrand g r φ θ := by
  calc
    _ = ∫ φ in Ioc (-(Real.pi / 2)) (Real.pi / 2),
        ∫ θ in -Real.pi..Real.pi,
          angularIntegrand g r φ θ :=
      (integral_Ioc_eq_integral_Ioo
        (f := fun φ : ℝ =>
          ∫ θ in -Real.pi..Real.pi,
            angularIntegrand g r φ θ)).symm
    _ = _ := by
      rw [intervalIntegral.integral_of_le]
      linarith [Real.pi_nonneg]

private theorem spherical_to_triple_neg_pi
    (g : Vec3 → ℝ) (hg : Continuous g)
    (R : ℝ) (hR : 0 < R) :
    (∫ q in sphericalRegion R, sphericalIntegrand g q) =
      ∫ r in (0 : ℝ)..R,
        ∫ φ in -(Real.pi / 2)..Real.pi / 2,
          ∫ θ in -Real.pi..Real.pi,
            angularIntegrand g r φ θ := by
  have hS : IntegrableOn (sphericalIntegrand g)
      (sphericalRegion R) := by
    rw [← integrable_indicator_iff
      (sphericalRegion_measurable R)]
    exact spherical_indicator_integrable hg
  rw [sphericalRegion_eq_prod] at hS ⊢
  have hprod :
      (∫ q in
          Ioc (0 : ℝ) R ×ˢ
            (Ioo (-(Real.pi / 2)) (Real.pi / 2) ×ˢ
              Ioo (-Real.pi) Real.pi),
          sphericalIntegrand g q) =
        ∫ r in Ioc (0 : ℝ) R,
          ∫ u in
            Ioo (-(Real.pi / 2)) (Real.pi / 2) ×ˢ
              Ioo (-Real.pi) Real.pi,
            sphericalIntegrand g (r, u) := by
    exact MeasureTheory.setIntegral_prod
      (sphericalIntegrand g) hS
  rw [hprod]
  change
    (∫ r in Ioc (0 : ℝ) R,
      ∫ u in
        Ioo (-(Real.pi / 2)) (Real.pi / 2) ×ˢ
          Ioo (-Real.pi) Real.pi,
        angularIntegrand g r u.1 u.2) = _
  simp_rw [angular_setIntegral_prod hg]
  simp_rw [theta_setIntegral_eq_interval]
  simp_rw [phi_setIntegral_eq_interval]
  rw [← intervalIntegral.integral_of_le hR.le]

private theorem angularIntegrand_periodic
    (g : Vec3 → ℝ) (r φ : ℝ) :
    Function.Periodic
      (fun θ => angularIntegrand g r φ θ)
      (2 * Real.pi) := by
  intro θ
  simp only [angularIntegrand, sphereParam,
    Real.cos_add_two_pi, Real.sin_add_two_pi]

private theorem theta_interval_shift
    (g : Vec3 → ℝ) (r φ : ℝ) :
    (∫ θ in -Real.pi..Real.pi,
        angularIntegrand g r φ θ) =
      ∫ θ in (0 : ℝ)..2 * Real.pi,
        angularIntegrand g r φ θ := by
  have h :=
    (angularIntegrand_periodic g r φ).intervalIntegral_add_eq
      (-Real.pi) 0
  convert h using 1 <;> ring_nf

/-- A reusable three-dimensional spherical-coordinate change of variables.
The two polar-coordinate singular sets have zero volume, so no boundary
regularity beyond continuity of `g` is needed. -/
private theorem ball_integral_spherical_coordinates
    (g : Vec3 → ℝ) (hg : Continuous g)
    (R : ℝ) (hR : 0 < R) :
    (∫ p in ball R, g p) =
      ∫ r in (0 : ℝ)..R,
        ∫ φ in -(Real.pi / 2)..Real.pi / 2,
          ∫ θ in (0 : ℝ)..2 * Real.pi,
            r ^ 2 * Real.cos φ *
              g (sphereParam r φ θ) := by
  rw [ball_to_cylindrical g hg R hR,
    cylindrical_to_spherical g hg R hR,
    spherical_to_triple_neg_pi g hg R hR]
  simp_rw [theta_interval_shift]
  rfl

private def box3 (a₁ b₁ a₂ b₂ a₃ b₃ : ℝ) : Set Vec3 :=
  Icc a₁ b₁ ×ˢ (Icc a₂ b₂ ×ˢ Icc a₃ b₃)

private theorem integral_box3_eq_iterated
    (h : Vec3 → ℝ) (hh : Continuous h)
    {a₁ b₁ a₂ b₂ a₃ b₃ : ℝ}
    (h₁ : a₁ ≤ b₁) (h₂ : a₂ ≤ b₂) (h₃ : a₃ ≤ b₃) :
    (∫ z in box3 a₁ b₁ a₂ b₂ a₃ b₃, h z) =
      ∫ x in a₁..b₁, ∫ y in a₂..b₂, ∫ z in a₃..b₃, h (x, y, z) := by
  have hi :
      IntegrableOn h (box3 a₁ b₁ a₂ b₂ a₃ b₃) :=
    hh.continuousOn.integrableOn_compact
      (isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc))
  simp_rw [intervalIntegral.integral_of_le h₁,
    intervalIntegral.integral_of_le h₂,
    intervalIntegral.integral_of_le h₃]
  simp_rw [← integral_Icc_eq_integral_Ioc]
  have hv₃ :
      (volume : Measure Vec3) =
        (volume : Measure ℝ).prod
          (volume : Measure (ℝ × ℝ)) := rfl
  have hv₂ :
      (volume : Measure (ℝ × ℝ)) =
        (volume : Measure ℝ).prod
          (volume : Measure ℝ) := rfl
  have hi' :
      Integrable h
        ((volume.restrict (Icc a₁ b₁)).prod
          ((volume.restrict (Icc a₂ b₂)).prod
            (volume.restrict (Icc a₃ b₃)))) := by
    rw [Measure.prod_restrict, Measure.prod_restrict]
    simpa [box3, ← hv₃, ← hv₂] using hi
  unfold box3
  rw [hv₃, hv₂, ← Measure.prod_restrict,
    ← Measure.prod_restrict]
  rw [integral_prod _ hi']
  apply integral_congr_ae
  filter_upwards [hi'.prod_right_ae] with x hx
  exact integral_prod _ hx

private theorem hasDerivAt_integral_compact
    {K : Set Vec3} (hK : IsCompact K)
    {F F' : ℝ → Vec3 → ℝ}
    (hF : Continuous F.uncurry)
    (hF' : Continuous F'.uncurry)
    (hd : ∀ s x,
      HasDerivAt (fun u => F u x) (F' s x) s)
    (t : ℝ) :
    HasDerivAt (fun s => ∫ x in K, F s x)
      (∫ x in K, F' t x) t := by
  let J : Set ℝ := Icc (t - 1) (t + 1)
  have hJ : IsCompact J := isCompact_Icc
  obtain ⟨M, hM⟩ :=
    (hJ.prod hK).bddAbove_image hF'.norm.continuousOn
  have hJ_mem : J ∈ nhds t := by
    change Icc (t - 1) (t + 1) ∈ nhds t
    exact Icc_mem_nhds (sub_lt_self t zero_lt_one)
      (lt_add_of_pos_right t zero_lt_one)
  have hFi : Integrable (F t) (volume.restrict K) :=
    (hF.comp (continuous_const.prodMk continuous_id)).continuousOn
      |>.integrableOn_compact hK
  have hF'i :
      AEStronglyMeasurable (F' t) (volume.restrict K) :=
    (hF'.comp
      (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  have hMi :
      Integrable (fun _ : Vec3 => M)
        (volume.restrict K) := by
    show IntegrableOn (fun _ : Vec3 => M) K
    exact integrableOn_const hK.measure_ne_top
  refine
    (hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := volume.restrict K) (bound := fun _ => M)
      hJ_mem ?_ hFi hF'i ?_ hMi ?_).2
  · filter_upwards with s
    exact
      (hF.comp
        (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · filter_upwards
      [ae_restrict_mem hK.measurableSet] with x hx s hs
    exact hM ⟨(s, x), ⟨hs, hx⟩, rfl⟩
  · filter_upwards with x s hs
    exact hd s x

private def meridian (f : SpaceTimeField) (φ θ : ℝ) :
    ℝ × ℝ → ℝ :=
  fun z => f (sphereParam z.1 φ θ) z.2

private theorem meridian_contDiff
    {f : SpaceTimeField} (hf : IsC1 f) (φ θ : ℝ) :
    ContDiff ℝ 1 (meridian f φ θ) := by
  have hm :
      ContDiff ℝ 1
        (fun z : ℝ × ℝ =>
          (sphereParam z.1 φ θ, z.2)) := by
    unfold sphereParam
    fun_prop
  simpa only [meridian, Function.comp_apply] using hf.comp hm

private theorem meridian_diag_hasDerivAt
    {f : SpaceTimeField} (hf : IsC1 f)
    (φ θ s r : ℝ) :
    HasDerivAt
      (fun u => meridian f φ θ (u * r, u))
      ((fderiv ℝ (meridian f φ θ)
        (s * r, s)) (r, 1)) s := by
  have hm :
      HasFDerivAt (meridian f φ θ)
        (fderiv ℝ (meridian f φ θ) (s * r, s))
        (s * r, s) :=
    ((meridian_contDiff hf φ θ).differentiable
      (by norm_num)).differentiableAt.hasFDerivAt
  have h₁ :
      HasDerivAt (fun u : ℝ => u * r) r s := by
    simpa using (hasDerivAt_id s).mul_const r
  have h₂ :
      HasDerivAt (fun u : ℝ => u) 1 s :=
    hasDerivAt_id s
  have hi :=
    HasFDerivAt.prodMk h₁.hasFDerivAt h₂.hasFDerivAt
  have hc := HasFDerivAt.comp
    (f := fun u : ℝ => (u * r, u)) s hm hi
  convert hc.hasDerivAt using 1
  simp

private theorem meridian_radial_hasDerivAt
    {f : SpaceTimeField} (hf : IsC1 f)
    (φ θ s r : ℝ) :
    HasDerivAt
      (fun u => meridian f φ θ (s * u, s))
      ((fderiv ℝ (meridian f φ θ)
        (s * r, s)) (s, 0)) r := by
  have hm :
      HasFDerivAt (meridian f φ θ)
        (fderiv ℝ (meridian f φ θ) (s * r, s))
        (s * r, s) :=
    ((meridian_contDiff hf φ θ).differentiable
      (by norm_num)).differentiableAt.hasFDerivAt
  have h₁ :
      HasDerivAt (fun u : ℝ => s * u) s r := by
    simpa using (hasDerivAt_id r).const_mul s
  have h₂ :
      HasDerivAt (fun _u : ℝ => s) 0 r :=
    hasDerivAt_const r s
  have hi :=
    HasFDerivAt.prodMk h₁.hasFDerivAt h₂.hasFDerivAt
  have hc := HasFDerivAt.comp
    (f := fun u : ℝ => (s * u, s)) r hm hi
  convert hc.hasDerivAt using 1
  simp

private theorem meridian_time_hasDerivAt
    {f : SpaceTimeField} (hf : IsC1 f)
    (φ θ s r : ℝ) :
    HasDerivAt
      (fun u => meridian f φ θ (s * r, u))
      ((fderiv ℝ (meridian f φ θ)
        (s * r, s)) (0, 1)) s := by
  have hm :
      HasFDerivAt (meridian f φ θ)
        (fderiv ℝ (meridian f φ θ) (s * r, s))
        (s * r, s) :=
    ((meridian_contDiff hf φ θ).differentiable
      (by norm_num)).differentiableAt.hasFDerivAt
  have h₁ :
      HasDerivAt (fun _u : ℝ => s * r) 0 s :=
    hasDerivAt_const s _
  have h₂ :
      HasDerivAt (fun u : ℝ => u) 1 s :=
    hasDerivAt_id s
  have hi :=
    HasFDerivAt.prodMk h₁.hasFDerivAt h₂.hasFDerivAt
  have hc := HasFDerivAt.comp
    (f := fun u : ℝ => (s * r, u)) s hm hi
  convert hc.hasDerivAt using 1
  simp

private def timePartial (f : SpaceTimeField)
    (p : Vec3) (t : ℝ) : ℝ :=
  fderiv ℝ (fun z : Vec3 × ℝ => f z.1 z.2)
    (p, t) ((0 : Vec3), (1 : ℝ))

private theorem timePartial_continuous
    (f : SpaceTimeField) (hf : IsC1 f) :
    Continuous
      (fun z : Vec3 × ℝ => timePartial f z.1 z.2) := by
  unfold IsC1 at hf
  unfold timePartial
  exact
    (hf.continuous_fderiv one_ne_zero).clm_apply
      continuous_const

private theorem timeSlice_hasDerivAt
    (f : SpaceTimeField) (hf : IsC1 f)
    (p : Vec3) (t : ℝ) :
    HasDerivAt (fun s : ℝ => f p s)
      (timePartial f p t) t := by
  unfold IsC1 at hf
  have hcurve :
      HasFDerivAt (fun s : ℝ => (p, s))
        (ContinuousLinearMap.inr ℝ Vec3 ℝ) t :=
    hasFDerivAt_prodMk_right p t
  have hmain :=
    hf.differentiable_one.differentiableAt.hasFDerivAt.comp
      t hcurve
  convert hmain.hasDerivAt using 1

private theorem timeDerivative_eq_timePartial
    (f : SpaceTimeField) (hf : IsC1 f)
    (p : Vec3) (t : ℝ) :
    timeDerivative f p t = timePartial f p t := by
  unfold timeDerivative
  exact (timeSlice_hasDerivAt f hf p t).deriv

private theorem hasDerivAt_intervalIntegral_of_continuous
    (F F' : ℝ → ℝ → ℝ) (x₀ a b : ℝ)
    (hF : Continuous (fun z : ℝ × ℝ => F z.1 z.2))
    (hF' : Continuous
      (fun z : ℝ × ℝ => F' z.1 z.2))
    (hdiff : ∀ x y,
      HasDerivAt (fun u : ℝ => F u y) (F' x y) x) :
    HasDerivAt
      (fun x : ℝ => ∫ y in a..b, F x y)
      (∫ y in a..b, F' x₀ y) x₀ := by
  let S : Set ℝ := Icc (x₀ - 1) (x₀ + 1)
  have hSnhds : S ∈ 𝓝 x₀ := by
    apply Icc_mem_nhds
    · linarith
    · linarith
  have hK :
      IsCompact (S ×ˢ Set.uIcc a b) :=
    isCompact_Icc.prod isCompact_uIcc
  obtain ⟨C, hC⟩ :=
    hK.exists_bound_of_continuousOn hF'.continuousOn
  have hmain :=
    intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := volume) (a := a) (b := b)
      (F := F) (F' := F') (x₀ := x₀)
      (s := S) (bound := fun _ => C)
      hSnhds
      (Filter.Eventually.of_forall fun x =>
        (hF.comp
          (continuous_const.prodMk continuous_id))
          |>.aestronglyMeasurable)
      ((hF.comp
        (continuous_const.prodMk continuous_id))
        |>.intervalIntegrable a b)
      ((hF'.comp
        (continuous_const.prodMk continuous_id))
        |>.aestronglyMeasurable)
      (Filter.Eventually.of_forall fun y hy x hx => by
        apply hC (x, y)
        exact ⟨hx, Set.uIoc_subset_uIcc hy⟩)
      (continuous_const.intervalIntegrable a b)
      (Filter.Eventually.of_forall fun y _ x _ =>
        hdiff x y)
  exact hmain.2

private theorem continuous_intervalIntegral_of_continuous
    {X : Type*} [MetricSpace X] [ProperSpace X]
    (F : X → ℝ → ℝ) (a b : ℝ)
    (hF : Continuous F.uncurry) :
    Continuous (fun x : X => ∫ y in a..b, F x y) := by
  by_cases hab : a ≤ b
  · have hset :
        Continuous
          (fun x : X => ∫ y in Icc a b, F x y) :=
      continuous_parametric_integral_of_continuous
        hF isCompact_Icc
    simpa only [intervalIntegral.integral_of_le hab,
      ← integral_Icc_eq_integral_Ioc] using hset
  · have hba : b ≤ a := (not_le.mp hab).le
    have hset :
        Continuous
          (fun x : X => ∫ y in Icc b a, F x y) :=
      continuous_parametric_integral_of_continuous
        hF isCompact_Icc
    have hneg :
        Continuous
          (fun x : X => -(∫ y in Icc b a, F x y)) :=
      hset.neg
    simpa only [intervalIntegral.integral_of_ge hba,
      ← integral_Icc_eq_integral_Ioc] using hneg

private theorem movingResidual_hasDerivAt_zero
    (F : ℝ → ℝ → ℝ) (t : ℝ)
    (hF : Continuous F.uncurry) :
    HasDerivAt
      (fun s : ℝ => ∫ r in t..s, F s r - F t r)
      0 t := by
  let B : ℝ → ℝ := fun s =>
    ∫ u in (0 : ℝ)..1,
      (F s ((s - t) * u + t) -
        F t ((s - t) * u + t))
  have hBcont : Continuous B := by
    apply continuous_intervalIntegral_of_continuous
      (fun s u =>
        F s ((s - t) * u + t) -
          F t ((s - t) * u + t)) 0 1
    have hcoord :
        Continuous
          (fun z : ℝ × ℝ => (z.1 - t) * z.2 + t) :=
      (continuous_fst.sub continuous_const).mul
        continuous_snd |>.add continuous_const
    exact
      (hF.comp
        (continuous_fst.prodMk hcoord)).sub
        (hF.comp
          (continuous_const.prodMk hcoord))
  have hBzero : B t = 0 := by
    simp [B]
  have hBtend : Tendsto B (𝓝 t) (𝓝 0) := by
    have h : ContinuousAt B t := hBcont.continuousAt
    change Tendsto B (𝓝 t) (𝓝 (B t)) at h
    simpa only [hBzero] using h
  have hA :
      (fun s : ℝ => s - t) =O[𝓝 t]
        (fun s : ℝ => s - t) :=
    Asymptotics.isBigO_refl _ _
  have hBo :
      B =o[𝓝 t] (fun _ : ℝ => (1 : ℝ)) :=
    (Asymptotics.isLittleO_one_iff ℝ).2 hBtend
  have hprod :
      (fun s : ℝ => (s - t) * B s) =o[𝓝 t]
        (fun s : ℝ => (s - t) * 1) :=
    hA.mul_isLittleO hBo
  have heq (s : ℝ) :
      (∫ r in t..s, F s r - F t r) =
        (s - t) * B s := by
    calc
      (∫ r in t..s, F s r - F t r) =
          ∫ r in (s - t) * 0 + t..
              (s - t) * 1 + t,
            F s r - F t r := by
              congr 1 <;> ring
      _ = (s - t) * B s := by
        simpa only [B, smul_eq_mul] using
          (intervalIntegral.smul_integral_comp_mul_add
            (f := fun r : ℝ => F s r - F t r)
            (a := (0 : ℝ)) (b := 1) (s - t) t).symm
  apply HasDerivAt.of_isLittleO
  convert hprod using 1
  · funext s
    rw [heq]
    simp
  · funext s
    simp

private theorem hasDerivAt_moving_upper_of_continuous
    (F F' : ℝ → ℝ → ℝ) (t : ℝ)
    (hF : Continuous F.uncurry)
    (hF' : Continuous F'.uncurry)
    (hdiff : ∀ s r,
      HasDerivAt (fun u : ℝ => F u r) (F' s r) s) :
    HasDerivAt
      (fun s : ℝ => ∫ r in (0 : ℝ)..s, F s r)
      (F t t + ∫ r in (0 : ℝ)..t, F' t r) t := by
  have hfixed :
      HasDerivAt
        (fun s : ℝ => ∫ r in (0 : ℝ)..t, F s r)
        (∫ r in (0 : ℝ)..t, F' t r) t :=
    hasDerivAt_intervalIntegral_of_continuous
      F F' t 0 t hF hF' hdiff
  have hFt : Continuous (F t) :=
    hF.comp (continuous_const.prodMk continuous_id)
  have hmove :
      HasDerivAt
        (fun s : ℝ => ∫ r in t..s, F t r)
        (F t t) t :=
    (hFt.integral_hasStrictDerivAt t t).hasDerivAt
  have hres :
      HasDerivAt
        (fun s : ℝ => ∫ r in t..s, F s r - F t r)
        0 t :=
    movingResidual_hasDerivAt_zero F t hF
  have hdecomp (s : ℝ) :
      (∫ r in (0 : ℝ)..s, F s r) =
        (∫ r in (0 : ℝ)..t, F s r) +
          (∫ r in t..s, F t r) +
          (∫ r in t..s, F s r - F t r) := by
    have hFs : Continuous (F s) :=
      hF.comp (continuous_const.prodMk continuous_id)
    have hpath :
        (∫ r in (0 : ℝ)..s, F s r) =
          (∫ r in (0 : ℝ)..t, F s r) +
            (∫ r in t..s, F s r) := by
      symm
      exact
        intervalIntegral.integral_add_adjacent_intervals
          (hFs.intervalIntegrable 0 t)
          (hFs.intervalIntegrable t s)
    have hsplit :
        (∫ r in t..s, F s r) =
          (∫ r in t..s, F t r) +
            (∫ r in t..s, F s r - F t r) := by
      rw [intervalIntegral.integral_sub
        (hFs.intervalIntegrable t s)
        (hFt.intervalIntegrable t s)]
      ring
    rw [hpath, hsplit]
    ring
  have hfun :
      (fun s : ℝ => ∫ r in (0 : ℝ)..s, F s r) =
        fun s =>
          (∫ r in (0 : ℝ)..t, F s r) +
            (∫ r in t..s, F t r) +
            (∫ r in t..s, F s r - F t r) :=
    funext hdecomp
  rw [hfun]
  convert (hfixed.add hmove).add hres using 1
  all_goals ring

private def kernel (f : SpaceTimeField)
    (s r φ θ : ℝ) : ℝ :=
  r ^ 2 * Real.cos φ * f (sphereParam r φ θ) s

private def kernelTime (f : SpaceTimeField)
    (s r φ θ : ℝ) : ℝ :=
  r ^ 2 * Real.cos φ *
    timePartial f (sphereParam r φ θ) s

private def thetaIntegral (f : SpaceTimeField)
    (s r φ : ℝ) : ℝ :=
  ∫ θ in (0 : ℝ)..2 * Real.pi,
    kernel f s r φ θ

private def thetaTimeIntegral (f : SpaceTimeField)
    (s r φ : ℝ) : ℝ :=
  ∫ θ in (0 : ℝ)..2 * Real.pi,
    kernelTime f s r φ θ

private def shell (f : SpaceTimeField) (s r : ℝ) : ℝ :=
  ∫ φ in -Real.pi / 2..Real.pi / 2,
    thetaIntegral f s r φ

private def shellTime
    (f : SpaceTimeField) (s r : ℝ) : ℝ :=
  ∫ φ in -Real.pi / 2..Real.pi / 2,
    thetaTimeIntegral f s r φ

private def sphericalVolume
    (f : SpaceTimeField) (s : ℝ) : ℝ :=
  ∫ r in (0 : ℝ)..s, shell f s r

private theorem kernel_continuous
    (f : SpaceTimeField) (hf : IsC1 f) :
    Continuous
      (fun z : (ℝ × (ℝ × ℝ)) × ℝ =>
        kernel f z.1.1 z.1.2.1 z.1.2.2 z.2) := by
  have hparam :
      Continuous
        (fun z : (ℝ × (ℝ × ℝ)) × ℝ =>
          sphereParam z.1.2.1 z.1.2.2 z.2) := by
    unfold sphereParam
    fun_prop
  have hpoint :
      Continuous
        (fun z : (ℝ × (ℝ × ℝ)) × ℝ =>
          (sphereParam z.1.2.1 z.1.2.2 z.2,
            z.1.1)) :=
    hparam.prodMk (by fun_prop)
  have hvalue :
      Continuous
        (fun z : (ℝ × (ℝ × ℝ)) × ℝ =>
          f (sphereParam z.1.2.1 z.1.2.2 z.2)
            z.1.1) :=
    hf.continuous.comp hpoint
  have hfactor :
      Continuous
        (fun z : (ℝ × (ℝ × ℝ)) × ℝ =>
          z.1.2.1 ^ 2 * Real.cos z.1.2.2) := by
    fun_prop
  simpa only [kernel] using hfactor.mul hvalue

private theorem kernelTime_continuous
    (f : SpaceTimeField) (hf : IsC1 f) :
    Continuous
      (fun z : (ℝ × (ℝ × ℝ)) × ℝ =>
        kernelTime f z.1.1 z.1.2.1 z.1.2.2 z.2) := by
  have hparam :
      Continuous
        (fun z : (ℝ × (ℝ × ℝ)) × ℝ =>
          sphereParam z.1.2.1 z.1.2.2 z.2) := by
    unfold sphereParam
    fun_prop
  have hpoint :
      Continuous
        (fun z : (ℝ × (ℝ × ℝ)) × ℝ =>
          (sphereParam z.1.2.1 z.1.2.2 z.2,
            z.1.1)) :=
    hparam.prodMk (by fun_prop)
  have hvalue :
      Continuous
        (fun z : (ℝ × (ℝ × ℝ)) × ℝ =>
          timePartial f
            (sphereParam z.1.2.1 z.1.2.2 z.2)
            z.1.1) :=
    (timePartial_continuous f hf).comp hpoint
  have hfactor :
      Continuous
        (fun z : (ℝ × (ℝ × ℝ)) × ℝ =>
          z.1.2.1 ^ 2 * Real.cos z.1.2.2) := by
    fun_prop
  simpa only [kernelTime] using hfactor.mul hvalue

private theorem kernel_hasDerivAt
    (f : SpaceTimeField) (hf : IsC1 f)
    (s r φ θ : ℝ) :
    HasDerivAt (fun u : ℝ => kernel f u r φ θ)
      (kernelTime f s r φ θ) s := by
  simpa only [kernel, kernelTime] using
    (timeSlice_hasDerivAt f hf
      (sphereParam r φ θ) s).const_mul
        (r ^ 2 * Real.cos φ)

private theorem thetaIntegral_joint_continuous
    (f : SpaceTimeField) (hf : IsC1 f) :
    Continuous
      (fun z : ℝ × (ℝ × ℝ) =>
        thetaIntegral f z.1 z.2.1 z.2.2) := by
  simpa only [thetaIntegral,
    Function.uncurry_apply_pair] using
    continuous_intervalIntegral_of_continuous
      (fun z : ℝ × (ℝ × ℝ) => fun θ =>
        kernel f z.1 z.2.1 z.2.2 θ)
      0 (2 * Real.pi) (kernel_continuous f hf)

private theorem thetaTimeIntegral_joint_continuous
    (f : SpaceTimeField) (hf : IsC1 f) :
    Continuous
      (fun z : ℝ × (ℝ × ℝ) =>
        thetaTimeIntegral f z.1 z.2.1 z.2.2) := by
  simpa only [thetaTimeIntegral,
    Function.uncurry_apply_pair] using
    continuous_intervalIntegral_of_continuous
      (fun z : ℝ × (ℝ × ℝ) => fun θ =>
        kernelTime f z.1 z.2.1 z.2.2 θ)
      0 (2 * Real.pi) (kernelTime_continuous f hf)

private theorem thetaIntegral_hasDerivAt
    (f : SpaceTimeField) (hf : IsC1 f)
    (s r φ : ℝ) :
    HasDerivAt
      (fun u : ℝ => thetaIntegral f u r φ)
      (thetaTimeIntegral f s r φ) s := by
  apply hasDerivAt_intervalIntegral_of_continuous
      (fun u θ => kernel f u r φ θ)
      (fun u θ => kernelTime f u r φ θ)
      s 0 (2 * Real.pi)
  · exact (kernel_continuous f hf).comp
      ((continuous_fst.prodMk
        (continuous_const.prodMk
          continuous_const)).prodMk continuous_snd)
  · exact (kernelTime_continuous f hf).comp
      ((continuous_fst.prodMk
        (continuous_const.prodMk
          continuous_const)).prodMk continuous_snd)
  · exact fun u θ =>
      kernel_hasDerivAt f hf u r φ θ

private theorem shell_joint_continuous
    (f : SpaceTimeField) (hf : IsC1 f) :
    Continuous (fun z : ℝ × ℝ => shell f z.1 z.2) := by
  have htheta :
      Continuous
        (fun z : (ℝ × ℝ) × ℝ =>
          thetaIntegral f z.1.1 z.1.2 z.2) :=
    (thetaIntegral_joint_continuous f hf).comp
      ((continuous_fst.comp continuous_fst).prodMk
        ((continuous_snd.comp continuous_fst).prodMk
          continuous_snd))
  simpa only [shell, Function.uncurry_apply_pair] using
    continuous_intervalIntegral_of_continuous
      (fun z : ℝ × ℝ => fun φ =>
        thetaIntegral f z.1 z.2 φ)
      (-Real.pi / 2) (Real.pi / 2) htheta

private theorem shellTime_joint_continuous
    (f : SpaceTimeField) (hf : IsC1 f) :
    Continuous
      (fun z : ℝ × ℝ => shellTime f z.1 z.2) := by
  have htheta :
      Continuous
        (fun z : (ℝ × ℝ) × ℝ =>
          thetaTimeIntegral f z.1.1 z.1.2 z.2) :=
    (thetaTimeIntegral_joint_continuous f hf).comp
      ((continuous_fst.comp continuous_fst).prodMk
        ((continuous_snd.comp continuous_fst).prodMk
          continuous_snd))
  simpa only [shellTime,
    Function.uncurry_apply_pair] using
    continuous_intervalIntegral_of_continuous
      (fun z : ℝ × ℝ => fun φ =>
        thetaTimeIntegral f z.1 z.2 φ)
      (-Real.pi / 2) (Real.pi / 2) htheta

private theorem shell_hasDerivAt
    (f : SpaceTimeField) (hf : IsC1 f)
    (s r : ℝ) :
    HasDerivAt (fun u : ℝ => shell f u r)
      (shellTime f s r) s := by
  apply hasDerivAt_intervalIntegral_of_continuous
      (fun u φ => thetaIntegral f u r φ)
      (fun u φ => thetaTimeIntegral f u r φ)
      s (-Real.pi / 2) (Real.pi / 2)
  · exact (thetaIntegral_joint_continuous f hf).comp
      (continuous_fst.prodMk
        (continuous_const.prodMk continuous_snd))
  · exact
      (thetaTimeIntegral_joint_continuous f hf).comp
        (continuous_fst.prodMk
          (continuous_const.prodMk continuous_snd))
  · exact fun u φ =>
      thetaIntegral_hasDerivAt f hf u r φ

private theorem sphericalVolume_hasDerivAt
    (f : SpaceTimeField) (hf : IsC1 f) (t : ℝ) :
    HasDerivAt (sphericalVolume f)
      (shell f t t +
        ∫ r in (0 : ℝ)..t, shellTime f t r) t := by
  unfold sphericalVolume
  exact hasDerivAt_moving_upper_of_continuous
    (shell f) (shellTime f) t
    (shell_joint_continuous f hf)
    (shellTime_joint_continuous f hf)
    (shell_hasDerivAt f hf)

private theorem movingBall_of_sphericalChange
    (f : SpaceTimeField) (t : ℝ)
    (ht : 0 < t) (hf : IsC1 f)
    (hsphere :
      ∀ (g : Vec3 → ℝ) (s : ℝ),
        Continuous g → 0 < s →
          (∫ p in ball s, g p) =
            ∫ r in (0 : ℝ)..s,
              ∫ φ in -Real.pi / 2..Real.pi / 2,
                ∫ θ in (0 : ℝ)..2 * Real.pi,
                  r ^ 2 * Real.cos φ *
                    g (sphereParam r φ θ)) :
    deriv (ballIntegral f) t =
      sphereSurfaceIntegral f t +
        timeDerivativeVolume f t := by
  have hslice (s : ℝ) :
      Continuous (fun p : Vec3 => f p s) :=
    hf.continuous.comp
      (continuous_id.prodMk continuous_const)
  have heq :
      ballIntegral f =ᶠ[𝓝 t] sphericalVolume f := by
    filter_upwards [Ioi_mem_nhds ht] with s hs
    simpa only [ballIntegral, sphericalVolume, shell,
      thetaIntegral, kernel] using
      hsphere (fun p : Vec3 => f p s) s
        (hslice s) hs
  have htimePartial :
      Continuous (fun p : Vec3 => timePartial f p t) :=
    (timePartial_continuous f hf).comp
      (continuous_id.prodMk continuous_const)
  have htime :
      Continuous
        (fun p : Vec3 => timeDerivative f p t) := by
    have hfun :
        (fun p : Vec3 => timeDerivative f p t) =
          fun p : Vec3 => timePartial f p t := by
      funext p
      exact timeDerivative_eq_timePartial f hf p t
    rw [hfun]
    exact htimePartial
  have htimeSphere :=
    hsphere (fun p : Vec3 => timeDerivative f p t)
      t htime ht
  have hboundary :
      shell f t t = sphereSurfaceIntegral f t := by
    rfl
  have hvolume :
      (∫ r in (0 : ℝ)..t, shellTime f t r) =
        timeDerivativeVolume f t := by
    simpa only [shellTime, thetaTimeIntegral, kernelTime,
      timeDerivativeVolume,
      timeDerivative_eq_timePartial f hf] using
      htimeSphere.symm
  have hball :=
    (sphericalVolume_hasDerivAt f hf t).congr_of_eventuallyEq heq
  rw [hboundary, hvolume] at hball
  exact hball.deriv

private theorem reynolds_formula
    (f : SpaceTimeField) (t : ℝ) (ht : 0 < t) (hf : IsC1 f) :
    deriv (ballIntegral f) t =
      sphereSurfaceIntegral f t + timeDerivativeVolume f t := by
  exact movingBall_of_sphericalChange f t ht hf
    (fun g s hg hs => by
      simpa only [neg_div] using
        ball_integral_spherical_coordinates g hg s hs)

private theorem scalePoint_eq_smul (t : ℝ) (p : Vec3) :
    scalePoint t p = t • p := by
  change (t * p.1, t * p.2.1, t * p.2.2) =
    (t * p.1, t * p.2.1, t * p.2.2)
  rfl

private theorem smul_unitBall_eq_ball (t : ℝ) (ht : 0 < t) :
    t • unitBall = ball t := by
  ext p
  rw [Set.mem_smul_set_iff_inv_smul_mem₀ ht.ne']
  change
    (t⁻¹ * p.1) ^ 2 + (t⁻¹ * p.2.1) ^ 2 +
          (t⁻¹ * p.2.2) ^ 2 ≤ 1 ↔
      p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2 ≤ t ^ 2
  have hid :
      t ^ 2 * ((t⁻¹ * p.1) ^ 2 + (t⁻¹ * p.2.1) ^ 2 +
        (t⁻¹ * p.2.2) ^ 2) =
        p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2 := by
    field_simp [ht.ne']
  constructor <;> intro h <;>
    nlinarith [sq_pos_of_pos ht]

private theorem unitBall_scaling_integral
    (g : Vec3 → ℝ) (t : ℝ) (ht : 0 < t) :
    (∫ q in unitBall, t ^ 3 * g (scalePoint t q)) =
      ∫ p in ball t, g p := by
  have hdim : Module.finrank ℝ Vec3 = 3 := by
    simp [Vec3]
  have hchange :=
    Measure.setIntegral_comp_smul_of_pos
      ((volume : Measure ℝ).prod
        ((volume : Measure ℝ).prod (volume : Measure ℝ)))
      g unitBall ht
  rw [smul_unitBall_eq_ball t ht] at hchange
  have hscale :
      (∫ q in unitBall, g (scalePoint t q)) =
        (t ^ 3)⁻¹ * ∫ p in ball t, g p := by
    simpa [scalePoint_eq_smul, hdim, smul_eq_mul] using hchange
  calc
    (∫ q in unitBall, t ^ 3 * g (scalePoint t q)) =
        t ^ 3 * ∫ q in unitBall, g (scalePoint t q) := by
      rw [← MeasureTheory.integral_const_mul]
    _ = ∫ p in ball t, g p := by
      rw [hscale]
      field_simp [ht.ne']

private def spacePartialX (f : SpaceTimeField)
    (p : Vec3) (t : ℝ) : ℝ :=
  fderiv ℝ (fun z : Vec3 × ℝ => f z.1 z.2)
    (p, t) (((1, 0, 0) : Vec3), (0 : ℝ))

private def spacePartialY (f : SpaceTimeField)
    (p : Vec3) (t : ℝ) : ℝ :=
  fderiv ℝ (fun z : Vec3 × ℝ => f z.1 z.2)
    (p, t) (((0, 1, 0) : Vec3), (0 : ℝ))

private def spacePartialZ (f : SpaceTimeField)
    (p : Vec3) (t : ℝ) : ℝ :=
  fderiv ℝ (fun z : Vec3 × ℝ => f z.1 z.2)
    (p, t) (((0, 0, 1) : Vec3), (0 : ℝ))

private theorem spacePartials_continuous
    (f : SpaceTimeField) (hf : IsC1 f) :
    Continuous
      (fun z : Vec3 × ℝ =>
        (spacePartialX f z.1 z.2,
          spacePartialY f z.1 z.2,
          spacePartialZ f z.1 z.2)) := by
  unfold IsC1 at hf
  have hfd :
      Continuous
        (fun z : Vec3 × ℝ =>
          fderiv ℝ (fun w : Vec3 × ℝ => f w.1 w.2) z) :=
    hf.continuous_fderiv one_ne_zero
  unfold spacePartialX spacePartialY spacePartialZ
  exact
    (hfd.clm_apply continuous_const).prodMk
      ((hfd.clm_apply continuous_const).prodMk
        (hfd.clm_apply continuous_const))

private theorem spaceSliceX_hasDerivAt
    (f : SpaceTimeField) (hf : IsC1 f)
    (p : Vec3) (t : ℝ) :
    HasDerivAt
      (fun x : ℝ => f (x, p.2.1, p.2.2) t)
      (spacePartialX f p t) p.1 := by
  unfold IsC1 at hf
  have hx : HasDerivAt (fun x : ℝ => x) 1 p.1 :=
    hasDerivAt_id p.1
  have hy : HasDerivAt (fun _x : ℝ => p.2.1) 0 p.1 :=
    hasDerivAt_const p.1 _
  have hz : HasDerivAt (fun _x : ℝ => p.2.2) 0 p.1 :=
    hasDerivAt_const p.1 _
  have ht : HasDerivAt (fun _x : ℝ => t) 0 p.1 :=
    hasDerivAt_const p.1 _
  have hp3 :=
    HasFDerivAt.prodMk hx.hasFDerivAt
      (HasFDerivAt.prodMk hy.hasFDerivAt hz.hasFDerivAt)
  have hcurve := HasFDerivAt.prodMk hp3 ht.hasFDerivAt
  have hmain :=
    hf.differentiable_one.differentiableAt.hasFDerivAt.comp
      p.1 hcurve
  convert hmain.hasDerivAt using 1 <;>
    simp [spacePartialX]

private theorem spaceSliceY_hasDerivAt
    (f : SpaceTimeField) (hf : IsC1 f)
    (p : Vec3) (t : ℝ) :
    HasDerivAt
      (fun y : ℝ => f (p.1, y, p.2.2) t)
      (spacePartialY f p t) p.2.1 := by
  unfold IsC1 at hf
  have hx : HasDerivAt (fun _y : ℝ => p.1) 0 p.2.1 :=
    hasDerivAt_const p.2.1 _
  have hy : HasDerivAt (fun y : ℝ => y) 1 p.2.1 :=
    hasDerivAt_id p.2.1
  have hz : HasDerivAt (fun _y : ℝ => p.2.2) 0 p.2.1 :=
    hasDerivAt_const p.2.1 _
  have ht : HasDerivAt (fun _y : ℝ => t) 0 p.2.1 :=
    hasDerivAt_const p.2.1 _
  have hp3 :=
    HasFDerivAt.prodMk hx.hasFDerivAt
      (HasFDerivAt.prodMk hy.hasFDerivAt hz.hasFDerivAt)
  have hcurve := HasFDerivAt.prodMk hp3 ht.hasFDerivAt
  have hmain :=
    hf.differentiable_one.differentiableAt.hasFDerivAt.comp
      p.2.1 hcurve
  convert hmain.hasDerivAt using 1 <;>
    simp [spacePartialY]

private theorem spaceSliceZ_hasDerivAt
    (f : SpaceTimeField) (hf : IsC1 f)
    (p : Vec3) (t : ℝ) :
    HasDerivAt
      (fun z : ℝ => f (p.1, p.2.1, z) t)
      (spacePartialZ f p t) p.2.2 := by
  unfold IsC1 at hf
  have hx : HasDerivAt (fun _z : ℝ => p.1) 0 p.2.2 :=
    hasDerivAt_const p.2.2 _
  have hy : HasDerivAt (fun _z : ℝ => p.2.1) 0 p.2.2 :=
    hasDerivAt_const p.2.2 _
  have hz : HasDerivAt (fun z : ℝ => z) 1 p.2.2 :=
    hasDerivAt_id p.2.2
  have ht : HasDerivAt (fun _z : ℝ => t) 0 p.2.2 :=
    hasDerivAt_const p.2.2 _
  have hp3 :=
    HasFDerivAt.prodMk hx.hasFDerivAt
      (HasFDerivAt.prodMk hy.hasFDerivAt hz.hasFDerivAt)
  have hcurve := HasFDerivAt.prodMk hp3 ht.hasFDerivAt
  have hmain :=
    hf.differentiable_one.differentiableAt.hasFDerivAt.comp
      p.2.2 hcurve
  convert hmain.hasDerivAt using 1 <;>
    simp [spacePartialZ]

private theorem spatialGradient_eq_spacePartials
    (f : SpaceTimeField) (hf : IsC1 f)
    (p : Vec3) (t : ℝ) :
    spatialGradient f p t =
      (spacePartialX f p t,
        spacePartialY f p t,
        spacePartialZ f p t) := by
  unfold spatialGradient
  rw [(spaceSliceX_hasDerivAt f hf p t).deriv,
    (spaceSliceY_hasDerivAt f hf p t).deriv,
    (spaceSliceZ_hasDerivAt f hf p t).deriv]

private theorem fullFderiv_diagonal_eq
    (f : SpaceTimeField) (hf : IsC1 f)
    (p q : Vec3) (t : ℝ) :
    fderiv ℝ (fun z : Vec3 × ℝ => f z.1 z.2)
        (p, t) (q, (1 : ℝ)) =
      dot (spatialGradient f p t) q +
        timeDerivative f p t := by
  let L :=
    fderiv ℝ (fun z : Vec3 × ℝ => f z.1 z.2) (p, t)
  have hdecomp :
      (q, (1 : ℝ)) =
        q.1 • (((1, 0, 0) : Vec3), (0 : ℝ)) +
          q.2.1 • (((0, 1, 0) : Vec3), (0 : ℝ)) +
          q.2.2 • (((0, 0, 1) : Vec3), (0 : ℝ)) +
          ((0 : Vec3), (1 : ℝ)) := by
    ext <;> simp
  rw [spatialGradient_eq_spacePartials f hf p t,
    timeDerivative_eq_timePartial f hf p t]
  change L (q, (1 : ℝ)) =
    dot
        (spacePartialX f p t,
          spacePartialY f p t,
          spacePartialZ f p t) q +
      timePartial f p t
  rw [hdecomp]
  simp only [map_add, map_smul]
  unfold L spacePartialX spacePartialY spacePartialZ timePartial dot
  simp only [smul_eq_mul]
  ring

private theorem diagonalSlice_hasDerivAt
    (f : SpaceTimeField) (hf : IsC1 f)
    (q : Vec3) (s : ℝ) :
    HasDerivAt
      (fun u : ℝ => f (scalePoint u q) u)
      (dot (spatialGradient f (scalePoint s q) s) q +
        timeDerivative f (scalePoint s q) s) s := by
  unfold IsC1 at hf
  have hx :
      HasDerivAt (fun u : ℝ => u * q.1) q.1 s := by
    simpa using (hasDerivAt_id s).mul_const q.1
  have hy :
      HasDerivAt (fun u : ℝ => u * q.2.1) q.2.1 s := by
    simpa using (hasDerivAt_id s).mul_const q.2.1
  have hz :
      HasDerivAt (fun u : ℝ => u * q.2.2) q.2.2 s := by
    simpa using (hasDerivAt_id s).mul_const q.2.2
  have ht : HasDerivAt (fun u : ℝ => u) 1 s :=
    hasDerivAt_id s
  have hp3 :=
    HasFDerivAt.prodMk hx.hasFDerivAt
      (HasFDerivAt.prodMk hy.hasFDerivAt hz.hasFDerivAt)
  have hcurve := HasFDerivAt.prodMk hp3 ht.hasFDerivAt
  have hmain :=
    hf.differentiable_one.differentiableAt.hasFDerivAt.comp
      s hcurve
  have hdiag :=
    fullFderiv_diagonal_eq f
      (show IsC1 f from hf) (scalePoint s q) q s
  convert hmain.hasDerivAt using 1
  simpa [scalePoint] using hdiag.symm

private def positivePullbackIntegrand
    (f : SpaceTimeField) (s : ℝ) (q : Vec3) : ℝ :=
  s ^ 3 * f (scalePoint s q) s

private def pullbackDerivIntegrand
    (f : SpaceTimeField) (s : ℝ) (q : Vec3) : ℝ :=
  scalingDerivativeCore f s q +
    s ^ 3 * timeDerivative f (scalePoint s q) s

private theorem positivePullbackIntegrand_hasDerivAt
    (f : SpaceTimeField) (hf : IsC1 f)
    (q : Vec3) (s : ℝ) :
    HasDerivAt
      (fun u : ℝ => positivePullbackIntegrand f u q)
      (pullbackDerivIntegrand f s q) s := by
  have hpow : HasDerivAt (fun u : ℝ => u ^ 3)
      (3 * s ^ 2) s := by
    convert (hasDerivAt_id s).pow 3 using 1 <;>
      simp [id] <;> ring
  have hdiag := diagonalSlice_hasDerivAt f hf q s
  have hmul := hpow.mul hdiag
  convert hmul using 1
  unfold pullbackDerivIntegrand scalingDerivativeCore
  ring

private theorem positivePullbackIntegrand_continuous
    (f : SpaceTimeField) (hf : IsC1 f) :
    Continuous
      (fun z : ℝ × Vec3 =>
        positivePullbackIntegrand f z.1 z.2) := by
  unfold positivePullbackIntegrand scalePoint
  have hfc := hf.continuous
  fun_prop

private theorem pullbackDerivIntegrand_continuous
    (f : SpaceTimeField) (hf : IsC1 f) :
    Continuous
      (fun z : ℝ × Vec3 =>
        pullbackDerivIntegrand f z.1 z.2) := by
  simp_rw [pullbackDerivIntegrand, scalingDerivativeCore,
    spatialGradient_eq_spacePartials f hf,
    timeDerivative_eq_timePartial f hf]
  unfold spacePartialX spacePartialY spacePartialZ timePartial
  unfold dot scalePoint
  have hfc := hf.continuous
  have hfd := hf.continuous_fderiv one_ne_zero
  fun_prop

private theorem unitBallPullback_hasDerivAt
    (f : SpaceTimeField) (t : ℝ) (ht : 0 < t)
    (hf : IsC1 f) :
    HasDerivAt (unitBallPullback f)
      (∫ q in unitBall, pullbackDerivIntegrand f t q) t := by
  have hunit : IsCompact unitBall := by
    simpa [unitBall, ball] using
      (ball_compact (R := (1 : ℝ)) zero_lt_one)
  have hfixed :=
    hasDerivAt_integral_compact
      (F := positivePullbackIntegrand f)
      (F' := pullbackDerivIntegrand f) hunit
      (positivePullbackIntegrand_continuous f hf)
      (pullbackDerivIntegrand_continuous f hf)
      (fun s q =>
        positivePullbackIntegrand_hasDerivAt f hf q s) t
  have heq :
      unitBallPullback f =ᶠ[𝓝 t]
        fun s => ∫ q in unitBall,
          positivePullbackIntegrand f s q := by
    filter_upwards [Ioi_mem_nhds ht] with s hs
    unfold unitBallPullback positivePullbackIntegrand
    rw [abs_of_pos (show 0 < s from hs)]
  exact hfixed.congr_of_eventuallyEq heq

private theorem ballIntegral_eq_unitBallPullback
    (f : SpaceTimeField) (t : ℝ) (ht : 0 < t) :
    ballIntegral f t = unitBallPullback f t := by
  unfold ballIntegral unitBallPullback
  rw [abs_of_pos ht]
  exact
    (unitBall_scaling_integral
      (fun p : Vec3 => f p t) t ht).symm

private theorem productDivergence_eq
    (f : SpaceTimeField) (t : ℝ) (p : Vec3)
    (hf : IsC1 f) :
    productDivergence f t p =
      dot (spatialGradient f p t) p + 3 * f p t := by
  have hx :
      deriv
          (fun x : ℝ =>
            f (x, p.2.1, p.2.2) t * x) p.1 =
        spacePartialX f p t * p.1 + f p t := by
    simpa using
      ((spaceSliceX_hasDerivAt f hf p t).mul
        (hasDerivAt_id p.1)).deriv
  have hy :
      deriv
          (fun y : ℝ =>
            f (p.1, y, p.2.2) t * y) p.2.1 =
        spacePartialY f p t * p.2.1 + f p t := by
    simpa using
      ((spaceSliceY_hasDerivAt f hf p t).mul
        (hasDerivAt_id p.2.1)).deriv
  have hz :
      deriv
          (fun z : ℝ =>
            f (p.1, p.2.1, z) t * z) p.2.2 =
        spacePartialZ f p t * p.2.2 + f p t := by
    simpa using
      ((spaceSliceZ_hasDerivAt f hf p t).mul
        (hasDerivAt_id p.2.2)).deriv
  unfold productDivergence divergence productVectorField
  rw [hx, hy, hz, spatialGradient_eq_spacePartials f hf p t]
  unfold dot
  ring

private theorem scalingDerivativeCore_eq_scaledDivergence
    (f : SpaceTimeField) (t : ℝ) (q : Vec3)
    (hf : IsC1 f) :
    scalingDerivativeCore f t q =
      t ^ 2 * productDivergence f t (scalePoint t q) := by
  rw [productDivergence_eq f t (scalePoint t q) hf]
  unfold scalingDerivativeCore dot scalePoint
  ring

private theorem scalingDerivativeCore_comp_continuous
    (f : SpaceTimeField) (hf : IsC1 f) (t : ℝ) :
    Continuous
      (fun q : Vec3 => scalingDerivativeCore f t q) := by
  simp_rw [scalingDerivativeCore,
    spatialGradient_eq_spacePartials f hf]
  unfold spacePartialX spacePartialY spacePartialZ dot scalePoint
  have hfc := hf.continuous
  have hfd := hf.continuous_fderiv one_ne_zero
  fun_prop

private theorem scaledTimeDerivative_comp_continuous
    (f : SpaceTimeField) (hf : IsC1 f) (t : ℝ) :
    Continuous
      (fun q : Vec3 =>
        t ^ 3 * timeDerivative f (scalePoint t q) t) := by
  simp_rw [timeDerivative_eq_timePartial f hf]
  unfold timePartial scalePoint
  have hfd := hf.continuous_fderiv one_ne_zero
  fun_prop

private theorem scaledDivergence_integral
    (f : SpaceTimeField) (t : ℝ) (ht : 0 < t) :
    (∫ q in unitBall,
        t ^ 2 *
          productDivergence f t (scalePoint t q)) =
      1 / t * productDivergenceVolume f t := by
  have hscale :=
    unitBall_scaling_integral
      (productDivergence f t) t ht
  have hconst :
      (∫ q in unitBall,
          t ^ 3 *
            productDivergence f t (scalePoint t q)) =
        t *
          ∫ q in unitBall,
            t ^ 2 *
              productDivergence f t (scalePoint t q) := by
    rw [← MeasureTheory.integral_const_mul]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with q
    ring
  unfold productDivergenceVolume
  rw [← hscale, hconst]
  field_simp [ht.ne']

private theorem scalingDerivativeCore_integral
    (f : SpaceTimeField) (t : ℝ) (ht : 0 < t)
    (hf : IsC1 f) :
    (∫ q in unitBall, scalingDerivativeCore f t q) =
      1 / t * productDivergenceVolume f t := by
  calc
    (∫ q in unitBall, scalingDerivativeCore f t q) =
        ∫ q in unitBall,
          t ^ 2 *
            productDivergence f t (scalePoint t q) := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards with q
      exact scalingDerivativeCore_eq_scaledDivergence
        f t q hf
    _ = 1 / t * productDivergenceVolume f t :=
      scaledDivergence_integral f t ht

private theorem scaledTimeDerivative_integral
    (f : SpaceTimeField) (t : ℝ) (ht : 0 < t) :
    (∫ q in unitBall,
        t ^ 3 * timeDerivative f (scalePoint t q) t) =
      timeDerivativeVolume f t := by
  unfold timeDerivativeVolume
  exact unitBall_scaling_integral
    (fun p : Vec3 => timeDerivative f p t) t ht

private theorem ballDerivative_divergence_formula
    (f : SpaceTimeField) (t : ℝ) (ht : 0 < t)
    (hf : IsC1 f) :
    deriv (ballIntegral f) t =
      1 / t * productDivergenceVolume f t +
        timeDerivativeVolume f t := by
  have heq :
      ballIntegral f =ᶠ[𝓝 t] unitBallPullback f := by
    filter_upwards [Ioi_mem_nhds ht] with s hs
    exact ballIntegral_eq_unitBallPullback f s hs
  have hderiv :
      deriv (ballIntegral f) t =
        ∫ q in unitBall,
          (scalingDerivativeCore f t q +
            t ^ 3 * timeDerivative f (scalePoint t q) t) := by
    rw [heq.deriv_eq]
    simpa only [pullbackDerivIntegrand] using
      (unitBallPullback_hasDerivAt f t ht hf).deriv
  have hunit : IsCompact unitBall := by
    simpa [unitBall, ball] using
      (ball_compact (R := (1 : ℝ)) zero_lt_one)
  have hcore :
      IntegrableOn
        (fun q : Vec3 => scalingDerivativeCore f t q)
        unitBall :=
    (scalingDerivativeCore_comp_continuous f hf t).continuousOn
      |>.integrableOn_compact hunit
  have htime :
      IntegrableOn
        (fun q : Vec3 =>
          t ^ 3 * timeDerivative f (scalePoint t q) t)
        unitBall :=
    (scaledTimeDerivative_comp_continuous f hf t).continuousOn
      |>.integrableOn_compact hunit
  rw [hderiv, MeasureTheory.integral_add hcore htime,
    scalingDerivativeCore_integral f t ht hf,
    scaledTimeDerivative_integral f t ht]

private theorem sphereParam_mem_sphere
    (t φ θ : ℝ) :
    sphereParam t φ θ ∈ sphere t := by
  unfold sphere sphereParam
  dsimp
  calc
    (t * Real.cos φ * Real.cos θ) ^ 2 +
          (t * Real.cos φ * Real.sin θ) ^ 2 +
        (t * Real.sin φ) ^ 2 =
      t ^ 2 *
        (Real.cos φ ^ 2 *
            (Real.cos θ ^ 2 + Real.sin θ ^ 2) +
          Real.sin φ ^ 2) := by ring
    _ = t ^ 2 := by
      rw [Real.cos_sq_add_sin_sq, mul_one,
        Real.cos_sq_add_sin_sq]
      ring

private theorem productVectorField_dot_sphereNormal
    (f : SpaceTimeField) (t : ℝ) (p : Vec3)
    (ht : 0 < t) (hp : p ∈ sphere t) :
    dot (productVectorField f t p) (sphereNormal t p) =
      t * f p t := by
  have hs :
      p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2 = t ^ 2 := hp
  unfold dot productVectorField sphereNormal
  calc
    f p t * p.1 * (p.1 / t) +
          f p t * p.2.1 * (p.2.1 / t) +
        f p t * p.2.2 * (p.2.2 / t) =
      f p t *
        ((p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2) / t) := by
          ring
    _ = f p t * (t ^ 2 / t) := by rw [hs]
    _ = t * f p t := by field_simp [ht.ne']

private theorem radialFlux_formula
    (f : SpaceTimeField) (t : ℝ) (ht : 0 < t) :
    radialFlux f t = t * sphereSurfaceIntegral f t := by
  unfold radialFlux sphereSurfaceIntegral
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro φ _hφ
  change
    (∫ θ in (0 : ℝ)..2 * Real.pi,
      t ^ 2 * Real.cos φ *
        dot (productVectorField f t (sphereParam t φ θ))
          (sphereNormal t (sphereParam t φ θ))) =
      t *
        ∫ θ in (0 : ℝ)..2 * Real.pi,
          t ^ 2 * Real.cos φ * f (sphereParam t φ θ) t
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro θ _hθ
  change
    t ^ 2 * Real.cos φ *
        dot (productVectorField f t (sphereParam t φ θ))
          (sphereNormal t (sphereParam t φ θ)) =
      t * (t ^ 2 * Real.cos φ * f (sphereParam t φ θ) t)
  rw [productVectorField_dot_sphereNormal f t
    (sphereParam t φ θ) ht (sphereParam_mem_sphere t φ θ)]
  ring

private theorem divergenceFlux_formula
    (f : SpaceTimeField) (t : ℝ) (ht : 0 < t)
    (hf : IsC1 f) :
    productDivergenceVolume f t = radialFlux f t := by
  have hdiv := ballDerivative_divergence_formula f t ht hf
  have hrey := reynolds_formula f t ht hf
  have hrel :
      1 / t * productDivergenceVolume f t =
        sphereSurfaceIntegral f t := by
    linarith
  rw [radialFlux_formula f t ht]
  calc
    productDivergenceVolume f t =
        t * (1 / t * productDivergenceVolume f t) := by
      field_simp [ht.ne']
    _ = t * sphereSurfaceIntegral f t := by rw [hrel]

theorem gap1 (f : SpaceTimeField) (t : ℝ) (ht : 0 < t)
    (hf : IsC1 f) :
    deriv (ballIntegral f) t = deriv (unitBallPullback f) t := by
  have heq :
      ballIntegral f =ᶠ[𝓝 t] unitBallPullback f := by
    filter_upwards [Ioi_mem_nhds ht] with s hs
    exact ballIntegral_eq_unitBallPullback f s hs
  exact heq.deriv_eq

theorem gap2 (f : SpaceTimeField) (t : ℝ) (ht : 0 < t)
    (hf : IsC1 f) :
    deriv (unitBallPullback f) t =
      ∫ q in unitBall,
        (scalingDerivativeCore f t q +
          t ^ 3 * timeDerivative f (scalePoint t q) t) := by
  simpa only [pullbackDerivIntegrand] using
    (unitBallPullback_hasDerivAt f t ht hf).deriv

theorem gap3 (f : SpaceTimeField) (t : ℝ) (q : Vec3)
    (hf : IsC1 f) :
    scalingDerivativeCore f t q =
      t ^ 2 * productDivergence f t (scalePoint t q) := by
  exact scalingDerivativeCore_eq_scaledDivergence f t q hf

theorem gap4 (f : SpaceTimeField) (t : ℝ) (ht : 0 < t)
    (hf : IsC1 f) :
    deriv (ballIntegral f) t =
      1 / t * productDivergenceVolume f t +
        timeDerivativeVolume f t := by
  exact ballDerivative_divergence_formula f t ht hf

theorem gap5 (f : SpaceTimeField) (t : ℝ) (ht : 0 < t)
    (hf : IsC1 f) :
    productDivergenceVolume f t = radialFlux f t := by
  exact divergenceFlux_formula f t ht hf

theorem gap6 (t : ℝ) (p : Vec3) (ht : 0 < t) (hp : p ∈ sphere t) :
    (sphereNormal t p).1 = p.1 / t := by
  rfl

theorem gap7 (t : ℝ) (p : Vec3) (ht : 0 < t) (hp : p ∈ sphere t) :
    (sphereNormal t p).2.1 = p.2.1 / t := by
  rfl

theorem gap8 (t : ℝ) (p : Vec3) (ht : 0 < t) (hp : p ∈ sphere t) :
    (sphereNormal t p).2.2 = p.2.2 / t := by
  rfl

theorem gap9 (f : SpaceTimeField) (t : ℝ) (ht : 0 < t) :
    radialFlux f t = t * sphereSurfaceIntegral f t := by
  exact radialFlux_formula f t ht

theorem gap10 (f : SpaceTimeField) (t : ℝ) (ht : 0 < t)
    (hf : IsC1 f) :
    deriv (ballIntegral f) t =
      sphereSurfaceIntegral f t + timeDerivativeVolume f t := by
  exact reynolds_formula f t ht hf

theorem gap11 (f : SpaceTimeField) (t : ℝ) (ht : 0 < t)
    (hf : IsC1 f) :
    deriv (ballIntegral f) t =
      sphereSurfaceIntegral f t + timeDerivativeVolume f t := by
  exact reynolds_formula f t ht hf

end

end ProofGap.Exercise4386
