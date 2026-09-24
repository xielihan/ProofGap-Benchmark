import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise4194

noncomputable section

open MeasureTheory Set

private abbrev Point3 := ℝ × ℝ × ℝ

def cube (a : ℝ) : Set (ℝ × ℝ × ℝ) :=
  {w | 0 ≤ w.1 ∧ w.1 ≤ a ∧
    0 ≤ w.2.1 ∧ w.2.1 ≤ a ∧
    0 ≤ w.2.2 ∧ w.2.2 ≤ a}

def singularRadiusSquared (phi psi : ℝ → ℝ) (x y z : ℝ) : ℝ :=
  (y - phi x) ^ 2 + (z - psi x) ^ 2

def modelWeight (phi psi : ℝ → ℝ) (p : ℝ)
    (w : ℝ × ℝ × ℝ) : ℝ :=
  1 / Real.rpow
    (singularRadiusSquared phi psi w.1 w.2.1 w.2.2) p

def weightedIntegrand (f : ℝ × ℝ × ℝ → ℝ)
    (phi psi : ℝ → ℝ) (p : ℝ) (w : ℝ × ℝ × ℝ) : ℝ :=
  f w / Real.rpow
    (singularRadiusSquared phi psi w.1 w.2.1 w.2.2) p

def modelIntegral (a : ℝ) (phi psi : ℝ → ℝ) (p : ℝ) : ℝ :=
  ∫ w in cube a, modelWeight phi psi p w

def absoluteWeightedIntegral (a : ℝ) (f : ℝ × ℝ × ℝ → ℝ)
    (phi psi : ℝ → ℝ) (p : ℝ) : ℝ :=
  ∫ w in cube a,
    |f w| / Real.rpow
      (singularRadiusSquared phi psi w.1 w.2.1 w.2.2) p

def sliceIntegral (a : ℝ) (phi psi : ℝ → ℝ) (p x : ℝ) : ℝ :=
  ∫ y in (0 : ℝ)..a,
    ∫ z in (0 : ℝ)..a,
      1 / Real.rpow (singularRadiusSquared phi psi x y z) p

def translatedRectangle (a : ℝ) (phi psi : ℝ → ℝ)
    (x : ℝ) : Set (ℝ × ℝ) :=
  {w | -phi x ≤ w.1 ∧ w.1 ≤ a - phi x ∧
    -psi x ≤ w.2 ∧ w.2 ≤ a - psi x}

def disk (radius : ℝ) : Set (ℝ × ℝ) :=
  {w | w.1 ^ 2 + w.2 ^ 2 ≤ radius ^ 2}

def diskModelIntegral (radius p : ℝ) : ℝ :=
  ∫ w in disk radius,
    1 / Real.rpow (w.1 ^ 2 + w.2 ^ 2) p

def curveAvoidsCube (a : ℝ) (phi psi : ℝ → ℝ) : Prop :=
  ∀ x ∈ Set.Icc (0 : ℝ) a,
    phi x < 0 ∨ a < phi x ∨ psi x < 0 ∨ a < psi x

def interiorCurvePoint (a : ℝ) (phi psi : ℝ → ℝ) : Prop :=
  ∃ x ∈ Set.Icc (0 : ℝ) a,
    0 < phi x ∧ phi x < a ∧ 0 < psi x ∧ psi x < a

def translationJacobian : ℝ :=
  1

private abbrev integrand := weightedIntegrand

private def curveMissesCube (φ ψ : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x ∈ Icc (0 : ℝ) a, ¬(φ x ∈ Icc (0 : ℝ) a ∧ ψ x ∈ Icc (0 : ℝ) a)

private def curveEntersInterior (φ ψ : ℝ → ℝ) (a : ℝ) : Prop :=
  ∃ x ∈ Icc (0 : ℝ) a, φ x ∈ Ioo (0 : ℝ) a ∧ ψ x ∈ Ioo (0 : ℝ) a

/-! Exercise 4194. -/

private abbrev Point2 := ℝ × ℝ

private def normSq (w : Point2) : ℝ :=
  w.1 ^ 2 + w.2 ^ 2

private theorem disk_measurable (R : ℝ) :
    MeasurableSet (disk R) := by
  unfold disk
  measurability

private theorem normSq_nonneg (w : Point2) :
    0 ≤ normSq w := by
  unfold normSq
  positivity

private theorem measurable_rpow_const (a : ℝ) :
    Measurable (fun x : ℝ => Real.rpow x a) := by
  apply measurable_of_continuousOn_compl_singleton 0
  exact continuousOn_id.rpow_const
    (fun x hx => Or.inl (by simpa using hx))

private def radialKernel (p : ℝ) (w : Point2) : ℝ :=
  1 / Real.rpow (normSq w) p

private theorem radialKernel_eq (p : ℝ) (w : Point2) :
    radialKernel p w = Real.rpow (normSq w) (-p) := by
  unfold radialKernel
  rw [one_div]
  exact (Real.rpow_neg (normSq_nonneg w) p).symm

private theorem radialKernel_measurable (p : ℝ) :
    Measurable (radialKernel p) := by
  have heq :
      radialKernel p =
        fun w : Point2 => Real.rpow (normSq w) (-p) := by
    funext w
    exact radialKernel_eq p w
  rw [heq]
  exact (measurable_rpow_const (-p)).comp
    ((measurable_fst.pow_const 2).add
      (measurable_snd.pow_const 2))

private theorem radialKernel_nonneg (p : ℝ) (w : Point2) :
    0 ≤ radialKernel p w := by
  rw [radialKernel_eq]
  exact Real.rpow_nonneg (normSq_nonneg w) (-p)

private def radialOrigin (p r : ℝ) : ℝ :=
  r * Real.rpow r (-2 * p)

private theorem radialOrigin_integrableOn_iff
    (p R : ℝ) (hR : 0 < R) :
    IntegrableOn (radialOrigin p) (Ioc (0 : ℝ) R) volume ↔
      p < 1 := by
  rw [integrableOn_Ioc_iff_integrableOn_Ioo]
  have hcongr :
      IntegrableOn (radialOrigin p) (Ioo (0 : ℝ) R) volume ↔
        IntegrableOn
          (fun r : ℝ => Real.rpow r (1 - 2 * p))
          (Ioo (0 : ℝ) R) volume := by
    apply integrableOn_congr_fun
    · intro r hr
      unfold radialOrigin
      calc
        r * Real.rpow r (-2 * p) =
            Real.rpow r 1 * Real.rpow r (-2 * p) := by
          congr 1
          exact (Real.rpow_one r).symm
        _ = Real.rpow r (1 + (-2 * p)) :=
          (Real.rpow_add hr.1 1 (-2 * p)).symm
        _ = Real.rpow r (1 - 2 * p) := by ring
    · exact measurableSet_Ioo
  rw [hcongr]
  constructor
  · intro h
    have he :=
      (intervalIntegral.integrableOn_Ioo_rpow_iff hR).mp h
    linarith
  · intro hp
    apply (intervalIntegral.integrableOn_Ioo_rpow_iff hR).mpr
    linarith

private theorem integrable_polar_iff (F : Point2 → ℝ) :
    Integrable F volume ↔
      IntegrableOn
        (fun z : Point2 => z.1 * F (polarCoord.symm z))
        polarCoord.target volume := by
  have hchange :=
    integrableOn_image_iff_integrableOn_abs_det_fderiv_smul
      (μ := (volume : Measure Point2))
      (f := polarCoord.symm)
      (f' := fderivPolarCoordSymm)
      polarCoord.open_target.measurableSet
      (fun z _ =>
        (hasFDerivAt_polarCoord_symm z).hasFDerivWithinAt)
      polarCoord.symm.injOn F
  rw [polarCoord.symm_image_target_eq_source] at hchange
  have hsource :
      IntegrableOn F polarCoord.source volume ↔
        Integrable F volume := by
    rw [IntegrableOn,
      Measure.restrict_congr_set polarCoord_source_ae_eq_univ,
      Measure.restrict_univ]
  calc
    Integrable F volume ↔
        IntegrableOn F polarCoord.source volume :=
      hsource.symm
    _ ↔ IntegrableOn
          (fun z : Point2 =>
            |(fderivPolarCoordSymm z).det| •
              F (polarCoord.symm z))
          polarCoord.target volume :=
      hchange
    _ ↔ IntegrableOn
          (fun z : Point2 => z.1 * F (polarCoord.symm z))
          polarCoord.target volume := by
      apply integrableOn_congr_fun
      · intro z hz
        change
          |(fderivPolarCoordSymm z).det| •
              F (polarCoord.symm z) =
            z.1 * F (polarCoord.symm z)
        rw [det_fderivPolarCoordSymm,
          abs_of_pos hz.1, smul_eq_mul]
      · exact polarCoord.open_target.measurableSet

private theorem integrableOn_indicator_subset_iff
    {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {s t : Set α} {F : α → ℝ}
    (hs : MeasurableSet s) (ht : MeasurableSet t)
    (hst : s ⊆ t) :
    IntegrableOn (s.indicator F) t μ ↔
      IntegrableOn F s μ := by
  constructor
  · intro h
    have hi := h.integrable_indicator ht
    have heq :
        t.indicator (s.indicator F) = s.indicator F := by
      funext x
      by_cases hx : x ∈ s
      · simp [hx, hst hx]
      · simp [hx]
    rw [heq] at hi
    exact (integrable_indicator_iff hs).mp hi
  · intro h
    exact (h.integrable_indicator hs).integrableOn

private def polarRectangle (R : ℝ) : Set Point2 :=
  Ioc (0 : ℝ) R ×ˢ Ioo (-Real.pi) Real.pi

private theorem polarRectangle_measurable (R : ℝ) :
    MeasurableSet (polarRectangle R) :=
  measurableSet_Ioc.prod measurableSet_Ioo

private theorem polarRectangle_subset_target (R : ℝ) :
    polarRectangle R ⊆ polarCoord.target := by
  intro z hz
  exact ⟨hz.1.1, hz.2⟩

private def diskModel (R p : ℝ) (w : Point2) : ℝ :=
  (disk R).indicator (radialKernel p) w

private theorem polar_normSq (z : Point2) :
    normSq (polarCoord.symm z) = z.1 ^ 2 := by
  unfold normSq
  simp only [polarCoord_symm_apply]
  nlinarith [Real.sin_sq_add_cos_sq z.2]

private theorem radialKernel_axis
    (p r : ℝ) (hr : 0 < r) :
    radialKernel p (r, 0) =
      Real.rpow r (-2 * p) := by
  calc
    radialKernel p (r, 0) =
        Real.rpow (r ^ 2) (-p) := by
      rw [radialKernel_eq]
      unfold normSq
      norm_num
    _ = Real.rpow r ((2 : ℝ) * (-p)) :=
      (Real.rpow_natCast_mul hr.le 2 (-p)).symm
    _ = Real.rpow r (-2 * p) := by
      congr 1
      ring

private theorem polar_rpow_identity
    (p r : ℝ) (hr : 0 < r) :
    r * radialKernel p (r, 0) =
      Real.rpow r (1 - 2 * p) := by
  rw [radialKernel_axis p r hr]
  calc
    r * Real.rpow r (-2 * p) =
        Real.rpow r 1 * Real.rpow r (-2 * p) := by
      congr 1
      exact (Real.rpow_one r).symm
    _ = Real.rpow r (1 + (-2 * p)) :=
      (Real.rpow_add hr 1 (-2 * p)).symm
    _ = Real.rpow r (1 - 2 * p) := by ring

private theorem polar_diskModel_eq
    (R p : ℝ) (hR : 0 < R) :
    EqOn
      (fun z : Point2 =>
        z.1 * diskModel R p (polarCoord.symm z))
      ((polarRectangle R).indicator
        (fun z : Point2 => radialOrigin p z.1))
      polarCoord.target := by
  intro z hz
  have hr : 0 < z.1 := hz.1
  by_cases hrR : z.1 ≤ R
  · have hdisk : polarCoord.symm z ∈ disk R := by
      change normSq (polarCoord.symm z) ≤ R ^ 2
      rw [polar_normSq]
      nlinarith
    have hrect : z ∈ polarRectangle R :=
      ⟨⟨hr, hrR⟩, hz.2⟩
    simp only [diskModel]
    rw [indicator_of_mem hdisk, indicator_of_mem hrect]
    unfold radialOrigin
    have hkernel :
        radialKernel p (polarCoord.symm z) =
          radialKernel p (z.1, 0) := by
      unfold radialKernel
      rw [polar_normSq]
      unfold normSq
      norm_num
    rw [hkernel, radialKernel_axis p z.1 hr]
  · have hdisk : polarCoord.symm z ∉ disk R := by
      intro hdisk
      apply hrR
      change normSq (polarCoord.symm z) ≤ R ^ 2 at hdisk
      rw [polar_normSq] at hdisk
      nlinarith
    have hrect : z ∉ polarRectangle R := by
      intro hrect
      exact hrR hrect.1.2
    simp only [diskModel]
    rw [indicator_of_notMem hdisk,
      indicator_of_notMem hrect, mul_zero]

private theorem radialOnPolarRectangle_iff
    (p R : ℝ) :
    IntegrableOn
        (fun z : Point2 => radialOrigin p z.1)
        (polarRectangle R) volume ↔
      IntegrableOn (radialOrigin p) (Ioc (0 : ℝ) R) volume := by
  have hangleVol :
      (volume : Measure ℝ) (Ioo (-Real.pi) Real.pi) ≠ 0 := by
    rw [Real.volume_Ioo]
    apply ENNReal.ofReal_ne_zero_iff.mpr
    linarith [Real.pi_pos]
  have hangleNe :
      (volume : Measure ℝ).restrict
          (Ioo (-Real.pi) Real.pi) ≠ 0 := by
    exact mt Measure.restrict_eq_zero.mp hangleVol
  rw [IntegrableOn, Measure.volume_eq_prod,
    polarRectangle, ← Measure.prod_restrict]
  exact Integrable.comp_fst_iff hangleNe

private theorem diskModel_integrable_iff
    (R p : ℝ) (hR : 0 < R) :
    Integrable (diskModel R p) volume ↔ p < 1 := by
  calc
    Integrable (diskModel R p) volume ↔
        IntegrableOn
          (fun z : Point2 =>
            z.1 * diskModel R p (polarCoord.symm z))
          polarCoord.target volume :=
      integrable_polar_iff (diskModel R p)
    _ ↔ IntegrableOn
          ((polarRectangle R).indicator
            (fun z : Point2 => radialOrigin p z.1))
          polarCoord.target volume := by
      apply integrableOn_congr_fun
      · exact polar_diskModel_eq R p hR
      · exact polarCoord.open_target.measurableSet
    _ ↔ IntegrableOn
          (fun z : Point2 => radialOrigin p z.1)
          (polarRectangle R) volume :=
      integrableOn_indicator_subset_iff
        (polarRectangle_measurable R)
        polarCoord.open_target.measurableSet
        (polarRectangle_subset_target R)
    _ ↔ IntegrableOn (radialOrigin p)
          (Ioc (0 : ℝ) R) volume :=
      radialOnPolarRectangle_iff p R
    _ ↔ p < 1 :=
      radialOrigin_integrableOn_iff p R hR

private theorem radialKernel_integrableOn_disk_iff
    (R p : ℝ) (hR : 0 < R) :
    IntegrableOn (radialKernel p) (disk R) volume ↔
      p < 1 := by
  rw [← integrable_indicator_iff (disk_measurable R)]
  exact diskModel_integrable_iff R p hR

private theorem cube_eq_box (a : ℝ) :
    cube a =
      Icc (0 : ℝ) a ×ˢ
        (Icc (0 : ℝ) a ×ˢ Icc (0 : ℝ) a) := by
  ext q
  simp only [cube, mem_setOf_eq, mem_prod, mem_Icc]
  tauto

private theorem cube_measurable (a : ℝ) :
    MeasurableSet (cube a) := by
  rw [cube_eq_box]
  exact measurableSet_Icc.prod
    (measurableSet_Icc.prod measurableSet_Icc)

private theorem cube_compact (a : ℝ) :
    IsCompact (cube a) := by
  rw [cube_eq_box]
  exact isCompact_Icc.prod
    (isCompact_Icc.prod isCompact_Icc)

private theorem volume_point3 :
    (volume : Measure Point3) =
      (volume : Measure ℝ).prod
        (volume : Measure Point2) := by
  rw [Measure.volume_eq_prod]

private def modelKernel
    (φ ψ : ℝ → ℝ) (p : ℝ) (q : Point3) : ℝ :=
  radialKernel p (q.2.1 - φ q.1, q.2.2 - ψ q.1)

private theorem modelKernel_nonneg
    (φ ψ : ℝ → ℝ) (p : ℝ) (q : Point3) :
    0 ≤ modelKernel φ ψ p q :=
  radialKernel_nonneg p _

private def extendIcc (a : ℝ) (g : ℝ → ℝ) : ℝ → ℝ :=
  (Icc (0 : ℝ) a).piecewise g 0

private theorem extendIcc_eq
    (a : ℝ) (g : ℝ → ℝ) {x : ℝ}
    (hx : x ∈ Icc (0 : ℝ) a) :
    extendIcc a g x = g x := by
  simp [extendIcc, hx]

private theorem extendIcc_measurable
    (a : ℝ) (g : ℝ → ℝ)
    (hg : ContinuousOn g (Icc (0 : ℝ) a)) :
    Measurable (extendIcc a g) := by
  unfold extendIcc
  exact hg.measurable_piecewise
    continuous_const.continuousOn measurableSet_Icc

private def shiftEquivRaw
    (Φ Ψ : ℝ → ℝ) : Point3 ≃ Point3 where
  toFun q :=
    (q.1, (q.2.1 + Φ q.1, q.2.2 + Ψ q.1))
  invFun q :=
    (q.1, (q.2.1 - Φ q.1, q.2.2 - Ψ q.1))
  left_inv q := by
    ext <;> simp
  right_inv q := by
    ext <;> simp

private def shiftEquiv
    (Φ Ψ : ℝ → ℝ) (hΦ : Measurable Φ) (hΨ : Measurable Ψ) :
    Point3 ≃ᵐ Point3 where
  toEquiv := shiftEquivRaw Φ Ψ
  measurable_toFun := by
    exact measurable_fst.prodMk
      ((measurable_snd.fst.add
          (hΦ.comp measurable_fst)).prodMk
        (measurable_snd.snd.add
          (hΨ.comp measurable_fst)))
  measurable_invFun := by
    exact measurable_fst.prodMk
      ((measurable_snd.fst.sub
          (hΦ.comp measurable_fst)).prodMk
        (measurable_snd.snd.sub
          (hΨ.comp measurable_fst)))

@[simp] private theorem shiftEquiv_apply
    (Φ Ψ : ℝ → ℝ) (hΦ : Measurable Φ) (hΨ : Measurable Ψ)
    (q : Point3) :
    shiftEquiv Φ Ψ hΦ hΨ q =
      (q.1, (q.2.1 + Φ q.1, q.2.2 + Ψ q.1)) := rfl

private theorem shiftEquiv_measurePreserving
    (Φ Ψ : ℝ → ℝ) (hΦ : Measurable Φ) (hΨ : Measurable Ψ) :
    MeasurePreserving
      (shiftEquiv Φ Ψ hΦ hΨ) volume volume := by
  have huncurry :
      Measurable
        (Function.uncurry
          (fun x (w : Point2) =>
            (w.1 + Φ x, w.2 + Ψ x))) := by
    exact
      (measurable_snd.fst.add
        (hΦ.comp measurable_fst)).prodMk
          (measurable_snd.snd.add
            (hΨ.comp measurable_fst))
  have hmp :
      MeasurePreserving
        (fun q : ℝ × Point2 =>
          (q.1,
            (q.2.1 + Φ q.1, q.2.2 + Ψ q.1)))
        ((volume : Measure ℝ).prod (volume : Measure Point2))
        ((volume : Measure ℝ).prod (volume : Measure Point2)) := by
    apply (MeasurePreserving.id
      (volume : Measure ℝ)).skew_product huncurry
    filter_upwards with x
    have ht :=
      measurePreserving_add_right
        (volume : Measure Point2) (Φ x, Ψ x)
    simpa [Prod.fst, Prod.snd] using ht.map_eq
  rw [volume_point3]
  exact hmp

private theorem exists_common_bound
    (φ ψ : ℝ → ℝ) (a : ℝ)
    (hφ : ContinuousOn φ (Icc (0 : ℝ) a))
    (hψ : ContinuousOn ψ (Icc (0 : ℝ) a)) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ x ∈ Icc (0 : ℝ) a,
        |φ x| ≤ C ∧ |ψ x| ≤ C := by
  have hφb :
      BddAbove ((fun x : ℝ => |φ x|) ''
        Icc (0 : ℝ) a) :=
    isCompact_Icc.bddAbove_image hφ.abs
  have hψb :
      BddAbove ((fun x : ℝ => |ψ x|) ''
        Icc (0 : ℝ) a) :=
    isCompact_Icc.bddAbove_image hψ.abs
  rcases hφb with ⟨Cφ, hCφ⟩
  rcases hψb with ⟨Cψ, hCψ⟩
  refine ⟨max (max Cφ Cψ) 0, le_max_right _ _, ?_⟩
  intro x hx
  constructor
  · exact (hCφ ⟨x, hx, rfl⟩).trans
      ((le_max_left Cφ Cψ).trans
        (le_max_left (max Cφ Cψ) 0))
  · exact (hCψ ⟨x, hx, rfl⟩).trans
      ((le_max_right Cφ Cψ).trans
        (le_max_left (max Cφ Cψ) 0))

private theorem modelKernel_integrable_of_lt
    (φ ψ : ℝ → ℝ) (a p : ℝ)
    (ha : 0 < a)
    (hφ : ContinuousOn φ (Icc (0 : ℝ) a))
    (hψ : ContinuousOn ψ (Icc (0 : ℝ) a))
    (hp : p < 1) :
    IntegrableOn (modelKernel φ ψ p) (cube a) volume := by
  let Φ := extendIcc a φ
  let Ψ := extendIcc a ψ
  have hΦ : Measurable Φ := extendIcc_measurable a φ hφ
  have hΨ : Measurable Ψ := extendIcc_measurable a ψ hψ
  let T : Point3 ≃ᵐ Point3 := shiftEquiv Φ Ψ hΦ hΨ
  have hT : MeasurePreserving T volume volume :=
    shiftEquiv_measurePreserving Φ Ψ hΦ hΨ
  rcases exists_common_bound φ ψ a hφ hψ with
    ⟨C, hC0, hC⟩
  let B : ℝ := a + C
  let R : ℝ := 2 * B
  have hB : 0 < B := by
    dsimp [B]
    linarith
  have hR : 0 < R := by
    dsimp [R]
    positivity
  have hrad :
      IntegrableOn (radialKernel p) (disk R) volume :=
    (radialKernel_integrableOn_disk_iff R p hR).mpr hp
  have hxconst :
      IntegrableOn (fun _ : ℝ => (1 : ℝ))
        (Icc (0 : ℝ) a) volume :=
    integrableOn_const (hs := isCompact_Icc.measure_ne_top)
  have hprodRaw :=
    (show Integrable (fun _ : ℝ => (1 : ℝ))
        ((volume : Measure ℝ).restrict (Icc (0 : ℝ) a))
      from hxconst).mul_prod
      (show Integrable (radialKernel p)
          ((volume : Measure Point2).restrict (disk R))
        from hrad)
  have hprod :
      IntegrableOn
        (fun q : Point3 => radialKernel p q.2)
        (Icc (0 : ℝ) a ×ˢ disk R) volume := by
    rw [IntegrableOn, volume_point3,
      ← Measure.prod_restrict]
    simpa using hprodRaw
  have hpreSubset :
      T ⁻¹' cube a ⊆
        Icc (0 : ℝ) a ×ˢ disk R := by
    intro q hq
    change T q ∈ cube a at hq
    change
      0 ≤ (T q).1 ∧ (T q).1 ≤ a ∧
        0 ≤ (T q).2.1 ∧ (T q).2.1 ≤ a ∧
        0 ≤ (T q).2.2 ∧ (T q).2.2 ≤ a at hq
    have hx : q.1 ∈ Icc (0 : ℝ) a := by
      exact ⟨by simpa [T] using hq.1,
        by simpa [T] using hq.2.1⟩
    have hφC := (hC q.1 hx).1
    have hψC := (hC q.1 hx).2
    have hΦeq : Φ q.1 = φ q.1 :=
      extendIcc_eq a φ hx
    have hΨeq : Ψ q.1 = ψ q.1 :=
      extendIcc_eq a ψ hx
    have hyBounds :
        0 ≤ q.2.1 + φ q.1 ∧
          q.2.1 + φ q.1 ≤ a := by
      constructor
      · simpa [T, hΦeq] using hq.2.2.1
      · simpa [T, hΦeq] using hq.2.2.2.1
    have hzBounds :
        0 ≤ q.2.2 + ψ q.1 ∧
          q.2.2 + ψ q.1 ≤ a := by
      constructor
      · simpa [T, hΨeq] using hq.2.2.2.2.1
      · simpa [T, hΨeq] using hq.2.2.2.2.2
    have hφabs := abs_le.mp hφC
    have hψabs := abs_le.mp hψC
    have hyAbs : |q.2.1| ≤ B := by
      rw [abs_le]
      dsimp [B]
      constructor <;> linarith
    have hzAbs : |q.2.2| ≤ B := by
      rw [abs_le]
      dsimp [B]
      constructor <;> linarith
    have hySq : q.2.1 ^ 2 ≤ B ^ 2 := by
      nlinarith [sq_nonneg (B - |q.2.1|)]
    have hzSq : q.2.2 ^ 2 ≤ B ^ 2 := by
      nlinarith [sq_nonneg (B - |q.2.2|)]
    refine ⟨hx, ?_⟩
    change normSq q.2 ≤ R ^ 2
    unfold normSq
    dsimp [R]
    nlinarith [sq_nonneg B]
  have hshifted :
      IntegrableOn
        (fun q : Point3 => radialKernel p q.2)
        (T ⁻¹' cube a) volume :=
    hprod.mono_set hpreSubset
  have hcomp :
      IntegrableOn (modelKernel φ ψ p ∘ T)
        (T ⁻¹' cube a) volume := by
    apply hshifted.congr_fun
    · intro q hq
      have hcube : T q ∈ cube a := hq
      have hx : q.1 ∈ Icc (0 : ℝ) a := by
        change
          0 ≤ (T q).1 ∧ (T q).1 ≤ a ∧
            0 ≤ (T q).2.1 ∧ (T q).2.1 ≤ a ∧
            0 ≤ (T q).2.2 ∧ (T q).2.2 ≤ a at hcube
        exact ⟨by simpa [T] using hcube.1,
          by simpa [T] using hcube.2.1⟩
      have hΦeq : Φ q.1 = φ q.1 :=
        extendIcc_eq a φ hx
      have hΨeq : Ψ q.1 = ψ q.1 :=
        extendIcc_eq a ψ hx
      unfold Function.comp modelKernel
      simp [T, hΦeq, hΨeq]
    · exact (cube_measurable a).preimage T.measurable
  exact
    (hT.integrableOn_comp_preimage T.measurableEmbedding).mp hcomp

private theorem integrand_eq_mul_model
    (f : Point3 → ℝ) (φ ψ : ℝ → ℝ) (p : ℝ)
    (q : Point3) :
    integrand f φ ψ p q =
      f q * modelKernel φ ψ p q := by
  unfold integrand weightedIntegrand singularRadiusSquared
    modelKernel radialKernel normSq
  ring

private theorem integrand_integrable_of_model
    (f : Point3 → ℝ) (φ ψ : ℝ → ℝ)
    (a p M : ℝ)
    (hf : Measurable f)
    (hupper : ∀ q ∈ cube a, |f q| ≤ M)
    (hmodel :
      IntegrableOn (modelKernel φ ψ p) (cube a) volume) :
    IntegrableOn (integrand f φ ψ p) (cube a) volume := by
  have hfmeas :
      AEStronglyMeasurable f
        (volume.restrict (cube a)) :=
    hf.aestronglyMeasurable.restrict
  have hfbound :
      ∀ᵐ q ∂volume.restrict (cube a), ‖f q‖ ≤ M := by
    filter_upwards [ae_restrict_mem (cube_measurable a)] with q hq
    rw [Real.norm_eq_abs]
    exact hupper q hq
  have hmul :
      Integrable
        (fun q : Point3 =>
          f q * modelKernel φ ψ p q)
        (volume.restrict (cube a)) :=
    hmodel.bdd_mul hfmeas hfbound
  apply hmul.congr
  filter_upwards with q
  exact (integrand_eq_mul_model f φ ψ p q).symm

private theorem model_integrable_of_integrand
    (f : Point3 → ℝ) (φ ψ : ℝ → ℝ)
    (a p m : ℝ)
    (hm : 0 < m)
    (hf : Measurable f)
    (hlower : ∀ q ∈ cube a, m ≤ |f q|)
    (hint :
      IntegrableOn (integrand f φ ψ p) (cube a) volume) :
    IntegrableOn (modelKernel φ ψ p) (cube a) volume := by
  have hfne :
      ∀ q ∈ cube a, f q ≠ 0 := by
    intro q hq hzero
    have h := hlower q hq
    simp [hzero] at h
    linarith
  have hinvMeas :
      AEStronglyMeasurable
        (fun q : Point3 => 1 / f q)
        (volume.restrict (cube a)) :=
    (measurable_const.div hf).aestronglyMeasurable.restrict
  have hinvBound :
      ∀ᵐ q ∂volume.restrict (cube a),
        ‖1 / f q‖ ≤ 1 / m := by
    filter_upwards [ae_restrict_mem (cube_measurable a)] with q hq
    rw [Real.norm_eq_abs, abs_div, abs_one]
    exact one_div_le_one_div_of_le hm (hlower q hq)
  have hmul :
      Integrable
        (fun q : Point3 =>
          (1 / f q) * integrand f φ ψ p q)
        (volume.restrict (cube a)) :=
    hint.bdd_mul hinvMeas hinvBound
  apply hmul.congr
  filter_upwards [ae_restrict_mem (cube_measurable a)] with q hq
  rw [integrand_eq_mul_model]
  calc
    (1 / f q) * (f q * modelKernel φ ψ p q) =
        ((1 / f q) * f q) *
          modelKernel φ ψ p q := by ring
    _ = modelKernel φ ψ p q := by
      rw [one_div_mul_cancel (hfne q hq), one_mul]

private theorem modelKernel_integrable_of_miss
    (φ ψ : ℝ → ℝ) (a p : ℝ)
    (hp : 1 ≤ p)
    (hφ : ContinuousOn φ (Icc (0 : ℝ) a))
    (hψ : ContinuousOn ψ (Icc (0 : ℝ) a))
    (hmiss : curveMissesCube φ ψ a) :
    IntegrableOn (modelKernel φ ψ p) (cube a) volume := by
  have hφcomp :
      ContinuousOn (fun q : Point3 => φ q.1) (cube a) := by
    apply hφ.comp continuousOn_fst
    intro q hq
    change
      0 ≤ q.1 ∧ q.1 ≤ a ∧
        0 ≤ q.2.1 ∧ q.2.1 ≤ a ∧
        0 ≤ q.2.2 ∧ q.2.2 ≤ a at hq
    exact ⟨hq.1, hq.2.1⟩
  have hψcomp :
      ContinuousOn (fun q : Point3 => ψ q.1) (cube a) := by
    apply hψ.comp continuousOn_fst
    intro q hq
    change
      0 ≤ q.1 ∧ q.1 ≤ a ∧
        0 ≤ q.2.1 ∧ q.2.1 ≤ a ∧
        0 ≤ q.2.2 ∧ q.2.2 ≤ a at hq
    exact ⟨hq.1, hq.2.1⟩
  let base : Point3 → ℝ := fun q =>
    (q.2.1 - φ q.1) ^ 2 +
      (q.2.2 - ψ q.1) ^ 2
  have hbase :
      ContinuousOn base (cube a) := by
    dsimp [base]
    exact ((continuousOn_snd.fst.sub hφcomp).pow 2).add
      ((continuousOn_snd.snd.sub hψcomp).pow 2)
  have hbasePos :
      ∀ q ∈ cube a, 0 < base q := by
    intro q hq
    have hqc := hq
    change
      0 ≤ q.1 ∧ q.1 ≤ a ∧
        0 ≤ q.2.1 ∧ q.2.1 ≤ a ∧
        0 ≤ q.2.2 ∧ q.2.2 ≤ a at hqc
    have hx : q.1 ∈ Icc (0 : ℝ) a :=
      ⟨hqc.1, hqc.2.1⟩
    have hnothit := hmiss q.1 hx
    have hdiff :
        q.2.1 - φ q.1 ≠ 0 ∨
          q.2.2 - ψ q.1 ≠ 0 := by
      by_contra hnot
      push_neg at hnot
      apply hnothit
      have hy : q.2.1 = φ q.1 := sub_eq_zero.mp hnot.1
      have hz : q.2.2 = ψ q.1 := sub_eq_zero.mp hnot.2
      exact
        ⟨by simpa [← hy] using
            (show q.2.1 ∈ Icc (0 : ℝ) a from
              ⟨hqc.2.2.1, hqc.2.2.2.1⟩),
          by simpa [← hz] using
            (show q.2.2 ∈ Icc (0 : ℝ) a from
              ⟨hqc.2.2.2.2.1, hqc.2.2.2.2.2⟩)⟩
    dsimp [base]
    rcases hdiff with hy | hz
    · nlinarith [sq_pos_of_ne_zero hy,
        sq_nonneg (q.2.2 - ψ q.1)]
    · nlinarith [sq_nonneg (q.2.1 - φ q.1),
        sq_pos_of_ne_zero hz]
  have hden :
      ContinuousOn
        (fun q : Point3 => Real.rpow (base q) p)
        (cube a) :=
    (Real.continuous_rpow_const
      (le_trans zero_le_one hp)).comp_continuousOn hbase
  have hmodelCont :
      ContinuousOn (modelKernel φ ψ p) (cube a) := by
    have hrecip :
        ContinuousOn
          (fun q : Point3 => 1 / Real.rpow (base q) p)
          (cube a) :=
      continuousOn_const.div hden
        (fun q hq =>
          (Real.rpow_pos_of_pos (hbasePos q hq) p).ne')
    dsimp [base] at hrecip
    unfold modelKernel radialKernel normSq
    exact hrecip
  exact hmodelCont.integrableOn_compact (cube_compact a)

private theorem exists_interval_near
    (a x₀ δ : ℝ) (ha : 0 < a)
    (hx₀ : x₀ ∈ Icc (0 : ℝ) a) (hδ : 0 < δ) :
    ∃ l u : ℝ, l < u ∧
      Icc l u ⊆ Icc (0 : ℝ) a ∧
      ∀ x ∈ Icc l u, |x - x₀| < δ := by
  by_cases hxright : x₀ < a
  · let η : ℝ := min (δ / 2) ((a - x₀) / 2)
    have hη : 0 < η := by
      dsimp [η]
      exact lt_min (by linarith) (by linarith)
    refine ⟨x₀, x₀ + η, by linarith, ?_, ?_⟩
    · intro x hx
      have hηa : η ≤ (a - x₀) / 2 :=
        (min_le_right _ _)
      exact ⟨by linarith [hx₀.1, hx.1],
        by linarith [hx.2]⟩
    · intro x hx
      have hηδ : η ≤ δ / 2 :=
        min_le_left _ _
      rw [abs_of_nonneg (by linarith [hx.1])]
      linarith [hx.2]
  · have hxEq : x₀ = a := by
      linarith [hx₀.2]
    let η : ℝ := min (δ / 2) (a / 2)
    have hη : 0 < η := by
      dsimp [η]
      exact lt_min (by linarith) (by linarith)
    refine ⟨x₀ - η, x₀, by linarith, ?_, ?_⟩
    · intro x hx
      have hηa : η ≤ a / 2 :=
        min_le_right _ _
      exact ⟨by linarith [hx.1], by linarith [hx.2, hx₀.2]⟩
    · intro x hx
      have hηδ : η ≤ δ / 2 :=
        min_le_left _ _
      rw [abs_of_nonpos (by linarith [hx.2])]
      linarith [hx.1]

private theorem exists_uniform_interior_bounds
    (φ ψ : ℝ → ℝ) (a : ℝ) (ha : 0 < a)
    (hφ : ContinuousOn φ (Icc (0 : ℝ) a))
    (hψ : ContinuousOn ψ (Icc (0 : ℝ) a))
    (henter : curveEntersInterior φ ψ a) :
    ∃ ε l u : ℝ, 0 < ε ∧ l < u ∧
      Icc l u ⊆ Icc (0 : ℝ) a ∧
      ∀ x ∈ Icc l u,
        ε ≤ φ x ∧ φ x ≤ a - ε ∧
        ε ≤ ψ x ∧ ψ x ≤ a - ε := by
  rcases henter with ⟨x₀, hx₀, hφ₀, hψ₀⟩
  let d : ℝ :=
    min (min (φ x₀) (a - φ x₀))
      (min (ψ x₀) (a - ψ x₀))
  have hd : 0 < d := by
    dsimp [d]
    exact lt_min
      (lt_min hφ₀.1 (by linarith [hφ₀.2]))
      (lt_min hψ₀.1 (by linarith [hψ₀.2]))
  let ε : ℝ := d / 3
  have hε : 0 < ε := by
    dsimp [ε]
    positivity
  have hdφlo : d ≤ φ x₀ :=
    (min_le_left _ _).trans (min_le_left _ _)
  have hdφhi : d ≤ a - φ x₀ :=
    (min_le_left _ _).trans (min_le_right _ _)
  have hdψlo : d ≤ ψ x₀ :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hdψhi : d ≤ a - ψ x₀ :=
    (min_le_right _ _).trans (min_le_right _ _)
  rcases
      (Metric.continuousWithinAt_iff.mp
        (hφ.continuousWithinAt hx₀)) ε hε with
    ⟨δφ, hδφ, hφclose⟩
  rcases
      (Metric.continuousWithinAt_iff.mp
        (hψ.continuousWithinAt hx₀)) ε hε with
    ⟨δψ, hδψ, hψclose⟩
  let δ : ℝ := min δφ δψ
  have hδ : 0 < δ := by
    dsimp [δ]
    exact lt_min hδφ hδψ
  rcases exists_interval_near a x₀ δ ha hx₀ hδ with
    ⟨l, u, hlu, hsub, hnear⟩
  refine ⟨ε, l, u, hε, hlu, hsub, ?_⟩
  intro x hx
  have hxI := hsub hx
  have hφd :
      |φ x - φ x₀| < ε := by
    have hc := hφclose hxI
      (show dist x x₀ < δφ by
        rw [Real.dist_eq]
        exact (hnear x hx).trans_le
          (min_le_left δφ δψ))
    simpa [Real.dist_eq] using hc
  have hψd :
      |ψ x - ψ x₀| < ε := by
    have hc := hψclose hxI
      (show dist x x₀ < δψ by
        rw [Real.dist_eq]
        exact (hnear x hx).trans_le
          (min_le_right δφ δψ))
    simpa [Real.dist_eq] using hc
  have hdeq : d = 3 * ε := by
    dsimp [ε]
    ring
  have hφdiff := abs_lt.mp hφd
  have hψdiff := abs_lt.mp hψd
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor <;> nlinarith

private theorem modelKernel_not_integrable_of_enter
    (φ ψ : ℝ → ℝ) (a p : ℝ)
    (ha : 0 < a) (hp : 1 ≤ p)
    (hφ : ContinuousOn φ (Icc (0 : ℝ) a))
    (hψ : ContinuousOn ψ (Icc (0 : ℝ) a))
    (henter : curveEntersInterior φ ψ a) :
    ¬ IntegrableOn (modelKernel φ ψ p) (cube a) volume := by
  intro hmodel
  let Φ := extendIcc a φ
  let Ψ := extendIcc a ψ
  have hΦ : Measurable Φ := extendIcc_measurable a φ hφ
  have hΨ : Measurable Ψ := extendIcc_measurable a ψ hψ
  let T : Point3 ≃ᵐ Point3 := shiftEquiv Φ Ψ hΦ hΨ
  have hT : MeasurePreserving T volume volume :=
    shiftEquiv_measurePreserving Φ Ψ hΦ hΨ
  have hcomp :
      IntegrableOn (modelKernel φ ψ p ∘ T)
        (T ⁻¹' cube a) volume :=
    (hT.integrableOn_comp_preimage T.measurableEmbedding).mpr hmodel
  have hshifted :
      IntegrableOn
        (fun q : Point3 => radialKernel p q.2)
        (T ⁻¹' cube a) volume := by
    apply hcomp.congr_fun
    · intro q hq
      have hcube : T q ∈ cube a := hq
      have hx : q.1 ∈ Icc (0 : ℝ) a := by
        change
          0 ≤ (T q).1 ∧ (T q).1 ≤ a ∧
            0 ≤ (T q).2.1 ∧ (T q).2.1 ≤ a ∧
            0 ≤ (T q).2.2 ∧ (T q).2.2 ≤ a at hcube
        exact ⟨by simpa [T] using hcube.1,
          by simpa [T] using hcube.2.1⟩
      have hΦeq : Φ q.1 = φ q.1 :=
        extendIcc_eq a φ hx
      have hΨeq : Ψ q.1 = ψ q.1 :=
        extendIcc_eq a ψ hx
      unfold Function.comp modelKernel
      simp [T, hΦeq, hΨeq]
    · exact (cube_measurable a).preimage T.measurable
  rcases
      exists_uniform_interior_bounds φ ψ a ha hφ hψ henter with
    ⟨ε, l, u, hε, hlu, hJsub, hbounds⟩
  let J : Set ℝ := Icc l u
  have hlocalSubset :
      J ×ˢ disk ε ⊆ T ⁻¹' cube a := by
    intro q hq
    have hxJ : q.1 ∈ Icc l u := hq.1
    have hxI : q.1 ∈ Icc (0 : ℝ) a :=
      hJsub hxJ
    have hb := hbounds q.1 hxJ
    have hΦeq : Φ q.1 = φ q.1 :=
      extendIcc_eq a φ hxI
    have hΨeq : Ψ q.1 = ψ q.1 :=
      extendIcc_eq a ψ hxI
    have hdisk : normSq q.2 ≤ ε ^ 2 := hq.2
    have hyAbs : |q.2.1| ≤ ε := by
      rw [abs_le]
      unfold normSq at hdisk
      constructor <;>
        nlinarith [sq_nonneg q.2.2]
    have hzAbs : |q.2.2| ≤ ε := by
      rw [abs_le]
      unfold normSq at hdisk
      constructor <;>
        nlinarith [sq_nonneg q.2.1]
    change T q ∈ cube a
    change
      0 ≤ (T q).1 ∧ (T q).1 ≤ a ∧
        0 ≤ (T q).2.1 ∧ (T q).2.1 ≤ a ∧
        0 ≤ (T q).2.2 ∧ (T q).2.2 ≤ a
    simp only [T, shiftEquiv_apply]
    rw [hΦeq, hΨeq]
    exact
      ⟨hxI.1, hxI.2,
        by nlinarith [(abs_le.mp hyAbs).1],
        by nlinarith [(abs_le.mp hyAbs).2],
        by nlinarith [(abs_le.mp hzAbs).1],
        by nlinarith [(abs_le.mp hzAbs).2]⟩
  have hlocal :
      IntegrableOn
        (fun q : Point3 => radialKernel p q.2)
        (J ×ˢ disk ε) volume :=
    hshifted.mono_set hlocalSubset
  have hJvol :
      (volume : Measure ℝ) J ≠ 0 := by
    dsimp [J]
    rw [Real.volume_Icc]
    exact ENNReal.ofReal_ne_zero_iff.mpr (sub_pos.mpr hlu)
  have hJne :
      (volume : Measure ℝ).restrict J ≠ 0 :=
    mt Measure.restrict_eq_zero.mp hJvol
  have hrad :
      IntegrableOn (radialKernel p) (disk ε) volume := by
    rw [IntegrableOn, volume_point3,
      ← Measure.prod_restrict] at hlocal
    exact (Integrable.comp_snd_iff hJne).mp hlocal
  have hp' :=
    (radialKernel_integrableOn_disk_iff ε p hε).mp hrad
  linarith

private theorem originalProblem
    (f : Point3 → ℝ) (φ ψ : ℝ → ℝ) (a p m M : ℝ)
    (ha : 0 < a)
    (hf : Measurable f)
    (hφ : ContinuousOn φ (Icc (0 : ℝ) a))
    (hψ : ContinuousOn ψ (Icc (0 : ℝ) a))
    (hm : 0 < m) (hM : 0 < M)
    (hbound : ∀ q ∈ cube a, m ≤ |f q| ∧ |f q| ≤ M) :
    (p < 1 →
      IntegrableOn (integrand f φ ψ p) (cube a) MeasureTheory.volume) ∧
    (1 ≤ p ∧ curveMissesCube φ ψ a →
      IntegrableOn (integrand f φ ψ p) (cube a) MeasureTheory.volume) ∧
    (1 ≤ p ∧ curveEntersInterior φ ψ a →
      ¬ IntegrableOn (integrand f φ ψ p) (cube a) MeasureTheory.volume) := by
  constructor
  · intro hp
    apply integrand_integrable_of_model f φ ψ a p M hf
      (fun q hq => (hbound q hq).2)
    exact modelKernel_integrable_of_lt
      φ ψ a p ha hφ hψ hp
  constructor
  · rintro ⟨hp, hmiss⟩
    apply integrand_integrable_of_model f φ ψ a p M hf
      (fun q hq => (hbound q hq).2)
    exact modelKernel_integrable_of_miss
      φ ψ a p hp hφ hψ hmiss
  · rintro ⟨hp, henter⟩ hint
    have hmodel :
        IntegrableOn (modelKernel φ ψ p) (cube a) volume :=
      model_integrable_of_integrand f φ ψ a p m hm hf
        (fun q hq => (hbound q hq).1) hint
    exact
      (modelKernel_not_integrable_of_enter
        φ ψ a p ha hp hφ hψ henter) hmodel

private theorem singularRadiusSquared_pos
    (phi psi : ℝ → ℝ) (x y z : ℝ)
    (hnonsingular : y ≠ phi x ∨ z ≠ psi x) :
    0 < singularRadiusSquared phi psi x y z := by
  unfold singularRadiusSquared
  rcases hnonsingular with hy | hz
  · nlinarith [sq_pos_of_ne_zero (sub_ne_zero.mpr hy),
      sq_nonneg (z - psi x)]
  · nlinarith [sq_nonneg (y - phi x),
      sq_pos_of_ne_zero (sub_ne_zero.mpr hz)]

private theorem modelKernel_eq_modelWeight
    (phi psi : ℝ → ℝ) (p : ℝ) (w : Point3) :
    modelKernel phi psi p w = modelWeight phi psi p w := by
  rfl

private theorem modelWeight_nonneg
    (phi psi : ℝ → ℝ) (p : ℝ) (w : Point3) :
    0 ≤ modelWeight phi psi p w := by
  unfold modelWeight
  exact one_div_nonneg.mpr
    (Real.rpow_nonneg
      (by
        unfold singularRadiusSquared
        positivity)
      p)

theorem gap1 (f : ℝ × ℝ × ℝ → ℝ)
    (phi psi : ℝ → ℝ) (m p x y z : ℝ)
    (hnonsingular : y ≠ phi x ∨ z ≠ psi x)
    (hm : ∀ w, m ≤ |f w|) :
    m / Real.rpow (singularRadiusSquared phi psi x y z) p ≤
      |f (x, y, z)| /
        Real.rpow (singularRadiusSquared phi psi x y z) p := by
  exact div_le_div_of_nonneg_right
    (hm (x, y, z))
    (Real.rpow_pos_of_pos
      (singularRadiusSquared_pos
        phi psi x y z hnonsingular) p).le

theorem gap2 (f : ℝ × ℝ × ℝ → ℝ)
    (phi psi : ℝ → ℝ) (M p x y z : ℝ)
    (hnonsingular : y ≠ phi x ∨ z ≠ psi x)
    (hM : ∀ w, |f w| ≤ M) :
    |f (x, y, z)| /
        Real.rpow (singularRadiusSquared phi psi x y z) p ≤
      M / Real.rpow (singularRadiusSquared phi psi x y z) p := by
  exact div_le_div_of_nonneg_right
    (hM (x, y, z))
    (Real.rpow_pos_of_pos
      (singularRadiusSquared_pos
        phi psi x y z hnonsingular) p).le

theorem gap3 (f : ℝ × ℝ × ℝ → ℝ)
    (phi psi : ℝ → ℝ) (m M p x y z : ℝ)
    (hnonsingular : y ≠ phi x ∨ z ≠ psi x)
    (hm : ∀ w, m ≤ |f w|) (hM : ∀ w, |f w| ≤ M) :
    m / Real.rpow (singularRadiusSquared phi psi x y z) p ≤
      M / Real.rpow (singularRadiusSquared phi psi x y z) p :=
  (gap1 f phi psi m p x y z hnonsingular hm).trans
    (gap2 f phi psi M p x y z hnonsingular hM)

theorem gap4 (a : ℝ) (f : ℝ × ℝ × ℝ → ℝ)
    (phi psi : ℝ → ℝ) (m p : ℝ)
    (ha : 0 < a) (hp : p < 1) (hm0 : 0 < m)
    (hf : Measurable f) (hm : ∀ w, m ≤ |f w|)
    (habs : IntegrableOn
      (fun w =>
        |f w| / Real.rpow
          (singularRadiusSquared
            phi psi w.1 w.2.1 w.2.2) p)
      (cube a)) :
    m * modelIntegral a phi psi p ≤
      absoluteWeightedIntegral a f phi psi p := by
  have habsCore :
      IntegrableOn
        (integrand (fun w => |f w|) phi psi p)
        (cube a) volume := by
    simpa [integrand, weightedIntegrand] using habs
  have hmodelCore :
      IntegrableOn (modelKernel phi psi p) (cube a) volume :=
    model_integrable_of_integrand
      (fun w => |f w|) phi psi a p m hm0
      hf.norm (fun w hw => by simpa using hm w) habsCore
  have hmodel :
      IntegrableOn (modelWeight phi psi p) (cube a) volume := by
    apply hmodelCore.congr_fun
    · intro w hw
      exact modelKernel_eq_modelWeight phi psi p w
    · exact cube_measurable a
  have hleft :
      Integrable
        (fun w => m * modelWeight phi psi p w)
        (volume.restrict (cube a)) :=
    hmodel.const_mul m
  have hpoint :
      ∀ᵐ w ∂volume.restrict (cube a),
        m * modelWeight phi psi p w ≤
          |f w| / Real.rpow
            (singularRadiusSquared
              phi psi w.1 w.2.1 w.2.2) p := by
    filter_upwards with w
    have hbase :
        0 ≤ singularRadiusSquared
          phi psi w.1 w.2.1 w.2.2 := by
      unfold singularRadiusSquared
      positivity
    have hfactor :
        0 ≤
          (Real.rpow
            (singularRadiusSquared
              phi psi w.1 w.2.1 w.2.2) p)⁻¹ :=
      inv_nonneg.mpr (Real.rpow_nonneg hbase p)
    simpa only [modelWeight, div_eq_mul_inv, one_mul] using
      mul_le_mul_of_nonneg_right (hm w) hfactor
  have hmono := integral_mono_ae hleft habs hpoint
  unfold modelIntegral absoluteWeightedIntegral
  simpa only [integral_const_mul] using hmono

theorem gap5 (a : ℝ) (f : ℝ × ℝ × ℝ → ℝ)
    (phi psi : ℝ → ℝ) (M p : ℝ)
    (ha : 0 < a) (hp : p < 1)
    (hf : Measurable f) (hM : ∀ w, |f w| ≤ M)
    (hmodel : IntegrableOn
      (modelWeight phi psi p) (cube a)) :
    absoluteWeightedIntegral a f phi psi p ≤
      M * modelIntegral a phi psi p := by
  have hmodelCore :
      IntegrableOn (modelKernel phi psi p) (cube a) volume := by
    apply hmodel.congr_fun
    · intro w hw
      exact (modelKernel_eq_modelWeight phi psi p w).symm
    · exact cube_measurable a
  have habsCore :
      IntegrableOn
        (integrand (fun w => |f w|) phi psi p)
        (cube a) volume :=
    integrand_integrable_of_model
      (fun w => |f w|) phi psi a p M hf.norm
      (fun w hw => by simpa using hM w) hmodelCore
  have habs :
      IntegrableOn
        (fun w =>
          |f w| / Real.rpow
            (singularRadiusSquared
              phi psi w.1 w.2.1 w.2.2) p)
        (cube a) volume := by
    simpa [integrand, weightedIntegrand] using habsCore
  have hright :
      Integrable
        (fun w => M * modelWeight phi psi p w)
        (volume.restrict (cube a)) :=
    hmodel.const_mul M
  have hpoint :
      ∀ᵐ w ∂volume.restrict (cube a),
        |f w| / Real.rpow
            (singularRadiusSquared
              phi psi w.1 w.2.1 w.2.2) p ≤
          M * modelWeight phi psi p w := by
    filter_upwards with w
    have hbase :
        0 ≤ singularRadiusSquared
          phi psi w.1 w.2.1 w.2.2 := by
      unfold singularRadiusSquared
      positivity
    have hfactor :
        0 ≤
          (Real.rpow
            (singularRadiusSquared
              phi psi w.1 w.2.1 w.2.2) p)⁻¹ :=
      inv_nonneg.mpr (Real.rpow_nonneg hbase p)
    simpa only [modelWeight, div_eq_mul_inv, one_mul] using
      mul_le_mul_of_nonneg_right (hM w) hfactor
  have hmono := integral_mono_ae habs hright hpoint
  unfold absoluteWeightedIntegral modelIntegral
  simpa only [integral_const_mul] using hmono

theorem gap6 (a : ℝ) (f : ℝ × ℝ × ℝ → ℝ)
    (phi psi : ℝ → ℝ) (m M p : ℝ)
    (ha : 0 < a) (hp : p < 1) (hm0 : 0 < m)
    (hm : ∀ w, m ≤ |f w|) (hM : ∀ w, |f w| ≤ M) :
    m * modelIntegral a phi psi p ≤
      M * modelIntegral a phi psi p := by
  have hmM : m ≤ M :=
    (hm (0, 0, 0)).trans (hM (0, 0, 0))
  have hnonneg : 0 ≤ modelIntegral a phi psi p := by
    unfold modelIntegral
    exact integral_nonneg_of_ae
      (Filter.Eventually.of_forall fun w =>
        modelWeight_nonneg phi psi p w)
  exact mul_le_mul_of_nonneg_right hmM hnonneg

theorem gap7 :
    translationJacobian = 1 := by
  rfl

private theorem translatedRectangle_eq_prod
    (a : ℝ) (phi psi : ℝ → ℝ) (x : ℝ) :
    translatedRectangle a phi psi x =
      Set.Icc (-phi x) (a - phi x) ×ˢ
        Set.Icc (-psi x) (a - psi x) := by
  ext w
  simp only [translatedRectangle, Set.mem_setOf_eq,
    Set.mem_prod, Set.mem_Icc]
  tauto

private theorem radialKernel_integrableOn_translatedRectangle
    (a : ℝ) (phi psi : ℝ → ℝ) (p x : ℝ)
    (ha : 0 < a) (hp : p < 1) :
    IntegrableOn (radialKernel p)
      (translatedRectangle a phi psi x) volume := by
  let B : ℝ := a + |phi x| + |psi x|
  let R : ℝ := 2 * B
  have hB : 0 < B := by
    dsimp [B]
    positivity
  have hR : 0 < R := by
    dsimp [R]
    positivity
  have hdisk :
      IntegrableOn (radialKernel p) (disk R) volume :=
    (radialKernel_integrableOn_disk_iff R p hR).mpr hp
  apply hdisk.mono_set
  intro w hw
  rw [translatedRectangle_eq_prod] at hw
  have huAbs : |w.1| ≤ B := by
    rw [abs_le]
    have hphiB : phi x ≤ B := by
      dsimp [B]
      linarith [le_abs_self (phi x), abs_nonneg (psi x)]
    have hupper : a - phi x ≤ B := by
      dsimp [B]
      linarith [neg_le_abs (phi x), abs_nonneg (psi x)]
    exact ⟨(neg_le_neg hphiB).trans hw.1.1,
      hw.1.2.trans hupper⟩
  have hvAbs : |w.2| ≤ B := by
    rw [abs_le]
    have hpsiB : psi x ≤ B := by
      dsimp [B]
      linarith [le_abs_self (psi x), abs_nonneg (phi x)]
    have hupper : a - psi x ≤ B := by
      dsimp [B]
      linarith [neg_le_abs (psi x), abs_nonneg (phi x)]
    exact ⟨(neg_le_neg hpsiB).trans hw.2.1,
      hw.2.2.trans hupper⟩
  change w.1 ^ 2 + w.2 ^ 2 ≤ R ^ 2
  have huSq : w.1 ^ 2 ≤ B ^ 2 := by
    have hb := abs_le.mp huAbs
    nlinarith
      [mul_nonneg (sub_nonneg.mpr hb.2)
        (by linarith [hb.1] : 0 ≤ B + w.1)]
  have hvSq : w.2 ^ 2 ≤ B ^ 2 := by
    have hb := abs_le.mp hvAbs
    nlinarith
      [mul_nonneg (sub_nonneg.mpr hb.2)
        (by linarith [hb.1] : 0 ≤ B + w.2)]
  dsimp [R]
  nlinarith [sq_nonneg B]

private theorem iteratedIntegral_eq_set_prod_Icc
    (F : ℝ × ℝ → ℝ) (a b c d : ℝ)
    (hab : a ≤ b) (hcd : c ≤ d)
    (hF : IntegrableOn F
      (Set.Icc a b ×ˢ Set.Icc c d) volume) :
    (∫ x in a..b, ∫ y in c..d, F (x, y)) =
      ∫ w in Set.Icc a b ×ˢ Set.Icc c d, F w := by
  let G : ℝ × ℝ → ℝ :=
    (Set.Icc a b ×ˢ Set.Icc c d).indicator F
  have hGvol : Integrable G volume := by
    dsimp [G]
    exact
      (integrable_indicator_iff
        (measurableSet_Icc.prod measurableSet_Icc)).mpr hF
  have hGprod :
      Integrable G ((volume : Measure ℝ).prod volume) := by
    simpa only [← Measure.volume_eq_prod] using hGvol
  have hsections :
      (fun x : ℝ => ∫ y : ℝ, G (x, y)) =
        (Set.Icc a b).indicator
          (fun x => ∫ y in c..d, F (x, y)) := by
    funext x
    by_cases hx : x ∈ Set.Icc a b
    · rw [Set.indicator_of_mem hx]
      have hsection :
          (fun y : ℝ => G (x, y)) =
            (Set.Icc c d).indicator
              (fun y => F (x, y)) := by
        funext y
        by_cases hy : y ∈ Set.Icc c d
        · have hxy :
              (x, y) ∈ Set.Icc a b ×ˢ Set.Icc c d :=
            ⟨hx, hy⟩
          change
            (Set.Icc a b ×ˢ Set.Icc c d).indicator
                F (x, y) =
              (Set.Icc c d).indicator
                (fun y => F (x, y)) y
          rw [Set.indicator_of_mem hxy,
            Set.indicator_of_mem hy]
        · have hxy :
              (x, y) ∉ Set.Icc a b ×ˢ Set.Icc c d := by
            intro h
            exact hy h.2
          change
            (Set.Icc a b ×ˢ Set.Icc c d).indicator
                F (x, y) =
              (Set.Icc c d).indicator
                (fun y => F (x, y)) y
          rw [Set.indicator_of_notMem hxy,
            Set.indicator_of_notMem hy]
      rw [hsection, integral_indicator measurableSet_Icc,
        MeasureTheory.integral_Icc_eq_integral_Ioc,
        ← intervalIntegral.integral_of_le hcd]
    · rw [Set.indicator_of_notMem hx]
      have hzero :
          (fun y : ℝ => G (x, y)) =
            fun _ => (0 : ℝ) := by
        funext y
        apply Set.indicator_of_notMem
        intro h
        exact hx h.1
      rw [hzero]
      simp
  calc
    (∫ x in a..b, ∫ y in c..d, F (x, y)) =
        ∫ x in Set.Icc a b,
          ∫ y in c..d, F (x, y) := by
      rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
        ← intervalIntegral.integral_of_le hab]
    _ = ∫ x : ℝ,
          (Set.Icc a b).indicator
            (fun x => ∫ y in c..d, F (x, y)) x := by
      rw [integral_indicator measurableSet_Icc]
    _ = ∫ x : ℝ, ∫ y : ℝ, G (x, y) := by
      rw [← hsections]
    _ = ∫ w : ℝ × ℝ, G w := by
      rw [Measure.volume_eq_prod]
      exact (integral_prod G hGprod).symm
    _ = ∫ w in Set.Icc a b ×ˢ Set.Icc c d, F w := by
      dsimp [G]
      rw [integral_indicator
        (measurableSet_Icc.prod measurableSet_Icc)]

theorem gap8 (a : ℝ) (phi psi : ℝ → ℝ) (p x : ℝ)
    (ha : 0 < a) (hp : p < 1) :
    sliceIntegral a phi psi p x =
      ∫ w in translatedRectangle a phi psi x,
        1 / Real.rpow (w.1 ^ 2 + w.2 ^ 2) p := by
  have hrect :
      IntegrableOn (radialKernel p)
        (translatedRectangle a phi psi x) volume :=
    radialKernel_integrableOn_translatedRectangle
      a phi psi p x ha hp
  have hiter :
      (∫ u in -phi x..a - phi x,
          ∫ v in -psi x..a - psi x,
            radialKernel p (u, v)) =
        ∫ w in translatedRectangle a phi psi x,
          radialKernel p w := by
    rw [translatedRectangle_eq_prod] at hrect ⊢
    exact iteratedIntegral_eq_set_prod_Icc
      (radialKernel p)
      (-phi x) (a - phi x)
      (-psi x) (a - psi x)
      (by linarith) (by linarith) hrect
  change
    sliceIntegral a phi psi p x =
      ∫ w in translatedRectangle a phi psi x,
        radialKernel p w
  rw [← hiter]
  unfold sliceIntegral singularRadiusSquared
    radialKernel normSq
  calc
    (∫ y in (0 : ℝ)..a,
        ∫ z in (0 : ℝ)..a,
          1 / Real.rpow
            ((y - phi x) ^ 2 + (z - psi x) ^ 2) p) =
        ∫ y in (0 : ℝ)..a,
          ∫ v in -psi x..a - psi x,
            1 / Real.rpow
              ((y - phi x) ^ 2 + v ^ 2) p := by
      apply intervalIntegral.integral_congr
      intro y hy
      change
        (∫ z in (0 : ℝ)..a,
            1 / Real.rpow
              ((y - phi x) ^ 2 + (z - psi x) ^ 2) p) =
          ∫ v in -psi x..a - psi x,
            1 / Real.rpow
              ((y - phi x) ^ 2 + v ^ 2) p
      simpa only [zero_sub] using
        (intervalIntegral.integral_comp_sub_right
          (f := fun v : ℝ =>
            1 / Real.rpow
              ((y - phi x) ^ 2 + v ^ 2) p)
          (a := (0 : ℝ)) (b := a) (d := psi x))
    _ = ∫ u in -phi x..a - phi x,
          ∫ v in -psi x..a - psi x,
            1 / Real.rpow (u ^ 2 + v ^ 2) p := by
      simpa only [zero_sub] using
        (intervalIntegral.integral_comp_sub_right
          (f := fun u : ℝ =>
            ∫ v in -psi x..a - psi x,
              1 / Real.rpow (u ^ 2 + v ^ 2) p)
          (a := (0 : ℝ)) (b := a) (d := phi x))

private theorem radialKernel_setIntegral_pos_translatedRectangle
    (a : ℝ) (phi psi : ℝ → ℝ) (p x : ℝ)
    (ha : 0 < a) (hp : p < 1) :
    0 <
      ∫ w in translatedRectangle a phi psi x,
        radialKernel p w := by
  have hrect :
      IntegrableOn (radialKernel p)
        (translatedRectangle a phi psi x) volume :=
    radialKernel_integrableOn_translatedRectangle
      a phi psi p x ha hp
  apply
    (setIntegral_pos_iff_support_of_nonneg_ae
      (Filter.Eventually.of_forall fun w =>
        radialKernel_nonneg p w)
      hrect).2
  have hrectVol :
      0 < (volume : Measure Point2)
        (translatedRectangle a phi psi x) := by
    rw [translatedRectangle_eq_prod,
      Measure.volume_eq_prod, Measure.prod_prod,
      Real.volume_Icc, Real.volume_Icc]
    have hlen1 :
        a - phi x - -phi x = a := by ring
    have hlen2 :
        a - psi x - -psi x = a := by ring
    rw [hlen1, hlen2]
    exact ENNReal.mul_pos_iff.mpr
      ⟨ENNReal.ofReal_pos.mpr ha,
        ENNReal.ofReal_pos.mpr ha⟩
  have hsubset :
      translatedRectangle a phi psi x \ {(0, 0)} ⊆
        Function.support (radialKernel p) ∩
          translatedRectangle a phi psi x := by
    intro w hw
    have hwne : w ≠ (0, 0) := by
      simpa using hw.2
    have hcoord : w.1 ≠ 0 ∨ w.2 ≠ 0 := by
      by_contra h
      push_neg at h
      apply hwne
      ext <;> simp [h.1, h.2]
    have hnorm : 0 < normSq w := by
      unfold normSq
      rcases hcoord with h1 | h2
      · nlinarith [sq_pos_of_ne_zero h1, sq_nonneg w.2]
      · nlinarith [sq_nonneg w.1, sq_pos_of_ne_zero h2]
    have hvalue : radialKernel p w ≠ 0 := by
      unfold radialKernel
      exact one_div_ne_zero
        (Real.rpow_pos_of_pos hnorm p).ne'
    exact ⟨hvalue, hw.1⟩
  have hmono :
      (volume : Measure Point2)
          (translatedRectangle a phi psi x \ {(0, 0)}) ≤
        volume
          (Function.support (radialKernel p) ∩
            translatedRectangle a phi psi x) :=
    measure_mono hsubset
  rw [measure_diff_null (measure_singleton (0, 0))] at hmono
  exact hrectVol.trans_le hmono

theorem gap9 (a : ℝ) (phi psi : ℝ → ℝ) (p x : ℝ)
    (ha : 0 < a) (hp : p < 1) :
    0 < sliceIntegral a phi psi p x := by
  rw [gap8 a phi psi p x ha hp]
  exact
    radialKernel_setIntegral_pos_translatedRectangle
      a phi psi p x ha hp

theorem gap10 (a c : ℝ) (phi psi : ℝ → ℝ) (p x : ℝ)
    (ha : 0 < a) (hc : 0 ≤ c) (hp : p < 1)
    (hx : x ∈ Set.Icc (0 : ℝ) a)
    (hbound : ∀ t ∈ Set.Icc (0 : ℝ) a,
      |phi t| + |psi t| ≤ c) :
    sliceIntegral a phi psi p x ≤
      diskModelIntegral (Real.sqrt 2 * (a + c)) p := by
  let B : ℝ := a + c
  let R : ℝ := Real.sqrt 2 * B
  have hB : 0 < B := by
    dsimp [B]
    linarith
  have hR : 0 < R := by
    dsimp [R]
    positivity
  have hrad :
      IntegrableOn (radialKernel p) (disk R) volume :=
    (radialKernel_integrableOn_disk_iff R p hR).mpr hp
  have hsubset :
      translatedRectangle a phi psi x ⊆ disk R := by
    intro w hw
    rw [translatedRectangle_eq_prod] at hw
    have hsum := hbound x hx
    have hphi : |phi x| ≤ c := by
      linarith [abs_nonneg (psi x)]
    have hpsi : |psi x| ≤ c := by
      linarith [abs_nonneg (phi x)]
    have huAbs : |w.1| ≤ B := by
      rw [abs_le]
      have hphiB : phi x ≤ B := by
        dsimp [B]
        linarith [le_abs_self (phi x)]
      have hupper : a - phi x ≤ B := by
        dsimp [B]
        linarith [neg_le_abs (phi x)]
      exact ⟨(neg_le_neg hphiB).trans hw.1.1,
        hw.1.2.trans hupper⟩
    have hvAbs : |w.2| ≤ B := by
      rw [abs_le]
      have hpsiB : psi x ≤ B := by
        dsimp [B]
        linarith [le_abs_self (psi x)]
      have hupper : a - psi x ≤ B := by
        dsimp [B]
        linarith [neg_le_abs (psi x)]
      exact ⟨(neg_le_neg hpsiB).trans hw.2.1,
        hw.2.2.trans hupper⟩
    have huSq : w.1 ^ 2 ≤ B ^ 2 := by
      have hb := abs_le.mp huAbs
      nlinarith
        [mul_nonneg (sub_nonneg.mpr hb.2)
          (by linarith [hb.1] : 0 ≤ B + w.1)]
    have hvSq : w.2 ^ 2 ≤ B ^ 2 := by
      have hb := abs_le.mp hvAbs
      nlinarith
        [mul_nonneg (sub_nonneg.mpr hb.2)
          (by linarith [hb.1] : 0 ≤ B + w.2)]
    change w.1 ^ 2 + w.2 ^ 2 ≤ R ^ 2
    have hsqrt :
        (Real.sqrt 2) ^ 2 = (2 : ℝ) :=
      Real.sq_sqrt (by norm_num)
    dsimp [R]
    rw [mul_pow, hsqrt]
    nlinarith [sq_nonneg B]
  rw [gap8 a phi psi p x ha hp]
  change
    (∫ w in translatedRectangle a phi psi x,
        radialKernel p w) ≤
      ∫ w in disk R, radialKernel p w
  exact setIntegral_mono_set hrad
    (Filter.Eventually.of_forall fun w =>
      radialKernel_nonneg p w)
    (Filter.Eventually.of_forall hsubset)

private theorem diskModelIntegral_eq_polarRectangle
    (R p : ℝ) (hR : 0 < R) :
    diskModelIntegral R p =
      ∫ z in polarRectangle R, radialOrigin p z.1 := by
  change
    (∫ w in disk R, radialKernel p w) =
      ∫ z in polarRectangle R, radialOrigin p z.1
  calc
    (∫ w in disk R, radialKernel p w) =
        ∫ w : Point2, diskModel R p w := by
      unfold diskModel
      rw [integral_indicator (disk_measurable R)]
    _ = ∫ z in polarCoord.target,
          z.1 * diskModel R p (polarCoord.symm z) := by
      simpa only [smul_eq_mul] using
        (integral_comp_polarCoord_symm
          (diskModel R p)).symm
    _ = ∫ z in polarCoord.target,
          (polarRectangle R).indicator
            (fun z : Point2 => radialOrigin p z.1) z := by
      apply setIntegral_congr_fun
        polarCoord.open_target.measurableSet
      intro z hz
      exact polar_diskModel_eq R p hR hz
    _ = ∫ z in polarRectangle R, radialOrigin p z.1 := by
      rw [← integral_indicator
        polarCoord.open_target.measurableSet]
      have heq :
          polarCoord.target.indicator
              ((polarRectangle R).indicator
                (fun z : Point2 => radialOrigin p z.1)) =
            (polarRectangle R).indicator
              (fun z : Point2 => radialOrigin p z.1) := by
        funext z
        by_cases hz : z ∈ polarRectangle R
        · have ht : z ∈ polarCoord.target :=
            polarRectangle_subset_target R hz
          rw [indicator_of_mem ht, indicator_of_mem hz]
        · rw [indicator_of_notMem hz]
          by_cases ht : z ∈ polarCoord.target
          · rw [indicator_of_mem ht, indicator_of_notMem hz]
          · rw [indicator_of_notMem ht]
      rw [heq, integral_indicator
        (polarRectangle_measurable R)]

private theorem polarRectangle_integral_eq_interval
    (R p : ℝ) (hR : 0 < R) (hp : p < 1) :
    (∫ z in polarRectangle R, radialOrigin p z.1) =
      2 * Real.pi *
        ∫ r in (0 : ℝ)..R, Real.rpow r (1 - 2 * p) := by
  have hr :
      IntegrableOn (radialOrigin p) (Set.Ioc (0 : ℝ) R) volume :=
    (radialOrigin_integrableOn_iff p R hR).mpr hp
  have hangle :
      IntegrableOn (fun _ : ℝ => (1 : ℝ))
        (Set.Ioo (-Real.pi) Real.pi) volume :=
    integrableOn_const (C := (1 : ℝ))
      measure_Ioo_lt_top.ne
  have hprod :
      Integrable
        (fun z : Point2 => radialOrigin p z.1)
        ((volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) R) |>.prod
          ((volume : Measure ℝ).restrict
            (Set.Ioo (-Real.pi) Real.pi))) := by
    have hraw :=
      (show Integrable (radialOrigin p)
          ((volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) R))
        from hr).mul_prod
        (show Integrable (fun _ : ℝ => (1 : ℝ))
            ((volume : Measure ℝ).restrict
              (Set.Ioo (-Real.pi) Real.pi))
          from hangle)
    simpa only [mul_one] using hraw
  have hangleMeasure :
      (volume : Measure ℝ).real
          (Set.Ioo (-Real.pi) Real.pi) =
        2 * Real.pi := by
    rw [Real.volume_real_Ioo_of_le]
    · ring
    · linarith [Real.pi_pos]
  calc
    (∫ z in polarRectangle R, radialOrigin p z.1) =
        ∫ z : Point2, radialOrigin p z.1
          ∂((volume : Measure ℝ).restrict
              (Set.Ioc (0 : ℝ) R)).prod
            ((volume : Measure ℝ).restrict
              (Set.Ioo (-Real.pi) Real.pi)) := by
      rw [Measure.volume_eq_prod, polarRectangle,
        ← Measure.prod_restrict]
    _ = ∫ r in Set.Ioc (0 : ℝ) R,
          ∫ theta in Set.Ioo (-Real.pi) Real.pi,
            radialOrigin p r := by
      exact integral_prod _ hprod
    _ = ∫ r in Set.Ioc (0 : ℝ) R,
          (2 * Real.pi) * radialOrigin p r := by
      apply setIntegral_congr_fun measurableSet_Ioc
      intro r hrmem
      change
        (∫ theta in Set.Ioo (-Real.pi) Real.pi,
            radialOrigin p r) =
          (2 * Real.pi) * radialOrigin p r
      rw [setIntegral_const, smul_eq_mul,
        hangleMeasure]
    _ = 2 * Real.pi *
          ∫ r in Set.Ioc (0 : ℝ) R,
            radialOrigin p r := by
      rw [integral_const_mul]
    _ = 2 * Real.pi *
          ∫ r in Set.Ioc (0 : ℝ) R,
            Real.rpow r (1 - 2 * p) := by
      congr 1
      apply setIntegral_congr_fun measurableSet_Ioc
      intro r hrmem
      unfold radialOrigin
      calc
        r * Real.rpow r (-2 * p) =
            Real.rpow r 1 * Real.rpow r (-2 * p) := by
          congr 1
          exact (Real.rpow_one r).symm
        _ = Real.rpow r (1 + (-2 * p)) :=
          (Real.rpow_add hrmem.1 1 (-2 * p)).symm
        _ = Real.rpow r (1 - 2 * p) := by ring
    _ = 2 * Real.pi *
          ∫ r in (0 : ℝ)..R,
            Real.rpow r (1 - 2 * p) := by
      rw [intervalIntegral.integral_of_le hR.le]

theorem gap11 (a c p : ℝ)
    (ha : 0 < a) (hc : 0 ≤ c) (hp : p < 1) :
    diskModelIntegral (Real.sqrt 2 * (a + c)) p =
      Real.pi / (1 - p) *
        Real.rpow (Real.sqrt 2 * (a + c)) (2 - 2 * p) := by
  let R : ℝ := Real.sqrt 2 * (a + c)
  have hR : 0 < R := by
    dsimp [R]
    positivity
  rw [show Real.sqrt 2 * (a + c) = R by rfl]
  rw [diskModelIntegral_eq_polarRectangle R p hR,
    polarRectangle_integral_eq_interval R p hR hp]
  have hpow :
      (∫ r in (0 : ℝ)..R,
          Real.rpow r (1 - 2 * p)) =
        (Real.rpow R ((1 - 2 * p) + 1) -
          Real.rpow 0 ((1 - 2 * p) + 1)) /
            ((1 - 2 * p) + 1) := by
    change
      (∫ r in (0 : ℝ)..R, r ^ (1 - 2 * p)) =
        (R ^ ((1 - 2 * p) + 1) -
          (0 : ℝ) ^ ((1 - 2 * p) + 1)) /
            ((1 - 2 * p) + 1)
    exact integral_rpow (Or.inl (by linarith))
  rw [hpow]
  have hexponent :
      (1 - 2 * p) + 1 = 2 - 2 * p := by ring
  rw [hexponent]
  have hzero :
      Real.rpow 0 (2 - 2 * p) = 0 :=
    Real.zero_rpow (by linarith)
  rw [hzero, sub_zero]
  have hden1 : 1 - p ≠ 0 := by linarith
  have hden2 : 2 - 2 * p ≠ 0 := by linarith
  field_simp [hden1, hden2]

theorem gap12 (a c p : ℝ)
    (ha : 0 < a) (hc : 0 ≤ c) (hp : p < 1) :
    0 <
      Real.pi / (1 - p) *
        Real.rpow (Real.sqrt 2 * (a + c)) (2 - 2 * p) := by
  have hR :
      0 < Real.sqrt 2 * (a + c) := by
    positivity
  have hpi : 0 < Real.pi := Real.pi_pos
  have hden : 0 < 1 - p := by linarith
  have hpow :
      0 <
        Real.rpow (Real.sqrt 2 * (a + c)) (2 - 2 * p) :=
    Real.rpow_pos_of_pos hR _
  positivity

theorem gap13 (a : ℝ) (phi psi : ℝ → ℝ) (p : ℝ)
    (ha : 0 < a) (hp : p < 1)
    (hphi : ContinuousOn phi (Set.Icc (0 : ℝ) a))
    (hpsi : ContinuousOn psi (Set.Icc (0 : ℝ) a)) :
    IntervalIntegrable (sliceIntegral a phi psi p) volume 0 a := by
  have hmodelCore :
      IntegrableOn (modelKernel phi psi p) (cube a) volume :=
    modelKernel_integrable_of_lt
      phi psi a p ha hphi hpsi hp
  have hmodel :
      IntegrableOn (modelWeight phi psi p) (cube a) volume := by
    apply hmodelCore.congr_fun
    · intro w hw
      exact modelKernel_eq_modelWeight phi psi p w
    · exact cube_measurable a
  let G : Point3 → ℝ :=
    (cube a).indicator (modelWeight phi psi p)
  have hGvol : Integrable G volume := by
    dsimp [G]
    exact
      (integrable_indicator_iff (cube_measurable a)).mpr hmodel
  have hGprod :
      Integrable G
        ((volume : Measure ℝ).prod
          (volume : Measure Point2)) := by
    rw [← volume_point3]
    exact hGvol
  have hsections :
      ∀ᵐ x ∂(volume : Measure ℝ),
        Integrable (fun w : Point2 => G (x, w)) volume :=
    ((integrable_prod_iff hGprod.aestronglyMeasurable).mp hGprod).1
  have houter :
      Integrable
        (fun x : ℝ => ∫ w : Point2, G (x, w)) volume :=
    hGprod.integral_prod_left
  have heq :
      (fun x : ℝ => ∫ w : Point2, G (x, w)) =ᵐ[volume]
        (Set.Icc (0 : ℝ) a).indicator
          (sliceIntegral a phi psi p) := by
    filter_upwards [hsections] with x hxint
    by_cases hx : x ∈ Set.Icc (0 : ℝ) a
    · rw [Set.indicator_of_mem hx]
      let F : Point2 → ℝ :=
        fun w => modelWeight phi psi p (x, w)
      have hsectionEq :
          (fun w : Point2 => G (x, w)) =
            (Set.Icc (0 : ℝ) a ×ˢ
              Set.Icc (0 : ℝ) a).indicator F := by
        funext w
        by_cases hw :
            w ∈ Set.Icc (0 : ℝ) a ×ˢ
              Set.Icc (0 : ℝ) a
        · have hxw : (x, w) ∈ cube a :=
            ⟨hx.1, hx.2, hw.1.1, hw.1.2,
              hw.2.1, hw.2.2⟩
          change
            (cube a).indicator
                (modelWeight phi psi p) (x, w) =
              (Set.Icc (0 : ℝ) a ×ˢ
                Set.Icc (0 : ℝ) a).indicator F w
          rw [Set.indicator_of_mem hxw,
            Set.indicator_of_mem hw]
        · have hxw : (x, w) ∉ cube a := by
            intro h
            exact hw
              ⟨⟨h.2.2.1, h.2.2.2.1⟩,
                ⟨h.2.2.2.2.1, h.2.2.2.2.2⟩⟩
          change
            (cube a).indicator
                (modelWeight phi psi p) (x, w) =
              (Set.Icc (0 : ℝ) a ×ˢ
                Set.Icc (0 : ℝ) a).indicator F w
          rw [Set.indicator_of_notMem hxw,
            Set.indicator_of_notMem hw]
      rw [hsectionEq] at hxint ⊢
      have hF :
          IntegrableOn F
            (Set.Icc (0 : ℝ) a ×ˢ
              Set.Icc (0 : ℝ) a) volume :=
        (integrable_indicator_iff
          (measurableSet_Icc.prod measurableSet_Icc)).mp hxint
      have hiter :=
        iteratedIntegral_eq_set_prod_Icc
          F 0 a 0 a ha.le ha.le hF
      rw [integral_indicator
        (measurableSet_Icc.prod measurableSet_Icc)]
      rw [← hiter]
      rfl
    · rw [Set.indicator_of_notMem hx]
      have hzero :
          (fun w : Point2 => G (x, w)) =
            fun _ => (0 : ℝ) := by
        funext w
        apply Set.indicator_of_notMem
        intro h
        exact hx ⟨h.1, h.2.1⟩
      rw [hzero]
      simp
  have hind :
      Integrable
        ((Set.Icc (0 : ℝ) a).indicator
          (sliceIntegral a phi psi p)) volume :=
    houter.congr heq
  have hon :
      IntegrableOn (sliceIntegral a phi psi p)
        (Set.Icc (0 : ℝ) a) volume :=
    (integrable_indicator_iff measurableSet_Icc).mp hind
  exact
    (intervalIntegrable_iff_integrableOn_Icc_of_le ha.le).mpr hon

private theorem curveMissesCube_of_curveAvoidsCube
    (a : ℝ) (phi psi : ℝ → ℝ)
    (havoid : curveAvoidsCube a phi psi) :
    curveMissesCube phi psi a := by
  intro x hx hhit
  rcases havoid x hx with hφlo | hφhi | hψlo | hψhi
  · linarith [hhit.1.1]
  · linarith [hhit.1.2]
  · linarith [hhit.2.1]
  · linarith [hhit.2.2]

private theorem curveEntersInterior_of_interiorCurvePoint
    (a : ℝ) (phi psi : ℝ → ℝ)
    (hinterior : interiorCurvePoint a phi psi) :
    curveEntersInterior phi psi a := by
  rcases hinterior with
    ⟨x, hx, hφ0, hφa, hψ0, hψa⟩
  exact ⟨x, hx, ⟨hφ0, hφa⟩, ⟨hψ0, hψa⟩⟩

theorem gap14 (a : ℝ) (phi psi : ℝ → ℝ) (p : ℝ)
    (ha : 0 < a) (hp : 1 ≤ p)
    (hphi : ContinuousOn phi (Set.Icc (0 : ℝ) a))
    (hpsi : ContinuousOn psi (Set.Icc (0 : ℝ) a))
    (havoid : curveAvoidsCube a phi psi) :
    IntegrableOn (modelWeight phi psi p) (cube a) := by
  have hcore :
      IntegrableOn (modelKernel phi psi p) (cube a) volume :=
    modelKernel_integrable_of_miss
      phi psi a p hp hphi hpsi
      (curveMissesCube_of_curveAvoidsCube
        a phi psi havoid)
  apply hcore.congr_fun
  · intro w hw
    exact modelKernel_eq_modelWeight phi psi p w
  · exact cube_measurable a

theorem gap15 (a : ℝ) (phi psi : ℝ → ℝ)
    (ha : 0 < a)
    (hphi : ContinuousOn phi (Set.Icc (0 : ℝ) a))
    (hpsi : ContinuousOn psi (Set.Icc (0 : ℝ) a))
    (hinterior : interiorCurvePoint a phi psi) :
    ∃ x₀ ∈ Set.Icc (0 : ℝ) a, ∃ epsilon > 0, ∃ delta > 0,
      ∀ x ∈ Set.Icc (0 : ℝ) a,
        |x - x₀| < delta →
        epsilon ≤ phi x ∧ phi x ≤ a - epsilon ∧
        epsilon ≤ psi x ∧ psi x ≤ a - epsilon := by
  rcases hinterior with
    ⟨x₀, hx₀, hφ0, hφa, hψ0, hψa⟩
  let d : ℝ :=
    min (min (phi x₀) (a - phi x₀))
      (min (psi x₀) (a - psi x₀))
  have hd : 0 < d := by
    dsimp [d]
    exact lt_min
      (lt_min hφ0 (by linarith))
      (lt_min hψ0 (by linarith))
  let epsilon : ℝ := d / 3
  have hepsilon : 0 < epsilon := by
    dsimp [epsilon]
    positivity
  have hdφlo : d ≤ phi x₀ :=
    (min_le_left _ _).trans (min_le_left _ _)
  have hdφhi : d ≤ a - phi x₀ :=
    (min_le_left _ _).trans (min_le_right _ _)
  have hdψlo : d ≤ psi x₀ :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hdψhi : d ≤ a - psi x₀ :=
    (min_le_right _ _).trans (min_le_right _ _)
  rcases
      (Metric.continuousWithinAt_iff.mp
        (hphi.continuousWithinAt hx₀))
        epsilon hepsilon with
    ⟨deltaPhi, hdeltaPhi, hphiClose⟩
  rcases
      (Metric.continuousWithinAt_iff.mp
        (hpsi.continuousWithinAt hx₀))
        epsilon hepsilon with
    ⟨deltaPsi, hdeltaPsi, hpsiClose⟩
  let delta : ℝ := min deltaPhi deltaPsi
  have hdelta : 0 < delta := by
    dsimp [delta]
    exact lt_min hdeltaPhi hdeltaPsi
  refine ⟨x₀, hx₀, epsilon, hepsilon,
    delta, hdelta, ?_⟩
  intro x hx hnear
  have hphiDiff :
      |phi x - phi x₀| < epsilon := by
    have hclose := hphiClose hx
      (show dist x x₀ < deltaPhi by
        rw [Real.dist_eq]
        exact hnear.trans_le (min_le_left _ _))
    simpa [Real.dist_eq] using hclose
  have hpsiDiff :
      |psi x - psi x₀| < epsilon := by
    have hclose := hpsiClose hx
      (show dist x x₀ < deltaPsi by
        rw [Real.dist_eq]
        exact hnear.trans_le (min_le_right _ _))
    simpa [Real.dist_eq] using hclose
  have hdeq : d = 3 * epsilon := by
    dsimp [epsilon]
    ring
  have hφbounds := abs_lt.mp hphiDiff
  have hψbounds := abs_lt.mp hpsiDiff
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor <;> nlinarith

theorem gap16 (epsilon p : ℝ)
    (hepsilon : 0 < epsilon) (hp : 1 ≤ p) :
    ¬ IntegrableOn
      (fun w : ℝ × ℝ =>
        1 / Real.rpow (w.1 ^ 2 + w.2 ^ 2) p)
      {w | w.1 ^ 2 + w.2 ^ 2 < epsilon ^ 2} := by
  intro hopen
  let R : ℝ := epsilon / 2
  have hR : 0 < R := by
    dsimp [R]
    positivity
  change
    IntegrableOn (radialKernel p)
      {w : Point2 | normSq w < epsilon ^ 2} volume at hopen
  have hsubset :
      disk R ⊆ {w : Point2 | normSq w < epsilon ^ 2} := by
    intro w hw
    change normSq w < epsilon ^ 2
    change w.1 ^ 2 + w.2 ^ 2 ≤ R ^ 2 at hw
    have hRsq : R ^ 2 < epsilon ^ 2 := by
      dsimp [R]
      nlinarith [sq_pos_of_pos hepsilon]
    exact hw.trans_lt hRsq
  have hclosed :
      IntegrableOn (radialKernel p) (disk R) volume :=
    hopen.mono_set hsubset
  have hp' :=
    (radialKernel_integrableOn_disk_iff R p hR).mp hclosed
  linarith

theorem gap17 (a : ℝ) (phi psi : ℝ → ℝ) (p : ℝ)
    (ha : 0 < a) (hp : 1 ≤ p)
    (hphi : ContinuousOn phi (Set.Icc (0 : ℝ) a))
    (hpsi : ContinuousOn psi (Set.Icc (0 : ℝ) a))
    (hinterior : interiorCurvePoint a phi psi) :
    ¬ IntegrableOn (modelWeight phi psi p) (cube a) := by
  intro hmodel
  have hcore :
      IntegrableOn (modelKernel phi psi p) (cube a) volume := by
    apply hmodel.congr_fun
    · intro w hw
      exact (modelKernel_eq_modelWeight phi psi p w).symm
    · exact cube_measurable a
  exact
    (modelKernel_not_integrable_of_enter
      phi psi a p ha hp hphi hpsi
      (curveEntersInterior_of_interiorCurvePoint
        a phi psi hinterior)) hcore

theorem gap18 (a : ℝ) (f : ℝ × ℝ × ℝ → ℝ)
    (phi psi : ℝ → ℝ) (m M p : ℝ)
    (ha : 0 < a) (hm0 : 0 < m)
    (hf : Measurable f)
    (hm : ∀ w, m ≤ |f w|) (hM : ∀ w, |f w| ≤ M)
    (hphi : ContinuousOn phi (Set.Icc (0 : ℝ) a))
    (hpsi : ContinuousOn psi (Set.Icc (0 : ℝ) a)) :
    (p < 1 →
      IntegrableOn (weightedIntegrand f phi psi p) (cube a)) ∧
    (1 ≤ p → curveAvoidsCube a phi psi →
      IntegrableOn (weightedIntegrand f phi psi p) (cube a)) ∧
    (1 ≤ p → interiorCurvePoint a phi psi →
      ¬ IntegrableOn (weightedIntegrand f phi psi p) (cube a)) := by
  constructor
  · intro hp
    apply integrand_integrable_of_model
      f phi psi a p M hf (fun w hw => hM w)
    exact modelKernel_integrable_of_lt
      phi psi a p ha hphi hpsi hp
  constructor
  · intro hp havoid
    apply integrand_integrable_of_model
      f phi psi a p M hf (fun w hw => hM w)
    exact modelKernel_integrable_of_miss
      phi psi a p hp hphi hpsi
      (curveMissesCube_of_curveAvoidsCube
        a phi psi havoid)
  · intro hp hinterior hint
    have hcore :
        IntegrableOn (modelKernel phi psi p) (cube a) volume :=
      model_integrable_of_integrand
        f phi psi a p m hm0 hf
        (fun w hw => hm w) hint
    exact
      (modelKernel_not_integrable_of_enter
        phi psi a p ha hp hphi hpsi
        (curveEntersInterior_of_interiorCurvePoint
          a phi psi hinterior)) hcore

end

end ProofGap.Exercise4194
