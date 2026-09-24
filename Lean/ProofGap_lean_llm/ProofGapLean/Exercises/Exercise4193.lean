import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Integral.Prod

namespace ProofGap.Exercise4193

noncomputable section

/- Internal change-of-variables and symmetry lemmas. -/

open MeasureTheory Set
open scoped ENNReal

private theorem lintegral_comp_rpow_Ioi_of_pos
    (g : ℝ → ℝ≥0∞) {a : ℝ} (ha : 0 < a) :
    (∫⁻ x in Ioi (0 : ℝ),
      ENNReal.ofReal (a * Real.rpow x (a - 1)) * g (Real.rpow x a)) =
      ∫⁻ y in Ioi (0 : ℝ), g y := by
  have hderiv :
      ∀ x ∈ Ioi (0 : ℝ),
        HasDerivWithinAt (fun t : ℝ => Real.rpow t a)
          (a * Real.rpow x (a - 1)) (Ioi (0 : ℝ)) x := by
    intro x hx
    exact
      (Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt hx))).hasDerivWithinAt
  have hinj :
      Set.InjOn (fun x : ℝ => Real.rpow x a) (Ioi (0 : ℝ)) := by
    exact StrictMonoOn.injOn fun x hx y _ hxy =>
      Real.rpow_lt_rpow hx.le hxy ha
  have himage :
      (fun x : ℝ => Real.rpow x a) '' Ioi (0 : ℝ) =
        Ioi (0 : ℝ) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact Real.rpow_pos_of_pos hx a
    · intro hy
      refine ⟨Real.rpow y (1 / a), Real.rpow_pos_of_pos hy _, ?_⟩
      change Real.rpow (Real.rpow y (1 / a)) a = y
      calc
        Real.rpow (Real.rpow y (1 / a)) a =
            Real.rpow y ((1 / a) * a) :=
          (Real.rpow_mul hy.le (1 / a) a).symm
        _ = y := by
          rw [one_div_mul_cancel ha.ne']
          exact Real.rpow_one y
  calc
    (∫⁻ x in Ioi (0 : ℝ),
        ENNReal.ofReal (a * Real.rpow x (a - 1)) *
          g (Real.rpow x a)) =
        ∫⁻ x in Ioi (0 : ℝ),
          ENNReal.ofReal |a * Real.rpow x (a - 1)| *
            g (Real.rpow x a) := by
      apply setLIntegral_congr_fun measurableSet_Ioi
      intro x hx
      dsimp only
      rw [abs_of_pos]
      exact mul_pos ha (Real.rpow_pos_of_pos hx _)
    _ = ∫⁻ y in
          (fun x : ℝ => Real.rpow x a) '' Ioi (0 : ℝ), g y :=
      (MeasureTheory.lintegral_image_eq_lintegral_abs_deriv_mul
        measurableSet_Ioi hderiv hinj g).symm
    _ = ∫⁻ y in Ioi (0 : ℝ), g y := by rw [himage]

private abbrev Point3 := ℝ × ℝ × ℝ

private def positiveOctant : Set Point3 :=
  Ioi (0 : ℝ) ×ˢ (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ))

private theorem setLIntegral_positiveOctant
    (F : Point3 → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ z in positiveOctant, F z) =
      ∫⁻ x in Ioi (0 : ℝ),
        ∫⁻ y in Ioi (0 : ℝ),
          ∫⁻ z in Ioi (0 : ℝ), F (x, y, z) := by
  unfold positiveOctant
  rw [Measure.volume_eq_prod]
  rw [MeasureTheory.setLIntegral_prod F
    (hF.aemeasurable.restrict)]
  apply setLIntegral_congr_fun measurableSet_Ioi
  intro x hx
  dsimp only
  rw [Measure.volume_eq_prod]
  rw [MeasureTheory.setLIntegral_prod
    (fun yz : ℝ × ℝ => F (x, yz.1, yz.2))
    ((hF.comp (by fun_prop)).aemeasurable.restrict)]

private theorem setLIntegral_positiveOctant_rpow
    (F : Point3 → ℝ≥0∞) (hF : Measurable F)
    {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (∫⁻ z in positiveOctant, F z) =
      ∫⁻ u in Ioi (0 : ℝ),
        ENNReal.ofReal (a * Real.rpow u (a - 1)) *
          ∫⁻ v in Ioi (0 : ℝ),
            ENNReal.ofReal (b * Real.rpow v (b - 1)) *
              ∫⁻ w in Ioi (0 : ℝ),
              ENNReal.ofReal (c * Real.rpow w (c - 1)) *
              F (Real.rpow u a, Real.rpow v b, Real.rpow w c) := by
  rw [setLIntegral_positiveOctant F hF]
  calc
    (∫⁻ x in Ioi (0 : ℝ),
        ∫⁻ y in Ioi (0 : ℝ),
          ∫⁻ z in Ioi (0 : ℝ), F (x, y, z)) =
        ∫⁻ u in Ioi (0 : ℝ),
          ENNReal.ofReal (a * Real.rpow u (a - 1)) *
            ∫⁻ y in Ioi (0 : ℝ),
              ∫⁻ z in Ioi (0 : ℝ),
                F (Real.rpow u a, y, z) :=
      (lintegral_comp_rpow_Ioi_of_pos
        (g := fun x =>
          ∫⁻ y in Ioi (0 : ℝ),
            ∫⁻ z in Ioi (0 : ℝ), F (x, y, z)) ha).symm
    _ = ∫⁻ u in Ioi (0 : ℝ),
          ENNReal.ofReal (a * Real.rpow u (a - 1)) *
            ∫⁻ v in Ioi (0 : ℝ),
              ENNReal.ofReal (b * Real.rpow v (b - 1)) *
                ∫⁻ z in Ioi (0 : ℝ),
                  F (Real.rpow u a, Real.rpow v b, z) := by
      apply setLIntegral_congr_fun measurableSet_Ioi
      intro u hu
      dsimp only
      rw [← lintegral_comp_rpow_Ioi_of_pos
        (g := fun y =>
          ∫⁻ z in Ioi (0 : ℝ), F (Real.rpow u a, y, z)) hb]
    _ = ∫⁻ u in Ioi (0 : ℝ),
          ENNReal.ofReal (a * Real.rpow u (a - 1)) *
            ∫⁻ v in Ioi (0 : ℝ),
              ENNReal.ofReal (b * Real.rpow v (b - 1)) *
                ∫⁻ w in Ioi (0 : ℝ),
                  ENNReal.ofReal (c * Real.rpow w (c - 1)) *
                    F (Real.rpow u a, Real.rpow v b,
                      Real.rpow w c) := by
      apply setLIntegral_congr_fun measurableSet_Ioi
      intro u hu
      dsimp only
      congr 1
      apply setLIntegral_congr_fun measurableSet_Ioi
      intro v hv
      dsimp only
      rw [← lintegral_comp_rpow_Ioi_of_pos
        (g := fun z =>
          F (Real.rpow u a, Real.rpow v b, z)) hc]

private def positiveQuadrant : Set (ℝ × ℝ) :=
  Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)

private theorem polar_target_preimage_positiveQuadrant :
    {p : ℝ × ℝ |
        p ∈ polarCoord.target ∧
          (polarCoord.symm p : ℝ × ℝ) ∈ positiveQuadrant} =
      Ioi (0 : ℝ) ×ˢ Ioo (0 : ℝ) (Real.pi / 2) := by
  rw [polarCoord_target]
  ext p
  simp only [mem_setOf_eq, mem_prod, mem_Ioi, mem_Ioo,
    positiveQuadrant, polarCoord_symm_apply]
  constructor
  · rintro ⟨⟨hr, htheta⟩, hxy⟩
    have hcos : 0 < Real.cos p.2 := by
      rcases mul_pos_iff.mp hxy.1 with h | h
      · exact h.2
      · exact (not_lt_of_ge hr.le h.1).elim
    have hsin : 0 < Real.sin p.2 := by
      rcases mul_pos_iff.mp hxy.2 with h | h
      · exact h.2
      · exact (not_lt_of_ge hr.le h.1).elim
    have htheta0 : 0 < p.2 := by
      by_contra h
      exact (not_lt_of_ge
        (Real.sin_nonpos_of_nonpos_of_neg_pi_le
          (not_lt.mp h) htheta.1.le)) hsin
    have htheta1 : p.2 < Real.pi / 2 := by
      by_contra h
      exact (not_lt_of_ge
        (Real.cos_nonpos_of_pi_div_two_le_of_le
          (not_lt.mp h) (by linarith [htheta.2, Real.pi_pos]))) hcos
    exact ⟨hr, htheta0, htheta1⟩
  · rintro ⟨hr, htheta0, htheta1⟩
    have hpi : p.2 < Real.pi := by
      linarith [htheta1, Real.pi_pos]
    have hnegpi : -Real.pi < p.2 := by
      linarith [htheta0, Real.pi_pos]
    have hcos : 0 < Real.cos p.2 :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], htheta1⟩
    have hsin : 0 < Real.sin p.2 :=
      Real.sin_pos_of_pos_of_lt_pi htheta0 hpi
    exact ⟨⟨hr, hnegpi, hpi⟩, mul_pos hr hcos, mul_pos hr hsin⟩

private theorem setLIntegral_positiveQuadrant_polar
    (F : ℝ × ℝ → ℝ≥0∞) :
    (∫⁻ z in positiveQuadrant, F z) =
      ∫⁻ p in Ioi (0 : ℝ) ×ˢ Ioo (0 : ℝ) (Real.pi / 2),
        ENNReal.ofReal p.1 *
          F (p.1 * Real.cos p.2, p.1 * Real.sin p.2) := by
  have hQ : MeasurableSet positiveQuadrant :=
    measurableSet_Ioi.prod measurableSet_Ioi
  have hD :
      MeasurableSet
        (Ioi (0 : ℝ) ×ˢ Ioo (0 : ℝ) (Real.pi / 2)) :=
    measurableSet_Ioi.prod measurableSet_Ioo
  have hT : MeasurableSet polarCoord.target := by
    rw [polarCoord_target]
    exact measurableSet_Ioi.prod measurableSet_Ioo
  calc
    (∫⁻ z in positiveQuadrant, F z) =
        ∫⁻ z, positiveQuadrant.indicator F z :=
      (lintegral_indicator hQ F).symm
    _ = ∫⁻ p in polarCoord.target,
          ENNReal.ofReal p.1 *
            positiveQuadrant.indicator F (polarCoord.symm p) :=
      (lintegral_comp_polarCoord_symm
        (positiveQuadrant.indicator F)).symm
    _ = ∫⁻ p in Ioi (0 : ℝ) ×ˢ
          Ioo (0 : ℝ) (Real.pi / 2),
          ENNReal.ofReal p.1 *
            F (p.1 * Real.cos p.2,
              p.1 * Real.sin p.2) := by
      rw [← lintegral_indicator hT, ← lintegral_indicator hD]
      apply lintegral_congr
      intro p
      by_cases hpT : p ∈ polarCoord.target
      · by_cases hpQ :
          (polarCoord.symm p : ℝ × ℝ) ∈ positiveQuadrant
        · have hpD :
              p ∈ Ioi (0 : ℝ) ×ˢ
                Ioo (0 : ℝ) (Real.pi / 2) := by
            have :
                p ∈ {p : ℝ × ℝ |
                  p ∈ polarCoord.target ∧
                    (polarCoord.symm p : ℝ × ℝ) ∈
                      positiveQuadrant} :=
              ⟨hpT, hpQ⟩
            rwa [polar_target_preimage_positiveQuadrant] at this
          rw [indicator_of_mem hpT, indicator_of_mem hpQ,
            indicator_of_mem hpD, polarCoord_symm_apply]
        · have hpD :
              p ∉ Ioi (0 : ℝ) ×ˢ
                Ioo (0 : ℝ) (Real.pi / 2) := by
            intro h
            have :
                p ∈ {p : ℝ × ℝ |
                  p ∈ polarCoord.target ∧
                    (polarCoord.symm p : ℝ × ℝ) ∈
                      positiveQuadrant} := by
              rwa [polar_target_preimage_positiveQuadrant]
            exact hpQ this.2
          rw [indicator_of_mem hpT, indicator_of_notMem hpQ,
            indicator_of_notMem hpD, mul_zero]
      · have hpD :
            p ∉ Ioi (0 : ℝ) ×ˢ
              Ioo (0 : ℝ) (Real.pi / 2) := by
          intro h
          have hsub :
              Ioi (0 : ℝ) ×ˢ Ioo (0 : ℝ) (Real.pi / 2) ⊆
                polarCoord.target := by
            rw [polarCoord_target]
            rintro x ⟨hx, htheta⟩
            exact ⟨hx, by
              constructor <;> linarith [htheta.1, htheta.2,
                Real.pi_pos]⟩
          exact hpT (hsub h)
        rw [indicator_of_notMem hpT, indicator_of_notMem hpD]

private theorem setLIntegral_positiveOctant_rpow'
    (F : Point3 → ℝ≥0∞) (hF : Measurable F)
    {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (∫⁻ z in positiveOctant, F z) =
      ∫⁻ u in positiveOctant,
        ENNReal.ofReal (a * Real.rpow u.1 (a - 1)) *
          ENNReal.ofReal (b * Real.rpow u.2.1 (b - 1)) *
          ENNReal.ofReal (c * Real.rpow u.2.2 (c - 1)) *
          F (Real.rpow u.1 a, Real.rpow u.2.1 b,
            Real.rpow u.2.2 c) := by
  let G : Point3 → ℝ≥0∞ := fun u =>
    ENNReal.ofReal (a * Real.rpow u.1 (a - 1)) *
      ENNReal.ofReal (b * Real.rpow u.2.1 (b - 1)) *
      ENNReal.ofReal (c * Real.rpow u.2.2 (c - 1)) *
      F (Real.rpow u.1 a, Real.rpow u.2.1 b,
        Real.rpow u.2.2 c)
  have hG : Measurable G := by
    dsimp [G]
    fun_prop
  rw [setLIntegral_positiveOctant_rpow F hF ha hb hc]
  rw [setLIntegral_positiveOctant G hG]
  apply setLIntegral_congr_fun measurableSet_Ioi
  intro u hu
  dsimp [G]
  let A : ℝ≥0∞ :=
    ENNReal.ofReal (a * Real.rpow u (a - 1))
  calc
    A * ∫⁻ v in Ioi (0 : ℝ),
        ENNReal.ofReal (b * Real.rpow v (b - 1)) *
          ∫⁻ w in Ioi (0 : ℝ),
            ENNReal.ofReal (c * Real.rpow w (c - 1)) *
              F (Real.rpow u a, Real.rpow v b,
                Real.rpow w c) =
        ∫⁻ v in Ioi (0 : ℝ),
          A * (ENNReal.ofReal (b * Real.rpow v (b - 1)) *
            ∫⁻ w in Ioi (0 : ℝ),
              ENNReal.ofReal (c * Real.rpow w (c - 1)) *
                F (Real.rpow u a, Real.rpow v b,
                  Real.rpow w c)) :=
      (MeasureTheory.lintegral_const_mul' A _ (by finiteness)).symm
    _ = ∫⁻ v in Ioi (0 : ℝ),
          ∫⁻ w in Ioi (0 : ℝ),
            A *
              ENNReal.ofReal (b * Real.rpow v (b - 1)) *
              ENNReal.ofReal (c * Real.rpow w (c - 1)) *
              F (Real.rpow u a, Real.rpow v b,
                Real.rpow w c) := by
      apply setLIntegral_congr_fun measurableSet_Ioi
      intro v hv
      dsimp only
      let B : ℝ≥0∞ :=
        ENNReal.ofReal (b * Real.rpow v (b - 1))
      calc
        A * (B *
            ∫⁻ w in Ioi (0 : ℝ),
              ENNReal.ofReal (c * Real.rpow w (c - 1)) *
                F (Real.rpow u a, Real.rpow v b,
                  Real.rpow w c)) =
            (A * B) *
              ∫⁻ w in Ioi (0 : ℝ),
                ENNReal.ofReal (c * Real.rpow w (c - 1)) *
                  F (Real.rpow u a, Real.rpow v b,
                    Real.rpow w c) := by ring
        _ = ∫⁻ w in Ioi (0 : ℝ),
              (A * B) *
                (ENNReal.ofReal (c * Real.rpow w (c - 1)) *
                  F (Real.rpow u a, Real.rpow v b,
                    Real.rpow w c)) :=
          (MeasureTheory.lintegral_const_mul'
            (A * B)
            (fun w =>
              ENNReal.ofReal (c * Real.rpow w (c - 1)) *
                F (Real.rpow u a, Real.rpow v b,
                  Real.rpow w c)) (by finiteness)).symm
        _ = ∫⁻ w in Ioi (0 : ℝ),
              A * B *
                ENNReal.ofReal (c * Real.rpow w (c - 1)) *
                F (Real.rpow u a, Real.rpow v b,
                  Real.rpow w c) := by
          apply setLIntegral_congr_fun measurableSet_Ioi
          intro w hw
          ring
    _ = ∫⁻ v in Ioi (0 : ℝ),
          ∫⁻ w in Ioi (0 : ℝ),
            ENNReal.ofReal (a * Real.rpow u (a - 1)) *
              ENNReal.ofReal (b * Real.rpow v (b - 1)) *
              ENNReal.ofReal (c * Real.rpow w (c - 1)) *
              F (Real.rpow u a, Real.rpow v b,
                Real.rpow w c) := by rfl

private theorem prodAssoc_image_positive :
    MeasurableEquiv.prodAssoc ''
        (positiveQuadrant ×ˢ Ioi (0 : ℝ)) =
      positiveOctant := by
  ext z
  constructor
  · rintro ⟨⟨⟨u, v⟩, w⟩, huv, rfl⟩
    exact ⟨huv.1.1, huv.1.2, huv.2⟩
  · rintro ⟨hu, hv, hw⟩
    exact ⟨((z.1, z.2.1), z.2.2),
      ⟨⟨hu, hv⟩, hw⟩, rfl⟩

private theorem setLIntegral_positiveOctant_assoc
    (F : Point3 → ℝ≥0∞) :
    (∫⁻ z in positiveOctant, F z) =
      ∫⁻ z in positiveQuadrant ×ˢ Ioi (0 : ℝ),
        F (z.1.1, z.1.2, z.2) := by
  symm
  rw [← prodAssoc_image_positive]
  exact MeasureTheory.volume_preserving_prodAssoc.setLIntegral_comp_emb
    MeasurableEquiv.prodAssoc.measurableEmbedding F
    (positiveQuadrant ×ˢ Ioi (0 : ℝ))

private theorem setLIntegral_prod_mul_ennreal
    {s t : Set ℝ} (f g : ℝ → ℝ≥0∞)
    (hf : Measurable f) (hg : Measurable g) :
    (∫⁻ z in s ×ˢ t, f z.1 * g z.2) =
      (∫⁻ x in s, f x) * ∫⁻ y in t, g y := by
  rw [Measure.volume_eq_prod]
  rw [← Measure.prod_restrict]
  exact MeasureTheory.lintegral_prod_mul
    hf.aemeasurable.restrict hg.aemeasurable.restrict

private noncomputable def angleKernel (a b theta : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.rpow (Real.cos theta) (a - 1)) *
    ENNReal.ofReal (Real.rpow (Real.sin theta) (b - 1))

private noncomputable def angleLIntegral (a b : ℝ) : ℝ≥0∞ :=
  ∫⁻ theta in Ioo (0 : ℝ) (Real.pi / 2),
    angleKernel a b theta

private theorem measurable_real_rpow_const (s : ℝ) :
    Measurable (fun x : ℝ => Real.rpow x s) := by
  apply measurable_of_continuousOn_compl_singleton (0 : ℝ)
  exact continuousOn_of_forall_continuousAt fun x hx =>
    Real.continuousAt_rpow_const x s (Or.inl hx)

private theorem measurable_angleKernel (a b : ℝ) :
    Measurable (angleKernel a b) := by
  unfold angleKernel
  exact
    (ENNReal.measurable_ofReal.comp
      ((measurable_real_rpow_const (a - 1)).comp
        Real.measurable_cos)).mul
      (ENNReal.measurable_ofReal.comp
        ((measurable_real_rpow_const (b - 1)).comp
          Real.measurable_sin))

private theorem quadrant_weighted_radial_lintegral
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (H : ℝ → ℝ≥0∞) (hH : Measurable H) :
    (∫⁻ z in positiveQuadrant,
        ENNReal.ofReal (Real.rpow z.1 (a - 1)) *
          ENNReal.ofReal (Real.rpow z.2 (b - 1)) *
          H (z.1 ^ 2 + z.2 ^ 2)) =
      angleLIntegral a b *
        ∫⁻ R in Ioi (0 : ℝ),
          ENNReal.ofReal (Real.rpow R (a + b - 1)) *
            H (R ^ 2) := by
  rw [setLIntegral_positiveQuadrant_polar]
  have hpoint :
      ∀ p ∈ Ioi (0 : ℝ) ×ˢ Ioo (0 : ℝ) (Real.pi / 2),
        ENNReal.ofReal p.1 *
            (ENNReal.ofReal
                (Real.rpow (p.1 * Real.cos p.2) (a - 1)) *
              ENNReal.ofReal
                (Real.rpow (p.1 * Real.sin p.2) (b - 1)) *
              H ((p.1 * Real.cos p.2) ^ 2 +
                (p.1 * Real.sin p.2) ^ 2)) =
          (ENNReal.ofReal (Real.rpow p.1 (a + b - 1)) *
              H (p.1 ^ 2)) *
            angleKernel a b p.2 := by
    intro p hp
    have hr : 0 < p.1 := hp.1
    have ht0 : 0 < p.2 := hp.2.1
    have ht1 : p.2 < Real.pi / 2 := hp.2.2
    have hcos : 0 < Real.cos p.2 :=
      Real.cos_pos_of_mem_Ioo
        ⟨by linarith [ht0, Real.pi_pos], ht1⟩
    have hsin : 0 < Real.sin p.2 :=
      Real.sin_pos_of_pos_of_lt_pi ht0
        (by linarith [ht1, Real.pi_pos])
    have hcosMul :
        Real.rpow (p.1 * Real.cos p.2) (a - 1) =
          Real.rpow p.1 (a - 1) *
            Real.rpow (Real.cos p.2) (a - 1) := by
      exact Real.mul_rpow hr.le hcos.le
    have hsinMul :
        Real.rpow (p.1 * Real.sin p.2) (b - 1) =
          Real.rpow p.1 (b - 1) *
            Real.rpow (Real.sin p.2) (b - 1) := by
      exact Real.mul_rpow hr.le hsin.le
    have hsquare :
        (p.1 * Real.cos p.2) ^ 2 +
            (p.1 * Real.sin p.2) ^ 2 =
          p.1 ^ 2 := by
      calc
        _ = p.1 ^ 2 *
            (Real.cos p.2 ^ 2 + Real.sin p.2 ^ 2) := by ring
        _ = p.1 ^ 2 := by
          rw [Real.cos_sq_add_sin_sq]
          ring
    have hrpow :
        p.1 * Real.rpow p.1 (a - 1) *
            Real.rpow p.1 (b - 1) =
          Real.rpow p.1 (a + b - 1) := by
      calc
        p.1 * Real.rpow p.1 (a - 1) *
              Real.rpow p.1 (b - 1) =
            Real.rpow p.1 1 *
                Real.rpow p.1 (a - 1) *
              Real.rpow p.1 (b - 1) := by
          exact congrArg
            (fun x : ℝ =>
              x * Real.rpow p.1 (a - 1) *
                Real.rpow p.1 (b - 1))
            (Real.rpow_one p.1).symm
        _ = Real.rpow p.1 (1 + (a - 1)) *
              Real.rpow p.1 (b - 1) := by
          exact congrArg
            (fun x : ℝ =>
              x * Real.rpow p.1 (b - 1))
            (Real.rpow_add hr 1 (a - 1)).symm
        _ = Real.rpow p.1
              ((1 + (a - 1)) + (b - 1)) := by
          exact
            (Real.rpow_add hr
              (1 + (a - 1)) (b - 1)).symm
        _ = Real.rpow p.1 (a + b - 1) := by
          congr 1
          ring
    have hradENN :
        ENNReal.ofReal p.1 *
              ENNReal.ofReal (Real.rpow p.1 (a - 1)) *
            ENNReal.ofReal (Real.rpow p.1 (b - 1)) =
          ENNReal.ofReal (Real.rpow p.1 (a + b - 1)) := by
      calc
        ENNReal.ofReal p.1 *
              ENNReal.ofReal (Real.rpow p.1 (a - 1)) *
            ENNReal.ofReal (Real.rpow p.1 (b - 1)) =
            ENNReal.ofReal
                (p.1 * Real.rpow p.1 (a - 1)) *
              ENNReal.ofReal (Real.rpow p.1 (b - 1)) := by
          rw [ENNReal.ofReal_mul hr.le]
        _ = ENNReal.ofReal
              ((p.1 * Real.rpow p.1 (a - 1)) *
                Real.rpow p.1 (b - 1)) := by
          exact (ENNReal.ofReal_mul
            (mul_nonneg hr.le
              (Real.rpow_nonneg hr.le _))).symm
        _ = ENNReal.ofReal
              (Real.rpow p.1 (a + b - 1)) := by
          exact congrArg ENNReal.ofReal hrpow
    have hcosENN :
        ENNReal.ofReal
            (Real.rpow p.1 (a - 1) *
              Real.rpow (Real.cos p.2) (a - 1)) =
          ENNReal.ofReal (Real.rpow p.1 (a - 1)) *
            ENNReal.ofReal
              (Real.rpow (Real.cos p.2) (a - 1)) :=
      ENNReal.ofReal_mul (Real.rpow_nonneg hr.le _)
    have hsinENN :
        ENNReal.ofReal
            (Real.rpow p.1 (b - 1) *
              Real.rpow (Real.sin p.2) (b - 1)) =
          ENNReal.ofReal (Real.rpow p.1 (b - 1)) *
            ENNReal.ofReal
              (Real.rpow (Real.sin p.2) (b - 1)) :=
      ENNReal.ofReal_mul (Real.rpow_nonneg hr.le _)
    rw [hcosMul, hsinMul, hsquare]
    unfold angleKernel
    rw [hcosENN, hsinENN]
    calc
      ENNReal.ofReal p.1 *
            (ENNReal.ofReal (Real.rpow p.1 (a - 1)) *
                  ENNReal.ofReal
                    (Real.rpow (Real.cos p.2) (a - 1)) *
                (ENNReal.ofReal (Real.rpow p.1 (b - 1)) *
                  ENNReal.ofReal
                    (Real.rpow (Real.sin p.2) (b - 1))) *
              H (p.1 ^ 2)) =
          (ENNReal.ofReal p.1 *
                ENNReal.ofReal (Real.rpow p.1 (a - 1)) *
              ENNReal.ofReal (Real.rpow p.1 (b - 1))) *
            H (p.1 ^ 2) *
            (ENNReal.ofReal
                (Real.rpow (Real.cos p.2) (a - 1)) *
              ENNReal.ofReal
                (Real.rpow (Real.sin p.2) (b - 1))) := by ring
      _ = ENNReal.ofReal (Real.rpow p.1 (a + b - 1)) *
            H (p.1 ^ 2) *
            (ENNReal.ofReal
                (Real.rpow (Real.cos p.2) (a - 1)) *
              ENNReal.ofReal
                (Real.rpow (Real.sin p.2) (b - 1))) := by
          rw [hradENN]
  calc
    (∫⁻ p in Ioi (0 : ℝ) ×ˢ Ioo (0 : ℝ) (Real.pi / 2),
        ENNReal.ofReal p.1 *
          (ENNReal.ofReal
              (Real.rpow (p.1 * Real.cos p.2) (a - 1)) *
            ENNReal.ofReal
              (Real.rpow (p.1 * Real.sin p.2) (b - 1)) *
            H ((p.1 * Real.cos p.2) ^ 2 +
              (p.1 * Real.sin p.2) ^ 2))) =
        ∫⁻ p in Ioi (0 : ℝ) ×ˢ Ioo (0 : ℝ) (Real.pi / 2),
          (ENNReal.ofReal (Real.rpow p.1 (a + b - 1)) *
              H (p.1 ^ 2)) *
            angleKernel a b p.2 := by
      exact setLIntegral_congr_fun
        (measurableSet_Ioi.prod measurableSet_Ioo) hpoint
    _ = (∫⁻ R in Ioi (0 : ℝ),
            ENNReal.ofReal (Real.rpow R (a + b - 1)) *
              H (R ^ 2)) *
          angleLIntegral a b := by
      exact setLIntegral_prod_mul_ennreal
        (fun R =>
          ENNReal.ofReal (Real.rpow R (a + b - 1)) *
            H (R ^ 2))
        (angleKernel a b)
        ((ENNReal.measurable_ofReal.comp
          (measurable_real_rpow_const (a + b - 1))).mul
          (hH.comp (measurable_id.pow_const 2)))
        (measurable_angleKernel a b)
    _ = angleLIntegral a b *
        ∫⁻ R in Ioi (0 : ℝ),
          ENNReal.ofReal (Real.rpow R (a + b - 1)) *
            H (R ^ 2) := by
      rw [mul_comm]

private theorem octant_weighted_radial_lintegral
    (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (habFinite : angleLIntegral a b ≠ ∞)
    (H : ℝ → ℝ≥0∞) (hH : Measurable H) :
    (∫⁻ z in positiveOctant,
        ENNReal.ofReal (Real.rpow z.1 (a - 1)) *
          ENNReal.ofReal (Real.rpow z.2.1 (b - 1)) *
          ENNReal.ofReal (Real.rpow z.2.2 (c - 1)) *
          H (z.1 ^ 2 + z.2.1 ^ 2 + z.2.2 ^ 2)) =
      angleLIntegral a b * angleLIntegral (a + b) c *
        ∫⁻ R in Ioi (0 : ℝ),
          ENNReal.ofReal
              (Real.rpow R (a + b + c - 1)) *
            H (R ^ 2) := by
  let K : Point3 → ℝ≥0∞ := fun z =>
    ENNReal.ofReal (Real.rpow z.1 (a - 1)) *
      ENNReal.ofReal (Real.rpow z.2.1 (b - 1)) *
      ENNReal.ofReal (Real.rpow z.2.2 (c - 1)) *
      H (z.1 ^ 2 + z.2.1 ^ 2 + z.2.2 ^ 2)
  have hK : Measurable K := by
    dsimp [K]
    exact
      (((ENNReal.measurable_ofReal.comp
          ((measurable_real_rpow_const (a - 1)).comp
            measurable_fst)).mul
        (ENNReal.measurable_ofReal.comp
          ((measurable_real_rpow_const (b - 1)).comp
            (measurable_fst.comp measurable_snd)))).mul
        (ENNReal.measurable_ofReal.comp
          ((measurable_real_rpow_const (c - 1)).comp
            (measurable_snd.comp measurable_snd)))).mul
        (hH.comp (by fun_prop))
  have hAssoc :
      Measurable
        (fun z : (ℝ × ℝ) × ℝ =>
          ((z.1.1, (z.1.2, z.2)) : Point3)) := by
    fun_prop
  rw [show
    (∫⁻ z in positiveOctant,
        ENNReal.ofReal (Real.rpow z.1 (a - 1)) *
          ENNReal.ofReal (Real.rpow z.2.1 (b - 1)) *
          ENNReal.ofReal (Real.rpow z.2.2 (c - 1)) *
          H (z.1 ^ 2 + z.2.1 ^ 2 + z.2.2 ^ 2)) =
      ∫⁻ z in positiveOctant, K z by rfl]
  rw [setLIntegral_positiveOctant_assoc K]
  rw [Measure.volume_eq_prod]
  rw [MeasureTheory.setLIntegral_prod_symm
    (fun z : (ℝ × ℝ) × ℝ =>
      K (z.1.1, z.1.2, z.2))
    ((hK.comp hAssoc).aemeasurable.restrict)]
  have hinner (w : ℝ) :
      (∫⁻ uv in positiveQuadrant,
          K (uv.1, uv.2, w)) =
        angleLIntegral a b *
          ∫⁻ rho in Ioi (0 : ℝ),
            ENNReal.ofReal
                (Real.rpow rho (a + b - 1)) *
              (ENNReal.ofReal (Real.rpow w (c - 1)) *
                H (rho ^ 2 + w ^ 2)) := by
    let Hw : ℝ → ℝ≥0∞ := fun s =>
      ENNReal.ofReal (Real.rpow w (c - 1)) *
        H (s + w ^ 2)
    have hHw : Measurable Hw :=
      measurable_const.mul
        (hH.comp (measurable_id.add_const _))
    calc
      (∫⁻ uv in positiveQuadrant,
          K (uv.1, uv.2, w)) =
          ∫⁻ uv in positiveQuadrant,
            ENNReal.ofReal (Real.rpow uv.1 (a - 1)) *
              ENNReal.ofReal (Real.rpow uv.2 (b - 1)) *
              Hw (uv.1 ^ 2 + uv.2 ^ 2) := by
        apply setLIntegral_congr_fun
          (measurableSet_Ioi.prod measurableSet_Ioi)
        intro uv huv
        dsimp [K, Hw]
        ring
      _ = angleLIntegral a b *
          ∫⁻ rho in Ioi (0 : ℝ),
            ENNReal.ofReal
                (Real.rpow rho (a + b - 1)) *
              Hw (rho ^ 2) :=
        quadrant_weighted_radial_lintegral
          a b ha hb Hw hHw
  let F₂ : ℝ × ℝ → ℝ≥0∞ := fun z =>
    ENNReal.ofReal
        (Real.rpow z.1 (a + b - 1)) *
      ENNReal.ofReal (Real.rpow z.2 (c - 1)) *
      H (z.1 ^ 2 + z.2 ^ 2)
  have hF₂ : Measurable F₂ := by
    dsimp [F₂]
    exact
      ((ENNReal.measurable_ofReal.comp
        ((measurable_real_rpow_const
          (a + b - 1)).comp measurable_fst)).mul
        (ENNReal.measurable_ofReal.comp
          ((measurable_real_rpow_const
            (c - 1)).comp measurable_snd))).mul
        (hH.comp (by fun_prop))
  have hpair :
      (∫⁻ w in Ioi (0 : ℝ),
          ∫⁻ rho in Ioi (0 : ℝ),
            ENNReal.ofReal
                (Real.rpow rho (a + b - 1)) *
              (ENNReal.ofReal (Real.rpow w (c - 1)) *
                H (rho ^ 2 + w ^ 2))) =
        ∫⁻ z in positiveQuadrant, F₂ z := by
    rw [Measure.volume_eq_prod]
    change
      (∫⁻ w in Ioi (0 : ℝ),
          ∫⁻ rho in Ioi (0 : ℝ),
            ENNReal.ofReal
                (Real.rpow rho (a + b - 1)) *
              (ENNReal.ofReal (Real.rpow w (c - 1)) *
                H (rho ^ 2 + w ^ 2))) =
        ∫⁻ z in Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ),
          F₂ z ∂volume.prod volume
    rw [MeasureTheory.setLIntegral_prod_symm F₂
      hF₂.aemeasurable.restrict]
    apply setLIntegral_congr_fun measurableSet_Ioi
    intro w hw
    apply setLIntegral_congr_fun measurableSet_Ioi
    intro rho hrho
    dsimp [F₂]
    ring
  calc
    (∫⁻ w in Ioi (0 : ℝ),
        ∫⁻ uv in positiveQuadrant,
          K (uv.1, uv.2, w)) =
        ∫⁻ w in Ioi (0 : ℝ),
          angleLIntegral a b *
            ∫⁻ rho in Ioi (0 : ℝ),
              ENNReal.ofReal
                  (Real.rpow rho (a + b - 1)) *
                (ENNReal.ofReal (Real.rpow w (c - 1)) *
                  H (rho ^ 2 + w ^ 2)) := by
      apply setLIntegral_congr_fun measurableSet_Ioi
      intro w hw
      exact hinner w
    _ = angleLIntegral a b *
        ∫⁻ w in Ioi (0 : ℝ),
          ∫⁻ rho in Ioi (0 : ℝ),
            ENNReal.ofReal
                (Real.rpow rho (a + b - 1)) *
              (ENNReal.ofReal (Real.rpow w (c - 1)) *
                H (rho ^ 2 + w ^ 2)) := by
      exact MeasureTheory.lintegral_const_mul'
        (angleLIntegral a b) _ habFinite
    _ = angleLIntegral a b *
        (∫⁻ z in positiveQuadrant,
          ENNReal.ofReal
              (Real.rpow z.1 (a + b - 1)) *
            ENNReal.ofReal (Real.rpow z.2 (c - 1)) *
            H (z.1 ^ 2 + z.2 ^ 2)) := by
      exact congrArg
        (fun x : ℝ≥0∞ => angleLIntegral a b * x) hpair
    _ = angleLIntegral a b *
        (angleLIntegral (a + b) c *
          ∫⁻ R in Ioi (0 : ℝ),
            ENNReal.ofReal
                (Real.rpow R ((a + b) + c - 1)) *
              H (R ^ 2)) := by
      rw [quadrant_weighted_radial_lintegral
        (a + b) c (add_pos ha hb) hc H hH]
    _ = angleLIntegral a b * angleLIntegral (a + b) c *
        ∫⁻ R in Ioi (0 : ℝ),
          ENNReal.ofReal
              (Real.rpow R (a + b + c - 1)) *
            H (R ^ 2) := by
      have hexp :
          (a + b) + c - 1 = a + b + c - 1 := by ring
      rw [hexp]
      ring

private noncomputable def betaFnLocal (x y : ℝ) : ℝ :=
  ∫ t in Ioc (0 : ℝ) 1,
    Real.rpow t (x - 1) * Real.rpow (1 - t) (y - 1)

private theorem betaKernel_intervalIntegrable
    (u v : ℝ) (hu : 0 < u) (hv : 0 < v) :
    IntervalIntegrable
      (fun t : ℝ =>
        Real.rpow t (u - 1) * Real.rpow (1 - t) (v - 1))
      volume 0 1 := by
  have huExp : -1 < u - 1 := by linarith
  have hvExp : -1 < v - 1 := by linarith
  have huPow :
      IntervalIntegrable (fun t : ℝ => Real.rpow t (u - 1))
        volume 0 (1 / 2 : ℝ) :=
    intervalIntegral.intervalIntegrable_rpow' huExp
  have hvAway :
      ContinuousOn (fun t : ℝ => Real.rpow (1 - t) (v - 1))
        (Set.uIcc (0 : ℝ) (1 / 2 : ℝ)) := by
    apply continuousOn_of_forall_continuousAt
    intro t ht
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1 / 2)] at ht
    exact
      (Real.continuousAt_rpow_const (1 - t) (v - 1)
        (Or.inl (by linarith [ht.2]))).comp
        (continuous_const.sub continuous_id).continuousAt
  have hleft :
      IntervalIntegrable
        (fun t : ℝ =>
          Real.rpow t (u - 1) * Real.rpow (1 - t) (v - 1))
        volume 0 (1 / 2 : ℝ) :=
    huPow.mul_continuousOn hvAway
  have hvPow :
      IntervalIntegrable (fun t : ℝ => Real.rpow t (v - 1))
        volume 0 (1 / 2 : ℝ) :=
    intervalIntegral.intervalIntegrable_rpow' hvExp
  have hvRight :
      IntervalIntegrable (fun t : ℝ => Real.rpow (1 - t) (v - 1))
        volume (1 / 2 : ℝ) 1 := by
    have h := (hvPow.comp_sub_left 1).symm
    convert h using 1 <;> norm_num
  have huAway :
      ContinuousOn (fun t : ℝ => Real.rpow t (u - 1))
        (Set.uIcc (1 / 2 : ℝ) 1) := by
    apply continuousOn_of_forall_continuousAt
    intro t ht
    rw [Set.uIcc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 1)] at ht
    exact Real.continuousAt_rpow_const t (u - 1)
      (Or.inl (by linarith [ht.1]))
  have hright :
      IntervalIntegrable
        (fun t : ℝ =>
          Real.rpow t (u - 1) * Real.rpow (1 - t) (v - 1))
        volume (1 / 2 : ℝ) 1 :=
    hvRight.continuousOn_mul huAway
  exact hleft.trans hright

private theorem trigBeta_kernel_eq
    (u v theta : ℝ)
    (htheta0 : 0 < theta) (htheta1 : theta < Real.pi / 2) :
    (2 * Real.sin theta * Real.cos theta) *
        (Real.rpow (Real.sin theta ^ 2) (u - 1) *
          Real.rpow (1 - Real.sin theta ^ 2) (v - 1)) =
      2 *
        (Real.rpow (Real.sin theta) (2 * u - 1) *
          Real.rpow (Real.cos theta) (2 * v - 1)) := by
  have hs : 0 < Real.sin theta :=
    Real.sin_pos_of_pos_of_lt_pi htheta0
      (htheta1.trans (half_lt_self Real.pi_pos))
  have hc : 0 < Real.cos theta :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], htheta1⟩
  have hone :
      1 - Real.sin theta ^ 2 = Real.cos theta ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq theta]
  have hsinPow :
      Real.rpow (Real.sin theta ^ 2) (u - 1) =
        Real.rpow (Real.sin theta) (2 * (u - 1)) := by
    exact (Real.rpow_natCast_mul hs.le 2 (u - 1)).symm
  have hcosPow :
      Real.rpow (Real.cos theta ^ 2) (v - 1) =
        Real.rpow (Real.cos theta) (2 * (v - 1)) := by
    exact (Real.rpow_natCast_mul hc.le 2 (v - 1)).symm
  have hsinCombine :
      Real.sin theta *
          Real.rpow (Real.sin theta) (2 * (u - 1)) =
        Real.rpow (Real.sin theta) (2 * u - 1) := by
    calc
      Real.sin theta *
          Real.rpow (Real.sin theta) (2 * (u - 1)) =
          Real.rpow (Real.sin theta) 1 *
            Real.rpow (Real.sin theta) (2 * (u - 1)) := by
              exact congrArg
                (fun t : ℝ =>
                  t * Real.rpow (Real.sin theta) (2 * (u - 1)))
                (Real.rpow_one (Real.sin theta)).symm
      _ = Real.rpow (Real.sin theta) (1 + 2 * (u - 1)) :=
        (Real.rpow_add hs 1 (2 * (u - 1))).symm
      _ = Real.rpow (Real.sin theta) (2 * u - 1) := by ring_nf
  have hcosCombine :
      Real.cos theta *
          Real.rpow (Real.cos theta) (2 * (v - 1)) =
        Real.rpow (Real.cos theta) (2 * v - 1) := by
    calc
      Real.cos theta *
          Real.rpow (Real.cos theta) (2 * (v - 1)) =
          Real.rpow (Real.cos theta) 1 *
            Real.rpow (Real.cos theta) (2 * (v - 1)) := by
              exact congrArg
                (fun t : ℝ =>
                  t * Real.rpow (Real.cos theta) (2 * (v - 1)))
                (Real.rpow_one (Real.cos theta)).symm
      _ = Real.rpow (Real.cos theta) (1 + 2 * (v - 1)) :=
        (Real.rpow_add hc 1 (2 * (v - 1))).symm
      _ = Real.rpow (Real.cos theta) (2 * v - 1) := by ring_nf
  rw [hsinPow, hone, hcosPow]
  calc
    (2 * Real.sin theta * Real.cos theta) *
        (Real.rpow (Real.sin theta) (2 * (u - 1)) *
          Real.rpow (Real.cos theta) (2 * (v - 1))) =
      2 *
        (Real.sin theta *
          Real.rpow (Real.sin theta) (2 * (u - 1))) *
        (Real.cos theta *
          Real.rpow (Real.cos theta) (2 * (v - 1))) := by ring
    _ = 2 *
        (Real.rpow (Real.sin theta) (2 * u - 1) *
          Real.rpow (Real.cos theta) (2 * v - 1)) := by
      rw [hsinCombine, hcosCombine]
      ring

private theorem trigBeta_integral
    (u v : ℝ) (hu : 0 < u) (hv : 0 < v) :
    (∫ theta in (0 : ℝ)..Real.pi / 2,
      Real.rpow (Real.sin theta) (2 * u - 1) *
        Real.rpow (Real.cos theta) (2 * v - 1)) =
      (1 / 2 : ℝ) *
        ∫ t in (0 : ℝ)..1,
          Real.rpow t (u - 1) *
            Real.rpow (1 - t) (v - 1) := by
  let f : ℝ → ℝ := fun theta => Real.sin theta ^ 2
  let f' : ℝ → ℝ :=
    fun theta => 2 * Real.sin theta * Real.cos theta
  let g : ℝ → ℝ :=
    fun t =>
      Real.rpow t (u - 1) * Real.rpow (1 - t) (v - 1)
  let h : ℝ → ℝ :=
    fun theta =>
      Real.rpow (Real.sin theta) (2 * u - 1) *
        Real.rpow (Real.cos theta) (2 * v - 1)
  have hpi : 0 ≤ Real.pi / 2 := by positivity
  have hfcont :
      ContinuousOn f (Set.Icc (0 : ℝ) (Real.pi / 2)) := by
    exact (Real.continuous_sin.pow 2).continuousOn
  have hfmono :
      MonotoneOn f (Set.Icc (0 : ℝ) (Real.pi / 2)) := by
    intro x hx y hy hxy
    have hx' : x ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) :=
      ⟨(neg_nonpos.mpr hpi).trans hx.1, hx.2⟩
    have hy' : y ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) :=
      ⟨(neg_nonpos.mpr hpi).trans hy.1, hy.2⟩
    have hsxy : Real.sin x ≤ Real.sin y :=
      Real.monotoneOn_sin hx' hy' hxy
    have hsx0 : 0 ≤ Real.sin x :=
      Real.sin_nonneg_of_nonneg_of_le_pi hx.1
        (hx.2.trans (half_le_self Real.pi_pos.le))
    have hsy0 : 0 ≤ Real.sin y :=
      Real.sin_nonneg_of_nonneg_of_le_pi hy.1
        (hy.2.trans (half_le_self Real.pi_pos.le))
    dsimp [f]
    nlinarith
  have hfimage :
      f '' Set.Icc (0 : ℝ) (Real.pi / 2) =
        Set.Icc (0 : ℝ) 1 := by
    apply Set.Subset.antisymm
    · simpa [f] using hfmono.image_Icc_subset
    · simpa [f] using intermediate_value_Icc hpi hfcont
  have hfder :
      ∀ theta ∈ Set.Icc (0 : ℝ) (Real.pi / 2),
        HasDerivWithinAt f (f' theta)
          (Set.Icc (0 : ℝ) (Real.pi / 2)) theta := by
    intro theta htheta
    have hd :=
      (Real.hasDerivAt_sin theta).mul
        (Real.hasDerivAt_sin theta)
    apply HasDerivAt.hasDerivWithinAt
    convert hd using 1
    · funext t
      simp [f, pow_two]
    · dsimp [f']
      ring
  have hchange :
      (∫ t in Set.Icc (0 : ℝ) 1, g t) =
        ∫ theta in Set.Icc (0 : ℝ) (Real.pi / 2),
          f' theta • g (f theta) := by
    have hc :=
      integral_image_eq_integral_deriv_smul_of_monotoneOn
        (f := f) (f' := f')
        measurableSet_Icc hfder hfmono g
    rw [hfimage] at hc
    exact hc
  have hkernelAE :
      (fun theta => f' theta • g (f theta)) =ᵐ[
        volume.restrict (Set.Icc (0 : ℝ) (Real.pi / 2))]
        (fun theta => 2 * h theta) := by
    filter_upwards
      [ae_restrict_mem measurableSet_Icc,
        ae_restrict_of_ae (Measure.ae_ne volume (0 : ℝ)),
        ae_restrict_of_ae
          (Measure.ae_ne volume (Real.pi / 2))] with
        theta htheta htheta0 htheta1
    have ht0 : 0 < theta := lt_of_le_of_ne htheta.1
      (Ne.symm htheta0)
    have ht1 : theta < Real.pi / 2 :=
      lt_of_le_of_ne htheta.2 htheta1
    simpa [f, f', g, h, smul_eq_mul] using
      trigBeta_kernel_eq u v theta ht0 ht1
  have hkernelIntegral :
      (∫ theta in Set.Icc (0 : ℝ) (Real.pi / 2),
          f' theta • g (f theta)) =
        ∫ theta in Set.Icc (0 : ℝ) (Real.pi / 2),
          2 * h theta :=
    integral_congr_ae hkernelAE
  have hbetaSet :
      (∫ t in Set.Icc (0 : ℝ) 1, g t) =
        ∫ t in (0 : ℝ)..1, g t := by
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
      intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  have htrigSet :
      (∫ theta in Set.Icc (0 : ℝ) (Real.pi / 2), h theta) =
        ∫ theta in (0 : ℝ)..Real.pi / 2, h theta := by
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
      intervalIntegral.integral_of_le hpi]
  have htwo :
      (∫ theta in Set.Icc (0 : ℝ) (Real.pi / 2),
          2 * h theta) =
        2 * ∫ theta in (0 : ℝ)..Real.pi / 2, h theta := by
    rw [MeasureTheory.integral_const_mul, htrigSet]
  have hmain :
      (∫ t in (0 : ℝ)..1, g t) =
        2 * ∫ theta in (0 : ℝ)..Real.pi / 2, h theta := by
    calc
      (∫ t in (0 : ℝ)..1, g t) =
          ∫ t in Set.Icc (0 : ℝ) 1, g t := hbetaSet.symm
      _ = ∫ theta in Set.Icc (0 : ℝ) (Real.pi / 2),
          f' theta • g (f theta) := hchange
      _ = ∫ theta in Set.Icc (0 : ℝ) (Real.pi / 2),
          2 * h theta := hkernelIntegral
      _ = 2 * ∫ theta in (0 : ℝ)..Real.pi / 2, h theta := htwo
  dsimp [g, h] at hmain ⊢
  rw [hmain]
  ring

private theorem trigBeta_integrableOn_Ioo
    (u v : ℝ) (hu : 0 < u) (hv : 0 < v) :
    IntegrableOn
      (fun theta : ℝ =>
        Real.rpow (Real.sin theta) (2 * u - 1) *
          Real.rpow (Real.cos theta) (2 * v - 1))
      (Ioo (0 : ℝ) (Real.pi / 2)) := by
  let f : ℝ → ℝ := fun theta => Real.sin theta ^ 2
  let f' : ℝ → ℝ :=
    fun theta => 2 * Real.sin theta * Real.cos theta
  let g : ℝ → ℝ :=
    fun t =>
      Real.rpow t (u - 1) * Real.rpow (1 - t) (v - 1)
  let h : ℝ → ℝ :=
    fun theta =>
      Real.rpow (Real.sin theta) (2 * u - 1) *
        Real.rpow (Real.cos theta) (2 * v - 1)
  have hpi : 0 ≤ Real.pi / 2 := by positivity
  have hfcont :
      ContinuousOn f (Icc (0 : ℝ) (Real.pi / 2)) :=
    (Real.continuous_sin.pow 2).continuousOn
  have hfmono :
      MonotoneOn f (Icc (0 : ℝ) (Real.pi / 2)) := by
    intro x hx y hy hxy
    have hx' : x ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) :=
      ⟨(neg_nonpos.mpr hpi).trans hx.1, hx.2⟩
    have hy' : y ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) :=
      ⟨(neg_nonpos.mpr hpi).trans hy.1, hy.2⟩
    have hsxy : Real.sin x ≤ Real.sin y :=
      Real.monotoneOn_sin hx' hy' hxy
    have hsx0 : 0 ≤ Real.sin x :=
      Real.sin_nonneg_of_nonneg_of_le_pi hx.1
        (hx.2.trans (half_le_self Real.pi_pos.le))
    have hsy0 : 0 ≤ Real.sin y :=
      Real.sin_nonneg_of_nonneg_of_le_pi hy.1
        (hy.2.trans (half_le_self Real.pi_pos.le))
    dsimp [f]
    nlinarith
  have hfimage :
      f '' Icc (0 : ℝ) (Real.pi / 2) = Icc (0 : ℝ) 1 := by
    apply Set.Subset.antisymm
    · simpa [f] using hfmono.image_Icc_subset
    · simpa [f] using intermediate_value_Icc hpi hfcont
  have hfder :
      ∀ theta ∈ Icc (0 : ℝ) (Real.pi / 2),
        HasDerivWithinAt f (f' theta)
          (Icc (0 : ℝ) (Real.pi / 2)) theta := by
    intro theta htheta
    have hd :=
      (Real.hasDerivAt_sin theta).mul
        (Real.hasDerivAt_sin theta)
    apply HasDerivAt.hasDerivWithinAt
    convert hd using 1
    · funext t
      simp [f, pow_two]
    · dsimp [f']
      ring
  have hgIcc : IntegrableOn g (Icc (0 : ℝ) 1) := by
    have hg :=
      betaKernel_intervalIntegrable u v hu hv
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le
      (by norm_num : (0 : ℝ) ≤ 1)] at hg
    rwa [integrableOn_Icc_iff_integrableOn_Ioc]
  have hderivInt :
      IntegrableOn
        (fun theta => f' theta • g (f theta))
        (Icc (0 : ℝ) (Real.pi / 2)) := by
    apply
      (integrableOn_image_iff_integrableOn_deriv_smul_of_monotoneOn
        measurableSet_Icc hfder hfmono g).mp
    rw [hfimage]
    exact hgIcc
  have hkernelAE :
      (fun theta => f' theta • g (f theta)) =ᵐ[
        volume.restrict (Icc (0 : ℝ) (Real.pi / 2))]
        (fun theta => 2 * h theta) := by
    filter_upwards
      [ae_restrict_mem measurableSet_Icc,
        ae_restrict_of_ae (Measure.ae_ne volume (0 : ℝ)),
        ae_restrict_of_ae
          (Measure.ae_ne volume (Real.pi / 2))] with
        theta htheta htheta0 htheta1
    have ht0 : 0 < theta := lt_of_le_of_ne htheta.1
      (Ne.symm htheta0)
    have ht1 : theta < Real.pi / 2 :=
      lt_of_le_of_ne htheta.2 htheta1
    simpa [f, f', g, h, smul_eq_mul] using
      trigBeta_kernel_eq u v theta ht0 ht1
  have htwo :
      IntegrableOn (fun theta => 2 * h theta)
        (Icc (0 : ℝ) (Real.pi / 2)) :=
    hderivInt.congr hkernelAE
  have hhIcc :
      IntegrableOn h (Icc (0 : ℝ) (Real.pi / 2)) := by
    have hscaled := htwo.const_mul (1 / 2 : ℝ)
    apply hscaled.congr
    filter_upwards with theta
    dsimp [h]
    ring
  exact hhIcc.mono_set Ioo_subset_Icc_self

private theorem angleLIntegral_eq_beta
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    angleLIntegral a b =
      ENNReal.ofReal
        ((1 / 2 : ℝ) * betaFnLocal (b / 2) (a / 2)) := by
  let A : ℝ → ℝ := fun theta =>
    Real.rpow (Real.cos theta) (a - 1) *
      Real.rpow (Real.sin theta) (b - 1)
  have hhalfA : 0 < a / 2 := by positivity
  have hhalfB : 0 < b / 2 := by positivity
  have haExp : 2 * (a / 2) - 1 = a - 1 := by ring
  have hbExp : 2 * (b / 2) - 1 = b - 1 := by ring
  have hAint :
      IntegrableOn A (Ioo (0 : ℝ) (Real.pi / 2)) := by
    have h :=
      trigBeta_integrableOn_Ioo
        (b / 2) (a / 2) hhalfB hhalfA
    simpa [A, haExp, hbExp, mul_comm] using h
  have hAnonneg :
      ∀ theta ∈ Ioo (0 : ℝ) (Real.pi / 2),
        0 ≤ A theta := by
    intro theta htheta
    dsimp [A]
    exact mul_nonneg
      (Real.rpow_nonneg
        (Real.cos_nonneg_of_neg_pi_div_two_le_of_le
          (by linarith [htheta.1, Real.pi_pos]) htheta.2.le) _)
      (Real.rpow_nonneg
        (Real.sin_nonneg_of_nonneg_of_le_pi htheta.1.le
          (by linarith [htheta.2, Real.pi_pos])) _)
  have hLnorm :
      angleLIntegral a b =
        ∫⁻ theta in Ioo (0 : ℝ) (Real.pi / 2),
          ENNReal.ofReal ‖A theta‖ := by
    unfold angleLIntegral angleKernel
    apply setLIntegral_congr_fun measurableSet_Ioo
    intro theta htheta
    dsimp only
    rw [Real.norm_of_nonneg (hAnonneg theta htheta)]
    dsimp [A]
    rw [ENNReal.ofReal_mul
      (Real.rpow_nonneg
        (Real.cos_nonneg_of_neg_pi_div_two_le_of_le
          (by linarith [htheta.1, Real.pi_pos]) htheta.2.le) _)]
  have hfinite : angleLIntegral a b ≠ ∞ := by
    rw [hLnorm]
    exact ne_of_lt
      ((MeasureTheory.hasFiniteIntegral_iff_norm A).mp hAint.2)
  have hreal :
      (∫ theta in Ioo (0 : ℝ) (Real.pi / 2), A theta) =
        (angleLIntegral a b).toReal := by
    rw [MeasureTheory.integral_eq_lintegral_of_nonneg_ae
      (ae_restrict_of_forall_mem measurableSet_Ioo hAnonneg)
      hAint.1]
    congr 1
    unfold angleLIntegral angleKernel
    apply setLIntegral_congr_fun measurableSet_Ioo
    intro theta htheta
    dsimp [A]
    rw [ENNReal.ofReal_mul
      (Real.rpow_nonneg
        (Real.cos_nonneg_of_neg_pi_div_two_le_of_le
          (by linarith [htheta.1, Real.pi_pos]) htheta.2.le) _)]
  have hsetInterval :
      (∫ theta in Ioo (0 : ℝ) (Real.pi / 2), A theta) =
        ∫ theta in (0 : ℝ)..Real.pi / 2, A theta := by
    rw [← integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le
        (by positivity : (0 : ℝ) ≤ Real.pi / 2)]
  have htrig :=
    trigBeta_integral
      (b / 2) (a / 2) hhalfB hhalfA
  have htrig' :
      (∫ theta in (0 : ℝ)..Real.pi / 2, A theta) =
        (1 / 2 : ℝ) *
          betaFnLocal (b / 2) (a / 2) := by
    unfold betaFnLocal
    rw [← intervalIntegral.integral_of_le
      (by norm_num : (0 : ℝ) ≤ 1)]
    simpa [A, haExp, hbExp, mul_comm] using htrig
  calc
    angleLIntegral a b =
        ENNReal.ofReal (angleLIntegral a b).toReal :=
      (ENNReal.ofReal_toReal hfinite).symm
    _ = ENNReal.ofReal
        (∫ theta in Ioo (0 : ℝ) (Real.pi / 2), A theta) := by
      rw [hreal]
    _ = ENNReal.ofReal
        (∫ theta in (0 : ℝ)..Real.pi / 2, A theta) := by
      rw [hsetInterval]
    _ = ENNReal.ofReal
        ((1 / 2 : ℝ) * betaFnLocal (b / 2) (a / 2)) := by
      rw [htrig']

private noncomputable def denominatorLocal
    (p q r : ℝ) (z : Point3) : ℝ :=
  Real.rpow |z.1| p + Real.rpow |z.2.1| q +
    Real.rpow |z.2.2| r

private noncomputable def integrandLocal
    (p q r : ℝ) (z : Point3) : ℝ :=
  1 / denominatorLocal p q r z

private def omegaTailLocal (p q r : ℝ) : Set Point3 :=
  {z | 0 ≤ z.1 ∧ 0 ≤ z.2.1 ∧ 0 ≤ z.2.2 ∧
    3 < denominatorLocal p q r z}

private noncomputable def positiveTail
    (p q r : ℝ) : Set Point3 :=
  {z | z ∈ positiveOctant ∧ 3 < denominatorLocal p q r z}

private noncomputable def tailF
    (p q r : ℝ) (z : Point3) : ℝ≥0∞ :=
  if 3 < denominatorLocal p q r z then
    ENNReal.ofReal (integrandLocal p q r z)
  else 0

private theorem denominatorLocal_measurable (p q r : ℝ) :
    Measurable (denominatorLocal p q r) := by
  unfold denominatorLocal
  exact
    (((measurable_real_rpow_const p).comp
      (continuous_abs.measurable.comp measurable_fst)).add
      ((measurable_real_rpow_const q).comp
        (continuous_abs.measurable.comp
          (measurable_fst.comp measurable_snd)))).add
      ((measurable_real_rpow_const r).comp
        (continuous_abs.measurable.comp
          (measurable_snd.comp measurable_snd)))

private theorem integrandLocal_measurable (p q r : ℝ) :
    Measurable (integrandLocal p q r) := by
  unfold integrandLocal
  exact measurable_const.div (denominatorLocal_measurable p q r)

private theorem tailF_measurable (p q r : ℝ) :
    Measurable (tailF p q r) := by
  unfold tailF
  exact Measurable.ite
    (measurableSet_lt measurable_const
      (denominatorLocal_measurable p q r))
    (ENNReal.measurable_ofReal.comp
      (integrandLocal_measurable p q r))
    measurable_const

private theorem positiveOctant_measurable :
    MeasurableSet positiveOctant := by
  unfold positiveOctant
  exact measurableSet_Ioi.prod
    (measurableSet_Ioi.prod measurableSet_Ioi)

private theorem positiveTail_measurable (p q r : ℝ) :
    MeasurableSet (positiveTail p q r) := by
  unfold positiveTail
  exact positiveOctant_measurable.inter
    (measurableSet_lt measurable_const
      (denominatorLocal_measurable p q r))

private theorem omegaTailLocal_measurable (p q r : ℝ) :
    MeasurableSet (omegaTailLocal p q r) := by
  unfold omegaTailLocal
  exact
    (measurableSet_le measurable_const measurable_fst).inter
      ((measurableSet_le measurable_const
        (measurable_fst.comp measurable_snd)).inter
        ((measurableSet_le measurable_const
          (measurable_snd.comp measurable_snd)).inter
          (measurableSet_lt measurable_const
            (denominatorLocal_measurable p q r))))

private theorem off_coordinate_planes_ae :
    ∀ᵐ z ∂(volume : Measure Point3),
      z.1 ≠ 0 ∧ z.2.1 ≠ 0 ∧ z.2.2 ≠ 0 := by
  have hpair :
      ∀ᵐ y ∂(volume : Measure (ℝ × ℝ)),
        y.1 ≠ 0 ∧ y.2 ≠ 0 := by
    rw [Measure.volume_eq_prod]
    have hmeas₂ :
        MeasurableSet
          {z : ℝ × ℝ | z.1 ≠ 0 ∧ z.2 ≠ 0} := by
      change MeasurableSet
        (({0}ᶜ : Set ℝ) ×ˢ ({0}ᶜ : Set ℝ))
      exact
        (measurableSet_singleton (0 : ℝ)).compl.prod
          (measurableSet_singleton (0 : ℝ)).compl
    apply (Measure.ae_prod_iff_ae_ae hmeas₂).2
    filter_upwards [Measure.ae_ne volume (0 : ℝ)] with y hy
    filter_upwards [Measure.ae_ne volume (0 : ℝ)] with z hz
    exact ⟨hy, hz⟩
  rw [Measure.volume_eq_prod]
  have hmeas :
      MeasurableSet
        {z : Point3 |
          z.1 ≠ 0 ∧ z.2.1 ≠ 0 ∧ z.2.2 ≠ 0} := by
    change MeasurableSet
      (({0}ᶜ : Set ℝ) ×ˢ
        (({0}ᶜ : Set ℝ) ×ˢ ({0}ᶜ : Set ℝ)))
    exact
      (measurableSet_singleton (0 : ℝ)).compl.prod
        ((measurableSet_singleton (0 : ℝ)).compl.prod
          (measurableSet_singleton (0 : ℝ)).compl)
  apply (Measure.ae_prod_iff_ae_ae hmeas).2
  filter_upwards [Measure.ae_ne volume (0 : ℝ)] with x hx
  filter_upwards [hpair] with y hy
  exact ⟨hx, hy.1, hy.2⟩

private theorem omegaTail_ae_eq_positiveTail
    (p q r : ℝ) :
    omegaTailLocal p q r =ᵐ[volume] positiveTail p q r := by
  filter_upwards [off_coordinate_planes_ae] with z hz
  apply propext
  constructor
  · intro h
    exact
      ⟨⟨lt_of_le_of_ne h.1 (Ne.symm hz.1),
          lt_of_le_of_ne h.2.1 (Ne.symm hz.2.1),
          lt_of_le_of_ne h.2.2.1 (Ne.symm hz.2.2)⟩,
        h.2.2.2⟩
  · intro h
    exact
      ⟨h.1.1.le, h.1.2.1.le, h.1.2.2.le, h.2⟩

private theorem omegaTail_lintegral_eq_positiveOctant
    (p q r : ℝ) :
    (∫⁻ z in omegaTailLocal p q r,
        ENNReal.ofReal (integrandLocal p q r z)) =
      ∫⁻ z in positiveOctant, tailF p q r z := by
  calc
    (∫⁻ z in omegaTailLocal p q r,
        ENNReal.ofReal (integrandLocal p q r z)) =
        ∫⁻ z in positiveTail p q r,
          ENNReal.ofReal (integrandLocal p q r z) := by
      exact setLIntegral_congr
        (omegaTail_ae_eq_positiveTail p q r)
    _ = ∫⁻ z in positiveOctant, tailF p q r z := by
      rw [← lintegral_indicator
        (positiveTail_measurable p q r),
        ← lintegral_indicator positiveOctant_measurable]
      apply lintegral_congr
      intro z
      by_cases hz : z ∈ positiveOctant
      · by_cases hd : 3 < denominatorLocal p q r z
        · have hpt : z ∈ positiveTail p q r := ⟨hz, hd⟩
          rw [indicator_of_mem hpt, indicator_of_mem hz]
          simp [tailF, hd]
        · have hnpt : z ∉ positiveTail p q r :=
            fun h => hd h.2
          rw [indicator_of_notMem hnpt, indicator_of_mem hz]
          simp [tailF, hd]
      · have hnpt : z ∉ positiveTail p q r :=
          fun h => hz h.1
        rw [indicator_of_notMem hnpt,
          indicator_of_notMem hz]

private theorem rpow_two_div_rpow
    {x p : ℝ} (hx : 0 < x) (hp : p ≠ 0) :
    Real.rpow (Real.rpow x (2 / p)) p = x ^ 2 := by
  calc
    Real.rpow (Real.rpow x (2 / p)) p =
        Real.rpow x ((2 / p) * p) :=
      (Real.rpow_mul hx.le (2 / p) p).symm
    _ = Real.rpow x 2 := by
      rw [div_mul_cancel₀ _ hp]
    _ = x ^ 2 := Real.rpow_two x

private noncomputable def tailH (s : ℝ) : ℝ≥0∞ :=
  if 3 < s then ENNReal.ofReal (1 / s) else 0

private theorem tailH_measurable : Measurable tailH := by
  unfold tailH
  exact Measurable.ite
    (measurableSet_lt measurable_const measurable_id)
    (ENNReal.measurable_ofReal.comp
      (measurable_const.div measurable_id))
    measurable_const

private theorem tailF_powerMap
    {p q r u v w : ℝ}
    (hp : p ≠ 0) (hq : q ≠ 0) (hr : r ≠ 0)
    (hu : 0 < u) (hv : 0 < v) (hw : 0 < w) :
    tailF p q r
        (Real.rpow u (2 / p),
          Real.rpow v (2 / q),
          Real.rpow w (2 / r)) =
      tailH (u ^ 2 + v ^ 2 + w ^ 2) := by
  have hup : 0 < Real.rpow u (2 / p) :=
    Real.rpow_pos_of_pos hu _
  have hvp : 0 < Real.rpow v (2 / q) :=
    Real.rpow_pos_of_pos hv _
  have hwp : 0 < Real.rpow w (2 / r) :=
    Real.rpow_pos_of_pos hw _
  unfold tailF tailH integrandLocal denominatorLocal
  rw [abs_of_pos hup, abs_of_pos hvp, abs_of_pos hwp,
    rpow_two_div_rpow hu hp, rpow_two_div_rpow hv hq,
    rpow_two_div_rpow hw hr]

private theorem tail_lintegral_power_transform
    (p q r : ℝ) (hp : 0 < p) (hq : 0 < q) (hr : 0 < r) :
    (∫⁻ z in positiveOctant, tailF p q r z) =
      ENNReal.ofReal (8 / (p * q * r)) *
        ∫⁻ u in positiveOctant,
          ENNReal.ofReal
              (Real.rpow u.1 (2 / p - 1)) *
            ENNReal.ofReal
              (Real.rpow u.2.1 (2 / q - 1)) *
            ENNReal.ofReal
              (Real.rpow u.2.2 (2 / r - 1)) *
            tailH (u.1 ^ 2 + u.2.1 ^ 2 + u.2.2 ^ 2) := by
  have hap : 0 < 2 / p := div_pos (by norm_num) hp
  have haq : 0 < 2 / q := div_pos (by norm_num) hq
  have har : 0 < 2 / r := div_pos (by norm_num) hr
  let G : Point3 → ℝ≥0∞ := fun u =>
    ENNReal.ofReal (Real.rpow u.1 (2 / p - 1)) *
      ENNReal.ofReal (Real.rpow u.2.1 (2 / q - 1)) *
      ENNReal.ofReal (Real.rpow u.2.2 (2 / r - 1)) *
      tailH (u.1 ^ 2 + u.2.1 ^ 2 + u.2.2 ^ 2)
  have hG : Measurable G := by
    dsimp [G]
    exact
      (((ENNReal.measurable_ofReal.comp
          ((measurable_real_rpow_const (2 / p - 1)).comp
            measurable_fst)).mul
        (ENNReal.measurable_ofReal.comp
          ((measurable_real_rpow_const (2 / q - 1)).comp
            (measurable_fst.comp measurable_snd)))).mul
        (ENNReal.measurable_ofReal.comp
          ((measurable_real_rpow_const (2 / r - 1)).comp
            (measurable_snd.comp measurable_snd)))).mul
        (tailH_measurable.comp (by fun_prop))
  have hcoeff :
      ENNReal.ofReal (2 / p) *
            ENNReal.ofReal (2 / q) *
          ENNReal.ofReal (2 / r) =
        ENNReal.ofReal (8 / (p * q * r)) := by
    rw [← ENNReal.ofReal_mul hap.le,
      ← ENNReal.ofReal_mul (mul_nonneg hap.le haq.le)]
    congr 1
    field_simp
    ring
  rw [setLIntegral_positiveOctant_rpow'
    (tailF p q r) (tailF_measurable p q r)
    hap haq har]
  calc
    (∫⁻ u in positiveOctant,
        ENNReal.ofReal
              ((2 / p) * Real.rpow u.1 (2 / p - 1)) *
          ENNReal.ofReal
              ((2 / q) * Real.rpow u.2.1 (2 / q - 1)) *
          ENNReal.ofReal
              ((2 / r) * Real.rpow u.2.2 (2 / r - 1)) *
          tailF p q r
            (Real.rpow u.1 (2 / p),
              Real.rpow u.2.1 (2 / q),
              Real.rpow u.2.2 (2 / r))) =
        ∫⁻ u in positiveOctant,
          ENNReal.ofReal (8 / (p * q * r)) * G u := by
      apply setLIntegral_congr_fun positiveOctant_measurable
      intro u hu
      have hu₁ : 0 < u.1 := hu.1
      have hu₂ : 0 < u.2.1 := hu.2.1
      have hu₃ : 0 < u.2.2 := hu.2.2
      dsimp only
      rw [tailF_powerMap hp.ne' hq.ne' hr.ne' hu₁ hu₂ hu₃,
        ENNReal.ofReal_mul hap.le,
        ENNReal.ofReal_mul haq.le,
        ENNReal.ofReal_mul har.le]
      dsimp [G]
      rw [← hcoeff]
      ring
    _ = ENNReal.ofReal (8 / (p * q * r)) *
        ∫⁻ u in positiveOctant, G u := by
      exact MeasureTheory.lintegral_const_mul'
        (ENNReal.ofReal (8 / (p * q * r))) G (by finiteness)

private theorem tail_lintegral_radial
    (p q r : ℝ) (hp : 0 < p) (hq : 0 < q) (hr : 0 < r) :
    (∫⁻ z in positiveOctant, tailF p q r z) =
      ENNReal.ofReal (8 / (p * q * r)) *
        angleLIntegral (2 / p) (2 / q) *
        angleLIntegral (2 / p + 2 / q) (2 / r) *
        ∫⁻ R in Ioi (0 : ℝ),
          ENNReal.ofReal
              (Real.rpow R
                (2 / p + 2 / q + 2 / r - 1)) *
            tailH (R ^ 2) := by
  have hap : 0 < 2 / p := div_pos (by norm_num) hp
  have haq : 0 < 2 / q := div_pos (by norm_num) hq
  have har : 0 < 2 / r := div_pos (by norm_num) hr
  have hang :
      angleLIntegral (2 / p) (2 / q) ≠ ∞ := by
    rw [angleLIntegral_eq_beta (2 / p) (2 / q) hap haq]
    finiteness
  rw [tail_lintegral_power_transform p q r hp hq hr,
    octant_weighted_radial_lintegral
      (2 / p) (2 / q) (2 / r)
      hap haq har hang tailH tailH_measurable]
  ring

private noncomputable def radialKernel
    (p q r R : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal
    (Real.rpow R (2 / p + 2 / q + 2 / r - 3))

private theorem radial_tail_lintegral
    (p q r : ℝ) :
    (∫⁻ R in Ioi (0 : ℝ),
        ENNReal.ofReal
            (Real.rpow R
              (2 / p + 2 / q + 2 / r - 1)) *
          tailH (R ^ 2)) =
      ∫⁻ R in Ioi (Real.sqrt 3), radialKernel p q r R := by
  have hsqrt : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  let E : ℝ := 2 / p + 2 / q + 2 / r - 1
  have hpoint :
      ∀ R ∈ Ioi (0 : ℝ),
        ENNReal.ofReal (Real.rpow R E) * tailH (R ^ 2) =
          (Ioi (Real.sqrt 3)).indicator
            (radialKernel p q r) R := by
    intro R hR
    by_cases htail : Real.sqrt 3 < R
    · have hsq : 3 < R ^ 2 :=
        (Real.sqrt_lt' hR).1 htail
      have htail' : R ∈ Ioi (Real.sqrt 3) := htail
      rw [indicator_of_mem htail']
      unfold tailH radialKernel
      rw [if_pos hsq]
      calc
        ENNReal.ofReal (Real.rpow R E) *
              ENNReal.ofReal (1 / R ^ 2) =
            ENNReal.ofReal
              (Real.rpow R E * (1 / R ^ 2)) :=
          (ENNReal.ofReal_mul
            (Real.rpow_nonneg hR.le E)).symm
        _ = ENNReal.ofReal
              (Real.rpow R
                (2 / p + 2 / q + 2 / r - 3)) := by
          congr 1
          dsimp [E]
          calc
            Real.rpow R
                  (2 / p + 2 / q + 2 / r - 1) *
                (1 / R ^ 2) =
              Real.rpow R
                  (2 / p + 2 / q + 2 / r - 1) /
                Real.rpow R 2 := by
              have hr2 :
                  Real.rpow R (2 : ℝ) = R ^ 2 :=
                Real.rpow_two R
              rw [hr2]
              ring
            _ = Real.rpow R
                ((2 / p + 2 / q + 2 / r - 1) - 2) :=
              (Real.rpow_sub hR
                (2 / p + 2 / q + 2 / r - 1) 2).symm
            _ = Real.rpow R
                (2 / p + 2 / q + 2 / r - 3) := by
              congr 1
              ring
    · have hsq : ¬ 3 < R ^ 2 :=
        fun h => htail ((Real.sqrt_lt' hR).2 h)
      have htail' : R ∉ Ioi (Real.sqrt 3) := htail
      rw [indicator_of_notMem htail']
      simp [tailH, hsq]
  calc
    (∫⁻ R in Ioi (0 : ℝ),
        ENNReal.ofReal
            (Real.rpow R
              (2 / p + 2 / q + 2 / r - 1)) *
          tailH (R ^ 2)) =
        ∫⁻ R in Ioi (0 : ℝ),
          (Ioi (Real.sqrt 3)).indicator
            (radialKernel p q r) R := by
      apply setLIntegral_congr_fun measurableSet_Ioi
      intro R hR
      exact hpoint R hR
    _ = ∫⁻ R in Ioi (Real.sqrt 3),
          radialKernel p q r R := by
      rw [← lintegral_indicator measurableSet_Ioi,
        ← lintegral_indicator measurableSet_Ioi]
      apply lintegral_congr
      intro R
      by_cases htail : R ∈ Ioi (Real.sqrt 3)
      · have hpos : R ∈ Ioi (0 : ℝ) :=
          lt_trans hsqrt htail
        rw [indicator_of_mem htail,
          indicator_of_mem hpos,
          indicator_of_mem htail]
      · rw [indicator_of_notMem htail]
        by_cases hpos : R ∈ Ioi (0 : ℝ)
        · rw [indicator_of_mem hpos,
            indicator_of_notMem htail]
        · rw [indicator_of_notMem hpos]

private theorem betaFnLocal_nonneg (x y : ℝ) :
    0 ≤ betaFnLocal x y := by
  unfold betaFnLocal
  apply setIntegral_nonneg measurableSet_Ioc
  intro t ht
  exact mul_nonneg
    (Real.rpow_nonneg ht.1.le _)
    (Real.rpow_nonneg (sub_nonneg.mpr ht.2) _)

private theorem omegaTail_lintegral_beta
    (p q r : ℝ) (hp : 0 < p) (hq : 0 < q) (hr : 0 < r) :
    (∫⁻ z in omegaTailLocal p q r,
        ENNReal.ofReal (integrandLocal p q r z)) =
      ENNReal.ofReal
          (2 / (p * q * r) *
            betaFnLocal (1 / r) (1 / p + 1 / q) *
            betaFnLocal (1 / q) (1 / p)) *
        ∫⁻ R in Ioi (Real.sqrt 3), radialKernel p q r R := by
  have hap : 0 < 2 / p := div_pos (by norm_num) hp
  have haq : 0 < 2 / q := div_pos (by norm_num) hq
  have har : 0 < 2 / r := div_pos (by norm_num) hr
  have hab : 0 < 2 / p + 2 / q := add_pos hap haq
  have hpqr : 0 < p * q * r :=
    mul_pos (mul_pos hp hq) hr
  have hargp : (2 / p) / 2 = 1 / p := by
    field_simp
  have hargq : (2 / q) / 2 = 1 / q := by
    field_simp
  have hargr : (2 / r) / 2 = 1 / r := by
    field_simp
  have hargpq :
      (2 / p + 2 / q) / 2 = 1 / p + 1 / q := by
    field_simp
  rw [omegaTail_lintegral_eq_positiveOctant,
    tail_lintegral_radial p q r hp hq hr,
    angleLIntegral_eq_beta (2 / p) (2 / q) hap haq,
    angleLIntegral_eq_beta
      (2 / p + 2 / q) (2 / r) hab har,
    radial_tail_lintegral]
  rw [hargp, hargq, hargr, hargpq]
  congr 1
  have hb₁ :
      0 ≤ betaFnLocal (1 / q) (1 / p) :=
    betaFnLocal_nonneg _ _
  have hb₂ :
      0 ≤ betaFnLocal (1 / r) (1 / p + 1 / q) :=
    betaFnLocal_nonneg _ _
  have hc : 0 ≤ 8 / (p * q * r) :=
    div_nonneg (by norm_num) hpqr.le
  have hf₁ :
      0 ≤ (1 / 2 : ℝ) * betaFnLocal (1 / q) (1 / p) :=
    mul_nonneg (by norm_num) hb₁
  have hf₂ :
      0 ≤ (1 / 2 : ℝ) *
        betaFnLocal (1 / r) (1 / p + 1 / q) :=
    mul_nonneg (by norm_num) hb₂
  rw [← ENNReal.ofReal_mul hc,
    ← ENNReal.ofReal_mul (mul_nonneg hc hf₁)]
  congr 1
  ring

private theorem denominatorLocal_nonneg
    (p q r : ℝ) (z : Point3) :
    0 ≤ denominatorLocal p q r z := by
  unfold denominatorLocal
  exact add_nonneg
    (add_nonneg
      (Real.rpow_nonneg (abs_nonneg _) _)
      (Real.rpow_nonneg (abs_nonneg _) _))
    (Real.rpow_nonneg (abs_nonneg _) _)

private theorem integrandLocal_nonneg
    (p q r : ℝ) (z : Point3) :
    0 ≤ integrandLocal p q r z := by
  unfold integrandLocal
  exact one_div_nonneg.mpr (denominatorLocal_nonneg p q r z)

private noncomputable def radialWeightLocal
    (p q r R : ℝ) : ℝ :=
  Real.rpow R (2 / p + 2 / q + 2 / r - 3)

private theorem radialWeightLocal_measurable
    (p q r : ℝ) :
    Measurable (radialWeightLocal p q r) := by
  unfold radialWeightLocal
  exact measurable_real_rpow_const _

private theorem radialWeightLocal_nonneg
    (p q r R : ℝ) (hR : 0 ≤ R) :
    0 ≤ radialWeightLocal p q r R := by
  unfold radialWeightLocal
  exact Real.rpow_nonneg hR _

private theorem omegaTail_integral_beta
    (p q r : ℝ) (hp : 0 < p) (hq : 0 < q) (hr : 0 < r) :
    (∫ z in omegaTailLocal p q r,
        integrandLocal p q r z) =
      2 / (p * q * r) *
        betaFnLocal (1 / r) (1 / p + 1 / q) *
        betaFnLocal (1 / q) (1 / p) *
        ∫ R in Ioi (Real.sqrt 3),
          radialWeightLocal p q r R := by
  let C : ℝ :=
    2 / (p * q * r) *
      betaFnLocal (1 / r) (1 / p + 1 / q) *
      betaFnLocal (1 / q) (1 / p)
  have hpqr : 0 < p * q * r :=
    mul_pos (mul_pos hp hq) hr
  have hC : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg
      (mul_nonneg
        (div_nonneg (by norm_num) hpqr.le)
        (betaFnLocal_nonneg _ _))
      (betaFnLocal_nonneg _ _)
  have hleft :
      (∫ z in omegaTailLocal p q r,
          integrandLocal p q r z) =
        ENNReal.toReal
          (∫⁻ z in omegaTailLocal p q r,
            ENNReal.ofReal (integrandLocal p q r z)) := by
    exact integral_eq_lintegral_of_nonneg_ae
      (Filter.Eventually.of_forall
        (integrandLocal_nonneg p q r))
      (integrandLocal_measurable p q r).aestronglyMeasurable
  have hrad :
      (∫ R in Ioi (Real.sqrt 3),
          radialWeightLocal p q r R) =
        ENNReal.toReal
          (∫⁻ R in Ioi (Real.sqrt 3),
            radialKernel p q r R) := by
    convert integral_eq_lintegral_of_nonneg_ae
      (μ := volume.restrict (Ioi (Real.sqrt 3)))
      (ae_restrict_of_forall_mem measurableSet_Ioi
        (fun R hR =>
          radialWeightLocal_nonneg p q r R
            (le_trans (Real.sqrt_nonneg 3) hR.le)))
      (radialWeightLocal_measurable p q r).aestronglyMeasurable
      using 1
  calc
    (∫ z in omegaTailLocal p q r,
        integrandLocal p q r z) =
        ENNReal.toReal
          (∫⁻ z in omegaTailLocal p q r,
            ENNReal.ofReal (integrandLocal p q r z)) :=
      hleft
    _ = ENNReal.toReal
        (ENNReal.ofReal C *
          ∫⁻ R in Ioi (Real.sqrt 3),
            radialKernel p q r R) := by
      rw [omegaTail_lintegral_beta p q r hp hq hr]
    _ = C *
        ENNReal.toReal
          (∫⁻ R in Ioi (Real.sqrt 3),
            radialKernel p q r R) := by
      rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hC]
    _ = 2 / (p * q * r) *
        betaFnLocal (1 / r) (1 / p + 1 / q) *
        betaFnLocal (1 / q) (1 / p) *
        ∫ R in Ioi (Real.sqrt 3),
          radialWeightLocal p q r R := by
      rw [← hrad]

private def flipX (z : Point3) : Point3 :=
  (-z.1, z.2.1, z.2.2)

private def flipY (z : Point3) : Point3 :=
  (z.1, -z.2.1, z.2.2)

private def flipZ (z : Point3) : Point3 :=
  (z.1, z.2.1, -z.2.2)

private theorem flipX_measurePreserving :
    MeasurePreserving flipX
      (volume : Measure Point3) volume := by
  rw [Measure.volume_eq_prod]
  exact MeasurePreserving.prod
    (Measure.measurePreserving_neg (volume : Measure ℝ))
    (MeasurePreserving.id (volume : Measure (ℝ × ℝ)))

private theorem flipY_measurePreserving :
    MeasurePreserving flipY
      (volume : Measure Point3) volume := by
  rw [Measure.volume_eq_prod, Measure.volume_eq_prod]
  exact MeasurePreserving.prod
    (MeasurePreserving.id (volume : Measure ℝ))
    (MeasurePreserving.prod
      (Measure.measurePreserving_neg (volume : Measure ℝ))
      (MeasurePreserving.id (volume : Measure ℝ)))

private theorem flipZ_measurePreserving :
    MeasurePreserving flipZ
      (volume : Measure Point3) volume := by
  rw [Measure.volume_eq_prod, Measure.volume_eq_prod]
  exact MeasurePreserving.prod
    (MeasurePreserving.id (volume : Measure ℝ))
    (MeasurePreserving.prod
      (MeasurePreserving.id (volume : Measure ℝ))
      (Measure.measurePreserving_neg (volume : Measure ℝ)))

private theorem flipX_measurableEmbedding :
    MeasurableEmbedding flipX := by
  simpa [flipX, Prod.map] using
    (measurableEmbedding_neg.prodMap
      (MeasurableEmbedding.id :
        MeasurableEmbedding (id : ℝ × ℝ → ℝ × ℝ)))

private theorem flipY_measurableEmbedding :
    MeasurableEmbedding flipY := by
  simpa [flipY, Prod.map] using
    ((MeasurableEmbedding.id :
        MeasurableEmbedding (id : ℝ → ℝ)).prodMap
      (measurableEmbedding_neg.prodMap
        (MeasurableEmbedding.id :
          MeasurableEmbedding (id : ℝ → ℝ))))

private theorem flipZ_measurableEmbedding :
    MeasurableEmbedding flipZ := by
  simpa [flipZ, Prod.map] using
    ((MeasurableEmbedding.id :
        MeasurableEmbedding (id : ℝ → ℝ)).prodMap
      ((MeasurableEmbedding.id :
          MeasurableEmbedding (id : ℝ → ℝ)).prodMap
        measurableEmbedding_neg))

private theorem integrandLocal_flipX
    (p q r : ℝ) (z : Point3) :
    integrandLocal p q r (flipX z) =
      integrandLocal p q r z := by
  simp [integrandLocal, denominatorLocal, flipX]

private theorem integrandLocal_flipY
    (p q r : ℝ) (z : Point3) :
    integrandLocal p q r (flipY z) =
      integrandLocal p q r z := by
  simp [integrandLocal, denominatorLocal, flipY]

private theorem integrandLocal_flipZ
    (p q r : ℝ) (z : Point3) :
    integrandLocal p q r (flipZ z) =
      integrandLocal p q r z := by
  simp [integrandLocal, denominatorLocal, flipZ]

private noncomputable def tailYZ
    (p q r : ℝ) : Set Point3 :=
  {z | 0 ≤ z.2.1 ∧ 0 ≤ z.2.2 ∧
    3 < denominatorLocal p q r z}

private noncomputable def tailZ
    (p q r : ℝ) : Set Point3 :=
  {z | 0 ≤ z.2.2 ∧
    3 < denominatorLocal p q r z}

private noncomputable def tailAll
    (p q r : ℝ) : Set Point3 :=
  {z | 3 < denominatorLocal p q r z}

private theorem tailYZ_eq
    (p q r : ℝ) :
    tailYZ p q r =
      omegaTailLocal p q r ∪
        flipX ⁻¹' omegaTailLocal p q r := by
  ext z
  simp only [tailYZ, omegaTailLocal, mem_setOf_eq,
    mem_union, mem_preimage]
  rw [show denominatorLocal p q r (flipX z) =
    denominatorLocal p q r z by
      simp [denominatorLocal, flipX]]
  constructor
  · intro h
    by_cases hx : 0 ≤ z.1
    · exact Or.inl ⟨hx, h.1, h.2.1, h.2.2⟩
    · exact Or.inr
        ⟨by simpa [flipX] using (not_le.mp hx).le,
          h.1, h.2.1, h.2.2⟩
  · rintro (h | h)
    · exact ⟨h.2.1, h.2.2.1, h.2.2.2⟩
    · exact ⟨h.2.1, h.2.2.1, h.2.2.2⟩

private theorem tailZ_eq
    (p q r : ℝ) :
    tailZ p q r =
      tailYZ p q r ∪ flipY ⁻¹' tailYZ p q r := by
  ext z
  simp only [tailZ, tailYZ, mem_setOf_eq,
    mem_union, mem_preimage]
  rw [show denominatorLocal p q r (flipY z) =
    denominatorLocal p q r z by
      simp [denominatorLocal, flipY]]
  constructor
  · intro h
    by_cases hy : 0 ≤ z.2.1
    · exact Or.inl ⟨hy, h.1, h.2⟩
    · exact Or.inr
        ⟨by simpa [flipY] using (not_le.mp hy).le,
          h.1, h.2⟩
  · rintro (h | h)
    · exact ⟨h.2.1, h.2.2⟩
    · exact ⟨h.2.1, h.2.2⟩

private theorem tailAll_eq
    (p q r : ℝ) :
    tailAll p q r =
      tailZ p q r ∪ flipZ ⁻¹' tailZ p q r := by
  ext z
  simp only [tailAll, tailZ, mem_setOf_eq,
    mem_union, mem_preimage]
  rw [show denominatorLocal p q r (flipZ z) =
    denominatorLocal p q r z by
      simp [denominatorLocal, flipZ]]
  constructor
  · intro h
    by_cases hz : 0 ≤ z.2.2
    · exact Or.inl ⟨hz, h⟩
    · exact Or.inr
        ⟨by simpa [flipZ] using (not_le.mp hz).le, h⟩
  · rintro (h | h) <;> exact h.2

private theorem tailAll_integrable_iff_omegaTail
    (p q r : ℝ) :
    IntegrableOn (integrandLocal p q r) (tailAll p q r) ↔
      IntegrableOn (integrandLocal p q r)
        (omegaTailLocal p q r) := by
  constructor
  · intro h
    apply h.mono_set
    intro z hz
    exact hz.2.2.2
  · intro hpos
    have hxcomp :
        IntegrableOn
          (integrandLocal p q r ∘ flipX)
          (flipX ⁻¹' omegaTailLocal p q r) :=
      (flipX_measurePreserving.integrableOn_comp_preimage
        flipX_measurableEmbedding).2 hpos
    have hx :
        IntegrableOn (integrandLocal p q r)
          (flipX ⁻¹' omegaTailLocal p q r) :=
      hxcomp.congr_fun
        (fun z hz => integrandLocal_flipX p q r z)
        ((omegaTailLocal_measurable p q r).preimage
          flipX_measurableEmbedding.measurable)
    have hyz :
        IntegrableOn (integrandLocal p q r) (tailYZ p q r) := by
      rw [tailYZ_eq]
      exact hpos.union hx
    have hycomp :
        IntegrableOn
          (integrandLocal p q r ∘ flipY)
          (flipY ⁻¹' tailYZ p q r) :=
      (flipY_measurePreserving.integrableOn_comp_preimage
        flipY_measurableEmbedding).2 hyz
    have htailYZMeas :
        MeasurableSet (tailYZ p q r) := by
      rw [tailYZ_eq]
      exact (omegaTailLocal_measurable p q r).union
        ((omegaTailLocal_measurable p q r).preimage
          flipX_measurableEmbedding.measurable)
    have hy :
        IntegrableOn (integrandLocal p q r)
          (flipY ⁻¹' tailYZ p q r) :=
      hycomp.congr_fun
        (fun z hz => integrandLocal_flipY p q r z)
        (htailYZMeas.preimage
          flipY_measurableEmbedding.measurable)
    have hzpos :
        IntegrableOn (integrandLocal p q r) (tailZ p q r) := by
      rw [tailZ_eq]
      exact hyz.union hy
    have hzcomp :
        IntegrableOn
          (integrandLocal p q r ∘ flipZ)
          (flipZ ⁻¹' tailZ p q r) :=
      (flipZ_measurePreserving.integrableOn_comp_preimage
        flipZ_measurableEmbedding).2 hzpos
    have htailZMeas :
        MeasurableSet (tailZ p q r) := by
      rw [tailZ_eq]
      exact htailYZMeas.union
        (htailYZMeas.preimage
          flipY_measurableEmbedding.measurable)
    have hz :
        IntegrableOn (integrandLocal p q r)
          (flipZ ⁻¹' tailZ p q r) :=
      hzcomp.congr_fun
        (fun z hz => integrandLocal_flipZ p q r z)
        (htailZMeas.preimage
          flipZ_measurableEmbedding.measurable)
    rw [tailAll_eq]
    exact hzpos.union hz

private theorem angleLIntegral_pos (a b : ℝ) :
    0 < angleLIntegral a b := by
  unfold angleLIntegral
  rw [setLIntegral_pos_iff (measurable_angleKernel a b)]
  have hvol :
      0 < (volume : Measure ℝ)
        (Ioo (0 : ℝ) (Real.pi / 2)) := by
    simp [Real.pi_pos]
  refine hvol.trans_le (measure_mono ?_)
  intro theta htheta
  have hcos : 0 < Real.cos theta :=
    Real.cos_pos_of_mem_Ioo
      ⟨by linarith [htheta.1, Real.pi_pos],
        htheta.2⟩
  have hsin : 0 < Real.sin theta :=
    Real.sin_pos_of_pos_of_lt_pi htheta.1
      (by linarith [htheta.2, Real.pi_pos])
  refine ⟨?_, htheta⟩
  change angleKernel a b theta ≠ 0
  exact ne_of_gt ((ENNReal.mul_pos_iff).2
    ⟨ENNReal.ofReal_pos.2
        (Real.rpow_pos_of_pos hcos _),
      ENNReal.ofReal_pos.2
        (Real.rpow_pos_of_pos hsin _)⟩)

private theorem betaFnLocal_pos
    (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    0 < betaFnLocal x y := by
  have hangle := angleLIntegral_pos (2 * y) (2 * x)
  rw [angleLIntegral_eq_beta
    (2 * y) (2 * x)
    (mul_pos (by norm_num) hy)
    (mul_pos (by norm_num) hx)] at hangle
  have hargx : (2 * x) / 2 = x := by ring
  have hargy : (2 * y) / 2 = y := by ring
  rw [hargx, hargy, ENNReal.ofReal_pos] at hangle
  nlinarith

private theorem omegaTail_integrable_iff
    (p q r : ℝ) (hp : 0 < p) (hq : 0 < q) (hr : 0 < r) :
    IntegrableOn (integrandLocal p q r)
        (omegaTailLocal p q r) ↔
      1 / p + 1 / q + 1 / r < 1 := by
  let C : ℝ :=
    2 / (p * q * r) *
      betaFnLocal (1 / r) (1 / p + 1 / q) *
      betaFnLocal (1 / q) (1 / p)
  have hpqr : 0 < p * q * r :=
    mul_pos (mul_pos hp hq) hr
  have hCpos : 0 < C := by
    dsimp [C]
    exact mul_pos
      (mul_pos
        (div_pos (by norm_num) hpqr)
        (betaFnLocal_pos _ _
          (one_div_pos.mpr hr)
          (add_pos (one_div_pos.mpr hp)
            (one_div_pos.mpr hq))))
      (betaFnLocal_pos _ _
        (one_div_pos.mpr hq)
        (one_div_pos.mpr hp))
  have htailFinite :
      ((∫⁻ z in omegaTailLocal p q r,
          ENNReal.ofReal (integrandLocal p q r z)) ≠ ∞) ↔
        IntegrableOn (integrandLocal p q r)
          (omegaTailLocal p q r) := by
    exact lintegral_ofReal_ne_top_iff_integrable
      (integrandLocal_measurable p q r).aestronglyMeasurable
      (Filter.Eventually.of_forall
        (integrandLocal_nonneg p q r))
  have hradFinite :
      ((∫⁻ R in Ioi (Real.sqrt 3),
          radialKernel p q r R) ≠ ∞) ↔
        2 / p + 2 / q + 2 / r - 3 < -1 := by
    have hnonneg :
        0 ≤ᵐ[volume.restrict (Ioi (Real.sqrt 3))]
          radialWeightLocal p q r :=
      ae_restrict_of_forall_mem measurableSet_Ioi
        (fun R hR =>
          radialWeightLocal_nonneg p q r R
            (le_trans (Real.sqrt_nonneg 3) hR.le))
    calc
      ((∫⁻ R in Ioi (Real.sqrt 3),
          radialKernel p q r R) ≠ ∞) ↔
          IntegrableOn (radialWeightLocal p q r)
            (Ioi (Real.sqrt 3)) := by
        convert lintegral_ofReal_ne_top_iff_integrable
          (radialWeightLocal_measurable p q r).aestronglyMeasurable
          hnonneg using 1
      _ ↔ 2 / p + 2 / q + 2 / r - 3 < -1 := by
        simpa [radialWeightLocal] using
          (integrableOn_Ioi_rpow_iff
            (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 3))
            (s := 2 / p + 2 / q + 2 / r - 3))
  have hproduct :
      (ENNReal.ofReal C *
          ∫⁻ R in Ioi (Real.sqrt 3),
            radialKernel p q r R) ≠ ∞ ↔
        (∫⁻ R in Ioi (Real.sqrt 3),
          radialKernel p q r R) ≠ ∞ := by
    constructor
    · intro h
      exact (ENNReal.lt_top_of_mul_ne_top_right h
        ((ENNReal.ofReal_ne_zero_iff).2 hCpos)).ne
    · intro h
      exact ENNReal.mul_ne_top (by finiteness) h
  rw [← htailFinite,
    omegaTail_lintegral_beta p q r hp hq hr]
  change
    (ENNReal.ofReal C *
        ∫⁻ R in Ioi (Real.sqrt 3),
          radialKernel p q r R) ≠ ∞ ↔ _
  rw [hproduct, hradFinite]
  have hexp :
      2 / p + 2 / q + 2 / r - 3 =
        2 * (1 / p + 1 / q + 1 / r) - 3 := by
    ring
  rw [hexp]
  constructor <;> intro h <;> linarith

private def exteriorLocal : Set Point3 :=
  {z | 1 < |z.1| + |z.2.1| + |z.2.2|}

private noncomputable def nearAll
    (p q r : ℝ) : Set Point3 :=
  {z | z ∈ exteriorLocal ∧
    denominatorLocal p q r z ≤ 3}

private theorem exteriorLocal_measurable :
    MeasurableSet exteriorLocal := by
  unfold exteriorLocal
  exact measurableSet_lt measurable_const
    (((continuous_abs.measurable.comp measurable_fst).add
      (continuous_abs.measurable.comp
        (measurable_fst.comp measurable_snd))).add
      (continuous_abs.measurable.comp
        (measurable_snd.comp measurable_snd)))

private theorem nearAll_measurable (p q r : ℝ) :
    MeasurableSet (nearAll p q r) := by
  unfold nearAll
  exact exteriorLocal_measurable.inter
    (measurableSet_le
      (denominatorLocal_measurable p q r) measurable_const)

private theorem nearAll_integrable
    (p q r : ℝ) (hp : 0 < p) (hq : 0 < q) (hr : 0 < r) :
    IntegrableOn (integrandLocal p q r) (nearAll p q r) := by
  let Bp : ℝ := Real.rpow 3 p⁻¹
  let Bq : ℝ := Real.rpow 3 q⁻¹
  let Br : ℝ := Real.rpow 3 r⁻¹
  let box : Set Point3 :=
    Icc (-Bp) Bp ×ˢ (Icc (-Bq) Bq ×ˢ Icc (-Br) Br)
  have hsubset : nearAll p q r ⊆ box := by
    intro z hz
    change z ∈ exteriorLocal ∧
      denominatorLocal p q r z ≤ 3 at hz
    have hden := hz.2
    unfold denominatorLocal at hden
    have hxp :
        Real.rpow |z.1| p ≤ 3 := by
      have hy := Real.rpow_nonneg (abs_nonneg z.2.1) q
      have hz' := Real.rpow_nonneg (abs_nonneg z.2.2) r
      exact (calc
        Real.rpow |z.1| p ≤
            Real.rpow |z.1| p +
              Real.rpow |z.2.1| q :=
          le_add_of_nonneg_right hy
        _ ≤ Real.rpow |z.1| p +
              Real.rpow |z.2.1| q +
              Real.rpow |z.2.2| r :=
          le_add_of_nonneg_right hz'
        _ ≤ 3 := hden)
    have hyq :
        Real.rpow |z.2.1| q ≤ 3 := by
      have hx := Real.rpow_nonneg (abs_nonneg z.1) p
      have hz' := Real.rpow_nonneg (abs_nonneg z.2.2) r
      exact (calc
        Real.rpow |z.2.1| q ≤
            Real.rpow |z.1| p +
              Real.rpow |z.2.1| q :=
          le_add_of_nonneg_left hx
        _ ≤ Real.rpow |z.1| p +
              Real.rpow |z.2.1| q +
              Real.rpow |z.2.2| r :=
          le_add_of_nonneg_right hz'
        _ ≤ 3 := hden)
    have hzr :
        Real.rpow |z.2.2| r ≤ 3 := by
      have hx := Real.rpow_nonneg (abs_nonneg z.1) p
      have hy := Real.rpow_nonneg (abs_nonneg z.2.1) q
      exact (calc
        Real.rpow |z.2.2| r ≤
            (Real.rpow |z.1| p +
              Real.rpow |z.2.1| q) +
              Real.rpow |z.2.2| r :=
          le_add_of_nonneg_left (add_nonneg hx hy)
        _ ≤ 3 := hden)
    have hxabs : |z.1| ≤ Bp := by
      dsimp [Bp]
      exact (Real.le_rpow_inv_iff_of_pos
        (abs_nonneg z.1) (by norm_num) hp).2 hxp
    have hyabs : |z.2.1| ≤ Bq := by
      dsimp [Bq]
      exact (Real.le_rpow_inv_iff_of_pos
        (abs_nonneg z.2.1) (by norm_num) hq).2 hyq
    have hzabs : |z.2.2| ≤ Br := by
      dsimp [Br]
      exact (Real.le_rpow_inv_iff_of_pos
        (abs_nonneg z.2.2) (by norm_num) hr).2 hzr
    exact
      ⟨(abs_le.mp hxabs),
        (abs_le.mp hyabs),
        (abs_le.mp hzabs)⟩
  have hboxCompact : IsCompact box := by
    dsimp [box]
    exact isCompact_Icc.prod
      (isCompact_Icc.prod isCompact_Icc)
  have hnearFinite :
      (volume : Measure Point3) (nearAll p q r) < ∞ :=
    (measure_mono hsubset).trans_lt hboxCompact.measure_lt_top
  let delta : ℝ :=
    min (Real.rpow (1 / 3 : ℝ) p)
      (min (Real.rpow (1 / 3 : ℝ) q)
        (Real.rpow (1 / 3 : ℝ) r))
  have hdelta : 0 < delta := by
    dsimp [delta]
    exact lt_min
      (Real.rpow_pos_of_pos (by norm_num) _)
      (lt_min
        (Real.rpow_pos_of_pos (by norm_num) _)
        (Real.rpow_pos_of_pos (by norm_num) _))
  apply IntegrableOn.of_bound hnearFinite
    (integrandLocal_measurable p q r).aestronglyMeasurable
    (1 / delta)
  filter_upwards
    [ae_restrict_mem (nearAll_measurable p q r)] with z hz
  change z ∈ exteriorLocal ∧
    denominatorLocal p q r z ≤ 3 at hz
  rw [Real.norm_eq_abs,
    abs_of_nonneg (integrandLocal_nonneg p q r z)]
  apply one_div_le_one_div_of_le hdelta
  have hlarge :
      (1 / 3 : ℝ) < |z.1| ∨
        (1 / 3 : ℝ) < |z.2.1| ∨
        (1 / 3 : ℝ) < |z.2.2| := by
    by_contra h
    push_neg at h
    have hext :
        1 < |z.1| + |z.2.1| + |z.2.2| := hz.1
    linarith [h.1, h.2.1, h.2.2]
  rcases hlarge with hx | hy | hz'
  · have hpw :
        Real.rpow (1 / 3 : ℝ) p ≤
          Real.rpow |z.1| p :=
      Real.rpow_le_rpow (by norm_num) hx.le hp.le
    have hd :
        delta ≤ Real.rpow |z.1| p :=
      (min_le_left _ _).trans hpw
    have hy0 := Real.rpow_nonneg (abs_nonneg z.2.1) q
    have hz0 := Real.rpow_nonneg (abs_nonneg z.2.2) r
    unfold denominatorLocal
    exact hd.trans (calc
      Real.rpow |z.1| p ≤
          Real.rpow |z.1| p +
            Real.rpow |z.2.1| q :=
        le_add_of_nonneg_right hy0
      _ ≤ Real.rpow |z.1| p +
            Real.rpow |z.2.1| q +
            Real.rpow |z.2.2| r :=
        le_add_of_nonneg_right hz0)
  · have hpw :
        Real.rpow (1 / 3 : ℝ) q ≤
          Real.rpow |z.2.1| q :=
      Real.rpow_le_rpow (by norm_num) hy.le hq.le
    have hd :
        delta ≤ Real.rpow |z.2.1| q :=
      (min_le_right _ _).trans
        ((min_le_left _ _).trans hpw)
    have hx0 := Real.rpow_nonneg (abs_nonneg z.1) p
    have hz0 := Real.rpow_nonneg (abs_nonneg z.2.2) r
    unfold denominatorLocal
    exact hd.trans (calc
      Real.rpow |z.2.1| q ≤
          Real.rpow |z.1| p +
            Real.rpow |z.2.1| q :=
        le_add_of_nonneg_left hx0
      _ ≤ Real.rpow |z.1| p +
            Real.rpow |z.2.1| q +
            Real.rpow |z.2.2| r :=
        le_add_of_nonneg_right hz0)
  · have hpw :
        Real.rpow (1 / 3 : ℝ) r ≤
          Real.rpow |z.2.2| r :=
      Real.rpow_le_rpow (by norm_num) hz'.le hr.le
    have hd :
        delta ≤ Real.rpow |z.2.2| r :=
      (min_le_right _ _).trans
        ((min_le_right _ _).trans hpw)
    have hx0 := Real.rpow_nonneg (abs_nonneg z.1) p
    have hy0 := Real.rpow_nonneg (abs_nonneg z.2.1) q
    unfold denominatorLocal
    exact hd.trans
      (le_add_of_nonneg_left (add_nonneg hx0 hy0))

private theorem tailAll_subset_exterior
    (p q r : ℝ) (hp : 0 < p) (hq : 0 < q) (hr : 0 < r) :
    tailAll p q r ⊆ exteriorLocal := by
  intro z hz
  by_contra h
  have hsum :
      |z.1| + |z.2.1| + |z.2.2| ≤ 1 :=
    not_lt.mp h
  have hxle : |z.1| ≤ 1 := by
    linarith [abs_nonneg z.2.1, abs_nonneg z.2.2]
  have hyle : |z.2.1| ≤ 1 := by
    linarith [abs_nonneg z.1, abs_nonneg z.2.2]
  have hzle : |z.2.2| ≤ 1 := by
    linarith [abs_nonneg z.1, abs_nonneg z.2.1]
  have hxp :
      Real.rpow |z.1| p ≤ 1 :=
    Real.rpow_le_one (abs_nonneg z.1) hxle hp.le
  have hyq :
      Real.rpow |z.2.1| q ≤ 1 :=
    Real.rpow_le_one (abs_nonneg z.2.1) hyle hq.le
  have hzr :
      Real.rpow |z.2.2| r ≤ 1 :=
    Real.rpow_le_one (abs_nonneg z.2.2) hzle hr.le
  have hden : denominatorLocal p q r z ≤ 3 := by
    unfold denominatorLocal
    linarith [hxp, hyq, hzr]
  exact (not_lt_of_ge hden) hz

private theorem exterior_eq_near_union_tail
    (p q r : ℝ) (hp : 0 < p) (hq : 0 < q) (hr : 0 < r) :
    exteriorLocal = nearAll p q r ∪ tailAll p q r := by
  ext z
  constructor
  · intro hz
    by_cases hd : denominatorLocal p q r z ≤ 3
    · exact Or.inl ⟨hz, hd⟩
    · exact Or.inr (lt_of_not_ge hd)
  · rintro (hz | hz)
    · exact hz.1
    · exact tailAll_subset_exterior p q r hp hq hr hz

private theorem exterior_integrable_iff
    (p q r : ℝ) (hp : 0 < p) (hq : 0 < q) (hr : 0 < r) :
    IntegrableOn (integrandLocal p q r) exteriorLocal ↔
      1 / p + 1 / q + 1 / r < 1 := by
  constructor
  · intro h
    have htail :
        IntegrableOn (integrandLocal p q r) (tailAll p q r) :=
      h.mono_set (tailAll_subset_exterior p q r hp hq hr)
    exact (omegaTail_integrable_iff p q r hp hq hr).1
      ((tailAll_integrable_iff_omegaTail p q r).1 htail)
  · intro hcond
    have htail :
        IntegrableOn (integrandLocal p q r) (tailAll p q r) :=
      (tailAll_integrable_iff_omegaTail p q r).2
        ((omegaTail_integrable_iff p q r hp hq hr).2 hcond)
    rw [exterior_eq_near_union_tail p q r hp hq hr]
    exact (nearAll_integrable p q r hp hq hr).union htail

private def positivePart (S : Set Point3) : Set Point3 :=
  S ∩ (Ici (0 : ℝ) ×ˢ
    (Ici (0 : ℝ) ×ˢ Ici (0 : ℝ)))

private def yzPart (S : Set Point3) : Set Point3 :=
  S ∩ (univ ×ˢ
    (Ici (0 : ℝ) ×ˢ Ici (0 : ℝ)))

private def zPart (S : Set Point3) : Set Point3 :=
  S ∩ (univ ×ˢ
    (univ ×ˢ Ici (0 : ℝ)))

private theorem positivePart_measurable
    {S : Set Point3} (hS : MeasurableSet S) :
    MeasurableSet (positivePart S) := by
  exact hS.inter
    (measurableSet_Ici.prod
      (measurableSet_Ici.prod measurableSet_Ici))

private theorem yzPart_measurable
    {S : Set Point3} (hS : MeasurableSet S) :
    MeasurableSet (yzPart S) := by
  exact hS.inter
    ((MeasurableSet.univ : MeasurableSet (univ : Set ℝ)).prod
      (measurableSet_Ici.prod measurableSet_Ici))

private theorem zPart_measurable
    {S : Set Point3} (hS : MeasurableSet S) :
    MeasurableSet (zPart S) := by
  exact hS.inter
    ((MeasurableSet.univ : MeasurableSet (univ : Set ℝ)).prod
      ((MeasurableSet.univ : MeasurableSet (univ : Set ℝ)).prod
        measurableSet_Ici))

private theorem coordinatePlaneX_null :
    (volume : Measure Point3) {z | z.1 = 0} = 0 := by
  have h :
      ∀ᵐ z ∂(volume : Measure Point3), z.1 ≠ 0 :=
    off_coordinate_planes_ae.mono (fun z hz => hz.1)
  simpa only [not_ne_iff] using (ae_iff.mp h)

private theorem coordinatePlaneY_null :
    (volume : Measure Point3) {z | z.2.1 = 0} = 0 := by
  have h :
      ∀ᵐ z ∂(volume : Measure Point3), z.2.1 ≠ 0 :=
    off_coordinate_planes_ae.mono (fun z hz => hz.2.1)
  simpa only [not_ne_iff] using (ae_iff.mp h)

private theorem coordinatePlaneZ_null :
    (volume : Measure Point3) {z | z.2.2 = 0} = 0 := by
  have h :
      ∀ᵐ z ∂(volume : Measure Point3), z.2.2 ≠ 0 :=
    off_coordinate_planes_ae.mono (fun z hz => hz.2.2)
  simpa only [not_ne_iff] using (ae_iff.mp h)

private theorem yzPart_union
    (S : Set Point3)
    (hSx : ∀ z, flipX z ∈ S ↔ z ∈ S) :
    yzPart S =
      positivePart S ∪ flipX ⁻¹' positivePart S := by
  ext z
  simp only [yzPart, positivePart, mem_inter_iff,
    mem_prod, mem_Ici, mem_univ, true_and,
    mem_union, mem_preimage]
  rw [hSx z]
  constructor
  · intro h
    by_cases hx : 0 ≤ z.1
    · exact Or.inl ⟨h.1, hx, h.2.1, h.2.2⟩
    · exact Or.inr
        ⟨h.1, by simpa [flipX] using (not_le.mp hx).le,
          h.2.1, h.2.2⟩
  · rintro (h | h)
    · exact ⟨h.1, h.2.2.1, h.2.2.2⟩
    · exact ⟨h.1, h.2.2.1, h.2.2.2⟩

private theorem zPart_union
    (S : Set Point3)
    (hSy : ∀ z, flipY z ∈ S ↔ z ∈ S) :
    zPart S =
      yzPart S ∪ flipY ⁻¹' yzPart S := by
  ext z
  simp only [zPart, yzPart, mem_inter_iff,
    mem_prod, mem_Ici, mem_univ, true_and,
    mem_union, mem_preimage]
  rw [hSy z]
  constructor
  · intro h
    by_cases hy : 0 ≤ z.2.1
    · exact Or.inl ⟨h.1, hy, h.2⟩
    · exact Or.inr
        ⟨h.1, by simpa [flipY] using (not_le.mp hy).le,
          h.2⟩
  · rintro (h | h)
    · exact ⟨h.1, h.2.2⟩
    · exact ⟨h.1, h.2.2⟩

private theorem univPart_union
    (S : Set Point3)
    (hSz : ∀ z, flipZ z ∈ S ↔ z ∈ S) :
    S = zPart S ∪ flipZ ⁻¹' zPart S := by
  ext z
  simp only [zPart, mem_inter_iff, mem_prod,
    mem_Ici, mem_univ, true_and,
    mem_union, mem_preimage]
  rw [hSz z]
  constructor
  · intro h
    by_cases hz : 0 ≤ z.2.2
    · exact Or.inl ⟨h, hz⟩
    · exact Or.inr
        ⟨h, by simpa [flipZ] using (not_le.mp hz).le⟩
  · rintro (h | h) <;> exact h.1

private theorem setIntegral_eq_eight_positivePart
    (S : Set Point3) (hSmeas : MeasurableSet S)
    (f : Point3 → ℝ)
    (hSx : ∀ z, flipX z ∈ S ↔ z ∈ S)
    (hSy : ∀ z, flipY z ∈ S ↔ z ∈ S)
    (hSz : ∀ z, flipZ z ∈ S ↔ z ∈ S)
    (hfx : ∀ z, f (flipX z) = f z)
    (hfy : ∀ z, f (flipY z) = f z)
    (hfz : ∀ z, f (flipZ z) = f z)
    (hfInt : IntegrableOn f S) :
    (∫ z in S, f z) =
      8 * ∫ z in positivePart S, f z := by
  have hPmeas : MeasurableSet (positivePart S) :=
    positivePart_measurable hSmeas
  have hYZmeas : MeasurableSet (yzPart S) :=
    yzPart_measurable hSmeas
  have hZmeas : MeasurableSet (zPart S) :=
    zPart_measurable hSmeas
  have hPXmeas :
      MeasurableSet (flipX ⁻¹' positivePart S) :=
    hPmeas.preimage flipX_measurableEmbedding.measurable
  have hYZYmeas :
      MeasurableSet (flipY ⁻¹' yzPart S) :=
    hYZmeas.preimage flipY_measurableEmbedding.measurable
  have hZZmeas :
      MeasurableSet (flipZ ⁻¹' zPart S) :=
    hZmeas.preimage flipZ_measurableEmbedding.measurable
  have hPInt : IntegrableOn f (positivePart S) :=
    hfInt.mono_set inter_subset_left
  have hPXsub :
      flipX ⁻¹' positivePart S ⊆ S := by
    intro z hz
    exact (hSx z).1 hz.1
  have hPXInt :
      IntegrableOn f (flipX ⁻¹' positivePart S) :=
    hfInt.mono_set hPXsub
  have hYZInt : IntegrableOn f (yzPart S) :=
    hfInt.mono_set inter_subset_left
  have hYZYsub :
      flipY ⁻¹' yzPart S ⊆ S := by
    intro z hz
    exact (hSy z).1 hz.1
  have hYZYInt :
      IntegrableOn f (flipY ⁻¹' yzPart S) :=
    hfInt.mono_set hYZYsub
  have hZInt : IntegrableOn f (zPart S) :=
    hfInt.mono_set inter_subset_left
  have hZZsub :
      flipZ ⁻¹' zPart S ⊆ S := by
    intro z hz
    exact (hSz z).1 hz.1
  have hZZInt :
      IntegrableOn f (flipZ ⁻¹' zPart S) :=
    hfInt.mono_set hZZsub
  have hdX :
      AEDisjoint (volume : Measure Point3)
        (positivePart S) (flipX ⁻¹' positivePart S) := by
    change (volume : Measure Point3)
      (positivePart S ∩ flipX ⁻¹' positivePart S) = 0
    apply measure_mono_null _ coordinatePlaneX_null
    intro z hz
    rcases hz with ⟨h₁, h₂⟩
    change z ∈ S ∧
      0 ≤ z.1 ∧ 0 ≤ z.2.1 ∧ 0 ≤ z.2.2 at h₁
    change flipX z ∈ S ∧
      0 ≤ (flipX z).1 ∧
        0 ≤ (flipX z).2.1 ∧
        0 ≤ (flipX z).2.2 at h₂
    change z.1 = 0
    dsimp [flipX] at h₂
    linarith [h₁.2.1, h₂.2.1]
  have hdY :
      AEDisjoint (volume : Measure Point3)
        (yzPart S) (flipY ⁻¹' yzPart S) := by
    change (volume : Measure Point3)
      (yzPart S ∩ flipY ⁻¹' yzPart S) = 0
    apply measure_mono_null _ coordinatePlaneY_null
    intro z hz
    rcases hz with ⟨h₁, h₂⟩
    change flipY z ∈ yzPart S at h₂
    simp only [yzPart, mem_inter_iff, mem_prod,
      mem_univ, true_and, mem_Ici] at h₁ h₂
    change z.2.1 = 0
    dsimp [flipY] at h₂
    linarith [h₁.2.1, h₂.2.1]
  have hdZ :
      AEDisjoint (volume : Measure Point3)
        (zPart S) (flipZ ⁻¹' zPart S) := by
    change (volume : Measure Point3)
      (zPart S ∩ flipZ ⁻¹' zPart S) = 0
    apply measure_mono_null _ coordinatePlaneZ_null
    intro z hz
    rcases hz with ⟨h₁, h₂⟩
    change flipZ z ∈ zPart S at h₂
    simp only [zPart, mem_inter_iff, mem_prod,
      mem_univ, true_and, mem_Ici] at h₁ h₂
    change z.2.2 = 0
    dsimp [flipZ] at h₂
    linarith [h₁.2, h₂.2]
  have hIX :
      (∫ z in flipX ⁻¹' positivePart S, f z) =
        ∫ z in positivePart S, f z := by
    calc
      (∫ z in flipX ⁻¹' positivePart S, f z) =
          ∫ z in flipX ⁻¹' positivePart S,
            f (flipX z) := by
        apply setIntegral_congr_fun hPXmeas
        intro z hz
        exact (hfx z).symm
      _ = ∫ z in positivePart S, f z :=
        flipX_measurePreserving.setIntegral_preimage_emb
          flipX_measurableEmbedding f (positivePart S)
  have hIY :
      (∫ z in flipY ⁻¹' yzPart S, f z) =
        ∫ z in yzPart S, f z := by
    calc
      (∫ z in flipY ⁻¹' yzPart S, f z) =
          ∫ z in flipY ⁻¹' yzPart S,
            f (flipY z) := by
        apply setIntegral_congr_fun hYZYmeas
        intro z hz
        exact (hfy z).symm
      _ = ∫ z in yzPart S, f z :=
        flipY_measurePreserving.setIntegral_preimage_emb
          flipY_measurableEmbedding f (yzPart S)
  have hIZ :
      (∫ z in flipZ ⁻¹' zPart S, f z) =
        ∫ z in zPart S, f z := by
    calc
      (∫ z in flipZ ⁻¹' zPart S, f z) =
          ∫ z in flipZ ⁻¹' zPart S,
            f (flipZ z) := by
        apply setIntegral_congr_fun hZZmeas
        intro z hz
        exact (hfz z).symm
      _ = ∫ z in zPart S, f z :=
        flipZ_measurePreserving.setIntegral_preimage_emb
          flipZ_measurableEmbedding f (zPart S)
  have hIYZ :
      (∫ z in yzPart S, f z) =
        2 * ∫ z in positivePart S, f z := by
    rw [yzPart_union S hSx,
      setIntegral_union₀ hdX hPXmeas.nullMeasurableSet
        hPInt hPXInt, hIX]
    ring
  have hIZPart :
      (∫ z in zPart S, f z) =
        4 * ∫ z in positivePart S, f z := by
    rw [zPart_union S hSy,
      setIntegral_union₀ hdY hYZYmeas.nullMeasurableSet
        hYZInt hYZYInt, hIY, hIYZ]
    ring
  nth_rewrite 1 [univPart_union S hSz]
  rw [setIntegral_union₀ hdZ hZZmeas.nullMeasurableSet
      hZInt hZZInt, hIZ, hIZPart]
  ring

private noncomputable def omegaNearLocal
    (p q r : ℝ) : Set Point3 :=
  {z | 0 ≤ z.1 ∧ 0 ≤ z.2.1 ∧ 0 ≤ z.2.2 ∧
    1 < z.1 + z.2.1 + z.2.2 ∧
    denominatorLocal p q r z ≤ 3}

private theorem tailAll_measurable (p q r : ℝ) :
    MeasurableSet (tailAll p q r) := by
  unfold tailAll
  exact measurableSet_lt measurable_const
    (denominatorLocal_measurable p q r)

private theorem tailAll_flipX (p q r : ℝ) (z : Point3) :
    flipX z ∈ tailAll p q r ↔ z ∈ tailAll p q r := by
  simp [tailAll, denominatorLocal, flipX]

private theorem tailAll_flipY (p q r : ℝ) (z : Point3) :
    flipY z ∈ tailAll p q r ↔ z ∈ tailAll p q r := by
  simp [tailAll, denominatorLocal, flipY]

private theorem tailAll_flipZ (p q r : ℝ) (z : Point3) :
    flipZ z ∈ tailAll p q r ↔ z ∈ tailAll p q r := by
  simp [tailAll, denominatorLocal, flipZ]

private theorem nearAll_flipX (p q r : ℝ) (z : Point3) :
    flipX z ∈ nearAll p q r ↔ z ∈ nearAll p q r := by
  simp [nearAll, exteriorLocal, denominatorLocal, flipX]

private theorem nearAll_flipY (p q r : ℝ) (z : Point3) :
    flipY z ∈ nearAll p q r ↔ z ∈ nearAll p q r := by
  simp [nearAll, exteriorLocal, denominatorLocal, flipY]

private theorem nearAll_flipZ (p q r : ℝ) (z : Point3) :
    flipZ z ∈ nearAll p q r ↔ z ∈ nearAll p q r := by
  simp [nearAll, exteriorLocal, denominatorLocal, flipZ]

private theorem positivePart_tailAll
    (p q r : ℝ) :
    positivePart (tailAll p q r) =
      omegaTailLocal p q r := by
  ext z
  simp only [positivePart, tailAll, omegaTailLocal,
    mem_inter_iff, mem_prod, mem_Ici, mem_setOf_eq]
  constructor
  · intro h
    exact ⟨h.2.1, h.2.2.1, h.2.2.2, h.1⟩
  · intro h
    exact ⟨h.2.2.2, h.1, h.2.1, h.2.2.1⟩

private theorem positivePart_nearAll
    (p q r : ℝ) :
    positivePart (nearAll p q r) =
      omegaNearLocal p q r := by
  ext z
  simp only [positivePart, nearAll, omegaNearLocal,
    mem_inter_iff, mem_prod, mem_Ici, mem_setOf_eq]
  constructor
  · intro h
    have hx : |z.1| = z.1 := abs_of_nonneg h.2.1
    have hy : |z.2.1| = z.2.1 := abs_of_nonneg h.2.2.1
    have hz : |z.2.2| = z.2.2 := abs_of_nonneg h.2.2.2
    exact
      ⟨h.2.1, h.2.2.1, h.2.2.2,
        by simpa [exteriorLocal, hx, hy, hz] using h.1.1,
        h.1.2⟩
  · intro h
    have hx : |z.1| = z.1 := abs_of_nonneg h.1
    have hy : |z.2.1| = z.2.1 := abs_of_nonneg h.2.1
    have hz : |z.2.2| = z.2.2 := abs_of_nonneg h.2.2.1
    exact
      ⟨⟨by simpa [exteriorLocal, hx, hy, hz] using h.2.2.2.1,
          h.2.2.2.2⟩,
        h.1, h.2.1, h.2.2.1⟩

private theorem exterior_integral_split_eight
    (p q r : ℝ) (hp : 0 < p) (hq : 0 < q) (hr : 0 < r)
    (hcond : 1 / p + 1 / q + 1 / r < 1) :
    (∫ z in exteriorLocal, integrandLocal p q r z) =
      8 * (∫ z in omegaNearLocal p q r,
        integrandLocal p q r z) +
      8 * (∫ z in omegaTailLocal p q r,
        integrandLocal p q r z) := by
  have hnear := nearAll_integrable p q r hp hq hr
  have htail :
      IntegrableOn (integrandLocal p q r) (tailAll p q r) :=
    (tailAll_integrable_iff_omegaTail p q r).2
      ((omegaTail_integrable_iff p q r hp hq hr).2 hcond)
  have hnearSym :
      (∫ z in nearAll p q r, integrandLocal p q r z) =
        8 * ∫ z in omegaNearLocal p q r,
          integrandLocal p q r z := by
    rw [← positivePart_nearAll p q r]
    exact setIntegral_eq_eight_positivePart
      (nearAll p q r) (nearAll_measurable p q r)
      (integrandLocal p q r)
      (nearAll_flipX p q r)
      (nearAll_flipY p q r)
      (nearAll_flipZ p q r)
      (integrandLocal_flipX p q r)
      (integrandLocal_flipY p q r)
      (integrandLocal_flipZ p q r)
      hnear
  have htailSym :
      (∫ z in tailAll p q r, integrandLocal p q r z) =
        8 * ∫ z in omegaTailLocal p q r,
          integrandLocal p q r z := by
    rw [← positivePart_tailAll p q r]
    exact setIntegral_eq_eight_positivePart
      (tailAll p q r) (tailAll_measurable p q r)
      (integrandLocal p q r)
      (tailAll_flipX p q r)
      (tailAll_flipY p q r)
      (tailAll_flipZ p q r)
      (integrandLocal_flipX p q r)
      (integrandLocal_flipY p q r)
      (integrandLocal_flipZ p q r)
      htail
  have hdisj :
      Disjoint (nearAll p q r) (tailAll p q r) := by
    apply Set.disjoint_left.2
    intro z hn ht
    exact (not_lt_of_ge hn.2) ht
  calc
    (∫ z in exteriorLocal, integrandLocal p q r z) =
        ∫ z in nearAll p q r ∪ tailAll p q r,
          integrandLocal p q r z := by
      rw [← exterior_eq_near_union_tail p q r hp hq hr]
    _ = (∫ z in nearAll p q r,
          integrandLocal p q r z) +
        ∫ z in tailAll p q r,
          integrandLocal p q r z :=
      setIntegral_union hdisj (tailAll_measurable p q r)
        hnear htail
    _ = 8 * (∫ z in omegaNearLocal p q r,
          integrandLocal p q r z) +
        8 * (∫ z in omegaTailLocal p q r,
          integrandLocal p q r z) := by
      rw [hnearSym, htailSym]

def exteriorDiamond : Set (ℝ × ℝ × ℝ) :=
  {z | 1 < |z.1| + |z.2.1| + |z.2.2|}

def denominator (p q r : ℝ) (z : ℝ × ℝ × ℝ) : ℝ :=
  Real.rpow |z.1| p + Real.rpow |z.2.1| q +
    Real.rpow |z.2.2| r

def integrand (p q r : ℝ) (z : ℝ × ℝ × ℝ) : ℝ :=
  1 / denominator p q r z

def omegaNear (p q r : ℝ) : Set (ℝ × ℝ × ℝ) :=
  {z | 0 ≤ z.1 ∧ 0 ≤ z.2.1 ∧ 0 ≤ z.2.2 ∧
    1 < z.1 + z.2.1 + z.2.2 ∧ denominator p q r z ≤ 3}

def omegaTail (p q r : ℝ) : Set (ℝ × ℝ × ℝ) :=
  {z | 0 ≤ z.1 ∧ 0 ≤ z.2.1 ∧ 0 ≤ z.2.2 ∧
    3 < denominator p q r z}

def coordinateMap (p q r R phi psi : ℝ) : ℝ × ℝ × ℝ :=
  (Real.rpow R (2 / p) *
      Real.rpow (Real.cos phi) (2 / p) *
      Real.rpow (Real.cos psi) (2 / p),
    Real.rpow R (2 / q) *
      Real.rpow (Real.sin phi) (2 / q) *
      Real.rpow (Real.cos psi) (2 / q),
    Real.rpow R (2 / r) *
      Real.rpow (Real.sin psi) (2 / r))

def jacobianFactor (p q r R phi psi : ℝ) : ℝ :=
  8 / (p * q * r) *
    Real.rpow R (2 / p + 2 / q + 2 / r - 1) *
    Real.rpow (Real.cos phi) (2 / p - 1) *
    Real.rpow (Real.sin phi) (2 / q - 1) *
    Real.rpow (Real.sin psi) (2 / r - 1) *
    Real.rpow (Real.cos psi) (2 / p + 2 / q - 1)

def betaFn (x y : ℝ) : ℝ :=
  ∫ t in Set.Ioc (0 : ℝ) 1,
    Real.rpow t (x - 1) * Real.rpow (1 - t) (y - 1)

def radialWeight (p q r R : ℝ) : ℝ :=
  Real.rpow R (2 / p + 2 / q + 2 / r - 3)

theorem gap1 (p q r : ℝ)
    (hp : 0 < p) (hq : 0 < q) (hr : 0 < r)
    (hcond : 1 / p + 1 / q + 1 / r < 1) :
    (∫ z in exteriorDiamond, integrand p q r z) =
      8 * (∫ z in omegaNear p q r, integrand p q r z) +
        8 * (∫ z in omegaTail p q r, integrand p q r z) := by
  change
    (∫ z in exteriorLocal, integrandLocal p q r z) =
      8 * (∫ z in omegaNearLocal p q r,
        integrandLocal p q r z) +
      8 * (∫ z in omegaTailLocal p q r,
        integrandLocal p q r z)
  exact exterior_integral_split_eight p q r hp hq hr hcond

theorem gap2 (p q r : ℝ)
    (hp : 0 < p) (hq : 0 < q) (hr : 0 < r) :
    {z : ℝ × ℝ × ℝ |
      0 ≤ z.1 ∧ 0 ≤ z.2.1 ∧ 0 ≤ z.2.2 ∧
      1 < z.1 + z.2.1 + z.2.2 ∧
      3 < denominator p q r z} =
      omegaTail p q r := by
  change
    {z : Point3 |
      0 ≤ z.1 ∧ 0 ≤ z.2.1 ∧ 0 ≤ z.2.2 ∧
      1 < z.1 + z.2.1 + z.2.2 ∧
      3 < denominatorLocal p q r z} =
      omegaTailLocal p q r
  ext z
  constructor
  · intro h
    exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.2⟩
  · intro h
    have ht : z ∈ tailAll p q r := h.2.2.2
    have he :=
      tailAll_subset_exterior p q r hp hq hr ht
    have hsum :
        1 < z.1 + z.2.1 + z.2.2 := by
      simpa [exteriorLocal, abs_of_nonneg h.1,
        abs_of_nonneg h.2.1,
        abs_of_nonneg h.2.2.1] using he
    exact ⟨h.1, h.2.1, h.2.2.1, hsum, h.2.2.2⟩

theorem gap3 (p q r R phi psi : ℝ)
    (hp : 0 < p) (hq : 0 < q) (hr : 0 < r)
    (hR : 0 < R)
    (hphi0 : 0 < phi) (hphi1 : phi < Real.pi / 2)
    (hpsi0 : 0 < psi) (hpsi1 : psi < Real.pi / 2) :
    jacobianFactor p q r R phi psi =
      8 / (p * q * r) *
        Real.rpow R (2 / p + 2 / q + 2 / r - 1) *
        Real.rpow (Real.cos phi) (2 / p - 1) *
        Real.rpow (Real.sin phi) (2 / q - 1) *
        Real.rpow (Real.sin psi) (2 / r - 1) *
        Real.rpow (Real.cos psi) (2 / p + 2 / q - 1) := by
  rfl

theorem gap4 (p q r : ℝ)
    (hp : 0 < p) (hq : 0 < q) (hr : 0 < r)
    (hcond : 1 / p + 1 / q + 1 / r < 1) :
    (∫ z in omegaTail p q r, integrand p q r z) =
      2 / (p * q * r) *
        betaFn (1 / r) (1 / p + 1 / q) *
        betaFn (1 / q) (1 / p) *
        ∫ R in Set.Ioi (Real.sqrt 3), radialWeight p q r R := by
  change
    (∫ z in omegaTailLocal p q r,
        integrandLocal p q r z) =
      2 / (p * q * r) *
        betaFnLocal (1 / r) (1 / p + 1 / q) *
        betaFnLocal (1 / q) (1 / p) *
        ∫ R in Ioi (Real.sqrt 3),
          radialWeightLocal p q r R
  exact omegaTail_integral_beta p q r hp hq hr

theorem gap5 (p q r : ℝ)
    (hp : 0 < p) (hq : 0 < q) (hr : 0 < r) :
    IntegrableOn (integrand p q r) exteriorDiamond ↔
      1 / p + 1 / q + 1 / r < 1 := by
  change
    IntegrableOn (integrandLocal p q r) exteriorLocal ↔
      1 / p + 1 / q + 1 / r < 1
  exact exterior_integrable_iff p q r hp hq hr

end

end ProofGap.Exercise4193
