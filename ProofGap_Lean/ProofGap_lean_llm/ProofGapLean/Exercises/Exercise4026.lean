import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Data.Real.Sqrt
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise4026

noncomputable section

open MeasureTheory
open scoped Interval

def normalizedRadiusSq (a b x y : ℝ) : ℝ :=
  x ^ 2 / a ^ 2 + y ^ 2 / b ^ 2

def baseRegion (a b : ℝ) : Set (ℝ × ℝ) :=
  {p |
    normalizedRadiusSq a b p.1 p.2 ^ 2 ≤
      p.1 ^ 2 / a ^ 2 - p.2 ^ 2 / b ^ 2}

def upperSurface (c r : ℝ) : ℝ :=
  c * Real.sqrt (1 - r ^ 2)

def lowerSurface (c r : ℝ) : ℝ :=
  -c * Real.sqrt (1 - r ^ 2)

def volume (a b c : ℝ) : ℝ :=
  ∫ p in baseRegion a b,
    2 * c * Real.sqrt (1 - normalizedRadiusSq a b p.1 p.2)

def angularPrimitive (a b c φ : ℝ) : ℝ :=
  8 * a * b * c / 3 *
    (φ + Real.sqrt 8 * Real.cos φ -
      Real.sqrt 8 / 3 * Real.cos φ ^ 3)

theorem gap1 (c r : ℝ) :
    upperSurface c r = c * Real.sqrt (1 - r ^ 2) ∧
      lowerSurface c r = -c * Real.sqrt (1 - r ^ 2) := by
  exact ⟨rfl, rfl⟩

theorem gap2 (r φ : ℝ) (hr : r ≠ 0)
    (hboundary :
      r ^ 4 = r ^ 2 * (Real.cos φ ^ 2 - Real.sin φ ^ 2)) :
    r ^ 2 = Real.cos φ ^ 2 - Real.sin φ ^ 2 := by
  have hrsq : 0 < r ^ 2 := sq_pos_of_ne_zero hr
  nlinarith

theorem gap3 (φ : ℝ) :
    Real.cos φ ^ 2 - Real.sin φ ^ 2 = Real.cos (2 * φ) := by
  rw [Real.cos_two_mul]
  nlinarith [Real.sin_sq_add_cos_sq φ]

theorem gap4 (r φ : ℝ) (hr : r ≠ 0)
    (hboundary :
      r ^ 4 = r ^ 2 * (Real.cos φ ^ 2 - Real.sin φ ^ 2)) :
    r ^ 2 = Real.cos (2 * φ) := by
  rw [← gap3 φ]
  exact gap2 r φ hr hboundary

theorem gap5 (φ : ℝ)
    (hφ : φ ∈ Set.Icc (-Real.pi / 4) (5 * Real.pi / 4)) :
    0 ≤ Real.cos (2 * φ) ↔
      (-Real.pi / 4 ≤ φ ∧ φ ≤ Real.pi / 4) ∨
        (3 * Real.pi / 4 ≤ φ ∧ φ ≤ 5 * Real.pi / 4) := by
  constructor
  · intro hcos
    by_cases hleft : φ ≤ Real.pi / 4
    · exact Or.inl ⟨hφ.1, hleft⟩
    · by_cases hright : 3 * Real.pi / 4 ≤ φ
      · exact Or.inr ⟨hright, hφ.2⟩
      · have hmid :
            Real.pi / 4 < φ ∧ φ < 3 * Real.pi / 4 :=
          ⟨lt_of_not_ge hleft, lt_of_not_ge hright⟩
        have hneg : Real.cos (2 * φ) < 0 :=
          Real.cos_neg_of_pi_div_two_lt_of_lt
            (by linarith [hmid.1])
            (by linarith [hmid.2])
        linarith
  · rintro (hfirst | hsecond)
    · exact Real.cos_nonneg_of_neg_pi_div_two_le_of_le
        (by linarith [hfirst.1])
        (by linarith [hfirst.2])
    · rw [← Real.cos_sub_two_pi (2 * φ)]
      exact Real.cos_nonneg_of_neg_pi_div_two_le_of_le
        (by linarith [hsecond.1])
        (by linarith [hsecond.2])

private def diagCLM (a b : ℝ) : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
  (ContinuousLinearMap.lsmul ℝ ℝ a).prodMap
    (ContinuousLinearMap.lsmul ℝ ℝ b)

private theorem diag_det (a b : ℝ) : (diagCLM a b).det = a * b := by
  unfold diagCLM
  rw [ContinuousLinearMap.det, ContinuousLinearMap.coe_prodMap,
    LinearMap.det_prodMap]
  simp

private theorem integral_diag (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (g : ℝ × ℝ → ℝ) :
    (∫ p : ℝ × ℝ, g p) =
      a * b * ∫ q : ℝ × ℝ, g (a * q.1, b * q.2) := by
  let F : ℝ × ℝ → ℝ × ℝ := fun q => (a * q.1, b * q.2)
  have hinj : Function.Injective F := by
    rintro ⟨x, y⟩ ⟨x', y'⟩ h
    simp only [F, Prod.mk.injEq] at h
    ext
    · exact mul_left_cancel₀ (ne_of_gt ha) h.1
    · exact mul_left_cancel₀ (ne_of_gt hb) h.2
  have hsurj : Function.Surjective F := by
    rintro ⟨x, y⟩
    refine ⟨(x / a, y / b), ?_⟩
    simp only [F, Prod.mk.injEq]
    constructor <;> field_simp [ne_of_gt ha, ne_of_gt hb]
  have hchange :=
    MeasureTheory.integral_image_eq_integral_abs_det_fderiv_smul
      (MeasureTheory.volume : Measure (ℝ × ℝ))
      (s := Set.univ) MeasurableSet.univ
      (f := F) (f' := fun _ => diagCLM a b)
      (fun q _ => (diagCLM a b).hasFDerivAt.hasFDerivWithinAt)
      hinj.injOn g
  rw [Set.image_univ_of_surjective hsurj] at hchange
  simp only [MeasureTheory.setIntegral_univ, diag_det,
    abs_of_pos (mul_pos ha hb), smul_eq_mul, F] at hchange
  rw [MeasureTheory.integral_const_mul] at hchange
  exact hchange

private def unitBase : Set (ℝ × ℝ) :=
  {p | (p.1 ^ 2 + p.2 ^ 2) ^ 2 ≤ p.1 ^ 2 - p.2 ^ 2}

private def unitIntegrand (c : ℝ) (p : ℝ × ℝ) : ℝ :=
  2 * c * Real.sqrt (1 - (p.1 ^ 2 + p.2 ^ 2))

private def quadrant : Set (ℝ × ℝ) :=
  Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ)

private def unitQuadrantBase : Set (ℝ × ℝ) :=
  quadrant ∩ unitBase

private theorem unitBase_closed : IsClosed unitBase := by
  unfold unitBase
  exact isClosed_le (by fun_prop) (by fun_prop)

private theorem unitBase_compact : IsCompact unitBase := by
  have hsub :
      unitBase ⊆ Set.Icc (-1 : ℝ) 1 ×ˢ Set.Icc (-1 : ℝ) 1 := by
    rintro ⟨x, y⟩ hxy
    change (x ^ 2 + y ^ 2) ^ 2 ≤ x ^ 2 - y ^ 2 at hxy
    have hs0 : 0 ≤ x ^ 2 + y ^ 2 := by positivity
    have hdiff : x ^ 2 - y ^ 2 ≤ x ^ 2 + y ^ 2 := by
      nlinarith [sq_nonneg y]
    have hrad : x ^ 2 + y ^ 2 ≤ 1 := by
      by_contra h
      have hlt : 1 < x ^ 2 + y ^ 2 := lt_of_not_ge h
      have hpos :
          0 < (x ^ 2 + y ^ 2) * ((x ^ 2 + y ^ 2) - 1) :=
        mul_pos (by linarith) (sub_pos.mpr hlt)
      nlinarith
    constructor <;> constructor <;>
      nlinarith [sq_nonneg (x + 1), sq_nonneg (x - 1),
        sq_nonneg (y + 1), sq_nonneg (y - 1)]
  exact
    (isCompact_Icc.prod isCompact_Icc).of_isClosed_subset
      unitBase_closed hsub

private theorem unitIntegrand_integrable (c : ℝ) :
    Integrable
      (unitBase.indicator (unitIntegrand c))
      ((MeasureTheory.volume : Measure ℝ).prod MeasureTheory.volume) := by
  refine (integrable_indicator_iff unitBase_closed.measurableSet).2 ?_
  have hc : Continuous (unitIntegrand c) := by
    unfold unitIntegrand
    fun_prop
  exact hc.continuousOn.integrableOn_compact unitBase_compact

private theorem unit_volume_quadrant (c : ℝ) :
    (∫ p in unitBase, unitIntegrand c p) =
      4 * ∫ p in unitQuadrantBase, unitIntegrand c p := by
  let g : ℝ × ℝ → ℝ := unitBase.indicator (unitIntegrand c)
  have hg :
      Integrable g
        ((MeasureTheory.volume : Measure ℝ).prod MeasureTheory.volume) := by
    simpa [g] using unitIntegrand_integrable c
  have hevenY : ∀ x y : ℝ, g (x, -y) = g (x, y) := by
    intro x y
    have hm : (x, -y) ∈ unitBase ↔ (x, y) ∈ unitBase := by
      simp only [unitBase, Set.mem_setOf_eq]
      ring_nf
    by_cases h : (x, y) ∈ unitBase
    · dsimp [g]
      rw [Set.indicator_of_mem h, Set.indicator_of_mem (hm.mpr h)]
      unfold unitIntegrand
      ring_nf
    · dsimp [g]
      rw [Set.indicator_of_notMem h,
        Set.indicator_of_notMem (fun hn => h (hm.mp hn))]
  have hevenX : ∀ x y : ℝ, g (-x, y) = g (x, y) := by
    intro x y
    have hm : (-x, y) ∈ unitBase ↔ (x, y) ∈ unitBase := by
      simp only [unitBase, Set.mem_setOf_eq]
      ring_nf
    by_cases h : (x, y) ∈ unitBase
    · dsimp [g]
      rw [Set.indicator_of_mem h, Set.indicator_of_mem (hm.mpr h)]
      unfold unitIntegrand
      ring_nf
    · dsimp [g]
      rw [Set.indicator_of_notMem h,
        Set.indicator_of_notMem (fun hn => h (hm.mp hn))]
  have habsY : ∀ x y : ℝ, g (x, |y|) = g (x, y) := by
    intro x y
    rcases le_total 0 y with hy | hy
    · rw [abs_of_nonneg hy]
    · rw [abs_of_nonpos hy, hevenY]
  have habsX : ∀ x y : ℝ, g (|x|, y) = g (x, y) := by
    intro x y
    rcases le_total 0 x with hx | hx
    · rw [abs_of_nonneg hx]
    · rw [abs_of_nonpos hx, hevenX]
  let H : ℝ → ℝ := fun x => ∫ y in Set.Ioi (0 : ℝ), g (x, y)
  have hinner : ∀ x : ℝ, (∫ y : ℝ, g (x, y)) = 2 * H x := by
    intro x
    calc
      (∫ y : ℝ, g (x, y)) = ∫ y : ℝ, g (x, |y|) := by
        apply MeasureTheory.integral_congr_ae
        exact Filter.Eventually.of_forall fun y => (habsY x y).symm
      _ = 2 * ∫ y in Set.Ioi (0 : ℝ), g (x, y) := by
        simpa using
          (integral_comp_abs (f := fun y : ℝ => g (x, y)))
      _ = 2 * H x := rfl
  have hHabs : ∀ x : ℝ, H |x| = H x := by
    intro x
    unfold H
    apply MeasureTheory.integral_congr_ae
    exact Filter.Eventually.of_forall fun y => habsX x y
  have houter :
      (∫ x : ℝ, H x) = 2 * ∫ x in Set.Ioi (0 : ℝ), H x := by
    calc
      (∫ x : ℝ, H x) = ∫ x : ℝ, H |x| := by
        apply MeasureTheory.integral_congr_ae
        exact Filter.Eventually.of_forall fun x => (hHabs x).symm
      _ = 2 * ∫ x in Set.Ioi (0 : ℝ), H x := by
        simpa using (integral_comp_abs (f := H))
  have hquadMeas : MeasurableSet quadrant :=
    measurableSet_Ioi.prod measurableSet_Ioi
  have hqg :
      Integrable (quadrant.indicator g)
        ((MeasureTheory.volume : Measure ℝ).prod MeasureTheory.volume) :=
    hg.indicator hquadMeas
  have hFub :
      (∫ p in quadrant, g p) =
        ∫ x in Set.Ioi (0 : ℝ),
          ∫ y in Set.Ioi (0 : ℝ), g (x, y) := by
    calc
      (∫ p in quadrant, g p) =
          ∫ p : ℝ × ℝ, quadrant.indicator g p := by
            rw [MeasureTheory.integral_indicator hquadMeas]
      _ = ∫ x : ℝ, ∫ y : ℝ, quadrant.indicator g (x, y) := by
            exact MeasureTheory.integral_prod _ hqg
      _ = ∫ x in Set.Ioi (0 : ℝ),
          ∫ y in Set.Ioi (0 : ℝ), g (x, y) := by
            rw [← MeasureTheory.integral_indicator measurableSet_Ioi]
            apply MeasureTheory.integral_congr_ae
            exact Filter.Eventually.of_forall fun x => by
              by_cases hx : x ∈ Set.Ioi (0 : ℝ)
              · rw [Set.indicator_of_mem hx]
                have hpoint :
                    (fun y : ℝ => quadrant.indicator g (x, y)) =
                      (Set.Ioi (0 : ℝ)).indicator (fun y => g (x, y)) := by
                  funext y
                  by_cases hy : y ∈ Set.Ioi (0 : ℝ)
                  · rw [Set.indicator_of_mem hy,
                      Set.indicator_of_mem
                        (show (x, y) ∈ quadrant from ⟨hx, hy⟩)]
                  · rw [Set.indicator_of_notMem hy,
                      Set.indicator_of_notMem
                        (fun hp : (x, y) ∈ quadrant => hy hp.2)]
                change (∫ y : ℝ, quadrant.indicator g (x, y)) =
                  ∫ y in Set.Ioi (0 : ℝ), g (x, y)
                rw [hpoint, MeasureTheory.integral_indicator measurableSet_Ioi]
              · rw [Set.indicator_of_notMem hx]
                have hz :
                    (fun y : ℝ => quadrant.indicator g (x, y)) =
                      (fun _ => (0 : ℝ)) := by
                  funext y
                  rw [Set.indicator_of_notMem
                    (fun hp : (x, y) ∈ quadrant => hx hp.1)]
                change (∫ y : ℝ, quadrant.indicator g (x, y)) = 0
                rw [hz]
                simp
  have hquadBase :
      (∫ p in quadrant, g p) =
        ∫ p in unitQuadrantBase, unitIntegrand c p := by
    unfold unitQuadrantBase
    rw [← MeasureTheory.integral_indicator hquadMeas,
      ← MeasureTheory.integral_indicator
        (hquadMeas.inter unitBase_closed.measurableSet)]
    apply MeasureTheory.integral_congr_ae
    exact Filter.Eventually.of_forall fun p => by
      by_cases hq : p ∈ quadrant
      · by_cases hb : p ∈ unitBase
        · simp [g, hq, hb]
        · simp [g, hq, hb]
      · simp [g, hq]
  calc
    (∫ p in unitBase, unitIntegrand c p) =
        ∫ p : ℝ × ℝ, g p := by
          rw [MeasureTheory.integral_indicator unitBase_closed.measurableSet]
    _ = ∫ x : ℝ, ∫ y : ℝ, g (x, y) := by
          exact MeasureTheory.integral_prod _ hg
    _ = ∫ x : ℝ, 2 * H x := by
          apply MeasureTheory.integral_congr_ae
          exact Filter.Eventually.of_forall hinner
    _ = 2 * ∫ x : ℝ, H x := by
          rw [MeasureTheory.integral_const_mul]
    _ = 4 * ∫ x in Set.Ioi (0 : ℝ), H x := by
          rw [houter]
          ring
    _ = 4 * ∫ p in quadrant, g p := by rw [hFub]
    _ = 4 * ∫ p in unitQuadrantBase, unitIntegrand c p := by
          rw [hquadBase]

private def polarRegion : Set (ℝ × ℝ) :=
  {p |
    0 < p.2 ∧ p.2 < Real.pi / 4 ∧
      0 < p.1 ∧ p.1 ≤ Real.sqrt (Real.cos (2 * p.2))}

private theorem polarRegion_measurable : MeasurableSet polarRegion := by
  unfold polarRegion
  measurability

private theorem polar_characterization (p : ℝ × ℝ) :
    p ∈ polarCoord.target ∧
        polarCoord.symm p ∈ unitQuadrantBase ↔
      p ∈ polarRegion := by
  rcases p with ⟨r, φ⟩
  have hsum :
      (r * Real.cos φ) ^ 2 + (r * Real.sin φ) ^ 2 = r ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq φ]
  have hdiff :
      (r * Real.cos φ) ^ 2 - (r * Real.sin φ) ^ 2 =
        r ^ 2 * Real.cos (2 * φ) := by
    rw [Real.cos_two_mul]
    nlinarith [Real.sin_sq_add_cos_sq φ]
  constructor
  · rintro ⟨ht, hqb⟩
    have ht' : 0 < r ∧ -Real.pi < φ ∧ φ < Real.pi := by
      simpa [polarCoord_target] using ht
    have hquad :
        0 < r * Real.cos φ ∧ 0 < r * Real.sin φ := hqb.1
    have hbase :
        (r ^ 2) ^ 2 ≤ r ^ 2 * Real.cos (2 * φ) := by
      simpa [unitQuadrantBase, unitBase, polarCoord_symm_apply,
        hsum, hdiff] using hqb.2
    have hcosφ : 0 < Real.cos φ := by nlinarith
    have hsinφ : 0 < Real.sin φ := by nlinarith
    have hφpos : 0 < φ := by
      by_contra h
      have hnonpos : φ ≤ 0 := le_of_not_gt h
      have := Real.sin_nonpos_of_nonpos_of_neg_pi_le hnonpos ht'.2.1.le
      linarith
    have hφhalf : φ < Real.pi / 2 := by
      by_contra h
      have hhalf : Real.pi / 2 ≤ φ := le_of_not_gt h
      have := Real.cos_nonpos_of_pi_div_two_le_of_le hhalf
        (by linarith [ht'.2.2, Real.pi_pos])
      linarith
    have hrsq : 0 < r ^ 2 := sq_pos_of_pos ht'.1
    have hradSq : r ^ 2 ≤ Real.cos (2 * φ) := by
      by_contra h
      have hlt : Real.cos (2 * φ) < r ^ 2 := lt_of_not_ge h
      have hpos : 0 < r ^ 2 * (r ^ 2 - Real.cos (2 * φ)) :=
        mul_pos hrsq (sub_pos.mpr hlt)
      nlinarith
    have hcos2 : 0 < Real.cos (2 * φ) := lt_of_lt_of_le hrsq hradSq
    have hφquarter : φ < Real.pi / 4 := by
      by_contra h
      have hquarter : Real.pi / 4 ≤ φ := le_of_not_gt h
      have hnonpos :=
        Real.cos_nonpos_of_pi_div_two_le_of_le (x := 2 * φ)
          (by linarith [hquarter])
          (by linarith [hφhalf, Real.pi_pos])
      linarith
    have hsqrtSq :
        Real.sqrt (Real.cos (2 * φ)) ^ 2 = Real.cos (2 * φ) :=
      Real.sq_sqrt hcos2.le
    have hrbound : r ≤ Real.sqrt (Real.cos (2 * φ)) := by
      by_contra h
      have hlt : Real.sqrt (Real.cos (2 * φ)) < r := lt_of_not_ge h
      have hsqLt :
          Real.sqrt (Real.cos (2 * φ)) ^ 2 < r ^ 2 :=
        (sq_lt_sq₀ (Real.sqrt_nonneg _) ht'.1.le).2 hlt
      nlinarith
    exact ⟨hφpos, hφquarter, ht'.1, hrbound⟩
  · rintro ⟨hφpos, hφquarter, hrpos, hrbound⟩
    have hφhalf : φ < Real.pi / 2 := by
      linarith [Real.pi_pos]
    have hsinφ : 0 < Real.sin φ :=
      Real.sin_pos_of_pos_of_lt_pi hφpos (by linarith [hφhalf])
    have hcosφ : 0 < Real.cos φ :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hφhalf⟩
    have hcos2 : 0 ≤ Real.cos (2 * φ) :=
      Real.cos_nonneg_of_neg_pi_div_two_le_of_le
        ((neg_nonpos.mpr (by positivity : 0 ≤ Real.pi / 2)).trans
          (mul_nonneg (by norm_num) hφpos.le))
        (by linarith [hφquarter])
    have hsqrtSq :
        Real.sqrt (Real.cos (2 * φ)) ^ 2 = Real.cos (2 * φ) :=
      Real.sq_sqrt hcos2
    have hradSq : r ^ 2 ≤ Real.cos (2 * φ) := by
      exact (sq_le_sq₀ hrpos.le (Real.sqrt_nonneg _)).2 hrbound
        |>.trans_eq hsqrtSq
    have ht : (r, φ) ∈ polarCoord.target := by
      simp only [polarCoord_target, Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo]
      exact ⟨hrpos, by constructor <;> linarith [Real.pi_pos, hφquarter]⟩
    have hqb : polarCoord.symm (r, φ) ∈ unitQuadrantBase := by
      constructor
      · exact ⟨mul_pos hrpos hcosφ, mul_pos hrpos hsinφ⟩
      · simp only [unitBase, polarCoord_symm_apply, Set.mem_setOf_eq,
          hsum, hdiff]
        nlinarith [sq_nonneg r]
    exact ⟨ht, hqb⟩

private theorem unit_quadrant_polar (c : ℝ) :
    (∫ p in unitQuadrantBase, unitIntegrand c p) =
      ∫ φ in (0 : ℝ)..Real.pi / 4,
        ∫ r in (0 : ℝ)..Real.sqrt (Real.cos (2 * φ)),
          2 * c * Real.sqrt (1 - r ^ 2) * r := by
  let f : ℝ × ℝ → ℝ := unitIntegrand c
  let q : ℝ × ℝ → ℝ :=
    fun p => 2 * c * Real.sqrt (1 - p.1 ^ 2) * p.1
  have hqbMeas : MeasurableSet unitQuadrantBase :=
    (measurableSet_Ioi.prod measurableSet_Ioi).inter
      unitBase_closed.measurableSet
  have hpoint : ∀ p : ℝ × ℝ,
      polarCoord.target.indicator
          (fun z => z.1 * unitQuadrantBase.indicator f
            (polarCoord.symm z)) p =
        polarRegion.indicator q p := by
    intro p
    by_cases hp : p ∈ polarRegion
    · have hc := polar_characterization p |>.mpr hp
      rw [Set.indicator_of_mem hp, Set.indicator_of_mem hc.1,
        Set.indicator_of_mem hc.2]
      rcases p with ⟨r, φ⟩
      simp only [q, f, unitIntegrand, polarCoord_symm_apply]
      have hsum :
          (r * Real.cos φ) ^ 2 + (r * Real.sin φ) ^ 2 = r ^ 2 := by
        nlinarith [Real.sin_sq_add_cos_sq φ]
      rw [hsum]
      ring
    · have hc :
        ¬(p ∈ polarCoord.target ∧
          polarCoord.symm p ∈ unitQuadrantBase) := by
        intro h
        exact hp ((polar_characterization p).mp h)
      rw [Set.indicator_of_notMem hp]
      by_cases ht : p ∈ polarCoord.target
      · have hb : polarCoord.symm p ∉ unitQuadrantBase :=
          fun h => hc ⟨ht, h⟩
        rw [Set.indicator_of_mem ht, Set.indicator_of_notMem hb]
        simp
      · rw [Set.indicator_of_notMem ht]
  have hqcont : Continuous q := by
    dsimp [q]
    fun_prop
  have hsubset :
      polarRegion ⊆
        Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) (Real.pi / 4) := by
    rintro ⟨r, φ⟩ hp
    have hcosle : Real.cos (2 * φ) ≤ 1 := Real.cos_le_one _
    have hsqrtle : Real.sqrt (Real.cos (2 * φ)) ≤ 1 := by
      rw [Real.sqrt_le_one]
      exact hcosle
    exact ⟨⟨hp.2.2.1.le, hp.2.2.2.trans hsqrtle⟩,
      ⟨hp.1.le, hp.2.1.le⟩⟩
  have hbox :
      IsCompact
        (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) (Real.pi / 4)) :=
    isCompact_Icc.prod isCompact_Icc
  have hqint : IntegrableOn q polarRegion :=
    (hqcont.continuousOn.integrableOn_compact hbox).mono_set hsubset
  have hglobal : Integrable (polarRegion.indicator q) :=
    (integrable_indicator_iff polarRegion_measurable).2 hqint
  have hinner : ∀ φ : ℝ,
      (∫ r : ℝ, polarRegion.indicator q (r, φ)) =
        (Set.Ioo (0 : ℝ) (Real.pi / 4)).indicator
          (fun φ =>
            ∫ r in (0 : ℝ)..Real.sqrt (Real.cos (2 * φ)),
              2 * c * Real.sqrt (1 - r ^ 2) * r) φ := by
    intro φ
    by_cases hφ : φ ∈ Set.Ioo (0 : ℝ) (Real.pi / 4)
    · rw [Set.indicator_of_mem hφ]
      have hu0 : 0 ≤ Real.sqrt (Real.cos (2 * φ)) :=
        Real.sqrt_nonneg _
      have hind :
          (fun r : ℝ => polarRegion.indicator q (r, φ)) =
            (Set.Ioc (0 : ℝ)
              (Real.sqrt (Real.cos (2 * φ)))).indicator
              (fun r : ℝ => 2 * c * Real.sqrt (1 - r ^ 2) * r) := by
        funext r
        have hmem :
            (r, φ) ∈ polarRegion ↔
              r ∈ Set.Ioc (0 : ℝ)
                (Real.sqrt (Real.cos (2 * φ))) := by
          constructor
          · intro hp
            exact ⟨hp.2.2.1, hp.2.2.2⟩
          · intro hr
            exact ⟨hφ.1, hφ.2, hr.1, hr.2⟩
        by_cases hr :
            r ∈ Set.Ioc (0 : ℝ) (Real.sqrt (Real.cos (2 * φ)))
        · rw [Set.indicator_of_mem hr,
            Set.indicator_of_mem (hmem.mpr hr)]
        · rw [Set.indicator_of_notMem hr,
            Set.indicator_of_notMem (fun hp => hr (hmem.mp hp))]
      rw [hind, MeasureTheory.integral_indicator measurableSet_Ioc]
      rw [← intervalIntegral.integral_of_le hu0]
    · rw [Set.indicator_of_notMem hφ]
      have hnone : ∀ r : ℝ, (r, φ) ∉ polarRegion := by
        intro r hp
        exact hφ ⟨hp.1, hp.2.1⟩
      simp [hnone]
  calc
    (∫ p in unitQuadrantBase, unitIntegrand c p) =
        ∫ p : ℝ × ℝ, unitQuadrantBase.indicator f p := by
          rw [MeasureTheory.integral_indicator hqbMeas]
    _ = ∫ p in polarCoord.target,
          p.1 * unitQuadrantBase.indicator f (polarCoord.symm p) := by
          simpa [smul_eq_mul] using
            (integral_comp_polarCoord_symm
              (unitQuadrantBase.indicator f)).symm
    _ = ∫ p : ℝ × ℝ, polarRegion.indicator q p := by
          rw [← MeasureTheory.integral_indicator
            polarCoord.open_target.measurableSet]
          apply MeasureTheory.integral_congr_ae
          exact Filter.Eventually.of_forall hpoint
    _ = ∫ φ : ℝ, ∫ r : ℝ, polarRegion.indicator q (r, φ) := by
          simpa using MeasureTheory.integral_prod_symm _ hglobal
    _ = ∫ φ : ℝ,
          (Set.Ioo (0 : ℝ) (Real.pi / 4)).indicator
            (fun φ =>
              ∫ r in (0 : ℝ)..Real.sqrt (Real.cos (2 * φ)),
                2 * c * Real.sqrt (1 - r ^ 2) * r) φ := by
          apply MeasureTheory.integral_congr_ae
          exact Filter.Eventually.of_forall hinner
    _ = ∫ φ in Set.Ioo (0 : ℝ) (Real.pi / 4),
          ∫ r in (0 : ℝ)..Real.sqrt (Real.cos (2 * φ)),
            2 * c * Real.sqrt (1 - r ^ 2) * r := by
          rw [MeasureTheory.integral_indicator measurableSet_Ioo]
    _ = ∫ φ in Set.Ioc (0 : ℝ) (Real.pi / 4),
          ∫ r in (0 : ℝ)..Real.sqrt (Real.cos (2 * φ)),
            2 * c * Real.sqrt (1 - r ^ 2) * r := by
          rw [Measure.restrict_congr_set Ioo_ae_eq_Ioc]
    _ = ∫ φ in (0 : ℝ)..Real.pi / 4,
          ∫ r in (0 : ℝ)..Real.sqrt (Real.cos (2 * φ)),
            2 * c * Real.sqrt (1 - r ^ 2) * r := by
          rw [intervalIntegral.integral_of_le
            (by linarith [Real.pi_pos])]

private theorem volume_polar_formula (a b c : ℝ)
    (ha : 0 < a) (hb : 0 < b) :
    volume a b c =
      8 * a * b * c *
        ∫ φ in (0 : ℝ)..Real.pi / 4,
          ∫ r in (0 : ℝ)..Real.sqrt (Real.cos (2 * φ)),
            Real.sqrt (1 - r ^ 2) * r := by
  let g : ℝ × ℝ → ℝ :=
    (baseRegion a b).indicator
      (fun p => 2 * c *
        Real.sqrt (1 - normalizedRadiusSq a b p.1 p.2))
  let h : ℝ × ℝ → ℝ := unitBase.indicator (unitIntegrand c)
  have hbase : MeasurableSet (baseRegion a b) := by
    unfold baseRegion normalizedRadiusSq
    measurability
  have hpoint : ∀ q : ℝ × ℝ,
      g (a * q.1, b * q.2) = h q := by
    rintro ⟨x, y⟩
    have hx : (a * x) ^ 2 / a ^ 2 = x ^ 2 := by
      field_simp [ne_of_gt ha]
    have hy : (b * y) ^ 2 / b ^ 2 = y ^ 2 := by
      field_simp [ne_of_gt hb]
    have hnorm :
        normalizedRadiusSq a b (a * x) (b * y) = x ^ 2 + y ^ 2 := by
      simp [normalizedRadiusSq, hx, hy]
    have hmem :
        (a * x, b * y) ∈ baseRegion a b ↔ (x, y) ∈ unitBase := by
      simp only [baseRegion, unitBase, Set.mem_setOf_eq,
        Prod.fst, Prod.snd, hnorm, hx, hy]
    by_cases hm : (x, y) ∈ unitBase
    · dsimp only [g, h]
      rw [Set.indicator_of_mem hm,
        Set.indicator_of_mem (hmem.mpr hm)]
      simp only [unitIntegrand, hnorm]
    · dsimp only [g, h]
      rw [Set.indicator_of_notMem hm,
        Set.indicator_of_notMem (fun hxy => hm (hmem.mp hxy))]
  calc
    volume a b c = ∫ p : ℝ × ℝ, g p := by
      rw [volume, ← MeasureTheory.integral_indicator hbase]
    _ = a * b * ∫ q : ℝ × ℝ, g (a * q.1, b * q.2) :=
      integral_diag a b ha hb g
    _ = a * b * ∫ q : ℝ × ℝ, h q := by
      congr 1
      apply MeasureTheory.integral_congr_ae
      exact Filter.Eventually.of_forall hpoint
    _ = a * b * ∫ q in unitBase, unitIntegrand c q := by
      rw [← MeasureTheory.integral_indicator unitBase_closed.measurableSet]
    _ = a * b *
        (4 * ∫ q in unitQuadrantBase, unitIntegrand c q) := by
      rw [unit_volume_quadrant c]
    _ = a * b *
        (4 * ∫ φ in (0 : ℝ)..Real.pi / 4,
          ∫ r in (0 : ℝ)..Real.sqrt (Real.cos (2 * φ)),
            2 * c * Real.sqrt (1 - r ^ 2) * r) := by
      rw [unit_quadrant_polar c]
    _ = 8 * a * b * c *
        ∫ φ in (0 : ℝ)..Real.pi / 4,
          ∫ r in (0 : ℝ)..Real.sqrt (Real.cos (2 * φ)),
            Real.sqrt (1 - r ^ 2) * r := by
      have hinner : ∀ φ : ℝ,
          (∫ r in (0 : ℝ)..Real.sqrt (Real.cos (2 * φ)),
            2 * c * Real.sqrt (1 - r ^ 2) * r) =
          2 * c * ∫ r in (0 : ℝ)..Real.sqrt (Real.cos (2 * φ)),
            Real.sqrt (1 - r ^ 2) * r := by
        intro φ
        calc
          _ = ∫ r in (0 : ℝ)..Real.sqrt (Real.cos (2 * φ)),
              (2 * c) * (Real.sqrt (1 - r ^ 2) * r) := by
                apply intervalIntegral.integral_congr
                intro r hr
                ring
          _ = _ := by rw [intervalIntegral.integral_const_mul]
      have houter :
          (∫ φ in (0 : ℝ)..Real.pi / 4,
            ∫ r in (0 : ℝ)..Real.sqrt (Real.cos (2 * φ)),
              2 * c * Real.sqrt (1 - r ^ 2) * r) =
            ∫ φ in (0 : ℝ)..Real.pi / 4,
              2 * c *
                (∫ r in (0 : ℝ)..Real.sqrt (Real.cos (2 * φ)),
                  Real.sqrt (1 - r ^ 2) * r) := by
        apply intervalIntegral.integral_congr
        intro φ hφ
        exact hinner φ
      rw [houter, intervalIntegral.integral_const_mul]
      ring

theorem gap6 (a b c : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    volume a b c =
      8 * a * b * c *
        ∫ φ in (0 : ℝ)..Real.pi / 4,
          ∫ r in (0 : ℝ)..Real.sqrt (Real.cos (2 * φ)),
            Real.sqrt (1 - r ^ 2) * r := by
  exact volume_polar_formula a b c ha hb

private theorem radial_value (φ : ℝ)
    (hφ : φ ∈ Set.uIcc (0 : ℝ) (Real.pi / 4)) :
    (∫ r in (0 : ℝ)..Real.sqrt (Real.cos (2 * φ)),
      Real.sqrt (1 - r ^ 2) * r) =
      1 / 3 * (1 - Real.sqrt 8 * Real.sin φ ^ 3) := by
  have hφ' : 0 ≤ φ ∧ φ ≤ Real.pi / 4 := by
    rw [Set.uIcc_of_le (by positivity : (0 : ℝ) ≤ Real.pi / 4)] at hφ
    exact hφ
  have hcos : 0 ≤ Real.cos (2 * φ) :=
    Real.cos_nonneg_of_neg_pi_div_two_le_of_le
      ((neg_nonpos.mpr (by positivity : 0 ≤ Real.pi / 2)).trans
        (mul_nonneg (by norm_num) hφ'.1))
      (by linarith [hφ'.2])
  have hcosle : Real.cos (2 * φ) ≤ 1 := Real.cos_le_one _
  have hu0 : 0 ≤ Real.sqrt (Real.cos (2 * φ)) := Real.sqrt_nonneg _
  have hu1 : Real.sqrt (Real.cos (2 * φ)) ≤ 1 := by
    rw [Real.sqrt_le_one]
    exact hcosle
  let F : ℝ → ℝ :=
    fun r => (r ^ 2 - 1) * Real.sqrt (1 - r ^ 2) / 3
  have hcont : ContinuousOn F
      (Set.Icc (0 : ℝ) (Real.sqrt (Real.cos (2 * φ)))) := by
    exact (by fun_prop : Continuous F).continuousOn
  have hd : ∀ r ∈ Set.Ioo (0 : ℝ)
      (Real.sqrt (Real.cos (2 * φ))),
      HasDerivAt F (Real.sqrt (1 - r ^ 2) * r) r := by
    intro r hr
    have hr1 : r < 1 := hr.2.trans_le hu1
    have hpos : 0 < 1 - r ^ 2 := by
      nlinarith [sq_lt_sq₀ hr.1.le (by norm_num : (0 : ℝ) ≤ 1) |>.2 hr1]
    have hinner : HasDerivAt (fun x : ℝ => 1 - x ^ 2) (-2 * r) r := by
      convert (hasDerivAt_const r 1).sub ((hasDerivAt_id r).pow 2) using 1 <;>
        simp only [id_eq] <;> ring
    have hfirst : HasDerivAt (fun x : ℝ => x ^ 2 - 1) (2 * r) r := by
      convert ((hasDerivAt_id r).pow 2).sub_const 1 using 1 <;>
        simp only [id_eq] <;> ring
    have hsqrt : HasDerivAt (fun x : ℝ => Real.sqrt (1 - x ^ 2))
        (1 / (2 * Real.sqrt (1 - r ^ 2)) * (-2 * r)) r := by
      simpa only [Function.comp_apply] using
        (Real.hasDerivAt_sqrt hpos.ne').comp r hinner
    have hsquare : Real.sqrt (1 - r ^ 2) ^ 2 = 1 - r ^ 2 :=
      Real.sq_sqrt hpos.le
    dsimp [F]
    convert ((hfirst.mul hsqrt).div_const 3) using 1
    field_simp [Real.sqrt_ne_zero'.mpr hpos]
    rw [hsquare]
    ring
  have hi : IntervalIntegrable
      (fun r : ℝ => Real.sqrt (1 - r ^ 2) * r)
      MeasureTheory.volume 0 (Real.sqrt (Real.cos (2 * φ))) :=
    (by fun_prop : Continuous
      (fun r : ℝ => Real.sqrt (1 - r ^ 2) * r)).intervalIntegrable _ _
  have hFTC :
      (∫ r in (0 : ℝ)..Real.sqrt (Real.cos (2 * φ)),
        Real.sqrt (1 - r ^ 2) * r) =
        F (Real.sqrt (Real.cos (2 * φ))) - F 0 := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hu0 hcont hd hi
  have hsqrtCos :
      Real.sqrt (Real.cos (2 * φ)) ^ 2 = Real.cos (2 * φ) :=
    Real.sq_sqrt hcos
  have hsin0 : 0 ≤ Real.sin φ :=
    (Real.sin_nonneg_of_nonneg_of_le_pi hφ'.1
      (by linarith [hφ'.2, Real.pi_pos]))
  have hone :
      1 - Real.cos (2 * φ) = 2 * Real.sin φ ^ 2 := by
    rw [Real.cos_two_mul]
    nlinarith [Real.sin_sq_add_cos_sq φ]
  have hsqrtOne :
      Real.sqrt (1 - Real.cos (2 * φ)) =
        Real.sqrt 2 * Real.sin φ := by
    rw [hone, show 2 * Real.sin φ ^ 2 =
      (2 : ℝ) * (Real.sin φ ^ 2) by ring,
      Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2),
      Real.sqrt_sq_eq_abs, abs_of_nonneg hsin0]
  have hsqrt4 : Real.sqrt 4 = (2 : ℝ) := by
    rw [show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num,
      Real.sqrt_sq_eq_abs, abs_of_nonneg (by norm_num)]
  have hsqrt8 : Real.sqrt 8 = 2 * Real.sqrt 2 := by
    rw [show (8 : ℝ) = 4 * 2 by norm_num,
      Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4), hsqrt4]
  rw [hFTC]
  dsimp [F]
  rw [hsqrtCos, hsqrtOne, hsqrt8]
  rw [Real.cos_two_mul]
  have htrig : Real.cos φ ^ 2 = 1 - Real.sin φ ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq φ]
  rw [htrig]
  norm_num
  ring

theorem gap7 (a b c : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    volume a b c =
      8 * a * b * c *
        ∫ φ in (0 : ℝ)..Real.pi / 4,
          1 / 3 * (1 - Real.sqrt 8 * Real.sin φ ^ 3) := by
  rw [gap6 a b c ha hb hc]
  congr 1
  apply intervalIntegral.integral_congr
  intro φ hφ
  exact radial_value φ hφ

private theorem angular_deriv (a b c φ : ℝ) :
    HasDerivAt (angularPrimitive a b c)
      (8 * a * b * c *
        (1 / 3 * (1 - Real.sqrt 8 * Real.sin φ ^ 3))) φ := by
  unfold angularPrimitive
  convert
    (hasDerivAt_const φ (8 * a * b * c / 3)).mul
      (((hasDerivAt_id φ).add
        ((hasDerivAt_const φ (Real.sqrt 8)).mul
          (Real.hasDerivAt_cos φ))).sub
        (((hasDerivAt_const φ (Real.sqrt 8 / 3)).mul
          ((Real.hasDerivAt_cos φ).pow 3)))) using 1 <;>
    (try simp only [id_eq])
  · have hsin3 :
        Real.sin φ ^ 3 =
          Real.sin φ * (1 - Real.cos φ ^ 2) := by
      rw [show Real.sin φ ^ 3 = Real.sin φ * Real.sin φ ^ 2 by ring,
        Real.sin_sq]
    rw [hsin3]
    ring

theorem gap8 (a b c : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    volume a b c =
      angularPrimitive a b c (Real.pi / 4) -
        angularPrimitive a b c 0 := by
  rw [gap7 a b c ha hb hc]
  have hi : IntervalIntegrable
      (fun φ : ℝ =>
        8 * a * b * c *
          (1 / 3 * (1 - Real.sqrt 8 * Real.sin φ ^ 3)))
      MeasureTheory.volume 0 (Real.pi / 4) :=
    (by fun_prop : Continuous
      (fun φ : ℝ =>
        8 * a * b * c *
          (1 / 3 * (1 - Real.sqrt 8 * Real.sin φ ^ 3)))).intervalIntegrable _ _
  calc
    8 * a * b * c *
        (∫ φ in (0 : ℝ)..Real.pi / 4,
          1 / 3 * (1 - Real.sqrt 8 * Real.sin φ ^ 3)) =
        ∫ φ in (0 : ℝ)..Real.pi / 4,
          8 * a * b * c *
            (1 / 3 * (1 - Real.sqrt 8 * Real.sin φ ^ 3)) := by
          simpa using
            (intervalIntegral.integral_const_mul
              (μ := MeasureTheory.volume)
              (a := (0 : ℝ)) (b := Real.pi / 4)
              (8 * a * b * c)
              (fun φ : ℝ =>
                1 / 3 * (1 - Real.sqrt 8 * Real.sin φ ^ 3))).symm
    _ = angularPrimitive a b c (Real.pi / 4) -
        angularPrimitive a b c 0 := by
          apply intervalIntegral.integral_eq_sub_of_hasDerivAt
          · intro φ hφ
            exact angular_deriv a b c φ
          · exact hi

private theorem endpoint_value (a b c : ℝ) :
    angularPrimitive a b c (Real.pi / 4) -
        angularPrimitive a b c 0 =
      8 * a * b * c / 3 *
        (Real.pi / 4 + 5 / 3 - 4 * Real.sqrt 2 / 3) := by
  have hsqrt2 : Real.sqrt (2 : ℝ) ^ 2 = 2 :=
    Real.sq_sqrt (by norm_num)
  have hsqrt4 : Real.sqrt 4 = (2 : ℝ) := by
    rw [show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num,
      Real.sqrt_sq_eq_abs, abs_of_nonneg (by norm_num)]
  have hsqrt8 : Real.sqrt 8 = 2 * Real.sqrt 2 := by
    rw [show (8 : ℝ) = 4 * 2 by norm_num,
      Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4), hsqrt4]
  unfold angularPrimitive
  rw [Real.cos_pi_div_four, Real.cos_zero, hsqrt8]
  have hsqrt2four : Real.sqrt 2 ^ 4 = 4 := by
    rw [show Real.sqrt 2 ^ 4 = (Real.sqrt 2 ^ 2) ^ 2 by ring,
      hsqrt2]
    norm_num
  ring_nf
  rw [hsqrt2, hsqrt2four]
  ring

theorem gap9 (a b c : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    volume a b c =
      8 * a * b * c / 3 *
        (Real.pi / 4 + 5 / 3 - 4 * Real.sqrt 2 / 3) := by
  rw [gap8 a b c ha hb hc, endpoint_value]

theorem gap10 (a b c : ℝ) :
    8 * a * b * c / 3 *
        (Real.pi / 4 + 5 / 3 - 4 * Real.sqrt 2 / 3) =
      2 * a * b * c / 9 * (3 * Real.pi + 20 - 16 * Real.sqrt 2) := by
  ring

theorem gap11 (a b c : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    volume a b c =
      2 * a * b * c / 9 *
        (3 * Real.pi + 20 - 16 * Real.sqrt 2) := by
  rw [gap9 a b c ha hb hc, gap10]

end

end ProofGap.Exercise4026
