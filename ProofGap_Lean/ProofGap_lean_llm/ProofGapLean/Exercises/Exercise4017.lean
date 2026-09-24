import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise4017

noncomputable section

open MeasureTheory
open scoped Interval

def polarX (r φ : ℝ) : ℝ :=
  r * Real.cos φ

def polarY (r φ : ℝ) : ℝ :=
  r * Real.sin φ

def radialHeight (a r : ℝ) : ℝ :=
  r ^ 2 / a

def baseRegion (a : ℝ) : Set (ℝ × ℝ) :=
  {p |
    (p.1 ^ 2 + p.2 ^ 2) ^ 2 ≤
      a ^ 2 * (p.1 ^ 2 - p.2 ^ 2)}

def volume (a : ℝ) : ℝ :=
  ∫ p in baseRegion a, (p.1 ^ 2 + p.2 ^ 2) / a

theorem gap1 (a r : ℝ) (ha : 0 < a) :
    radialHeight a r = r ^ 2 / a := by
  rfl

theorem gap2 (a r φ : ℝ) (ha : 0 < a) (hr : r ≠ 0)
    (hboundary :
      (polarX r φ ^ 2 + polarY r φ ^ 2) ^ 2 =
        a ^ 2 * (polarX r φ ^ 2 - polarY r φ ^ 2)) :
    r ^ 2 = a ^ 2 * Real.cos (2 * φ) := by
  have hsum :
      polarX r φ ^ 2 + polarY r φ ^ 2 = r ^ 2 := by
    unfold polarX polarY
    nlinarith [Real.sin_sq_add_cos_sq φ]
  have hdiff :
      polarX r φ ^ 2 - polarY r φ ^ 2 =
        r ^ 2 * Real.cos (2 * φ) := by
    unfold polarX polarY
    rw [Real.cos_two_mul]
    nlinarith [Real.sin_sq_add_cos_sq φ]
  rw [hsum, hdiff] at hboundary
  have hrsq : 0 < r ^ 2 := sq_pos_of_ne_zero hr
  nlinarith

private def integrand (a : ℝ) (p : ℝ × ℝ) : ℝ :=
  (p.1 ^ 2 + p.2 ^ 2) / a

private def quadrant : Set (ℝ × ℝ) :=
  Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ)

private def quadrantBase (a : ℝ) : Set (ℝ × ℝ) :=
  quadrant ∩ baseRegion a

private theorem baseRegion_closed (a : ℝ) : IsClosed (baseRegion a) := by
  unfold baseRegion
  exact isClosed_le (by fun_prop) (by fun_prop)

private theorem baseRegion_compact (a : ℝ) (ha : 0 < a) :
    IsCompact (baseRegion a) := by
  have hsub :
      baseRegion a ⊆ Set.Icc (-a) a ×ˢ Set.Icc (-a) a := by
    rintro ⟨x, y⟩ hxy
    change (x ^ 2 + y ^ 2) ^ 2 ≤
      a ^ 2 * (x ^ 2 - y ^ 2) at hxy
    have hs0 : 0 ≤ x ^ 2 + y ^ 2 := by positivity
    have hdiff : x ^ 2 - y ^ 2 ≤ x ^ 2 + y ^ 2 := by
      nlinarith [sq_nonneg y]
    have hmul :
        a ^ 2 * (x ^ 2 - y ^ 2) ≤
          a ^ 2 * (x ^ 2 + y ^ 2) :=
      mul_le_mul_of_nonneg_left hdiff (sq_nonneg a)
    have hrad : x ^ 2 + y ^ 2 ≤ a ^ 2 := by
      by_contra h
      have hlt : a ^ 2 < x ^ 2 + y ^ 2 := lt_of_not_ge h
      have hspos : 0 < x ^ 2 + y ^ 2 := by
        nlinarith [sq_nonneg a]
      have hpos :
          0 < (x ^ 2 + y ^ 2) *
            ((x ^ 2 + y ^ 2) - a ^ 2) :=
        mul_pos hspos (sub_pos.mpr hlt)
      nlinarith
    constructor <;> constructor <;>
      nlinarith [sq_nonneg (x + a), sq_nonneg (x - a),
        sq_nonneg (y + a), sq_nonneg (y - a)]
  exact
    (isCompact_Icc.prod isCompact_Icc).of_isClosed_subset
      (baseRegion_closed a) hsub

private theorem integrand_integrable (a : ℝ) (ha : 0 < a) :
    Integrable
      ((baseRegion a).indicator (integrand a))
      ((MeasureTheory.volume : Measure ℝ).prod MeasureTheory.volume) := by
  refine (integrable_indicator_iff (baseRegion_closed a).measurableSet).2 ?_
  have hc : Continuous (integrand a) := by
    unfold integrand
    fun_prop
  exact hc.continuousOn.integrableOn_compact (baseRegion_compact a ha)

private theorem volume_quadrant (a : ℝ) (ha : 0 < a) :
    volume a = 4 * ∫ p in quadrantBase a, integrand a p := by
  let g : ℝ × ℝ → ℝ := (baseRegion a).indicator (integrand a)
  have hg :
      Integrable g
        ((MeasureTheory.volume : Measure ℝ).prod MeasureTheory.volume) := by
    simpa [g] using integrand_integrable a ha
  have hevenY : ∀ x y : ℝ, g (x, -y) = g (x, y) := by
    intro x y
    have hm : (x, -y) ∈ baseRegion a ↔ (x, y) ∈ baseRegion a := by
      simp only [baseRegion, Set.mem_setOf_eq, Prod.fst, Prod.snd]
      ring_nf
    by_cases h : (x, y) ∈ baseRegion a
    · dsimp [g]
      rw [Set.indicator_of_mem h, Set.indicator_of_mem (hm.mpr h)]
      unfold integrand
      ring
    · dsimp [g]
      rw [Set.indicator_of_notMem h,
        Set.indicator_of_notMem (fun hn => h (hm.mp hn))]
  have hevenX : ∀ x y : ℝ, g (-x, y) = g (x, y) := by
    intro x y
    have hm : (-x, y) ∈ baseRegion a ↔ (x, y) ∈ baseRegion a := by
      simp only [baseRegion, Set.mem_setOf_eq, Prod.fst, Prod.snd]
      ring_nf
    by_cases h : (x, y) ∈ baseRegion a
    · dsimp [g]
      rw [Set.indicator_of_mem h, Set.indicator_of_mem (hm.mpr h)]
      unfold integrand
      ring
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
  have hinner : ∀ x : ℝ,
      (∫ y : ℝ, g (x, y)) = 2 * H x := by
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
      (∫ x : ℝ, H x) =
        2 * ∫ x in Set.Ioi (0 : ℝ), H x := by
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
                      Set.indicator_of_mem (show (x, y) ∈ quadrant from ⟨hx, hy⟩)]
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
        ∫ p in quadrantBase a, integrand a p := by
    unfold quadrantBase
    rw [← MeasureTheory.integral_indicator hquadMeas,
      ← MeasureTheory.integral_indicator
        (hquadMeas.inter (baseRegion_closed a).measurableSet)]
    apply MeasureTheory.integral_congr_ae
    exact Filter.Eventually.of_forall fun p => by
      by_cases hq : p ∈ quadrant
      · by_cases hb : p ∈ baseRegion a
        · simp [g, quadrantBase, hq, hb]
        · simp [g, quadrantBase, hq, hb]
      · simp [g, quadrantBase, hq]
  calc
    volume a = ∫ p : ℝ × ℝ, g p := by
      change (∫ p in baseRegion a, integrand a p) = _
      rw [MeasureTheory.integral_indicator
        (baseRegion_closed a).measurableSet]
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
    _ = 4 * ∫ p in quadrantBase a, integrand a p := by rw [hquadBase]

private def polarRegion (a : ℝ) : Set (ℝ × ℝ) :=
  {p |
    0 < p.2 ∧ p.2 < Real.pi / 4 ∧
      0 < p.1 ∧
      p.1 ≤ a * Real.sqrt (Real.cos (2 * p.2))}

private theorem polarRegion_measurable (a : ℝ) :
    MeasurableSet (polarRegion a) := by
  unfold polarRegion
  measurability

private theorem polar_characterization (a : ℝ) (ha : 0 < a)
    (p : ℝ × ℝ) :
    p ∈ polarCoord.target ∧
        polarCoord.symm p ∈ quadrantBase a ↔
      p ∈ polarRegion a := by
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
        0 < r * Real.cos φ ∧ 0 < r * Real.sin φ := by
      exact hqb.1
    have hbase :
        (r ^ 2) ^ 2 ≤ a ^ 2 * (r ^ 2 * Real.cos (2 * φ)) := by
      simpa [quadrantBase, baseRegion, polarCoord_symm_apply, hsum, hdiff]
        using hqb.2
    have hcosφ : 0 < Real.cos φ := by nlinarith
    have hsinφ : 0 < Real.sin φ := by nlinarith
    have hφpos : 0 < φ := by
      by_contra h
      have hφnonpos : φ ≤ 0 := le_of_not_gt h
      have := Real.sin_nonpos_of_nonpos_of_neg_pi_le hφnonpos ht'.2.1.le
      linarith
    have hφhalf : φ < Real.pi / 2 := by
      by_contra h
      have hhalf : Real.pi / 2 ≤ φ := le_of_not_gt h
      have := Real.cos_nonpos_of_pi_div_two_le_of_le hhalf
        (by linarith [ht'.2.2, Real.pi_pos])
      linarith
    have hrsq : 0 < r ^ 2 := sq_pos_of_pos ht'.1
    have hradSq : r ^ 2 ≤ a ^ 2 * Real.cos (2 * φ) := by
      by_contra h
      have hlt : a ^ 2 * Real.cos (2 * φ) < r ^ 2 :=
        lt_of_not_ge h
      have hpos :
          0 < r ^ 2 * (r ^ 2 - a ^ 2 * Real.cos (2 * φ)) :=
        mul_pos hrsq (sub_pos.mpr hlt)
      nlinarith
    have hcos2 : 0 < Real.cos (2 * φ) := by
      nlinarith [sq_nonneg a]
    have hφquarter : φ < Real.pi / 4 := by
      by_contra h
      have hquarter : Real.pi / 4 ≤ φ := le_of_not_gt h
      have hnonpos :=
        Real.cos_nonpos_of_pi_div_two_le_of_le
          (show Real.pi / 2 ≤ 2 * φ by linarith)
          (show 2 * φ ≤ Real.pi + Real.pi / 2 by
            linarith [hφhalf, Real.pi_pos])
      linarith
    have hsqrtSq :
        Real.sqrt (Real.cos (2 * φ)) ^ 2 = Real.cos (2 * φ) :=
      Real.sq_sqrt hcos2.le
    have hrbound :
        r ≤ a * Real.sqrt (Real.cos (2 * φ)) := by
      have hsqrt0 : 0 ≤ Real.sqrt (Real.cos (2 * φ)) :=
        Real.sqrt_nonneg _
      by_contra h
      have hlt : a * Real.sqrt (Real.cos (2 * φ)) < r :=
        lt_of_not_ge h
      have hsqLt :
          (a * Real.sqrt (Real.cos (2 * φ))) ^ 2 < r ^ 2 :=
        (sq_lt_sq₀ (mul_nonneg ha.le hsqrt0) ht'.1.le).2 hlt
      rw [mul_pow, hsqrtSq] at hsqLt
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
        (by linarith [Real.pi_pos])
        (by linarith [hφquarter])
    have hsqrtSq :
        Real.sqrt (Real.cos (2 * φ)) ^ 2 = Real.cos (2 * φ) :=
      Real.sq_sqrt hcos2
    have hradSq : r ^ 2 ≤ a ^ 2 * Real.cos (2 * φ) := by
      have hsqrt0 : 0 ≤ Real.sqrt (Real.cos (2 * φ)) :=
        Real.sqrt_nonneg _
      nlinarith
    have ht : (r, φ) ∈ polarCoord.target := by
      simp only [polarCoord_target, Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo]
      exact ⟨hrpos, by constructor <;> linarith [Real.pi_pos, hφquarter]⟩
    have hqb : polarCoord.symm (r, φ) ∈ quadrantBase a := by
      constructor
      · exact ⟨mul_pos hrpos hcosφ, mul_pos hrpos hsinφ⟩
      · simp only [baseRegion, polarCoord_symm_apply, Set.mem_setOf_eq,
          Prod.fst, Prod.snd, hsum, hdiff]
        have hrsq : 0 ≤ r ^ 2 := sq_nonneg r
        nlinarith
    exact ⟨ht, hqb⟩

private theorem quadrant_polar (a : ℝ) (ha : 0 < a) :
    (∫ p in quadrantBase a, integrand a p) =
      ∫ φ in (0 : ℝ)..Real.pi / 4,
        ∫ r in (0 : ℝ)..a * Real.sqrt (Real.cos (2 * φ)),
          r ^ 2 / a * r := by
  let f : ℝ × ℝ → ℝ := integrand a
  let q : ℝ × ℝ → ℝ := fun p => p.1 ^ 3 / a
  have hqbMeas : MeasurableSet (quadrantBase a) :=
    (measurableSet_Ioi.prod measurableSet_Ioi).inter
      (baseRegion_closed a).measurableSet
  have hpoint : ∀ p : ℝ × ℝ,
      polarCoord.target.indicator
          (fun z => z.1 * (quadrantBase a).indicator f (polarCoord.symm z)) p =
        (polarRegion a).indicator q p := by
    intro p
    by_cases hp : p ∈ polarRegion a
    · have hc := (polar_characterization a ha p).mpr hp
      rw [Set.indicator_of_mem hp, Set.indicator_of_mem hc.1,
        Set.indicator_of_mem hc.2]
      rcases p with ⟨r, φ⟩
      simp only [q, f, integrand, polarCoord_symm_apply, Prod.fst, Prod.snd]
      have hsum :
          (r * Real.cos φ) ^ 2 + (r * Real.sin φ) ^ 2 = r ^ 2 := by
        nlinarith [Real.sin_sq_add_cos_sq φ]
      rw [hsum]
      ring
    · have hc :
        ¬(p ∈ polarCoord.target ∧
          polarCoord.symm p ∈ quadrantBase a) := by
        intro h
        exact hp ((polar_characterization a ha p).mp h)
      rw [Set.indicator_of_notMem hp]
      by_cases ht : p ∈ polarCoord.target
      · have hb : polarCoord.symm p ∉ quadrantBase a :=
          fun h => hc ⟨ht, h⟩
        rw [Set.indicator_of_mem ht, Set.indicator_of_notMem hb]
        simp
      · rw [Set.indicator_of_notMem ht]
  have hqcont : Continuous q := by
    dsimp [q]
    fun_prop
  have hsubset :
      polarRegion a ⊆
        Set.Icc (0 : ℝ) a ×ˢ Set.Icc (0 : ℝ) (Real.pi / 4) := by
    rintro ⟨r, φ⟩ hp
    have hcosle : Real.cos (2 * φ) ≤ 1 := Real.cos_le_one _
    have hsqrtle : Real.sqrt (Real.cos (2 * φ)) ≤ 1 := by
      rw [Real.sqrt_le_one]
      exact hcosle
    exact
      ⟨⟨hp.2.2.1.le, hp.2.2.2.trans (by nlinarith)⟩,
        ⟨hp.1.le, hp.2.1.le⟩⟩
  have hbox :
      IsCompact
        (Set.Icc (0 : ℝ) a ×ˢ Set.Icc (0 : ℝ) (Real.pi / 4)) :=
    isCompact_Icc.prod isCompact_Icc
  have hqint : IntegrableOn q (polarRegion a) :=
    (hqcont.continuousOn.integrableOn_compact hbox).mono_set hsubset
  have hglobal : Integrable ((polarRegion a).indicator q) :=
    (integrable_indicator_iff (polarRegion_measurable a)).2 hqint
  have hinner : ∀ φ : ℝ,
      (∫ r : ℝ, (polarRegion a).indicator q (r, φ)) =
        (Set.Ioo (0 : ℝ) (Real.pi / 4)).indicator
          (fun φ =>
            ∫ r in (0 : ℝ)..a * Real.sqrt (Real.cos (2 * φ)),
              r ^ 2 / a * r) φ := by
    intro φ
    by_cases hφ : φ ∈ Set.Ioo (0 : ℝ) (Real.pi / 4)
    · rw [Set.indicator_of_mem hφ]
      have hcos2 : 0 ≤ Real.cos (2 * φ) :=
        Real.cos_nonneg_of_neg_pi_div_two_le_of_le
          ((neg_nonpos.mpr (by positivity : 0 ≤ Real.pi / 2)).trans
            (mul_nonneg (by norm_num) hφ.1.le))
          (by linarith [hφ.2])
      have hu0 :
          0 ≤ a * Real.sqrt (Real.cos (2 * φ)) :=
        mul_nonneg ha.le (Real.sqrt_nonneg _)
      have hind :
          (fun r : ℝ => (polarRegion a).indicator q (r, φ)) =
            (Set.Ioc (0 : ℝ)
              (a * Real.sqrt (Real.cos (2 * φ)))).indicator
              (fun r : ℝ => r ^ 2 / a * r) := by
        funext r
        have hmem :
            (r, φ) ∈ polarRegion a ↔
              r ∈ Set.Ioc (0 : ℝ)
                (a * Real.sqrt (Real.cos (2 * φ))) := by
          constructor
          · intro hp
            exact ⟨hp.2.2.1, hp.2.2.2⟩
          · intro hr
            exact ⟨hφ.1, hφ.2, hr.1, hr.2⟩
        by_cases hr :
            r ∈ Set.Ioc (0 : ℝ)
              (a * Real.sqrt (Real.cos (2 * φ)))
        · rw [Set.indicator_of_mem hr,
            Set.indicator_of_mem (hmem.mpr hr)]
          dsimp [q]
          ring
        · rw [Set.indicator_of_notMem hr,
            Set.indicator_of_notMem (fun hp => hr (hmem.mp hp))]
      rw [hind, MeasureTheory.integral_indicator measurableSet_Ioc]
      rw [← intervalIntegral.integral_of_le hu0]
    · rw [Set.indicator_of_notMem hφ]
      have hnone : ∀ r : ℝ, (r, φ) ∉ polarRegion a := by
        intro r hp
        exact hφ ⟨hp.1, hp.2.1⟩
      simp [hnone]
  calc
    (∫ p in quadrantBase a, integrand a p) =
        ∫ p : ℝ × ℝ, (quadrantBase a).indicator f p := by
          rw [MeasureTheory.integral_indicator hqbMeas]
    _ = ∫ p in polarCoord.target,
          p.1 * (quadrantBase a).indicator f (polarCoord.symm p) := by
          simpa [smul_eq_mul] using
            (integral_comp_polarCoord_symm
              ((quadrantBase a).indicator f)).symm
    _ = ∫ p : ℝ × ℝ, (polarRegion a).indicator q p := by
          rw [← MeasureTheory.integral_indicator
            polarCoord.open_target.measurableSet]
          apply MeasureTheory.integral_congr_ae
          exact Filter.Eventually.of_forall hpoint
    _ = ∫ φ : ℝ, ∫ r : ℝ,
          (polarRegion a).indicator q (r, φ) := by
          simpa using MeasureTheory.integral_prod_symm _ hglobal
    _ = ∫ φ : ℝ,
          (Set.Ioo (0 : ℝ) (Real.pi / 4)).indicator
            (fun φ =>
              ∫ r in (0 : ℝ)..a * Real.sqrt (Real.cos (2 * φ)),
                r ^ 2 / a * r) φ := by
          apply MeasureTheory.integral_congr_ae
          exact Filter.Eventually.of_forall hinner
    _ = ∫ φ in Set.Ioo (0 : ℝ) (Real.pi / 4),
          ∫ r in (0 : ℝ)..a * Real.sqrt (Real.cos (2 * φ)),
            r ^ 2 / a * r := by
          rw [MeasureTheory.integral_indicator measurableSet_Ioo]
    _ = ∫ φ in Set.Ioc (0 : ℝ) (Real.pi / 4),
          ∫ r in (0 : ℝ)..a * Real.sqrt (Real.cos (2 * φ)),
            r ^ 2 / a * r := by
          rw [Measure.restrict_congr_set Ioo_ae_eq_Ioc]
    _ = ∫ φ in (0 : ℝ)..Real.pi / 4,
          ∫ r in (0 : ℝ)..a * Real.sqrt (Real.cos (2 * φ)),
            r ^ 2 / a * r := by
          rw [intervalIntegral.integral_of_le
            (by linarith [Real.pi_pos])]

theorem gap3 (a : ℝ) (ha : 0 < a) :
    volume a =
      4 *
        ∫ φ in (0 : ℝ)..Real.pi / 4,
          ∫ r in (0 : ℝ)..a * Real.sqrt (Real.cos (2 * φ)),
            r ^ 2 / a * r := by
  rw [volume_quadrant a ha, quadrant_polar a ha]

private theorem radial_integral (a φ : ℝ) (ha : 0 < a)
    (hφ : φ ∈ Set.uIcc (0 : ℝ) (Real.pi / 4)) :
    (∫ r in (0 : ℝ)..a * Real.sqrt (Real.cos (2 * φ)),
        r ^ 2 / a * r) =
      a ^ 3 / 4 * Real.cos (2 * φ) ^ 2 := by
  have hφ' : 0 ≤ φ ∧ φ ≤ Real.pi / 4 := by
    rw [Set.uIcc_of_le (by positivity : (0 : ℝ) ≤ Real.pi / 4)] at hφ
    exact hφ
  have hcos : 0 ≤ Real.cos (2 * φ) :=
    Real.cos_nonneg_of_neg_pi_div_two_le_of_le
      (by linarith [Real.pi_pos])
      (by linarith [hφ'.2])
  have hsqrt :
      Real.sqrt (Real.cos (2 * φ)) ^ 2 = Real.cos (2 * φ) :=
    Real.sq_sqrt hcos
  let F : ℝ → ℝ := fun r => r ^ 4 / (4 * a)
  have hd : ∀ r : ℝ, HasDerivAt F (r ^ 2 / a * r) r := by
    intro r
    dsimp [F]
    convert ((hasDerivAt_id r).pow 4).div_const (4 * a) using 1 <;>
      simp only [id_eq]
    · field_simp [ne_of_gt ha]
      ring
  have hi : IntervalIntegrable (fun r : ℝ => r ^ 2 / a * r)
      MeasureTheory.volume 0
        (a * Real.sqrt (Real.cos (2 * φ))) := by
    exact (by fun_prop : Continuous (fun r : ℝ => r ^ 2 / a * r)).intervalIntegrable _ _
  calc
    _ = F (a * Real.sqrt (Real.cos (2 * φ))) - F 0 := by
      apply intervalIntegral.integral_eq_sub_of_hasDerivAt
      · intro r hr
        exact hd r
      · exact hi
    _ = _ := by
      dsimp [F]
      field_simp [ne_of_gt ha]
      rw [show Real.sqrt (Real.cos (2 * φ)) ^ 4 =
        (Real.sqrt (Real.cos (2 * φ)) ^ 2) ^ 2 by ring, hsqrt]
      ring

theorem gap4 (a : ℝ) (ha : 0 < a) :
    volume a =
      a ^ 3 *
        ∫ φ in (0 : ℝ)..Real.pi / 4,
          Real.cos (2 * φ) ^ 2 := by
  rw [gap3 a ha]
  calc
    4 * (∫ φ in (0 : ℝ)..Real.pi / 4,
      ∫ r in (0 : ℝ)..a * Real.sqrt (Real.cos (2 * φ)),
        r ^ 2 / a * r) =
        4 * ∫ φ in (0 : ℝ)..Real.pi / 4,
          a ^ 3 / 4 * Real.cos (2 * φ) ^ 2 := by
            congr 1
            apply intervalIntegral.integral_congr
            intro φ hφ
            exact radial_integral a φ ha hφ
    _ = a ^ 3 *
        ∫ φ in (0 : ℝ)..Real.pi / 4,
          Real.cos (2 * φ) ^ 2 := by
            rw [intervalIntegral.integral_const_mul]
            ring

private theorem cos_two_sq_integral :
    (∫ φ in (0 : ℝ)..Real.pi / 4,
      Real.cos (2 * φ) ^ 2) = Real.pi / 8 := by
  let F : ℝ → ℝ := fun φ => φ / 2 + Real.sin (4 * φ) / 8
  have hd : ∀ φ : ℝ,
      HasDerivAt F (Real.cos (2 * φ) ^ 2) φ := by
    intro φ
    have htrig :
        Real.cos (2 * φ) ^ 2 =
          1 / 2 + Real.cos (4 * φ) / 2 := by
      rw [Real.cos_sq]
      congr 1
      ring
    rw [htrig]
    convert
      ((hasDerivAt_id φ).div_const 2).add
        (((Real.hasDerivAt_sin (4 * φ)).comp φ
          ((hasDerivAt_const φ (4 : ℝ)).mul (hasDerivAt_id φ))).div_const 8)
      using 1 <;> ring
  have hi : IntervalIntegrable
      (fun φ : ℝ => Real.cos (2 * φ) ^ 2)
      MeasureTheory.volume 0 (Real.pi / 4) := by
    exact
      (by fun_prop : Continuous (fun φ : ℝ => Real.cos (2 * φ) ^ 2)).intervalIntegrable _ _
  calc
    _ = F (Real.pi / 4) - F 0 := by
      apply intervalIntegral.integral_eq_sub_of_hasDerivAt
      · intro φ hφ
        exact hd φ
      · exact hi
    _ = Real.pi / 8 := by
      dsimp [F]
      rw [show 4 * (Real.pi / 4) = Real.pi by ring,
        Real.sin_pi]
      simp
      ring

theorem gap5 (a : ℝ) (ha : 0 < a) :
    a ^ 3 *
        (∫ φ in (0 : ℝ)..Real.pi / 4,
          Real.cos (2 * φ) ^ 2) =
      Real.pi * a ^ 3 / 8 := by
  rw [cos_two_sq_integral]
  ring

theorem gap6 (a : ℝ) (ha : 0 < a) :
    volume a = Real.pi * a ^ 3 / 8 := by
  rw [gap4 a ha, gap5 a ha]

end

end ProofGap.Exercise4017
