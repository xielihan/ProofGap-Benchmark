import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise4118

noncomputable section

open MeasureTheory
open scoped Interval

def region (a b c : ℝ) : Set (ℝ × ℝ × ℝ) :=
  {p | (p.1 / a + p.2.1 / b) ^ 2 + (p.2.2 / c) ^ 2 ≤ 1 ∧
    0 < p.1 ∧ 0 < p.2.1 ∧ 0 < p.2.2}

def coordinateMap (a b c r phi psi : ℝ) : ℝ × ℝ × ℝ :=
  (a * r * Real.cos phi ^ 2 * Real.cos psi,
    b * r * Real.sin phi ^ 2 * Real.cos psi,
    c * r * Real.sin psi)

def parameterDomain : Set (ℝ × ℝ × ℝ) :=
  {p | 0 < p.1 ∧ p.1 ≤ 1 ∧
    0 < p.2.1 ∧ p.2.1 < Real.pi / 2 ∧
    0 < p.2.2 ∧ p.2.2 < Real.pi / 2}

def jacobianAbs (a b c r phi psi : ℝ) : ℝ :=
  |2 * a * b * c * r ^ 2 *
    Real.cos phi * Real.sin phi * Real.cos psi|

def volume (a b c : ℝ) : ℝ :=
  ∫ _ in region a b c, (1 : ℝ)

theorem gap1 (a b c r phi psi : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hr : 0 ≤ r)
    (hphi0 : 0 ≤ phi) (hphi1 : phi ≤ Real.pi / 2)
    (hpsi0 : 0 ≤ psi) (hpsi1 : psi ≤ Real.pi / 2) :
    jacobianAbs a b c r phi psi =
      2 * a * b * c * r ^ 2 *
        Real.cos phi * Real.sin phi * Real.cos psi := by
  have hsinphi :
      0 ≤ Real.sin phi :=
    Real.sin_nonneg_of_nonneg_of_le_pi hphi0
      (hphi1.trans (by linarith [Real.pi_pos]))
  have hcosphi :
      0 ≤ Real.cos phi :=
    Real.cos_nonneg_of_neg_pi_div_two_le_of_le
      (by linarith [Real.pi_pos]) hphi1
  have hcospsi :
      0 ≤ Real.cos psi :=
    Real.cos_nonneg_of_neg_pi_div_two_le_of_le
      (by linarith [Real.pi_pos]) hpsi1
  unfold jacobianAbs
  rw [abs_of_nonneg]
  positivity

private theorem exists_firstQuadrant_angle (x y : ℝ)
    (hx : 0 < x) (hy : 0 < y) :
    ∃ theta : ℝ,
      0 < theta ∧ theta < Real.pi / 2 ∧
      Real.sqrt (x ^ 2 + y ^ 2) * Real.cos theta = x ∧
      Real.sqrt (x ^ 2 + y ^ 2) * Real.sin theta = y := by
  let t : ℝ := y / x
  have ht : 0 < t := div_pos hy hx
  have htheta0 : 0 < Real.arctan t :=
    Real.arctan_pos.2 ht
  have htheta1 : Real.arctan t < Real.pi / 2 :=
    Real.arctan_lt_pi_div_two _
  have hdenrad : 0 < 1 + t ^ 2 := by positivity
  have hden : 0 < Real.sqrt (1 + t ^ 2) :=
    Real.sqrt_pos.2 hdenrad
  have hsumrad : 0 ≤ x ^ 2 + y ^ 2 := by positivity
  have hsumsq :
      Real.sqrt (x ^ 2 + y ^ 2) ^ 2 =
        x ^ 2 + y ^ 2 :=
    Real.sq_sqrt hsumrad
  have hdensq :
      Real.sqrt (1 + t ^ 2) ^ 2 =
        1 + t ^ 2 :=
    Real.sq_sqrt hdenrad.le
  have halg :
      x ^ 2 + y ^ 2 =
        x ^ 2 * (1 + t ^ 2) := by
    dsimp [t]
    field_simp [hx.ne']
  have hscale :
      Real.sqrt (x ^ 2 + y ^ 2) =
        x * Real.sqrt (1 + t ^ 2) := by
    have hright :
        (x * Real.sqrt (1 + t ^ 2)) ^ 2 =
          x ^ 2 + y ^ 2 := by
      rw [mul_pow, hdensq]
      exact halg.symm
    nlinarith [Real.sqrt_nonneg (x ^ 2 + y ^ 2),
      mul_pos hx hden]
  refine
    ⟨Real.arctan t, htheta0, htheta1, ?_, ?_⟩
  · rw [Real.cos_arctan, hscale]
    field_simp [hden.ne']
  · rw [Real.sin_arctan, hscale]
    dsimp [t]
    field_simp [hx.ne', hden.ne']

theorem gap2 (a b c : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (fun p => coordinateMap a b c p.1 p.2.1 p.2.2) ''
        parameterDomain =
      region a b c := by
  ext q
  constructor
  · rintro ⟨⟨r, phi, psi⟩,
      ⟨hr0, hr1, hphi0, hphi1, hpsi0, hpsi1⟩, rfl⟩
    change 0 < r at hr0
    change r ≤ 1 at hr1
    change 0 < phi at hphi0
    change phi < Real.pi / 2 at hphi1
    change 0 < psi at hpsi0
    change psi < Real.pi / 2 at hpsi1
    have hsinphi :
        0 < Real.sin phi :=
      Real.sin_pos_of_pos_of_lt_pi hphi0
        (hphi1.trans (half_lt_self Real.pi_pos))
    have hcosphi :
        0 < Real.cos phi :=
      Real.cos_pos_of_mem_Ioo
        ⟨(neg_lt_zero.mpr (half_pos Real.pi_pos)).trans hphi0,
          hphi1⟩
    have hsinpsi :
        0 < Real.sin psi :=
      Real.sin_pos_of_pos_of_lt_pi hpsi0
        (hpsi1.trans (half_lt_self Real.pi_pos))
    have hcospsi :
        0 < Real.cos psi :=
      Real.cos_pos_of_mem_Ioo
        ⟨(neg_lt_zero.mpr (half_pos Real.pi_pos)).trans hpsi0,
          hpsi1⟩
    have hxa :
        (a * r * Real.cos phi ^ 2 * Real.cos psi) / a =
          r * Real.cos phi ^ 2 * Real.cos psi := by
      field_simp [ha.ne']
    have hyb :
        (b * r * Real.sin phi ^ 2 * Real.cos psi) / b =
          r * Real.sin phi ^ 2 * Real.cos psi := by
      field_simp [hb.ne']
    have hzc :
        (c * r * Real.sin psi) / c =
          r * Real.sin psi := by
      field_simp [hc.ne']
    have hsum :
        r * Real.cos phi ^ 2 * Real.cos psi +
            r * Real.sin phi ^ 2 * Real.cos psi =
          r * Real.cos psi := by
      calc
        r * Real.cos phi ^ 2 * Real.cos psi +
              r * Real.sin phi ^ 2 * Real.cos psi =
            r * Real.cos psi *
              (Real.cos phi ^ 2 + Real.sin phi ^ 2) := by ring
        _ = r * Real.cos psi := by
          rw [Real.cos_sq_add_sin_sq]
          ring
    have hsphere :
        (r * Real.cos psi) ^ 2 +
            (r * Real.sin psi) ^ 2 =
          r ^ 2 := by
      calc
        (r * Real.cos psi) ^ 2 +
              (r * Real.sin psi) ^ 2 =
            r ^ 2 *
              (Real.cos psi ^ 2 + Real.sin psi ^ 2) := by ring
        _ = r ^ 2 := by
          rw [Real.cos_sq_add_sin_sq]
          ring
    change
      ((a * r * Real.cos phi ^ 2 * Real.cos psi) / a +
          (b * r * Real.sin phi ^ 2 * Real.cos psi) / b) ^ 2 +
            ((c * r * Real.sin psi) / c) ^ 2 ≤ 1 ∧
        0 < a * r * Real.cos phi ^ 2 * Real.cos psi ∧
        0 < b * r * Real.sin phi ^ 2 * Real.cos psi ∧
        0 < c * r * Real.sin psi
    rw [hxa, hyb, hzc, hsum]
    constructor
    · rw [hsphere]
      nlinarith
    · constructor
      · positivity
      · constructor <;> positivity
  · rcases q with ⟨x, y, z⟩
    rintro ⟨hball, hx, hy, hz⟩
    let u : ℝ := x / a
    let v : ℝ := y / b
    let w : ℝ := z / c
    have hu : 0 < u := div_pos hx ha
    have hv : 0 < v := div_pos hy hb
    have hw : 0 < w := div_pos hz hc
    have hball' :
        (u + v) ^ 2 + w ^ 2 ≤ 1 := by
      simpa [u, v, w] using hball
    obtain ⟨psi, hpsi0, hpsi1, hrcos, hrsin⟩ :=
      exists_firstQuadrant_angle (u + v) w
        (add_pos hu hv) hw
    let r : ℝ := Real.sqrt ((u + v) ^ 2 + w ^ 2)
    have hr0 : 0 < r := by
      apply Real.sqrt_pos.2
      positivity
    have hr1 : r ≤ 1 := by
      dsimp [r]
      rw [Real.sqrt_le_one]
      exact hball'
    have hsqrtu : 0 < Real.sqrt u :=
      Real.sqrt_pos.2 hu
    have hsqrtv : 0 < Real.sqrt v :=
      Real.sqrt_pos.2 hv
    obtain ⟨phi, hphi0, hphi1, hScos, hSsin⟩ :=
      exists_firstQuadrant_angle
        (Real.sqrt u) (Real.sqrt v) hsqrtu hsqrtv
    have hSsq :
        Real.sqrt
            (Real.sqrt u ^ 2 + Real.sqrt v ^ 2) ^ 2 =
          u + v := by
      rw [Real.sq_sqrt (by positivity)]
      rw [Real.sq_sqrt hu.le, Real.sq_sqrt hv.le]
    have hcos2 :
        (u + v) * Real.cos phi ^ 2 = u := by
      have h := congrArg (fun t : ℝ => t ^ 2) hScos
      nlinarith [Real.sq_sqrt hu.le]
    have hsin2 :
        (u + v) * Real.sin phi ^ 2 = v := by
      have h := congrArg (fun t : ℝ => t ^ 2) hSsin
      nlinarith [Real.sq_sqrt hv.le]
    have hrcos' : r * Real.cos psi = u + v := by
      simpa [r] using hrcos
    have hrsin' : r * Real.sin psi = w := by
      simpa [r] using hrsin
    refine
      ⟨(r, phi, psi),
        ⟨hr0, hr1, hphi0, hphi1, hpsi0, hpsi1⟩, ?_⟩
    apply Prod.ext
    · calc
        a * r * Real.cos phi ^ 2 * Real.cos psi =
            a * ((r * Real.cos psi) * Real.cos phi ^ 2) := by ring
        _ = a * ((u + v) * Real.cos phi ^ 2) := by rw [hrcos']
        _ = a * u := by rw [hcos2]
        _ = x := by
          dsimp [u]
          field_simp [ha.ne']
    · apply Prod.ext
      · calc
          b * r * Real.sin phi ^ 2 * Real.cos psi =
              b * ((r * Real.cos psi) * Real.sin phi ^ 2) := by ring
          _ = b * ((u + v) * Real.sin phi ^ 2) := by rw [hrcos']
          _ = b * v := by rw [hsin2]
          _ = y := by
            dsimp [v]
            field_simp [hb.ne']
      · calc
          c * r * Real.sin psi =
              c * (r * Real.sin psi) := by ring
          _ = c * w := by rw [hrsin']
          _ = z := by
            dsimp [w]
            field_simp [hc.ne']

private def sectionRadius (c z : ℝ) : ℝ :=
  Real.sqrt (1 - (z / c) ^ 2)

private theorem mem_region_iff_sections
    (a b c x y z : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (x, y, z) ∈ region a b c ↔
      (0 < z ∧ z ≤ c) ∧
      (0 < y ∧ y ≤ b * sectionRadius c z) ∧
      x ∈ Set.Ioc (0 : ℝ)
        (a * (sectionRadius c z - y / b)) := by
  constructor
  · rintro ⟨hball, hx, hy, hz⟩
    have hw0 : 0 < z / c := div_pos hz hc
    have hs0 : 0 < x / a + y / b :=
      add_pos (div_pos hx ha) (div_pos hy hb)
    have hw2 : (z / c) ^ 2 ≤ (1 : ℝ) ^ 2 := by
      nlinarith [sq_nonneg (x / a + y / b)]
    have hw1 : z / c ≤ 1 :=
      (sq_le_sq₀ hw0.le (by norm_num)).1 hw2
    have hzc : z ≤ c := (div_le_one hc).1 hw1
    have hrad :
        0 ≤ 1 - (z / c) ^ 2 := by
      nlinarith
    have hsqrt :
        sectionRadius c z ^ 2 =
          1 - (z / c) ^ 2 := by
      exact Real.sq_sqrt hrad
    have hs2 :
        (x / a + y / b) ^ 2 ≤
          sectionRadius c z ^ 2 := by
      rw [hsqrt]
      linarith
    have hsle :
        x / a + y / b ≤ sectionRadius c z :=
      (sq_le_sq₀ hs0.le (Real.sqrt_nonneg _)).1 hs2
    have hydiv :
        y / b ≤ sectionRadius c z := by
      linarith [div_pos hx ha]
    have hyupper :
        y ≤ b * sectionRadius c z := by
      have := (div_le_iff₀ hb).1 hydiv
      simpa [mul_comm] using this
    have hxdiv :
        x / a ≤ sectionRadius c z - y / b := by
      linarith
    have hxupper :
        x ≤ a * (sectionRadius c z - y / b) := by
      have := (div_le_iff₀ ha).1 hxdiv
      simpa [mul_comm] using this
    exact
      ⟨⟨hz, hzc⟩, ⟨hy, hyupper⟩, ⟨hx, hxupper⟩⟩
  · rintro ⟨⟨hz, hzc⟩, ⟨hy, hyupper⟩,
      ⟨hx, hxupper⟩⟩
    have hrad :
        0 ≤ 1 - (z / c) ^ 2 := by
      have hw0 : 0 ≤ z / c := (div_pos hz hc).le
      have hw1 : z / c ≤ 1 := (div_le_one hc).2 hzc
      nlinarith
    have hsqrt :
        sectionRadius c z ^ 2 =
          1 - (z / c) ^ 2 := by
      exact Real.sq_sqrt hrad
    have hydiv :
        y / b ≤ sectionRadius c z := by
      apply (div_le_iff₀ hb).2
      simpa [mul_comm] using hyupper
    have hxdiv :
        x / a ≤ sectionRadius c z - y / b := by
      apply (div_le_iff₀ ha).2
      simpa [mul_comm] using hxupper
    have hsle :
        x / a + y / b ≤ sectionRadius c z := by
      linarith
    have hs0 : 0 ≤ x / a + y / b :=
      (add_pos (div_pos hx ha) (div_pos hy hb)).le
    have hs2 :
        (x / a + y / b) ^ 2 ≤
          sectionRadius c z ^ 2 :=
      (sq_le_sq₀ hs0 (Real.sqrt_nonneg _)).2 hsle
    exact
      ⟨by rw [hsqrt] at hs2
          linarith,
        hx, hy, hz⟩

private theorem region_measurable (a b c : ℝ) :
    MeasurableSet (region a b c) := by
  unfold region
  measurability

private theorem region_subset_box (a b c : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    region a b c ⊆
      Set.Icc (0 : ℝ) a ×ˢ
        (Set.Icc (0 : ℝ) b ×ˢ Set.Icc (0 : ℝ) c) := by
  rintro ⟨x, y, z⟩ h
  rw [mem_region_iff_sections a b c x y z ha hb hc] at h
  rcases h with ⟨hz, hy, hx⟩
  have hradle : sectionRadius c z ≤ 1 := by
    unfold sectionRadius
    rw [Real.sqrt_le_one]
    nlinarith [sq_nonneg (z / c)]
  have hyb : y ≤ b := hy.2.trans
    (mul_le_of_le_one_right hb.le hradle)
  have hdiff :
      sectionRadius c z - y / b ≤ 1 := by
    have : 0 < y / b := div_pos hy.1 hb
    linarith
  have hxa : x ≤ a :=
    hx.2.trans (mul_le_of_le_one_right ha.le hdiff)
  exact
    ⟨⟨hx.1.le, hxa⟩,
      ⟨⟨hy.1.le, hyb⟩, hz.1.le, hz.2⟩⟩

private theorem region_indicator_integrable (a b c : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    Integrable
      ((region a b c).indicator
        (fun _p : ℝ × ℝ × ℝ => (1 : ℝ)))
      MeasureTheory.volume := by
  have hbox :
      IntegrableOn (fun _p : ℝ × ℝ × ℝ => (1 : ℝ))
        (Set.Icc (0 : ℝ) a ×ˢ
          (Set.Icc (0 : ℝ) b ×ˢ Set.Icc (0 : ℝ) c))
        MeasureTheory.volume :=
    ((continuous_const :
      Continuous (fun _p : ℝ × ℝ × ℝ => (1 : ℝ))).continuousOn).integrableOn_compact
        (isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc))
  exact
    (integrable_indicator_iff (region_measurable a b c)).2
      (hbox.mono_set (region_subset_box a b c ha hb hc))

private theorem volume_eq_integral_zyx
    (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    volume a b c =
      ∫ z : ℝ, ∫ y : ℝ, ∫ x : ℝ,
        (region a b c).indicator
          (fun _p : ℝ × ℝ × ℝ => (1 : ℝ)) (x, y, z) := by
  let g : (ℝ × ℝ × ℝ) → ℝ :=
    (region a b c).indicator (fun _p => (1 : ℝ))
  have hg : Integrable g MeasureTheory.volume :=
    region_indicator_integrable a b c ha hb hc
  have hp :
      MeasurePreserving
        (MeasurableEquiv.prodAssoc :
          (ℝ × ℝ) × ℝ ≃ᵐ ℝ × ℝ × ℝ) :=
    MeasureTheory.volume_preserving_prodAssoc
  have hgassoc :
      Integrable
        (fun p : (ℝ × ℝ) × ℝ =>
          g (p.1.1, p.1.2, p.2))
        MeasureTheory.volume := by
    simpa [Function.comp_def] using
      hp.integrable_comp_of_integrable hg
  calc
    volume a b c =
        ∫ p : ℝ × ℝ × ℝ, g p := by
      rw [volume, MeasureTheory.integral_indicator
        (region_measurable a b c)]
    _ = ∫ p : (ℝ × ℝ) × ℝ,
          g (p.1.1, p.1.2, p.2) := by
      symm
      simpa [Function.comp_def] using hp.integral_comp' g
    _ = ∫ z : ℝ, ∫ q : ℝ × ℝ,
          g (q.1, q.2, z) := by
      exact MeasureTheory.integral_prod_symm _ hgassoc
    _ = ∫ z : ℝ, ∫ y : ℝ, ∫ x : ℝ,
          g (x, y, z) := by
      apply integral_congr_ae
      filter_upwards [hgassoc.prod_left_ae] with z hz
      exact MeasureTheory.integral_prod_symm _ hz

private theorem volume_value
    (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    volume a b c = (1 / 3 : ℝ) * a * b * c := by
  classical
  let g : (ℝ × ℝ × ℝ) → ℝ :=
    (region a b c).indicator (fun _p => (1 : ℝ))
  have hxint (z y : ℝ) :
      (∫ x : ℝ, g (x, y, z)) =
        if hz : 0 < z ∧ z ≤ c then
          if hy : 0 < y ∧ y ≤ b * sectionRadius c z then
            a * (sectionRadius c z - y / b)
          else 0
        else 0 := by
    by_cases hz : 0 < z ∧ z ≤ c
    · rw [dif_pos hz]
      by_cases hy :
          0 < y ∧ y ≤ b * sectionRadius c z
      · rw [dif_pos hy]
        have hydiv :
            y / b ≤ sectionRadius c z := by
          apply (div_le_iff₀ hb).2
          simpa [mul_comm] using hy.2
        have hu0 :
            0 ≤ a * (sectionRadius c z - y / b) :=
          mul_nonneg ha.le (sub_nonneg.2 hydiv)
        calc
          (∫ x : ℝ, g (x, y, z)) =
              ∫ _x in
                Set.Ioc (0 : ℝ)
                  (a * (sectionRadius c z - y / b)),
                (1 : ℝ) := by
            rw [← MeasureTheory.integral_indicator measurableSet_Ioc]
            apply integral_congr_ae
            filter_upwards with x
            simp only [g, Set.indicator_apply]
            rw [mem_region_iff_sections
              a b c x y z ha hb hc]
            simp [hz, hy, Set.indicator_apply]
          _ = ∫ _x in
                (0 : ℝ)..a * (sectionRadius c z - y / b),
                (1 : ℝ) := by
            rw [intervalIntegral.integral_of_le hu0]
          _ = a * (sectionRadius c z - y / b) := by
            rw [intervalIntegral.integral_const]
            simp
      · rw [dif_neg hy]
        apply integral_eq_zero_of_ae
        filter_upwards with x
        change g (x, y, z) = (0 : ℝ)
        simp only [g, Set.indicator_apply]
        rw [mem_region_iff_sections
          a b c x y z ha hb hc]
        simp [hz, hy]
    · rw [dif_neg hz]
      apply integral_eq_zero_of_ae
      filter_upwards with x
      change g (x, y, z) = (0 : ℝ)
      simp only [g, Set.indicator_apply]
      rw [mem_region_iff_sections
        a b c x y z ha hb hc]
      simp [hz]
  have hyint (z : ℝ) :
      (∫ y : ℝ, ∫ x : ℝ, g (x, y, z)) =
        if hz : 0 < z ∧ z ≤ c then
          a * b / 2 * sectionRadius c z ^ 2
        else 0 := by
    by_cases hz : 0 < z ∧ z ≤ c
    · rw [dif_pos hz]
      have hR0 : 0 ≤ sectionRadius c z :=
        Real.sqrt_nonneg _
      have hU0 : 0 ≤ b * sectionRadius c z :=
        mul_nonneg hb.le hR0
      calc
        (∫ y : ℝ, ∫ x : ℝ, g (x, y, z)) =
            ∫ y in
              Set.Ioc (0 : ℝ) (b * sectionRadius c z),
              a * (sectionRadius c z - y / b) := by
          rw [← MeasureTheory.integral_indicator measurableSet_Ioc]
          apply integral_congr_ae
          filter_upwards with y
          rw [hxint]
          simp [hz, Set.indicator_apply]
        _ = ∫ y in
              (0 : ℝ)..b * sectionRadius c z,
              a * (sectionRadius c z - y / b) := by
          rw [intervalIntegral.integral_of_le hU0]
        _ = a * b / 2 * sectionRadius c z ^ 2 := by
          rw [show
            (fun y : ℝ =>
              a * (sectionRadius c z - y / b)) =
              fun y =>
                a * sectionRadius c z - (a / b) * y by
                funext y
                field_simp [hb.ne']
                ]
          have hconst :
              IntervalIntegrable
                (fun _y : ℝ => a * sectionRadius c z)
                MeasureTheory.volume 0
                  (b * sectionRadius c z) :=
            continuous_const.intervalIntegrable _ _
          have hlin :
              IntervalIntegrable
                (fun y : ℝ => (a / b) * y)
                MeasureTheory.volume 0
                  (b * sectionRadius c z) :=
            (continuous_const.mul continuous_id).intervalIntegrable _ _
          rw [intervalIntegral.integral_sub hconst hlin,
            intervalIntegral.integral_const,
            intervalIntegral.integral_const_mul,
            integral_id]
          simp only [smul_eq_mul, sub_zero]
          field_simp [hb.ne']
          ring
    · rw [dif_neg hz]
      apply integral_eq_zero_of_ae
      filter_upwards with y
      rw [hxint, dif_neg hz]
      rfl
  rw [volume_eq_integral_zyx a b c ha hb hc]
  change
    (∫ z : ℝ, ∫ y : ℝ, ∫ x : ℝ, g (x, y, z)) =
      (1 / 3 : ℝ) * a * b * c
  simp_rw [hyint]
  calc
    (∫ z : ℝ,
        if hz : 0 < z ∧ z ≤ c then
          a * b / 2 * sectionRadius c z ^ 2
        else 0) =
        ∫ z in Set.Ioc (0 : ℝ) c,
          a * b / 2 * (1 - (z / c) ^ 2) := by
      rw [← MeasureTheory.integral_indicator measurableSet_Ioc]
      apply integral_congr_ae
      filter_upwards with z
      by_cases hz : z ∈ Set.Ioc (0 : ℝ) c
      · have hrad :
            0 ≤ 1 - (z / c) ^ 2 := by
          have hw0 : 0 ≤ z / c :=
            (div_pos hz.1 hc).le
          have hw1 : z / c ≤ 1 :=
            (div_le_one hc).2 hz.2
          nlinarith
        have hsquare :
            sectionRadius c z ^ 2 =
              1 - (z / c) ^ 2 :=
          Real.sq_sqrt hrad
        have hzc : 0 < z ∧ z ≤ c := ⟨hz.1, hz.2⟩
        rw [dif_pos hzc, Set.indicator_of_mem hz, hsquare]
      · have hzc : ¬(0 < z ∧ z ≤ c) := by
          intro h
          exact hz ⟨h.1, h.2⟩
        rw [dif_neg hzc, Set.indicator_of_notMem hz]
    _ = ∫ z in (0 : ℝ)..c,
          a * b / 2 * (1 - (z / c) ^ 2) := by
      rw [intervalIntegral.integral_of_le hc.le]
    _ = (1 / 3 : ℝ) * a * b * c := by
      rw [show
        (fun z : ℝ =>
          a * b / 2 * (1 - (z / c) ^ 2)) =
          fun z =>
            a * b / 2 -
              (a * b / (2 * c ^ 2)) * z ^ 2 by
            funext z
            field_simp [hc.ne']
            ]
      have hconst :
          IntervalIntegrable
            (fun _z : ℝ => a * b / 2)
            MeasureTheory.volume 0 c :=
        continuous_const.intervalIntegrable _ _
      have hpow :
          IntervalIntegrable
            (fun z : ℝ =>
              (a * b / (2 * c ^ 2)) * z ^ 2)
            MeasureTheory.volume 0 c :=
        (continuous_const.mul (continuous_pow 2)).intervalIntegrable _ _
      rw [intervalIntegral.integral_sub hconst hpow,
        intervalIntegral.integral_const,
        intervalIntegral.integral_const_mul,
        integral_pow]
      simp only [smul_eq_mul, sub_zero]
      norm_num
      field_simp [hc.ne']
      ring

private theorem parameter_integral_value (a b c : ℝ) :
    2 * a * b * c *
        (∫ phi in (0 : ℝ)..Real.pi / 2,
          ∫ psi in (0 : ℝ)..Real.pi / 2,
            ∫ r in (0 : ℝ)..1,
              r ^ 2 * Real.cos phi * Real.sin phi *
                Real.cos psi) =
      (1 / 3 : ℝ) * a * b * c := by
  have hr :
      (∫ r in (0 : ℝ)..1, r ^ 2) = (1 / 3 : ℝ) := by
    rw [integral_pow]
    norm_num
  have hinner (phi psi : ℝ) :
      (∫ r in (0 : ℝ)..1,
          r ^ 2 * Real.cos phi * Real.sin phi *
            Real.cos psi) =
        (1 / 3 : ℝ) *
          (Real.cos phi * Real.sin phi) *
            Real.cos psi := by
    rw [show
      (fun r : ℝ =>
        r ^ 2 * Real.cos phi * Real.sin phi *
          Real.cos psi) =
        fun r =>
          (Real.cos phi * Real.sin phi *
            Real.cos psi) * r ^ 2 by
          funext r
          ring]
    rw [intervalIntegral.integral_const_mul, hr]
    ring
  simp_rw [hinner]
  have hpsi_factor (phi : ℝ) :
      (∫ psi in (0 : ℝ)..Real.pi / 2,
          (1 / 3 : ℝ) *
            (Real.cos phi * Real.sin phi) *
              Real.cos psi) =
        (1 / 3 : ℝ) *
          (Real.cos phi * Real.sin phi) *
            ∫ psi in (0 : ℝ)..Real.pi / 2,
              Real.cos psi := by
    rw [intervalIntegral.integral_const_mul]
  simp_rw [hpsi_factor]
  have houter :
      (∫ phi in (0 : ℝ)..Real.pi / 2,
          (1 / 3 : ℝ) *
            (Real.cos phi * Real.sin phi) *
              ∫ psi in (0 : ℝ)..Real.pi / 2,
                Real.cos psi) =
        (1 / 3 : ℝ) *
          (∫ phi in (0 : ℝ)..Real.pi / 2,
            Real.cos phi * Real.sin phi) *
          ∫ psi in (0 : ℝ)..Real.pi / 2,
            Real.cos psi := by
    rw [show
      (fun phi : ℝ =>
        (1 / 3 : ℝ) *
          (Real.cos phi * Real.sin phi) *
            ∫ psi in (0 : ℝ)..Real.pi / 2,
              Real.cos psi) =
        fun phi =>
          ((1 / 3 : ℝ) *
            ∫ psi in (0 : ℝ)..Real.pi / 2,
              Real.cos psi) *
            (Real.cos phi * Real.sin phi) by
          funext phi
          ring]
    rw [intervalIntegral.integral_const_mul]
    ring
  rw [houter]
  have hphi :
      (∫ phi in (0 : ℝ)..Real.pi / 2,
          Real.cos phi * Real.sin phi) =
        (1 / 2 : ℝ) := by
    let F : ℝ → ℝ :=
      fun x => Real.sin x ^ 2 / 2
    have hderiv (x : ℝ) :
        HasDerivAt F (Real.cos x * Real.sin x) x := by
      dsimp [F]
      convert ((Real.hasDerivAt_sin x).pow 2).div_const 2 using 1
      ring
    have hint :
        IntervalIntegrable
          (fun x : ℝ => Real.cos x * Real.sin x)
          MeasureTheory.volume 0 (Real.pi / 2) :=
      (Real.continuous_cos.mul Real.continuous_sin).intervalIntegrable _ _
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x _ => hderiv x) hint]
    simp [F]
  have hpsi :
      (∫ psi in (0 : ℝ)..Real.pi / 2,
          Real.cos psi) = 1 := by
    rw [integral_cos]
    simp
  rw [hphi, hpsi]
  ring

theorem gap3 (a b c : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    volume a b c =
      2 * a * b * c *
        ∫ phi in (0 : ℝ)..Real.pi / 2,
          ∫ psi in (0 : ℝ)..Real.pi / 2,
            ∫ r in (0 : ℝ)..1,
              r ^ 2 * Real.cos phi * Real.sin phi *
                Real.cos psi := by
  calc
    volume a b c = (1 / 3 : ℝ) * a * b * c :=
      volume_value a b c ha hb hc
    _ = 2 * a * b * c *
        ∫ phi in (0 : ℝ)..Real.pi / 2,
          ∫ psi in (0 : ℝ)..Real.pi / 2,
            ∫ r in (0 : ℝ)..1,
              r ^ 2 * Real.cos phi * Real.sin phi *
                Real.cos psi :=
      (parameter_integral_value a b c).symm

theorem gap4 (a b c : ℝ) :
    2 * a * b * c *
        (∫ phi in (0 : ℝ)..Real.pi / 2,
          ∫ psi in (0 : ℝ)..Real.pi / 2,
            ∫ r in (0 : ℝ)..1,
              r ^ 2 * Real.cos phi * Real.sin phi *
                Real.cos psi) =
      (2 / 3 : ℝ) * a * b * c *
        (∫ phi in (0 : ℝ)..Real.pi / 2,
          Real.cos phi * Real.sin phi) *
        (∫ psi in (0 : ℝ)..Real.pi / 2,
          Real.cos psi) := by
  have hr :
      (∫ r in (0 : ℝ)..1, r ^ 2) = (1 / 3 : ℝ) := by
    rw [integral_pow]
    norm_num
  have hinner (phi psi : ℝ) :
      (∫ r in (0 : ℝ)..1,
          r ^ 2 * Real.cos phi * Real.sin phi *
            Real.cos psi) =
        (1 / 3 : ℝ) *
          (Real.cos phi * Real.sin phi) *
            Real.cos psi := by
    rw [show
      (fun r : ℝ =>
        r ^ 2 * Real.cos phi * Real.sin phi *
          Real.cos psi) =
        fun r =>
          (Real.cos phi * Real.sin phi *
            Real.cos psi) * r ^ 2 by
          funext r
          ring]
    rw [intervalIntegral.integral_const_mul, hr]
    ring
  simp_rw [hinner]
  have hpsi (phi : ℝ) :
      (∫ psi in (0 : ℝ)..Real.pi / 2,
          (1 / 3 : ℝ) *
            (Real.cos phi * Real.sin phi) *
              Real.cos psi) =
        (1 / 3 : ℝ) *
          (Real.cos phi * Real.sin phi) *
            ∫ psi in (0 : ℝ)..Real.pi / 2,
              Real.cos psi := by
    rw [intervalIntegral.integral_const_mul]
  simp_rw [hpsi]
  have houter :
      (∫ phi in (0 : ℝ)..Real.pi / 2,
          (1 / 3 : ℝ) *
            (Real.cos phi * Real.sin phi) *
              ∫ psi in (0 : ℝ)..Real.pi / 2,
                Real.cos psi) =
        (1 / 3 : ℝ) *
          (∫ phi in (0 : ℝ)..Real.pi / 2,
            Real.cos phi * Real.sin phi) *
          ∫ psi in (0 : ℝ)..Real.pi / 2,
            Real.cos psi := by
    rw [show
      (fun phi : ℝ =>
        (1 / 3 : ℝ) *
          (Real.cos phi * Real.sin phi) *
            ∫ psi in (0 : ℝ)..Real.pi / 2,
              Real.cos psi) =
        fun phi =>
          ((1 / 3 : ℝ) *
            ∫ psi in (0 : ℝ)..Real.pi / 2,
              Real.cos psi) *
            (Real.cos phi * Real.sin phi) by
          funext phi
          ring]
    rw [intervalIntegral.integral_const_mul]
    ring
  rw [houter]
  ring

theorem gap5 (a b c : ℝ) :
    (2 / 3 : ℝ) * a * b * c *
        (∫ phi in (0 : ℝ)..Real.pi / 2,
          Real.cos phi * Real.sin phi) *
        (∫ psi in (0 : ℝ)..Real.pi / 2,
          Real.cos psi) =
      (1 / 3 : ℝ) * a * b * c := by
  have hphi :
      (∫ phi in (0 : ℝ)..Real.pi / 2,
          Real.cos phi * Real.sin phi) =
        (1 / 2 : ℝ) := by
    let F : ℝ → ℝ :=
      fun x => Real.sin x ^ 2 / 2
    have hderiv (x : ℝ) :
        HasDerivAt F (Real.cos x * Real.sin x) x := by
      dsimp [F]
      convert ((Real.hasDerivAt_sin x).pow 2).div_const 2 using 1
      ring
    have hint :
        IntervalIntegrable
          (fun x : ℝ => Real.cos x * Real.sin x)
          MeasureTheory.volume 0 (Real.pi / 2) :=
      (Real.continuous_cos.mul Real.continuous_sin).intervalIntegrable _ _
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x _ => hderiv x) hint]
    simp [F]
  have hpsi :
      (∫ psi in (0 : ℝ)..Real.pi / 2,
          Real.cos psi) = 1 := by
    rw [integral_cos]
    simp
  rw [hphi, hpsi]
  ring

theorem gap6 (a b c : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    volume a b c = (1 / 3 : ℝ) * a * b * c := by
  rw [gap3 a b c ha hb hc, gap4, gap5]

end

end ProofGap.Exercise4118
