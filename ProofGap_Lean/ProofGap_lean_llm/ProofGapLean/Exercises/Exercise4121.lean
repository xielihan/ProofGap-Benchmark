import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Group.Arithmetic
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise4121

noncomputable section

open MeasureTheory
open scoped Interval ENNReal

def region (a : ℝ) : Set (ℝ × ℝ × ℝ) :=
  {p | (p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2) ^ 3 ≤
    a ^ 6 * p.2.2 ^ 2 / (p.1 ^ 2 + p.2.1 ^ 2)}

def firstOctant : Set (ℝ × ℝ × ℝ) :=
  {p | 0 ≤ p.1 ∧ 0 ≤ p.2.1 ∧ 0 ≤ p.2.2}

def sphericalMap (r phi psi : ℝ) : ℝ × ℝ × ℝ :=
  (r * Real.cos phi * Real.cos psi,
    r * Real.sin phi * Real.cos psi,
    r * Real.sin psi)

def radialBound (a psi : ℝ) : ℝ :=
  a * Real.rpow (Real.tan psi) (1 / 3 : ℝ)

def parameterDomain (a : ℝ) : Set (ℝ × ℝ × ℝ) :=
  {p | 0 ≤ p.1 ∧ p.1 ≤ radialBound a p.2.2 ∧
    0 ≤ p.2.1 ∧ p.2.1 ≤ Real.pi / 2 ∧
    0 ≤ p.2.2 ∧ p.2.2 ≤ Real.pi / 2}

def volume (a : ℝ) : ℝ :=
  ∫ _ in region a, (1 : ℝ)

private theorem exists_quarter_angle (x y : ℝ)
    (hx : 0 ≤ x) (hy : 0 ≤ y) :
    ∃ theta : ℝ,
      0 ≤ theta ∧ theta ≤ Real.pi / 2 ∧
      Real.sqrt (x ^ 2 + y ^ 2) * Real.cos theta = x ∧
      Real.sqrt (x ^ 2 + y ^ 2) * Real.sin theta = y := by
  by_cases hx0 : x = 0
  · subst x
    refine ⟨Real.pi / 2, by positivity, le_rfl, ?_, ?_⟩
    · simp
    · norm_num
      rw [Real.sqrt_sq_eq_abs,
        abs_of_nonneg hy]
  · have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
    let t : ℝ := y / x
    have ht : 0 ≤ t := div_nonneg hy hx
    have htheta0 : 0 ≤ Real.arctan t :=
      Real.arctan_nonneg.mpr ht
    have htheta1 : Real.arctan t ≤ Real.pi / 2 :=
      (Real.arctan_lt_pi_div_two t).le
    have hdenrad : 0 < 1 + t ^ 2 := by positivity
    have hden : 0 < Real.sqrt (1 + t ^ 2) :=
      Real.sqrt_pos.2 hdenrad
    have hsumrad : 0 ≤ x ^ 2 + y ^ 2 := by positivity
    have hdensq :
        Real.sqrt (1 + t ^ 2) ^ 2 = 1 + t ^ 2 :=
      Real.sq_sqrt hdenrad.le
    have halg :
        x ^ 2 + y ^ 2 = x ^ 2 * (1 + t ^ 2) := by
      dsimp [t]
      field_simp [hx0]
    have hscale :
        Real.sqrt (x ^ 2 + y ^ 2) =
          x * Real.sqrt (1 + t ^ 2) := by
      have hsumsq :
          Real.sqrt (x ^ 2 + y ^ 2) ^ 2 =
            x ^ 2 + y ^ 2 :=
        Real.sq_sqrt hsumrad
      have hright :
          (x * Real.sqrt (1 + t ^ 2)) ^ 2 =
            x ^ 2 + y ^ 2 := by
        rw [mul_pow, hdensq]
        exact halg.symm
      nlinarith [Real.sqrt_nonneg (x ^ 2 + y ^ 2),
        mul_pos hxpos hden]
    refine
      ⟨Real.arctan t, htheta0, htheta1, ?_, ?_⟩
    · rw [Real.cos_arctan, hscale]
      field_simp [hden.ne']
    · rw [Real.sin_arctan, hscale]
      dsimp [t]
      field_simp [hx0, hden.ne']

theorem gap1 (a : ℝ) (ha : 0 < a) :
    (fun p => sphericalMap p.1 p.2.1 p.2.2) ''
        parameterDomain a =
      region a ∩ firstOctant := by
  ext q
  constructor
  · rintro ⟨⟨r, phi, psi⟩,
      ⟨hr0, hr1, hphi0, hphi1, hpsi0, hpsi1⟩, rfl⟩
    change 0 ≤ r at hr0
    change r ≤ radialBound a psi at hr1
    change 0 ≤ phi at hphi0
    change phi ≤ Real.pi / 2 at hphi1
    change 0 ≤ psi at hpsi0
    change psi ≤ Real.pi / 2 at hpsi1
    have hsinphi : 0 ≤ Real.sin phi :=
      Real.sin_nonneg_of_nonneg_of_le_pi hphi0
        (hphi1.trans (by linarith [Real.pi_pos]))
    have hcosphi : 0 ≤ Real.cos phi :=
      Real.cos_nonneg_of_neg_pi_div_two_le_of_le
        (by linarith [Real.pi_pos]) hphi1
    have hsinpsi : 0 ≤ Real.sin psi :=
      Real.sin_nonneg_of_nonneg_of_le_pi hpsi0
        (hpsi1.trans (by linarith [Real.pi_pos]))
    have hcospsi : 0 ≤ Real.cos psi :=
      Real.cos_nonneg_of_neg_pi_div_two_le_of_le
        (by linarith [Real.pi_pos]) hpsi1
    have hxy :
        (r * Real.cos phi * Real.cos psi) ^ 2 +
            (r * Real.sin phi * Real.cos psi) ^ 2 =
          r ^ 2 * Real.cos psi ^ 2 := by
      nlinarith [Real.cos_sq_add_sin_sq phi]
    have hsum :
        r ^ 2 * Real.cos psi ^ 2 +
            (r * Real.sin psi) ^ 2 =
          r ^ 2 := by
      nlinarith [Real.cos_sq_add_sin_sq psi]
    constructor
    · change
        ((r * Real.cos phi * Real.cos psi) ^ 2 +
              (r * Real.sin phi * Real.cos psi) ^ 2 +
              (r * Real.sin psi) ^ 2) ^ 3 ≤
          a ^ 6 * (r * Real.sin psi) ^ 2 /
            ((r * Real.cos phi * Real.cos psi) ^ 2 +
              (r * Real.sin phi * Real.cos psi) ^ 2)
      rw [hxy, hsum]
      by_cases hrzero : r = 0
      · simp [hrzero]
      have hrpos : 0 < r := lt_of_le_of_ne hr0 (Ne.symm hrzero)
      by_cases hcoszero : Real.cos psi = 0
      · have htan0 : Real.tan psi = 0 := by
          rw [Real.tan_eq_sin_div_cos, hcoszero, div_zero]
        have hrle0 : r ≤ 0 := by
          simpa [radialBound, htan0] using hr1
        linarith
      · have hcospos : 0 < Real.cos psi :=
          lt_of_le_of_ne hcospsi (Ne.symm hcoszero)
        have htan :
            0 ≤ Real.tan psi :=
          Real.tan_nonneg_of_nonneg_of_le_pi_div_two
            hpsi0 hpsi1
        let t : ℝ :=
          Real.rpow (Real.tan psi) (1 / 3 : ℝ)
        have ht0 : 0 ≤ t := Real.rpow_nonneg htan _
        have ht3 : t ^ 3 = Real.tan psi := by
          dsimp [t]
          have hp :=
            Real.rpow_inv_natCast_pow htan
              (n := 3) (by norm_num)
          simpa [show (1 / 3 : ℝ) = (3 : ℝ)⁻¹ by norm_num]
            using hp
        have hrle : r ≤ a * t := by
          simpa [radialBound, t] using hr1
        have hp6 : r ^ 6 ≤ (a * t) ^ 6 :=
          pow_le_pow_left₀ hr0 hrle 6
        have ht6 : t ^ 6 = Real.tan psi ^ 2 := by
          calc
            t ^ 6 = (t ^ 3) ^ 2 := by ring
            _ = Real.tan psi ^ 2 := by rw [ht3]
        have hbound :
            r ^ 6 ≤ a ^ 6 * Real.tan psi ^ 2 := by
          calc
            r ^ 6 ≤ (a * t) ^ 6 := hp6
            _ = a ^ 6 * Real.tan psi ^ 2 := by
              rw [mul_pow, ht6]
        have htanmul :
            Real.tan psi * Real.cos psi = Real.sin psi :=
          Real.tan_mul_cos hcoszero
        have hscaled :
            r ^ 6 * Real.cos psi ^ 2 ≤
              a ^ 6 * Real.sin psi ^ 2 := by
          calc
            r ^ 6 * Real.cos psi ^ 2 ≤
                (a ^ 6 * Real.tan psi ^ 2) *
                  Real.cos psi ^ 2 :=
              mul_le_mul_of_nonneg_right hbound (sq_nonneg _)
            _ = a ^ 6 * Real.sin psi ^ 2 := by
              rw [show
                (a ^ 6 * Real.tan psi ^ 2) *
                    Real.cos psi ^ 2 =
                  a ^ 6 *
                    (Real.tan psi * Real.cos psi) ^ 2 by ring,
                htanmul]
        have hden :
            0 < r ^ 2 * Real.cos psi ^ 2 := by positivity
        apply (le_div_iff₀ hden).2
        calc
          (r ^ 2) ^ 3 * (r ^ 2 * Real.cos psi ^ 2) =
              r ^ 2 * (r ^ 6 * Real.cos psi ^ 2) := by ring
          _ ≤ r ^ 2 * (a ^ 6 * Real.sin psi ^ 2) :=
            mul_le_mul_of_nonneg_left hscaled (sq_nonneg r)
          _ = a ^ 6 * (r * Real.sin psi) ^ 2 := by ring
    · change
        0 ≤ r * Real.cos phi * Real.cos psi ∧
          0 ≤ r * Real.sin phi * Real.cos psi ∧
          0 ≤ r * Real.sin psi
      exact ⟨by positivity, by positivity, by positivity⟩
  · rcases q with ⟨x, y, z⟩
    rintro ⟨hreg, hx, hy, hz⟩
    change
      (x ^ 2 + y ^ 2 + z ^ 2) ^ 3 ≤
        a ^ 6 * z ^ 2 / (x ^ 2 + y ^ 2) at hreg
    change 0 ≤ x at hx
    change 0 ≤ y at hy
    change 0 ≤ z at hz
    have hxy0 : 0 ≤ x ^ 2 + y ^ 2 := by positivity
    by_cases hxyzero : x ^ 2 + y ^ 2 = 0
    · have hxzero : x = 0 := by nlinarith [sq_nonneg x, sq_nonneg y]
      have hyzero : y = 0 := by nlinarith [sq_nonneg x, sq_nonneg y]
      subst x
      subst y
      have hzpow : (z ^ 2) ^ 3 ≤ 0 := by
        simpa using hreg
      have hzsq : z ^ 2 = 0 := by
        have hzle : z ^ 2 ≤ 0 := by
          by_contra h
          have hzpos : 0 < z ^ 2 := lt_of_not_ge h
          have hpowpos : 0 < (z ^ 2) ^ 3 := pow_pos hzpos 3
          linarith
        exact le_antisymm hzle (sq_nonneg z)
      have hzzero : z = 0 := sq_eq_zero_iff.mp hzsq
      subst z
      refine ⟨(0, 0, 0), ?_, ?_⟩
      · have hpihalf : (0 : ℝ) ≤ Real.pi / 2 := by positivity
        simp [parameterDomain, radialBound, hpihalf]
      · simp [sphericalMap]
    · have hxypos : 0 < x ^ 2 + y ^ 2 :=
        lt_of_le_of_ne hxy0 (Ne.symm hxyzero)
      let rho : ℝ := Real.sqrt (x ^ 2 + y ^ 2)
      have hrho0 : 0 ≤ rho := Real.sqrt_nonneg _
      have hrhopos : 0 < rho := Real.sqrt_pos.2 hxypos
      have hrho2 : rho ^ 2 = x ^ 2 + y ^ 2 :=
        Real.sq_sqrt hxy0
      obtain ⟨phi, hphi0, hphi1, hrhocos, hrhosin⟩ :=
        exists_quarter_angle x y hx hy
      obtain ⟨psi, hpsi0, hpsi1, hrcos, hrsin⟩ :=
        exists_quarter_angle rho z hrho0 hz
      let r : ℝ := Real.sqrt (rho ^ 2 + z ^ 2)
      have hr0 : 0 ≤ r := Real.sqrt_nonneg _
      have hrsumpos : 0 < rho ^ 2 + z ^ 2 := by positivity
      have hrpos : 0 < r := Real.sqrt_pos.2 hrsumpos
      have hr2 : r ^ 2 = rho ^ 2 + z ^ 2 :=
        Real.sq_sqrt hrsumpos.le
      have hrcos' : r * Real.cos psi = rho := by
        simpa [r] using hrcos
      have hrsin' : r * Real.sin psi = z := by
        simpa [r] using hrsin
      have hcospos : 0 < Real.cos psi := by
        have hp : 0 < r * Real.cos psi := by
          rw [hrcos']
          exact hrhopos
        rcases (mul_pos_iff.mp hp) with h | h
        · exact h.2
        · linarith
      have hzne : z ≠ 0 := by
        intro hzzero'
        have hleft :
            0 < (x ^ 2 + y ^ 2 + z ^ 2) ^ 3 := by
          rw [hzzero']
          norm_num
          positivity
        have hright :
            a ^ 6 * z ^ 2 / (x ^ 2 + y ^ 2) = 0 := by
          rw [hzzero']
          simp
        rw [hright] at hreg
        linarith
      have hzpos : 0 < z := lt_of_le_of_ne hz (Ne.symm hzne)
      have htan0 :
          0 ≤ Real.tan psi :=
        Real.tan_nonneg_of_nonneg_of_le_pi_div_two
          hpsi0 hpsi1
      have htanmul :
          Real.tan psi * Real.cos psi = Real.sin psi :=
        Real.tan_mul_cos hcospos.ne'
      have htanrho :
          Real.tan psi * rho = z := by
        calc
          Real.tan psi * rho =
              r * (Real.tan psi * Real.cos psi) := by
                rw [← hrcos']
                ring
          _ = r * Real.sin psi := by rw [htanmul]
          _ = z := hrsin'
      have htaneq :
          Real.tan psi = z / rho :=
        (eq_div_iff hrhopos.ne').2 htanrho
      have hsum :
          x ^ 2 + y ^ 2 + z ^ 2 = r ^ 2 := by
        rw [← hrho2, hr2]
      have hineq :
          r ^ 6 ≤ a ^ 6 * z ^ 2 / rho ^ 2 := by
        rw [show r ^ 6 = (r ^ 2) ^ 3 by ring, ← hsum, hrho2]
        exact hreg
      have hbound :
          r ^ 6 ≤ a ^ 6 * Real.tan psi ^ 2 := by
        calc
          r ^ 6 ≤ a ^ 6 * z ^ 2 / rho ^ 2 := hineq
          _ = a ^ 6 * Real.tan psi ^ 2 := by
            rw [htaneq]
            field_simp [hrhopos.ne']
      let t : ℝ :=
        Real.rpow (Real.tan psi) (1 / 3 : ℝ)
      have ht0 : 0 ≤ t := Real.rpow_nonneg htan0 _
      have ht3 : t ^ 3 = Real.tan psi := by
        dsimp [t]
        have hp :=
          Real.rpow_inv_natCast_pow htan0
            (n := 3) (by norm_num)
        simpa [show (1 / 3 : ℝ) = (3 : ℝ)⁻¹ by norm_num]
          using hp
      have ht6 : t ^ 6 = Real.tan psi ^ 2 := by
        calc
          t ^ 6 = (t ^ 3) ^ 2 := by ring
          _ = Real.tan psi ^ 2 := by rw [ht3]
      have hp6 : r ^ 6 ≤ (a * t) ^ 6 := by
        calc
          r ^ 6 ≤ a ^ 6 * Real.tan psi ^ 2 := hbound
          _ = (a * t) ^ 6 := by rw [mul_pow, ht6]
      have hrle : r ≤ a * t :=
        (pow_le_pow_iff_left₀ hr0 (mul_nonneg ha.le ht0)
          (by norm_num : (6 : ℕ) ≠ 0)).mp hp6
      refine ⟨(r, phi, psi), ?_, ?_⟩
      · exact
          ⟨hr0, by simpa [radialBound, t] using hrle,
            hphi0, hphi1, hpsi0, hpsi1⟩
      · apply Prod.ext
        · calc
            r * Real.cos phi * Real.cos psi =
                (r * Real.cos psi) * Real.cos phi := by ring
            _ = rho * Real.cos phi := by rw [hrcos']
            _ = x := hrhocos
        · apply Prod.ext
          · calc
              r * Real.sin phi * Real.cos psi =
                  (r * Real.cos psi) * Real.sin phi := by ring
              _ = rho * Real.sin phi := by rw [hrcos']
              _ = y := hrhosin
          · exact hrsin'

private def meridianRegion (a : ℝ) : Set (ℝ × ℝ) :=
  {q | (q.1 ^ 2 + q.2 ^ 2) ^ 3 ≤
    a ^ 6 * q.2 ^ 2 / q.1 ^ 2}

private theorem region_measurable (a : ℝ) :
    MeasurableSet (region a) := by
  unfold region
  measurability

private theorem meridianRegion_measurable (a : ℝ) :
    MeasurableSet (meridianRegion a) := by
  unfold meridianRegion
  measurability

private theorem region_polar_xy_iff
    (a rho phi z : ℝ) :
    (rho * Real.cos phi, rho * Real.sin phi, z) ∈ region a ↔
      (rho, z) ∈ meridianRegion a := by
  have hrad :
      (rho * Real.cos phi) ^ 2 +
          (rho * Real.sin phi) ^ 2 =
        rho ^ 2 := by
    nlinarith [Real.cos_sq_add_sin_sq phi]
  change
    (((rho * Real.cos phi) ^ 2 +
        (rho * Real.sin phi) ^ 2 + z ^ 2) ^ 3 ≤
      a ^ 6 * z ^ 2 /
        ((rho * Real.cos phi) ^ 2 +
          (rho * Real.sin phi) ^ 2)) ↔
      (rho ^ 2 + z ^ 2) ^ 3 ≤
        a ^ 6 * z ^ 2 / rho ^ 2
  rw [hrad]

private def meridianKernel (a rho z : ℝ) : ℝ≥0∞ :=
  (meridianRegion a).indicator
    (fun _q => ENNReal.ofReal rho) (rho, z)

private theorem meridianKernel_measurable (a : ℝ) :
    Measurable (fun q : ℝ × ℝ =>
      meridianKernel a q.1 q.2) := by
  change Measurable
    ((meridianRegion a).indicator
      (fun q : ℝ × ℝ => ENNReal.ofReal q.1))
  exact (ENNReal.measurable_ofReal.comp measurable_fst).indicator
    (meridianRegion_measurable a)

private theorem planar_slice_lintegral (a z : ℝ) :
    (∫⁻ q : ℝ × ℝ,
        (region a).indicator
          (fun _p => (1 : ℝ≥0∞)) (q.1, q.2, z)) =
      ENNReal.ofReal (2 * Real.pi) *
        ∫⁻ rho in Set.Ioi (0 : ℝ),
          meridianKernel a rho z := by
  classical
  let f : ℝ × ℝ → ℝ≥0∞ := fun q =>
    (region a).indicator
      (fun _p => (1 : ℝ≥0∞)) (q.1, q.2, z)
  have hp := lintegral_comp_polarCoord_symm f
  rw [polarCoord_target] at hp
  have hmeas :
      Measurable (fun rho : ℝ =>
        meridianKernel a rho z) := by
    change Measurable (fun rho : ℝ =>
      if (rho, z) ∈ meridianRegion a then
        ENNReal.ofReal rho else 0)
    exact Measurable.ite
      ((meridianRegion_measurable a).preimage
        (measurable_id.prodMk measurable_const))
      (ENNReal.measurable_ofReal.comp measurable_id)
      measurable_const
  have hpoint :
      ∀ p ∈ Set.Ioi (0 : ℝ) ×ˢ
          Set.Ioo (-Real.pi) Real.pi,
        ENNReal.ofReal p.1 • f (polarCoord.symm p) =
          meridianKernel a p.1 z := by
    rintro ⟨rho, phi⟩ ⟨hrho, _hphi⟩
    simp only [polarCoord_symm_apply, smul_eq_mul, f]
    by_cases hm : (rho, z) ∈ meridianRegion a
    · have hrmem :
          (rho * Real.cos phi, rho * Real.sin phi, z) ∈
            region a :=
        (region_polar_xy_iff a rho phi z).2 hm
      rw [Set.indicator_of_mem hrmem]
      simp [meridianKernel, hm]
    · have hrmem :
          (rho * Real.cos phi, rho * Real.sin phi, z) ∉
            region a := by
        simpa [region_polar_xy_iff a rho phi z] using hm
      rw [Set.indicator_of_notMem hrmem]
      simp [meridianKernel, hm]
  have hprod :
      (∫⁻ p in Set.Ioi (0 : ℝ) ×ˢ
          Set.Ioo (-Real.pi) Real.pi,
          ENNReal.ofReal p.1 • f (polarCoord.symm p)) =
        ∫⁻ rho in Set.Ioi (0 : ℝ),
          ∫⁻ _phi in Set.Ioo (-Real.pi) Real.pi,
            meridianKernel a rho z := by
    calc
      _ = ∫⁻ p in Set.Ioi (0 : ℝ) ×ˢ
            Set.Ioo (-Real.pi) Real.pi,
            meridianKernel a p.1 z := by
          apply setLIntegral_congr_fun
            (measurableSet_Ioi.prod measurableSet_Ioo)
          exact hpoint
      _ = _ := by
        rw [Measure.volume_eq_prod]
        rw [setLIntegral_prod]
        exact (hmeas.comp measurable_fst).aemeasurable
  rw [hprod] at hp
  have hconst (rho : ℝ) :
      (∫⁻ _phi in Set.Ioo (-Real.pi) Real.pi,
          meridianKernel a rho z) =
        meridianKernel a rho z *
          ENNReal.ofReal (2 * Real.pi) := by
    rw [setLIntegral_const, Real.volume_Ioo]
    congr 2
    ring
  simp_rw [hconst] at hp
  rw [lintegral_mul_const
    (ENNReal.ofReal (2 * Real.pi)) hmeas] at hp
  calc
    (∫⁻ q : ℝ × ℝ,
        (region a).indicator
          (fun _p => (1 : ℝ≥0∞)) (q.1, q.2, z)) =
        (∫⁻ rho in Set.Ioi (0 : ℝ),
          meridianKernel a rho z) *
            ENNReal.ofReal (2 * Real.pi) := hp.symm
    _ = ENNReal.ofReal (2 * Real.pi) *
          ∫⁻ rho in Set.Ioi (0 : ℝ),
            meridianKernel a rho z := mul_comm _ _

private theorem meridianKernel_even (a rho z : ℝ) :
    meridianKernel a rho (-z) =
      meridianKernel a rho z := by
  classical
  have hmem :
      (rho, -z) ∈ meridianRegion a ↔
        (rho, z) ∈ meridianRegion a := by
    simp only [meridianRegion, Set.mem_setOf_eq, neg_sq]
  by_cases hm : (rho, z) ∈ meridianRegion a
  · have hmneg : (rho, -z) ∈ meridianRegion a := hmem.2 hm
    simp [meridianKernel, hm, hmneg]
  · have hmneg : (rho, -z) ∉ meridianRegion a := by
      simpa [hmem] using hm
    simp [meridianKernel, hm, hmneg]

private theorem meridian_negative_eq_positive (a rho : ℝ) :
    (∫⁻ z in Set.Iio (0 : ℝ),
        meridianKernel a rho z) =
      ∫⁻ z in Set.Ioi (0 : ℝ),
        meridianKernel a rho z := by
  let e : ℝ ≃ᵐ ℝ :=
    { toFun := fun z => -z
      invFun := fun z => -z
      left_inv := neg_neg
      right_inv := neg_neg
      measurable_toFun := measurable_id.neg
      measurable_invFun := measurable_id.neg }
  have hmp : MeasurePreserving e :=
    Measure.measurePreserving_neg
      (MeasureTheory.volume : Measure ℝ)
  have hpre :
      e ⁻¹' Set.Ioi (0 : ℝ) = Set.Iio (0 : ℝ) := by
    ext z
    simp [e]
  have hchange :=
    hmp.setLIntegral_comp_preimage_emb e.measurableEmbedding
      (fun z => meridianKernel a rho z) (Set.Ioi (0 : ℝ))
  rw [hpre] at hchange
  calc
    (∫⁻ z in Set.Iio (0 : ℝ),
        meridianKernel a rho z) =
        ∫⁻ z in Set.Iio (0 : ℝ),
          meridianKernel a rho (e z) := by
      apply setLIntegral_congr_fun measurableSet_Iio
      intro z hz
      exact (meridianKernel_even a rho z).symm
    _ = ∫⁻ z in Set.Ioi (0 : ℝ),
          meridianKernel a rho z := hchange

private theorem meridian_full_eq_two_positive (a rho : ℝ) :
    (∫⁻ z : ℝ, meridianKernel a rho z) =
      2 * ∫⁻ z in Set.Ioi (0 : ℝ),
        meridianKernel a rho z := by
  rw [← setLIntegral_univ]
  rw [← Set.Iic_union_Ioi (a := (0 : ℝ))]
  rw [lintegral_union measurableSet_Ioi
    (Set.Iic_disjoint_Ioi le_rfl)]
  rw [← setLIntegral_congr
    (Iio_ae_eq_Iic :
      Set.Iio (0 : ℝ) =ᵐ[MeasureTheory.volume]
        Set.Iic 0)]
  rw [meridian_negative_eq_positive]
  rw [two_mul]

private theorem region_lintegral_factor (a : ℝ) :
    (∫⁻ p in region a, (1 : ℝ≥0∞)) =
      ENNReal.ofReal (2 * Real.pi) * 2 *
        ∫⁻ rho in Set.Ioi (0 : ℝ),
          ∫⁻ z in Set.Ioi (0 : ℝ),
            meridianKernel a rho z := by
  classical
  let g : ℝ × (ℝ × ℝ) → ℝ≥0∞ :=
    (region a).indicator (fun _p => (1 : ℝ≥0∞))
  have hg : Measurable g :=
    measurable_const.indicator (region_measurable a)
  rw [← lintegral_indicator (region_measurable a)]
  change (∫⁻ p : ℝ × (ℝ × ℝ), g p) = _
  let A : ((ℝ × ℝ) × ℝ) ≃ᵐ (ℝ × (ℝ × ℝ)) :=
    MeasurableEquiv.prodAssoc
  have hA : MeasurePreserving A :=
    MeasureTheory.volume_preserving_prodAssoc
  have hcomp :
      (∫⁻ p : ℝ × (ℝ × ℝ), g p) =
        ∫⁻ u : (ℝ × ℝ) × ℝ, g (A u) := by
    exact
      (hA.lintegral_comp_emb A.measurableEmbedding g).symm
  rw [hcomp]
  have hmeasA :
      Measurable (fun u : (ℝ × ℝ) × ℝ =>
        g (A u)) :=
    hg.comp A.measurable
  rw [Measure.volume_eq_prod (ℝ × ℝ) ℝ]
  rw [lintegral_prod_symm' _ hmeasA]
  have hslice (z : ℝ) :
      (∫⁻ q : ℝ × ℝ, g (A (q, z))) =
        ENNReal.ofReal (2 * Real.pi) *
          ∫⁻ rho in Set.Ioi (0 : ℝ),
            meridianKernel a rho z := by
    simpa [g, A] using planar_slice_lintegral a z
  simp_rw [hslice]
  have hradmeas :
      Measurable (fun z : ℝ =>
        ∫⁻ rho in Set.Ioi (0 : ℝ),
          meridianKernel a rho z) := by
    exact
      (meridianKernel_measurable a).lintegral_prod_left'
  rw [lintegral_const_mul
    (ENNReal.ofReal (2 * Real.pi)) hradmeas]
  have hswap :
      (∫⁻ z : ℝ,
          ∫⁻ rho in Set.Ioi (0 : ℝ),
            meridianKernel a rho z) =
        ∫⁻ rho in Set.Ioi (0 : ℝ),
          ∫⁻ z : ℝ,
            meridianKernel a rho z := by
    apply lintegral_lintegral_swap
    exact
      ((meridianKernel_measurable a).comp measurable_swap).aemeasurable
  rw [hswap]
  simp_rw [meridian_full_eq_two_positive]
  have hposmeas :
      Measurable (fun rho : ℝ =>
        ∫⁻ z in Set.Ioi (0 : ℝ),
          meridianKernel a rho z) := by
    exact
      (meridianKernel_measurable a).lintegral_prod_right'
  rw [lintegral_const_mul 2 hposmeas]
  ring

private theorem polar_symm_mem_positive_iff
    (r psi : ℝ) (hr : 0 < r)
    (hpsi : psi ∈ Set.Ioo (-Real.pi) Real.pi) :
    polarCoord.symm (r, psi) ∈
        Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ) ↔
      psi ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
  rw [polarCoord_symm_apply]
  constructor
  · rintro ⟨hrcos, hrsin⟩
    change 0 < r * Real.cos psi at hrcos
    change 0 < r * Real.sin psi at hrsin
    have hcos : 0 < Real.cos psi := by
      rcases (mul_pos_iff.mp hrcos) with h | h
      · exact h.2
      · linarith
    have hsin : 0 < Real.sin psi := by
      rcases (mul_pos_iff.mp hrsin) with h | h
      · exact h.2
      · linarith
    constructor
    · by_contra h
      have hnonpos : psi ≤ 0 := le_of_not_gt h
      have hsinnonpos :
          Real.sin psi ≤ 0 :=
        Real.sin_nonpos_of_nonpos_of_neg_pi_le
          hnonpos hpsi.1.le
      linarith
    · by_contra h
      have hhalf : Real.pi / 2 ≤ psi := le_of_not_gt h
      have hcosnonpos :
          Real.cos psi ≤ 0 :=
        Real.cos_nonpos_of_pi_div_two_le_of_le hhalf
          (by linarith [hpsi.2, Real.pi_pos])
      linarith
  · rintro ⟨hpsi0, hpsi1⟩
    exact
      ⟨mul_pos hr (Real.cos_pos_of_mem_Ioo
          ⟨by linarith [Real.pi_pos], hpsi1⟩),
        mul_pos hr
          (Real.sin_pos_of_pos_of_lt_pi hpsi0
            (hpsi1.trans (by linarith [Real.pi_pos])))⟩

private theorem meridian_polar_radial_iff
    (a r psi : ℝ) (ha : 0 < a) (hr : 0 < r)
    (hpsi0 : 0 < psi) (hpsi1 : psi < Real.pi / 2) :
    polarCoord.symm (r, psi) ∈ meridianRegion a ↔
      r ≤ radialBound a psi := by
  have hcos :
      0 < Real.cos psi :=
    Real.cos_pos_of_mem_Ioo
      ⟨by linarith [hpsi0, Real.pi_pos], hpsi1⟩
  have hsin :
      0 < Real.sin psi :=
    Real.sin_pos_of_pos_of_lt_pi hpsi0
      (hpsi1.trans (by linarith [Real.pi_pos]))
  have htan :
      0 < Real.tan psi :=
    Real.tan_pos_of_pos_of_lt_pi_div_two hpsi0 hpsi1
  have htanmul :
      Real.tan psi * Real.cos psi = Real.sin psi :=
    Real.tan_mul_cos hcos.ne'
  have htrig :
      (r * Real.cos psi) ^ 2 +
          (r * Real.sin psi) ^ 2 =
        r ^ 2 := by
    nlinarith [Real.cos_sq_add_sin_sq psi]
  have hden :
      0 < r ^ 2 * Real.cos psi ^ 2 := by positivity
  have hcore :
      polarCoord.symm (r, psi) ∈ meridianRegion a ↔
        r ^ 6 ≤ a ^ 6 * Real.tan psi ^ 2 := by
    rw [polarCoord_symm_apply]
    change
      (((r * Real.cos psi) ^ 2 +
          (r * Real.sin psi) ^ 2) ^ 3 ≤
        a ^ 6 * (r * Real.sin psi) ^ 2 /
          (r * Real.cos psi) ^ 2) ↔
        r ^ 6 ≤ a ^ 6 * Real.tan psi ^ 2
    rw [htrig]
    constructor
    · intro hm
      have hm' :=
        (le_div_iff₀ hden).1
          (show
            (r ^ 2) ^ 3 ≤
              a ^ 6 * (r * Real.sin psi) ^ 2 /
                (r ^ 2 * Real.cos psi ^ 2) by
            simpa [mul_pow] using hm)
      have hmul :
          r ^ 2 * (r ^ 6 * Real.cos psi ^ 2) ≤
            r ^ 2 * (a ^ 6 * Real.sin psi ^ 2) := by
        convert hm' using 1 <;> ring
      have hscaled :
          r ^ 6 * Real.cos psi ^ 2 ≤
            a ^ 6 * Real.sin psi ^ 2 :=
        le_of_mul_le_mul_left hmul (sq_pos_of_pos hr)
      have hscaled' :
          r ^ 6 * Real.cos psi ^ 2 ≤
            (a ^ 6 * Real.tan psi ^ 2) *
              Real.cos psi ^ 2 := by
        calc
          r ^ 6 * Real.cos psi ^ 2 ≤
              a ^ 6 * Real.sin psi ^ 2 := hscaled
          _ = (a ^ 6 * Real.tan psi ^ 2) *
                Real.cos psi ^ 2 := by
            rw [show
              (a ^ 6 * Real.tan psi ^ 2) *
                  Real.cos psi ^ 2 =
                a ^ 6 *
                  (Real.tan psi * Real.cos psi) ^ 2 by ring,
              htanmul]
      exact
        le_of_mul_le_mul_right hscaled' (sq_pos_of_pos hcos)
    · intro hm
      have hscaled :
          r ^ 6 * Real.cos psi ^ 2 ≤
            (a ^ 6 * Real.tan psi ^ 2) *
              Real.cos psi ^ 2 :=
        mul_le_mul_of_nonneg_right hm (sq_nonneg _)
      have hscaled' :
          r ^ 6 * Real.cos psi ^ 2 ≤
            a ^ 6 * Real.sin psi ^ 2 := by
        calc
          r ^ 6 * Real.cos psi ^ 2 ≤
              (a ^ 6 * Real.tan psi ^ 2) *
                Real.cos psi ^ 2 := hscaled
          _ = a ^ 6 * Real.sin psi ^ 2 := by
            rw [show
              (a ^ 6 * Real.tan psi ^ 2) *
                  Real.cos psi ^ 2 =
                a ^ 6 *
                  (Real.tan psi * Real.cos psi) ^ 2 by ring,
              htanmul]
      rw [show
        (r * Real.cos psi) ^ 2 =
          r ^ 2 * Real.cos psi ^ 2 by ring]
      apply (le_div_iff₀ hden).2
      calc
        (r ^ 2) ^ 3 *
            (r ^ 2 * Real.cos psi ^ 2) =
            r ^ 2 *
              (r ^ 6 * Real.cos psi ^ 2) := by ring
        _ ≤ r ^ 2 *
              (a ^ 6 * Real.sin psi ^ 2) :=
          mul_le_mul_of_nonneg_left hscaled' (sq_nonneg r)
        _ = a ^ 6 * (r * Real.sin psi) ^ 2 := by ring
  rw [hcore]
  let t : ℝ :=
    Real.rpow (Real.tan psi) (1 / 3 : ℝ)
  have ht0 : 0 ≤ t := Real.rpow_nonneg htan.le _
  have ht3 : t ^ 3 = Real.tan psi := by
    dsimp [t]
    have hp :=
      Real.rpow_inv_natCast_pow htan.le
        (n := 3) (by norm_num)
    simpa [show (1 / 3 : ℝ) = (3 : ℝ)⁻¹ by norm_num]
      using hp
  have ht6 : t ^ 6 = Real.tan psi ^ 2 := by
    calc
      t ^ 6 = (t ^ 3) ^ 2 := by ring
      _ = Real.tan psi ^ 2 := by rw [ht3]
  have heq :
      (a * t) ^ 6 =
        a ^ 6 * Real.tan psi ^ 2 := by
    rw [mul_pow, ht6]
  rw [← heq]
  simpa [radialBound, t] using
    (pow_le_pow_iff_left₀ hr.le (mul_nonneg ha.le ht0)
      (by norm_num : (6 : ℕ) ≠ 0))

private def positiveMeridianKernel (a : ℝ)
    (q : ℝ × ℝ) : ℝ≥0∞ :=
  (Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ)).indicator
    (fun q => meridianKernel a q.1 q.2) q

private theorem positiveMeridianKernel_measurable (a : ℝ) :
    Measurable (positiveMeridianKernel a) := by
  exact (meridianKernel_measurable a).indicator
    (measurableSet_Ioi.prod measurableSet_Ioi)

private theorem second_polar_pointwise
    (a : ℝ) (ha : 0 < a) (p : ℝ × ℝ)
    (hp : p ∈ polarCoord.target) :
    ENNReal.ofReal p.1 •
        positiveMeridianKernel a (polarCoord.symm p) =
      (Set.Ioo (0 : ℝ) (Real.pi / 2)).indicator
        (fun psi =>
          (Set.Iic (radialBound a psi)).indicator
            (fun r =>
              ENNReal.ofReal
                (r ^ 2 * Real.cos psi)) p.1) p.2 := by
  rcases p with ⟨r, psi⟩
  rw [polarCoord_target] at hp
  have hr : 0 < r := hp.1
  have hquad :=
    polar_symm_mem_positive_iff r psi hr hp.2
  by_cases hpsi :
      psi ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)
  · have hq :
        polarCoord.symm (r, psi) ∈
          Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ) :=
      hquad.2 hpsi
    have hrad :=
      meridian_polar_radial_iff
        a r psi ha hr hpsi.1 hpsi.2
    by_cases hrle : r ≤ radialBound a psi
    · have hm :
          polarCoord.symm (r, psi) ∈ meridianRegion a :=
        hrad.2 hrle
      have hrmem :
          r ∈ Set.Iic (radialBound a psi) := hrle
      simp only [Prod.fst, Prod.snd, smul_eq_mul]
      rw [positiveMeridianKernel, Set.indicator_of_mem hq,
        meridianKernel, Set.indicator_of_mem hm,
        Set.indicator_of_mem hpsi,
        Set.indicator_of_mem hrmem,
        polarCoord_symm_apply]
      rw [← ENNReal.ofReal_mul hr.le]
      congr 1
      ring
    · have hm :
          polarCoord.symm (r, psi) ∉ meridianRegion a := by
        exact fun h => hrle (hrad.1 h)
      have hrmem :
          r ∉ Set.Iic (radialBound a psi) := hrle
      simp only [Prod.fst, Prod.snd, smul_eq_mul]
      rw [positiveMeridianKernel, Set.indicator_of_mem hq,
        meridianKernel, Set.indicator_of_notMem hm,
        Set.indicator_of_mem hpsi,
        Set.indicator_of_notMem hrmem]
      simp
  · have hq :
        polarCoord.symm (r, psi) ∉
          Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ) := by
      intro hqmem
      exact hpsi (hquad.1 hqmem)
    simp only [Prod.fst, Prod.snd, smul_eq_mul]
    rw [positiveMeridianKernel, Set.indicator_of_notMem hq,
      Set.indicator_of_notMem hpsi]
    simp

private theorem positive_meridian_polar_lintegral
    (a : ℝ) (ha : 0 < a) :
    (∫⁻ rho in Set.Ioi (0 : ℝ),
        ∫⁻ z in Set.Ioi (0 : ℝ),
          meridianKernel a rho z) =
      ∫⁻ psi in Set.Ioo (0 : ℝ) (Real.pi / 2),
        ∫⁻ r in Set.Ioc (0 : ℝ) (radialBound a psi),
          ENNReal.ofReal (r ^ 2 * Real.cos psi) := by
  classical
  have hquad :
      (∫⁻ q in Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ),
          meridianKernel a q.1 q.2) =
        ∫⁻ rho in Set.Ioi (0 : ℝ),
          ∫⁻ z in Set.Ioi (0 : ℝ),
            meridianKernel a rho z := by
    rw [Measure.volume_eq_prod]
    rw [setLIntegral_prod]
    exact (meridianKernel_measurable a).aemeasurable
  have hwhole :
      (∫⁻ q : ℝ × ℝ, positiveMeridianKernel a q) =
        ∫⁻ q in Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ),
          meridianKernel a q.1 q.2 := by
    change
      (∫⁻ q : ℝ × ℝ,
        (Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ)).indicator
          (fun q => meridianKernel a q.1 q.2) q) = _
    rw [lintegral_indicator
      (measurableSet_Ioi.prod measurableSet_Ioi)]
  have hp :=
    lintegral_comp_polarCoord_symm
      (positiveMeridianKernel a)
  have hpolarMeas :
      Measurable (fun p : ℝ × ℝ =>
        ENNReal.ofReal p.1 *
          positiveMeridianKernel a (polarCoord.symm p)) :=
    (ENNReal.measurable_ofReal.comp measurable_fst).mul
      ((positiveMeridianKernel_measurable a).comp
        continuous_polarCoord_symm.measurable)
  have hiter :
      (∫⁻ p in polarCoord.target,
          ENNReal.ofReal p.1 •
            positiveMeridianKernel a (polarCoord.symm p)) =
        ∫⁻ psi in Set.Ioo (-Real.pi) Real.pi,
          ∫⁻ r in Set.Ioi (0 : ℝ),
            ENNReal.ofReal r •
              positiveMeridianKernel a
                (polarCoord.symm (r, psi)) := by
    rw [polarCoord_target, Measure.volume_eq_prod]
    rw [setLIntegral_prod_symm]
    simpa only [smul_eq_mul] using hpolarMeas.aemeasurable
  have hinner (psi : ℝ)
      (hpsiTarget : psi ∈ Set.Ioo (-Real.pi) Real.pi) :
      (∫⁻ r in Set.Ioi (0 : ℝ),
          ENNReal.ofReal r •
            positiveMeridianKernel a
              (polarCoord.symm (r, psi))) =
        (Set.Ioo (0 : ℝ) (Real.pi / 2)).indicator
          (fun psi =>
            ∫⁻ r in Set.Ioc (0 : ℝ) (radialBound a psi),
              ENNReal.ofReal
                (r ^ 2 * Real.cos psi)) psi := by
    by_cases hpsi :
        psi ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)
    · rw [Set.indicator_of_mem hpsi]
      calc
        (∫⁻ r in Set.Ioi (0 : ℝ),
            ENNReal.ofReal r •
              positiveMeridianKernel a
                (polarCoord.symm (r, psi))) =
            ∫⁻ r in Set.Ioi (0 : ℝ),
              (Set.Iic (radialBound a psi)).indicator
                (fun r =>
                  ENNReal.ofReal
                    (r ^ 2 * Real.cos psi)) r := by
          apply setLIntegral_congr_fun measurableSet_Ioi
          intro r hr
          have hp' :
              (r, psi) ∈ polarCoord.target := by
            rw [polarCoord_target]
            exact ⟨hr, hpsiTarget⟩
          simpa [hpsi] using
            second_polar_pointwise a ha (r, psi) hp'
        _ = ∫⁻ r in
              Set.Ioc (0 : ℝ) (radialBound a psi),
              ENNReal.ofReal
                (r ^ 2 * Real.cos psi) := by
          rw [← lintegral_indicator measurableSet_Ioi]
          rw [Set.indicator_indicator]
          rw [lintegral_indicator
            (measurableSet_Ioi.inter measurableSet_Iic)]
          have hinter :
              Set.Ioi (0 : ℝ) ∩
                  Set.Iic (radialBound a psi) =
                Set.Ioc (0 : ℝ) (radialBound a psi) := by
            ext r
            simp
          rw [hinter]
    · rw [Set.indicator_of_notMem hpsi]
      calc
        (∫⁻ r in Set.Ioi (0 : ℝ),
            ENNReal.ofReal r •
              positiveMeridianKernel a
                (polarCoord.symm (r, psi))) =
            ∫⁻ _r in Set.Ioi (0 : ℝ), (0 : ℝ≥0∞) := by
          apply setLIntegral_congr_fun measurableSet_Ioi
          intro r hr
          have hp' :
              (r, psi) ∈ polarCoord.target := by
            rw [polarCoord_target]
            exact ⟨hr, hpsiTarget⟩
          have hpw :=
            second_polar_pointwise a ha (r, psi) hp'
          rw [Set.indicator_of_notMem hpsi] at hpw
          simpa using hpw
        _ = 0 := by simp
  rw [← hquad, ← hwhole, ← hp, hiter]
  calc
    (∫⁻ psi in Set.Ioo (-Real.pi) Real.pi,
        ∫⁻ r in Set.Ioi (0 : ℝ),
          ENNReal.ofReal r •
            positiveMeridianKernel a
              (polarCoord.symm (r, psi))) =
        ∫⁻ psi in Set.Ioo (-Real.pi) Real.pi,
          (Set.Ioo (0 : ℝ) (Real.pi / 2)).indicator
            (fun psi =>
              ∫⁻ r in
                  Set.Ioc (0 : ℝ) (radialBound a psi),
                ENNReal.ofReal
                  (r ^ 2 * Real.cos psi)) psi := by
      apply setLIntegral_congr_fun measurableSet_Ioo
      exact hinner
    _ = ∫⁻ psi in Set.Ioo (0 : ℝ) (Real.pi / 2),
          ∫⁻ r in Set.Ioc (0 : ℝ) (radialBound a psi),
            ENNReal.ofReal
              (r ^ 2 * Real.cos psi) := by
      rw [← lintegral_indicator measurableSet_Ioo]
      rw [Set.indicator_indicator]
      rw [lintegral_indicator
        (measurableSet_Ioo.inter measurableSet_Ioo)]
      have hinter :
          Set.Ioo (-Real.pi) Real.pi ∩
              Set.Ioo (0 : ℝ) (Real.pi / 2) =
            Set.Ioo (0 : ℝ) (Real.pi / 2) := by
        apply Set.inter_eq_right.mpr
        intro psi hpsi
        exact
          ⟨by linarith [hpsi.1, Real.pi_pos],
            by linarith [hpsi.2, Real.pi_pos]⟩
      rw [hinter]

private theorem radial_real_set_integral_value
    (a psi : ℝ) (ha : 0 < a)
    (hpsi0 : 0 < psi) (hpsi1 : psi < Real.pi / 2) :
    (∫ r in Set.Ioc (0 : ℝ) (radialBound a psi),
        r ^ 2 * Real.cos psi) =
      a ^ 3 / 3 * Real.sin psi := by
  have htan : 0 ≤ Real.tan psi :=
    (Real.tan_pos_of_pos_of_lt_pi_div_two hpsi0 hpsi1).le
  have hcube :
      radialBound a psi ^ 3 =
        a ^ 3 * Real.tan psi := by
    have hp :=
      Real.rpow_inv_natCast_pow htan
        (n := 3) (by norm_num)
    unfold radialBound
    rw [mul_pow]
    have hexp : (1 / 3 : ℝ) = (3 : ℝ)⁻¹ := by
      norm_num
    rw [hexp]
    exact congrArg (fun t : ℝ => a ^ 3 * t) hp
  have hboundpos : 0 < radialBound a psi := by
    unfold radialBound
    exact mul_pos ha
      (Real.rpow_pos_of_pos
        (Real.tan_pos_of_pos_of_lt_pi_div_two hpsi0 hpsi1) _)
  calc
    (∫ r in Set.Ioc (0 : ℝ) (radialBound a psi),
        r ^ 2 * Real.cos psi) =
        ∫ r in (0 : ℝ)..radialBound a psi,
          r ^ 2 * Real.cos psi :=
      (intervalIntegral.integral_of_le hboundpos.le).symm
    _ = ∫ r in (0 : ℝ)..radialBound a psi,
          Real.cos psi * r ^ 2 := by
      apply intervalIntegral.integral_congr
      intro r hr
      ring
    _ = Real.cos psi *
          ∫ r in (0 : ℝ)..radialBound a psi,
            r ^ 2 := by
      rw [intervalIntegral.integral_const_mul]
    _ = Real.cos psi *
          (radialBound a psi ^ 3 / 3) := by
      rw [integral_pow]
      norm_num
    _ = a ^ 3 / 3 * Real.sin psi := by
      rw [hcube]
      rw [show
        Real.cos psi * (a ^ 3 * Real.tan psi / 3) =
          a ^ 3 / 3 *
            (Real.tan psi * Real.cos psi) by ring]
      rw [Real.tan_mul_cos
        (Real.cos_pos_of_mem_Ioo
          ⟨by linarith [hpsi0, Real.pi_pos], hpsi1⟩).ne']

private theorem radial_lintegral_value
    (a psi : ℝ) (ha : 0 < a)
    (hpsi0 : 0 < psi) (hpsi1 : psi < Real.pi / 2) :
    (∫⁻ r in Set.Ioc (0 : ℝ) (radialBound a psi),
        ENNReal.ofReal (r ^ 2 * Real.cos psi)) =
      ENNReal.ofReal (a ^ 3 / 3 * Real.sin psi) := by
  let f : ℝ → ℝ := fun r => r ^ 2 * Real.cos psi
  have hfcont : Continuous f := by
    dsimp [f]
    fun_prop
  have hfint :
      IntegrableOn f
        (Set.Ioc (0 : ℝ) (radialBound a psi))
        MeasureTheory.volume := by
    exact
      (hfcont.continuousOn.integrableOn_compact isCompact_Icc).mono_set
        Set.Ioc_subset_Icc_self
  have hfnn :
      0 ≤ᵐ[MeasureTheory.volume.restrict
        (Set.Ioc (0 : ℝ) (radialBound a psi))] f := by
    filter_upwards
      [ae_restrict_mem measurableSet_Ioc] with r hr
    dsimp [f]
    exact mul_nonneg (sq_nonneg r)
      (Real.cos_pos_of_mem_Ioo
        ⟨by linarith [hpsi0, Real.pi_pos], hpsi1⟩).le
  rw [← ofReal_integral_eq_lintegral_ofReal hfint hfnn]
  exact congrArg ENNReal.ofReal
    (radial_real_set_integral_value a psi ha hpsi0 hpsi1)

private theorem positive_meridian_lintegral_value
    (a : ℝ) (ha : 0 < a) :
    (∫⁻ rho in Set.Ioi (0 : ℝ),
        ∫⁻ z in Set.Ioi (0 : ℝ),
          meridianKernel a rho z) =
      ENNReal.ofReal (a ^ 3 / 3) := by
  rw [positive_meridian_polar_lintegral a ha]
  have hpoint (psi : ℝ)
      (hpsi : psi ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
      (∫⁻ r in Set.Ioc (0 : ℝ) (radialBound a psi),
          ENNReal.ofReal (r ^ 2 * Real.cos psi)) =
        ENNReal.ofReal (a ^ 3 / 3 * Real.sin psi) :=
    radial_lintegral_value a psi ha hpsi.1 hpsi.2
  rw [setLIntegral_congr_fun measurableSet_Ioo hpoint]
  let f : ℝ → ℝ := fun psi =>
    a ^ 3 / 3 * Real.sin psi
  have hfcont : Continuous f := by
    dsimp [f]
    fun_prop
  have hfint :
      IntegrableOn f
        (Set.Ioo (0 : ℝ) (Real.pi / 2))
        MeasureTheory.volume := by
    exact
      (hfcont.continuousOn.integrableOn_compact isCompact_Icc).mono_set
        Set.Ioo_subset_Icc_self
  have hfnn :
      0 ≤ᵐ[MeasureTheory.volume.restrict
        (Set.Ioo (0 : ℝ) (Real.pi / 2))] f := by
    filter_upwards
      [ae_restrict_mem measurableSet_Ioo] with psi hpsi
    dsimp [f]
    exact mul_nonneg (by positivity)
      (Real.sin_pos_of_pos_of_lt_pi hpsi.1
        (hpsi.2.trans (by linarith [Real.pi_pos]))).le
  rw [← ofReal_integral_eq_lintegral_ofReal hfint hfnn]
  congr 1
  calc
    (∫ psi in Set.Ioo (0 : ℝ) (Real.pi / 2),
        f psi) =
        ∫ psi in (0 : ℝ)..Real.pi / 2,
          a ^ 3 / 3 * Real.sin psi := by
      rw [← integral_Ioc_eq_integral_Ioo]
      exact (intervalIntegral.integral_of_le
        (by positivity : (0 : ℝ) ≤ Real.pi / 2)).symm
    _ = a ^ 3 / 3 *
          ∫ psi in (0 : ℝ)..Real.pi / 2,
            Real.sin psi := by
      rw [intervalIntegral.integral_const_mul]
    _ = a ^ 3 / 3 := by
      rw [integral_sin]
      simp

private theorem volume_value
    (a : ℝ) (ha : 0 < a) :
    volume a = 4 * Real.pi * a ^ 3 / 3 := by
  have hmeasure := region_lintegral_factor a
  rw [positive_meridian_lintegral_value a ha] at hmeasure
  rw [setLIntegral_one] at hmeasure
  unfold volume
  rw [integral_const]
  simp only [smul_eq_mul, mul_one]
  rw [measureReal_restrict_apply_univ, measureReal_def, hmeasure]
  simp only [ENNReal.toReal_mul]
  have hpi : 0 ≤ 2 * Real.pi := by positivity
  rw [ENNReal.toReal_ofReal hpi]
  rw [ENNReal.toReal_ofReal
    (by positivity : 0 ≤ a ^ 3 / 3)]
  norm_num
  ring

theorem gap3 (a : ℝ) (ha : 0 < a) :
    8 *
        (∫ phi in (0 : ℝ)..Real.pi / 2,
          ∫ psi in (0 : ℝ)..Real.pi / 2,
            ∫ r in (0 : ℝ)..radialBound a psi,
              r ^ 2 * Real.cos psi) =
      4 * Real.pi * a ^ 3 / 3 *
        ∫ psi in (0 : ℝ)..Real.pi / 2,
          Real.sin psi := by
  have hcube (psi : ℝ) (hpsi0 : 0 ≤ psi)
      (hpsi1 : psi ≤ Real.pi / 2) :
      radialBound a psi ^ 3 =
        a ^ 3 * Real.tan psi := by
    have htan :
        0 ≤ Real.tan psi :=
      Real.tan_nonneg_of_nonneg_of_le_pi_div_two
        hpsi0 hpsi1
    have hp :=
      Real.rpow_inv_natCast_pow htan
        (n := 3) (by norm_num)
    unfold radialBound
    rw [mul_pow]
    have hexp : (1 / 3 : ℝ) = (3 : ℝ)⁻¹ := by
      norm_num
    rw [hexp]
    exact congrArg (fun t : ℝ => a ^ 3 * t) hp
  have hinner (psi : ℝ) (hpsi0 : 0 ≤ psi)
      (hpsi1 : psi ≤ Real.pi / 2) :
      (∫ r in (0 : ℝ)..radialBound a psi,
          r ^ 2 * Real.cos psi) =
        a ^ 3 / 3 *
          (Real.tan psi * Real.cos psi) := by
    rw [show
      (fun r : ℝ => r ^ 2 * Real.cos psi) =
        fun r => Real.cos psi * r ^ 2 by
          funext r
          ring]
    rw [intervalIntegral.integral_const_mul,
      integral_pow, hcube psi hpsi0 hpsi1]
    norm_num
    ring
  have hpsiIntegral :
      (∫ psi in (0 : ℝ)..Real.pi / 2,
          ∫ r in (0 : ℝ)..radialBound a psi,
            r ^ 2 * Real.cos psi) =
        a ^ 3 / 3 *
          ∫ psi in (0 : ℝ)..Real.pi / 2,
            Real.sin psi := by
    calc
      (∫ psi in (0 : ℝ)..Real.pi / 2,
          ∫ r in (0 : ℝ)..radialBound a psi,
            r ^ 2 * Real.cos psi) =
          ∫ psi in (0 : ℝ)..Real.pi / 2,
            a ^ 3 / 3 *
              (Real.tan psi * Real.cos psi) := by
        apply intervalIntegral.integral_congr
        intro psi hpsi
        rw [Set.uIcc_of_le
          (by linarith [Real.pi_pos] :
            (0 : ℝ) ≤ Real.pi / 2)] at hpsi
        exact hinner psi hpsi.1 hpsi.2
      _ = ∫ psi in (0 : ℝ)..Real.pi / 2,
            a ^ 3 / 3 * Real.sin psi := by
        apply intervalIntegral.integral_congr_ae
        filter_upwards
          [MeasureTheory.volume.ae_ne (Real.pi / 2)]
            with psi hne
        intro hpsi
        rw [Set.uIoc_of_le
          (by linarith [Real.pi_pos] :
            (0 : ℝ) ≤ Real.pi / 2)] at hpsi
        have hpsilt : psi < Real.pi / 2 :=
          lt_of_le_of_ne hpsi.2 hne
        have hcos :
            Real.cos psi ≠ 0 :=
          (Real.cos_pos_of_mem_Ioo
            ⟨by linarith [hpsi.1, Real.pi_pos],
              hpsilt⟩).ne'
        rw [Real.tan_mul_cos hcos]
      _ = a ^ 3 / 3 *
            ∫ psi in (0 : ℝ)..Real.pi / 2,
              Real.sin psi := by
        rw [intervalIntegral.integral_const_mul]
  rw [hpsiIntegral]
  rw [intervalIntegral.integral_const]
  simp only [smul_eq_mul]
  ring

theorem gap4 (a : ℝ) :
    4 * Real.pi * a ^ 3 / 3 *
        (∫ psi in (0 : ℝ)..Real.pi / 2,
          Real.sin psi) =
      4 * Real.pi * a ^ 3 / 3 := by
  rw [integral_sin]
  simp

theorem gap2 (a : ℝ) (ha : 0 < a) :
    volume a =
      8 *
        ∫ phi in (0 : ℝ)..Real.pi / 2,
          ∫ psi in (0 : ℝ)..Real.pi / 2,
            ∫ r in (0 : ℝ)..radialBound a psi,
              r ^ 2 * Real.cos psi := by
  calc
    volume a = 4 * Real.pi * a ^ 3 / 3 :=
      volume_value a ha
    _ = 8 *
          (∫ phi in (0 : ℝ)..Real.pi / 2,
            ∫ psi in (0 : ℝ)..Real.pi / 2,
              ∫ r in (0 : ℝ)..radialBound a psi,
                r ^ 2 * Real.cos psi) :=
      ((gap3 a ha).trans (gap4 a)).symm

theorem gap5 (a : ℝ) (ha : 0 < a) :
    volume a = 4 * Real.pi * a ^ 3 / 3 := by
  rw [gap2 a ha, gap3 a ha, gap4]

end

end ProofGap.Exercise4121
