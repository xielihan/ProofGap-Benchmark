import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Data.Real.Sqrt
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise4022

noncomputable section

open MeasureTheory
open scoped Interval

def baseRegion (a b : ℝ) : Set (ℝ × ℝ) :=
  {p | p.1 ^ 2 / a ^ 2 + p.2 ^ 2 / b ^ 2 ≤ 1}

def upperSurface (c r : ℝ) : ℝ :=
  c * Real.sqrt (1 + r ^ 2)

def lowerSurface (c r : ℝ) : ℝ :=
  -c * Real.sqrt (1 + r ^ 2)

def parameterDomain : Set (ℝ × ℝ) :=
  Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) (2 * Real.pi)

def volume (a b c : ℝ) : ℝ :=
  ∫ p in baseRegion a b,
    2 * c *
      Real.sqrt (1 + (p.1 ^ 2 / a ^ 2 + p.2 ^ 2 / b ^ 2))

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

private theorem unitDisk_radial (c : ℝ) :
    (∫ p in {p : ℝ × ℝ | p.1 ^ 2 + p.2 ^ 2 ≤ 1},
      2 * c * Real.sqrt (1 + (p.1 ^ 2 + p.2 ^ 2))) =
      (∫ r in (0 : ℝ)..1, 2 * c * r * Real.sqrt (1 + r ^ 2)) *
        (2 * Real.pi) := by
  let D : Set (ℝ × ℝ) := {p | p.1 ^ 2 + p.2 ^ 2 ≤ 1}
  let f : ℝ × ℝ → ℝ :=
    fun p => 2 * c * Real.sqrt (1 + (p.1 ^ 2 + p.2 ^ 2))
  let q : ℝ → ℝ := fun r => 2 * c * r * Real.sqrt (1 + r ^ 2)
  have hD : MeasurableSet D := by
    dsimp [D]
    measurability
  have hpoint : ∀ p : ℝ × ℝ,
      polarCoord.target.indicator
          (fun z => z.1 * D.indicator f (polarCoord.symm z)) p =
        (Set.Ioc (0 : ℝ) 1 ×ˢ Set.Ioo (-Real.pi) Real.pi).indicator
          (fun z => q z.1) p := by
    rintro ⟨r, φ⟩
    have htrig :
        (r * Real.cos φ) ^ 2 + (r * Real.sin φ) ^ 2 = r ^ 2 := by
      nlinarith [Real.sin_sq_add_cos_sq φ]
    by_cases ht : 0 < r ∧ -Real.pi < φ ∧ φ < Real.pi
    · by_cases hr : r ≤ 1
      · have htargetmem : (r, φ) ∈ polarCoord.target := by
          simpa [polarCoord_target] using ht
        have hrectmem :
            (r, φ) ∈ Set.Ioc (0 : ℝ) 1 ×ˢ Set.Ioo (-Real.pi) Real.pi :=
          ⟨⟨ht.1, hr⟩, ht.2⟩
        have hpolarmem : polarCoord.symm (r, φ) ∈ D := by
          simp only [polarCoord_symm_apply, D, Set.mem_setOf_eq, htrig]
          nlinarith
        rw [Set.indicator_of_mem htargetmem, Set.indicator_of_mem hrectmem,
          Set.indicator_of_mem hpolarmem]
        simp only [f, q, polarCoord_symm_apply]
        rw [htrig]
        ring
      · have htargetmem : (r, φ) ∈ polarCoord.target := by
          simpa [polarCoord_target] using ht
        have hrect :
            (r, φ) ∉ Set.Ioc (0 : ℝ) 1 ×ˢ Set.Ioo (-Real.pi) Real.pi := by
          intro hp
          exact hr hp.1.2
        have hpolar : polarCoord.symm (r, φ) ∉ D := by
          simp only [polarCoord_symm_apply, D, Set.mem_setOf_eq, htrig]
          nlinarith
        rw [Set.indicator_of_mem htargetmem, Set.indicator_of_notMem hrect,
          Set.indicator_of_notMem hpolar]
        simp
    · have hrect :
          (r, φ) ∉ Set.Ioc (0 : ℝ) 1 ×ˢ Set.Ioo (-Real.pi) Real.pi := by
        intro hp
        exact ht ⟨hp.1.1, hp.2.1, hp.2.2⟩
      have htarget : (r, φ) ∉ polarCoord.target := by
        simpa [polarCoord_target, Set.mem_prod] using ht
      rw [Set.indicator_of_notMem htarget, Set.indicator_of_notMem hrect]
  have hangle :
      (∫ _φ in Set.Ioo (-Real.pi) Real.pi, (1 : ℝ)) =
        2 * Real.pi := by
    rw [MeasureTheory.setIntegral_const]
    simp [Real.pi_pos.le]
    ring
  calc
    (∫ p in {p : ℝ × ℝ | p.1 ^ 2 + p.2 ^ 2 ≤ 1},
        2 * c * Real.sqrt (1 + (p.1 ^ 2 + p.2 ^ 2))) =
        ∫ p : ℝ × ℝ, D.indicator f p := by
          rw [MeasureTheory.integral_indicator hD]
    _ = ∫ p in polarCoord.target,
          p.1 * D.indicator f (polarCoord.symm p) := by
          simpa [smul_eq_mul] using
            (integral_comp_polarCoord_symm (D.indicator f)).symm
    _ = ∫ p : ℝ × ℝ,
          (Set.Ioc (0 : ℝ) 1 ×ˢ Set.Ioo (-Real.pi) Real.pi).indicator
            (fun z => q z.1) p := by
          rw [← MeasureTheory.integral_indicator polarCoord.open_target.measurableSet]
          apply MeasureTheory.integral_congr_ae
          exact Filter.Eventually.of_forall hpoint
    _ = ∫ p in Set.Ioc (0 : ℝ) 1 ×ˢ Set.Ioo (-Real.pi) Real.pi,
          q p.1 * (1 : ℝ) := by
          rw [MeasureTheory.integral_indicator
            (measurableSet_Ioc.prod measurableSet_Ioo)]
          apply MeasureTheory.setIntegral_congr_fun
            (measurableSet_Ioc.prod measurableSet_Ioo)
          intro p hp
          simp
    _ = (∫ r in Set.Ioc (0 : ℝ) 1, q r) *
          ∫ _φ in Set.Ioo (-Real.pi) Real.pi, (1 : ℝ) := by
          exact MeasureTheory.setIntegral_prod_mul q (fun _ : ℝ => 1)
            (Set.Ioc (0 : ℝ) 1) (Set.Ioo (-Real.pi) Real.pi)
    _ = (∫ r in (0 : ℝ)..1, 2 * c * r * Real.sqrt (1 + r ^ 2)) *
          (2 * Real.pi) := by
          rw [intervalIntegral.integral_of_le (by norm_num), hangle]

private theorem radial_value :
    (∫ r in (0 : ℝ)..1, r * Real.sqrt (1 + r ^ 2)) =
      (2 * Real.sqrt 2 - 1) / 3 := by
  let F : ℝ → ℝ := fun r => (1 + r ^ 2) * Real.sqrt (1 + r ^ 2) / 3
  have hderiv : ∀ r : ℝ,
      HasDerivAt F (r * Real.sqrt (1 + r ^ 2)) r := by
    intro r
    have hpos : 0 < 1 + r ^ 2 := by positivity
    have hinner : HasDerivAt (fun x : ℝ => 1 + x ^ 2) (2 * r) r := by
      convert (hasDerivAt_const r 1).add ((hasDerivAt_id r).pow 2) using 1 <;>
        simp only [id_eq] <;> ring
    have hsqrt : HasDerivAt (fun x : ℝ => Real.sqrt (1 + x ^ 2))
        (1 / (2 * Real.sqrt (1 + r ^ 2)) * (2 * r)) r := by
      simpa only [Function.comp_apply] using
        (Real.hasDerivAt_sqrt hpos.ne').comp r hinner
    have hsquare : Real.sqrt (1 + r ^ 2) ^ 2 = 1 + r ^ 2 :=
      Real.sq_sqrt hpos.le
    change HasDerivAt
      (fun x : ℝ => (1 + x ^ 2) * Real.sqrt (1 + x ^ 2) / 3)
      (r * Real.sqrt (1 + r ^ 2)) r
    convert (hinner.mul hsqrt).div_const 3 using 1
    field_simp [Real.sqrt_ne_zero'.mpr hpos]
    rw [hsquare]
    ring
  have hint : IntervalIntegrable
      (fun r : ℝ => r * Real.sqrt (1 + r ^ 2))
      MeasureTheory.volume 0 1 :=
    (by fun_prop : Continuous
      (fun r : ℝ => r * Real.sqrt (1 + r ^ 2))).intervalIntegrable 0 1
  calc
    (∫ r in (0 : ℝ)..1, r * Real.sqrt (1 + r ^ 2)) =
        F 1 - F 0 := by
          apply intervalIntegral.integral_eq_sub_of_hasDerivAt
          · intro r hr
            exact hderiv r
          · exact hint
    _ = (2 * Real.sqrt 2 - 1) / 3 := by
          have hs2 : Real.sqrt (2 : ℝ) ^ 2 = 2 :=
            Real.sq_sqrt (by norm_num)
          simp [F]
          ring

private theorem volume_formula (a b c : ℝ)
    (ha : 0 < a) (hb : 0 < b) :
    volume a b c =
      4 * Real.pi / 3 * a * b * c * (2 * Real.sqrt 2 - 1) := by
  let g : ℝ × ℝ → ℝ := fun p =>
    (baseRegion a b).indicator
      (fun z => 2 * c *
        Real.sqrt (1 + (z.1 ^ 2 / a ^ 2 + z.2 ^ 2 / b ^ 2))) p
  let D : Set (ℝ × ℝ) := {p | p.1 ^ 2 + p.2 ^ 2 ≤ 1}
  let h : ℝ × ℝ → ℝ :=
    fun p => D.indicator
      (fun z => 2 * c * Real.sqrt (1 + (z.1 ^ 2 + z.2 ^ 2))) p
  have hbase : MeasurableSet (baseRegion a b) := by
    unfold baseRegion
    measurability
  have hpoint : ∀ q : ℝ × ℝ, g (a * q.1, b * q.2) = h q := by
    rintro ⟨x, y⟩
    have ha0 : a ≠ 0 := ne_of_gt ha
    have hb0 : b ≠ 0 := ne_of_gt hb
    have hx : (a * x) ^ 2 / a ^ 2 = x ^ 2 := by
      field_simp [ha0]
    have hy : (b * y) ^ 2 / b ^ 2 = y ^ 2 := by
      field_simp [hb0]
    have hmem :
        (a * x, b * y) ∈ baseRegion a b ↔ (x, y) ∈ D := by
      simp only [baseRegion, D, Set.mem_setOf_eq, Prod.fst, Prod.snd, hx, hy]
    by_cases hm : (x, y) ∈ D
    · dsimp only [g, h, Prod.fst, Prod.snd]
      rw [Set.indicator_of_mem hm,
        Set.indicator_of_mem (hmem.mpr hm)]
      rw [hx, hy]
    · dsimp only [g, h, Prod.fst, Prod.snd]
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
    _ = a * b *
        ∫ q in {p : ℝ × ℝ | p.1 ^ 2 + p.2 ^ 2 ≤ 1},
          2 * c * Real.sqrt (1 + (q.1 ^ 2 + q.2 ^ 2)) := by
      have hD : MeasurableSet D := by
        dsimp [D]
        measurability
      rw [← MeasureTheory.integral_indicator hD]
    _ = a * b *
        ((∫ r in (0 : ℝ)..1, 2 * c * r * Real.sqrt (1 + r ^ 2)) *
          (2 * Real.pi)) := by
      rw [unitDisk_radial c]
    _ = 4 * Real.pi / 3 * a * b * c * (2 * Real.sqrt 2 - 1) := by
      have hrad :
          (∫ r in (0 : ℝ)..1, 2 * c * r * Real.sqrt (1 + r ^ 2)) =
            2 * c * ((2 * Real.sqrt 2 - 1) / 3) := by
        calc
          _ = ∫ r in (0 : ℝ)..1,
              (2 * c) * (r * Real.sqrt (1 + r ^ 2)) := by
                apply intervalIntegral.integral_congr
                intro r hr
                ring
          _ = 2 * c * ∫ r in (0 : ℝ)..1,
              r * Real.sqrt (1 + r ^ 2) := by
                rw [intervalIntegral.integral_const_mul]
          _ = 2 * c * ((2 * Real.sqrt 2 - 1) / 3) := by
                rw [radial_value]
      rw [hrad]
      ring

theorem gap1 (c r : ℝ) :
    upperSurface c r = c * Real.sqrt (1 + r ^ 2) ∧
      lowerSurface c r = -c * Real.sqrt (1 + r ^ 2) := by
  exact ⟨rfl, rfl⟩

theorem gap2 (r φ : ℝ) (hp : (r, φ) ∈ parameterDomain) :
    0 ≤ φ := by
  exact hp.2.1

theorem gap3 (r φ : ℝ) (hp : (r, φ) ∈ parameterDomain) :
    φ ≤ 2 * Real.pi := by
  exact hp.2.2

theorem gap4 (r φ : ℝ) (hp : (r, φ) ∈ parameterDomain) :
    0 ≤ r := by
  exact hp.1.1

theorem gap5 (r φ : ℝ) (hp : (r, φ) ∈ parameterDomain) :
    r ≤ 1 := by
  exact hp.1.2

theorem gap6 (a b c : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    volume a b c =
      ∫ φ in (0 : ℝ)..2 * Real.pi,
        ∫ r in (0 : ℝ)..1,
          2 * a * b * c * r * Real.sqrt (1 + r ^ 2) := by
  rw [volume_formula a b c ha hb]
  have hinner :
      (∫ r in (0 : ℝ)..1,
        2 * a * b * c * r * Real.sqrt (1 + r ^ 2)) =
        2 * a * b * c * ((2 * Real.sqrt 2 - 1) / 3) := by
    calc
      _ = ∫ r in (0 : ℝ)..1,
          (2 * a * b * c) * (r * Real.sqrt (1 + r ^ 2)) := by
            apply intervalIntegral.integral_congr
            intro r hr
            ring
      _ = 2 * a * b * c *
          ∫ r in (0 : ℝ)..1, r * Real.sqrt (1 + r ^ 2) := by
            rw [intervalIntegral.integral_const_mul]
      _ = _ := by rw [radial_value]
  rw [hinner, intervalIntegral.integral_const]
  simp only [smul_eq_mul]
  ring

theorem gap7 (a b c : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    volume a b c =
      2 * a * b * c *
        ∫ φ in (0 : ℝ)..2 * Real.pi,
          ∫ r in (0 : ℝ)..1, r * Real.sqrt (1 + r ^ 2) := by
  rw [volume_formula a b c ha hb, radial_value,
    intervalIntegral.integral_const]
  simp only [smul_eq_mul]
  ring

theorem gap8 (a b c : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    2 * a * b * c *
        (∫ φ in (0 : ℝ)..2 * Real.pi,
          ∫ r in (0 : ℝ)..1, r * Real.sqrt (1 + r ^ 2)) =
      4 * Real.pi / 3 * a * b * c * (2 * Real.sqrt 2 - 1) := by
  rw [radial_value, intervalIntegral.integral_const]
  simp only [smul_eq_mul]
  ring

theorem gap9 (a b c : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    volume a b c =
      4 * Real.pi / 3 * a * b * c * (2 * Real.sqrt 2 - 1) := by
  exact volume_formula a b c ha hb

end

end ProofGap.Exercise4022
