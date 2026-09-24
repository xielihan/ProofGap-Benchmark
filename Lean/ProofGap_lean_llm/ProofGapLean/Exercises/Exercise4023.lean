import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Data.Real.Sqrt
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise4023

noncomputable section

open MeasureTheory
open scoped Interval

def baseRegion (a b : ℝ) : Set (ℝ × ℝ) :=
  {p |
    p.1 ^ 2 / a ^ 2 + p.2 ^ 2 / b ^ 2 ≤
      p.1 / a + p.2 / b}

def shiftedX (a r φ : ℝ) : ℝ :=
  a * (1 / 2 + r * Real.cos φ)

def shiftedY (b r φ : ℝ) : ℝ :=
  b * (1 / 2 + r * Real.sin φ)

def radialHeight (c r φ : ℝ) : ℝ :=
  c * (1 / 2 + r * (Real.cos φ + Real.sin φ) + r ^ 2)

def parameterDomain : Set (ℝ × ℝ) :=
  Set.Icc (0 : ℝ) (1 / Real.sqrt 2) ×ˢ
    Set.Icc (0 : ℝ) (2 * Real.pi)

def volume (a b c : ℝ) : ℝ :=
  ∫ p in baseRegion a b,
    c * (p.1 ^ 2 / a ^ 2 + p.2 ^ 2 / b ^ 2)

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

private theorem angular_value (c r : ℝ) :
    (∫ φ in -Real.pi..Real.pi,
      c * r *
        (1 / 2 + r * (Real.cos φ + Real.sin φ) + r ^ 2)) =
      2 * Real.pi * c * r * (1 / 2 + r ^ 2) := by
  let F : ℝ → ℝ := fun φ =>
    c * r *
      ((1 / 2 + r ^ 2) * φ +
        r * (Real.sin φ - Real.cos φ))
  have hderiv : ∀ φ : ℝ,
      HasDerivAt F
        (c * r *
          (1 / 2 + r * (Real.cos φ + Real.sin φ) + r ^ 2)) φ := by
    intro φ
    have hs := Real.hasDerivAt_sin φ
    have hc := Real.hasDerivAt_cos φ
    change HasDerivAt
      (fun x : ℝ => c * r *
        ((1 / 2 + r ^ 2) * x +
          r * (Real.sin x - Real.cos x)))
      _ φ
    convert
      (((hasDerivAt_id φ).const_mul (1 / 2 + r ^ 2)).add
        ((hs.sub hc).const_mul r)).const_mul (c * r) using 1 <;>
      ring
  have hint : IntervalIntegrable
      (fun φ : ℝ => c * r *
        (1 / 2 + r * (Real.cos φ + Real.sin φ) + r ^ 2))
      MeasureTheory.volume (-Real.pi) Real.pi :=
    (by fun_prop : Continuous
      (fun φ : ℝ => c * r *
        (1 / 2 + r * (Real.cos φ + Real.sin φ) + r ^ 2))).intervalIntegrable
      (-Real.pi) Real.pi
  calc
    _ = F Real.pi - F (-Real.pi) := by
      apply intervalIntegral.integral_eq_sub_of_hasDerivAt
      · intro φ hφ
        exact hderiv φ
      · exact hint
    _ = 2 * Real.pi * c * r * (1 / 2 + r ^ 2) := by
      simp [F]
      ring

private theorem radial_polynomial_value (c : ℝ) :
    (∫ r in (0 : ℝ)..1 / Real.sqrt 2,
      2 * Real.pi * c * r * (1 / 2 + r ^ 2)) =
      3 / 8 * Real.pi * c := by
  have hs2 : Real.sqrt (2 : ℝ) ^ 2 = 2 :=
    Real.sq_sqrt (by norm_num)
  have hs0 : Real.sqrt (2 : ℝ) ≠ 0 :=
    Real.sqrt_ne_zero'.mpr (by norm_num)
  have hs4 : Real.sqrt (2 : ℝ) ^ 4 = 4 := by
    calc
      Real.sqrt (2 : ℝ) ^ 4 =
          (Real.sqrt (2 : ℝ) ^ 2) ^ 2 := by ring
      _ = 4 := by rw [hs2]; norm_num
  let F : ℝ → ℝ := fun r =>
    2 * Real.pi * c * (r ^ 2 / 4 + r ^ 4 / 4)
  have hderiv : ∀ r : ℝ,
      HasDerivAt F (2 * Real.pi * c * r * (1 / 2 + r ^ 2)) r := by
    intro r
    change HasDerivAt
      (fun x : ℝ => 2 * Real.pi * c * (x ^ 2 / 4 + x ^ 4 / 4))
      _ r
    convert
      ((((hasDerivAt_id r).pow 2).div_const 4).add
        (((hasDerivAt_id r).pow 4).div_const 4)).const_mul
          (2 * Real.pi * c) using 1 <;>
      simp only [id_eq] <;> ring
  have hint : IntervalIntegrable
      (fun r : ℝ => 2 * Real.pi * c * r * (1 / 2 + r ^ 2))
      MeasureTheory.volume 0 (1 / Real.sqrt 2) :=
    (by fun_prop : Continuous
      (fun r : ℝ => 2 * Real.pi * c * r * (1 / 2 + r ^ 2))).intervalIntegrable
      0 (1 / Real.sqrt 2)
  calc
    _ = F (1 / Real.sqrt 2) - F 0 := by
      apply intervalIntegral.integral_eq_sub_of_hasDerivAt
      · intro r hr
        exact hderiv r
      · exact hint
    _ = 3 / 8 * Real.pi * c := by
      dsimp [F]
      field_simp [hs0]
      rw [hs2, hs4]
      ring

private theorem centeredDisk_value (c : ℝ) :
    (∫ p in {p : ℝ × ℝ | p.1 ^ 2 + p.2 ^ 2 ≤ 1 / 2},
      c * (1 / 2 + p.1 + p.2 + p.1 ^ 2 + p.2 ^ 2)) =
      3 / 8 * Real.pi * c := by
  let s : ℝ := 1 / Real.sqrt 2
  let D : Set (ℝ × ℝ) := {p | p.1 ^ 2 + p.2 ^ 2 ≤ 1 / 2}
  let f : ℝ × ℝ → ℝ :=
    fun p => c * (1 / 2 + p.1 + p.2 + p.1 ^ 2 + p.2 ^ 2)
  let q : ℝ × ℝ → ℝ := fun p =>
    c * p.1 *
      (1 / 2 + p.1 * (Real.cos p.2 + Real.sin p.2) + p.1 ^ 2)
  have hs0 : Real.sqrt (2 : ℝ) ≠ 0 :=
    Real.sqrt_ne_zero'.mpr (by norm_num)
  have hs2 : Real.sqrt (2 : ℝ) ^ 2 = 2 :=
    Real.sq_sqrt (by norm_num)
  have hs : 0 ≤ s := by
    dsimp [s]
    positivity
  have hsquare : s ^ 2 = 1 / 2 := by
    dsimp [s]
    field_simp [hs0]
    rw [hs2]
  have hD : MeasurableSet D := by
    dsimp [D]
    measurability
  have hpoint : ∀ p : ℝ × ℝ,
      polarCoord.target.indicator
          (fun z => z.1 * D.indicator f (polarCoord.symm z)) p =
        (Set.Ioc (0 : ℝ) s ×ˢ Set.Ioo (-Real.pi) Real.pi).indicator
          q p := by
    rintro ⟨r, φ⟩
    have htrig :
        (r * Real.cos φ) ^ 2 + (r * Real.sin φ) ^ 2 = r ^ 2 := by
      nlinarith [Real.sin_sq_add_cos_sq φ]
    by_cases ht : 0 < r ∧ -Real.pi < φ ∧ φ < Real.pi
    · have hriff : r ^ 2 ≤ s ^ 2 ↔ r ≤ s := by
        constructor <;> intro h <;> nlinarith
      by_cases hr : r ≤ s
      · have htargetmem : (r, φ) ∈ polarCoord.target := by
          simpa [polarCoord_target] using ht
        have hrectmem :
            (r, φ) ∈ Set.Ioc (0 : ℝ) s ×ˢ Set.Ioo (-Real.pi) Real.pi :=
          ⟨⟨ht.1, hr⟩, ht.2⟩
        have hpolarmem : polarCoord.symm (r, φ) ∈ D := by
          simp only [polarCoord_symm_apply, D, Set.mem_setOf_eq, htrig,
            ← hsquare]
          exact hriff.mpr hr
        rw [Set.indicator_of_mem htargetmem, Set.indicator_of_mem hrectmem,
          Set.indicator_of_mem hpolarmem]
        simp only [f, q, polarCoord_symm_apply]
        have halg :
            1 / 2 + r * Real.cos φ + r * Real.sin φ +
                (r * Real.cos φ) ^ 2 + (r * Real.sin φ) ^ 2 =
              1 / 2 + r * (Real.cos φ + Real.sin φ) + r ^ 2 := by
          calc
            _ = 1 / 2 + r * (Real.cos φ + Real.sin φ) +
                ((r * Real.cos φ) ^ 2 + (r * Real.sin φ) ^ 2) := by
                  ring
            _ = _ := by rw [htrig]
        rw [halg]
        ring
      · have htargetmem : (r, φ) ∈ polarCoord.target := by
          simpa [polarCoord_target] using ht
        have hrect :
            (r, φ) ∉ Set.Ioc (0 : ℝ) s ×ˢ Set.Ioo (-Real.pi) Real.pi := by
          intro hp
          exact hr hp.1.2
        have hpolar : polarCoord.symm (r, φ) ∉ D := by
          simp only [polarCoord_symm_apply, D, Set.mem_setOf_eq, htrig,
            ← hsquare]
          intro hsq
          exact hr (hriff.mp hsq)
        rw [Set.indicator_of_mem htargetmem, Set.indicator_of_notMem hrect,
          Set.indicator_of_notMem hpolar]
        simp
    · have hrect :
          (r, φ) ∉ Set.Ioc (0 : ℝ) s ×ˢ Set.Ioo (-Real.pi) Real.pi := by
        intro hp
        exact ht ⟨hp.1.1, hp.2.1, hp.2.2⟩
      have htarget : (r, φ) ∉ polarCoord.target := by
        simpa [polarCoord_target, Set.mem_prod] using ht
      rw [Set.indicator_of_notMem htarget, Set.indicator_of_notMem hrect]
  have hqcont : Continuous q := by
    dsimp [q]
    fun_prop
  have hbox :
      IsCompact (Set.Icc (0 : ℝ) s ×ˢ
        Set.Icc (-Real.pi) Real.pi) :=
    isCompact_Icc.prod isCompact_Icc
  have hsubset :
      Set.Ioc (0 : ℝ) s ×ˢ Set.Ioo (-Real.pi) Real.pi ⊆
        Set.Icc (0 : ℝ) s ×ˢ Set.Icc (-Real.pi) Real.pi := by
    intro p hp
    exact ⟨⟨hp.1.1.le, hp.1.2⟩, ⟨hp.2.1.le, hp.2.2.le⟩⟩
  have hqint : IntegrableOn q
      (Set.Ioc (0 : ℝ) s ×ˢ Set.Ioo (-Real.pi) Real.pi) :=
    (hqcont.continuousOn.integrableOn_compact hbox).mono_set hsubset
  have hprod :
      (∫ p in Set.Ioc (0 : ℝ) s ×ˢ Set.Ioo (-Real.pi) Real.pi, q p) =
        ∫ r in Set.Ioc (0 : ℝ) s,
          ∫ φ in Set.Ioo (-Real.pi) Real.pi, q (r, φ) :=
    MeasureTheory.setIntegral_prod q hqint
  calc
    (∫ p in {p : ℝ × ℝ | p.1 ^ 2 + p.2 ^ 2 ≤ 1 / 2},
        c * (1 / 2 + p.1 + p.2 + p.1 ^ 2 + p.2 ^ 2)) =
        ∫ p : ℝ × ℝ, D.indicator f p := by
          rw [MeasureTheory.integral_indicator hD]
    _ = ∫ p in polarCoord.target,
          p.1 * D.indicator f (polarCoord.symm p) := by
          simpa [smul_eq_mul] using
            (integral_comp_polarCoord_symm (D.indicator f)).symm
    _ = ∫ p : ℝ × ℝ,
          (Set.Ioc (0 : ℝ) s ×ˢ Set.Ioo (-Real.pi) Real.pi).indicator
            q p := by
          rw [← MeasureTheory.integral_indicator polarCoord.open_target.measurableSet]
          apply MeasureTheory.integral_congr_ae
          exact Filter.Eventually.of_forall hpoint
    _ = ∫ p in Set.Ioc (0 : ℝ) s ×ˢ Set.Ioo (-Real.pi) Real.pi,
          q p := by
          rw [MeasureTheory.integral_indicator
            (measurableSet_Ioc.prod measurableSet_Ioo)]
    _ = ∫ r in Set.Ioc (0 : ℝ) s,
          ∫ φ in Set.Ioo (-Real.pi) Real.pi, q (r, φ) := hprod
    _ = ∫ r in (0 : ℝ)..s,
          ∫ φ in -Real.pi..Real.pi,
            c * r *
              (1 / 2 + r * (Real.cos φ + Real.sin φ) + r ^ 2) := by
          rw [intervalIntegral.integral_of_le hs]
          apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
          intro r hr
          change
            (∫ φ in Set.Ioo (-Real.pi) Real.pi,
              c * r *
                (1 / 2 + r * (Real.cos φ + Real.sin φ) + r ^ 2)) =
              ∫ φ in -Real.pi..Real.pi,
                c * r *
                  (1 / 2 + r * (Real.cos φ + Real.sin φ) + r ^ 2)
          rw [intervalIntegral.integral_of_le (by linarith [Real.pi_pos])]
          rw [Measure.restrict_congr_set Ioo_ae_eq_Ioc]
    _ = ∫ r in (0 : ℝ)..s,
          2 * Real.pi * c * r * (1 / 2 + r ^ 2) := by
          apply intervalIntegral.integral_congr
          intro r hr
          exact angular_value c r
    _ = 3 / 8 * Real.pi * c := by
          exact radial_polynomial_value c

private theorem volume_formula (a b c : ℝ)
    (ha : 0 < a) (hb : 0 < b) :
    volume a b c = 3 / 8 * Real.pi * a * b * c := by
  let g : ℝ × ℝ → ℝ := fun p =>
    (baseRegion a b).indicator
      (fun z => c * (z.1 ^ 2 / a ^ 2 + z.2 ^ 2 / b ^ 2)) p
  let S : Set (ℝ × ℝ) :=
    {p | p.1 ^ 2 + p.2 ^ 2 ≤ p.1 + p.2}
  let h : ℝ × ℝ → ℝ :=
    fun p => S.indicator (fun z => c * (z.1 ^ 2 + z.2 ^ 2)) p
  let k : ℝ × ℝ → ℝ :=
    fun p =>
      ({z : ℝ × ℝ | z.1 ^ 2 + z.2 ^ 2 ≤ 1 / 2}).indicator
        (fun z => c * (1 / 2 + z.1 + z.2 + z.1 ^ 2 + z.2 ^ 2)) p
  have hbase : MeasurableSet (baseRegion a b) := by
    unfold baseRegion
    measurability
  have hscale : ∀ q : ℝ × ℝ, g (a * q.1, b * q.2) = h q := by
    rintro ⟨x, y⟩
    have ha0 : a ≠ 0 := ne_of_gt ha
    have hb0 : b ≠ 0 := ne_of_gt hb
    have hx : (a * x) ^ 2 / a ^ 2 = x ^ 2 := by field_simp [ha0]
    have hy : (b * y) ^ 2 / b ^ 2 = y ^ 2 := by field_simp [hb0]
    have hx' : a * x / a = x := by field_simp [ha0]
    have hy' : b * y / b = y := by field_simp [hb0]
    have hmem :
        (a * x, b * y) ∈ baseRegion a b ↔ (x, y) ∈ S := by
      simp only [baseRegion, S, Set.mem_setOf_eq, hx, hy, hx', hy']
    by_cases hm : (x, y) ∈ S
    · dsimp only [g, h, Prod.fst, Prod.snd]
      rw [Set.indicator_of_mem hm, Set.indicator_of_mem (hmem.mpr hm), hx, hy]
    · dsimp only [g, h, Prod.fst, Prod.snd]
      rw [Set.indicator_of_notMem hm,
        Set.indicator_of_notMem (fun hs => hm (hmem.mp hs))]
  have hshift : ∀ z : ℝ × ℝ,
      h ((1 / 2, 1 / 2) + z) = k z := by
    rintro ⟨x, y⟩
    have hregion :
        ((1 / 2, 1 / 2) + (x, y)) ∈ S ↔
          (x, y) ∈ {z : ℝ × ℝ | z.1 ^ 2 + z.2 ^ 2 ≤ 1 / 2} := by
      simp only [S, Set.mem_setOf_eq, Prod.fst_add, Prod.snd_add,
        Prod.fst, Prod.snd]
      constructor <;> intro hxy <;> nlinarith
    by_cases hm :
        (x, y) ∈ {z : ℝ × ℝ | z.1 ^ 2 + z.2 ^ 2 ≤ 1 / 2}
    · dsimp only [h, k]
      rw [Set.indicator_of_mem hm,
        Set.indicator_of_mem (hregion.mpr hm)]
      simp only [Prod.fst_add, Prod.snd_add, Prod.fst, Prod.snd]
      ring
    · dsimp only [h, k]
      rw [Set.indicator_of_notMem hm,
        Set.indicator_of_notMem (fun hs => hm (hregion.mp hs))]
  calc
    volume a b c = ∫ p : ℝ × ℝ, g p := by
      rw [volume, ← MeasureTheory.integral_indicator hbase]
    _ = a * b * ∫ q : ℝ × ℝ, g (a * q.1, b * q.2) :=
      integral_diag a b ha hb g
    _ = a * b * ∫ q : ℝ × ℝ, h q := by
      congr 1
      apply MeasureTheory.integral_congr_ae
      exact Filter.Eventually.of_forall hscale
    _ = a * b * ∫ z : ℝ × ℝ, h ((1 / 2, 1 / 2) + z) := by
      rw [integral_add_left_eq_self h (1 / 2, 1 / 2)]
    _ = a * b * ∫ z : ℝ × ℝ, k z := by
      congr 1
      apply MeasureTheory.integral_congr_ae
      exact Filter.Eventually.of_forall hshift
    _ = a * b *
        ∫ z in {p : ℝ × ℝ | p.1 ^ 2 + p.2 ^ 2 ≤ 1 / 2},
          c * (1 / 2 + z.1 + z.2 + z.1 ^ 2 + z.2 ^ 2) := by
      have hD : MeasurableSet
          {p : ℝ × ℝ | p.1 ^ 2 + p.2 ^ 2 ≤ 1 / 2} := by
        measurability
      rw [← MeasureTheory.integral_indicator hD]
    _ = a * b * (3 / 8 * Real.pi * c) := by
      rw [centeredDisk_value c]
    _ = 3 / 8 * Real.pi * a * b * c := by ring

theorem gap1 (a b x y : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) :
    x ^ 2 / a ^ 2 + y ^ 2 / b ^ 2 = x / a + y / b ↔
      (x / a - 1 / 2) ^ 2 + (y / b - 1 / 2) ^ 2 = 1 / 2 := by
  field_simp [ha, hb]
  constructor <;> intro h <;> nlinarith

theorem gap2 (a b c r φ : ℝ)
    (ha : 0 < a) (hb : 0 < b) :
    c *
        (shiftedX a r φ ^ 2 / a ^ 2 +
          shiftedY b r φ ^ 2 / b ^ 2) =
      radialHeight c r φ := by
  have ha0 : a ≠ 0 := ne_of_gt ha
  have hb0 : b ≠ 0 := ne_of_gt hb
  have hx :
      shiftedX a r φ ^ 2 / a ^ 2 =
        (1 / 2 + r * Real.cos φ) ^ 2 := by
    unfold shiftedX
    field_simp [ha0]
  have hy :
      shiftedY b r φ ^ 2 / b ^ 2 =
        (1 / 2 + r * Real.sin φ) ^ 2 := by
    unfold shiftedY
    field_simp [hb0]
  rw [hx, hy]
  unfold radialHeight
  have hinside :
      (1 / 2 + r * Real.cos φ) ^ 2 +
          (1 / 2 + r * Real.sin φ) ^ 2 =
        1 / 2 + r * (Real.cos φ + Real.sin φ) + r ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq φ]
  rw [hinside]

theorem gap3 (r φ : ℝ) (hp : (r, φ) ∈ parameterDomain) :
    0 ≤ φ := hp.2.1

theorem gap4 (r φ : ℝ) (hp : (r, φ) ∈ parameterDomain) :
    φ ≤ 2 * Real.pi := hp.2.2

theorem gap5 (r φ : ℝ) (hp : (r, φ) ∈ parameterDomain) :
    0 ≤ r := hp.1.1

theorem gap6 (r φ : ℝ) (hp : (r, φ) ∈ parameterDomain) :
    r ≤ 1 / Real.sqrt 2 := hp.1.2

private theorem target_integral_value (a b c : ℝ) :
    (∫ φ in (0 : ℝ)..2 * Real.pi,
      ∫ r in (0 : ℝ)..1 / Real.sqrt 2,
        a * b * c * r *
          (1 / 2 + r * (Real.cos φ + Real.sin φ) + r ^ 2)) =
      3 / 8 * Real.pi * a * b * c := by
  have hs2 : Real.sqrt (2 : ℝ) ^ 2 = 2 :=
    Real.sq_sqrt (by norm_num)
  have hs0 : Real.sqrt (2 : ℝ) ≠ 0 :=
    Real.sqrt_ne_zero'.mpr (by norm_num)
  have hinner : ∀ φ : ℝ,
      (∫ r in (0 : ℝ)..1 / Real.sqrt 2,
        a * b * c * r *
          (1 / 2 + r * (Real.cos φ + Real.sin φ) + r ^ 2)) =
        a * b * c *
          (1 / 8 + 1 / (6 * Real.sqrt 2) *
            (Real.cos φ + Real.sin φ) + 1 / 16) := by
    intro φ
    let F : ℝ → ℝ := fun r =>
      a * b * c *
        (r ^ 2 / 4 +
          (Real.cos φ + Real.sin φ) * r ^ 3 / 3 + r ^ 4 / 4)
    have hd : ∀ r : ℝ, HasDerivAt F
        (a * b * c * r *
          (1 / 2 + r * (Real.cos φ + Real.sin φ) + r ^ 2)) r := by
      intro r
      change HasDerivAt
        (fun x : ℝ => a * b * c *
          (x ^ 2 / 4 +
            (Real.cos φ + Real.sin φ) * x ^ 3 / 3 + x ^ 4 / 4))
        _ r
      convert
        (((((hasDerivAt_id r).pow 2).div_const 4).add
          ((((hasDerivAt_id r).pow 3).const_mul
            (Real.cos φ + Real.sin φ)).div_const 3)).add
          (((hasDerivAt_id r).pow 4).div_const 4)).const_mul
            (a * b * c) using 1 <;>
        simp only [id_eq] <;> ring
    have hi : IntervalIntegrable
        (fun r : ℝ => a * b * c * r *
          (1 / 2 + r * (Real.cos φ + Real.sin φ) + r ^ 2))
        MeasureTheory.volume 0 (1 / Real.sqrt 2) :=
      (by fun_prop : Continuous
        (fun r : ℝ => a * b * c * r *
          (1 / 2 + r * (Real.cos φ + Real.sin φ) + r ^ 2))).intervalIntegrable
        0 (1 / Real.sqrt 2)
    calc
      _ = F (1 / Real.sqrt 2) - F 0 := by
        apply intervalIntegral.integral_eq_sub_of_hasDerivAt
        · intro r hr
          exact hd r
        · exact hi
      _ = _ := by
        dsimp [F]
        have hp2 : (1 / Real.sqrt 2) ^ 2 = (1 / 2 : ℝ) := by
          field_simp [hs0]
          rw [hs2]
        have hp3 :
            (1 / Real.sqrt 2) ^ 3 = 1 / (2 * Real.sqrt 2) := by
          calc
            (1 / Real.sqrt 2) ^ 3 =
                (1 / Real.sqrt 2) ^ 2 * (1 / Real.sqrt 2) := by ring
            _ = 1 / (2 * Real.sqrt 2) := by rw [hp2]; ring
        have hp4 : (1 / Real.sqrt 2) ^ 4 = (1 / 4 : ℝ) := by
          calc
            (1 / Real.sqrt 2) ^ 4 =
                ((1 / Real.sqrt 2) ^ 2) ^ 2 := by ring
            _ = 1 / 4 := by rw [hp2]; ring
        rw [hp2, hp3, hp4]
        ring
  have hang :
      (∫ φ in (0 : ℝ)..2 * Real.pi,
        1 / 8 + 1 / (6 * Real.sqrt 2) *
          (Real.cos φ + Real.sin φ) + 1 / 16) =
        3 * (2 * Real.pi) / 16 := by
    let F : ℝ → ℝ := fun φ =>
      3 / 16 * φ +
        1 / (6 * Real.sqrt 2) * (Real.sin φ - Real.cos φ)
    have hd : ∀ φ : ℝ, HasDerivAt F
        (1 / 8 + 1 / (6 * Real.sqrt 2) *
          (Real.cos φ + Real.sin φ) + 1 / 16) φ := by
      intro φ
      change HasDerivAt
        (fun x : ℝ => 3 / 16 * x +
          1 / (6 * Real.sqrt 2) * (Real.sin x - Real.cos x)) _ φ
      convert
        ((hasDerivAt_id φ).const_mul (3 / 16)).add
          (((Real.hasDerivAt_sin φ).sub (Real.hasDerivAt_cos φ)).const_mul
            (1 / (6 * Real.sqrt 2))) using 1 <;>
        ring
    have hi : IntervalIntegrable
        (fun φ : ℝ => 1 / 8 + 1 / (6 * Real.sqrt 2) *
          (Real.cos φ + Real.sin φ) + 1 / 16)
        MeasureTheory.volume 0 (2 * Real.pi) :=
      (by fun_prop : Continuous
        (fun φ : ℝ => 1 / 8 + 1 / (6 * Real.sqrt 2) *
          (Real.cos φ + Real.sin φ) + 1 / 16)).intervalIntegrable
        0 (2 * Real.pi)
    calc
      _ = F (2 * Real.pi) - F 0 := by
        apply intervalIntegral.integral_eq_sub_of_hasDerivAt
        · intro φ hφ
          exact hd φ
        · exact hi
      _ = _ := by simp [F]; ring
  calc
    _ = ∫ φ in (0 : ℝ)..2 * Real.pi,
        a * b * c *
          (1 / 8 + 1 / (6 * Real.sqrt 2) *
            (Real.cos φ + Real.sin φ) + 1 / 16) := by
          apply intervalIntegral.integral_congr
          intro φ hφ
          exact hinner φ
    _ = a * b * c *
        ∫ φ in (0 : ℝ)..2 * Real.pi,
          (1 / 8 + 1 / (6 * Real.sqrt 2) *
            (Real.cos φ + Real.sin φ) + 1 / 16) := by
          rw [intervalIntegral.integral_const_mul]
    _ = _ := by rw [hang]; ring

theorem gap7 (a b c : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    volume a b c =
      ∫ φ in (0 : ℝ)..2 * Real.pi,
        ∫ r in (0 : ℝ)..1 / Real.sqrt 2,
          a * b * c * r *
            (1 / 2 + r * (Real.cos φ + Real.sin φ) + r ^ 2) := by
  rw [volume_formula a b c ha hb, target_integral_value a b c]

theorem gap8 (a b c : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    volume a b c =
      a * b * c *
        ∫ φ in (0 : ℝ)..2 * Real.pi,
          1 / 8 +
            1 / (6 * Real.sqrt 2) * (Real.cos φ + Real.sin φ) +
            1 / 16 := by
  rw [volume_formula a b c ha hb]
  have h := target_integral_value a b c
  have hang :
      (∫ φ in (0 : ℝ)..2 * Real.pi,
        1 / 8 + 1 / (6 * Real.sqrt 2) *
          (Real.cos φ + Real.sin φ) + 1 / 16) =
        3 * (2 * Real.pi) / 16 := by
    let F : ℝ → ℝ := fun φ =>
      3 / 16 * φ +
        1 / (6 * Real.sqrt 2) * (Real.sin φ - Real.cos φ)
    have hd : ∀ φ : ℝ, HasDerivAt F
        (1 / 8 + 1 / (6 * Real.sqrt 2) *
          (Real.cos φ + Real.sin φ) + 1 / 16) φ := by
      intro φ
      change HasDerivAt
        (fun x : ℝ => 3 / 16 * x +
          1 / (6 * Real.sqrt 2) * (Real.sin x - Real.cos x)) _ φ
      convert
        ((hasDerivAt_id φ).const_mul (3 / 16)).add
          (((Real.hasDerivAt_sin φ).sub (Real.hasDerivAt_cos φ)).const_mul
            (1 / (6 * Real.sqrt 2))) using 1 <;>
        ring
    have hi : IntervalIntegrable
        (fun φ : ℝ => 1 / 8 + 1 / (6 * Real.sqrt 2) *
          (Real.cos φ + Real.sin φ) + 1 / 16)
        MeasureTheory.volume 0 (2 * Real.pi) :=
      (by fun_prop : Continuous
        (fun φ : ℝ => 1 / 8 + 1 / (6 * Real.sqrt 2) *
          (Real.cos φ + Real.sin φ) + 1 / 16)).intervalIntegrable
        0 (2 * Real.pi)
    calc
      _ = F (2 * Real.pi) - F 0 := by
        apply intervalIntegral.integral_eq_sub_of_hasDerivAt
        · intro φ hφ
          exact hd φ
        · exact hi
      _ = _ := by simp [F]; ring
  rw [hang]
  ring

theorem gap9 (a b c : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    a * b * c *
        (∫ φ in (0 : ℝ)..2 * Real.pi,
          1 / 8 +
            1 / (6 * Real.sqrt 2) * (Real.cos φ + Real.sin φ) +
            1 / 16) =
      a * b * c * (3 * (2 * Real.pi) / 16) := by
  let F : ℝ → ℝ := fun φ =>
    3 / 16 * φ +
      1 / (6 * Real.sqrt 2) * (Real.sin φ - Real.cos φ)
  have hd : ∀ φ : ℝ, HasDerivAt F
      (1 / 8 + 1 / (6 * Real.sqrt 2) *
        (Real.cos φ + Real.sin φ) + 1 / 16) φ := by
    intro φ
    change HasDerivAt
      (fun x : ℝ => 3 / 16 * x +
        1 / (6 * Real.sqrt 2) * (Real.sin x - Real.cos x)) _ φ
    convert
      ((hasDerivAt_id φ).const_mul (3 / 16)).add
        (((Real.hasDerivAt_sin φ).sub (Real.hasDerivAt_cos φ)).const_mul
          (1 / (6 * Real.sqrt 2))) using 1 <;>
      ring
  have hi : IntervalIntegrable
      (fun φ : ℝ => 1 / 8 + 1 / (6 * Real.sqrt 2) *
        (Real.cos φ + Real.sin φ) + 1 / 16)
      MeasureTheory.volume 0 (2 * Real.pi) :=
    (by fun_prop : Continuous
      (fun φ : ℝ => 1 / 8 + 1 / (6 * Real.sqrt 2) *
        (Real.cos φ + Real.sin φ) + 1 / 16)).intervalIntegrable
      0 (2 * Real.pi)
  have hang :
      (∫ φ in (0 : ℝ)..2 * Real.pi,
        1 / 8 + 1 / (6 * Real.sqrt 2) *
          (Real.cos φ + Real.sin φ) + 1 / 16) =
        3 * (2 * Real.pi) / 16 := by
    calc
      _ = F (2 * Real.pi) - F 0 := by
        apply intervalIntegral.integral_eq_sub_of_hasDerivAt
        · intro φ hφ
          exact hd φ
        · exact hi
      _ = _ := by simp [F]; ring
  rw [hang]

theorem gap10 (a b c : ℝ) :
    a * b * c * (3 * (2 * Real.pi) / 16) =
      3 / 8 * Real.pi * a * b * c := by
  ring

theorem gap11 (a b c : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    volume a b c = 3 / 8 * Real.pi * a * b * c := by
  exact volume_formula a b c ha hb

end

end ProofGap.Exercise4023
