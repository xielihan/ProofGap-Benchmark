import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise4018

noncomputable section

open MeasureTheory
open scoped Interval

def disk (R : ℝ) : Set (ℝ × ℝ) :=
  {p | p.1 ^ 2 + p.2 ^ 2 ≤ R ^ 2}

def weightedVolume (R : ℝ) : ℝ :=
  ∫ p in disk R, Real.exp (-(p.1 ^ 2 + p.2 ^ 2))

private theorem weightedVolume_polar (R : ℝ) (hR : 0 ≤ R) :
    weightedVolume R =
      (∫ r in (0 : ℝ)..R, Real.exp (-(r ^ 2)) * r) *
        (2 * Real.pi) := by
  let f : ℝ × ℝ → ℝ :=
    fun p => Real.exp (-(p.1 ^ 2 + p.2 ^ 2))
  let q : ℝ → ℝ := fun r => Real.exp (-(r ^ 2)) * r
  have hdisk : MeasurableSet (disk R) := by
    unfold disk
    measurability
  have hpoint : ∀ p : ℝ × ℝ,
      polarCoord.target.indicator
          (fun z =>
            z.1 * (disk R).indicator f (polarCoord.symm z)) p =
        (Set.Ioc (0 : ℝ) R ×ˢ Set.Ioo (-Real.pi) Real.pi).indicator
          (fun z => q z.1) p := by
    rintro ⟨r, φ⟩
    have htrig :
        (r * Real.cos φ) ^ 2 + (r * Real.sin φ) ^ 2 = r ^ 2 := by
      nlinarith [Real.sin_sq_add_cos_sq φ]
    by_cases ht : 0 < r ∧ -Real.pi < φ ∧ φ < Real.pi
    · have hriff : r ^ 2 ≤ R ^ 2 ↔ r ≤ R := by
        constructor
        · intro hsq
          nlinarith
        · intro hr
          nlinarith
      by_cases hr : r ≤ R
      · have htargetmem : (r, φ) ∈ polarCoord.target := by
          simpa [polarCoord_target] using ht
        have hrectmem :
            (r, φ) ∈ Set.Ioc (0 : ℝ) R ×ˢ Set.Ioo (-Real.pi) Real.pi :=
          ⟨⟨ht.1, hr⟩, ht.2⟩
        have hpolarmem : polarCoord.symm (r, φ) ∈ disk R := by
          simp only [polarCoord_symm_apply, disk, Set.mem_setOf_eq, Prod.fst,
            Prod.snd, htrig]
          exact hriff.mpr hr
        rw [Set.indicator_of_mem htargetmem, Set.indicator_of_mem hrectmem,
          Set.indicator_of_mem hpolarmem]
        simp only [f, q, polarCoord_symm_apply, Prod.fst, Prod.snd]
        rw [htrig]
        ring
      · have hsq : ¬r ^ 2 ≤ R ^ 2 := by
          intro h
          exact hr (hriff.mp h)
        simp [polarCoord_target, Set.indicator_of_mem, ht, disk, f, q,
          htrig, hr, hsq]
    · have hrect :
          (r, φ) ∉ Set.Ioc (0 : ℝ) R ×ˢ Set.Ioo (-Real.pi) Real.pi := by
        intro hp
        exact ht ⟨hp.1.1, hp.2.1, hp.2.2⟩
      have htarget : (r, φ) ∉ polarCoord.target := by
        simpa [polarCoord_target, Set.mem_prod] using ht
      rw [Set.indicator_of_notMem htarget, Set.indicator_of_notMem hrect]
  calc
    weightedVolume R =
        ∫ p : ℝ × ℝ, (disk R).indicator f p := by
          rw [weightedVolume, MeasureTheory.integral_indicator hdisk]
    _ = ∫ p in polarCoord.target,
          p.1 * (disk R).indicator f (polarCoord.symm p) := by
          simpa [smul_eq_mul] using
            (integral_comp_polarCoord_symm ((disk R).indicator f)).symm
    _ = ∫ p : ℝ × ℝ,
          (Set.Ioc (0 : ℝ) R ×ˢ Set.Ioo (-Real.pi) Real.pi).indicator
            (fun z => q z.1) p := by
          rw [← MeasureTheory.integral_indicator polarCoord.open_target.measurableSet]
          apply MeasureTheory.integral_congr_ae
          exact Filter.Eventually.of_forall hpoint
    _ = ∫ p in Set.Ioc (0 : ℝ) R ×ˢ Set.Ioo (-Real.pi) Real.pi,
          q p.1 * (1 : ℝ) := by
          rw [MeasureTheory.integral_indicator
            (measurableSet_Ioc.prod measurableSet_Ioo)]
          apply MeasureTheory.setIntegral_congr_fun
            (measurableSet_Ioc.prod measurableSet_Ioo)
          intro p hp
          simp
    _ = (∫ r in Set.Ioc (0 : ℝ) R, q r) *
          ∫ _φ in Set.Ioo (-Real.pi) Real.pi, (1 : ℝ) := by
          exact MeasureTheory.setIntegral_prod_mul q (fun _ : ℝ => 1)
            (Set.Ioc (0 : ℝ) R) (Set.Ioo (-Real.pi) Real.pi)
    _ = (∫ r in (0 : ℝ)..R, Real.exp (-(r ^ 2)) * r) *
          (2 * Real.pi) := by
          have hangle :
              (∫ _φ in Set.Ioo (-Real.pi) Real.pi, (1 : ℝ)) =
                2 * Real.pi := by
            rw [MeasureTheory.setIntegral_const]
            simp [Real.pi_pos.le]
            ring
          rw [intervalIntegral.integral_of_le hR]
          simp only [q]
          rw [hangle]

theorem gap1 (R : ℝ) (hR : 0 ≤ R) :
    weightedVolume R =
      4 *
        ∫ φ in (0 : ℝ)..Real.pi / 2,
          ∫ r in (0 : ℝ)..R, Real.exp (-(r ^ 2)) * r := by
  rw [weightedVolume_polar R hR]
  rw [intervalIntegral.integral_const]
  simp only [smul_eq_mul]
  ring

theorem gap2 (R : ℝ) (hR : 0 ≤ R) :
    weightedVolume R =
      Real.pi * (1 - Real.exp (-(R ^ 2))) := by
  rw [weightedVolume_polar R hR]
  have hderiv : ∀ r : ℝ,
      HasDerivAt (fun x : ℝ => -(Real.exp (-(x ^ 2))) / 2)
        (Real.exp (-(r ^ 2)) * r) r := by
    intro r
    have hinner : HasDerivAt (fun x : ℝ => -(x ^ 2)) (-2 * r) r := by
      convert ((hasDerivAt_id r).pow 2).neg using 1 <;>
        simp only [id_eq] <;> ring
    have hexp :=
      (Real.hasDerivAt_exp (-(r ^ 2))).comp r hinner
    convert hexp.neg.div_const 2 using 1 <;> ring
  have hint : IntervalIntegrable
      (fun r : ℝ => Real.exp (-(r ^ 2)) * r) volume 0 R := by
    exact (by fun_prop : Continuous
      (fun r : ℝ => Real.exp (-(r ^ 2)) * r)).intervalIntegrable 0 R
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun r _ => hderiv r) hint]
  simp
  ring

end

end ProofGap.Exercise4018
