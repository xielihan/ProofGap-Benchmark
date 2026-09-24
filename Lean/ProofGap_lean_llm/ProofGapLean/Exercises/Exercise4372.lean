import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Data.Real.Sqrt
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise4372

noncomputable section

open MeasureTheory

abbrev Vec3 := ℝ × ℝ × ℝ

def upperSpherePoint (R : ℝ) (p : Vec3) : Prop :=
  (p.1 - R) ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2 = R ^ 2 ∧
    0 < p.2.2

def normalCosines (R : ℝ) (p : Vec3) : Vec3 :=
  ((p.1 - R) / R, p.2.1 / R, p.2.2 / R)

def projectedDisk (r : ℝ) : Set (ℝ × ℝ) :=
  {p | p.1 ^ 2 + p.2 ^ 2 ≤ 2 * r * p.1}

def upperHeight (R : ℝ) (p : ℝ × ℝ) : ℝ :=
  Real.sqrt (2 * R * p.1 - p.1 ^ 2 - p.2 ^ 2)

def surfaceYMoment (R r : ℝ) : ℝ :=
  ∫ p in projectedDisk r,
    p.2 * (R / upperHeight R p)

def surfaceZMoment (R r : ℝ) : ℝ :=
  ∫ p in projectedDisk r,
    upperHeight R p * (R / upperHeight R p)

def normalZProjectionFlux (R r : ℝ) : ℝ :=
  ∫ _p in projectedDisk r, R

def curlSurfaceIntegral (R r : ℝ) : ℝ :=
  surfaceZMoment R r - surfaceYMoment R r

def boundaryCurve (R r t : ℝ) : Vec3 :=
  let p : ℝ × ℝ := (r + r * Real.cos t, r * Real.sin t)
  (p.1, p.2, upperHeight R p)

def vectorField (p : Vec3) : Vec3 :=
  (p.2.1 ^ 2 + p.2.2 ^ 2,
    p.2.2 ^ 2 + p.1 ^ 2,
    p.1 ^ 2 + p.2.1 ^ 2)

def curveIntegral (F : Vec3 → Vec3) (γ : ℝ → Vec3)
    (c d : ℝ) : ℝ :=
  ∫ t in c..d,
    (F (γ t)).1 * deriv (fun s => (γ s).1) t +
      (F (γ t)).2.1 * deriv (fun s => (γ s).2.1) t +
      (F (γ t)).2.2 * deriv (fun s => (γ s).2.2) t

def lineIntegral (R r : ℝ) : ℝ :=
  curveIntegral vectorField (boundaryCurve R r) (-Real.pi) Real.pi

theorem gap1 (R : ℝ) (p : Vec3) (hR : 0 < R)
    (hp : upperSpherePoint R p) :
    (normalCosines R p).1 = (p.1 - R) / R := by
  rfl

theorem gap2 (R : ℝ) (p : Vec3) (hR : 0 < R)
    (hp : upperSpherePoint R p) :
    (normalCosines R p).2.1 = p.2.1 / R := by
  rfl

theorem gap3 (R : ℝ) (p : Vec3) (hR : 0 < R)
    (hp : upperSpherePoint R p) :
    (normalCosines R p).2.2 = p.2.2 / R := by
  rfl

private def curveX (r t : ℝ) : ℝ :=
  r + r * Real.cos t

private def curveY (r t : ℝ) : ℝ :=
  r * Real.sin t

private def curveZ (R r t : ℝ) : ℝ :=
  upperHeight R (curveX r t, curveY r t)

private def rawIntegrand (R r t : ℝ) : ℝ :=
  (curveY r t ^ 2 + curveZ R r t ^ 2) * deriv (curveX r) t +
    (curveZ R r t ^ 2 + curveX r t ^ 2) * deriv (curveY r) t +
    (curveX r t ^ 2 + curveY r t ^ 2) * deriv (curveZ R r) t

private def oddPart (R r t : ℝ) : ℝ :=
  -(r ^ 3) * Real.sin t ^ 3 -
    2 * (R - r) * r ^ 2 * Real.sin t * (1 + Real.cos t)

private def evenPart (R r t : ℝ) : ℝ :=
  (2 * (R - r) * r ^ 2 + r ^ 3) * Real.cos t +
    (2 * (R - r) * r ^ 2 + 2 * r ^ 3) * Real.cos t ^ 2 +
    r ^ 3 * Real.cos t ^ 3

private def heightPart (R r t : ℝ) : ℝ :=
  -2 * r ^ 2 * Real.sqrt (r * (R - r)) *
    (1 + Real.cos t) * Real.sin (t / 2)

private def reducedIntegrand (R r t : ℝ) : ℝ :=
  oddPart R r t + evenPart R r t + heightPart R r t

private theorem lineIntegral_eq_raw (R r : ℝ) :
    lineIntegral R r =
      ∫ t in -Real.pi..Real.pi, rawIntegrand R r t := by
  rfl

private theorem deriv_curveX (r t : ℝ) :
    deriv (curveX r) t = -r * Real.sin t := by
  have h :=
    (hasDerivAt_const t r).add
      ((Real.hasDerivAt_cos t).const_mul r)
  unfold curveX
  convert h.deriv using 1
  all_goals ring

private theorem deriv_curveY (r t : ℝ) :
    deriv (curveY r) t = r * Real.cos t := by
  have h := (Real.hasDerivAt_sin t).const_mul r
  unfold curveY
  convert h.deriv using 1

private theorem circle_identity (r t : ℝ) :
    curveX r t ^ 2 + curveY r t ^ 2 =
      2 * r * curveX r t := by
  unfold curveX curveY
  have hs :
      Real.sin t ^ 2 = 1 - Real.cos t ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq t]
  calc
    (r + r * Real.cos t) ^ 2 + (r * Real.sin t) ^ 2 =
        r ^ 2 * ((1 + Real.cos t) ^ 2 + Real.sin t ^ 2) := by ring
    _ = r ^ 2 *
        ((1 + Real.cos t) ^ 2 + (1 - Real.cos t ^ 2)) := by rw [hs]
    _ = 2 * r * (r + r * Real.cos t) := by ring

private theorem curveZ_sq
    (R r t : ℝ) (hr : 0 < r) (hrR : r < R) :
    curveZ R r t ^ 2 =
      2 * (R - r) * curveX r t := by
  have hx : 0 ≤ curveX r t := by
    unfold curveX
    have hc := Real.neg_one_le_cos t
    nlinarith
  have hargEq :
      2 * R * curveX r t -
          curveX r t ^ 2 - curveY r t ^ 2 =
        2 * (R - r) * curveX r t := by
    calc
      2 * R * curveX r t -
            curveX r t ^ 2 - curveY r t ^ 2 =
          2 * R * curveX r t -
            (curveX r t ^ 2 + curveY r t ^ 2) := by ring
      _ = 2 * R * curveX r t -
            2 * r * curveX r t := by rw [circle_identity]
      _ = _ := by ring
  have harg :
      0 ≤ 2 * R * curveX r t -
        curveX r t ^ 2 - curveY r t ^ 2 := by
    rw [hargEq]
    nlinarith
  unfold curveZ upperHeight
  rw [Real.sq_sqrt harg]
  exact hargEq

private theorem curveZ_formula
    (R r t : ℝ) (hr : 0 < r) (hrR : r < R)
    (ht : t ∈ Set.Icc (-Real.pi) Real.pi) :
    curveZ R r t =
      2 * Real.sqrt (r * (R - r)) * Real.cos (t / 2) := by
  have hA : 0 ≤ r * (R - r) :=
    mul_nonneg hr.le (sub_nonneg.mpr hrR.le)
  have hhalf : 0 ≤ Real.cos (t / 2) :=
    Real.cos_nonneg_of_mem_Icc
      ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hscale :
      Real.sqrt (r * (R - r)) ^ 2 = r * (R - r) :=
    Real.sq_sqrt hA
  have hcos :
      1 + Real.cos t = 2 * Real.cos (t / 2) ^ 2 := by
    have hc := Real.cos_two_mul (t / 2)
    rw [show 2 * (t / 2) = t by ring] at hc
    nlinarith
  have hzsq := curveZ_sq R r t hr hrR
  have hznonneg : 0 ≤ curveZ R r t := by
    unfold curveZ upperHeight
    positivity
  have hrhs :
      0 ≤ 2 * Real.sqrt (r * (R - r)) * Real.cos (t / 2) :=
    mul_nonneg
      (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)) hhalf
  unfold curveX at hzsq
  nlinarith

private theorem deriv_curveZ
    (R r t : ℝ) (hr : 0 < r) (hrR : r < R)
    (ht : t ∈ Set.Ioo (-Real.pi) Real.pi) :
    deriv (curveZ R r) t =
      -Real.sqrt (r * (R - r)) * Real.sin (t / 2) := by
  let z₀ : ℝ → ℝ := fun s =>
    2 * Real.sqrt (r * (R - r)) * Real.cos (s / 2)
  have heq : curveZ R r =ᶠ[nhds t] z₀ := by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
    exact curveZ_formula R r s hr hrR ⟨hs.1.le, hs.2.le⟩
  have hhalf :
      HasDerivAt (fun s : ℝ => s / 2) (1 / 2 : ℝ) t :=
    (hasDerivAt_id t).div_const 2
  have hcos :
      HasDerivAt (fun s : ℝ => Real.cos (s / 2))
        (-(Real.sin (t / 2)) * (1 / 2)) t := by
    convert (Real.hasDerivAt_cos (t / 2)).comp t hhalf using 1
  have hz₀ :
      HasDerivAt z₀
        (-Real.sqrt (r * (R - r)) * Real.sin (t / 2)) t := by
    dsimp [z₀]
    convert hcos.const_mul
      (2 * Real.sqrt (r * (R - r))) using 1
    all_goals ring
  rw [heq.deriv_eq, hz₀.deriv]

private theorem raw_eq_reduced
    (R r t : ℝ) (hr : 0 < r) (hrR : r < R)
    (ht : t ∈ Set.Icc (-Real.pi) Real.pi) :
    rawIntegrand R r t = reducedIntegrand R r t := by
  by_cases hleft : t = -Real.pi
  · subst t
    simp [rawIntegrand, reducedIntegrand, oddPart, evenPart, heightPart,
      curveX, curveY, curveZ, upperHeight, deriv_curveX, deriv_curveY,
      Real.sin_neg, Real.cos_neg]
    ring
  by_cases hright : t = Real.pi
  · subst t
    simp [rawIntegrand, reducedIntegrand, oddPart, evenPart, heightPart,
      curveX, curveY, curveZ, upperHeight, deriv_curveX, deriv_curveY]
    ring
  have htopen : t ∈ Set.Ioo (-Real.pi) Real.pi :=
    ⟨lt_of_le_of_ne ht.1 (Ne.symm hleft),
      lt_of_le_of_ne ht.2 hright⟩
  rw [rawIntegrand, deriv_curveX, deriv_curveY,
    curveZ_sq R r t hr hrR, circle_identity,
    deriv_curveZ R r t hr hrR htopen]
  unfold reducedIntegrand oddPart evenPart heightPart curveX curveY
  ring

private theorem integral_eq_zero_of_odd_symmetric
    (f : ℝ → ℝ) (a : ℝ) (hodd : ∀ x, f (-x) = -f x) :
    (∫ x in -a..a, f x) = 0 := by
  have hreflect :
      (∫ x in -a..a, f (-x)) = ∫ x in -a..a, f x := by
    rw [intervalIntegral.integral_comp_neg]
    ring_nf
  have hfun :
      (fun x : ℝ => f (-x)) = fun x : ℝ => -f x := by
    funext x
    exact hodd x
  have hneg :
      (∫ x in -a..a, f (-x)) = -(∫ x in -a..a, f x) := by
    rw [hfun, intervalIntegral.integral_neg]
  exact neg_eq_self.mp (hneg.symm.trans hreflect)

private theorem oddPart_odd (R r : ℝ) :
    ∀ t, oddPart R r (-t) = -oddPart R r t := by
  intro t
  unfold oddPart
  rw [Real.sin_neg, Real.cos_neg]
  ring

private theorem heightPart_odd (R r : ℝ) :
    ∀ t, heightPart R r (-t) = -heightPart R r t := by
  intro t
  unfold heightPart
  rw [Real.cos_neg]
  have harg : -t / 2 = -(t / 2) := by ring
  rw [harg, Real.sin_neg]
  ring

private theorem evenPart_integral (R r : ℝ) :
    (∫ t in -Real.pi..Real.pi, evenPart R r t) =
      2 * Real.pi * R * r ^ 2 := by
  let A : ℝ := 2 * (R - r) * r ^ 2 + r ^ 3
  let B : ℝ := 2 * (R - r) * r ^ 2 + 2 * r ^ 3
  let C : ℝ := r ^ 3
  have hcos :
      IntervalIntegrable (fun t : ℝ => A * Real.cos t)
        MeasureTheory.volume (-Real.pi) Real.pi := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hcosSq :
      IntervalIntegrable (fun t : ℝ => B * Real.cos t ^ 2)
        MeasureTheory.volume (-Real.pi) Real.pi := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hcosCube :
      IntervalIntegrable (fun t : ℝ => C * Real.cos t ^ 3)
        MeasureTheory.volume (-Real.pi) Real.pi := by
    apply Continuous.intervalIntegrable
    fun_prop
  change
    (∫ t in -Real.pi..Real.pi,
      A * Real.cos t + B * Real.cos t ^ 2 +
        C * Real.cos t ^ 3) = _
  rw [intervalIntegral.integral_add (hcos.add hcosSq) hcosCube,
    intervalIntegral.integral_add hcos hcosSq,
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul,
    integral_cos, integral_cos_sq, integral_cos_pow_three]
  simp [A, B, C, Real.sin_neg, Real.cos_neg]
  ring

private theorem reduced_integral
    (R r : ℝ) :
    (∫ t in -Real.pi..Real.pi, reducedIntegrand R r t) =
      2 * Real.pi * R * r ^ 2 := by
  have hodd :
      IntervalIntegrable (oddPart R r) MeasureTheory.volume
        (-Real.pi) Real.pi := by
    apply Continuous.intervalIntegrable
    unfold oddPart
    fun_prop
  have heven :
      IntervalIntegrable (evenPart R r) MeasureTheory.volume
        (-Real.pi) Real.pi := by
    apply Continuous.intervalIntegrable
    unfold evenPart
    fun_prop
  have hheight :
      IntervalIntegrable (heightPart R r) MeasureTheory.volume
        (-Real.pi) Real.pi := by
    apply Continuous.intervalIntegrable
    unfold heightPart
    fun_prop
  unfold reducedIntegrand
  rw [intervalIntegral.integral_add (hodd.add heven) hheight,
    intervalIntegral.integral_add hodd heven,
    integral_eq_zero_of_odd_symmetric
      (oddPart R r) Real.pi (oddPart_odd R r),
    integral_eq_zero_of_odd_symmetric
      (heightPart R r) Real.pi (heightPart_odd R r),
    evenPart_integral]
  ring

private theorem lineIntegral_formula
    (R r : ℝ) (hr : 0 < r) (hrR : r < R) :
    lineIntegral R r = 2 * Real.pi * R * r ^ 2 := by
  rw [lineIntegral_eq_raw]
  calc
    (∫ t in -Real.pi..Real.pi, rawIntegrand R r t) =
        ∫ t in -Real.pi..Real.pi, reducedIntegrand R r t := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [Set.uIcc_of_le (by linarith [Real.pi_pos])] at ht
      exact raw_eq_reduced R r t hr hrR ht
    _ = _ := reduced_integral R r

private def centeredDisk (r : ℝ) : Set (ℝ × ℝ) :=
  {p | p.1 ^ 2 + p.2 ^ 2 ≤ r ^ 2}

private theorem centeredDisk_area (r : ℝ) (hr : 0 < r) :
    (∫ _p in centeredDisk r, (1 : ℝ)) = Real.pi * r ^ 2 := by
  let f : ℝ × ℝ → ℝ := fun _p => 1
  let q : ℝ → ℝ := fun ρ => ρ
  have hdisk : MeasurableSet (centeredDisk r) := by
    unfold centeredDisk
    measurability
  have hpoint : ∀ p : ℝ × ℝ,
      polarCoord.target.indicator
          (fun z =>
            z.1 * (centeredDisk r).indicator f (polarCoord.symm z)) p =
        (Set.Ioc (0 : ℝ) r ×ˢ Set.Ioo (-Real.pi) Real.pi).indicator
          (fun z => q z.1) p := by
    rintro ⟨ρ, φ⟩
    have htrig :
        (ρ * Real.cos φ) ^ 2 + (ρ * Real.sin φ) ^ 2 = ρ ^ 2 := by
      nlinarith [Real.sin_sq_add_cos_sq φ]
    by_cases ht : 0 < ρ ∧ -Real.pi < φ ∧ φ < Real.pi
    · have hriff : ρ ^ 2 ≤ r ^ 2 ↔ ρ ≤ r := by
        constructor <;> intro h
        · nlinarith
        · nlinarith
      by_cases hρ : ρ ≤ r
      · have htargetmem : (ρ, φ) ∈ polarCoord.target := by
          simpa [polarCoord_target] using ht
        have hrectmem :
            (ρ, φ) ∈ Set.Ioc (0 : ℝ) r ×ˢ Set.Ioo (-Real.pi) Real.pi :=
          ⟨⟨ht.1, hρ⟩, ht.2⟩
        have hpolarmem : polarCoord.symm (ρ, φ) ∈ centeredDisk r := by
          simp only [polarCoord_symm_apply, centeredDisk, Set.mem_setOf_eq,
            Prod.fst, Prod.snd, htrig]
          exact hriff.mpr hρ
        rw [Set.indicator_of_mem htargetmem, Set.indicator_of_mem hrectmem,
          Set.indicator_of_mem hpolarmem]
        simp [f, q]
      · have hsq : ¬ρ ^ 2 ≤ r ^ 2 := by
          intro h
          exact hρ (hriff.mp h)
        simp [polarCoord_target, Set.indicator_of_mem, ht, centeredDisk, f, q,
          htrig, hρ, hsq]
    · have hrect :
          (ρ, φ) ∉ Set.Ioc (0 : ℝ) r ×ˢ Set.Ioo (-Real.pi) Real.pi := by
        intro hp
        exact ht ⟨hp.1.1, hp.2.1, hp.2.2⟩
      have htarget : (ρ, φ) ∉ polarCoord.target := by
        simpa [polarCoord_target, Set.mem_prod] using ht
      rw [Set.indicator_of_notMem htarget, Set.indicator_of_notMem hrect]
  calc
    (∫ _p in centeredDisk r, (1 : ℝ)) =
        ∫ p : ℝ × ℝ, (centeredDisk r).indicator f p := by
      rw [MeasureTheory.integral_indicator hdisk]
    _ = ∫ p in polarCoord.target,
          p.1 * (centeredDisk r).indicator f (polarCoord.symm p) := by
      simpa [smul_eq_mul] using
        (integral_comp_polarCoord_symm ((centeredDisk r).indicator f)).symm
    _ = ∫ p : ℝ × ℝ,
          (Set.Ioc (0 : ℝ) r ×ˢ Set.Ioo (-Real.pi) Real.pi).indicator
            (fun z => q z.1) p := by
      rw [← MeasureTheory.integral_indicator polarCoord.open_target.measurableSet]
      apply MeasureTheory.integral_congr_ae
      exact Filter.Eventually.of_forall hpoint
    _ = ∫ p in Set.Ioc (0 : ℝ) r ×ˢ Set.Ioo (-Real.pi) Real.pi,
          q p.1 * (1 : ℝ) := by
      rw [MeasureTheory.integral_indicator
        (measurableSet_Ioc.prod measurableSet_Ioo)]
      apply MeasureTheory.setIntegral_congr_fun
        (measurableSet_Ioc.prod measurableSet_Ioo)
      intro p hp
      simp
    _ = (∫ ρ in Set.Ioc (0 : ℝ) r, q ρ) *
          ∫ _φ in Set.Ioo (-Real.pi) Real.pi, (1 : ℝ) := by
      exact MeasureTheory.setIntegral_prod_mul q (fun _ : ℝ => 1)
        (Set.Ioc (0 : ℝ) r) (Set.Ioo (-Real.pi) Real.pi)
    _ = (∫ ρ in (0 : ℝ)..r, ρ) * (2 * Real.pi) := by
      have hangle :
          (∫ _φ in Set.Ioo (-Real.pi) Real.pi, (1 : ℝ)) =
            2 * Real.pi := by
        rw [MeasureTheory.setIntegral_const]
        simp [Real.pi_pos.le]
        ring
      rw [intervalIntegral.integral_of_le hr.le]
      simp only [q]
      rw [hangle]
    _ = Real.pi * r ^ 2 := by
      rw [integral_id]
      ring

private theorem projectedDisk_area (r : ℝ) (hr : 0 < r) :
    (∫ _p in projectedDisk r, (1 : ℝ)) = Real.pi * r ^ 2 := by
  let f : ℝ × ℝ → ℝ := fun _p => 1
  let shift : ℝ × ℝ := (r, 0)
  have hpmeas : MeasurableSet (projectedDisk r) := by
    unfold projectedDisk
    measurability
  have hcmeas : MeasurableSet (centeredDisk r) := by
    unfold centeredDisk
    measurability
  have hpoint : ∀ p : ℝ × ℝ,
      (projectedDisk r).indicator f (p + shift) =
        (centeredDisk r).indicator f p := by
    intro p
    have hmem :
        p + shift ∈ projectedDisk r ↔ p ∈ centeredDisk r := by
      simp only [projectedDisk, centeredDisk, Set.mem_setOf_eq, shift,
        Prod.fst_add, Prod.snd_add, Prod.fst, Prod.snd]
      constructor <;> intro h <;> nlinarith
    by_cases hp : p ∈ centeredDisk r
    · rw [Set.indicator_of_mem hp, Set.indicator_of_mem (hmem.mpr hp)]
    · have hpn : p + shift ∉ projectedDisk r :=
        fun h => hp (hmem.mp h)
      rw [Set.indicator_of_notMem hp, Set.indicator_of_notMem hpn]
  calc
    (∫ _p in projectedDisk r, (1 : ℝ)) =
        ∫ p : ℝ × ℝ, (projectedDisk r).indicator f p := by
      rw [MeasureTheory.integral_indicator hpmeas]
    _ = ∫ p : ℝ × ℝ, (projectedDisk r).indicator f (p + shift) := by
      exact (MeasureTheory.integral_add_right_eq_self
        ((projectedDisk r).indicator f) shift).symm
    _ = ∫ p : ℝ × ℝ, (centeredDisk r).indicator f p := by
      apply MeasureTheory.integral_congr_ae
      exact Filter.Eventually.of_forall hpoint
    _ = ∫ _p in centeredDisk r, (1 : ℝ) := by
      rw [MeasureTheory.integral_indicator hcmeas]
    _ = Real.pi * r ^ 2 := centeredDisk_area r hr

private def reflectY (p : ℝ × ℝ) : ℝ × ℝ :=
  (p.1, -p.2)

private def reflectYEquiv : (ℝ × ℝ) ≃ᵐ (ℝ × ℝ) :=
  MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℝ)
    (MeasurableEquiv.neg ℝ)

private theorem reflectY_measurePreserving :
    MeasurePreserving reflectY
      (volume : Measure (ℝ × ℝ)) (volume : Measure (ℝ × ℝ)) := by
  have h := (MeasurePreserving.id (volume : Measure ℝ)).prod
    (Measure.measurePreserving_neg (volume : Measure ℝ))
  rw [Measure.volume_eq_prod ℝ ℝ]
  simpa [reflectY, Prod.map] using h

private theorem surfaceYMoment_zero
    (R r : ℝ) :
    surfaceYMoment R r = 0 := by
  let f : ℝ × ℝ → ℝ :=
    fun p => p.2 * (R / upperHeight R p)
  let g : ℝ × ℝ → ℝ := (projectedDisk r).indicator f
  have hdisk : MeasurableSet (projectedDisk r) := by
    unfold projectedDisk
    measurability
  have hodd : ∀ p, g (reflectY p) = -g p := by
    rintro ⟨x, y⟩
    by_cases hp : x ^ 2 + y ^ 2 ≤ 2 * r * x
    · have hrp :
          reflectY (x, y) ∈ projectedDisk r := by
        simpa [reflectY, projectedDisk] using hp
      have hp' : (x, y) ∈ projectedDisk r := by
        simpa [projectedDisk] using hp
      rw [show g (reflectY (x, y)) = f (reflectY (x, y)) by
          exact Set.indicator_of_mem hrp _,
        show g (x, y) = f (x, y) by exact Set.indicator_of_mem hp' _]
      simp only [f, reflectY, Prod.fst, Prod.snd]
      have hh :
          upperHeight R (x, -y) = upperHeight R (x, y) := by
        unfold upperHeight
        rw [neg_sq]
      rw [hh]
      ring
    · have hp' : (x, y) ∉ projectedDisk r := by
        simpa [projectedDisk] using hp
      have hrp : reflectY (x, y) ∉ projectedDisk r := by
        intro h
        apply hp
        simpa [reflectY, projectedDisk] using h
      rw [show g (reflectY (x, y)) = 0 by
          exact Set.indicator_of_notMem hrp _,
        show g (x, y) = 0 by exact Set.indicator_of_notMem hp' _]
      simp
  have hreflect :
      (∫ p : ℝ × ℝ, g (reflectY p)) = ∫ p : ℝ × ℝ, g p := by
    have h := reflectY_measurePreserving.integral_comp
      reflectYEquiv.measurableEmbedding g
    simpa [reflectYEquiv, reflectY] using h
  have hfun :
      (fun p : ℝ × ℝ => g (reflectY p)) =
        fun p : ℝ × ℝ => -g p := by
    funext p
    exact hodd p
  have hneg :
      (∫ p : ℝ × ℝ, g (reflectY p)) =
        -(∫ p : ℝ × ℝ, g p) := by
    rw [hfun, integral_neg]
  have hzero : (∫ p : ℝ × ℝ, g p) = 0 :=
    neg_eq_self.mp (hneg.symm.trans hreflect)
  unfold surfaceYMoment
  calc
    (∫ p in projectedDisk r, p.2 * (R / upperHeight R p)) =
        ∫ p : ℝ × ℝ, g p := by
      rw [MeasureTheory.integral_indicator hdisk]
    _ = 0 := hzero

private theorem upperHeight_ne_zero_of_mem
    (R r : ℝ) (hr : 0 < r) (hrR : r < R)
    (p : ℝ × ℝ) (hp : p ∈ projectedDisk r)
    (hp0 : p ≠ (0, 0)) :
    upperHeight R p ≠ 0 := by
  rintro hz
  rcases p with ⟨x, y⟩
  simp only [projectedDisk, Set.mem_setOf_eq, Prod.fst, Prod.snd] at hp
  have hx : 0 ≤ x := by
    nlinarith [sq_nonneg x, sq_nonneg y]
  have harg : 0 ≤ 2 * R * x - x ^ 2 - y ^ 2 := by
    nlinarith
  have hsqrt := Real.sq_sqrt harg
  unfold upperHeight at hz
  simp only [Prod.fst, Prod.snd] at hz
  rw [hz] at hsqrt
  have hx0 : x = 0 := by
    nlinarith
  have hy0 : y = 0 := by
    nlinarith [sq_nonneg y]
  apply hp0
  simp [hx0, hy0]

private theorem surfaceZMoment_eq_projection
    (R r : ℝ) (hr : 0 < r) (hrR : r < R) :
    surfaceZMoment R r = normalZProjectionFlux R r := by
  have hdisk : MeasurableSet (projectedDisk r) := by
    unfold projectedDisk
    measurability
  unfold surfaceZMoment normalZProjectionFlux
  apply MeasureTheory.integral_congr_ae
  filter_upwards [ae_restrict_mem hdisk,
    (volume.restrict (projectedDisk r)).ae_ne ((0, 0) : ℝ × ℝ)]
      with p hp hp0
  have hh := upperHeight_ne_zero_of_mem R r hr hrR p hp hp0
  field_simp

private theorem normalZProjectionFlux_formula
    (R r : ℝ) (hr : 0 < r) :
    normalZProjectionFlux R r = R * Real.pi * r ^ 2 := by
  unfold normalZProjectionFlux
  calc
    (∫ _p in projectedDisk r, R) =
        R * ∫ _p in projectedDisk r, (1 : ℝ) := by
      rw [← MeasureTheory.integral_const_mul]
      simp
    _ = R * Real.pi * r ^ 2 := by
      rw [projectedDisk_area r hr]
      ring

private theorem surfaceZMoment_formula
    (R r : ℝ) (hr : 0 < r) (hrR : r < R) :
    surfaceZMoment R r = R * Real.pi * r ^ 2 := by
  rw [surfaceZMoment_eq_projection R r hr hrR,
    normalZProjectionFlux_formula R r hr]

theorem gap4 (R r : ℝ) (hr : 0 < r) (hrR : r < R) :
    lineIntegral R r = 2 * curlSurfaceIntegral R r := by
  rw [lineIntegral_formula R r hr hrR]
  unfold curlSurfaceIntegral
  rw [surfaceZMoment_formula R r hr hrR, surfaceYMoment_zero R r]
  ring

theorem gap5 (R r : ℝ) (hr : 0 < r) (hrR : r < R) :
    curlSurfaceIntegral R r =
      surfaceZMoment R r - surfaceYMoment R r := by
  rfl

theorem gap6 (R r : ℝ) (hr : 0 < r) (hrR : r < R) :
    surfaceYMoment R r = 0 := by
  exact surfaceYMoment_zero R r

theorem gap7 (R r : ℝ) (hr : 0 < r) (hrR : r < R) :
    surfaceZMoment R r = normalZProjectionFlux R r := by
  exact surfaceZMoment_eq_projection R r hr hrR

theorem gap8 (R r : ℝ) (hr : 0 < r) (hrR : r < R) :
    normalZProjectionFlux R r = R * Real.pi * r ^ 2 := by
  exact normalZProjectionFlux_formula R r hr

theorem gap9 (R r : ℝ) (hr : 0 < r) (hrR : r < R) :
    surfaceZMoment R r = R * Real.pi * r ^ 2 := by
  exact surfaceZMoment_formula R r hr hrR

theorem gap10 (R r : ℝ) (hr : 0 < r) (hrR : r < R) :
    lineIntegral R r = 2 * Real.pi * R * r ^ 2 := by
  exact lineIntegral_formula R r hr hrR

end

end ProofGap.Exercise4372
