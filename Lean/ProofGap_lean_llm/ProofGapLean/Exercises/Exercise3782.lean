import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise3782

noncomputable section

open Filter MeasureTheory Set
open scoped BigOperators Interval Topology

def integrand (α x : ℝ) : ℝ :=
  Real.exp (-x) / Real.rpow |Real.sin x| α

def blockIntegral (α : ℝ) (n : ℕ) : ℝ :=
  ∫ x in (n : ℝ) * Real.pi..(n + 1 : ℝ) * Real.pi, integrand α x

def shiftedBlock (α : ℝ) (n : ℕ) : ℝ :=
  ∫ t in (0 : ℝ)..Real.pi,
    Real.exp (-((n : ℝ) * Real.pi + t)) /
      Real.rpow (Real.sin t) α

def F (α : ℝ) : ℝ :=
  ∫ x in Set.Ioi (0 : ℝ), integrand α x

private def singular (r x : ℝ) : ℝ :=
  Real.rpow |Real.sin x| (-r)

private def envelope (r x : ℝ) : ℝ :=
  Real.exp (-x) * singular r x

private def block (n : ℕ) : Set ℝ :=
  Ico ((n : ℝ) * Real.pi) (((n + 1 : ℕ) : ℝ) * Real.pi)

private lemma singular_nonneg (r x : ℝ) : 0 ≤ singular r x :=
  Real.rpow_nonneg (abs_nonneg _) _

private lemma envelope_nonneg (r x : ℝ) : 0 ≤ envelope r x :=
  mul_nonneg (Real.exp_pos _).le (singular_nonneg r x)

private lemma singular_periodic (r : ℝ) :
    Function.Periodic (singular r) Real.pi := by
  intro x
  simp [singular, Real.sin_add_pi]

private lemma singular_continuousOn_Ioo (r : ℝ) :
    ContinuousOn (singular r) (Ioo 0 Real.pi) := by
  intro x hx
  have hs : 0 < Real.sin x :=
    Real.sin_pos_of_pos_of_lt_pi hx.1 hx.2
  exact
    (Real.continuous_sin.continuousAt.abs.rpow_const
      (Or.inl (abs_pos.mpr hs.ne').ne')).continuousWithinAt

private lemma singular_integrable_period {r : ℝ}
    (hr0 : 0 < r) (hr1 : r < 1) :
    IntervalIntegrable (singular r) volume 0 Real.pi := by
  let c : ℝ := 2 / Real.pi
  have hc0 : 0 < c := by
    dsimp [c]
    positivity
  have hp :
      IntegrableOn (fun x : ℝ => Real.rpow x (-r))
        (Ioo (0 : ℝ) (Real.pi / 2)) :=
    (intervalIntegral.integrableOn_Ioo_rpow_iff
      Real.pi_div_two_pos).2 (by linarith)
  have hdom :
      IntegrableOn
        (fun x : ℝ =>
          Real.rpow c (-r) * Real.rpow x (-r))
        (Ioo (0 : ℝ) (Real.pi / 2)) :=
    hp.const_mul (Real.rpow c (-r))
  have hleftOn :
      IntegrableOn (singular r)
        (Ioo (0 : ℝ) (Real.pi / 2)) := by
    apply hdom.mono'
    · exact
        (singular_continuousOn_Ioo r).aestronglyMeasurable
          measurableSet_Ioo |>.mono_measure
            (Measure.restrict_mono
              (Ioo_subset_Ioo le_rfl
                (by linarith [Real.pi_pos])) le_rfl)
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
      have hxp : x < Real.pi := by
        linarith [hx.2, Real.pi_pos]
      have hs : 0 < Real.sin x :=
        Real.sin_pos_of_pos_of_lt_pi hx.1 hxp
      have hj : c * x ≤ Real.sin x := by
        simpa [c] using Real.mul_le_sin hx.1.le hx.2.le
      have hpow :=
        Real.rpow_le_rpow_of_nonpos (mul_pos hc0 hx.1) hj
          (by linarith : -r ≤ 0)
      have hnorm : ‖singular r x‖ = singular r x :=
        Real.norm_of_nonneg (singular_nonneg r x)
      rw [hnorm]
      calc
        singular r x = Real.rpow (Real.sin x) (-r) := by
          simp [singular, abs_of_pos hs]
        _ ≤ Real.rpow (c * x) (-r) := hpow
        _ = Real.rpow c (-r) * Real.rpow x (-r) :=
          Real.mul_rpow hc0.le hx.1.le
  have hleft :
      IntervalIntegrable (singular r) volume 0 (Real.pi / 2) :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le
      Real.pi_div_two_pos.le).2 hleftOn
  have hrightComp :
      IntervalIntegrable
        (fun x : ℝ => singular r (Real.pi - x))
        volume (Real.pi / 2) Real.pi := by
    convert (hleft.comp_sub_left Real.pi).symm using 1 <;> ring
  have hright :
      IntervalIntegrable (singular r) volume
        (Real.pi / 2) Real.pi := by
    apply hrightComp.congr
    intro x _
    simp [singular, Real.sin_pi_sub]
  exact hleft.trans hright

private lemma singular_intervalIntegrable {r a b : ℝ}
    (hr0 : 0 < r) (hr1 : r < 1) :
    IntervalIntegrable (singular r) volume a b := by
  exact
    (singular_periodic r).intervalIntegrable₀ Real.pi_ne_zero
      (singular_integrable_period hr0 hr1) a b

private lemma envelope_intervalIntegrable {r a b : ℝ}
    (hr0 : 0 < r) (hr1 : r < 1) :
    IntervalIntegrable (envelope r) volume a b := by
  have hs :=
    singular_intervalIntegrable (a := a) (b := b) hr0 hr1
  have he :
      ContinuousOn (fun x : ℝ => Real.exp (-x)) [[a, b]] := by
    fun_prop
  exact hs.continuousOn_mul he

private lemma envelope_integrable_block {r : ℝ}
    (hr0 : 0 < r) (hr1 : r < 1) (n : ℕ) :
    IntegrableOn (envelope r) (block n) := by
  let a : ℝ := (n : ℝ) * Real.pi
  let b : ℝ := ((n + 1 : ℕ) : ℝ) * Real.pi
  have hab : a ≤ b := by
    dsimp [a, b]
    apply mul_le_mul_of_nonneg_right _ Real.pi_nonneg
    norm_num
  have hi :
      IntegrableOn (envelope r) (Ioc a b) := by
    have H :=
      (envelope_intervalIntegrable (a := a) (b := b)
        hr0 hr1).def'
    rwa [uIoc_of_le hab] at H
  have hic : Ico a b =ᵐ[volume] Ioc a b := Ico_ae_eq_Ioc
  exact hi.congr_set_ae (by simpa [block, a, b] using hic)

private lemma block_integral_norm_le {r : ℝ}
    (hr0 : 0 < r) (hr1 : r < 1) (n : ℕ) :
    (∫ x in block n, ‖envelope r x‖) ≤
      Real.exp (-((n : ℝ) * Real.pi)) *
        ∫ x in (0 : ℝ)..Real.pi, singular r x := by
  let a : ℝ := (n : ℝ) * Real.pi
  let b : ℝ := ((n + 1 : ℕ) : ℝ) * Real.pi
  have hab : a ≤ b := by
    dsimp [a, b]
    apply mul_le_mul_of_nonneg_right _ Real.pi_nonneg
    norm_num
  have hs : IntervalIntegrable (singular r) volume a b :=
    singular_intervalIntegrable hr0 hr1
  have he : IntervalIntegrable (envelope r) volume a b :=
    envelope_intervalIntegrable hr0 hr1
  have hg :
      IntervalIntegrable
        (fun x : ℝ => Real.exp (-a) * singular r x)
        volume a b :=
    hs.const_mul (Real.exp (-a))
  have hle :
      (∫ x in a..b, envelope r x) ≤
        ∫ x in a..b, Real.exp (-a) * singular r x := by
    apply intervalIntegral.integral_mono_on hab he hg
    intro x hx
    exact mul_le_mul_of_nonneg_right
      (Real.exp_le_exp.mpr (neg_le_neg hx.1))
      (singular_nonneg r x)
  have hb : b = a + Real.pi := by
    dsimp [a, b]
    push_cast
    ring
  have hperiod :
      (∫ x in a..b, singular r x) =
        ∫ x in (0 : ℝ)..Real.pi, singular r x := by
    rw [hb]
    simpa using
      (singular_periodic r).intervalIntegral_add_eq a 0
  have hright :
      (∫ x in a..b, Real.exp (-a) * singular r x) =
        Real.exp (-a) *
          ∫ x in (0 : ℝ)..Real.pi, singular r x := by
    rw [intervalIntegral.integral_const_mul, hperiod]
  have hset :
      (∫ x in block n, ‖envelope r x‖) =
        ∫ x in a..b, envelope r x := by
    rw [intervalIntegral.integral_of_le hab]
    change
      (∫ x : ℝ, ‖envelope r x‖ ∂volume.restrict (block n)) =
        ∫ x : ℝ, envelope r x ∂volume.restrict (Ioc a b)
    have hic : block n =ᵐ[volume] Ioc a b := by
      simpa [block, a, b] using
        (Ico_ae_eq_Ioc : Ico a b =ᵐ[volume] Ioc a b)
    rw [Measure.restrict_congr_set hic]
    apply integral_congr_ae
    filter_upwards with x
    exact Real.norm_of_nonneg (envelope_nonneg r x)
  calc
    (∫ x in block n, ‖envelope r x‖) =
        ∫ x in a..b, envelope r x := hset
    _ ≤ ∫ x in a..b,
          Real.exp (-a) * singular r x := hle
    _ = Real.exp (-((n : ℝ) * Real.pi)) *
        ∫ x in (0 : ℝ)..Real.pi, singular r x := by
      simpa [a] using hright

private lemma exp_block_summable :
    Summable
      (fun n : ℕ => Real.exp (-((n : ℝ) * Real.pi))) := by
  have H :=
    Real.summable_exp_nat_mul_iff.mpr
      (by linarith [Real.pi_pos] : -Real.pi < 0)
  convert H using 1
  funext n
  congr 1
  ring

private lemma envelope_integrable_Ioi {r : ℝ}
    (hr0 : 0 < r) (hr1 : r < 1) :
    IntegrableOn (envelope r) (Ioi (0 : ℝ)) := by
  have hexp := exp_block_summable
  have hdom :
      Summable
        (fun n : ℕ =>
          Real.exp (-((n : ℝ) * Real.pi)) *
            ∫ x in (0 : ℝ)..Real.pi, singular r x) := by
    simpa [mul_comm] using
      hexp.mul_left
        (∫ x in (0 : ℝ)..Real.pi, singular r x)
  have hsum :
      Summable
        (fun n : ℕ => ∫ x in block n, ‖envelope r x‖) :=
    hdom.of_nonneg_of_le
      (fun n => integral_nonneg (fun x => norm_nonneg _))
      (fun n => block_integral_norm_le hr0 hr1 n)
  have hu :
      IntegrableOn (envelope r) (⋃ n : ℕ, block n) :=
    integrableOn_iUnion_of_summable_integral_norm
      (fun n => envelope_integrable_block hr0 hr1 n) hsum
  apply hu.mono_set
  intro x hx
  have hx0 : 0 ≤ x := hx.le
  let y : ℝ := x / Real.pi
  have hy0 : 0 ≤ y := by
    dsimp [y]
    positivity
  let n : ℕ := ⌊y⌋₊
  have hnle : (n : ℝ) ≤ y := by
    dsimp [n]
    exact Nat.floor_le hy0
  have hnlt : y < (n : ℝ) + 1 := by
    dsimp [n]
    simpa using Nat.lt_floor_add_one y
  apply mem_iUnion.2
  refine ⟨n, ?_⟩
  change
    (n : ℝ) * Real.pi ≤ x ∧
      x < (((n + 1 : ℕ) : ℝ) * Real.pi)
  constructor
  · exact (le_div_iff₀ Real.pi_pos).mp
      (by simpa [y] using hnle)
  · have H :=
      (div_lt_iff₀ Real.pi_pos).mp
        (by simpa [y] using hnlt)
    simpa using H

private lemma integrand_eq_envelope {a x : ℝ} :
    integrand a x = envelope a x := by
  have hneg :
      Real.rpow |Real.sin x| (-a) =
        (Real.rpow |Real.sin x| a)⁻¹ :=
    Real.rpow_neg (abs_nonneg _) a
  rw [integrand, envelope, singular, hneg, div_eq_mul_inv]

private lemma integrand_norm_le_envelope {a r x : ℝ}
    (ha0 : 0 < a) (har : a < r) (hr0 : 0 < r) :
    ‖integrand a x‖ ≤ envelope r x := by
  by_cases hs0 : |Real.sin x| = 0
  · simp [integrand, hs0, envelope, singular,
      Real.zero_rpow, ha0.ne', hr0.ne']
  have hspos : 0 < |Real.sin x| :=
    (abs_nonneg _).lt_of_ne' hs0
  have hsle : |Real.sin x| ≤ 1 :=
    Real.abs_sin_le_one x
  rw [integrand_eq_envelope, envelope, singular]
  have hnonneg :
      0 ≤ Real.exp (-x) * Real.rpow |Real.sin x| (-a) :=
    mul_nonneg (Real.exp_pos _).le
      (Real.rpow_nonneg hspos.le (-a))
  rw [Real.norm_of_nonneg hnonneg]
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_ge hspos hsle
      (by linarith))
    (Real.exp_pos _).le

private lemma ae_sin_ne_zero :
    ∀ᵐ x : ℝ ∂volume, Real.sin x ≠ 0 := by
  let z : ℤ → ℝ := fun n => (n : ℝ) * Real.pi
  filter_upwards [(Set.countable_range z).ae_notMem volume] with x hx
  intro hs
  apply hx
  rcases Real.sin_eq_zero_iff.mp hs with ⟨n, hn⟩
  exact ⟨n, hn⟩

private lemma integrand_integrable_Ioi {a : ℝ}
    (ha0 : 0 < a) (ha1 : a < 1) :
    IntegrableOn (integrand a) (Ioi (0 : ℝ)) := by
  have heq : integrand a = envelope a := by
    funext x
    exact integrand_eq_envelope
  rw [heq]
  exact envelope_integrable_Ioi ha0 ha1

private lemma pairwise_disjoint_block :
    ∀ ⦃i j : ℕ⦄, i ≠ j → Disjoint (block i) (block j) := by
  intro i j hij
  rcases lt_or_gt_of_ne hij with hijlt | hjilt
  · rw [Set.disjoint_left]
    intro x hxi hxj
    have hijNat : i + 1 ≤ j := Nat.succ_le_iff.mpr hijlt
    have hijReal : ((i + 1 : ℕ) : ℝ) ≤ (j : ℝ) := by
      exact_mod_cast hijNat
    have hbound :
        (((i + 1 : ℕ) : ℝ) * Real.pi) ≤
          (j : ℝ) * Real.pi :=
      mul_le_mul_of_nonneg_right hijReal Real.pi_nonneg
    change
      (i : ℝ) * Real.pi ≤ x ∧
          x < (((i + 1 : ℕ) : ℝ) * Real.pi) at hxi
    change
      (j : ℝ) * Real.pi ≤ x ∧
          x < (((j + 1 : ℕ) : ℝ) * Real.pi) at hxj
    linarith
  · rw [Set.disjoint_left]
    intro x hxi hxj
    have hjiNat : j + 1 ≤ i := Nat.succ_le_iff.mpr hjilt
    have hjiReal : ((j + 1 : ℕ) : ℝ) ≤ (i : ℝ) := by
      exact_mod_cast hjiNat
    have hbound :
        (((j + 1 : ℕ) : ℝ) * Real.pi) ≤
          (i : ℝ) * Real.pi :=
      mul_le_mul_of_nonneg_right hjiReal Real.pi_nonneg
    change
      (i : ℝ) * Real.pi ≤ x ∧
          x < (((i + 1 : ℕ) : ℝ) * Real.pi) at hxi
    change
      (j : ℝ) * Real.pi ≤ x ∧
          x < (((j + 1 : ℕ) : ℝ) * Real.pi) at hxj
    linarith

private lemma iUnion_block_eq_Ici :
    (⋃ n : ℕ, block n) = Ici (0 : ℝ) := by
  ext x
  constructor
  · intro hx
    rcases mem_iUnion.1 hx with ⟨n, hn⟩
    exact
      (mul_nonneg (Nat.cast_nonneg n) Real.pi_nonneg).trans hn.1
  · intro hx
    have hx0 : 0 ≤ x := hx
    let y : ℝ := x / Real.pi
    have hy0 : 0 ≤ y := by
      dsimp [y]
      positivity
    let n : ℕ := ⌊y⌋₊
    have hnle : (n : ℝ) ≤ y := by
      dsimp [n]
      exact Nat.floor_le hy0
    have hnlt : y < (n : ℝ) + 1 := by
      dsimp [n]
      simpa using Nat.lt_floor_add_one y
    apply mem_iUnion.2
    refine ⟨n, ?_⟩
    change
      (n : ℝ) * Real.pi ≤ x ∧
        x < (((n + 1 : ℕ) : ℝ) * Real.pi)
    constructor
    · exact (le_div_iff₀ Real.pi_pos).mp
        (by simpa [y] using hnle)
    · have H :=
        (div_lt_iff₀ Real.pi_pos).mp
          (by simpa [y] using hnlt)
      simpa using H

private lemma blockIntegral_eq_setIntegral (a : ℝ) (n : ℕ) :
    blockIntegral a n = ∫ x in block n, integrand a x := by
  have hcast :
      (n : ℝ) + 1 = ((n + 1 : ℕ) : ℝ) := by
    norm_num
  have hab :
      (n : ℝ) * Real.pi ≤
        ((n + 1 : ℕ) : ℝ) * Real.pi := by
    apply mul_le_mul_of_nonneg_right _ Real.pi_nonneg
    norm_num
  unfold blockIntegral
  rw [hcast]
  rw [intervalIntegral.integral_of_le hab]
  exact
    (setIntegral_congr_set
      (Ico_ae_eq_Ioc :
        Ico ((n : ℝ) * Real.pi)
            (((n + 1 : ℕ) : ℝ) * Real.pi) =ᵐ[volume]
          Ioc ((n : ℝ) * Real.pi)
            (((n + 1 : ℕ) : ℝ) * Real.pi))).symm

theorem gap1 (α : ℝ) (hα : 0 < α) (hα1 : α < 1) :
    F α = ∑' n : ℕ, blockIntegral α n := by
  have hint := integrand_integrable_Ioi hα hα1
  have hintUnion :
      IntegrableOn (integrand α) (⋃ n : ℕ, block n) := by
    rw [iUnion_block_eq_Ici]
    exact hint.congr_set_ae Ioi_ae_eq_Ici.symm
  calc
    F α = ∫ x in (⋃ n : ℕ, block n), integrand α x := by
      unfold F
      rw [iUnion_block_eq_Ici]
      exact setIntegral_congr_set Ioi_ae_eq_Ici
    _ = ∑' n : ℕ, ∫ x in block n, integrand α x :=
      integral_iUnion (fun _ => measurableSet_Ico)
        pairwise_disjoint_block hintUnion
    _ = ∑' n : ℕ, blockIntegral α n := by
      apply tsum_congr
      intro n
      exact (blockIntegral_eq_setIntegral α n).symm

private lemma blockIntegral_eq_shiftedBlock (a : ℝ) (n : ℕ) :
    blockIntegral a n = shiftedBlock a n := by
  have hshift :
      (∫ t in (0 : ℝ)..Real.pi,
          integrand a (t + (n : ℝ) * Real.pi)) =
        ∫ x in (n : ℝ) * Real.pi..
            Real.pi + (n : ℝ) * Real.pi, integrand a x :=
    by
      simpa only [zero_add] using
        (intervalIntegral.integral_comp_add_right
          (f := integrand a) (a := 0) (b := Real.pi)
            ((n : ℝ) * Real.pi))
  have hright :
      Real.pi + (n : ℝ) * Real.pi =
        ((n : ℝ) + 1) * Real.pi := by ring
  unfold blockIntegral shiftedBlock
  rw [← hright, ← hshift]
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le Real.pi_nonneg] at ht
  have hsin0 :
      0 ≤ Real.sin t :=
    Real.sin_nonneg_of_nonneg_of_le_pi ht.1 ht.2
  unfold integrand
  change
    Real.exp (-(t + (n : ℝ) * Real.pi)) /
        Real.rpow |Real.sin (t + (n : ℝ) * Real.pi)| a =
      Real.exp (-((n : ℝ) * Real.pi + t)) /
        Real.rpow (Real.sin t) a
  rw [Real.sin_add_nat_mul_pi, abs_mul, abs_pow,
    abs_neg, abs_one, one_pow, one_mul, abs_of_nonneg hsin0]
  congr 2 <;> ring

theorem gap2 (α : ℝ) (hα : 0 < α) (hα1 : α < 1) :
    F α = ∑' n : ℕ, shiftedBlock α n := by
  rw [gap1 α hα hα1]
  apply tsum_congr
  intro n
  exact blockIntegral_eq_shiftedBlock α n

private lemma reciprocal_sin_intervalIntegrable {a : ℝ}
    (ha0 : 0 < a) (ha1 : a < 1) :
    IntervalIntegrable
      (fun t : ℝ => 1 / Real.rpow (Real.sin t) a)
      volume 0 Real.pi := by
  have hs := singular_integrable_period ha0 ha1
  apply hs.congr
  intro t ht
  rw [uIoc_of_le Real.pi_nonneg] at ht
  have hsin0 :
      0 ≤ Real.sin t :=
    Real.sin_nonneg_of_nonneg_of_le_pi ht.1.le ht.2
  unfold singular
  rw [abs_of_nonneg hsin0]
  change
    Real.rpow (Real.sin t) (-a) =
      1 / Real.rpow (Real.sin t) a
  rw [one_div]
  exact Real.rpow_neg hsin0 a

private lemma shifted_pointwise_le
    {a r : ℝ} (n : ℕ) (ha0 : 0 < a)
    (har : a ≤ r) (hr0 : 0 < r)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) Real.pi) :
    Real.exp (-((n : ℝ) * Real.pi + t)) /
        Real.rpow (Real.sin t) a ≤
      Real.exp (-((n : ℝ) * Real.pi)) *
        (1 / Real.rpow (Real.sin t) r) := by
  have hs0 :
      0 ≤ Real.sin t :=
    Real.sin_nonneg_of_nonneg_of_le_pi ht.1 ht.2
  have hs1 : Real.sin t ≤ 1 :=
    (le_abs_self _).trans (Real.abs_sin_le_one t)
  by_cases hs : Real.sin t = 0
  · simp [hs, Real.zero_rpow, ha0.ne', hr0.ne']
  have hspos : 0 < Real.sin t := hs0.lt_of_ne' hs
  have hpow :
      Real.rpow (Real.sin t) r ≤
        Real.rpow (Real.sin t) a :=
    Real.rpow_le_rpow_of_exponent_ge hspos hs1 har
  have hinv :
      1 / Real.rpow (Real.sin t) a ≤
        1 / Real.rpow (Real.sin t) r :=
    one_div_le_one_div_of_le
      (Real.rpow_pos_of_pos hspos r) hpow
  have hinv' :
      (Real.rpow (Real.sin t) a)⁻¹ ≤
        (Real.rpow (Real.sin t) r)⁻¹ := by
    simpa only [one_div] using hinv
  have hexp :
      Real.exp (-((n : ℝ) * Real.pi + t)) ≤
        Real.exp (-((n : ℝ) * Real.pi)) :=
    Real.exp_le_exp.mpr (by linarith [ht.1])
  rw [div_eq_mul_inv, one_div]
  exact mul_le_mul hexp hinv'
    (inv_nonneg.mpr (Real.rpow_nonneg hs0 a))
    (Real.exp_pos _).le

theorem gap3 (α α₀ : ℝ) (n : ℕ) (hα : 0 < α)
    (hαα₀ : α ≤ α₀) (hα₀ : α₀ < 1) :
    shiftedBlock α n ≤
      Real.exp (-((n : ℝ) * Real.pi)) *
        ∫ t in (0 : ℝ)..Real.pi,
          1 / Real.rpow (Real.sin t) α₀ := by
  have hα₀pos : 0 < α₀ := hα.trans_le hαα₀
  have hrecip :=
    reciprocal_sin_intervalIntegrable hα₀pos hα₀
  have hmajor :
      IntervalIntegrable
        (fun t : ℝ =>
          Real.exp (-((n : ℝ) * Real.pi)) *
            (1 / Real.rpow (Real.sin t) α₀))
        volume 0 Real.pi :=
    hrecip.const_mul _
  have hshift :
      IntervalIntegrable
        (fun t : ℝ =>
          Real.exp (-((n : ℝ) * Real.pi + t)) /
            Real.rpow (Real.sin t) α)
        volume 0 Real.pi := by
    apply hmajor.mono_fun
    · have hp :
          Continuous
            (fun t : ℝ => Real.rpow (Real.sin t) α) :=
        (Real.continuous_rpow_const hα.le).comp
          Real.continuous_sin
      exact
        ((by fun_prop :
          Measurable fun t : ℝ =>
            Real.exp (-((n : ℝ) * Real.pi + t))).div
          hp.measurable).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_uIoc] with t ht
      rw [uIoc_of_le Real.pi_nonneg] at ht
      have htIcc : t ∈ Icc (0 : ℝ) Real.pi :=
        ⟨ht.1.le, ht.2⟩
      have hs0 :
          0 ≤ Real.sin t :=
        Real.sin_nonneg_of_nonneg_of_le_pi htIcc.1 htIcc.2
      have hleft0 :
          0 ≤ Real.exp (-((n : ℝ) * Real.pi + t)) /
            Real.rpow (Real.sin t) α :=
        div_nonneg (Real.exp_pos _).le
          (Real.rpow_nonneg hs0 α)
      have hright0 :
          0 ≤ Real.exp (-((n : ℝ) * Real.pi)) *
            (1 / Real.rpow (Real.sin t) α₀) :=
        mul_nonneg (Real.exp_pos _).le
          (one_div_nonneg.mpr
            (Real.rpow_nonneg hs0 α₀))
      change
        |(Real.exp (-((n : ℝ) * Real.pi + t)) /
          Real.rpow (Real.sin t) α)| ≤
        |(Real.exp (-((n : ℝ) * Real.pi)) *
          (1 / Real.rpow (Real.sin t) α₀))|
      rw [abs_of_nonneg hleft0, abs_of_nonneg hright0]
      exact shifted_pointwise_le n hα hαα₀ hα₀pos htIcc
  unfold shiftedBlock
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_mono_on
    Real.pi_nonneg hshift hmajor
  intro t ht
  exact shifted_pointwise_le n hα hαα₀ hα₀pos ht

theorem gap4 (α α₀ : ℝ) (hα : 0 < α)
    (hαα₀ : α ≤ α₀) (hα₀ : α₀ < 1) :
    (∫ t in (0 : ℝ)..Real.pi,
        1 / Real.rpow (Real.sin t) α₀) =
      2 * ∫ t in (0 : ℝ)..Real.pi / 2,
        1 / Real.rpow (Real.sin t) α₀ := by
  have hα₀pos : 0 < α₀ := hα.trans_le hαα₀
  have hint :=
    reciprocal_sin_intervalIntegrable hα₀pos hα₀
  have hleft :
      IntervalIntegrable
        (fun t : ℝ => 1 / Real.rpow (Real.sin t) α₀)
        volume 0 (Real.pi / 2) := by
    apply hint.mono_set
    rw [uIcc_of_le Real.pi_nonneg,
      uIcc_of_le Real.pi_div_two_pos.le]
    intro t ht
    exact ⟨ht.1, ht.2.trans (by linarith [Real.pi_pos])⟩
  have hright :
      IntervalIntegrable
        (fun t : ℝ => 1 / Real.rpow (Real.sin t) α₀)
        volume (Real.pi / 2) Real.pi := by
    apply hint.mono_set
    rw [uIcc_of_le Real.pi_nonneg,
      uIcc_of_le (by linarith [Real.pi_pos] :
        Real.pi / 2 ≤ Real.pi)]
    intro t ht
    exact ⟨(by linarith [Real.pi_pos, ht.1]), ht.2⟩
  have hsym :
      (∫ t in Real.pi / 2..Real.pi,
          1 / Real.rpow (Real.sin t) α₀) =
        ∫ t in (0 : ℝ)..Real.pi / 2,
          1 / Real.rpow (Real.sin t) α₀ := by
    have hcomp :=
      intervalIntegral.integral_comp_sub_left
        (f := fun t : ℝ =>
          1 / Real.rpow (Real.sin t) α₀)
        (a := Real.pi / 2) (b := Real.pi) Real.pi
    rw [show Real.pi - Real.pi = (0 : ℝ) by ring,
      show Real.pi - Real.pi / 2 = Real.pi / 2 by ring] at hcomp
    simpa only [Real.sin_pi_sub] using hcomp
  rw [← intervalIntegral.integral_add_adjacent_intervals
      hleft hright, hsym]
  ring

theorem gap5 (α α₀ : ℝ) (hα : 0 < α)
    (hαα₀ : α ≤ α₀) (hα₀ : α₀ < 1) :
    ∃ L : ℝ,
      Tendsto
        (fun η : ℝ => ∫ t in η..Real.pi - η,
          1 / Real.rpow (Real.sin t) α₀)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds L) := by
  have hα₀pos : 0 < α₀ := hα.trans_le hαα₀
  let g : ℝ → ℝ :=
    fun t => 1 / Real.rpow (Real.sin t) α₀
  have hint : IntervalIntegrable g volume 0 Real.pi := by
    exact reciprocal_sin_intervalIntegrable hα₀pos hα₀
  let P : ℝ → ℝ := fun b => ∫ t in (0 : ℝ)..b, g t
  let S : Set ℝ := Icc (0 : ℝ) (Real.pi / 2)
  have hP :
      ContinuousOn P (Icc (0 : ℝ) Real.pi) := by
    simpa only [P, uIcc_of_le Real.pi_nonneg] using
      intervalIntegral.continuousOn_primitive_interval'
        hint left_mem_uIcc
  have hleft :
      ContinuousOn (fun η : ℝ => P η) S := by
    apply hP.mono
    intro η hη
    exact ⟨hη.1, hη.2.trans
      (by linarith [Real.pi_pos])⟩
  have hright :
      ContinuousOn (fun η : ℝ => P (Real.pi - η)) S := by
    apply hP.comp
      (continuous_const.sub continuous_id).continuousOn
    intro η hη
    change Real.pi - η ∈ Icc (0 : ℝ) Real.pi
    constructor <;> linarith [Real.pi_pos, hη.1, hη.2]
  have hdiff :
      ContinuousOn
        (fun η : ℝ => P (Real.pi - η) - P η) S :=
    hright.sub hleft
  have heq :
      ∀ η ∈ S,
        (∫ t in η..Real.pi - η, g t) =
          P (Real.pi - η) - P η := by
    intro η hη
    have hηpi : η ≤ Real.pi - η := by
      linarith [hη.2]
    have h0η :
        IntervalIntegrable g volume 0 η := by
      apply hint.mono_set
      rw [uIcc_of_le Real.pi_nonneg,
        uIcc_of_le hη.1]
      intro t ht
      exact ⟨ht.1, ht.2.trans
        (hη.2.trans (by linarith [Real.pi_pos]))⟩
    have hηright :
        IntervalIntegrable g volume η (Real.pi - η) := by
      apply hint.mono_set
      rw [uIcc_of_le Real.pi_nonneg,
        uIcc_of_le hηpi]
      intro t ht
      exact ⟨hη.1.trans ht.1,
        ht.2.trans (by linarith [hη.1])⟩
    have hadd :=
      intervalIntegral.integral_add_adjacent_intervals
        h0η hηright
    dsimp [P]
    linarith
  let H : ℝ → ℝ :=
    fun η => ∫ t in η..Real.pi - η, g t
  have hH :
      ContinuousOn H S := by
    apply hdiff.congr
    intro η hη
    simpa only [H] using heq η hη
  have hzero : (0 : ℝ) ∈ S := by
    exact ⟨le_rfl, Real.pi_div_two_pos.le⟩
  have hSmem : S ∈ 𝓝[Ioi (0 : ℝ)] 0 := by
    rw [mem_nhdsWithin_iff_exists_mem_nhds_inter]
    refine ⟨Iio (Real.pi / 2),
      Iio_mem_nhds Real.pi_div_two_pos, ?_⟩
    intro η hη
    exact ⟨hη.2.le, hη.1.le⟩
  have hcont :
      ContinuousWithinAt H (Ioi (0 : ℝ)) 0 :=
    (hH 0 hzero).mono_of_mem_nhdsWithin hSmem
  refine
    ⟨∫ t in (0 : ℝ)..Real.pi,
        1 / Real.rpow (Real.sin t) α₀, ?_⟩
  change Tendsto H (𝓝[Ioi (0 : ℝ)] 0)
    (𝓝 (∫ t in (0 : ℝ)..Real.pi, g t))
  have ht := hcont
  change Tendsto H (𝓝[Ioi (0 : ℝ)] 0) (𝓝 (H 0)) at ht
  simpa [H, g] using ht

theorem gap6 (α α₀ : ℝ) (hα : 0 < α)
    (hαα₀ : α ≤ α₀) (hα₀ : α₀ < 1) :
    Summable
      (fun n : ℕ => Real.exp (-((n : ℝ) * Real.pi))) := by
  exact exp_block_summable

private lemma shiftedBlock_nonneg {a : ℝ} (ha : 0 < a)
    (n : ℕ) :
    0 ≤ shiftedBlock a n := by
  unfold shiftedBlock
  apply intervalIntegral.integral_nonneg Real.pi_nonneg
  intro t ht
  have hs0 :
      0 ≤ Real.sin t :=
    Real.sin_nonneg_of_nonneg_of_le_pi ht.1 ht.2
  exact div_nonneg (Real.exp_pos _).le
    (Real.rpow_nonneg hs0 a)

theorem gap7 (α₀ : ℝ) (hα₀pos : 0 < α₀) (hα₀ : α₀ < 1)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ N₁ : ℕ, N ≤ N₁ → ∀ α ∈ Set.Ioc (0 : ℝ) α₀,
      |∑ n ∈ Finset.Icc N N₁, shiftedBlock α n| < ε := by
  let C : ℝ :=
    ∫ t in (0 : ℝ)..Real.pi,
      1 / Real.rpow (Real.sin t) α₀
  let d : ℕ → ℝ :=
    fun n => Real.exp (-((n : ℝ) * Real.pi)) * C
  have hC0 : 0 ≤ C := by
    dsimp [C]
    apply intervalIntegral.integral_nonneg Real.pi_nonneg
    intro t ht
    have hs0 :
        0 ≤ Real.sin t :=
      Real.sin_nonneg_of_nonneg_of_le_pi ht.1 ht.2
    exact one_div_nonneg.mpr (Real.rpow_nonneg hs0 α₀)
  have hd0 : ∀ n : ℕ, 0 ≤ d n := by
    intro n
    exact mul_nonneg (Real.exp_pos _).le hC0
  have hd : Summable d := by
    dsimp [d]
    exact exp_block_summable.mul_right C
  have hcauchy :
      CauchySeq (fun m : ℕ => ∑ n ∈ Finset.range m, d n) :=
    hd.hasSum.tendsto_sum_nat.cauchySeq
  obtain ⟨N, hN⟩ :=
    (Metric.cauchySeq_iff'.1 hcauchy) ε hε
  refine ⟨N, ?_⟩
  intro N₁ hNN₁ α hα
  have hNsucc : N ≤ N₁ + 1 :=
    hNN₁.trans (Nat.le_succ N₁)
  have htail := hN (N₁ + 1) hNsucc
  rw [Real.dist_eq,
    ← Finset.sum_Ico_eq_sub _ hNsucc] at htail
  have hshift0 :
      0 ≤ ∑ n ∈ Finset.Icc N N₁, shiftedBlock α n := by
    exact Finset.sum_nonneg fun n _ =>
      shiftedBlock_nonneg hα.1 n
  have hdSum0 :
      0 ≤ ∑ n ∈ Finset.Icc N N₁, d n :=
    Finset.sum_nonneg fun n _ => hd0 n
  have hle :
      (∑ n ∈ Finset.Icc N N₁, shiftedBlock α n) ≤
        ∑ n ∈ Finset.Icc N N₁, d n := by
    apply Finset.sum_le_sum
    intro n hn
    simpa [d, C] using
      gap3 α α₀ n hα.1 hα.2 hα₀
  calc
    |∑ n ∈ Finset.Icc N N₁, shiftedBlock α n| =
        ∑ n ∈ Finset.Icc N N₁, shiftedBlock α n :=
      abs_of_nonneg hshift0
    _ ≤ ∑ n ∈ Finset.Icc N N₁, d n := hle
    _ = |∑ n ∈ Finset.Icc N N₁, d n| :=
      (abs_of_nonneg hdSum0).symm
    _ < ε := by
      simpa [Finset.Ico_succ_right_eq_Icc] using htail

private theorem F_continuous_Ioo :
    ContinuousOn F (Ioo (0 : ℝ) 1) := by
  intro α hα
  change 0 < α ∧ α < 1 at hα
  let q : ℝ := α / 2
  let r : ℝ := (α + 1) / 2
  have hq0 : 0 < q := by
    dsimp [q]
    linarith
  have hqα : q < α := by
    dsimp [q]
    linarith
  have hαr : α < r := by
    dsimp [r]
    linarith
  have hr0 : 0 < r := hα.1.trans hαr
  have hr1 : r < 1 := by
    dsimp [r]
    linarith
  have henv :
      Integrable (envelope r)
        (volume.restrict (Ioi (0 : ℝ))) :=
    envelope_integrable_Ioi hr0 hr1
  have hmeas :
      ∀ᶠ a in 𝓝 α,
        AEStronglyMeasurable (integrand a)
          (volume.restrict (Ioi (0 : ℝ))) := by
    filter_upwards [Ioi_mem_nhds hqα] with a ha
    change q < a at ha
    have hp :
        Continuous
          (fun x : ℝ => Real.rpow |Real.sin x| a) :=
      (Real.continuous_rpow_const (hq0.trans ha).le).comp
        Real.continuous_sin.abs
    exact
      ((by fun_prop :
          Measurable fun x : ℝ => Real.exp (-x)).div
          hp.measurable).aestronglyMeasurable
  have hbound :
      ∀ᶠ a in 𝓝 α, ∀ᵐ x ∂volume.restrict (Ioi (0 : ℝ)),
        ‖integrand a x‖ ≤ envelope r x := by
    filter_upwards [Ioo_mem_nhds hqα hαr] with a ha
    change q < a ∧ a < r at ha
    filter_upwards with x
    exact integrand_norm_le_envelope
      (hq0.trans ha.1) ha.2 hr0
  have hcont :
      ∀ᵐ x ∂volume.restrict (Ioi (0 : ℝ)),
        ContinuousAt (fun a : ℝ => integrand a x) α := by
    filter_upwards
      [ae_sin_ne_zero.filter_mono
        (ae_mono Measure.restrict_le_self)] with x hx
    have habs : 0 < |Real.sin x| := abs_pos.mpr hx
    have hp :
        ContinuousAt
          (fun a : ℝ => Real.rpow |Real.sin x| a) α :=
      continuousAt_const.rpow continuousAt_id
        (Or.inl habs.ne')
    unfold integrand
    exact continuousAt_const.div hp
      (Real.rpow_pos_of_pos habs α).ne'
  have H :=
    continuousAt_of_dominated
      (μ := volume.restrict (Ioi (0 : ℝ)))
      hmeas hbound henv hcont
  simpa [F] using H.continuousWithinAt

theorem gap8 (α₀ : ℝ) (hα₀pos : 0 < α₀) (hα₀ : α₀ < 1) :
    ContinuousOn F (Set.Ioc (0 : ℝ) α₀) := by
  apply F_continuous_Ioo.mono
  intro α hα
  exact ⟨hα.1, hα.2.trans_lt hα₀⟩

theorem gap9 :
    ContinuousOn F (Set.Ioo 0 1) := by
  exact F_continuous_Ioo

theorem gap10 :
    ContinuousOn F (Set.Ioo 0 1) := by
  exact gap9

end

end ProofGap.Exercise3782
