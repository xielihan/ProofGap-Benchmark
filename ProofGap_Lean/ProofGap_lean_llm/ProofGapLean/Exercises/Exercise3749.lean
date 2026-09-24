import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise3749

noncomputable section

open Filter MeasureTheory Set
open scoped BigOperators Interval Topology

def cubeRootSinSq (x : ℝ) : ℝ :=
  Real.rpow ((Real.sin x) ^ 2) (1 / 3 : ℝ)

def integrand (p x : ℝ) : ℝ :=
  1 / (Real.rpow x p * cubeRootSinSq x)

def partialIntegral (p A : ℝ) : ℝ :=
  ∫ x in Real.pi..A, integrand p x

def Converges (p : ℝ) : Prop :=
  (∀ A : ℝ, Real.pi < A →
    IntervalIntegrable (integrand p) MeasureTheory.volume Real.pi A) ∧
  ∃ L : ℝ, Tendsto (partialIntegral p) atTop (𝓝 L)

def block (p : ℝ) (n : ℕ) : ℝ :=
  ∫ x in (n : ℝ) * Real.pi..((n : ℝ) + 1) * Real.pi,
    integrand p x

def shiftedBlock (p : ℝ) (n : ℕ) : ℝ :=
  ∫ x in (0 : ℝ)..Real.pi,
    1 /
      (Real.rpow (x + (n : ℝ) * Real.pi) p *
        cubeRootSinSq x)

def baseWeight (x : ℝ) : ℝ :=
  1 / cubeRootSinSq x

def weightIntegral : ℝ :=
  ∫ x in (0 : ℝ)..Real.pi, baseWeight x

def pSeriesTerm (p : ℝ) (k : ℕ) : ℝ :=
  1 / Real.rpow ((k + 1 : ℕ) : ℝ) p

def lowerTerm (p : ℝ) (k : ℕ) : ℝ :=
  1 /
    (Real.rpow ((k + 2 : ℕ) : ℝ) p *
      Real.rpow Real.pi p)

def upperTerm (p : ℝ) (k : ℕ) : ℝ :=
  1 /
    (Real.rpow ((k + 1 : ℕ) : ℝ) p *
      Real.rpow Real.pi p)

private def ImproperConverges (p : ℝ) : Prop :=
  ∃ L : ℝ, Tendsto (partialIntegral p) atTop (𝓝 L)

private theorem sin_sq_rpow (x : ℝ) :
    cubeRootSinSq x =
      Real.rpow |Real.sin x| (2 / 3 : ℝ) := by
  unfold cubeRootSinSq
  have hs : 0 ≤ |Real.sin x| := abs_nonneg _
  calc
    Real.rpow (Real.sin x ^ 2) (1 / 3 : ℝ) =
        Real.rpow (|Real.sin x| ^ 2) (1 / 3 : ℝ) := by
      rw [sq_abs]
    _ = Real.rpow |Real.sin x|
          ((2 : ℝ) * (1 / 3 : ℝ)) := by
      rw [← Real.rpow_natCast]
      exact (Real.rpow_mul hs 2 (1 / 3 : ℝ)).symm
    _ = Real.rpow |Real.sin x| (2 / 3 : ℝ) := by
      norm_num

private theorem baseWeight_eq (x : ℝ) :
    baseWeight x =
      Real.rpow |Real.sin x| (-2 / 3 : ℝ) := by
  unfold baseWeight
  rw [sin_sq_rpow, one_div]
  have hneg :
      Real.rpow |Real.sin x| (-(2 / 3 : ℝ)) =
        (Real.rpow |Real.sin x| (2 / 3 : ℝ))⁻¹ :=
    Real.rpow_neg (abs_nonneg _) (2 / 3 : ℝ)
  calc
    (Real.rpow |Real.sin x| (2 / 3 : ℝ))⁻¹ =
        Real.rpow |Real.sin x| (-(2 / 3 : ℝ)) :=
      hneg.symm
    _ = Real.rpow |Real.sin x| (-2 / 3 : ℝ) := by
      congr 2
      ring

private theorem baseWeight_measurable :
    Measurable baseWeight := by
  unfold baseWeight cubeRootSinSq
  exact measurable_const.div
    ((Real.continuous_rpow_const
      (by norm_num : (0 : ℝ) ≤ 1 / 3)).comp
        (Real.continuous_sin.pow 2)).measurable

private theorem baseWeight_left_integrable :
    IntervalIntegrable baseWeight volume 0 (Real.pi / 2) := by
  let q : ℝ := -2 / 3
  let c : ℝ := 2 / Real.pi
  have hq : -1 < q := by
    dsimp [q]
    norm_num
  have hc : 0 < c := by
    dsimp [c]
    positivity
  have hpow :
      IntegrableOn (fun x : ℝ => Real.rpow x q)
        (Ioo (0 : ℝ) (Real.pi / 2)) :=
    (intervalIntegral.integrableOn_Ioo_rpow_iff
      Real.pi_div_two_pos).2 hq
  have hmajor :
      IntegrableOn
        (fun x : ℝ =>
          Real.rpow c q * Real.rpow x q)
        (Ioo (0 : ℝ) (Real.pi / 2)) :=
    hpow.const_mul _
  have hbase :
      IntegrableOn baseWeight
        (Ioo (0 : ℝ) (Real.pi / 2)) := by
    apply hmajor.mono'
      baseWeight_measurable.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    have hsinpos : 0 < Real.sin x :=
      Real.sin_pos_of_pos_of_lt_pi hx.1
        (hx.2.trans (by linarith [Real.pi_pos]))
    have hlinear : c * x ≤ Real.sin x := by
      dsimp [c]
      exact Real.mul_le_sin hx.1.le hx.2.le
    have hrpow :
        Real.rpow (Real.sin x) q ≤
          Real.rpow (c * x) q :=
      Real.rpow_le_rpow_of_nonpos
        (mul_pos hc hx.1) hlinear
        (by dsimp [q]; norm_num)
    rw [Real.norm_eq_abs, baseWeight_eq,
      abs_of_pos hsinpos]
    have habs :
        |Real.rpow (Real.sin x) (-2 / 3 : ℝ)| =
          Real.rpow (Real.sin x) (-2 / 3 : ℝ) :=
      abs_of_nonneg (Real.rpow_nonneg hsinpos.le _)
    rw [habs]
    have hmul :
        Real.rpow (c * x) q =
          Real.rpow c q * Real.rpow x q :=
      Real.mul_rpow hc.le hx.1.le
    rw [hmul] at hrpow
    simpa [q] using hrpow
  rwa [intervalIntegrable_iff_integrableOn_Ioo_of_le
    (by positivity : (0 : ℝ) ≤ Real.pi / 2)]

private theorem baseWeight_pi_sub (x : ℝ) :
    baseWeight (Real.pi - x) = baseWeight x := by
  unfold baseWeight cubeRootSinSq
  rw [Real.sin_pi_sub]

private theorem baseWeight_intervalIntegrable :
    IntervalIntegrable baseWeight volume 0 Real.pi := by
  have hleft := baseWeight_left_integrable
  have hright0 := hleft.comp_sub_left Real.pi
  have hright :
      IntervalIntegrable baseWeight volume
        (Real.pi / 2) Real.pi := by
    convert hright0.symm using 1
    · funext x
      exact (baseWeight_pi_sub x).symm
    · ring
    · ring
  exact hleft.trans hright

private theorem baseWeight_nonneg (x : ℝ) :
    0 ≤ baseWeight x := by
  unfold baseWeight cubeRootSinSq
  exact one_div_nonneg.mpr
    (Real.rpow_nonneg (sq_nonneg _) _)

private theorem baseWeight_periodic_nat (x : ℝ) (k : ℕ) :
    baseWeight (x + (k : ℝ) * Real.pi) =
      baseWeight x := by
  unfold baseWeight cubeRootSinSq
  rw [Real.sin_add_nat_mul_pi]
  congr 2
  rw [mul_pow]
  have hsign : (((-1 : ℝ) ^ k) ^ 2) = 1 := by
    rw [← pow_mul]
    norm_num
  rw [hsign, one_mul]

private theorem baseWeight_periodic :
    Function.Periodic baseWeight Real.pi := by
  intro x
  unfold baseWeight cubeRootSinSq
  rw [Real.sin_add_pi]
  congr 2
  ring

private theorem baseWeight_arbitrary_interval (a b : ℝ) :
    IntervalIntegrable baseWeight volume a b :=
  baseWeight_periodic.intervalIntegrable₀ Real.pi_ne_zero
    baseWeight_intervalIntegrable a b

private theorem measurable_rpow_const (a : ℝ) :
    Measurable (fun x : ℝ => Real.rpow x a) := by
  apply measurable_of_continuousOn_compl_singleton 0
  exact continuousOn_id.rpow_const
    (fun x hx => Or.inl (by simpa using hx))

private theorem integrand_measurable (p : ℝ) :
    Measurable (integrand p) := by
  unfold integrand cubeRootSinSq
  exact measurable_const.div
    ((measurable_rpow_const p).mul
      (((Real.continuous_rpow_const
        (by norm_num : (0 : ℝ) ≤ 1 / 3)).comp
          (Real.continuous_sin.pow 2)).measurable))

private theorem integrand_nonneg (p x : ℝ) (hx : 0 ≤ x) :
    0 ≤ integrand p x := by
  unfold integrand cubeRootSinSq
  exact one_div_nonneg.mpr
    (mul_nonneg (Real.rpow_nonneg hx _)
      (Real.rpow_nonneg (sq_nonneg _) _))

private theorem integrand_factor (p x : ℝ) :
    integrand p x =
      (1 / Real.rpow x p) * baseWeight x := by
  unfold integrand baseWeight
  simp only [one_div, mul_inv_rev]
  ring

private theorem local_intervalIntegrable
    (p b : ℝ) (hb : Real.pi ≤ b) :
    IntervalIntegrable (integrand p) volume Real.pi b := by
  have hbase := baseWeight_arbitrary_interval Real.pi b
  have hcoef :
      ContinuousOn (fun x : ℝ => 1 / Real.rpow x p)
        (Set.uIcc Real.pi b) := by
    intro x hx
    rw [Set.uIcc_of_le hb] at hx
    have hx0 : 0 < x := Real.pi_pos.trans_le hx.1
    exact
      (continuousAt_const.div
        (continuousAt_id.rpow_const (Or.inl hx0.ne'))
        (Real.rpow_pos_of_pos hx0 p).ne').continuousWithinAt
  have hprod := hbase.continuousOn_mul hcoef
  rw [intervalIntegrable_iff] at hprod ⊢
  exact hprod.congr_fun
    (fun x _ => (integrand_factor p x).symm)
    measurableSet_uIoc

private def blockLeft (k : ℕ) : ℝ :=
  ((k + 1 : ℕ) : ℝ) * Real.pi

private def blockRight (k : ℕ) : ℝ :=
  ((k + 2 : ℕ) : ℝ) * Real.pi

private def blockSet (k : ℕ) : Set ℝ :=
  Icc (blockLeft k) (blockRight k)

private def blockCoeff (p : ℝ) (k : ℕ) : ℝ :=
  1 / Real.rpow (blockLeft k) p

private theorem block_bounds (k : ℕ) :
    0 < blockLeft k ∧ blockLeft k < blockRight k := by
  constructor
  · unfold blockLeft
    exact mul_pos (by positivity) Real.pi_pos
  · unfold blockLeft blockRight
    push_cast
    nlinarith [Real.pi_pos]

private theorem shifted_majorant_intervalIntegrable
    (p : ℝ) (k : ℕ) :
    IntervalIntegrable
      (fun x : ℝ =>
        blockCoeff p k *
          baseWeight (x - blockLeft k))
      volume (blockLeft k) (blockRight k) := by
  have hshift :=
    baseWeight_intervalIntegrable.comp_sub_right
      (blockLeft k)
  have hshift' :
      IntervalIntegrable
        (fun x : ℝ => baseWeight (x - blockLeft k))
        volume (blockLeft k) (blockRight k) := by
    convert hshift using 1
    · ring
    · unfold blockRight blockLeft
      push_cast
      ring
  exact hshift'.const_mul _

private theorem integrand_le_shifted_majorant
    (p : ℝ) (hp : 0 < p) (k : ℕ) (x : ℝ)
    (hx : x ∈ blockSet k) :
    integrand p x ≤
      blockCoeff p k *
        baseWeight (x - blockLeft k) := by
  have hbounds := block_bounds k
  have hxleft : blockLeft k ≤ x := hx.1
  have hxpos : 0 < x := hbounds.1.trans_le hxleft
  have hrpow :
      Real.rpow (blockLeft k) p ≤ Real.rpow x p :=
    Real.rpow_le_rpow hbounds.1.le hxleft hp.le
  have hleftpow : 0 < Real.rpow (blockLeft k) p :=
    Real.rpow_pos_of_pos hbounds.1 p
  have hcoef :
      1 / Real.rpow x p ≤
        1 / Real.rpow (blockLeft k) p :=
    one_div_le_one_div_of_le hleftpow hrpow
  have hperiod :
      baseWeight x = baseWeight (x - blockLeft k) := by
    have hrepr :
        x = (x - blockLeft k) +
          (((k + 1 : ℕ) : ℝ) * Real.pi) := by
      unfold blockLeft
      ring
    calc
      baseWeight x =
          baseWeight ((x - blockLeft k) +
            (((k + 1 : ℕ) : ℝ) * Real.pi)) :=
        congrArg baseWeight hrepr
      _ = baseWeight (x - blockLeft k) :=
        baseWeight_periodic_nat (x - blockLeft k) (k + 1)
  rw [integrand_factor, hperiod]
  exact mul_le_mul_of_nonneg_right hcoef
    (baseWeight_nonneg _)

private theorem integrand_block_intervalIntegrable
    (p : ℝ) (hp : 0 < p) (k : ℕ) :
    IntervalIntegrable (integrand p) volume
      (blockLeft k) (blockRight k) := by
  have hmajor := shifted_majorant_intervalIntegrable p k
  apply hmajor.mono_fun
    (integrand_measurable p).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_uIoc] with x hx
  have hxIoc :
      x ∈ Ioc (blockLeft k) (blockRight k) := by
    rwa [uIoc_of_le (block_bounds k).2.le] at hx
  have hx0 : 0 ≤ x :=
    (block_bounds k).1.le.trans hxIoc.1.le
  have hmajorNonneg :
      0 ≤ blockCoeff p k *
        baseWeight (x - blockLeft k) :=
    mul_nonneg
      (one_div_nonneg.mpr
        (Real.rpow_nonneg (block_bounds k).1.le p))
      (baseWeight_nonneg _)
  have hmajorAbs :
      |blockCoeff p k *
        baseWeight (x - blockLeft k)| =
        blockCoeff p k *
          baseWeight (x - blockLeft k) :=
    abs_of_nonneg hmajorNonneg
  rw [Real.norm_eq_abs,
    abs_of_nonneg (integrand_nonneg p x hx0),
    Real.norm_eq_abs, hmajorAbs]
  apply integrand_le_shifted_majorant p hp k x
  exact ⟨hxIoc.1.le, hxIoc.2⟩

private theorem shifted_majorant_integral
    (p : ℝ) (k : ℕ) :
    (∫ x in blockLeft k..blockRight k,
      blockCoeff p k *
        baseWeight (x - blockLeft k)) =
      blockCoeff p k * weightIntegral := by
  rw [intervalIntegral.integral_const_mul]
  rw [intervalIntegral.integral_comp_sub_right]
  unfold weightIntegral
  congr 2
  · ring
  · unfold blockRight blockLeft
    push_cast
    ring

private theorem block_norm_integral_le
    (p : ℝ) (hp : 0 < p) (k : ℕ) :
    (∫ x in blockSet k, ‖integrand p x‖) ≤
      blockCoeff p k * weightIntegral := by
  have hbounds := block_bounds k
  have hint :=
    integrand_block_intervalIntegrable p hp k
  have hmajor :=
    shifted_majorant_intervalIntegrable p k
  have hintSet :
      IntegrableOn (fun x : ℝ => ‖integrand p x‖)
        (blockSet k) volume :=
    ((intervalIntegrable_iff_integrableOn_Icc_of_le
      hbounds.2.le).1 hint).norm
  have hmajorSet :
      IntegrableOn
        (fun x : ℝ => blockCoeff p k *
          baseWeight (x - blockLeft k))
        (blockSet k) volume :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le
      hbounds.2.le).1 hmajor
  calc
    (∫ x in blockSet k, ‖integrand p x‖) ≤
        ∫ x in blockSet k,
          blockCoeff p k *
            baseWeight (x - blockLeft k) := by
      apply setIntegral_mono_on hintSet hmajorSet
        measurableSet_Icc
      intro x hx
      have hx0 : 0 ≤ x := hbounds.1.le.trans hx.1
      rw [Real.norm_eq_abs,
        abs_of_nonneg (integrand_nonneg p x hx0)]
      exact integrand_le_shifted_majorant p hp k x hx
    _ = ∫ x in blockLeft k..blockRight k,
          blockCoeff p k *
            baseWeight (x - blockLeft k) := by
      unfold blockSet
      rw [integral_Icc_eq_integral_Ioc,
        ← intervalIntegral.integral_of_le hbounds.2.le]
    _ = blockCoeff p k * weightIntegral :=
      shifted_majorant_integral p k

private theorem blockCoeff_nonneg (p : ℝ) (k : ℕ) :
    0 ≤ blockCoeff p k := by
  unfold blockCoeff
  exact one_div_nonneg.mpr
    (Real.rpow_nonneg (block_bounds k).1.le p)

private theorem weightIntegral_nonneg :
    0 ≤ weightIntegral := by
  unfold weightIntegral
  exact intervalIntegral.integral_nonneg Real.pi_pos.le
    (fun x _ => baseWeight_nonneg x)

private theorem blockCoeff_summable (p : ℝ) (hp : 1 < p) :
    Summable (blockCoeff p) := by
  have hs0 :
      Summable (fun n : ℕ => Real.rpow (n : ℝ) (-p)) :=
    Real.summable_nat_rpow.2 (by linarith)
  have hs :
      Summable
        (fun k : ℕ =>
          Real.rpow (((k + 1 : ℕ) : ℝ)) (-p)) :=
    (summable_nat_add_iff 1).2 hs0
  have hsMul :=
    hs.mul_left (Real.rpow Real.pi (-p))
  apply hsMul.congr
  intro k
  have hleft : 0 < blockLeft k := (block_bounds k).1
  have hneg :
      Real.rpow (blockLeft k) (-p) =
        (Real.rpow (blockLeft k) p)⁻¹ :=
    Real.rpow_neg hleft.le p
  have hmul :
      Real.rpow
          ((((k + 1 : ℕ) : ℝ)) * Real.pi) (-p) =
        Real.rpow (((k + 1 : ℕ) : ℝ)) (-p) *
          Real.rpow Real.pi (-p) :=
    Real.mul_rpow (by positivity) Real.pi_pos.le
  change
    Real.rpow Real.pi (-p) *
        Real.rpow (((k + 1 : ℕ) : ℝ)) (-p) =
      blockCoeff p k
  unfold blockCoeff
  rw [one_div]
  calc
    Real.rpow Real.pi (-p) *
        Real.rpow (((k + 1 : ℕ) : ℝ)) (-p) =
        Real.rpow
          ((((k + 1 : ℕ) : ℝ)) * Real.pi) (-p) := by
      rw [hmul]
      ring
    _ = Real.rpow (blockLeft k) (-p) := by rfl
    _ = (Real.rpow (blockLeft k) p)⁻¹ := hneg

private theorem block_norm_integrals_summable
    (p : ℝ) (hp : 1 < p) :
    Summable
      (fun k : ℕ =>
        ∫ x in blockSet k, ‖integrand p x‖) := by
  have hmajor :
      Summable
        (fun k : ℕ => blockCoeff p k * weightIntegral) :=
    (blockCoeff_summable p hp).mul_right weightIntegral
  exact Summable.of_nonneg_of_le
    (fun k => integral_nonneg (fun _ => norm_nonneg _))
    (fun k => block_norm_integral_le p
      (zero_lt_one.trans hp) k)
    hmajor

private theorem Ioi_pi_subset_blocks :
    Ioi Real.pi ⊆ ⋃ k : ℕ, blockSet k := by
  intro x hx
  let z : ℝ := x / Real.pi
  have hz : 1 < z := by
    dsimp [z]
    exact (lt_div_iff₀ Real.pi_pos).2
      (by simpa using hx)
  let m : ℕ := ⌊z⌋₊
  have hmle : (m : ℝ) ≤ z := by
    dsimp [m]
    exact Nat.floor_le (zero_le_one.trans hz.le)
  have hzlt : z < (m : ℝ) + 1 := by
    dsimp [m]
    exact Nat.lt_floor_add_one z
  have hm1 : 1 ≤ m := by
    apply Nat.one_le_iff_ne_zero.mpr
    intro hm0
    rw [hm0] at hzlt
    norm_num at hzlt
    linarith
  let k : ℕ := m - 1
  have hk1 : k + 1 = m := by
    dsimp [k]
    omega
  have hk2 : k + 2 = m + 1 := by
    dsimp [k]
    omega
  have hk1r : (k : ℝ) + 1 = (m : ℝ) := by
    exact_mod_cast hk1
  have hk2r : (k : ℝ) + 2 = (m : ℝ) + 1 := by
    exact_mod_cast hk2
  have hzpi : z * Real.pi = x := by
    dsimp [z]
    field_simp [Real.pi_ne_zero]
  apply Set.mem_iUnion.2
  refine ⟨k, ?_⟩
  unfold blockSet blockLeft blockRight
  constructor
  · push_cast
    rw [hk1r]
    calc
      (m : ℝ) * Real.pi ≤ z * Real.pi :=
        mul_le_mul_of_nonneg_right hmle Real.pi_pos.le
      _ = x := hzpi
  · push_cast
    rw [hk2r]
    calc
      x = z * Real.pi := hzpi.symm
      _ ≤ ((m : ℝ) + 1) * Real.pi :=
        mul_le_mul_of_nonneg_right hzlt.le Real.pi_pos.le

private theorem integrableOn_Ioi_of_one_lt
    (p : ℝ) (hp : 1 < p) :
    IntegrableOn (integrand p) (Ioi Real.pi) volume := by
  have hi :
      ∀ k : ℕ,
        IntegrableOn (integrand p) (blockSet k) volume := by
    intro k
    exact
      (intervalIntegrable_iff_integrableOn_Icc_of_le
        (block_bounds k).2.le).1
        (integrand_block_intervalIntegrable p
          (zero_lt_one.trans hp) k)
  have hall :
      IntegrableOn (integrand p)
        (⋃ k : ℕ, blockSet k) volume :=
    integrableOn_iUnion_of_summable_integral_norm hi
      (block_norm_integrals_summable p hp)
  exact hall.mono_set Ioi_pi_subset_blocks

private theorem ae_sin_ne_zero :
    ∀ᵐ x : ℝ ∂volume, Real.sin x ≠ 0 := by
  have hcount :
      {x : ℝ | Real.sin x = 0}.Countable := by
    apply
      (Set.countable_range
        (fun n : ℤ => (n : ℝ) * Real.pi)).mono
    intro x hx
    rcases Real.sin_eq_zero_iff.mp hx with ⟨n, hn⟩
    exact ⟨n, hn⟩
  filter_upwards [hcount.ae_notMem volume] with x hx
  simpa only [Set.mem_setOf_eq, not_false_eq_true] using hx

private theorem one_div_le_integrand
    (p x : ℝ) (hp : p ≤ 1) (hx : Real.pi ≤ x)
    (hsin : Real.sin x ≠ 0) :
    1 / x ≤ integrand p x := by
  have hx1 : 1 ≤ x := by
    linarith [Real.pi_gt_three]
  have hx0 : 0 < x := zero_lt_one.trans_le hx1
  have hxpow :
      Real.rpow x p ≤ x := by
    calc
      Real.rpow x p ≤ Real.rpow x (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hx1 hp
      _ = x := Real.rpow_one x
  have hsinSqPos : 0 < Real.sin x ^ 2 :=
    sq_pos_of_ne_zero hsin
  have hweightPos :
      0 < cubeRootSinSq x :=
    Real.rpow_pos_of_pos hsinSqPos _
  have hweightLe :
      cubeRootSinSq x ≤ 1 := by
    unfold cubeRootSinSq
    calc
      Real.rpow (Real.sin x ^ 2) (1 / 3 : ℝ) ≤
          Real.rpow 1 (1 / 3 : ℝ) :=
        Real.rpow_le_rpow (sq_nonneg _)
          (Real.sin_sq_le_one x) (by norm_num)
      _ = 1 := by simp
  have hxpowPos : 0 < Real.rpow x p :=
    Real.rpow_pos_of_pos hx0 p
  have hdenPos :
      0 < Real.rpow x p * cubeRootSinSq x :=
    mul_pos hxpowPos hweightPos
  have hdenLe :
      Real.rpow x p * cubeRootSinSq x ≤ x := by
    calc
      Real.rpow x p * cubeRootSinSq x ≤
          Real.rpow x p * 1 :=
        mul_le_mul_of_nonneg_left hweightLe hxpowPos.le
      _ ≤ x := by simpa using hxpow
  unfold integrand
  exact one_div_le_one_div_of_le hdenPos hdenLe

private theorem harmonic_lower_bound
    (p b : ℝ) (hp : p ≤ 1) (hb : Real.pi ≤ b) :
    Real.log (b / Real.pi) ≤ partialIntegral p b := by
  have hinv :
      IntervalIntegrable (fun x : ℝ => 1 / x)
        volume Real.pi b := by
    apply ContinuousOn.intervalIntegrable
    intro x hx
    rw [Set.uIcc_of_le hb] at hx
    have hx0 : x ≠ 0 :=
      ne_of_gt (Real.pi_pos.trans_le hx.1)
    exact
      (continuousAt_const.div continuousAt_id hx0).continuousWithinAt
  have hint := local_intervalIntegrable p b hb
  have hmono :=
    intervalIntegral.integral_mono_ae_restrict hb hinv hint
      (by
        have hsin :
            ∀ᵐ x : ℝ
              ∂volume.restrict (Icc Real.pi b),
              Real.sin x ≠ 0 :=
          ae_restrict_of_ae ae_sin_ne_zero
        filter_upwards
          [hsin, ae_restrict_mem measurableSet_Icc] with x hsin hx
        exact one_div_le_integrand p x hp hx.1 hsin)
  rw [integral_one_div_of_pos Real.pi_pos
    (Real.pi_pos.trans_le hb)] at hmono
  exact hmono

private theorem not_improperConverges_of_le_one
    (p : ℝ) (hp : p ≤ 1) :
    ¬ImproperConverges p := by
  rintro ⟨L, hL⟩
  have hup :
      ∀ᶠ b : ℝ in atTop,
        partialIntegral p b < L + 1 :=
    (tendsto_order.1 hL).2 (L + 1) (by linarith)
  have hdiv :
      Tendsto (fun b : ℝ => b / Real.pi)
        atTop atTop := by
    refine tendsto_atTop.2 ?_
    intro c
    filter_upwards
      [eventually_ge_atTop (c * Real.pi)] with b hb
    exact (le_div_iff₀ Real.pi_pos).2
      (by simpa [mul_comm] using hb)
  have hlog :
      Tendsto (fun b : ℝ => Real.log (b / Real.pi))
        atTop atTop :=
    Real.tendsto_log_atTop.comp hdiv
  have hlow :
      ∀ᶠ b : ℝ in atTop,
        L + 1 < Real.log (b / Real.pi) :=
    hlog (eventually_gt_atTop (L + 1))
  rcases
      (hup.and
        (hlow.and (eventually_ge_atTop Real.pi))).exists with
    ⟨b, hbup, hblow, hbpi⟩
  have hcomp := harmonic_lower_bound p b hp hbpi
  linarith

private theorem improperConverges_of_one_lt
    (p : ℝ) (hp : 1 < p) :
    ImproperConverges p := by
  have hint := integrableOn_Ioi_of_one_lt p hp
  exact
    ⟨∫ x : ℝ in Ioi Real.pi, integrand p x,
      by
        unfold partialIntegral
        exact intervalIntegral_tendsto_integral_Ioi
          Real.pi hint tendsto_id⟩

private theorem one_lt_iff_converges (p : ℝ) :
    1 < p ↔ Converges p := by
  constructor
  · intro hp
    constructor
    · intro A hA
      exact local_intervalIntegrable p A hA.le
    · exact improperConverges_of_one_lt p hp
  · intro hconv
    by_contra hp
    exact not_improperConverges_of_le_one p
      (le_of_not_gt hp) hconv.2

theorem gap7 :
    ∃ L : ℝ,
      Tendsto
        (fun A : ℝ =>
          ∫ x in (0 : ℝ)..A, baseWeight x)
        (𝓝[<] Real.pi) (𝓝 L) := by
  have hP :
      ContinuousOn
        (fun A : ℝ =>
          ∫ x in (0 : ℝ)..A, baseWeight x)
        (Icc (0 : ℝ) Real.pi) := by
    simpa only [uIcc_of_le Real.pi_nonneg] using
      intervalIntegral.continuousOn_primitive_interval'
        baseWeight_intervalIntegrable left_mem_uIcc
  have hmem :
      Icc (0 : ℝ) Real.pi ∈
        𝓝[Iio Real.pi] Real.pi := by
    rw [mem_nhdsWithin_iff_exists_mem_nhds_inter]
    refine ⟨Ioi (0 : ℝ), Ioi_mem_nhds Real.pi_pos, ?_⟩
    intro x hx
    exact ⟨hx.1.le, hx.2.le⟩
  have hc :
      ContinuousWithinAt
        (fun A : ℝ =>
          ∫ x in (0 : ℝ)..A, baseWeight x)
        (Iio Real.pi) Real.pi :=
    (hP Real.pi ⟨Real.pi_nonneg, le_rfl⟩)
      |>.mono_of_mem_nhdsWithin hmem
  refine ⟨weightIntegral, ?_⟩
  simpa [weightIntegral] using hc

private lemma pSeriesTerm_eq_rpow (p : ℝ) (k : ℕ) :
    pSeriesTerm p k =
      Real.rpow (((k + 1 : ℕ) : ℝ)) (-p) := by
  unfold pSeriesTerm
  rw [one_div]
  exact
    (Real.rpow_neg
      (by positivity : (0 : ℝ) ≤ ((k + 1 : ℕ) : ℝ)) p).symm

theorem gap8 (p : ℝ) :
    Converges p → Summable (pSeriesTerm p) := by
  intro hconv
  have hp : 1 < p := (one_lt_iff_converges p).2 hconv
  have hs0 :
      Summable (fun n : ℕ => Real.rpow (n : ℝ) (-p)) :=
    Real.summable_nat_rpow.2 (by linarith)
  have hs :
      Summable
        (fun k : ℕ =>
          Real.rpow (((k + 1 : ℕ) : ℝ)) (-p)) :=
    (summable_nat_add_iff 1).2 hs0
  exact hs.congr (fun k => (pSeriesTerm_eq_rpow p k).symm)

theorem gap9 (p : ℝ) (hp : p ≤ 1) :
    ¬ Summable (pSeriesTerm p) := by
  intro hs
  have hshift :
      Summable
        (fun k : ℕ =>
          Real.rpow (((k + 1 : ℕ) : ℝ)) (-p)) :=
    hs.congr (fun k => pSeriesTerm_eq_rpow p k)
  have hbase :
      Summable (fun n : ℕ => Real.rpow (n : ℝ) (-p)) :=
    (summable_nat_add_iff 1).1 hshift
  have hneg : -p < -1 :=
    Real.summable_nat_rpow.1 hbase
  linarith

theorem gap10 (p : ℝ) :
    1 < p ↔ Converges p := by
  exact one_lt_iff_converges p

private lemma block_eq_helper (p : ℝ) (k : ℕ) :
    block p (k + 1) =
      ∫ x in blockLeft k..blockRight k, integrand p x := by
  unfold block blockLeft blockRight
  push_cast
  congr 1 <;> ring

theorem gap2 (p : ℝ) (k : ℕ) :
    block p (k + 1) = shiftedBlock p (k + 1) := by
  have hshift :
      (∫ x in (0 : ℝ)..Real.pi,
          integrand p
            (x + ((k + 1 : ℕ) : ℝ) * Real.pi)) =
        ∫ x in ((k + 1 : ℕ) : ℝ) * Real.pi..
            Real.pi + ((k + 1 : ℕ) : ℝ) * Real.pi,
          integrand p x := by
    simpa only [zero_add] using
      (intervalIntegral.integral_comp_add_right
        (f := integrand p) (a := 0) (b := Real.pi)
          (((k + 1 : ℕ) : ℝ) * Real.pi))
  rw [block_eq_helper]
  have hleft :
      blockLeft k =
        ((k + 1 : ℕ) : ℝ) * Real.pi := rfl
  have hright :
      blockRight k =
        Real.pi + ((k + 1 : ℕ) : ℝ) * Real.pi := by
    unfold blockRight
    push_cast
    ring
  rw [hleft, hright, ← hshift]
  unfold shiftedBlock
  apply intervalIntegral.integral_congr
  intro x hx
  unfold integrand
  have hcube :
      cubeRootSinSq
          (x + ((k + 1 : ℕ) : ℝ) * Real.pi) =
        cubeRootSinSq x := by
    unfold cubeRootSinSq
    rw [Real.sin_add_nat_mul_pi, mul_pow]
    have hsign :
        (((-1 : ℝ) ^ (k + 1)) ^ 2) = 1 := by
      rw [← pow_mul]
      norm_num
    rw [hsign, one_mul]
  change
    1 /
        (Real.rpow
          (x + ((k + 1 : ℕ) : ℝ) * Real.pi) p *
          cubeRootSinSq
            (x + ((k + 1 : ℕ) : ℝ) * Real.pi)) =
      1 /
        (Real.rpow
          (x + ((k + 1 : ℕ) : ℝ) * Real.pi) p *
          cubeRootSinSq x)
  rw [hcube]

private lemma block_nonneg (p : ℝ) (k : ℕ) :
    0 ≤ block p (k + 1) := by
  rw [block_eq_helper]
  apply intervalIntegral.integral_nonneg
    (block_bounds k).2.le
  intro x hx
  exact integrand_nonneg p x
    ((block_bounds k).1.le.trans hx.1)

private lemma sum_blocks_eq_partial
    (p : ℝ) (hp : 0 < p) (n : ℕ) :
    (∑ k ∈ Finset.range n, block p (k + 1)) =
      partialIntegral p (blockLeft n) := by
  induction n with
  | zero =>
      simp [partialIntegral, blockLeft]
  | succ n ih =>
      rw [Finset.sum_range_succ, ih, block_eq_helper]
      have hfirst :
          IntervalIntegrable (integrand p) volume
            Real.pi (blockLeft n) :=
        local_intervalIntegrable p (blockLeft n)
          (by
            unfold blockLeft
            push_cast
            nlinarith [Real.pi_nonneg])
      have hnext :=
        integrand_block_intervalIntegrable p hp n
      have hadd :=
        intervalIntegral.integral_add_adjacent_intervals
          hfirst hnext
      unfold partialIntegral
      rw [hadd]
      congr 1

theorem gap1 (p : ℝ) :
    Converges p →
      ∃ L : ℝ,
        Tendsto (partialIntegral p) atTop (𝓝 L) ∧
        HasSum (fun k : ℕ => block p (k + 1)) L := by
  intro hconv
  rcases hconv.2 with ⟨L, hL⟩
  have hp : 1 < p := (one_lt_iff_converges p).2 hconv
  have hblocks :
      Tendsto (fun n : ℕ => blockLeft n) atTop atTop := by
    have hplus :
        Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
      tendsto_atTop_add_const_right atTop 1
        tendsto_natCast_atTop_atTop
    have hmul := hplus.atTop_mul_const Real.pi_pos
    simpa [blockLeft, Nat.cast_add, Nat.cast_one] using hmul
  have hseq :
      Tendsto
        (fun n : ℕ =>
          ∑ k ∈ Finset.range n, block p (k + 1))
        atTop (𝓝 L) := by
    have hc := hL.comp hblocks
    apply hc.congr'
    filter_upwards with n
    exact (sum_blocks_eq_partial p
      (zero_lt_one.trans hp) n).symm
  have hsum :
      HasSum (fun k : ℕ => block p (k + 1)) L :=
    (hasSum_iff_tendsto_nat_of_nonneg
      (fun k => block_nonneg p k) L).2 hseq
  exact ⟨L, hL, hsum⟩

theorem gap3 (p : ℝ) :
    Converges p →
      ∃ L : ℝ,
        Tendsto (partialIntegral p) atTop (𝓝 L) ∧
        HasSum (fun k : ℕ => shiftedBlock p (k + 1)) L := by
  intro hconv
  rcases gap1 p hconv with ⟨L, hL, hsum⟩
  refine ⟨L, hL, ?_⟩
  exact HasSum.congr_fun hsum (fun k => (gap2 p k).symm)

private lemma lowerTerm_eq_blockCoeff (p : ℝ) (k : ℕ) :
    lowerTerm p k =
      1 / Real.rpow (blockRight k) p := by
  unfold lowerTerm blockRight
  exact congrArg (fun z : ℝ => 1 / z)
    (Real.mul_rpow
      (by positivity : (0 : ℝ) ≤ ((k + 2 : ℕ) : ℝ))
      Real.pi_nonneg).symm

private lemma upperTerm_eq_blockCoeff (p : ℝ) (k : ℕ) :
    upperTerm p k = blockCoeff p k := by
  unfold upperTerm blockCoeff blockLeft
  exact congrArg (fun z : ℝ => 1 / z)
    (Real.mul_rpow
      (by positivity : (0 : ℝ) ≤ ((k + 1 : ℕ) : ℝ))
      Real.pi_nonneg).symm

private def shiftKernel (p : ℝ) (k : ℕ) (x : ℝ) : ℝ :=
  1 /
    (Real.rpow (x + blockLeft k) p *
      cubeRootSinSq x)

private lemma shiftedBlock_eq_kernel (p : ℝ) (k : ℕ) :
    shiftedBlock p (k + 1) =
      ∫ x in (0 : ℝ)..Real.pi, shiftKernel p k x := by
  rfl

private lemma shiftKernel_factor (p : ℝ) (k : ℕ) (x : ℝ) :
    shiftKernel p k x =
      (1 / Real.rpow (x + blockLeft k) p) *
        baseWeight x := by
  unfold shiftKernel baseWeight
  simp only [one_div, mul_inv_rev]
  ring

private lemma shiftKernel_intervalIntegrable
    (p : ℝ) (k : ℕ) :
    IntervalIntegrable (shiftKernel p k) volume
      0 Real.pi := by
  have hcoef :
      ContinuousOn
        (fun x : ℝ =>
          1 / Real.rpow (x + blockLeft k) p)
        (uIcc (0 : ℝ) Real.pi) := by
    intro x hx
    rw [uIcc_of_le Real.pi_nonneg] at hx
    have hxpos : 0 < x + blockLeft k :=
      (block_bounds k).1.trans_le
        (by linarith [hx.1])
    exact
      (continuousAt_const.div
        ((continuousAt_id.add continuousAt_const).rpow_const
          (Or.inl hxpos.ne'))
        (Real.rpow_pos_of_pos hxpos p).ne').continuousWithinAt
  have hprod :=
    baseWeight_intervalIntegrable.continuousOn_mul hcoef
  apply hprod.congr
  intro x hx
  rw [shiftKernel_factor]

private lemma baseWeight_pos_Ioo {x : ℝ}
    (hx : x ∈ Ioo (0 : ℝ) Real.pi) :
    0 < baseWeight x := by
  have hs : 0 < Real.sin x :=
    Real.sin_pos_of_pos_of_lt_pi hx.1 hx.2
  unfold baseWeight cubeRootSinSq
  exact one_div_pos.mpr
    (Real.rpow_pos_of_pos (sq_pos_of_pos hs) _)

private lemma lower_coefficient_lt
    {p x : ℝ} (hp : 0 < p) (k : ℕ)
    (hx : x ∈ Ioo (0 : ℝ) Real.pi) :
    lowerTerm p k <
      1 / Real.rpow (x + blockLeft k) p := by
  rw [lowerTerm_eq_blockCoeff]
  have hmid0 : 0 < x + blockLeft k :=
    add_pos hx.1 (block_bounds k).1
  have hbase : x + blockLeft k < blockRight k := by
    unfold blockLeft blockRight
    push_cast
    ring_nf
    linarith [hx.2]
  have hpow :
      Real.rpow (x + blockLeft k) p <
        Real.rpow (blockRight k) p :=
    Real.rpow_lt_rpow hmid0.le hbase hp
  exact one_div_lt_one_div_of_lt
    (Real.rpow_pos_of_pos hmid0 p) hpow

private lemma upper_coefficient_gt
    {p x : ℝ} (hp : 0 < p) (k : ℕ)
    (hx : x ∈ Ioo (0 : ℝ) Real.pi) :
    1 / Real.rpow (x + blockLeft k) p <
      upperTerm p k := by
  rw [upperTerm_eq_blockCoeff]
  unfold blockCoeff
  have hleft0 : 0 < blockLeft k := (block_bounds k).1
  have hbase : blockLeft k < x + blockLeft k := by
    linarith [hx.1]
  have hpow :
      Real.rpow (blockLeft k) p <
        Real.rpow (x + blockLeft k) p :=
    Real.rpow_lt_rpow hleft0.le hbase hp
  exact one_div_lt_one_div_of_lt
    (Real.rpow_pos_of_pos hleft0 p) hpow

private lemma scaled_lower_lt_shifted
    (p : ℝ) (hp : 0 < p) (k : ℕ) :
    weightIntegral * lowerTerm p k <
      shiftedBlock p (k + 1) := by
  have hshift := shiftKernel_intervalIntegrable p k
  have hlow :
      IntervalIntegrable
        (fun x : ℝ => lowerTerm p k * baseWeight x)
        volume 0 Real.pi :=
    baseWeight_intervalIntegrable.const_mul _
  have hdiff :
      IntervalIntegrable
        (fun x : ℝ =>
          shiftKernel p k x -
            lowerTerm p k * baseWeight x)
        volume 0 Real.pi :=
    hshift.sub hlow
  have hpos :
      0 < ∫ x in (0 : ℝ)..Real.pi,
        shiftKernel p k x -
          lowerTerm p k * baseWeight x := by
    apply intervalIntegral.intervalIntegral_pos_of_pos_on hdiff
    · intro x hx
      rw [shiftKernel_factor]
      exact sub_pos.mpr
        (mul_lt_mul_of_pos_right
          (lower_coefficient_lt hp k hx)
          (baseWeight_pos_Ioo hx))
    · exact Real.pi_pos
  rw [intervalIntegral.integral_sub hshift hlow,
    intervalIntegral.integral_const_mul] at hpos
  rw [shiftedBlock_eq_kernel]
  unfold weightIntegral
  nlinarith

private lemma shifted_lt_scaled_upper
    (p : ℝ) (hp : 0 < p) (k : ℕ) :
    shiftedBlock p (k + 1) <
      weightIntegral * upperTerm p k := by
  have hshift := shiftKernel_intervalIntegrable p k
  have hupp :
      IntervalIntegrable
        (fun x : ℝ => upperTerm p k * baseWeight x)
        volume 0 Real.pi :=
    baseWeight_intervalIntegrable.const_mul _
  have hdiff :
      IntervalIntegrable
        (fun x : ℝ =>
          upperTerm p k * baseWeight x -
            shiftKernel p k x)
        volume 0 Real.pi :=
    hupp.sub hshift
  have hpos :
      0 < ∫ x in (0 : ℝ)..Real.pi,
        upperTerm p k * baseWeight x -
          shiftKernel p k x := by
    apply intervalIntegral.intervalIntegral_pos_of_pos_on hdiff
    · intro x hx
      rw [shiftKernel_factor]
      exact sub_pos.mpr
        (mul_lt_mul_of_pos_right
          (upper_coefficient_gt hp k hx)
          (baseWeight_pos_Ioo hx))
    · exact Real.pi_pos
  rw [intervalIntegral.integral_sub hupp hshift,
    intervalIntegral.integral_const_mul] at hpos
  rw [shiftedBlock_eq_kernel]
  unfold weightIntegral
  nlinarith

private lemma lowerTerm_eq_blockCoeff_succ (p : ℝ) (k : ℕ) :
    lowerTerm p k = blockCoeff p (k + 1) := by
  rw [lowerTerm_eq_blockCoeff]
  congr 2

private lemma lowerTerm_summable (p : ℝ) (hp : 1 < p) :
    Summable (lowerTerm p) := by
  have hs :
      Summable (fun k : ℕ => blockCoeff p (k + 1)) :=
    (summable_nat_add_iff 1).2 (blockCoeff_summable p hp)
  exact hs.congr
    (fun k => (lowerTerm_eq_blockCoeff_succ p k).symm)

private lemma upperTerm_summable (p : ℝ) (hp : 1 < p) :
    Summable (upperTerm p) := by
  exact (blockCoeff_summable p hp).congr
    (fun k => (upperTerm_eq_blockCoeff p k).symm)

private lemma lowerTerm_nonneg (p : ℝ) (k : ℕ) :
    0 ≤ lowerTerm p k := by
  unfold lowerTerm
  exact one_div_nonneg.mpr
    (mul_nonneg
      (Real.rpow_nonneg (by positivity) p)
      (Real.rpow_nonneg Real.pi_nonneg p))

private lemma upperTerm_nonneg (p : ℝ) (k : ℕ) :
    0 ≤ upperTerm p k := by
  unfold upperTerm
  exact one_div_nonneg.mpr
    (mul_nonneg
      (Real.rpow_nonneg (by positivity) p)
      (Real.rpow_nonneg Real.pi_nonneg p))

private lemma shiftedBlock_nonneg (p : ℝ) (k : ℕ) :
    0 ≤ shiftedBlock p (k + 1) := by
  rw [← gap2 p k]
  exact block_nonneg p k

private lemma shiftedBlock_summable (p : ℝ) (hp : 1 < p) :
    Summable (fun k : ℕ => shiftedBlock p (k + 1)) := by
  have hconv : Converges p :=
    (one_lt_iff_converges p).1 hp
  rcases gap3 p hconv with ⟨L, hL, hsum⟩
  exact hsum.summable

theorem gap4 (p : ℝ) (hp : 1 < p) :
    weightIntegral * ∑' k : ℕ, lowerTerm p k <
      ∑' k : ℕ, shiftedBlock p (k + 1) := by
  have hraw :
      (∑' k : ℕ, weightIntegral * lowerTerm p k) <
        ∑' k : ℕ, shiftedBlock p (k + 1) :=
    Summable.tsum_lt_tsum_of_nonneg
      (fun k =>
        mul_nonneg weightIntegral_nonneg
          (lowerTerm_nonneg p k))
      (fun k => (scaled_lower_lt_shifted p
        (zero_lt_one.trans hp) k).le)
      (scaled_lower_lt_shifted p
        (zero_lt_one.trans hp) 0)
      (shiftedBlock_summable p hp)
  rw [tsum_mul_left] at hraw
  exact hraw

theorem gap5 (p : ℝ) (hp : 1 < p) :
    ∑' k : ℕ, shiftedBlock p (k + 1) <
      weightIntegral * ∑' k : ℕ, upperTerm p k := by
  have hscaled :
      Summable
        (fun k : ℕ => weightIntegral * upperTerm p k) :=
    (upperTerm_summable p hp).mul_left weightIntegral
  have hraw :
      (∑' k : ℕ, shiftedBlock p (k + 1)) <
        ∑' k : ℕ, weightIntegral * upperTerm p k :=
    Summable.tsum_lt_tsum_of_nonneg
      (fun k => shiftedBlock_nonneg p k)
      (fun k => (shifted_lt_scaled_upper p
        (zero_lt_one.trans hp) k).le)
      (shifted_lt_scaled_upper p
        (zero_lt_one.trans hp) 0)
      hscaled
  rw [tsum_mul_left] at hraw
  exact hraw

theorem gap6 (p : ℝ) (hp : 1 < p) :
    weightIntegral * ∑' k : ℕ, lowerTerm p k <
      weightIntegral * ∑' k : ℕ, upperTerm p k := by
  exact (gap4 p hp).trans (gap5 p hp)

end

end ProofGap.Exercise3749
