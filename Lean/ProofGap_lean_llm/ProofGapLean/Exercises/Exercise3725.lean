import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise3725

noncomputable section

open Filter
open scoped Interval Topology

def radicand (k φ : ℝ) : ℝ :=
  1 - k ^ 2 * Real.sin φ ^ 2

def ellipticE (k : ℝ) : ℝ :=
  ∫ φ in (0 : ℝ)..Real.pi / 2, Real.sqrt (radicand k φ)

def ellipticK (k : ℝ) : ℝ :=
  ∫ φ in (0 : ℝ)..Real.pi / 2, 1 / Real.sqrt (radicand k φ)

def rewrittenEDerivative (k : ℝ) : ℝ :=
  (1 / k) *
    ∫ φ in (0 : ℝ)..Real.pi / 2,
      (radicand k φ - 1) / Real.sqrt (radicand k φ)

private lemma radicand_pos {k : ℝ} (hk0 : 0 ≤ k) (hk1 : k < 1) (φ : ℝ) :
    0 < radicand k φ := by
  have hs0 : 0 ≤ Real.sin φ ^ 2 := sq_nonneg _
  have hs1 : Real.sin φ ^ 2 ≤ 1 := Real.sin_sq_le_one φ
  have hk2 : k ^ 2 < 1 := by nlinarith
  have hmul : k ^ 2 * Real.sin φ ^ 2 ≤ k ^ 2 :=
    mul_le_of_le_one_right (sq_nonneg k) hs1
  unfold radicand
  linarith

private lemma hasDerivAt_sqrt_radicand {k : ℝ} (hk0 : 0 ≤ k) (hk1 : k < 1)
    (φ : ℝ) :
    HasDerivAt
      (fun t => Real.sqrt (radicand t φ))
      (-(k * Real.sin φ ^ 2 / Real.sqrt (radicand k φ))) k := by
  have hrad :
      HasDerivAt (fun t => radicand t φ) (-2 * k * Real.sin φ ^ 2) k := by
    unfold radicand
    convert (hasDerivAt_const k 1).sub
      (((hasDerivAt_id k).pow 2).mul_const (Real.sin φ ^ 2)) using 1 <;>
        simp [id] <;> ring
  have hpos := radicand_pos hk0 hk1 φ
  convert hrad.sqrt hpos.ne' using 1 <;> field_simp <;> ring

private lemma continuous_sqrt_radicand (k : ℝ) :
    Continuous (fun φ => Real.sqrt (radicand k φ)) := by
  unfold radicand
  fun_prop

private lemma continuous_radicand (k : ℝ) :
    Continuous (fun φ => radicand k φ) := by
  unfold radicand
  fun_prop

private lemma continuous_EDeriv {k : ℝ} (hk0 : 0 ≤ k) (hk1 : k < 1) :
    Continuous
      (fun φ =>
        -(k * Real.sin φ ^ 2 / Real.sqrt (radicand k φ))) := by
  apply Continuous.neg
  apply Continuous.div
  · fun_prop
  · exact continuous_sqrt_radicand k
  · intro φ
    exact (Real.sqrt_pos.2 (radicand_pos hk0 hk1 φ)).ne'

private lemma continuous_KIntegrand {k : ℝ} (hk0 : 0 ≤ k) (hk1 : k < 1) :
    Continuous (fun φ => 1 / Real.sqrt (radicand k φ)) := by
  apply Continuous.div continuous_const (continuous_sqrt_radicand k)
  intro φ
  exact (Real.sqrt_pos.2 (radicand_pos hk0 hk1 φ)).ne'

private lemma hasDerivAt_inv_sqrt_radicand {k : ℝ} (hk0 : 0 ≤ k) (hk1 : k < 1)
    (φ : ℝ) :
    HasDerivAt
      (fun t => 1 / Real.sqrt (radicand t φ))
      (k * Real.sin φ ^ 2 /
        (radicand k φ * Real.sqrt (radicand k φ))) k := by
  have hsqrt := hasDerivAt_sqrt_radicand hk0 hk1 φ
  have hpos := radicand_pos hk0 hk1 φ
  have hsqrt0 : Real.sqrt (radicand k φ) ≠ 0 :=
    (Real.sqrt_pos.2 hpos).ne'
  convert (hasDerivAt_const k 1).div hsqrt hsqrt0 using 1
  simp only [zero_mul, one_mul, zero_sub, neg_neg]
  field_simp [hsqrt0]
  rw [Real.sq_sqrt hpos.le]

private lemma continuous_KDeriv {k : ℝ} (hk0 : 0 ≤ k) (hk1 : k < 1) :
    Continuous
      (fun φ =>
        k * Real.sin φ ^ 2 /
          (radicand k φ * Real.sqrt (radicand k φ))) := by
  apply Continuous.div
  · fun_prop
  · exact (continuous_radicand k).mul (continuous_sqrt_radicand k)
  · intro φ
    exact mul_ne_zero (radicand_pos hk0 hk1 φ).ne'
      (Real.sqrt_pos.2 (radicand_pos hk0 hk1 φ)).ne'

private lemma ellipticE_hasDerivAt (k : ℝ) (hk0 : 0 < k) (hk1 : k < 1) :
    HasDerivAt ellipticE
      (∫ φ in (0 : ℝ)..Real.pi / 2,
        -(k * Real.sin φ ^ 2 / Real.sqrt (radicand k φ))) k := by
  let r : ℝ := (k + 1) / 2
  let c : ℝ := 1 - r ^ 2
  let s : Set ℝ := Set.Icc 0 r
  let bound : ℝ → ℝ := fun _ => r / Real.sqrt c
  have hkr : k < r := by
    dsimp [r]
    linarith
  have hr1 : r < 1 := by
    dsimp [r]
    linarith
  have hr0 : 0 < r := hk0.trans hkr
  have hc : 0 < c := by
    dsimp [c]
    nlinarith
  have hs : s ∈ 𝓝 k := by
    apply Icc_mem_nhds
    · simpa [s] using hk0
    · simpa [s] using hkr
  have hbound (t φ : ℝ) (ht : t ∈ s) :
      ‖-(t * Real.sin φ ^ 2 / Real.sqrt (radicand t φ))‖ ≤ bound φ := by
    have ht0 : 0 ≤ t := ht.1
    have htr : t ≤ r := ht.2
    have hs0 : 0 ≤ Real.sin φ ^ 2 := sq_nonneg _
    have hs1 : Real.sin φ ^ 2 ≤ 1 := Real.sin_sq_le_one φ
    have hnum : t * Real.sin φ ^ 2 ≤ r := by
      calc
        t * Real.sin φ ^ 2 ≤ t := mul_le_of_le_one_right ht0 hs1
        _ ≤ r := htr
    have hrad :
        c ≤ radicand t φ := by
      have ht2 : t ^ 2 ≤ r ^ 2 := by nlinarith
      have hmul : t ^ 2 * Real.sin φ ^ 2 ≤ r ^ 2 := by
        calc
          t ^ 2 * Real.sin φ ^ 2 ≤ t ^ 2 :=
            mul_le_of_le_one_right (sq_nonneg t) hs1
          _ ≤ r ^ 2 := ht2
      dsimp [c]
      unfold radicand
      linarith
    have hsqrt :
        Real.sqrt c ≤ Real.sqrt (radicand t φ) :=
      Real.sqrt_le_sqrt hrad
    have hsqrtc : 0 < Real.sqrt c := Real.sqrt_pos.2 hc
    have htpos : 0 < radicand t φ :=
      lt_of_lt_of_le hc hrad
    rw [Real.norm_eq_abs, abs_neg, abs_div, abs_mul,
      abs_of_nonneg ht0, abs_of_nonneg hs0,
      abs_of_pos (Real.sqrt_pos.2 htpos)]
    dsimp [bound]
    exact div_le_div₀ hr0.le hnum hsqrtc hsqrt
  have hmain :
      HasDerivAt ellipticE
        (∫ φ in (0 : ℝ)..Real.pi / 2,
          -(k * Real.sin φ ^ 2 / Real.sqrt (radicand k φ))) k := by
    unfold ellipticE
    refine (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (F := fun t φ => Real.sqrt (radicand t φ))
      (F' := fun t φ =>
        -(t * Real.sin φ ^ 2 / Real.sqrt (radicand t φ)))
      (a := (0 : ℝ)) (b := Real.pi / 2)
      (s := s) (bound := bound) hs ?_ ?_ ?_ ?_ ?_ ?_).2
    · filter_upwards [] with t
      exact (continuous_sqrt_radicand t).aestronglyMeasurable
    · exact (continuous_sqrt_radicand k).intervalIntegrable _ _
    · exact (continuous_EDeriv hk0.le hk1).aestronglyMeasurable
    · filter_upwards [] with φ hφ t ht
      exact hbound t φ ht
    · exact continuous_const.intervalIntegrable _ _
    · filter_upwards [] with φ hφ t ht
      exact hasDerivAt_sqrt_radicand ht.1 (ht.2.trans_lt hr1) φ
  exact hmain

theorem gap1 (k : ℝ) (hk0 : 0 < k) (hk1 : k < 1) :
    deriv ellipticE k =
      -(∫ φ in (0 : ℝ)..Real.pi / 2,
          k * Real.sin φ ^ 2 / Real.sqrt (radicand k φ)) := by
  rw [(ellipticE_hasDerivAt k hk0 hk1).deriv,
    ← intervalIntegral.integral_neg]

theorem gap2 (k : ℝ) (hk0 : 0 < k) (hk1 : k < 1) :
    deriv ellipticE k = rewrittenEDerivative k := by
  rw [gap1 k hk0 hk1]
  unfold rewrittenEDerivative
  rw [← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_neg]
  apply intervalIntegral.integral_congr
  intro φ hφ
  unfold radicand
  field_simp [hk0.ne']
  ring

theorem gap3 (k : ℝ) (hk0 : 0 < k) (hk1 : k < 1) :
    rewrittenEDerivative k = (ellipticE k - ellipticK k) / k := by
  have hEint :
      IntervalIntegrable (fun φ => Real.sqrt (radicand k φ))
        MeasureTheory.volume 0 (Real.pi / 2) :=
    (continuous_sqrt_radicand k).intervalIntegrable _ _
  have hKint :
      IntervalIntegrable (fun φ => 1 / Real.sqrt (radicand k φ))
        MeasureTheory.volume 0 (Real.pi / 2) :=
    (continuous_KIntegrand hk0.le hk1).intervalIntegrable _ _
  have hint :
      (∫ φ in (0 : ℝ)..Real.pi / 2,
          (radicand k φ - 1) / Real.sqrt (radicand k φ)) =
        ∫ φ in (0 : ℝ)..Real.pi / 2,
          (Real.sqrt (radicand k φ) -
            1 / Real.sqrt (radicand k φ)) := by
    apply intervalIntegral.integral_congr
    intro φ hφ
    have hpos := radicand_pos hk0.le hk1 φ
    have hsqrt : Real.sqrt (radicand k φ) ≠ 0 :=
      (Real.sqrt_pos.2 hpos).ne'
    dsimp
    field_simp [hsqrt]
    nlinarith [Real.sq_sqrt hpos.le]
  unfold rewrittenEDerivative ellipticE ellipticK
  rw [hint]
  rw [← intervalIntegral.integral_sub hEint hKint]
  ring

theorem gap4 (k : ℝ) (hk0 : 0 < k) (hk1 : k < 1) :
    deriv ellipticE k = (ellipticE k - ellipticK k) / k := by
  exact (gap2 k hk0 hk1).trans (gap3 k hk0 hk1)

private lemma ellipticK_hasDerivAt (k : ℝ) (hk0 : 0 < k) (hk1 : k < 1) :
    HasDerivAt ellipticK
      (∫ φ in (0 : ℝ)..Real.pi / 2,
        k * Real.sin φ ^ 2 /
          (radicand k φ * Real.sqrt (radicand k φ))) k := by
  let r : ℝ := (k + 1) / 2
  let c : ℝ := 1 - r ^ 2
  let s : Set ℝ := Set.Icc 0 r
  let bound : ℝ → ℝ :=
    fun _ => r / (c * Real.sqrt c)
  have hkr : k < r := by
    dsimp [r]
    linarith
  have hr1 : r < 1 := by
    dsimp [r]
    linarith
  have hr0 : 0 < r := hk0.trans hkr
  have hc : 0 < c := by
    dsimp [c]
    nlinarith
  have hs : s ∈ 𝓝 k := by
    apply Icc_mem_nhds
    · simpa [s] using hk0
    · simpa [s] using hkr
  have hbound (t φ : ℝ) (ht : t ∈ s) :
      ‖t * Real.sin φ ^ 2 /
          (radicand t φ * Real.sqrt (radicand t φ))‖ ≤ bound φ := by
    have ht0 : 0 ≤ t := ht.1
    have htr : t ≤ r := ht.2
    have hs0 : 0 ≤ Real.sin φ ^ 2 := sq_nonneg _
    have hs1 : Real.sin φ ^ 2 ≤ 1 := Real.sin_sq_le_one φ
    have hnum : t * Real.sin φ ^ 2 ≤ r := by
      calc
        t * Real.sin φ ^ 2 ≤ t := mul_le_of_le_one_right ht0 hs1
        _ ≤ r := htr
    have hrad :
        c ≤ radicand t φ := by
      have ht2 : t ^ 2 ≤ r ^ 2 := by nlinarith
      have hmul : t ^ 2 * Real.sin φ ^ 2 ≤ r ^ 2 := by
        calc
          t ^ 2 * Real.sin φ ^ 2 ≤ t ^ 2 :=
            mul_le_of_le_one_right (sq_nonneg t) hs1
          _ ≤ r ^ 2 := ht2
      dsimp [c]
      unfold radicand
      linarith
    have hsqrt :
        Real.sqrt c ≤ Real.sqrt (radicand t φ) :=
      Real.sqrt_le_sqrt hrad
    have hsqrtc : 0 < Real.sqrt c := Real.sqrt_pos.2 hc
    have htpos : 0 < radicand t φ := lt_of_lt_of_le hc hrad
    have hden :
        c * Real.sqrt c ≤
          radicand t φ * Real.sqrt (radicand t φ) :=
      mul_le_mul hrad hsqrt (Real.sqrt_nonneg _) htpos.le
    rw [Real.norm_eq_abs, abs_div, abs_mul, abs_mul,
      abs_of_nonneg ht0, abs_of_nonneg hs0,
      abs_of_pos htpos, abs_of_pos (Real.sqrt_pos.2 htpos)]
    dsimp [bound]
    exact div_le_div₀ hr0.le hnum (mul_pos hc hsqrtc) hden
  have hmain :
      HasDerivAt ellipticK
        (∫ φ in (0 : ℝ)..Real.pi / 2,
          k * Real.sin φ ^ 2 /
            (radicand k φ * Real.sqrt (radicand k φ))) k := by
    unfold ellipticK
    refine (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (F := fun t φ => 1 / Real.sqrt (radicand t φ))
      (F' := fun t φ =>
        t * Real.sin φ ^ 2 /
          (radicand t φ * Real.sqrt (radicand t φ)))
      (a := (0 : ℝ)) (b := Real.pi / 2)
      (s := s) (bound := bound) hs ?_ ?_ ?_ ?_ ?_ ?_).2
    · filter_upwards [hs] with t ht
      exact (continuous_KIntegrand ht.1 (ht.2.trans_lt hr1)).aestronglyMeasurable
    · exact (continuous_KIntegrand hk0.le hk1).intervalIntegrable _ _
    · exact (continuous_KDeriv hk0.le hk1).aestronglyMeasurable
    · filter_upwards [] with φ hφ t ht
      exact hbound t φ ht
    · exact continuous_const.intervalIntegrable _ _
    · filter_upwards [] with φ hφ t ht
      exact hasDerivAt_inv_sqrt_radicand ht.1 (ht.2.trans_lt hr1) φ
  exact hmain

theorem gap5 (k : ℝ) (hk0 : 0 < k) (hk1 : k < 1) :
    deriv ellipticK k =
      ∫ φ in (0 : ℝ)..Real.pi / 2,
        k * Real.sin φ ^ 2 /
          (radicand k φ * Real.sqrt (radicand k φ)) := by
  exact (ellipticK_hasDerivAt k hk0 hk1).deriv

theorem gap6 (k : ℝ) (hk0 : 0 < k) (hk1 : k < 1) :
    deriv ellipticK k =
      -(ellipticK k / k) +
        ellipticE k / (k * (1 - k ^ 2)) := by
  let q : ℝ → ℝ := fun φ =>
    Real.sin φ * Real.cos φ / Real.sqrt (radicand k φ)
  let q' : ℝ → ℝ := fun φ =>
    (Real.cos φ ^ 2 - Real.sin φ ^ 2) /
        Real.sqrt (radicand k φ) +
      k ^ 2 * Real.sin φ ^ 2 * Real.cos φ ^ 2 /
        (radicand k φ * Real.sqrt (radicand k φ))
  have hq (φ : ℝ) : HasDerivAt q (q' φ) φ := by
    have hpos := radicand_pos hk0.le hk1 φ
    have hrad :
        HasDerivAt (fun x => radicand k x)
          (-2 * k ^ 2 * Real.sin φ * Real.cos φ) φ := by
      unfold radicand
      convert (hasDerivAt_const φ 1).sub
        ((Real.hasDerivAt_sin φ).pow 2 |>.const_mul (k ^ 2)) using 1 <;>
          simp [id] <;> ring
    have hsqrt := hrad.sqrt hpos.ne'
    have hsqrt0 : Real.sqrt (radicand k φ) ≠ 0 :=
      (Real.sqrt_pos.2 hpos).ne'
    have hinv :
        HasDerivAt
          (fun x => 1 / Real.sqrt (radicand k x))
          (k ^ 2 * Real.sin φ * Real.cos φ /
            (radicand k φ * Real.sqrt (radicand k φ))) φ := by
      convert (hasDerivAt_const φ 1).div hsqrt hsqrt0 using 1
      simp only [zero_mul, one_mul, zero_sub]
      field_simp [hsqrt0]
      rw [Real.sq_sqrt hpos.le]
    have htrig :
        HasDerivAt
          (fun x => Real.sin x * Real.cos x)
          (Real.cos φ ^ 2 - Real.sin φ ^ 2) φ := by
      convert (Real.hasDerivAt_sin φ).mul (Real.hasDerivAt_cos φ) using 1 <;>
        ring
    dsimp [q, q']
    convert htrig.mul hinv using 1
    · funext x
      simp [div_eq_mul_inv]
    · field_simp [hsqrt0, hpos.ne']
  have hq'cont : Continuous q' := by
    apply Continuous.add
    · apply Continuous.div
      · fun_prop
      · exact continuous_sqrt_radicand k
      · intro φ
        exact (Real.sqrt_pos.2 (radicand_pos hk0.le hk1 φ)).ne'
    · apply Continuous.div
      · fun_prop
      · exact (continuous_radicand k).mul (continuous_sqrt_radicand k)
      · intro φ
        exact mul_ne_zero (radicand_pos hk0.le hk1 φ).ne'
          (Real.sqrt_pos.2 (radicand_pos hk0.le hk1 φ)).ne'
  have hqint :
      (∫ φ in (0 : ℝ)..Real.pi / 2, q' φ) = 0 := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun φ hφ => hq φ) (hq'cont.intervalIntegrable _ _)]
    dsimp [q]
    rw [Real.sin_zero, Real.sin_pi_div_two, Real.cos_zero,
      Real.cos_pi_div_two]
    norm_num
  have hpoint (φ : ℝ) :
      k * Real.sin φ ^ 2 /
          (radicand k φ * Real.sqrt (radicand k φ)) =
        -(1 / Real.sqrt (radicand k φ) / k) +
          Real.sqrt (radicand k φ) / (k * (1 - k ^ 2)) -
          k / (1 - k ^ 2) * q' φ := by
    have hpos := radicand_pos hk0.le hk1 φ
    have hsqrt0 : Real.sqrt (radicand k φ) ≠ 0 :=
      (Real.sqrt_pos.2 hpos).ne'
    have hkden : 1 - k ^ 2 ≠ 0 := by nlinarith
    have htrig := Real.sin_sq_add_cos_sq φ
    dsimp [q']
    field_simp [hk0.ne', hkden, hpos.ne', hsqrt0]
    rw [Real.sq_sqrt hpos.le]
    unfold radicand
    nlinarith
  let A : ℝ → ℝ := fun φ =>
    1 / Real.sqrt (radicand k φ) / k
  let B : ℝ → ℝ := fun φ =>
    Real.sqrt (radicand k φ) / (k * (1 - k ^ 2))
  let Q : ℝ → ℝ := fun φ =>
    k / (1 - k ^ 2) * q' φ
  have hA :
      IntervalIntegrable A
        MeasureTheory.volume 0 (Real.pi / 2) :=
    ((continuous_KIntegrand hk0.le hk1).div_const k).intervalIntegrable _ _
  have hB :
      IntervalIntegrable B
        MeasureTheory.volume 0 (Real.pi / 2) :=
    ((continuous_sqrt_radicand k).div_const _).intervalIntegrable _ _
  have hQ :
      IntervalIntegrable Q
        MeasureTheory.volume 0 (Real.pi / 2) :=
    (continuous_const.mul hq'cont).intervalIntegrable _ _
  have hneg :
      (∫ φ in (0 : ℝ)..Real.pi / 2, (-A) φ) =
        -(∫ φ in (0 : ℝ)..Real.pi / 2, A φ) := by
    change
      (∫ φ in (0 : ℝ)..Real.pi / 2, -A φ) =
        -(∫ φ in (0 : ℝ)..Real.pi / 2, A φ)
    exact intervalIntegral.integral_neg
  have hadd :
      (∫ φ in (0 : ℝ)..Real.pi / 2, (-A + B) φ) =
        -(∫ φ in (0 : ℝ)..Real.pi / 2, A φ) +
          ∫ φ in (0 : ℝ)..Real.pi / 2, B φ := by
    calc
      (∫ φ in (0 : ℝ)..Real.pi / 2, (-A + B) φ) =
          (∫ φ in (0 : ℝ)..Real.pi / 2, (-A) φ) +
            ∫ φ in (0 : ℝ)..Real.pi / 2, B φ :=
        intervalIntegral.integral_add hA.neg hB
      _ =
          -(∫ φ in (0 : ℝ)..Real.pi / 2, A φ) +
            ∫ φ in (0 : ℝ)..Real.pi / 2, B φ := by
              rw [hneg]
  rw [gap5 k hk0 hk1]
  calc
    (∫ φ in (0 : ℝ)..Real.pi / 2,
        k * Real.sin φ ^ 2 /
          (radicand k φ * Real.sqrt (radicand k φ))) =
        ∫ φ in (0 : ℝ)..Real.pi / 2,
          (-(1 / Real.sqrt (radicand k φ) / k) +
            Real.sqrt (radicand k φ) / (k * (1 - k ^ 2)) -
            k / (1 - k ^ 2) * q' φ) := by
              apply intervalIntegral.integral_congr
              intro φ hφ
              exact hpoint φ
    _ =
        -(ellipticK k / k) +
          ellipticE k / (k * (1 - k ^ 2)) := by
            change
              (∫ φ in (0 : ℝ)..Real.pi / 2,
                ((-A + B - Q) φ)) =
                -(ellipticK k / k) +
                  ellipticE k / (k * (1 - k ^ 2))
            calc
              (∫ φ in (0 : ℝ)..Real.pi / 2, (-A + B - Q) φ) =
                  ((∫ φ in (0 : ℝ)..Real.pi / 2, (-A + B) φ) -
                    ∫ φ in (0 : ℝ)..Real.pi / 2, Q φ) :=
                intervalIntegral.integral_sub (hA.neg.add hB) hQ
              _ =
                  ((-(∫ φ in (0 : ℝ)..Real.pi / 2, A φ) +
                      ∫ φ in (0 : ℝ)..Real.pi / 2, B φ) -
                    ∫ φ in (0 : ℝ)..Real.pi / 2, Q φ) := by
                      rw [hadd]
              _ =
                  -(ellipticK k / k) +
                    ellipticE k / (k * (1 - k ^ 2)) := by
                      simp [A, B, Q, ellipticE, ellipticK, hqint]

theorem gap7 (k : ℝ) (hk0 : 0 < k) (hk1 : k < 1) :
    deriv (deriv ellipticE) k =
      (((deriv ellipticE k - deriv ellipticK k) * k) -
        (ellipticE k - ellipticK k)) / k ^ 2 := by
  have heq :
      deriv ellipticE =ᶠ[𝓝 k]
        (fun t => (ellipticE t - ellipticK t) / t) := by
    filter_upwards [Ioo_mem_nhds hk0 hk1] with t ht
    exact gap4 t ht.1 ht.2
  have hE₀ := ellipticE_hasDerivAt k hk0 hk1
  have hK₀ := ellipticK_hasDerivAt k hk0 hk1
  have hE :
      HasDerivAt ellipticE (deriv ellipticE k) k :=
    hE₀.congr_deriv hE₀.deriv.symm
  have hK :
      HasDerivAt ellipticK (deriv ellipticK k) k :=
    hK₀.congr_deriv hK₀.deriv.symm
  have hquot :=
    (hE.sub hK).div (hasDerivAt_id k) hk0.ne'
  rw [heq.deriv_eq]
  convert hquot.deriv using 1 <;> simp [id] <;> ring

theorem gap8 (k : ℝ) (hk0 : 0 < k) (hk1 : k < 1) :
    deriv (deriv ellipticE) k =
      -(ellipticE k / (1 - k ^ 2)) - deriv ellipticE k / k := by
  have hkden : 1 - k ^ 2 ≠ 0 := by nlinarith
  rw [gap7 k hk0 hk1, gap6 k hk0 hk1, gap4 k hk0 hk1]
  field_simp [hk0.ne', hkden]
  ring

theorem gap9 (k : ℝ) (hk0 : 0 < k) (hk1 : k < 1) :
    deriv (deriv ellipticE) k +
        deriv ellipticE k / k +
        ellipticE k / (1 - k ^ 2) =
      0 := by
  rw [gap8 k hk0 hk1]
  ring

theorem gap10 (k : ℝ) (hk0 : 0 < k) (hk1 : k < 1) :
    deriv (deriv ellipticE) k +
        (1 / k) * deriv ellipticE k +
        ellipticE k / (1 - k ^ 2) =
      0 := by
  rw [← gap9 k hk0 hk1]
  ring

end

end ProofGap.Exercise3725
