import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise3690

noncomputable section

open Filter Topology

structure Params where
  α : ℝ
  h : ℝ
  R : ℝ
  deriving DecidableEq

def surface (p : Params) : ℝ :=
  Real.pi * p.R ^ 2 + 2 * Real.pi * p.R * p.h +
    Real.pi * p.R ^ 2 / Real.cos p.α

def volume (p : Params) : ℝ :=
  Real.pi * p.R ^ 2 * p.h +
    (1 / 3 : ℝ) * Real.pi * p.R ^ 3 * Real.tan p.α

def feasible (Q : ℝ) (p : Params) : Prop :=
  0 < p.R ∧ 0 < p.h ∧ 0 ≤ p.α ∧ p.α < Real.pi / 2 ∧
    surface p = Q

def critical (Q : ℝ) (p : Params) (μ : ℝ) : Prop :=
  feasible Q p ∧
    p.R ^ 3 / Real.cos p.α ^ 2 -
      μ * p.R ^ 2 * Real.sin p.α / Real.cos p.α ^ 2 = 0 ∧
    3 * p.R ^ 2 - 2 * p.R * μ = 0 ∧
    6 * p.R * p.h + 3 * p.R ^ 2 * Real.tan p.α -
      (2 * p.R + 2 * p.h + 2 * p.R / Real.cos p.α) * μ = 0

def candidateRadius (Q : ℝ) : ℝ :=
  Real.sqrt 2 * (Real.sqrt 5 - 1) / 4 * Real.sqrt (Q / Real.pi)

def candidate (Q : ℝ) : Params :=
  ⟨Real.arcsin (2 / 3), (1 + 1 / Real.sqrt 5) * candidateRadius Q,
    candidateRadius Q⟩

def maximumVolume (Q : ℝ) : ℝ :=
  Real.sqrt 2 * (Real.sqrt 5 - 1) / 12 *
    Real.sqrt (Q ^ 3 / Real.pi)

def hZeroBoundary (Q : ℝ) : Set Params :=
  {p | 0 < p.R ∧ p.h = 0 ∧ 0 ≤ p.α ∧ p.α < Real.pi / 2 ∧
    surface p = Q}

def angleZeroBoundary (Q : ℝ) : Set Params :=
  {p | 0 < p.R ∧ 0 ≤ p.h ∧ p.α = 0 ∧ surface p = Q}

def hZeroSupremum (Q : ℝ) : ℝ :=
  1 / (6 * Real.sqrt 2) * Real.sqrt (Q ^ 3 / Real.pi)

def angleZeroSupremum (Q : ℝ) : ℝ :=
  Real.sqrt (Q ^ 3 / (54 * Real.pi))

def maximizers (Q : ℝ) : Set Params :=
  {p | feasible Q p ∧ ∀ q, feasible Q q → volume q ≤ volume p}

private theorem cos_pos_of_critical {Q μ : ℝ} {p : Params}
    (hcrit : critical Q p μ) :
    0 < Real.cos p.α := by
  rcases hcrit.1 with ⟨hR, hh, hα0, hαlt, hsurface⟩
  exact Real.cos_pos_of_mem_Ioo ⟨by
    have hpipos := Real.pi_pos
    linarith, hαlt⟩

theorem gap1 (Q μ : ℝ) (p : Params) (hcrit : critical Q p μ) :
    μ = (3 / 2 : ℝ) * p.R := by
  have hR := hcrit.1.1
  have heq := hcrit.2.2.1
  nlinarith [mul_pos hR hR]

theorem gap2 (Q μ : ℝ) (p : Params) (hcrit : critical Q p μ) :
    Real.sin p.α = 2 / 3 := by
  have hR := hcrit.1.1
  have hcos := cos_pos_of_critical hcrit
  have heq := hcrit.2.1
  rw [gap1 Q μ p hcrit] at heq
  field_simp [hcos.ne'] at heq
  have hR3 : 0 < p.R ^ 3 := pow_pos hR 3
  nlinarith

theorem gap3 (Q μ : ℝ) (p : Params) (hcrit : critical Q p μ) :
    Real.cos p.α = Real.sqrt 5 / 3 := by
  have hsin := gap2 Q μ p hcrit
  have hcos := cos_pos_of_critical hcrit
  have htrig := Real.sin_sq_add_cos_sq p.α
  have hsqrt : (Real.sqrt 5) ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hsqrtpos : 0 < Real.sqrt 5 := Real.sqrt_pos.2 (by norm_num)
  nlinarith

theorem gap4 (Q μ : ℝ) (p : Params) (hcrit : critical Q p μ) :
    Real.tan p.α = 2 / Real.sqrt 5 := by
  rw [Real.tan_eq_sin_div_cos, gap2 Q μ p hcrit, gap3 Q μ p hcrit]
  have hsqrt : Real.sqrt 5 ≠ 0 := (Real.sqrt_pos.2 (by norm_num)).ne'
  field_simp

theorem gap5 (Q μ : ℝ) (p : Params) (hcrit : critical Q p μ) :
    6 * p.R * p.h + 6 / Real.sqrt 5 * p.R ^ 2 =
      3 * p.R ^ 2 + 3 * p.R * p.h +
        9 / Real.sqrt 5 * p.R ^ 2 := by
  have heq := hcrit.2.2.2
  rw [gap1 Q μ p hcrit, gap3 Q μ p hcrit,
    gap4 Q μ p hcrit] at heq
  have hsqrt : Real.sqrt 5 ≠ 0 := (Real.sqrt_pos.2 (by norm_num)).ne'
  field_simp [hsqrt] at heq ⊢
  nlinarith

theorem gap6 (Q μ : ℝ) (p : Params) (hcrit : critical Q p μ) :
    p.R * p.h = p.R ^ 2 + p.R ^ 2 / Real.sqrt 5 := by
  have heq := gap5 Q μ p hcrit
  have hsqrt : Real.sqrt 5 ≠ 0 := (Real.sqrt_pos.2 (by norm_num)).ne'
  field_simp [hsqrt] at heq ⊢
  nlinarith

theorem gap7 (Q μ : ℝ) (p : Params) (hcrit : critical Q p μ) :
    p.h = (1 + 1 / Real.sqrt 5) * p.R := by
  have hR := hcrit.1.1
  have heq := gap6 Q μ p hcrit
  have hsqrt : Real.sqrt 5 ≠ 0 := (Real.sqrt_pos.2 (by norm_num)).ne'
  field_simp [hR.ne', hsqrt] at heq ⊢
  nlinarith

theorem gap8 (Q μ : ℝ) (p : Params) (hcrit : critical Q p μ) :
    p.R ^ 2 + (2 + 2 / Real.sqrt 5) * p.R ^ 2 +
      3 / Real.sqrt 5 * p.R ^ 2 = Q / Real.pi := by
  rcases hcrit.1 with ⟨hR, hh, hα0, hαlt, hsurface⟩
  have hRh := gap6 Q μ p hcrit
  have hhformula := gap7 Q μ p hcrit
  have hcos := gap3 Q μ p hcrit
  unfold surface at hsurface
  rw [hcos, hhformula] at hsurface
  have hsqrt : Real.sqrt 5 ≠ 0 := (Real.sqrt_pos.2 (by norm_num)).ne'
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp [hsqrt, hpi] at hsurface ⊢
  nlinarith

private theorem sqrt_five_sq :
    (Real.sqrt 5) ^ 2 = 5 :=
  Real.sq_sqrt (by norm_num)

private theorem inv_sqrt_five :
    1 / Real.sqrt 5 = Real.sqrt 5 / 5 := by
  have hsqrt : Real.sqrt 5 ≠ 0 := (Real.sqrt_pos.2 (by norm_num)).ne'
  field_simp [hsqrt]
  nlinarith [sqrt_five_sq]

private theorem candidateRadius_sq_identity (Q : ℝ) (hQ : 0 ≤ Q) :
    candidateRadius Q ^ 2 * (3 + Real.sqrt 5) = Q / Real.pi := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hquot : 0 ≤ Q / Real.pi := div_nonneg hQ hpi.le
  have hsqrtQ : Real.sqrt (Q / Real.pi) ^ 2 = Q / Real.pi :=
    Real.sq_sqrt hquot
  have hsqrtTwo : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  unfold candidateRadius
  rw [show
    (Real.sqrt 2 * (Real.sqrt 5 - 1) / 4 *
      Real.sqrt (Q / Real.pi)) ^ 2 * (3 + Real.sqrt 5) =
      (Real.sqrt 2) ^ 2 * (Real.sqrt 5 - 1) ^ 2 / 16 *
        (Real.sqrt (Q / Real.pi)) ^ 2 * (3 + Real.sqrt 5) by ring,
    hsqrtTwo, hsqrtQ]
  calc
    2 * (Real.sqrt 5 - 1) ^ 2 / 16 * (Q / Real.pi) *
        (3 + Real.sqrt 5) =
        (2 * (Real.sqrt 5 - 1) ^ 2 / 16 *
          (3 + Real.sqrt 5)) * (Q / Real.pi) := by ring
    _ = 1 * (Q / Real.pi) := by
      congr 1
      nlinarith [sqrt_five_sq]
    _ = Q / Real.pi := by ring

private theorem candidateRadius_pos (Q : ℝ) (hQ : 0 < Q) :
    0 < candidateRadius Q := by
  unfold candidateRadius
  have h2 : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have h5 : 1 < Real.sqrt 5 := by
    have hp : 0 < Real.sqrt 5 := Real.sqrt_pos.2 (by norm_num)
    nlinarith [sqrt_five_sq]
  have hquot : 0 < Q / Real.pi := div_pos hQ Real.pi_pos
  have hsq : 0 < Real.sqrt (Q / Real.pi) := Real.sqrt_pos.2 hquot
  exact mul_pos (div_pos (mul_pos h2 (sub_pos.mpr h5)) (by norm_num)) hsq

theorem gap9 (Q μ : ℝ) (hQ : 0 < Q) (p : Params)
    (hcrit : critical Q p μ) :
    p.R = candidateRadius Q := by
  have hR : 0 < p.R := hcrit.1.1
  have heq := gap8 Q μ p hcrit
  have hsqrt : Real.sqrt 5 ≠ 0 := (Real.sqrt_pos.2 (by norm_num)).ne'
  field_simp [hsqrt] at heq
  have hRidentity :
      p.R ^ 2 * (3 + Real.sqrt 5) = Q / Real.pi := by
    have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
    field_simp [hpi]
    have hmul :
        Real.sqrt 5 *
          (p.R ^ 2 * (3 + Real.sqrt 5) * Real.pi - Q) = 0 := by
      calc
        Real.sqrt 5 *
            (p.R ^ 2 * (3 + Real.sqrt 5) * Real.pi - Q) =
            p.R ^ 2 * (3 * Real.sqrt 5 + (Real.sqrt 5) ^ 2) *
              Real.pi - Real.sqrt 5 * Q := by ring
        _ = p.R ^ 2 * (3 * Real.sqrt 5 + 5) *
              Real.pi - Real.sqrt 5 * Q := by rw [sqrt_five_sq]
        _ = p.R ^ 2 *
              (Real.sqrt 5 + 2 * (Real.sqrt 5 + 1) + 3) *
              Real.pi - Real.sqrt 5 * Q := by ring
        _ = 0 := by rw [heq]; ring
    have hzero := (mul_eq_zero.mp hmul).resolve_left hsqrt
    nlinarith
  have hcidentity := candidateRadius_sq_identity Q hQ.le
  have hsum : 0 < 3 + Real.sqrt 5 := by positivity
  have hsquares : p.R ^ 2 = candidateRadius Q ^ 2 := by
    nlinarith
  have hcpos := candidateRadius_pos Q hQ
  nlinarith [sq_nonneg (p.R - candidateRadius Q),
    sq_nonneg (p.R + candidateRadius Q)]

private theorem candidate_sin :
    Real.sin (Real.arcsin (2 / 3)) = 2 / 3 := by
  exact Real.sin_arcsin (by norm_num) (by norm_num)

private theorem candidate_cos :
    Real.cos (Real.arcsin (2 / 3)) = Real.sqrt 5 / 3 := by
  rw [Real.cos_arcsin]
  norm_num
  rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.sqrt_sq_eq_abs]
  norm_num

private theorem candidate_tan :
    Real.tan (Real.arcsin (2 / 3)) = 2 / Real.sqrt 5 := by
  rw [Real.tan_eq_sin_div_cos, candidate_sin, candidate_cos]
  have hsqrt : Real.sqrt 5 ≠ 0 := (Real.sqrt_pos.2 (by norm_num)).ne'
  field_simp

theorem gap10 (Q : ℝ) (hQ : 0 < Q) :
    ∃ μ : ℝ, critical Q (candidate Q) μ := by
  let r := candidateRadius Q
  refine ⟨(3 / 2 : ℝ) * r, ?_⟩
  have hr : 0 < r := candidateRadius_pos Q hQ
  have hsqrtpos : 0 < Real.sqrt 5 := Real.sqrt_pos.2 (by norm_num)
  have hsqrt : Real.sqrt 5 ≠ 0 := hsqrtpos.ne'
  have hrSq := candidateRadius_sq_identity Q hQ.le
  have hfeas : feasible Q (candidate Q) := by
    refine ⟨hr, ?_, ?_, ?_, ?_⟩
    · change 0 < (1 + 1 / Real.sqrt 5) * r
      exact mul_pos (by positivity) hr
    · change 0 ≤ Real.arcsin (2 / 3)
      exact Real.arcsin_nonneg.mpr (by norm_num)
    · change Real.arcsin (2 / 3) < Real.pi / 2
      exact Real.arcsin_lt_pi_div_two.mpr (by norm_num)
    · unfold surface candidate
      simp only
      rw [candidate_cos]
      change Real.pi * r ^ 2 +
          2 * Real.pi * r * ((1 + 1 / Real.sqrt 5) * r) +
          Real.pi * r ^ 2 / (Real.sqrt 5 / 3) = Q
      have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
      have hmul : Real.pi * (r ^ 2 * (3 + Real.sqrt 5)) = Q := by
        rw [hrSq]
        field_simp [hpi]
      field_simp [hsqrt]
      field_simp [hsqrt] at hmul
      nlinarith [sqrt_five_sq]
  refine ⟨hfeas, ?_, ?_, ?_⟩
  · change r ^ 3 / Real.cos (Real.arcsin (2 / 3)) ^ 2 -
      ((3 / 2 : ℝ) * r) * r ^ 2 *
        Real.sin (Real.arcsin (2 / 3)) /
          Real.cos (Real.arcsin (2 / 3)) ^ 2 = 0
    rw [candidate_sin, candidate_cos]
    field_simp [hsqrt]
    ring
  · change 3 * r ^ 2 - 2 * r * ((3 / 2 : ℝ) * r) = 0
    ring
  · change
      6 * r * ((1 + 1 / Real.sqrt 5) * r) +
        3 * r ^ 2 * Real.tan (Real.arcsin (2 / 3)) -
        (2 * r + 2 * ((1 + 1 / Real.sqrt 5) * r) +
          2 * r / Real.cos (Real.arcsin (2 / 3))) *
          ((3 / 2 : ℝ) * r) = 0
    rw [candidate_tan, candidate_cos]
    field_simp [hsqrt]
    ring

private theorem sqrt_Q_cube_div_pi (Q : ℝ) (hQ : 0 ≤ Q) :
    Real.sqrt (Q ^ 3 / Real.pi) =
      Q * Real.sqrt (Q / Real.pi) := by
  rw [show Q ^ 3 / Real.pi = Q ^ 2 * (Q / Real.pi) by ring,
    Real.sqrt_mul (sq_nonneg Q), Real.sqrt_sq_eq_abs,
    abs_of_nonneg hQ]

theorem gap11 (Q : ℝ) (hQ : 0 < Q) :
    volume (candidate Q) = maximumVolume Q := by
  let r := candidateRadius Q
  have hrSq := candidateRadius_sq_identity Q hQ.le
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have hmul : Real.pi * (r ^ 2 * (3 + Real.sqrt 5)) = Q := by
    rw [hrSq]
    field_simp [hpi]
  have hsqrt : Real.sqrt 5 ≠ 0 := (Real.sqrt_pos.2 (by norm_num)).ne'
  have hvolume : volume (candidate Q) = Q * r / 3 := by
    unfold volume candidate
    simp only
    rw [candidate_tan]
    change
      Real.pi * r ^ 2 * ((1 + 1 / Real.sqrt 5) * r) +
        (1 / 3 : ℝ) * Real.pi * r ^ 3 *
          (2 / Real.sqrt 5) = Q * r / 3
    field_simp [hsqrt]
    calc
      Real.pi * r ^ 3 *
          ((Real.sqrt 5 + 1) * 3 + 2) =
          r * Real.sqrt 5 *
            (Real.pi * (r ^ 2 * (3 + Real.sqrt 5))) := by
        calc
          Real.pi * r ^ 3 *
              ((Real.sqrt 5 + 1) * 3 + 2) =
              Real.pi * r ^ 3 * (3 * Real.sqrt 5 + 5) := by ring
          _ = Real.pi * r ^ 3 *
              (3 * Real.sqrt 5 + (Real.sqrt 5) ^ 2) := by
            rw [sqrt_five_sq]
          _ = r * Real.sqrt 5 *
              (Real.pi * (r ^ 2 * (3 + Real.sqrt 5))) := by ring
      _ = r * Real.sqrt 5 * Q := by rw [hmul]
  rw [hvolume]
  unfold maximumVolume r candidateRadius
  rw [sqrt_Q_cube_div_pi Q hQ.le]
  ring

private theorem volume_nonnegative_of_feasible {Q : ℝ} {p : Params}
    (hp : feasible Q p) :
    0 ≤ volume p := by
  rcases hp with ⟨hR, hh, hα0, hαlt, hsurface⟩
  have hsin : 0 ≤ Real.sin p.α :=
    Real.sin_nonneg_of_nonneg_of_le_pi hα0
      (by linarith [Real.pi_pos])
  have hcos : 0 < Real.cos p.α :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hαlt⟩
  rw [volume, Real.tan_eq_sin_div_cos]
  positivity

private theorem volume_le_radius_bound {Q : ℝ} (hQ : 0 < Q)
    {p : Params} (hp : feasible Q p) :
    volume p ≤ (5 / 6 : ℝ) * Q * p.R := by
  rcases hp with ⟨hR, hh, hα0, hαlt, hsurface⟩
  have hsin : 0 ≤ Real.sin p.α :=
    Real.sin_nonneg_of_nonneg_of_le_pi hα0
      (by linarith [Real.pi_pos])
  have hsinOne : Real.sin p.α ≤ 1 := Real.sin_le_one _
  have hcos : 0 < Real.cos p.α :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hαlt⟩
  have hA : 0 ≤ Real.pi * p.R ^ 2 := by positivity
  have hB : 0 ≤ 2 * Real.pi * p.R * p.h := by positivity
  have hC : 0 ≤ Real.pi * p.R ^ 2 / Real.cos p.α := by positivity
  have hB_le : 2 * Real.pi * p.R * p.h ≤ Q := by
    rw [← hsurface]
    unfold surface
    linarith
  have hC_le : Real.pi * p.R ^ 2 / Real.cos p.α ≤ Q := by
    rw [← hsurface]
    unfold surface
    linarith
  have hcylinder :
      Real.pi * p.R ^ 2 * p.h ≤ (1 / 2 : ℝ) * Q * p.R := by
    calc
      Real.pi * p.R ^ 2 * p.h =
          (p.R / 2) * (2 * Real.pi * p.R * p.h) := by ring
      _ ≤ (p.R / 2) * Q :=
        mul_le_mul_of_nonneg_left hB_le (by positivity)
      _ = (1 / 2 : ℝ) * Q * p.R := by ring
  have hcone :
      (1 / 3 : ℝ) * Real.pi * p.R ^ 3 * Real.tan p.α ≤
        (1 / 3 : ℝ) * Q * p.R := by
    rw [Real.tan_eq_sin_div_cos]
    calc
      (1 / 3 : ℝ) * Real.pi * p.R ^ 3 *
          (Real.sin p.α / Real.cos p.α) =
          (p.R * Real.sin p.α / 3) *
            (Real.pi * p.R ^ 2 / Real.cos p.α) := by ring
      _ ≤ (p.R * Real.sin p.α / 3) * Q :=
        mul_le_mul_of_nonneg_left hC_le (by positivity)
      _ ≤ (p.R / 3) * Q := by
        gcongr
        simpa using mul_le_mul_of_nonneg_left hsinOne hR.le
      _ = (1 / 3 : ℝ) * Q * p.R := by ring
  unfold volume
  linarith

theorem gap12 (Q : ℝ) (hQ : 0 < Q) (p : ℕ → Params)
    (hfeas : ∀ n, feasible Q (p n))
    (hR : Filter.Tendsto (fun n => (p n).R) Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun n => volume (p n)) Filter.atTop (nhds 0) := by
  apply squeeze_zero
  · intro n
    exact volume_nonnegative_of_feasible (hfeas n)
  · intro n
    exact volume_le_radius_bound hQ (hfeas n)
  · have ht :
        Tendsto (fun n => (5 / 6 : ℝ) * Q * (p n).R)
          atTop (𝓝 ((5 / 6 : ℝ) * Q * 0)) :=
      tendsto_const_nhds.mul hR
    simpa using ht

private theorem hZero_volume_le (Q : ℝ) (hQ : 0 < Q)
    (p : Params) (hp : p ∈ hZeroBoundary Q) :
    volume p ≤ hZeroSupremum Q := by
  rcases hp with ⟨hR, hhzero, hα0, hαlt, hsurface⟩
  have hcos : 0 < Real.cos p.α :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hαlt⟩
  have hsin : 0 ≤ Real.sin p.α :=
    Real.sin_nonneg_of_nonneg_of_le_pi hα0
      (by linarith [Real.pi_pos])
  have htrig := Real.sin_sq_add_cos_sq p.α
  have hangle :
      8 * Real.sin p.α ^ 2 * Real.cos p.α ≤
        (1 + Real.cos p.α) ^ 3 := by
    have hfac :
        0 ≤ (3 * Real.cos p.α - 1) ^ 2 *
          (Real.cos p.α + 1) := by positivity
    nlinarith
  have hQexpr :
      Q = Real.pi * p.R ^ 2 *
        (1 + Real.cos p.α) / Real.cos p.α := by
    rw [← hsurface]
    unfold surface
    rw [hhzero]
    field_simp [hcos.ne']
    ring
  have hvolnonneg : 0 ≤ volume p := by
    unfold volume
    rw [hhzero, Real.tan_eq_sin_div_cos]
    positivity
  have hsupnonneg : 0 ≤ hZeroSupremum Q := by
    unfold hZeroSupremum
    positivity
  have hinside : 0 ≤ Q ^ 3 / Real.pi := by positivity
  have hsupSq :
      hZeroSupremum Q ^ 2 = Q ^ 3 / Real.pi / 72 := by
    unfold hZeroSupremum
    rw [mul_pow, Real.sq_sqrt hinside]
    have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    have h2ne : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.2 (by norm_num)).ne'
    field_simp [h2ne]
    nlinarith
  have hvolSq :
      volume p ^ 2 =
        (Real.pi ^ 2 * p.R ^ 6 /
          (72 * Real.cos p.α ^ 3)) *
            (8 * Real.sin p.α ^ 2 * Real.cos p.α) := by
    unfold volume
    rw [hhzero, Real.tan_eq_sin_div_cos]
    field_simp [hcos.ne']
    ring
  have hsupSq' :
      hZeroSupremum Q ^ 2 =
        (Real.pi ^ 2 * p.R ^ 6 /
          (72 * Real.cos p.α ^ 3)) *
            (1 + Real.cos p.α) ^ 3 := by
    rw [hsupSq, hQexpr]
    field_simp [Real.pi_ne_zero, hcos.ne']
  have hfactor :
      0 ≤ Real.pi ^ 2 * p.R ^ 6 /
        (72 * Real.cos p.α ^ 3) := by positivity
  apply (sq_le_sq₀ hvolnonneg hsupnonneg).mp
  rw [hvolSq, hsupSq']
  exact mul_le_mul_of_nonneg_left hangle hfactor

theorem gap13 (Q : ℝ) (hQ : 0 < Q) :
    sSup (volume '' hZeroBoundary Q) = hZeroSupremum Q := by
  let a : ℝ := Real.arccos (1 / 3)
  let x : ℝ := Real.sqrt (Q / Real.pi)
  let p₀ : Params := ⟨a, 0, x / 2⟩
  have hx : 0 < x := by
    dsimp [x]
    exact Real.sqrt_pos.2 (div_pos hQ Real.pi_pos)
  have hxSq : x ^ 2 = Q / Real.pi := by
    dsimp [x]
    exact Real.sq_sqrt (div_nonneg hQ.le Real.pi_pos.le)
  have hpixSq : Real.pi * x ^ 2 = Q := by
    rw [hxSq]
    field_simp [Real.pi_ne_zero]
  have hcos : Real.cos a = 1 / 3 := by
    dsimp [a]
    exact Real.cos_arccos (by norm_num) (by norm_num)
  have hsin : Real.sin a = 2 * Real.sqrt 2 / 3 := by
    have hs : 0 ≤ Real.sin a := by
      dsimp [a]
      rw [Real.sin_arccos]
      positivity
    have htrig := Real.sin_sq_add_cos_sq a
    rw [hcos] at htrig
    have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    have hs2 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
    nlinarith
  have htan : Real.tan a = 2 * Real.sqrt 2 := by
    rw [Real.tan_eq_sin_div_cos, hsin, hcos]
    ring
  have hp₀ : p₀ ∈ hZeroBoundary Q := by
    refine ⟨by
      change 0 < x / 2
      positivity, rfl, ?_, ?_, ?_⟩
    · change 0 ≤ a
      exact Real.arccos_nonneg _
    · change a < Real.pi / 2
      exact Real.arccos_lt_pi_div_two.mpr (by norm_num)
    · unfold surface p₀
      simp only
      rw [hcos]
      field_simp
      nlinarith
  have hp₀Volume : volume p₀ = hZeroSupremum Q := by
    have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    have h2ne : Real.sqrt 2 ≠ 0 :=
      (Real.sqrt_pos.2 (by norm_num)).ne'
    calc
      volume p₀ =
          Real.pi * x ^ 3 * Real.sqrt 2 / 12 := by
            unfold volume p₀
            simp only
            rw [htan]
            ring
      _ = Q * x * Real.sqrt 2 / 12 := by
            rw [show Real.pi * x ^ 3 = Q * x by
              calc
                Real.pi * x ^ 3 = (Real.pi * x ^ 2) * x := by ring
                _ = Q * x := by rw [hpixSq]]
      _ = 1 / (6 * Real.sqrt 2) * (Q * x) := by
            field_simp [h2ne]
            nlinarith
      _ = hZeroSupremum Q := by
            unfold hZeroSupremum
            rw [sqrt_Q_cube_div_pi Q hQ.le]
  have hmem : hZeroSupremum Q ∈ volume '' hZeroBoundary Q :=
    ⟨p₀, hp₀, hp₀Volume⟩
  apply le_antisymm
  · exact csSup_le ⟨hZeroSupremum Q, hmem⟩ (by
      intro v hv
      rcases hv with ⟨p, hp, rfl⟩
      exact hZero_volume_le Q hQ p hp)
  · apply le_csSup
    · exact ⟨hZeroSupremum Q, by
        intro v hv
        rcases hv with ⟨p, hp, rfl⟩
        exact hZero_volume_le Q hQ p hp⟩
    · exact hmem


theorem gap14 (Q : ℝ) (hQ : 0 < Q) :
    hZeroSupremum Q < maximumVolume Q := by
  have hroot : 0 < Real.sqrt (Q ^ 3 / Real.pi) := by
    apply Real.sqrt_pos.2
    positivity
  unfold hZeroSupremum maximumVolume
  apply mul_lt_mul_of_pos_right _ hroot
  have h2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h2ne : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.2 (by norm_num)).ne'
  have h5lt : 2 < Real.sqrt 5 := by
    have h5pos : 0 < Real.sqrt 5 := Real.sqrt_pos.2 (by norm_num)
    nlinarith [sqrt_five_sq]
  field_simp [h2ne]
  nlinarith

theorem gap15 (Q : ℝ) (hQ : 0 < Q) (p : ℕ → Params)
    (hfeas : ∀ n, feasible Q (p n))
    (hh : Filter.Tendsto (fun n => (p n).h) Filter.atTop Filter.atTop) :
    Filter.Tendsto (fun n => (p n).R) Filter.atTop (nhds 0) := by
  have hinv :
      Tendsto (fun n => ((p n).h)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hh
  have hupper :
      Tendsto (fun n => (Q / (2 * Real.pi)) * ((p n).h)⁻¹)
        atTop (𝓝 0) := by
    convert tendsto_const_nhds.mul hinv using 1 <;> ring
  apply squeeze_zero
  · intro n
    exact (hfeas n).1.le
  · intro n
    rcases hfeas n with ⟨hR, hhpos, hα0, hαlt, hsurface⟩
    have hcos : 0 < Real.cos (p n).α :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hαlt⟩
    have hA : 0 ≤ Real.pi * (p n).R ^ 2 := by positivity
    have hC : 0 ≤ Real.pi * (p n).R ^ 2 / Real.cos (p n).α := by
      positivity
    have hB : 2 * Real.pi * (p n).R * (p n).h ≤ Q := by
      rw [← hsurface]
      unfold surface
      linarith
    have hden : 0 < 2 * Real.pi * (p n).h := by positivity
    calc
      (p n).R ≤ Q / (2 * Real.pi * (p n).h) := by
        rw [le_div_iff₀ hden]
        nlinarith
      _ = (Q / (2 * Real.pi)) * ((p n).h)⁻¹ := by
        field_simp [Real.pi_ne_zero, hhpos.ne']
  · exact hupper

theorem gap16 (Q : ℝ) (hQ : 0 < Q) (p : ℕ → Params)
    (hfeas : ∀ n, feasible Q (p n))
    (hh : Filter.Tendsto (fun n => (p n).h) Filter.atTop Filter.atTop) :
    Filter.Tendsto (fun n => volume (p n)) Filter.atTop (nhds 0) := by
  exact gap12 Q hQ p hfeas (gap15 Q hQ p hfeas hh)

theorem gap17 (Q : ℝ) (hQ : 0 < Q) (p : ℕ → Params)
    (hfeas : ∀ n, feasible Q (p n))
    (hα : Filter.Tendsto (fun n => (p n).α) Filter.atTop
      (nhds (Real.pi / 2))) :
    Filter.Tendsto (fun n => (p n).R) Filter.atTop (nhds 0) := by
  have hcos :
      Tendsto (fun n => Real.cos (p n).α) atTop (𝓝 0) := by
    have ht := Real.continuous_cos.continuousAt.tendsto.comp hα
    simpa using ht
  have hscaled :
      Tendsto (fun n => (Q / Real.pi) * Real.cos (p n).α)
        atTop (𝓝 0) := by
    convert tendsto_const_nhds.mul hcos using 1 <;> ring
  have hsqrt :
      Tendsto
        (fun n => Real.sqrt ((Q / Real.pi) * Real.cos (p n).α))
        atTop (𝓝 0) := by
    have ht := Real.continuous_sqrt.continuousAt.tendsto.comp hscaled
    simpa using ht
  apply squeeze_zero
  · intro n
    exact (hfeas n).1.le
  · intro n
    rcases hfeas n with ⟨hR, hhpos, hα0, hαlt, hsurface⟩
    have hcospos : 0 < Real.cos (p n).α :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hαlt⟩
    have hA : 0 ≤ Real.pi * (p n).R ^ 2 := by positivity
    have hB : 0 ≤ 2 * Real.pi * (p n).R * (p n).h := by positivity
    have hC_le :
        Real.pi * (p n).R ^ 2 / Real.cos (p n).α ≤ Q := by
      rw [← hsurface]
      unfold surface
      linarith
    have hsq :
        (p n).R ^ 2 ≤ (Q / Real.pi) * Real.cos (p n).α := by
      have hmul := mul_le_mul_of_nonneg_right hC_le hcospos.le
      field_simp [Real.pi_ne_zero, hcospos.ne'] at hmul ⊢
      nlinarith [Real.pi_pos]
    exact
      (Real.le_sqrt hR.le (mul_nonneg (div_nonneg hQ.le Real.pi_pos.le)
        hcospos.le)).2 hsq
  · exact hsqrt

theorem gap18 (Q : ℝ) (hQ : 0 < Q) (p : ℕ → Params)
    (hfeas : ∀ n, feasible Q (p n))
    (hα : Filter.Tendsto (fun n => (p n).α) Filter.atTop
      (nhds (Real.pi / 2))) :
    Filter.Tendsto (fun n => volume (p n)) Filter.atTop (nhds 0) := by
  exact gap12 Q hQ p hfeas (gap17 Q hQ p hfeas hα)

private theorem angleZero_value (Q : ℝ) (hQ : 0 < Q) :
    angleZeroSupremum Q =
      2 * Real.pi * (Real.sqrt (Q / (6 * Real.pi))) ^ 3 := by
  let a : ℝ := Real.sqrt (Q / (6 * Real.pi))
  have ha : 0 ≤ a := by
    dsimp [a]
    positivity
  have haSq : a ^ 2 = Q / (6 * Real.pi) := by
    dsimp [a]
    exact Real.sq_sqrt (by positivity)
  have hinside : 0 ≤ Q ^ 3 / (54 * Real.pi) := by positivity
  have hright : 0 ≤ 2 * Real.pi * a ^ 3 := by positivity
  have hsq :
      (2 * Real.pi * a ^ 3) ^ 2 =
        Q ^ 3 / (54 * Real.pi) := by
    calc
      (2 * Real.pi * a ^ 3) ^ 2 =
          4 * Real.pi ^ 2 * (a ^ 2) ^ 3 := by ring
      _ = 4 * Real.pi ^ 2 *
          (Q / (6 * Real.pi)) ^ 3 := by rw [haSq]
      _ = Q ^ 3 / (54 * Real.pi) := by
        field_simp [Real.pi_ne_zero]
        ring
  unfold angleZeroSupremum
  change Real.sqrt (Q ^ 3 / (54 * Real.pi)) =
    2 * Real.pi * a ^ 3
  apply (sq_eq_sq₀ (Real.sqrt_nonneg _) hright).mp
  rw [Real.sq_sqrt hinside, hsq]

private theorem angleZero_volume_le (Q : ℝ) (hQ : 0 < Q)
    (p : Params) (hp : p ∈ angleZeroBoundary Q) :
    volume p ≤ angleZeroSupremum Q := by
  let a : ℝ := Real.sqrt (Q / (6 * Real.pi))
  rcases hp with ⟨hR, hh, hαzero, hsurface⟩
  have ha : 0 < a := by
    dsimp [a]
    exact Real.sqrt_pos.2 (by positivity)
  have haSq : a ^ 2 = Q / (6 * Real.pi) := by
    dsimp [a]
    exact Real.sq_sqrt (by positivity)
  have hQeq : Q = 6 * Real.pi * a ^ 2 := by
    rw [haSq]
    field_simp [Real.pi_ne_zero]
  have hsurface' := hsurface
  unfold surface at hsurface'
  rw [hαzero] at hsurface'
  simp only [Real.cos_zero, div_one] at hsurface'
  have hconstraint : p.R * p.h = 3 * a ^ 2 - p.R ^ 2 := by
    have hzero :
        2 * Real.pi *
          (p.R ^ 2 + p.R * p.h - 3 * a ^ 2) = 0 := by
      rw [hQeq] at hsurface'
      linarith
    have hfactor :=
      (mul_eq_zero.mp hzero).resolve_left
        (by positivity : 2 * Real.pi ≠ 0)
    linarith
  have hfactor :
      0 ≤ Real.pi * (p.R - a) ^ 2 * (p.R + 2 * a) := by
    positivity
  rw [angleZero_value Q hQ]
  calc
    volume p =
        Real.pi * p.R * (3 * a ^ 2 - p.R ^ 2) := by
      unfold volume
      rw [hαzero]
      simp only [Real.tan_zero, mul_zero, add_zero]
      rw [show Real.pi * p.R ^ 2 * p.h =
        Real.pi * p.R * (p.R * p.h) by ring, hconstraint]
    _ ≤ 2 * Real.pi * a ^ 3 := by
      nlinarith

theorem gap19 (Q : ℝ) (hQ : 0 < Q) :
    sSup (volume '' angleZeroBoundary Q) = angleZeroSupremum Q := by
  let a : ℝ := Real.sqrt (Q / (6 * Real.pi))
  let p₀ : Params := ⟨0, 2 * a, a⟩
  have ha : 0 < a := by
    dsimp [a]
    exact Real.sqrt_pos.2 (by positivity)
  have haSq : a ^ 2 = Q / (6 * Real.pi) := by
    dsimp [a]
    exact Real.sq_sqrt (by positivity)
  have hQeq : Q = 6 * Real.pi * a ^ 2 := by
    rw [haSq]
    field_simp [Real.pi_ne_zero]
  have hp₀ : p₀ ∈ angleZeroBoundary Q := by
    refine ⟨by
      change 0 < a
      exact ha, by
      change 0 ≤ 2 * a
      positivity, rfl, ?_⟩
    unfold surface p₀
    simp only [Real.cos_zero, div_one]
    nlinarith
  have hp₀Volume : volume p₀ = angleZeroSupremum Q := by
    rw [angleZero_value Q hQ]
    unfold volume p₀
    simp only [Real.tan_zero, mul_zero, add_zero]
    ring
  have hmem : angleZeroSupremum Q ∈
      volume '' angleZeroBoundary Q :=
    ⟨p₀, hp₀, hp₀Volume⟩
  apply le_antisymm
  · exact csSup_le ⟨angleZeroSupremum Q, hmem⟩ (by
      intro v hv
      rcases hv with ⟨p, hp, rfl⟩
      exact angleZero_volume_le Q hQ p hp)
  · apply le_csSup
    · exact ⟨angleZeroSupremum Q, by
        intro v hv
        rcases hv with ⟨p, hp, rfl⟩
        exact angleZero_volume_le Q hQ p hp⟩
    · exact hmem

theorem gap20 (Q : ℝ) (hQ : 0 < Q) :
    angleZeroSupremum Q < maximumVolume Q := by
  have hT : 0 < Q ^ 3 / Real.pi := by positivity
  have hA : 0 ≤ angleZeroSupremum Q := by
    unfold angleZeroSupremum
    exact Real.sqrt_nonneg _
  have hM : 0 ≤ maximumVolume Q := by
    unfold maximumVolume
    have h5 : 1 ≤ Real.sqrt 5 := by
      have h5pos : 0 < Real.sqrt 5 := Real.sqrt_pos.2 (by norm_num)
      nlinarith [sqrt_five_sq]
    exact mul_nonneg
      (div_nonneg
        (mul_nonneg (Real.sqrt_nonneg _) (sub_nonneg.mpr h5))
        (by norm_num))
      (Real.sqrt_nonneg _)
  have hASq :
      angleZeroSupremum Q ^ 2 =
        (1 / 54 : ℝ) * (Q ^ 3 / Real.pi) := by
    unfold angleZeroSupremum
    rw [Real.sq_sqrt (by positivity)]
    ring
  have hMSq :
      maximumVolume Q ^ 2 =
        (Real.sqrt 2 * (Real.sqrt 5 - 1) / 12) ^ 2 *
          (Q ^ 3 / Real.pi) := by
    unfold maximumVolume
    rw [mul_pow, Real.sq_sqrt hT.le]
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h5lt : Real.sqrt 5 < 7 / 3 := by
    have h5pos : 0 < Real.sqrt 5 := Real.sqrt_pos.2 (by norm_num)
    nlinarith [sqrt_five_sq]
  have hcoeff :
      (1 / 54 : ℝ) <
        (Real.sqrt 2 * (Real.sqrt 5 - 1) / 12) ^ 2 := by
    rw [show
      (Real.sqrt 2 * (Real.sqrt 5 - 1) / 12) ^ 2 =
        Real.sqrt 2 ^ 2 * (Real.sqrt 5 - 1) ^ 2 / 144 by ring,
      h2]
    nlinarith [sqrt_five_sq]
  apply (sq_lt_sq₀ hA hM).mp
  rw [hASq, hMSq]
  exact mul_lt_mul_of_pos_right hcoeff hT

private theorem angle_coefficient_ge_and_eq {α : ℝ}
    (hα0 : 0 ≤ α) (hαlt : α < Real.pi / 2) :
    1 + Real.sqrt 5 / 3 ≤
        1 + (1 - 2 * Real.sin α / 3) / Real.cos α ∧
      (1 + (1 - 2 * Real.sin α / 3) / Real.cos α =
          1 + Real.sqrt 5 / 3 →
        Real.sin α = 2 / 3) := by
  have hcos : 0 < Real.cos α :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hαlt⟩
  have hsin : 0 ≤ Real.sin α :=
    Real.sin_nonneg_of_nonneg_of_le_pi hα0
      (by linarith [Real.pi_pos])
  have hsinOne : Real.sin α ≤ 1 := Real.sin_le_one _
  have hleft : 0 ≤ Real.sqrt 5 * Real.cos α := by positivity
  have hright : 0 ≤ 3 - 2 * Real.sin α := by linarith
  have htrig := Real.sin_sq_add_cos_sq α
  have hsq :
      (Real.sqrt 5 * Real.cos α) ^ 2 ≤
        (3 - 2 * Real.sin α) ^ 2 := by
    nlinarith [sqrt_five_sq, sq_nonneg (3 * Real.sin α - 2)]
  have hlinear :
      Real.sqrt 5 * Real.cos α ≤
        3 - 2 * Real.sin α :=
    (sq_le_sq₀ hleft hright).mp hsq
  have hratio :
      Real.sqrt 5 / 3 ≤
        (1 - 2 * Real.sin α / 3) / Real.cos α := by
    rw [le_div_iff₀ hcos]
    nlinarith
  refine ⟨by linarith, ?_⟩
  intro heq
  have hratioEq :
      (1 - 2 * Real.sin α / 3) / Real.cos α =
        Real.sqrt 5 / 3 := by
    linarith
  have hlinearEq :
      3 - 2 * Real.sin α = Real.sqrt 5 * Real.cos α := by
    field_simp [hcos.ne'] at hratioEq
    nlinarith
  have hsqEq := congrArg (fun z : ℝ => z ^ 2) hlinearEq
  nlinarith [sqrt_five_sq]

private theorem maximumVolume_sq_identity (Q : ℝ) (hQ : 0 ≤ Q) :
    maximumVolume Q ^ 2 =
      Q ^ 3 /
        (27 * Real.pi * (1 + Real.sqrt 5 / 3)) := by
  have hinside : 0 ≤ Q ^ 3 / Real.pi := by positivity
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hcoef : 1 + Real.sqrt 5 / 3 ≠ 0 := by positivity
  have hcoeff :
      (Real.sqrt 2 * (Real.sqrt 5 - 1) / 12) ^ 2 =
        1 / (27 * (1 + Real.sqrt 5 / 3)) := by
    rw [show
      (Real.sqrt 2 * (Real.sqrt 5 - 1) / 12) ^ 2 =
        Real.sqrt 2 ^ 2 * (Real.sqrt 5 - 1) ^ 2 / 144 by ring,
      h2]
    field_simp [hcoef]
    nlinarith [sqrt_five_sq]
  unfold maximumVolume
  rw [mul_pow, Real.sq_sqrt hinside, hcoeff]
  field_simp [Real.pi_ne_zero, hcoef]

private def interiorU (p : Params) : ℝ :=
  p.R * p.h +
    p.R ^ 2 * Real.sin p.α / (3 * Real.cos p.α)

private def interiorW (p : Params) : ℝ :=
  p.R ^ 2 *
    (1 + (1 - 2 * Real.sin p.α / 3) / Real.cos p.α)

private theorem feasible_volume_bound_data (Q : ℝ) (hQ : 0 < Q)
    (p : Params) (hp : feasible Q p) :
    volume p ≤ maximumVolume Q ∧
      (volume p = maximumVolume Q →
        Real.sin p.α = 2 / 3 ∧ interiorU p = interiorW p) := by
  rcases hp with ⟨hR, hh, hα0, hαlt, hsurface⟩
  have hcos : 0 < Real.cos p.α :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hαlt⟩
  have hsin : 0 ≤ Real.sin p.α :=
    Real.sin_nonneg_of_nonneg_of_le_pi hα0
      (by linarith [Real.pi_pos])
  have hangle :=
    angle_coefficient_ge_and_eq hα0 hαlt
  have hu : 0 < interiorU p := by
    unfold interiorU
    have hfirst : 0 < p.R * p.h := mul_pos hR hh
    have hsecond :
        0 ≤ p.R ^ 2 * Real.sin p.α /
          (3 * Real.cos p.α) := by
      positivity
    linarith
  have hwBound :
      p.R ^ 2 * (1 + Real.sqrt 5 / 3) ≤ interiorW p := by
    unfold interiorW
    exact mul_le_mul_of_nonneg_left hangle.1 (sq_nonneg p.R)
  have hw : 0 < interiorW p := by
    have hlower :
        0 < p.R ^ 2 * (1 + Real.sqrt 5 / 3) := by positivity
    exact lt_of_lt_of_le hlower hwBound
  have hvolume :
      volume p = Real.pi * p.R * interiorU p := by
    unfold volume interiorU
    rw [Real.tan_eq_sin_div_cos]
    field_simp [hcos.ne']
  have hsurfaceForm :
      Q = Real.pi * (2 * interiorU p + interiorW p) := by
    calc
      Q = surface p := hsurface.symm
      _ = Real.pi * (2 * interiorU p + interiorW p) := by
        unfold surface interiorU interiorW
        field_simp [hcos.ne']
        ring
  have hpoly :
      0 ≤ (interiorU p - interiorW p) ^ 2 *
        (8 * interiorU p + interiorW p) := by
    positivity
  have hAMGM :
      27 * interiorU p ^ 2 * interiorW p ≤
        (2 * interiorU p + interiorW p) ^ 3 := by
    nlinarith
  have hWStep :
      27 * interiorU p ^ 2 *
          (p.R ^ 2 * (1 + Real.sqrt 5 / 3)) ≤
        27 * interiorU p ^ 2 * interiorW p :=
    mul_le_mul_of_nonneg_left hwBound (by positivity)
  have hglobal :
      27 * Real.pi * (1 + Real.sqrt 5 / 3) * volume p ^ 2 ≤
        Q ^ 3 := by
    calc
      27 * Real.pi * (1 + Real.sqrt 5 / 3) * volume p ^ 2 =
          Real.pi ^ 3 *
            (27 * interiorU p ^ 2 *
              (p.R ^ 2 * (1 + Real.sqrt 5 / 3))) := by
        rw [hvolume]
        ring
      _ ≤ Real.pi ^ 3 *
          (27 * interiorU p ^ 2 * interiorW p) :=
        mul_le_mul_of_nonneg_left hWStep (by positivity)
      _ ≤ Real.pi ^ 3 *
          (2 * interiorU p + interiorW p) ^ 3 :=
        mul_le_mul_of_nonneg_left hAMGM (by positivity)
      _ = Q ^ 3 := by
        rw [hsurfaceForm]
        ring
  have hden :
      0 < 27 * Real.pi * (1 + Real.sqrt 5 / 3) := by positivity
  have hsqBound :
      volume p ^ 2 ≤ maximumVolume Q ^ 2 := by
    rw [maximumVolume_sq_identity Q hQ.le]
    apply (le_div_iff₀ hden).2
    simpa [mul_assoc, mul_left_comm, mul_comm] using hglobal
  have hvolumeNonneg :
      0 ≤ volume p :=
    volume_nonnegative_of_feasible
      ⟨hR, hh, hα0, hαlt, hsurface⟩
  have hmaximumNonneg : 0 ≤ maximumVolume Q := by
    rw [← gap11 Q hQ]
    exact volume_nonnegative_of_feasible (gap10 Q hQ).choose_spec.1
  refine ⟨(sq_le_sq₀ hvolumeNonneg hmaximumNonneg).mp hsqBound, ?_⟩
  intro hvolumeEq
  have hglobalEq :
      27 * Real.pi * (1 + Real.sqrt 5 / 3) * volume p ^ 2 =
        Q ^ 3 := by
    rw [hvolumeEq, maximumVolume_sq_identity Q hQ.le]
    field_simp [hden.ne']
  have hleftEq :
      Real.pi ^ 3 *
          (27 * interiorU p ^ 2 *
            (p.R ^ 2 * (1 + Real.sqrt 5 / 3))) =
        Q ^ 3 := by
    calc
      Real.pi ^ 3 *
          (27 * interiorU p ^ 2 *
            (p.R ^ 2 * (1 + Real.sqrt 5 / 3))) =
          27 * Real.pi * (1 + Real.sqrt 5 / 3) *
            volume p ^ 2 := by
        rw [hvolume]
        ring
      _ = Q ^ 3 := hglobalEq
  have hrightEq :
      Real.pi ^ 3 *
          (2 * interiorU p + interiorW p) ^ 3 =
        Q ^ 3 := by
    rw [hsurfaceForm]
    ring
  have hfirstEq :
      Real.pi ^ 3 *
          (27 * interiorU p ^ 2 *
            (p.R ^ 2 * (1 + Real.sqrt 5 / 3))) =
        Real.pi ^ 3 *
          (27 * interiorU p ^ 2 * interiorW p) := by
    apply le_antisymm
    · exact mul_le_mul_of_nonneg_left hWStep (by positivity)
    · calc
        Real.pi ^ 3 *
            (27 * interiorU p ^ 2 * interiorW p) ≤
            Real.pi ^ 3 *
              (2 * interiorU p + interiorW p) ^ 3 :=
          mul_le_mul_of_nonneg_left hAMGM (by positivity)
        _ = Q ^ 3 := hrightEq
        _ = Real.pi ^ 3 *
            (27 * interiorU p ^ 2 *
              (p.R ^ 2 * (1 + Real.sqrt 5 / 3))) :=
          hleftEq.symm
  have hsecondEq :
      Real.pi ^ 3 *
          (27 * interiorU p ^ 2 * interiorW p) =
        Real.pi ^ 3 *
          (2 * interiorU p + interiorW p) ^ 3 := by
    apply le_antisymm
    · exact mul_le_mul_of_nonneg_left hAMGM (by positivity)
    · calc
        Real.pi ^ 3 *
            (2 * interiorU p + interiorW p) ^ 3 =
            Q ^ 3 := hrightEq
        _ = Real.pi ^ 3 *
            (27 * interiorU p ^ 2 *
              (p.R ^ 2 * (1 + Real.sqrt 5 / 3))) :=
          hleftEq.symm
        _ ≤ Real.pi ^ 3 *
            (27 * interiorU p ^ 2 * interiorW p) :=
          mul_le_mul_of_nonneg_left hWStep (by positivity)
  have hwEq :
      interiorW p =
        p.R ^ 2 * (1 + Real.sqrt 5 / 3) := by
    have hscaled :
        (Real.pi ^ 3 * (27 * interiorU p ^ 2)) *
            (p.R ^ 2 * (1 + Real.sqrt 5 / 3)) =
          (Real.pi ^ 3 * (27 * interiorU p ^ 2)) *
            interiorW p := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using hfirstEq
    exact (mul_left_cancel₀ (by positivity :
      Real.pi ^ 3 * (27 * interiorU p ^ 2) ≠ 0) hscaled).symm
  have hcoefficientEq :
      1 + (1 - 2 * Real.sin p.α / 3) / Real.cos p.α =
        1 + Real.sqrt 5 / 3 := by
    unfold interiorW at hwEq
    exact mul_left_cancel₀ (pow_ne_zero 2 hR.ne') hwEq
  have hsinEq : Real.sin p.α = 2 / 3 :=
    hangle.2 hcoefficientEq
  have hAMGMEq :
      27 * interiorU p ^ 2 * interiorW p =
        (2 * interiorU p + interiorW p) ^ 3 := by
    exact mul_left_cancel₀ (pow_ne_zero 3 Real.pi_ne_zero) hsecondEq
  have hfactorEq :
      (interiorU p - interiorW p) ^ 2 *
          (8 * interiorU p + interiorW p) = 0 := by
    nlinarith
  have huWEq : interiorU p = interiorW p := by
    have hsqzero :=
      (mul_eq_zero.mp hfactorEq).resolve_right
        (by positivity : 8 * interiorU p + interiorW p ≠ 0)
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp hsqzero)
  exact ⟨hsinEq, huWEq⟩

private theorem feasible_eq_candidate_of_volume_eq
    (Q : ℝ) (hQ : 0 < Q) (p : Params)
    (hp : feasible Q p) (hvolumeEq : volume p = maximumVolume Q) :
    p = candidate Q := by
  have hdata :=
    (feasible_volume_bound_data Q hQ p hp).2 hvolumeEq
  rcases hdata with ⟨hsinEq, huWEq⟩
  rcases hp with ⟨hR, hh, hα0, hαlt, hsurface⟩
  have hcosPos : 0 < Real.cos p.α :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hαlt⟩
  have hcosEq : Real.cos p.α = Real.sqrt 5 / 3 := by
    have htrig := Real.sin_sq_add_cos_sq p.α
    have h5pos : 0 < Real.sqrt 5 := Real.sqrt_pos.2 (by norm_num)
    rw [hsinEq] at htrig
    nlinarith [sqrt_five_sq]
  have hαEq :
      p.α = Real.arcsin (2 / 3) := by
    have harcsin :=
      Real.arcsin_sin
        (show -(Real.pi / 2) ≤ p.α by
          linarith [Real.pi_pos])
        (le_of_lt hαlt)
    rw [hsinEq] at harcsin
    exact harcsin.symm
  have hsqrt : Real.sqrt 5 ≠ 0 :=
    (Real.sqrt_pos.2 (by norm_num)).ne'
  have hRhEq :
      p.R * p.h =
        p.R ^ 2 + p.R ^ 2 / Real.sqrt 5 := by
    unfold interiorU interiorW at huWEq
    rw [hsinEq, hcosEq] at huWEq
    field_simp [hsqrt] at huWEq ⊢
    nlinarith [sqrt_five_sq]
  have hhEq :
      p.h = (1 + 1 / Real.sqrt 5) * p.R := by
    have hscaled :
        p.R * p.h =
          p.R * ((1 + 1 / Real.sqrt 5) * p.R) := by
      rw [hRhEq]
      ring
    exact mul_left_cancel₀ hR.ne' hscaled
  have htanEq : Real.tan p.α = 2 / Real.sqrt 5 := by
    rw [Real.tan_eq_sin_div_cos, hsinEq, hcosEq]
    field_simp [hsqrt]
  have hcrit :
      critical Q p ((3 / 2 : ℝ) * p.R) := by
    refine ⟨⟨hR, hh, hα0, hαlt, hsurface⟩, ?_, ?_, ?_⟩
    · rw [hsinEq, hcosEq]
      field_simp [hsqrt]
      ring
    · ring
    · rw [hhEq, htanEq, hcosEq]
      field_simp [hsqrt]
      ring
  have hREq :
      p.R = candidateRadius Q :=
    gap9 Q ((3 / 2 : ℝ) * p.R) hQ p hcrit
  calc
    p = ⟨p.α, p.h, p.R⟩ := by rfl
    _ = ⟨Real.arcsin (2 / 3),
        (1 + 1 / Real.sqrt 5) * candidateRadius Q,
        candidateRadius Q⟩ := by
      rw [hαEq, hhEq, hREq]
    _ = candidate Q := rfl

theorem gap21 (Q : ℝ) (hQ : 0 < Q) :
    maximizers Q = ({candidate Q} : Set Params) := by
  have hcandidateFeasible : feasible Q (candidate Q) :=
    (gap10 Q hQ).choose_spec.1
  ext p
  constructor
  · intro hp
    rcases hp with ⟨hpFeasible, hpMaximal⟩
    have hpUpper :=
      (feasible_volume_bound_data Q hQ p hpFeasible).1
    have hcandidateLower :=
      hpMaximal (candidate Q) hcandidateFeasible
    have hpVolumeEq :
        volume p = maximumVolume Q := by
      apply le_antisymm hpUpper
      rw [← gap11 Q hQ]
      exact hcandidateLower
    have hpEq :=
      feasible_eq_candidate_of_volume_eq Q hQ p
        hpFeasible hpVolumeEq
    simpa using hpEq
  · intro hp
    have hpEq : p = candidate Q := by
      simpa using hp
    rw [hpEq]
    refine ⟨hcandidateFeasible, ?_⟩
    intro q hq
    rw [gap11 Q hQ]
    exact (feasible_volume_bound_data Q hQ q hq).1

end

end ProofGap.Exercise3690
