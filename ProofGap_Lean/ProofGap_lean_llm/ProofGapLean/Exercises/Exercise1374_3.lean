import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FunProp
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Topology.Neighborhoods

namespace ProofGap.Exercise1374_3

noncomputable section

open Filter

def originalNumerator (x : ℝ) : ℝ :=
  Real.exp (-2 * x) * (Real.cos x + 2 * Real.sin x) +
    Real.exp (-x ^ 2) * Real.sin x ^ 2

def originalDenominator (x : ℝ) : ℝ :=
  Real.exp (-x) * (Real.cos x + Real.sin x)

def derivativeRatio (x : ℝ) : ℝ :=
  (-5 * Real.exp (-2 * x) * Real.sin x -
      2 * x * Real.exp (-x ^ 2) * Real.sin x ^ 2 +
      Real.exp (-x ^ 2) * Real.sin (2 * x)) /
    (-2 * Real.exp (-x) * Real.sin x)

def simplifiedRatio (x : ℝ) : ℝ :=
  (5 / 2 : ℝ) * Real.exp (-x) +
    x * Real.exp (-x ^ 2 + x) * Real.sin x -
    Real.exp (-x ^ 2 + x) * Real.cos x

def quotient (x : ℝ) : ℝ := originalNumerator x / originalDenominator x

def sample (n : ℕ) : ℝ := (n : ℝ) * Real.pi + 3 * Real.pi / 4

def SameLimitAtTop (u v : ℝ → ℝ) : Prop :=
  ∀ L : ℝ, Tendsto u atTop (nhds L) ↔ Tendsto v atTop (nhds L)

private theorem sin_cast_add_one_mul_pi (n : ℕ) :
    Real.sin (((n : ℝ) + 1) * Real.pi) = 0 := by
  rw [add_mul, one_mul, Real.sin_add, Real.sin_nat_mul_pi, Real.sin_pi]
  ring

private theorem denominator_identity (x : ℝ) :
    originalDenominator x =
      Real.sqrt 2 * Real.exp (-x) * Real.sin (x + Real.pi / 4) := by
  unfold originalDenominator
  rw [Real.sin_add, Real.sin_pi_div_four, Real.cos_pi_div_four]
  have hs : Real.sqrt 2 * Real.sqrt 2 = (2 : ℝ) := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  calc
    Real.exp (-x) * (Real.cos x + Real.sin x) =
        Real.exp (-x) *
          ((Real.sqrt 2 * Real.sqrt 2) / 2 *
            (Real.sin x + Real.cos x)) := by rw [hs]; ring
    _ = Real.sqrt 2 * Real.exp (-x) *
          (Real.sin x * (Real.sqrt 2 / 2) +
            Real.cos x * (Real.sqrt 2 / 2)) := by ring

private theorem sample_angle (n : ℕ) :
    sample n + Real.pi / 4 = ((n + 1 : ℕ) : ℝ) * Real.pi := by
  unfold sample
  norm_num
  ring

private theorem denominator_sample_zero (n : ℕ) :
    originalDenominator (sample n) = 0 := by
  have hs : Real.sin (((n + 1 : ℕ) : ℝ) * Real.pi) = 0 := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      sin_cast_add_one_mul_pi n
  rw [denominator_identity, sample_angle, hs]
  ring

private theorem sample_above_two (n : ℕ) : (2 : ℝ) < sample n := by
  have hnpi : 0 ≤ (n : ℝ) * Real.pi :=
    mul_nonneg (Nat.cast_nonneg n) (le_of_lt Real.pi_pos)
  unfold sample
  nlinarith [Real.pi_gt_three]

private theorem numerator_sample_ne_zero (n : ℕ) :
    originalNumerator (sample n) ≠ 0 := by
  let a : ℝ := sample n
  have ha : 2 < a := by simpa [a] using sample_above_two n
  have hroot : Real.sin (a + Real.pi / 4) = 0 := by
    rw [show a + Real.pi / 4 = ((n + 1 : ℕ) : ℝ) * Real.pi by
      simpa [a] using sample_angle n]
    simpa only [Nat.cast_add, Nat.cast_one] using
      sin_cast_add_one_mul_pi n
  have hsqrt : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hfac :
      (Real.sqrt 2 / 2) * (Real.sin a + Real.cos a) = 0 := by
    calc
      (Real.sqrt 2 / 2) * (Real.sin a + Real.cos a) =
          Real.sin a * (Real.sqrt 2 / 2) +
            Real.cos a * (Real.sqrt 2 / 2) := by ring
      _ = Real.sin (a + Real.pi / 4) := by
        rw [Real.sin_add, Real.sin_pi_div_four, Real.cos_pi_div_four]
      _ = 0 := hroot
  have hsum : Real.cos a + Real.sin a = 0 := by
    have hne : Real.sqrt 2 / 2 ≠ 0 := div_ne_zero (ne_of_gt hsqrt) (by norm_num)
    have := (mul_eq_zero.mp hfac).resolve_left hne
    linarith
  have hcos : Real.cos a = -Real.sin a := by linarith
  have hsq : Real.sin a ^ 2 = (1 / 2 : ℝ) := by
    have htrig := Real.sin_sq_add_cos_sq a
    rw [hcos] at htrig
    nlinarith
  have hform :
      originalNumerator a =
        Real.exp (-2 * a) * Real.sin a + Real.exp (-a ^ 2) / 2 := by
    unfold originalNumerator
    rw [hcos, hsq]
    ring
  by_cases hsin : 0 ≤ Real.sin a
  · have hfirst : 0 ≤ Real.exp (-2 * a) * Real.sin a :=
      mul_nonneg (le_of_lt (Real.exp_pos _)) hsin
    have hsecond : 0 < Real.exp (-a ^ 2) / 2 := by positivity
    rw [hform]
    nlinarith
  · have hsinneg : Real.sin a < 0 := lt_of_not_ge hsin
    have hminus : (1 / 2 : ℝ) < -Real.sin a := by
      nlinarith [hsq]
    have hminus' : (2 : ℝ)⁻¹ < -Real.sin a := by
      simpa only [one_div] using hminus
    have hexparg : -a ^ 2 < -2 * a := by nlinarith
    have hexp : Real.exp (-a ^ 2) < Real.exp (-2 * a) :=
      Real.exp_lt_exp.mpr hexparg
    have hdom1 :
        Real.exp (-2 * a) / 2 <
          Real.exp (-2 * a) * (-Real.sin a) := by
      exact mul_lt_mul_of_pos_left hminus' (Real.exp_pos _)
    have hdom2 :
        Real.exp (-a ^ 2) / 2 < Real.exp (-2 * a) / 2 := by
      nlinarith
    rw [hform]
    nlinarith

private theorem sample_tendsto_atTop : Tendsto sample atTop atTop := by
  refine tendsto_atTop.2 ?_
  intro b
  obtain ⟨n, hn⟩ := exists_nat_gt ((b - 3 * Real.pi / 4) / Real.pi)
  filter_upwards [eventually_ge_atTop n] with m hm
  have hcast : (n : ℝ) ≤ (m : ℝ) := Nat.cast_le.2 hm
  have hnpi : b < (n : ℝ) * Real.pi + 3 * Real.pi / 4 := by
    have hp := Real.pi_pos
    have hmul := mul_lt_mul_of_pos_right hn hp
    field_simp at hmul
    nlinarith
  have hmono :
      (n : ℝ) * Real.pi ≤ (m : ℝ) * Real.pi :=
    mul_le_mul_of_nonneg_right hcast (le_of_lt Real.pi_pos)
  unfold sample
  linarith

private theorem simplifiedRatio_tendsto_zero :
    Tendsto simplifiedRatio atTop (nhds 0) := by
  have he : Tendsto (fun x : ℝ => Real.exp (-x)) atTop (nhds 0) :=
    Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot
  have hxe : Tendsto (fun x : ℝ => x * Real.exp (-x)) atTop (nhds 0) := by
    simpa [pow_one] using
      (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1)
  have hsinNorm :
      Tendsto
        (fun x : ℝ => ‖x * Real.exp (-x ^ 2 + x) * Real.sin x‖)
        atTop (nhds 0) := by
    refine squeeze_zero' ?_ ?_ hxe
    · filter_upwards [] with x
      exact norm_nonneg _
    · filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx
      have hx0 : 0 ≤ x := by linarith
      have hexp_le : Real.exp (-x ^ 2 + x) ≤ Real.exp (-x) :=
        Real.exp_le_exp.mpr (by nlinarith)
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hx0,
        abs_of_pos (Real.exp_pos _)]
      calc
        x * Real.exp (-x ^ 2 + x) * |Real.sin x| ≤
            x * Real.exp (-x ^ 2 + x) * 1 :=
          mul_le_mul_of_nonneg_left (Real.abs_sin_le_one x)
            (mul_nonneg hx0 (le_of_lt (Real.exp_pos _)))
        _ = x * Real.exp (-x ^ 2 + x) := by ring
        _ ≤ x * Real.exp (-x) :=
          mul_le_mul_of_nonneg_left hexp_le hx0
  have hsinTerm :
      Tendsto
        (fun x : ℝ => x * Real.exp (-x ^ 2 + x) * Real.sin x)
        atTop (nhds 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simpa using hsinNorm
  have hcosNorm :
      Tendsto
        (fun x : ℝ => ‖Real.exp (-x ^ 2 + x) * Real.cos x‖)
        atTop (nhds 0) := by
    refine squeeze_zero' ?_ ?_ he
    · filter_upwards [] with x
      exact norm_nonneg _
    · filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx
      have hexp_le : Real.exp (-x ^ 2 + x) ≤ Real.exp (-x) :=
        Real.exp_le_exp.mpr (by nlinarith)
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
      calc
        Real.exp (-x ^ 2 + x) * |Real.cos x| ≤
            Real.exp (-x ^ 2 + x) * 1 :=
          mul_le_mul_of_nonneg_left (Real.abs_cos_le_one x)
            (le_of_lt (Real.exp_pos _))
        _ = Real.exp (-x ^ 2 + x) := by ring
        _ ≤ Real.exp (-x) := hexp_le
  have hcosTerm :
      Tendsto
        (fun x : ℝ => Real.exp (-x ^ 2 + x) * Real.cos x)
        atTop (nhds 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simpa using hcosNorm
  have hc :
      Tendsto (fun _ : ℝ => (5 / 2 : ℝ)) atTop (nhds (5 / 2 : ℝ)) :=
    tendsto_const_nhds
  unfold simplifiedRatio
  simpa only [mul_zero, add_zero, sub_zero] using
    ((hc.mul he).add hsinTerm).sub hcosTerm

private theorem derivativeRatio_eq_simplifiedRatio_of_sin_ne_zero
    (x : ℝ) (hsin : Real.sin x ≠ 0) :
    derivativeRatio x = simplifiedRatio x := by
  have he1 : Real.exp (-2 * x) = Real.exp (-x) * Real.exp (-x) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have he2 :
      Real.exp (-x ^ 2) = Real.exp (-x) * Real.exp (-x ^ 2 + x) := by
    rw [← Real.exp_add]
    congr 1
    ring
  unfold derivativeRatio simplifiedRatio
  rw [he1, he2, Real.sin_two_mul]
  field_simp [hsin, Real.exp_ne_zero]
  ring

private theorem derivativeRatio_tendsto_zero :
    Tendsto derivativeRatio atTop (nhds 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero' (g := fun x : ℝ => ‖simplifiedRatio x‖) ?_ ?_ ?_
  · filter_upwards [] with x
    exact norm_nonneg _
  · filter_upwards [] with x
    by_cases hsin : Real.sin x = 0
    · have hz : derivativeRatio x = 0 := by
        simp [derivativeRatio, hsin, Real.sin_two_mul]
      simpa [hz] using (norm_nonneg (simplifiedRatio x))
    · rw [derivativeRatio_eq_simplifiedRatio_of_sin_ne_zero x hsin]
  · simpa using simplifiedRatio_tendsto_zero.norm

private theorem quotient_has_no_finite_limit :
    ¬ ∃ L : ℝ, Tendsto quotient atTop (nhds L) := by
  rintro ⟨L, hL⟩
  let M : ℝ := |L| + 1
  have hM : 0 < M := by dsimp [M]; positivity
  have hnear : ∀ᶠ x in atTop, dist (quotient x) L < 1 :=
    (Metric.tendsto_nhds.1 hL) 1 zero_lt_one
  rcases eventually_atTop.1 hnear with ⟨A, hA⟩
  have hsamp : ∀ᶠ n in atTop, A + 1 < sample n :=
    sample_tendsto_atTop.eventually (eventually_gt_atTop (A + 1))
  rcases hsamp.exists with ⟨n, hn⟩
  let a : ℝ := sample n
  have haA : A + 1 < a := by simpa [a] using hn
  have hNa : originalNumerator a ≠ 0 := by
    simpa [a] using numerator_sample_ne_zero n
  have hDa : originalDenominator a = 0 := by
    simpa [a] using denominator_sample_zero n
  have hNc : ContinuousAt originalNumerator a := by
    unfold originalNumerator
    fun_prop
  have hDc : ContinuousAt originalDenominator a := by
    unfold originalDenominator
    fun_prop
  have hNaabs : 0 < |originalNumerator a| := abs_pos.mpr hNa
  have hNev :
      ∀ᶠ x in nhds a,
        |originalNumerator x - originalNumerator a| <
          |originalNumerator a| / 2 := by
    have h := (Metric.tendsto_nhds.1 hNc.tendsto)
      (|originalNumerator a| / 2) (by positivity)
    simpa [Real.dist_eq] using h
  have hDev :
      ∀ᶠ x in nhds a,
        |originalDenominator x - originalDenominator a| <
          |originalNumerator a| / (2 * M) := by
    have h := (Metric.tendsto_nhds.1 hDc.tendsto)
      (|originalNumerator a| / (2 * M)) (by positivity)
    simpa [Real.dist_eq] using h
  rcases Metric.mem_nhds_iff.1 (hNev.and hDev) with
    ⟨ε, hε, hsub⟩
  let δ : ℝ := min (ε / 2) (Real.pi / 2)
  have hδ : 0 < δ := by
    dsimp [δ]
    exact lt_min (by positivity) (by positivity)
  have hδε : δ < ε := by
    calc
      δ ≤ ε / 2 := min_le_left _ _
      _ < ε := by linarith
  have hδpi : δ < Real.pi := by
    calc
      δ ≤ Real.pi / 2 := min_le_right _ _
      _ < Real.pi := by nlinarith [Real.pi_pos]
  let x : ℝ := a + δ
  have hxball : x ∈ Metric.ball a ε := by
    rw [Metric.mem_ball, Real.dist_eq]
    change |a + δ - a| < ε
    have heq : a + δ - a = δ := by ring
    rw [heq, abs_of_pos hδ]
    exact hδε
  have hxprops := hsub hxball
  have hNclose := hxprops.1
  have hDclose := hxprops.2
  have haangle :
      a + Real.pi / 4 = ((n + 1 : ℕ) : ℝ) * Real.pi := by
    simpa [a] using sample_angle n
  have hangle :
      x + Real.pi / 4 =
        ((n + 1 : ℕ) : ℝ) * Real.pi + δ := by
    dsimp [x]
    calc
      a + δ + Real.pi / 4 = (a + Real.pi / 4) + δ := by ring
      _ = ((n + 1 : ℕ) : ℝ) * Real.pi + δ := by rw [haangle]
  have hbaseSin :
      Real.sin (((n + 1 : ℕ) : ℝ) * Real.pi) = 0 := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      sin_cast_add_one_mul_pi n
  have hbaseCos :
      Real.cos (((n + 1 : ℕ) : ℝ) * Real.pi) ≠ 0 := by
    intro hz
    have htrig := Real.sin_sq_add_cos_sq
      (((n + 1 : ℕ) : ℝ) * Real.pi)
    rw [hbaseSin, hz] at htrig
    norm_num at htrig
  have hsinδ : 0 < Real.sin δ :=
    Real.sin_pos_of_pos_of_lt_pi hδ hδpi
  have hsinx : Real.sin (x + Real.pi / 4) ≠ 0 := by
    rw [hangle, Real.sin_add, hbaseSin, zero_mul, zero_add]
    exact mul_ne_zero hbaseCos (ne_of_gt hsinδ)
  have hDx : originalDenominator x ≠ 0 := by
    rw [denominator_identity]
    exact mul_ne_zero
      (mul_ne_zero (ne_of_gt (Real.sqrt_pos.2 (by norm_num)))
        (Real.exp_ne_zero _)) hsinx
  have hDsmall :
      |originalDenominator x| < |originalNumerator a| / (2 * M) := by
    simpa [hDa] using hDclose
  have htri :
      |originalNumerator a| ≤
        |originalNumerator x - originalNumerator a| +
          |originalNumerator x| := by
    calc
      |originalNumerator a| =
          |(originalNumerator a - originalNumerator x) +
            originalNumerator x| := by congr 1 <;> ring
      _ ≤ |originalNumerator a - originalNumerator x| +
          |originalNumerator x| := abs_add_le _ _
      _ = |originalNumerator x - originalNumerator a| +
          |originalNumerator x| := by rw [abs_sub_comm]
  have hNlarge :
      |originalNumerator a| / 2 < |originalNumerator x| := by
    linarith
  have hMd :
      M * |originalDenominator x| < |originalNumerator a| / 2 := by
    calc
      M * |originalDenominator x| <
          M * (|originalNumerator a| / (2 * M)) :=
        mul_lt_mul_of_pos_left hDsmall hM
      _ = |originalNumerator a| / 2 := by
        field_simp [ne_of_gt hM]
  have hlarge : M < |quotient x| := by
    have hratio :
        M < |originalNumerator x| / |originalDenominator x| := by
      apply (lt_div_iff₀ (abs_pos.mpr hDx)).2
      exact lt_trans hMd hNlarge
    simpa [quotient, abs_div] using hratio
  have hxA : A ≤ x := by
    dsimp [x]
    linarith
  have hdist := hA x hxA
  have hsmall : |quotient x| < M := by
    have hd : |quotient x - L| < 1 := by
      simpa [Real.dist_eq] using hdist
    calc
      |quotient x| = |(quotient x - L) + L| := by congr 1 <;> ring
      _ ≤ |quotient x - L| + |L| := abs_add_le _ _
      _ < M := by dsimp [M]; linarith
  linarith

theorem gap1 :
    ¬ SameLimitAtTop quotient derivativeRatio := by
  intro hsame
  have hq : Tendsto quotient atTop (nhds 0) :=
    (hsame 0).2 derivativeRatio_tendsto_zero
  exact quotient_has_no_finite_limit ⟨0, hq⟩

theorem gap2 :
    SameLimitAtTop derivativeRatio simplifiedRatio := by
  intro L
  constructor
  · intro h
    have hL : L = 0 := tendsto_nhds_unique h derivativeRatio_tendsto_zero
    simpa [hL] using simplifiedRatio_tendsto_zero
  · intro h
    have hL : L = 0 := tendsto_nhds_unique h simplifiedRatio_tendsto_zero
    simpa [hL] using derivativeRatio_tendsto_zero

theorem gap3 :
    Tendsto simplifiedRatio atTop (nhds 0) := by
  exact simplifiedRatio_tendsto_zero

theorem gap4 :
    Tendsto derivativeRatio atTop (nhds 0) := by
  exact derivativeRatio_tendsto_zero

theorem gap5 :
    Tendsto sample atTop atTop := by
  exact sample_tendsto_atTop

theorem gap6 (n : ℕ) :
    originalDenominator (sample n) =
      Real.sqrt 2 * Real.exp (-(sample n)) *
        Real.sin (sample n + Real.pi / 4) := by
  exact denominator_identity (sample n)

theorem gap7 (n : ℕ) :
    Real.sqrt 2 * Real.exp (-(sample n)) *
        Real.sin (sample n + Real.pi / 4) =
      Real.sqrt 2 * Real.exp (-((n : ℝ) * Real.pi + 3 * Real.pi / 4)) *
        Real.sin (((n : ℝ) + 1) * Real.pi) := by
  simp only [sample]
  rw [show
    (n : ℝ) * Real.pi + 3 * Real.pi / 4 + Real.pi / 4 =
      ((n : ℝ) + 1) * Real.pi by ring]

theorem gap8 (n : ℕ) :
    Real.sqrt 2 * Real.exp (-((n : ℝ) * Real.pi + 3 * Real.pi / 4)) *
      Real.sin (((n : ℝ) + 1) * Real.pi) = 0 := by
  simp only [sin_cast_add_one_mul_pi, mul_zero]

theorem gap9 (n : ℕ) :
    originalDenominator (sample n) = 0 := by
  exact denominator_sample_zero n

theorem gap10 (n : ℕ) :
    originalNumerator (sample n) ≠ 0 := by
  exact numerator_sample_ne_zero n

theorem gap11 :
    ¬ ∃ L : ℝ, Tendsto quotient atTop (nhds L) := by
  exact quotient_has_no_finite_limit

end

end ProofGap.Exercise1374_3
