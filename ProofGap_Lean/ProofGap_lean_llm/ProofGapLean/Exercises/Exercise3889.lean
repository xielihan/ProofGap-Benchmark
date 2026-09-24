import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

namespace ProofGap.Exercise3889

noncomputable section

open Filter MeasureTheory
open scoped FourierTransform Interval

def cutoffWave (A ω : ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  if |t| ≤ 2 * Real.pi * (n : ℝ) / ω then
    A * Real.sin (ω * t)
  else
    0

def sineTransform (f : ℝ → ℝ) (lam : ℝ) : ℝ :=
  2 / Real.pi *
    ∫ ξ in Set.Ioi (0 : ℝ), f ξ * Real.sin (lam * ξ)

private theorem hasDerivAt_sin_linear_div (c x : ℝ) (hc : c ≠ 0) :
    HasDerivAt (fun t : ℝ => Real.sin (c * t) / c) (Real.cos (c * x)) x := by
  convert (((Real.hasDerivAt_sin (c * x)).comp x
    ((hasDerivAt_const x c).mul (hasDerivAt_id x))).div_const c) using 1 <;>
    field_simp [hc] <;> ring

private theorem cutoffRadius_pos (ω : ℝ) (n : ℕ)
    (hω : 0 < ω) (hn : 0 < n) :
    0 < 2 * Real.pi * (n : ℝ) / ω := by
  positivity

private theorem omega_mul_cutoffRadius (ω : ℝ) (n : ℕ)
    (hω : 0 < ω) :
    ω * (2 * Real.pi * (n : ℝ) / ω) =
      (n : ℝ) * (2 * Real.pi) := by
  field_simp [hω.ne']

private theorem sin_nat_mul_two_pi (n : ℕ) :
    Real.sin ((n : ℝ) * (2 * Real.pi)) = 0 := by
  simpa using Real.sin_add_nat_mul_two_pi 0 n

theorem gap1 (A ω : ℝ) (n : ℕ) (hω : 0 < ω) (hn : 0 < n) :
    Continuous (cutoffWave A ω n) := by
  unfold cutoffWave
  refine
    (continuous_const.mul
      (Real.continuous_sin.comp
        (continuous_const.mul continuous_id))).if_le
      continuous_const continuous_id.abs continuous_const ?_
  intro t ht
  let B : ℝ := 2 * Real.pi * (n : ℝ) / ω
  have hB : 0 < B := cutoffRadius_pos ω n hω hn
  by_cases ht0 : 0 ≤ t
  · have hteq : t = B := by
      simpa [B, abs_of_nonneg ht0] using ht
    rw [hteq]
    change A * Real.sin (ω * B) = 0
    have hωB := omega_mul_cutoffRadius ω n hω
    rw [hωB, sin_nat_mul_two_pi]
    ring
  · have ht0' : t ≤ 0 := le_of_not_ge ht0
    rw [abs_of_nonpos ht0'] at ht
    have hteq : t = -B := by
      dsimp [B]
      linarith
    rw [hteq]
    change A * Real.sin (ω * -B) = 0
    have hωB := omega_mul_cutoffRadius ω n hω
    rw [show ω * -B = -(ω * B) by ring, hωB, Real.sin_neg,
      sin_nat_mul_two_pi, neg_zero]
    ring

theorem gap2 (A ω : ℝ) (n : ℕ) (hω : 0 < ω) (hn : 0 < n) :
    Function.Odd (cutoffWave A ω n) := by
  intro t
  by_cases ht : |t| ≤ 2 * Real.pi * (n : ℝ) / ω <;>
    simp [cutoffWave, abs_neg, Real.sin_neg, ht]

theorem gap3 (f : ℝ → ℝ) (lam : ℝ) :
    sineTransform f lam =
      2 / Real.pi *
        ∫ ξ in Set.Ioi (0 : ℝ), f ξ * Real.sin (lam * ξ) := by
  rfl

theorem gap4 (A ω lam : ℝ) (n : ℕ) (hω : 0 < ω) (hn : 0 < n) :
    2 / Real.pi *
        (∫ ξ in Set.Ioi (0 : ℝ),
          cutoffWave A ω n ξ * Real.sin (lam * ξ)) =
      2 * A / Real.pi *
        ∫ ξ in (0 : ℝ)..(2 * Real.pi * (n : ℝ) / ω),
          Real.sin (ω * ξ) * Real.sin (lam * ξ) := by
  let B : ℝ := 2 * Real.pi * (n : ℝ) / ω
  have hB : 0 < B := cutoffRadius_pos ω n hω hn
  let f : ℝ → ℝ := fun ξ =>
    cutoffWave A ω n ξ * Real.sin (lam * ξ)
  have hfcont : Continuous f := by
    dsimp [f]
    exact (gap1 A ω n hω hn).mul
      (Real.continuous_sin.comp
        (continuous_const.mul continuous_id))
  have hf : Integrable f := by
    apply hfcont.integrable_of_hasCompactSupport
    refine
      HasCompactSupport.intro
        (isCompact_Icc : IsCompact (Set.Icc (-B) B)) ?_
    intro ξ hξ
    have hout : ¬|ξ| ≤ B := by
      intro hξB
      exact hξ ⟨neg_le_of_abs_le hξB, le_of_abs_le hξB⟩
    simp [f, cutoffWave, B, hout]
  have hset :
      (∫ ξ in Set.Ioi (0 : ℝ), f ξ) =
        A * ∫ ξ in (0 : ℝ)..B,
          Real.sin (ω * ξ) * Real.sin (lam * ξ) := by
    have himproper :
        Tendsto (fun b : ℝ => ∫ ξ in (0 : ℝ)..b, f ξ)
          Filter.atTop
          (nhds (∫ ξ in Set.Ioi (0 : ℝ), f ξ)) :=
      intervalIntegral_tendsto_integral_Ioi 0 hf.integrableOn tendsto_id
    have hfinite :
        Tendsto (fun b : ℝ => ∫ ξ in (0 : ℝ)..b, f ξ)
          Filter.atTop (nhds (∫ ξ in (0 : ℝ)..B, f ξ)) := by
      refine (tendsto_congr' ?_).2 tendsto_const_nhds
      filter_upwards [Filter.eventually_ge_atTop B] with b hb
      have hzero : (∫ ξ in B..b, f ξ) = 0 := by
        calc
          (∫ ξ in B..b, f ξ) = ∫ ξ in B..b, (0 : ℝ) := by
            apply intervalIntegral.integral_congr
            intro ξ hξ
            rw [Set.uIcc_of_le hb] at hξ
            have hξ0 : 0 ≤ ξ := hB.le.trans hξ.1
            by_cases hξB : ξ ≤ B
            · have heq : ξ = B := le_antisymm hξB hξ.1
              subst ξ
              change
                cutoffWave A ω n B * Real.sin (lam * B) = 0
              have hinside : |B| ≤ B := by rw [abs_of_pos hB]
              have hωB := omega_mul_cutoffRadius ω n hω
              rw [cutoffWave, if_pos (by simpa [B] using hinside)]
              rw [show ω * B = (n : ℝ) * (2 * Real.pi) by
                simpa [B] using hωB, sin_nat_mul_two_pi]
              ring
            · have hout : ¬|ξ| ≤ B := by
                rw [abs_of_nonneg hξ0]
                exact hξB
              simp [f, cutoffWave, B, hout]
          _ = 0 := by simp
      calc
        (∫ ξ in (0 : ℝ)..b, f ξ) =
            (∫ ξ in (0 : ℝ)..B, f ξ) + ∫ ξ in B..b, f ξ := by
          symm
          exact intervalIntegral.integral_add_adjacent_intervals
            (hfcont.intervalIntegrable 0 B)
            (hfcont.intervalIntegrable B b)
        _ = ∫ ξ in (0 : ℝ)..B, f ξ := by rw [hzero, add_zero]
    have heq :
        (∫ ξ in Set.Ioi (0 : ℝ), f ξ) =
          ∫ ξ in (0 : ℝ)..B, f ξ :=
      tendsto_nhds_unique himproper hfinite
    rw [heq, ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro ξ hξ
    rw [Set.uIcc_of_le hB.le] at hξ
    dsimp [f]
    have hinside : |ξ| ≤ B := by
      rw [abs_of_nonneg hξ.1]
      exact hξ.2
    simp [cutoffWave, B, hinside]
    ring
  change 2 / Real.pi * ∫ ξ in Set.Ioi (0 : ℝ), f ξ = _
  rw [hset]
  dsimp [B]
  ring

theorem gap5 (A ω lam : ℝ) (n : ℕ) (hω : 0 < ω) (hn : 0 < n)
    (hres : lam ^ 2 ≠ ω ^ 2) :
    2 * A / Real.pi *
        (∫ ξ in (0 : ℝ)..(2 * Real.pi * (n : ℝ) / ω),
          Real.sin (ω * ξ) * Real.sin (lam * ξ)) =
      2 * A * ω *
          Real.sin (2 * Real.pi * (n : ℝ) * lam / ω) /
        (Real.pi * (lam ^ 2 - ω ^ 2)) := by
  have hm : ω - lam ≠ 0 := by
    intro hz
    apply hres
    have : lam = ω := by linarith
    rw [this]
  have hp : ω + lam ≠ 0 := by
    intro hz
    apply hres
    have : lam = -ω := by linarith
    rw [this]
    ring
  have hs : lam ^ 2 - ω ^ 2 ≠ 0 := sub_ne_zero.mpr hres
  let B : ℝ := 2 * Real.pi * (n : ℝ) / ω
  let F : ℝ → ℝ := fun x =>
    (Real.sin ((ω - lam) * x) / (ω - lam) -
      Real.sin ((ω + lam) * x) / (ω + lam)) / 2
  have hd (x : ℝ) :
      HasDerivAt F (Real.sin (ω * x) * Real.sin (lam * x)) x := by
    have h1 := hasDerivAt_sin_linear_div (ω - lam) x hm
    have h2 := hasDerivAt_sin_linear_div (ω + lam) x hp
    dsimp [F]
    convert (h1.sub h2).div_const 2 using 1
    rw [show (ω - lam) * x = ω * x - lam * x by ring,
      show (ω + lam) * x = ω * x + lam * x by ring,
      Real.cos_sub, Real.cos_add]
    ring
  have hInt :
      (∫ x in (0 : ℝ)..B,
        Real.sin (ω * x) * Real.sin (lam * x)) = F B - F 0 := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · intro x _
      exact hd x
    · exact
        ((Real.continuous_sin.comp
          (continuous_const.mul continuous_id)).mul
          (Real.continuous_sin.comp
            (continuous_const.mul continuous_id))).intervalIntegrable 0 B
  have hωB := omega_mul_cutoffRadius ω n hω
  have hminus :
      Real.sin ((ω - lam) * B) =
        -Real.sin (lam * B) := by
    rw [show (ω - lam) * B = ω * B - lam * B by ring, hωB]
    exact Real.sin_nat_mul_two_pi_sub (lam * B) n
  have hplus :
      Real.sin ((ω + lam) * B) =
        Real.sin (lam * B) := by
    rw [show (ω + lam) * B = lam * B + ω * B by ring, hωB]
    exact Real.sin_add_nat_mul_two_pi (lam * B) n
  rw [show 2 * Real.pi * (n : ℝ) / ω = B by rfl, hInt]
  dsimp [F]
  simp only [mul_zero, Real.sin_zero, zero_div, sub_zero]
  rw [hminus, hplus]
  dsimp [B]
  field_simp [hm, hp, hs, hω.ne', Real.pi_ne_zero]
  ring

theorem gap6 (A ω lam : ℝ) (n : ℕ) (hω : 0 < ω) (hn : 0 < n)
    (hres : lam ^ 2 ≠ ω ^ 2) :
    sineTransform (cutoffWave A ω n) lam =
      2 * A * ω *
          Real.sin (2 * Real.pi * (n : ℝ) * lam / ω) /
        (Real.pi * (lam ^ 2 - ω ^ 2)) := by
  exact (gap3 (cutoffWave A ω n) lam).trans
    ((gap4 A ω lam n hω hn).trans (gap5 A ω lam n hω hn hres))

set_option maxHeartbeats 800000 in
private theorem dimensionlessRatio_abs_le
    (n : ℕ) (hn : 0 < n) (z : ℝ) :
    |Real.sin (2 * Real.pi * (n : ℝ) * z) / (z ^ 2 - 1)| ≤
      2 * Real.pi * (n : ℝ) := by
  let β : ℝ := 2 * Real.pi * (n : ℝ)
  have hβ : 0 < β := by
    dsimp [β]
    positivity
  have hβn : β = (n : ℝ) * (2 * Real.pi) := by
    dsimp [β]
    ring
  have hsinβ : Real.sin β = 0 := by
    rw [hβn]
    simpa using Real.sin_add_nat_mul_two_pi 0 n
  have hcosβ : Real.cos β = 1 := by
    rw [hβn]
    exact Real.cos_nat_mul_two_pi n
  by_cases hz : 0 ≤ z
  · by_cases hz1 : z = 1
    · simp [hz1]
      positivity
    have hzsub : z - 1 ≠ 0 := sub_ne_zero.mpr hz1
    have harg : β * (z - 1) ≠ 0 :=
      mul_ne_zero hβ.ne' hzsub
    have hsin :
        Real.sin (β * z) = Real.sin (β * (z - 1)) := by
      rw [show β * z = β * (z - 1) + β by ring,
        Real.sin_add, hsinβ, hcosβ]
      ring
    have hsq : z ^ 2 - 1 ≠ 0 := by
      intro hzero
      have : z ^ 2 = 1 := by linarith
      apply hz1
      nlinarith [sq_nonneg (z - 1)]
    have heq :
        Real.sin (β * z) / (z ^ 2 - 1) =
          β * Real.sinc (β * (z - 1)) / (z + 1) := by
      rw [hsin]
      simp only [Real.sinc, if_neg harg]
      field_simp [hβ.ne', hzsub, hsq]
      ring
    change |Real.sin (β * z) / (z ^ 2 - 1)| ≤ β
    rw [heq, abs_div, abs_mul, abs_of_pos hβ,
      abs_of_pos (by linarith : 0 < z + 1)]
    have hsinc := Real.abs_sinc_le_one (β * (z - 1))
    have hden : 0 < z + 1 := by linarith
    apply (div_le_iff₀ hden).2
    nlinarith
  · have hzle : z ≤ 0 := le_of_not_ge hz
    by_cases hzm1 : z = -1
    · simp [hzm1]
      positivity
    have hzplus : z + 1 ≠ 0 := by
      intro hzero
      apply hzm1
      linarith
    have hzminus : z - 1 ≠ 0 := by linarith
    have harg : β * (z + 1) ≠ 0 :=
      mul_ne_zero hβ.ne' hzplus
    have hsin :
        Real.sin (β * z) = Real.sin (β * (z + 1)) := by
      rw [show β * z = β * (z + 1) - β by ring,
        Real.sin_sub, hsinβ, hcosβ]
      ring
    have hsq : z ^ 2 - 1 ≠ 0 := by
      intro hzero
      have : z ^ 2 = 1 := by linarith
      apply hzm1
      nlinarith [sq_nonneg (z + 1)]
    have heq :
        Real.sin (β * z) / (z ^ 2 - 1) =
          β * Real.sinc (β * (z + 1)) / (z - 1) := by
      rw [hsin]
      simp only [Real.sinc, if_neg harg]
      field_simp [hβ.ne', hzplus, hzminus, hsq]
      ring
    change |Real.sin (β * z) / (z ^ 2 - 1)| ≤ β
    rw [heq, abs_div, abs_mul, abs_of_pos hβ,
      abs_of_neg (by linarith : z - 1 < 0)]
    rw [show -(z - 1) = 1 - z by ring]
    have hsinc := Real.abs_sinc_le_one (β * (z + 1))
    have hden : 0 < 1 - z := by linarith
    apply (div_le_iff₀ hden).2
    nlinarith

private theorem dimensionlessRatio_integrable
    (n : ℕ) (hn : 0 < n) :
    Integrable
      (fun z : ℝ =>
        Real.sin (2 * Real.pi * (n : ℝ) * z) / (z ^ 2 - 1)) := by
  let β : ℝ := 2 * Real.pi * (n : ℝ)
  have hβ : 0 < β := by
    dsimp [β]
    positivity
  let g : ℝ → ℝ := fun z =>
    (5 * β + 2) * (1 + z ^ 2)⁻¹
  have hg : Integrable g :=
    integrable_inv_one_add_sq.const_mul (5 * β + 2)
  refine hg.mono' (by
    exact
      ((Real.measurable_sin.comp
        ((measurable_const.mul measurable_const).mul measurable_id)).div
          ((measurable_id.pow_const 2).sub
            measurable_const)).aestronglyMeasurable) ?_
  filter_upwards with z
  rw [Real.norm_eq_abs]
  dsimp [g]
  have hden : 0 < 1 + z ^ 2 := by positivity
  by_cases hz : |z| ≤ 2
  · have hz_sq : z ^ 2 ≤ 4 := by
      nlinarith [sq_abs z, sq_nonneg (2 - |z|), abs_nonneg z]
    calc
      |Real.sin (2 * Real.pi * (n : ℝ) * z) / (z ^ 2 - 1)| ≤
          2 * Real.pi * (n : ℝ) :=
        dimensionlessRatio_abs_le n hn z
      _ = β := by rfl
      _ ≤ (5 * β + 2) * (1 + z ^ 2)⁻¹ := by
        rw [inv_eq_one_div, mul_one_div]
        apply (le_div_iff₀ hden).2
        nlinarith
  · have habs : 2 < |z| := lt_of_not_ge hz
    have hz_sq : 4 < z ^ 2 := by
      rw [← sq_abs z]
      nlinarith
    have hden2 : 0 < z ^ 2 - 1 := by linarith
    have hsin :
        |Real.sin (2 * Real.pi * (n : ℝ) * z)| ≤ 1 :=
      Real.abs_sin_le_one _
    rw [abs_div, abs_of_pos hden2]
    calc
      |Real.sin (2 * Real.pi * (n : ℝ) * z)| / (z ^ 2 - 1) ≤
          1 / (z ^ 2 - 1) :=
        (div_le_div_iff_of_pos_right hden2).2 hsin
      _ ≤ 2 / (1 + z ^ 2) := by
        apply (div_le_div_iff₀ hden2 hden).2
        linarith
      _ ≤ (5 * β + 2) * (1 + z ^ 2)⁻¹ := by
        rw [inv_eq_one_div, mul_one_div]
        apply (div_le_div_iff_of_pos_right hden).2
        nlinarith

private theorem waveRatio_integrable
    (ω : ℝ) (n : ℕ) (hω : 0 < ω) (hn : 0 < n) :
    Integrable
      (fun lam : ℝ =>
        Real.sin (2 * Real.pi * (n : ℝ) * lam / ω) /
          (lam ^ 2 - ω ^ 2)) := by
  let q : ℝ → ℝ := fun z =>
    Real.sin (2 * Real.pi * (n : ℝ) * z) / (z ^ 2 - 1)
  have hq : Integrable q := dimensionlessRatio_integrable n hn
  have hscaled : Integrable (fun lam : ℝ => q ((1 / ω) * lam)) :=
    hq.comp_mul_left' (one_div_ne_zero hω.ne')
  have hmul :
      Integrable (fun lam : ℝ => (1 / ω ^ 2) * q ((1 / ω) * lam)) :=
    hscaled.const_mul (1 / ω ^ 2)
  apply hmul.congr
  filter_upwards with lam
  dsimp [q]
  field_simp [hω.ne']

private theorem cutoffWave_hasCompactSupport
    (A ω : ℝ) (n : ℕ) :
    HasCompactSupport (cutoffWave A ω n) := by
  let B : ℝ := 2 * Real.pi * (n : ℝ) / ω
  refine
    HasCompactSupport.intro
      (isCompact_Icc : IsCompact (Set.Icc (-B) B)) ?_
  intro t ht
  have hout : ¬|t| ≤ B := by
    intro htB
    exact ht ⟨neg_le_of_abs_le htB, le_of_abs_le htB⟩
  simp [cutoffWave, B, hout]

private theorem cutoffWave_integrable
    (A ω : ℝ) (n : ℕ) (hω : 0 < ω) (hn : 0 < n) :
    Integrable (cutoffWave A ω n) :=
  (gap1 A ω n hω hn).integrable_of_hasCompactSupport
    (cutoffWave_hasCompactSupport A ω n)

private theorem cutoffWave_sin_integrable
    (A ω k : ℝ) (n : ℕ) (hω : 0 < ω) (hn : 0 < n) :
    Integrable
      (fun t : ℝ => cutoffWave A ω n t * Real.sin (k * t)) := by
  apply (cutoffWave_integrable A ω n hω hn).mul_bdd (c := 1)
  · apply Continuous.aestronglyMeasurable
    fun_prop
  · filter_upwards with t
    simpa [Real.norm_eq_abs] using Real.abs_sin_le_one (k * t)

private theorem half_sine_integral
    (A ω k : ℝ) (n : ℕ) (hω : 0 < ω) (hn : 0 < n)
    (hres : k ^ 2 ≠ ω ^ 2) :
    (∫ t in Set.Ioi (0 : ℝ),
        cutoffWave A ω n t * Real.sin (k * t)) =
      A * ω *
        (Real.sin (2 * Real.pi * (n : ℝ) * k / ω) /
          (k ^ 2 - ω ^ 2)) := by
  have heq :=
    (gap4 A ω k n hω hn).trans (gap5 A ω k n hω hn hres)
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have hden : k ^ 2 - ω ^ 2 ≠ 0 := sub_ne_zero.mpr hres
  field_simp [hpi, hden] at heq ⊢
  linarith

private theorem full_sine_integral
    (A ω k : ℝ) (n : ℕ) (hω : 0 < ω) (hn : 0 < n)
    (hres : k ^ 2 ≠ ω ^ 2) :
    (∫ t : ℝ, cutoffWave A ω n t * Real.sin (k * t)) =
      2 * A * ω *
        (Real.sin (2 * Real.pi * (n : ℝ) * k / ω) /
          (k ^ 2 - ω ^ 2)) := by
  let r : ℝ → ℝ := fun t =>
    cutoffWave A ω n t * Real.sin (k * t)
  have hr : Integrable r :=
    cutoffWave_sin_integrable A ω k n hω hn
  have hge (t : ℝ) : r (-t) = r t := by
    dsimp [r]
    rw [gap2 A ω n hω hn t]
    rw [show k * -t = -(k * t) by ring, Real.sin_neg]
    ring
  have habs (t : ℝ) : r |t| = r t := by
    by_cases ht : 0 ≤ t
    · rw [abs_of_nonneg ht]
    · rw [abs_of_neg (lt_of_not_ge ht), hge]
  calc
    (∫ t : ℝ, cutoffWave A ω n t * Real.sin (k * t)) =
        ∫ t : ℝ, r t := by rfl
    _ = ∫ t : ℝ, r |t| := by
      apply integral_congr_ae
      filter_upwards with t
      exact (habs t).symm
    _ = 2 * ∫ t in Set.Ioi (0 : ℝ), r t :=
      integral_comp_abs
    _ = 2 * A * ω *
        (Real.sin (2 * Real.pi * (n : ℝ) * k / ω) /
          (k ^ 2 - ω ^ 2)) := by
      rw [half_sine_integral A ω k n hω hn hres]
      ring

private theorem integral_cosine_zero
    (A ω k : ℝ) (n : ℕ) (hω : 0 < ω) (hn : 0 < n) :
    (∫ t : ℝ, cutoffWave A ω n t * Real.cos (k * t)) = 0 := by
  let r : ℝ → ℝ := fun t =>
    cutoffWave A ω n t * Real.cos (k * t)
  have hr : Integrable r := by
    apply (cutoffWave_integrable A ω n hω hn).mul_bdd (c := 1)
    · apply Continuous.aestronglyMeasurable
      fun_prop
    · filter_upwards with t
      simpa [Real.norm_eq_abs] using Real.abs_cos_le_one (k * t)
  have hneg := integral_neg_eq_self r volume
  have hpoint (t : ℝ) : r (-t) = -r t := by
    dsimp [r]
    rw [gap2 A ω n hω hn t]
    rw [show k * -t = -(k * t) by ring, Real.cos_neg]
    ring
  simp_rw [hpoint, integral_neg] at hneg
  change (∫ t : ℝ, r t) = 0
  linarith

private def cf (A ω : ℝ) (n : ℕ) (t : ℝ) : ℂ :=
  (cutoffWave A ω n t : ℝ)

private theorem cf_integrable
    (A ω : ℝ) (n : ℕ) (hω : 0 < ω) (hn : 0 < n) :
    Integrable (cf A ω n) :=
  (cutoffWave_integrable A ω n hω hn).ofReal

private theorem cf_fourier
    (A ω w : ℝ) (n : ℕ) (hω : 0 < ω) (hn : 0 < n)
    (hw : (2 * Real.pi * w) ^ 2 ≠ ω ^ 2) :
    𝓕 (cf A ω n) w =
      -((2 * A * ω *
        (Real.sin
          (2 * Real.pi * (n : ℝ) * (2 * Real.pi * w) / ω) /
          ((2 * Real.pi * w) ^ 2 - ω ^ 2)) : ℝ) : ℂ) *
        Complex.I := by
  let q : ℝ :=
    2 * A * ω *
      (Real.sin
        (2 * Real.pi * (n : ℝ) * (2 * Real.pi * w) / ω) /
        ((2 * Real.pi * w) ^ 2 - ω ^ 2))
  change 𝓕 (cf A ω n) w = -(q : ℂ) * Complex.I
  rw [Real.fourier_real_eq_integral_exp_smul]
  simp only [smul_eq_mul]
  let J : ℝ → ℂ := fun t =>
    Complex.exp ((-2 * Real.pi * t * w : ℝ) * Complex.I) *
      cf A ω n t
  change (∫ t : ℝ, J t) = _
  have hJ : Integrable J := by
    apply (cf_integrable A ω n hω hn).bdd_mul (c := 1)
    · apply Continuous.aestronglyMeasurable
      fun_prop
    · filter_upwards with t
      rw [Complex.norm_exp]
      simp
  have hre := integral_re hJ
  have him := integral_im hJ
  change (∫ t : ℝ, (J t).re) = (∫ t : ℝ, J t).re at hre
  change (∫ t : ℝ, (J t).im) = (∫ t : ℝ, J t).im at him
  have hrePoint (t : ℝ) :
      (J t).re =
        cutoffWave A ω n t *
          Real.cos ((2 * Real.pi * w) * t) := by
    dsimp [J, cf]
    rw [Complex.exp_re, Complex.exp_im]
    simp
    ring_nf
  have himPoint (t : ℝ) :
      (J t).im =
        -(cutoffWave A ω n t *
          Real.sin ((2 * Real.pi * w) * t)) := by
    dsimp [J, cf]
    rw [Complex.exp_re, Complex.exp_im]
    simp
    ring_nf
  simp_rw [hrePoint,
    integral_cosine_zero A ω (2 * Real.pi * w) n hω hn] at hre
  simp_rw [himPoint, integral_neg,
    full_sine_integral A ω (2 * Real.pi * w) n hω hn hw] at him
  have hqre : (-((q : ℝ) : ℂ)).re = -q := by norm_cast
  have hqim : (-((q : ℝ) : ℂ)).im = 0 := by norm_cast
  apply Complex.ext
  · rw [Complex.mul_re, hqre, hqim]
    norm_num
    exact hre.symm
  · rw [Complex.mul_im, hqre, hqim]
    norm_num
    dsimp [q]
    exact him.symm

private theorem frequency_nonresonant_ae (ω : ℝ) (hω : 0 < ω) :
    ∀ᵐ w : ℝ, (2 * Real.pi * w) ^ 2 ≠ ω ^ 2 := by
  let c : ℝ := 2 * Real.pi
  have hc : c ≠ 0 :=
    mul_ne_zero (by norm_num) Real.pi_ne_zero
  filter_upwards
    [volume.ae_ne (ω / c), volume.ae_ne (-ω / c)] with w hw₁ hw₂
  intro hsq
  have hfac : (c * w - ω) * (c * w + ω) = 0 := by
    dsimp [c] at hsq ⊢
    nlinarith
  rcases mul_eq_zero.mp hfac with hminus | hplus
  · apply hw₁
    field_simp [hc]
    nlinarith
  · apply hw₂
    field_simp [hc]
    nlinarith

private theorem cf_fourier_integrable
    (A ω : ℝ) (n : ℕ) (hω : 0 < ω) (hn : 0 < n) :
    Integrable (𝓕 (cf A ω n)) := by
  let c : ℝ := 2 * Real.pi
  have hc : c ≠ 0 :=
    mul_ne_zero (by norm_num) Real.pi_ne_zero
  let q : ℝ → ℝ := fun k =>
    Real.sin (2 * Real.pi * (n : ℝ) * k / ω) /
      (k ^ 2 - ω ^ 2)
  have hq : Integrable q := waveRatio_integrable ω n hω hn
  have hscaled : Integrable (fun w : ℝ => q (c * w)) :=
    hq.comp_mul_left' hc
  have hreal :
      Integrable (fun w : ℝ => -(2 * A * ω * q (c * w))) :=
    (hscaled.const_mul (2 * A * ω)).neg
  have hcomplex :
      Integrable
        (fun w : ℝ =>
          ((-(2 * A * ω * q (c * w)) : ℝ) : ℂ) * Complex.I) :=
    hreal.ofReal.mul_const Complex.I
  apply hcomplex.congr
  filter_upwards [frequency_nonresonant_ae ω hω] with w hw
  dsimp [q, c]
  let r : ℝ :=
    2 * A * ω *
      (Real.sin
        (2 * Real.pi * (n : ℝ) * (2 * Real.pi * w) / ω) /
        ((2 * Real.pi * w) ^ 2 - ω ^ 2))
  change (((-r : ℝ) : ℂ) * Complex.I) = 𝓕 (cf A ω n) w
  have hcast : ((-r : ℝ) : ℂ) = -(r : ℂ) := by
    norm_cast
  rw [hcast]
  dsimp [r]
  exact (cf_fourier A ω w n hω hn hw).symm

private theorem fourier_full_real
    (A ω t : ℝ) (n : ℕ) (hω : 0 < ω) (hn : 0 < n) :
    (∫ w : ℝ,
        2 * A * ω *
          (Real.sin
            (2 * Real.pi * (n : ℝ) * (2 * Real.pi * w) / ω) /
            ((2 * Real.pi * w) ^ 2 - ω ^ 2)) *
          Real.sin (2 * Real.pi * w * t)) =
      cutoffWave A ω n t := by
  have hinv :=
    (cf_integrable A ω n hω hn).fourierInv_fourier_eq
      (cf_fourier_integrable A ω n hω hn)
      (v := t) (by
        unfold cf
        exact
          (Complex.continuous_ofReal.comp
            (gap1 A ω n hω hn)).continuousAt)
  let K : ℝ → ℂ := fun w =>
    Complex.exp (((2 * Real.pi * w * t : ℝ) : ℂ) * Complex.I) *
      𝓕 (cf A ω n) w
  have hinvK : (∫ w : ℝ, K w) = cf A ω n t := by
    rw [Real.fourierInv_eq'] at hinv
    have hinner (v : ℝ) : inner ℝ v t = v * t := by
      change t * v = v * t
      ring
    simp_rw [hinner] at hinv
    simpa [K, smul_eq_mul, RCLike.inner_apply, mul_comm, mul_left_comm,
      mul_assoc] using hinv
  have hK : Integrable K := by
    apply (cf_fourier_integrable A ω n hω hn).bdd_mul (c := 1)
    · apply Continuous.aestronglyMeasurable
      fun_prop
    · filter_upwards with w
      rw [Complex.norm_exp]
      simp
  have hre := integral_re hK
  change (∫ w : ℝ, (K w).re) = (∫ w : ℝ, K w).re at hre
  have hreval := congrArg Complex.re hinvK
  have htotal := hre.trans hreval
  have hpoint :
      ∀ᵐ w : ℝ,
        (K w).re =
          2 * A * ω *
            (Real.sin
              (2 * Real.pi * (n : ℝ) * (2 * Real.pi * w) / ω) /
              ((2 * Real.pi * w) ^ 2 - ω ^ 2)) *
            Real.sin (2 * Real.pi * w * t) := by
    filter_upwards [frequency_nonresonant_ae ω hω] with w hw
    let q : ℝ :=
      2 * A * ω *
        (Real.sin
          (2 * Real.pi * (n : ℝ) * (2 * Real.pi * w) / ω) /
          ((2 * Real.pi * w) ^ 2 - ω ^ 2))
    have hqre : (-((q : ℝ) : ℂ)).re = -q := by norm_cast
    have hqim : (-((q : ℝ) : ℂ)).im = 0 := by norm_cast
    have hFre : (-((q : ℝ) : ℂ) * Complex.I).re = 0 := by
      rw [Complex.mul_re, hqre, hqim]
      norm_num
    have hFim : (-((q : ℝ) : ℂ) * Complex.I).im = -q := by
      rw [Complex.mul_im, hqre, hqim]
      norm_num
    dsimp [K]
    rw [cf_fourier A ω w n hω hn hw]
    change
      (Complex.exp
        (((2 * Real.pi * w * t : ℝ) : ℂ) * Complex.I) *
          (-((q : ℝ) : ℂ) * Complex.I)).re = _
    rw [Complex.mul_re, hFre, hFim, Complex.exp_re, Complex.exp_im]
    dsimp [q]
    simp
    ring
  rw [integral_congr_ae hpoint] at htotal
  have hcfre : (cf A ω n t).re = cutoffWave A ω n t := by
    change (((cutoffWave A ω n t : ℝ) : ℂ)).re =
      cutoffWave A ω n t
    norm_cast
  rw [hcfre] at htotal
  exact htotal

private theorem waveKernel_integrable
    (ω t : ℝ) (n : ℕ) (hω : 0 < ω) (hn : 0 < n) :
    Integrable
      (fun lam : ℝ =>
        (Real.sin (2 * Real.pi * (n : ℝ) * lam / ω) /
          (lam ^ 2 - ω ^ 2)) * Real.sin (lam * t)) := by
  apply (waveRatio_integrable ω n hω hn).mul_bdd (c := 1)
  · apply Continuous.aestronglyMeasurable
    fun_prop
  · filter_upwards with lam
    simpa [Real.norm_eq_abs] using Real.abs_sin_le_one (lam * t)

private theorem inverse_sine_half
    (A ω t : ℝ) (n : ℕ) (hω : 0 < ω) (hn : 0 < n) :
    cutoffWave A ω n t =
      2 * A * ω / Real.pi *
        ∫ lam in Set.Ioi (0 : ℝ),
          (Real.sin (2 * Real.pi * (n : ℝ) * lam / ω) /
              (lam ^ 2 - ω ^ 2)) *
            Real.sin (lam * t) := by
  let g : ℝ → ℝ := fun lam =>
    (Real.sin (2 * Real.pi * (n : ℝ) * lam / ω) /
      (lam ^ 2 - ω ^ 2)) * Real.sin (lam * t)
  have hg : Integrable g := waveKernel_integrable ω t n hω hn
  have hge (lam : ℝ) : g (-lam) = g lam := by
    dsimp [g]
    rw [show 2 * Real.pi * (n : ℝ) * -lam / ω =
      -(2 * Real.pi * (n : ℝ) * lam / ω) by ring,
      show -lam * t = -(lam * t) by ring,
      Real.sin_neg, Real.sin_neg]
    ring
  have habs (lam : ℝ) : g |lam| = g lam := by
    by_cases hlam : 0 ≤ lam
    · rw [abs_of_nonneg hlam]
    · rw [abs_of_neg (lt_of_not_ge hlam), hge]
  have heven :
      (∫ lam : ℝ, g lam) =
        2 * ∫ lam in Set.Ioi (0 : ℝ), g lam := by
    calc
      (∫ lam : ℝ, g lam) =
          ∫ lam : ℝ, g |lam| := by
        apply integral_congr_ae
        filter_upwards with lam
        exact (habs lam).symm
      _ = 2 * ∫ lam in Set.Ioi (0 : ℝ), g lam :=
        integral_comp_abs
  let c : ℝ := 2 * Real.pi
  have hc : 0 < c := mul_pos (by norm_num) Real.pi_pos
  have hscale :
      (∫ w : ℝ, 2 * A * ω * g (c * w)) =
        A * ω / Real.pi * ∫ lam : ℝ, g lam := by
    rw [integral_const_mul, MeasureTheory.Measure.integral_comp_mul_left]
    rw [abs_of_pos (inv_pos.2 hc)]
    dsimp [c]
    field_simp [Real.pi_ne_zero]
  have hfull :
      (∫ w : ℝ, 2 * A * ω * g (c * w)) =
        cutoffWave A ω n t := by
    rw [← fourier_full_real A ω t n hω hn]
    apply integral_congr_ae
    filter_upwards with w
    dsimp [g, c]
    ring
  have hmain :
      A * ω / Real.pi *
          (2 * ∫ lam in Set.Ioi (0 : ℝ), g lam) =
        cutoffWave A ω n t := by
    rw [← heven]
    exact hscale.symm.trans hfull
  change cutoffWave A ω n t =
    2 * A * ω / Real.pi *
      ∫ lam in Set.Ioi (0 : ℝ), g lam
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp [hpi] at hmain ⊢
  linarith

theorem gap7 (A ω t : ℝ) (n : ℕ) (hω : 0 < ω) (hn : 0 < n) :
    cutoffWave A ω n t =
      2 * A * ω / Real.pi *
        ∫ lam in Set.Ioi (0 : ℝ),
          (Real.sin (2 * Real.pi * (n : ℝ) * lam / ω) /
              (lam ^ 2 - ω ^ 2)) *
            Real.sin (lam * t) := by
  exact inverse_sine_half A ω t n hω hn

end

end ProofGap.Exercise3889
