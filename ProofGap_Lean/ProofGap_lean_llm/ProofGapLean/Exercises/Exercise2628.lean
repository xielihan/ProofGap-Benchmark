import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

namespace ProofGap.Exercise2628

noncomputable section

open Filter

def cot (x : ℝ) : ℝ := Real.cos x / Real.sin x

def cotDefect (n : ℕ) : ℝ :=
  1 - cot ((n : ℝ) * Real.pi / (4 * n - 2 : ℕ))

def sinDefect (n : ℕ) : ℝ :=
  1 - Real.sin ((n : ℝ) * Real.pi / (2 * n + 1 : ℕ))

def term (n : ℕ) : ℝ :=
  cot ((n : ℝ) * Real.pi / (4 * n - 2 : ℕ)) -
    Real.sin ((n : ℝ) * Real.pi / (2 * n + 1 : ℕ))

theorem gap1 (n : ℕ) (hn : 1 ≤ n) :
    term n = -cotDefect n + sinDefect n := by
  unfold term cotDefect sinDefect
  ring

theorem gap2 (n : ℕ) (hn : 1 ≤ n) :
    0 < cotDefect n := by
  let x : ℝ := (n : ℝ) * Real.pi / ((4 * n - 2 : ℕ) : ℝ)
  have hDnat : 0 < 4 * n - 2 := by omega
  have hD : 0 < (((4 * n - 2 : ℕ) : ℝ)) := by exact_mod_cast hDnat
  have hDcast : (((4 * n - 2 : ℕ) : ℝ)) = 4 * (n : ℝ) - 2 := by
    rw [Nat.cast_sub (by omega : 2 ≤ 4 * n)]
    push_cast
    ring
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hnone : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hxpos : 0 < x := by
    exact div_pos (mul_pos hnpos Real.pi_pos) hD
  have hxquarter : Real.pi / 4 < x := by
    dsimp only [x]
    rw [div_lt_div_iff₀ (by norm_num : (0 : ℝ) < 4) hD]
    rw [hDcast]
    nlinarith [Real.pi_pos]
  have hxhalf : x ≤ Real.pi / 2 := by
    dsimp only [x]
    rw [div_le_iff₀ hD]
    rw [hDcast]
    nlinarith [Real.pi_pos]
  have hsinpos : 0 < Real.sin x :=
    Real.sin_pos_of_pos_of_lt_pi hxpos (by linarith [Real.pi_pos])
  have hcoslt : Real.cos x < Real.sin x := by
    rw [← Real.sin_pi_div_two_sub]
    apply Real.sin_lt_sin_of_lt_of_le_pi_div_two
    · linarith [Real.pi_pos]
    · exact hxhalf
    · linarith
  unfold cotDefect cot
  change 0 < 1 - Real.cos x / Real.sin x
  rw [sub_pos, div_lt_one hsinpos]
  exact hcoslt

theorem gap3 (n : ℕ) (hn : 1 ≤ n) :
    0 < sinDefect n := by
  let x : ℝ := (n : ℝ) * Real.pi / ((2 * n + 1 : ℕ) : ℝ)
  have hD : 0 < (((2 * n + 1 : ℕ) : ℝ)) := by positivity
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hxpos : 0 < x := div_pos (mul_pos hnpos Real.pi_pos) hD
  have hxhalf : x < Real.pi / 2 := by
    dsimp only [x]
    rw [div_lt_iff₀ hD]
    push_cast
    nlinarith [Real.pi_pos]
  have hsinlt : Real.sin x < 1 := by
    have h := Real.sin_lt_sin_of_lt_of_le_pi_div_two
      (x := x) (y := Real.pi / 2) (by linarith [Real.pi_pos]) le_rfl hxhalf
    simpa using h
  unfold sinDefect
  change 0 < 1 - Real.sin x
  linarith

private def scale (n : ℕ) : ℝ :=
  1 / ((n + 1 : ℕ) : ℝ)

private def cotDelta (n : ℕ) : ℝ :=
  Real.pi / (8 * (n : ℝ) + 4)

private def sinDelta (n : ℕ) : ℝ :=
  Real.pi / (4 * (n : ℝ) + 6)

private theorem scale_pos (n : ℕ) : 0 < scale n := by
  unfold scale
  positivity

private theorem scale_tendsto_zero :
    Tendsto scale atTop (nhds 0) := by
  change Tendsto (fun n : ℕ => 1 / (((n + 1 : ℕ) : ℝ))) atTop (nhds 0)
  simpa only [Nat.cast_add, Nat.cast_one, one_div] using
    (tendsto_one_div_add_atTop_nhds_zero_nat :
      Tendsto (fun n : ℕ => (1 : ℝ) / (n + 1)) atTop (nhds 0))

private theorem cotDelta_over_scale_tendsto :
    Tendsto (fun n : ℕ => cotDelta n / scale n) atTop
      (nhds (Real.pi / 8)) := by
  have hden : Tendsto (fun n : ℕ => 8 - 4 * scale n) atTop (nhds (8 : ℝ)) := by
    have hconst8 : Tendsto (fun _ : ℕ => (8 : ℝ)) atTop (nhds 8) :=
      tendsto_const_nhds
    have hconst4 : Tendsto (fun _ : ℕ => (4 : ℝ)) atTop (nhds 4) :=
      tendsto_const_nhds
    have h := hconst8.sub (hconst4.mul scale_tendsto_zero)
    norm_num at h ⊢
    exact h
  have hlim : Tendsto (fun n : ℕ => Real.pi / (8 - 4 * scale n)) atTop
      (nhds (Real.pi / 8)) :=
    tendsto_const_nhds.div hden (by norm_num)
  apply hlim.congr'
  filter_upwards [] with n
  have hm : 0 < (n : ℝ) + 1 := by positivity
  have hqle : 1 / ((n : ℝ) + 1) ≤ 1 := by
    rw [div_le_one hm]
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := by positivity
    linarith
  have haux : 0 < 8 - 4 * (1 / ((n : ℝ) + 1)) := by nlinarith
  have hdirect : 8 * (n : ℝ) + 4 ≠ 0 := by positivity
  have hdirect' : 4 + (n : ℝ) * 8 ≠ 0 := by positivity
  unfold cotDelta scale
  norm_num only [Nat.cast_add, Nat.cast_one]
  field_simp [hm.ne', haux.ne', hdirect]
  rw [show 8 * ((n : ℝ) + 1) - 4 = 8 * (n : ℝ) + 4 by ring,
    div_self hdirect]

private theorem sinDelta_over_scale_tendsto :
    Tendsto (fun n : ℕ => sinDelta n / scale n) atTop
      (nhds (Real.pi / 4)) := by
  have hden : Tendsto (fun n : ℕ => 4 + 2 * scale n) atTop (nhds (4 : ℝ)) := by
    have hconst4 : Tendsto (fun _ : ℕ => (4 : ℝ)) atTop (nhds 4) :=
      tendsto_const_nhds
    have hconst2 : Tendsto (fun _ : ℕ => (2 : ℝ)) atTop (nhds 2) :=
      tendsto_const_nhds
    have h := hconst4.add (hconst2.mul scale_tendsto_zero)
    norm_num at h ⊢
    exact h
  have hlim : Tendsto (fun n : ℕ => Real.pi / (4 + 2 * scale n)) atTop
      (nhds (Real.pi / 4)) :=
    tendsto_const_nhds.div hden (by norm_num)
  apply hlim.congr'
  filter_upwards [] with n
  have hm : 0 < (n : ℝ) + 1 := by positivity
  have hdirect : 4 * (n : ℝ) + 6 ≠ 0 := by positivity
  unfold sinDelta scale
  norm_num only [Nat.cast_add, Nat.cast_one]
  field_simp [hm.ne', hdirect]
  ring

private theorem cotDelta_tendsto_zero :
    Tendsto cotDelta atTop (nhds 0) := by
  have h := cotDelta_over_scale_tendsto.mul scale_tendsto_zero
  have h' : Tendsto (fun n : ℕ => cotDelta n / scale n * scale n)
      atTop (nhds 0) := by
    norm_num at h ⊢
    exact h
  apply h'.congr'
  filter_upwards [] with n
  field_simp [(scale_pos n).ne']

private theorem sinDelta_tendsto_zero :
    Tendsto sinDelta atTop (nhds 0) := by
  have h := sinDelta_over_scale_tendsto.mul scale_tendsto_zero
  have h' : Tendsto (fun n : ℕ => sinDelta n / scale n * scale n)
      atTop (nhds 0) := by
    norm_num at h ⊢
    exact h
  apply h'.congr'
  filter_upwards [] with n
  field_simp [(scale_pos n).ne']

private theorem cotDelta_ne (n : ℕ) : cotDelta n ≠ 0 := by
  unfold cotDelta
  positivity

private theorem sinDelta_ne (n : ℕ) : sinDelta n ≠ 0 := by
  unfold sinDelta
  positivity

private theorem cot_angle_shift (n : ℕ) :
    ((n + 1 : ℕ) : ℝ) * Real.pi / ((4 * (n + 1) - 2 : ℕ) : ℝ) =
      Real.pi / 4 + cotDelta n := by
  rw [show 4 * (n + 1) - 2 = 4 * n + 2 by omega]
  push_cast
  unfold cotDelta
  have h₁ : 4 * (n : ℝ) + 2 ≠ 0 := by positivity
  have h₂ : 8 * (n : ℝ) + 4 ≠ 0 := by positivity
  field_simp [h₁, h₂]
  ring

private theorem sin_angle_shift (n : ℕ) :
    ((n + 1 : ℕ) : ℝ) * Real.pi / ((2 * (n + 1) + 1 : ℕ) : ℝ) =
      Real.pi / 2 - sinDelta n := by
  push_cast
  unfold sinDelta
  have h₁ : 2 * ((n : ℝ) + 1) + 1 ≠ 0 := by positivity
  have h₂ : 4 * (n : ℝ) + 6 ≠ 0 := by positivity
  field_simp [h₁, h₂]
  ring

private theorem cot_pi_div_four : cot (Real.pi / 4) = 1 := by
  unfold cot
  rw [Real.cos_pi_div_four, Real.sin_pi_div_four]
  exact div_self (by positivity)

private theorem hasDerivAt_cot_pi_div_four :
    HasDerivAt cot (-2) (Real.pi / 4) := by
  unfold cot
  have hs : Real.sin (Real.pi / 4) ≠ 0 := by
    rw [Real.sin_pi_div_four]
    positivity
  convert (Real.hasDerivAt_cos (Real.pi / 4)).div
      (Real.hasDerivAt_sin (Real.pi / 4)) hs using 1
  rw [Real.sin_pi_div_four, Real.cos_pi_div_four]
  field_simp [show Real.sqrt 2 ≠ 0 by positivity]
  ring

private theorem hasDerivAt_cotDefect_aux :
    HasDerivAt (fun x : ℝ => 1 - cot x) 2 (Real.pi / 4) := by
  convert (hasDerivAt_const (Real.pi / 4) (1 : ℝ)).sub
      hasDerivAt_cot_pi_div_four using 1 <;> norm_num

private theorem cotDefect_over_delta_tendsto :
    Tendsto (fun n : ℕ => cotDefect (n + 1) / cotDelta n)
      atTop (nhds 2) := by
  have hdeltaWithin : Tendsto cotDelta atTop (nhdsWithin 0 ({0}ᶜ : Set ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨cotDelta_tendsto_zero,
      Eventually.of_forall (fun n => by simpa using cotDelta_ne n)⟩
  have h := hasDerivAt_cotDefect_aux.tendsto_slope_zero.comp hdeltaWithin
  apply h.congr'
  filter_upwards [] with n
  simp only [Function.comp_apply, cotDefect, cot_angle_shift, cot_pi_div_four,
    sub_self, sub_zero, smul_eq_mul]
  rw [div_eq_mul_inv]
  ring

private theorem one_sub_cos_eq (x : ℝ) :
    1 - Real.cos x = 2 * Real.sin (x / 2) ^ 2 := by
  rw [Real.sin_sq_eq_half_sub]
  congr 2
  ring

private theorem sin_slope_tendsto_one :
    Tendsto (fun n : ℕ => Real.sin (sinDelta n / 2) / (sinDelta n / 2))
      atTop (nhds 1) := by
  have hhalf : Tendsto (fun n : ℕ => sinDelta n / 2) atTop (nhds 0) := by
    simpa using sinDelta_tendsto_zero.div_const 2
  have hhalfWithin : Tendsto (fun n : ℕ => sinDelta n / 2) atTop
      (nhdsWithin 0 ({0}ᶜ : Set ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hhalf,
      Eventually.of_forall (fun n => by
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
        exact div_ne_zero (sinDelta_ne n) (by norm_num))⟩
  have hderiv : HasDerivAt Real.sin 1 0 := by
    simpa using Real.hasDerivAt_sin 0
  have h := hderiv.tendsto_slope_zero.comp hhalfWithin
  apply h.congr'
  filter_upwards [] with n
  simp only [Function.comp_apply, zero_add, Real.sin_zero, sub_zero, smul_eq_mul]
  rw [div_eq_mul_inv]
  ring

private theorem sinDefect_over_delta_sq_tendsto :
    Tendsto (fun n : ℕ => sinDefect (n + 1) / sinDelta n ^ 2)
      atTop (nhds (1 / 2 : ℝ)) := by
  have hconst : Tendsto (fun _ : ℕ => (1 / 2 : ℝ)) atTop (nhds (1 / 2 : ℝ)) :=
    tendsto_const_nhds
  have h := hconst.mul (sin_slope_tendsto_one.pow 2)
  have h' : Tendsto (fun n : ℕ =>
      (1 / 2 : ℝ) * (Real.sin (sinDelta n / 2) / (sinDelta n / 2)) ^ 2)
      atTop (nhds (1 / 2 : ℝ)) := by
    norm_num at h ⊢
    exact h
  apply h'.congr'
  filter_upwards [] with n
  unfold sinDefect
  rw [sin_angle_shift, Real.sin_pi_div_two_sub, one_sub_cos_eq]
  field_simp [sinDelta_ne n]

theorem gap4 :
    Tendsto
      (fun n : ℕ => cotDefect (n + 1) / (1 / ((n + 1 : ℕ) : ℝ)))
      atTop (nhds (Real.pi / 4)) := by
  have h := cotDefect_over_delta_tendsto.mul cotDelta_over_scale_tendsto
  have hscale : Tendsto (fun n : ℕ => cotDefect (n + 1) / scale n)
      atTop (nhds (Real.pi / 4)) := by
    convert h using 1
    · funext n
      field_simp [cotDelta_ne n, (scale_pos n).ne']
    · ring
  simpa [scale] using hscale

theorem gap5 :
    Tendsto
      (fun n : ℕ => sinDefect (n + 1) / (1 / ((n + 1 : ℕ) : ℝ) ^ 2))
      atTop (nhds (Real.pi ^ 2 / 32)) := by
  have h := sinDefect_over_delta_sq_tendsto.mul
    (sinDelta_over_scale_tendsto.pow 2)
  have h' : Tendsto (fun n : ℕ =>
      sinDefect (n + 1) / sinDelta n ^ 2 *
        (sinDelta n / scale n) ^ 2) atTop
      (nhds (Real.pi ^ 2 / 32)) := by
    convert h using 1
    ring
  have hscale : Tendsto (fun n : ℕ => sinDefect (n + 1) / scale n ^ 2)
      atTop (nhds (Real.pi ^ 2 / 32)) := by
    apply h'.congr'
    filter_upwards [] with n
    field_simp [sinDelta_ne n, (scale_pos n).ne']
  simpa [scale] using hscale

theorem gap6 :
    ¬ Summable (fun n : ℕ => 1 / ((n + 1 : ℕ) : ℝ)) := by
  intro hshift
  apply Real.not_summable_one_div_natCast
  exact (summable_nat_add_iff 1).mp hshift

theorem gap7 :
    Summable (fun n : ℕ => 1 / ((n + 1 : ℕ) : ℝ) ^ 2) := by
  have hall : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 2) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  exact (summable_nat_add_iff 1).mpr hall

theorem gap8 :
    ¬ Summable (fun n : ℕ => cotDefect (n + 1)) := by
  let L : ℝ := Real.pi / 4
  have hL : L ≠ 0 := by
    dsimp only [L]
    exact div_ne_zero Real.pi_ne_zero (by norm_num)
  have hratio : Tendsto
      (fun n : ℕ => cotDefect (n + 1) / scale n) atTop (nhds L) := by
    simpa [L, scale] using gap4
  have hratioNe : ∀ᶠ n : ℕ in atTop,
      cotDefect (n + 1) / scale n ≠ 0 :=
    hratio.eventually (eventually_ne_nhds hL)
  have hcotNe : ∀ᶠ n : ℕ in atTop, cotDefect (n + 1) ≠ 0 := by
    filter_upwards [hratioNe] with n hn
    exact (div_ne_zero_iff.mp hn).1
  have hinv := hratio.inv₀ hL
  have hrev : Tendsto
      (fun n : ℕ => scale n / cotDefect (n + 1)) atTop (nhds L⁻¹) := by
    apply hinv.congr'
    filter_upwards [hcotNe] with n hn
    field_simp [hn, (scale_pos n).ne']
  have hO : scale =O[atTop] (fun n : ℕ => cotDefect (n + 1)) := by
    refine Asymptotics.isBigO_of_div_tendsto_nhds ?_ L⁻¹ hrev
    filter_upwards [hcotNe] with n hn hzero
    exact False.elim (hn hzero)
  intro hcot
  apply gap6
  have hscale : Summable scale := summable_of_isBigO_nat hcot hO
  change Summable scale
  exact hscale

theorem gap9 :
    Summable (fun n : ℕ => sinDefect (n + 1)) := by
  have hO : (fun n : ℕ => sinDefect (n + 1)) =O[atTop]
      (fun n : ℕ => 1 / ((n + 1 : ℕ) : ℝ) ^ 2) := by
    refine Asymptotics.isBigO_of_div_tendsto_nhds ?_
      (Real.pi ^ 2 / 32) gap5
    filter_upwards [] with n hzero
    have hbase : 0 < (((n + 1 : ℕ) : ℝ)) := by positivity
    exact False.elim ((one_div_ne_zero (pow_ne_zero 2 hbase.ne')) hzero)
  exact summable_of_isBigO_nat gap7 hO

theorem gap10 :
    ¬ Summable (fun n : ℕ => term (n + 1)) := by
  intro hterm
  apply gap8
  have hcot : Summable (fun n : ℕ => cotDefect (n + 1)) := by
    apply (gap9.sub hterm).congr
    intro n
    rw [gap1 (n + 1) (by omega)]
    ring
  exact hcot

theorem gap11 :
    ¬ Summable (fun n : ℕ => term (n + 1)) := by
  exact gap10

end

end ProofGap.Exercise2628
