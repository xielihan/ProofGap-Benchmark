import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Topology.Neighborhoods

namespace ProofGap.Exercise1374_4

noncomputable section

open Filter

def quotient (x : ℝ) : ℝ :=
  (1 + x + Real.sin x * Real.cos x) /
    ((x + Real.sin x * Real.cos x) * Real.exp (Real.sin x))

def derivativeRatio (x : ℝ) : ℝ :=
  (1 + Real.cos (2 * x)) /
    (Real.exp (Real.sin x) *
      (1 + Real.cos (2 * x) + Real.cos x * (x + Real.sin x * Real.cos x)))

def cosineRatio (x : ℝ) : ℝ :=
  (2 * Real.cos x ^ 2) /
    (Real.exp (Real.sin x) *
      (2 * Real.cos x ^ 2 + Real.cos x * (x + Real.sin x * Real.cos x)))

def dividedRatio (x : ℝ) : ℝ :=
  1 / (Real.exp (Real.sin x) *
    (1 + (1 / (2 * Real.cos x)) * (x + Real.sin x * Real.cos x)))

def sampleA (n : ℕ) : ℝ := 2 * (n : ℝ) * Real.pi + Real.pi / 2
def sampleB (n : ℕ) : ℝ := 2 * (n : ℝ) * Real.pi

def SameLimitAtTop (u v : ℝ → ℝ) : Prop :=
  ∀ L : ℝ, Tendsto u atTop (nhds L) ↔ Tendsto v atTop (nhds L)

private lemma sampleA_sin (n : ℕ) : Real.sin (sampleA n) = 1 := by
  induction n with
  | zero => simp [sampleA]
  | succ n ih =>
      have hstep : sampleA (Nat.succ n) = sampleA n + 2 * Real.pi := by
        simp only [sampleA, Nat.cast_succ]
        ring
      rw [hstep, Real.sin_add, ih, Real.sin_two_pi, Real.cos_two_pi]
      ring

private lemma sampleA_cos (n : ℕ) : Real.cos (sampleA n) = 0 := by
  induction n with
  | zero => simp [sampleA]
  | succ n ih =>
      have hstep : sampleA (Nat.succ n) = sampleA n + 2 * Real.pi := by
        simp only [sampleA, Nat.cast_succ]
        ring
      rw [hstep, Real.cos_add, ih, Real.sin_two_pi, Real.cos_two_pi]
      ring

private lemma sampleB_sin (n : ℕ) : Real.sin (sampleB n) = 0 := by
  induction n with
  | zero => simp [sampleB]
  | succ n ih =>
      have hstep : sampleB (Nat.succ n) = sampleB n + 2 * Real.pi := by
        simp only [sampleB, Nat.cast_succ]
        ring
      rw [hstep, Real.sin_add, ih, Real.sin_two_pi, Real.cos_two_pi]
      ring

private lemma sampleB_cos (n : ℕ) : Real.cos (sampleB n) = 1 := by
  induction n with
  | zero => simp [sampleB]
  | succ n ih =>
      have hstep : sampleB (Nat.succ n) = sampleB n + 2 * Real.pi := by
        simp only [sampleB, Nat.cast_succ]
        ring
      rw [hstep, Real.cos_add, ih, Real.sin_two_pi, Real.cos_two_pi]
      ring

private lemma sampleA_pos (n : ℕ) : 0 < sampleA n := by
  unfold sampleA
  positivity

private lemma sampleB_tendsto_atTop : Tendsto sampleB atTop atTop := by
  refine tendsto_atTop.2 ?_
  intro b
  have hcoef : 0 < 2 * Real.pi := by positivity
  obtain ⟨N, hN⟩ := exists_nat_gt (b / (2 * Real.pi))
  filter_upwards [eventually_ge_atTop N] with n hn
  have hNn : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hbN : b < (N : ℝ) * (2 * Real.pi) :=
    (div_lt_iff₀ hcoef).mp hN
  have hmono : (N : ℝ) * (2 * Real.pi) ≤ (n : ℝ) * (2 * Real.pi) :=
    mul_le_mul_of_nonneg_right hNn hcoef.le
  calc
    b ≤ (N : ℝ) * (2 * Real.pi) := hbN.le
    _ ≤ (n : ℝ) * (2 * Real.pi) := hmono
    _ = sampleB n := by unfold sampleB; ring

private lemma sampleA_tendsto_atTop : Tendsto sampleA atTop atTop := by
  refine tendsto_atTop.2 ?_
  intro b
  filter_upwards [(tendsto_atTop.1 sampleB_tendsto_atTop b)] with n hn
  calc
    b ≤ sampleB n := hn
    _ ≤ sampleA n := by
      unfold sampleA sampleB
      nlinarith [Real.pi_pos]

private lemma quotient_sampleA_tendsto :
    Tendsto (fun n : ℕ => quotient (sampleA n)) atTop
      (nhds (1 / Real.exp 1)) := by
  have hinv : Tendsto (fun n : ℕ => (sampleA n)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp sampleA_tendsto_atTop
  have hone : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1) :=
    tendsto_const_nhds
  have he : Tendsto (fun _ : ℕ => (Real.exp 1)⁻¹) atTop
      (nhds ((Real.exp 1)⁻¹)) := tendsto_const_nhds
  have ht : Tendsto (fun n : ℕ => (1 + (sampleA n)⁻¹) / Real.exp 1)
      atTop (nhds (1 / Real.exp 1)) := by
    simpa [div_eq_mul_inv] using (hone.add hinv).mul he
  have hform :
      (fun n : ℕ => quotient (sampleA n)) =ᶠ[atTop]
        (fun n : ℕ => (1 + (sampleA n)⁻¹) / Real.exp 1) := by
    filter_upwards with n
    simp [quotient, sampleA_sin, sampleA_cos]
    field_simp [ne_of_gt (sampleA_pos n), Real.exp_ne_zero]
    <;> ring
  rw [tendsto_congr' hform]
  exact ht

private lemma quotient_sampleB_tendsto :
    Tendsto (fun n : ℕ => quotient (sampleB n)) atTop (nhds 1) := by
  have hinv : Tendsto (fun n : ℕ => (sampleB n)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp sampleB_tendsto_atTop
  have hone : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1) :=
    tendsto_const_nhds
  have ht : Tendsto (fun n : ℕ => 1 + (sampleB n)⁻¹) atTop (nhds 1) := by
    simpa using hone.add hinv
  have hform :
      (fun n : ℕ => quotient (sampleB n)) =ᶠ[atTop]
        (fun n : ℕ => 1 + (sampleB n)⁻¹) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hnpos : 0 < n := lt_of_lt_of_le Nat.zero_lt_one hn
    have hncast : 0 < (n : ℝ) := by exact_mod_cast hnpos
    have hspos : 0 < sampleB n := by
      unfold sampleB
      positivity
    simp [quotient, sampleB_sin, sampleB_cos]
    field_simp [ne_of_gt hspos]
    <;> ring
  rw [tendsto_congr' hform]
  exact ht

private lemma dividedRatio_sampleA_tendsto :
    Tendsto (fun n : ℕ => dividedRatio (sampleA n)) atTop
      (nhds (1 / Real.exp 1)) := by
  simpa [dividedRatio, sampleA_sin, sampleA_cos] using
    (tendsto_const_nhds :
      Tendsto (fun _ : ℕ => 1 / Real.exp 1) atTop
        (nhds (1 / Real.exp 1)))

private lemma dividedRatio_sampleB_tendsto :
    Tendsto (fun n : ℕ => dividedRatio (sampleB n)) atTop (nhds 0) := by
  have hd : Tendsto (fun n : ℕ => 1 + sampleB n / 2) atTop atTop := by
    refine tendsto_atTop.2 ?_
    intro b
    filter_upwards [(tendsto_atTop.1 sampleB_tendsto_atTop (2 * b))] with n hn
    nlinarith
  have hi : Tendsto (fun n : ℕ => (1 + sampleB n / 2)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp hd
  have hform :
      (fun n : ℕ => dividedRatio (sampleB n)) =ᶠ[atTop]
        (fun n : ℕ => (1 + sampleB n / 2)⁻¹) := by
    filter_upwards with n
    have hden :
        Real.exp (Real.sin (sampleB n)) *
            (1 + (1 / (2 * Real.cos (sampleB n))) *
              (sampleB n + Real.sin (sampleB n) * Real.cos (sampleB n))) =
          1 + sampleB n / 2 := by
      rw [sampleB_sin, sampleB_cos]
      norm_num
      ring
    rw [dividedRatio, hden]
    simp
  rw [tendsto_congr' hform]
  exact hi

private lemma dividedRatio_has_no_limit :
    ¬ ∃ L : ℝ, Tendsto dividedRatio atTop (nhds L) := by
  rintro ⟨L, hL⟩
  have hA : Tendsto (fun n : ℕ => dividedRatio (sampleA n)) atTop
      (nhds L) := by
    simpa [Function.comp_def] using hL.comp sampleA_tendsto_atTop
  have hB : Tendsto (fun n : ℕ => dividedRatio (sampleB n)) atTop
      (nhds L) := by
    simpa [Function.comp_def] using hL.comp sampleB_tendsto_atTop
  have hLA : L = 1 / Real.exp 1 :=
    tendsto_nhds_unique hA dividedRatio_sampleA_tendsto
  have hLB : L = 0 :=
    tendsto_nhds_unique hB dividedRatio_sampleB_tendsto
  have hz : 1 / Real.exp 1 = 0 := hLA.symm.trans hLB
  have hp : 0 < 1 / Real.exp 1 := one_div_pos.mpr (Real.exp_pos 1)
  linarith

private lemma cosineRatio_abs_bound {x : ℝ} (hx : 6 ≤ x) :
    |cosineRatio x| ≤ 4 * Real.exp 1 / x := by
  have hxpos : 0 < x := by linarith
  have hcabs : |Real.cos x| ≤ 1 := Real.abs_cos_le_one x
  have hsabs : |Real.sin x| ≤ 1 := Real.abs_sin_le_one x
  have hscabs : |Real.sin x * Real.cos x| ≤ 1 := by
    calc
      |Real.sin x * Real.cos x| = |Real.sin x| * |Real.cos x| :=
        abs_mul _ _
      _ ≤ 1 * 1 :=
        mul_le_mul hsabs hcabs (abs_nonneg _) (by norm_num)
      _ = 1 := by norm_num
  have hclow : -1 ≤ Real.cos x := neg_le_of_abs_le hcabs
  have hslow : -1 ≤ Real.sin x := neg_le_of_abs_le hsabs
  have hsclow : -1 ≤ Real.sin x * Real.cos x :=
    neg_le_of_abs_le hscabs
  let q := 2 * Real.cos x + x + Real.sin x * Real.cos x
  have hqhalf : x / 2 ≤ q := by
    dsimp [q]
    nlinarith
  have hqpos : 0 < q := lt_of_lt_of_le (half_pos hxpos) hqhalf
  have hexp : Real.exp (-1) ≤ Real.exp (Real.sin x) :=
    Real.exp_le_exp.mpr hslow
  have hlowpos : 0 < Real.exp (-1) * (x / 2) := by positivity
  have hdenlower :
      Real.exp (-1) * (x / 2) ≤ Real.exp (Real.sin x) * q := by
    exact mul_le_mul hexp hqhalf (by positivity) (Real.exp_nonneg _)
  have hdenpos : 0 < Real.exp (Real.sin x) * q :=
    mul_pos (Real.exp_pos _) hqpos
  by_cases hc : Real.cos x = 0
  · simp [cosineRatio, hc]
    positivity
  · have hratio :
        (2 * Real.cos x ^ 2) /
            (Real.exp (Real.sin x) *
              (2 * Real.cos x ^ 2 +
                Real.cos x * (x + Real.sin x * Real.cos x))) =
          (2 * Real.cos x) / (Real.exp (Real.sin x) * q) := by
        dsimp [q]
        field_simp [hc, Real.exp_ne_zero, ne_of_gt hqpos]
        <;> ring
    rw [cosineRatio, hratio, abs_div, abs_of_pos hdenpos]
    have hnum : |2 * Real.cos x| ≤ 2 := by
      rw [abs_mul]
      norm_num
      nlinarith
    have hquot :
        |2 * Real.cos x| / (Real.exp (Real.sin x) * q) ≤
          2 / (Real.exp (-1) * (x / 2)) := by
      gcongr
    calc
      |2 * Real.cos x| / (Real.exp (Real.sin x) * q)
          ≤ 2 / (Real.exp (-1) * (x / 2)) := hquot
      _ = 4 * Real.exp 1 / x := by
        rw [show Real.exp (-1) = (Real.exp 1)⁻¹ by
          simpa using Real.exp_neg 1]
        field_simp [Real.exp_ne_zero, ne_of_gt hxpos]
        <;> ring

private lemma cosineRatio_tendsto_zero :
    Tendsto cosineRatio atTop (nhds 0) := by
  have hinv : Tendsto (fun x : ℝ => x⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero
  have hc : Tendsto (fun _ : ℝ => 4 * Real.exp 1) atTop
      (nhds (4 * Real.exp 1)) := tendsto_const_nhds
  have hg : Tendsto (fun x : ℝ => 4 * Real.exp 1 / x) atTop (nhds 0) := by
    simpa [div_eq_mul_inv] using hc.mul hinv
  have hneg : Tendsto (fun x : ℝ => -(4 * Real.exp 1 / x)) atTop
      (nhds 0) := by
    simpa using hg.neg
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hneg hg ?_ ?_
  · filter_upwards [eventually_ge_atTop (6 : ℝ)] with x hx
    exact neg_le_of_abs_le (cosineRatio_abs_bound hx)
  · filter_upwards [eventually_ge_atTop (6 : ℝ)] with x hx
    exact le_of_abs_le (cosineRatio_abs_bound hx)

private lemma derivativeRatio_eq_cosineRatio :
    derivativeRatio = cosineRatio := by
  funext x
  unfold derivativeRatio cosineRatio
  rw [Real.cos_two_mul]
  ring

private lemma quotient_has_no_limit :
    ¬ ∃ L : ℝ, Tendsto quotient atTop (nhds L) := by
  rintro ⟨L, hL⟩
  have hA : Tendsto (fun n : ℕ => quotient (sampleA n)) atTop
      (nhds L) := by
    simpa [Function.comp_def] using hL.comp sampleA_tendsto_atTop
  have hB : Tendsto (fun n : ℕ => quotient (sampleB n)) atTop
      (nhds L) := by
    simpa [Function.comp_def] using hL.comp sampleB_tendsto_atTop
  have hLA : L = 1 / Real.exp 1 :=
    tendsto_nhds_unique hA quotient_sampleA_tendsto
  have hLB : L = 1 :=
    tendsto_nhds_unique hB quotient_sampleB_tendsto
  have heq : 1 / Real.exp 1 = 1 := hLA.symm.trans hLB
  have he : 1 < Real.exp 1 := by
    simpa using Real.exp_lt_exp.mpr (show (0 : ℝ) < 1 by norm_num)
  field_simp [Real.exp_ne_zero] at heq
  nlinarith

theorem gap1 :
    ¬ SameLimitAtTop quotient derivativeRatio := by
  intro h
  have hd : Tendsto derivativeRatio atTop (nhds 0) := by
    rw [derivativeRatio_eq_cosineRatio]
    exact cosineRatio_tendsto_zero
  have hq : Tendsto quotient atTop (nhds 0) := (h 0).mpr hd
  exact quotient_has_no_limit ⟨0, hq⟩

theorem gap2 :
    SameLimitAtTop derivativeRatio cosineRatio := by
  unfold SameLimitAtTop
  intro L
  rw [derivativeRatio_eq_cosineRatio]

theorem gap3 :
    ¬ SameLimitAtTop cosineRatio dividedRatio := by
  intro h
  have hd : Tendsto dividedRatio atTop (nhds 0) :=
    (h 0).mp cosineRatio_tendsto_zero
  exact dividedRatio_has_no_limit ⟨0, hd⟩

theorem gap4 :
    ¬ ∃ L : ℝ, Tendsto dividedRatio atTop (nhds L) := by
  exact dividedRatio_has_no_limit

theorem gap5 :
    Tendsto cosineRatio atTop (nhds 0) := by
  exact cosineRatio_tendsto_zero

theorem gap6 :
    Tendsto sampleA atTop atTop := by
  exact sampleA_tendsto_atTop

theorem gap7 :
    Tendsto sampleB atTop atTop := by
  exact sampleB_tendsto_atTop

theorem gap8 :
    Tendsto (fun n : ℕ => quotient (sampleA n)) atTop
      (nhds (1 / Real.exp 1)) := by
  exact quotient_sampleA_tendsto

theorem gap9 :
    Tendsto (fun n : ℕ => quotient (sampleB n)) atTop (nhds 1) := by
  exact quotient_sampleB_tendsto

theorem gap10 :
    ¬ ∃ L : ℝ, Tendsto quotient atTop (nhds L) := by
  exact quotient_has_no_limit

end

end ProofGap.Exercise1374_4
