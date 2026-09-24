import ProofGapLean.Prelude.Analysis
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Lean.Elab.Tactic.Omega
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Data.Real.Sqrt
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Neighborhoods
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Basic

open Filter Topology
open scoped Interval

namespace ProofGap.Exercise2227

noncomputable section

def admissible (k n : ℕ) : Prop := 1 ≤ k ∧ k < n

def angle (k n : ℕ) : ℝ := (k : ℝ) * Real.pi / (n : ℝ) ^ 2

def errorTerm (k n : ℕ) : ℝ :=
  (1 + (k : ℝ) / n) * (angle k n - Real.sin (angle k n))

def errorSum (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.Ico 1 n, errorTerm k n

def majorantTerm (k n : ℕ) : ℝ :=
  (1 + (k : ℝ) / n) *
    (2 * (k : ℝ) * Real.pi / (n : ℝ) ^ 2) *
      (1 - Real.cos (Real.pi / n))

def majorantSum (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.Ico 1 n, majorantTerm k n

def sineSum (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.Ico 1 n,
    (1 + (k : ℝ) / n) * Real.sin (angle k n)

def linearSum (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.Ico 1 n, (1 + (k : ℝ) / n) * angle k n

def polynomialRiemannSum (n : ℕ) : ℝ :=
  (1 / (n : ℝ)) *
    ∑ k ∈ Finset.Ico 1 n,
      ((k : ℝ) * Real.pi / n + (k : ℝ) ^ 2 * Real.pi / (n : ℝ) ^ 2)

private lemma sum_Ico_cast_formulas (n : ℕ) :
    (∑ k ∈ Finset.Ico 1 n, (k : ℝ)) =
        (n : ℝ) * ((n : ℝ) - 1) / 2 ∧
      (∑ k ∈ Finset.Ico 1 n, (k : ℝ) ^ 2) =
        (n : ℝ) * ((n : ℝ) - 1) * (2 * (n : ℝ) - 1) / 6 := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      by_cases hn : n = 0
      · subst n
        norm_num
      · have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
        constructor
        · rw [Finset.sum_Ico_succ_top hn1, ih.1]
          norm_num only [Nat.cast_add, Nat.cast_one]
          ring
        · rw [Finset.sum_Ico_succ_top hn1, ih.2]
          norm_num only [Nat.cast_add, Nat.cast_one]
          ring

private lemma integral_polynomial_value :
    (∫ x in (0 : ℝ)..1, Real.pi * (x + x ^ 2)) = 5 * Real.pi / 6 := by
  let F : ℝ → ℝ := fun x => Real.pi * (x ^ 2 / 2 + x ^ 3 / 3)
  have hprimitive (x : ℝ) :
      HasDerivAt (fun y : ℝ => y ^ 2 / 2 + y ^ 3 / 3) (x + x ^ 2) x := by
    convert (((hasDerivAt_id x).pow 2).div_const 2).add
      (((hasDerivAt_id x).pow 3).div_const 3) using 1 <;> simp [id] <;> ring
  have hderiv (x : ℝ) :
      HasDerivAt F (Real.pi * (x + x ^ 2)) x := by
    dsimp [F]
    convert (hasDerivAt_const x Real.pi).mul (hprimitive x) using 1 <;> ring
  have hint :
      IntervalIntegrable (fun x : ℝ => Real.pi * (x + x ^ 2))
        MeasureTheory.volume 0 1 :=
    (continuous_const.mul (continuous_id.add (continuous_id.pow 2))).intervalIntegrable 0 1
  calc
    (∫ x in (0 : ℝ)..1, Real.pi * (x + x ^ 2)) = F 1 - F 0 :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun x _ => hderiv x) hint
    _ = 5 * Real.pi / 6 := by
      dsimp [F]
      ring

theorem gap1 (k n : ℕ) (hkn : admissible k n) :
    0 ≤ angle k n - Real.sin (angle k n) := by
  apply sub_nonneg.mpr
  apply Real.sin_le
  unfold angle
  positivity

theorem gap2 (k n : ℕ) (hkn : admissible k n) :
    angle k n - Real.sin (angle k n) ≤
      Real.tan (angle k n) - Real.sin (angle k n) := by
  have hn : 2 ≤ n :=
    Nat.succ_le_iff.mpr (lt_of_le_of_lt hkn.1 hkn.2)
  have hk_succ : k + 1 ≤ n := Nat.succ_le_iff.mpr hkn.2
  have hkR : (k : ℝ) + 1 ≤ (n : ℝ) := by
    exact_mod_cast hk_succ
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast hn
  have hfour : 4 * (k : ℝ) ≤ (n : ℝ) ^ 2 := by
    nlinarith [sq_nonneg ((n : ℝ) - 2)]
  have hnpos : 0 < (n : ℝ) := by nlinarith
  have hangle : angle k n ≤ Real.pi / 4 := by
    unfold angle
    apply (div_le_iff₀ (sq_pos_of_pos hnpos)).2
    have hp := mul_le_mul_of_nonneg_right hfour Real.pi_nonneg
    nlinarith
  have hangle0 : 0 ≤ angle k n := by
    unfold angle
    positivity
  have hangle_lt : angle k n < Real.pi / 2 := by
    nlinarith [Real.pi_pos]
  linarith [Real.le_tan hangle0 hangle_lt]

theorem gap3 (k n : ℕ) (hkn : admissible k n) :
    Real.tan (angle k n) - Real.sin (angle k n) ≤
      Real.tan (angle k n) * (1 - Real.cos (angle k n)) := by
  have hn : 2 ≤ n :=
    Nat.succ_le_iff.mpr (lt_of_le_of_lt hkn.1 hkn.2)
  have hk_succ : k + 1 ≤ n := Nat.succ_le_iff.mpr hkn.2
  have hkR : (k : ℝ) + 1 ≤ (n : ℝ) := by
    exact_mod_cast hk_succ
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast hn
  have hfour : 4 * (k : ℝ) ≤ (n : ℝ) ^ 2 := by
    nlinarith [sq_nonneg ((n : ℝ) - 2)]
  have hnpos : 0 < (n : ℝ) := by nlinarith
  have hangle0 : 0 ≤ angle k n := by
    unfold angle
    positivity
  have hangle_lt : angle k n < Real.pi / 2 := by
    have hquarter : angle k n ≤ Real.pi / 4 := by
      unfold angle
      apply (div_le_iff₀ (sq_pos_of_pos hnpos)).2
      have hp := mul_le_mul_of_nonneg_right hfour Real.pi_nonneg
      nlinarith
    nlinarith [Real.pi_pos]
  have hcpos : 0 < Real.cos (angle k n) :=
    Real.cos_pos_of_mem_Ioo ⟨by nlinarith [Real.pi_pos], hangle_lt⟩
  apply le_of_eq
  rw [Real.tan_eq_sin_div_cos]
  field_simp [ne_of_gt hcpos]

theorem gap4 (k n : ℕ) (hkn : admissible k n) :
    Real.tan (angle k n) * (1 - Real.cos (angle k n)) ≤
      (Real.sin (angle k n) / Real.cos (angle k n)) *
        (1 - Real.cos (angle k n)) := by
  rw [Real.tan_eq_sin_div_cos]

theorem gap5 (k n : ℕ) (hkn : admissible k n) :
    (Real.sin (angle k n) / Real.cos (angle k n)) *
        (1 - Real.cos (angle k n)) ≤
      (2 * (k : ℝ) * Real.pi / (n : ℝ) ^ 2) *
        (1 - Real.cos (Real.pi / n)) := by
  have hn : 2 ≤ n :=
    Nat.succ_le_iff.mpr (lt_of_le_of_lt hkn.1 hkn.2)
  have hk_succ : k + 1 ≤ n := Nat.succ_le_iff.mpr hkn.2
  have hkR : (k : ℝ) + 1 ≤ (n : ℝ) := by
    exact_mod_cast hk_succ
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast hn
  have hnpos : 0 < (n : ℝ) := by nlinarith
  have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hnpos
  have hk_le_n : (k : ℝ) ≤ (n : ℝ) := by linarith
  have hfour : 4 * (k : ℝ) ≤ (n : ℝ) ^ 2 := by
    nlinarith [sq_nonneg ((n : ℝ) - 2)]
  have ha0 : 0 ≤ angle k n := by
    unfold angle
    positivity
  have hb0 : 0 ≤ Real.pi / (n : ℝ) := by positivity
  have hb_le : Real.pi / (n : ℝ) ≤ Real.pi / 2 := by
    apply (div_le_iff₀ hnpos).2
    nlinarith [Real.pi_pos]
  have hab : angle k n ≤ Real.pi / (n : ℝ) := by
    unfold angle
    apply (div_le_iff₀ (sq_pos_of_pos hnpos)).2
    have hid : (Real.pi / (n : ℝ)) * (n : ℝ) ^ 2 = Real.pi * (n : ℝ) := by
      field_simp [hn0]
    rw [hid]
    simpa [mul_comm] using
      mul_le_mul_of_nonneg_right hk_le_n Real.pi_nonneg
  have ha_quarter : angle k n ≤ Real.pi / 4 := by
    unfold angle
    apply (div_le_iff₀ (sq_pos_of_pos hnpos)).2
    have hp := mul_le_mul_of_nonneg_right hfour Real.pi_nonneg
    nlinarith
  have hq0 : (0 : ℝ) ≤ Real.pi / 4 := by positivity
  have hqpi : Real.pi / 4 ≤ Real.pi := by nlinarith [Real.pi_pos]
  have hapi : angle k n ≤ Real.pi := by nlinarith [Real.pi_pos]
  have hbpi : Real.pi / (n : ℝ) ≤ Real.pi := by nlinarith [Real.pi_pos]
  have hcos_q_le : Real.cos (Real.pi / 4) ≤ Real.cos (angle k n) :=
    Real.strictAntiOn_cos.antitoneOn ⟨ha0, hapi⟩ ⟨hq0, hqpi⟩ ha_quarter
  have hhalf_cos : (1 : ℝ) / 2 ≤ Real.cos (angle k n) := by
    rw [Real.cos_pi_div_four] at hcos_q_le
    nlinarith [le_of_lt Real.one_lt_sqrt_two]
  have hcpos : 0 < Real.cos (angle k n) := by nlinarith
  have hsin : Real.sin (angle k n) ≤ angle k n := Real.sin_le ha0
  have htan_bound :
      Real.sin (angle k n) / Real.cos (angle k n) ≤ 2 * angle k n := by
    apply (div_le_iff₀ hcpos).2
    have haux : 0 ≤ angle k n * (2 * Real.cos (angle k n) - 1) :=
      mul_nonneg ha0 (by nlinarith)
    nlinarith
  have hcos_mono : Real.cos (Real.pi / (n : ℝ)) ≤ Real.cos (angle k n) :=
    Real.strictAntiOn_cos.antitoneOn ⟨ha0, hapi⟩ ⟨hb0, hbpi⟩ hab
  have hdiff :
      1 - Real.cos (angle k n) ≤ 1 - Real.cos (Real.pi / (n : ℝ)) := by
    linarith
  have hleft_nonneg : 0 ≤ 1 - Real.cos (angle k n) :=
    sub_nonneg.mpr (Real.cos_le_one _)
  have hright_nonneg : 0 ≤ 2 * angle k n := by positivity
  have hmul := mul_le_mul htan_bound hdiff hleft_nonneg hright_nonneg
  have hscale :
      2 * angle k n = 2 * (k : ℝ) * Real.pi / (n : ℝ) ^ 2 := by
    unfold angle
    ring
  rw [hscale] at hmul
  exact hmul

theorem gap6 (k n : ℕ) (hkn : admissible k n) :
    0 ≤
      (2 * (k : ℝ) * Real.pi / (n : ℝ) ^ 2) *
        (1 - Real.cos (Real.pi / n)) := by
  have hc : 0 ≤ 1 - Real.cos (Real.pi / (n : ℝ)) :=
    sub_nonneg.mpr (Real.cos_le_one _)
  positivity

theorem gap7 (n : ℕ) (hn : 2 ≤ n) :
    0 ≤ errorSum n := by
  unfold errorSum
  apply Finset.sum_nonneg
  intro k hk
  simp only [Finset.mem_Ico] at hk
  unfold errorTerm
  exact mul_nonneg (by positivity) (gap1 k n ⟨hk.1, hk.2⟩)

theorem gap8 (n : ℕ) (hn : 2 ≤ n) :
    errorSum n ≤ majorantSum n := by
  have hnposNat : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast hnposNat
  unfold errorSum majorantSum
  apply Finset.sum_le_sum
  intro j hj
  simp only [Finset.mem_Ico] at hj
  have hadm : admissible j n := ⟨hj.1, hj.2⟩
  have hdiff :
      angle j n - Real.sin (angle j n) ≤
        (2 * (j : ℝ) * Real.pi / (n : ℝ) ^ 2) *
          (1 - Real.cos (Real.pi / (n : ℝ))) := by
    calc
      angle j n - Real.sin (angle j n) ≤
          Real.tan (angle j n) - Real.sin (angle j n) := gap2 j n hadm
      _ ≤ Real.tan (angle j n) * (1 - Real.cos (angle j n)) := gap3 j n hadm
      _ ≤ (Real.sin (angle j n) / Real.cos (angle j n)) *
          (1 - Real.cos (angle j n)) := gap4 j n hadm
      _ ≤ (2 * (j : ℝ) * Real.pi / (n : ℝ) ^ 2) *
          (1 - Real.cos (Real.pi / (n : ℝ))) := gap5 j n hadm
  have hweight : 0 ≤ 1 + (j : ℝ) / (n : ℝ) := by positivity
  unfold errorTerm majorantTerm
  simpa [mul_assoc] using mul_le_mul_of_nonneg_left hdiff hweight

theorem gap9 (n : ℕ) (hn : 2 ≤ n) :
    majorantSum n ≤ 2 * Real.pi * (1 - Real.cos (Real.pi / n)) := by
  have hnpos : 0 < (n : ℝ) := by positivity
  have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hnpos
  have hs := sum_Ico_cast_formulas n
  have heq :
      majorantSum n =
        (2 * Real.pi * (1 - Real.cos (Real.pi / (n : ℝ)))) *
          (((n : ℝ) - 1) / (2 * (n : ℝ)) +
            (((n : ℝ) - 1) * (2 * (n : ℝ) - 1)) /
              (6 * (n : ℝ) ^ 2)) := by
    unfold majorantSum majorantTerm
    calc
      Finset.sum (Finset.Ico 1 n) (fun j : ℕ =>
          (1 + (j : ℝ) / (n : ℝ)) *
            (2 * (j : ℝ) * Real.pi / (n : ℝ) ^ 2) *
              (1 - Real.cos (Real.pi / (n : ℝ)))) =
          Finset.sum (Finset.Ico 1 n) (fun j : ℕ =>
            (2 * Real.pi * (1 - Real.cos (Real.pi / (n : ℝ))) /
                (n : ℝ) ^ 2) *
              ((j : ℝ) + (j : ℝ) ^ 2 / (n : ℝ))) := by
              apply Finset.sum_congr rfl
              intro i hi
              ring
      _ = (2 * Real.pi * (1 - Real.cos (Real.pi / (n : ℝ))) /
              (n : ℝ) ^ 2) *
            Finset.sum (Finset.Ico 1 n) (fun j : ℕ =>
              (j : ℝ) + (j : ℝ) ^ 2 / (n : ℝ)) := by
              rw [Finset.mul_sum]
      _ = (2 * Real.pi * (1 - Real.cos (Real.pi / (n : ℝ)))) *
          (((n : ℝ) - 1) / (2 * (n : ℝ)) +
            (((n : ℝ) - 1) * (2 * (n : ℝ) - 1)) /
              (6 * (n : ℝ) ^ 2)) := by
              rw [Finset.sum_add_distrib]
              have hdiv :
                  Finset.sum (Finset.Ico 1 n) (fun j : ℕ =>
                    (j : ℝ) ^ 2 / (n : ℝ)) =
                    (1 / (n : ℝ)) *
                      Finset.sum (Finset.Ico 1 n) (fun j : ℕ =>
                        (j : ℝ) ^ 2) := by
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro i hi
                ring
              rw [hdiv, hs.1, hs.2]
              field_simp [hn0]
  have hcoef_eq :
      (((n : ℝ) - 1) / (2 * (n : ℝ)) +
          (((n : ℝ) - 1) * (2 * (n : ℝ) - 1)) /
            (6 * (n : ℝ) ^ 2)) =
        (5 * (n : ℝ) ^ 2 - 6 * (n : ℝ) + 1) /
          (6 * (n : ℝ) ^ 2) := by
    field_simp [hn0]
    ring
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hden : 0 < 6 * (n : ℝ) ^ 2 := by positivity
  have hcoef :
      (((n : ℝ) - 1) / (2 * (n : ℝ)) +
          (((n : ℝ) - 1) * (2 * (n : ℝ) - 1)) /
            (6 * (n : ℝ) ^ 2)) ≤ 1 := by
    rw [hcoef_eq]
    apply (div_le_iff₀ hden).2
    nlinarith
  rw [heq]
  have hnonneg : 0 ≤ 2 * Real.pi * (1 - Real.cos (Real.pi / (n : ℝ))) :=
    mul_nonneg (mul_nonneg (by norm_num) Real.pi_nonneg)
      (sub_nonneg.mpr (Real.cos_le_one _))
  have hbound := mul_le_mul_of_nonneg_left hcoef hnonneg
  simpa using hbound

theorem gap10 :
    Tendsto (fun n : ℕ => 2 * Real.pi * (1 - Real.cos (Real.pi / n)))
      atTop (𝓝 0) := by
  have harg :
      Tendsto (fun n : ℕ => Real.pi / (n : ℝ)) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hcos :
      Tendsto (fun n : ℕ => Real.cos (Real.pi / (n : ℝ))) atTop
        (nhds (Real.cos 0)) :=
    Real.continuous_cos.continuousAt.tendsto.comp harg
  convert tendsto_const_nhds.mul (tendsto_const_nhds.sub hcos) using 1 <;>
    norm_num

theorem gap11 : (0 : ℝ) ≤ 0 := by
  rfl

theorem gap12 :
    ∀ A E : ℝ,
      Tendsto linearSum atTop (𝓝 A) →
      Tendsto errorSum atTop (𝓝 E) →
      Tendsto sineSum atTop (𝓝 (A - E)) := by
  intro A E hA hE
  have hrel : ∀ n, sineSum n = linearSum n - errorSum n := by
    intro n
    unfold sineSum linearSum errorSum errorTerm
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  have h := hA.sub hE
  convert h using 1
  funext n
  exact hrel n

theorem gap13 :
    ∀ L : ℝ, Tendsto sineSum atTop (𝓝 L) ↔
      Tendsto polynomialRiemannSum atTop (𝓝 L) := by
  intro L
  have herr : Tendsto errorSum atTop (nhds 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds gap10 ?_ ?_
    · intro n
      by_cases hn : 2 ≤ n
      · exact gap7 n hn
      · have hnsmall : n = 0 ∨ n = 1 := by omega
        rcases hnsmall with rfl | rfl <;> simp [errorSum]
    · intro n
      by_cases hn : 2 ≤ n
      · exact (gap8 n hn).trans (gap9 n hn)
      · have hnsmall : n = 0 ∨ n = 1 := by omega
        rcases hnsmall with rfl | rfl
        · have hzero : errorSum 0 = 0 := by simp [errorSum]
          rw [hzero]
          exact mul_nonneg (mul_nonneg (by norm_num) Real.pi_nonneg)
            (sub_nonneg.mpr (Real.cos_le_one _))
        · have hone : errorSum 1 = 0 := by simp [errorSum]
          rw [hone]
          exact mul_nonneg (mul_nonneg (by norm_num) Real.pi_nonneg)
            (sub_nonneg.mpr (Real.cos_le_one _))
  have hrel : ∀ n, sineSum n = linearSum n - errorSum n := by
    intro n
    unfold sineSum linearSum errorSum errorTerm
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  have hlp : ∀ n, linearSum n = polynomialRiemannSum n := by
    intro n
    unfold linearSum polynomialRiemannSum angle
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  constructor
  · intro hs
    have hadd := hs.add herr
    have hlin : Tendsto linearSum atTop (nhds L) := by
      convert hadd using 1
      · funext n
        rw [hrel n]
        ring
      · ring
    convert hlin using 1
    funext n
    exact (hlp n).symm
  · intro hp
    have hlin : Tendsto linearSum atTop (nhds L) := by
      convert hp using 1
      funext n
      exact hlp n
    have hsub := hlin.sub herr
    convert hsub using 1
    · funext n
      exact hrel n
    · ring

theorem gap14 :
    Tendsto polynomialRiemannSum atTop
      (𝓝 (∫ x in (0 : ℝ)..1, Real.pi * (x + x ^ 2))) := by
  rw [integral_polynomial_value]
  have hinv :
      Tendsto (fun n : ℕ => (1 : ℝ) / (n : ℝ)) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hfirst :
      Tendsto (fun n : ℕ => ((1 : ℝ) - 1 / (n : ℝ)) / 2) atTop
        (nhds ((1 - 0) / 2)) :=
    (tendsto_const_nhds.sub hinv).div_const 2
  have hthree :
      Tendsto (fun n : ℕ => (3 : ℝ) * (1 / (n : ℝ))) atTop (nhds (3 * 0)) :=
    tendsto_const_nhds.mul hinv
  have hsquare :
      Tendsto (fun n : ℕ => ((1 : ℝ) / (n : ℝ)) ^ 2) atTop (nhds (0 ^ 2)) :=
    hinv.pow 2
  have hsecond :
      Tendsto
        (fun n : ℕ =>
          ((2 : ℝ) - 3 * (1 / (n : ℝ)) + (1 / (n : ℝ)) ^ 2) / 6)
        atTop (nhds ((2 - 3 * 0 + 0 ^ 2) / 6)) :=
    ((tendsto_const_nhds.sub hthree).add hsquare).div_const 6
  have ht :
      Tendsto
        (fun n : ℕ =>
          Real.pi *
            (((1 : ℝ) - 1 / (n : ℝ)) / 2 +
              ((2 : ℝ) - 3 * (1 / (n : ℝ)) +
                (1 / (n : ℝ)) ^ 2) / 6))
        atTop (nhds (5 * Real.pi / 6)) := by
    convert tendsto_const_nhds.mul (hfirst.add hsecond) using 1 <;>
      norm_num <;> ring
  have hevent :
      polynomialRiemannSum =ᶠ[atTop]
        (fun n : ℕ =>
          Real.pi *
            (((1 : ℝ) - 1 / (n : ℝ)) / 2 +
              ((2 : ℝ) - 3 * (1 / (n : ℝ)) +
                (1 / (n : ℝ)) ^ 2) / 6)) := by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have hnpos : 0 < n := by omega
    have hnRpos : 0 < (n : ℝ) := by exact_mod_cast hnpos
    have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hnRpos
    have hs := sum_Ico_cast_formulas n
    unfold polynomialRiemannSum
    rw [Finset.sum_add_distrib]
    have hlin :
        (∑ k ∈ Finset.Ico 1 n, (k : ℝ) * Real.pi / (n : ℝ)) =
          (∑ k ∈ Finset.Ico 1 n, (k : ℝ)) * Real.pi / (n : ℝ) := by
      calc
        (∑ k ∈ Finset.Ico 1 n, (k : ℝ) * Real.pi / (n : ℝ)) =
            ∑ k ∈ Finset.Ico 1 n, (k : ℝ) * (Real.pi / (n : ℝ)) := by
              apply Finset.sum_congr rfl
              intro k hk
              ring
        _ = (∑ k ∈ Finset.Ico 1 n, (k : ℝ)) *
              (Real.pi / (n : ℝ)) := by
              rw [Finset.sum_mul]
        _ = (∑ k ∈ Finset.Ico 1 n, (k : ℝ)) * Real.pi /
              (n : ℝ) := by ring
    have hsq :
        (∑ k ∈ Finset.Ico 1 n,
            (k : ℝ) ^ 2 * Real.pi / (n : ℝ) ^ 2) =
          (∑ k ∈ Finset.Ico 1 n, (k : ℝ) ^ 2) * Real.pi /
            (n : ℝ) ^ 2 := by
      calc
        (∑ k ∈ Finset.Ico 1 n,
            (k : ℝ) ^ 2 * Real.pi / (n : ℝ) ^ 2) =
            ∑ k ∈ Finset.Ico 1 n,
              (k : ℝ) ^ 2 * (Real.pi / (n : ℝ) ^ 2) := by
                apply Finset.sum_congr rfl
                intro k hk
                ring
        _ = (∑ k ∈ Finset.Ico 1 n, (k : ℝ) ^ 2) *
              (Real.pi / (n : ℝ) ^ 2) := by
              rw [Finset.sum_mul]
        _ = (∑ k ∈ Finset.Ico 1 n, (k : ℝ) ^ 2) * Real.pi /
              (n : ℝ) ^ 2 := by ring
    rw [hlin, hsq, hs.1, hs.2]
    field_simp [hn0] <;> ring
  exact (tendsto_congr' hevent).2 ht

theorem gap15 :
    (∫ x in (0 : ℝ)..1, Real.pi * (x + x ^ 2)) =
      5 * Real.pi / 6 := by
  exact integral_polynomial_value

theorem gap16 :
    Tendsto sineSum atTop (𝓝 (5 * Real.pi / 6)) := by
  apply (gap13 (5 * Real.pi / 6)).2
  rw [← gap15]
  exact gap14

end

end ProofGap.Exercise2227
