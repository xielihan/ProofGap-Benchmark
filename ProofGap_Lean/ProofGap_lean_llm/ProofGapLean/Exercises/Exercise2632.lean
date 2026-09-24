import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

namespace ProofGap.Exercise2632

noncomputable section

def term (n : ℕ) : ℝ :=
  (n : ℝ) ^ 2 * Real.exp (-Real.sqrt n)

def comparison (n : ℕ) : ℝ :=
  1 / Real.rpow n (3 / 2 : ℝ)

theorem gap1 (B : ℝ) :
    ∃ T : ℝ, ∀ t ≥ T, B * t ^ 7 ≤ Real.exp t := by
  refine ⟨max 0 (B * (8 : ℝ) ^ 8), ?_⟩
  intro t ht
  have ht0 : 0 ≤ t :=
    (le_max_left 0 (B * (8 : ℝ) ^ 8)).trans ht
  have hBt : B * (8 : ℝ) ^ 8 ≤ t :=
    (le_max_right 0 (B * (8 : ℝ) ^ 8)).trans ht
  have hprod :
      (B * (8 : ℝ) ^ 8) * t ^ 7 ≤ t * t ^ 7 :=
    mul_le_mul_of_nonneg_right hBt (pow_nonneg ht0 7)
  have hpoly : B * t ^ 7 ≤ (t / 8) ^ 8 := by
    calc
      B * t ^ 7 = ((B * (8 : ℝ) ^ 8) * t ^ 7) / (8 : ℝ) ^ 8 := by ring
      _ ≤ (t * t ^ 7) / (8 : ℝ) ^ 8 :=
        div_le_div_of_nonneg_right hprod (by positivity)
      _ = (t / 8) ^ 8 := by ring
  have hbase : t / 8 ≤ Real.exp (t / 8) := by
    nlinarith [Real.add_one_le_exp (t / 8)]
  have hpow : (t / 8) ^ 8 ≤ (Real.exp (t / 8)) ^ 8 := by
    gcongr
  have hexpid : (Real.exp (t / 8)) ^ 8 = Real.exp t := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  exact hpoly.trans (hpow.trans_eq hexpid)

theorem gap2 (B : ℝ) (hB : 0 < B) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ n ≥ N,
      0 < term n ∧
      term n ≤ (1 / B) * Real.rpow n (-(7 / 2 : ℝ) + 2) ∧
      (1 / B) * Real.rpow n (-(7 / 2 : ℝ) + 2) =
        (1 / B) * comparison n := by
  obtain ⟨T, hT⟩ := gap1 B
  obtain ⟨N, hN⟩ := exists_nat_ge (max ((max T 0) ^ 2) 1)
  have hNoneR : (1 : ℝ) ≤ (N : ℝ) :=
    (le_max_right ((max T 0) ^ 2) 1).trans hN
  have hNone : 1 ≤ N := by exact_mod_cast hNoneR
  refine ⟨N, hNone, ?_⟩
  intro n hn
  have hNnR : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnR : 0 < (n : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one (hNone.trans hn))
  have hsq : (max T 0) ^ 2 ≤ (n : ℝ) :=
    (le_max_left ((max T 0) ^ 2) 1).trans (hN.trans hNnR)
  have hmax0 : 0 ≤ max T 0 := le_max_right T 0
  have hroot : max T 0 ≤ Real.sqrt (n : ℝ) := by
    calc
      max T 0 = Real.sqrt ((max T 0) ^ 2) :=
        (Real.sqrt_sq hmax0).symm
      _ ≤ Real.sqrt (n : ℝ) := Real.sqrt_le_sqrt hsq
  have hTroot : T ≤ Real.sqrt (n : ℝ) :=
    (le_max_left T 0).trans hroot
  have hexp := hT (Real.sqrt (n : ℝ)) hTroot
  have hsqrtpow :
      (Real.sqrt (n : ℝ)) ^ 7 = Real.rpow (n : ℝ) (7 / 2 : ℝ) := by
    rw [Real.sqrt_eq_rpow]
    calc
      (Real.rpow (n : ℝ) (1 / 2 : ℝ)) ^ 7 =
          Real.rpow (Real.rpow (n : ℝ) (1 / 2 : ℝ)) (7 : ℝ) := by
        simpa using
          (Real.rpow_natCast (Real.rpow (n : ℝ) (1 / 2 : ℝ)) 7).symm
      _ = Real.rpow (n : ℝ) ((1 / 2 : ℝ) * 7) := by
        simpa using (Real.rpow_mul hnR.le (1 / 2 : ℝ) (7 : ℝ)).symm
      _ = Real.rpow (n : ℝ) (7 / 2 : ℝ) := by norm_num
  rw [hsqrtpow] at hexp
  have hrpowpos : 0 < Real.rpow (n : ℝ) (7 / 2 : ℝ) :=
    Real.rpow_pos_of_pos hnR _
  have hdenpos : 0 < B * Real.rpow (n : ℝ) (7 / 2 : ℝ) :=
    mul_pos hB hrpowpos
  have hdiv :
      (n : ℝ) ^ 2 / Real.exp (Real.sqrt (n : ℝ)) ≤
        (n : ℝ) ^ 2 / (B * Real.rpow (n : ℝ) (7 / 2 : ℝ)) :=
    div_le_div_of_nonneg_left (sq_nonneg (n : ℝ)) hdenpos hexp
  have hcalc :
      (n : ℝ) ^ 2 / (B * Real.rpow (n : ℝ) (7 / 2 : ℝ)) =
        (1 / B) * Real.rpow (n : ℝ) (-(7 / 2 : ℝ) + 2) := by
    rw [show -(7 / 2 : ℝ) + 2 = 2 - 7 / 2 by norm_num]
    have hrsub :
        Real.rpow (n : ℝ) (2 - 7 / 2 : ℝ) =
          Real.rpow (n : ℝ) 2 / Real.rpow (n : ℝ) (7 / 2) :=
      Real.rpow_sub hnR 2 (7 / 2)
    have hrpowtwo : Real.rpow (n : ℝ) (2 : ℝ) = (n : ℝ) ^ 2 := by
      simpa using (Real.rpow_natCast (n : ℝ) 2)
    rw [hrsub, hrpowtwo]
    field_simp [ne_of_gt hB, ne_of_gt hrpowpos] <;> ring
  have htermpos : 0 < term n := by
    unfold term
    positivity
  refine ⟨htermpos, ?_, ?_⟩
  · calc
      term n = (n : ℝ) ^ 2 / Real.exp (Real.sqrt (n : ℝ)) := by
        simp [term, Real.exp_neg, div_eq_mul_inv]
      _ ≤ (n : ℝ) ^ 2 /
          (B * Real.rpow (n : ℝ) (7 / 2 : ℝ)) := hdiv
      _ = (1 / B) * Real.rpow (n : ℝ) (-(7 / 2 : ℝ) + 2) := hcalc
  · rw [show -(7 / 2 : ℝ) + 2 = -(3 / 2 : ℝ) by norm_num]
    unfold comparison
    have hneg :
        Real.rpow (n : ℝ) (-(3 / 2 : ℝ)) =
          1 / Real.rpow (n : ℝ) (3 / 2 : ℝ) := by
      simpa [one_div] using
        (Real.rpow_neg hnR.le (3 / 2 : ℝ))
    exact congrArg (fun x : ℝ => (1 / B) * x) hneg

theorem gap3 :
    Summable (fun n : ℕ => comparison (n + 1)) := by
  have hs : Summable
      (fun n : ℕ => Real.rpow (n : ℝ) (-(3 / 2 : ℝ))) :=
    Real.summable_nat_rpow.2 (by norm_num)
  have heq :
      (fun n : ℕ => comparison n) =
        (fun n : ℕ => Real.rpow (n : ℝ) (-(3 / 2 : ℝ))) := by
    funext n
    unfold comparison
    have hneg :
        Real.rpow (n : ℝ) (-(3 / 2 : ℝ)) =
          1 / Real.rpow (n : ℝ) (3 / 2 : ℝ) := by
      simpa [one_div] using
        (Real.rpow_neg (Nat.cast_nonneg n) (3 / 2 : ℝ))
    exact hneg.symm
  have hc : Summable (fun n : ℕ => comparison n) := by
    rw [heq]
    exact hs
  exact hc.comp_injective (fun a b hab => Nat.add_right_cancel hab)

theorem gap4 :
    Summable (fun n : ℕ => term (n + 1)) := by
  obtain ⟨N, hNone, htail⟩ := gap2 1 (by norm_num)
  rw [← summable_nat_add_iff N]
  have hc :
      Summable (fun n : ℕ => comparison ((n + N) + 1)) := by
    exact gap3.comp_injective
      (fun a b hab => Nat.add_right_cancel hab)
  apply hc.of_norm_bounded
  intro n
  have hindex : N ≤ (n + N) + 1 := by omega
  obtain ⟨htpos, hle, heq⟩ := htail ((n + N) + 1) hindex
  have hle' : term ((n + N) + 1) ≤ comparison ((n + N) + 1) := by
    simpa using hle.trans_eq heq
  have hnpos : 0 < (((n + N) + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.succ_pos (n + N)
  have hrpos :
      0 < Real.rpow (((n + N) + 1 : ℕ) : ℝ) (3 / 2 : ℝ) :=
    Real.rpow_pos_of_pos hnpos _
  have hcnonneg : 0 ≤ comparison ((n + N) + 1) := by
    unfold comparison
    exact one_div_nonneg.mpr hrpos.le
  simpa [Real.norm_eq_abs, abs_of_pos htpos, abs_of_nonneg hcnonneg] using hle'

theorem gap5 :
    Summable (fun n : ℕ => term (n + 1)) := by
  exact gap4

end

end ProofGap.Exercise2632
