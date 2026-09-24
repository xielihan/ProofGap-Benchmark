import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Algebra.InfiniteSum.Basic

namespace ProofGap.Exercise2644

noncomputable section

open Filter

def term (a b : ℝ) (n : ℕ) : ℝ :=
  Real.rpow n (2 * n : ℝ) /
    (Real.rpow (n + a) (n + b) * Real.rpow (n + b) (n + a))

def comparison (a b : ℝ) (n : ℕ) : ℝ :=
  1 / Real.rpow n (a + b)

def normalizedTerm (a b : ℝ) (n : ℕ) : ℝ :=
  Real.rpow n (2 * n + a + b) /
    (Real.rpow (n + a) (n + b) * Real.rpow (n + b) (n + a))

def converges (a b : ℝ) : Prop :=
  Summable (fun n : ℕ => term a b (n + 1))

private theorem tendsto_ratio_rpow_add (c d : ℝ) (hc : 0 < c) :
    Tendsto
      (fun n : ℕ => Real.rpow ((n : ℝ) / (n + c)) ((n : ℝ) + d))
      atTop (nhds (Real.exp (-c))) := by
  have hmain0 := (Real.tendsto_one_add_div_pow_exp c).inv₀ (Real.exp_ne_zero c)
  have hmain :
      Tendsto
        (fun n : ℕ => Real.rpow ((n : ℝ) / (n + c)) (n : ℝ))
        atTop (nhds (Real.exp (-c))) := by
    have hlimit : (Real.exp c)⁻¹ = Real.exp (-c) := by
      rw [Real.exp_neg]
    rw [hlimit] at hmain0
    refine hmain0.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    have hbase : (1 + c / (n : ℝ))⁻¹ = (n : ℝ) / (n + c) := by
      field_simp
    calc
      ((1 + c / (n : ℝ)) ^ n)⁻¹ = ((1 + c / (n : ℝ))⁻¹) ^ n := by
        exact (inv_pow _ n).symm
      _ = ((n : ℝ) / (n + c)) ^ n := by rw [hbase]
      _ = Real.rpow ((n : ℝ) / (n + c)) (n : ℝ) :=
        (Real.rpow_natCast _ n).symm
  have hratio : Tendsto (fun n : ℕ => (n : ℝ) / (n + c)) atTop (nhds 1) :=
    tendsto_natCast_div_add_atTop c
  have hfixed :
      Tendsto (fun n : ℕ => Real.rpow ((n : ℝ) / (n + c)) d)
        atTop (nhds 1) := by
    simpa using
      (Real.continuousAt_rpow_const 1 d (Or.inl one_ne_zero)).tendsto.comp hratio
  have h := hmain.mul hfixed
  simp only [mul_one] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hbase : 0 < (n : ℝ) / (n + c) := by positivity
  exact (Real.rpow_add hbase (n : ℝ) d).symm

theorem gap1 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    ∀ n : ℕ, 1 ≤ n →
      term a b n / comparison a b n = normalizedTerm a b n := by
  intro n hn
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hna : 0 < (n : ℝ) + a := by positivity
  have hnb : 0 < (n : ℝ) + b := by positivity
  have hpow :
      Real.rpow n (2 * n + a + b) =
        Real.rpow n (2 * n) * Real.rpow n (a + b) := by
    calc
      Real.rpow n (2 * n + a + b) = Real.rpow n (2 * n + (a + b)) := by
        congr 1
        ring
      _ = Real.rpow n (2 * n) * Real.rpow n (a + b) :=
        Real.rpow_add hnpos _ _
  unfold term comparison normalizedTerm
  rw [hpow]
  field_simp

theorem gap2 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    Tendsto (fun n : ℕ => normalizedTerm a b (n + 1)) atTop
      (nhds (Real.exp (-(a + b)))) := by
  have h0 := (tendsto_ratio_rpow_add a b ha).mul
    (tendsto_ratio_rpow_add b a hb)
  have hlimit : Real.exp (-a) * Real.exp (-b) = Real.exp (-(a + b)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hlimit] at h0
  have h := h0.comp (tendsto_add_atTop_nat 1)
  refine h.congr' ?_
  filter_upwards with n
  have hnpos : 0 < (((n + 1 : ℕ) : ℝ)) := by exact_mod_cast Nat.succ_pos n
  have hna : 0 < (((n + 1 : ℕ) : ℝ)) + a := by positivity
  have hnb : 0 < (((n + 1 : ℕ) : ℝ)) + b := by positivity
  have hdiva :
      Real.rpow ((((n + 1 : ℕ) : ℝ)) / (((n + 1 : ℕ) : ℝ) + a))
          (((n + 1 : ℕ) : ℝ) + b) =
        Real.rpow (((n + 1 : ℕ) : ℝ)) (((n + 1 : ℕ) : ℝ) + b) /
          Real.rpow (((n + 1 : ℕ) : ℝ) + a) (((n + 1 : ℕ) : ℝ) + b) :=
    Real.div_rpow hnpos.le hna.le _
  have hdivb :
      Real.rpow ((((n + 1 : ℕ) : ℝ)) / (((n + 1 : ℕ) : ℝ) + b))
          (((n + 1 : ℕ) : ℝ) + a) =
        Real.rpow (((n + 1 : ℕ) : ℝ)) (((n + 1 : ℕ) : ℝ) + a) /
          Real.rpow (((n + 1 : ℕ) : ℝ) + b) (((n + 1 : ℕ) : ℝ) + a) :=
    Real.div_rpow hnpos.le hnb.le _
  have hnum :
      Real.rpow (((n + 1 : ℕ) : ℝ)) (((n + 1 : ℕ) : ℝ) + b) *
          Real.rpow (((n + 1 : ℕ) : ℝ)) (((n + 1 : ℕ) : ℝ) + a) =
        Real.rpow (((n + 1 : ℕ) : ℝ))
          (2 * (((n + 1 : ℕ) : ℝ)) + a + b) := by
    calc
      Real.rpow (((n + 1 : ℕ) : ℝ)) (((n + 1 : ℕ) : ℝ) + b) *
          Real.rpow (((n + 1 : ℕ) : ℝ)) (((n + 1 : ℕ) : ℝ) + a) =
        Real.rpow (((n + 1 : ℕ) : ℝ))
          ((((n + 1 : ℕ) : ℝ) + b) + (((n + 1 : ℕ) : ℝ) + a)) :=
        (Real.rpow_add hnpos _ _).symm
      _ = Real.rpow (((n + 1 : ℕ) : ℝ))
          (2 * (((n + 1 : ℕ) : ℝ)) + a + b) := by
        congr 1
        ring
  simp only [Function.comp_apply]
  unfold normalizedTerm
  rw [hdiva, hdivb]
  rw [div_mul_div_comm, hnum]

theorem gap3 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    Tendsto (fun n : ℕ => term a b (n + 1) / comparison a b (n + 1))
      atTop (nhds (Real.exp (-(a + b)))) := by
  refine (gap2 a b ha hb).congr' (.of_forall fun n => ?_)
  exact (gap1 a b ha hb (n + 1) (by omega)).symm

private theorem comparison_pos (a b : ℝ) (n : ℕ) (hn : 1 ≤ n) :
    0 < comparison a b n := by
  unfold comparison
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  exact one_div_pos.mpr (Real.rpow_pos_of_pos hnpos _)

private theorem term_pos (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (n : ℕ) (hn : 1 ≤ n) : 0 < term a b n := by
  unfold term
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hna : 0 < (n : ℝ) + a := by positivity
  have hnb : 0 < (n : ℝ) + b := by positivity
  exact div_pos (Real.rpow_pos_of_pos hnpos _)
    (mul_pos (Real.rpow_pos_of_pos hna _) (Real.rpow_pos_of_pos hnb _))

theorem gap4 (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hab : 1 < a + b) :
    Summable (fun n : ℕ => comparison a b (n + 1)) := by
  have hfull : Summable (fun n : ℕ => 1 / ((n : ℝ) ^ (a + b))) :=
    Real.summable_one_div_nat_rpow.mpr hab
  have hshift :
      Summable (fun n : ℕ => 1 / (((n + 1 : ℕ) : ℝ) ^ (a + b))) :=
    (summable_nat_add_iff 1).mpr hfull
  simpa [comparison] using hshift

theorem gap5 (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hab : 1 < a + b) :
    converges a b := by
  have hlimit : Real.exp (-(a + b)) < 1 := by
    rw [Real.exp_lt_one_iff]
    linarith
  have hupper :
      ∀ᶠ n : ℕ in atTop,
        term a b (n + 1) / comparison a b (n + 1) < 1 :=
    (tendsto_order.mp (gap3 a b ha hb)).2 1 hlimit
  unfold converges
  refine (gap4 a b ha hb hab).of_norm_bounded_eventually_nat ?_
  filter_upwards [hupper] with n hn
  have hp := comparison_pos a b (n + 1) (by omega)
  have hle : term a b (n + 1) ≤ comparison a b (n + 1) := by
    have := (div_lt_iff₀ hp).mp hn
    linarith
  rw [Real.norm_eq_abs, abs_of_pos (term_pos a b ha hb (n + 1) (by omega))]
  exact hle

theorem gap6 (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hab : a + b ≤ 1) :
    ¬ Summable (fun n : ℕ => comparison a b (n + 1)) := by
  intro hs
  have hs' :
      Summable (fun n : ℕ => 1 / (((n + 1 : ℕ) : ℝ) ^ (a + b))) := by
    simpa [comparison] using hs
  have hfull : Summable (fun n : ℕ => 1 / ((n : ℝ) ^ (a + b))) :=
    (summable_nat_add_iff 1).mp hs'
  have : 1 < a + b := Real.summable_one_div_nat_rpow.mp hfull
  linarith

theorem gap7 (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hab : a + b ≤ 1) :
    ¬ converges a b := by
  intro hs
  let K : ℝ := Real.exp (-(a + b)) / 2
  have hK : 0 < K := by dsimp [K]; positivity
  have hKlim : K < Real.exp (-(a + b)) := by
    dsimp [K]
    exact half_lt_self (Real.exp_pos _)
  have hlower :
      ∀ᶠ n : ℕ in atTop,
        K < term a b (n + 1) / comparison a b (n + 1) :=
    (tendsto_order.mp (gap3 a b ha hb)).1 K hKlim
  have hscaled : Summable (fun n : ℕ => term a b (n + 1) / K) :=
    hs.div_const K
  have hcomp : Summable (fun n : ℕ => comparison a b (n + 1)) :=
    hscaled.of_norm_bounded_eventually_nat (by
      filter_upwards [hlower] with n hn
      have hp := comparison_pos a b (n + 1) (by omega)
      have hmul := (lt_div_iff₀ hp).mp hn
      rw [Real.norm_eq_abs, abs_of_pos hp]
      apply (le_div_iff₀ hK).mpr
      simpa [mul_comm] using hmul.le)
  exact gap6 a b ha hb hab hcomp

theorem gap8 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    converges a b ↔ 1 < a + b := by
  constructor
  · intro hs
    by_contra hnot
    exact gap7 a b ha hb (le_of_not_gt hnot) hs
  · exact gap5 a b ha hb

end

end ProofGap.Exercise2644
