import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.RingTheory.RootsOfUnity.Lemmas
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise3874

noncomputable section

open Filter MeasureTheory Set
open scoped BigOperators Interval

def HasImproperIntegral (a : ℝ) (f : ℝ → ℝ) (L : ℝ) : Prop :=
  Tendsto (fun b : ℝ => ∫ x in a..b, f x) atTop (nhds L)

def improperIntegral (a : ℝ) (f : ℝ → ℝ) : ℝ :=
  sInf {L : ℝ | HasImproperIntegral a f L}

def J (n m : ℕ) : ℝ :=
  improperIntegral 0
    (fun x =>
      Real.rpow x ((m : ℝ) - 1) *
        Real.exp (-Real.rpow x (n : ℝ)))

def E (n : ℕ) : ℝ :=
  ∏ m ∈ Finset.Icc 1 (n - 1), Real.Gamma ((m : ℝ) / (n : ℝ))

def sineProduct (n : ℕ) : ℝ :=
  ∏ m ∈ Finset.Icc 1 (n - 1),
    Real.sin ((m : ℝ) * Real.pi / (n : ℝ))

def rootDistanceProduct (n : ℕ) : ℝ :=
  ∏ m ∈ Finset.Icc 1 (n - 1),
    ‖
      ((1 : ℂ) -
        ((Real.cos (2 * (m : ℝ) * Real.pi / (n : ℝ)) : ℂ) +
          Complex.I *
            (Real.sin (2 * (m : ℝ) * Real.pi / (n : ℝ)) : ℂ)))‖

private lemma improperIntegral_eq_setIntegral
    (f : ℝ → ℝ)
    (hf : IntegrableOn f (Ioi (0 : ℝ))) :
    improperIntegral 0 f =
      ∫ x in Ioi (0 : ℝ), f x := by
  have hHas :
      HasImproperIntegral 0 f
        (∫ x in Ioi (0 : ℝ), f x) := by
    unfold HasImproperIntegral
    exact
      intervalIntegral_tendsto_integral_Ioi
        0 hf tendsto_id
  have hset :
      {L : ℝ | HasImproperIntegral 0 f L} =
        {∫ x in Ioi (0 : ℝ), f x} := by
    ext L
    simp only [mem_setOf_eq, mem_singleton_iff]
    constructor
    · intro hL
      exact tendsto_nhds_unique hL hHas
    · rintro rfl
      exact hHas
  unfold improperIntegral
  rw [hset]
  simp

private lemma J_eq (n m : ℕ) (hn : 0 < n) (hm : 1 ≤ m) :
    J n m =
      (1 / (n : ℝ)) *
        Real.Gamma ((m : ℝ) / (n : ℝ)) := by
  have hnR : (0 : ℝ) < n := by
    exact_mod_cast hn
  have hnR1 : (1 : ℝ) ≤ n := by
    exact_mod_cast hn
  have hq : (-1 : ℝ) < (m : ℝ) - 1 := by
    have hmR : (1 : ℝ) ≤ m := by
      exact_mod_cast hm
    linarith
  have hint :
      IntegrableOn
        (fun x : ℝ =>
          Real.rpow x ((m : ℝ) - 1) *
            Real.exp (-Real.rpow x (n : ℝ)))
        (Ioi (0 : ℝ)) := by
    exact integrableOn_rpow_mul_exp_neg_rpow hq hnR1
  rw [J, improperIntegral_eq_setIntegral _ hint]
  simpa only [sub_add_cancel] using
    (integral_rpow_mul_exp_neg_rpow hnR hq)

private lemma E_eq_range (n : ℕ) (hn : 0 < n) :
    E n =
      ∏ k ∈ Finset.range (n - 1),
        Real.Gamma (((k + 1 : ℕ) : ℝ) / (n : ℝ)) := by
  unfold E
  rw [← Finset.Ico_succ_right_eq_Icc 1 (n - 1)]
  have htop : Order.succ (n - 1) = n := by
    change Nat.succ (n - 1) = n
    omega
  rw [htop, Finset.prod_Ico_eq_prod_range]
  simp only [Nat.add_comm]

private lemma gamma_product_Icc_eq_E
    (n : ℕ) (hn : 0 < n) :
    (∏ m ∈ Finset.Icc 1 n,
      Real.Gamma ((m : ℝ) / (n : ℝ))) = E n := by
  rw [← Finset.Ico_succ_right_eq_Icc 1 n,
    Finset.prod_Ico_eq_prod_range]
  have hsucc : Order.succ n - 1 = n := by
    change Nat.succ n - 1 = n
    omega
  rw [hsucc]
  have horder : n - 1 + 1 = n :=
    Nat.sub_add_cancel hn
  have hsplit :
      (∏ k ∈ Finset.range n,
        Real.Gamma (((1 + k : ℕ) : ℝ) / (n : ℝ))) =
        (∏ k ∈ Finset.range (n - 1),
          Real.Gamma (((1 + k : ℕ) : ℝ) / (n : ℝ))) *
          Real.Gamma
            (((1 + (n - 1) : ℕ) : ℝ) / (n : ℝ)) := by
    simpa only [horder] using
      (Finset.prod_range_succ
        (f := fun k : ℕ =>
          Real.Gamma
            (((1 + k : ℕ) : ℝ) / (n : ℝ)))
        (n - 1))
  rw [hsplit, show 1 + (n - 1) = n by omega]
  have hnR : (n : ℝ) ≠ 0 := by
    exact_mod_cast hn.ne'
  rw [div_self hnR, Real.Gamma_one, mul_one,
    E_eq_range n hn]
  congr 2
  funext k
  rw [Nat.add_comm]

private lemma E_reflect (n : ℕ) (hn : 0 < n) :
    E n =
      ∏ m ∈ Finset.Icc 1 (n - 1),
        Real.Gamma (((n - m : ℕ) : ℝ) / (n : ℝ)) := by
  unfold E
  rw [← Finset.Ico_succ_right_eq_Icc 1 (n - 1)]
  have htop : Order.succ (n - 1) = n := by
    change Nat.succ (n - 1) = n
    omega
  rw [htop]
  have hreflect :=
    Finset.prod_Ico_reflect
      (fun m : ℕ =>
        Real.Gamma ((m : ℝ) / (n : ℝ)))
      1 (m := n) (n := n) (by omega)
  simpa only [Nat.add_sub_cancel_left,
    Nat.add_sub_cancel] using hreflect.symm

private lemma gamma_pair (n m : ℕ)
    (hn : 0 < n) (hm : m ∈ Finset.Icc 1 (n - 1)) :
    Real.Gamma ((m : ℝ) / (n : ℝ)) *
        Real.Gamma (((n - m : ℕ) : ℝ) / (n : ℝ)) =
      Real.pi /
        Real.sin ((m : ℝ) * Real.pi / (n : ℝ)) := by
  have hmn : m ≤ n := by
    have hmle := (Finset.mem_Icc.mp hm).2
    omega
  have hnR : (n : ℝ) ≠ 0 := by
    exact_mod_cast hn.ne'
  have hsub :
      (((n - m : ℕ) : ℝ) / (n : ℝ)) =
        1 - (m : ℝ) / (n : ℝ) := by
    rw [Nat.cast_sub hmn]
    field_simp
  rw [hsub, Real.Gamma_mul_Gamma_one_sub]
  congr 2
  ring

private lemma sine_product_range (n : ℕ) (hn : 0 < n) :
    (∏ k ∈ Finset.range (n - 1),
      Real.sin (((k + 1 : ℕ) : ℝ) *
        Real.pi / (n : ℝ))) =
      (n : ℝ) / (2 : ℝ) ^ (n - 1) := by
  let μ : ℂ :=
    Complex.exp (2 * Real.pi * Complex.I / (n : ℂ))
  have hμ : IsPrimitiveRoot μ n :=
    Complex.isPrimitiveRoot_exp n hn.ne'
  have horder : n - 1 + 1 = n :=
    Nat.sub_add_cancel hn
  have hμ' : IsPrimitiveRoot μ (n - 1 + 1) := by
    simpa only [horder] using hμ
  have hprodC := hμ'.prod_one_sub_pow_eq_order
  have hnorm := congrArg norm hprodC
  simp only [norm_prod, norm_natCast] at hnorm
  have hfactor (k : ℕ)
      (hk : k ∈ Finset.range (n - 1)) :
      ‖(1 : ℂ) - μ ^ (k + 1)‖ =
        2 * Real.sin (((k + 1 : ℕ) : ℝ) *
          Real.pi / (n : ℝ)) := by
    have hk1lt : k + 1 < n := by
      simp only [Finset.mem_range] at hk
      omega
    have hspos :
        0 < Real.sin (((k + 1 : ℕ) : ℝ) *
          Real.pi / (n : ℝ)) := by
      apply Real.sin_pos_of_pos_of_lt_pi
      · positivity
      · have hnR : (0 : ℝ) < n := by
          exact_mod_cast hn
        have hkR : ((k + 1 : ℕ) : ℝ) < n := by
          exact_mod_cast hk1lt
        rw [div_lt_iff₀ hnR]
        simpa only [mul_comm] using
          mul_lt_mul_of_pos_right hkR Real.pi_pos
    rw [norm_sub_rev]
    have hpow :
        μ ^ (k + 1) =
          Complex.exp
            (Complex.I *
              ((((2 : ℝ) * Real.pi *
                ((k + 1 : ℕ) : ℝ)) /
                (n : ℝ) : ℝ) : ℂ)) := by
      dsimp [μ]
      rw [← Complex.exp_nat_mul]
      congr 1
      push_cast
      field_simp
    rw [hpow, Complex.norm_exp_I_mul_ofReal_sub_one]
    norm_num
    rw [abs_of_pos]
    · congr 1 <;> ring
    · convert hspos using 1
      congr 1
      push_cast
      ring
  rw [Finset.prod_congr rfl hfactor] at hnorm
  rw [Finset.prod_mul_distrib] at hnorm
  simp only [Finset.prod_const,
    Finset.card_range] at hnorm
  have hrhs :
      ‖((n - 1 : ℕ) : ℂ) + 1‖ = (n : ℝ) := by
    have hcast :
        (((n - 1 : ℕ) : ℂ) + 1) = (n : ℂ) := by
      exact_mod_cast horder
    rw [hcast]
    simp
  rw [hrhs] at hnorm
  have hpow2 : (2 : ℝ) ^ (n - 1) ≠ 0 :=
    pow_ne_zero _ (by norm_num)
  field_simp [hpow2]
  nlinarith

private lemma sineProduct_eq (n : ℕ) (hn : 0 < n) :
    sineProduct n =
      (n : ℝ) / (2 : ℝ) ^ (n - 1) := by
  unfold sineProduct
  rw [← Finset.Ico_succ_right_eq_Icc 1 (n - 1)]
  have htop : Order.succ (n - 1) = n := by
    change Nat.succ (n - 1) = n
    omega
  rw [htop, Finset.prod_Ico_eq_prod_range]
  simpa only [Nat.add_comm] using
    sine_product_range n hn

private lemma E_sq (n : ℕ) (hn : 0 < n) :
    E n ^ 2 =
      Real.pi ^ (n - 1) / sineProduct n := by
  rw [pow_two]
  nth_rw 2 [E_reflect n hn]
  unfold E
  rw [← Finset.prod_mul_distrib]
  rw [Finset.prod_congr rfl
    (fun m hm => gamma_pair n m hn hm)]
  rw [Finset.prod_div_distrib]
  simp only [Finset.prod_const, Nat.card_Icc]
  have hcard : n - 1 + 1 - 1 = n - 1 := by
    omega
  rw [hcard]
  rfl

private lemma E_pos (n : ℕ) (hn : 0 < n) :
    0 < E n := by
  unfold E
  apply Finset.prod_pos
  intro m hm
  apply Real.Gamma_pos_of_pos
  apply div_pos
  · exact_mod_cast (Finset.mem_Icc.mp hm).1
  · exact_mod_cast hn

private lemma E_eq_closed (n : ℕ) (hn : 0 < n) :
    E n =
      Real.rpow Real.pi (((n : ℝ) - 1) / 2) *
        Real.rpow
          ((2 : ℝ) ^ (n - 1) / (n : ℝ))
          (1 / 2 : ℝ) := by
  have hEpos := E_pos n hn
  have hsq := E_sq n hn
  rw [sineProduct_eq n hn] at hsq
  have hnR : (0 : ℝ) < n := by
    exact_mod_cast hn
  have hsq' :
      E n ^ 2 =
        Real.pi ^ (n - 1) *
          ((2 : ℝ) ^ (n - 1) / (n : ℝ)) := by
    rw [hsq]
    field_simp
  have hroot :=
    Real.pow_rpow_inv_natCast hEpos.le
      (n := 2) (by norm_num : (2 : ℕ) ≠ 0)
  norm_num at hroot
  rw [hsq'] at hroot
  calc
    E n =
        (Real.pi ^ (n - 1) *
          ((2 : ℝ) ^ (n - 1) / (n : ℝ))) ^
            (1 / 2 : ℝ) := hroot.symm
    _ =
        (Real.pi ^ (n - 1)) ^ (1 / 2 : ℝ) *
          ((2 : ℝ) ^ (n - 1) / (n : ℝ)) ^
            (1 / 2 : ℝ) := by
      rw [Real.mul_rpow]
      · positivity
      · positivity
    _ =
        Real.pi ^ (((n : ℝ) - 1) / 2) *
          ((2 : ℝ) ^ (n - 1) / (n : ℝ)) ^
            (1 / 2 : ℝ) := by
      congr 1
      rw [← Real.rpow_natCast_mul Real.pi_pos.le]
      congr 1
      rw [Nat.cast_sub (show 1 ≤ n by omega)]
      ring

private lemma final_algebra (n : ℕ) (hn : 0 < n) :
    1 / (n : ℝ) ^ n *
          Real.rpow Real.pi (((n : ℝ) - 1) / 2) *
          Real.rpow
            ((2 : ℝ) ^ (n - 1) / (n : ℝ))
            (1 / 2 : ℝ) =
      Real.rpow (1 / (n : ℝ))
          ((n : ℝ) + 1 / 2) *
        Real.rpow (2 * Real.pi)
          (((n : ℝ) - 1) / 2) := by
  have hnR : (0 : ℝ) < n := by
    exact_mod_cast hn
  have hb : 0 < 1 / (n : ℝ) :=
    one_div_pos.mpr hnR
  have htwoPow :
      ((2 : ℝ) ^ (n - 1)) ^ (1 / 2 : ℝ) =
        (2 : ℝ) ^ (((n : ℝ) - 1) / 2) := by
    rw [← Real.rpow_natCast_mul
      (show (0 : ℝ) ≤ 2 by norm_num)]
    congr 1
    rw [Nat.cast_sub (show 1 ≤ n by omega)]
    ring
  have honeDiv :
      (1 / (n : ℝ)) ^ (1 / 2 : ℝ) =
        1 / ((n : ℝ) ^ (1 / 2 : ℝ)) := by
    rw [Real.div_rpow (by norm_num) hnR.le]
    simp
  have hC :
      ((2 : ℝ) ^ (n - 1) / (n : ℝ)) ^
          (1 / 2 : ℝ) =
        (2 : ℝ) ^ (((n : ℝ) - 1) / 2) *
          (1 / (n : ℝ)) ^ (1 / 2 : ℝ) := by
    rw [Real.div_rpow (by positivity) hnR.le,
      htwoPow, honeDiv]
    ring
  rw [← one_div_pow]
  change
    (1 / (n : ℝ)) ^ n *
        (Real.pi ^ (((n : ℝ) - 1) / 2 : ℝ)) *
        (((2 : ℝ) ^ (n - 1) / (n : ℝ)) ^
          (1 / 2 : ℝ)) =
      (1 / (n : ℝ)) ^
          ((n : ℝ) + 1 / 2 : ℝ) *
        (2 * Real.pi) ^
          (((n : ℝ) - 1) / 2 : ℝ)
  rw [hC, ← Real.rpow_natCast
    (1 / (n : ℝ)) n]
  calc
    (1 / (n : ℝ)) ^ (n : ℝ) *
        Real.pi ^ (((n : ℝ) - 1) / 2) *
        ((2 : ℝ) ^ (((n : ℝ) - 1) / 2) *
          (1 / (n : ℝ)) ^ (1 / 2 : ℝ)) =
      ((1 / (n : ℝ)) ^ (n : ℝ) *
          (1 / (n : ℝ)) ^ (1 / 2 : ℝ)) *
        ((2 : ℝ) ^ (((n : ℝ) - 1) / 2) *
          Real.pi ^ (((n : ℝ) - 1) / 2)) := by
      ring
    _ =
      (1 / (n : ℝ)) ^ ((n : ℝ) + 1 / 2) *
        ((2 : ℝ) * Real.pi) ^
          (((n : ℝ) - 1) / 2) := by
      rw [Real.rpow_add hb,
        Real.mul_rpow (by norm_num) Real.pi_pos.le]

private def rootOfUnity (n : ℕ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I / (n : ℂ))

private lemma rootOfUnity_pow_eq
    (n m : ℕ) (hn : 0 < n) :
    rootOfUnity n ^ m =
      (Real.cos
          (2 * (m : ℝ) * Real.pi / (n : ℝ)) : ℂ) +
        Complex.I *
          (Real.sin
            (2 * (m : ℝ) * Real.pi / (n : ℝ)) : ℂ) := by
  unfold rootOfUnity
  rw [← Complex.exp_nat_mul]
  have hnC : (n : ℂ) ≠ 0 := by
    exact_mod_cast hn.ne'
  have harg :
      (m : ℂ) *
          (2 * Real.pi * Complex.I / (n : ℂ)) =
        (((2 * (m : ℝ) * Real.pi / (n : ℝ)) : ℝ) : ℂ) *
          Complex.I := by
    push_cast
    field_simp [hnC]
  rw [harg, Complex.exp_mul_I]
  push_cast
  ring

private lemma root_product_eq_range
    (n : ℕ) (hn : 0 < n) (z : ℂ) :
    (∏ m ∈ Finset.Icc 1 (n - 1),
        (z -
          ((Real.cos
              (2 * (m : ℝ) * Real.pi / (n : ℝ)) : ℂ) +
            Complex.I *
              (Real.sin
                (2 * (m : ℝ) * Real.pi / (n : ℝ)) : ℂ)))) =
      ∏ k ∈ Finset.range (n - 1),
        (z - rootOfUnity n ^ (k + 1)) := by
  rw [← Finset.Ico_succ_right_eq_Icc 1 (n - 1)]
  have htop : Order.succ (n - 1) = n := by
    change Nat.succ (n - 1) = n
    omega
  rw [htop, Finset.prod_Ico_eq_prod_range]
  apply Finset.prod_congr rfl
  intro k hk
  rw [Nat.add_comm 1 k,
    rootOfUnity_pow_eq n (k + 1) hn]

private lemma rootDistanceProduct_eq_range
    (n : ℕ) (hn : 0 < n) :
    rootDistanceProduct n =
      ∏ k ∈ Finset.range (n - 1),
        ‖(1 : ℂ) - rootOfUnity n ^ (k + 1)‖ := by
  unfold rootDistanceProduct
  rw [← Finset.Ico_succ_right_eq_Icc 1 (n - 1)]
  have htop : Order.succ (n - 1) = n := by
    change Nat.succ (n - 1) = n
    omega
  rw [htop, Finset.prod_Ico_eq_prod_range]
  apply Finset.prod_congr rfl
  intro k hk
  rw [Nat.add_comm 1 k,
    rootOfUnity_pow_eq n (k + 1) hn]

private lemma root_norm_factor
    (n m : ℕ) (hn : 0 < n)
    (hm : m ∈ Finset.Icc 1 (n - 1)) :
    ‖
      ((1 : ℂ) -
        ((Real.cos
            (2 * (m : ℝ) * Real.pi / (n : ℝ)) : ℂ) +
          Complex.I *
            (Real.sin
              (2 * (m : ℝ) * Real.pi / (n : ℝ)) : ℂ)))‖ =
      2 * Real.sin
        ((m : ℝ) * Real.pi / (n : ℝ)) := by
  have hmpos : 0 < m :=
    (Finset.mem_Icc.mp hm).1
  have hmlt : m < n := by
    have hmle := (Finset.mem_Icc.mp hm).2
    omega
  have hspos :
      0 < Real.sin
        ((m : ℝ) * Real.pi / (n : ℝ)) := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · positivity
    · have hnR : (0 : ℝ) < n := by
        exact_mod_cast hn
      have hmR : (m : ℝ) < n := by
        exact_mod_cast hmlt
      rw [div_lt_iff₀ hnR]
      simpa only [mul_comm] using
        mul_lt_mul_of_pos_right hmR Real.pi_pos
  rw [← rootOfUnity_pow_eq n m hn, norm_sub_rev]
  have hpow :
      rootOfUnity n ^ m =
        Complex.exp
          (Complex.I *
            (((2 * (m : ℝ) * Real.pi /
              (n : ℝ)) : ℝ) : ℂ)) := by
    unfold rootOfUnity
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    field_simp
  rw [hpow, Complex.norm_exp_I_mul_ofReal_sub_one]
  norm_num
  rw [abs_of_pos]
  · congr 1
    ring
  · convert hspos using 1
    congr 1
    ring

theorem gap1 (n : ℕ) (hn : 0 < n) :
    (∏ m ∈ Finset.Icc 1 n, J n m) =
      ∏ m ∈ Finset.Icc 1 n,
        ((1 / (n : ℝ)) * Real.Gamma ((m : ℝ) / (n : ℝ))) := by
  apply Finset.prod_congr rfl
  intro m hm
  exact J_eq n m hn (Finset.mem_Icc.mp hm).1

theorem gap2 (n : ℕ) (hn : 0 < n) :
    (∏ m ∈ Finset.Icc 1 n,
        ((1 / (n : ℝ)) * Real.Gamma ((m : ℝ) / (n : ℝ)))) =
      (1 / (n : ℝ)) ^ n * E n := by
  rw [Finset.prod_mul_distrib]
  simp only [Finset.prod_const, Nat.card_Icc]
  have hcard : n + 1 - 1 = n := by
    omega
  rw [hcard, gamma_product_Icc_eq_E n hn]

theorem gap3 (n : ℕ) (hn : 0 < n) :
    (∏ m ∈ Finset.Icc 1 n, J n m) =
      (1 / (n : ℝ)) ^ n * E n := by
  rw [gap1 n hn, gap2 n hn]

theorem gap4 (n : ℕ) (hn : 0 < n) :
    E n =
      ∏ m ∈ Finset.Icc 1 (n - 1),
        Real.Gamma (((n - m : ℕ) : ℝ) / (n : ℝ)) := by
  exact E_reflect n hn

theorem gap5 (n : ℕ) (hn : 0 < n) :
    E n ^ 2 =
      ∏ m ∈ Finset.Icc 1 (n - 1),
        (Real.Gamma ((m : ℝ) / (n : ℝ)) *
          Real.Gamma (((n - m : ℕ) : ℝ) / (n : ℝ))) := by
  rw [pow_two]
  nth_rw 2 [gap4 n hn]
  unfold E
  rw [← Finset.prod_mul_distrib]

theorem gap6 (n : ℕ) (hn : 0 < n) :
    (∏ m ∈ Finset.Icc 1 (n - 1),
        (Real.Gamma ((m : ℝ) / (n : ℝ)) *
          Real.Gamma (((n - m : ℕ) : ℝ) / (n : ℝ)))) =
      ∏ m ∈ Finset.Icc 1 (n - 1),
        (Real.pi /
          Real.sin ((m : ℝ) * Real.pi / (n : ℝ))) := by
  apply Finset.prod_congr rfl
  intro m hm
  exact gamma_pair n m hn hm

theorem gap7 (n : ℕ) (hn : 0 < n) :
    (∏ m ∈ Finset.Icc 1 (n - 1),
        (Real.pi /
          Real.sin ((m : ℝ) * Real.pi / (n : ℝ)))) =
      Real.pi ^ (n - 1) / sineProduct n := by
  unfold sineProduct
  rw [Finset.prod_div_distrib]
  simp only [Finset.prod_const, Nat.card_Icc]
  have hcard : n - 1 + 1 - 1 = n - 1 := by
    omega
  rw [hcard]

theorem gap8 (n : ℕ) (hn : 0 < n) :
    E n ^ 2 = Real.pi ^ (n - 1) / sineProduct n := by
  exact E_sq n hn

theorem gap9 (n : ℕ) (hn : 0 < n) (z : ℂ) (hz : z ≠ 1) :
    (z ^ n - 1) / (z - 1) =
      ∏ m ∈ Finset.Icc 1 (n - 1),
        (z -
          ((Real.cos (2 * (m : ℝ) * Real.pi / (n : ℝ)) : ℂ) +
            Complex.I *
              (Real.sin (2 * (m : ℝ) * Real.pi / (n : ℝ)) : ℂ))) := by
  have hμ :
      IsPrimitiveRoot (rootOfUnity n) n := by
    exact Complex.isPrimitiveRoot_exp n hn.ne'
  have hpoly :=
    X_pow_sub_C_eq_prod hμ hn
      (show (1 : ℂ) ^ n = 1 by simp)
  apply_fun Polynomial.eval z at hpoly
  simp only [Polynomial.eval_sub, Polynomial.eval_pow,
    Polynomial.eval_X, Polynomial.eval_C,
    Polynomial.eval_prod, one_pow, mul_one] at hpoly
  have horder : n - 1 + 1 = n :=
    Nat.sub_add_cancel hn
  have hsplit :=
    Finset.prod_range_succ'
      (fun k : ℕ =>
        z - rootOfUnity n ^ k) (n - 1)
  rw [horder] at hsplit
  rw [hsplit] at hpoly
  simp only [pow_zero, sub_one_mul] at hpoly
  have hz1 : z - 1 ≠ 0 :=
    sub_ne_zero.mpr hz
  calc
    (z ^ n - 1) / (z - 1) =
        ∏ k ∈ Finset.range (n - 1),
          (z - rootOfUnity n ^ (k + 1)) := by
      rw [hpoly]
      field_simp [hz1]
    _ = ∏ m ∈ Finset.Icc 1 (n - 1),
        (z -
          ((Real.cos
              (2 * (m : ℝ) * Real.pi / (n : ℝ)) : ℂ) +
            Complex.I *
              (Real.sin
                (2 * (m : ℝ) * Real.pi / (n : ℝ)) : ℂ))) :=
      (root_product_eq_range n hn z).symm

theorem gap10 (n : ℕ) (hn : 0 < n) :
    (n : ℝ) = rootDistanceProduct n := by
  have hμ :
      IsPrimitiveRoot (rootOfUnity n) n := by
    exact Complex.isPrimitiveRoot_exp n hn.ne'
  have horder : n - 1 + 1 = n :=
    Nat.sub_add_cancel hn
  have hμ' :
      IsPrimitiveRoot (rootOfUnity n) (n - 1 + 1) := by
    simpa only [horder] using hμ
  have hprod := hμ'.prod_one_sub_pow_eq_order
  have hnorm := congrArg norm hprod
  simp only [norm_prod] at hnorm
  have hrhs :
      ‖((n - 1 : ℕ) : ℂ) + 1‖ = (n : ℝ) := by
    have hcast :
        (((n - 1 : ℕ) : ℂ) + 1) = (n : ℂ) := by
      exact_mod_cast horder
    rw [hcast]
    simp
  rw [hrhs] at hnorm
  rw [rootDistanceProduct_eq_range n hn]
  exact hnorm.symm

theorem gap11 (n : ℕ) (hn : 0 < n) :
    rootDistanceProduct n =
      (2 : ℝ) ^ (n - 1) * sineProduct n := by
  unfold rootDistanceProduct sineProduct
  rw [Finset.prod_congr rfl
    (fun m hm => root_norm_factor n m hn hm)]
  rw [Finset.prod_mul_distrib]
  simp only [Finset.prod_const, Nat.card_Icc]
  have hcard : n - 1 + 1 - 1 = n - 1 := by
    omega
  rw [hcard]

theorem gap12 (n : ℕ) (hn : 0 < n) :
    (n : ℝ) = (2 : ℝ) ^ (n - 1) * sineProduct n := by
  rw [gap10 n hn, gap11 n hn]

theorem gap13 (n : ℕ) (hn : 0 < n) :
    sineProduct n = (n : ℝ) / (2 : ℝ) ^ (n - 1) := by
  exact sineProduct_eq n hn

theorem gap14 (n : ℕ) (hn : 0 < n) :
    (∏ m ∈ Finset.Icc 1 n, J n m) =
      (1 / (n : ℝ)) ^ n * E n := by
  exact gap3 n hn

theorem gap15 (n : ℕ) (hn : 0 < n) :
    (1 / (n : ℝ)) ^ n * E n =
      1 / (n : ℝ) ^ n *
        Real.rpow Real.pi (((n : ℝ) - 1) / 2) *
          Real.rpow
            ((2 : ℝ) ^ (n - 1) / (n : ℝ)) (1 / 2 : ℝ) := by
  rw [E_eq_closed n hn]
  ring

theorem gap16 (n : ℕ) (hn : 0 < n) :
    1 / (n : ℝ) ^ n *
          Real.rpow Real.pi (((n : ℝ) - 1) / 2) *
          Real.rpow
            ((2 : ℝ) ^ (n - 1) / (n : ℝ)) (1 / 2 : ℝ) =
      Real.rpow (1 / (n : ℝ)) ((n : ℝ) + 1 / 2) *
        Real.rpow (2 * Real.pi) (((n : ℝ) - 1) / 2) := by
  exact final_algebra n hn

theorem gap17 (n : ℕ) (hn : 0 < n) :
    (∏ m ∈ Finset.Icc 1 n, J n m) =
      Real.rpow (1 / (n : ℝ)) ((n : ℝ) + 1 / 2) *
        Real.rpow (2 * Real.pi) (((n : ℝ) - 1) / 2) := by
  rw [gap14 n hn, gap15 n hn, gap16 n hn]

theorem gap18 (n : ℕ) (hn : 0 < n) :
    (∏ m ∈ Finset.Icc 1 n, J n m) =
      Real.rpow (1 / (n : ℝ)) ((n : ℝ) + 1 / 2) *
        Real.rpow (2 * Real.pi) (((n : ℝ) - 1) / 2) := by
  exact gap17 n hn

end

end ProofGap.Exercise3874
