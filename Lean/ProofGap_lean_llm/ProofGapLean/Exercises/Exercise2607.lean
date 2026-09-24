import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.PSeries

namespace ProofGap.Exercise2607

noncomputable section

open Filter
open scoped BigOperators
open Asymptotics

def monicPoly (d : ℕ) (c : ℕ → ℝ) (x : ℝ) : ℝ :=
  x ^ d + ∑ i ∈ Finset.range d, c i * x ^ i

def term (p q : ℕ) (a b : ℕ → ℝ) (n : ℕ) : ℝ :=
  monicPoly p a n / monicPoly q b n

def comparison (p q : ℕ) (n : ℕ) : ℝ :=
  1 / Real.rpow n ((q : ℝ) - p)

def converges (p q : ℕ) (a b : ℕ → ℝ) : Prop :=
  Summable (fun n : ℕ => term p q a b (n + 1))

private def normalizedPoly (d : ℕ) (c : ℕ → ℝ) (n : ℕ) : ℝ :=
  monicPoly d c (n + 1) / ((n + 1 : ℕ) : ℝ) ^ d

private theorem normalizedPoly_tendsto (d : ℕ) (c : ℕ → ℝ) :
    Tendsto (normalizedPoly d c) atTop (nhds 1) := by
  have hcast : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
  have hsum : Tendsto (fun n : ℕ => ∑ i ∈ Finset.range d,
      c i * (((n : ℝ) + 1) ^ i / ((n : ℝ) + 1) ^ d)) atTop (nhds 0) := by
    convert tendsto_finset_sum (Finset.range d) (by
      intro i hi
      have hiD : i < d := Finset.mem_range.mp hi
      simpa using Filter.Tendsto.const_mul (c i)
        ((tendsto_pow_div_pow_atTop_zero hiD).comp hcast)) using 1 <;> simp
  have hone : Tendsto (fun n : ℕ => 1 + ∑ i ∈ Finset.range d,
      c i * (((n : ℝ) + 1) ^ i / ((n : ℝ) + 1) ^ d)) atTop (nhds 1) := by
    simpa using tendsto_const_nhds.add hsum
  apply hone.congr'
  filter_upwards [] with n
  unfold normalizedPoly monicPoly
  simp only [Nat.cast_add, Nat.cast_one]
  have hx : ((n : ℝ) + 1) ^ d ≠ 0 := pow_ne_zero _ (by positivity)
  rw [add_div, div_self hx, Finset.sum_div]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  ring

private theorem comparison_eq_rpow (p q n : ℕ) (hn : 1 ≤ n) :
    comparison p q n = Real.rpow n ((p : ℝ) - q) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hqp : Real.rpow n ((q : ℝ) - p) =
      Real.rpow n q / Real.rpow n p := Real.rpow_sub hnpos q p
  have hpq : Real.rpow n ((p : ℝ) - q) =
      Real.rpow n p / Real.rpow n q := Real.rpow_sub hnpos p q
  have hpne : Real.rpow n p ≠ 0 := (Real.rpow_pos_of_pos hnpos p).ne'
  have hqne : Real.rpow n q ≠ 0 := (Real.rpow_pos_of_pos hnpos q).ne'
  unfold comparison
  rw [hqp, hpq]
  field_simp [hpne, hqne]

private theorem comparison_eq_pow_div (p q n : ℕ) (hn : 1 ≤ n) :
    comparison p q n = (n : ℝ) ^ p / (n : ℝ) ^ q := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hrsub : Real.rpow n ((q : ℝ) - p) =
      Real.rpow n q / Real.rpow n p := Real.rpow_sub hnpos q p
  have hq : Real.rpow n q = (n : ℝ) ^ q := Real.rpow_natCast (n : ℝ) q
  have hp : Real.rpow n p = (n : ℝ) ^ p := Real.rpow_natCast (n : ℝ) p
  unfold comparison
  rw [hrsub, hq, hp]
  have hpn : (n : ℝ) ^ p ≠ 0 := pow_ne_zero _ hnpos.ne'
  have hqn : (n : ℝ) ^ q ≠ 0 := pow_ne_zero _ hnpos.ne'
  field_simp [hpn, hqn]

private theorem term_isEquivalent_comparison (p q : ℕ) (a b : ℕ → ℝ)
    (hden : ∀ x ≥ 1, 0 < monicPoly q b x) :
    (fun n : ℕ => term p q a b (n + 1)) ~[atTop]
      (fun n : ℕ => comparison p q (n + 1)) := by
  have hcompNe : ∀ᶠ n : ℕ in atTop, comparison p q (n + 1) ≠ 0 :=
    Filter.Eventually.of_forall (fun n => by
      unfold comparison
      exact one_div_ne_zero (Real.rpow_pos_of_pos (by positivity) _).ne')
  apply (isEquivalent_iff_tendsto_one hcompNe).2
  have hquot : Tendsto (fun n : ℕ =>
      normalizedPoly p a n / normalizedPoly q b n) atTop (nhds 1) := by
    convert (normalizedPoly_tendsto p a).div (normalizedPoly_tendsto q b) one_ne_zero
      using 1 <;> norm_num
  apply hquot.congr'
  filter_upwards [] with n
  simp only [Pi.div_apply]
  have hx : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hxp : ((n : ℝ) + 1) ^ p ≠ 0 := pow_ne_zero _ hx.ne'
  have hxq : ((n : ℝ) + 1) ^ q ≠ 0 := pow_ne_zero _ hx.ne'
  have hxone : (1 : ℝ) ≤ (n : ℝ) + 1 := by
    have hn0 : (0 : ℝ) ≤ n := by positivity
    linarith
  have hQ : monicPoly q b ((n : ℝ) + 1) ≠ 0 :=
    (hden ((n : ℝ) + 1) hxone).ne'
  unfold term normalizedPoly
  simp only [Nat.cast_add, Nat.cast_one]
  rw [comparison_eq_pow_div p q (n + 1) (by omega)]
  simp only [Nat.cast_add, Nat.cast_one]
  field_simp [hxp, hxq, hQ]

private theorem summable_comparison_iff (p q : ℕ) :
    Summable (fun n : ℕ => comparison p q (n + 1)) ↔ p + 1 < q := by
  let e : ℝ := (p : ℝ) - q
  constructor
  · intro hcomp
    have hshift : Summable (fun n : ℕ => Real.rpow (n + 1 : ℕ) e) :=
      hcomp.congr (fun n => comparison_eq_rpow p q (n + 1) (by omega))
    have hall : Summable (fun n : ℕ => Real.rpow n e) :=
      (summable_nat_add_iff 1).mp hshift
    have he := Real.summable_nat_rpow.mp hall
    have hpqReal : (p : ℝ) + 1 < q := by dsimp [e] at he; linarith
    exact_mod_cast hpqReal
  · intro hpq
    have hpqReal : (p : ℝ) + 1 < q := by exact_mod_cast hpq
    have hall : Summable (fun n : ℕ => Real.rpow n e) :=
      Real.summable_nat_rpow.mpr (by dsimp [e]; linarith)
    have hshift : Summable (fun n : ℕ => Real.rpow (n + 1 : ℕ) e) :=
      (summable_nat_add_iff 1).mpr hall
    exact hshift.congr
      (fun n => (comparison_eq_rpow p q (n + 1) (by omega)).symm)

theorem gap1 (p q : ℕ) (a b : ℕ → ℝ)
    (hden : ∀ n ≥ 1, 0 < monicPoly q b n) :
    Asymptotics.IsBigO atTop
      (fun n : ℕ => term p q a b (n + 1))
      (fun n : ℕ => comparison p q (n + 1)) := by
  exact (term_isEquivalent_comparison p q a b hden).isBigO

theorem gap2 (p q : ℕ) (a b : ℕ → ℝ)
    (hden : ∀ n ≥ 1, 0 < monicPoly q b n)
    (hpq : p + 1 < q) :
    converges p q a b := by
  unfold converges
  exact summable_of_isBigO_nat ((summable_comparison_iff p q).2 hpq)
    (gap1 p q a b hden)

theorem gap3 (p q : ℕ) :
    (1 < (q : ℤ) - p) ↔ p + 1 < q := by omega

theorem gap4 (p q : ℕ) (a b : ℕ → ℝ)
    (hden : ∀ n ≥ 1, 0 < monicPoly q b n) :
    converges p q a b ↔ p + 1 < q := by
  constructor
  · intro hconv
    unfold converges at hconv
    have hcomparison : Summable (fun n : ℕ => comparison p q (n + 1)) :=
      summable_of_isBigO_nat hconv
        (term_isEquivalent_comparison p q a b hden).isBigO_symm
    exact (summable_comparison_iff p q).1 hcomparison
  · exact gap2 p q a b hden

end

end ProofGap.Exercise2607
