import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.Real.Pi.Bounds

namespace ProofGap.Exercise1623

noncomputable section

def f (x : ℝ) := Real.cos x * Real.cosh x - 1
def Approx (actual expected tolerance : ℝ) : Prop :=
  |actual - expected| < tolerance
def FirstRoot (α : ℝ) : Prop :=
  α ∈ Set.Ioo (3 * Real.pi / 2) (2 * Real.pi) ∧ f α = 0
def SecondRoot (β : ℝ) : Prop :=
  β ∈ Set.Ioo (2 * Real.pi) (5 * Real.pi / 2) ∧ f β = 0
def ThirdRoot (γ : ℝ) : Prop :=
  γ ∈ Set.Ioo (7 * Real.pi / 2) (4 * Real.pi) ∧ f γ = 0
def tangentApproximant : ℕ → ℝ
  | 1 => 4.7345
  | 2 => 4.7301
  | _ => 0
def chordStep (a b : ℝ) := a - f a / (f b - f a) * (b - a)
def chordApproximant : ℕ → ℝ
  | 1 => 4.7280
  | 2 => 4.7300
  | _ => 0
def thirdApproximant : ℕ → ℝ
  | 1 => 10.9956
  | _ => 0
def ApproxRootPair (sample : ℝ × ℝ) (tolerance : ℝ) : Prop :=
  ∃ α γ, FirstRoot α ∧ ThirdRoot γ ∧
    |sample.1 - α| < tolerance ∧ |sample.2 - γ| < tolerance

private lemma deriv_f (x : ℝ) :
    deriv f x =
      -Real.sin x * Real.cosh x + Real.cos x * Real.sinh x := by
  unfold f
  have hprod := (Real.hasDerivAt_cos x).mul (Real.hasDerivAt_cosh x)
  convert hprod.sub_const 1 |>.deriv using 1 <;> ring

private lemma deriv2_f (x : ℝ) :
    deriv (deriv f) x = -2 * Real.sin x * Real.sinh x := by
  have heq : deriv f = fun y =>
      -Real.sin y * Real.cosh y + Real.cos y * Real.sinh y :=
    funext deriv_f
  rw [heq]
  have hfirst := (Real.hasDerivAt_sin x).neg.mul (Real.hasDerivAt_cosh x)
  have hsecond := (Real.hasDerivAt_cos x).mul (Real.hasDerivAt_sinh x)
  convert (hfirst.add hsecond).deriv using 1 <;> simp <;> ring

private lemma continuous_f : Continuous f := by
  unfold f
  fun_prop

private lemma exists_second_root : ∃ β, SecondRoot β := by
  let l : ℝ := 2 * Real.pi
  let r : ℝ := 5 * Real.pi / 2
  have hlr : l < r := by
    dsimp [l, r]
    nlinarith [Real.pi_pos]
  have hfl : 0 < f l := by
    dsimp [l]
    simp only [f, Real.cos_two_pi, one_mul]
    have hne : (2 * Real.pi : ℝ) ≠ 0 := by positivity
    nlinarith [(Real.one_lt_cosh).2 hne]
  have hfr : f r < 0 := by
    dsimp [r]
    unfold f
    rw [show 5 * Real.pi / 2 = Real.pi / 2 + 2 * Real.pi by ring,
      Real.cos_add_two_pi]
    simp
  have hiv := intermediate_value_Icc' hlr.le continuous_f.continuousOn
  rcases hiv ⟨hfr.le, hfl.le⟩ with ⟨β, hβ, hfβ⟩
  have hβopen : β ∈ Set.Ioo l r := by
    constructor
    · exact lt_of_le_of_ne hβ.1 (by
        intro heq
        subst β
        linarith)
    · exact lt_of_le_of_ne hβ.2 (by
        intro heq
        subst β
        linarith)
  exact ⟨β, hβopen, hfβ⟩

private lemma deriv_f_pos_first (x : ℝ)
    (hx : x ∈ Set.Ioo (3 * Real.pi / 2) (2 * Real.pi)) :
    0 < deriv f x := by
  rw [deriv_f]
  rcases hx with ⟨hxlo, hxhi⟩
  let u := 2 * Real.pi - x
  have hu0 : 0 < u := by dsimp [u]; linarith
  have hupi2 : u < Real.pi / 2 := by
    dsimp [u]
    linarith
  have husin : 0 < Real.sin u :=
    Real.sin_pos_of_pos_of_lt_pi hu0 (lt_trans hupi2 (by nlinarith [Real.pi_pos]))
  have hucos : 0 < Real.cos u :=
    Real.cos_pos_of_mem_Ioo ⟨by nlinarith [Real.pi_pos], hupi2⟩
  have hsin : Real.sin x < 0 := by
    dsimp [u] at husin
    rw [Real.sin_two_pi_sub] at husin
    linarith
  have hcos : 0 < Real.cos x := by
    dsimp [u] at hucos
    rwa [Real.cos_two_pi_sub] at hucos
  have hx0 : 0 < x := by nlinarith [hxlo, Real.pi_pos]
  have hsinh : 0 < Real.sinh x := (Real.sinh_pos_iff).2 hx0
  have hcosh : 0 < Real.cosh x := Real.cosh_pos x
  exact add_pos (mul_pos (neg_pos.mpr hsin) hcosh) (mul_pos hcos hsinh)

private lemma strictMono_f_first :
    StrictMonoOn f (Set.Ioo (3 * Real.pi / 2) (2 * Real.pi)) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioo _ _)
  · exact continuous_f.continuousOn
  · intro x hx
    exact deriv_f_pos_first x (by simpa using hx)

private lemma deriv_f_pos_third (x : ℝ)
    (hx : x ∈ Set.Ioo (7 * Real.pi / 2) (4 * Real.pi)) :
    0 < deriv f x := by
  rw [deriv_f]
  rcases hx with ⟨hxlo, hxhi⟩
  let u := 4 * Real.pi - x
  have hu0 : 0 < u := by dsimp [u]; linarith
  have hupi2 : u < Real.pi / 2 := by
    dsimp [u]
    linarith
  have husin : 0 < Real.sin u :=
    Real.sin_pos_of_pos_of_lt_pi hu0 (lt_trans hupi2 (by nlinarith [Real.pi_pos]))
  have hucos : 0 < Real.cos u :=
    Real.cos_pos_of_mem_Ioo ⟨by nlinarith [Real.pi_pos], hupi2⟩
  have hsin : Real.sin x < 0 := by
    dsimp [u] at husin
    rw [show 4 * Real.pi - x = (2 * Real.pi - x) + 2 * Real.pi by ring,
      Real.sin_add_two_pi, Real.sin_two_pi_sub] at husin
    linarith
  have hcos : 0 < Real.cos x := by
    dsimp [u] at hucos
    rw [show 4 * Real.pi - x = (2 * Real.pi - x) + 2 * Real.pi by ring,
      Real.cos_add_two_pi, Real.cos_two_pi_sub] at hucos
    exact hucos
  have hx0 : 0 < x := by nlinarith [hxlo, Real.pi_pos]
  have hsinh : 0 < Real.sinh x := (Real.sinh_pos_iff).2 hx0
  have hcosh : 0 < Real.cosh x := Real.cosh_pos x
  exact add_pos (mul_pos (neg_pos.mpr hsin) hcosh) (mul_pos hcos hsinh)

private lemma strictMono_f_third :
    StrictMonoOn f (Set.Ioo (7 * Real.pi / 2) (4 * Real.pi)) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioo _ _)
  · exact continuous_f.continuousOn
  · intro x hx
    exact deriv_f_pos_third x (by simpa using hx)

private lemma exp_eq_pow_six (x : ℝ) :
    Real.exp x = (Real.exp (x / 6)) ^ (6 : ℕ) := by
  rw [← Real.exp_nat_mul]
  congr 1
  ring

private lemma exp_eq_pow_sixteen (x : ℝ) :
    Real.exp x = (Real.exp (x / 16)) ^ (16 : ℕ) := by
  rw [← Real.exp_nat_mul]
  congr 1
  ring

private lemma exp_small_bounds_14 {x l u : ℝ}
    (hx : |x| ≤ 1)
    (hl : l <
      Finset.sum (Finset.range 14)
          (fun m => x ^ m / (Nat.factorial m : ℝ)) -
        |x| ^ 14 * ((15 : ℝ) / ((Nat.factorial 14 : ℝ) * 14)))
    (hu :
      Finset.sum (Finset.range 14)
          (fun m => x ^ m / (Nat.factorial m : ℝ)) +
        |x| ^ 14 * ((15 : ℝ) / ((Nat.factorial 14 : ℝ) * 14)) < u) :
    l < Real.exp x ∧ Real.exp x < u := by
  have h := Real.exp_bound (x := x) (n := 14) hx (by norm_num)
  rw [abs_le] at h
  constructor <;> nlinarith [h.1, h.2]

private lemma exp47_bounds :
    (1099471 / 10000 : ℝ) < Real.exp 4.7 ∧
      Real.exp 4.7 < (1099473 / 10000 : ℝ) := by
  have h := exp_small_bounds_14
    (x := (47 / 60 : ℝ))
    (l := (21887559 / 10000000 : ℝ))
    (u := (21887561 / 10000000 : ℝ))
    (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])
    (by norm_num [Finset.sum_range_succ, Nat.factorial])
  rcases h with ⟨hlo, hhi⟩
  rw [exp_eq_pow_six]
  norm_num at ⊢
  constructor
  · calc
      _ < (21887559 / 10000000 : ℝ) ^ (6 : ℕ) := by norm_num
      _ < _ := by gcongr
  · calc
      _ < (21887561 / 10000000 : ℝ) ^ (6 : ℕ) := by gcongr
      _ < _ := by norm_num

private lemma exp48_bounds :
    (1215103 / 10000 : ℝ) < Real.exp 4.8 ∧
      Real.exp 4.8 < (1215106 / 10000 : ℝ) := by
  have h := exp_small_bounds_14
    (x := (4 / 5 : ℝ))
    (l := (22255408 / 10000000 : ℝ))
    (u := (22255411 / 10000000 : ℝ))
    (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])
    (by norm_num [Finset.sum_range_succ, Nat.factorial])
  rcases h with ⟨hlo, hhi⟩
  rw [exp_eq_pow_six]
  norm_num at ⊢
  constructor
  · calc
      _ < (22255408 / 10000000 : ℝ) ^ (6 : ℕ) := by norm_num
      _ < _ := by gcongr
  · calc
      _ < (22255411 / 10000000 : ℝ) ^ (6 : ℕ) := by gcongr
      _ < _ := by norm_num

private lemma exp4728_bounds :
    (1130691 / 10000 : ℝ) < Real.exp 4.728 ∧
      Real.exp 4.728 < (1130693 / 10000 : ℝ) := by
  have h := exp_small_bounds_14
    (x := (197 / 250 : ℝ))
    (l := (21989939 / 10000000 : ℝ))
    (u := (21989942 / 10000000 : ℝ))
    (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])
    (by norm_num [Finset.sum_range_succ, Nat.factorial])
  rcases h with ⟨hlo, hhi⟩
  rw [exp_eq_pow_six]
  norm_num at hlo hhi ⊢
  have hhi' : Real.exp (197 / 250 : ℝ) <
      (21989942 / 10000000 : ℝ) := by
    norm_num at hhi ⊢
    exact hhi
  constructor
  · calc
      _ < (21989939 / 10000000 : ℝ) ^ (6 : ℕ) := by norm_num
      _ < _ := by gcongr
  · calc
      _ < (21989942 / 10000000 : ℝ) ^ (6 : ℕ) := by gcongr
      _ < _ := by norm_num

private lemma exp47345_bounds :
    (1138064 / 10000 : ℝ) < Real.exp 4.7345 ∧
      Real.exp 4.7345 < (1138067 / 10000 : ℝ) := by
  have h := exp_small_bounds_14
    (x := (47345 / 60000 : ℝ))
    (l := (22013774 / 10000000 : ℝ))
    (u := (22013778 / 10000000 : ℝ))
    (by rw [abs_of_nonneg (by norm_num)]; norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])
    (by norm_num [Finset.sum_range_succ, Nat.factorial])
  rcases h with ⟨hlo, hhi⟩
  rw [exp_eq_pow_six]
  norm_num at hlo hhi ⊢
  have hlo' : (22013774 / 10000000 : ℝ) <
      Real.exp (9469 / 12000 : ℝ) := by
    norm_num at hlo ⊢
    exact hlo
  have hhi' : Real.exp (9469 / 12000 : ℝ) <
      (22013778 / 10000000 : ℝ) := by
    norm_num at hhi ⊢
    exact hhi
  constructor
  · calc
      _ < (22013774 / 10000000 : ℝ) ^ (6 : ℕ) := by norm_num
      _ < _ := by gcongr
  · calc
      _ < (22013778 / 10000000 : ℝ) ^ (6 : ℕ) := by gcongr
      _ < _ := by norm_num

private lemma exp473_bounds :
    (1132954 / 10000 : ℝ) < Real.exp 4.730 ∧
      Real.exp 4.730 < (1132957 / 10000 : ℝ) := by
  have h := exp_small_bounds_14
    (x := (473 / 600 : ℝ))
    (l := (21997270 / 10000000 : ℝ))
    (u := (21997273 / 10000000 : ℝ))
    (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])
    (by norm_num [Finset.sum_range_succ, Nat.factorial])
  rcases h with ⟨hlo, hhi⟩
  rw [exp_eq_pow_six]
  norm_num at ⊢
  constructor
  · calc
      _ < (21997270 / 10000000 : ℝ) ^ (6 : ℕ) := by norm_num
      _ < _ := by gcongr
  · calc
      _ < (21997273 / 10000000 : ℝ) ^ (6 : ℕ) := by gcongr
      _ < _ := by norm_num

private lemma exp47301_bounds :
    (1133067 / 10000 : ℝ) < Real.exp 4.7301 ∧
      Real.exp 4.7301 < (1133071 / 10000 : ℝ) := by
  have h := exp_small_bounds_14
    (x := (15767 / 20000 : ℝ))
    (l := (21997636 / 10000000 : ℝ))
    (u := (21997640 / 10000000 : ℝ))
    (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])
    (by norm_num [Finset.sum_range_succ, Nat.factorial])
  rcases h with ⟨hlo, hhi⟩
  rw [exp_eq_pow_six]
  norm_num at ⊢
  constructor
  · calc
      _ < (21997636 / 10000000 : ℝ) ^ (6 : ℕ) := by norm_num
      _ < _ := by gcongr
  · calc
      _ < (21997640 / 10000000 : ℝ) ^ (6 : ℕ) := by gcongr
      _ < _ := by norm_num

private lemma exp11_bounds :
    (59874 : ℝ) < Real.exp 11 ∧ Real.exp 11 < (59875 : ℝ) := by
  have h := exp_small_bounds_14
    (x := (11 / 16 : ℝ))
    (l := (19887374 / 10000000 : ℝ))
    (u := (19887376 / 10000000 : ℝ))
    (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])
    (by norm_num [Finset.sum_range_succ, Nat.factorial])
  rcases h with ⟨hlo, hhi⟩
  rw [exp_eq_pow_sixteen]
  norm_num at ⊢
  constructor
  · calc
      _ < (19887374 / 10000000 : ℝ) ^ (16 : ℕ) := by norm_num
      _ < _ := by gcongr
  · calc
      _ < (19887376 / 10000000 : ℝ) ^ (16 : ℕ) := by gcongr
      _ < _ := by norm_num

private lemma exp8_gt : (2900 : ℝ) < Real.exp 8 := by
  have h := exp_small_bounds_14
    (x := (4 / 5 : ℝ))
    (l := (22255408 / 10000000 : ℝ))
    (u := (22255411 / 10000000 : ℝ))
    (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])
    (by norm_num [Finset.sum_range_succ, Nat.factorial])
  rcases h with ⟨hlo, hhi⟩
  have heq : Real.exp 8 = (Real.exp (4 / 5 : ℝ)) ^ (10 : ℕ) := by
    rw [← Real.exp_nat_mul]
    congr 1
    norm_num
  rw [heq]
  calc
    _ < (22255408 / 10000000 : ℝ) ^ (10 : ℕ) := by norm_num
    _ < _ := by gcongr

private lemma sin_pos_interval {t l u : ℝ}
    (hl : 0 ≤ l) (hlt : l < t) (htu : t < u) (hu : u ≤ 1) :
    l - u ^ 3 / 6 - u ^ 4 * (5 / 96 : ℝ) < Real.sin t ∧
      Real.sin t < u - l ^ 3 / 6 + u ^ 4 * (5 / 96 : ℝ) := by
  have ht0 : 0 ≤ t := le_trans hl (le_of_lt hlt)
  have ht1 : t ≤ 1 := (le_of_lt htu).trans hu
  have hs := Real.sin_bound (x := t) (by simpa [abs_of_nonneg ht0] using ht1)
  rw [abs_of_nonneg ht0, abs_le] at hs
  have h3lo : l ^ 3 < t ^ 3 := by gcongr
  have h3hi : t ^ 3 < u ^ 3 := by gcongr
  have h4 : t ^ 4 < u ^ 4 := by gcongr
  constructor <;> nlinarith [hs.1, hs.2]

private lemma cos_after_three_interval {x l u cl cu : ℝ}
    (hlt : l < x - 3 * Real.pi / 2)
    (htu : x - 3 * Real.pi / 2 < u)
    (hl : 0 ≤ l) (hu : u ≤ 1)
    (hcl : cl < l - u ^ 3 / 6 - u ^ 4 * (5 / 96 : ℝ))
    (hcu : u - l ^ 3 / 6 + u ^ 4 * (5 / 96 : ℝ) < cu) :
    cl < Real.cos x ∧ Real.cos x < cu := by
  let t : ℝ := x - 3 * Real.pi / 2
  have hs := sin_pos_interval (t := t) (l := l) (u := u)
    hl (by simpa [t] using hlt) (by simpa [t] using htu) hu
  have hcos : Real.cos x = Real.sin t := by
    dsimp [t]
    rw [show x = 3 * Real.pi / 2 + (x - 3 * Real.pi / 2) by ring,
      Real.cos_add]
    rw [show 3 * Real.pi / 2 = Real.pi + Real.pi / 2 by ring,
      Real.cos_add, Real.sin_add]
    simp
  rw [hcos]
  constructor <;> linarith [hs.1, hs.2]

private lemma cos_after_seven_interval {x l u cl cu : ℝ}
    (hlt : l < x - 7 * Real.pi / 2)
    (htu : x - 7 * Real.pi / 2 < u)
    (hl : 0 ≤ l) (hu : u ≤ 1)
    (hcl : cl < l - u ^ 3 / 6 - u ^ 4 * (5 / 96 : ℝ))
    (hcu : u - l ^ 3 / 6 + u ^ 4 * (5 / 96 : ℝ) < cu) :
    cl < Real.cos x ∧ Real.cos x < cu := by
  let t : ℝ := x - 7 * Real.pi / 2
  have hs := sin_pos_interval (t := t) (l := l) (u := u)
    hl (by simpa [t] using hlt) (by simpa [t] using htu) hu
  have hcos : Real.cos x = Real.sin t := by
    dsimp [t]
    rw [show x = 7 * Real.pi / 2 + (x - 7 * Real.pi / 2) by ring,
      Real.cos_add]
    rw [show 7 * Real.pi / 2 = 3 * Real.pi + Real.pi / 2 by ring,
      Real.cos_add, Real.sin_add]
    rw [show 3 * Real.pi = Real.pi + 2 * Real.pi by ring,
      Real.cos_add_two_pi, Real.sin_add_two_pi]
    simp
  rw [hcos]
  constructor <;> linarith [hs.1, hs.2]

private lemma cos47_bounds :
    (-12390 / 1000000 : ℝ) < Real.cos 4.7 ∧
      Real.cos 4.7 < (-12388 / 1000000 : ℝ) := by
  let t : ℝ := 3 * Real.pi / 2 - 4.7
  have hlt : (123889 / 10000000 : ℝ) < t := by
    dsimp [t]
    nlinarith [Real.pi_gt_d20]
  have htu : t < (123891 / 10000000 : ℝ) := by
    dsimp [t]
    nlinarith [Real.pi_lt_d20]
  have hs := sin_pos_interval (l := (123889 / 10000000 : ℝ))
    (u := (123891 / 10000000 : ℝ)) (by norm_num) hlt htu (by norm_num)
  have hs' :
      (12388 / 1000000 : ℝ) < Real.sin t ∧
        Real.sin t < (12390 / 1000000 : ℝ) := by
    norm_num at hs ⊢
    constructor <;> linarith [hs.1, hs.2]
  have hcos : Real.cos 4.7 = -Real.sin t := by
    dsimp [t]
    rw [show (4.7 : ℝ) = 3 * Real.pi / 2 -
        (3 * Real.pi / 2 - 4.7) by ring, Real.cos_sub]
    rw [show 3 * Real.pi / 2 = Real.pi + Real.pi / 2 by ring,
      Real.cos_add, Real.sin_add]
    simp
  rw [hcos]
  constructor <;> linarith [hs'.1, hs'.2]

private lemma cos48_bounds :
    (87495 / 1000000 : ℝ) < Real.cos 4.8 ∧
      Real.cos 4.8 < (87503 / 1000000 : ℝ) := by
  apply cos_after_three_interval
      (l := (876109 / 10000000 : ℝ))
      (u := (876112 / 10000000 : ℝ))
  · norm_num at ⊢
    nlinarith [Real.pi_lt_d20]
  · norm_num at ⊢
    nlinarith [Real.pi_gt_d20]
  · norm_num
  · norm_num
  · norm_num
  · norm_num

private lemma cos4728_bounds :
    (15610 / 1000000 : ℝ) < Real.cos 4.728 ∧
      Real.cos 4.728 < (15611 / 1000000 : ℝ) := by
  apply cos_after_three_interval
      (l := (156109 / 10000000 : ℝ))
      (u := (156112 / 10000000 : ℝ))
  · norm_num at ⊢
    nlinarith [Real.pi_lt_d20]
  · norm_num at ⊢
    nlinarith [Real.pi_gt_d20]
  · norm_num
  · norm_num
  · norm_num
  · norm_num

private lemma cos47345_bounds :
    (22109 / 1000000 : ℝ) < Real.cos 4.7345 ∧
      Real.cos 4.7345 < (22110 / 1000000 : ℝ) := by
  apply cos_after_three_interval
      (l := (221109 / 10000000 : ℝ))
      (u := (221112 / 10000000 : ℝ))
  · norm_num at ⊢
    nlinarith [Real.pi_lt_d20]
  · norm_num at ⊢
    nlinarith [Real.pi_gt_d20]
  · norm_num
  · norm_num
  · norm_num
  · norm_num

private lemma cos473_bounds :
    (17609 / 1000000 : ℝ) < Real.cos 4.730 ∧
      Real.cos 4.730 < (17611 / 1000000 : ℝ) := by
  apply cos_after_three_interval
      (l := (176109 / 10000000 : ℝ))
      (u := (176112 / 10000000 : ℝ))
  · norm_num at ⊢
    nlinarith [Real.pi_lt_d20]
  · norm_num at ⊢
    nlinarith [Real.pi_gt_d20]
  · norm_num
  · norm_num
  · norm_num
  · norm_num

private lemma cos47301_bounds :
    (17709 / 1000000 : ℝ) < Real.cos 4.7301 ∧
      Real.cos 4.7301 < (17711 / 1000000 : ℝ) := by
  apply cos_after_three_interval
      (l := (177109 / 10000000 : ℝ))
      (u := (177112 / 10000000 : ℝ))
  · norm_num at ⊢
    nlinarith [Real.pi_lt_d20]
  · norm_num at ⊢
    nlinarith [Real.pi_gt_d20]
  · norm_num
  · norm_num
  · norm_num
  · norm_num

private lemma cos11_bounds :
    (4425 / 1000000 : ℝ) < Real.cos 11 ∧
      Real.cos 11 < (4426 / 1000000 : ℝ) := by
  apply cos_after_seven_interval
      (l := (44256 / 10000000 : ℝ))
      (u := (44258 / 10000000 : ℝ))
  · norm_num at ⊢
    nlinarith [Real.pi_lt_d20]
  · norm_num at ⊢
    nlinarith [Real.pi_gt_d20]
  · norm_num
  · norm_num
  · norm_num
  · norm_num

private lemma cos10997_bounds :
    (14255 / 10000000 : ℝ) < Real.cos 10.997 ∧
      Real.cos 10.997 < (1426 / 1000000 : ℝ) := by
  apply cos_after_seven_interval
      (l := (14256 / 10000000 : ℝ))
      (u := (14258 / 10000000 : ℝ))
  · norm_num at ⊢
    nlinarith [Real.pi_lt_d20]
  · norm_num at ⊢
    nlinarith [Real.pi_gt_d20]
  · norm_num
  · norm_num
  · norm_num
  · norm_num

private lemma cosh_bounds_of_exp {x eLo eHi cLo cHi : ℝ}
    (h100 : 100 < eLo)
    (heLo : eLo < Real.exp x) (heHi : Real.exp x < eHi)
    (hcLo : cLo < eLo / 2)
    (hcHi : (eHi + 1 / 100) / 2 < cHi) :
    cLo < Real.cosh x ∧ Real.cosh x < cHi := by
  have hnegPos := Real.exp_pos (-x)
  have hnegHi : Real.exp (-x) < (1 / 100 : ℝ) := by
    rw [Real.exp_neg, inv_lt_comm₀ (Real.exp_pos x) (by norm_num)]
    linarith
  rw [Real.cosh_eq]
  constructor <;> nlinarith

private lemma mul_bounds_pos {a b al au bl bu : ℝ}
    (hal : 0 < al) (hbl : 0 < bl)
    (hal' : al < a) (hau : a < au)
    (hbl' : bl < b) (hbu : b < bu) :
    al * bl < a * b ∧ a * b < au * bu := by
  constructor
  · exact (mul_lt_mul_of_pos_left hbl' hal).trans
      (mul_lt_mul_of_pos_right hal' (lt_trans hbl hbl'))
  · exact (mul_lt_mul_of_pos_right hau (lt_trans hbl hbl')).trans
      (mul_lt_mul_of_pos_left hbu ((hal.trans hal').trans hau))

private lemma f47_bounds :
    (-16813 / 10000 : ℝ) < f 4.7 ∧ f 4.7 < (-16810 / 10000 : ℝ) := by
  rcases exp47_bounds with ⟨heLo, heHi⟩
  rcases cos47_bounds with ⟨hcLo, hcHi⟩
  have hnegHi : Real.exp (-4.7 : ℝ) < (1 / 100 : ℝ) := by
    rw [Real.exp_neg, inv_lt_comm₀ (by positivity) (by norm_num)]
    norm_num at heLo ⊢
    linarith
  have hcoshLo : (549735 / 10000 : ℝ) < Real.cosh 4.7 := by
    rw [Real.cosh_eq]
    nlinarith [Real.exp_pos (-4.7)]
  have hcoshHi : Real.cosh 4.7 < (549787 / 10000 : ℝ) := by
    rw [Real.cosh_eq]
    nlinarith
  have hcNeg : Real.cos 4.7 < 0 := by linarith
  have hpLo :
      (-12390 / 1000000 : ℝ) * (549787 / 10000 : ℝ) <
        Real.cos 4.7 * Real.cosh 4.7 := by
    calc
      _ < (-12390 / 1000000 : ℝ) * Real.cosh 4.7 :=
        mul_lt_mul_of_neg_left hcoshHi (by norm_num)
      _ < _ := mul_lt_mul_of_pos_right hcLo (Real.cosh_pos 4.7)
  have hpHi :
      Real.cos 4.7 * Real.cosh 4.7 <
        (-12388 / 1000000 : ℝ) * (549735 / 10000 : ℝ) := by
    calc
      _ < Real.cos 4.7 * (549735 / 10000 : ℝ) :=
        mul_lt_mul_of_neg_left hcoshLo hcNeg
      _ < _ := mul_lt_mul_of_pos_right hcHi (by norm_num)
  unfold f
  norm_num at hpLo hpHi ⊢
  constructor <;> linarith

private lemma f48_bounds :
    (43157 / 10000 : ℝ) < f 4.8 ∧ f 4.8 < (43168 / 10000 : ℝ) := by
  rcases exp48_bounds with ⟨heLo, heHi⟩
  rcases cos48_bounds with ⟨hcLo, hcHi⟩
  have hh := cosh_bounds_of_exp
    (eLo := (1215103 / 10000 : ℝ))
    (eHi := (1215106 / 10000 : ℝ))
    (cLo := (607551 / 10000 : ℝ))
    (cHi := (607604 / 10000 : ℝ))
    (by norm_num) heLo heHi (by norm_num) (by norm_num)
  have hp := mul_bounds_pos (a := Real.cos 4.8) (b := Real.cosh 4.8)
    (al := (87495 / 1000000 : ℝ)) (au := (87503 / 1000000 : ℝ))
    (bl := (607551 / 10000 : ℝ)) (bu := (607604 / 10000 : ℝ))
    (by norm_num) (by norm_num) hcLo hcHi hh.1 hh.2
  unfold f
  norm_num at hp ⊢
  constructor <;> linarith [hp.1, hp.2]

private lemma f4728_bounds :
    (-1175 / 10000 : ℝ) < f 4.728 ∧ f 4.728 < (-1173 / 10000 : ℝ) := by
  rcases exp4728_bounds with ⟨heLo, heHi⟩
  rcases cos4728_bounds with ⟨hcLo, hcHi⟩
  have hh := cosh_bounds_of_exp
    (eLo := (1130691 / 10000 : ℝ))
    (eHi := (1130693 / 10000 : ℝ))
    (cLo := (565345 / 10000 : ℝ))
    (cHi := (565397 / 10000 : ℝ))
    (by norm_num) heLo heHi (by norm_num) (by norm_num)
  have hp := mul_bounds_pos (a := Real.cos 4.728) (b := Real.cosh 4.728)
    (al := (15610 / 1000000 : ℝ)) (au := (15611 / 1000000 : ℝ))
    (bl := (565345 / 10000 : ℝ)) (bu := (565397 / 10000 : ℝ))
    (by norm_num) (by norm_num) hcLo hcHi hh.1 hh.2
  unfold f
  norm_num at hp ⊢
  constructor <;> linarith [hp.1, hp.2]

private lemma f47345_bounds :
    (2580 / 10000 : ℝ) < f 4.7345 ∧ f 4.7345 < (2583 / 10000 : ℝ) := by
  rcases exp47345_bounds with ⟨heLo, heHi⟩
  rcases cos47345_bounds with ⟨hcLo, hcHi⟩
  have hh := cosh_bounds_of_exp
    (eLo := (1138064 / 10000 : ℝ))
    (eHi := (1138067 / 10000 : ℝ))
    (cLo := (569031 / 10000 : ℝ))
    (cHi := (569084 / 10000 : ℝ))
    (by norm_num) heLo heHi (by norm_num) (by norm_num)
  have hp := mul_bounds_pos (a := Real.cos 4.7345) (b := Real.cosh 4.7345)
    (al := (22109 / 1000000 : ℝ)) (au := (22110 / 1000000 : ℝ))
    (bl := (569031 / 10000 : ℝ)) (bu := (569084 / 10000 : ℝ))
    (by norm_num) (by norm_num) hcLo hcHi hh.1 hh.2
  unfold f
  norm_num at hp ⊢
  constructor <;> linarith [hp.1, hp.2]

private lemma f473_bounds :
    (-26 / 10000 : ℝ) < f 4.730 ∧ f 4.730 < (-22 / 10000 : ℝ) := by
  rcases exp473_bounds with ⟨heLo, heHi⟩
  rcases cos473_bounds with ⟨hcLo, hcHi⟩
  have hh := cosh_bounds_of_exp
    (eLo := (1132954 / 10000 : ℝ))
    (eHi := (1132957 / 10000 : ℝ))
    (cLo := (566476 / 10000 : ℝ))
    (cHi := (566529 / 10000 : ℝ))
    (by norm_num) heLo heHi (by norm_num) (by norm_num)
  have hp := mul_bounds_pos (a := Real.cos 4.730) (b := Real.cosh 4.730)
    (al := (17609 / 1000000 : ℝ)) (au := (17611 / 1000000 : ℝ))
    (bl := (566476 / 10000 : ℝ)) (bu := (566529 / 10000 : ℝ))
    (by norm_num) (by norm_num) hcLo hcHi hh.1 hh.2
  unfold f
  norm_num at hp ⊢
  constructor <;> linarith [hp.1, hp.2]

private lemma f47301_bounds :
    (32 / 10000 : ℝ) < f 4.7301 ∧ f 4.7301 < (35 / 10000 : ℝ) := by
  rcases exp47301_bounds with ⟨heLo, heHi⟩
  rcases cos47301_bounds with ⟨hcLo, hcHi⟩
  have hh := cosh_bounds_of_exp
    (eLo := (1133067 / 10000 : ℝ))
    (eHi := (1133071 / 10000 : ℝ))
    (cLo := (566533 / 10000 : ℝ))
    (cHi := (566586 / 10000 : ℝ))
    (by norm_num) heLo heHi (by norm_num) (by norm_num)
  have hp := mul_bounds_pos (a := Real.cos 4.7301) (b := Real.cosh 4.7301)
    (al := (17709 / 1000000 : ℝ)) (au := (17711 / 1000000 : ℝ))
    (bl := (566533 / 10000 : ℝ)) (bu := (566586 / 10000 : ℝ))
    (by norm_num) (by norm_num) hcLo hcHi hh.1 hh.2
  unfold f
  norm_num at hp ⊢
  constructor <;> linarith [hp.1, hp.2]

private lemma f11_bounds :
    (13147 / 100 : ℝ) < f 11 ∧ f 11 < (13151 / 100 : ℝ) := by
  rcases exp11_bounds with ⟨heLo, heHi⟩
  rcases cos11_bounds with ⟨hcLo, hcHi⟩
  have hnegHi : Real.exp (-11 : ℝ) < (1 / 100 : ℝ) := by
    rw [Real.exp_neg, inv_lt_comm₀ (by positivity) (by norm_num)]
    linarith
  have hhLo : (29937 : ℝ) < Real.cosh 11 := by
    rw [Real.cosh_eq]
    nlinarith [Real.exp_pos (-11)]
  have hhHi : Real.cosh 11 < (2993751 / 100 : ℝ) := by
    rw [Real.cosh_eq]
    nlinarith
  have hp := mul_bounds_pos (a := Real.cos 11) (b := Real.cosh 11)
    (al := (4425 / 1000000 : ℝ)) (au := (4426 / 1000000 : ℝ))
    (bl := (29937 : ℝ)) (bu := (2993751 / 100 : ℝ))
    (by norm_num) (by norm_num) hcLo hcHi hhLo hhHi
  unfold f
  norm_num at hp ⊢
  constructor <;> linarith [hp.1, hp.2]

private lemma f10997_pos : 0 < f 10.997 := by
  have he : Real.exp 8 < Real.exp 10.997 :=
    Real.exp_lt_exp.mpr (by norm_num)
  have hh : (1450 : ℝ) < Real.cosh 10.997 := by
    rw [Real.cosh_eq]
    nlinarith [exp8_gt, Real.exp_pos (-10.997)]
  have hc := cos10997_bounds.1
  have hp :
      (14255 / 10000000 : ℝ) * (1450 : ℝ) <
        Real.cos 10.997 * Real.cosh 10.997 := by
    calc
      _ < (14255 / 10000000 : ℝ) * Real.cosh 10.997 :=
        mul_lt_mul_of_pos_left hh (by norm_num)
      _ < _ := mul_lt_mul_of_pos_right hc (Real.cosh_pos 10.997)
  unfold f
  norm_num at hp ⊢
  linarith

private lemma firstRoot_gt_of_neg (c α : ℝ)
    (hc : c ∈ Set.Ioo (3 * Real.pi / 2) (2 * Real.pi))
    (hfc : f c < 0) (hα : FirstRoot α) : c < α := by
  by_contra hn
  have hle : α ≤ c := le_of_not_gt hn
  rcases hle.eq_or_lt with heq | hlt
  · subst α
    linarith [hα.2]
  · have hstrict := strictMono_f_first hα.1 hc hlt
    linarith [hα.2]

private lemma firstRoot_lt_of_pos (c α : ℝ)
    (hc : c ∈ Set.Ioo (3 * Real.pi / 2) (2 * Real.pi))
    (hfc : 0 < f c) (hα : FirstRoot α) : α < c := by
  by_contra hn
  have hle : c ≤ α := le_of_not_gt hn
  rcases hle.eq_or_lt with heq | hlt
  · subst α
    linarith [hα.2]
  · have hstrict := strictMono_f_first hc hα.1 hlt
    linarith [hα.2]

private lemma thirdRoot_lt_of_pos (c γ : ℝ)
    (hc : c ∈ Set.Ioo (7 * Real.pi / 2) (4 * Real.pi))
    (hfc : 0 < f c) (hγ : ThirdRoot γ) : γ < c := by
  by_contra hn
  have hle : c ≤ γ := le_of_not_gt hn
  rcases hle.eq_or_lt with heq | hlt
  · subst γ
    linarith [hγ.2]
  · have hstrict := strictMono_f_third hc hγ.1 hlt
    linarith [hγ.2]

theorem gap1 (α : ℝ) (hα : FirstRoot α) :
    3 * Real.pi / 2 < α := by exact hα.1.1
theorem gap2 (α : ℝ) (hα : FirstRoot α) :
    α < 2 * Real.pi := by exact hα.1.2
theorem gap3 : ∃ β : ℝ, SecondRoot β ∧ 2 * Real.pi < β := by
  rcases exists_second_root with ⟨β, hβ⟩
  exact ⟨β, hβ, hβ.1.1⟩
theorem gap4 : ∃ β : ℝ, SecondRoot β ∧ β < 5 * Real.pi / 2 := by
  rcases exists_second_root with ⟨β, hβ⟩
  exact ⟨β, hβ, hβ.1.2⟩
theorem gap5 (γ : ℝ) (hγ : ThirdRoot γ) :
    7 * Real.pi / 2 < γ := by exact hγ.1.1
theorem gap6 (γ : ℝ) (hγ : ThirdRoot γ) :
    γ < 4 * Real.pi := by exact hγ.1.2
theorem gap7 : Approx (f 4.7) (-1.6812) (1 / 1000) := by
  unfold Approx
  rw [abs_lt]
  rcases f47_bounds with ⟨hlo, hhi⟩
  norm_num at hlo hhi ⊢
  constructor <;> linarith
theorem gap8 : Approx (f 4.8) 4.3159 (1 / 1000) := by
  unfold Approx
  rw [abs_lt]
  rcases f48_bounds with ⟨hlo, hhi⟩
  norm_num at hlo hhi ⊢
  constructor <;> linarith
theorem gap9 (α : ℝ) (hα : FirstRoot α) : 4.7 < α := by
  have hlo := hα.1.1
  nlinarith [Real.pi_gt_d20]
theorem gap10 (α : ℝ) (hα : FirstRoot α) : α < 4.8 := by
  have happ := gap8
  rw [Approx, abs_lt] at happ
  have hfpos : 0 < f 4.8 := by norm_num at happ ⊢; linarith
  have hmem : (4.8 : ℝ) ∈ Set.Ioo (3 * Real.pi / 2) (2 * Real.pi) := by
    constructor
    · nlinarith [Real.pi_lt_d20]
    · nlinarith [Real.pi_gt_d20]
  by_contra hn
  have hle : (4.8 : ℝ) ≤ α := le_of_not_gt hn
  rcases hle.eq_or_lt with heq | hlt
  · subst α
    linarith [hα.2]
  · have hstrict := strictMono_f_first hmem hα.1 hlt
    linarith [hα.2]
theorem gap11 : (4.7 : ℝ) < 4.8 := by norm_num
theorem gap12 (x : ℝ) (hx : x ∈ Set.Ioo (3 * Real.pi / 2) (2 * Real.pi)) :
    deriv (deriv f) x > 0 := by
  rw [deriv2_f]
  have hu0 : 0 < 2 * Real.pi - x := sub_pos.mpr hx.2
  have hupi : 2 * Real.pi - x < Real.pi := by
    nlinarith [hx.1, Real.pi_pos]
  have hsinpos := Real.sin_pos_of_pos_of_lt_pi hu0 hupi
  have hsineg : Real.sin x < 0 := by
    rw [Real.sin_two_pi_sub] at hsinpos
    linarith
  have hx0 : 0 < x := by nlinarith [hx.1, Real.pi_pos]
  have hsinh : 0 < Real.sinh x := (Real.sinh_pos_iff).2 hx0
  exact mul_pos (mul_pos_of_neg_of_neg (by norm_num) hsineg) hsinh
theorem gap13 : tangentApproximant 1 = 4.7345 := by rfl
theorem gap14 : tangentApproximant 2 = 4.7301 := by rfl
theorem gap15 : chordStep 4.7 4.8 =
    4.7 - f 4.7 / (f 4.8 - f 4.7) * (4.8 - 4.7) := by rfl
theorem gap16 : Approx (chordStep 4.7 4.8) 4.7280 (1 / 10000) := by
  rcases f47_bounds with ⟨haLo, haHi⟩
  rcases f48_bounds with ⟨hbLo, hbHi⟩
  have hden : 0 < f 4.8 - f 4.7 := by linarith
  have hrLo :
      (279 / 1000 : ℝ) < (-f 4.7) / (f 4.8 - f 4.7) := by
    rw [lt_div_iff₀ hden]
    norm_num at haLo haHi hbLo hbHi ⊢
    linarith
  have hrHi :
      (-f 4.7) / (f 4.8 - f 4.7) < (281 / 1000 : ℝ) := by
    rw [div_lt_iff₀ hden]
    norm_num at haLo haHi hbLo hbHi ⊢
    linarith
  unfold Approx chordStep
  rw [abs_lt]
  norm_num at ⊢
  rw [show f (47 / 10) / (f (24 / 5) - f (47 / 10)) =
      -((-f (47 / 10)) / (f (24 / 5) - f (47 / 10))) by ring]
  constructor <;> nlinarith
theorem gap17 : chordApproximant 1 = 4.7280 := by rfl
theorem gap18 (α : ℝ) (hα : FirstRoot α) : 4.7280 < α := by
  have hmem : (4.728 : ℝ) ∈
      Set.Ioo (3 * Real.pi / 2) (2 * Real.pi) := by
    constructor
    · nlinarith [Real.pi_lt_d20]
    · nlinarith [Real.pi_gt_d20]
  have hneg : f 4.728 < 0 := by linarith [f4728_bounds.2]
  have h := firstRoot_gt_of_neg 4.728 α hmem hneg hα
  norm_num at h ⊢
  exact h
theorem gap19 (α : ℝ) (hα : FirstRoot α) : α < 4.7345 := by
  apply firstRoot_lt_of_pos 4.7345 α
  · constructor
    · nlinarith [Real.pi_lt_d20]
    · nlinarith [Real.pi_gt_d20]
  · linarith [f47345_bounds.1]
  · exact hα
theorem gap20 : (4.7280 : ℝ) < 4.7345 := by norm_num
theorem gap21 : chordStep 4.7280 4.7345 =
    4.7280 - f 4.7280 / (f 4.7345 - f 4.7280) * (4.7345 - 4.7280) := by rfl
theorem gap22 :
    Approx (chordStep 4.7280 4.7345) 4.7300 (1 / 10000) := by
  rcases f4728_bounds with ⟨haLo, haHi⟩
  rcases f47345_bounds with ⟨hbLo, hbHi⟩
  have hden : 0 < f 4.7345 - f 4.728 := by linarith
  have hrLo :
      (3 / 10 : ℝ) < (-f 4.728) / (f 4.7345 - f 4.728) := by
    rw [lt_div_iff₀ hden]
    norm_num at haLo haHi hbLo hbHi ⊢
    linarith
  have hrHi :
      (-f 4.728) / (f 4.7345 - f 4.728) < (8 / 25 : ℝ) := by
    rw [div_lt_iff₀ hden]
    norm_num at haLo haHi hbLo hbHi ⊢
    linarith
  unfold Approx chordStep
  rw [abs_lt]
  norm_num at ⊢
  rw [show f (591 / 125) / (f (9469 / 2000) - f (591 / 125)) =
      -((-f (591 / 125)) / (f (9469 / 2000) - f (591 / 125))) by ring]
  constructor <;> nlinarith
theorem gap23 : chordApproximant 2 = 4.7300 := by rfl
theorem gap24 (α : ℝ) (hα : FirstRoot α) : 4.7300 < α := by
  have hmem : (4.730 : ℝ) ∈
      Set.Ioo (3 * Real.pi / 2) (2 * Real.pi) := by
    constructor
    · nlinarith [Real.pi_lt_d20]
    · nlinarith [Real.pi_gt_d20]
  have hneg : f 4.730 < 0 := by linarith [f473_bounds.2]
  have h := firstRoot_gt_of_neg 4.730 α hmem hneg hα
  norm_num at h ⊢
  exact h
theorem gap25 (α : ℝ) (hα : FirstRoot α) : α < 4.7301 := by
  apply firstRoot_lt_of_pos 4.7301 α
  · constructor
    · nlinarith [Real.pi_lt_d20]
    · nlinarith [Real.pi_gt_d20]
  · linarith [f47301_bounds.1]
  · exact hα
theorem gap26 : (4.7300 : ℝ) < 4.7301 := by norm_num
theorem gap27 (α : ℝ) (hα : FirstRoot α) :
    |4.730 - α| < 0.001 := by
  have hlo := gap24 α hα
  have hhi := gap25 α hα
  rw [abs_of_nonpos (by norm_num at hlo ⊢; linarith)]
  norm_num at hhi ⊢
  linarith
theorem gap28 : f (7 * Real.pi / 2) = -1 := by
  unfold f
  have hs : Real.sin (3 * Real.pi) = 0 := by
    rw [show 3 * Real.pi = Real.pi + 2 * Real.pi by ring,
      Real.sin_add_two_pi, Real.sin_pi]
  rw [show 7 * Real.pi / 2 = 3 * Real.pi + Real.pi / 2 by ring,
    Real.cos_add]
  simp [hs]
theorem gap29 : Approx (f 11) 131.5 (1 / 10) := by
  unfold Approx
  rw [abs_lt]
  rcases f11_bounds with ⟨hlo, hhi⟩
  norm_num at hlo hhi ⊢
  constructor <;> linarith
theorem gap30 (γ : ℝ) (hγ : ThirdRoot γ) :
    7 * Real.pi / 2 < γ := by exact hγ.1.1
theorem gap31 (γ : ℝ) (hγ : ThirdRoot γ) : γ < 11 := by
  have happ := gap29
  rw [Approx, abs_lt] at happ
  have hfpos : 0 < f 11 := by norm_num at happ ⊢; linarith
  have hmem : (11 : ℝ) ∈ Set.Ioo (7 * Real.pi / 2) (4 * Real.pi) := by
    constructor
    · nlinarith [Real.pi_lt_d20]
    · nlinarith [Real.pi_gt_d20]
  by_contra hn
  have hle : (11 : ℝ) ≤ γ := le_of_not_gt hn
  rcases hle.eq_or_lt with heq | hlt
  · subst γ
    linarith [hγ.2]
  · have hstrict := strictMono_f_third hmem hγ.1 hlt
    linarith [hγ.2]
theorem gap32 : 7 * Real.pi / 2 < 11 := by
  nlinarith [Real.pi_lt_d20]
theorem gap33 : thirdApproximant 1 = 10.9956 := by rfl
theorem gap34 : thirdApproximant 1 = 10.9956 := by rfl
theorem gap35 (γ : ℝ) (hγ : ThirdRoot γ) :
    |10.996 - γ| < 0.001 := by
  have hlo : (10.995 : ℝ) < γ := by
    calc
      (10.995 : ℝ) < 7 * Real.pi / 2 := by
        nlinarith [Real.pi_gt_d20]
      _ < γ := hγ.1.1
  have hmem : (10.997 : ℝ) ∈
      Set.Ioo (7 * Real.pi / 2) (4 * Real.pi) := by
    constructor
    · nlinarith [Real.pi_lt_d20]
    · nlinarith [Real.pi_gt_d20]
  have hhi : γ < (10.997 : ℝ) :=
    thirdRoot_lt_of_pos 10.997 γ hmem f10997_pos hγ
  rw [abs_lt]
  norm_num at hlo hhi ⊢
  constructor <;> linarith
theorem gap36 : ApproxRootPair (4.730, 10.996) 0.001 := by
  have hf48 : 0 < f 4.8 := by
    have h := gap8
    rw [Approx, abs_lt] at h
    norm_num at h ⊢
    linarith
  have hfleft : f (3 * Real.pi / 2) < 0 := by
    unfold f
    rw [show 3 * Real.pi / 2 = Real.pi + Real.pi / 2 by ring,
      Real.cos_add]
    simp
  have horder1 : 3 * Real.pi / 2 < (4.8 : ℝ) := by
    nlinarith [Real.pi_lt_d20]
  have hiv1 := intermediate_value_Icc horder1.le continuous_f.continuousOn
  rcases hiv1 ⟨hfleft.le, hf48.le⟩ with ⟨α, hαclosed, hfα⟩
  have hαopen : α ∈ Set.Ioo (3 * Real.pi / 2) (4.8 : ℝ) := by
    constructor
    · exact lt_of_le_of_ne hαclosed.1 (by
        intro heq
        subst α
        linarith)
    · exact lt_of_le_of_ne hαclosed.2 (by
        intro heq
        subst α
        linarith)
  have hαroot : FirstRoot α := by
    refine ⟨⟨hαopen.1, ?_⟩, hfα⟩
    nlinarith [hαopen.2, Real.pi_gt_d20]
  have hf11 : 0 < f 11 := by
    have h := gap29
    rw [Approx, abs_lt] at h
    norm_num at h ⊢
    linarith
  have horder3 : 7 * Real.pi / 2 < (11 : ℝ) := by
    nlinarith [Real.pi_lt_d20]
  have hiv3 := intermediate_value_Icc horder3.le continuous_f.continuousOn
  rcases hiv3 ⟨(by rw [gap28]; norm_num : f (7 * Real.pi / 2) ≤ 0),
      hf11.le⟩ with ⟨γ, hγclosed, hfγ⟩
  have hγopen : γ ∈ Set.Ioo (7 * Real.pi / 2) (11 : ℝ) := by
    constructor
    · exact lt_of_le_of_ne hγclosed.1 (by
        intro heq
        subst γ
        rw [gap28] at hfγ
        norm_num at hfγ)
    · exact lt_of_le_of_ne hγclosed.2 (by
        intro heq
        subst γ
        linarith)
  have hγroot : ThirdRoot γ := by
    refine ⟨⟨hγopen.1, ?_⟩, hfγ⟩
    nlinarith [hγopen.2, Real.pi_gt_d20]
  exact ⟨α, γ, hαroot, hγroot, gap27 α hαroot, gap35 γ hγroot⟩

end
end ProofGap.Exercise1623
