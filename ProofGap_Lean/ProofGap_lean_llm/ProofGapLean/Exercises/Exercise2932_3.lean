import ProofGapLean.Prelude.Analysis
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul

namespace ProofGap.Exercise2932_3

noncomputable section

open scoped BigOperators Interval

def sinc (x : ℝ) : ℝ :=
  Real.sin x / x

def sincTerm (n : ℕ) (x : ℝ) : ℝ :=
  (-1 : ℝ) ^ n * x ^ (2 * n) /
    (Nat.factorial (2 * n + 1) : ℝ)

def integratedTerm (n : ℕ) : ℝ :=
  (-1 : ℝ) ^ n * 2 ^ (2 * n + 1) /
    (((2 * n + 1 : ℕ) : ℝ) *
      (Nat.factorial (2 * n + 1) : ℝ))

def sincIntegral : ℝ :=
  ∫ x in (0 : ℝ)..2, sinc x

def partialIntegral : ℝ :=
  ∑ n ∈ Finset.range 4, integratedTerm n

def remainder : ℝ :=
  sincIntegral - partialIntegral

def Approx (u v ε : ℝ) : Prop :=
  |u - v| < ε

private def sincCoeff (n : ℕ) : ℝ :=
  2 ^ (2 * n + 1) /
    (((2 * n + 1 : ℕ) : ℝ) * (Nat.factorial (2 * n + 1) : ℝ))

private theorem two_mul_add_injective (c : ℕ) :
    Function.Injective (fun n : ℕ => 2 * n + c) := by
  intro a b hab
  have hmul : 2 * a = 2 * b := Nat.add_right_cancel hab
  exact mul_left_cancel₀ (by norm_num : (2 : ℕ) ≠ 0) hmul

private theorem sinc_eq_tsum_sincTerm (x : ℝ) (hx : x ≠ 0) :
    sinc x = ∑' n : ℕ, sincTerm n x := by
  have h := (Real.hasSum_sin x).div_const x
  have heq :
      (fun n : ℕ =>
          ((-1 : ℝ) ^ n * x ^ (2 * n + 1) /
            (Nat.factorial (2 * n + 1) : ℝ)) / x) =
        fun n : ℕ => sincTerm n x := by
    funext n
    dsimp [sincTerm]
    field_simp
    ring
  have hs : HasSum (fun n : ℕ => sincTerm n x) (sinc x) := by
    rw [← heq]
    simpa [sinc] using h
  exact hs.tsum_eq.symm

private theorem sincCoeff_pos (n : ℕ) : 0 < sincCoeff n := by
  unfold sincCoeff
  positivity

private theorem sincCoeff_succ_lt (n : ℕ) :
    sincCoeff (n + 1) < sincCoeff n := by
  unfold sincCoeff
  rw [show 2 * (n + 1) + 1 = (2 * n + 1) + 2 by omega]
  rw [Nat.factorial_succ, Nat.factorial_succ]
  norm_num [pow_add]
  field_simp
  nlinarith [show (0 : ℝ) < (Nat.factorial (2 * n + 1) : ℝ) by positivity,
    sq_nonneg (n : ℝ)]

private theorem summable_sincCoeff : Summable sincCoeff := by
  have hinj : Function.Injective (fun n : ℕ => 2 * n + 1) :=
    two_mul_add_injective 1
  have hodd : Summable (fun n : ℕ =>
      (2 : ℝ) ^ (2 * n + 1) / (Nat.factorial (2 * n + 1) : ℝ)) := by
    simpa [Function.comp_def] using
      (Real.summable_pow_div_factorial 2).comp_injective hinj
  apply Summable.of_norm_bounded hodd
  intro n
  rw [Real.norm_eq_abs, abs_of_pos (sincCoeff_pos n)]
  unfold sincCoeff
  have hfac : (0 : ℝ) < (Nat.factorial (2 * n + 1) : ℝ) := by
    positivity
  have hoddcast : (1 : ℝ) ≤ ((2 * n + 1 : ℕ) : ℝ) := by
    norm_num
  apply div_le_div_of_nonneg_left (by positivity) hfac
  nlinarith

private theorem summable_integratedTerm : Summable integratedTerm := by
  apply Summable.of_norm_bounded summable_sincCoeff
  intro n
  rw [Real.norm_eq_abs]
  unfold integratedTerm sincCoeff
  rw [abs_div, abs_mul, abs_pow]
  norm_num
  rw [abs_of_pos (show (0 : ℝ) < 2 * (n : ℝ) + 1 by positivity)]

private theorem continuous_sincTerm (n : ℕ) : Continuous (sincTerm n) := by
  unfold sincTerm
  exact ((continuous_const.mul (continuous_id.pow (2 * n))).div_const
    (Nat.factorial (2 * n + 1) : ℝ))

private theorem hasDerivAt_pow_succ_aux (k : ℕ) (x : ℝ) :
    HasDerivAt (fun y : ℝ => y ^ (k + 1))
      (((k + 1 : ℕ) : ℝ) * x ^ k) x := by
  induction k with
  | zero =>
      simpa using (hasDerivAt_id x)
  | succ k ih =>
      convert ih.mul (hasDerivAt_id x) using 1 <;>
        simp [Nat.succ_eq_add_one, pow_succ, Nat.cast_add, Nat.cast_one] <;>
        ring

private theorem integral_pow_zero_two (k : ℕ) :
    (∫ x in (0 : ℝ)..2, x ^ k) =
      2 ^ (k + 1) / (((k + 1 : ℕ) : ℝ)) := by
  have hderiv : ∀ x : ℝ,
      HasDerivAt
        (fun y : ℝ => y ^ (k + 1) / (((k + 1 : ℕ) : ℝ)))
        (x ^ k) x := by
    intro x
    have hk : ((k + 1 : ℕ) : ℝ) ≠ 0 := by
      positivity
    convert (hasDerivAt_pow_succ_aux k x).div_const
      ((k + 1 : ℕ) : ℝ) using 1 <;>
      field_simp [hk] <;>
      ring
  have hint : IntervalIntegrable (fun x : ℝ => x ^ k)
      MeasureTheory.volume 0 2 :=
    (continuous_id.pow k).intervalIntegrable 0 2
  simpa using
    (intervalIntegral.integral_eq_sub_of_hasDerivAt
      (a := (0 : ℝ)) (b := 2) (fun x _ => hderiv x) hint)

private theorem integral_sincTerm (n : ℕ) :
    (∫ x in (0 : ℝ)..2, sincTerm n x) = integratedTerm n := by
  have heq : (fun x : ℝ => sincTerm n x) =
      fun x : ℝ =>
        (((-1 : ℝ) ^ n) / (Nat.factorial (2 * n + 1) : ℝ)) *
          x ^ (2 * n) := by
    funext x
    simp only [sincTerm]
    ring
  rw [heq, intervalIntegral.integral_const_mul, integral_pow_zero_two]
  unfold integratedTerm
  ring

private theorem integral_norm_sincTerm (n : ℕ) :
    (∫ x in (0 : ℝ)..2, ‖sincTerm n x‖) = sincCoeff n := by
  have hp : ∀ x : ℝ, 0 ≤ x ^ (2 * n) := by
    intro x
    rw [show 2 * n = n * 2 by omega, pow_mul]
    positivity
  have heq : (fun x : ℝ => ‖sincTerm n x‖) =
      fun x : ℝ =>
        (1 / (Nat.factorial (2 * n + 1) : ℝ)) * x ^ (2 * n) := by
    funext x
    rw [Real.norm_eq_abs]
    unfold sincTerm
    rw [abs_div, abs_mul, abs_pow, abs_of_nonneg (hp x)]
    norm_num
    rw [div_eq_mul_inv]
    ring
  rw [heq, intervalIntegral.integral_const_mul, integral_pow_zero_two]
  unfold sincCoeff
  ring

private theorem integrableOn_sincTerm_Ioc (n : ℕ) :
    MeasureTheory.IntegrableOn (sincTerm n) (Set.Ioc (0 : ℝ) 2) := by
  have h : IntervalIntegrable (sincTerm n) MeasureTheory.volume (0 : ℝ) 2 :=
    (continuous_sincTerm n).intervalIntegrable 0 2
  exact h.1

private theorem lintegral_enorm_sincTerm (n : ℕ) :
    (∫⁻ x in Set.Ioc (0 : ℝ) 2, ‖sincTerm n x‖ₑ) =
      ENNReal.ofReal (sincCoeff n) := by
  rw [← MeasureTheory.ofReal_integral_norm_eq_lintegral_enorm
    (integrableOn_sincTerm_Ioc n)]
  congr 1
  rw [← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 2)]
  exact integral_norm_sincTerm n

private theorem integratedTerm_even (n : ℕ) :
    integratedTerm (2 * n) = sincCoeff (2 * n) := by
  unfold integratedTerm sincCoeff
  rw [show (-1 : ℝ) ^ (2 * n) = 1 by rw [pow_mul]; norm_num]
  simp

private theorem integratedTerm_odd (n : ℕ) :
    integratedTerm (2 * n + 1) = -sincCoeff (2 * n + 1) := by
  unfold integratedTerm sincCoeff
  rw [show (-1 : ℝ) ^ (2 * n + 1) = -1 by
    rw [pow_add, pow_mul]
    norm_num]
  ring

private theorem remainder_bounds_of_series
    (hseries : sincIntegral = ∑' n : ℕ, integratedTerm n) :
    0 < remainder ∧ remainder < sincCoeff 4 := by
  have htail : remainder = ∑' n : ℕ, integratedTerm (n + 4) := by
    rw [remainder, partialIntegral, hseries]
    have hsplit := summable_integratedTerm.sum_add_tsum_nat_add 4
    linarith
  let e : ℕ → ℝ := fun n => sincCoeff (2 * n + 4)
  let o : ℕ → ℝ := fun n => sincCoeff (2 * n + 5)
  let e₁ : ℕ → ℝ := fun n => sincCoeff (2 * n + 6)
  have hinj4 : Function.Injective (fun n : ℕ => 2 * n + 4) :=
    two_mul_add_injective 4
  have hinj5 : Function.Injective (fun n : ℕ => 2 * n + 5) :=
    two_mul_add_injective 5
  have hinj6 : Function.Injective (fun n : ℕ => 2 * n + 6) :=
    two_mul_add_injective 6
  have he : Summable e := by
    simpa [e, Function.comp_def] using
      summable_sincCoeff.comp_injective hinj4
  have ho : Summable o := by
    simpa [o, Function.comp_def] using
      summable_sincCoeff.comp_injective hinj5
  have he₁ : Summable e₁ := by
    simpa [e₁, Function.comp_def] using
      summable_sincCoeff.comp_injective hinj6
  let d : ℕ → ℝ := fun n => e n - o n
  have hd : Summable d := he.sub ho
  have hd_nonneg : ∀ n, 0 ≤ d n := by
    intro n
    dsimp [d, e, o]
    linarith [sincCoeff_succ_lt (2 * n + 4)]
  have hd_zero : 0 < d 0 := by
    dsimp [d, e, o]
    linarith [sincCoeff_succ_lt 4]
  have hd_pos : 0 < ∑' n, d n := by
    have hs := hd.sum_add_tsum_nat_add 1
    have ht : 0 ≤ ∑' n, d (n + 1) := tsum_nonneg (fun n => hd_nonneg (n + 1))
    calc
      0 < d 0 + ∑' n, d (n + 1) := add_pos_of_pos_of_nonneg hd_zero ht
      _ = ∑' n, d n := by simpa using hs
  let d₁ : ℕ → ℝ := fun n => o n - e₁ n
  have hd₁ : Summable d₁ := ho.sub he₁
  have hd₁_nonneg : ∀ n, 0 ≤ d₁ n := by
    intro n
    dsimp [d₁, o, e₁]
    linarith [sincCoeff_succ_lt (2 * n + 5)]
  have hd₁_zero : 0 < d₁ 0 := by
    dsimp [d₁, o, e₁]
    linarith [sincCoeff_succ_lt 5]
  have hd₁_pos : 0 < ∑' n, d₁ n := by
    have hs := hd₁.sum_add_tsum_nat_add 1
    have ht : 0 ≤ ∑' n, d₁ (n + 1) :=
      tsum_nonneg (fun n => hd₁_nonneg (n + 1))
    calc
      0 < d₁ 0 + ∑' n, d₁ (n + 1) := add_pos_of_pos_of_nonneg hd₁_zero ht
      _ = ∑' n, d₁ n := by simpa using hs
  have hinjEvenTail : Function.Injective (fun n : ℕ => 2 * n + 4) :=
    two_mul_add_injective 4
  have hinjOddTail : Function.Injective (fun n : ℕ => 2 * n + 1 + 4) := by
    simpa [Nat.add_assoc] using (two_mul_add_injective 5)
  have hsumEvenTail : Summable (fun n : ℕ => integratedTerm (2 * n + 4)) :=
    summable_integratedTerm.comp_injective hinjEvenTail
  have hsumOddTail : Summable (fun n : ℕ => integratedTerm (2 * n + 1 + 4)) :=
    summable_integratedTerm.comp_injective hinjOddTail
  have hdecomp : remainder = (∑' n, e n) - ∑' n, o n := by
    rw [htail, ← tsum_even_add_odd]
    simp_rw [show ∀ n : ℕ, integratedTerm (2 * n + 4) = e n by
      intro n
      dsimp [e]
      convert integratedTerm_even (n + 2) using 1 <;> omega]
    simp_rw [show ∀ n : ℕ, integratedTerm (2 * n + 1 + 4) = -o n by
      intro n
      dsimp [o]
      convert integratedTerm_odd (n + 2) using 1 <;> omega]
    rw [tsum_neg]
    ring
    · exact hsumEvenTail
    · exact hsumOddTail
  have hesplit : (∑' n, e n) = sincCoeff 4 + ∑' n, e₁ n := by
    have hs := he.sum_add_tsum_nat_add 1
    simpa [e, e₁] using hs.symm
  have hsumd : (∑' n, d n) = (∑' n, e n) - ∑' n, o n := by
    simpa [d] using (he.hasSum.sub ho.hasSum).tsum_eq
  have hsumd₁ : (∑' n, d₁ n) = (∑' n, o n) - ∑' n, e₁ n := by
    simpa [d₁] using (ho.hasSum.sub he₁.hasSum).tsum_eq
  constructor
  · rw [hdecomp, ← hsumd]
    exact hd_pos
  · have hpositive : 0 < (∑' n, o n) - ∑' n, e₁ n := by
      rw [← hsumd₁]
      exact hd₁_pos
    rw [hdecomp, hesplit]
    linarith

theorem gap1 :
    sincIntegral =
      ∫ x in (0 : ℝ)..2, ∑' n : ℕ, sincTerm n x := by
  apply intervalIntegral.integral_congr_ae
  apply Filter.Eventually.of_forall
  intro x hx
  apply sinc_eq_tsum_sincTerm x
  simp only [Set.mem_uIoc] at hx
  rcases hx with hx | hx
  · exact ne_of_gt hx.1
  · exfalso
    linarith [hx.1, hx.2]

theorem gap2 :
    sincIntegral = ∑' n : ℕ, integratedTerm n := by
  rw [gap1]
  calc
    (∫ x in (0 : ℝ)..2, ∑' n : ℕ, sincTerm n x) =
        ∫ x in Set.Ioc (0 : ℝ) 2, ∑' n : ℕ, sincTerm n x := by
      rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 2)]
    _ = ∑' n : ℕ, ∫ x in Set.Ioc (0 : ℝ) 2, sincTerm n x := by
      apply MeasureTheory.integral_tsum
      · intro n
        exact (continuous_sincTerm n).aestronglyMeasurable
      · simp_rw [lintegral_enorm_sincTerm]
        rw [← ENNReal.ofReal_tsum_of_nonneg
          (fun n => (sincCoeff_pos n).le) summable_sincCoeff]
        exact ENNReal.ofReal_ne_top
    _ = ∑' n : ℕ, integratedTerm n := by
      apply tsum_congr
      intro n
      rw [← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 2)]
      exact integral_sincTerm n

theorem gap3 :
    0 < remainder := by
  exact (remainder_bounds_of_series gap2).1

theorem gap4 :
    remainder <
      (2 ^ 9 : ℝ) /
        (9 * (Nat.factorial 9 : ℝ)) := by
  simpa [sincCoeff] using (remainder_bounds_of_series gap2).2

theorem gap5 :
    ((2 ^ 9 : ℝ) / (9 * (Nat.factorial 9 : ℝ))) <
      (1 / 10 ^ 3 : ℝ) := by
  norm_num [Nat.factorial]

theorem gap6 :
    (0 : ℝ) < 1 / 10 ^ 3 := by
  norm_num

theorem gap7 :
    (16051 / 10000 : ℝ) < sincIntegral := by
  have hr := gap3
  norm_num [remainder, partialIntegral, integratedTerm, Finset.sum_range_succ,
    Nat.factorial] at hr ⊢
  linarith

theorem gap8 :
    sincIntegral < (16055 / 10000 : ℝ) := by
  have hr := gap4
  norm_num [remainder, partialIntegral, integratedTerm, Finset.sum_range_succ,
    Nat.factorial] at hr ⊢
  linarith

theorem gap9 :
    (16051 / 10000 : ℝ) < (16055 / 10000 : ℝ) := by
  norm_num

theorem gap10 :
    Approx sincIntegral (1605 / 1000 : ℝ)
      (1 / 1000 : ℝ) := by
  have hlo := gap7
  have hhi := gap8
  rw [Approx, abs_lt]
  constructor <;> norm_num at hlo hhi ⊢ <;> linarith

end

end ProofGap.Exercise2932_3
