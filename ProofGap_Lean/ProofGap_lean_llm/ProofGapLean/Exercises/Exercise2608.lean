import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.PSeries

namespace ProofGap.Exercise2608

noncomputable section

open Filter

def term (p : ℝ) (n : ℕ) : ℝ :=
  Real.rpow n (-p) * Real.sin (Real.pi / n)

def comparison (p : ℝ) (n : ℕ) : ℝ :=
  Real.rpow n (-(p + 1))

def converges (p : ℝ) : Prop :=
  Summable (fun n : ℕ => term p (n + 1))

private theorem quotient_eq (p : ℝ) (n : ℕ) (hn : 1 ≤ n) :
    term p n / comparison p n = (n : ℝ) * Real.sin (Real.pi / n) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hrp : Real.rpow n (-p) ≠ 0 := (Real.rpow_pos_of_pos hnpos (-p)).ne'
  have hone : Real.rpow n 1 = (n : ℝ) := by
    simpa using Real.rpow_natCast (n : ℝ) 1
  have hden : Real.rpow n (-(p + 1)) = Real.rpow n (-p) / (n : ℝ) := by
    calc
      Real.rpow n (-(p + 1)) = Real.rpow n ((-p) - 1) := by congr 1; ring
      _ = Real.rpow n (-p) / Real.rpow n 1 := Real.rpow_sub hnpos (-p) 1
      _ = Real.rpow n (-p) / (n : ℝ) := by rw [hone]
  unfold term comparison
  rw [hden]
  field_simp [hnpos.ne', hrp]

private theorem quotient_tendsto (p : ℝ) :
    Tendsto (fun n : ℕ => term p (n + 1) / comparison p (n + 1))
      atTop (nhds Real.pi) := by
  have hsin : Tendsto (fun x : ℝ => Real.sin x / x)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
    have h := (Real.hasDerivAt_sin 0).tendsto_slope_zero_right
    convert h using 1 <;> simp [div_eq_mul_inv, mul_comm]
  have hcast : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
  have hinvZero : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1))
      atTop (nhds 0) := by
    simpa [one_div] using tendsto_inv_atTop_zero.comp hcast
  have hargZero : Tendsto (fun n : ℕ => Real.pi / ((n : ℝ) + 1))
      atTop (nhds 0) := by
    simpa [div_eq_mul_inv] using Filter.Tendsto.const_mul Real.pi hinvZero
  have harg : Tendsto (fun n : ℕ => Real.pi / ((n : ℝ) + 1))
      atTop (nhdsWithin 0 (Set.Ioi 0)) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · exact hargZero
    · exact Filter.Eventually.of_forall (fun n => by
        simp only [Set.mem_Ioi]
        positivity)
  have hscaled : Tendsto (fun n : ℕ => Real.pi *
      (Real.sin (Real.pi / ((n : ℝ) + 1)) / (Real.pi / ((n : ℝ) + 1))))
      atTop (nhds Real.pi) := by
    simpa using Filter.Tendsto.const_mul Real.pi (hsin.comp harg)
  apply hscaled.congr'
  filter_upwards [] with n
  rw [quotient_eq p (n + 1) (by omega)]
  simp only [Nat.cast_add, Nat.cast_one]
  have hm : (n : ℝ) + 1 ≠ 0 := by positivity
  field_simp [hm, Real.pi_ne_zero]

private theorem comparison_summable_iff (p : ℝ) :
    Summable (fun n : ℕ => comparison p (n + 1)) ↔ 0 < p := by
  let e : ℝ := -(p + 1)
  change Summable (fun n : ℕ => Real.rpow (n + 1 : ℕ) e) ↔ 0 < p
  constructor
  · intro hshift
    have hall : Summable (fun n : ℕ => Real.rpow n e) :=
      (summable_nat_add_iff 1).mp hshift
    have he := Real.summable_nat_rpow.mp hall
    dsimp [e] at he
    linarith
  · intro hp
    have hall : Summable (fun n : ℕ => Real.rpow n e) :=
      Real.summable_nat_rpow.mpr (by dsimp [e]; linarith)
    exact (summable_nat_add_iff 1).mpr hall

private theorem term_pos (p : ℝ) (n : ℕ) (hn : 1 < n) : 0 < term p n := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (Nat.zero_lt_of_lt hn)
  have hnreal : (1 : ℝ) < n := by exact_mod_cast hn
  have hargPos : 0 < Real.pi / (n : ℝ) := div_pos Real.pi_pos hnpos
  have hargLt : Real.pi / (n : ℝ) < Real.pi := by
    rw [div_lt_iff₀ hnpos]
    nlinarith [Real.pi_pos]
  unfold term
  exact mul_pos (Real.rpow_pos_of_pos hnpos (-p))
    (Real.sin_pos_of_pos_of_lt_pi hargPos hargLt)

private theorem comparison_isBigO_term (p : ℝ) :
    Asymptotics.IsBigO atTop
      (fun n : ℕ => comparison p (n + 1))
      (fun n : ℕ => term p (n + 1)) := by
  have hinv := (quotient_tendsto p).inv₀ Real.pi_ne_zero
  have hinv' : Tendsto (fun n : ℕ =>
      (term p (n + 1) / comparison p (n + 1))⁻¹)
      atTop (nhds (1 / Real.pi)) := by
    simpa [one_div] using hinv
  have hrev : Tendsto (fun n : ℕ => comparison p (n + 1) / term p (n + 1))
      atTop (nhds (1 / Real.pi)) := by
    apply hinv'.congr'
    filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    have ht : term p (n + 1) ≠ 0 := (term_pos p (n + 1) (by omega)).ne'
    have hc : comparison p (n + 1) ≠ 0 := by
      unfold comparison
      exact (Real.rpow_pos_of_pos (by positivity) _).ne'
    field_simp [ht, hc]
  refine Asymptotics.isBigO_of_div_tendsto_nhds
    (f := fun n : ℕ => comparison p (n + 1))
    (g := fun n : ℕ => term p (n + 1)) ?_ (1 / Real.pi) ?_
  · filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    intro hzero
    exact False.elim ((term_pos p (n + 1) (by omega)).ne' hzero)
  · simpa only [Pi.div_apply] using hrev

theorem gap1 (p : ℝ) (n : ℕ) (hn : 1 ≤ n) :
    0 ≤ term p n := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hnreal : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hargNonneg : 0 ≤ Real.pi / (n : ℝ) := (div_pos Real.pi_pos hnpos).le
  have hargLe : Real.pi / (n : ℝ) ≤ Real.pi := by
    rw [div_le_iff₀ hnpos]
    nlinarith [Real.pi_pos]
  unfold term
  exact mul_nonneg (Real.rpow_nonneg hnpos.le _)
    (Real.sin_nonneg_of_nonneg_of_le_pi hargNonneg hargLe)

theorem gap2 (p : ℝ) :
    Tendsto
      (fun n : ℕ => term p (n + 1) / comparison p (n + 1))
      atTop (nhds Real.pi) := by
  exact quotient_tendsto p

theorem gap3 (p : ℝ) :
    Asymptotics.IsBigO atTop
      (fun n : ℕ => term p (n + 1))
      (fun n : ℕ => comparison p (n + 1)) := by
  apply Asymptotics.isBigO_of_div_tendsto_nhds
    (Filter.Eventually.of_forall (fun n hzero =>
      False.elim ((show comparison p (n + 1) ≠ 0 by
        unfold comparison
        exact (Real.rpow_pos_of_pos (by positivity) _).ne') hzero))) Real.pi
  simpa only [Pi.div_apply] using gap2 p

theorem gap4 (p : ℝ) (hp : 0 < p) :
    converges p := by
  unfold converges
  exact summable_of_isBigO_nat ((comparison_summable_iff p).2 hp) (gap3 p)

theorem gap5 (p : ℝ) :
    p + 1 > 1 ↔ p > 0 := by constructor <;> intro h <;> linarith

theorem gap6 (p : ℝ) :
    converges p ↔ 0 < p := by
  constructor
  · intro hconv
    unfold converges at hconv
    have hcomparison : Summable (fun n : ℕ => comparison p (n + 1)) :=
      summable_of_isBigO_nat hconv (comparison_isBigO_term p)
    exact (comparison_summable_iff p).1 hcomparison
  · exact gap4 p

end

end ProofGap.Exercise2608
