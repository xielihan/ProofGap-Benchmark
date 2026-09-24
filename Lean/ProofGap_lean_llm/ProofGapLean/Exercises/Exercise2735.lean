import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace ProofGap.Exercise2735

noncomputable section

open Filter

def term (x y : ℝ) (n : ℕ) : ℝ :=
  Real.log (1 + x ^ n) / Real.rpow n y

def geometricModel (x y : ℝ) (n : ℕ) : ℝ :=
  x ^ n / Real.rpow n y

def polynomialGeometricMajorant (x y : ℝ) (n : ℕ) : ℝ :=
  Real.rpow n |y| * x ^ n

def leadingTerm (x y : ℝ) (n : ℕ) : ℝ :=
  Real.log x / Real.rpow n (y - 1)

def remainderTerm (x y : ℝ) (n : ℕ) : ℝ :=
  Real.log (1 + 1 / x ^ n) / Real.rpow n y

def rootMajorant (x y : ℝ) (n : ℕ) : ℝ :=
  Real.rpow (polynomialGeometricMajorant x y n) (1 / (n : ℝ))

theorem gap1 (x y : ℝ) (hx0 : 0 < x) (hx1 : x < 1) :
    Tendsto
      (fun n : ℕ => Real.log (1 + x ^ (n + 1)) / x ^ (n + 1))
      atTop (nhds 1) := by
  have hxpow : Tendsto (fun n : ℕ => x ^ (n + 1)) atTop (nhdsWithin 0 (Set.Ioi 0)) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · exact (tendsto_pow_atTop_nhds_zero_of_lt_one hx0.le hx1).comp (tendsto_add_atTop_nat 1)
    · exact Eventually.of_forall (fun n => pow_pos hx0 _)
  have hlog := (Real.hasDerivAt_log one_ne_zero).tendsto_slope_zero_right
  convert hlog.comp hxpow using 1
  · funext n
    simp [smul_eq_mul, div_eq_mul_inv, mul_comm]
  · norm_num

theorem gap2 (x y : ℝ) (hx0 : 0 ≤ x) (hx1 : x < 1) :
    Summable (fun n : ℕ => term x y (n + 1)) ↔
      Summable (fun n : ℕ => geometricModel x y (n + 1)) := by
  rcases hx0.eq_or_lt with rfl | hxpos
  · simp [term, geometricModel]
  · apply Asymptotics.IsEquivalent.summable_iff_nat
    rw [Asymptotics.isEquivalent_iff_exists_eq_mul]
    refine ⟨(fun n : ℕ => Real.log (1 + x ^ (n + 1)) / x ^ (n + 1)),
      gap1 x y hxpos hx1, ?_⟩
    filter_upwards [] with n
    have hxpow : x ^ (n + 1) ≠ 0 := pow_ne_zero _ hxpos.ne'
    have hnpos : 0 < (((n + 1 : ℕ) : ℝ)) := by positivity
    have hrpow : Real.rpow (((n + 1 : ℕ) : ℝ)) y ≠ 0 :=
      (Real.rpow_pos_of_pos hnpos y).ne'
    simp only [term, geometricModel, Pi.mul_apply]
    field_simp

theorem gap3 (x y : ℝ) (hx0 : 0 ≤ x) (hx1 : x < 1) :
    ∀ n : ℕ, 1 ≤ n →
      geometricModel x y n ≤ polynomialGeometricMajorant x y n := by
  intro n hn
  have hn1 : 1 ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : 0 < (n : ℝ) := zero_lt_one.trans_le hn1
  have hrpow : Real.rpow (n : ℝ) (-y) ≤ Real.rpow (n : ℝ) |y| :=
    Real.rpow_le_rpow_of_exponent_le hn1 (neg_le_abs y)
  have hinv : (Real.rpow (n : ℝ) y)⁻¹ = Real.rpow (n : ℝ) (-y) := by
    exact (Real.rpow_neg hnpos.le y).symm
  rw [geometricModel, polynomialGeometricMajorant, div_eq_mul_inv, hinv]
  simpa [mul_comm] using mul_le_mul_of_nonneg_right hrpow (pow_nonneg hx0 n)

theorem gap4 (x y : ℝ) (hx0 : 0 ≤ x) :
    Tendsto (fun n : ℕ => rootMajorant x y (n + 1)) atTop (nhds x) := by
  have hnat : Tendsto (fun n : ℕ => (((n + 1 : ℕ) : ℝ))) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hroot : Tendsto
      (fun n : ℕ => Real.rpow (((n + 1 : ℕ) : ℝ))
        (|y| / (((n + 1 : ℕ) : ℝ)))) atTop (nhds 1) := by
    simpa using (tendsto_rpow_div_mul_add |y| 1 0 zero_ne_one).comp hnat
  have heq (n : ℕ) : rootMajorant x y (n + 1) =
      Real.rpow (((n + 1 : ℕ) : ℝ)) (|y| / (((n + 1 : ℕ) : ℝ))) * x := by
    have hn0 : n + 1 ≠ 0 := Nat.succ_ne_zero n
    have hnnonneg : 0 ≤ (((n + 1 : ℕ) : ℝ)) := by positivity
    rw [rootMajorant, polynomialGeometricMajorant]
    have hmul :
        Real.rpow (Real.rpow (((n + 1 : ℕ) : ℝ)) |y| * x ^ (n + 1))
            (1 / (((n + 1 : ℕ) : ℝ))) =
          Real.rpow (Real.rpow (((n + 1 : ℕ) : ℝ)) |y|)
              (1 / (((n + 1 : ℕ) : ℝ))) *
            Real.rpow (x ^ (n + 1)) (1 / (((n + 1 : ℕ) : ℝ))) := by
      exact Real.mul_rpow (Real.rpow_nonneg hnnonneg _) (pow_nonneg hx0 _)
    rw [hmul]
    congr 1
    · calc
        Real.rpow (Real.rpow (((n + 1 : ℕ) : ℝ)) |y|)
            (1 / (((n + 1 : ℕ) : ℝ))) =
            Real.rpow (((n + 1 : ℕ) : ℝ))
              (|y| * (1 / (((n + 1 : ℕ) : ℝ)))) :=
          (Real.rpow_mul hnnonneg |y| (1 / (((n + 1 : ℕ) : ℝ)))).symm
        _ = Real.rpow (((n + 1 : ℕ) : ℝ))
            (|y| / (((n + 1 : ℕ) : ℝ))) := by congr 1; ring
    · simpa [one_div] using Real.pow_rpow_inv_natCast hx0 hn0
  convert hroot.mul_const x using 1
  · funext n
    exact heq n
  · simp

theorem gap5 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x < 1) :
    x < 1 := by
  exact hx1

theorem gap6 (x y : ℝ) (hx0 : 0 ≤ x) (hx1 : x < 1) :
    ∃ r : ℝ, r < 1 ∧
      ∀ᶠ n : ℕ in atTop, rootMajorant x y (n + 1) ≤ r := by
  refine ⟨(x + 1) / 2, by linarith, ?_⟩
  exact (gap4 x y hx0).eventually_le_const (by linarith)

theorem gap7 (x y : ℝ) (hx0 : 0 ≤ x) (hx1 : x < 1) :
    Summable (fun n : ℕ => polynomialGeometricMajorant x y (n + 1)) := by
  rcases gap6 x y hx0 hx1 with ⟨r, hr1, hrbound⟩
  have hr0 : 0 ≤ r := by
    rcases hrbound.exists with ⟨n, hn⟩
    have hmajorant : 0 ≤ polynomialGeometricMajorant x y (n + 1) := by
      rw [polynomialGeometricMajorant]
      exact mul_nonneg (Real.rpow_nonneg (by positivity) _) (pow_nonneg hx0 _)
    have hroot : 0 ≤ rootMajorant x y (n + 1) := by
      rw [rootMajorant]
      exact Real.rpow_nonneg hmajorant _
    exact hroot.trans hn
  have hrnorm : ‖r‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hr0]
    exact hr1
  have hgeom : Summable (fun n : ℕ => r ^ (n + 1)) := by
    simpa [pow_succ'] using
      (summable_geometric_of_norm_lt_one hrnorm).mul_left r
  refine hgeom.of_norm_bounded_eventually_nat ?_
  filter_upwards [hrbound] with n hn
  have hmajorant : 0 ≤ polynomialGeometricMajorant x y (n + 1) := by
    rw [polynomialGeometricMajorant]
    exact mul_nonneg (Real.rpow_nonneg (by positivity) _) (pow_nonneg hx0 _)
  have hroot_nonneg : 0 ≤ rootMajorant x y (n + 1) := by
    rw [rootMajorant]
    exact Real.rpow_nonneg hmajorant _
  have hp := pow_le_pow_left₀ hroot_nonneg hn (n + 1)
  have hrootpow : (rootMajorant x y (n + 1)) ^ (n + 1) =
      polynomialGeometricMajorant x y (n + 1) := by
    simpa [rootMajorant, one_div] using
      Real.rpow_inv_natCast_pow hmajorant (Nat.succ_ne_zero n)
  rw [hrootpow] at hp
  rw [Real.norm_eq_abs, abs_of_nonneg hmajorant]
  exact hp

theorem gap8 (x y : ℝ) (hx0 : 0 ≤ x) (hx1 : x < 1) :
    Summable (fun n : ℕ => |term x y (n + 1)|) := by
  have hgeom : Summable (fun n : ℕ => geometricModel x y (n + 1)) := by
    refine (gap7 x y hx0 hx1).of_nonneg_of_le (fun n => ?_) (fun n => ?_)
    · rw [geometricModel]
      have hn0 : 0 ≤ (((n + 1 : ℕ) : ℝ)) := by positivity
      exact div_nonneg (pow_nonneg hx0 _) (Real.rpow_nonneg hn0 y)
    · exact gap3 x y hx0 hx1 (n + 1) (by omega)
  exact ((gap2 x y hx0 hx1).2 hgeom).abs

theorem gap9 (y : ℝ) :
    ∀ n : ℕ, 1 ≤ n → term 1 y n = Real.log 2 / Real.rpow n y := by
  intro n _
  norm_num [term]

theorem gap10 (y : ℝ) (hy : 1 < y) :
    Summable (fun n : ℕ => |Real.log 2 / Real.rpow (n + 1) y|) := by
  have hbase : Summable (fun n : ℕ => 1 / Real.rpow (n : ℝ) y) := by
    exact Real.summable_one_div_nat_rpow.mpr hy
  have hshift : Summable (fun n : ℕ => 1 / Real.rpow (((n + 1 : ℕ) : ℝ)) y) :=
    (summable_nat_add_iff 1).2 hbase
  refine (hshift.mul_left (Real.log 2)).congr (fun n => ?_)
  rw [abs_of_pos]
  · simp [div_eq_mul_inv]
  · exact div_pos (Real.log_pos one_lt_two) (Real.rpow_pos_of_pos (by positivity) y)

theorem gap11 (y : ℝ) (hy : y ≤ 1) :
    ¬ Summable (fun n : ℕ => Real.log 2 / Real.rpow (n + 1) y) := by
  intro hs
  have hlog : Real.log 2 ≠ 0 := (Real.log_pos one_lt_two).ne'
  have hshift : Summable (fun n : ℕ => 1 / Real.rpow (((n + 1 : ℕ) : ℝ)) y) := by
    refine (hs.mul_left (1 / Real.log 2)).congr (fun n => ?_)
    norm_num [Nat.cast_add]
    field_simp
  have hbase : Summable (fun n : ℕ => 1 / Real.rpow (n : ℝ) y) :=
    (summable_nat_add_iff 1).1 hshift
  exact (not_lt_of_ge hy) (Real.summable_one_div_nat_rpow.mp hbase)

theorem gap12 (x y : ℝ) (hx : 1 < x) :
    ∀ n : ℕ, 1 ≤ n → term x y n = leadingTerm x y n + remainderTerm x y n := by
  intro n hn
  have hxpos : 0 < x := zero_lt_one.trans hx
  have hxn : 0 < x ^ n := pow_pos hxpos n
  have hfactor : 1 + x ^ n = x ^ n * (1 + 1 / x ^ n) := by
    field_simp
    ring
  have hone : 1 + 1 / x ^ n ≠ 0 := by positivity
  have hlog : Real.log (1 + x ^ n) =
      (n : ℝ) * Real.log x + Real.log (1 + 1 / x ^ n) := by
    rw [hfactor, Real.log_mul hxn.ne' hone, Real.log_pow]
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hrpow : Real.rpow (n : ℝ) y =
      Real.rpow (n : ℝ) (y - 1) * (n : ℝ) := by
    calc
      Real.rpow (n : ℝ) y = Real.rpow (n : ℝ) ((y - 1) + 1) := by congr 1 <;> ring
      _ = Real.rpow (n : ℝ) (y - 1) * Real.rpow (n : ℝ) 1 :=
        Real.rpow_add hnpos _ _
      _ = Real.rpow (n : ℝ) (y - 1) * (n : ℝ) := by
        congr 1
        exact Real.rpow_one _
  rw [term, leadingTerm, remainderTerm, hlog, add_div]
  congr 1
  rw [hrpow]
  field_simp

theorem gap13 (x y : ℝ) (hx : 1 < x) (hy : 2 < y) :
    Summable (fun n : ℕ => leadingTerm x y (n + 1)) := by
  have hbase : Summable (fun n : ℕ => 1 / Real.rpow (n : ℝ) (y - 1)) := by
    exact Real.summable_one_div_nat_rpow.mpr (by linarith)
  have hshift : Summable
      (fun n : ℕ => 1 / Real.rpow (((n + 1 : ℕ) : ℝ)) (y - 1)) :=
    (summable_nat_add_iff 1).2 hbase
  simpa [leadingTerm, div_eq_mul_inv] using hshift.mul_left (Real.log x)

theorem gap14 (x y : ℝ) (hx : 1 < x) (hy : 2 < y) :
    Summable (fun n : ℕ => remainderTerm x y (n + 1)) := by
  have hxpos : 0 < x := zero_lt_one.trans hx
  have hratio : ‖(1 / x : ℝ)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (div_pos zero_lt_one hxpos)]
    exact (div_lt_one hxpos).2 hx
  have hgeom : Summable (fun n : ℕ => (1 / x) ^ (n + 1)) := by
    simpa [pow_succ'] using
      (summable_geometric_of_norm_lt_one hratio).mul_left (1 / x : ℝ)
  have hrecip : Summable (fun n : ℕ => 1 / x ^ (n + 1)) := by
    refine hgeom.congr (fun n => ?_)
    simp [div_pow]
  have hlog : Summable (fun n : ℕ => Real.log (1 + 1 / x ^ (n + 1))) :=
    Real.summable_log_one_add_of_summable hrecip
  refine hlog.of_nonneg_of_le (fun n => ?_) (fun n => ?_)
  · rw [remainderTerm]
    have hinv : 0 ≤ 1 / x ^ (n + 1) := by positivity
    have hnum : 0 ≤ Real.log (1 + 1 / x ^ (n + 1)) :=
      Real.log_nonneg (by linarith)
    exact div_nonneg hnum (Real.rpow_nonneg (by positivity) _)
  · rw [remainderTerm]
    have hinv : 0 ≤ 1 / x ^ (n + 1) := by positivity
    have hnum : 0 ≤ Real.log (1 + 1 / x ^ (n + 1)) :=
      Real.log_nonneg (by linarith)
    have hn1 : (1 : ℝ) ≤ (((n + 1 : ℕ) : ℝ)) := by
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
    exact div_le_self hnum (Real.one_le_rpow hn1 (by linarith))

theorem gap15 (x y : ℝ) (hx : 1 < x) (hy : 2 < y) :
    Summable (fun n : ℕ => |term x y (n + 1)|) := by
  have hs := (gap13 x y hx hy).add (gap14 x y hx hy)
  have ht : Summable (fun n : ℕ => term x y (n + 1)) := by
    refine hs.congr (fun n => ?_)
    exact (gap12 x y hx (n + 1) (by omega)).symm
  exact ht.abs

theorem gap16 (x y : ℝ) (hx : 1 < x) (hy : y ≤ 2) :
    ¬ Summable (fun n : ℕ => leadingTerm x y (n + 1)) := by
  intro hs
  have hlog : Real.log x ≠ 0 := (Real.log_pos hx).ne'
  have hshift : Summable
      (fun n : ℕ => 1 / Real.rpow (((n + 1 : ℕ) : ℝ)) (y - 1)) := by
    refine (hs.mul_left (1 / Real.log x)).congr (fun n => ?_)
    rw [leadingTerm]
    field_simp
  have hbase : Summable (fun n : ℕ => 1 / Real.rpow (n : ℝ) (y - 1)) :=
    (summable_nat_add_iff 1).1 hshift
  exact (not_lt_of_ge (by linarith : y - 1 ≤ 1))
    (Real.summable_one_div_nat_rpow.mp hbase)

theorem gap17 (x y : ℝ) (hx : 1 < x) (hy : y ≤ 2) :
    ¬ Summable (fun n : ℕ => term x y (n + 1)) := by
  intro hs
  apply gap16 x y hx hy
  refine hs.of_nonneg_of_le (fun n => ?_) (fun n => ?_)
  · rw [leadingTerm]
    exact div_nonneg (Real.log_pos hx).le (Real.rpow_nonneg (by positivity) _)
  · rw [gap12 x y hx (n + 1) (by omega)]
    apply le_add_of_nonneg_right
    rw [remainderTerm]
    have hinv : 0 ≤ 1 / x ^ (n + 1) := by positivity
    have hnum : 0 ≤ Real.log (1 + 1 / x ^ (n + 1)) :=
      Real.log_nonneg (by linarith)
    exact div_nonneg hnum (Real.rpow_nonneg (by positivity) _)

theorem gap18 (x y : ℝ) (hx : 0 ≤ x) :
    ((0 ≤ x ∧ x < 1) ∨ (x = 1 ∧ 1 < y) ∨ (1 < x ∧ 2 < y)) ↔
      Summable (fun n : ℕ => |term x y (n + 1)|) := by
  constructor
  · rintro (hsmall | hone | hlarge)
    · exact gap8 x y hsmall.1 hsmall.2
    · rcases hone with ⟨rfl, hy⟩
      refine (gap10 y hy).congr (fun n => ?_)
      rw [gap9 y (n + 1) (by omega)]
      norm_num [Nat.cast_add]
    · exact gap15 x y hlarge.1 hlarge.2
  · intro habs
    have hs : Summable (fun n : ℕ => term x y (n + 1)) := by
      apply Summable.of_norm
      simpa [Real.norm_eq_abs] using habs
    rcases lt_trichotomy x 1 with hsmall | heq | hlarge
    · exact Or.inl ⟨hx, hsmall⟩
    · subst x
      apply Or.inr
      apply Or.inl
      refine ⟨rfl, ?_⟩
      by_contra hnot
      apply gap11 y (le_of_not_gt hnot)
      refine hs.congr (fun n => ?_)
      simpa [Nat.cast_add] using gap9 y (n + 1) (by omega)
    · apply Or.inr
      apply Or.inr
      refine ⟨hlarge, ?_⟩
      by_contra hnot
      exact gap17 x y hlarge (le_of_not_gt hnot) hs

end

end ProofGap.Exercise2735
