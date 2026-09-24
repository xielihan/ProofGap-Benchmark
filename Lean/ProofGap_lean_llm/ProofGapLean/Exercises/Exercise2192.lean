import ProofGapLean.Prelude.Analysis
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Complex.BigOperators
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Integrals.PosLogEqCircleAverage
import Mathlib.FieldTheory.KummerExtension
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Tactic.Continuity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise2192
noncomputable section

open Filter ComplexConjugate
open scoped BigOperators ComplexConjugate Interval

def factor (α x : ℝ) : ℝ :=
  1 - 2 * α * Real.cos x + α ^ 2

def S (α : ℝ) (n : ℕ) : ℝ :=
  (Real.pi / n) *
    ∑ i ∈ Finset.range n, Real.log (factor α (((i : ℝ) + 1) * Real.pi / n))

def interiorProduct (t : ℝ) (n : ℕ) : ℝ :=
  ∏ i ∈ Finset.range (n - 1), factor t (((i : ℝ) + 1) * Real.pi / n)

def epsilon (i n : ℕ) : ℂ :=
  (Real.cos ((i : ℝ) * Real.pi / n) : ℂ) +
    Complex.I * Real.sin ((i : ℝ) * Real.pi / n)

def complexInteriorProduct (t : ℂ) (n : ℕ) : ℂ :=
  ∏ i ∈ Finset.range (n - 1),
    (t - epsilon (i + 1) n) * (t - conj (epsilon (i + 1) n))

private theorem prod_range_double_pair {M : Type*} [CommMonoid M]
    (f : ℕ → M) (n : ℕ) (hn : 0 < n) :
    (∏ k ∈ Finset.range (2 * n), f k) =
      f 0 * f n *
        ∏ j ∈ Finset.range (n - 1), f (j + 1) * f (2 * n - (j + 1)) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  change
    (∏ k ∈ Finset.range (2 * (m + 1)), f k) =
      f 0 * f (m + 1) *
        ∏ j ∈ Finset.range m,
          f (j + 1) * f (2 * (m + 1) - (j + 1))
  have hreflect :
      (∏ j ∈ Finset.range m, f ((m + 1) + (j + 1))) =
        ∏ j ∈ Finset.range m, f (2 * (m + 1) - (j + 1)) := by
    calc
      (∏ j ∈ Finset.range m, f ((m + 1) + (j + 1))) =
          ∏ j ∈ Finset.range m,
            f ((m + 1) + ((m - 1 - j) + 1)) :=
        (Finset.prod_range_reflect
          (fun j => f ((m + 1) + (j + 1))) m).symm
      _ = ∏ j ∈ Finset.range m,
          f (2 * (m + 1) - (j + 1)) := by
        apply Finset.prod_congr rfl
        intro j hj
        simp only [Finset.mem_range] at hj
        congr 1
        omega
  conv_lhs =>
    rw [show 2 * (m + 1) = (m + 1) + (m + 1) by omega,
      Finset.prod_range_add]
  rw [Finset.prod_range_succ', Finset.prod_range_succ']
  simp only [Nat.add_zero]
  rw [hreflect, Finset.prod_mul_distrib]
  ac_rfl

private theorem epsilon_eq_pow (i n : ℕ) (hn : 0 < n) :
    epsilon i n = (epsilon 1 n) ^ i := by
  have h := Complex.cos_add_sin_mul_I_pow i
    (((Real.pi / (n : ℝ) : ℝ) : ℂ))
  have harg :
      (i : ℂ) * (((Real.pi / (n : ℝ) : ℝ) : ℂ)) =
        ((((i : ℝ) * Real.pi / n : ℝ) : ℂ)) := by
    push_cast
    ring
  rw [harg] at h
  unfold epsilon
  symm
  simpa only [Nat.cast_one, one_mul, mul_one, ← Complex.ofReal_cos,
    ← Complex.ofReal_sin, mul_comm] using h

private theorem epsilon_one_eq_exp (n : ℕ) (hn : 0 < n) :
    epsilon 1 n = Complex.exp (2 * Real.pi * Complex.I / (2 * n)) := by
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have harg :
      (2 : ℂ) * Real.pi * Complex.I / (2 * (n : ℂ)) =
        (((Real.pi / (n : ℝ) : ℝ) : ℂ)) * Complex.I := by
    push_cast
    field_simp [hnC]
  rw [harg, Complex.exp_mul_I]
  unfold epsilon
  simp only [Nat.cast_one, one_mul, mul_one, ← Complex.ofReal_cos,
    ← Complex.ofReal_sin]
  ring

private theorem epsilon_one_isPrimitiveRoot (n : ℕ) (hn : 0 < n) :
    IsPrimitiveRoot (epsilon 1 n) (2 * n) := by
  have h2n : 2 * n ≠ 0 := Nat.mul_ne_zero (by norm_num) (Nat.ne_of_gt hn)
  have h := Complex.isPrimitiveRoot_exp (2 * n) h2n
  rw [epsilon_one_eq_exp n hn]
  simpa only [Nat.cast_mul, Nat.cast_ofNat] using h

private theorem epsilon_self (n : ℕ) (hn : 0 < n) :
    epsilon n n = (-1 : ℂ) := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  unfold epsilon
  have harg : (n : ℝ) * Real.pi / n = Real.pi := by
    field_simp [hnR]
  rw [harg, Real.cos_pi, Real.sin_pi]
  norm_num

private theorem epsilon_mul_conj (i n : ℕ) :
    epsilon i n * conj (epsilon i n) = 1 := by
  let θ : ℝ := (i : ℝ) * Real.pi / n
  have hI : Complex.I * Complex.I = (-1 : ℂ) := by norm_num
  have htrigR : Real.cos θ * Real.cos θ + Real.sin θ * Real.sin θ = 1 := by
    nlinarith [Real.cos_sq_add_sin_sq θ]
  have htrigC :
      (Real.cos θ : ℂ) * Real.cos θ +
        (Real.sin θ : ℂ) * Real.sin θ = 1 := by
    exact_mod_cast htrigR
  unfold epsilon
  rw [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I,
    Complex.conj_ofReal]
  change
    ((Real.cos θ : ℂ) + Complex.I * Real.sin θ) *
        ((Real.cos θ : ℂ) + (-Complex.I) * Real.sin θ) = 1
  calc
    ((Real.cos θ : ℂ) + Complex.I * Real.sin θ) *
          ((Real.cos θ : ℂ) + (-Complex.I) * Real.sin θ) =
        (Real.cos θ : ℂ) * Real.cos θ -
          (Complex.I * Complex.I) *
            ((Real.sin θ : ℂ) * Real.sin θ) := by ring
    _ = (Real.cos θ : ℂ) * Real.cos θ +
          (Real.sin θ : ℂ) * Real.sin θ := by rw [hI]; ring
    _ = 1 := htrigC

private theorem epsilon_complement_pow (k n : ℕ) (hn : 0 < n)
    (hk : k < n) :
    (epsilon 1 n) ^ (2 * n - k) = conj (epsilon k n) := by
  let ζ : ℂ := epsilon 1 n
  have hroot : IsPrimitiveRoot ζ (2 * n) := epsilon_one_isPrimitiveRoot n hn
  have hζ0 : ζ ≠ 0 := by
    intro hzero
    have hp := hroot.pow_eq_one
    rw [hzero, zero_pow (by omega : 2 * n ≠ 0)] at hp
    exact zero_ne_one hp
  have hk2 : k ≤ 2 * n := by omega
  have hleft : ζ ^ (2 * n - k) * ζ ^ k = 1 := by
    rw [← pow_add, Nat.sub_add_cancel hk2, hroot.pow_eq_one]
  have hright : conj (epsilon k n) * ζ ^ k = 1 := by
    rw [← epsilon_eq_pow k n hn]
    simpa only [mul_comm] using epsilon_mul_conj k n
  apply mul_right_cancel₀ (pow_ne_zero k hζ0)
  rw [hleft, hright]

private theorem factor_cast (t : ℝ) (i n : ℕ) :
    ((factor t ((i : ℝ) * Real.pi / n) : ℝ) : ℂ) =
      ((t : ℂ) - epsilon i n) * ((t : ℂ) - conj (epsilon i n)) := by
  have hsum :
      epsilon i n + conj (epsilon i n) =
        2 * (Real.cos ((i : ℝ) * Real.pi / n) : ℂ) := by
    unfold epsilon
    rw [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I,
      Complex.conj_ofReal]
    ring
  have hprod := epsilon_mul_conj i n
  calc
    ((factor t ((i : ℝ) * Real.pi / n) : ℝ) : ℂ) =
        (1 : ℂ) - 2 * t * Real.cos ((i : ℝ) * Real.pi / n) + t ^ 2 := by
      norm_cast
    _ = (t : ℂ) ^ 2 - (t : ℂ) *
          (epsilon i n + conj (epsilon i n)) +
          epsilon i n * conj (epsilon i n) := by rw [hsum, hprod]; ring
    _ = ((t : ℂ) - epsilon i n) *
          ((t : ℂ) - conj (epsilon i n)) := by ring

private theorem complex_factorization (t : ℂ) (n : ℕ) (hn : 0 < n) :
    t ^ (2 * n) - 1 =
      (t + 1) * (t - 1) * complexInteriorProduct t n := by
  let ζ : ℂ := epsilon 1 n
  have hroot : IsPrimitiveRoot ζ (2 * n) := epsilon_one_isPrimitiveRoot n hn
  have h2n : 0 < 2 * n := by omega
  have hpoly := X_pow_sub_C_eq_prod hroot h2n
    (by simp : (1 : ℂ) ^ (2 * n) = 1)
  have heval := congrArg (Polynomial.eval t) hpoly
  have hprod :
      t ^ (2 * n) - 1 =
        ∏ k ∈ Finset.range (2 * n), (t - ζ ^ k) := by
    simpa [ζ, Polynomial.eval_prod] using heval
  rw [prod_range_double_pair (fun k => t - ζ ^ k) n hn] at hprod
  have hzn : ζ ^ n = (-1 : ℂ) := by
    dsimp [ζ]
    rw [← epsilon_eq_pow n n hn]
    exact epsilon_self n hn
  have hpair :
      (∏ j ∈ Finset.range (n - 1),
          (t - ζ ^ (j + 1)) * (t - ζ ^ (2 * n - (j + 1)))) =
        complexInteriorProduct t n := by
    unfold complexInteriorProduct
    apply Finset.prod_congr rfl
    intro j hj
    simp only [Finset.mem_range] at hj
    have hk : j + 1 < n := by omega
    dsimp [ζ]
    rw [← epsilon_eq_pow (j + 1) n hn,
      epsilon_complement_pow (j + 1) n hn hk]
  rw [pow_zero, hzn, hpair] at hprod
  calc
    t ^ (2 * n) - 1 =
        (t - 1) * (t - (-1)) * complexInteriorProduct t n := hprod
    _ = (t + 1) * (t - 1) * complexInteriorProduct t n := by ring

private theorem complexInteriorProduct_ofReal (t : ℝ) (n : ℕ) :
    ((interiorProduct t n : ℝ) : ℂ) = complexInteriorProduct t n := by
  change
    ((∏ i ∈ Finset.range (n - 1),
        factor t (((i : ℝ) + 1) * Real.pi / n) : ℝ) : ℂ) =
      ∏ i ∈ Finset.range (n - 1),
        ((t : ℂ) - epsilon (i + 1) n) *
          ((t : ℂ) - conj (epsilon (i + 1) n))
  calc
    ((∏ i ∈ Finset.range (n - 1),
        factor t (((i : ℝ) + 1) * Real.pi / n) : ℝ) : ℂ) =
        ∏ i ∈ Finset.range (n - 1),
          ((factor t (((i : ℝ) + 1) * Real.pi / n) : ℝ) : ℂ) :=
      Complex.ofReal_prod _ _
    _ = ∏ i ∈ Finset.range (n - 1),
        ((t : ℂ) - epsilon (i + 1) n) *
          ((t : ℂ) - conj (epsilon (i + 1) n)) := by
      apply Finset.prod_congr rfl
      intro i hi
      convert factor_cast t (i + 1) n using 1 <;> push_cast <;> ring

private theorem factor_eq_circleNorm_sq (α x : ℝ) :
    factor α x = ‖circleMap 0 1 x - (α : ℂ)‖ ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_sub]
  simp [factor, circleMap, Complex.normSq_apply, Complex.exp_mul_I,
    Complex.cos_ofReal_re, Complex.sin_ofReal_re]
  nlinarith [Real.cos_sq_add_sin_sq x]

private theorem log_factor_eq_two_circleLog (α x : ℝ) :
    Real.log (factor α x) =
      2 * Real.log ‖circleMap 0 1 x - (α : ℂ)‖ := by
  rw [factor_eq_circleNorm_sq, Real.log_pow]
  norm_num

private theorem circleLog_reflect (α x : ℝ) :
    Real.log ‖circleMap 0 1 (2 * Real.pi - x) - (α : ℂ)‖ =
      Real.log ‖circleMap 0 1 x - (α : ℂ)‖ := by
  have hsquares :
      ‖circleMap 0 1 (2 * Real.pi - x) - (α : ℂ)‖ ^ 2 =
        ‖circleMap 0 1 x - (α : ℂ)‖ ^ 2 := by
    rw [← factor_eq_circleNorm_sq, ← factor_eq_circleNorm_sq]
    unfold factor
    rw [Real.cos_two_pi_sub]
  have hnorm :
      ‖circleMap 0 1 (2 * Real.pi - x) - (α : ℂ)‖ =
        ‖circleMap 0 1 x - (α : ℂ)‖ := by
    nlinarith [norm_nonneg (circleMap 0 1 (2 * Real.pi - x) - (α : ℂ)),
      norm_nonneg (circleMap 0 1 x - (α : ℂ))]
  rw [hnorm]

private theorem integral_log_factor_eq_circleLog (α : ℝ) :
    (∫ x in (0 : ℝ)..Real.pi, Real.log (factor α x)) =
      ∫ x in (0 : ℝ)..2 * Real.pi,
        Real.log ‖circleMap 0 1 x - (α : ℂ)‖ := by
  let g : ℝ → ℝ := fun x => Real.log ‖circleMap 0 1 x - (α : ℂ)‖
  have hfull :
      IntervalIntegrable g MeasureTheory.volume 0 (2 * Real.pi) := by
    simpa [g] using
      (circleIntegrable_log_norm_sub_const
        (a := (α : ℂ)) (c := (0 : ℂ)) (r := (1 : ℝ)))
  have hhalf :
      IntervalIntegrable g MeasureTheory.volume 0 Real.pi := by
    apply hfull.mono_set
    rw [Set.uIcc_of_le Real.pi_pos.le,
      Set.uIcc_of_le (mul_nonneg (by norm_num) Real.pi_pos.le)]
    exact Set.Icc_subset_Icc le_rfl (by linarith [Real.pi_pos])
  have hsecond :
      IntervalIntegrable g MeasureTheory.volume Real.pi (2 * Real.pi) := by
    apply hfull.mono_set
    rw [Set.uIcc_of_le (by linarith [Real.pi_pos]),
      Set.uIcc_of_le (mul_nonneg (by norm_num) Real.pi_pos.le)]
    exact Set.Icc_subset_Icc Real.pi_pos.le le_rfl
  have hsub :
      (∫ x in (0 : ℝ)..Real.pi, g (2 * Real.pi - x)) =
        ∫ x in Real.pi..2 * Real.pi, g x := by
    convert intervalIntegral.integral_comp_sub_left
      (f := g) (a := (0 : ℝ)) (b := Real.pi) (2 * Real.pi) using 1 <;> ring
  have hsecond_eq :
      (∫ x in Real.pi..2 * Real.pi, g x) =
        ∫ x in (0 : ℝ)..Real.pi, g x := by
    calc
      (∫ x in Real.pi..2 * Real.pi, g x) =
          ∫ x in (0 : ℝ)..Real.pi, g (2 * Real.pi - x) := hsub.symm
      _ = ∫ x in (0 : ℝ)..Real.pi, g x := by
        apply intervalIntegral.integral_congr
        intro x hx
        exact circleLog_reflect α x
  calc
    (∫ x in (0 : ℝ)..Real.pi, Real.log (factor α x)) =
        ∫ x in (0 : ℝ)..Real.pi, 2 * g x := by
      apply intervalIntegral.integral_congr
      intro x hx
      exact log_factor_eq_two_circleLog α x
    _ = 2 * ∫ x in (0 : ℝ)..Real.pi, g x := by
      rw [intervalIntegral.integral_const_mul]
    _ = (∫ x in (0 : ℝ)..Real.pi, g x) +
          ∫ x in Real.pi..2 * Real.pi, g x := by
      rw [hsecond_eq]
      ring
    _ = ∫ x in (0 : ℝ)..2 * Real.pi, g x :=
      intervalIntegral.integral_add_adjacent_intervals hhalf hsecond

private theorem integral_log_factor_formula (α : ℝ) :
    (∫ x in (0 : ℝ)..Real.pi, Real.log (factor α x)) =
      2 * Real.pi * Real.posLog |α| := by
  rw [integral_log_factor_eq_circleLog]
  have havg :=
    circleAverage_log_norm_sub_const_eq_posLog (a := (α : ℂ))
  rw [Real.circleAverage_def] at havg
  simp only [smul_eq_mul] at havg
  calc
    (∫ x in (0 : ℝ)..2 * Real.pi,
        Real.log ‖circleMap 0 1 x - (α : ℂ)‖) =
        2 * Real.pi *
          ((2 * Real.pi)⁻¹ *
            ∫ x in (0 : ℝ)..2 * Real.pi,
              Real.log ‖circleMap 0 1 x - (α : ℂ)‖) := by
      field_simp [Real.pi_ne_zero]
    _ = 2 * Real.pi * Real.posLog ‖(α : ℂ)‖ := by rw [havg]
    _ = 2 * Real.pi * Real.posLog |α| := by simp

theorem gap1 (α x : ℝ) :
    (1 - |α|) ^ 2 ≤ factor α x := by
  have hcos : α * Real.cos x ≤ |α| := by
    calc
      α * Real.cos x ≤ |α * Real.cos x| := le_abs_self _
      _ = |α| * |Real.cos x| := abs_mul _ _
      _ ≤ |α| * 1 :=
        mul_le_mul_of_nonneg_left (Real.abs_cos_le_one x) (abs_nonneg α)
      _ = |α| := mul_one _
  have hsquare : |α| ^ 2 = α ^ 2 := sq_abs α
  unfold factor
  nlinarith

theorem gap2 (α : ℝ) (hα : |α| ≠ 1) :
    ContinuousOn (fun x => Real.log (factor α x)) (Set.Icc 0 Real.pi) := by
  have hnonzero : 1 - |α| ≠ 0 := sub_ne_zero.mpr hα.symm
  have hpositive : ∀ x : ℝ, 0 < factor α x := by
    intro x
    have hlower := gap1 α x
    have hsquare : 0 < (1 - |α|) ^ 2 := sq_pos_of_ne_zero hnonzero
    linarith
  apply ContinuousOn.log
  · unfold factor
    fun_prop
  · intro x hx
    exact ne_of_gt (hpositive x)

theorem gap3 (α : ℝ) (n : ℕ) (hn : 0 < n) :
    S α n =
      (Real.pi / n) *
        ∑ i ∈ Finset.range n,
          Real.log (factor α (((i : ℝ) + 1) * Real.pi / n)) := by
  rfl

theorem gap4 (α : ℝ) (n : ℕ) (hn : 0 < n) (hα : |α| ≠ 1) :
    S α n =
      (Real.pi / n) *
        Real.log ((1 + α) ^ 2 * interiorProduct α n) := by
  have hbase : 1 - |α| ≠ 0 := sub_ne_zero.mpr hα.symm
  have hfactor : ∀ x : ℝ, 0 < factor α x := by
    intro x
    have hlower := gap1 α x
    have hsquare : 0 < (1 - |α|) ^ 2 := sq_pos_of_ne_zero hbase
    linarith
  have hprod :
      (∏ i ∈ Finset.range n,
          factor α (((i : ℝ) + 1) * Real.pi / n)) =
        (1 + α) ^ 2 * interiorProduct α n := by
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
    have hmR : ((m + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    have hangle :
        (((m : ℝ) + 1) * Real.pi / (m + 1 : ℕ)) = Real.pi := by
      field_simp [hmR]
      norm_cast
    rw [Finset.prod_range_succ]
    unfold interiorProduct
    simp only [Nat.succ_sub_one]
    rw [hangle]
    unfold factor
    rw [Real.cos_pi]
    ring
  unfold S
  have hlog :
      (∑ i ∈ Finset.range n,
          Real.log (factor α (((i : ℝ) + 1) * Real.pi / n))) =
        Real.log (∏ i ∈ Finset.range n,
          factor α (((i : ℝ) + 1) * Real.pi / n)) :=
    (Real.log_prod (s := Finset.range n)
      (f := fun i => factor α (((i : ℝ) + 1) * Real.pi / n))
      (fun i hi => ne_of_gt
        (hfactor (((i : ℝ) + 1) * Real.pi / n)))).symm
  rw [hlog, hprod]

theorem gap5 (n : ℕ) (hn : 0 < n) :
    ∃ ε : ℕ → ℂ, ∀ t : ℂ,
      t ^ (2 * n) - 1 =
        (t + 1) * (t - 1) *
          ∏ i ∈ Finset.range (n - 1),
            (t - ε (i + 1)) * (t - conj (ε (i + 1))) := by
  refine ⟨fun i => epsilon i n, ?_⟩
  intro t
  simpa only [complexInteriorProduct] using complex_factorization t n hn

theorem gap6 (n : ℕ) (hn : 0 < n) :
    ∃ ε : ℕ → ℂ, ∀ i < n,
      ε i =
        (Real.cos ((i : ℝ) * Real.pi / n) : ℂ) +
          Complex.I * Real.sin ((i : ℝ) * Real.pi / n) := by
  refine ⟨fun i => epsilon i n, ?_⟩
  intro i hi
  rfl

theorem gap7 (n : ℕ) (hn : 0 < n) :
    ∃ ε : ℕ → ℂ, ∀ i < n,
      conj (ε i) =
        (Real.cos ((i : ℝ) * Real.pi / n) : ℂ) -
          Complex.I * Real.sin ((i : ℝ) * Real.pi / n) := by
  refine ⟨fun i => epsilon i n, ?_⟩
  intro i hi
  unfold epsilon
  rw [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I,
    Complex.conj_ofReal]
  ring

theorem gap8 (t : ℝ) (n : ℕ) (hn : 0 < n) :
    t ^ (2 * n) - 1 = (t ^ 2 - 1) * interiorProduct t n := by
  have hc := complex_factorization (t : ℂ) n hn
  rw [← complexInteriorProduct_ofReal t n] at hc
  have hc' :
      (((t ^ (2 * n) - 1 : ℝ) : ℂ)) =
        ((((t ^ 2 - 1) * interiorProduct t n : ℝ) : ℂ)) := by
    push_cast
    calc
      (t : ℂ) ^ (2 * n) - 1 =
          ((t : ℂ) + 1) * ((t : ℂ) - 1) *
            (interiorProduct t n : ℂ) := hc
      _ = (((t : ℂ) ^ 2 - 1) * (interiorProduct t n : ℂ)) := by ring
  exact_mod_cast hc'

theorem gap9 (t : ℝ) (n : ℕ) (hn : 0 < n) :
    t ^ (2 * n) - 1 = (t ^ 2 - 1) * interiorProduct t n := by
  exact gap8 t n hn

theorem gap10 (α : ℝ) (n : ℕ) (hn : 0 < n) (hα : |α| ≠ 1) :
    S α n =
      (Real.pi / n) *
        Real.log (((α + 1) / (α - 1)) * (α ^ (2 * n) - 1)) := by
  have hα1 : α ≠ 1 := by
    intro h
    subst α
    norm_num at hα
  have hαneg1 : α ≠ -1 := by
    intro h
    subst α
    norm_num at hα
  have hden : α - 1 ≠ 0 := sub_ne_zero.mpr hα1
  rw [gap4 α n hn hα]
  congr 2
  rw [gap8 α n hn]
  field_simp [hden]
  ring

theorem gap11 (α : ℝ) (hα : |α| < 1) :
    Tendsto (S α) atTop (nhds (0 : ℝ)) := by
  have hαbounds : -1 < α ∧ α < 1 := abs_lt.mp hα
  have hαne : |α| ≠ 1 := ne_of_lt hα
  let c : ℝ := (α + 1) / (α - 1)
  have hsq : |α ^ 2| < 1 := by
    rw [abs_pow]
    nlinarith [abs_nonneg α]
  have hpow : Tendsto (fun n : ℕ => α ^ (2 * n)) atTop (nhds (0 : ℝ)) := by
    have h := tendsto_pow_atTop_nhds_zero_of_abs_lt_one hsq
    simpa only [pow_mul] using h
  have harg :
      Tendsto (fun n : ℕ => c * (α ^ (2 * n) - 1)) atTop
        (nhds (c * (0 - 1))) :=
    tendsto_const_nhds.mul (hpow.sub tendsto_const_nhds)
  have hcpos : 0 < c * (0 - 1) := by
    dsimp [c]
    have hnum : 0 < α + 1 := by linarith
    have hden : α - 1 < 0 := by linarith
    exact mul_pos_of_neg_of_neg (div_neg_of_pos_of_neg hnum hden) (by norm_num)
  have hlog :
      Tendsto (fun n : ℕ => Real.log (c * (α ^ (2 * n) - 1))) atTop
        (nhds (Real.log (c * (0 - 1)))) :=
    (Real.continuousAt_log (ne_of_gt hcpos)).tendsto.comp harg
  have hscale :
      Tendsto (fun n : ℕ => Real.pi / (n : ℝ)) atTop (nhds (0 : ℝ)) :=
    tendsto_const_div_atTop_nhds_zero_nat Real.pi
  have hproduct :
      Tendsto
        (fun n : ℕ =>
          (Real.pi / (n : ℝ)) * Real.log (c * (α ^ (2 * n) - 1)))
        atTop (nhds (0 : ℝ)) := by
    convert hscale.mul hlog using 1 <;> simp
  apply hproduct.congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  rw [gap10 α n hn hαne]

theorem gap12 (α : ℝ) (hα : |α| < 1) :
    (∫ x in (0 : ℝ)..Real.pi, Real.log (factor α x)) = 0 := by
  rw [integral_log_factor_formula]
  rw [(Real.posLog_eq_zero_iff |α|).2]
  · ring
  · simpa [abs_of_nonneg (abs_nonneg α)] using le_of_lt hα

theorem gap13 (α : ℝ) (n : ℕ) (hn : 0 < n) (hα : 1 < |α|) :
    S α n =
      2 * Real.pi * Real.log |α| +
        (Real.pi / n) *
          Real.log (((α + 1) / (α - 1)) *
            ((α ^ (2 * n) - 1) / α ^ (2 * n))) := by
  have hα0 : α ≠ 0 := by
    exact abs_ne_zero.mp (ne_of_gt (lt_trans zero_lt_one hα))
  have hα1 : α ≠ 1 := by
    intro h
    subst α
    norm_num at hα
  have hαneg1 : α ≠ -1 := by
    intro h
    subst α
    norm_num at hα
  have hαplus : α + 1 ≠ 0 := by
    intro h
    apply hαneg1
    linarith
  have hαne : |α| ≠ 1 := ne_of_gt hα
  have hA0 : α ^ (2 * n) ≠ 0 := pow_ne_zero _ hα0
  have hApos : 0 < α ^ (2 * n) := by
    rw [show 2 * n = n * 2 by omega, pow_mul]
    exact sq_pos_of_ne_zero (pow_ne_zero n hα0)
  have hAgt : 1 < α ^ (2 * n) := by
    have habs : 1 < |α ^ (2 * n)| := by
      rw [abs_pow]
      exact one_lt_pow₀ hα (by omega)
    simpa [abs_of_pos hApos] using habs
  have hB0 :
      ((α + 1) / (α - 1)) *
          ((α ^ (2 * n) - 1) / α ^ (2 * n)) ≠ 0 := by
    apply mul_ne_zero
    · exact div_ne_zero hαplus (sub_ne_zero.mpr hα1)
    · exact div_ne_zero (sub_ne_zero.mpr (ne_of_gt hAgt)) hA0
  have hfactor :
      ((α + 1) / (α - 1)) * (α ^ (2 * n) - 1) =
        α ^ (2 * n) *
          (((α + 1) / (α - 1)) *
            ((α ^ (2 * n) - 1) / α ^ (2 * n))) := by
    field_simp [hA0]
  rw [gap10 α n hn hαne, hfactor, Real.log_mul hA0 hB0,
    Real.log_pow, ← Real.log_abs α]
  have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  push_cast
  field_simp [hnR]

theorem gap14 (α : ℝ) (hα : 1 < |α|) :
    Tendsto (fun n : ℕ => (α ^ (2 * n) - 1) / α ^ (2 * n))
      atTop (nhds (1 : ℝ)) := by
  have hαpos : 0 < |α| := lt_trans zero_lt_one hα
  have hα0 : α ≠ 0 := abs_pos.mp hαpos
  let q : ℝ := (α⁻¹) ^ 2
  have hinvpos : 0 < |α|⁻¹ := inv_pos.mpr hαpos
  have hinvlt : |α|⁻¹ < 1 := (inv_lt_one₀ hαpos).2 hα
  have hqabs : |q| < 1 := by
    dsimp [q]
    rw [abs_of_nonneg (sq_nonneg _), ← sq_abs (α⁻¹), abs_inv]
    nlinarith
  have hq : Tendsto (fun n : ℕ => q ^ n) atTop (nhds (0 : ℝ)) :=
    tendsto_pow_atTop_nhds_zero_of_abs_lt_one hqabs
  have hlimit :
      Tendsto (fun n : ℕ => (1 : ℝ) - q ^ n) atTop
        (nhds ((1 : ℝ) - 0)) :=
    tendsto_const_nhds.sub hq
  convert hlimit using 1
  · funext n
    have hpow : α ^ (2 * n) ≠ 0 := pow_ne_zero _ hα0
    have hqpow : q ^ n = (α ^ (2 * n))⁻¹ := by
      dsimp [q]
      rw [← pow_mul, inv_pow]
    rw [hqpow]
    field_simp [hpow]
  · ring

theorem gap15 (α : ℝ) (hα : 1 < |α|) :
    Tendsto (S α) atTop (nhds (2 * Real.pi * Real.log |α|)) := by
  let c : ℝ := (α + 1) / (α - 1)
  have hcpos : 0 < c := by
    by_cases hnonneg : 0 ≤ α
    · have hgt : 1 < α := by simpa [abs_of_nonneg hnonneg] using hα
      dsimp [c]
      exact div_pos (by linarith) (by linarith)
    · have hneg : α < 0 := lt_of_not_ge hnonneg
      have hlt : α < -1 := by
        have : 1 < -α := by simpa [abs_of_neg hneg] using hα
        linarith
      dsimp [c]
      exact div_pos_of_neg_of_neg (by linarith) (by linarith)
  have harg :
      Tendsto
        (fun n : ℕ =>
          c * ((α ^ (2 * n) - 1) / α ^ (2 * n)))
        atTop (nhds c) := by
    convert tendsto_const_nhds.mul (gap14 α hα) using 1 <;> simp
  have hlog :
      Tendsto
        (fun n : ℕ =>
          Real.log (c * ((α ^ (2 * n) - 1) / α ^ (2 * n))))
        atTop (nhds (Real.log c)) :=
    (Real.continuousAt_log (ne_of_gt hcpos)).tendsto.comp harg
  have hscale :
      Tendsto (fun n : ℕ => Real.pi / (n : ℝ)) atTop (nhds (0 : ℝ)) :=
    tendsto_const_div_atTop_nhds_zero_nat Real.pi
  have hresidual :
      Tendsto
        (fun n : ℕ =>
          (Real.pi / (n : ℝ)) *
            Real.log (c * ((α ^ (2 * n) - 1) / α ^ (2 * n))))
        atTop (nhds (0 : ℝ)) := by
    convert hscale.mul hlog using 1 <;> simp
  have htotal :
      Tendsto
        (fun n : ℕ =>
          2 * Real.pi * Real.log |α| +
            (Real.pi / (n : ℝ)) *
              Real.log (c * ((α ^ (2 * n) - 1) / α ^ (2 * n))))
        atTop (nhds (2 * Real.pi * Real.log |α|)) := by
    convert tendsto_const_nhds.add hresidual using 1 <;> simp
  apply htotal.congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  rw [gap13 α n hn hα]

theorem gap16 (α : ℝ) (hα : 1 < |α|) :
    (∫ x in (0 : ℝ)..Real.pi, Real.log (factor α x)) =
      2 * Real.pi * Real.log |α| := by
  rw [integral_log_factor_formula,
    Real.posLog_eq_log (by simpa using le_of_lt hα)]

end
end ProofGap.Exercise2192
