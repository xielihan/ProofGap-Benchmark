import ProofGapLean.Prelude.Analysis
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

open scoped Interval

namespace ProofGap.Exercise2541

noncomputable section

def integrand (x : ℝ) : ℝ := Real.exp (x ^ 2)
def fourthDerivative (x : ℝ) : ℝ :=
  2 * Real.exp (x ^ 2) * (8 * x ^ 4 + 24 * x ^ 2 + 6)
def mesh (i : ℕ) : ℝ := i / 6
def sample (i : ℕ) : ℝ := integrand (mesh i)
def integralValue : ℝ := ∫ x in (0 : ℝ)..1, integrand x
def simpsonApprox : ℝ :=
  1 / 18 * (sample 0 + sample 6 +
    4 * (sample 1 + sample 3 + sample 5) +
    2 * (sample 2 + sample 4))
def remainder : ℝ := integralValue - simpsonApprox

private def expPoly (A x : ℝ) : ℝ :=
  1 + x ^ 2 + x ^ 4 / 2 + x ^ 6 / 6 + x ^ 8 / 24 +
    x ^ 10 / 120 + x ^ 12 / 720 + x ^ 14 / 5040 + A * x ^ 16

private theorem hasDerivAt_weighted_expPoly (A x : ℝ) :
    HasDerivAt (fun y : ℝ => Real.exp (-(y ^ 2)) * expPoly A y)
      (Real.exp (-(x ^ 2)) * x ^ 15 *
        (16 * A - 1 / 2520 - 2 * A * x ^ 2)) x := by
  have h2 : HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by
    convert ((hasDerivAt_id x).mul (hasDerivAt_id x)) using 1 <;>
      (try funext y) <;> dsimp <;> ring
  have h4 : HasDerivAt (fun y : ℝ => y ^ 4) (4 * x ^ 3) x := by
    convert (h2.mul h2) using 1 <;>
      (try funext y) <;> dsimp <;> ring
  have h6 : HasDerivAt (fun y : ℝ => y ^ 6) (6 * x ^ 5) x := by
    convert (h4.mul h2) using 1 <;>
      (try funext y) <;> dsimp <;> ring
  have h8 : HasDerivAt (fun y : ℝ => y ^ 8) (8 * x ^ 7) x := by
    convert (h4.mul h4) using 1 <;>
      (try funext y) <;> dsimp <;> ring
  have h10 : HasDerivAt (fun y : ℝ => y ^ 10) (10 * x ^ 9) x := by
    convert (h8.mul h2) using 1 <;>
      (try funext y) <;> dsimp <;> ring
  have h12 : HasDerivAt (fun y : ℝ => y ^ 12) (12 * x ^ 11) x := by
    convert (h6.mul h6) using 1 <;>
      (try funext y) <;> dsimp <;> ring
  have h14 : HasDerivAt (fun y : ℝ => y ^ 14) (14 * x ^ 13) x := by
    convert (h12.mul h2) using 1 <;>
      (try funext y) <;> dsimp <;> ring
  have h16 : HasDerivAt (fun y : ℝ => y ^ 16) (16 * x ^ 15) x := by
    convert (h8.mul h8) using 1 <;>
      (try funext y) <;> dsimp <;> ring
  have hp :=
    ((((((((hasDerivAt_const x (1 : ℝ)).add h2).add
      (h4.div_const 2)).add
      (h6.div_const 6)).add
      (h8.div_const 24)).add
      (h10.div_const 120)).add
      (h12.div_const 720)).add
      (h14.div_const 5040)).add
      ((hasDerivAt_const x A).mul h16)
  have he :=
    (Real.hasDerivAt_exp (-(x ^ 2))).comp x (h2.neg)
  convert (he.mul hp) using 1 <;>
    (try funext y) <;>
    dsimp [Function.comp_def, expPoly] <;> ring

private theorem exp_sq_poly_bounds (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    expPoly 0 x ≤ Real.exp (x ^ 2) ∧
      Real.exp (x ^ 2) ≤ expPoly (1 / 35000) x := by
  have huMono : StrictMonoOn
      (fun y : ℝ => Real.exp (-(y ^ 2)) * expPoly (1 / 35000) y)
      (Set.Icc (0 : ℝ) 1) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc (0 : ℝ) 1)
    · dsimp [expPoly]
      fun_prop
    · intro y hy
      have hy' : y ∈ Set.Ioo (0 : ℝ) 1 := by simpa using hy
      rw [(hasDerivAt_weighted_expPoly (1 / 35000) y).deriv]
      have hy2 : y ^ 2 < 1 := by
        nlinarith [mul_pos hy'.1 (sub_pos.mpr hy'.2)]
      have hf : 0 < 16 * (1 / 35000 : ℝ) - 1 / 2520 -
          2 * (1 / 35000 : ℝ) * y ^ 2 := by
        norm_num
        nlinarith
      exact mul_pos
        (mul_pos (Real.exp_pos (-(y ^ 2))) (pow_pos hy'.1 15)) hf
  have hlMono : StrictMonoOn
      (fun y : ℝ => -(Real.exp (-(y ^ 2)) * expPoly 0 y))
      (Set.Icc (0 : ℝ) 1) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc (0 : ℝ) 1)
    · dsimp [expPoly]
      fun_prop
    · intro y hy
      have hy' : y ∈ Set.Ioo (0 : ℝ) 1 := by simpa using hy
      have hd : HasDerivAt
          (fun z : ℝ => -(Real.exp (-(z ^ 2)) * expPoly 0 z))
          (Real.exp (-(y ^ 2)) * y ^ 15 / 2520) y := by
        convert (hasDerivAt_weighted_expPoly 0 y).neg using 1 <;>
          norm_num <;> ring
      rw [hd.deriv]
      exact div_pos
        (mul_pos (Real.exp_pos (-(y ^ 2))) (pow_pos hy'.1 15))
        (by norm_num)
  by_cases hx0 : x = 0
  · subst x
    norm_num [expPoly]
  · have hxpos : 0 < x := lt_of_le_of_ne hx.1 (Ne.symm hx0)
    have h0mem : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by norm_num
    have hu := huMono h0mem hx hxpos
    have hl := hlMono h0mem hx hxpos
    have hu' : 1 < Real.exp (-(x ^ 2)) * expPoly (1 / 35000) x := by
      simpa [expPoly] using hu
    have hl' : Real.exp (-(x ^ 2)) * expPoly 0 x < 1 := by
      have h := neg_lt_neg_iff.mp hl
      simpa [expPoly] using h
    have hid : Real.exp (-(x ^ 2)) * Real.exp (x ^ 2) = 1 := by
      calc
        Real.exp (-(x ^ 2)) * Real.exp (x ^ 2) =
            Real.exp (-(x ^ 2) + x ^ 2) :=
          (Real.exp_add (-(x ^ 2)) (x ^ 2)).symm
        _ = Real.exp 0 := congrArg Real.exp (by ring)
        _ = 1 := Real.exp_zero
    have hcancel (p : ℝ) :
        (Real.exp (-(x ^ 2)) * p) * Real.exp (x ^ 2) = p := by
      calc
        (Real.exp (-(x ^ 2)) * p) * Real.exp (x ^ 2) =
            p * (Real.exp (-(x ^ 2)) * Real.exp (x ^ 2)) := by ring
        _ = p := by rw [hid, mul_one]
    constructor
    · have hm := mul_le_mul_of_nonneg_right (le_of_lt hl')
        (le_of_lt (Real.exp_pos (x ^ 2)))
      calc
        expPoly 0 x =
            (Real.exp (-(x ^ 2)) * expPoly 0 x) * Real.exp (x ^ 2) :=
          (hcancel (expPoly 0 x)).symm
        _ ≤ 1 * Real.exp (x ^ 2) := hm
        _ = Real.exp (x ^ 2) := one_mul _
    · have hm := mul_le_mul_of_nonneg_right (le_of_lt hu')
        (le_of_lt (Real.exp_pos (x ^ 2)))
      calc
        Real.exp (x ^ 2) = 1 * Real.exp (x ^ 2) := (one_mul _).symm
        _ ≤ (Real.exp (-(x ^ 2)) * expPoly (1 / 35000) x) *
            Real.exp (x ^ 2) := hm
        _ = expPoly (1 / 35000) x := hcancel (expPoly (1 / 35000) x)

private theorem exp_one_bounds :
    (2.7182 : ℝ) < Real.exp 1 ∧ Real.exp 1 < (2.7184 : ℝ) := by
  have h := exp_sq_poly_bounds 1 (by norm_num)
  constructor
  · calc
      (2.7182 : ℝ) < expPoly 0 1 := by norm_num [expPoly]
      _ ≤ Real.exp (1 ^ 2) := h.1
      _ = Real.exp 1 := by norm_num
  · calc
      Real.exp 1 = Real.exp (1 ^ 2) := by norm_num
      _ ≤ expPoly (1 / 35000) 1 := h.2
      _ < (2.7184 : ℝ) := by norm_num [expPoly]

private theorem exp_rational_bounds
    (p q : ℕ) (hp : 0 < p) (hq : 0 < q)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hl : a ^ q < (2.7182 : ℝ) ^ p)
    (hu : (2.7184 : ℝ) ^ p < b ^ q) :
    a < Real.exp ((p : ℝ) / q) ∧ Real.exp ((p : ℝ) / q) < b := by
  have helo := exp_one_bounds.1
  have hehi := exp_one_bounds.2
  have hid :
      (Real.exp ((p : ℝ) / q)) ^ q = (Real.exp 1) ^ p := by
    rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]
    congr 1
    field_simp [Nat.ne_of_gt hq]
  have hq_ne : q ≠ 0 := Nat.ne_of_gt hq
  have helo_pow : (2.7182 : ℝ) ^ p < (Real.exp 1) ^ p := by
    gcongr
  have hehi_pow : (Real.exp 1) ^ p < (2.7184 : ℝ) ^ p := by
    gcongr
  have hlo_pow : a ^ q < (Real.exp ((p : ℝ) / q)) ^ q := by
    rw [hid]
    exact lt_trans hl helo_pow
  have hup_pow : (Real.exp ((p : ℝ) / q)) ^ q < b ^ q := by
    rw [hid]
    exact lt_trans hehi_pow hu
  constructor
  · exact (pow_lt_pow_iff_left₀ ha (le_of_lt (Real.exp_pos _)) hq_ne).mp hlo_pow
  · exact (pow_lt_pow_iff_left₀ (le_of_lt (Real.exp_pos _)) hb hq_ne).mp hup_pow

private def expPolyAnti (A x : ℝ) : ℝ :=
  x + x ^ 3 / 3 + x ^ 5 / 10 + x ^ 7 / 42 + x ^ 9 / 216 +
    x ^ 11 / 1320 + x ^ 13 / 9360 + x ^ 15 / 75600 +
      A * x ^ 17 / 17

private theorem hasDerivAt_expPolyAnti (A x : ℝ) :
    HasDerivAt (expPolyAnti A) (expPoly A x) x := by
  have h2 : HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by
    convert ((hasDerivAt_id x).mul (hasDerivAt_id x)) using 1 <;>
      (try funext y) <;> dsimp <;> ring
  have h3 : HasDerivAt (fun y : ℝ => y ^ 3) (3 * x ^ 2) x := by
    convert (h2.mul (hasDerivAt_id x)) using 1 <;>
      (try funext y) <;> dsimp <;> ring
  have h5 : HasDerivAt (fun y : ℝ => y ^ 5) (5 * x ^ 4) x := by
    convert (h3.mul h2) using 1 <;>
      (try funext y) <;> dsimp <;> ring
  have h7 : HasDerivAt (fun y : ℝ => y ^ 7) (7 * x ^ 6) x := by
    convert (h5.mul h2) using 1 <;>
      (try funext y) <;> dsimp <;> ring
  have h9 : HasDerivAt (fun y : ℝ => y ^ 9) (9 * x ^ 8) x := by
    convert (h7.mul h2) using 1 <;>
      (try funext y) <;> dsimp <;> ring
  have h11 : HasDerivAt (fun y : ℝ => y ^ 11) (11 * x ^ 10) x := by
    convert (h9.mul h2) using 1 <;>
      (try funext y) <;> dsimp <;> ring
  have h13 : HasDerivAt (fun y : ℝ => y ^ 13) (13 * x ^ 12) x := by
    convert (h11.mul h2) using 1 <;>
      (try funext y) <;> dsimp <;> ring
  have h15 : HasDerivAt (fun y : ℝ => y ^ 15) (15 * x ^ 14) x := by
    convert (h13.mul h2) using 1 <;>
      (try funext y) <;> dsimp <;> ring
  have h17 : HasDerivAt (fun y : ℝ => y ^ 17) (17 * x ^ 16) x := by
    convert (h15.mul h2) using 1 <;>
      (try funext y) <;> dsimp <;> ring
  have h :=
    ((((((((hasDerivAt_id x).add
      (h3.div_const 3)).add
      (h5.div_const 10)).add
      (h7.div_const 42)).add
      (h9.div_const 216)).add
      (h11.div_const 1320)).add
      (h13.div_const 9360)).add
      (h15.div_const 75600)).add
      (((hasDerivAt_const x A).mul h17).div_const 17)
  convert h using 1 <;>
    (try funext y) <;>
    dsimp [expPolyAnti, expPoly] <;> ring

private theorem integral_expPoly_unit (A : ℝ) :
    (∫ x in (0 : ℝ)..1, expPoly A x) =
      expPolyAnti A 1 - expPolyAnti A 0 := by
  have hc : Continuous (expPoly A) := by
    unfold expPoly
    fun_prop
  have hca : Continuous (expPolyAnti A) := by
    unfold expPolyAnti
    fun_prop
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  all_goals
    first
    | exact hc.continuousOn
    | exact hca.continuousOn
    | exact hc.intervalIntegrable 0 1
    | intro y hy
      exact hasDerivAt_expPolyAnti A y
    | intro y hy
      exact (hasDerivAt_expPolyAnti A y).hasDerivWithinAt
    | intro y
      exact hasDerivAt_expPolyAnti A y
    | intro y
      exact (hasDerivAt_expPolyAnti A y).hasDerivWithinAt
    | norm_num

private theorem integral_exp_sq_bounds :
    (1.4626 : ℝ) < integralValue ∧ integralValue < (1.4627 : ℝ) := by
  have hp_cont0 : Continuous (expPoly 0) := by
    unfold expPoly
    fun_prop
  have hp_cont1 : Continuous (expPoly (1 / 35000)) := by
    unfold expPoly
    fun_prop
  have he_cont : Continuous (fun x : ℝ => Real.exp (x ^ 2)) := by
    fun_prop
  have hlpoint : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      expPoly 0 x ≤ Real.exp (x ^ 2) := by
    intro x hx
    exact (exp_sq_poly_bounds x hx).1
  have hupoint : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      Real.exp (x ^ 2) ≤ expPoly (1 / 35000) x := by
    intro x hx
    exact (exp_sq_poly_bounds x hx).2
  have hlmono :
      (∫ x in (0 : ℝ)..1, expPoly 0 x) ≤
        (∫ x in (0 : ℝ)..1, Real.exp (x ^ 2)) :=
    intervalIntegral.integral_mono_on
      (a := (0 : ℝ)) (b := 1) (f := expPoly 0)
      (g := fun x : ℝ => Real.exp (x ^ 2)) (by norm_num)
      (hp_cont0.intervalIntegrable 0 1) (he_cont.intervalIntegrable 0 1) hlpoint
  have humono :
      (∫ x in (0 : ℝ)..1, Real.exp (x ^ 2)) ≤
        (∫ x in (0 : ℝ)..1, expPoly (1 / 35000) x) :=
    intervalIntegral.integral_mono_on
      (a := (0 : ℝ)) (b := 1) (f := fun x : ℝ => Real.exp (x ^ 2))
      (g := expPoly (1 / 35000)) (by norm_num)
      (he_cont.intervalIntegrable 0 1) (hp_cont1.intervalIntegrable 0 1) hupoint
  have hlcalc : (1.4626 : ℝ) < ∫ x in (0 : ℝ)..1, expPoly 0 x := by
    rw [integral_expPoly_unit 0]
    norm_num [expPolyAnti]
  have hucalc : (∫ x in (0 : ℝ)..1, expPoly (1 / 35000) x) <
      (1.4627 : ℝ) := by
    rw [integral_expPoly_unit (1 / 35000)]
    norm_num [expPolyAnti]
  constructor
  · change (1.4626 : ℝ) < ∫ x in (0 : ℝ)..1, Real.exp (x ^ 2)
    exact lt_of_lt_of_le hlcalc hlmono
  · change (∫ x in (0 : ℝ)..1, Real.exp (x ^ 2)) < (1.4627 : ℝ)
    exact lt_of_le_of_lt humono hucalc

private theorem simpson_exp_sq_remainder :
    ∃ ξ ∈ Set.Ioo (0 : ℝ) 1,
      remainder = -(1 / (180 * 6 ^ 4) : ℝ) * fourthDerivative ξ := by
  have h1 := exp_rational_bounds 1 36 (by norm_num) (by norm_num)
    (1.0281 : ℝ) 1.0283 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  have h2 := exp_rational_bounds 1 9 (by norm_num) (by norm_num)
    (1.1174 : ℝ) 1.1176 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  have h3 := exp_rational_bounds 1 4 (by norm_num) (by norm_num)
    (1.2839 : ℝ) 1.2841 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  have h4 := exp_rational_bounds 4 9 (by norm_num) (by norm_num)
    (1.5595 : ℝ) 1.5597 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  have h5 := exp_rational_bounds 25 36 (by norm_num) (by norm_num)
    (2.0025 : ℝ) 2.0027 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  have h6 := exp_one_bounds
  have hs : (1.46276 : ℝ) < simpsonApprox ∧
      simpsonApprox < (1.463 : ℝ) := by
    unfold simpsonApprox sample mesh integrand
    norm_num at h1 h2 h3 h4 h5 h6 ⊢
    constructor <;> linarith
  have hi := integral_exp_sq_bounds
  have hrlo : (-1 / 2000 : ℝ) < remainder := by
    unfold remainder
    nlinarith [hi.1, hs.2]
  have hrhi : remainder < (-3 / 50000 : ℝ) := by
    unfold remainder
    nlinarith [hi.2, hs.1]
  let c : ℝ := -remainder * (180 * 6 ^ 4)
  have hc0 : fourthDerivative 0 < c := by
    norm_num [fourthDerivative, c]
    norm_num at hrhi
    nlinarith
  have hc1 : c < fourthDerivative 1 := by
    have he := exp_one_bounds.1
    norm_num [fourthDerivative, c]
    norm_num at hrlo he
    nlinarith
  have hcont : Continuous fourthDerivative := by
    unfold fourthDerivative
    fun_prop
  have hc : c ∈ Set.Icc (fourthDerivative 0) (fourthDerivative 1) :=
    ⟨le_of_lt hc0, le_of_lt hc1⟩
  rcases intermediate_value_Icc (f := fourthDerivative) (a := (0 : ℝ))
      (b := 1) (by norm_num) hcont.continuousOn hc with ⟨ξ, hξ, hval⟩
  have hξ0 : 0 < ξ := by
    apply lt_of_le_of_ne hξ.1
    intro heq
    have hz : fourthDerivative 0 = c := by
      simpa [heq] using hval
    linarith
  have hξ1 : ξ < 1 := by
    apply lt_of_le_of_ne hξ.2
    intro heq
    have hz : fourthDerivative 1 = c := by
      simpa [heq] using hval
    linarith
  refine ⟨ξ, ⟨hξ0, hξ1⟩, ?_⟩
  rw [hval]
  dsimp [c]
  ring

theorem gap1 :
    ∃ ξ ∈ Set.Ioo (0 : ℝ) 1,
      remainder = -(1 / (180 * 6 ^ 4) : ℝ) * fourthDerivative ξ := by
  exact simpson_exp_sq_remainder
theorem gap2 :
    |remainder| < (2 * 38 * Real.exp 1) / (180 * 6 ^ 4) := by
  rcases gap1 with ⟨ξ, hξ, hr⟩
  have hx2_nonneg : 0 ≤ ξ ^ 2 := sq_nonneg ξ
  have hx2_lt : ξ ^ 2 < 1 := by
    nlinarith [mul_pos hξ.1 (sub_pos.mpr hξ.2)]
  have hx4_nonneg : 0 ≤ ξ ^ 4 := by positivity
  have hx4_lt : ξ ^ 4 < 1 := by
    nlinarith [sq_nonneg (ξ ^ 2 - 1)]
  have hp_pos : 0 < 8 * ξ ^ 4 + 24 * ξ ^ 2 + 6 := by nlinarith
  have hp_lt : 8 * ξ ^ 4 + 24 * ξ ^ 2 + 6 < 38 := by nlinarith
  have he_lt : Real.exp (ξ ^ 2) < Real.exp 1 :=
    Real.exp_lt_exp.mpr hx2_lt
  have hprod :
      Real.exp (ξ ^ 2) * (8 * ξ ^ 4 + 24 * ξ ^ 2 + 6) <
        Real.exp 1 * 38 := by
    calc
      Real.exp (ξ ^ 2) * (8 * ξ ^ 4 + 24 * ξ ^ 2 + 6) <
          Real.exp 1 * (8 * ξ ^ 4 + 24 * ξ ^ 2 + 6) :=
        mul_lt_mul_of_pos_right he_lt hp_pos
      _ < Real.exp 1 * 38 :=
        mul_lt_mul_of_pos_left hp_lt (Real.exp_pos 1)
  rw [hr]
  have hfd_pos : 0 < fourthDerivative ξ := by
    unfold fourthDerivative
    positivity
  rw [abs_mul, abs_neg, abs_of_pos hfd_pos]
  norm_num [fourthDerivative]
  nlinarith
theorem gap3 :
    (2 * 38 * Real.exp 1) / (180 * 6 ^ 4) < 10 ^ (-3 : ℤ) →
      |remainder| < 10 ^ (-3 : ℤ) := by
  intro h
  exact lt_trans gap2 h
theorem gap4 :
    (2 * 38 * Real.exp 1) / (180 * 6 ^ 4) < 10 ^ (-3 : ℤ) := by
  have he := exp_one_bounds.2
  norm_num at he ⊢
  nlinarith
theorem gap5 : |remainder| < 10 ^ (-3 : ℤ) := by
  exact gap3 gap4
theorem gap6 : mesh 0 = 0 := by
  norm_num [mesh]
theorem gap7 : sample 0 = 1 := by
  norm_num [sample, integrand, mesh]
theorem gap8 : mesh 1 = 1 / 6 := by
  norm_num [mesh]
theorem gap9 : sample 1 = Real.exp (1 / 36) := by
  norm_num [sample, integrand, mesh]
theorem gap10 : |Real.exp (1 / 36) - 1.0282| < 0.0001 := by
  have h := exp_rational_bounds 1 36 (by norm_num) (by norm_num)
    (1.0281 : ℝ) 1.0283 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  rw [abs_lt]
  constructor <;> nlinarith [h.1, h.2]
theorem gap11 : mesh 2 = 1 / 3 := by
  norm_num [mesh]
theorem gap12 : sample 2 = Real.exp (1 / 9) := by
  norm_num [sample, integrand, mesh]
theorem gap13 : |Real.exp (1 / 9) - 1.1175| < 0.0001 := by
  have h := exp_rational_bounds 1 9 (by norm_num) (by norm_num)
    (1.1174 : ℝ) 1.1176 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  rw [abs_lt]
  constructor <;> nlinarith [h.1, h.2]
theorem gap14 : mesh 3 = 1 / 2 := by
  norm_num [mesh]
theorem gap15 : sample 3 = Real.exp (1 / 4) := by
  norm_num [sample, integrand, mesh]
theorem gap16 : |Real.exp (1 / 4) - 1.2840| < 0.0001 := by
  have h := exp_rational_bounds 1 4 (by norm_num) (by norm_num)
    (1.2839 : ℝ) 1.2841 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  rw [abs_lt]
  constructor <;> nlinarith [h.1, h.2]
theorem gap17 : mesh 4 = 2 / 3 := by
  norm_num [mesh]
theorem gap18 : sample 4 = Real.exp (4 / 9) := by
  norm_num [sample, integrand, mesh]
theorem gap19 : |Real.exp (4 / 9) - 1.5596| < 0.0001 := by
  have h := exp_rational_bounds 4 9 (by norm_num) (by norm_num)
    (1.5595 : ℝ) 1.5597 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  rw [abs_lt]
  constructor <;> nlinarith [h.1, h.2]
theorem gap20 : mesh 5 = 5 / 6 := by
  norm_num [mesh]
theorem gap21 : sample 5 = Real.exp (25 / 36) := by
  norm_num [sample, integrand, mesh]
theorem gap22 : |Real.exp (25 / 36) - 2.0026| < 0.0001 := by
  have h := exp_rational_bounds 25 36 (by norm_num) (by norm_num)
    (2.0025 : ℝ) 2.0027 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  rw [abs_lt]
  constructor <;> nlinarith [h.1, h.2]
theorem gap23 : mesh 6 = 1 := by
  norm_num [mesh]
theorem gap24 : sample 6 = Real.exp 1 := by
  norm_num [sample, integrand, mesh]
theorem gap25 : |Real.exp 1 - 2.7183| < 0.0001 := by
  have hlo := exp_one_bounds.1
  have hup := exp_one_bounds.2
  rw [abs_lt]
  norm_num at hlo hup ⊢
  constructor <;> nlinarith
theorem gap26 :
    |integralValue - simpsonApprox| < 0.001 := by
  have h := gap5
  unfold remainder at h
  norm_num at h ⊢
  exact h
theorem gap27 : |simpsonApprox - 1.463| < 0.001 := by
  have h1 := abs_lt.mp gap10
  have h2 := abs_lt.mp gap13
  have h3 := abs_lt.mp gap16
  have h4 := abs_lt.mp gap19
  have h5 := abs_lt.mp gap22
  have h6 := abs_lt.mp gap25
  rw [abs_lt]
  simp only [simpsonApprox, gap7, gap9, gap12, gap15, gap18, gap21, gap24]
  constructor <;> norm_num at * <;> linarith
theorem gap28 : |integralValue - 1.463| < 0.001 := by
  have hlower : (1.462 : ℝ) < integralValue := by
    nlinarith [integral_exp_sq_bounds.1]
  have hs := abs_lt.mp gap27
  have hrneg : remainder < 0 := by
    rcases gap1 with ⟨ξ, hξ, hr⟩
    rw [hr]
    have hfd : 0 < fourthDerivative ξ := by
      unfold fourthDerivative
      positivity
    norm_num
    positivity
  have hi_lt : integralValue < simpsonApprox := by
    unfold remainder at hrneg
    linarith
  rw [abs_lt]
  norm_num at hs ⊢
  constructor
  · nlinarith [hlower]
  · nlinarith [hi_lt, hs.2]

end

end ProofGap.Exercise2541
