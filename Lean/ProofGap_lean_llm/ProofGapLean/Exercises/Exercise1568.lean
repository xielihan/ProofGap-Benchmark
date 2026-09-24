import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum

namespace ProofGap.Exercise1568

noncomputable section

def height (R x : ℝ) : ℝ := Real.sqrt (R ^ 2 - 2 * x ^ 2)
def volume (R x : ℝ) : ℝ := 4 * x ^ 2 * height R x
def optimum (R : ℝ) : ℝ := R / Real.sqrt 3

def Feasible (R x y : ℝ) : Prop :=
  0 < x ∧ 0 < y ∧ 2 * x ^ 2 + y ^ 2 = R ^ 2

def IsOptimal (R x y : ℝ) : Prop :=
  Feasible R x y ∧ ∀ x₁ y₁, Feasible R x₁ y₁ →
    4 * x₁ ^ 2 * y₁ ≤ 4 * x ^ 2 * y

private theorem positive_real_eq_of_sq_eq {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hsq : a ^ 2 = b ^ 2) : a = b := by
  have h := congrArg Real.sqrt hsq
  simpa [Real.sqrt_sq_eq_abs, abs_of_pos ha, abs_of_pos hb] using h

private theorem optimum_feasible (R : ℝ) (hR : 0 < R) :
    Feasible R (optimum R) (optimum R) := by
  have hspos : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  have hssq : (Real.sqrt 3) ^ 2 = (3 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  have htpos : 0 < optimum R := by
    unfold optimum
    exact div_pos hR hspos
  have htsq : (optimum R) ^ 2 = R ^ 2 / 3 := by
    unfold optimum
    rw [div_pow, hssq]
  exact ⟨htpos, htpos, by nlinarith⟩

private theorem product_bound_and_eq
    (R x y : ℝ) (hR : 0 < R) (hx : 0 < x) (hy : 0 < y)
    (hcon : 2 * x ^ 2 + y ^ 2 = R ^ 2) :
    x ^ 2 * y ≤ (optimum R) ^ 3 ∧
      (x ^ 2 * y = (optimum R) ^ 3 → x = y) := by
  have hspos : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  have hssq : (Real.sqrt 3) ^ 2 = (3 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  have htpos : 0 < optimum R := by
    unfold optimum
    exact div_pos hR hspos
  have htsq : (optimum R) ^ 2 = R ^ 2 / 3 := by
    unfold optimum
    rw [div_pow, hssq]
  have htthree : 3 * (optimum R) ^ 2 = R ^ 2 := by
    nlinarith
  have ht6 : 27 * ((optimum R) ^ 3) ^ 2 = R ^ 6 := by
    calc
      27 * ((optimum R) ^ 3) ^ 2 =
          (3 * (optimum R) ^ 2) ^ 3 := by ring
      _ = (R ^ 2) ^ 3 := by rw [htthree]
      _ = R ^ 6 := by ring
  have hid :
      (2 * x ^ 2 + y ^ 2) ^ 3 - 27 * (x ^ 2 * y) ^ 2 =
        (x ^ 2 - y ^ 2) ^ 2 * (8 * x ^ 2 + y ^ 2) := by
    ring
  have hfactor_nonneg : 0 ≤ 8 * x ^ 2 + y ^ 2 := by
    nlinarith [sq_nonneg x, sq_nonneg y]
  have hnonneg :
      0 ≤ (x ^ 2 - y ^ 2) ^ 2 * (8 * x ^ 2 + y ^ 2) :=
    mul_nonneg (sq_nonneg _) hfactor_nonneg
  have hcube : (2 * x ^ 2 + y ^ 2) ^ 3 = R ^ 6 := by
    rw [hcon]
    ring
  have hbound : 27 * (x ^ 2 * y) ^ 2 ≤ R ^ 6 := by
    nlinarith [hid, hnonneg, hcube]
  have hpsq : (x ^ 2 * y) ^ 2 ≤ ((optimum R) ^ 3) ^ 2 := by
    nlinarith [hbound, ht6]
  have hp : 0 < x ^ 2 * y := mul_pos (pow_pos hx 2) hy
  have ht : 0 < (optimum R) ^ 3 := pow_pos htpos 3
  have hupper : x ^ 2 * y ≤ (optimum R) ^ 3 := by
    by_contra hn
    have hgt : (optimum R) ^ 3 < x ^ 2 * y := lt_of_not_ge hn
    have hsum : 0 < x ^ 2 * y + (optimum R) ^ 3 := add_pos hp ht
    have hdiff :
        0 < (x ^ 2 * y) ^ 2 - ((optimum R) ^ 3) ^ 2 := by
      rw [show (x ^ 2 * y) ^ 2 - ((optimum R) ^ 3) ^ 2 =
          (x ^ 2 * y - (optimum R) ^ 3) *
            (x ^ 2 * y + (optimum R) ^ 3) by ring]
      exact mul_pos (sub_pos.mpr hgt) hsum
    nlinarith
  refine ⟨hupper, ?_⟩
  intro heq
  have hid' := hid
  rw [heq] at hid'
  have hzero :
      (x ^ 2 - y ^ 2) ^ 2 * (8 * x ^ 2 + y ^ 2) = 0 := by
    nlinarith [hid', hcube, ht6]
  have hfactor_pos : 0 < 8 * x ^ 2 + y ^ 2 := by
    nlinarith [pow_pos hx 2, sq_nonneg y]
  have hsquare_zero : (x ^ 2 - y ^ 2) ^ 2 = 0 :=
    (mul_eq_zero.mp hzero).resolve_right (ne_of_gt hfactor_pos)
  have hsqxy : x ^ 2 = y ^ 2 := by
    nlinarith
  exact positive_real_eq_of_sq_eq hx hy hsqxy

theorem gap1 (R x y : ℝ) (hfeas : Feasible R x y) :
    y = height R x := by
  rcases hfeas with ⟨hx, hy, hcon⟩
  unfold height
  have hrad : R ^ 2 - 2 * x ^ 2 = y ^ 2 := by
    linarith
  rw [hrad, Real.sqrt_sq_eq_abs, abs_of_pos hy]

theorem gap2 (R x : ℝ) :
    volume R x = 4 * x ^ 2 * Real.sqrt (R ^ 2 - 2 * x ^ 2) := by
  rfl

theorem gap3 (R x : ℝ) (hx : 0 < x)
    (hrad : 0 < R ^ 2 - 2 * x ^ 2) :
    deriv (volume R) x =
      8 * x * (R ^ 2 - 3 * x ^ 2) /
        Real.sqrt (R ^ 2 - 2 * x ^ 2) := by
  unfold volume height
  have hsq : HasDerivAt (fun z : ℝ => z ^ 2) (2 * x) x := by
    convert (hasDerivAt_id x).pow 2 using 1 <;> norm_num <;> ring
  have hmul : HasDerivAt (fun z : ℝ => 2 * z ^ 2) (4 * x) x := by
    convert (hasDerivAt_const x (2 : ℝ)).mul hsq using 1 <;> ring
  have hg : HasDerivAt (fun z : ℝ => R ^ 2 - 2 * z ^ 2) (-4 * x) x := by
    simpa [Pi.sub_apply, neg_mul] using
      (hasDerivAt_const x (R ^ 2)).sub hmul
  have hp : HasDerivAt (fun z : ℝ => 4 * z ^ 2) (8 * x) x := by
    convert (hasDerivAt_const x (4 : ℝ)).mul hsq using 1 <;> ring
  have hsqrt := (Real.hasDerivAt_sqrt (ne_of_gt hrad)).comp x hg
  have hv := hp.mul hsqrt
  have hderiv :
      deriv (fun z : ℝ => 4 * z ^ 2 * Real.sqrt (R ^ 2 - 2 * z ^ 2)) x =
        8 * x * Real.sqrt (R ^ 2 - 2 * x ^ 2) +
          4 * x ^ 2 *
            (1 / (2 * Real.sqrt (R ^ 2 - 2 * x ^ 2)) * (-4 * x)) := by
    simpa [Function.comp_def] using hv.deriv
  rw [hderiv]
  have hspos : 0 < Real.sqrt (R ^ 2 - 2 * x ^ 2) := Real.sqrt_pos.2 hrad
  have hssq : (Real.sqrt (R ^ 2 - 2 * x ^ 2)) ^ 2 =
      R ^ 2 - 2 * x ^ 2 := Real.sq_sqrt (le_of_lt hrad)
  have hrel : (Real.sqrt (R ^ 2 - 2 * x ^ 2)) ^ 2 - x ^ 2 =
      R ^ 2 - 3 * x ^ 2 := by
    rw [hssq]
    ring
  rw [← hrel]
  field_simp [ne_of_gt hspos]
  ring

theorem gap4 (R x : ℝ) (hR : 0 < R) (hx : 0 < x)
    (hcrit : deriv (volume R) x = 0)
    (hrad : 0 < R ^ 2 - 2 * x ^ 2) :
    x = optimum R := by
  rw [gap3 R x hx hrad] at hcrit
  have hsqrtpos : 0 < Real.sqrt (R ^ 2 - 2 * x ^ 2) :=
    Real.sqrt_pos.2 hrad
  have hscaled := congrArg
    (fun z : ℝ => z * Real.sqrt (R ^ 2 - 2 * x ^ 2)) hcrit
  have hnum : 8 * x * (R ^ 2 - 3 * x ^ 2) = 0 := by
    simpa [ne_of_gt hsqrtpos] using hscaled
  have hquad : R ^ 2 - 3 * x ^ 2 = 0 :=
    (mul_eq_zero.mp hnum).resolve_left
      (mul_ne_zero (by norm_num) (ne_of_gt hx))
  have hspos : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  have hssq : (Real.sqrt 3) ^ 2 = (3 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  have hxsq : (x * Real.sqrt 3) ^ 2 = R ^ 2 := by
    calc
      (x * Real.sqrt 3) ^ 2 = x ^ 2 * (Real.sqrt 3) ^ 2 := by ring
      _ = x ^ 2 * 3 := by rw [hssq]
      _ = R ^ 2 := by nlinarith
  have hxmul : x * Real.sqrt 3 = R :=
    positive_real_eq_of_sq_eq (mul_pos hx hspos) hR hxsq
  unfold optimum
  exact (eq_div_iff (ne_of_gt hspos)).2 hxmul

theorem gap5 (R x y : ℝ) (hR : 0 < R) (hopt : IsOptimal R x y) :
    x = optimum R ∧ y = optimum R := by
  rcases hopt with ⟨⟨hx, hy, hcon⟩, hmax⟩
  have hcomp := hmax (optimum R) (optimum R) (optimum_feasible R hR)
  have hlower : (optimum R) ^ 3 ≤ x ^ 2 * y := by
    nlinarith
  have hbound := product_bound_and_eq R x y hR hx hy hcon
  have heqprod : x ^ 2 * y = (optimum R) ^ 3 :=
    le_antisymm hbound.1 hlower
  have hxy : x = y := hbound.2 heqprod
  have hspos : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  have hssq : (Real.sqrt 3) ^ 2 = (3 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  have hconx := hcon
  rw [← hxy] at hconx
  have hxthree : 3 * x ^ 2 = R ^ 2 := by
    nlinarith
  have hxsq : (x * Real.sqrt 3) ^ 2 = R ^ 2 := by
    calc
      (x * Real.sqrt 3) ^ 2 = x ^ 2 * (Real.sqrt 3) ^ 2 := by ring
      _ = x ^ 2 * 3 := by rw [hssq]
      _ = R ^ 2 := by nlinarith
  have hxmul : x * Real.sqrt 3 = R :=
    positive_real_eq_of_sq_eq (mul_pos hx hspos) hR hxsq
  have hxopt : x = optimum R := by
    unfold optimum
    exact (eq_div_iff (ne_of_gt hspos)).2 hxmul
  exact ⟨hxopt, hxy.symm.trans hxopt⟩

theorem gap6 (R : ℝ) (hR : 0 < R) :
    ∀ x ∈ Set.Ioo 0 (R / Real.sqrt 2),
      volume R x ≤ volume R (optimum R) := by
  intro x hxmem
  rcases hxmem with ⟨hx, hxupper⟩
  have hs2pos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hs2sq : (Real.sqrt 2) ^ 2 = (2 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  have hxmul : x * Real.sqrt 2 < R :=
    (lt_div_iff₀ hs2pos).mp hxupper
  have hmul : 0 < (R - x * Real.sqrt 2) * (R + x * Real.sqrt 2) :=
    mul_pos (sub_pos.mpr hxmul)
      (add_pos hR (mul_pos hx hs2pos))
  have hsq_lt : (x * Real.sqrt 2) ^ 2 < R ^ 2 := by
    nlinarith
  have hxsq : (x * Real.sqrt 2) ^ 2 = 2 * x ^ 2 := by
    calc
      (x * Real.sqrt 2) ^ 2 = x ^ 2 * (Real.sqrt 2) ^ 2 := by ring
      _ = 2 * x ^ 2 := by rw [hs2sq]; ring
  have hrad : 0 < R ^ 2 - 2 * x ^ 2 := by
    nlinarith
  let y : ℝ := height R x
  have hy : 0 < y := by
    dsimp [y, height]
    exact Real.sqrt_pos.2 hrad
  have hcon : 2 * x ^ 2 + y ^ 2 = R ^ 2 := by
    dsimp [y, height]
    rw [Real.sq_sqrt (le_of_lt hrad)]
    ring
  have hb := (product_bound_and_eq R x y hR hx hy hcon).1
  dsimp [y] at hb
  have hheight : height R (optimum R) = optimum R :=
    (gap1 R (optimum R) (optimum R) (optimum_feasible R hR)).symm
  unfold volume
  rw [hheight]
  nlinarith

theorem gap7 (R : ℝ) (hR : 0 < R) :
    volume R (optimum R) = 4 * R ^ 3 / (3 * Real.sqrt 3) := by
  have hheight : height R (optimum R) = optimum R :=
    (gap1 R (optimum R) (optimum R) (optimum_feasible R hR)).symm
  have hspos : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  have hssq : (Real.sqrt 3) ^ 2 = (3 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  have hscube : (Real.sqrt 3) ^ 3 = 3 * Real.sqrt 3 := by
    calc
      (Real.sqrt 3) ^ 3 = (Real.sqrt 3) ^ 2 * Real.sqrt 3 := by ring
      _ = 3 * Real.sqrt 3 := by rw [hssq]
  unfold volume
  rw [hheight]
  calc
    4 * (optimum R) ^ 2 * optimum R = 4 * (optimum R) ^ 3 := by ring
    _ = 4 * R ^ 3 / (3 * Real.sqrt 3) := by
      unfold optimum
      rw [div_pow, hscube]
      ring

theorem gap8 (R : ℝ) (hR : 0 < R) :
    IsOptimal R (optimum R) (optimum R) := by
  refine ⟨optimum_feasible R hR, ?_⟩
  intro x y hfeas
  rcases hfeas with ⟨hx, hy, hcon⟩
  have hb := (product_bound_and_eq R x y hR hx hy hcon).1
  nlinarith

end

end ProofGap.Exercise1568
