import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv

namespace ProofGap.Exercise1090

noncomputable section

def differential (f : ℝ → ℝ) (x dx : ℝ) : ℝ := deriv f x * dx

def f₁ (x : ℝ) : ℝ := x * Real.exp x
def f₂ (x : ℝ) : ℝ := Real.sin x - x * Real.cos x
def f₃ (x : ℝ) : ℝ := 1 / x ^ 3
def f₄ (x : ℝ) : ℝ := Real.log x / Real.sqrt x
def f₅ (a x : ℝ) : ℝ := Real.sqrt (a ^ 2 + x ^ 2)
def f₆ (x : ℝ) : ℝ := x / Real.sqrt (1 - x ^ 2)
def f₇ (x : ℝ) : ℝ := Real.log (1 - x ^ 2)
def f₈ (x : ℝ) : ℝ := Real.arccos (1 / |x|)
def f₉ (x : ℝ) : ℝ :=
  Real.sin x / (2 * Real.cos x ^ 2) +
    (1 / 2 : ℝ) * Real.log |Real.tan (x / 2 + Real.pi / 4)|

def threeHalves (x : ℝ) : ℝ := Real.rpow x (3 / 2 : ℝ)

private lemma threeHalves_eq_mul_sqrt (u : ℝ) (hu : 0 < u) :
    threeHalves u = u * Real.sqrt u := by
  unfold threeHalves
  change u ^ (3 / 2 : ℝ) = u * Real.sqrt u
  rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num]
  rw [Real.rpow_add hu, Real.rpow_one, ← Real.sqrt_eq_rpow]

private lemma hasDerivAt_log_abs (x : ℝ) (hx : x ≠ 0) :
    HasDerivAt (fun z : ℝ => Real.log |z|) (1 / x) x := by
  have hfun : (fun z : ℝ => Real.log |z|) = Real.log := by
    funext z
    exact Real.log_abs z
  rw [hfun]
  simpa [one_div] using Real.hasDerivAt_log hx

theorem gap1 (x dx : ℝ) :
    differential f₁ x dx = deriv f₁ x * dx := by rfl

theorem gap2 (x dx : ℝ) :
    deriv f₁ x * dx = Real.exp x * (x + 1) * dx := by
  have hf : HasDerivAt f₁ (Real.exp x * (x + 1)) x := by
    unfold f₁
    convert HasDerivAt.mul (hasDerivAt_id x) (Real.hasDerivAt_exp x)
      using 1 <;> simp only [id_eq] <;> ring
  rw [hf.deriv]

theorem gap3 (x dx : ℝ) :
    differential f₁ x dx = Real.exp x * (x + 1) * dx := by
  rw [gap1, gap2]

theorem gap4 (x dx : ℝ) :
    differential f₂ x dx = deriv f₂ x * dx := by rfl

theorem gap5 (x dx : ℝ) :
    deriv f₂ x * dx = x * Real.sin x * dx := by
  have hprod :
      HasDerivAt (fun z : ℝ => z * Real.cos z)
        (Real.cos x - x * Real.sin x) x := by
    convert HasDerivAt.mul (hasDerivAt_id x) (Real.hasDerivAt_cos x)
      using 1 <;> simp only [id_eq] <;> ring
  have hf : HasDerivAt f₂ (x * Real.sin x) x := by
    unfold f₂
    convert HasDerivAt.sub (Real.hasDerivAt_sin x) hprod using 1 <;> ring
  rw [hf.deriv]

theorem gap6 (x dx : ℝ) :
    differential f₂ x dx = x * Real.sin x * dx := by
  rw [gap4, gap5]

theorem gap7 (x dx : ℝ) (hx : x ≠ 0) :
    differential f₃ x dx = -(3 / x ^ 4) * dx := by
  have hpow :
      HasDerivAt (fun z : ℝ => z ^ 3) (3 * x ^ 2) x := by
    convert (hasDerivAt_id x).pow 3 using 1 <;>
      simp only [id_eq] <;> ring
  have hf : HasDerivAt f₃ (-(3 / x ^ 4)) x := by
    unfold f₃
    convert HasDerivAt.div (hasDerivAt_const x (1 : ℝ)) hpow
      (pow_ne_zero 3 hx) using 1 <;>
      field_simp [hx] <;> ring
  unfold differential
  rw [hf.deriv]

theorem gap8 (x dx : ℝ) (hx : 0 < x) :
    differential f₄ x dx =
      (((1 / x) * Real.sqrt x -
          (1 / (2 * Real.sqrt x)) * Real.log x) / x) * dx := by
  have hspos : 0 < Real.sqrt x := Real.sqrt_pos.2 hx
  have hs0 : Real.sqrt x ≠ 0 := ne_of_gt hspos
  have hs2 : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx.le
  have hlog :
      HasDerivAt Real.log (1 / x) x := by
    simpa [one_div] using Real.hasDerivAt_log hx.ne'
  have hsqrt :
      HasDerivAt Real.sqrt (1 / (2 * Real.sqrt x)) x :=
    Real.hasDerivAt_sqrt hx.ne'
  have hf :
      HasDerivAt f₄
        (((1 / x) * Real.sqrt x -
          (1 / (2 * Real.sqrt x)) * Real.log x) / x) x := by
    unfold f₄
    convert HasDerivAt.div hlog hsqrt hs0 using 1 <;>
      field_simp [hx.ne', hs0] <;>
      rw [hs2] <;> ring
  unfold differential
  rw [hf.deriv]

theorem gap9 (x dx : ℝ) (hx : 0 < x) :
    (((1 / x) * Real.sqrt x -
        (1 / (2 * Real.sqrt x)) * Real.log x) / x) * dx =
      (2 - Real.log x) / (2 * x * Real.sqrt x) * dx := by
  have hs0 : Real.sqrt x ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hx)
  have hs2 : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx.le
  field_simp [hx.ne', hs0] <;> rw [hs2] <;> ring

theorem gap10 (x dx : ℝ) (hx : 0 < x) :
    differential f₄ x dx =
      (2 - Real.log x) / (2 * x * Real.sqrt x) * dx := by
  rw [gap8 x dx hx, gap9 x dx hx]

theorem gap11 (a x dx : ℝ) (h : 0 < a ^ 2 + x ^ 2) :
    differential (f₅ a) x dx =
      x * dx / Real.sqrt (a ^ 2 + x ^ 2) := by
  have hs0 : Real.sqrt (a ^ 2 + x ^ 2) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 h)
  have hinner :
      HasDerivAt (fun z : ℝ => a ^ 2 + z ^ 2) (2 * x) x := by
    convert HasDerivAt.add (hasDerivAt_const x (a ^ 2))
      ((hasDerivAt_id x).pow 2) using 1 <;>
      simp only [id_eq] <;> ring
  have hf :
      HasDerivAt (f₅ a) (x / Real.sqrt (a ^ 2 + x ^ 2)) x := by
    unfold f₅
    convert (Real.hasDerivAt_sqrt h.ne').comp x hinner using 1 <;>
      field_simp [hs0] <;> ring
  unfold differential
  rw [hf.deriv]
  ring

theorem gap12 (x dx : ℝ) (hx : x ^ 2 < 1) :
    differential f₆ x dx =
      ((Real.sqrt (1 - x ^ 2) +
          x ^ 2 / Real.sqrt (1 - x ^ 2)) /
        (1 - x ^ 2)) * dx := by
  have hq : 0 < 1 - x ^ 2 := sub_pos.mpr hx
  have hs0 : Real.sqrt (1 - x ^ 2) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hq)
  have hs2 : Real.sqrt (1 - x ^ 2) ^ 2 = 1 - x ^ 2 :=
    Real.sq_sqrt hq.le
  have hinner :
      HasDerivAt (fun z : ℝ => 1 - z ^ 2) (-2 * x) x := by
    convert HasDerivAt.sub (hasDerivAt_const x (1 : ℝ))
      ((hasDerivAt_id x).pow 2) using 1 <;>
      simp only [id_eq] <;> ring
  have hsqrt :
      HasDerivAt (fun z : ℝ => Real.sqrt (1 - z ^ 2))
        (-x / Real.sqrt (1 - x ^ 2)) x := by
    convert (Real.hasDerivAt_sqrt hq.ne').comp x hinner using 1 <;>
      field_simp [hs0] <;> ring
  have hf :
      HasDerivAt f₆
        ((Real.sqrt (1 - x ^ 2) +
            x ^ 2 / Real.sqrt (1 - x ^ 2)) /
          (1 - x ^ 2)) x := by
    unfold f₆
    convert HasDerivAt.div (hasDerivAt_id x) hsqrt hs0 using 1 <;>
      simp only [id_eq] <;>
      field_simp [hs0, hq.ne'] <;>
      rw [hs2] <;> ring
  unfold differential
  rw [hf.deriv]

theorem gap13 (x dx : ℝ) (hx : x ^ 2 < 1) :
    ((Real.sqrt (1 - x ^ 2) +
        x ^ 2 / Real.sqrt (1 - x ^ 2)) /
      (1 - x ^ 2)) * dx =
      dx / threeHalves (1 - x ^ 2) := by
  have hq : 0 < 1 - x ^ 2 := sub_pos.mpr hx
  have hs0 : Real.sqrt (1 - x ^ 2) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hq)
  have hs2 : Real.sqrt (1 - x ^ 2) ^ 2 = 1 - x ^ 2 :=
    Real.sq_sqrt hq.le
  rw [threeHalves_eq_mul_sqrt (1 - x ^ 2) hq]
  field_simp [hq.ne', hs0] <;> rw [hs2] <;> ring

theorem gap14 (x dx : ℝ) (hx : x ^ 2 < 1) :
    differential f₆ x dx = dx / threeHalves (1 - x ^ 2) := by
  rw [gap12 x dx hx, gap13 x dx hx]

theorem gap15 (x dx : ℝ) (hx : x ^ 2 < 1) :
    differential f₇ x dx = -(2 * x * dx / (1 - x ^ 2)) := by
  have hq : 0 < 1 - x ^ 2 := sub_pos.mpr hx
  have hinner :
      HasDerivAt (fun z : ℝ => 1 - z ^ 2) (-2 * x) x := by
    convert HasDerivAt.sub (hasDerivAt_const x (1 : ℝ))
      ((hasDerivAt_id x).pow 2) using 1 <;>
      simp only [id_eq] <;> ring
  have hf : HasDerivAt f₇ (-2 * x / (1 - x ^ 2)) x := by
    unfold f₇
    convert (Real.hasDerivAt_log hq.ne').comp x hinner using 1 <;>
      field_simp [hq.ne'] <;> ring
  unfold differential
  rw [hf.deriv]
  ring

theorem gap16 (x dx : ℝ) (hx : 1 < |x|) :
    differential f₈ x dx =
      (-(1 / Real.sqrt (1 - 1 / x ^ 2))) *
        (-(1 / x ^ 2)) * (|x| / x) * dx := by
  have habspos : 0 < |x| := lt_trans zero_lt_one hx
  have hx0 : x ≠ 0 := abs_pos.mp habspos
  have habs0 : |x| ≠ 0 := ne_of_gt habspos
  have habs :
      HasDerivAt (fun z : ℝ => |z|) (|x| / x) x := by
    rcases lt_or_gt_of_ne hx0 with hxneg | hxpos
    · have heq : |x| / x = -1 := by
        rw [abs_of_neg hxneg]
        field_simp [hx0]
      rw [heq]
      exact hasDerivAt_abs_neg hxneg
    · have heq : |x| / x = 1 := by
        rw [abs_of_pos hxpos]
        field_simp [hx0]
      rw [heq]
      exact hasDerivAt_abs_pos hxpos
  have hrec :
      HasDerivAt (fun z : ℝ => 1 / |z|)
        ((-(1 / x ^ 2)) * (|x| / x)) x := by
    convert HasDerivAt.div (hasDerivAt_const x (1 : ℝ)) habs habs0
      using 1 <;>
      field_simp [hx0, habs0] <;> nlinarith [sq_abs x]
  have hu_pos : 0 < 1 / |x| := one_div_pos.mpr habspos
  have hu_lt : 1 / |x| < 1 := (div_lt_one habspos).2 hx
  have hneg : (1 / |x| : ℝ) ≠ -1 := by nlinarith
  have hone : (1 / |x| : ℝ) ≠ 1 := ne_of_lt hu_lt
  have hu_sq : (1 / |x| : ℝ) ^ 2 = 1 / x ^ 2 := by
    field_simp [hx0, habs0]
    nlinarith [sq_abs x]
  have hf :
      HasDerivAt f₈
        ((-(1 / Real.sqrt (1 - 1 / x ^ 2))) *
          (-(1 / x ^ 2)) * (|x| / x)) x := by
    unfold f₈
    convert (Real.hasDerivAt_arccos hneg hone).comp x hrec using 1 <;>
      (try simp only [Function.comp_apply]) <;> (try rw [hu_sq]) <;> ring
  unfold differential
  rw [hf.deriv]

theorem gap17 (x dx : ℝ) (hx : 1 < |x|) :
    (-(1 / Real.sqrt (1 - 1 / x ^ 2))) *
        (-(1 / x ^ 2)) * (|x| / x) * dx =
      dx / (x * Real.sqrt (x ^ 2 - 1)) := by
  have habspos : 0 < |x| := lt_trans zero_lt_one hx
  have hx0 : x ≠ 0 := abs_pos.mp habspos
  have habs0 : |x| ≠ 0 := ne_of_gt habspos
  have hx2 : 1 < x ^ 2 := by nlinarith [sq_abs x]
  have harg : 0 < 1 - 1 / x ^ 2 := by
    have hx2pos : 0 < x ^ 2 := sq_pos_of_ne_zero hx0
    exact sub_pos.mpr ((div_lt_one hx2pos).2 hx2)
  have hs0 : Real.sqrt (1 - 1 / x ^ 2) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 harg)
  have hsqrt :
      Real.sqrt (x ^ 2 - 1) =
        |x| * Real.sqrt (1 - 1 / x ^ 2) := by
    have halg : x ^ 2 - 1 = x ^ 2 * (1 - 1 / x ^ 2) := by
      field_simp [hx0] <;> ring
    rw [halg, Real.sqrt_mul (sq_nonneg x), Real.sqrt_sq_eq_abs]
  rw [hsqrt]
  field_simp [hx0, habs0, hs0] <;> rw [sq_abs x] <;> ring

theorem gap18 (x dx : ℝ) (hx : 1 < |x|) :
    differential f₈ x dx =
      dx / (x * Real.sqrt (x ^ 2 - 1)) := by
  rw [gap16 x dx hx, gap17 x dx hx]

theorem gap19 (x dx : ℝ) (hx : Real.cos x ≠ 0) :
    differential f₉ x dx =
      (((Real.cos x ^ 3 +
          2 * Real.sin x ^ 2 * Real.cos x) /
          (2 * Real.cos x ^ 4) +
        1 / (2 * Real.cos x)) * dx) := by
  let u : ℝ := x / 2 + Real.pi / 4
  have htwou : 2 * u = x + Real.pi / 2 := by
    dsimp [u]
    ring
  have hcosrel :
      2 * Real.sin u * Real.cos u = Real.cos x := by
    calc
      2 * Real.sin u * Real.cos u = Real.sin (2 * u) := by
        rw [Real.sin_two_mul]
      _ = Real.sin (x + Real.pi / 2) := by rw [htwou]
      _ = Real.cos x := by
        rw [Real.sin_add, Real.sin_pi_div_two, Real.cos_pi_div_two]
        ring
  have hsinu : Real.sin u ≠ 0 := by
    intro h
    apply hx
    rw [← hcosrel, h]
    ring
  have hcosu : Real.cos u ≠ 0 := by
    intro h
    apply hx
    rw [← hcosrel, h]
    ring
  have htanu : Real.tan u ≠ 0 := by
    rw [Real.tan_eq_sin_div_cos]
    exact div_ne_zero hsinu hcosu
  have hline :
      HasDerivAt (fun z : ℝ => z / 2 + Real.pi / 4) (1 / 2) x := by
    convert ((hasDerivAt_id x).div_const 2).add_const (Real.pi / 4)
      using 1 <;> norm_num
  have htan :
      HasDerivAt (fun z : ℝ => Real.tan (z / 2 + Real.pi / 4))
        ((1 / Real.cos u ^ 2) * (1 / 2)) x := by
    simpa only [Function.comp_apply, u] using
      (Real.hasDerivAt_tan hcosu).comp x hline
  have hblog :
      HasDerivAt
        (fun z : ℝ =>
          Real.log |Real.tan (z / 2 + Real.pi / 4)|)
        ((1 / Real.tan u) *
          ((1 / Real.cos u ^ 2) * (1 / 2))) x := by
    simpa only [Function.comp_apply, u] using
      (hasDerivAt_log_abs (Real.tan u) htanu).comp x htan
  have hbcoef :
      (1 / 2 : ℝ) *
          ((1 / Real.tan u) *
            ((1 / Real.cos u ^ 2) * (1 / 2))) =
        1 / (2 * Real.cos x) := by
    rw [Real.tan_eq_sin_div_cos, ← hcosrel]
    field_simp [hsinu, hcosu, hx]
    <;> ring
  have hb :
      HasDerivAt
        (fun z : ℝ =>
          (1 / 2 : ℝ) *
            Real.log |Real.tan (z / 2 + Real.pi / 4)|)
        (1 / (2 * Real.cos x)) x := by
    rw [← hbcoef]
    exact hblog.const_mul (1 / 2)
  have hden :
      HasDerivAt (fun z : ℝ => 2 * Real.cos z ^ 2)
        (-4 * Real.sin x * Real.cos x) x := by
    convert ((Real.hasDerivAt_cos x).pow 2).const_mul 2 using 1 <;>
      (try simp only [Pi.pow_apply]) <;> ring
  have ha :
      HasDerivAt
        (fun z : ℝ => Real.sin z / (2 * Real.cos z ^ 2))
        ((Real.cos x ^ 3 +
            2 * Real.sin x ^ 2 * Real.cos x) /
          (2 * Real.cos x ^ 4)) x := by
    convert HasDerivAt.div (Real.hasDerivAt_sin x) hden
      (mul_ne_zero (by norm_num) (pow_ne_zero 2 hx)) using 1 <;>
      field_simp [hx] <;> ring
  have hf :
      HasDerivAt f₉
        ((Real.cos x ^ 3 +
            2 * Real.sin x ^ 2 * Real.cos x) /
            (2 * Real.cos x ^ 4) +
          1 / (2 * Real.cos x)) x := by
    unfold f₉
    simpa only [Pi.add_apply] using HasDerivAt.add ha hb
  unfold differential
  rw [hf.deriv]

theorem gap20 (x dx : ℝ) (hx : Real.cos x ≠ 0) :
    ((Real.cos x ^ 3 +
        2 * Real.sin x ^ 2 * Real.cos x) /
        (2 * Real.cos x ^ 4) +
      1 / (2 * Real.cos x)) * dx =
      dx / Real.cos x ^ 3 := by
  have htrig := Real.sin_sq_add_cos_sq x
  field_simp [hx]
  have hsum :
      Real.cos x ^ 2 + 2 * Real.sin x ^ 2 + Real.cos x ^ 2 = 2 := by
    nlinarith
  rw [hsum]

theorem gap21 (x dx : ℝ) (hx : Real.cos x ≠ 0) :
    differential f₉ x dx = dx / Real.cos x ^ 3 := by
  rw [gap19 x dx hx, gap20 x dx hx]

end

end ProofGap.Exercise1090
