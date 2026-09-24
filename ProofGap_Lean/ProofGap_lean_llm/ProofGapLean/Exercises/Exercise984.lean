import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise984

noncomputable section

def cbrt (z : ℝ) : ℝ :=
  Real.sign z * Real.rpow |z| (1 / 3 : ℝ)

def y1 (x : ℝ) : ℝ :=
  x * Real.sqrt ((1 - x) / (1 + x))

def y2 (x : ℝ) : ℝ :=
  x ^ 2 / (1 - x) * cbrt ((3 - x) / (3 + x) ^ 2)

def dlog1 (x : ℝ) : ℝ :=
  1 / x - 1 / (2 * (1 - x)) - 1 / (2 * (1 + x))

def dlog1Final (x : ℝ) : ℝ :=
  (1 - x - x ^ 2) / (x * (1 - x ^ 2))

def dlog2 (x : ℝ) : ℝ :=
  2 / x + 1 / (1 - x) - 1 / (3 * (3 - x)) -
    2 / (3 * (3 + x))

def dlog2Final (x : ℝ) : ℝ :=
  (54 - 36 * x + 4 * x ^ 2 + 2 * x ^ 3) /
    (3 * x * (1 - x) * (9 - x ^ 2))

def y3 {n : ℕ} (a : Fin n → ℝ) (m : Fin n → ℕ) (x : ℝ) : ℝ :=
  ∏ i, (x - a i) ^ m i

def y4 (n : ℕ) (x : ℝ) : ℝ :=
  (x + Real.sqrt (1 + x ^ 2)) ^ n

private theorem cbrt_ne_zero_and_log (z : ℝ) (hz : z ≠ 0) :
    cbrt z ≠ 0 ∧ Real.log |cbrt z| =
      (1 / 3 : ℝ) * Real.log |z| := by
  rcases lt_or_gt_of_ne hz with hzneg | hzpos
  · have hp : 0 < -z := neg_pos.mpr hzneg
    have hr : 0 < Real.rpow (-z) (1 / 3 : ℝ) :=
      Real.rpow_pos_of_pos hp _
    have hc : cbrt z = -Real.rpow (-z) (1 / 3 : ℝ) := by
      simp only [cbrt, Real.sign_of_neg hzneg, abs_of_neg hzneg, neg_one_mul]
    constructor
    · rw [hc]
      exact neg_ne_zero.mpr hr.ne'
    · rw [hc, abs_neg, abs_of_pos hr, abs_of_neg hzneg]
      have hpow : Real.rpow (-z) (1 / 3 : ℝ) =
          Real.exp (Real.log (-z) * (1 / 3 : ℝ)) :=
        Real.rpow_def_of_pos hp (1 / 3 : ℝ)
      rw [hpow, Real.log_exp]
      ring
  · have hr : 0 < Real.rpow z (1 / 3 : ℝ) :=
      Real.rpow_pos_of_pos hzpos _
    have hc : cbrt z = Real.rpow z (1 / 3 : ℝ) := by
      simp only [cbrt, Real.sign_of_pos hzpos, abs_of_pos hzpos, one_mul]
    constructor
    · rw [hc]
      exact hr.ne'
    · rw [hc, abs_of_pos hr, abs_of_pos hzpos]
      have hpow : Real.rpow z (1 / 3 : ℝ) =
          Real.exp (Real.log z * (1 / 3 : ℝ)) :=
        Real.rpow_def_of_pos hzpos (1 / 3 : ℝ)
      rw [hpow, Real.log_exp]
      ring

theorem gap1 (x : ℝ) (hx : -1 < x ∧ x < 1) (hx0 : x ≠ 0) :
    Real.log |y1 x| =
      Real.log |x| + (1 / 2) * Real.log |1 - x| -
        (1 / 2) * Real.log |1 + x| := by
  have hnum : 0 < 1 - x := by linarith
  have hden : 0 < 1 + x := by linarith
  have hquot : 0 < (1 - x) / (1 + x) := div_pos hnum hden
  have hsqrt : 0 < Real.sqrt ((1 - x) / (1 + x)) :=
    Real.sqrt_pos.2 hquot
  calc
    Real.log |y1 x| =
        Real.log |x| + Real.log (Real.sqrt ((1 - x) / (1 + x))) := by
      rw [y1, abs_mul, abs_of_pos hsqrt,
        Real.log_mul (abs_ne_zero.mpr hx0) hsqrt.ne']
    _ = Real.log |x| +
        (1 / 2 : ℝ) * (Real.log (1 - x) - Real.log (1 + x)) := by
      rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hquot, Real.log_exp,
        Real.log_div hnum.ne' hden.ne']
      ring
    _ = Real.log |x| + (1 / 2) * Real.log |1 - x| -
        (1 / 2) * Real.log |1 + x| := by
      rw [abs_of_pos hnum, abs_of_pos hden]
      ring

theorem gap2 (x : ℝ) (hx : -1 < x ∧ x < 1) (hx0 : x ≠ 0) :
    HasDerivAt (fun z => Real.log |y1 z|) (dlog1 x) x := by
  have hm : 1 - x ≠ 0 := by linarith
  have hp : 1 + x ≠ 0 := by linarith
  have hlogx : HasDerivAt (fun z : ℝ => Real.log |z|) (1 / x) x := by
    simpa [Real.log_abs, one_div] using Real.hasDerivAt_log hx0
  have hlinm : HasDerivAt (fun z : ℝ => 1 - z) (-1) x := by
    convert (hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id x) using 1 <;> ring
  have hlinp : HasDerivAt (fun z : ℝ => 1 + z) 1 x := by
    convert (hasDerivAt_const x (1 : ℝ)).add (hasDerivAt_id x) using 1 <;> ring
  have hlogm : HasDerivAt (fun z : ℝ => Real.log |1 - z|)
      (-1 / (1 - x)) x := by
    simpa only [Real.log_abs] using hlinm.log hm
  have hlogp : HasDerivAt (fun z : ℝ => Real.log |1 + z|)
      (1 / (1 + x)) x := by
    simpa only [Real.log_abs] using hlinp.log hp
  have hder : HasDerivAt
      (fun z : ℝ => Real.log |z| + (1 / 2) * Real.log |1 - z| -
        (1 / 2) * Real.log |1 + z|) (dlog1 x) x := by
    convert (hlogx.add (hlogm.const_mul (1 / 2 : ℝ))).sub
      (hlogp.const_mul (1 / 2 : ℝ)) using 1
    unfold dlog1
    field_simp [hx0, hm, hp] <;> ring_nf
  have heq :
      (fun z : ℝ => Real.log |z| + (1 / 2) * Real.log |1 - z| -
        (1 / 2) * Real.log |1 + z|) =ᶠ[nhds x]
      (fun z : ℝ => Real.log |y1 z|) := by
    filter_upwards [isOpen_Ioo.mem_nhds hx, eventually_ne_nhds hx0] with z hz hz0
    exact (gap1 z hz hz0).symm
  exact hder.congr_of_eventuallyEq heq.symm

theorem gap3 (x : ℝ) (hx : -1 < x ∧ x < 1) (hx0 : x ≠ 0) :
    dlog1 x = dlog1Final x := by
  have hm : 1 - x ≠ 0 := by linarith
  have hp : 1 + x ≠ 0 := by linarith
  have hs : 1 - x ^ 2 ≠ 0 := by
    rw [show 1 - x ^ 2 = (1 - x) * (1 + x) by ring]
    exact mul_ne_zero hm hp
  unfold dlog1 dlog1Final
  field_simp [hx0, hm, hp, hs] <;> ring

theorem gap4 (x : ℝ) (hx : -1 < x ∧ x < 1) (hx0 : x ≠ 0) :
    HasDerivAt (fun z => Real.log |y1 z|) (dlog1Final x) x := by
  rw [← gap3 x hx hx0]
  exact gap2 x hx hx0

theorem gap5 (x : ℝ) (hx0 : x ≠ 0) (hx1 : x ≠ 1)
    (hx3 : x ≠ 3) (hxm3 : x ≠ -3) :
    Real.log |y2 x| =
      2 * Real.log |x| - Real.log |1 - x| +
        (1 / 3) * Real.log |3 - x| -
        (2 / 3) * Real.log |3 + x| := by
  have h1 : 1 - x ≠ 0 := by
    intro h
    apply hx1
    linarith
  have h3 : 3 - x ≠ 0 := by
    intro h
    apply hx3
    linarith
  have hp3 : 3 + x ≠ 0 := by
    intro h
    apply hxm3
    linarith
  have hx2 : x ^ 2 ≠ 0 := pow_ne_zero 2 hx0
  have hp32 : (3 + x) ^ 2 ≠ 0 := pow_ne_zero 2 hp3
  have hleft : x ^ 2 / (1 - x) ≠ 0 := div_ne_zero hx2 h1
  have hquot : (3 - x) / (3 + x) ^ 2 ≠ 0 := div_ne_zero h3 hp32
  have hc := cbrt_ne_zero_and_log ((3 - x) / (3 + x) ^ 2) hquot
  calc
    Real.log |y2 x| = Real.log |x ^ 2 / (1 - x)| +
        Real.log |cbrt ((3 - x) / (3 + x) ^ 2)| := by
      rw [y2, abs_mul,
        Real.log_mul (abs_ne_zero.mpr hleft) (abs_ne_zero.mpr hc.1)]
    _ = (Real.log |x ^ 2| - Real.log |1 - x|) +
        (1 / 3 : ℝ) * Real.log |(3 - x) / (3 + x) ^ 2| := by
      rw [abs_div,
        Real.log_div (abs_ne_zero.mpr hx2) (abs_ne_zero.mpr h1), hc.2]
    _ = 2 * Real.log |x| - Real.log |1 - x| +
        (1 / 3) * Real.log |3 - x| -
        (2 / 3) * Real.log |3 + x| := by
      rw [abs_pow, Real.log_pow, abs_div,
        Real.log_div (abs_ne_zero.mpr h3) (abs_ne_zero.mpr hp32),
        abs_pow, Real.log_pow]
      ring

theorem gap6 (x : ℝ) (hx0 : x ≠ 0) (hx1 : x ≠ 1)
    (hx3 : x ≠ 3) (hxm3 : x ≠ -3) :
    HasDerivAt (fun z => Real.log |y2 z|) (dlog2 x) x := by
  have h1 : 1 - x ≠ 0 := by
    intro h
    apply hx1
    linarith
  have h3 : 3 - x ≠ 0 := by
    intro h
    apply hx3
    linarith
  have hp3 : 3 + x ≠ 0 := by
    intro h
    apply hxm3
    linarith
  have hlogx : HasDerivAt (fun z : ℝ => Real.log |z|) (1 / x) x := by
    simpa [Real.log_abs, one_div] using Real.hasDerivAt_log hx0
  have hlin1 : HasDerivAt (fun z : ℝ => 1 - z) (-1) x := by
    convert (hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id x) using 1 <;> ring
  have hlin3 : HasDerivAt (fun z : ℝ => 3 - z) (-1) x := by
    convert (hasDerivAt_const x (3 : ℝ)).sub (hasDerivAt_id x) using 1 <;> ring
  have hlinp3 : HasDerivAt (fun z : ℝ => 3 + z) 1 x := by
    convert (hasDerivAt_const x (3 : ℝ)).add (hasDerivAt_id x) using 1 <;> ring
  have hlog1 : HasDerivAt (fun z : ℝ => Real.log |1 - z|)
      (-1 / (1 - x)) x := by
    simpa only [Real.log_abs] using hlin1.log h1
  have hlog3 : HasDerivAt (fun z : ℝ => Real.log |3 - z|)
      (-1 / (3 - x)) x := by
    simpa only [Real.log_abs] using hlin3.log h3
  have hlogp3 : HasDerivAt (fun z : ℝ => Real.log |3 + z|)
      (1 / (3 + x)) x := by
    simpa only [Real.log_abs] using hlinp3.log hp3
  have hder : HasDerivAt
      (fun z : ℝ => 2 * Real.log |z| - Real.log |1 - z| +
        (1 / 3) * Real.log |3 - z| - (2 / 3) * Real.log |3 + z|)
      (dlog2 x) x := by
    convert (((hlogx.const_mul (2 : ℝ)).sub hlog1).add
      (hlog3.const_mul (1 / 3 : ℝ))).sub
      (hlogp3.const_mul (2 / 3 : ℝ)) using 1
    unfold dlog2
    field_simp [hx0, h1, h3, hp3] <;> ring_nf
  have heq :
      (fun z : ℝ => 2 * Real.log |z| - Real.log |1 - z| +
        (1 / 3) * Real.log |3 - z| - (2 / 3) * Real.log |3 + z|) =ᶠ[nhds x]
      (fun z : ℝ => Real.log |y2 z|) := by
    filter_upwards [eventually_ne_nhds hx0, eventually_ne_nhds hx1,
      eventually_ne_nhds hx3, eventually_ne_nhds hxm3] with z hz0 hz1 hz3 hzm3
    exact (gap5 z hz0 hz1 hz3 hzm3).symm
  exact hder.congr_of_eventuallyEq heq.symm

theorem gap7 (x : ℝ) (hx0 : x ≠ 0) (hx1 : x ≠ 1)
    (hx3 : x ≠ 3) (hxm3 : x ≠ -3) :
    HasDerivAt (fun z => Real.log |y2 z|) (dlog2Final x) x := by
  have h1 : 1 - x ≠ 0 := by
    intro h
    apply hx1
    linarith
  have h3 : 3 - x ≠ 0 := by
    intro h
    apply hx3
    linarith
  have hp3 : 3 + x ≠ 0 := by
    intro h
    apply hxm3
    linarith
  have h9 : 9 - x ^ 2 ≠ 0 := by
    rw [show 9 - x ^ 2 = (3 - x) * (3 + x) by ring]
    exact mul_ne_zero h3 hp3
  have heq : dlog2 x = dlog2Final x := by
    unfold dlog2 dlog2Final
    field_simp [hx0, h1, h3, hp3, h9] <;> ring
  rw [← heq]
  exact gap6 x hx0 hx1 hx3 hxm3

theorem gap8 {n : ℕ} (a : Fin n → ℝ) (m : Fin n → ℕ) (x : ℝ)
    (hpos : 0 < y3 a m x) :
    0 < ∏ i, (x - a i) ^ m i := by
  simpa only [y3] using hpos

theorem gap9 {n : ℕ} (a : Fin n → ℝ) (m : Fin n → ℕ) (x : ℝ)
    (hpos : 0 < y3 a m x) :
    Real.log (y3 a m x) =
      Real.log (∏ i, (x - a i) ^ m i) := by
  rfl

theorem gap10 {n : ℕ} (a : Fin n → ℝ) (m : Fin n → ℕ) (x : ℝ)
    (hroot : ∀ i, x ≠ a i) :
    Real.log |∏ i, (x - a i) ^ m i| =
      ∑ i, (m i : ℝ) * Real.log |x - a i| := by
  classical
  have hmain : ∀ s : Finset (Fin n),
      Real.log |∏ i ∈ s, (x - a i) ^ m i| =
        ∑ i ∈ s, (m i : ℝ) * Real.log |x - a i| := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
        have hfi : (x - a i) ^ m i ≠ 0 :=
          pow_ne_zero _ (sub_ne_zero.mpr (hroot i))
        have hprod : ∏ j ∈ s, (x - a j) ^ m j ≠ 0 := by
          exact Finset.prod_ne_zero_iff.mpr fun j _ =>
            pow_ne_zero _ (sub_ne_zero.mpr (hroot j))
        have hpow : Real.log |(x - a i) ^ m i| =
            (m i : ℝ) * Real.log |x - a i| := by
          rw [abs_pow, Real.log_pow]
        rw [Finset.prod_insert hi, Finset.sum_insert hi, abs_mul,
          Real.log_mul (abs_ne_zero.mpr hfi) (abs_ne_zero.mpr hprod),
          hpow, ih]
  simpa using hmain Finset.univ

theorem gap11 {n : ℕ} (a : Fin n → ℝ) (m : Fin n → ℕ) (x : ℝ)
    (hroot : ∀ i, x ≠ a i) :
    Real.log |y3 a m x| =
      ∑ i, (m i : ℝ) * Real.log |x - a i| := by
  simpa only [y3] using gap10 a m x hroot

theorem gap12 {n : ℕ} (a : Fin n → ℝ) (m : Fin n → ℕ) (x : ℝ)
    (hroot : ∀ i, x ≠ a i) :
    HasDerivAt (fun z => Real.log |y3 a m z|)
      (∑ i, (m i : ℝ) / (x - a i)) x := by
  classical
  have hterm (i : Fin n) :
      HasDerivAt (fun z : ℝ => (m i : ℝ) * Real.log |z - a i|)
        ((m i : ℝ) / (x - a i)) x := by
    have hlin : HasDerivAt (fun z : ℝ => z - a i) 1 x := by
      simpa only [id_eq, sub_zero] using
        (hasDerivAt_id x).sub (hasDerivAt_const x (a i))
    have hlog : HasDerivAt (fun z : ℝ => Real.log |z - a i|)
        (1 / (x - a i)) x := by
      simpa [Real.log_abs, one_div] using
        hlin.log (sub_ne_zero.mpr (hroot i))
    simpa [div_eq_mul_inv] using hlog.const_mul (m i : ℝ)
  have hder_univ : HasDerivAt
      (∑ i ∈ (Finset.univ : Finset (Fin n)),
        fun z : ℝ => (m i : ℝ) * Real.log |z - a i|)
      (∑ i ∈ (Finset.univ : Finset (Fin n)),
        (m i : ℝ) / (x - a i)) x := by
    exact HasDerivAt.sum fun i _ => hterm i
  have hfun :
      (∑ i ∈ (Finset.univ : Finset (Fin n)),
        fun z : ℝ => (m i : ℝ) * Real.log |z - a i|) =
      (fun z : ℝ => ∑ i ∈ (Finset.univ : Finset (Fin n)),
        (m i : ℝ) * Real.log |z - a i|) := by
    funext z
    simp only [Finset.sum_apply]
  rw [hfun] at hder_univ
  have hder : HasDerivAt
      (fun z : ℝ => ∑ i, (m i : ℝ) * Real.log |z - a i|)
      (∑ i, (m i : ℝ) / (x - a i)) x := hder_univ
  have hev : ∀ᶠ z in nhds x, ∀ i, z ≠ a i := by
    have hall : ∀ s : Finset (Fin n),
        ∀ᶠ z in nhds x, ∀ i ∈ s, z ≠ a i := by
      intro s
      induction s using Finset.induction_on with
      | empty => simp
      | @insert i s his ih =>
          filter_upwards [eventually_ne_nhds (hroot i), ih] with z hzi hzs
          intro j hj
          rcases Finset.mem_insert.mp hj with hji | hjs
          · subst j
            exact hzi
          · exact hzs j hjs
    filter_upwards [hall Finset.univ] with z hz
    intro i
    exact hz i (Finset.mem_univ i)
  have heq :
      (fun z : ℝ => ∑ i, (m i : ℝ) * Real.log |z - a i|) =ᶠ[nhds x]
      (fun z : ℝ => Real.log |y3 a m z|) := by
    filter_upwards [hev] with z hz
    exact (gap11 a m z hz).symm
  exact hder.congr_of_eventuallyEq heq.symm

theorem gap13 {n : ℕ} (a : Fin n → ℝ) (m : Fin n → ℕ) :
    ∃ A : Set ℝ, A = {x | 0 < y3 a m x} := by
  exact ⟨{x | 0 < y3 a m x}, rfl⟩

theorem gap14 (n : ℕ) (x : ℝ) :
    Real.log (y4 n x) =
      (n : ℝ) * Real.log (x + Real.sqrt (1 + x ^ 2)) := by
  unfold y4
  rw [Real.log_pow]

theorem gap15 (n : ℕ) (x : ℝ) :
    HasDerivAt (fun z => Real.log (y4 n z))
      ((n : ℝ) / Real.sqrt (1 + x ^ 2)) x := by
  have hqpos : 0 < 1 + x ^ 2 := by nlinarith [sq_nonneg x]
  have hspos : 0 < Real.sqrt (1 + x ^ 2) := Real.sqrt_pos.2 hqpos
  have hsquare : (Real.sqrt (1 + x ^ 2)) ^ 2 = 1 + x ^ 2 :=
    Real.sq_sqrt hqpos.le
  have hpow : HasDerivAt (fun z : ℝ => z ^ 2) (2 * x) x := by
    convert (hasDerivAt_id x).pow 2 using 1 <;>
      simp only [id_eq] <;> ring
  have hinner : HasDerivAt (fun z : ℝ => 1 + z ^ 2) (2 * x) x := by
    convert (hasDerivAt_const x (1 : ℝ)).add hpow using 1 <;> ring
  have hloginner : HasDerivAt
      (fun z : ℝ => Real.log (1 + z ^ 2))
      ((2 * x) / (1 + x ^ 2)) x :=
    hinner.log hqpos.ne'
  have hexp : HasDerivAt
      (fun z : ℝ => Real.exp ((1 / 2 : ℝ) * Real.log (1 + z ^ 2)))
      (Real.exp ((1 / 2 : ℝ) * Real.log (1 + x ^ 2)) *
        ((1 / 2 : ℝ) * ((2 * x) / (1 + x ^ 2)))) x :=
    (hloginner.const_mul (1 / 2 : ℝ)).exp
  have hsqrt_eq :
      (fun z : ℝ => Real.sqrt (1 + z ^ 2)) =
      (fun z : ℝ => Real.exp ((1 / 2 : ℝ) * Real.log (1 + z ^ 2))) := by
    funext z
    have hzpos : 0 < 1 + z ^ 2 := by nlinarith [sq_nonneg z]
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hzpos]
    congr 1
    ring
  have hexpval :
      Real.exp ((1 / 2 : ℝ) * Real.log (1 + x ^ 2)) =
        Real.sqrt (1 + x ^ 2) :=
    (congrFun hsqrt_eq x).symm
  have hcoef :
      Real.exp ((1 / 2 : ℝ) * Real.log (1 + x ^ 2)) *
          ((1 / 2 : ℝ) * ((2 * x) / (1 + x ^ 2))) =
        x / Real.sqrt (1 + x ^ 2) := by
    have hxsquare :
        x * (Real.sqrt (1 + x ^ 2)) ^ 2 = x * (1 + x ^ 2) :=
      congrArg (fun t : ℝ => x * t) hsquare
    rw [hexpval]
    field_simp [hqpos.ne', hspos.ne'] <;> nlinarith [hxsquare]
  have hsqrt : HasDerivAt (fun z : ℝ => Real.sqrt (1 + z ^ 2))
      (x / Real.sqrt (1 + x ^ 2)) x := by
    rw [hsqrt_eq]
    rw [hcoef] at hexp
    exact hexp
  have hbase : HasDerivAt
      (fun z : ℝ => z + Real.sqrt (1 + z ^ 2))
      (1 + x / Real.sqrt (1 + x ^ 2)) x := by
    exact (hasDerivAt_id x).add hsqrt
  have hbpos : 0 < x + Real.sqrt (1 + x ^ 2) := by
    nlinarith [hsquare]
  have hder : HasDerivAt
      (fun z : ℝ => (n : ℝ) *
        Real.log (z + Real.sqrt (1 + z ^ 2)))
      ((n : ℝ) / Real.sqrt (1 + x ^ 2)) x := by
    convert (hbase.log hbpos.ne').const_mul (n : ℝ) using 1
    field_simp [hspos.ne', hbpos.ne', hsquare] <;> ring
  simpa only [gap14] using hder

end

end ProofGap.Exercise984
