import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.Neighborhoods
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Topology.Order.OrderClosed

namespace ProofGap.Exercise1222_2

noncomputable section

def iterDeriv (n : ℕ) (f : ℝ → ℝ) : ℝ → ℝ := (deriv^[n]) f
def f (x : ℝ) : ℝ := Real.arcsin x ^ 2

def recurrenceProduct (k : ℕ) : ℝ :=
  (∏ j ∈ Finset.range (k - 1), (2 * (j + 1) : ℝ) ^ 2) * iterDeriv 2 f 0

def closedForm (k : ℕ) : ℝ :=
  2 ^ (2 * k - 1) * (Nat.factorial (k - 1) : ℝ) ^ 2

private def recurrenceExpr (n : ℕ) (x : ℝ) : ℝ :=
  (1 - x ^ 2) * iterDeriv (n + 2) f x -
    (2 * (n : ℝ) + 1) * x * iterDeriv (n + 1) f x -
    (n : ℝ) ^ 2 * iterDeriv n f x

theorem gap1 (x : ℝ) (hx : |x| < 1) :
    deriv f x = 2 / Real.sqrt (1 - x ^ 2) * Real.arcsin x := by
  have hx' : x ∈ Set.Ioo (-1 : ℝ) 1 := abs_lt.mp hx
  have hasin :
      HasDerivAt Real.arcsin (1 / Real.sqrt (1 - x ^ 2)) x :=
    Real.hasDerivAt_arcsin (ne_of_gt hx'.1) (ne_of_lt hx'.2)
  have hder :
      deriv f x =
        (2 : ℝ) * Real.arcsin x * (1 / Real.sqrt (1 - x ^ 2)) := by
    simpa [f] using (hasin.pow 2).deriv
  calc
    deriv f x = (2 : ℝ) * Real.arcsin x * (1 / Real.sqrt (1 - x ^ 2)) := hder
    _ = 2 / Real.sqrt (1 - x ^ 2) * Real.arcsin x := by ring

theorem gap2 (x : ℝ) (hx : |x| < 1) :
    Real.sqrt (1 - x ^ 2) * deriv f x = 2 * Real.arcsin x := by
  have hx' : x ∈ Set.Ioo (-1 : ℝ) 1 := abs_lt.mp hx
  have hxm : 0 < 1 - x := by linarith [hx'.2]
  have hxp : 0 < 1 + x := by linarith [hx'.1]
  have hq : 0 < 1 - x ^ 2 := by nlinarith [mul_pos hxm hxp]
  have hsne : Real.sqrt (1 - x ^ 2) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hq)
  rw [gap1 x hx]
  field_simp [hsne]

theorem gap3 (x : ℝ) (hx : |x| < 1) :
    Real.sqrt (1 - x ^ 2) * iterDeriv 2 f x -
        x * deriv f x / Real.sqrt (1 - x ^ 2) =
      2 / Real.sqrt (1 - x ^ 2) := by
  have hx' : x ∈ Set.Ioo (-1 : ℝ) 1 := abs_lt.mp hx
  have hxm : 0 < 1 - x := by linarith [hx'.2]
  have hxp : 0 < 1 + x := by linarith [hx'.1]
  have hq : 0 < 1 - x ^ 2 := by nlinarith [mul_pos hxm hxp]
  have hsne : Real.sqrt (1 - x ^ 2) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hq)
  have hqder : HasDerivAt (fun y : ℝ => 1 - y ^ 2) (-2 * x) x := by
    convert (hasDerivAt_const x (1 : ℝ)).sub ((hasDerivAt_id x).pow 2) using 1 <;>
      simp <;> ring
  have hsder :
      HasDerivAt (fun y : ℝ => Real.sqrt (1 - y ^ 2))
        (-x / Real.sqrt (1 - x ^ 2)) x := by
    convert (Real.hasDerivAt_sqrt (ne_of_gt hq)).comp x hqder using 1 <;>
      field_simp [hsne] <;> ring
  have hquot :
      HasDerivAt (fun y : ℝ => 2 / Real.sqrt (1 - y ^ 2))
        (2 * x / Real.sqrt (1 - x ^ 2) ^ 3) x := by
    convert (hasDerivAt_const x (2 : ℝ)).div hsder hsne using 1 <;>
      field_simp [hsne] <;> ring
  have hasin :
      HasDerivAt Real.arcsin (1 / Real.sqrt (1 - x ^ 2)) x :=
    Real.hasDerivAt_arcsin (ne_of_gt hx'.1) (ne_of_lt hx'.2)
  have heq :
      deriv f =ᶠ[nhds x]
        (fun y : ℝ => 2 / Real.sqrt (1 - y ^ 2) * Real.arcsin y) := by
    filter_upwards [isOpen_Ioo.mem_nhds hx'] with y hy
    exact gap1 y (abs_lt.mpr hy)
  have hsecond :
      iterDeriv 2 f x =
        (2 * x / Real.sqrt (1 - x ^ 2) ^ 3) * Real.arcsin x +
          (2 / Real.sqrt (1 - x ^ 2)) *
            (1 / Real.sqrt (1 - x ^ 2)) := by
    change deriv (deriv f) x = _
    rw [heq.deriv_eq]
    exact (hquot.mul hasin).deriv
  rw [hsecond, gap1 x hx]
  field_simp [hsne]
  ring

theorem gap4 (x : ℝ) (hx : |x| < 1) :
    (1 - x ^ 2) * iterDeriv 2 f x - x * deriv f x - 2 = 0 := by
  have hx' : x ∈ Set.Ioo (-1 : ℝ) 1 := abs_lt.mp hx
  have hxm : 0 < 1 - x := by linarith [hx'.2]
  have hxp : 0 < 1 + x := by linarith [hx'.1]
  have hq : 0 < 1 - x ^ 2 := by nlinarith [mul_pos hxm hxp]
  have hsne : Real.sqrt (1 - x ^ 2) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hq)
  have hs2 : Real.sqrt (1 - x ^ 2) ^ 2 = 1 - x ^ 2 :=
    Real.sq_sqrt (le_of_lt hq)
  have h := gap3 x hx
  field_simp [hsne] at h
  rw [hs2] at h
  linarith [h]

private theorem contDiffAt_f (x : ℝ) (hx : |x| < 1) :
    ContDiffAt ℝ ⊤ f x := by
  have hx' : x ∈ Set.Ioo (-1 : ℝ) 1 := abs_lt.mp hx
  simpa [f] using
    (Real.contDiffAt_arcsin (ne_of_gt hx'.1) (ne_of_lt hx'.2) :
      ContDiffAt ℝ ⊤ Real.arcsin x).pow 2

private theorem contDiffAt_iterDeriv (n : ℕ) (x : ℝ) (hx : |x| < 1) :
    ContDiffAt ℝ ⊤ (iterDeriv n f) x := by
  induction n with
  | zero => simpa [iterDeriv] using contDiffAt_f x hx
  | succ n ih =>
      have hder := ih.derivWithin (m := ⊤) (by simp)
      simpa [iterDeriv, Function.iterate_succ_apply'] using hder

private theorem hasDerivAt_iterDeriv (n : ℕ) (x : ℝ) (hx : |x| < 1) :
    HasDerivAt (iterDeriv n f) (iterDeriv (n + 1) f x) x := by
  have hdiff :=
    (contDiffAt_iterDeriv n x hx).differentiableAt (by simp)
  simpa [iterDeriv, Function.iterate_succ_apply'] using hdiff.hasDerivAt

private theorem recurrence_base (x : ℝ) (hx : |x| < 1) :
    recurrenceExpr 1 x = 0 := by
  have hx' : x ∈ Set.Ioo (-1 : ℝ) 1 := abs_lt.mp hx
  have hpoly :
      HasDerivAt (fun y : ℝ => 1 - y ^ 2) (-2 * x) x := by
    convert (hasDerivAt_const x (1 : ℝ)).sub ((hasDerivAt_id x).pow 2) using 1 <;>
      simp <;> ring
  have hder :
      HasDerivAt
        (fun y : ℝ =>
          (1 - y ^ 2) * iterDeriv 2 f y -
            y * iterDeriv 1 f y - 2)
        (recurrenceExpr 1 x) x := by
    have h :=
      ((hpoly.mul (hasDerivAt_iterDeriv 2 x hx)).sub
        ((hasDerivAt_id x).mul (hasDerivAt_iterDeriv 1 x hx))).sub_const 2
    convert h using 1 <;>
      unfold recurrenceExpr <;>
      norm_num <;> ring
  have heq :
      (fun y : ℝ =>
        (1 - y ^ 2) * iterDeriv 2 f y -
          y * iterDeriv 1 f y - 2) =ᶠ[nhds x]
        (fun _ : ℝ => 0) := by
    filter_upwards [isOpen_Ioo.mem_nhds hx'] with y hy
    simpa using gap4 y (abs_lt.mpr hy)
  have heqder := heq.deriv_eq
  rw [hder.deriv, deriv_const] at heqder
  exact heqder

private theorem recurrence_step (n : ℕ)
    (hrec : ∀ y : ℝ, |y| < 1 → recurrenceExpr n y = 0)
    (x : ℝ) (hx : |x| < 1) :
    recurrenceExpr (n + 1) x = 0 := by
  have hx' : x ∈ Set.Ioo (-1 : ℝ) 1 := abs_lt.mp hx
  have hpoly :
      HasDerivAt (fun y : ℝ => 1 - y ^ 2) (-2 * x) x := by
    convert (hasDerivAt_const x (1 : ℝ)).sub ((hasDerivAt_id x).pow 2) using 1 <;>
      simp <;> ring
  have hder :
      HasDerivAt (recurrenceExpr n) (recurrenceExpr (n + 1) x) x := by
    have hfirst := hpoly.mul (hasDerivAt_iterDeriv (n + 2) x hx)
    have hsecond :=
      ((hasDerivAt_id x).mul (hasDerivAt_iterDeriv (n + 1) x hx)).const_mul
        (2 * (n : ℝ) + 1)
    have hthird :=
      (hasDerivAt_iterDeriv n x hx).const_mul ((n : ℝ) ^ 2)
    have h := (hfirst.sub hsecond).sub hthird
    convert h using 1
    · funext y
      simp [recurrenceExpr]
      ring
    · simp [recurrenceExpr, Nat.cast_add]
      ring
  have heq : recurrenceExpr n =ᶠ[nhds x] (fun _ : ℝ => 0) := by
    filter_upwards [isOpen_Ioo.mem_nhds hx'] with y hy
    exact hrec y (abs_lt.mpr hy)
  have heqder := heq.deriv_eq
  rw [hder.deriv, deriv_const] at heqder
  exact heqder

theorem gap5 (x : ℝ) (n : ℕ) (hx : |x| < 1) (hn : 1 ≤ n) :
    (1 - x ^ 2) * iterDeriv (n + 2) f x -
        2 * (n : ℝ) * x * iterDeriv (n + 1) f x -
        (n : ℝ) * (n - 1 : ℕ) * iterDeriv n f x -
        x * iterDeriv (n + 1) f x -
        (n : ℝ) * iterDeriv n f x = 0 := by
  have hall :
      ∀ m : ℕ, 1 ≤ m →
        ∀ y : ℝ, |y| < 1 → recurrenceExpr m y = 0 := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
        intro hm y hy
        by_cases hm1 : m = 1
        · subst m
          exact recurrence_base y hy
        · have hpredlt : m - 1 < m := by omega
          have hpredpos : 1 ≤ m - 1 := by omega
          have hmform : m = (m - 1) + 1 := by omega
          rw [hmform]
          exact recurrence_step (m - 1)
            (fun z hz => ih (m - 1) hpredlt hpredpos z hz) y hy
  have hr := hall n hn x hx
  unfold recurrenceExpr at hr
  rw [Nat.cast_sub hn]
  norm_num
  ring_nf at hr ⊢
  exact hr

theorem gap6 (n : ℕ) (hn : 1 ≤ n) :
    iterDeriv (n + 2) f 0 - (n : ℝ) ^ 2 * iterDeriv n f 0 = 0 := by
  have h := gap5 0 n (by norm_num) hn
  rw [Nat.cast_sub hn] at h
  norm_num at h
  ring_nf at h ⊢
  exact h

private theorem recurrenceProduct_succ (k : ℕ) (hk : 1 ≤ k) :
    recurrenceProduct (k + 1) =
      (2 * (k : ℝ)) ^ 2 * recurrenceProduct k := by
  unfold recurrenceProduct
  rw [Nat.add_sub_cancel]
  conv_lhs =>
    rw [show k = (k - 1) + 1 by omega, Finset.prod_range_succ]
  have hkcast : ((k - 1 : ℕ) : ℝ) + 1 = (k : ℝ) := by
    exact_mod_cast Nat.sub_add_cancel hk
  rw [hkcast]
  ring

private theorem closedForm_succ (k : ℕ) (hk : 1 ≤ k) :
    closedForm (k + 1) = (2 * (k : ℝ)) ^ 2 * closedForm k := by
  unfold closedForm
  rw [show 2 * (k + 1) - 1 = (2 * k - 1) + 2 by omega, pow_add]
  norm_num
  rw [show k = (k - 1) + 1 by omega, Nat.factorial_succ]
  push_cast
  ring

theorem gap7 (k : ℕ) (hk : 1 ≤ k) :
    iterDeriv (2 * k - 1) f 0 = 0 := by
  have hbase : iterDeriv 1 f 0 = 0 := by
    simpa [iterDeriv] using gap1 0 (by norm_num)
  induction k with
  | zero => omega
  | succ k ih =>
      by_cases hk0 : k = 0
      · subst k
        simpa using hbase
      · have hkpos : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk0
        have ih' := ih hkpos
        have hrec := gap6 (2 * k - 1) (by omega)
        rw [ih'] at hrec
        have hzero : iterDeriv ((2 * k - 1) + 2) f 0 = 0 := by
          nlinarith
        have hindex : 2 * (k + 1) - 1 = (2 * k - 1) + 2 := by omega
        simpa [hindex] using hzero

theorem gap8 (k : ℕ) (hk : 1 ≤ k) :
    iterDeriv (2 * k) f 0 = recurrenceProduct k := by
  induction k with
  | zero => omega
  | succ k ih =>
      by_cases hk0 : k = 0
      · subst k
        simp [recurrenceProduct]
      · have hkpos : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk0
        have ih' := ih hkpos
        have hrec := gap6 (2 * k) (by omega)
        have hp := recurrenceProduct_succ k hkpos
        rw [ih'] at hrec
        rw [hp]
        have hindex : 2 * (k + 1) = 2 * k + 2 := by omega
        rw [hindex]
        have hcast : ((2 * k : ℕ) : ℝ) = 2 * (k : ℝ) := by
          norm_num
        rw [hcast] at hrec
        nlinarith

theorem gap9 (k : ℕ) (hk : 1 ≤ k) :
    recurrenceProduct k = closedForm k := by
  have hsecond : iterDeriv 2 f 0 = 2 := by
    have h := gap4 0 (by norm_num)
    norm_num at h
    linarith
  induction k with
  | zero => omega
  | succ k ih =>
      by_cases hk0 : k = 0
      · subst k
        simp [recurrenceProduct, closedForm, hsecond]
      · have hkpos : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk0
        rw [recurrenceProduct_succ k hkpos, closedForm_succ k hkpos,
          ih hkpos]

theorem gap10 (k : ℕ) (hk : 1 ≤ k) :
    iterDeriv (2 * k) f 0 = closedForm k := by
  calc
    iterDeriv (2 * k) f 0 = recurrenceProduct k := gap8 k hk
    _ = closedForm k := gap9 k hk

end

end ProofGap.Exercise1222_2
