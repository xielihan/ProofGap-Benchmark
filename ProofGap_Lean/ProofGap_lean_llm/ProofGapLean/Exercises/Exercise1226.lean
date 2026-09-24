import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv

namespace ProofGap.Exercise1226

noncomputable section

def iterDeriv (n : ℕ) (f : ℝ → ℝ) : ℝ → ℝ := (deriv^[n]) f
def T (m : ℕ) (x : ℝ) : ℝ :=
  1 / (2 : ℝ) ^ (m - 1) * Real.cos ((m : ℝ) * Real.arccos x)

theorem gap1 (m : ℕ) (x : ℝ) (hm : 1 ≤ m) (hx : |x| < 1) :
    deriv (T m) x =
      (m : ℝ) / ((2 : ℝ) ^ (m - 1) * Real.sqrt (1 - x ^ 2)) *
        Real.sin ((m : ℝ) * Real.arccos x) := by
  have hxm : x ≠ -1 := by
    intro h
    subst x
    norm_num at hx
  have hxp : x ≠ 1 := by
    intro h
    subst x
    norm_num at hx
  have ha := Real.hasDerivAt_arccos hxm hxp
  have hu := ha.const_mul (m : ℝ)
  have hc := (Real.hasDerivAt_cos ((m : ℝ) * Real.arccos x)).comp x hu
  have ht := hc.const_mul (1 / (2 : ℝ) ^ (m - 1))
  rw [show T m = fun y =>
      1 / (2 : ℝ) ^ (m - 1) * Real.cos ((m : ℝ) * Real.arccos y) by
    rfl]
  convert ht.deriv using 1 <;> ring

theorem gap2 (m : ℕ) (x : ℝ) (hm : 1 ≤ m) (hx : |x| < 1) :
    iterDeriv 2 (T m) x =
      -(m : ℝ) ^ 2 / ((2 : ℝ) ^ (m - 1) * (1 - x ^ 2)) *
          Real.cos ((m : ℝ) * Real.arccos x) +
        (m : ℝ) * x / ((2 : ℝ) ^ (m - 1) * Real.sqrt (1 - x ^ 2) ^ 3) *
          Real.sin ((m : ℝ) * Real.arccos x) := by
  let g : ℝ → ℝ := fun y =>
    (m : ℝ) / ((2 : ℝ) ^ (m - 1) * Real.sqrt (1 - y ^ 2)) *
      Real.sin ((m : ℝ) * Real.arccos y)
  have hev : deriv (T m) =ᶠ[nhds x] g := by
    have hevent : ∀ᶠ y : ℝ in nhds x, |y| < 1 :=
      (continuous_abs.tendsto x).eventually (eventually_lt_nhds hx)
    filter_upwards [hevent] with y hy
    exact gap1 m y hm hy
  have hspos : 0 < 1 - x ^ 2 := by
    have habs := abs_lt.mp hx
    nlinarith
  have hsne : 1 - x ^ 2 ≠ 0 := ne_of_gt hspos
  have hsqrt : Real.sqrt (1 - x ^ 2) ≠ 0 :=
    Real.sqrt_ne_zero'.mpr hspos
  have ha := Real.hasDerivAt_arccos (x := x)
    (by intro h; subst x; norm_num at hx)
    (by intro h; subst x; norm_num at hx)
  have hu := ha.const_mul (m : ℝ)
  have hsin :=
    (Real.hasDerivAt_sin ((m : ℝ) * Real.arccos x)).comp x hu
  have hs : HasDerivAt (fun y : ℝ => 1 - y ^ 2) (-2 * x) x := by
    convert (hasDerivAt_const x (1 : ℝ)).sub ((hasDerivAt_id x).pow 2) using 1 <;>
      simp [id] <;> ring
  have hroot := (Real.hasDerivAt_sqrt hsne).comp x hs
  have hden := hroot.const_mul ((2 : ℝ) ^ (m - 1))
  have hquot := (hasDerivAt_const x (m : ℝ)).div hden
    (mul_ne_zero (by positivity) hsqrt)
  have hg := hquot.mul hsin
  change HasDerivAt g _ x at hg
  rw [show iterDeriv 2 (T m) x = deriv (deriv (T m)) x by
    simp [iterDeriv, Function.iterate_succ_apply']]
  rw [Filter.EventuallyEq.deriv_eq hev]
  change deriv g x = _
  rw [hg.deriv]
  dsimp [g]
  have hsqrt_sq : Real.sqrt (1 - x ^ 2) ^ 2 = 1 - x ^ 2 :=
    Real.sq_sqrt (le_of_lt hspos)
  have hsqrt_cube :
      Real.sqrt (1 - x ^ 2) ^ 3 =
        Real.sqrt (1 - x ^ 2) * (1 - x ^ 2) := by
    rw [pow_succ, hsqrt_sq]
    ring
  field_simp [hsne, hsqrt]
  rw [hsqrt_sq, hsqrt_cube]
  ring

theorem gap3 (m : ℕ) (x : ℝ) (hm : 1 ≤ m) (hx : |x| < 1) :
    (1 - x ^ 2) * iterDeriv 2 (T m) x =
      -(m : ℝ) ^ 2 / (2 : ℝ) ^ (m - 1) *
          Real.cos ((m : ℝ) * Real.arccos x) +
        (m : ℝ) * x / ((2 : ℝ) ^ (m - 1) * Real.sqrt (1 - x ^ 2)) *
          Real.sin ((m : ℝ) * Real.arccos x) := by
  rw [gap2 m x hm hx]
  have hspos : 0 < 1 - x ^ 2 := by
    have habs := abs_lt.mp hx
    nlinarith
  have hsne : 1 - x ^ 2 ≠ 0 := ne_of_gt hspos
  have hsqrt : Real.sqrt (1 - x ^ 2) ≠ 0 :=
    Real.sqrt_ne_zero'.mpr hspos
  have hsqrt_sq : Real.sqrt (1 - x ^ 2) ^ 2 = 1 - x ^ 2 :=
    Real.sq_sqrt (le_of_lt hspos)
  have hsqrt_cube :
      Real.sqrt (1 - x ^ 2) ^ 3 =
        Real.sqrt (1 - x ^ 2) * (1 - x ^ 2) := by
    rw [pow_succ, hsqrt_sq]
    ring
  field_simp [hsne, hsqrt]
  rw [hsqrt_sq, hsqrt_cube]
  ring

theorem gap4 (m : ℕ) (x : ℝ) (hm : 1 ≤ m) (hx : |x| < 1) :
    -(m : ℝ) ^ 2 / (2 : ℝ) ^ (m - 1) *
          Real.cos ((m : ℝ) * Real.arccos x) +
        (m : ℝ) * x / ((2 : ℝ) ^ (m - 1) * Real.sqrt (1 - x ^ 2)) *
          Real.sin ((m : ℝ) * Real.arccos x) =
      -(m : ℝ) ^ 2 * T m x + x * deriv (T m) x := by
  rw [gap1 m x hm hx]
  simp only [T]
  ring

theorem gap5 (m : ℕ) (x : ℝ) (hm : 1 ≤ m) (hx : |x| < 1) :
    (1 - x ^ 2) * iterDeriv 2 (T m) x =
      -(m : ℝ) ^ 2 * T m x + x * deriv (T m) x := by
  rw [gap3 m x hm hx, gap4 m x hm hx]

theorem gap6 (m : ℕ) (x : ℝ) (hm : 1 ≤ m) (hx : |x| < 1) :
    (1 - x ^ 2) * iterDeriv 2 (T m) x -
        x * deriv (T m) x + (m : ℝ) ^ 2 * T m x = 0 := by
  rw [gap5 m x hm hx]
  ring

theorem gap7 (m : ℕ) (x : ℝ) (hm : 1 ≤ m) (hx : |x| < 1) :
    (1 - x ^ 2) * iterDeriv 2 (T m) x -
        x * deriv (T m) x + (m : ℝ) ^ 2 * T m x = 0 := by
  exact gap6 m x hm hx

end

end ProofGap.Exercise1226
