import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Neighborhoods
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

namespace ProofGap.Exercise1420_1

noncomputable section

open scoped BigOperators

def y (n : ℕ) (x : ℝ) : ℝ :=
  (∑ k ∈ Finset.range (n + 1), x ^ k / (Nat.factorial k : ℝ)) * Real.exp (-x)

private theorem hasDerivAt_pow_succ_aux (n : ℕ) (x : ℝ) :
    HasDerivAt (fun t : ℝ => t ^ (n + 1))
      (((n + 1 : ℕ) : ℝ) * x ^ n) x := by
  induction n with
  | zero =>
      simpa using hasDerivAt_id x
  | succ n ih =>
      convert ih.mul (hasDerivAt_id x) using 1 <;>
        simp [pow_succ] <;> ring

private theorem hasDerivAt_y_aux (n : ℕ) (x : ℝ) :
    HasDerivAt (y n)
      (-(1 / (Nat.factorial n : ℝ)) * Real.exp (-x) * x ^ n) x := by
  induction n with
  | zero =>
      have hexp :
          HasDerivAt (fun t : ℝ => Real.exp (-t)) (-Real.exp (-x)) x := by
        convert (Real.hasDerivAt_exp (-x)).comp x (hasDerivAt_id x).neg using 1 <;> ring
      have hy0 : y 0 = fun t : ℝ => Real.exp (-t) := by
        funext t
        simp [y]
      rw [hy0]
      simpa using hexp
  | succ n ih =>
      have hpow :
          HasDerivAt
            (fun t : ℝ => t ^ (n + 1) / (Nat.factorial (n + 1) : ℝ))
            (((n + 1 : ℕ) : ℝ) * x ^ n /
              (Nat.factorial (n + 1) : ℝ)) x := by
        simpa using
          ((hasDerivAt_pow_succ_aux n x).div_const
            (Nat.factorial (n + 1) : ℝ))
      have hexp :
          HasDerivAt (fun t : ℝ => Real.exp (-t)) (-Real.exp (-x)) x := by
        convert (Real.hasDerivAt_exp (-x)).comp x (hasDerivAt_id x).neg using 1 <;> ring
      have hfun :
          y (n + 1) =
            fun t : ℝ => y n t +
              (t ^ (n + 1) / (Nat.factorial (n + 1) : ℝ)) * Real.exp (-t) := by
        funext t
        simp [y, Finset.sum_range_succ]
        <;> ring
      have hfac : (Nat.factorial n : ℝ) ≠ 0 := by positivity
      have hn1 : (n : ℝ) + 1 ≠ 0 := by positivity
      rw [hfun]
      convert ih.add (hpow.mul hexp) using 1
      simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
      field_simp [hfac, hn1]
      <;> ring

theorem gap1 (n : ℕ) (hn : 0 < n) (heven : Even n) (x : ℝ) :
    deriv (y n) x =
      -(1 / (Nat.factorial n : ℝ)) * Real.exp (-x) * x ^ n := by
  exact (hasDerivAt_y_aux n x).deriv

theorem gap2 (n : ℕ) (hn : 0 < n) (heven : Even n) (x : ℝ)
    (hcrit : deriv (y n) x = 0) :
    x = 0 := by
  rw [gap1 n hn heven x] at hcrit
  have hfac : (Nat.factorial n : ℝ) ≠ 0 := by
    positivity
  have hleft : -(1 / (Nat.factorial n : ℝ)) * Real.exp (-x) ≠ 0 := by
    exact mul_ne_zero
      (neg_ne_zero.mpr (div_ne_zero one_ne_zero hfac))
      (ne_of_gt (Real.exp_pos (-x)))
  have hxpow : x ^ n = 0 :=
    (mul_eq_zero.mp hcrit).resolve_left hleft
  exact eq_zero_of_pow_eq_zero hxpow

theorem gap3 (n : ℕ) (hn : 0 < n) (heven : Even n) (x : ℝ)
    (hx : x ≠ 0) :
    deriv (y n) x < 0 := by
  rw [gap1 n hn heven x]
  have hxpow : 0 < x ^ n := by
    rcases heven with ⟨m, rfl⟩
    rw [pow_add]
    exact mul_self_pos.mpr (pow_ne_zero m hx)
  have hfacpos : 0 < (Nat.factorial n : ℝ) := by
    positivity
  have hquotpos : 0 < 1 / (Nat.factorial n : ℝ) :=
    one_div_pos.mpr hfacpos
  have hcoeff : -(1 / (Nat.factorial n : ℝ)) < 0 :=
    neg_lt_zero.mpr hquotpos
  exact mul_neg_of_neg_of_pos
    (mul_neg_of_neg_of_pos hcoeff (Real.exp_pos (-x))) hxpow

theorem gap4 (n : ℕ) (hn : 0 < n) (heven : Even n) :
    ¬ IsLocalMax (y n) 0 ∧ ¬ IsLocalMin (y n) 0 := by
  have hnegdiff : Differentiable ℝ (fun z : ℝ => -(y n z)) := fun z =>
    (hasDerivAt_y_aux n z).neg.differentiableAt
  have hleftMono : StrictMonoOn (fun z : ℝ => -(y n z)) (Set.Iic 0) := by
    refine strictMonoOn_of_deriv_pos (convex_Iic (0 : ℝ))
      hnegdiff.continuous.continuousOn ?_
    intro z hz
    have hzneg : z < 0 := by
      rw [interior_Iic] at hz
      exact hz
    have hyneg : deriv (y n) z < 0 :=
      gap3 n hn heven z (ne_of_lt hzneg)
    have hnegderiv :
        deriv (fun w : ℝ => -(y n w)) z = -deriv (y n) z := by
      have hyhas : HasDerivAt (y n) (deriv (y n) z) z :=
        (hasDerivAt_y_aux n z).differentiableAt.hasDerivAt
      change deriv (-(y n)) z = -deriv (y n) z
      exact hyhas.neg.deriv
    rw [hnegderiv]
    exact neg_pos.mpr hyneg
  have hrightMono : StrictMonoOn (fun z : ℝ => -(y n z)) (Set.Ici 0) := by
    refine strictMonoOn_of_deriv_pos (convex_Ici (0 : ℝ))
      hnegdiff.continuous.continuousOn ?_
    intro z hz
    have hzpos : 0 < z := by
      rw [interior_Ici] at hz
      exact hz
    have hyneg : deriv (y n) z < 0 :=
      gap3 n hn heven z (ne_of_gt hzpos)
    have hnegderiv :
        deriv (fun w : ℝ => -(y n w)) z = -deriv (y n) z := by
      have hyhas : HasDerivAt (y n) (deriv (y n) z) z :=
        (hasDerivAt_y_aux n z).differentiableAt.hasDerivAt
      change deriv (-(y n)) z = -deriv (y n) z
      exact hyhas.neg.deriv
    rw [hnegderiv]
    exact neg_pos.mpr hyneg
  have hleft : StrictAntiOn (y n) (Set.Iic 0) := by
    intro a ha b hb hab
    have hm := hleftMono ha hb hab
    dsimp only at hm
    linarith
  have hright : StrictAntiOn (y n) (Set.Ici 0) := by
    intro a ha b hb hab
    have hm := hrightMono ha hb hab
    dsimp only at hm
    linarith
  constructor
  · intro hmax
    change ∀ᶠ z in nhds (0 : ℝ), y n z ≤ y n 0 at hmax
    rcases Metric.eventually_nhds_iff.mp hmax with ⟨ε, hε, hmax⟩
    let z : ℝ := -(ε / 2)
    have hzneg : z < 0 := by
      dsimp [z]
      linarith
    have hzdist : dist z 0 < ε := by
      have hhalf : ε / 2 < ε := by linarith
      simpa [Real.dist_eq, z, abs_of_pos hε] using hhalf
    have hzle : y n z ≤ y n 0 := hmax hzdist
    have hzlt : y n 0 < y n z :=
      hleft (le_of_lt hzneg) (by simp) hzneg
    exact (not_lt_of_ge hzle) hzlt
  · intro hmin
    change ∀ᶠ z in nhds (0 : ℝ), y n 0 ≤ y n z at hmin
    rcases Metric.eventually_nhds_iff.mp hmin with ⟨ε, hε, hmin⟩
    let z : ℝ := ε / 2
    have hzpos : 0 < z := by
      dsimp [z]
      linarith
    have hzdist : dist z 0 < ε := by
      have hhalf : ε / 2 < ε := by linarith
      simpa [Real.dist_eq, z, abs_of_pos hε] using hhalf
    have hzge : y n 0 ≤ y n z := hmin hzdist
    have hzlt : y n z < y n 0 :=
      hright (by simp) (le_of_lt hzpos) hzpos
    exact (not_lt_of_ge hzge) hzlt

end
end ProofGap.Exercise1420_1
