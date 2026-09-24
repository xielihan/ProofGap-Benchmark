import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.PSeries

namespace ProofGap.Exercise2619

noncomputable section

open Filter Set

def integrand (p x : ℝ) : ℝ :=
  1 / (x * Real.rpow (Real.log x) p)

def term (p : ℝ) (n : ℕ) : ℝ :=
  integrand p n

def primitive (p x : ℝ) : ℝ :=
  if p = 1 then Real.log (Real.log x)
  else Real.rpow (Real.log x) (1 - p) / (1 - p)

def converges (p : ℝ) : Prop :=
  Summable (fun n : ℕ => term p (n + 2))

theorem gap1 (p x : ℝ) (hx : 2 ≤ x) :
    0 < integrand p x := by
  unfold integrand
  have hxpos : 0 < x := by linarith
  have hlogpos : 0 < Real.log x := Real.log_pos (by linarith)
  exact one_div_pos.mpr (mul_pos hxpos (Real.rpow_pos_of_pos hlogpos _))

private def logExponent (p t : ℝ) : ℝ :=
  -t - p * Real.log t

private theorem integrand_eq_exp_logExponent (p x : ℝ) (hx : 1 < x) :
    integrand p x = Real.exp (logExponent p (Real.log x)) := by
  have hxpos : 0 < x := by linarith
  have hlogpos : 0 < Real.log x := Real.log_pos hx
  have hrpow : Real.rpow (Real.log x) p =
      Real.exp (Real.log (Real.log x) * p) := by
    change (Real.log x) ^ p = Real.exp (Real.log (Real.log x) * p)
    exact Real.rpow_def_of_pos hlogpos _
  unfold integrand logExponent
  rw [hrpow]
  have hxinv : x⁻¹ = Real.exp (-Real.log x) := by
    rw [Real.exp_neg, Real.exp_log hxpos]
  simp only [one_div, mul_inv]
  rw [hxinv, ← Real.exp_neg, ← Real.exp_add]
  congr 1
  ring

theorem gap2 (p : ℝ) :
    ∃ A ≥ 2, AntitoneOn (integrand p) (Ici A) := by
  let B : ℝ := max 1 (-p)
  let A : ℝ := Real.exp B
  have hB1 : 1 ≤ B := le_max_left _ _
  have hA2 : 2 ≤ A := by
    exact (le_of_lt Real.exp_one_gt_two).trans
      (Real.exp_le_exp.mpr hB1)
  have hlogExponent : AntitoneOn (logExponent p) (Ici B) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos
      (f' := fun t => -1 - p * (1 / t)) (convex_Ici B)
    · intro t ht
      have htpos : 0 < t := lt_of_lt_of_le zero_lt_one
        (hB1.trans (Set.mem_Ici.mp ht))
      exact (continuousAt_id.neg.sub
        (continuousAt_const.mul
          (Real.continuousAt_log htpos.ne'))).continuousWithinAt
    · intro t ht
      have htB : B < t := by simpa [interior_Ici] using ht
      have htpos : 0 < t := lt_of_lt_of_le zero_lt_one (hB1.trans htB.le)
      unfold logExponent
      convert ((hasDerivAt_id t).neg.sub
        ((Real.hasDerivAt_log htpos.ne').const_mul p)).hasDerivWithinAt using 1 <;>
        ring
    · intro t ht
      have htB : B < t := by simpa [interior_Ici] using ht
      have htpos : 0 < t := lt_of_lt_of_le zero_lt_one (hB1.trans htB.le)
      have htp : 0 ≤ t + p := by
        have : -p ≤ t := (le_max_right 1 (-p)).trans htB.le
        linarith
      have hfrac : 0 ≤ 1 + p / t := by
        rw [show 1 + p / t = (t + p) / t by field_simp [htpos.ne']]
        exact div_nonneg htp htpos.le
      rw [show -1 - p * (1 / t) = -(1 + p / t) by ring]
      exact neg_nonpos.mpr hfrac
  refine ⟨A, hA2, ?_⟩
  intro x hx y hy hxy
  have hAx : A ≤ x := Set.mem_Ici.mp hx
  have hAy : A ≤ y := Set.mem_Ici.mp hy
  have hxpos : 0 < x := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2)
    (hA2.trans hAx)
  have hypos : 0 < y := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2)
    (hA2.trans hAy)
  have hlogxB : B ≤ Real.log x := by
    exact (Real.le_log_iff_exp_le hxpos).2 hAx
  have hlogyB : B ≤ Real.log y := by
    exact (Real.le_log_iff_exp_le hypos).2 hAy
  have hlogxy : Real.log x ≤ Real.log y :=
    Real.strictMonoOn_log.monotoneOn (Set.mem_Ioi.mpr hxpos)
      (Set.mem_Ioi.mpr hypos) hxy
  have hx1 : 1 < x := lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2)
    (hA2.trans hAx)
  have hy1 : 1 < y := lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2)
    (hA2.trans hAy)
  rw [integrand_eq_exp_logExponent p x hx1,
    integrand_eq_exp_logExponent p y hy1]
  exact Real.exp_le_exp.mpr
    (hlogExponent hlogxB hlogyB hlogxy)

theorem gap3 (p x : ℝ) (hx : 1 < x) :
    HasDerivAt (primitive p) (integrand p x) x := by
  have hxpos : 0 < x := by linarith
  have hlogpos : 0 < Real.log x := Real.log_pos hx
  by_cases hp : p = 1
  · subst p
    have h := (Real.hasDerivAt_log hxpos.ne').log hlogpos.ne'
    convert h using 1
    · funext y
      simp [primitive]
    · unfold integrand
      have hrone : Real.rpow (Real.log x) 1 = Real.log x := by
        change (Real.log x) ^ (1 : ℝ) = Real.log x
        exact Real.rpow_one _
      rw [hrone]
      field_simp [hxpos.ne', hlogpos.ne']
  · have hr := (Real.hasDerivAt_log hxpos.ne').rpow_const
      (p := 1 - p) (Or.inl hlogpos.ne')
    have hdiv := hr.div_const (1 - p)
    convert hdiv using 1
    · funext y
      simp [primitive, hp]
    · unfold integrand
      have hpowrel : (Real.log x) ^ (1 - p - 1) =
          ((Real.log x) ^ p)⁻¹ := by
        rw [show 1 - p - 1 = -p by ring]
        exact Real.rpow_neg hlogpos.le p
      rw [hpowrel]
      have hp1 : 1 - p ≠ 0 := sub_ne_zero.mpr (Ne.symm hp)
      have hrp : Real.rpow (Real.log x) p ≠ 0 :=
        (Real.rpow_pos_of_pos hlogpos p).ne'
      field_simp [hp1, hxpos.ne', hrp]
      change Real.rpow (Real.log x) p = Real.rpow (Real.log x) p
      rfl

private theorem condensed_integrand_eq (p : ℝ) (k : ℕ) :
    (2 : ℝ) ^ k * integrand p (((2 ^ k : ℕ) : ℝ)) =
      Real.rpow (Real.log 2) (-p) * Real.rpow k (-p) := by
  by_cases hk : k = 0
  · subst k
    simp only [pow_zero, Nat.cast_one, Real.log_one, one_mul, integrand]
    by_cases hp : p = 0
    · subst p
      norm_num
    · have hz : Real.rpow 0 p = 0 := by
        change (0 : ℝ) ^ p = 0
        exact Real.zero_rpow hp
      have hzn : Real.rpow 0 (-p) = 0 := by
        change (0 : ℝ) ^ (-p) = 0
        exact Real.zero_rpow (neg_ne_zero.mpr hp)
      rw [hz]
      norm_num only [Nat.cast_zero]
      rw [hzn]
      norm_num
  · have hkpos : (0 : ℝ) < k := by exact_mod_cast Nat.pos_of_ne_zero hk
    have htwoPowPos : (0 : ℝ) < (2 : ℝ) ^ k := pow_pos (by norm_num) _
    have hlog2pos : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
    have hbasepos : 0 < (k : ℝ) * Real.log 2 := mul_pos hkpos hlog2pos
    have hrp : Real.rpow ((k : ℝ) * Real.log 2) p ≠ 0 :=
      (Real.rpow_pos_of_pos hbasepos p).ne'
    unfold integrand
    push_cast
    rw [Real.log_pow]
    calc
      (2 : ℝ) ^ k *
          (1 / ((2 : ℝ) ^ k * Real.rpow ((k : ℝ) * Real.log 2) p)) =
          1 / Real.rpow ((k : ℝ) * Real.log 2) p := by
        field_simp [htwoPowPos.ne', hrp]
      _ = Real.rpow ((k : ℝ) * Real.log 2) (-p) := by
        have hneg : Real.rpow ((k : ℝ) * Real.log 2) (-p) =
            (Real.rpow ((k : ℝ) * Real.log 2) p)⁻¹ := by
          change (((k : ℝ) * Real.log 2) ^ (-p)) =
            ((((k : ℝ) * Real.log 2) ^ p))⁻¹
          exact Real.rpow_neg hbasepos.le p
        rw [hneg]
        simp only [one_div]
      _ = Real.rpow k (-p) * Real.rpow (Real.log 2) (-p) := by
        change (((k : ℝ) * Real.log 2) ^ (-p)) =
          (k : ℝ) ^ (-p) * (Real.log 2) ^ (-p)
        exact Real.mul_rpow hkpos.le hlog2pos.le
      _ = Real.rpow (Real.log 2) (-p) * Real.rpow k (-p) := by ring

theorem gap4 (p : ℝ) :
    converges p ↔ 1 < p := by
  have hnonneg : 0 ≤ᶠ[atTop] (fun n : ℕ => integrand p n) := by
    filter_upwards [eventually_ge_atTop 2] with n hn
    exact (gap1 p n (by exact_mod_cast hn)).le
  rcases gap2 p with ⟨A, hA2, hanti⟩
  have hmono : ∀ᶠ n : ℕ in atTop,
      integrand p (((n + 1 : ℕ) : ℝ)) ≤ integrand p (n : ℝ) := by
    filter_upwards [eventually_ge_atTop ⌈A⌉₊] with n hn
    have hAn : A ≤ (n : ℝ) :=
      (Nat.le_ceil A).trans (Nat.cast_le.mpr hn)
    have hAn1 : A ≤ ((n + 1 : ℕ) : ℝ) :=
      hAn.trans (by exact_mod_cast Nat.le_succ n)
    exact hanti (Set.mem_Ici.mpr hAn) (Set.mem_Ici.mpr hAn1)
      (by exact_mod_cast Nat.le_succ n)
  have hcondiff := summable_condensed_iff_of_eventually_nonneg hnonneg hmono
  have hC : Real.rpow (Real.log 2) (-p) ≠ 0 :=
    (Real.rpow_pos_of_pos (Real.log_pos (by norm_num)) _).ne'
  constructor
  · intro hshift
    unfold converges term at hshift
    have hall : Summable (fun n : ℕ => integrand p (n : ℝ)) :=
      (summable_nat_add_iff 2).mp hshift
    have hcondensed : Summable (fun k : ℕ =>
        (2 : ℝ) ^ k * integrand p (((2 ^ k : ℕ) : ℝ))) := hcondiff.mpr hall
    have hc : Summable (fun k : ℕ =>
        Real.rpow (Real.log 2) (-p) * Real.rpow k (-p)) := by
      exact hcondensed.congr (fun k => condensed_integrand_eq p k)
    have hrpow : Summable (fun k : ℕ => Real.rpow k (-p)) :=
      (summable_mul_left_iff hC).mp hc
    have hexponent := Real.summable_nat_rpow.mp hrpow
    linarith
  · intro hp
    have hrpow : Summable (fun k : ℕ => Real.rpow k (-p)) :=
      Real.summable_nat_rpow.mpr (by linarith)
    have hc : Summable (fun k : ℕ =>
        Real.rpow (Real.log 2) (-p) * Real.rpow k (-p)) := hrpow.mul_left _
    have hcondensed : Summable (fun k : ℕ =>
        (2 : ℝ) ^ k * integrand p (((2 ^ k : ℕ) : ℝ))) := by
      exact hc.congr (fun k => (condensed_integrand_eq p k).symm)
    have hall : Summable (fun n : ℕ => integrand p n) := hcondiff.mp hcondensed
    unfold converges term
    have hshift : Summable (fun n : ℕ => integrand p (((n + 2 : ℕ) : ℝ))) :=
      (summable_nat_add_iff 2).mpr hall
    exact hshift

theorem gap5 (p : ℝ) :
    p ∈ {r : ℝ | 1 < r} ↔
      Summable (fun n : ℕ => term p (n + 2)) := by
  change 1 < p ↔ converges p
  exact (gap4 p).symm

end

end ProofGap.Exercise2619
