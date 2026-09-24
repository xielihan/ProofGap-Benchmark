import ProofGapLean.Prelude.Analysis
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.Calculus.Deriv.Basic

open Set
open scoped Interval

namespace ProofGap.Exercise2479

noncomputable section

def realDomain : Set ℝ := {x | 0 ≤ x ∧ 0 ≤ Real.sin x}

def componentIntegral (n : ℕ) : ℝ :=
  ∫ x in (2 * (n : ℝ) * Real.pi)..((2 * (n : ℝ) + 1) * Real.pi),
    Real.exp (-2 * x) * Real.sin x

def volume : ℝ := Real.pi * ∑' n : ℕ, componentIntegral n

def primitive (x : ℝ) : ℝ :=
  Real.pi / 5 * Real.exp (-2 * x) * (-2 * Real.sin x - Real.cos x)

private lemma trig_add_nat_period (x : ℝ) (n : ℕ) :
    Real.sin (x + (n : ℝ) * (2 * Real.pi)) = Real.sin x ∧
      Real.cos (x + (n : ℝ) * (2 * Real.pi)) = Real.cos x := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Nat.cast_succ]
      rw [show x + ((n : ℝ) + 1) * (2 * Real.pi) =
          (x + (n : ℝ) * (2 * Real.pi)) + 2 * Real.pi by ring]
      rw [Real.sin_add, Real.cos_add]
      simp [ih.1, ih.2]

private lemma primitive_hasDerivAt (x : ℝ) :
    HasDerivAt primitive
      (Real.pi * (Real.exp (-2 * x) * Real.sin x)) x := by
  have he : HasDerivAt (fun y : ℝ => Real.exp (-2 * y))
      (-2 * Real.exp (-2 * x)) x := by
    convert (Real.hasDerivAt_exp (-2 * x)).comp x
      ((hasDerivAt_id x).const_mul (-2)) using 1 <;> ring
  have hg : HasDerivAt
      (fun y : ℝ => -2 * Real.sin y - Real.cos y)
      (-2 * Real.cos x + Real.sin x) x := by
    convert ((Real.hasDerivAt_sin x).const_mul (-2)).sub
      (Real.hasDerivAt_cos x) using 1 <;> ring
  unfold primitive
  convert (he.mul hg).const_mul (Real.pi / 5) using 1 <;>
    first
    | (funext y; simp only [Pi.mul_apply]; ring)
    | ring

private lemma integral_eq_primitive_sub (a b : ℝ) :
    Real.pi *
        (∫ x in a..b, Real.exp (-2 * x) * Real.sin x) =
      primitive b - primitive a := by
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => primitive_hasDerivAt x)
  have hc : Continuous (fun x : ℝ =>
      Real.pi * (Real.exp (-2 * x) * Real.sin x)) :=
    continuous_const.mul
      ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul
        Real.continuous_sin)
  exact hc.intervalIntegrable a b

private lemma primitive_component_sub (n : ℕ) :
    primitive ((2 * (n : ℝ) + 1) * Real.pi) -
        primitive (2 * (n : ℝ) * Real.pi) =
      Real.pi / 5 * (Real.exp (-2 * Real.pi) + 1) *
        Real.exp (-4 * (n : ℝ) * Real.pi) := by
  have hbase :
      2 * (n : ℝ) * Real.pi = (n : ℝ) * (2 * Real.pi) := by
    ring
  have htop :
      (2 * (n : ℝ) + 1) * Real.pi =
        Real.pi + (n : ℝ) * (2 * Real.pi) := by
    ring
  have he0 :
      Real.exp (-2 * ((n : ℝ) * (2 * Real.pi))) =
        Real.exp (-4 * (n : ℝ) * Real.pi) := by
    congr 1
    ring
  have he1 :
      Real.exp (-2 * (Real.pi + (n : ℝ) * (2 * Real.pi))) =
        Real.exp (-2 * Real.pi) *
          Real.exp (-4 * (n : ℝ) * Real.pi) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hs0 : Real.sin ((n : ℝ) * (2 * Real.pi)) = 0 := by
    simpa using (trig_add_nat_period 0 n).1
  have hc0 : Real.cos ((n : ℝ) * (2 * Real.pi)) = 1 := by
    simpa using (trig_add_nat_period 0 n).2
  have hs1 :
      Real.sin (Real.pi + (n : ℝ) * (2 * Real.pi)) = 0 := by
    simpa using (trig_add_nat_period Real.pi n).1
  have hc1 :
      Real.cos (Real.pi + (n : ℝ) * (2 * Real.pi)) = -1 := by
    simpa using (trig_add_nat_period Real.pi n).2
  unfold primitive
  rw [htop, hbase, he1, he0, hs1, hc1, hs0, hc0]
  ring

theorem gap1 :
    realDomain =
      ⋃ n : ℕ,
        Set.Icc (2 * (n : ℝ) * Real.pi)
          ((2 * (n : ℝ) + 1) * Real.pi) := by
  ext x
  simp only [realDomain, Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_Icc]
  constructor
  · rintro ⟨hx0, hsin⟩
    let P : ℕ → Prop := fun n =>
      x < 2 * ((n : ℝ) + 1) * Real.pi
    have hP : ∃ n, P n := by
      have hden : 0 < 2 * Real.pi := by
        nlinarith [Real.pi_pos]
      obtain ⟨m, hm⟩ := exists_nat_gt (x / (2 * Real.pi))
      refine ⟨m, ?_⟩
      dsimp [P]
      have hm' : x < (m : ℝ) * (2 * Real.pi) :=
        (div_lt_iff₀ hden).mp hm
      nlinarith [Real.pi_pos, (Nat.cast_nonneg m : 0 ≤ (m : ℝ))]
    let n := Nat.find hP
    have hnP : P n := by
      simpa [n] using Nat.find_spec hP
    have hnmin : ∀ m < n, ¬ P m := by
      intro m hm hPm
      have hle : n ≤ m := by
        dsimp [n]
        exact Nat.find_min' hP hPm
      exact (not_le_of_gt hm) hle
    refine ⟨n, ?_, ?_⟩
    · by_cases hn : n = 0
      · simpa [hn] using hx0
      · obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hn
        have hklt : k < n := by
          rw [hk]
          exact Nat.lt_succ_self k
        have hnot : ¬ P k := hnmin k hklt
        have hle := le_of_not_gt hnot
        rw [hk]
        simpa [P, Nat.cast_succ] using hle
    · by_contra hupper
      have hgt : (2 * (n : ℝ) + 1) * Real.pi < x :=
        lt_of_not_ge hupper
      let u : ℝ := x - (2 * (n : ℝ) + 1) * Real.pi
      have hu0 : 0 < u := by
        dsimp [u]
        linarith
      have hupi : u < Real.pi := by
        dsimp [P] at hnP
        dsimp [u]
        nlinarith [Real.pi_pos]
      have husin : 0 < Real.sin u :=
        Real.sin_pos_of_pos_of_lt_pi hu0 hupi
      have hxrepr :
          x = (Real.pi + u) + (n : ℝ) * (2 * Real.pi) := by
        dsimp [u]
        ring
      have hsine : Real.sin x = -Real.sin u := by
        rw [hxrepr, (trig_add_nat_period (Real.pi + u) n).1]
        rw [Real.sin_add]
        simp
      rw [hsine] at hsin
      linarith
  · rintro ⟨n, hlo, hhi⟩
    constructor
    · nlinarith [Real.pi_pos, (Nat.cast_nonneg n : 0 ≤ (n : ℝ))]
    · let u : ℝ := x - 2 * (n : ℝ) * Real.pi
      have hu0 : 0 ≤ u := by
        dsimp [u]
        linarith
      have hupi : u ≤ Real.pi := by
        dsimp [u]
        nlinarith
      have husin : 0 ≤ Real.sin u :=
        Real.sin_nonneg_of_nonneg_of_le_pi hu0 hupi
      have hxrepr : x = u + (n : ℝ) * (2 * Real.pi) := by
        dsimp [u]
        ring
      rw [hxrepr, (trig_add_nat_period u n).1]
      exact husin

theorem gap2 (Vₓ : ℝ) (hV : Vₓ = volume) :
    Vₓ = Real.pi * ∑' n : ℕ,
      ∫ x in (2 * (n : ℝ) * Real.pi)..((2 * (n : ℝ) + 1) * Real.pi),
        Real.exp (-2 * x) * Real.sin x := by
  simpa [volume, componentIntegral] using hV

theorem gap3 (Vₓ : ℝ) (hV : Vₓ = volume) :
    Vₓ = ∑' n : ℕ,
      (primitive ((2 * (n : ℝ) + 1) * Real.pi) -
        primitive (2 * (n : ℝ) * Real.pi)) := by
  calc
    Vₓ = Real.pi * ∑' n : ℕ,
        ∫ x in (2 * (n : ℝ) * Real.pi)..((2 * (n : ℝ) + 1) * Real.pi),
          Real.exp (-2 * x) * Real.sin x := by
            simpa [volume, componentIntegral] using hV
    _ = ∑' n : ℕ, Real.pi *
        (∫ x in (2 * (n : ℝ) * Real.pi)..((2 * (n : ℝ) + 1) * Real.pi),
          Real.exp (-2 * x) * Real.sin x) := tsum_mul_left.symm
    _ = ∑' n : ℕ,
        (primitive ((2 * (n : ℝ) + 1) * Real.pi) -
          primitive (2 * (n : ℝ) * Real.pi)) := by
            apply tsum_congr
            intro n
            exact integral_eq_primitive_sub _ _

theorem gap4 (Vₓ : ℝ) (hV : Vₓ = volume) :
    Vₓ = Real.pi / 5 * (Real.exp (-2 * Real.pi) + 1) *
      ∑' n : ℕ, Real.exp (-4 * (n : ℝ) * Real.pi) := by
  calc
    Vₓ = ∑' n : ℕ,
        (primitive ((2 * (n : ℝ) + 1) * Real.pi) -
          primitive (2 * (n : ℝ) * Real.pi)) := gap3 Vₓ hV
    _ = ∑' n : ℕ,
        (Real.pi / 5 * (Real.exp (-2 * Real.pi) + 1) *
          Real.exp (-4 * (n : ℝ) * Real.pi)) := by
            apply tsum_congr
            intro n
            exact primitive_component_sub n
    _ = Real.pi / 5 * (Real.exp (-2 * Real.pi) + 1) *
        ∑' n : ℕ, Real.exp (-4 * (n : ℝ) * Real.pi) := tsum_mul_left

theorem gap5 (Vₓ : ℝ) (hV : Vₓ = volume) :
    Vₓ = Real.pi / 5 *
      (Real.exp (-2 * Real.pi) + 1) /
        (1 - Real.exp (-4 * Real.pi)) := by
  let q : ℝ := Real.exp (-4 * Real.pi)
  have hqpos : 0 < q := by
    dsimp [q]
    exact Real.exp_pos _
  have hq : q < 1 := by
    dsimp [q]
    have h := (Real.exp_lt_exp).mpr (show -4 * Real.pi < 0 by
      nlinarith [Real.pi_pos])
    simpa using h
  have hnorm : ‖q‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos hqpos]
    exact hq
  have hterm (n : ℕ) :
      Real.exp (-4 * (n : ℝ) * Real.pi) = q ^ n := by
    dsimp [q]
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hsum :
      (∑' n : ℕ, Real.exp (-4 * (n : ℝ) * Real.pi)) =
        1 / (1 - q) := by
    calc
      (∑' n : ℕ, Real.exp (-4 * (n : ℝ) * Real.pi)) =
          ∑' n : ℕ, q ^ n := by
            apply tsum_congr
            exact hterm
      _ = (1 - q)⁻¹ := (hasSum_geometric_of_norm_lt_one hnorm).tsum_eq
      _ = 1 / (1 - q) := by simp [div_eq_mul_inv]
  rw [gap4 Vₓ hV, hsum]
  dsimp [q]
  ring

theorem gap6 :
    Real.pi / 5 * (Real.exp (-2 * Real.pi) + 1) /
        (1 - Real.exp (-4 * Real.pi)) =
      Real.pi / (5 * (1 - Real.exp (-2 * Real.pi))) := by
  let q : ℝ := Real.exp (-2 * Real.pi)
  have hqpos : 0 < q := by
    dsimp [q]
    exact Real.exp_pos _
  have hq : q < 1 := by
    dsimp [q]
    have h := (Real.exp_lt_exp).mpr (show -2 * Real.pi < 0 by
      nlinarith [Real.pi_pos])
    simpa using h
  have hexp : Real.exp (-4 * Real.pi) = q ^ 2 := by
    calc
      Real.exp (-4 * Real.pi) =
          Real.exp ((-2 * Real.pi) + (-2 * Real.pi)) := by
            congr 1
            ring
      _ = Real.exp (-2 * Real.pi) * Real.exp (-2 * Real.pi) :=
        Real.exp_add _ _
      _ = q ^ 2 := by simp [q, pow_two]
  have hminus : 1 - q ≠ 0 := ne_of_gt (sub_pos.mpr hq)
  have hplus : 1 + q ≠ 0 := ne_of_gt (by nlinarith)
  have hsquare : 1 - q ^ 2 ≠ 0 := by
    rw [show 1 - q ^ 2 = (1 - q) * (1 + q) by ring]
    exact mul_ne_zero hminus hplus
  change Real.pi / 5 * (q + 1) /
      (1 - Real.exp (-4 * Real.pi)) =
    Real.pi / (5 * (1 - q))
  rw [hexp]
  field_simp [hminus, hsquare]
  ring

theorem gap7 (Vₓ : ℝ) (hV : Vₓ = volume) :
    Vₓ = Real.pi / (5 * (1 - Real.exp (-2 * Real.pi))) := by
  calc
    Vₓ = Real.pi / 5 *
        (Real.exp (-2 * Real.pi) + 1) /
          (1 - Real.exp (-4 * Real.pi)) := gap5 Vₓ hV
    _ = Real.pi / (5 * (1 - Real.exp (-2 * Real.pi))) := gap6

end

end ProofGap.Exercise2479
