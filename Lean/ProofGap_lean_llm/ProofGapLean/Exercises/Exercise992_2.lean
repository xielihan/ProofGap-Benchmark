import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise992_2

open Filter

noncomputable section

def f (n : ℕ) (x : ℝ) : ℝ :=
  if x = 0 then 0 else x ^ n * Real.sin (1 / x)

def dq (g : ℝ → ℝ) (a h : ℝ) : ℝ :=
  (g (a + h) - g a) / h

private def oscillationPoint (k : ℕ) : ℝ :=
  (Real.pi / 2 + (k : ℝ) * (2 * Real.pi))⁻¹

private theorem oscillationAngle_pos (k : ℕ) :
    0 < Real.pi / 2 + (k : ℝ) * (2 * Real.pi) := by
  have hc : 0 < (2 : ℝ) * Real.pi := by nlinarith [Real.pi_pos]
  have hk : 0 ≤ (k : ℝ) * (2 * Real.pi) :=
    mul_nonneg (Nat.cast_nonneg k) (le_of_lt hc)
  nlinarith [Real.pi_pos]

private theorem oscillationPoint_pos (k : ℕ) :
    0 < oscillationPoint k := by
  exact inv_pos.mpr (oscillationAngle_pos k)

private theorem oscillationPoint_ne_zero (k : ℕ) :
    oscillationPoint k ≠ 0 :=
  ne_of_gt (oscillationPoint_pos k)

private theorem oscillationPoint_tendsto :
    Tendsto oscillationPoint atTop (nhds 0) := by
  have hc : 0 < (2 : ℝ) * Real.pi := by nlinarith [Real.pi_pos]
  have hangle :
      Tendsto (fun k : ℕ => Real.pi / 2 + (k : ℝ) * (2 * Real.pi))
        atTop atTop := by
    refine tendsto_atTop.2 (fun b => ?_)
    obtain ⟨N, hN⟩ :=
      exists_nat_gt ((b - Real.pi / 2) / (2 * Real.pi))
    refine eventually_atTop.2 ⟨N, ?_⟩
    intro m hm
    have hcast : (N : ℝ) ≤ (m : ℝ) := Nat.cast_le.2 hm
    have hN' :
        b - Real.pi / 2 < (N : ℝ) * (2 * Real.pi) :=
      (div_lt_iff₀ hc).mp hN
    have hmul :
        (N : ℝ) * (2 * Real.pi) ≤ (m : ℝ) * (2 * Real.pi) :=
      mul_le_mul_of_nonneg_right hcast (le_of_lt hc)
    nlinarith
  simpa [oscillationPoint] using tendsto_inv_atTop_zero.comp hangle

private theorem sin_inv_oscillationPoint (k : ℕ) :
    Real.sin (1 / oscillationPoint k) = 1 := by
  simp only [oscillationPoint, one_div, inv_inv]
  induction k with
  | zero => simpa using Real.sin_pi_div_two
  | succ k ih =>
      rw [Nat.cast_succ]
      rw [show Real.pi / 2 + ((k : ℝ) + 1) * (2 * Real.pi) =
          (Real.pi / 2 + (k : ℝ) * (2 * Real.pi)) + 2 * Real.pi by ring]
      rw [Real.sin_add_two_pi, ih]

private theorem sin_inv_neg_oscillationPoint (k : ℕ) :
    Real.sin (1 / (-oscillationPoint k)) = -1 := by
  simpa only [one_div, inv_neg, Real.sin_neg, neg_inj] using
    sin_inv_oscillationPoint k

theorem gap1 (n : ℕ) (hn : 1 < n) :
    (fun h => dq (f n) 0 h) =
      fun h => h ^ (n - 1) * Real.sin (1 / h) := by
  funext h
  by_cases hh : h = 0
  · subst h
    simp [dq, f]
  · simp only [dq, zero_add, f, hh, if_false, if_pos, sub_zero]
    have hpow : h ^ n = h ^ (n - 1) * h := by
      calc
        h ^ n = h ^ ((n - 1) + 1) :=
          congrArg (fun m : ℕ => h ^ m) (by omega)
        _ = h ^ (n - 1) * h := by rw [pow_succ]
    rw [hpow]
    field_simp [hh]

theorem gap2 (n : ℕ) (hn : 1 < n) :
    Tendsto (fun h : ℝ => h ^ (n - 1) * Real.sin (1 / h))
      (nhds 0) (nhds 0) := by
  have hk : n - 1 ≠ 0 := by omega
  have hp : Tendsto (fun h : ℝ => h ^ (n - 1)) (nhds 0) (nhds 0) := by
    have hid : Tendsto (fun h : ℝ => h) (nhds 0) (nhds 0) := tendsto_id
    have hpow := hid.pow (n - 1)
    simpa [hk] using hpow
  rw [Metric.tendsto_nhds] at hp ⊢
  intro ε hε
  filter_upwards [hp ε hε] with h hh
  have hh' : |h ^ (n - 1)| < ε := by
    simpa [Real.dist_eq] using hh
  have hsin : |Real.sin (1 / h)| ≤ (1 : ℝ) :=
    abs_le.2 ⟨Real.neg_one_le_sin (1 / h), Real.sin_le_one (1 / h)⟩
  calc
    dist (h ^ (n - 1) * Real.sin (1 / h)) 0 =
        |h ^ (n - 1)| * |Real.sin (1 / h)| := by
          rw [Real.dist_eq, sub_zero, abs_mul]
    _ ≤ |h ^ (n - 1)| * 1 :=
      mul_le_mul_of_nonneg_left hsin (abs_nonneg (h ^ (n - 1)))
    _ = |h ^ (n - 1)| := mul_one _
    _ < ε := hh'

theorem gap3 (n : ℕ) (hn : 1 < n) :
    Tendsto (dq (f n) 0) (nhds 0) (nhds 0) := by
  have hEq : dq (f n) 0 =
      (fun h : ℝ => h ^ (n - 1) * Real.sin (1 / h)) := by
    exact gap1 n hn
  rw [hEq]
  exact gap2 n hn

theorem gap4 (n : ℕ) (hn : 1 < n) :
    HasDerivAt (f n) 0 0 := by
  rw [hasDerivAt_iff_tendsto]
  simpa only [dq, zero_add, sub_zero, smul_zero, norm_zero,
    div_eq_mul_inv, norm_mul, norm_inv, mul_comm] using (gap3 n hn).norm

theorem gap5 (n : ℕ) (hn : 1 < n) :
    DifferentiableAt ℝ (f n) 0 := by
  exact (gap4 n hn).differentiableAt

theorem gap6 (n : ℕ) :
    1 < n ↔ DifferentiableAt ℝ (f n) 0 := by
  constructor
  · exact gap5 n
  · intro hd
    by_contra hn
    have hcases : n = 0 ∨ n = 1 := by omega
    rcases hcases with rfl | rfl
    · have ht : Tendsto (f 0) (nhds 0) (nhds (f 0 0)) := hd.continuousAt
      have hc := ht.comp oscillationPoint_tendsto
      have hfzero : f 0 0 = 0 := by simp [f]
      rw [hfzero] at hc
      have hseq :
          (f 0 ∘ oscillationPoint) = (fun _ : ℕ => (1 : ℝ)) := by
        funext k
        simp only [Function.comp_apply, f, oscillationPoint_ne_zero,
          if_false, pow_zero, one_mul]
        exact sin_inv_oscillationPoint k
      rw [hseq] at hc
      have hconst : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1) :=
        tendsto_const_nhds
      have hbad : (0 : ℝ) = 1 := tendsto_nhds_unique hc hconst
      linarith
    · have hslope := hasDerivAt_iff_tendsto.mp hd.hasDerivAt
      have hfzero : f 1 0 = 0 := by simp [f]
      simp only [sub_zero, smul_eq_mul, hfzero] at hslope
      have hfpos (k : ℕ) : f 1 (oscillationPoint k) = oscillationPoint k := by
        simp only [f, oscillationPoint_ne_zero k, if_false, pow_one]
        rw [sin_inv_oscillationPoint]
        ring
      have hfneg (k : ℕ) : f 1 (-oscillationPoint k) = oscillationPoint k := by
        have hk : -oscillationPoint k ≠ 0 :=
          neg_ne_zero.mpr (oscillationPoint_ne_zero k)
        simp only [f, hk, if_false, pow_one]
        rw [sin_inv_neg_oscillationPoint]
        ring
      have hposseq :
          ((fun x : ℝ => ‖x‖⁻¹ *
              ‖f 1 x - x * deriv (f 1) 0‖) ∘ oscillationPoint) =
            (fun _ : ℕ => |1 - deriv (f 1) 0|) := by
        funext k
        rw [Function.comp_apply, hfpos k]
        have hp := oscillationPoint_pos k
        rw [show oscillationPoint k - oscillationPoint k * deriv (f 1) 0 =
            oscillationPoint k * (1 - deriv (f 1) 0) by ring]
        simp only [Real.norm_eq_abs, abs_mul, abs_of_pos hp]
        field_simp [ne_of_gt hp]
      have hcpos := hslope.comp oscillationPoint_tendsto
      rw [hposseq] at hcpos
      have hconst_pos :
          Tendsto (fun _ : ℕ => |1 - deriv (f 1) 0|) atTop
            (nhds |1 - deriv (f 1) 0|) := tendsto_const_nhds
      have hzpos : |1 - deriv (f 1) 0| = 0 :=
        tendsto_nhds_unique hconst_pos hcpos
      have hdpos : 1 - deriv (f 1) 0 = 0 := abs_eq_zero.mp hzpos
      have hnegseq :
          ((fun x : ℝ => ‖x‖⁻¹ *
              ‖f 1 x - x * deriv (f 1) 0‖) ∘
              (fun k : ℕ => -oscillationPoint k)) =
            (fun _ : ℕ => |1 + deriv (f 1) 0|) := by
        funext k
        rw [Function.comp_apply, hfneg k]
        have hp := oscillationPoint_pos k
        rw [show oscillationPoint k -
              (-oscillationPoint k) * deriv (f 1) 0 =
            oscillationPoint k * (1 + deriv (f 1) 0) by ring]
        simp only [Real.norm_eq_abs, abs_neg, abs_mul, abs_of_pos hp]
        field_simp [ne_of_gt hp]
      have hneg_tendsto :
          Tendsto (fun k : ℕ => -oscillationPoint k) atTop (nhds 0) := by
        simpa using oscillationPoint_tendsto.neg
      have hcneg := hslope.comp hneg_tendsto
      rw [hnegseq] at hcneg
      have hconst_neg :
          Tendsto (fun _ : ℕ => |1 + deriv (f 1) 0|) atTop
            (nhds |1 + deriv (f 1) 0|) := tendsto_const_nhds
      have hzneg : |1 + deriv (f 1) 0| = 0 :=
        tendsto_nhds_unique hconst_neg hcneg
      have hdneg : 1 + deriv (f 1) 0 = 0 := abs_eq_zero.mp hzneg
      linarith

end

end ProofGap.Exercise992_2
