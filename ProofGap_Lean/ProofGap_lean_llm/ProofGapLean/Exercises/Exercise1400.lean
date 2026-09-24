import ProofGapLean.Prelude.Analysis
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Topology.Neighborhoods

namespace ProofGap.Exercise1400

noncomputable section
open Filter
open scoped Topology

def original (x : ℝ) :=
  Real.rpow x (3 / 2 : ℝ) *
    (Real.sqrt (x + 1) + Real.sqrt (x - 1) - 2 * Real.sqrt x)
def normalized (x : ℝ) :=
  x ^ 2 *
    (Real.rpow (1 + 1 / x) (1 / 2 : ℝ) +
      Real.rpow (1 - 1 / x) (1 / 2 : ℝ) - 2)
def leadingStage (x : ℝ) := -(1 / 4 : ℝ) + 1 / x

private theorem exercise1400_core :
    Tendsto normalized atTop (nhds (-1 / 4 : ℝ)) ∧
      Tendsto original atTop (nhds (-1 / 4 : ℝ)) := by
  have hinv : Tendsto (fun x : ℝ => 1 / x) atTop (nhds 0) := by
    simpa [one_div] using
      (tendsto_inv_atTop_zero :
        Tendsto (fun x : ℝ => x⁻¹) atTop (nhds 0))
  have hpbase : Tendsto (fun x : ℝ => 1 + 1 / x) atTop (nhds 1) := by
    simpa using
      ((tendsto_const_nhds :
          Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (nhds 1)).add hinv)
  have hmbase : Tendsto (fun x : ℝ => 1 - 1 / x) atTop (nhds 1) := by
    simpa using
      ((tendsto_const_nhds :
          Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (nhds 1)).sub hinv)
  have hp :
      Tendsto (fun x : ℝ => Real.sqrt (1 + 1 / x)) atTop (nhds 1) := by
    simpa using (Real.continuous_sqrt.tendsto 1).comp hpbase
  have hm :
      Tendsto (fun x : ℝ => Real.sqrt (1 - 1 / x)) atTop (nhds 1) := by
    simpa using (Real.continuous_sqrt.tendsto 1).comp hmbase
  have hden :
      Tendsto
        (fun x : ℝ =>
          (Real.sqrt (1 + 1 / x) * Real.sqrt (1 - 1 / x) + 1) *
            (Real.sqrt (1 + 1 / x) + Real.sqrt (1 - 1 / x) + 2))
        atTop (nhds 8) := by
    have h₁ :=
      (hp.mul hm).add
        (tendsto_const_nhds :
          Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (nhds 1))
    have h₂ :=
      (hp.add hm).add
        (tendsto_const_nhds :
          Tendsto (fun _ : ℝ => (2 : ℝ)) atTop (nhds 2))
    convert h₁.mul h₂ using 1 <;> norm_num
  have hrat :
      Tendsto
        (fun x : ℝ =>
          (-2 : ℝ) /
            ((Real.sqrt (1 + 1 / x) * Real.sqrt (1 - 1 / x) + 1) *
              (Real.sqrt (1 + 1 / x) + Real.sqrt (1 - 1 / x) + 2)))
        atTop (nhds (-1 / 4 : ℝ)) := by
    convert
      ((tendsto_const_nhds :
          Tendsto (fun _ : ℝ => (-2 : ℝ)) atTop (nhds (-2 : ℝ))).div
        hden (by norm_num : (8 : ℝ) ≠ 0)) using 1 <;> norm_num
  have hnorm_eq : ∀ x : ℝ, 1 < x →
      normalized x =
        (-2 : ℝ) /
          ((Real.sqrt (1 + 1 / x) * Real.sqrt (1 - 1 / x) + 1) *
            (Real.sqrt (1 + 1 / x) + Real.sqrt (1 - 1 / x) + 2)) := by
    intro x hx
    have hxpos : 0 < x := lt_trans zero_lt_one hx
    have hx0 : x ≠ 0 := ne_of_gt hxpos
    have hitpos : 0 < 1 / x := one_div_pos.mpr hxpos
    have hitlt : 1 / x < 1 := (div_lt_one hxpos).2 hx
    have hplus : 0 ≤ 1 + 1 / x := by nlinarith
    have hminus : 0 ≤ 1 - 1 / x := by nlinarith
    have hplus_rpow :
        Real.rpow (1 + 1 / x) (1 / 2 : ℝ) =
          Real.sqrt (1 + 1 / x) := by
      rw [Real.sqrt_eq_rpow]
      norm_num
    have hminus_rpow :
        Real.rpow (1 - 1 / x) (1 / 2 : ℝ) =
          Real.sqrt (1 - 1 / x) := by
      rw [Real.sqrt_eq_rpow]
      norm_num
    unfold normalized
    rw [hplus_rpow, hminus_rpow]
    let a : ℝ := Real.sqrt (1 + 1 / x)
    let b : ℝ := Real.sqrt (1 - 1 / x)
    change x ^ 2 * (a + b - 2) =
      (-2 : ℝ) / ((a * b + 1) * (a + b + 2))
    have ha0 : 0 ≤ a := by
      dsimp [a]
      exact Real.sqrt_nonneg _
    have hb0 : 0 ≤ b := by
      dsimp [b]
      exact Real.sqrt_nonneg _
    have ha2 : a ^ 2 = 1 + 1 / x := by
      dsimp [a]
      exact Real.sq_sqrt hplus
    have hb2 : b ^ 2 = 1 - 1 / x := by
      dsimp [b]
      exact Real.sq_sqrt hminus
    have hfac₁ : 0 < a * b + 1 := by
      have hab0 : 0 ≤ a * b := mul_nonneg ha0 hb0
      nlinarith
    have hfac₂ : 0 < a + b + 2 := by nlinarith
    have hden0 : (a * b + 1) * (a + b + 2) ≠ 0 :=
      mul_ne_zero (ne_of_gt hfac₁) (ne_of_gt hfac₂)
    have hsum : (a + b - 2) * (a + b + 2) = 2 * (a * b - 1) := by
      nlinarith [ha2, hb2]
    have hab : (a * b - 1) * (a * b + 1) = -(1 / x) ^ 2 := by
      calc
        (a * b - 1) * (a * b + 1) = a ^ 2 * b ^ 2 - 1 := by ring
        _ = (1 + 1 / x) * (1 - 1 / x) - 1 := by rw [ha2, hb2]
        _ = -(1 / x) ^ 2 := by ring
    have hcombined :
        (a + b - 2) * (a + b + 2) * (a * b + 1) =
          -2 * (1 / x) ^ 2 := by
      calc
        (a + b - 2) * (a + b + 2) * (a * b + 1) =
            (2 * (a * b - 1)) * (a * b + 1) := by rw [hsum]
        _ = 2 * ((a * b - 1) * (a * b + 1)) := by ring
        _ = 2 * (-(1 / x) ^ 2) := by rw [hab]
        _ = -2 * (1 / x) ^ 2 := by ring
    have hinvx : x ^ 2 * (1 / x) ^ 2 = 1 := by
      field_simp [hx0] <;> ring
    apply (eq_div_iff hden0).2
    calc
      x ^ 2 * (a + b - 2) * ((a * b + 1) * (a + b + 2)) =
          x ^ 2 * ((a + b - 2) * (a + b + 2) * (a * b + 1)) := by ring
      _ = x ^ 2 * (-2 * (1 / x) ^ 2) := by rw [hcombined]
      _ = -2 * (x ^ 2 * (1 / x) ^ 2) := by ring
      _ = -2 := by rw [hinvx]; ring
  have hnormalized : Tendsto normalized atTop (nhds (-1 / 4 : ℝ)) := by
    apply hrat.congr'
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    exact (hnorm_eq x hx).symm
  have horig_eq : ∀ x : ℝ, 1 < x → original x = normalized x := by
    intro x hx
    have hxpos : 0 < x := lt_trans zero_lt_one hx
    have hx0 : x ≠ 0 := ne_of_gt hxpos
    have hxp : x + 1 = x * (1 + 1 / x) := by
      field_simp [hx0] <;> ring
    have hxm : x - 1 = x * (1 - 1 / x) := by
      field_simp [hx0] <;> ring
    have hsplus :
        Real.sqrt (x + 1) =
          Real.sqrt x * Real.sqrt (1 + 1 / x) := by
      rw [hxp, Real.sqrt_mul (le_of_lt hxpos)]
    have hsminus :
        Real.sqrt (x - 1) =
          Real.sqrt x * Real.sqrt (1 - 1 / x) := by
      rw [hxm, Real.sqrt_mul (le_of_lt hxpos)]
    have hcoef :
        Real.rpow x (3 / 2 : ℝ) * Real.sqrt x = x ^ 2 := by
      rw [Real.sqrt_eq_rpow]
      change Real.rpow x (3 / 2 : ℝ) *
        Real.rpow x (1 / 2 : ℝ) = x ^ 2
      calc
        Real.rpow x (3 / 2 : ℝ) * Real.rpow x (1 / 2 : ℝ) =
            Real.rpow x ((3 / 2 : ℝ) + (1 / 2 : ℝ)) := by
          exact (Real.rpow_add hxpos (3 / 2 : ℝ) (1 / 2 : ℝ)).symm
        _ = Real.rpow x 2 := by norm_num
        _ = x ^ 2 := by norm_num [Real.rpow_two]
    have hplus_rpow :
        Real.rpow (1 + 1 / x) (1 / 2 : ℝ) =
          Real.sqrt (1 + 1 / x) := by
      rw [Real.sqrt_eq_rpow]
      norm_num
    have hminus_rpow :
        Real.rpow (1 - 1 / x) (1 / 2 : ℝ) =
          Real.sqrt (1 - 1 / x) := by
      rw [Real.sqrt_eq_rpow]
      norm_num
    unfold original normalized
    rw [hplus_rpow, hminus_rpow]
    rw [hsplus, hsminus]
    calc
      Real.rpow x (3 / 2 : ℝ) *
          (Real.sqrt x * Real.sqrt (1 + 1 / x) +
            Real.sqrt x * Real.sqrt (1 - 1 / x) - 2 * Real.sqrt x) =
          (Real.rpow x (3 / 2 : ℝ) * Real.sqrt x) *
            (Real.sqrt (1 + 1 / x) + Real.sqrt (1 - 1 / x) - 2) := by ring
      _ = x ^ 2 *
            (Real.sqrt (1 + 1 / x) + Real.sqrt (1 - 1 / x) - 2) := by
          rw [hcoef]
  have horiginal : Tendsto original atTop (nhds (-1 / 4 : ℝ)) := by
    apply hnormalized.congr'
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    exact (horig_eq x hx).symm
  exact ⟨hnormalized, horiginal⟩

theorem gap1 : Tendsto original atTop (nhds (-1 / 4 : ℝ)) := by
  exact exercise1400_core.2
theorem gap2 : Tendsto normalized atTop (nhds (-1 / 4 : ℝ)) := by
  exact exercise1400_core.1
theorem gap3 : Tendsto leadingStage atTop (nhds (-1 / 4 : ℝ)) := by
  have hinv : Tendsto (fun x : ℝ => 1 / x) atTop (nhds 0) := by
    simpa [one_div] using
      (tendsto_inv_atTop_zero :
        Tendsto (fun x : ℝ => x⁻¹) atTop (nhds 0))
  have hconst :
      Tendsto (fun _ : ℝ => -(1 / 4 : ℝ)) atTop
        (nhds (-(1 / 4 : ℝ))) :=
    tendsto_const_nhds
  change Tendsto (fun x : ℝ => -(1 / 4 : ℝ) + 1 / x) atTop
    (nhds (-1 / 4 : ℝ))
  have hadd :
      Tendsto (fun x : ℝ => -(1 / 4 : ℝ) + 1 / x) atTop
        (nhds (-(1 / 4 : ℝ) + 0)) :=
    hconst.add hinv
  have hlim_eq :
      (-(1 / 4 : ℝ) + 0) = (-1 / 4 : ℝ) := by
    norm_num
  rw [hlim_eq] at hadd
  exact hadd
theorem gap4 : Tendsto leadingStage atTop (nhds (-1 / 4 : ℝ)) := by
  exact gap3
theorem gap5 : Tendsto original atTop (nhds (-1 / 4 : ℝ)) := by
  exact gap1

end
end ProofGap.Exercise1400
