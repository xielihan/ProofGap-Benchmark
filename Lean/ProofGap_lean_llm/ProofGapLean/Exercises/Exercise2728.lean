import ProofGapLean.Prelude.Analysis
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Lean.Elab.Tactic.Omega
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Neighborhoods

namespace ProofGap.Exercise2728

noncomputable section

open Filter

def term (x : ℝ) (n : ℕ) : ℝ :=
  n * Real.exp (-(n * x))

theorem gap1 (x : ℝ) :
    Tendsto
      (fun n : ℕ => term x (n + 2) / term x (n + 1))
      atTop (nhds (Real.exp (-x))) := by
  have hshift : Tendsto (fun n : ℕ => n + 1) atTop atTop := by
    refine tendsto_atTop.2 ?_
    intro b
    filter_upwards [eventually_ge_atTop b] with n hn
    omega
  have hcast :
      Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hshift
  have hinv :
      Tendsto (fun n : ℕ => (((n + 1 : ℕ) : ℝ))⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp hcast
  have hone :
      Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1) :=
    tendsto_const_nhds
  have hadd :
      Tendsto
        (fun n : ℕ => (1 : ℝ) + (((n + 1 : ℕ) : ℝ))⁻¹)
        atTop (nhds 1) := by
    simpa using hone.add hinv
  have hratio :
      Tendsto
        (fun n : ℕ =>
          ((1 : ℝ) + (((n + 1 : ℕ) : ℝ))⁻¹) * Real.exp (-x))
        atTop (nhds (Real.exp (-x))) := by
    simpa using hadd.mul
      (tendsto_const_nhds :
        Tendsto (fun _ : ℕ => Real.exp (-x)) atTop
          (nhds (Real.exp (-x))))
  refine hratio.congr' (Filter.Eventually.of_forall (fun n => ?_))
  symm
  have hexp :
      Real.exp (-(((n + 2 : ℕ) : ℝ) * x)) =
        Real.exp (-x) * Real.exp (-(((n + 1 : ℕ) : ℝ) * x)) := by
    rw [← Real.exp_add]
    congr 1
    norm_num [Nat.cast_add] <;> ring
  have hne : (((n + 1 : ℕ) : ℝ)) ≠ 0 := by
    positivity
  simp only [term]
  rw [hexp]
  field_simp [hne, Real.exp_ne_zero] <;>
    norm_num [Nat.cast_add] <;> ring

theorem gap2 (x : ℝ) (hx : 0 < x) :
    Real.exp (-x) < 1 := by
  rw [Real.exp_lt_one_iff]
  linarith

theorem gap3 (x : ℝ) (hx : 0 < x) :
    Summable (fun n : ℕ => |term x (n + 1)|) := by
  let q : ℝ := Real.exp (-x)
  let r : ℝ := (q + 1) / 2
  have hq : q < 1 := by
    exact gap2 x hx
  have hqr : q < r := by
    dsimp [r]
    linarith
  have hr : r < 1 := by
    dsimp [r]
    linarith
  have hevent :
      ∀ᶠ n : ℕ in atTop,
        term x (n + 2) / term x (n + 1) < r := by
    exact (tendsto_order.1 (gap1 x)).2 r hqr
  refine summable_of_ratio_norm_eventually_le (r := r) hr ?_
  filter_upwards [hevent] with n hn
  have hp1 : 0 < term x (n + 1) := by
    simp only [term]
    positivity
  have hp2 : 0 < term x (n + 2) := by
    simp only [term]
    positivity
  have hidx : (n + 1) + 1 = n + 2 := by omega
  rw [hidx]
  simp only [Real.norm_eq_abs, abs_abs]
  rw [abs_of_pos hp2, abs_of_pos hp1]
  exact le_of_lt ((div_lt_iff₀ hp1).mp hn)

theorem gap4 :
    ∀ n : ℕ, 1 ≤ n → term 0 n = n := by
  intro n hn
  simp [term]

theorem gap5 :
    ¬ Summable (fun n : ℕ => term 0 (n + 1)) := by
  intro hs
  have hlim :
      Tendsto (fun n : ℕ => term 0 (n + 1)) atTop (nhds 0) :=
    hs.tendsto_atTop_zero
  have hevent : ∀ᶠ n : ℕ in atTop, term 0 (n + 1) < 1 :=
    (tendsto_order.1 hlim).2 1 (by norm_num)
  rcases eventually_atTop.1 hevent with ⟨N, hN⟩
  have hlt := hN N le_rfl
  rw [gap4 (N + 1) (by omega)] at hlt
  have hge : (1 : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := by
    norm_num [Nat.cast_add] <;> positivity
  exact (not_lt_of_ge hge) hlt

theorem gap6 (x : ℝ) (hx : x < 0) :
    1 < Real.exp (-x) := by
  rw [Real.one_lt_exp_iff]
  linarith

theorem gap7 (x : ℝ) (hx : x < 0) :
    ¬ Summable (fun n : ℕ => term x (n + 1)) := by
  intro hs
  have hlim :
      Tendsto (fun n : ℕ => term x (n + 1)) atTop (nhds 0) :=
    hs.tendsto_atTop_zero
  have hevent : ∀ᶠ n : ℕ in atTop, term x (n + 1) < 1 :=
    (tendsto_order.1 hlim).2 1 (by norm_num)
  rcases eventually_atTop.1 hevent with ⟨N, hN⟩
  have hlt := hN N le_rfl
  have ha : 0 < (((N + 1 : ℕ) : ℝ)) := by
    positivity
  have hcoef : 1 ≤ (((N + 1 : ℕ) : ℝ)) := by
    norm_num [Nat.cast_add] <;> positivity
  have hprod : (((N + 1 : ℕ) : ℝ)) * x < 0 :=
    mul_neg_of_pos_of_neg ha hx
  have hexp :
      1 < Real.exp (-((((N + 1 : ℕ) : ℝ)) * x)) := by
    rw [Real.one_lt_exp_iff]
    exact neg_pos.mpr hprod
  have hm :
      0 ≤ ((((N + 1 : ℕ) : ℝ)) - 1) *
        Real.exp (-((((N + 1 : ℕ) : ℝ)) * x)) :=
    mul_nonneg (sub_nonneg.mpr hcoef) (le_of_lt (Real.exp_pos _))
  have ht : 1 < term x (N + 1) := by
    simp only [term]
    nlinarith
  linarith

theorem gap8 (x : ℝ) :
    0 < x ↔ Summable (fun n : ℕ => term x (n + 1)) := by
  constructor
  · intro hx
    have hnorm : Summable (fun n : ℕ => ‖term x (n + 1)‖) := by
      simpa [Real.norm_eq_abs] using gap3 x hx
    exact hnorm.of_norm
  · intro hs
    by_contra hnot
    have hxle : x ≤ 0 := le_of_not_gt hnot
    rcases lt_or_eq_of_le hxle with hxlt | hx0
    · exact gap7 x hxlt hs
    · subst x
      exact gap5 hs

end

end ProofGap.Exercise2728
