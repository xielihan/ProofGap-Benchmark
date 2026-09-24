import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Topology.Neighborhoods
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.NormNum.Core
import Lean.Elab.Tactic.Omega
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Defs.Filter
import Mathlib.Tactic.Positivity

namespace ProofGap.Exercise2636

noncomputable section

open Filter

def term (a : ℝ) (n : ℕ) : ℝ :=
  Real.cos (a / n) ^ (n ^ 3)

def rootProxy (a : ℝ) (n : ℕ) : ℝ :=
  Real.cos (a / n) ^ (n ^ 2)

def cosRemainder (a : ℝ) (n : ℕ) : ℝ :=
  Real.cos (a / n) - (1 - a ^ 2 / (2 * (n : ℝ) ^ 2))

def scaledLogRemainder (a : ℝ) (n : ℕ) : ℝ :=
  (n : ℝ) ^ 2 * Real.log (Real.cos (a / n)) + a ^ 2 / 2

def converges (a : ℝ) : Prop :=
  Summable (fun n : ℕ => term a (n + 1))

private theorem cos_quartic_bound (x : ℝ) (hx : |x| ≤ 1) :
    ‖Real.cos x - 1 + x ^ 2 / 2‖ ≤ |x| ^ 4 := by
  let t : ℝ := |x| / 2
  have ht0 : 0 ≤ t := by
    dsimp [t]
    positivity
  have htle : t ≤ 1 / 2 := by
    dsimp [t]
    linarith
  have ht1 : t ≤ 1 := by linarith
  have htSq : t ^ 2 ≤ 1 := by
    have hp : 0 ≤ t * (1 - t) := mul_nonneg ht0 (by linarith)
    nlinarith
  have htAbs : |t| ≤ 1 := by
    rw [abs_of_nonneg ht0]
    exact ht1
  have hsb :
      |Real.sin t - (t - t ^ 3 / 6)| ≤ |t| ^ 4 * (5 / 96) :=
    Real.sin_bound htAbs
  rw [abs_of_nonneg ht0] at hsb
  have hsloRaw :
      t - t ^ 3 / 6 - t ^ 4 * (5 / 96) ≤ Real.sin t := by
    have hneg := (abs_le.mp hsb).1
    nlinarith
  have htPow : t ^ 4 ≤ t ^ 3 := by
    calc
      t ^ 4 = t ^ 3 * t := by ring
      _ ≤ t ^ 3 * 1 :=
        mul_le_mul_of_nonneg_left ht1 (pow_nonneg ht0 3)
      _ = t ^ 3 := by ring
  have hslo : t - 7 * t ^ 3 / 32 ≤ Real.sin t := by
    nlinarith [hsloRaw, htPow]
  have hcoef : 0 ≤ 1 - 7 * t ^ 2 / 32 := by
    nlinarith [htSq]
  have hlow0 : 0 ≤ t - 7 * t ^ 3 / 32 := by
    calc
      0 ≤ t * (1 - 7 * t ^ 2 / 32) := mul_nonneg ht0 hcoef
      _ = t - 7 * t ^ 3 / 32 := by ring
  have hshi : Real.sin t ≤ t := by
    exact Real.sin_le ht0
  have hs0 : 0 ≤ Real.sin t := le_trans hlow0 hslo
  have hloSq : (t - 7 * t ^ 3 / 32) ^ 2 ≤ Real.sin t ^ 2 := by
    have h₁ : 0 ≤ Real.sin t - (t - 7 * t ^ 3 / 32) :=
      sub_nonneg.mpr hslo
    have h₂ : 0 ≤ Real.sin t + (t - 7 * t ^ 3 / 32) :=
      add_nonneg hs0 hlow0
    have hp := mul_nonneg h₁ h₂
    nlinarith
  have hhiSq : Real.sin t ^ 2 ≤ t ^ 2 := by
    have h₁ : 0 ≤ t - Real.sin t := sub_nonneg.mpr hshi
    have h₂ : 0 ≤ t + Real.sin t := add_nonneg ht0 hs0
    have hp := mul_nonneg h₁ h₂
    nlinarith
  have hsinSqLower : t ^ 2 - 8 * t ^ 4 ≤ Real.sin t ^ 2 := by
    calc
      t ^ 2 - 8 * t ^ 4 ≤ (t - 7 * t ^ 3 / 32) ^ 2 := by
        nlinarith [sq_nonneg (t ^ 2), sq_nonneg (t ^ 3)]
      _ ≤ Real.sin t ^ 2 := hloSq
  have htrig : Real.cos x = 1 - 2 * Real.sin t ^ 2 := by
    calc
      Real.cos x = Real.cos |x| := (Real.cos_abs x).symm
      _ = Real.cos (2 * t) := by
        congr 1
        dsimp [t]
        ring
      _ = 1 - 2 * Real.sin t ^ 2 := by
        rw [Real.cos_two_mul]
        nlinarith [Real.sin_sq_add_cos_sq t]
  have hxsq : x ^ 2 = 4 * t ^ 2 := by
    dsimp [t]
    nlinarith [sq_abs x]
  have hxfour : |x| ^ 4 = 16 * t ^ 4 := by
    dsimp [t]
    ring
  have hrem0 : 0 ≤ Real.cos x - 1 + x ^ 2 / 2 := by
    rw [htrig, hxsq]
    nlinarith
  have hremle : Real.cos x - 1 + x ^ 2 / 2 ≤ |x| ^ 4 := by
    rw [htrig, hxsq, hxfour]
    nlinarith [hsinSqLower]
  rw [Real.norm_eq_abs, abs_of_nonneg hrem0]
  exact hremle

theorem gap1 (a : ℝ) (ha : a = 0) (n : ℕ) (hn : 1 ≤ n) :
    term a n = 1 := by
  simp [term, ha]

theorem gap2 (a : ℝ) (ha : a = 0) :
    ¬ converges a := by
  intro h
  have ht := h.tendsto_atTop_zero
  simpa [converges, term, ha] using ht

theorem gap3 (a : ℝ) (n : ℕ) (hn : 1 ≤ n) :
    rootProxy a n = Real.cos (a / n) ^ (n ^ 2) := by
  rfl

theorem gap4 (a : ℝ) (n : ℕ) (hn : 1 ≤ n)
    (hcos : 0 < Real.cos (a / n)) :
    rootProxy a n =
      Real.exp ((n : ℝ) ^ 2 * Real.log (Real.cos (a / n))) := by
  rw [rootProxy, ← Real.rpow_natCast]
  rw [Real.rpow_def_of_pos hcos]
  congr 1
  norm_num [Nat.cast_pow]
  ring

theorem gap5 (a : ℝ) :
    (∀ (n : ℕ), n ≥ 1 →
      Real.cos (a / n) =
        1 - a ^ 2 / (2 * (n : ℝ) ^ 2) + cosRemainder a n) ∧
    Asymptotics.IsBigO atTop
      (fun n : ℕ => cosRemainder a (n + 1))
      (fun n : ℕ => 1 / ((n + 1 : ℕ) : ℝ) ^ 4) := by
  constructor
  · intro n hn
    unfold cosRemainder
    ring
  · obtain ⟨N, hN⟩ := exists_nat_gt |a|
    refine Asymptotics.IsBigO.of_bound (|a| ^ 4) ?_
    filter_upwards [eventually_ge_atTop N] with n hn
    have hk : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
    have hNn : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have han : |a| ≤ ((n + 1 : ℕ) : ℝ) := by
      norm_num at hN ⊢
      linarith
    have hx : |a / ((n + 1 : ℕ) : ℝ)| ≤ 1 := by
      rw [abs_div, abs_of_pos hk]
      exact (div_le_one hk).2 han
    have hb := cos_quartic_bound (a / ((n + 1 : ℕ) : ℝ)) hx
    calc
      ‖cosRemainder a (n + 1)‖ =
          ‖Real.cos (a / ((n + 1 : ℕ) : ℝ)) - 1 +
            (a / ((n + 1 : ℕ) : ℝ)) ^ 2 / 2‖ := by
              have heq : cosRemainder a (n + 1) =
                  Real.cos (a / ((n + 1 : ℕ) : ℝ)) - 1 +
                    (a / ((n + 1 : ℕ) : ℝ)) ^ 2 / 2 := by
                unfold cosRemainder
                field_simp [ne_of_gt hk] <;> ring
              rw [heq]
      _ ≤ |a / ((n + 1 : ℕ) : ℝ)| ^ 4 := hb
      _ = |a| ^ 4 * ‖1 / (((n + 1 : ℕ) : ℝ) ^ 4)‖ := by
        rw [Real.norm_eq_abs, abs_div, abs_div, abs_one, abs_of_pos hk,
          abs_of_pos (pow_pos hk 4)]
        field_simp [ne_of_gt hk]

theorem gap6 (a : ℝ) :
    Tendsto (fun n : ℕ => scaledLogRemainder a (n + 1))
      atTop (nhds 0) := by
  have hk : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ)) atTop atTop := by
    exact tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hx : Tendsto (fun n : ℕ => a / ((n + 1 : ℕ) : ℝ)) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop hk
  have hcos : Tendsto
      (fun n : ℕ => Real.cos (a / ((n + 1 : ℕ) : ℝ))) atTop (nhds 1) := by
    simpa using Real.continuous_cos.continuousAt.tendsto.comp hx
  have hlog :
      (fun x : ℝ => Real.log x - (x - 1)) =o[nhds 1]
        (fun x : ℝ => x - 1) := by
    convert (Real.hasDerivAt_log (by norm_num : (1 : ℝ) ≠ 0)).isLittleO using 1 <;>
      norm_num <;> ring
  have hlogcomp := hlog.comp_tendsto hcos
  have hscaledCos : Asymptotics.IsBigO atTop
      (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ 2 *
        (Real.cos (a / ((n + 1 : ℕ) : ℝ)) - 1))
      (fun _ : ℕ => (1 : ℝ)) := by
    refine Asymptotics.IsBigO.of_bound (a ^ 2 / 2)
      (Filter.Eventually.of_forall ?_)
    intro n
    have hn : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg _), norm_one, mul_one]
    calc
      ((n + 1 : ℕ) : ℝ) ^ 2 *
          |Real.cos (a / ((n + 1 : ℕ) : ℝ)) - 1| ≤
          ((n + 1 : ℕ) : ℝ) ^ 2 *
            ((a / ((n + 1 : ℕ) : ℝ)) ^ 2 / 2) := by
              gcongr
              let x : ℝ := a / ((n + 1 : ℕ) : ℝ)
              change |Real.cos x - 1| ≤ x ^ 2 / 2
              have hs : |Real.sin (x / 2)| ≤ |x / 2| :=
                Real.abs_sin_le_abs
              have hp : 0 ≤
                  (|x / 2| - |Real.sin (x / 2)|) *
                    (|x / 2| + |Real.sin (x / 2)|) := by
                exact mul_nonneg (sub_nonneg.mpr hs)
                  (add_nonneg (abs_nonneg _) (abs_nonneg _))
              have hsSq : Real.sin (x / 2) ^ 2 ≤ (x / 2) ^ 2 := by
                nlinarith [hp, sq_abs (x / 2), sq_abs (Real.sin (x / 2))]
              have hc : Real.cos x = 1 - 2 * Real.sin (x / 2) ^ 2 := by
                calc
                  Real.cos x = Real.cos (2 * (x / 2)) := by
                    congr 1
                    ring
                  _ = 1 - 2 * Real.sin (x / 2) ^ 2 := by
                    rw [Real.cos_two_mul]
                    nlinarith [Real.sin_sq_add_cos_sq (x / 2)]
              rw [abs_of_nonpos (sub_nonpos.mpr (Real.cos_le_one x)), hc]
              nlinarith [hsSq]
      _ = a ^ 2 / 2 := by
        field_simp [ne_of_gt hn]
  have hscaledCos' : Asymptotics.IsBigO atTop
      (fun n : ℕ =>
        (((fun x : ℝ => x - 1) ∘
          (fun n : ℕ => Real.cos (a / ((n + 1 : ℕ) : ℝ)))) n) *
          ((n + 1 : ℕ) : ℝ) ^ 2)
      (fun _ : ℕ => (1 : ℝ)) := by
    convert hscaledCos using 1 <;>
      ext n <;> simp [mul_comm]
  have hscaledLogLittle :
      (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ 2 *
        (Real.log (Real.cos (a / ((n + 1 : ℕ) : ℝ))) -
          (Real.cos (a / ((n + 1 : ℕ) : ℝ)) - 1))) =o[atTop]
        (fun _ : ℕ => (1 : ℝ)) := by
    have hprod := hlogcomp.mul_isBigO
      (Asymptotics.isBigO_refl
        (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ 2) atTop)
    have htrans := hprod.trans_isBigO hscaledCos'
    convert htrans using 1 <;>
      ext n <;> simp [mul_comm]
  have htLog : Tendsto
      (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ 2 *
        (Real.log (Real.cos (a / ((n + 1 : ℕ) : ℝ))) -
          (Real.cos (a / ((n + 1 : ℕ) : ℝ)) - 1)))
      atTop (nhds 0) := by
    exact (Asymptotics.isLittleO_one_iff ℝ).1 hscaledLogLittle
  have hrem := (gap5 a).2
  have hscaledRem : Asymptotics.IsBigO atTop
      (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ 2 * cosRemainder a (n + 1))
      (fun n : ℕ => 1 / (((n + 1 : ℕ) : ℝ) ^ 2)) := by
    have hm := (Asymptotics.isBigO_refl
      (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ 2) atTop).mul hrem
    convert hm using 1
    ext n
    have hn : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
    field_simp [ne_of_gt hn] <;> ring
  have hinv : Tendsto (fun n : ℕ => 1 / ((n + 1 : ℕ) : ℝ)) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop hk
  have hinvSq : Tendsto
      (fun n : ℕ => 1 / (((n + 1 : ℕ) : ℝ) ^ 2)) atTop (nhds 0) := by
    convert hinv.pow 2 using 1
    · ext n
      have hn : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
      field_simp [ne_of_gt hn] <;> ring
    · norm_num
  have hinvSqLittle :
      (fun n : ℕ => 1 / (((n + 1 : ℕ) : ℝ) ^ 2)) =o[atTop]
        (fun _ : ℕ => (1 : ℝ)) :=
    (Asymptotics.isLittleO_one_iff ℝ).2 hinvSq
  have hscaledRemLittle :
      (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ 2 * cosRemainder a (n + 1)) =o[atTop]
        (fun _ : ℕ => (1 : ℝ)) :=
    hscaledRem.trans_isLittleO hinvSqLittle
  have htRem : Tendsto
      (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ 2 * cosRemainder a (n + 1))
      atTop (nhds 0) :=
    (Asymptotics.isLittleO_one_iff ℝ).1 hscaledRemLittle
  convert htLog.add htRem using 1
  · ext n
    unfold scaledLogRemainder cosRemainder
    have hn : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
    field_simp [ne_of_gt hn] <;> ring
  · ring

theorem gap7 (a : ℝ) :
    ∃ N : ℕ, ∀ n ≥ N,
      rootProxy a n =
        Real.exp (-a ^ 2 / 2 + scaledLogRemainder a n) := by
  obtain ⟨N, hN⟩ := exists_nat_gt |a|
  refine ⟨N, ?_⟩
  intro n hn
  have hnreal : |a| < (n : ℝ) := lt_of_lt_of_le hN (by exact_mod_cast hn)
  have hnpos : 1 ≤ n := by
    have : (0 : ℝ) < (n : ℝ) := lt_of_le_of_lt (abs_nonneg a) hnreal
    exact_mod_cast (show (0 : ℕ) < n from by exact_mod_cast this)
  have hnrealpos : (0 : ℝ) < (n : ℝ) := by positivity
  have habs : |a / (n : ℝ)| < 1 := by
    rw [abs_div, abs_of_pos hnrealpos]
    exact (div_lt_one hnrealpos).2 hnreal
  have hpi : (1 : ℝ) < Real.pi / 2 := by
    nlinarith [Real.pi_gt_three]
  have hmem : a / (n : ℝ) ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    rcases abs_lt.mp habs with ⟨hl, hr⟩
    constructor <;> nlinarith
  have hcos : 0 < Real.cos (a / n) := Real.cos_pos_of_mem_Ioo hmem
  rw [gap4 a n hnpos hcos]
  unfold scaledLogRemainder
  congr 1
  ring

theorem gap8 (a : ℝ) :
    Tendsto (fun n : ℕ => rootProxy a (n + 1))
      atTop (nhds (Real.exp (-a ^ 2 / 2))) := by
  obtain ⟨N, hN⟩ := gap7 a
  have hin : Tendsto
      (fun n : ℕ => -a ^ 2 / 2 + scaledLogRemainder a (n + 1))
      atTop (nhds (-a ^ 2 / 2 + 0)) :=
    tendsto_const_nhds.add (gap6 a)
  have hout : Tendsto
      (fun n : ℕ => Real.exp (-a ^ 2 / 2 + scaledLogRemainder a (n + 1)))
      atTop (nhds (Real.exp (-a ^ 2 / 2))) := by
    simpa using Real.continuous_exp.continuousAt.tendsto.comp hin
  apply hout.congr'
  filter_upwards [eventually_ge_atTop N] with n hn
  exact (hN (n + 1) (by omega)).symm

theorem gap9 (a : ℝ) (ha : a ≠ 0) :
    Real.exp (-a ^ 2 / 2) < 1 := by
  rw [Real.exp_lt_one_iff]
  have hs : 0 < a ^ 2 := sq_pos_of_ne_zero ha
  nlinarith

theorem gap10 (a : ℝ) (ha : a ≠ 0) :
    ∃ q < 1, ∃ N : ℕ, ∀ n ≥ N, rootProxy a n ≤ q := by
  let L := Real.exp (-a ^ 2 / 2)
  let q := (L + 1) / 2
  have hL : L < 1 := gap9 a ha
  have hLq : L < q := by
    dsimp [q]
    linarith
  have hq : q < 1 := by
    dsimp [q]
    linarith
  have hev : ∀ᶠ n : ℕ in atTop, rootProxy a (n + 1) < q :=
    (tendsto_order.1 (gap8 a)).2 q hLq
  obtain ⟨K, hK⟩ := eventually_atTop.1 hev
  refine ⟨q, hq, K + 1, ?_⟩
  intro n hn
  have hkn : K ≤ n - 1 := by omega
  have h := hK (n - 1) hkn
  have heq : n - 1 + 1 = n := by omega
  simpa [heq] using le_of_lt h

theorem gap11 (a : ℝ) (ha : a ≠ 0) :
    converges a := by
  unfold converges
  obtain ⟨q, hq, Nq, hqN⟩ := gap10 a ha
  obtain ⟨Np, hpN⟩ := gap7 a
  let m := max Nq Np
  have hrpos : 0 < rootProxy a m := by
    rw [hpN m (le_max_right _ _)]
    positivity
  have hqpos : 0 < q := lt_of_lt_of_le hrpos (hqN m (le_max_left _ _))
  have hqnorm : ‖q‖ < 1 := by
    simpa [Real.norm_eq_abs, abs_of_pos hqpos] using hq
  refine (summable_geometric_of_norm_lt_one hqnorm).of_norm_bounded_eventually ?_
  have htail : ∀ᶠ n : ℕ in cofinite, max Nq Np ≤ n := by
    change {n : ℕ | max Nq Np ≤ n} ∈ cofinite
    rw [mem_cofinite]
    simpa only [Set.compl_setOf, Set.mem_setOf_eq, not_le] using
      (Set.finite_Iio (max Nq Np))
  filter_upwards [htail] with n hn
  have hrootpos : 0 < rootProxy a (n + 1) := by
    rw [hpN (n + 1) (by omega)]
    positivity
  have hrootle : rootProxy a (n + 1) ≤ q := hqN (n + 1) (by omega)
  have hterm : term a (n + 1) = rootProxy a (n + 1) ^ (n + 1) := by
    unfold term rootProxy
    rw [← pow_mul]
    congr 1
  rw [hterm, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (le_of_lt hrootpos) _)]
  have hpw : rootProxy a (n + 1) ^ (n + 1) ≤ q ^ (n + 1) := by
    exact pow_le_pow_left₀ (le_of_lt hrootpos) hrootle (n + 1)
  calc
    rootProxy a (n + 1) ^ (n + 1) ≤ q ^ (n + 1) := hpw
    _ = q ^ n * q := by rw [pow_succ]
    _ ≤ q ^ n := by
      have hqn : 0 ≤ q ^ n := pow_nonneg (le_of_lt hqpos) n
      nlinarith

theorem gap12 (a : ℝ) :
    a ∈ {r : ℝ | r ≠ 0} ↔ converges a := by
  simp only [Set.mem_setOf_eq]
  constructor
  · exact gap11 a
  · intro hconv ha
    exact gap2 a ha hconv

end

end ProofGap.Exercise2636
