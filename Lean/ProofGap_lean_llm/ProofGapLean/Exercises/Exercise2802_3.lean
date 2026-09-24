import ProofGapLean.Prelude.Analysis
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Neighborhoods
import Mathlib.Tactic.Positivity

namespace ProofGap.Exercise2802_3

noncomputable section

open Filter
open scoped Interval Topology

def term (α : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  Real.rpow (n : ℝ) α * x * Real.exp (-(n : ℝ) * x)

def pointwiseLimit (_ : ℝ) : ℝ := 0

def integralSeq (α : ℝ) (n : ℕ) : ℝ :=
  ∫ x in (0 : ℝ)..1, term α n x

def scaledIntegralSeq (α : ℝ) (n : ℕ) : ℝ :=
  Real.rpow (n : ℝ) α *
    ∫ x in (0 : ℝ)..1, x * Real.exp (-(n : ℝ) * x)

def integratedForm (α : ℝ) (n : ℕ) : ℝ :=
  Real.rpow (n : ℝ) α *
    (-(1 / (n : ℝ)) * Real.exp (-(n : ℝ)) -
      1 / (n : ℝ) ^ 2 * Real.exp (-(n : ℝ)) +
      1 / (n : ℝ) ^ 2)

def simplifiedForm (α : ℝ) (n : ℕ) : ℝ :=
  Real.rpow (n : ℝ) (α - 2) *
    (1 - Real.exp (-(n : ℝ)) - (n : ℝ) * Real.exp (-(n : ℝ)))

def InterchangeHolds (α : ℝ) : Prop :=
  Tendsto (integralSeq α) atTop
    (𝓝 (∫ x in (0 : ℝ)..1, pointwiseLimit x))

private theorem limit_characterizations (α : ℝ) :
    (Tendsto (integralSeq α) atTop (𝓝 0) ↔ α < 2) ∧
    (Tendsto (scaledIntegralSeq α) atTop (𝓝 0) ↔ α < 2) ∧
    (Tendsto (integratedForm α) atTop (𝓝 0) ↔ α < 2) ∧
    (Tendsto (simplifiedForm α) atTop (𝓝 0) ↔ α < 2) := by
  have hAB :
      Tendsto (integralSeq α) atTop (𝓝 0) ↔
        Tendsto (scaledIntegralSeq α) atTop (𝓝 0) := by
    apply tendsto_congr'
    filter_upwards with n
    simp [integralSeq, scaledIntegralSeq, term, mul_assoc]
  have hBC :
      Tendsto (scaledIntegralSeq α) atTop (𝓝 0) ↔
        Tendsto (integratedForm α) atTop (𝓝 0) := by
    apply tendsto_congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hnpos : (0 : ℝ) < (n : ℝ) :=
      Nat.cast_pos.mpr (lt_of_lt_of_le Nat.zero_lt_one hn)
    have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hnpos
    have hlin (x : ℝ) :
        HasDerivAt (fun y : ℝ => -(n : ℝ) * y) (-(n : ℝ)) x := by
      convert (hasDerivAt_id x).const_mul (-(n : ℝ)) using 1 <;>
        simp
    have he (x : ℝ) :
        HasDerivAt (fun y : ℝ => Real.exp (-(n : ℝ) * y))
          (Real.exp (-(n : ℝ) * x) * (-(n : ℝ))) x := by
      exact (Real.hasDerivAt_exp (-(n : ℝ) * x)).comp x (hlin x)
    have hderiv (x : ℝ) :
        HasDerivAt
          (fun y : ℝ =>
            (-(1 / (n : ℝ)) * y) * Real.exp (-(n : ℝ) * y) -
              (1 / (n : ℝ) ^ 2) * Real.exp (-(n : ℝ) * y))
          (x * Real.exp (-(n : ℝ) * x)) x := by
      convert
        (((hasDerivAt_id x).const_mul (-(1 / (n : ℝ)))).mul (he x)).sub
          ((he x).const_mul (1 / (n : ℝ) ^ 2)) using 1 <;>
        simp [id] <;>
        field_simp [hn0] <;>
        ring
    have hcontExp :
        Continuous (fun x : ℝ => Real.exp (-(n : ℝ) * x)) :=
      Real.continuous_exp.comp (continuous_const.mul continuous_id)
    have hint :
        IntervalIntegrable
          (fun x : ℝ => x * Real.exp (-(n : ℝ) * x))
          MeasureTheory.volume 0 1 :=
      (continuous_id.mul hcontExp).intervalIntegrable (0 : ℝ) 1
    have hi :
        (∫ x in (0 : ℝ)..1, x * Real.exp (-(n : ℝ) * x)) =
          ((-(1 / (n : ℝ)) * (1 : ℝ)) * Real.exp (-(n : ℝ) * 1) -
              (1 / (n : ℝ) ^ 2) * Real.exp (-(n : ℝ) * 1)) -
            ((-(1 / (n : ℝ)) * (0 : ℝ)) * Real.exp (-(n : ℝ) * 0) -
              (1 / (n : ℝ) ^ 2) * Real.exp (-(n : ℝ) * 0)) := by
      exact intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun x _ => hderiv x) hint
    have hi' :
        (∫ x in (0 : ℝ)..1, x * Real.exp (-(n : ℝ) * x)) =
          -(1 / (n : ℝ)) * Real.exp (-(n : ℝ)) -
            1 / (n : ℝ) ^ 2 * Real.exp (-(n : ℝ)) +
            1 / (n : ℝ) ^ 2 := by
      simpa [hn0] using hi
    simp only [scaledIntegralSeq, integratedForm]
    rw [hi']
  have hCD :
      Tendsto (integratedForm α) atTop (𝓝 0) ↔
        Tendsto (simplifiedForm α) atTop (𝓝 0) := by
    apply tendsto_congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hnpos : (0 : ℝ) < (n : ℝ) :=
      Nat.cast_pos.mpr (lt_of_lt_of_le Nat.zero_lt_one hn)
    have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hnpos
    have hpow :
        Real.rpow (n : ℝ) (α - 2) =
          Real.rpow (n : ℝ) α / (n : ℝ) ^ 2 := by
      simpa [Real.rpow_natCast] using
        (Real.rpow_sub hnpos α (2 : ℝ))
    unfold integratedForm simplifiedForm
    rw [hpow]
    field_simp [hn0]
    ring
  have hcast :
      Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hexp :
      Tendsto (fun n : ℕ => Real.exp (-(n : ℝ))) atTop (𝓝 0) := by
    simpa only [Function.comp_apply, pow_zero, one_mul] using
      (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 0).comp hcast
  have hnexp :
      Tendsto (fun n : ℕ => (n : ℝ) * Real.exp (-(n : ℝ))) atTop (𝓝 0) := by
    simpa only [Function.comp_apply, pow_one] using
      (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp hcast
  have hb :
      Tendsto
        (fun n : ℕ =>
          1 - Real.exp (-(n : ℝ)) -
            (n : ℝ) * Real.exp (-(n : ℝ)))
        atTop (𝓝 1) := by
    have hone : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) :=
      tendsto_const_nhds
    simpa using (hone.sub hexp).sub hnexp
  have hD :
      Tendsto (simplifiedForm α) atTop (𝓝 0) ↔ α < 2 := by
    constructor
    · intro hs
      by_contra hnot
      have hbeta : 0 ≤ α - 2 := by linarith
      have hlower :
          ∀ᶠ n : ℕ in atTop,
            (1 / 2 : ℝ) <
              1 - Real.exp (-(n : ℝ)) -
                (n : ℝ) * Real.exp (-(n : ℝ)) :=
        ((tendsto_order.1 hb).1 (1 / 2 : ℝ) (by norm_num))
      have hupper :
          ∀ᶠ n : ℕ in atTop, simplifiedForm α n < (1 / 2 : ℝ) :=
        ((tendsto_order.1 hs).2 (1 / 2 : ℝ) (by norm_num))
      have hfalse : ∀ᶠ _n : ℕ in atTop, False := by
        filter_upwards [eventually_ge_atTop 1, hlower, hupper] with n hn hbn hsn
        have hnbase : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
        have hp : 1 ≤ Real.rpow (n : ℝ) (α - 2) :=
          Real.one_le_rpow hnbase hbeta
        have hbnonneg :
            0 ≤ 1 - Real.exp (-(n : ℝ)) -
              (n : ℝ) * Real.exp (-(n : ℝ)) := by
          linarith
        have hval : (1 / 2 : ℝ) < simplifiedForm α n := by
          rw [simplifiedForm]
          calc
            (1 / 2 : ℝ) <
                1 - Real.exp (-(n : ℝ)) -
                  (n : ℝ) * Real.exp (-(n : ℝ)) := hbn
            _ = 1 *
                (1 - Real.exp (-(n : ℝ)) -
                  (n : ℝ) * Real.exp (-(n : ℝ))) := by ring
            _ ≤ Real.rpow (n : ℝ) (α - 2) *
                (1 - Real.exp (-(n : ℝ)) -
                  (n : ℝ) * Real.exp (-(n : ℝ))) :=
              mul_le_mul_of_nonneg_right hp hbnonneg
        linarith
      rcases hfalse.exists with ⟨n, hn⟩
      exact hn
    · intro hα
      have hβ : 0 < 2 - α := by linarith
      have hlog :
          Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
        Real.tendsto_log_atTop.comp hcast
      have hmul :
          Tendsto (fun n : ℕ => Real.log (n : ℝ) * (2 - α))
            atTop atTop := by
        refine tendsto_atTop.2 ?_
        intro b
        filter_upwards [tendsto_atTop.1 hlog (b / (2 - α))] with n hn
        exact (div_le_iff₀ hβ).1 hn
      have hexppow :
          Tendsto
            (fun n : ℕ => Real.exp (Real.log (n : ℝ) * (2 - α)))
            atTop atTop :=
        Real.tendsto_exp_atTop.comp hmul
      have heqpow :
          (fun n : ℕ => Real.exp (Real.log (n : ℝ) * (2 - α))) =ᶠ[atTop]
            (fun n : ℕ => Real.rpow (n : ℝ) (2 - α)) := by
        filter_upwards [eventually_ge_atTop 1] with n hn
        have hnpos : (0 : ℝ) < (n : ℝ) :=
          Nat.cast_pos.mpr (lt_of_lt_of_le Nat.zero_lt_one hn)
        have hrpow :
            Real.rpow (n : ℝ) (2 - α) =
              Real.exp (Real.log (n : ℝ) * (2 - α)) :=
          Real.rpow_def_of_pos hnpos (y := 2 - α)
        exact hrpow.symm
      have hq :
          Tendsto (fun n : ℕ => Real.rpow (n : ℝ) (2 - α))
            atTop atTop :=
        hexppow.congr' heqpow
      have hinv :
          Tendsto (fun n : ℕ => (Real.rpow (n : ℝ) (2 - α))⁻¹)
            atTop (𝓝 0) :=
        tendsto_inv_atTop_zero.comp hq
      have heq :
          (fun n : ℕ => (Real.rpow (n : ℝ) (2 - α))⁻¹) =ᶠ[atTop]
            (fun n : ℕ => Real.rpow (n : ℝ) (α - 2)) := by
        filter_upwards [eventually_ge_atTop 1] with n hn
        have hnpos : (0 : ℝ) < (n : ℝ) :=
          Nat.cast_pos.mpr (lt_of_lt_of_le Nat.zero_lt_one hn)
        have hrpow :
            Real.rpow (n : ℝ) (2 - α) =
              Real.exp (Real.log (n : ℝ) * (2 - α)) :=
          Real.rpow_def_of_pos hnpos (y := 2 - α)
        have hrpowneg :
            Real.rpow (n : ℝ) (-(2 - α)) =
              Real.exp (Real.log (n : ℝ) * (-(2 - α))) :=
          Real.rpow_def_of_pos hnpos (y := -(2 - α))
        rw [show α - 2 = -(2 - α) by ring]
        calc
          (Real.rpow (n : ℝ) (2 - α))⁻¹ =
              (Real.exp (Real.log (n : ℝ) * (2 - α)))⁻¹ :=
                congrArg (fun z : ℝ => z⁻¹) hrpow
          _ = Real.exp (-(Real.log (n : ℝ) * (2 - α))) := by
                rw [Real.exp_neg]
          _ = Real.exp (Real.log (n : ℝ) * (-(2 - α))) := by
                congr 1
                ring
          _ = Real.rpow (n : ℝ) (-(2 - α)) := hrpowneg.symm
      have hp :
          Tendsto (fun n : ℕ => Real.rpow (n : ℝ) (α - 2))
            atTop (𝓝 0) :=
        hinv.congr' heq
      simpa [simplifiedForm] using hp.mul hb
  exact
    ⟨hAB.trans (hBC.trans (hCD.trans hD)),
      hBC.trans (hCD.trans hD),
      hCD.trans hD,
      hD⟩

theorem gap1 :
    ∀ α : ℝ, α < 2 → InterchangeHolds α := by
  intro α hα
  simpa [InterchangeHolds, pointwiseLimit] using
    (limit_characterizations α).1.mpr hα

theorem gap2 :
    ∀ α : ℝ, α < 2 →
      InterchangeHolds α ↔
        (∫ x in (0 : ℝ)..1, pointwiseLimit x) =
          ∫ _x in (0 : ℝ)..1, (0 : ℝ) := by
  intro α
  constructor
  · intro _
    simp [pointwiseLimit]
  · intro _
    exact gap1 α

theorem gap3 :
    ∀ α : ℝ, α < 2 →
      InterchangeHolds α ↔
        (∫ _x in (0 : ℝ)..1, (0 : ℝ)) = 0 := by
  intro α
  constructor
  · intro _
    simp
  · intro _
    exact gap1 α

theorem gap4 :
    ∀ α : ℝ, α < 2 →
      InterchangeHolds α ↔
        (∫ x in (0 : ℝ)..1, pointwiseLimit x) = 0 := by
  intro α
  constructor
  · intro _
    simp [pointwiseLimit]
  · intro _
    exact gap1 α

theorem gap5 :
    ∀ α : ℝ,
      Tendsto (integralSeq α) atTop (𝓝 0) ↔
        Tendsto (scaledIntegralSeq α) atTop (𝓝 0) := by
  intro α
  exact (limit_characterizations α).1.trans
    (limit_characterizations α).2.1.symm

theorem gap6 :
    ∀ α : ℝ,
      Tendsto (scaledIntegralSeq α) atTop (𝓝 0) ↔
        Tendsto (integratedForm α) atTop (𝓝 0) := by
  intro α
  exact (limit_characterizations α).2.1.trans
    (limit_characterizations α).2.2.1.symm

theorem gap7 :
    ∀ α : ℝ,
      Tendsto (integratedForm α) atTop (𝓝 0) ↔
        Tendsto (simplifiedForm α) atTop (𝓝 0) := by
  intro α
  exact (limit_characterizations α).2.2.1.trans
    (limit_characterizations α).2.2.2.symm

theorem gap8 :
    ∀ α : ℝ,
      Tendsto (integralSeq α) atTop (𝓝 0) ↔
        Tendsto (simplifiedForm α) atTop (𝓝 0) := by
  intro α
  exact (limit_characterizations α).1.trans
    (limit_characterizations α).2.2.2.symm

theorem gap9 :
    ∀ α : ℝ, InterchangeHolds α →
      Tendsto (integralSeq α) atTop (𝓝 0) := by
  intro α h
  simpa [InterchangeHolds, pointwiseLimit] using h

theorem gap10 :
    ∀ α : ℝ, α ∈ {a : ℝ | a < 2} ↔ InterchangeHolds α := by
  intro α
  simpa [InterchangeHolds, pointwiseLimit] using
    (limit_characterizations α).1.symm

end

end ProofGap.Exercise2802_3
