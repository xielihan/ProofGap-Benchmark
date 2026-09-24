import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.LHopital
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Order.Filter.Tendsto
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Neighborhoods
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise2816

noncomputable section

open Filter
open scoped BigOperators Topology

def coefficient (n : ℕ) : ℝ :=
  (1 + 1 / (n : ℝ)) ^ (n ^ 2)

def powerTerm (n : ℕ) (x : ℝ) : ℝ :=
  coefficient n * x ^ n

def SeriesConvergesAt (x : ℝ) : Prop :=
  Summable (fun k : ℕ => powerTerm (k + 1) x)

def HasConvergenceRadius (r : ℝ) : Prop :=
  (∀ x : ℝ, |x| < r → SeriesConvergesAt x) ∧
    (∀ x : ℝ, r < |x| → ¬ SeriesConvergesAt x)

def ratioFormula (n : ℕ) : ℝ :=
  (((1 + 1 / (n : ℝ)) ^ n) /
      ((1 + 1 / ((n + 1 : ℕ) : ℝ)) ^ (n + 1))) ^ n /
    ((1 + 1 / ((n + 1 : ℕ) : ℝ)) ^ (n + 1))

def boundaryMagnitude (n : ℕ) : ℝ :=
  coefficient n * (1 / Real.exp 1) ^ n

private theorem boundaryMagnitude_succ_tendsto :
    Tendsto (fun n : ℕ => boundaryMagnitude (n + 1)) atTop
      (𝓝 (Real.exp (-1 / 2))) := by
  have hlog :
      Tendsto
        (fun t : ℝ => (Real.log (1 + t) - t) / t ^ 2)
        (𝓝[>] 0) (𝓝 (-1 / 2)) := by
    have hi : Tendsto (fun t : ℝ => t) (𝓝[>] 0) (𝓝 0) :=
      tendsto_id.mono_left inf_le_left
    have hone : Tendsto (fun t : ℝ => 1 + t) (𝓝[>] 0) (𝓝 1) := by
      convert tendsto_const_nhds.add hi using 1 <;> norm_num
    have hnum :
        Tendsto (fun t : ℝ => Real.log (1 + t) - t) (𝓝[>] 0) (𝓝 0) := by
      have hlog1 :=
        (Real.hasDerivAt_log (by norm_num : (1 : ℝ) ≠ 0)).continuousAt.tendsto.comp hone
      convert hlog1.sub hi using 1 <;> norm_num
    have hden : Tendsto (fun t : ℝ => t ^ 2) (𝓝[>] 0) (𝓝 0) := by
      convert hi.pow 2 using 1 <;> norm_num
    have hderiv :
        Tendsto
          (fun t : ℝ => (1 / (1 + t) - 1) / (2 * t))
          (𝓝[>] 0) (𝓝 (-1 / 2)) := by
      have heq :
          (fun t : ℝ => (1 / (1 + t) - 1) / (2 * t)) =ᶠ[𝓝[>] 0]
            fun t : ℝ => -1 / (2 * (1 + t)) := by
        filter_upwards [self_mem_nhdsWithin] with t ht
        have ht0 : t ≠ 0 := ne_of_gt ht
        have ht1 : 1 + t ≠ 0 := by
          have htpos : 0 < t := ht
          nlinarith
        field_simp [ht0, ht1] <;> ring
      rw [tendsto_congr' heq]
      have hdenlim :
          Tendsto (fun t : ℝ => 2 * (1 + t)) (𝓝[>] 0) (𝓝 2) := by
        convert tendsto_const_nhds.mul hone using 1 <;> norm_num
      convert tendsto_const_nhds.div hdenlim (by norm_num : (2 : ℝ) ≠ 0) using 1 <;>
        norm_num
    have hfd :
        ∀ᶠ t : ℝ in 𝓝[>] 0,
          HasDerivAt (fun t : ℝ => Real.log (1 + t) - t)
            (1 / (1 + t) - 1) t := by
      filter_upwards [self_mem_nhdsWithin] with t ht
      have ht1 : 1 + t ≠ 0 := by
        have htpos : 0 < t := ht
        nlinarith
      simpa [Function.comp_def, one_div] using
        (((Real.hasDerivAt_log ht1).comp t
          ((hasDerivAt_id t).const_add 1)).sub (hasDerivAt_id t))
    have hgd :
        ∀ᶠ t : ℝ in 𝓝[>] 0,
          HasDerivAt (fun t : ℝ => t ^ 2) (2 * t) t := by
      filter_upwards with t
      simpa using (hasDerivAt_id t).pow 2
    have hne : ∀ᶠ t : ℝ in 𝓝[>] 0, 2 * t ≠ 0 := by
      filter_upwards [self_mem_nhdsWithin] with t ht
      exact mul_ne_zero (by norm_num) (ne_of_gt ht)
    exact HasDerivAt.lhopital_zero_nhdsGT hfd hgd hne hnum hden hderiv
  have hnadd : Tendsto (fun n : ℕ => n + 1) atTop atTop :=
    (tendsto_add_atTop_iff_nat 1).2 tendsto_id
  have hcast :
      Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hnadd
  have ht_nhds :
      Tendsto (fun n : ℕ => 1 / ((n + 1 : ℕ) : ℝ)) atTop (𝓝 0) := by
    exact tendsto_const_nhds.div_atTop hcast
  have ht :
      Tendsto (fun n : ℕ => 1 / ((n + 1 : ℕ) : ℝ)) atTop (𝓝[>] 0) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · exact ht_nhds
    · exact Filter.Eventually.of_forall (fun n => by
        change 0 < 1 / ((n + 1 : ℕ) : ℝ)
        positivity)
  have hexponent :
      Tendsto
        (fun n : ℕ =>
          (((n + 1 : ℕ) : ℝ) ^ 2) *
              Real.log (1 + 1 / ((n + 1 : ℕ) : ℝ)) -
            ((n + 1 : ℕ) : ℝ))
        atTop (𝓝 (-1 / 2)) := by
    convert hlog.comp ht using 1
    funext n
    have hn : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
    change
      (((n + 1 : ℕ) : ℝ) ^ 2) *
            Real.log (1 + 1 / ((n + 1 : ℕ) : ℝ)) -
          ((n + 1 : ℕ) : ℝ) =
        (Real.log (1 + 1 / ((n + 1 : ℕ) : ℝ)) -
            1 / ((n + 1 : ℕ) : ℝ)) /
          (1 / ((n + 1 : ℕ) : ℝ)) ^ 2
    field_simp [hn.ne'] <;> ring
  have hexp := (Real.continuous_exp.tendsto (-1 / 2)).comp hexponent
  convert hexp using 1
  funext n
  unfold boundaryMagnitude coefficient
  have hn : 0 < 1 + 1 / ((n + 1 : ℕ) : ℝ) := by positivity
  have he : 1 / Real.exp 1 = Real.exp (-1) := by
    rw [Real.exp_neg]
    norm_num
  rw [← Real.exp_log hn, he, ← Real.exp_nat_mul, ← Real.exp_nat_mul,
    ← Real.exp_add]
  simp only [Function.comp_apply]
  congr 1
  push_cast
  ring

theorem gap1 :
    (fun n : ℕ => |coefficient (n + 1) / coefficient (n + 2)|) =
      fun n : ℕ => ratioFormula (n + 1) := by
  funext n
  have h₁ : 0 < coefficient (n + 1) := by
    unfold coefficient
    positivity
  have h₂ : 0 < coefficient (n + 2) := by
    unfold coefficient
    positivity
  rw [abs_of_pos (div_pos h₁ h₂)]
  unfold coefficient ratioFormula
  rw [div_pow, div_div]
  congr 1
  · rw [← pow_mul]
    congr 1
    ring
  · rw [← pow_mul, ← pow_add]
    congr 1
    ring

theorem gap2 :
    Tendsto ratioFormula atTop (𝓝 (1 / Real.exp 1)) := by
  have hb₂ :
      Tendsto (fun n : ℕ => boundaryMagnitude (n + 2)) atTop
        (𝓝 (Real.exp (-1 / 2))) := by
    simpa [Nat.add_assoc] using
      (tendsto_add_atTop_iff_nat 1).2 boundaryMagnitude_succ_tendsto
  have hc : Real.exp (-1 / 2) ≠ 0 := Real.exp_ne_zero _
  have hquot :
      Tendsto
        (fun n : ℕ => boundaryMagnitude (n + 1) /
          boundaryMagnitude (n + 2) / Real.exp 1)
        atTop (𝓝 (1 / Real.exp 1)) := by
    convert (boundaryMagnitude_succ_tendsto.div hb₂ hc).div_const
      (Real.exp 1) using 1 <;>
      field_simp [hc, Real.exp_ne_zero]
  have hrel :
      (fun n : ℕ => |coefficient (n + 1) / coefficient (n + 2)|) =
        fun n : ℕ => boundaryMagnitude (n + 1) /
          boundaryMagnitude (n + 2) / Real.exp 1 := by
    funext n
    have h₁ : 0 < coefficient (n + 1) := by
      unfold coefficient
      positivity
    have h₂ : 0 < coefficient (n + 2) := by
      unfold coefficient
      positivity
    rw [abs_of_pos (div_pos h₁ h₂)]
    unfold boundaryMagnitude
    field_simp [Real.exp_ne_zero, pow_succ]
    have hp :
        (1 / Real.exp 1) ^ (n + 2) =
          (1 / Real.exp 1) ^ (n + 1) * (1 / Real.exp 1) := by
      rw [show n + 2 = (n + 1) + 1 by ring, pow_succ]
    calc
      Real.exp 1 * (1 / Real.exp 1) ^ (n + 2) =
          Real.exp 1 *
            ((1 / Real.exp 1) ^ (n + 1) * (1 / Real.exp 1)) := by
        rw [hp]
      _ = (1 / Real.exp 1) ^ (n + 1) *
            (Real.exp 1 * (1 / Real.exp 1)) := by
        ring
      _ = (1 / Real.exp 1) ^ (n + 1) := by
        simp [Real.exp_ne_zero]
  have hshift :
      Tendsto (fun n : ℕ => ratioFormula (n + 1)) atTop
        (𝓝 (1 / Real.exp 1)) := by
    rw [← gap1, hrel]
    exact hquot
  exact (tendsto_add_atTop_iff_nat 1).1 hshift

theorem gap3 :
    Tendsto
      (fun n : ℕ => |coefficient (n + 1) / coefficient (n + 2)|)
      atTop (𝓝 (1 / Real.exp 1)) := by
  rw [gap1]
  exact (tendsto_add_atTop_iff_nat 1).2 gap2

theorem gap4 :
    HasConvergenceRadius (1 / Real.exp 1) := by
  constructor
  · intro x hx
    let q : ℝ := Real.exp 1 * |x|
    have hq0 : 0 ≤ q := by
      dsimp [q]
      positivity
    have hq : q < 1 := by
      dsimp [q]
      calc
        Real.exp 1 * |x| < Real.exp 1 * (1 / Real.exp 1) :=
          mul_lt_mul_of_pos_left hx (Real.exp_pos 1)
        _ = 1 := by field_simp [Real.exp_ne_zero]
    have hgeo : Summable (fun n : ℕ => q ^ (n + 1)) := by
      have hs := summable_geometric_of_norm_lt_one
        (show ‖q‖ < 1 by
          simpa [Real.norm_eq_abs, abs_of_nonneg hq0] using hq)
      simpa [pow_succ, mul_comm] using hs.mul_left q
    refine Summable.of_norm_bounded hgeo ?_
    intro n
    have hbase :
        1 + 1 / ((n + 1 : ℕ) : ℝ) ≤
          Real.exp (1 / ((n + 1 : ℕ) : ℝ)) := by
      simpa [add_comm] using
        Real.add_one_le_exp (1 / ((n + 1 : ℕ) : ℝ))
    have hcoeff : coefficient (n + 1) ≤ (Real.exp 1) ^ (n + 1) := by
      unfold coefficient
      calc
        (1 + 1 / ((n + 1 : ℕ) : ℝ)) ^ ((n + 1) ^ 2) ≤
            (Real.exp (1 / ((n + 1 : ℕ) : ℝ))) ^ ((n + 1) ^ 2) := by
              gcongr
        _ = (Real.exp 1) ^ (n + 1) := by
              rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]
              congr 1
              push_cast
              field_simp <;> ring
    have hcp : 0 ≤ coefficient (n + 1) := by
      unfold coefficient
      positivity
    calc
      ‖powerTerm (n + 1) x‖ = coefficient (n + 1) * |x| ^ (n + 1) := by
        simp [powerTerm, Real.norm_eq_abs, abs_of_nonneg hcp]
      _ ≤ (Real.exp 1) ^ (n + 1) * |x| ^ (n + 1) := by
        gcongr
      _ = q ^ (n + 1) := by simp [q, mul_pow]
  · intro x hx hs
    have hq : 1 < Real.exp 1 * |x| := by
      calc
        1 = Real.exp 1 * (1 / Real.exp 1) := by
          field_simp [Real.exp_ne_zero]
        _ < Real.exp 1 * |x| :=
          mul_lt_mul_of_pos_left hx (Real.exp_pos 1)
    have ht0 :
        Tendsto (fun n : ℕ => ‖powerTerm (n + 1) x‖) atTop (𝓝 0) := by
      have h := hs.tendsto_atTop_zero
      simpa using h.norm
    have hc : 0 < Real.exp (-1 / 2) := Real.exp_pos _
    have hevb :
        ∀ᶠ n : ℕ in atTop,
          Real.exp (-1 / 2) / 2 < boundaryMagnitude (n + 1) :=
      (tendsto_order.1 boundaryMagnitude_succ_tendsto).1 _ (by linarith)
    have hevnorm :
        ∀ᶠ n : ℕ in atTop,
          Real.exp (-1 / 2) / 2 < ‖powerTerm (n + 1) x‖ := by
      filter_upwards [hevb] with n hn
      have hpow : 1 ≤ (Real.exp 1 * |x|) ^ (n + 1) :=
        one_le_pow₀ (le_of_lt hq)
      have hexppow :
          Real.exp ((n : ℝ) + 1) = Real.exp 1 * Real.exp 1 ^ n := by
        have h : Real.exp (1 + (n : ℝ)) = Real.exp 1 * Real.exp 1 ^ n := by
          rw [← Real.exp_nat_mul, ← Real.exp_add]
          congr 1
          ring
        simpa [add_comm] using h
      have heq :
          ‖powerTerm (n + 1) x‖ =
            boundaryMagnitude (n + 1) *
              (Real.exp 1 * |x|) ^ (n + 1) := by
        unfold powerTerm boundaryMagnitude
        have hcp : 0 ≤ coefficient (n + 1) := by
          unfold coefficient
          positivity
        simp [Real.norm_eq_abs, abs_of_nonneg hcp]
        field_simp [Real.exp_ne_zero] <;>
          rw [hexppow] <;>
          simp only [mul_pow, pow_succ] <;>
          ring
      rw [heq]
      nlinarith [show 0 < boundaryMagnitude (n + 1) by
        unfold boundaryMagnitude coefficient
        positivity]
    have hevzero :
        ∀ᶠ n : ℕ in atTop,
          ‖powerTerm (n + 1) x‖ < Real.exp (-1 / 2) / 2 :=
      (tendsto_order.1 ht0).2 _ (by positivity)
    rcases (hevnorm.and hevzero).exists with ⟨n, hn₁, hn₂⟩
    linarith

theorem gap5 :
    ∀ x : ℝ, x ∈ Set.Ioo (-1 / Real.exp 1) (1 / Real.exp 1) →
      SeriesConvergesAt x := by
  intro x hx
  apply gap4.1 x
  exact (abs_lt).2 (by
    constructor
    · simpa only [neg_div] using hx.1
    · exact hx.2)

theorem gap6 :
    Tendsto (fun n : ℕ => boundaryMagnitude (n + 1))
      atTop (𝓝 (Real.exp (-1 / 2))) := by
  exact boundaryMagnitude_succ_tendsto

theorem gap7 :
    Real.exp (-1 / 2) ≠ 0 := by
  exact Real.exp_ne_zero _

theorem gap8 :
    ∀ x : ℝ, |x| = 1 / Real.exp 1 → ¬ SeriesConvergesAt x := by
  intro x hx hs
  have ht0 :
      Tendsto (fun n : ℕ => |powerTerm (n + 1) x|) atTop (𝓝 0) := by
    have h := hs.tendsto_atTop_zero
    simpa [Real.norm_eq_abs] using h.norm
  have heq :
      (fun n : ℕ => |powerTerm (n + 1) x|) =
        fun n : ℕ => boundaryMagnitude (n + 1) := by
    funext n
    unfold powerTerm boundaryMagnitude
    have hcp : 0 ≤ coefficient (n + 1) := by
      unfold coefficient
      positivity
    rw [abs_mul, abs_of_nonneg hcp, abs_pow, hx]
  have hb :
      Tendsto (fun n : ℕ => |powerTerm (n + 1) x|) atTop
        (𝓝 (Real.exp (-1 / 2))) := by
    rw [heq]
    exact gap6
  have hz : (0 : ℝ) = Real.exp (-1 / 2) := tendsto_nhds_unique ht0 hb
  exact gap7 hz.symm

theorem gap9 :
    ∀ x : ℝ,
      x ∈ Set.Ioo (-1 / Real.exp 1) (1 / Real.exp 1) ↔
        SeriesConvergesAt x := by
  intro x
  constructor
  · exact gap5 x
  · intro hs
    have hle : |x| ≤ 1 / Real.exp 1 := by
      apply le_of_not_gt
      intro hgt
      exact (gap4.2 x hgt) hs
    have hne : |x| ≠ 1 / Real.exp 1 := by
      intro heq
      exact (gap8 x heq) hs
    have hlt : |x| < 1 / Real.exp 1 := lt_of_le_of_ne hle hne
    have hi := abs_lt.1 hlt
    constructor
    · simpa only [neg_div] using hi.1
    · exact hi.2

end

end ProofGap.Exercise2816
