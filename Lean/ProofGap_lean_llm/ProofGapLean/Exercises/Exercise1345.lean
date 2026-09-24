import ProofGapLean.Prelude.Analysis
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Neighborhoods

namespace ProofGap.Exercise1345

noncomputable section

def HasRightLimitAtZero (f : ℝ → ℝ) (L : ℝ) : Prop :=
  Filter.Tendsto f (nhdsWithin 0 (Set.Ioi 0)) (nhds L)

def logExponent (k x : ℝ) : ℝ := k / (1 + Real.log x) * Real.log x
def derivativeRatio (k x : ℝ) : ℝ := k * ((1 / x) / (1 / x))
def powerForm (k x : ℝ) : ℝ := Real.rpow x (k / (1 + Real.log x))

private theorem logExponent_limit_aux (k : ℝ) :
    HasRightLimitAtZero (logExponent k) k := by
  unfold HasRightLimitAtZero
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hlog :
      Filter.Tendsto Real.log (nhdsWithin 0 (Set.Ioi 0)) Filter.atBot :=
    Real.tendsto_log_nhdsGT_zero
  have htail :
      ∀ᶠ y : ℝ in Filter.atBot, y < -(|k| / ε + 2) := by
    rw [Filter.eventually_atBot]
    refine ⟨-(|k| / ε + 2) - 1, ?_⟩
    intro y hy
    linarith
  have hev :
      ∀ᶠ x in nhdsWithin 0 (Set.Ioi 0),
        Real.log x < -(|k| / ε + 2) :=
    hlog.eventually htail
  filter_upwards [hev] with x hx
  rw [Real.dist_eq]
  have hden : 1 + Real.log x < 0 := by
    have habs : 0 ≤ |k| := abs_nonneg k
    have hdiv : 0 ≤ |k| / ε := div_nonneg habs (le_of_lt hε)
    linarith
  have hden_ne : 1 + Real.log x ≠ 0 := ne_of_lt hden
  have hid :
      logExponent k x - k = -(k / (1 + Real.log x)) := by
    unfold logExponent
    field_simp [hden_ne] <;> ring
  rw [hid, abs_neg, abs_div, abs_of_neg hden]
  have hratio : |k| / ε < -(1 + Real.log x) := by
    linarith
  apply (div_lt_iff₀ (neg_pos.mpr hden)).2
  calc
    |k| = ε * (|k| / ε) := by field_simp [ne_of_gt hε]
    _ < ε * (-(1 + Real.log x)) := mul_lt_mul_of_pos_left hratio hε

theorem gap1 (k : ℝ) :
    HasRightLimitAtZero (logExponent k) k ↔
      HasRightLimitAtZero (derivativeRatio k) k := by
  constructor
  · intro _
    unfold HasRightLimitAtZero
    apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hxpos : 0 < x := hx
    have hx0 : x ≠ 0 := ne_of_gt hxpos
    simp [derivativeRatio, hx0]
  · intro _
    exact logExponent_limit_aux k

theorem gap2 (k : ℝ) :
    HasRightLimitAtZero (derivativeRatio k) k := by
  unfold HasRightLimitAtZero
  apply tendsto_const_nhds.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hxpos : 0 < x := hx
  have hx0 : x ≠ 0 := ne_of_gt hxpos
  simp [derivativeRatio, hx0]

theorem gap3 (k : ℝ) :
    HasRightLimitAtZero (logExponent k) k := by
  exact logExponent_limit_aux k

theorem gap4 (k : ℝ) :
    HasRightLimitAtZero (powerForm k) (Real.exp k) := by
  unfold HasRightLimitAtZero
  have hlog := logExponent_limit_aux k
  unfold HasRightLimitAtZero at hlog
  have hexp :
      Filter.Tendsto (fun x => Real.exp (logExponent k x))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (Real.exp k)) :=
    (Real.continuous_exp.tendsto k).comp hlog
  apply hexp.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hxpos : 0 < x := hx
  unfold powerForm logExponent
  calc
    Real.exp (k / (1 + Real.log x) * Real.log x) =
        Real.exp (Real.log x * (k / (1 + Real.log x))) := by
      congr 1
      ring
    _ = Real.rpow x (k / (1 + Real.log x)) := by
      symm
      exact Real.rpow_def_of_pos hxpos (k / (1 + Real.log x))

end

end ProofGap.Exercise1345
