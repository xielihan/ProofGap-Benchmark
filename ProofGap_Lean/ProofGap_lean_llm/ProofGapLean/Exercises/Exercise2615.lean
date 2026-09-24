import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.PSeries

namespace ProofGap.Exercise2615

noncomputable section

open Filter

def exponentRatio (a : ℕ → ℝ) (n : ℕ) : ℝ :=
  Real.log (1 / a n) / Real.log n

def powerBound (α : ℝ) (n : ℕ) : ℝ :=
  1 / Real.rpow n (1 + α)

def converges (a : ℕ → ℝ) : Prop :=
  Summable (fun n : ℕ => a (n + 1))

theorem gap1 (a : ℕ → ℝ) (hpos : ∀ n ≥ 1, 0 < a n)
    (n : ℕ) (hn : 2 ≤ n) (α : ℝ)
    (h : 1 + α ≤ exponentRatio a n) :
    a n ≤ powerBound α n := by
  have hnreal : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hnlog : 0 < Real.log n := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  have ha : 0 < a n := hpos n (by omega)
  have hainv : 0 < 1 / a n := one_div_pos.mpr ha
  have hlog : (1 + α) * Real.log n ≤ Real.log (1 / a n) := by
    exact (le_div_iff₀ hnlog).mp h
  have hrpow : Real.rpow n (1 + α) ≤ 1 / a n :=
    (Real.rpow_le_iff_le_log hnreal hainv).2 hlog
  unfold powerBound
  have hp : 0 < Real.rpow n (1 + α) :=
    Real.rpow_pos_of_pos hnreal _
  apply (le_div_iff₀ hp).2
  calc
    a n * Real.rpow n (1 + α) ≤ a n * (1 / a n) :=
      mul_le_mul_of_nonneg_left hrpow ha.le
    _ = 1 := by field_simp [ha.ne']

theorem gap2 (α : ℝ) (hα : 0 < α) :
    Summable (fun n : ℕ => powerBound α (n + 1)) := by
  have hall : Summable (fun n : ℕ => Real.rpow n (-(1 + α))) :=
    Real.summable_nat_rpow.mpr (by linarith)
  have hshift := (summable_nat_add_iff 1).mpr hall
  apply hshift.congr
  intro n
  unfold powerBound
  have hneg : Real.rpow (((n + 1 : ℕ) : ℝ)) (-(1 + α)) =
      (Real.rpow (((n + 1 : ℕ) : ℝ)) (1 + α))⁻¹ := by
    change (((n + 1 : ℕ) : ℝ)) ^ (-(1 + α)) =
      ((((n + 1 : ℕ) : ℝ)) ^ (1 + α))⁻¹
    exact Real.rpow_neg (by positivity) _
  rw [hneg]
  simp only [one_div]

theorem gap3 (a : ℕ → ℝ) (hpos : ∀ n ≥ 1, 0 < a n)
    (α : ℝ) (hα : 0 < α)
    (h : ∃ N ≥ 2, ∀ n ≥ N, 1 + α ≤ exponentRatio a n) :
    converges a := by
  rcases h with ⟨N, hN2, hN⟩
  have hO : Asymptotics.IsBigO atTop
      (fun n : ℕ => a (n + 1))
      (fun n : ℕ => powerBound α (n + 1)) := by
    rw [Asymptotics.isBigO_iff]
    refine ⟨1, ?_⟩
    filter_upwards [eventually_ge_atTop N] with n hn
    have ha := hpos (n + 1) (by omega)
    have hp : 0 < powerBound α (n + 1) := by
      unfold powerBound
      exact one_div_pos.mpr (Real.rpow_pos_of_pos (by positivity) _)
    have hle := gap1 a hpos (n + 1) (by omega) α (hN (n + 1) (by omega))
    simpa [Real.norm_eq_abs, abs_of_pos ha, abs_of_pos hp] using hle
  unfold converges
  exact summable_of_isBigO_nat (gap2 α hα) hO

theorem gap4 (a : ℕ → ℝ) (hpos : ∀ n ≥ 1, 0 < a n)
    (n : ℕ) (hn : 2 ≤ n) (h : exponentRatio a n ≤ 1) :
    1 / (n : ℝ) ≤ a n := by
  have hnreal : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hnlog : 0 < Real.log n := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  have ha : 0 < a n := hpos n (by omega)
  have hainv : 0 < 1 / a n := one_div_pos.mpr ha
  have hlog : Real.log (1 / a n) ≤ Real.log n := by
    have := (div_le_iff₀ hnlog).mp h
    simpa using this
  have hinvle : 1 / a n ≤ (n : ℝ) :=
    (Real.log_le_log_iff hainv hnreal).mp hlog
  have hrecip := one_div_le_one_div_of_le hainv hinvle
  simpa [one_div, ha.ne'] using hrecip

theorem gap5 :
    ¬ Summable (fun n : ℕ => 1 / ((n + 1 : ℕ) : ℝ)) := by
  intro h
  have hall : Summable (fun n : ℕ => 1 / (n : ℝ)) :=
    (summable_nat_add_iff 1).mp h
  exact Real.not_summable_one_div_natCast hall

theorem gap6 (a : ℕ → ℝ) (hpos : ∀ n ≥ 1, 0 < a n)
    (h : ∃ N ≥ 2, ∀ n ≥ N, exponentRatio a n ≤ 1) :
    ¬ converges a := by
  rcases h with ⟨N, hN2, hN⟩
  intro hsum
  have hO : Asymptotics.IsBigO atTop
      (fun n : ℕ => 1 / (((n + 1 : ℕ) : ℝ)))
      (fun n : ℕ => a (n + 1)) := by
    rw [Asymptotics.isBigO_iff]
    refine ⟨1, ?_⟩
    filter_upwards [eventually_ge_atTop N] with n hn
    have ha := hpos (n + 1) (by omega)
    have hle := gap4 a hpos (n + 1) (by omega) (hN (n + 1) (by omega))
    have hharm : 0 < 1 / (((n + 1 : ℕ) : ℝ)) := by positivity
    simpa only [Real.norm_eq_abs, abs_of_pos hharm, abs_of_pos ha, one_mul] using hle
  apply gap5
  unfold converges at hsum
  exact summable_of_isBigO_nat hsum hO

theorem gap7 (a : ℕ → ℝ) (hpos : ∀ n ≥ 1, 0 < a n) :
    ((∃ N ≥ 2, ∃ α > 0, ∀ n ≥ N, 1 + α ≤ exponentRatio a n) →
        converges a) ∧
      ((∃ N ≥ 2, ∀ n ≥ N, exponentRatio a n ≤ 1) →
        ¬ converges a) := by
  constructor
  · rintro ⟨N, hN, α, hα, hbound⟩
    exact gap3 a hpos α hα ⟨N, hN, hbound⟩
  · exact gap6 a hpos

end

end ProofGap.Exercise2615
