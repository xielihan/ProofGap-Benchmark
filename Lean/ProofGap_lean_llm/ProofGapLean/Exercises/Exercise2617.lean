import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.PSeries

namespace ProofGap.Exercise2617

noncomputable section

open Filter

def term (n : ℕ) : ℝ :=
  1 / Real.rpow (Real.log (Real.log n)) (Real.log n)

def exponentRatio (n : ℕ) : ℝ :=
  Real.log (1 / term n) / Real.log n

def converges : Prop :=
  Summable (fun n : ℕ => term (n + 3))

theorem gap1 (n : ℕ) (hn : 3 ≤ n) :
    exponentRatio n = Real.log (Real.log (Real.log n)) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hlognpos : 0 < Real.log n :=
    Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  have honeLog : 1 < Real.log n :=
    (Real.lt_log_iff_exp_lt hnpos).2
      (Real.exp_one_lt_three.trans_le (by exact_mod_cast hn))
  have hloglogpos : 0 < Real.log (Real.log n) := Real.log_pos honeLog
  have hrpowpos : 0 < Real.rpow (Real.log (Real.log n)) (Real.log n) :=
    Real.rpow_pos_of_pos hloglogpos _
  have hinv : 1 / term n =
      Real.rpow (Real.log (Real.log n)) (Real.log n) := by
    unfold term
    field_simp [hrpowpos.ne']
  have hlogpow : Real.log
      (Real.rpow (Real.log (Real.log n)) (Real.log n)) =
      Real.log n * Real.log (Real.log (Real.log n)) := by
    change Real.log ((Real.log (Real.log n)) ^ Real.log n) =
      Real.log n * Real.log (Real.log (Real.log n))
    exact Real.log_rpow hloglogpos _
  unfold exponentRatio
  rw [hinv, hlogpow]
  field_simp [hlognpos.ne']

theorem gap2 (α : ℝ) :
    ∃ N : ℕ, ∀ n ≥ N, 1 + α ≤ Real.log (Real.log (Real.log n)) := by
  have hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hloglog : Tendsto (fun n : ℕ => Real.log (Real.log n)) atTop atTop := by
    simpa [Function.comp_def] using Real.tendsto_log_atTop.comp hlog
  have htriple : Tendsto (fun n : ℕ => Real.log (Real.log (Real.log n)))
      atTop atTop := by
    simpa [Function.comp_def] using Real.tendsto_log_atTop.comp hloglog
  rcases (eventually_atTop.1
    (htriple.eventually (eventually_ge_atTop (1 + α)))) with ⟨N, hN⟩
  exact ⟨N, fun n hn => hN n hn⟩

theorem gap3 :
    converges := by
  rcases gap2 1 with ⟨N, hN⟩
  have hO : Asymptotics.IsBigO atTop
      (fun n : ℕ => term (n + 3))
      (fun n : ℕ => 1 / (((n + 3 : ℕ) : ℝ) ^ 2)) := by
    rw [Asymptotics.isBigO_iff]
    refine ⟨1, ?_⟩
    filter_upwards [eventually_ge_atTop N] with n hn
    have hm : 3 ≤ n + 3 := by omega
    have hratio : (2 : ℝ) ≤ exponentRatio (n + 3) := by
      rw [gap1 (n + 3) hm]
      have hh := hN (n + 3) (by omega)
      norm_num at hh ⊢
      exact hh
    have hnpos : (0 : ℝ) < (n + 3 : ℕ) := by positivity
    have hlognpos : 0 < Real.log (n + 3 : ℕ) :=
      Real.log_pos (by exact_mod_cast (show 1 < n + 3 by omega))
    have ht : 0 < term (n + 3) := by
      unfold term
      exact one_div_pos.mpr (Real.rpow_pos_of_pos (by
        have hone : 1 < Real.log (n + 3 : ℕ) :=
          (Real.lt_log_iff_exp_lt hnpos).2
            (Real.exp_one_lt_three.trans_le (by exact_mod_cast hm))
        exact Real.log_pos hone) _)
    have hinv : 0 < 1 / term (n + 3) := one_div_pos.mpr ht
    have hlog : (2 : ℝ) * Real.log (n + 3 : ℕ) ≤
        Real.log (1 / term (n + 3)) :=
      (le_div_iff₀ hlognpos).mp hratio
    have hrpow : Real.rpow (n + 3 : ℕ) 2 ≤ 1 / term (n + 3) :=
      (Real.rpow_le_iff_le_log hnpos hinv).2 hlog
    have hp : 0 < Real.rpow (n + 3 : ℕ) 2 :=
      Real.rpow_pos_of_pos hnpos _
    have hle : term (n + 3) ≤ 1 / Real.rpow (n + 3 : ℕ) 2 := by
      apply (le_div_iff₀ hp).2
      calc
        term (n + 3) * Real.rpow (n + 3 : ℕ) 2 ≤
            term (n + 3) * (1 / term (n + 3)) :=
          mul_le_mul_of_nonneg_left hrpow ht.le
        _ = 1 := by field_simp [ht.ne']
    have hsquare : Real.rpow (n + 3 : ℕ) 2 =
        (((n + 3 : ℕ) : ℝ) ^ 2) := by
      change ((((n + 3 : ℕ) : ℝ)) ^ (2 : ℝ)) =
        (((n + 3 : ℕ) : ℝ) ^ (2 : ℕ))
      simpa using Real.rpow_natCast (((n + 3 : ℕ) : ℝ)) 2
    rw [hsquare] at hle
    have hc : 0 < 1 / (((n + 3 : ℕ) : ℝ) ^ 2) := by positivity
    simpa [Real.norm_eq_abs, abs_of_pos ht, abs_of_pos hc] using hle
  have hall : Summable (fun n : ℕ => 1 / ((n : ℝ) ^ 2)) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  have hshift : Summable (fun n : ℕ => 1 / (((n + 3 : ℕ) : ℝ) ^ 2)) :=
    (summable_nat_add_iff 3).mpr hall
  unfold converges
  exact summable_of_isBigO_nat hshift hO

theorem gap4 :
    Summable (fun n : ℕ => term (n + 3)) := by
  exact gap3

end

end ProofGap.Exercise2617
