import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

namespace ProofGap.Exercise1392

noncomputable section

open Filter

def logTaylor (x : ℝ) (n : ℕ) (h : ℝ) : ℝ :=
  Real.log x +
    ∑ k ∈ Finset.range n,
      (-1 : ℝ) ^ k * h ^ (k + 1) / ((k + 1 : ℕ) * x ^ (k + 1))

def AgreesToOrderAt (g p : ℝ → ℝ) (a : ℝ) (n : ℕ) : Prop :=
  Asymptotics.IsLittleO (nhds a) (fun h => g h - p h)
    (fun h => (h - a) ^ n)

theorem gap1 (x h : ℝ) (hx : 0 < x) :
    Real.log (x + h) = Real.log (x * (1 + h / x)) := by
  congr 1
  field_simp

theorem gap2 (x h : ℝ) (hx : 0 < x) (hh : 0 < 1 + h / x) :
    Real.log (x * (1 + h / x)) =
      Real.log x + Real.log (1 + h / x) := by
  exact Real.log_mul hx.ne' hh.ne'

theorem gap3 (x h : ℝ) (hx : 0 < x) (hh : 0 < 1 + h / x) :
    Real.log (x + h) = Real.log x + Real.log (1 + h / x) := by
  rw [gap1 x h hx]
  exact gap2 x h hx hh

private theorem term_identity (x h : ℝ) (hx : x ≠ 0) (k : ℕ) :
    (-h / x) ^ (k + 1) / (k + 1 : ℝ) =
      -((-1 : ℝ) ^ k * h ^ (k + 1) /
        ((k + 1 : ℝ) * x ^ (k + 1))) := by
  rw [div_pow]
  field_simp
  rw [neg_pow, pow_succ]
  ring

theorem gap4 (x : ℝ) (n : ℕ) (hx : 0 < x) (hn : 1 ≤ n) :
    AgreesToOrderAt (fun h => Real.log (x + h)) (logTaylor x n) 0 n := by
  let err : ℝ → ℝ := fun h =>
    Real.log (x + h) - logTaylor x n h
  have hO :
      Asymptotics.IsBigO (nhds 0) err (fun h : ℝ => h ^ (n + 1)) := by
    refine Asymptotics.IsBigO.of_bound
      (2 / x ^ (n + 1)) ?_
    filter_upwards [
      Metric.ball_mem_nhds (0 : ℝ) (by positivity : 0 < x / 2)]
      with h hh
    have habsh : |h| < x / 2 := by
      simpa [Real.dist_eq] using hh
    have hratio : |h / x| < 1 / 2 := by
      rw [abs_div, abs_of_pos hx]
      exact (div_lt_iff₀ hx).2 (by linarith)
    have hlt : |-h / x| < 1 := by
      calc
        |-h / x| = |h / x| := by rw [neg_div, abs_neg]
        _ < 1 / 2 := hratio
        _ < 1 := by norm_num
    have hb := Real.abs_log_sub_add_sum_range_le hlt n
    have herr :
        |Real.log (1 + h / x) -
            ∑ k ∈ Finset.range n,
              (-1 : ℝ) ^ k * h ^ (k + 1) /
                ((k + 1 : ℝ) * x ^ (k + 1))| ≤
          |-h / x| ^ (n + 1) / (1 - |-h / x|) := by
      convert hb using 1
      rw [show (1 : ℝ) - (-h / x) = 1 + h / x by ring]
      rw [add_comm, sub_eq_add_neg]
      congr 1
      rw [Finset.sum_congr rfl fun k hk =>
        term_identity x h hx.ne' k, Finset.sum_neg_distrib]
      ring
    have hlog :
        Real.log (x + h) = Real.log x + Real.log (1 + h / x) := by
      apply gap3 x h hx
      linarith [(abs_lt.mp hratio).1]
    have herr_eq :
        err h = Real.log (1 + h / x) -
          ∑ k ∈ Finset.range n,
            (-1 : ℝ) ^ k * h ^ (k + 1) /
              ((k + 1 : ℝ) * x ^ (k + 1)) := by
      dsimp [err, logTaylor]
      rw [hlog]
      simp only [Nat.cast_add, Nat.cast_one, Nat.add_comm]
      abel
    rw [Real.norm_eq_abs, herr_eq]
    calc
      |Real.log (1 + h / x) -
          ∑ k ∈ Finset.range n,
            (-1 : ℝ) ^ k * h ^ (k + 1) /
              ((k + 1 : ℝ) * x ^ (k + 1))|
          ≤ |-h / x| ^ (n + 1) / (1 - |-h / x|) := herr
      _ ≤ (2 / x ^ (n + 1)) * |h| ^ (n + 1) := by
        rw [abs_div, abs_neg, abs_of_pos hx, div_pow]
        have hden : 1 / 2 < 1 - |h| / x := by
          rw [abs_div, abs_of_pos hx] at hratio
          linarith
        have hxp : 0 < x ^ (n + 1) := pow_pos hx _
        have hpow : 0 ≤ |h| ^ (n + 1) := by positivity
        calc
          (|h| ^ (n + 1) / x ^ (n + 1)) / (1 - |h| / x)
              ≤ (|h| ^ (n + 1) / x ^ (n + 1)) / (1 / 2) := by
                gcongr
          _ = (2 / x ^ (n + 1)) * |h| ^ (n + 1) := by ring
      _ = (2 / x ^ (n + 1)) * ‖h ^ (n + 1)‖ := by
        rw [norm_pow, Real.norm_eq_abs]
  have hp :
      Asymptotics.IsLittleO (nhds 0)
        (fun h : ℝ => h ^ (n + 1)) (fun h : ℝ => h ^ n) := by
    simpa using Asymptotics.isLittleO_pow_pow
      (𝕜 := ℝ) (m := n) (n := n + 1) (by omega)
  simpa [AgreesToOrderAt, err] using hO.trans_isLittleO hp

end

end ProofGap.Exercise1392
