import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Topology.Algebra.InfiniteSum.Basic

namespace ProofGap.Exercise2857

noncomputable section

def logOnePlusTerm (x : ℝ) (n : ℕ) : ℝ :=
  let m := n + 1
  (-1 : ℝ) ^ (m - 1) * x ^ m / m

def oddLogTerm (x : ℝ) (n : ℕ) : ℝ :=
  x ^ (2 * n + 1) / (2 * n + 1)

private theorem hasSum_logOnePlusTerm {x : ℝ} (hx : |x| < 1) :
    HasSum (logOnePlusTerm x) (Real.log (1 + x)) := by
  have h :=
    (Real.hasSum_pow_div_log_of_abs_lt_one
      (x := -x) (by simpa using hx)).mul_left (-1 : ℝ)
  have h' : HasSum (logOnePlusTerm x) (-1 * (-Real.log (1 - -x))) := by
    refine h.congr_fun ?_
    intro n
    have hneg : (-x) ^ (n + 1) = (-1 : ℝ) ^ (n + 1) * x ^ (n + 1) := by
      rw [neg_pow]
    dsimp [logOnePlusTerm]
    rw [hneg]
    push_cast
    rw [pow_succ]
    ring
  simpa only [neg_neg, neg_mul, one_mul, sub_neg_eq_add] using h'

theorem gap1 :
    ∀ x : ℝ, x ∈ Set.Ioo (-1 : ℝ) 1 →
      Real.log (Real.sqrt ((1 + x) / (1 - x))) =
        (1 / 2 : ℝ) * (Real.log (1 + x) - Real.log (1 - x)) := by
  intro x hx
  have hp : 0 < 1 + x := by linarith [hx.1]
  have hm : 0 < 1 - x := by linarith [hx.2]
  rw [Real.log_sqrt (div_nonneg hp.le hm.le), Real.log_div hp.ne' hm.ne']
  ring

theorem gap2
    (hlog :
      ∀ x : ℝ, x ∈ Set.Ioo (-1 : ℝ) 1 →
        Real.log (Real.sqrt ((1 + x) / (1 - x))) =
          (1 / 2 : ℝ) * (Real.log (1 + x) - Real.log (1 - x))) :
    ∀ x : ℝ, |x| < 1 →
      (1 / 2 : ℝ) * (Real.log (1 + x) - Real.log (1 - x)) =
        (1 / 2 : ℝ) *
          ((∑' n, logOnePlusTerm x n) - (∑' n, logOnePlusTerm (-x) n)) := by
  intro x hx
  rw [(hasSum_logOnePlusTerm hx).tsum_eq,
    (hasSum_logOnePlusTerm (by simpa using hx : |-x| < 1)).tsum_eq]
  rw [show 1 + -x = 1 - x by ring]

theorem gap3
    (hlog :
      ∀ x : ℝ, x ∈ Set.Ioo (-1 : ℝ) 1 →
        Real.log (Real.sqrt ((1 + x) / (1 - x))) =
          (1 / 2 : ℝ) * (Real.log (1 + x) - Real.log (1 - x)))
    (hseries :
      ∀ x : ℝ, |x| < 1 →
        (1 / 2 : ℝ) * (Real.log (1 + x) - Real.log (1 - x)) =
          (1 / 2 : ℝ) *
            ((∑' n, logOnePlusTerm x n) - (∑' n, logOnePlusTerm (-x) n))) :
    ∀ x : ℝ, |x| < 1 →
      Real.log (Real.sqrt ((1 + x) / (1 - x))) =
        (1 / 2 : ℝ) *
          ((∑' n, logOnePlusTerm x n) - (∑' n, logOnePlusTerm (-x) n)) := by
  intro x hx
  rw [hlog x (by
    rcases abs_lt.mp hx with ⟨hlo, hhi⟩
    exact ⟨hlo, hhi⟩)]
  exact hseries x hx

theorem gap4
    (hcombined :
      ∀ x : ℝ, |x| < 1 →
        Real.log (Real.sqrt ((1 + x) / (1 - x))) =
          (1 / 2 : ℝ) *
            ((∑' n, logOnePlusTerm x n) - (∑' n, logOnePlusTerm (-x) n))) :
    ∀ x : ℝ, |x| < 1 →
      Real.log (Real.sqrt ((1 + x) / (1 - x))) =
        ∑' n, oddLogTerm x n := by
  intro x hx
  have hmem : x ∈ Set.Ioo (-1 : ℝ) 1 := by
    rcases abs_lt.mp hx with ⟨hlo, hhi⟩
    exact ⟨hlo, hhi⟩
  rw [gap1 x hmem]
  have hs := (Real.hasSum_log_sub_log_of_abs_lt_one hx).mul_left (1 / 2 : ℝ)
  have ho : HasSum (oddLogTerm x)
      ((1 / 2 : ℝ) * (Real.log (1 + x) - Real.log (1 - x))) := by
    convert hs using 1 with n
    unfold oddLogTerm
    push_cast
    ring
  exact ho.tsum_eq.symm

end

end ProofGap.Exercise2857
