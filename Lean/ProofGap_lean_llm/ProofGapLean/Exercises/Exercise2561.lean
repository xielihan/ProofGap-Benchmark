import ProofGapLean.Prelude.Sequences
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

namespace ProofGap.Exercise2561

noncomputable section

def term (n : ℕ) : ℝ := (n : ℝ) / (2 * (n : ℝ) - 1)
def a : ℕ → ℝ := term

theorem gap1 :
    ∀ L : ℝ, Tendsto a atTop (nhds L) ↔ Tendsto term atTop (nhds L) := by
  intro L
  rfl

theorem gap2
    (hlimits : ∀ L : ℝ, Tendsto a atTop (nhds L) ↔
      Tendsto term atTop (nhds L)) :
    Tendsto term atTop (nhds (1 / 2 : ℝ)) := by
  apply Metric.tendsto_atTop.2
  intro ε hε
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / (4 * ε) + 1)
  refine ⟨N, ?_⟩
  intro n hn
  have hnreal : (N : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast hn
  have hbig : 1 / (4 * ε) + 1 < (n : ℝ) := lt_of_lt_of_le hN hnreal
  have he4 : 0 < 4 * ε := by
    nlinarith
  have hinvpos : 0 < 1 / (4 * ε) := one_div_pos.mpr he4
  have hnlarge : 1 < (n : ℝ) := by
    nlinarith
  have hden : 0 < 2 * (n : ℝ) - 1 := by
    nlinarith
  have hden0 : 2 * (n : ℝ) - 1 ≠ 0 := ne_of_gt hden
  have hd : 0 < 2 * (2 * (n : ℝ) - 1) := mul_pos (by norm_num) hden
  have hprod :
      0 < ((n : ℝ) - (1 / (4 * ε) + 1)) * (4 * ε) :=
    mul_pos (sub_pos.mpr hbig) he4
  have hinv : (1 / (4 * ε)) * (4 * ε) = 1 := by
    field_simp [ne_of_gt hε]
  have hone : 1 < ε * (4 * (n : ℝ) - 2) := by
    nlinarith [hprod, hinv]
  have hcancel :
      (n : ℝ) / (2 * (n : ℝ) - 1) * (2 * (n : ℝ) - 1) =
        (n : ℝ) := by
    exact ((div_eq_iff hden0).mp
      (rfl : (n : ℝ) / (2 * (n : ℝ) - 1) =
        (n : ℝ) / (2 * (n : ℝ) - 1))).symm
  change dist ((n : ℝ) / (2 * (n : ℝ) - 1)) (1 / 2 : ℝ) < ε
  rw [Real.dist_eq]
  have hdiff :
      (n : ℝ) / (2 * (n : ℝ) - 1) - (1 / 2 : ℝ) =
        1 / (2 * (2 * (n : ℝ) - 1)) := by
    apply (eq_div_iff (ne_of_gt hd)).2
    calc
      ((n : ℝ) / (2 * (n : ℝ) - 1) - (1 / 2 : ℝ)) *
          (2 * (2 * (n : ℝ) - 1)) =
          2 * ((n : ℝ) / (2 * (n : ℝ) - 1) *
            (2 * (n : ℝ) - 1)) - (2 * (n : ℝ) - 1) := by
            ring
      _ = 2 * (n : ℝ) - (2 * (n : ℝ) - 1) := by
        rw [hcancel]
      _ = 1 := by
        ring
  rw [hdiff, abs_of_pos (one_div_pos.mpr hd)]
  apply (div_lt_iff₀ hd).2
  nlinarith [hone]

theorem gap3
    (hlimits : ∀ L : ℝ, Tendsto a atTop (nhds L) ↔
      Tendsto term atTop (nhds L))
    (hterm : Tendsto term atTop (nhds (1 / 2 : ℝ))) :
    (1 / 2 : ℝ) ≠ 0 := by
  norm_num

theorem gap4
    (hlimits : ∀ L : ℝ, Tendsto a atTop (nhds L) ↔
      Tendsto term atTop (nhds L))
    (hterm : Tendsto term atTop (nhds (1 / 2 : ℝ)))
    (hne : (1 / 2 : ℝ) ≠ 0) :
    ¬ Tendsto a atTop (nhds 0) := by
  intro ha0
  apply hne
  exact tendsto_nhds_unique hterm ((hlimits 0).mp ha0)

theorem gap5
    (hlimits : ∀ L : ℝ, Tendsto a atTop (nhds L) ↔
      Tendsto term atTop (nhds L))
    (hterm : Tendsto term atTop (nhds (1 / 2 : ℝ)))
    (hne : (1 / 2 : ℝ) ≠ 0)
    (hnotzero : ¬ Tendsto a atTop (nhds 0)) :
    ¬ Summable term := by
  intro hs
  apply hnotzero
  simpa [a] using hs.tendsto_atTop_zero

end

end ProofGap.Exercise2561
