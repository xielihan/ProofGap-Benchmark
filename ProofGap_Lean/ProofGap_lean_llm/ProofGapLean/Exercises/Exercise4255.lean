import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.NormNum

namespace ProofGap.Exercise4255

noncomputable section

open scoped Interval

def edgeAB : Set (ℝ × ℝ) :=
  {p | p.2 = 1 - p.1 ∧ 0 ≤ p.1 ∧ p.1 ≤ 1}

def edgeBC : Set (ℝ × ℝ) :=
  {p | p.2 = 1 + p.1 ∧ -1 ≤ p.1 ∧ p.1 ≤ 0}

def edgeCD : Set (ℝ × ℝ) :=
  {p | p.2 = -1 - p.1 ∧ -1 ≤ p.1 ∧ p.1 ≤ 0}

def edgeDA : Set (ℝ × ℝ) :=
  {p | p.2 = -1 + p.1 ∧ 0 ≤ p.1 ∧ p.1 ≤ 1}

def diamond : Set (ℝ × ℝ) :=
  edgeAB ∪ edgeBC ∪ edgeCD ∪ edgeDA

def lineIntegral : ℝ :=
  (∫ x in (1 : ℝ)..0, (1 - 1 : ℝ)) +
    (∫ x in (0 : ℝ)..-1, (2 : ℝ)) +
      (∫ x in (-1 : ℝ)..0, (1 - 1 : ℝ)) +
        ∫ x in (0 : ℝ)..1, (2 : ℝ)

theorem gap1 :
    edgeAB = {p | p.2 = 1 - p.1 ∧ 0 ≤ p.1 ∧ p.1 ≤ 1} := by
  rfl

theorem gap2 :
    edgeBC = {p | p.2 = 1 + p.1 ∧ -1 ≤ p.1 ∧ p.1 ≤ 0} := by
  rfl

theorem gap3 :
    edgeCD = {p | p.2 = -1 - p.1 ∧ -1 ≤ p.1 ∧ p.1 ≤ 0} := by
  rfl

theorem gap4 :
    edgeDA = {p | p.2 = -1 + p.1 ∧ 0 ≤ p.1 ∧ p.1 ≤ 1} := by
  rfl

theorem gap5 :
    lineIntegral =
      (∫ x in (1 : ℝ)..0, (1 - 1 : ℝ)) +
        (∫ x in (0 : ℝ)..-1, (2 : ℝ)) +
          (∫ x in (-1 : ℝ)..0, (1 - 1 : ℝ)) +
            ∫ x in (0 : ℝ)..1, (2 : ℝ) := by
  rfl

theorem gap6 :
    lineIntegral =
      (∫ x in (1 : ℝ)..0, (1 - 1 : ℝ)) +
        (∫ x in (0 : ℝ)..-1, (2 : ℝ)) +
          (∫ x in (-1 : ℝ)..0, (1 - 1 : ℝ)) +
            ∫ x in (0 : ℝ)..1, (2 : ℝ) := by
  rfl

theorem gap7 :
    (∫ x in (1 : ℝ)..0, (1 - 1 : ℝ)) +
          (∫ x in (0 : ℝ)..-1, (2 : ℝ)) +
            (∫ x in (-1 : ℝ)..0, (1 - 1 : ℝ)) +
              (∫ x in (0 : ℝ)..1, (2 : ℝ)) =
      0 := by
  norm_num [intervalIntegral.integral_const]

theorem gap8 :
    lineIntegral = 0 := by
  rw [gap5, gap7]

end

end ProofGap.Exercise4255
