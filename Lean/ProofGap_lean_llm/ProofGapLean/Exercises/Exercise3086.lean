import ProofGapLean.Prelude.Analysis
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega
import Mathlib.Topology.Defs.Filter

namespace ProofGap.Exercise3086

noncomputable section

open Filter
open scoped BigOperators Topology

def p (x : ℕ → ℝ) (n : ℕ) : ℝ :=
  Real.cos (x n)

def alpha (x : ℕ → ℝ) (n : ℕ) : ℝ :=
  p x n - 1

def SummableFromOne (f : ℕ → ℝ) : Prop :=
  Summable (fun k : ℕ => f (k + 1))

def partialProduct (x : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∏ i ∈ Finset.Icc 1 n, p x i

def ConvergentProduct (x : ℕ → ℝ) : Prop :=
  ∃ P : ℝ, Tendsto (partialProduct x) atTop (𝓝 P)

/-- Source: `proof_gap/exercise_3086/1.txt`; bind the whole sequence `x`. -/
theorem gap1 (x : ℕ → ℝ) (hx : Tendsto x atTop (𝓝 0)) :
    ∀ n, p x n = 1 + alpha x n := by
  intro n
  simp [alpha]

/-- Source: `proof_gap/exercise_3086/2.txt`; cosine is at most one. -/
theorem gap2 (x : ℕ → ℝ) (hx : Tendsto x atTop (𝓝 0)) :
    ∀ n, alpha x n ≤ 0 := by
  intro n
  unfold alpha p
  exact sub_nonpos.mpr (Real.cos_le_one _)

/--
Source: `proof_gap/exercise_3086/3.txt`; convergence to zero alone is
insufficient, so retain the necessary square-summability premise.
-/
theorem gap3 (x : ℕ → ℝ) (hx : Tendsto x atTop (𝓝 0))
    (hxsq : SummableFromOne (fun n => (x n) ^ 2)) :
    SummableFromOne (alpha x) := by
  unfold SummableFromOne at hxsq ⊢
  refine Summable.of_norm_bounded hxsq ?_
  intro n
  simp only [alpha, p]
  rw [Real.norm_eq_abs, abs_of_nonpos (sub_nonpos.mpr (Real.cos_le_one _))]
  let t := x (n + 1)
  let z := t / 2
  have harg : 2 * z = t := by
    dsimp [z]
    ring
  have htrig := Real.cos_two_mul' z
  rw [harg] at htrig
  have hsin : |Real.sin z| ≤ |z| := Real.abs_sin_le_abs
  have hsquare : (Real.sin z) ^ 2 ≤ z ^ 2 := by
    have habssquare : |Real.sin z| ^ 2 ≤ |z| ^ 2 := by
      nlinarith [abs_nonneg (Real.sin z), abs_nonneg z]
    simpa only [sq_abs] using habssquare
  have hpyth := Real.sin_sq_add_cos_sq z
  change -(Real.cos t - 1) ≤ t ^ 2
  dsimp [z] at hsquare
  nlinarith [sq_nonneg t]

/--
Source: `proof_gap/exercise_3086/4.txt`; state convergence of the partial
product sequence and retain summability of its additive deviations.
-/
theorem gap4 (x : ℕ → ℝ) (hx : Tendsto x atTop (𝓝 0))
    (ha : SummableFromOne (alpha x)) :
    ConvergentProduct x := by
  unfold ConvergentProduct
  unfold SummableFromOne at ha
  have hatend : Tendsto (fun k : ℕ => alpha x (k + 1)) atTop (𝓝 0) :=
    ha.tendsto_atTop_zero
  rw [Metric.tendsto_atTop] at hatend
  obtain ⟨N, hN⟩ := hatend 1 zero_lt_one
  have hfactor_pos (k : ℕ) : 0 < p x (N + k + 1) := by
    have hd := hN (N + k) (by omega)
    rw [Real.dist_eq, sub_zero] at hd
    have halower : -1 < alpha x (N + k + 1) := (abs_lt.mp hd).1
    rw [gap1 x hx (N + k + 1)]
    linarith
  have hp_le_one (n : ℕ) : p x n ≤ 1 := by
    have h := gap2 x hx n
    unfold alpha at h
    linarith
  have hrec (n : ℕ) :
      partialProduct x (n + 1) = partialProduct x n * p x (n + 1) := by
    unfold partialProduct
    have hsets :
        Finset.Icc 1 (n + 1) = insert (n + 1) (Finset.Icc 1 n) := by
      ext i
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    have hnot : n + 1 ∉ Finset.Icc 1 n := by
      simp only [Finset.mem_Icc]
      omega
    rw [hsets, Finset.prod_insert hnot]
    ring
  have hstep (k : ℕ) :
      partialProduct x (N + (k + 1)) =
        partialProduct x (N + k) * p x (N + k + 1) := by
    simpa [Nat.add_assoc] using hrec (N + k)
  have hshift (P : ℝ)
      (hP : Tendsto (fun k : ℕ => partialProduct x (N + k)) atTop (𝓝 P)) :
      Tendsto (partialProduct x) atTop (𝓝 P) := by
    rw [Metric.tendsto_atTop] at hP ⊢
    intro ε hε
    obtain ⟨K, hK⟩ := hP ε hε
    refine ⟨N + K, ?_⟩
    intro n hn
    have hNK : N ≤ n := by omega
    have hKn : K ≤ n - N := by omega
    have hd := hK (n - N) hKn
    have heq : N + (n - N) = n := by omega
    simpa only [heq] using hd
  by_cases hb : 0 ≤ partialProduct x N
  · have hnonneg : ∀ k : ℕ, 0 ≤ partialProduct x (N + k) := by
      intro k
      induction k with
      | zero => simpa using hb
      | succ k ih =>
          change 0 ≤ partialProduct x (N + (k + 1))
          rw [hstep k]
          exact mul_nonneg ih (hfactor_pos k).le
    have hanti : Antitone (fun k : ℕ => partialProduct x (N + k)) := by
      apply antitone_nat_of_succ_le
      intro k
      change partialProduct x (N + (k + 1)) ≤ partialProduct x (N + k)
      rw [hstep k]
      calc
        partialProduct x (N + k) * p x (N + k + 1) ≤
            partialProduct x (N + k) * 1 :=
          mul_le_mul_of_nonneg_left (hp_le_one (N + k + 1)) (hnonneg k)
        _ = partialProduct x (N + k) := mul_one _
    have hbdd :
        BddBelow (Set.range (fun k : ℕ => partialProduct x (N + k))) := by
      refine ⟨0, ?_⟩
      rintro y ⟨k, rfl⟩
      exact hnonneg k
    have hne :
        (Set.range (fun k : ℕ => partialProduct x (N + k))).Nonempty :=
      Set.range_nonempty _
    have hu_tend :
        Tendsto (fun k : ℕ => partialProduct x (N + k)) atTop
          (𝓝 (sInf (Set.range (fun k : ℕ => partialProduct x (N + k))))) := by
      apply tendsto_atTop_ciInf <;> assumption
    exact ⟨sInf (Set.range (fun k : ℕ => partialProduct x (N + k))),
      hshift _ hu_tend⟩
  · have hb' : partialProduct x N ≤ 0 := (lt_of_not_ge hb).le
    have hnonpos : ∀ k : ℕ, partialProduct x (N + k) ≤ 0 := by
      intro k
      induction k with
      | zero => simpa using hb'
      | succ k ih =>
          change partialProduct x (N + (k + 1)) ≤ 0
          rw [hstep k]
          exact mul_nonpos_of_nonpos_of_nonneg ih (hfactor_pos k).le
    have hmono : Monotone (fun k : ℕ => partialProduct x (N + k)) := by
      apply monotone_nat_of_le_succ
      intro k
      change partialProduct x (N + k) ≤ partialProduct x (N + (k + 1))
      rw [hstep k]
      calc
        partialProduct x (N + k) = partialProduct x (N + k) * 1 :=
          (mul_one _).symm
        _ ≤ partialProduct x (N + k) * p x (N + k + 1) :=
          mul_le_mul_of_nonpos_left (hp_le_one (N + k + 1)) (hnonpos k)
    have hbdd :
        BddAbove (Set.range (fun k : ℕ => partialProduct x (N + k))) := by
      refine ⟨0, ?_⟩
      rintro y ⟨k, rfl⟩
      exact hnonpos k
    have hne :
        (Set.range (fun k : ℕ => partialProduct x (N + k))).Nonempty :=
      Set.range_nonempty _
    have hu_tend :
        Tendsto (fun k : ℕ => partialProduct x (N + k)) atTop
          (𝓝 (sSup (Set.range (fun k : ℕ => partialProduct x (N + k))))) := by
      apply tendsto_atTop_ciSup <;> assumption
    exact ⟨sSup (Set.range (fun k : ℕ => partialProduct x (N + k))),
      hshift _ hu_tend⟩

/-- Source: `proof_gap/exercise_3086/5.txt`; square summability is the correct criterion. -/
theorem gap5 (x : ℕ → ℝ)
    (hxsq : SummableFromOne (fun n => (x n) ^ 2)) :
    ConvergentProduct x := by
  have hs := hxsq
  unfold SummableFromOne at hs
  have hsqtend : Tendsto (fun k : ℕ => (x (k + 1)) ^ 2) atTop (𝓝 0) :=
    hs.tendsto_atTop_zero
  have hx : Tendsto x atTop (𝓝 0) := by
    rw [Metric.tendsto_atTop] at hsqtend ⊢
    intro ε hε
    obtain ⟨N, hN⟩ := hsqtend (ε ^ 2) (sq_pos_of_pos hε)
    refine ⟨N + 1, ?_⟩
    intro n hn
    have hn1 : 1 ≤ n := by omega
    have htail := hN (n - 1) (by omega)
    rw [Real.dist_eq, sub_zero,
      abs_of_nonneg (sq_nonneg (x (n - 1 + 1))),
      Nat.sub_add_cancel hn1] at htail
    rw [Real.dist_eq, sub_zero]
    by_cases hxn : 0 ≤ x n
    · rw [abs_of_nonneg hxn]
      nlinarith
    · have hxn' : x n < 0 := lt_of_not_ge hxn
      rw [abs_of_neg hxn']
      nlinarith
  exact gap4 x hx (gap3 x hx hxsq)

end

end ProofGap.Exercise3086
