import ProofGapLean.Prelude.Sequences
import ProofGapLean.Prelude.Finite
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Topology.Instances.Real.Lemmas

open Filter Topology

namespace ProofGap.Exercise77

noncomputable section

def x (p : ℕ → ℕ) (n : ℕ) : ℝ :=
  (p 0 : ℝ) + ∑ i ∈ Finset.Icc 1 n, (p i : ℝ) / (10 : ℝ) ^ i

def decimalUpper (p : ℕ → ℕ) (n : ℕ) : ℝ :=
  (p 0 : ℝ) + 9 * ∑ i ∈ Finset.Icc 1 n, 1 / (10 : ℝ) ^ i

def Convergent (u : ℕ → ℝ) : Prop :=
  ∃ l : ℝ, Tendsto u atTop (𝓝 l)

/-- Source: `proof_gap/exercise_77/1.txt`. -/
theorem gap1 (p : ℕ → ℕ) :
    ∀ n : ℕ, x p (n + 1) = x p n + (p (n + 1) : ℝ) / 10 ^ (n + 1) := by
  intro n
  unfold x
  rw [Finset.sum_Icc_succ_top (by omega)]
  ring

/-- Source: `proof_gap/exercise_77/2.txt`; the missing positive-digit premise is explicit. -/
theorem gap2 (p : ℕ → ℕ) :
    ∀ n : ℕ, 0 < p (n + 1) → x p (n + 1) > x p n := by
  intro n hn
  rw [gap1]
  have hp : 0 < (p (n + 1) : ℝ) := by exact_mod_cast hn
  have hpow : 0 < (10 : ℝ) ^ (n + 1) := by positivity
  linarith [div_pos hp hpow]

/-- Source: `proof_gap/exercise_77/3.txt`; strict monotonicity needs every digit positive. -/
theorem gap3
    (p : ℕ → ℕ)
    (hpos : ∀ i : ℕ, 0 < i → 0 < p i) :
    StrictMono (x p) := by
  apply strictMono_nat_of_lt_succ
  intro n
  exact gap2 p n (hpos (n + 1) (by omega))

/-- Source: `proof_gap/exercise_77/4.txt`; n>1 makes the lower bound strict. -/
theorem gap4
    (p : ℕ → ℕ)
    (hpos : ∀ i : ℕ, 0 < i → 0 < p i) :
    ∀ n : ℕ, 1 < n → (p 0 : ℝ) + 1 / 10 < x p n := by
  intro n hn
  have hmono : StrictMono (x p) := gap3 p hpos
  have hp1 : (1 : ℝ) ≤ p 1 := by
    exact_mod_cast hpos 1 (by omega)
  have hx1 : (p 0 : ℝ) + 1 / 10 ≤ x p 1 := by
    norm_num [x]
    linarith
  exact lt_of_le_of_lt hx1 (hmono hn)

/-- Source: `proof_gap/exercise_77/5.txt`; the geometric sum is explicit. -/
theorem gap5
    (p : ℕ → ℕ)
    (hdigit : ∀ i : ℕ, 0 < i → p i ≤ 9) :
    ∀ n : ℕ, x p n ≤ decimalUpper p n := by
  intro n
  unfold x decimalUpper
  apply add_le_add (le_refl _)
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  have hi1 : 0 < i := (Finset.mem_Icc.mp hi).1
  have hp : (p i : ℝ) ≤ 9 := by exact_mod_cast hdigit i hi1
  have hpow : 0 < (10 : ℝ) ^ i := by positivity
  rw [div_le_iff₀ hpow]
  rw [one_div]
  field_simp
  nlinarith

/-- Source: `proof_gap/exercise_77/6.txt`; the geometric sum is explicit. -/
theorem gap6 (p : ℕ → ℕ) :
    ∀ n : ℕ, decimalUpper p n < 1 + (p 0 : ℝ) := by
  intro n
  have hsum :
      (∑ i ∈ Finset.Icc 1 n, 1 / (10 : ℝ) ^ i) =
        (((1 / 10 : ℝ) ^ 1 - (1 / 10 : ℝ) ^ (n + 1)) /
          (1 - (1 / 10 : ℝ))) := by
    rw [← Finset.Ico_add_one_right_eq_Icc]
    simpa only [one_div, inv_pow] using
      (geom_sum_Ico' (x := (1 / 10 : ℝ)) (m := 1) (n := n + 1)
        (by norm_num) (by omega))
  have hpow : 0 < (1 / 10 : ℝ) ^ (n + 1) := by positivity
  unfold decimalUpper
  rw [hsum]
  norm_num
  nlinarith

/-- Source: `proof_gap/exercise_77/7.txt`. -/
theorem gap7 (p : ℕ → ℕ) :
    (p 0 : ℝ) + 1 / 10 < 1 + (p 0 : ℝ) := by
  have : (1 / 10 : ℝ) < 1 := by norm_num
  linarith

/-- Source: `proof_gap/exercise_77/8.txt`. -/
theorem gap8
    (p : ℕ → ℕ)
    (hupper : ∀ n : ℕ, x p n < 1 + (p 0 : ℝ)) :
    Bornology.IsBounded (Set.range (x p)) := by
  apply isBounded_iff_bddBelow_bddAbove.mpr
  constructor
  · refine ⟨(p 0 : ℝ), ?_⟩
    intro y hy
    rcases hy with ⟨n, rfl⟩
    unfold x
    exact le_add_of_nonneg_right
      (Finset.sum_nonneg fun i hi => div_nonneg (by positivity) (by positivity))
  · refine ⟨1 + (p 0 : ℝ), ?_⟩
    intro y hy
    rcases hy with ⟨n, rfl⟩
    exact le_of_lt (hupper n)

/-- Source: `proof_gap/exercise_77/9.txt`. -/
theorem gap9
    (p : ℕ → ℕ)
    (hmono : Monotone (x p))
    (hbound : BddAbove (Set.range (x p))) :
    Convergent (x p) := by
  have himage : x p '' Set.Ici 0 = Set.range (x p) := by
    ext y
    constructor
    · rintro ⟨n, _, rfl⟩
      exact ⟨n, rfl⟩
    · rintro ⟨n, rfl⟩
      exact ⟨n, Nat.zero_le n, rfl⟩
  refine ⟨sSup (Set.range (x p)), ?_⟩
  have ht := Real.tendsto_atTop_csSup_of_monotoneOn_bddAbove_nat_Ici
    (f := x p) (k := 0) (hmono.monotoneOn (Set.Ici 0))
    (by rwa [himage])
  rwa [himage] at ht

/-- Source: `proof_gap/exercise_77/10.txt`. -/
theorem gap10
    (p : ℕ → ℕ)
    (hconv : Convergent (x p)) :
    Convergent (x p) := by
  exact hconv

end

end ProofGap.Exercise77
