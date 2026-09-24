import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Real.Basic
import ProofGapLean.Prelude.Finite
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise3667

noncomputable section

open scoped BigOperators

def objective {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  ∑ i, x i ^ 2

def constraint {n : ℕ} (a : Fin n → ℝ) : Set (Fin n → ℝ) :=
  {x | ∑ i, x i / a i = 1}

def critical {n : ℕ} (a x : Fin n → ℝ) (lambda : ℝ) : Prop :=
  (∀ i, 2 * x i + lambda / a i = 0) ∧ x ∈ constraint a

def reciprocalSquareSum {n : ℕ} (a : Fin n → ℝ) : ℝ :=
  ∑ j, 1 / a j ^ 2

def candidate {n : ℕ} (a : Fin n → ℝ) : Fin n → ℝ :=
  fun i => (1 / a i) * (reciprocalSquareSum a)⁻¹

def secondVariation {n : ℕ} (dx : Fin n → ℝ) : ℝ :=
  2 * ∑ i, dx i ^ 2

def minimizers {n : ℕ} (a : Fin n → ℝ) : Set (Fin n → ℝ) :=
  {x | x ∈ constraint a ∧
    ∀ y ∈ constraint a, objective x ≤ objective y}

private theorem candidate_facts {n : ℕ} (hn : 0 < n)
    (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) :
    0 < reciprocalSquareSum a ∧
    candidate a ∈ constraint a ∧
    objective (candidate a) = (reciprocalSquareSum a)⁻¹ ∧
    ∀ y ∈ constraint a,
      objective y = objective (candidate a) +
        ∑ i, (y i - candidate a i) ^ 2 := by
  let i : Fin n := ⟨0, hn⟩
  have hi : 0 < 1 / a i ^ 2 :=
    one_div_pos.mpr (pow_pos (ha i) 2)
  have hle : 1 / a i ^ 2 ≤ ∑ j, 1 / a j ^ 2 :=
    Finset.single_le_sum
      (fun j _ => le_of_lt (one_div_pos.mpr (pow_pos (ha j) 2)))
      (Finset.mem_univ i)
  have hSpos : 0 < reciprocalSquareSum a := by
    unfold reciprocalSquareSum
    linarith
  have hSne : reciprocalSquareSum a ≠ 0 := ne_of_gt hSpos
  have hc : candidate a ∈ constraint a := by
    change (∑ i, candidate a i / a i) = 1
    calc
      (∑ i, candidate a i / a i) =
          (∑ i, 1 / a i ^ 2) * (reciprocalSquareSum a)⁻¹ := by
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro i hi
            unfold candidate
            ring
      _ = reciprocalSquareSum a * (reciprocalSquareSum a)⁻¹ := by
            rfl
      _ = 1 := by
            field_simp [hSne] <;> ring
  have hobj :
      objective (candidate a) = (reciprocalSquareSum a)⁻¹ := by
    change (∑ i, ((1 / a i) * (reciprocalSquareSum a)⁻¹) ^ 2) =
      (reciprocalSquareSum a)⁻¹
    calc
      (∑ i, ((1 / a i) * (reciprocalSquareSum a)⁻¹) ^ 2) =
          (∑ i, 1 / a i ^ 2) * (reciprocalSquareSum a)⁻¹ ^ 2 := by
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro i hi
            ring
      _ = reciprocalSquareSum a * (reciprocalSquareSum a)⁻¹ ^ 2 := by
            rfl
      _ = (reciprocalSquareSum a)⁻¹ := by
            field_simp [hSne] <;> ring
  refine ⟨hSpos, hc, hobj, ?_⟩
  intro y hy
  have hycon := hy
  change (∑ i, y i / a i) = 1 at hycon
  have hcross :
      (∑ i, y i * candidate a i) =
        (reciprocalSquareSum a)⁻¹ := by
    calc
      (∑ i, y i * candidate a i) =
          (∑ i, y i / a i) * (reciprocalSquareSum a)⁻¹ := by
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro i hi
            unfold candidate
            ring
      _ = (reciprocalSquareSum a)⁻¹ := by rw [hycon, one_mul]
  have hexpand :
      (∑ i, (y i - candidate a i) ^ 2) =
        objective y - 2 * (∑ i, y i * candidate a i) +
          objective (candidate a) := by
    unfold objective
    calc
      (∑ i, (y i - candidate a i) ^ 2) =
          ∑ i, (y i ^ 2 - 2 * (y i * candidate a i) +
            candidate a i ^ 2) := by
              apply Finset.sum_congr rfl
              intro i hi
              ring
      _ = (∑ i, y i ^ 2) -
          2 * (∑ i, y i * candidate a i) +
            ∑ i, candidate a i ^ 2 := by
              simp only [Finset.sum_add_distrib,
                Finset.sum_sub_distrib, Finset.mul_sum]
  rw [hcross, hobj] at hexpand
  nlinarith

theorem gap1 {n : ℕ} (a x : Fin n → ℝ) (lambda : ℝ)
    (ha : ∀ i, 0 < a i) (hcrit : critical a x lambda) :
    ∀ i, x i = candidate a i := by
  intro i
  have hcon := hcrit.2
  change (∑ j, x j / a j) = 1 at hcon
  have hterm (j : Fin n) :
      x j / a j = (-lambda / 2) * (1 / a j ^ 2) := by
    have hj := hcrit.1 j
    have haj : a j ≠ 0 := ne_of_gt (ha j)
    field_simp [haj] at hj ⊢ <;> nlinarith
  have hrel :
      (-lambda / 2) * reciprocalSquareSum a = 1 := by
    calc
      (-lambda / 2) * reciprocalSquareSum a =
          ∑ j, (-lambda / 2) * (1 / a j ^ 2) := by
            unfold reciprocalSquareSum
            rw [Finset.mul_sum]
      _ = ∑ j, x j / a j := by
            apply Finset.sum_congr rfl
            intro j hj
            exact (hterm j).symm
      _ = 1 := hcon
  have hS : reciprocalSquareSum a ≠ 0 := by
    intro hz
    rw [hz] at hrel
    norm_num at hrel
  have hc : -lambda / 2 = (reciprocalSquareSum a)⁻¹ := by
    field_simp [hS] at hrel ⊢ <;> nlinarith
  have hi := hterm i
  rw [hc] at hi
  have hai : a i ≠ 0 := ne_of_gt (ha i)
  unfold candidate
  field_simp [hai] at hi ⊢ <;> nlinarith

theorem gap2 {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ)
    (ha : ∀ i, 0 < a i) :
    {x | ∃ lambda, critical a x lambda} =
      ({candidate a} : Set (Fin n → ℝ)) := by
  apply Set.ext
  intro x
  constructor
  · intro hx
    rcases hx with ⟨lambda, hcrit⟩
    have hfun : x = candidate a :=
      funext (gap1 a x lambda ha hcrit)
    simpa only [Set.mem_singleton_iff] using hfun
  · intro hx
    have hfun : x = candidate a := by
      simpa only [Set.mem_singleton_iff] using hx
    subst x
    refine ⟨-2 * (reciprocalSquareSum a)⁻¹, ?_⟩
    constructor
    · intro i
      unfold candidate
      ring
    · exact (candidate_facts hn a ha).2.1

theorem gap3 {n : ℕ} (dx : Fin n → ℝ) :
    secondVariation dx = 2 * ∑ i, dx i ^ 2 := by
  rfl

theorem gap4 {n : ℕ} (dx : Fin n → ℝ) (hdx : dx ≠ 0) :
    secondVariation dx > 0 := by
  have hi : ∃ i, dx i ≠ 0 := by
    by_contra h
    have hz : dx = 0 := by
      funext i
      by_contra hne
      exact h ⟨i, hne⟩
    exact hdx hz
  rcases hi with ⟨i, hi⟩
  have hsq : 0 < dx i ^ 2 := sq_pos_of_ne_zero hi
  have hle : dx i ^ 2 ≤ ∑ j, dx j ^ 2 :=
    Finset.single_le_sum
      (fun j _ => sq_nonneg (dx j))
      (Finset.mem_univ i)
  unfold secondVariation
  nlinarith

theorem gap5 {n : ℕ} (hn : 0 < n) :
    ∃ dx : Fin n → ℝ, secondVariation dx > 0 := by
  refine ⟨fun _ => 1, gap4 _ ?_⟩
  intro h
  have hi := congr_fun h (⟨0, hn⟩ : Fin n)
  exact one_ne_zero hi

theorem gap6 {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ)
    (ha : ∀ i, 0 < a i) :
    minimizers a = ({candidate a} : Set (Fin n → ℝ)) := by
  have hfacts := candidate_facts hn a ha
  have hc : candidate a ∈ constraint a := hfacts.2.1
  have hdecomp := hfacts.2.2.2
  apply Set.ext
  intro x
  constructor
  · intro hx
    change x ∈ constraint a ∧
      ∀ y ∈ constraint a, objective x ≤ objective y at hx
    have hxeq : x = candidate a := by
      by_contra hne
      let dx : Fin n → ℝ := fun i => x i - candidate a i
      have hdx : dx ≠ 0 := by
        intro hzero
        apply hne
        funext i
        have hi := congr_fun hzero i
        dsimp [dx] at hi
        linarith
      have hpos := gap4 dx hdx
      have hdec := hdecomp x hx.1
      have hle := hx.2 (candidate a) hc
      dsimp [dx] at hpos
      unfold secondVariation at hpos
      nlinarith
    simpa only [Set.mem_singleton_iff] using hxeq
  · intro hx
    have hxeq : x = candidate a := by
      simpa only [Set.mem_singleton_iff] using hx
    subst x
    change candidate a ∈ constraint a ∧
      ∀ y ∈ constraint a,
        objective (candidate a) ≤ objective y
    refine ⟨hc, ?_⟩
    intro y hy
    rw [hdecomp y hy]
    exact le_add_of_nonneg_right
      (Finset.sum_nonneg (fun i hi => sq_nonneg (y i - candidate a i)))

theorem gap7 {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ)
    (ha : ∀ i, 0 < a i) :
    objective (candidate a) = (reciprocalSquareSum a)⁻¹ := by
  exact (candidate_facts hn a ha).2.2.1

end

end ProofGap.Exercise3667
