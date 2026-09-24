import ProofGapLean.Prelude.Analysis
import Mathlib.Data.Rat.Lemmas
import ProofGapLean.Prelude.Discrete
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Neighborhoods
import Lean.Elab.Tactic.Omega

namespace ProofGap.Exercise2201
noncomputable section

open Filter
open scoped BigOperators

def IsRational (x : ℝ) : Prop := ∃ q : ℚ, (q : ℝ) = x

def f (x : ℝ) : ℝ := by
  classical
  exact if IsRational x then 1 else -1

def oscillationOn (g : ℝ → ℝ) (I : Set ℝ) : ℝ :=
  sSup {r : ℝ | ∃ u ∈ I, ∃ v ∈ I, r = |g u - g v|}

def IsPartitionOn (a b : ℝ) (n : ℕ) (x : ℕ → ℝ) : Prop :=
  x 0 = a ∧ x n = b ∧ ∀ i < n, x i < x (i + 1)

def width (x : ℕ → ℝ) (i : ℕ) : ℝ := x (i + 1) - x i

def omega (g : ℝ → ℝ) (x : ℕ → ℝ) (i : ℕ) : ℝ :=
  oscillationOn g (Set.Icc (x i) (x (i + 1)))

def oscillationSum (g : ℝ → ℝ) (n : ℕ) (x : ℕ → ℝ) : ℝ :=
  ∑ i ∈ Finset.range n, omega g x i * width x i

def DarbouxIntegrableOn (g : ℝ → ℝ) (a b : ℝ) : Prop :=
  ∀ ε > 0, ∃ n : ℕ, ∃ x : ℕ → ℝ,
    0 < n ∧ IsPartitionOn a b n x ∧ oscillationSum g n x < ε

theorem gap1 (x : ℝ) :
    |f x| = 1 := by
  classical
  by_cases hx : IsRational x <;> simp [f, hx]

private theorem oscillation_abs_f_eq_zero (I : Set ℝ) (hI : I.Nonempty) :
    oscillationOn (fun x => |f x|) I = 0 := by
  have hset :
      {r : ℝ | ∃ u ∈ I, ∃ v ∈ I, r = abs (|f u| - |f v|)} = {0} := by
    ext r
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨u, hu, v, hv, rfl⟩
      rw [gap1 u, gap1 v]
      norm_num
    · intro hr
      subst r
      obtain ⟨u, hu⟩ := hI
      exact ⟨u, hu, u, hu, by simp⟩
  unfold oscillationOn
  rw [hset]
  simp

theorem gap2 (a b : ℝ) :
    ContinuousOn (fun x => |f x|) (Set.Icc a b) := by
  have hfun : (fun x => |f x|) = fun _ : ℝ => 1 := funext gap1
  rw [hfun]
  exact continuousOn_const

theorem gap3 (a b : ℝ) (hab : a < b) :
    DarbouxIntegrableOn (fun x => |f x|) a b := by
  intro ε hε
  let x : ℕ → ℝ := fun i => if i = 0 then a else b
  refine ⟨1, x, by norm_num, ?_, ?_⟩
  · refine ⟨by simp [x], by simp [x], ?_⟩
    intro i hi
    have hi0 : i = 0 := by omega
    subst i
    simpa [x] using hab
  · have hI : (Set.Icc (x 0) (x (0 + 1))).Nonempty := by
      refine ⟨a, ?_⟩
      simp [x, le_of_lt hab]
    have hosc : omega (fun y => |f y|) x 0 = 0 := by
      unfold omega
      exact oscillation_abs_f_eq_zero _ hI
    simpa [oscillationSum, hosc] using hε

theorem gap4 (a b : ℝ) (hab : a < b) :
    oscillationOn f (Set.Icc a b) = 2 := by
  classical
  obtain ⟨q, hqa, hqb⟩ := exists_rat_btwn hab
  obtain ⟨y, hyirr, hya, hyb⟩ := exists_irrational_btwn hab
  have hqrat : IsRational (q : ℝ) := ⟨q, rfl⟩
  have hynrat : ¬ IsRational y := by
    rintro ⟨r, hr⟩
    exact hyirr ⟨r, hr⟩
  have htwo : (2 : ℝ) ∈
      {r : ℝ | ∃ u ∈ Set.Icc a b, ∃ v ∈ Set.Icc a b,
        r = |f u - f v|} := by
    refine ⟨(q : ℝ), ⟨le_of_lt hqa, le_of_lt hqb⟩,
      y, ⟨le_of_lt hya, le_of_lt hyb⟩, ?_⟩
    norm_num [f, hqrat, hynrat]
  have hupper : ∀ r ∈
      {r : ℝ | ∃ u ∈ Set.Icc a b, ∃ v ∈ Set.Icc a b,
        r = |f u - f v|}, r ≤ (2 : ℝ) := by
    rintro r ⟨u, hu, v, hv, rfl⟩
    by_cases hru : IsRational u <;>
      by_cases hrv : IsRational v <;>
      norm_num [f, hru, hrv]
  unfold oscillationOn
  apply le_antisymm
  · exact csSup_le ⟨2, htwo⟩ hupper
  · exact le_csSup ⟨2, hupper⟩ htwo

theorem gap5 (a b : ℝ) (n : ℕ) (x : ℕ → ℝ)
    (hab : a < b) (hp : IsPartitionOn a b n x) :
    oscillationSum f n x = 2 * (b - a) := by
  unfold oscillationSum
  calc
    (∑ i ∈ Finset.range n, omega f x i * width x i) =
        ∑ i ∈ Finset.range n, 2 * width x i := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [omega, gap4 (x i) (x (i + 1))
        (hp.2.2 i (Finset.mem_range.mp hi))]
    _ = 2 * ∑ i ∈ Finset.range n, width x i := by
      rw [Finset.mul_sum]
    _ = 2 * (x n - x 0) := by
      congr 1
      have htel : ∀ m : ℕ,
          (∑ i ∈ Finset.range m, width x i) = x m - x 0 := by
        intro m
        induction m with
        | zero =>
            simp [width]
        | succ m ih =>
            rw [Finset.sum_range_succ, ih]
            simp only [width]
            ring
      exact htel n
    _ = 2 * (b - a) := by
      rw [hp.2.1, hp.1]

theorem gap6 (a b : ℝ) (n : ℕ → ℕ) (x : ℕ → ℕ → ℝ)
    (hab : a < b)
    (hp : ∀ k, IsPartitionOn a b (n k) (x k)) :
    ¬ Tendsto (fun k => oscillationSum f (n k) (x k))
      atTop (nhds (0 : ℝ)) := by
  intro hlim
  have hfun :
      (fun k => oscillationSum f (n k) (x k)) =
        (fun _ : ℕ => 2 * (b - a)) := by
    funext k
    exact gap5 a b (n k) (x k) hab (hp k)
  rw [hfun] at hlim
  have hconst : Tendsto (fun _ : ℕ => 2 * (b - a))
      atTop (nhds (2 * (b - a))) := tendsto_const_nhds
  have heq : 2 * (b - a) = 0 := tendsto_nhds_unique hconst hlim
  nlinarith

theorem gap7 (a b : ℝ) (hab : a < b) :
    ¬ DarbouxIntegrableOn f a b := by
  intro hint
  have heps : 0 < b - a := sub_pos.mpr hab
  obtain ⟨n, x, hn, hp, hsum⟩ := hint (b - a) heps
  rw [gap5 a b n x hab hp] at hsum
  linarith

theorem gap8 (a b : ℝ) (hab : a < b) :
    ¬ (∀ g : ℝ → ℝ,
      DarbouxIntegrableOn (fun x => |g x|) a b →
        DarbouxIntegrableOn g a b) := by
  intro hall
  exact gap7 a b hab (hall f (gap3 a b hab))

end
end ProofGap.Exercise2201
