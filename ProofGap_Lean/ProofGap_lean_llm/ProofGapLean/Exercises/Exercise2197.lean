import ProofGapLean.Prelude.Analysis
import Mathlib.Data.Rat.Lemmas
import ProofGapLean.Prelude.Discrete
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Neighborhoods
import Lean.Elab.Tactic.Omega

namespace ProofGap.Exercise2197
noncomputable section

open Filter
open scoped BigOperators

def IsRational (x : ℝ) : Prop := ∃ q : ℚ, (q : ℝ) = x

def χ (x : ℝ) : ℝ := by
  classical
  exact if IsRational x then 1 else 0

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

theorem gap1 (a b : ℝ) (hab : a < b) :
    oscillationOn χ (Set.Icc a b) = 1 := by
  classical
  obtain ⟨q, hqa, hqb⟩ := exists_rat_btwn hab
  have hsqrtpos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hub : 0 < (b - (q : ℝ)) / Real.sqrt 2 :=
    div_pos (sub_pos.2 hqb) hsqrtpos
  obtain ⟨t, ht0, htupper⟩ := exists_rat_btwn hub
  have hprod : (t : ℝ) * Real.sqrt 2 < b - (q : ℝ) :=
    (lt_div_iff₀ hsqrtpos).1 htupper
  have hay : a < (q : ℝ) + (t : ℝ) * Real.sqrt 2 := by
    have htprodpos : 0 < (t : ℝ) * Real.sqrt 2 := mul_pos ht0 hsqrtpos
    linarith
  have hyb : (q : ℝ) + (t : ℝ) * Real.sqrt 2 < b := by
    linarith
  have hsqrt : ¬ IsRational (Real.sqrt 2) := by
    rintro ⟨r, hr⟩
    exact irrational_sqrt_two ⟨r, hr⟩
  have hynrat : ¬ IsRational ((q : ℝ) + (t : ℝ) * Real.sqrt 2) := by
    rintro ⟨r, hr⟩
    have hsqrteq : Real.sqrt 2 = ((r : ℝ) - (q : ℝ)) / (t : ℝ) := by
      apply (eq_div_iff (ne_of_gt ht0)).2
      rw [hr]
      ring
    apply hsqrt
    refine ⟨(r - q) / t, ?_⟩
    calc
      ((((r - q) / t : ℚ) : ℝ)) =
          ((r : ℝ) - (q : ℝ)) / (t : ℝ) := by norm_cast
      _ = Real.sqrt 2 := hsqrteq.symm
  have hqrat : IsRational (q : ℝ) := ⟨q, rfl⟩
  have hone : (1 : ℝ) ∈
      {r : ℝ | ∃ u ∈ Set.Icc a b, ∃ v ∈ Set.Icc a b,
        r = |χ u - χ v|} := by
    refine ⟨(q : ℝ), ⟨le_of_lt hqa, le_of_lt hqb⟩,
      (q : ℝ) + (t : ℝ) * Real.sqrt 2,
      ⟨le_of_lt hay, le_of_lt hyb⟩, ?_⟩
    simp [χ, hqrat, hynrat]
  have hupper : ∀ r ∈
      {r : ℝ | ∃ u ∈ Set.Icc a b, ∃ v ∈ Set.Icc a b,
        r = |χ u - χ v|}, r ≤ (1 : ℝ) := by
    rintro r ⟨u, hu, v, hv, rfl⟩
    by_cases hru : IsRational u <;>
      by_cases hrv : IsRational v <;>
      simp [χ, hru, hrv]
  unfold oscillationOn
  apply le_antisymm
  · exact csSup_le ⟨1, hone⟩ hupper
  · exact le_csSup ⟨1, hupper⟩ hone

theorem gap2 (a b : ℝ) (n : ℕ) (x : ℕ → ℝ)
    (hab : a < b) (hp : IsPartitionOn a b n x) :
    oscillationSum χ n x = b - a := by
  unfold oscillationSum
  calc
    (∑ i ∈ Finset.range n, omega χ x i * width x i) =
        ∑ i ∈ Finset.range n, width x i := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [omega, gap1 (x i) (x (i + 1))
        (hp.2.2 i (Finset.mem_range.mp hi))]
      simp
    _ = x n - x 0 := by
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
    _ = b - a := by
      rw [hp.2.1, hp.1]

theorem gap3 (a b : ℝ) (n : ℕ → ℕ) (x : ℕ → ℕ → ℝ)
    (hab : a < b)
    (hp : ∀ k, IsPartitionOn a b (n k) (x k)) :
    ¬ Tendsto (fun k => oscillationSum χ (n k) (x k))
      atTop (nhds (0 : ℝ)) := by
  intro hlim
  have hfun :
      (fun k => oscillationSum χ (n k) (x k)) =
        (fun _ : ℕ => b - a) := by
    funext k
    exact gap2 a b (n k) (x k) hab (hp k)
  rw [hfun] at hlim
  have hconst : Tendsto (fun _ : ℕ => b - a) atTop (nhds (b - a)) :=
    tendsto_const_nhds
  have heq : b - a = 0 := tendsto_nhds_unique hconst hlim
  exact (sub_ne_zero.mpr hab.ne') heq

theorem gap4 (a b : ℝ) (hab : a < b) :
    ¬ DarbouxIntegrableOn χ a b := by
  intro hint
  have heps : 0 < (b - a) / 2 := by
    linarith
  obtain ⟨n, x, hn, hp, hsum⟩ := hint ((b - a) / 2) heps
  rw [gap2 a b n x hab hp] at hsum
  linarith

theorem gap5 (a b : ℝ) (hab : a < b) :
    ¬ DarbouxIntegrableOn χ a b := by
  exact gap4 a b hab

end
end ProofGap.Exercise2197
