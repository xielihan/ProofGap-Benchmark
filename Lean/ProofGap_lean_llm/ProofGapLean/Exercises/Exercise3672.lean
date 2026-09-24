import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Convex.SpecificFunctions.Deriv
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise3672

noncomputable section

def objective (n : ℕ) (q : ℝ × ℝ) : ℝ :=
  (q.1 ^ n + q.2 ^ n) / 2

def slice (a : ℝ) : Set (ℝ × ℝ) :=
  {q | q.1 + q.2 = a ∧ 0 < a ∧ 0 ≤ q.1 ∧ 0 ≤ q.2}

def critical (n : ℕ) (a : ℝ) (q : ℝ × ℝ) (lambda : ℝ) : Prop :=
  (n : ℝ) / 2 * q.1 ^ (n - 1) + lambda = 0 ∧
    (n : ℝ) / 2 * q.2 ^ (n - 1) + lambda = 0 ∧
    q ∈ slice a

def midpoint (a : ℝ) : ℝ × ℝ :=
  (a / 2, a / 2)

def minimizers (n : ℕ) (a : ℝ) : Set (ℝ × ℝ) :=
  {q | q ∈ slice a ∧
    ∀ r ∈ slice a, objective n q ≤ objective n r}

private theorem pow_mean_le (n : ℕ) (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    ((x + y) / 2) ^ n ≤ (x ^ n + y ^ n) / 2 := by
  have h := Real.pow_arith_mean_le_arith_mean_pow
    (Finset.univ : Finset (Fin 2))
    (fun _ => (1 / 2 : ℝ)) (fun i => if i = 0 then x else y)
    (by intro i hi; norm_num)
    (by norm_num [Fin.sum_univ_two])
    (by intro i hi; fin_cases i <;> simp [hx, hy]) n
  simp [Fin.sum_univ_two] at h
  convert h using 1 <;> ring

private theorem eq_of_reverse_pow_mean (n : ℕ) (hn : 2 ≤ n)
    (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hrev : (x ^ n + y ^ n) / 2 ≤ ((x + y) / 2) ^ n) :
    x = y := by
  let w : Fin 2 → ℝ := fun _ => 1 / 2
  let z : Fin 2 → ℝ := fun i => if i = 0 then x else y
  have heq := (strictConvexOn_pow hn).eq_of_le_map_sum
    (t := Finset.univ) (w := w) (p := z)
    (by intro i hi; dsimp [w]; norm_num)
    (by dsimp [w]; norm_num [Fin.sum_univ_two])
    (by intro i hi; fin_cases i <;> simp [z, hx, hy])
    (by
      simp [w, z, Fin.sum_univ_two]
      convert hrev using 1 <;> ring)
    (j := (0 : Fin 2)) (by simp) (k := (1 : Fin 2)) (by simp)
  simpa [z] using heq

private theorem critical_coordinates (n : ℕ) (a : ℝ) (hn : 1 < n)
    {q : ℝ × ℝ} {lambda : ℝ} (hcrit : critical n a q lambda) :
    q.1 = a / 2 ∧ q.2 = a / 2 := by
  rcases hcrit with ⟨h₁, h₂, hsum, ha, hx, hy⟩
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (Nat.zero_lt_of_lt hn)
  have hp : q.1 ^ (n - 1) = q.2 ^ (n - 1) := by
    nlinarith
  have hnsub : n - 1 ≠ 0 := (Nat.sub_pos_of_lt hn).ne'
  have hxy : q.1 = q.2 := (pow_left_inj₀ hx hy hnsub).mp hp
  constructor <;> linarith

theorem gap1 (n : ℕ) (a : ℝ) (hn : 1 < n) (ha : 0 < a) :
    ∀ q lambda, critical n a q lambda → q.1 = a / 2 := by
  intro q lambda hcrit
  exact (critical_coordinates n a hn hcrit).1

theorem gap2 (n : ℕ) (a : ℝ) (hn : 1 < n) (ha : 0 < a) :
    ∀ q lambda, critical n a q lambda → q.2 = a / 2 := by
  intro q lambda hcrit
  exact (critical_coordinates n a hn hcrit).2

theorem gap3 (n : ℕ) (a : ℝ) (hn : 1 < n) (ha : 0 < a) :
    {q | ∃ lambda, critical n a q lambda} =
      ({midpoint a} : Set (ℝ × ℝ)) := by
  ext q
  constructor
  · rintro ⟨lambda, hcrit⟩
    rcases critical_coordinates n a hn hcrit with ⟨h₁, h₂⟩
    simp only [Set.mem_singleton_iff]
    exact Prod.ext h₁ h₂
  · intro hq
    simp only [Set.mem_singleton_iff] at hq
    subst q
    refine ⟨-((n : ℝ) / 2 * (a / 2) ^ (n - 1)), ?_⟩
    unfold critical slice midpoint
    dsimp
    refine ⟨?_, ?_, ?_⟩
    · ring
    · ring
    exact ⟨by ring, ha, by positivity, by positivity⟩

theorem gap4 (n : ℕ) (a : ℝ) :
    objective n (0, a) = objective n (a, 0) := by
  simp [objective, add_comm]

-- Statement correction: gap5 requires 1 ≤ n; the n = 0 case is false.
theorem gap5 (n : ℕ) (a : ℝ) (hn : 1 ≤ n) :
    objective n (a, 0) = a ^ n / 2 := by
  simp [objective, zero_pow (Nat.ne_zero_of_lt hn)]

theorem gap6 (n : ℕ) (a : ℝ) (hn : 1 ≤ n) (ha : 0 ≤ a) :
    a ^ n / 2 ≥ (a / 2) ^ n := by
  have h := pow_mean_le n a 0 ha le_rfl
  simpa [zero_pow (Nat.ne_zero_of_lt hn)] using h

theorem gap7 (n : ℕ) (a : ℝ) :
    (a / 2) ^ n = objective n (midpoint a) := by
  simp [objective, midpoint]

theorem gap8 (n : ℕ) (a : ℝ) (hn : 1 ≤ n) (ha : 0 ≤ a) :
    objective n (0, a) ≥ objective n (midpoint a) := by
  rw [gap4 n a, gap5 n a hn, ← gap7 n a]
  exact gap6 n a hn ha

theorem gap9 (n : ℕ) (a : ℝ) (hn : 1 < n) (ha : 0 < a) :
    minimizers n a = ({midpoint a} : Set (ℝ × ℝ)) := by
  ext q
  constructor
  · rintro ⟨hqslice, hmin⟩
    rcases hqslice with ⟨hsum, ha', hx, hy⟩
    have hmid : midpoint a ∈ slice a := by
      unfold midpoint slice
      dsimp
      exact ⟨by ring, ha, by positivity, by positivity⟩
    have hrev := hmin (midpoint a) hmid
    have hrev' :
        (q.1 ^ n + q.2 ^ n) / 2 ≤ ((q.1 + q.2) / 2) ^ n := by
      simpa [objective, midpoint, hsum] using hrev
    have hxy := eq_of_reverse_pow_mean n hn q.1 q.2 hx hy hrev'
    have h₁ : q.1 = a / 2 := by linarith
    have h₂ : q.2 = a / 2 := by linarith
    simp only [Set.mem_singleton_iff]
    exact Prod.ext h₁ h₂
  · intro hq
    simp only [Set.mem_singleton_iff] at hq
    subst q
    constructor
    · unfold midpoint slice
      dsimp
      exact ⟨by ring, ha, by positivity, by positivity⟩
    intro r hr
    rcases hr with ⟨hsum, ha', hx, hy⟩
    have h := pow_mean_le n r.1 r.2 hx hy
    simpa [objective, midpoint, hsum] using h

theorem gap10 (n : ℕ) (a : ℝ) (hn : 1 < n) (ha : 0 < a) :
    objective n (midpoint a) = (a / 2) ^ n := by
  exact (gap7 n a).symm

theorem gap11 (n : ℕ) (x y a : ℝ) (hn : 1 ≤ n)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hsum : x + y = a) :
    (x ^ n + y ^ n) / 2 ≥ (a / 2) ^ n := by
  simpa [← hsum] using pow_mean_le n x y hx hy

theorem gap12 (n : ℕ) (x y : ℝ) (hx : x = 0) (hy : y = 0) :
    (x ^ n + y ^ n) / 2 = ((x + y) / 2) ^ n := by
  subst x
  subst y
  simp

theorem gap13 (x y a : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hne : (x, y) ≠ (0, 0)) (hsum : a = x + y) :
    a > 0 := by
  have hpos : 0 < x ∨ 0 < y := by
    by_contra h
    push_neg at h
    have hx0 : x = 0 := le_antisymm h.1 hx
    have hy0 : y = 0 := le_antisymm h.2 hy
    exact hne (Prod.ext hx0 hy0)
  rcases hpos with hx' | hy' <;> linarith

theorem gap14 (n : ℕ) (x y a : ℝ) (hn : 1 ≤ n)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hne : (x, y) ≠ (0, 0))
    (hsum : a = x + y) :
    (x ^ n + y ^ n) / 2 ≥ (a / 2) ^ n := by
  rw [hsum]
  exact pow_mean_le n x y hx hy

theorem gap15 (n : ℕ) (x y a : ℝ) (hsum : a = x + y) :
    (a / 2) ^ n = ((x + y) / 2) ^ n := by
  rw [hsum]

theorem gap16 (n : ℕ) (x y a : ℝ) (hn : 1 ≤ n)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hne : (x, y) ≠ (0, 0))
    (hsum : a = x + y) :
    (x ^ n + y ^ n) / 2 ≥ ((x + y) / 2) ^ n := by
  exact pow_mean_le n x y hx hy

theorem gap17 (n : ℕ) (x y : ℝ) (hn : 1 ≤ n)
    (hx : 0 ≤ x) (hy : 0 ≤ y) :
    (x ^ n + y ^ n) / 2 ≥ ((x + y) / 2) ^ n := by
  exact pow_mean_le n x y hx hy

theorem gap18 :
    ∀ (n : ℕ) (x y : ℝ), 1 ≤ n → 0 ≤ x → 0 ≤ y →
      (x ^ n + y ^ n) / 2 ≥ ((x + y) / 2) ^ n := by
  intro n x y hn hx hy
  exact pow_mean_le n x y hx hy

end

end ProofGap.Exercise3672
