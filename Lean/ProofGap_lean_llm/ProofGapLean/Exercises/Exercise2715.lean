import ProofGapLean.Prelude.Analysis
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Lean.Elab.Tactic.Omega

namespace ProofGap.Exercise2715

noncomputable section

def u (n : ℕ) : ℝ :=
  if n = 1 then 1 else -((3 / 2 : ℝ) ^ (n - 1))

def v (n : ℕ) : ℝ :=
  if n = 1 then 1
  else (3 / 2 : ℝ) ^ (n - 2) * ((2 : ℝ) ^ (n - 1) + 1 / (2 : ℝ) ^ n)

def c (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 n, u k * v (n + 1 - k)

def expandedCoefficient (n : ℕ) : ℝ :=
  (3 / 2 : ℝ) ^ (n - 2) *
    ((2 : ℝ) ^ (n - 1) -
      (∑ j ∈ Finset.range (n - 1), (2 : ℝ) ^ j) +
      1 / (2 : ℝ) ^ n -
      ∑ j ∈ Finset.Icc 1 (n - 1), 1 / (2 : ℝ) ^ j)

private theorem sum_pow_two (m : ℕ) :
    ∑ j ∈ Finset.range m, (2 : ℝ) ^ j = (2 : ℝ) ^ m - 1 := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Finset.sum_range_succ, ih, pow_succ]
      ring

private theorem sum_inv_pow_two (m : ℕ) :
    ∑ j ∈ Finset.Icc 1 m, 1 / (2 : ℝ) ^ j =
      1 - 1 / (2 : ℝ) ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
      have hset :
          Finset.Icc 1 (m + 1) =
            insert (m + 1) (Finset.Icc 1 m) := by
        ext j
        simp only [Finset.mem_Icc, Finset.mem_insert]
        omega
      have hnot : m + 1 ∉ Finset.Icc 1 m := by
        simp [Finset.mem_Icc]
      rw [hset, Finset.sum_insert hnot, ih, pow_succ]
      field_simp
      <;> ring

private theorem sum_reverse_pow_two (n : ℕ) (hn : 2 ≤ n) :
    ∑ k ∈ Finset.Icc 2 n, (2 : ℝ) ^ (n - k) =
      ∑ j ∈ Finset.range (n - 1), (2 : ℝ) ^ j := by
  apply Finset.sum_bij (fun k _ => n - k)
  · intro k hk
    simp only [Finset.mem_range]
    have hk' := Finset.mem_Icc.mp hk
    omega
  · intro a ha b hb hab
    have ha' := Finset.mem_Icc.mp ha
    have hb' := Finset.mem_Icc.mp hb
    omega
  · intro j hj
    simp only [Finset.mem_range] at hj
    refine ⟨n - j, ?_⟩
    refine ⟨?_, ?_⟩
    · apply Finset.mem_Icc.mpr
      constructor <;> omega
    · omega
  · intro a ha
    rfl

private theorem sum_reverse_inv_pow_two (n : ℕ) (hn : 2 ≤ n) :
    ∑ k ∈ Finset.Icc 2 n, 1 / (2 : ℝ) ^ (n + 1 - k) =
      ∑ j ∈ Finset.Icc 1 (n - 1), 1 / (2 : ℝ) ^ j := by
  apply Finset.sum_bij (fun k _ => n + 1 - k)
  · intro k hk
    apply Finset.mem_Icc.mpr
    have hk' := Finset.mem_Icc.mp hk
    constructor <;> omega
  · intro a ha b hb hab
    have ha' := Finset.mem_Icc.mp ha
    have hb' := Finset.mem_Icc.mp hb
    omega
  · intro j hj
    have hj' := Finset.mem_Icc.mp hj
    refine ⟨n + 1 - j, ?_⟩
    refine ⟨?_, ?_⟩
    · apply Finset.mem_Icc.mpr
      constructor <;> omega
    · omega
  · intro a ha
    rfl

private theorem convolution_expansion (n : ℕ) (hn : 2 ≤ n) :
    c n = expandedCoefficient n := by
  have hn1 : n ≠ 1 := by omega
  have hsplit :
      Finset.Icc 1 n = insert 1 (Finset.Icc 2 n) := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  have hnot : 1 ∉ Finset.Icc 2 n := by
    simp [Finset.mem_Icc]
  have hfirst :
      u 1 * v (n + 1 - 1) =
        (3 / 2 : ℝ) ^ (n - 2) *
          ((2 : ℝ) ^ (n - 1) + 1 / (2 : ℝ) ^ n) := by
    simp [u, v, hn1]
  have hterm : ∀ k ∈ Finset.Icc 2 n,
      u k * v (n + 1 - k) =
        -((3 / 2 : ℝ) ^ (n - 2)) *
          ((2 : ℝ) ^ (n - k) + 1 / (2 : ℝ) ^ (n + 1 - k)) := by
    intro k hk
    have hk' := Finset.mem_Icc.mp hk
    by_cases hkn : k = n
    · subst k
      have he : n - 1 = (n - 2) + 1 := by omega
      have hz : n - n = 0 := by omega
      have hm : n + 1 - n = 1 := by omega
      rw [hz, hm]
      simp only [u, v, if_neg hn1, if_pos rfl]
      rw [he, pow_succ]
      norm_num
    · have hk1 : k ≠ 1 := by omega
      have hlt : k < n := by omega
      have hm1 : n + 1 - k ≠ 1 := by omega
      have he1 : n + 1 - k - 1 = n - k := by omega
      have hepow : (k - 1) + (n + 1 - k - 2) = n - 2 := by omega
      have hp :
          (3 / 2 : ℝ) ^ (k - 1) *
              (3 / 2 : ℝ) ^ (n + 1 - k - 2) =
            (3 / 2 : ℝ) ^ (n - 2) := by
        rw [← pow_add, hepow]
      simp only [u, v, if_neg hk1, if_neg hm1]
      calc
        -((3 / 2 : ℝ) ^ (k - 1)) *
              ((3 / 2 : ℝ) ^ (n + 1 - k - 2) *
                ((2 : ℝ) ^ (n + 1 - k - 1) +
                  1 / (2 : ℝ) ^ (n + 1 - k))) =
            -((3 / 2 : ℝ) ^ (k - 1) *
                (3 / 2 : ℝ) ^ (n + 1 - k - 2)) *
              ((2 : ℝ) ^ (n + 1 - k - 1) +
                1 / (2 : ℝ) ^ (n + 1 - k)) := by ring
        _ = -((3 / 2 : ℝ) ^ (n - 2)) *
              ((2 : ℝ) ^ (n - k) +
                1 / (2 : ℝ) ^ (n + 1 - k)) := by rw [hp, he1]
  have hsumterm :
      (∑ k ∈ Finset.Icc 2 n, u k * v (n + 1 - k)) =
        ∑ k ∈ Finset.Icc 2 n,
          -((3 / 2 : ℝ) ^ (n - 2)) *
            ((2 : ℝ) ^ (n - k) + 1 / (2 : ℝ) ^ (n + 1 - k)) := by
    apply Finset.sum_congr rfl
    intro k hk
    exact hterm k hk
  have hsumfactor :
      (∑ k ∈ Finset.Icc 2 n,
          -((3 / 2 : ℝ) ^ (n - 2)) *
            ((2 : ℝ) ^ (n - k) + 1 / (2 : ℝ) ^ (n + 1 - k))) =
        -((3 / 2 : ℝ) ^ (n - 2)) *
          ((∑ k ∈ Finset.Icc 2 n, (2 : ℝ) ^ (n - k)) +
            ∑ k ∈ Finset.Icc 2 n, 1 / (2 : ℝ) ^ (n + 1 - k)) := by
    rw [← Finset.mul_sum, Finset.sum_add_distrib]
  unfold c
  rw [hsplit, Finset.sum_insert hnot, hfirst, hsumterm, hsumfactor]
  rw [sum_reverse_pow_two n hn, sum_reverse_inv_pow_two n hn]
  unfold expandedCoefficient
  ring

theorem gap1 :
    c 1 = u 1 * v 1 := by
  simp [c, u, v]

theorem gap2 :
    u 1 * v 1 = 1 := by
  simp [u, v]

theorem gap3 :
    c 1 = 1 := by
  exact gap1.trans gap2

theorem gap4 :
    ∀ n : ℕ, 1 ≤ n →
      c n = ∑ k ∈ Finset.Icc 1 n, u k * v (n + 1 - k) := by
  intro n hn
  rfl

theorem gap5 :
    ∀ n : ℕ, 2 ≤ n → c n = expandedCoefficient n := by
  intro n hn
  exact convolution_expansion n hn

theorem gap6 :
    ∀ n : ℕ, 2 ≤ n →
      c n =
        (3 / 2 : ℝ) ^ (n - 2) *
          (1 / (2 : ℝ) ^ n + 1 / (2 : ℝ) ^ (n - 1)) := by
  intro n hn
  rw [gap5 n hn]
  unfold expandedCoefficient
  rw [sum_pow_two, sum_inv_pow_two]
  ring

theorem gap7 :
    ∀ n : ℕ, 2 ≤ n →
      (3 / 2 : ℝ) ^ (n - 2) *
          (1 / (2 : ℝ) ^ n + 1 / (2 : ℝ) ^ (n - 1)) =
        (3 / 2 : ℝ) ^ (n - 2) * (3 / (2 : ℝ) ^ n) := by
  intro n hn
  have hpow : (2 : ℝ) ^ n = (2 : ℝ) ^ (n - 1) * 2 := by
    calc
      (2 : ℝ) ^ n = (2 : ℝ) ^ ((n - 1) + 1) := by
        exact congrArg (fun k : ℕ => (2 : ℝ) ^ k) (by omega)
      _ = (2 : ℝ) ^ (n - 1) * 2 := by rw [pow_succ]
  have hinner :
      1 / (2 : ℝ) ^ n + 1 / (2 : ℝ) ^ (n - 1) =
        3 / (2 : ℝ) ^ n := by
    rw [hpow]
    field_simp
    <;> ring
  rw [hinner]

theorem gap8 :
    ∀ n : ℕ, 2 ≤ n →
      (3 / 2 : ℝ) ^ (n - 2) * (3 / (2 : ℝ) ^ n) =
        (3 / 4 : ℝ) ^ (n - 1) := by
  intro n hn
  have hn1 : n - 1 = (n - 2) + 1 := by omega
  have hn2 : n = (n - 2) + 2 := by omega
  rw [hn1, hn2]
  have hden :
      (3 : ℝ) / (2 : ℝ) ^ ((n - 2) + 2) =
        (1 / 2 : ℝ) ^ (n - 2) * (3 / 4 : ℝ) := by
    rw [pow_add, div_pow]
    norm_num
    field_simp
    <;> ring
  rw [hden]
  calc
    (3 / 2 : ℝ) ^ (n - 2) *
          ((1 / 2 : ℝ) ^ (n - 2) * (3 / 4 : ℝ)) =
        (((3 / 2 : ℝ) * (1 / 2 : ℝ)) ^ (n - 2)) * (3 / 4 : ℝ) := by
          rw [← mul_assoc, ← mul_pow]
    _ = (3 / 4 : ℝ) ^ (n - 2) * (3 / 4 : ℝ) := by norm_num
    _ = (3 / 4 : ℝ) ^ ((n - 2) + 1) := by rw [pow_succ]

theorem gap9 :
    ∀ n : ℕ, 1 ≤ n → c n = (3 / 4 : ℝ) ^ (n - 1) := by
  intro n hn
  by_cases h1 : n = 1
  · subst n
    simpa using gap3
  · have hn2 : 2 ≤ n := by omega
    rw [gap6 n hn2, gap7 n hn2, gap8 n hn2]

theorem gap10 :
    ∑' n : ℕ, c (n + 1) = ∑' n : ℕ, (3 / 4 : ℝ) ^ n := by
  apply tsum_congr
  intro n
  simpa using gap9 (n + 1) (by omega)

theorem gap11 :
    Summable (fun n : ℕ => c (n + 1)) := by
  have hgeom : Summable (fun n : ℕ => (3 / 4 : ℝ) ^ n) :=
    summable_geometric_of_norm_lt_one (by norm_num)
  apply hgeom.congr
  intro n
  symm
  simpa using gap9 (n + 1) (by omega)

theorem gap12 :
    Summable (fun n : ℕ => |c (n + 1)|) := by
  have hgeom : Summable (fun n : ℕ => (3 / 4 : ℝ) ^ n) :=
    summable_geometric_of_norm_lt_one (by norm_num)
  apply hgeom.congr
  intro n
  rw [gap9 (n + 1) (by omega)]
  exact (abs_of_nonneg (pow_nonneg (by norm_num) n)).symm

end

end ProofGap.Exercise2715
