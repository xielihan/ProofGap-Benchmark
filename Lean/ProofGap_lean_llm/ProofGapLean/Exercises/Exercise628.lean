import ProofGapLean.Prelude.Sequences
import ProofGapLean.Prelude.Finite
import ProofGapLean.Prelude.Elementary
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

namespace ProofGap.Exercise628

noncomputable section

def tail (x : ℝ) (n : ℕ) : ℝ :=
  (Finset.Icc (n + 1) (2 * n)).sum (fun k => x ^ k / (k.factorial : ℝ))
def absoluteTail (x : ℝ) (n : ℕ) : ℝ :=
  (Finset.Icc (n + 1) (2 * n)).sum (fun k => |x| ^ k / (k.factorial : ℝ))
def geometric (x : ℝ) (n : ℕ) : ℝ :=
  (Finset.range n).sum (fun k => |x| ^ k)
def bound (x : ℝ) (n : ℕ) : ℝ :=
  |x| ^ (n + 1) / ((n + 1).factorial : ℝ) * geometric x n
def closedBound (x : ℝ) (n : ℕ) : ℝ :=
  |x| ^ (n + 1) / ((n + 1).factorial : ℝ) *
    ((1 - |x| ^ n) / (1 - |x|))
def decomposedBound (x : ℝ) (n : ℕ) : ℝ :=
  (1 / (1 - |x|)) *
    (|x| ^ (n + 1) / ((n + 1).factorial : ℝ) -
      (|x| / (n + 1)) * ((|x| ^ 2) ^ n / (n.factorial : ℝ)))

/-- Exercise 628, gap 1; replace the sum ellipsis by `Finset.Icc`. -/
private theorem sum_Icc_succ_two_mul (f : ℕ → ℝ) (n : ℕ) :
    (Finset.Icc (n + 1) (2 * n)).sum f =
      (Finset.range n).sum (fun j => f (n + 1 + j)) := by
  have hset :
      Finset.Icc (n + 1) (2 * n) =
        (Finset.range n).image (fun j => n + 1 + j) := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_image, Finset.mem_range]
    constructor
    · intro hk
      refine ⟨k - (n + 1), ?_, ?_⟩
      · omega
      · omega
    · rintro ⟨j, hj, rfl⟩
      omega
  rw [hset, Finset.sum_image]
  intro a ha b hb hab
  exact Nat.add_left_cancel hab

private theorem geometric_sum_closed (r : ℝ) (n : ℕ) (hr : r ≠ 1) :
    (Finset.range n).sum (fun k => r ^ k) =
      (1 - r ^ n) / (1 - r) := by
  have hden : 1 - r ≠ 0 := sub_ne_zero.mpr (Ne.symm hr)
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih, pow_succ]
      field_simp [hden] <;> ring

private theorem factorial_le_factorial_add (a j : ℕ) :
    a.factorial ≤ (a + j).factorial := by
  induction j with
  | zero => simp
  | succ j ih =>
      calc
        a.factorial ≤ (a + j).factorial := ih
        _ ≤ (a + j + 1) * (a + j).factorial := by
          have h : 1 ≤ a + j + 1 := by omega
          simpa only [one_mul] using
            Nat.mul_le_mul_right (a + j).factorial h
        _ = (a + (j + 1)).factorial := by
          simpa [Nat.add_assoc] using (Nat.factorial_succ (a + j)).symm

private theorem factorial_succ_cast (n : ℕ) :
    ((n + 1).factorial : ℝ) =
      (((n + 1 : ℕ) : ℝ)) * (n.factorial : ℝ) := by
  exact_mod_cast Nat.factorial_succ n

private theorem pow_div_factorial_tendsto_zero (r : ℝ) :
    Filter.Tendsto (fun n : ℕ => r ^ n / (n.factorial : ℝ))
      Filter.atTop (nhds 0) := by
  have hs : Summable (fun n : ℕ => r ^ n / (n.factorial : ℝ)) := by
    refine summable_of_ratio_norm_eventually_le (r := (1 / 2 : ℝ)) (by norm_num) ?_
    obtain ⟨N, hN⟩ := exists_nat_ge (2 * |r|)
    filter_upwards [Filter.eventually_ge_atTop N] with n hn
    have hnr : 2 * |r| ≤ (((n + 1 : ℕ) : ℝ)) := by
      calc
        2 * |r| ≤ (N : ℝ) := hN
        _ ≤ (n : ℝ) := by exact_mod_cast hn
        _ ≤ (((n + 1 : ℕ) : ℝ)) := by exact_mod_cast Nat.le_succ n
    have hpos : 0 < (((n + 1 : ℕ) : ℝ)) := by positivity
    have hrhalf : |r| ≤ (((n + 1 : ℕ) : ℝ)) / 2 := by
      apply (le_div_iff₀ (show (0 : ℝ) < 2 by norm_num)).2
      simpa [mul_comm] using hnr
    have hfactor : |r| / (((n + 1 : ℕ) : ℝ)) ≤ (1 / 2 : ℝ) := by
      apply (div_le_iff₀ hpos).2
      calc
        |r| ≤ (((n + 1 : ℕ) : ℝ)) / 2 := hrhalf
        _ = (1 / 2 : ℝ) * (((n + 1 : ℕ) : ℝ)) := by ring
    have heq :
        ‖r ^ (n + 1) / ((n + 1).factorial : ℝ)‖ =
          (|r| / (((n + 1 : ℕ) : ℝ))) *
            ‖r ^ n / (n.factorial : ℝ)‖ := by
      simp only [Real.norm_eq_abs, abs_div, abs_pow]
      rw [factorial_succ_cast, abs_mul]
      rw [abs_of_pos hpos,
        abs_of_pos (show 0 < (n.factorial : ℝ) by positivity)]
      rw [pow_succ]
      have hs' : (((n + 1 : ℕ) : ℝ)) ≠ 0 := ne_of_gt hpos
      have hf : (n.factorial : ℝ) ≠ 0 := by positivity
      field_simp [hs', hf] <;> ring
    rw [heq]
    exact mul_le_mul_of_nonneg_right hfactor (norm_nonneg _)
  exact hs.tendsto_atTop_zero

private theorem nat_succ_tendsto_atTop :
    Filter.Tendsto (fun n : ℕ => n + 1) Filter.atTop Filter.atTop := by
  refine Filter.tendsto_atTop.2 ?_
  intro b
  filter_upwards [Filter.eventually_ge_atTop b] with n hn
  omega

private theorem tendsto_zero_of_abs_le_nonneg
    {f g : ℕ → ℝ}
    (hg : Filter.Tendsto g Filter.atTop (nhds 0))
    (hg0 : ∀ n, 0 ≤ g n)
    (hfg : ∀ n, |f n| ≤ g n) :
    Filter.Tendsto f Filter.atTop (nhds 0) := by
  rw [Metric.tendsto_atTop] at hg ⊢
  intro ε hε
  obtain ⟨N, hN⟩ := hg ε hε
  refine ⟨N, fun n hn => ?_⟩
  have hgn : g n < ε := by
    simpa [Real.dist_eq, abs_of_nonneg (hg0 n)] using hN n hn
  have hfn : |f n| < ε := lt_of_le_of_lt (hfg n) hgn
  simpa [Real.dist_eq] using hfn

theorem gap1 (x : ℝ) (n : ℕ) : |tail x n| ≤ absoluteTail x n := by
  unfold tail absoluteTail
  calc
    |(Finset.Icc (n + 1) (2 * n)).sum
        (fun k => x ^ k / (k.factorial : ℝ))| ≤
        (Finset.Icc (n + 1) (2 * n)).sum
          (fun k => |x ^ k / (k.factorial : ℝ)|) :=
      Finset.abs_sum_le_sum_abs _ _
    _ = (Finset.Icc (n + 1) (2 * n)).sum
        (fun k => |x| ^ k / (k.factorial : ℝ)) := by
      apply Finset.sum_congr rfl
      intro k hk
      simp [abs_div, abs_pow,
        abs_of_nonneg (show (0 : ℝ) ≤ (k.factorial : ℝ) by positivity)]

/-- Exercise 628, gap 2. -/
theorem gap2 (x : ℝ) (n : ℕ) : absoluteTail x n ≤ bound x n := by
  unfold absoluteTail bound geometric
  rw [sum_Icc_succ_two_mul]
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum (fun j hj => ?_)
  have hfac :
      (((n + 1).factorial : ℕ) : ℝ) ≤
        (((n + 1 + j).factorial : ℕ) : ℝ) := by
    exact_mod_cast factorial_le_factorial_add (n + 1) j
  calc
    |x| ^ (n + 1 + j) / ((n + 1 + j).factorial : ℝ) ≤
        (|x| ^ (n + 1) * |x| ^ j) / ((n + 1).factorial : ℝ) := by
      rw [pow_add]
      apply (div_le_div_iff₀ (by positivity) (by positivity)).2
      exact mul_le_mul_of_nonneg_left hfac (by positivity)
    _ = (|x| ^ (n + 1) / ((n + 1).factorial : ℝ)) * |x| ^ j := by
      ring

/-- Exercise 628, gap 3. -/
theorem gap3 (x : ℝ) (n : ℕ) : |tail x n| ≤ bound x n := by
  exact (gap1 x n).trans (gap2 x n)

/-- Exercise 628, gap 4. -/
theorem gap4 (x : ℝ) (hx : |x| = 1) :
    Filter.Tendsto (fun n : ℕ => (n : ℝ) / ((n + 1).factorial : ℝ))
      Filter.atTop (nhds 0) := by
  refine tendsto_zero_of_abs_le_nonneg
    (pow_div_factorial_tendsto_zero (1 : ℝ)) ?_ ?_
  · intro n
    positivity
  · intro n
    rw [abs_of_nonneg (by positivity)]
    simp only [one_pow]
    have hratio :
        (n : ℝ) / (((n + 1 : ℕ) : ℝ)) ≤ 1 := by
      apply (div_le_iff₀ (by positivity)).2
      norm_num
    have heq :
        (n : ℝ) / ((n + 1).factorial : ℝ) =
          ((n : ℝ) / (((n + 1 : ℕ) : ℝ))) *
            (1 / (n.factorial : ℝ)) := by
      rw [factorial_succ_cast]
      have hs : (((n + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
      have hf : (n.factorial : ℝ) ≠ 0 := by positivity
      field_simp [hs, hf] <;> ring
    rw [heq]
    simpa using
      (mul_le_mul_of_nonneg_right hratio
        (show (0 : ℝ) ≤ 1 / (n.factorial : ℝ) by positivity))

/-- Exercise 628, gap 5. -/
theorem gap5 (x : ℝ) (n : ℕ) (hx : |x| ≠ 1) :
    bound x n = closedBound x n := by
  unfold bound closedBound geometric
  rw [geometric_sum_closed |x| n hx]

/-- Exercise 628, gap 6. -/
theorem gap6 (x : ℝ) (n : ℕ) (hx : |x| ≠ 1) :
    closedBound x n = decomposedBound x n := by
  have hden : 1 - |x| ≠ 0 := sub_ne_zero.mpr (Ne.symm hx)
  have hterm :
      (|x| ^ (n + 1) / ((n + 1).factorial : ℝ)) * |x| ^ n =
        (|x| / (n + 1)) * ((|x| ^ 2) ^ n / (n.factorial : ℝ)) := by
    rw [factorial_succ_cast]
    have hs : (((n + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
    have hf : (n.factorial : ℝ) ≠ 0 := by positivity
    field_simp [hs, hf] <;>
      simp only [pow_succ, mul_pow, Nat.cast_add, Nat.cast_one] <;>
      ring
  unfold closedBound decomposedBound
  calc
    (|x| ^ (n + 1) / ((n + 1).factorial : ℝ)) *
          ((1 - |x| ^ n) / (1 - |x|)) =
        (1 / (1 - |x|)) *
          (|x| ^ (n + 1) / ((n + 1).factorial : ℝ) -
            (|x| ^ (n + 1) / ((n + 1).factorial : ℝ)) * |x| ^ n) := by
      have hf : ((n + 1).factorial : ℝ) ≠ 0 := by positivity
      field_simp [hden, hf] <;> ring
    _ = (1 / (1 - |x|)) *
          (|x| ^ (n + 1) / ((n + 1).factorial : ℝ) -
            (|x| / (n + 1)) * ((|x| ^ 2) ^ n / (n.factorial : ℝ))) := by
      rw [hterm]

/-- Exercise 628, gap 7. -/
theorem gap7 (x : ℝ) (n : ℕ) (hx : |x| ≠ 1) :
    bound x n = decomposedBound x n := by
  exact (gap5 x n hx).trans (gap6 x n hx)

/-- Exercise 628, gap 8. -/
theorem gap8 (x : ℝ) (hx : |x| ≠ 1) :
    Filter.Tendsto
      (fun n : ℕ => |x| ^ (n + 1) / ((n + 1).factorial : ℝ))
      Filter.atTop (nhds 0) := by
  simpa using
    (pow_div_factorial_tendsto_zero |x|).comp nat_succ_tendsto_atTop

/-- Exercise 628, gap 9. -/
theorem gap9 (x : ℝ) (hx : |x| ≠ 1) :
    Filter.Tendsto
      (fun n : ℕ => (|x| ^ 2) ^ n / (n.factorial : ℝ))
      Filter.atTop (nhds 0) := by
  simpa using pow_div_factorial_tendsto_zero (x ^ 2)

/-- Exercise 628, gap 10. -/
theorem gap10 (x : ℝ) :
    Filter.Tendsto (tail x) Filter.atTop (nhds 0) := by
  have hb : Filter.Tendsto (bound x) Filter.atTop (nhds 0) := by
    by_cases hx : |x| = 1
    · change Filter.Tendsto (fun n : ℕ => bound x n)
        Filter.atTop (nhds 0)
      simpa [bound, geometric, hx, div_eq_mul_inv, mul_comm] using gap4 x hx
    · have hscaled :
          Filter.Tendsto
            (fun n : ℕ => |x| * ((|x| ^ 2) ^ n / (n.factorial : ℝ)))
            Filter.atTop (nhds 0) := by
        simpa using (tendsto_const_nhds.mul (gap9 x hx))
      have hsecond :
          Filter.Tendsto
            (fun n : ℕ =>
              (|x| / (n + 1)) * ((|x| ^ 2) ^ n / (n.factorial : ℝ)))
            Filter.atTop (nhds 0) := by
        refine tendsto_zero_of_abs_le_nonneg hscaled ?_ ?_
        · intro n
          positivity
        · intro n
          rw [abs_of_nonneg (by positivity)]
          apply mul_le_mul_of_nonneg_right
          · apply (div_le_iff₀ (by positivity)).2
            have hnNat : 1 ≤ n + 1 := by omega
            have hn : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
              exact_mod_cast hnNat
            simpa using mul_le_mul_of_nonneg_left hn (abs_nonneg x)
          · positivity
      have hd :
          Filter.Tendsto (decomposedBound x) Filter.atTop (nhds 0) := by
        unfold decomposedBound
        simpa using
          (tendsto_const_nhds.mul ((gap8 x hx).sub hsecond))
      rw [show bound x = decomposedBound x from
        funext (fun n => gap7 x n hx)]
      exact hd
  refine tendsto_zero_of_abs_le_nonneg hb ?_ ?_
  · intro n
    unfold bound geometric
    positivity
  · intro n
    exact gap3 x n

end

end ProofGap.Exercise628
