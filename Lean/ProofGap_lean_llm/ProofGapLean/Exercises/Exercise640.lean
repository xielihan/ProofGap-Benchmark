import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

namespace ProofGap.Exercise640

noncomputable section

def Recurrence (ε m : ℝ) (x : ℕ → ℝ) : Prop :=
  x 0 = m ∧ ∀ n, x (n + 1) = m + ε * Real.sin (x n)
def geometricBlock (ε : ℝ) (i j : ℕ) : ℝ :=
  (Finset.Icc j (i - 1)).sum (fun k => ε ^ k)

/-- Exercise 640, gap 1. -/
private theorem abs_sin_le_abs_local (t : ℝ) :
    |Real.sin t| ≤ |t| := by
  exact (Real.abs_sin_le_abs : |Real.sin t| ≤ |t|)

private theorem abs_sin_sub_le (a b : ℝ) :
    |Real.sin a - Real.sin b| ≤ |a - b| := by
  rw [Real.sin_sub_sin]
  calc
    |2 * Real.sin ((a - b) / 2) * Real.cos ((a + b) / 2)| =
        2 * |Real.sin ((a - b) / 2)| * |Real.cos ((a + b) / 2)| := by
          rw [abs_mul, abs_mul]
          norm_num
    _ ≤ 2 * |Real.sin ((a - b) / 2)| * 1 :=
      mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (by positivity)
    _ = 2 * |Real.sin ((a - b) / 2)| := by ring
    _ ≤ 2 * |(a - b) / 2| :=
      mul_le_mul_of_nonneg_left (abs_sin_le_abs_local _) (by norm_num)
    _ = |a - b| := by
      rw [abs_div]
      norm_num
      ring

private theorem recurrence_diff (ε m : ℝ) (x : ℕ → ℝ) (n : ℕ)
    (hn : 1 ≤ n) (hx : Recurrence ε m x) :
    x (n + 1) - x n = ε * (Real.sin (x n) - Real.sin (x (n - 1))) := by
  rcases hx with ⟨hx0, hrec⟩
  have hprev := hrec (n - 1)
  have hidx : n - 1 + 1 = n := Nat.sub_add_cancel hn
  rw [hidx] at hprev
  rw [hrec n, hprev]
  ring

private theorem recurrence_step_le (ε m : ℝ) (x : ℕ → ℝ) (n : ℕ)
    (hε : 0 ≤ ε) (hn : 1 ≤ n) (hx : Recurrence ε m x) :
    |x (n + 1) - x n| ≤ ε * |x n - x (n - 1)| := by
  rw [recurrence_diff ε m x n hn hx, abs_mul, abs_of_nonneg hε]
  exact mul_le_mul_of_nonneg_left
    (abs_sin_sub_le (x n) (x (n - 1))) hε

private theorem sum_differences_Ico (x : ℕ → ℝ) :
    ∀ i j : ℕ, j ≤ i →
      (Finset.Ico j i).sum (fun k => x (k + 1) - x k) = x i - x j := by
  intro i
  induction i with
  | zero =>
      intro j hj
      have hj0 : j = 0 := by omega
      subst j
      simp
  | succ i ih =>
      intro j hj
      by_cases hji : j ≤ i
      · rw [Finset.sum_Ico_succ_top hji, ih j hji]
        ring
      · have hj' : j = i + 1 := by omega
        subst j
        simp

private theorem sum_powers_Ico (ε : ℝ) (hε : ε ≠ 1) :
    ∀ i j : ℕ, j ≤ i →
      (Finset.Ico j i).sum (fun k => ε ^ k) =
        ε ^ j * ((1 - ε ^ (i - j)) / (1 - ε)) := by
  have hden : 1 - ε ≠ 0 := sub_ne_zero.mpr (Ne.symm hε)
  intro i
  induction i with
  | zero =>
      intro j hj
      have hj0 : j = 0 := by omega
      subst j
      simp
  | succ i ih =>
      intro j hj
      by_cases hji : j ≤ i
      · rw [Finset.sum_Ico_succ_top hji, ih j hji]
        have he : i + 1 - j = (i - j) + 1 := by omega
        have hidx : j + (i - j) = i := by omega
        have hpow : ε ^ i = ε ^ j * ε ^ (i - j) := by
          calc
            ε ^ i = ε ^ (j + (i - j)) := by rw [hidx]
            _ = ε ^ j * ε ^ (i - j) := by rw [pow_add]
        rw [he, pow_succ, hpow]
        field_simp [hden]
        ring
      · have hj' : j = i + 1 := by omega
        subst j
        simp

theorem gap1 (ε m : ℝ) (x : ℕ → ℝ) (hx : Recurrence ε m x) :
    x 2 - x 1 = ε * (Real.sin (x 1) - Real.sin (x 0)) := by
  simpa using recurrence_diff ε m x 1 (by omega) hx

/-- Exercise 640, gap 2. -/
theorem gap2 (ε : ℝ) (x : ℕ → ℝ) :
    ε * (Real.sin (x 1) - Real.sin (x 0)) =
      2 * ε * Real.sin ((x 1 - x 0) / 2) *
        Real.cos ((x 1 + x 0) / 2) := by
  rw [Real.sin_sub_sin]
  ring

/-- Exercise 640, gap 3. -/
theorem gap3 (ε m : ℝ) (x : ℕ → ℝ) (hx : Recurrence ε m x) :
    x 2 - x 1 =
      2 * ε * Real.sin ((x 1 - x 0) / 2) *
        Real.cos ((x 1 + x 0) / 2) := by
  calc
    x 2 - x 1 = ε * (Real.sin (x 1) - Real.sin (x 0)) := gap1 ε m x hx
    _ = 2 * ε * Real.sin ((x 1 - x 0) / 2) *
        Real.cos ((x 1 + x 0) / 2) := gap2 ε x

/-- Exercise 640, gap 4. -/
theorem gap4 (ε m : ℝ) (x : ℕ → ℝ) (hε : 0 < ε)
    (hx : Recurrence ε m x) :
    |x 2 - x 1| ≤ ε * |x 1 - x 0| := by
  have h := recurrence_step_le ε m x 1 hε.le (by omega) hx
  simpa using h

/-- Exercise 640, gap 5. -/
theorem gap5 (ε m : ℝ) (x : ℕ → ℝ) (hε : 0 < ε)
    (hx : Recurrence ε m x) :
    |x 3 - x 2| ≤ ε ^ 2 * |x 1 - x 0| := by
  have hstep := recurrence_step_le ε m x 2 hε.le (by omega) hx
  have hprev := gap4 ε m x hε hx
  calc
    |x 3 - x 2| ≤ ε * |x 2 - x 1| := by simpa using hstep
    _ ≤ ε * (ε * |x 1 - x 0|) := mul_le_mul_of_nonneg_left hprev hε.le
    _ = ε ^ 2 * |x 1 - x 0| := by ring

/-- Exercise 640, gap 6; add `n≥1` before using `n-1`. -/
theorem gap6 (ε m : ℝ) (x : ℕ → ℝ) (n : ℕ) (hn : 1 ≤ n)
    (hε : 0 ≤ ε) (hx : Recurrence ε m x)
    (hind : |x n - x (n - 1)| ≤ ε ^ (n - 1) * |x 1 - x 0|) :
    |x (n + 1) - x n| =
      2 * ε * |Real.sin ((x n - x (n - 1)) / 2)| *
        |Real.cos ((x n + x (n - 1)) / 2)| := by
  rw [recurrence_diff ε m x n hn hx, abs_mul, abs_of_nonneg hε,
    Real.sin_sub_sin, abs_mul, abs_mul]
  norm_num
  ring

/-- Exercise 640, gap 7; add `n≥1`. -/
theorem gap7 (ε m : ℝ) (x : ℕ → ℝ) (n : ℕ) (hn : 1 ≤ n)
    (hε : 0 < ε) (hx : Recurrence ε m x)
    (hind : |x n - x (n - 1)| ≤ ε ^ (n - 1) * |x 1 - x 0|) :
    2 * ε * |Real.sin ((x n - x (n - 1)) / 2)| *
        |Real.cos ((x n + x (n - 1)) / 2)| ≤
      ε * |x n - x (n - 1)| := by
  have hid :
      2 * ε * |Real.sin ((x n - x (n - 1)) / 2)| *
          |Real.cos ((x n + x (n - 1)) / 2)| =
        ε * |Real.sin (x n) - Real.sin (x (n - 1))| := by
    rw [Real.sin_sub_sin, abs_mul, abs_mul]
    norm_num
    ring
  rw [hid]
  exact mul_le_mul_of_nonneg_left
    (abs_sin_sub_le (x n) (x (n - 1))) hε.le

/-- Exercise 640, gap 8; add `n≥1`. -/
theorem gap8 (ε : ℝ) (x : ℕ → ℝ) (n : ℕ) (hn : 1 ≤ n)
    (hε : 0 ≤ ε)
    (hind : |x n - x (n - 1)| ≤ ε ^ (n - 1) * |x 1 - x 0|) :
    ε * |x n - x (n - 1)| ≤ ε ^ n * |x 1 - x 0| := by
  calc
    ε * |x n - x (n - 1)|
        ≤ ε * (ε ^ (n - 1) * |x 1 - x 0|) :=
          mul_le_mul_of_nonneg_left hind hε
    _ = ε ^ ((n - 1) + 1) * |x 1 - x 0| := by
      rw [pow_succ]
      ring
    _ = ε ^ n * |x 1 - x 0| := by
      rw [Nat.sub_add_cancel hn]

/-- Exercise 640, gap 9; add `n≥1`. -/
theorem gap9 (ε m : ℝ) (x : ℕ → ℝ) (n : ℕ) (hn : 1 ≤ n)
    (hε : 0 < ε) (hx : Recurrence ε m x)
    (hind : |x n - x (n - 1)| ≤ ε ^ (n - 1) * |x 1 - x 0|) :
    |x (n + 1) - x n| ≤ ε ^ n * |x 1 - x 0| := by
  calc
    |x (n + 1) - x n| ≤ ε * |x n - x (n - 1)| :=
      recurrence_step_le ε m x n hε.le hn hx
    _ ≤ ε ^ n * |x 1 - x 0| := gap8 ε x n hn hε.le hind

/-- Exercise 640, gap 10. -/
theorem gap10 (ε m : ℝ) (x : ℕ → ℝ) (hε0 : 0 < ε) (hε1 : ε < 1)
    (hx : Recurrence ε m x) :
    ∀ n ≥ 1, |x n - x (n - 1)| ≤ ε ^ (n - 1) * |x 1 - x 0| := by
  intro n hn
  refine Nat.le_induction ?_ (fun k hk ih => ?_) n hn
  · simp
  · simpa using gap9 ε m x k hk hε0 hx ih

/-- Exercise 640, gap 11; rename the index shadowing the parameter `m` and replace the ellipsis by a finite sum. -/
theorem gap11 (ε m : ℝ) (x : ℕ → ℝ) (i j : ℕ) (hij : j < i)
    (hstep : ∀ n ≥ 1,
      |x n - x (n - 1)| ≤ ε ^ (n - 1) * |x 1 - x 0|) :
    |x i - x j| ≤ geometricBlock ε i j * |x 1 - x 0| := by
  have hset : Finset.Icc j (i - 1) = Finset.Ico j i := by
    ext k
    simp
    omega
  calc
    |x i - x j| =
        |(Finset.Ico j i).sum (fun k => x (k + 1) - x k)| := by
          rw [sum_differences_Ico x i j hij.le]
    _ ≤ (Finset.Ico j i).sum (fun k => |x (k + 1) - x k|) :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ (Finset.Ico j i).sum
        (fun k => ε ^ k * |x 1 - x 0|) := by
      apply Finset.sum_le_sum
      intro k hk
      have hk1 : 1 ≤ k + 1 := by omega
      simpa using hstep (k + 1) hk1
    _ = geometricBlock ε i j * |x 1 - x 0| := by
      unfold geometricBlock
      rw [hset, Finset.sum_mul]

/-- Exercise 640, gap 12; use renamed sequence indices. -/
theorem gap12 (ε : ℝ) (x : ℕ → ℝ) (i j : ℕ) (hij : j < i)
    (hε : ε ≠ 1)
    (hbound : |x i - x j| ≤ geometricBlock ε i j * |x 1 - x 0|) :
    |x i - x j| ≤
      ε ^ j * ((1 - ε ^ (i - j)) / (1 - ε)) * |x 1 - x 0| := by
  have hset : Finset.Icc j (i - 1) = Finset.Ico j i := by
    ext k
    simp
    omega
  have hgeom : geometricBlock ε i j =
      ε ^ j * ((1 - ε ^ (i - j)) / (1 - ε)) := by
    unfold geometricBlock
    rw [hset, sum_powers_Ico ε hε i j hij.le]
  calc
    |x i - x j| ≤ geometricBlock ε i j * |x 1 - x 0| := hbound
    _ = ε ^ j * ((1 - ε ^ (i - j)) / (1 - ε)) *
        |x 1 - x 0| := by rw [hgeom]

/-- Exercise 640, gap 13; remove irrelevant shadowing indices. -/
theorem gap13 (ε m : ℝ) (x : ℕ → ℝ) (hε : 0 ≤ ε)
    (hx : Recurrence ε m x) :
    |x 1 - x 0| = ε * |Real.sin (x 0)| := by
  rcases hx with ⟨hx0, hrec⟩
  have h1 := hrec 0
  norm_num at h1
  rw [h1, hx0]
  ring_nf
  rw [abs_mul, abs_of_nonneg hε]

/-- Exercise 640, gap 14. -/
theorem gap14 (ε : ℝ) (x : ℕ → ℝ) (hε : 0 ≤ ε) :
    ε * |Real.sin (x 0)| ≤ ε := by
  calc
    ε * |Real.sin (x 0)| ≤ ε * 1 :=
      mul_le_mul_of_nonneg_left (Real.abs_sin_le_one (x 0)) hε
    _ = ε := by ring

/-- Exercise 640, gap 15. -/
theorem gap15 (ε m : ℝ) (x : ℕ → ℝ) (hε : 0 ≤ ε)
    (hx : Recurrence ε m x) :
    |x 1 - x 0| ≤ ε := by
  rcases hx with ⟨hx0, hrec⟩
  have hdiff : x 1 - x 0 = ε * Real.sin (x 0) := by
    have h1 := hrec 0
    norm_num at h1
    rw [h1, hx0]
    ring
  rw [hdiff, abs_mul, abs_of_nonneg hε]
  exact gap14 ε x hε

/-- Exercise 640, gap 16; rename shadowing indices. -/
theorem gap16 (ε m : ℝ) (x : ℕ → ℝ) (i j : ℕ) (hij : j < i)
    (hε0 : 0 < ε) (hε1 : ε < 1) (hx : Recurrence ε m x) :
    |x i - x j| < ε ^ (j + 1) / (1 - ε) := by
  have hstep := gap10 ε m x hε0 hε1 hx
  have hblock := gap11 ε m x i j hij hstep
  have hb := gap12 ε x i j hij (ne_of_lt hε1) hblock
  have hd := gap15 ε m x hε0.le hx
  have hA : 0 < ε ^ j := pow_pos hε0 j
  have hB : 0 < ε ^ (i - j) := pow_pos hε0 (i - j)
  have hden : 0 < 1 - ε := sub_pos.mpr hε1
  have hprod :
      (1 - ε ^ (i - j)) * |x 1 - x 0| < ε := by
    by_cases hz : |x 1 - x 0| = 0
    · rw [hz]
      simpa using hε0
    · have hdpos : 0 < |x 1 - x 0| :=
        lt_of_le_of_ne (abs_nonneg _) (Ne.symm hz)
      have hmul : 0 < ε ^ (i - j) * |x 1 - x 0| :=
        mul_pos hB hdpos
      nlinarith
  calc
    |x i - x j| ≤
        ε ^ j * ((1 - ε ^ (i - j)) / (1 - ε)) *
          |x 1 - x 0| := hb
    _ = (ε ^ j * ((1 - ε ^ (i - j)) * |x 1 - x 0|)) /
        (1 - ε) := by ring
    _ < (ε ^ j * ε) / (1 - ε) :=
      (div_lt_div_iff_of_pos_right hden).2
        (mul_lt_mul_of_pos_left hprod hA)
    _ = ε ^ (j + 1) / (1 - ε) := by rw [pow_succ]

/-- Exercise 640, gap 17; bind the fixed sequence index. -/
theorem gap17 (ε m : ℝ) (x : ℕ → ℝ) (i : ℕ)
    (hε0 : 0 < ε) (hε1 : ε < 1) (hx : Recurrence ε m x) :
    Filter.Tendsto (fun n => |x (n + i + 1) - x n|)
      Filter.atTop (nhds 0) := by
  have hp0 : Filter.Tendsto (fun n : ℕ => ε ^ n)
      Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hε0.le hε1
  have hadd : Filter.Tendsto (fun n : ℕ => n + 1)
      Filter.atTop Filter.atTop := by
    refine Filter.tendsto_atTop.2 ?_
    intro b
    exact Filter.eventually_atTop.2 ⟨b, fun n hn => by omega⟩
  have hp : Filter.Tendsto
      (fun n : ℕ => ε ^ (n + 1) / (1 - ε))
      Filter.atTop (nhds 0) := by
    have ht := (hp0.comp hadd).div_const (1 - ε)
    simpa using ht
  rw [Metric.tendsto_atTop]
  intro δ hδ
  have hev : ∀ᶠ n : ℕ in Filter.atTop,
      ε ^ (n + 1) / (1 - ε) < δ :=
    (tendsto_order.1 hp).2 δ hδ
  rcases Filter.eventually_atTop.1 hev with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn
  have hb := gap16 ε m x (n + i + 1) n (by omega) hε0 hε1 hx
  simpa [Real.dist_eq] using lt_trans hb (hN n hn)

/-- Exercise 640, gap 18. -/
theorem gap18 (ε m : ℝ) (x : ℕ → ℝ)
    (hε0 : 0 < ε) (hε1 : ε < 1) (hx : Recurrence ε m x) :
    ∃ ξ, Filter.Tendsto x Filter.atTop (nhds ξ) := by
  have hadd : Filter.Tendsto (fun n : ℕ => n + 1)
      Filter.atTop Filter.atTop := by
    refine Filter.tendsto_atTop.2 ?_
    intro b
    exact Filter.eventually_atTop.2 ⟨b, fun n hn => by omega⟩
  have hp0 : Filter.Tendsto (fun n : ℕ => ε ^ n)
      Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hε0.le hε1
  have hp : Filter.Tendsto
      (fun n : ℕ => ε ^ (n + 1) / (1 - ε))
      Filter.atTop (nhds 0) := by
    have ht := (hp0.comp hadd).div_const (1 - ε)
    simpa using ht
  have hc : CauchySeq x := by
    rw [Metric.cauchySeq_iff]
    intro δ hδ
    have hev : ∀ᶠ n : ℕ in Filter.atTop,
        ε ^ (n + 1) / (1 - ε) < δ :=
      (tendsto_order.1 hp).2 δ hδ
    rcases Filter.eventually_atTop.1 hev with ⟨N, hN⟩
    refine ⟨N, ?_⟩
    intro i hi j hj
    rcases lt_trichotomy i j with hij | hij | hij
    · have hb := gap16 ε m x j i hij hε0 hε1 hx
      have ht := hN i hi
      simpa [Real.dist_eq, abs_sub_comm] using lt_trans hb ht
    · subst j
      simp [hδ]
    · have hb := gap16 ε m x i j hij hε0 hε1 hx
      have ht := hN j hj
      simpa [Real.dist_eq] using lt_trans hb ht
  exact cauchySeq_tendsto_of_complete hc

/-- Exercise 640, gap 19. -/
theorem gap19 (ε m : ℝ) (x : ℕ → ℝ)
    (hx : Recurrence ε m x)
    (hconv : ∃ ξ, Filter.Tendsto x Filter.atTop (nhds ξ)) :
    ∃ ξ, ξ = m + ε * Real.sin ξ := by
  rcases hconv with ⟨ξ, hlim⟩
  rcases hx with ⟨hx0, hrec⟩
  have hadd : Filter.Tendsto (fun n : ℕ => n + 1)
      Filter.atTop Filter.atTop := by
    refine Filter.tendsto_atTop.2 ?_
    intro b
    exact Filter.eventually_atTop.2 ⟨b, fun n hn => by omega⟩
  have hshift : Filter.Tendsto (fun n => x (n + 1))
      Filter.atTop (nhds ξ) := hlim.comp hadd
  have hsin : Filter.Tendsto (fun n => Real.sin (x n))
      Filter.atTop (nhds (Real.sin ξ)) :=
    Real.continuous_sin.continuousAt.tendsto.comp hlim
  have hrhs : Filter.Tendsto
      (fun n => m + ε * Real.sin (x n)) Filter.atTop
      (nhds (m + ε * Real.sin ξ)) :=
    tendsto_const_nhds.add (tendsto_const_nhds.mul hsin)
  have heq : (fun n => x (n + 1)) =
      (fun n => m + ε * Real.sin (x n)) := funext hrec
  rw [heq] at hshift
  exact ⟨ξ, tendsto_nhds_unique hshift hrhs⟩

/-- Exercise 640, gap 20. -/
theorem gap20 (ε m : ℝ) (x : ℕ → ℝ)
    (hx : Recurrence ε m x)
    (hconv : ∃ ξ, Filter.Tendsto x Filter.atTop (nhds ξ)) :
    ∃ ξ, ξ - ε * Real.sin ξ = m := by
  rcases gap19 ε m x hx hconv with ⟨ξ, hξ⟩
  refine ⟨ξ, ?_⟩
  linarith

/-- Exercise 640, gap 21; bind the selected fixed point. -/
theorem gap21 (ε m ξ : ℝ) (hξ : ξ - ε * Real.sin ξ = m) :
    ∀ ξ₁, ξ₁ - ε * Real.sin ξ₁ = m →
      ξ₁ - ξ = ε * (Real.sin ξ₁ - Real.sin ξ) := by
  intro ξ₁ hξ₁
  linarith

/-- Exercise 640, gap 22. -/
theorem gap22 (ε m ξ : ℝ) (hε : 0 ≤ ε)
    (hξ : ξ - ε * Real.sin ξ = m) :
    ∀ ξ₁, ξ₁ - ε * Real.sin ξ₁ = m →
      |ξ₁ - ξ| ≤ ε * |ξ₁ - ξ| := by
  intro ξ₁ hξ₁
  have heq := gap21 ε m ξ hξ ξ₁ hξ₁
  calc
    |ξ₁ - ξ| = |ε * (Real.sin ξ₁ - Real.sin ξ)| := by rw [heq]
    _ = ε * |Real.sin ξ₁ - Real.sin ξ| := by
      rw [abs_mul, abs_of_nonneg hε]
    _ ≤ ε * |ξ₁ - ξ| :=
      mul_le_mul_of_nonneg_left (abs_sin_sub_le ξ₁ ξ) hε

/-- Exercise 640, gap 23. -/
theorem gap23 (ε m ξ : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε < 1)
    (hξ : ξ - ε * Real.sin ξ = m) :
    ∀ ξ₁, ξ₁ - ε * Real.sin ξ₁ = m → ξ₁ = ξ := by
  intro ξ₁ hξ₁
  have hb := gap22 ε m ξ hε0 hξ ξ₁ hξ₁
  have hz : |ξ₁ - ξ| = 0 := by
    have ha : 0 ≤ |ξ₁ - ξ| := abs_nonneg _
    nlinarith
  exact sub_eq_zero.mp (abs_eq_zero.mp hz)

/-- Exercise 640, gap 24. -/
theorem gap24 (ε m : ℝ) (x : ℕ → ℝ)
    (hε0 : 0 < ε) (hε1 : ε < 1) (hx : Recurrence ε m x) :
    ∃ ξ, Filter.Tendsto x Filter.atTop (nhds ξ) ∧
      ξ - ε * Real.sin ξ = m ∧
      ∀ ξ₁, ξ₁ - ε * Real.sin ξ₁ = m → ξ₁ = ξ := by
  rcases gap18 ε m x hε0 hε1 hx with ⟨ξ, hlim⟩
  rcases hx with ⟨hx0, hrec⟩
  have hadd : Filter.Tendsto (fun n : ℕ => n + 1)
      Filter.atTop Filter.atTop := by
    refine Filter.tendsto_atTop.2 ?_
    intro b
    exact Filter.eventually_atTop.2 ⟨b, fun n hn => by omega⟩
  have hshift : Filter.Tendsto (fun n => x (n + 1))
      Filter.atTop (nhds ξ) := hlim.comp hadd
  have hsin : Filter.Tendsto (fun n => Real.sin (x n))
      Filter.atTop (nhds (Real.sin ξ)) :=
    Real.continuous_sin.continuousAt.tendsto.comp hlim
  have hrhs : Filter.Tendsto
      (fun n => m + ε * Real.sin (x n)) Filter.atTop
      (nhds (m + ε * Real.sin ξ)) :=
    tendsto_const_nhds.add (tendsto_const_nhds.mul hsin)
  have heq : (fun n => x (n + 1)) =
      (fun n => m + ε * Real.sin (x n)) := funext hrec
  rw [heq] at hshift
  have hfix : ξ = m + ε * Real.sin ξ :=
    tendsto_nhds_unique hshift hrhs
  have hξ : ξ - ε * Real.sin ξ = m := by linarith
  exact ⟨ξ, hlim, hξ, gap23 ε m ξ hε0.le hε1 hξ⟩

end

end ProofGap.Exercise640
