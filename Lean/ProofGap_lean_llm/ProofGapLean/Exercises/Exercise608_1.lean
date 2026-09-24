import ProofGapLean.Prelude.Sequences
import ProofGapLean.Prelude.Finite
import ProofGapLean.Prelude.Elementary
import ProofGapLean.Prelude.Discrete
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Lean.Elab.Tactic.Omega

namespace ProofGap.Exercise608_1

noncomputable section

def difference (f : ℝ → ℝ) (x : ℝ) : ℝ := f (x + 1) - f x
def normalized (f : ℝ → ℝ) (x : ℝ) : ℝ := f x / x
def τ (x X₀ : ℝ) (n : ℕ) : ℝ := x - X₀ - n
def errorSum (f : ℝ → ℝ) (A X₀ t : ℝ) (n : ℕ) : ℝ :=
  (Finset.Icc 1 n).sum (fun k =>
    f (X₀ + t + k) - f (X₀ + t + k - 1) - A)

/-- Exercise 608_1, gap 1; remove shadowed witnesses. -/
private theorem telescoping_error_sum (f : ℝ → ℝ) (A X₀ t : ℝ) (n : ℕ) :
    (Finset.Icc 1 n).sum (fun k =>
      f (X₀ + t + k) - f (X₀ + t + k - 1) - A) =
      f (X₀ + t + n) - f (X₀ + t) - (n : ℝ) * A := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hnot : n + 1 ∉ Finset.Icc 1 n := by
        simp
      have hset :
          Finset.Icc 1 (n + 1) = insert (n + 1) (Finset.Icc 1 n) := by
        ext k
        simp only [Finset.mem_Icc, Finset.mem_insert]
        omega
      rw [hset, Finset.sum_insert hnot, ih]
      simp only [Nat.cast_succ]
      have harg :
          X₀ + t + ((n : ℝ) + 1) - 1 = X₀ + t + (n : ℝ) := by
        ring
      rw [harg]
      ring

theorem gap1 (f : ℝ → ℝ) (A a : ℝ)
    (hlim : Filter.Tendsto (difference f) Filter.atTop (nhds A)) :
    ∀ ε > 0, ∃ X₀ > a, ∀ x ≥ X₀,
      |difference f x - A| < ε / 3 := by
  intro ε hε
  have hball : Metric.ball A (ε / 3) ∈ nhds A :=
    Metric.ball_mem_nhds A (by linarith)
  have hev : ∀ᶠ x in Filter.atTop, difference f x ∈ Metric.ball A (ε / 3) :=
    hlim.eventually hball
  rcases Filter.eventually_atTop.1 hev with ⟨b, hb⟩
  refine ⟨max b (a + 1), by linarith [le_max_right b (a + 1)], ?_⟩
  intro x hx
  have hbx : b ≤ x := le_trans (le_max_left b (a + 1)) hx
  simpa [Metric.mem_ball, Real.dist_eq] using hb x hbx

/-- Exercise 608_1, gap 2. -/
theorem gap2 (x X₀ ε : ℝ) (hε : 0 < ε) (hx : X₀ + 1 < x) :
    ∃ n : ℕ, 1 ≤ n ∧ (n : ℝ) ≤ x - X₀ ∧ x - X₀ < n + 1 := by
  let n : ℕ := ⌊x - X₀⌋₊
  have hy0 : 0 ≤ x - X₀ := by linarith
  have hnle : (n : ℝ) ≤ x - X₀ := by
    dsimp [n]
    exact Nat.floor_le hy0
  have hylt : x - X₀ < (n : ℝ) + 1 := by
    dsimp [n]
    exact Nat.lt_floor_add_one _
  have hn1 : 1 ≤ n := by
    apply Nat.one_le_iff_ne_zero.mpr
    intro hn0
    rw [hn0] at hylt
    norm_num at hylt
    linarith
  exact ⟨n, hn1, hnle, hylt⟩

/-- Exercise 608_1, gap 3; define `τ=x-X₀-n`. -/
theorem gap3 (x X₀ : ℝ) (n : ℕ) (hn : (n : ℝ) ≤ x - X₀) :
    0 ≤ τ x X₀ n := by
  dsimp [τ]
  linarith

/-- Exercise 608_1, gap 4; define `τ=x-X₀-n`. -/
theorem gap4 (x X₀ : ℝ) (n : ℕ) (hn : x - X₀ < n + 1) :
    τ x X₀ n < 1 := by
  dsimp [τ]
  linarith

/-- Exercise 608_1, gap 5; bind the integer witness. -/
theorem gap5 (x X₀ : ℝ) (n : ℕ) :
    x = X₀ + τ x X₀ n + n := by
  dsimp [τ]
  ring

/-- Exercise 608_1, gap 6; bind `n,τ` and the nonzero denominators. -/
theorem gap6 (f : ℝ → ℝ) (A x X₀ t : ℝ) (n : ℕ)
    (hx : x = X₀ + t + n) (hxn : x ≠ 0) (hn : n ≠ 0) :
    normalized f x - A =
      (n / x) * ((f x - f (X₀ + t)) / n - A) +
        f (X₀ + t) / x - (X₀ + t) * A / x := by
  unfold normalized
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have hx' : X₀ + t + (n : ℝ) ≠ 0 := by
    rw [← hx]
    exact hxn
  rw [hx]
  field_simp [hn', hx'] <;> ring

/-- Exercise 608_1, gap 7; add the missing size premise for `n/x≤1`. -/
theorem gap7 (f : ℝ → ℝ) (A x X₀ t : ℝ) (n : ℕ)
    (hx : x = X₀ + t + n) (hxpos : 0 < x)
    (hbase : 0 ≤ X₀ + t) :
    |(n / x) * ((f x - f (X₀ + t)) / n - A)| ≤
      |(f (X₀ + t + n) - f (X₀ + t)) / n - A| := by
  have hnnonneg : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hnle : (n : ℝ) ≤ x := by
    rw [hx]
    linarith [hnnonneg]
  have hratio0 : 0 ≤ (n : ℝ) / x :=
    div_nonneg hnnonneg (le_of_lt hxpos)
  have hratio_le : (n : ℝ) / x ≤ x / x :=
    div_le_div_of_nonneg_right hnle (le_of_lt hxpos)
  have hratio : |(n : ℝ) / x| ≤ (1 : ℝ) := by
    rw [abs_of_nonneg hratio0]
    simpa [ne_of_gt hxpos] using hratio_le
  have herrnonneg :
      0 ≤ |(f x - f (X₀ + t)) / (n : ℝ) - A| := abs_nonneg _
  calc
    |(n / x) * ((f x - f (X₀ + t)) / n - A)| =
        |(n : ℝ) / x| * |(f x - f (X₀ + t)) / n - A| := abs_mul _ _
    _ ≤ (1 : ℝ) * |(f x - f (X₀ + t)) / n - A| :=
      mul_le_mul_of_nonneg_right hratio herrnonneg
    _ = |(f (X₀ + t + n) - f (X₀ + t)) / n - A| := by
      simp only [one_mul]
      rw [hx]

/-- Exercise 608_1, gap 8; replace the ellipsis by `errorSum`. -/
theorem gap8 (f : ℝ → ℝ) (A X₀ t : ℝ) (n : ℕ) (hn : n ≠ 0) :
    |(f (X₀ + t + n) - f (X₀ + t)) / n - A| =
      (1 / n) * |errorSum f A X₀ t n| := by
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have hnpos : 0 < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  rw [errorSum, telescoping_error_sum]
  have hrearrange :
      (f (X₀ + t + n) - f (X₀ + t)) / (n : ℝ) - A =
        (f (X₀ + t + n) - f (X₀ + t) - (n : ℝ) * A) / (n : ℝ) := by
    field_simp [hn'] <;> ring
  rw [hrearrange, abs_div, abs_of_pos hnpos]
  field_simp [hn'] <;> ring

/-- Exercise 608_1, gap 9; replace both ellipses by finite sums. -/
theorem gap9 (f : ℝ → ℝ) (A X₀ t : ℝ) (n : ℕ) :
    (1 / (n : ℝ)) * |errorSum f A X₀ t n| ≤
      (1 / n) * (Finset.Icc 1 n).sum (fun k =>
        |f (X₀ + t + k) - f (X₀ + t + k - 1) - A|) := by
  have htri :
      |errorSum f A X₀ t n| ≤
        (Finset.Icc 1 n).sum (fun k =>
          |f (X₀ + t + k) - f (X₀ + t + k - 1) - A|) := by
    unfold errorSum
    classical
    induction (Finset.Icc 1 n) using Finset.induction_on with
    | empty => simp
    | @insert k s hk ih =>
        rw [Finset.sum_insert hk, Finset.sum_insert hk]
        refine le_trans (abs_add_le _ _) ?_
        linarith
  have hcoef : (0 : ℝ) ≤ 1 / (n : ℝ) :=
    div_nonneg zero_le_one (Nat.cast_nonneg n)
  have hdiff :
      (0 : ℝ) ≤
        (Finset.Icc 1 n).sum (fun k =>
          |f (X₀ + t + k) - f (X₀ + t + k - 1) - A|) -
        |errorSum f A X₀ t n| :=
    sub_nonneg.mpr htri
  have hprod :
      (0 : ℝ) ≤ (1 / (n : ℝ)) *
        ((Finset.Icc 1 n).sum (fun k =>
          |f (X₀ + t + k) - f (X₀ + t + k - 1) - A|) -
        |errorSum f A X₀ t n|) :=
    mul_nonneg hcoef hdiff
  nlinarith

/-- Exercise 608_1, gap 10; bind the tail estimate. -/
theorem gap10 (f : ℝ → ℝ) (A X₀ t ε : ℝ) (n : ℕ)
    (hn : 0 < n)
    (hterm : ∀ k ∈ Finset.Icc 1 n,
      |f (X₀ + t + k) - f (X₀ + t + k - 1) - A| < ε / 3) :
    (1 / (n : ℝ)) * (Finset.Icc 1 n).sum (fun k =>
      |f (X₀ + t + k) - f (X₀ + t + k - 1) - A|) < ε / 3 := by
  have h1 : 1 ∈ Finset.Icc 1 n := by
    simp only [Finset.mem_Icc]
    exact ⟨le_rfl, Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hn)⟩
  have hsum :
      (Finset.Icc 1 n).sum (fun k =>
        |f (X₀ + t + k) - f (X₀ + t + k - 1) - A|) <
      (Finset.Icc 1 n).sum (fun _ : ℕ => ε / 3) := by
    apply Finset.sum_lt_sum
    · intro k hk
      exact le_of_lt (hterm k hk)
    · exact ⟨1, h1, hterm 1 h1⟩
  have hsum' :
      (Finset.Icc 1 n).sum (fun k =>
        |f (X₀ + t + k) - f (X₀ + t + k - 1) - A|) <
      (n : ℝ) * (ε / 3) := by
    simpa [Nat.card_Icc, nsmul_eq_mul] using hsum
  have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  calc
    (1 / (n : ℝ)) * (Finset.Icc 1 n).sum (fun k =>
        |f (X₀ + t + k) - f (X₀ + t + k - 1) - A|) <
      (1 / (n : ℝ)) * ((n : ℝ) * (ε / 3)) :=
        mul_lt_mul_of_pos_left hsum' (one_div_pos.mpr hnR)
    _ = ε / 3 := by
      field_simp [ne_of_gt hnR] <;> ring

/-- Exercise 608_1, gap 11. -/
theorem gap11 (f : ℝ → ℝ) (A X₀ t ε : ℝ) (n : ℕ)
    (hbound : (1 / (n : ℝ)) * (Finset.Icc 1 n).sum (fun k =>
      |f (X₀ + t + k) - f (X₀ + t + k - 1) - A|) < ε / 3) :
    (1 / (n : ℝ)) * |errorSum f A X₀ t n| < ε / 3 := by
  exact lt_of_le_of_lt (gap9 f A X₀ t n) hbound

/-- Exercise 608_1, gap 12; bind a fixed `τ∈[0,1]`. -/
theorem gap12 (f : ℝ → ℝ) (X₀ t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    Filter.Tendsto (fun x : ℝ => f (X₀ + t) / x)
      Filter.atTop (nhds 0) := by
  have hinv : Filter.Tendsto (fun x : ℝ => x⁻¹)
      Filter.atTop (nhds 0) := tendsto_inv_atTop_zero
  have hc : Filter.Tendsto (fun _ : ℝ => f (X₀ + t))
      Filter.atTop (nhds (f (X₀ + t))) := tendsto_const_nhds
  simpa [div_eq_mul_inv] using hc.mul hinv

/-- Exercise 608_1, gap 13. -/
theorem gap13 (A X₀ : ℝ) :
    Filter.Tendsto (fun x : ℝ => (X₀ + 1) * A / x)
      Filter.atTop (nhds 0) := by
  have hinv : Filter.Tendsto (fun x : ℝ => x⁻¹)
      Filter.atTop (nhds 0) := tendsto_inv_atTop_zero
  have hc : Filter.Tendsto (fun _ : ℝ => (X₀ + 1) * A)
      Filter.atTop (nhds ((X₀ + 1) * A)) := tendsto_const_nhds
  simpa [div_eq_mul_inv] using hc.mul hinv

/-- Exercise 608_1, gap 14; replace the reversed `∀x∃X` quantifiers by an eventual estimate. -/
theorem gap14 (f : ℝ → ℝ) (A ε : ℝ)
    (h₁ : ∀ᶠ x in Filter.atTop, |normalized f x - A| < ε / 3 + ε / 3 + ε / 3) :
    ∀ᶠ x in Filter.atTop, |normalized f x - A| < ε / 3 + ε / 3 + ε / 3 := by
  exact h₁

/-- Exercise 608_1, gap 15; remove irrelevant shadowed `x,X`. -/
theorem gap15 (ε : ℝ) : ε / 3 + ε / 3 + ε / 3 = ε := by
  ring

/-- Exercise 608_1, gap 16; state the eventual epsilon estimate. -/
theorem gap16 (f : ℝ → ℝ) (A : ℝ)
    (h : ∀ ε > 0, ∀ᶠ x in Filter.atTop,
      |normalized f x - A| < ε / 3 + ε / 3 + ε / 3) :
    ∀ ε > 0, ∀ᶠ x in Filter.atTop, |normalized f x - A| < ε := by
  intro ε hε
  simpa [gap15] using h ε hε

/-- Exercise 608_1, gap 17; corrected Stolz-type conclusion. -/
theorem gap17 (f : ℝ → ℝ) (A : ℝ)
    (hlocal : ∀ a b : ℝ, a < b → ∃ M, ∀ x, a < x → x < b → |f x| ≤ M)
    (hdiff : Filter.Tendsto (difference f) Filter.atTop (nhds A)) :
    Filter.Tendsto (normalized f) Filter.atTop (nhds A) := by
  apply Metric.tendsto_atTop.2
  intro ε hε
  rcases gap1 f A 1 hdiff ε hε with ⟨X₀, hX₀, htail⟩
  rcases hlocal (X₀ - 1) (X₀ + 2) (by linarith) with ⟨M, hM⟩
  have hMnonneg : 0 ≤ M := by
    have hMX₀ : |f X₀| ≤ M := hM X₀ (by linarith) (by linarith)
    exact le_trans (abs_nonneg _) hMX₀
  have hMlim : Filter.Tendsto (fun y : ℝ => M / y)
      Filter.atTop (nhds 0) := by
    simpa using
      (gap12 (fun _ : ℝ => M) 0 0 (by norm_num) (by norm_num))
  rcases (Metric.tendsto_atTop.1 hMlim) (ε / 3) (by linarith) with
    ⟨BM, hBM⟩
  let C : ℝ := (|X₀| + 1) * |A|
  have hCnonneg : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg (by linarith [abs_nonneg X₀]) (abs_nonneg A)
  have hClim : Filter.Tendsto (fun y : ℝ => C / y)
      Filter.atTop (nhds 0) := by
    simpa using
      (gap12 (fun _ : ℝ => C) 0 0 (by norm_num) (by norm_num))
  rcases (Metric.tendsto_atTop.1 hClim) (ε / 3) (by linarith) with
    ⟨BC, hBC⟩
  refine ⟨max (X₀ + 2) (max BM BC), ?_⟩
  intro x hx
  have hxlarge : X₀ + 2 ≤ x :=
    le_trans (le_max_left (X₀ + 2) (max BM BC)) hx
  have hxBM : BM ≤ x := by
    exact le_trans
      (le_trans (le_max_left BM BC) (le_max_right (X₀ + 2) (max BM BC))) hx
  have hxBC : BC ≤ x := by
    exact le_trans
      (le_trans (le_max_right BM BC) (le_max_right (X₀ + 2) (max BM BC))) hx
  have hxpos : 0 < x := by linarith
  have hxstep : X₀ + 1 < x := by linarith
  have hMxRaw : |M| / |x| < ε / 3 := by
    simpa only [Real.dist_eq, sub_zero, abs_div] using hBM x hxBM
  have hMx : |M / x| < ε / 3 := by
    rw [abs_div]
    exact hMxRaw
  have hCxRaw : |C| / |x| < ε / 3 := by
    simpa only [Real.dist_eq, sub_zero, abs_div] using hBC x hxBC
  have hCx : |C / x| < ε / 3 := by
    rw [abs_div]
    exact hCxRaw
  rcases gap2 x X₀ ε hε hxstep with ⟨n, hn1, hnle, hnlt⟩
  have hnpos : 0 < n := lt_of_lt_of_le Nat.zero_lt_one hn1
  have hnne : n ≠ 0 := Nat.ne_of_gt hnpos
  let t : ℝ := τ x X₀ n
  have ht0 : 0 ≤ t := by
    simpa [t] using gap3 x X₀ n hnle
  have ht1 : t < 1 := by
    simpa [t] using gap4 x X₀ n hnlt
  have hxrep : x = X₀ + t + n := by
    simpa [t] using gap5 x X₀ n
  have hbase0 : 0 ≤ X₀ + t := by linarith
  have hterm : ∀ k ∈ Finset.Icc 1 n,
      |f (X₀ + t + k) - f (X₀ + t + k - 1) - A| < ε / 3 := by
    intro k hk
    have hkBounds : 1 ≤ k ∧ k ≤ n := by
      simpa only [Finset.mem_Icc] using hk
    have hkRcast : ((1 : ℕ) : ℝ) ≤ (k : ℝ) :=
      Nat.cast_le.mpr hkBounds.1
    have hkR : (1 : ℝ) ≤ (k : ℝ) := by
      simpa only [Nat.cast_one] using hkRcast
    have hy : X₀ ≤ X₀ + t + (k : ℝ) - 1 := by linarith
    have hkTail := htail (X₀ + t + (k : ℝ) - 1) hy
    unfold difference at hkTail
    convert hkTail using 1 <;> ring
  have havg := gap10 f A X₀ t ε n hnpos hterm
  have herr := gap11 f A X₀ t ε n havg
  have htel :
      |(f (X₀ + t + n) - f (X₀ + t)) / n - A| < ε / 3 := by
    rw [gap8 f A X₀ t n hnne]
    exact herr
  have hfirst :
      |(n / x) * ((f x - f (X₀ + t)) / n - A)| < ε / 3 :=
    lt_of_le_of_lt (gap7 f A x X₀ t n hxrep hxpos hbase0) htel
  have hfbase : |f (X₀ + t)| ≤ M := by
    apply hM (X₀ + t)
    · linarith
    · linarith
  have hfdiv : |f (X₀ + t) / x| < ε / 3 := by
    calc
      |f (X₀ + t) / x| = |f (X₀ + t)| / |x| := abs_div _ _
      _ = |f (X₀ + t)| / x := by rw [abs_of_pos hxpos]
      _ ≤ M / x := div_le_div_of_nonneg_right hfbase (le_of_lt hxpos)
      _ = |M / x| := by
        rw [abs_div, abs_of_nonneg hMnonneg, abs_of_pos hxpos]
      _ < ε / 3 := hMx
  have hbaseabs : |X₀ + t| ≤ |X₀| + 1 := by
    have hsumabs : |X₀ + t| ≤ |X₀| + |t| := by
      apply abs_le.2
      constructor
      · have hXlower : -|X₀| ≤ X₀ := neg_abs_le X₀
        have htlower : -|t| ≤ t := neg_abs_le t
        linarith
      · have hXupper : X₀ ≤ |X₀| := le_abs_self X₀
        have htupper : t ≤ |t| := le_abs_self t
        linarith
    calc
      |X₀ + t| ≤ |X₀| + |t| := hsumabs
      _ = |X₀| + t := by rw [abs_of_nonneg ht0]
      _ ≤ |X₀| + 1 := by linarith
  have hbprod : |(X₀ + t) * A| ≤ C := by
    dsimp [C]
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right hbaseabs (abs_nonneg A)
  have hbdiv : |(X₀ + t) * A / x| < ε / 3 := by
    calc
      |(X₀ + t) * A / x| = |(X₀ + t) * A| / |x| := abs_div _ _
      _ = |(X₀ + t) * A| / x := by rw [abs_of_pos hxpos]
      _ ≤ C / x := div_le_div_of_nonneg_right hbprod (le_of_lt hxpos)
      _ = |C / x| := by
        rw [abs_div, abs_of_nonneg hCnonneg, abs_of_pos hxpos]
      _ < ε / 3 := hCx
  let u : ℝ := (n / x) * ((f x - f (X₀ + t)) / n - A)
  let v : ℝ := f (X₀ + t) / x
  let w : ℝ := (X₀ + t) * A / x
  have hu : |u| < ε / 3 := by simpa [u] using hfirst
  have hv : |v| < ε / 3 := by simpa [v] using hfdiv
  have hw : |w| < ε / 3 := by simpa [w] using hbdiv
  have htri : |u + v - w| ≤ |u| + |v| + |w| := by
    apply abs_le.2
    constructor
    · have hulower : -|u| ≤ u := neg_abs_le u
      have hvlower : -|v| ≤ v := neg_abs_le v
      have hwupper : w ≤ |w| := le_abs_self w
      linarith
    · have huupper : u ≤ |u| := le_abs_self u
      have hvupper : v ≤ |v| := le_abs_self v
      have hwlower : -|w| ≤ w := neg_abs_le w
      linarith
  have hsum : |u + v - w| < ε := by
    exact lt_of_le_of_lt htri (by linarith)
  have hdecomp : normalized f x - A = u + v - w := by
    dsimp [u, v, w]
    exact gap6 f A x X₀ t n hxrep (ne_of_gt hxpos) hnne
  rw [Real.dist_eq, hdecomp]
  exact hsum

/-- Exercise 608_1, gap 18; express equality of the two limits through a common value. -/
theorem gap18 (f : ℝ → ℝ) (A : ℝ)
    (hlocal : ∀ a b : ℝ, a < b → ∃ M, ∀ x, a < x → x < b → |f x| ≤ M)
    (hdiff : Filter.Tendsto (difference f) Filter.atTop (nhds A)) :
    Filter.Tendsto (normalized f) Filter.atTop (nhds A) ∧
      Filter.Tendsto (difference f) Filter.atTop (nhds A) := by
  exact ⟨gap17 f A hlocal hdiff, hdiff⟩

end

end ProofGap.Exercise608_1
