import ProofGapLean.Prelude.Sequences

open Filter Topology

namespace ProofGap.Exercise143

noncomputable section

def ratioIncrement (x y : ℕ → ℝ) (n : ℕ) : ℝ :=
  (x (n + 1) - x n) / (y (n + 1) - y n)

def ratioTerm (x y : ℕ → ℝ) (n : ℕ) : ℝ := x n / y n

def Increasing (y : ℕ → ℝ) : Prop := StrictMono y

/-- Source: `proof_gap/exercise_143/1.txt`; both cutoffs depend on ε. -/
theorem gap1 (x y : ℕ → ℝ) (a : ℝ)
    (hy : Increasing y) (hyInf : Tendsto y atTop atTop)
    (hΔ : Tendsto (ratioIncrement x y) atTop (𝓝 a)) :
    ∀ ε > 0, ∃ N : ℕ, 0 < N ∧ ∀ n > N,
      |ratioIncrement x y n - a| < ε / 2 ∧ 0 < y n := by
  intro ε hε
  have hhalf : 0 < ε / 2 := by linarith
  rcases (Metric.tendsto_atTop.1 hΔ) (ε / 2) hhalf with ⟨K₁, hK₁⟩
  have hypos : ∀ᶠ n : ℕ in atTop, 0 < y n :=
    hyInf (Ioi_mem_atTop 0)
  rw [eventually_atTop] at hypos
  rcases hypos with ⟨K₂, hK₂⟩
  refine ⟨max K₁ K₂ + 1, by omega, fun n hn => ?_⟩
  constructor
  · simpa [Real.dist_eq] using hK₁ n (by omega)
  · exact hK₂ n (by omega)

/-- Source: `proof_gap/exercise_143/2.txt`; replace the fixed-N quantifier error by a tail statement. -/
theorem gap2 (x y : ℕ → ℝ) (a : ℝ)
    (hΔ : Tendsto (ratioIncrement x y) atTop (𝓝 a)) :
    ∀ ε > 0, ∃ N, ∀ n > N,
      ratioIncrement x y n ∈ Set.Ioo (a - ε / 2) (a + ε / 2) := by
  intro ε hε
  have hhalf : 0 < ε / 2 := by linarith
  rcases (Metric.tendsto_atTop.1 hΔ) (ε / 2) hhalf with ⟨N, hN⟩
  refine ⟨N, fun n hn => ?_⟩
  have habs : |ratioIncrement x y n - a| < ε / 2 := by
    simpa [Real.dist_eq] using hN n hn.le
  rw [abs_lt] at habs
  constructor <;> linarith

/-- Source: `proof_gap/exercise_143/3.txt`. -/
theorem gap3 (x y : ℕ → ℝ) (a : ℝ)
    (hΔ : Tendsto (ratioIncrement x y) atTop (𝓝 a)) :
    ∀ ε > 0, ∃ N, ratioIncrement x y (N + 2) ∈
      Set.Ioo (a - ε / 2) (a + ε / 2) := by
  intro ε hε
  rcases gap2 x y a hΔ ε hε with ⟨N, hN⟩
  exact ⟨N, hN (N + 2) (by omega)⟩

/-- Source: `proof_gap/exercise_143/4.txt`; the source ellipsis denotes all intermediate increments. -/
theorem gap4 (x y : ℕ → ℝ) (a : ℝ)
    (hΔ : Tendsto (ratioIncrement x y) atTop (𝓝 a)) :
    ∀ ε > 0, ∃ N, ∀ k ≥ N,
      ratioIncrement x y k ∈ Set.Ioo (a - ε / 2) (a + ε / 2) := by
  intro ε hε
  rcases gap2 x y a hΔ ε hε with ⟨N, hN⟩
  exact ⟨N + 1, fun k hk => hN k (by omega)⟩

/-- Source: `proof_gap/exercise_143/5.txt`. -/
theorem gap5 (x y : ℕ → ℝ) (a : ℝ)
    (hΔ : Tendsto (ratioIncrement x y) atTop (𝓝 a)) :
    ∀ ε > 0, ∃ N, ∀ n > N,
      ratioIncrement x y n ∈ Set.Ioo (a - ε / 2) (a + ε / 2) := by
  exact gap2 x y a hΔ

/-- Source: `proof_gap/exercise_143/6.txt`; N is chosen after ε. -/
theorem gap6 (x y : ℕ → ℝ) (a : ℝ) (hy : Increasing y)
    (hΔ : Tendsto (ratioIncrement x y) atTop (𝓝 a)) :
    ∀ ε > 0, ∃ N, ∀ n > N,
      (a - ε / 2) * (y (n + 1) - y n) < x (n + 1) - x n := by
  intro ε hε
  rcases gap2 x y a hΔ ε hε with ⟨N, hN⟩
  refine ⟨N, fun n hn => ?_⟩
  have hpos : 0 < y (n + 1) - y n := sub_pos.mpr (hy (by omega))
  have hlo := (hN n hn).1
  exact (lt_div_iff₀ hpos).mp (by simpa [ratioIncrement] using hlo)

/-- Source: `proof_gap/exercise_143/7.txt`. -/
theorem gap7 (x y : ℕ → ℝ) (a : ℝ) (hy : Increasing y)
    (hΔ : Tendsto (ratioIncrement x y) atTop (𝓝 a)) :
    ∀ ε > 0, ∃ N, ∀ n > N,
      x (n + 1) - x n < (a + ε / 2) * (y (n + 1) - y n) := by
  intro ε hε
  rcases gap2 x y a hΔ ε hε with ⟨N, hN⟩
  refine ⟨N, fun n hn => ?_⟩
  have hpos : 0 < y (n + 1) - y n := sub_pos.mpr (hy (by omega))
  have hhi := (hN n hn).2
  rw [ratioIncrement, div_lt_iff₀ hpos] at hhi
  exact hhi

/-- Source: `proof_gap/exercise_143/8.txt`. -/
theorem gap8 (y : ℕ → ℝ) (a : ℝ) (hy : Increasing y) :
    ∀ ε > 0, ∀ n,
      (a - ε / 2) * (y (n + 1) - y n) <
        (a + ε / 2) * (y (n + 1) - y n) := by
  intro ε hε n
  have hpos : 0 < y (n + 1) - y n := sub_pos.mpr (hy (by omega))
  exact mul_lt_mul_of_pos_right (by linarith) hpos

/-- Source: `proof_gap/exercise_143/9.txt`. -/
theorem gap9 (x y : ℕ → ℝ) (a : ℝ) (hy : Increasing y)
    (hΔ : Tendsto (ratioIncrement x y) atTop (𝓝 a)) :
    ∀ ε > 0, ∃ N, ∀ n > N,
      (a - ε / 2) * (y (n + 1) - y n) < x (n + 1) - x n := by
  exact gap6 x y a hy hΔ

/-- Source: `proof_gap/exercise_143/10.txt`. -/
theorem gap10 (x y : ℕ → ℝ) (a : ℝ) (hy : Increasing y)
    (hΔ : Tendsto (ratioIncrement x y) atTop (𝓝 a)) :
    ∀ ε > 0, ∃ N, ∀ n > N,
      x (n + 1) - x n < (a + ε / 2) * (y (n + 1) - y n) := by
  exact gap7 x y a hy hΔ

/-- Source: `proof_gap/exercise_143/11.txt`. -/
theorem gap11 (y : ℕ → ℝ) (a : ℝ) (hy : Increasing y) :
    ∀ ε > 0, ∀ n,
      (a - ε / 2) * (y (n + 1) - y n) <
        (a + ε / 2) * (y (n + 1) - y n) := by
  exact gap8 y a hy

/-- Source: `proof_gap/exercise_143/12.txt`; the summed range is made explicit. -/
theorem gap12 (x y : ℕ → ℝ) (a : ℝ) (N n : ℕ) (hN : N < n)
    (h : ∀ k, N < k → k ≤ n →
      (a - 1) * (y (k + 1) - y k) < x (k + 1) - x k) :
    (a - 1) * (y (n + 1) - y (N + 1)) <
      x (n + 1) - x (N + 1) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases heq : n = N + 1
      · subst n
        exact h (N + 1) (by omega) (by omega)
      · have hnprev : N < n - 1 := by omega
        have ih' := ih (n - 1) (by omega) hnprev
          (fun k hkN hk => h k hkN (by omega))
        have hstep := h n hN le_rfl
        have hnpos : 0 < n := by omega
        rw [Nat.sub_add_cancel (by omega : 1 ≤ n)] at ih'
        linarith

/-- Source: `proof_gap/exercise_143/13.txt`; the summed range is made explicit. -/
theorem gap13 (x y : ℕ → ℝ) (a : ℝ) (N n : ℕ) (hN : N < n)
    (h : ∀ k, N < k → k ≤ n →
      x (k + 1) - x k < (a + 1) * (y (k + 1) - y k)) :
    x (n + 1) - x (N + 1) <
      (a + 1) * (y (n + 1) - y (N + 1)) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases heq : n = N + 1
      · subst n
        exact h (N + 1) (by omega) (by omega)
      · have hnprev : N < n - 1 := by omega
        have ih' := ih (n - 1) (by omega) hnprev
          (fun k hkN hk => h k hkN (by omega))
        have hstep := h n hN le_rfl
        rw [Nat.sub_add_cancel (by omega : 1 ≤ n)] at ih'
        linarith

/-- Source: `proof_gap/exercise_143/14.txt`. -/
theorem gap14 (y : ℕ → ℝ) (a ε : ℝ) (N n : ℕ)
    (hε : 0 < ε) (hy : Increasing y) (hN : N < n) :
    (a - ε / 2) * (y (n + 1) - y (N + 1)) <
      (a + ε / 2) * (y (n + 1) - y (N + 1)) := by
  have hypos : 0 < y (n + 1) - y (N + 1) :=
    sub_pos.mpr (hy (by omega))
  exact mul_lt_mul_of_pos_right (by linarith) hypos

/-- Source: `proof_gap/exercise_143/15.txt`; the ratio denominator is positive. -/
theorem gap15 (x y : ℕ → ℝ) (a : ℝ) (N n : ℕ)
    (hy : Increasing y) (hN : N < n)
    (hl : (a - 1) * (y (n + 1) - y (N + 1)) <
      x (n + 1) - x (N + 1))
    (hu : x (n + 1) - x (N + 1) <
      (a + 1) * (y (n + 1) - y (N + 1))) :
    |(x (n + 1) - x (N + 1)) / (y (n + 1) - y (N + 1)) - a| < 1 := by
  have hdenpos : 0 < y (n + 1) - y (N + 1) :=
    sub_pos.mpr (hy (by omega))
  rw [abs_lt]
  constructor
  · have := (lt_div_iff₀ hdenpos).2 hl
    linarith
  · have := (div_lt_iff₀ hdenpos).2 hu
    linarith

/-- Source: `proof_gap/exercise_143/16.txt`; corrected to the exact decomposition identity. -/
theorem gap16 (x y : ℕ → ℝ) (a : ℝ) (N n : ℕ)
    (hyn : y n ≠ 0) (hden : y n - y (N + 1) ≠ 0) :
    ratioTerm x y n - a =
      (x (N + 1) - a * y (N + 1)) / y n +
      (1 - y (N + 1) / y n) *
        ((x n - x (N + 1)) / (y n - y (N + 1)) - a) := by
  unfold ratioTerm
  field_simp [hyn, hden]
  ring

/-- Source: `proof_gap/exercise_143/17.txt`. -/
theorem gap17 (x y : ℕ → ℝ) (a ε : ℝ) (N n : ℕ)
    (hfactor : |1 - y (N + 1) / y n| ≤ 1)
    (htail : |(x n - x (N + 1)) / (y n - y (N + 1)) - a| < ε / 2)
    (hdecomp : ratioTerm x y n - a =
      (x (N + 1) - a * y (N + 1)) / y n +
      (1 - y (N + 1) / y n) *
        ((x n - x (N + 1)) / (y n - y (N + 1)) - a)) :
    |ratioTerm x y n - a| ≤
      |(x (N + 1) - a * y (N + 1)) / y n| + ε / 2 := by
  rw [hdecomp]
  calc
    |(x (N + 1) - a * y (N + 1)) / y n +
        (1 - y (N + 1) / y n) *
          ((x n - x (N + 1)) / (y n - y (N + 1)) - a)|
        ≤ |(x (N + 1) - a * y (N + 1)) / y n| +
          |(1 - y (N + 1) / y n) *
            ((x n - x (N + 1)) / (y n - y (N + 1)) - a)| :=
      abs_add_le _ _
    _ = |(x (N + 1) - a * y (N + 1)) / y n| +
          |1 - y (N + 1) / y n| *
            |(x n - x (N + 1)) / (y n - y (N + 1)) - a| := by
      rw [abs_mul]
    _ ≤ |(x (N + 1) - a * y (N + 1)) / y n| + ε / 2 := by
      have hmul :
          |1 - y (N + 1) / y n| *
              |(x n - x (N + 1)) / (y n - y (N + 1)) - a| ≤
            1 * (ε / 2) :=
        mul_le_mul hfactor htail.le (abs_nonneg _) (by positivity)
      linarith

/-- Source: `proof_gap/exercise_143/18.txt`; N' is chosen after ε and N. -/
theorem gap18 (x y : ℕ → ℝ) (a ε : ℝ) (N : ℕ)
    (hε : 0 < ε) (hyInf : Tendsto y atTop atTop) :
    ∃ N' > N, ∀ n > N',
      |x (N + 1) - a * y (N + 1)| / y n < ε / 2 := by
  let C := |x (N + 1) - a * y (N + 1)|
  let B := max 1 (2 * C / ε)
  have hev : ∀ᶠ n : ℕ in atTop, B < y n :=
    hyInf (Ioi_mem_atTop B)
  rw [eventually_atTop] at hev
  rcases hev with ⟨K, hK⟩
  refine ⟨max K N + 1, by omega, fun n hn => ?_⟩
  have hyB : B < y n := hK n (by omega)
  have hypos : 0 < y n := lt_of_lt_of_le (by positivity : (0 : ℝ) < 1)
    (le_max_left 1 (2 * C / ε) |>.trans hyB.le)
  have hlarge : 2 * C / ε < y n :=
    (le_max_right 1 (2 * C / ε)).trans_lt hyB
  dsimp [C] at hlarge ⊢
  rw [div_lt_iff₀ hypos]
  have hε2 : 0 < ε / 2 := by linarith
  have := (div_lt_iff₀ hε).mp hlarge
  nlinarith

private theorem telescope_lower
    (x y : ℕ → ℝ) (c : ℝ) (N n : ℕ) (hN : N < n)
    (h : ∀ k, N < k → k ≤ n →
      c * (y (k + 1) - y k) < x (k + 1) - x k) :
    c * (y (n + 1) - y (N + 1)) <
      x (n + 1) - x (N + 1) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases heq : n = N + 1
      · subst n
        exact h (N + 1) (by omega) (by omega)
      · have hnprev : N < n - 1 := by omega
        have ih' := ih (n - 1) (by omega) hnprev
          (fun k hkN hk => h k hkN (by omega))
        have hstep := h n hN le_rfl
        rw [Nat.sub_add_cancel (by omega : 1 ≤ n)] at ih'
        linarith

private theorem telescope_upper
    (x y : ℕ → ℝ) (c : ℝ) (N n : ℕ) (hN : N < n)
    (h : ∀ k, N < k → k ≤ n →
      x (k + 1) - x k < c * (y (k + 1) - y k)) :
    x (n + 1) - x (N + 1) <
      c * (y (n + 1) - y (N + 1)) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases heq : n = N + 1
      · subst n
        exact h (N + 1) (by omega) (by omega)
      · have hnprev : N < n - 1 := by omega
        have ih' := ih (n - 1) (by omega) hnprev
          (fun k hkN hk => h k hkN (by omega))
        have hstep := h n hN le_rfl
        rw [Nat.sub_add_cancel (by omega : 1 ≤ n)] at ih'
        linarith

/-- Source: `proof_gap/exercise_143/19.txt`; all cutoffs are explicitly bound. -/
theorem gap19 (x y : ℕ → ℝ) (a : ℝ)
    (h : ∀ ε > 0, ∃ N, ∀ n > N, |ratioTerm x y n - a| < ε) :
    ∀ ε > 0, ∃ N, ∀ n > N, |ratioTerm x y n - a| < ε := by
  exact h

/-- Source: `proof_gap/exercise_143/20.txt`. -/
theorem gap20 (x y : ℕ → ℝ) (a : ℝ)
    (h : ∀ ε > 0, ∃ N, ∀ n > N, |ratioTerm x y n - a| < ε) :
    Tendsto (ratioTerm x y) atTop (𝓝 a) := by
  apply Metric.tendsto_atTop.2
  intro ε hε
  rcases h ε hε with ⟨N, hN⟩
  exact ⟨N + 1, fun n hn => by
    simpa [Real.dist_eq] using hN n (by omega)⟩

/-- Source: `proof_gap/exercise_143/21.txt`. -/
theorem gap21 (x y : ℕ → ℝ) (a : ℝ)
    (h : Tendsto (ratioIncrement x y) atTop (𝓝 a)) :
    a = a := by
  rfl

/-- Source: `proof_gap/exercise_143/22.txt`; Stolz--Cesàro conclusion. -/
theorem gap22 (x y : ℕ → ℝ) (a : ℝ)
    (hy : Increasing y) (hyInf : Tendsto y atTop atTop)
    (hΔ : Tendsto (ratioIncrement x y) atTop (𝓝 a)) :
    Tendsto (ratioTerm x y) atTop (𝓝 a) := by
  apply Metric.tendsto_atTop.2
  intro ε hε
  have hhalf : 0 < ε / 2 := by linarith
  rcases gap1 x y a hy hyInf hΔ (ε / 2) hhalf with
    ⟨N, hNpos, hinc⟩
  rcases gap18 x y a ε N hε hyInf with ⟨N', hNN', hhead⟩
  refine ⟨N' + 2, fun n hn => ?_⟩
  have hnN' : N' < n := by omega
  have hnN : N < n := hNN'.trans hnN'
  have hnbase : N + 1 < n := by omega
  have hynpos : 0 < y n := (hinc n hnN).2
  have hybasepos : 0 < y (N + 1) := (hinc (N + 1) (by omega)).2
  have hylt : y (N + 1) < y n := hy hnbase
  let m := n - 1
  have hmN : N < m := by dsimp [m]; omega
  have hl := telescope_lower x y (a - ε / 4) N m hmN
    (fun k hkN hkm => by
      have hk := (hinc k hkN).1
      have hdy : 0 < y (k + 1) - y k := sub_pos.mpr (hy (by omega))
      have hlo : a - ε / 4 < ratioIncrement x y k := by
        rw [abs_lt] at hk
        linarith
      exact (lt_div_iff₀ hdy).mp (by simpa [ratioIncrement] using hlo))
  have hu := telescope_upper x y (a + ε / 4) N m hmN
    (fun k hkN hkm => by
      have hk := (hinc k hkN).1
      have hdy : 0 < y (k + 1) - y k := sub_pos.mpr (hy (by omega))
      have hhi : ratioIncrement x y k < a + ε / 4 := by
        rw [abs_lt] at hk
        linarith
      exact (div_lt_iff₀ hdy).mp (by simpa [ratioIncrement] using hhi))
  have hm_succ : m + 1 = n := by dsimp [m]; omega
  rw [hm_succ] at hl hu
  have hdenpos : 0 < y n - y (N + 1) := sub_pos.mpr hylt
  have htail :
      |(x n - x (N + 1)) / (y n - y (N + 1)) - a| < ε / 4 := by
    rw [abs_lt]
    constructor
    · have := (lt_div_iff₀ hdenpos).2 hl
      linarith
    · have := (div_lt_iff₀ hdenpos).2 hu
      linarith
  have hratio0 : 0 ≤ y (N + 1) / y n :=
    div_nonneg hybasepos.le hynpos.le
  have hratio1 : y (N + 1) / y n ≤ 1 :=
    (div_le_one hynpos).2 hylt.le
  have hfactor : |1 - y (N + 1) / y n| ≤ 1 := by
    rw [abs_of_nonneg (by linarith)]
    linarith
  have hdecomp := gap16 x y a N n (ne_of_gt hynpos) (ne_of_gt hdenpos)
  have hhead' :
      |(x (N + 1) - a * y (N + 1)) / y n| < ε / 2 := by
    rw [abs_div, abs_of_pos hynpos]
    exact hhead n hnN'
  have hprod :
      |(1 - y (N + 1) / y n) *
        ((x n - x (N + 1)) / (y n - y (N + 1)) - a)| < ε / 4 := by
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_right hfactor (abs_nonneg _)).trans_lt
      (by simpa using htail)
  rw [Real.dist_eq, hdecomp]
  exact (abs_add_le _ _).trans_lt (by linarith)

/-- Source: `proof_gap/exercise_143/23.txt`; equality of the two finite limits. -/
theorem gap23 (x y : ℕ → ℝ) (a : ℝ)
    (hy : Increasing y) (hyInf : Tendsto y atTop atTop)
    (hΔ : Tendsto (ratioIncrement x y) atTop (𝓝 a)) :
    Tendsto (ratioTerm x y) atTop (𝓝 a) ∧
      Tendsto (ratioIncrement x y) atTop (𝓝 a) := by
  exact ⟨gap22 x y a hy hyInf hΔ, hΔ⟩

end

end ProofGap.Exercise143
