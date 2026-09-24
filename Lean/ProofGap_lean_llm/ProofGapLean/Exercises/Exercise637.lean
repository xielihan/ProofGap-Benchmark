import ProofGapLean.Prelude.Analysis
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Lean.Elab.Tactic.Omega

namespace ProofGap.Exercise637

noncomputable section

def Recurrence (a : ℝ) (x : ℕ → ℝ) : Prop :=
  x 1 = Real.sqrt a ∧
    ∀ n ≥ 2, x n = Real.sqrt (a + x (n - 1))

/-- Source: `proof_gap/exercise_637/1.txt`. -/
private lemma recurrence_facts (a : ℝ) (x : ℕ → ℝ) (ha : 0 < a)
    (hx : Recurrence a x) :
    (∀ n ≥ 1, 0 < x n) ∧
      (∀ n ≥ 2, x n ^ 2 = a + x (n - 1)) ∧
      (∀ n ≥ 1, x n < x (n + 1)) := by
  have hnonneg : ∀ n ≥ 1, 0 ≤ x n := by
    intro n hn
    by_cases h1 : n = 1
    · subst n
      rw [hx.1]
      exact Real.sqrt_nonneg a
    · have hn2 : 2 ≤ n := by omega
      rw [hx.2 n hn2]
      exact Real.sqrt_nonneg _
  have hpos : ∀ n ≥ 1, 0 < x n := by
    intro n hn
    by_cases h1 : n = 1
    · subst n
      rw [hx.1]
      exact Real.sqrt_pos.2 ha
    · have hn2 : 2 ≤ n := by omega
      rw [hx.2 n hn2]
      apply Real.sqrt_pos.2
      have hp := hnonneg (n - 1) (by omega)
      linarith
  have hsq : ∀ n ≥ 2, x n ^ 2 = a + x (n - 1) := by
    intro n hn
    rw [hx.2 n hn]
    apply Real.sq_sqrt
    have hp := hnonneg (n - 1) (by omega)
    linarith
  have hstep : ∀ n ≥ 1, x n < x (n + 1) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro hn
        by_cases h1 : n = 1
        · subst n
          have hsq1 : x 1 ^ 2 = a := by
            rw [hx.1]
            exact Real.sq_sqrt (le_of_lt ha)
          have hsq2 : x 2 ^ 2 = a + x 1 := by
            simpa using hsq 2 (by omega)
          have hp1 := hpos 1 (by omega)
          have hn2 := hnonneg 2 (by omega)
          nlinarith
        · have hn2 : 2 ≤ n := by omega
          have hprev : x (n - 1) < x n := by
            have h := ih (n - 1) (by omega) (by omega)
            simpa [Nat.sub_add_cancel (show 1 ≤ n by omega)] using h
          have hsqn := hsq n hn2
          have hsqnext : x (n + 1) ^ 2 = a + x n := by
            simpa using hsq (n + 1) (by omega)
          have hnonn := hnonneg n hn
          have hnonnext := hnonneg (n + 1) (by omega)
          nlinarith
  exact ⟨hpos, hsq, hstep⟩

theorem gap1 (a : ℝ) (x : ℕ → ℝ) (ha : 0 < a)
    (hx : Recurrence a x) :
    StrictMonoOn x (Set.Ici 1) := by
  have hs : StrictMono (fun k : ℕ => x (k + 1)) :=
    strictMono_nat_of_lt_succ (fun k =>
      (recurrence_facts a x ha hx).2.2 (k + 1) (by omega))
  intro m hm n hn hmn
  have hm1 : 1 ≤ m := hm
  have hn1 : 1 ≤ n := hn
  have hsub : m - 1 < n - 1 := by omega
  have h := hs hsub
  simpa [Nat.sub_add_cancel hm1, Nat.sub_add_cancel hn1] using h

/-- Source: `proof_gap/exercise_637/2.txt`; add the missing range `n≥2`. -/
theorem gap2 (a : ℝ) (x : ℕ → ℝ) (ha : 0 < a)
    (hx : Recurrence a x) :
    ∀ n ≥ 2, x n ^ 2 = a + x (n - 1) := by
  exact (recurrence_facts a x ha hx).2.1

/-- Source: `proof_gap/exercise_637/3.txt`; add `n≥2`. -/
theorem gap3 (a : ℝ) (x : ℕ → ℝ) (ha : 0 < a)
    (hx : Recurrence a x) :
    ∀ n ≥ 2, x n = a / x n + x (n - 1) / x n := by
  intro n hn
  have hsq := (recurrence_facts a x ha hx).2.1 n hn
  have hpos := (recurrence_facts a x ha hx).1 n (by omega)
  calc
    x n = x n ^ 2 / x n := by
      rw [pow_two]
      field_simp [ne_of_gt hpos]
    _ = (a + x (n - 1)) / x n := by rw [hsq]
    _ = a / x n + x (n - 1) / x n := by
      exact add_div _ _ _

/-- Source: `proof_gap/exercise_637/4.txt`; the strict inequality starts at `n≥3`. -/
theorem gap4 (a : ℝ) (x : ℕ → ℝ) (ha : 0 < a)
    (hx : Recurrence a x) :
    ∀ n ≥ 3, Real.sqrt a < x (n - 1) := by
  intro n hn
  have h := (gap1 a x ha hx)
    (show 1 ∈ Set.Ici 1 by simp)
    (show n - 1 ∈ Set.Ici 1 by simp; omega)
    (show 1 < n - 1 by omega)
  simpa [hx.1] using h

/-- Source: `proof_gap/exercise_637/5.txt`; add the missing range `n≥2`. -/
theorem gap5 (a : ℝ) (x : ℕ → ℝ) (ha : 0 < a)
    (hx : Recurrence a x) :
    ∀ n ≥ 2, x (n - 1) < x n := by
  intro n hn
  have h := (recurrence_facts a x ha hx).2.2 (n - 1) (by omega)
  simpa [Nat.sub_add_cancel (show 1 ≤ n by omega)] using h

/-- Source: `proof_gap/exercise_637/6.txt`; the strict inequality starts at `n≥2`. -/
theorem gap6 (a : ℝ) (x : ℕ → ℝ) (ha : 0 < a)
    (hx : Recurrence a x) :
    ∀ n ≥ 2, Real.sqrt a < x n := by
  intro n hn
  have h := (gap1 a x ha hx)
    (show 1 ∈ Set.Ici 1 by simp)
    (show n ∈ Set.Ici 1 by simp; omega)
    (show 1 < n by omega)
  simpa [hx.1] using h

/-- Source: `proof_gap/exercise_637/7.txt`; add the missing range `n≥2`. -/
theorem gap7 (a : ℝ) (x : ℕ → ℝ) (ha : 0 < a)
    (hx : Recurrence a x) :
    ∀ n ≥ 2, x n < a / x n + 1 := by
  intro n hn
  have hstep := gap5 a x ha hx n hn
  have hpos := (recurrence_facts a x ha hx).1 n (by omega)
  have hdiv : x (n - 1) / x n < 1 :=
    (div_lt_one hpos).2 hstep
  calc
    x n = a / x n + x (n - 1) / x n := gap3 a x ha hx n hn
    _ < a / x n + 1 := by linarith

/-- Source: `proof_gap/exercise_637/8.txt`; the strict inequality starts at `n≥2`. -/
theorem gap8 (a : ℝ) (x : ℕ → ℝ) (ha : 0 < a)
    (hx : Recurrence a x) :
    ∀ n ≥ 2, Real.sqrt a < x n := by
  exact gap6 a x ha hx

/-- Source: `proof_gap/exercise_637/9.txt`. -/
theorem gap9 (a : ℝ) (x : ℕ → ℝ) (ha : 0 < a)
    (hx : Recurrence a x) :
    ∀ n ≥ 1, x n < Real.sqrt a + 1 := by
  intro n hn
  by_cases h1 : n = 1
  · subst n
    rw [hx.1]
    linarith
  · have hn2 : 2 ≤ n := by omega
    have hrootpos : 0 < Real.sqrt a := Real.sqrt_pos.2 ha
    have hrootsq : (Real.sqrt a) ^ 2 = a :=
      Real.sq_sqrt (le_of_lt ha)
    have hxn : Real.sqrt a < x n := gap8 a x ha hx n hn2
    have hxnpos : 0 < x n := lt_trans hrootpos hxn
    have hmul : Real.sqrt a * Real.sqrt a < Real.sqrt a * x n :=
      mul_lt_mul_of_pos_left hxn hrootpos
    have hquot : a / x n < Real.sqrt a := by
      apply (div_lt_iff₀ hxnpos).2
      nlinarith [hrootsq, hmul]
    have hmain := gap7 a x ha hx n hn2
    linarith

/-- Source: `proof_gap/exercise_637/10.txt`. -/
theorem gap10 (a : ℝ) (x : ℕ → ℝ) (ha : 0 < a)
    (hx : Recurrence a x) :
    ∃ M, ∀ n, |x n| ≤ M := by
  refine ⟨max |x 0| (Real.sqrt a + 1), ?_⟩
  intro n
  by_cases h0 : n = 0
  · subst n
    exact le_max_left _ _
  · have hn1 : 1 ≤ n := by omega
    have hpos := (recurrence_facts a x ha hx).1 n hn1
    rw [abs_of_nonneg (le_of_lt hpos)]
    exact le_trans (le_of_lt (gap9 a x ha hx n hn1)) (le_max_right _ _)

/-- Source: `proof_gap/exercise_637/11.txt`. -/
theorem gap11 (a : ℝ) (x : ℕ → ℝ) (ha : 0 < a)
    (hx : Recurrence a x) :
    ∃ l, Filter.Tendsto x Filter.atTop (nhds l) := by
  let y : ℕ → ℝ := fun n => x (n + 1)
  have hy_strict : StrictMono y := by
    intro m n hmn
    exact (gap1 a x ha hx)
      (show m + 1 ∈ Set.Ici 1 by simp)
      (show n + 1 ∈ Set.Ici 1 by simp)
      (by omega)
  have hy_bdd : BddAbove (Set.range y) := by
    refine ⟨Real.sqrt a + 1, ?_⟩
    rintro z ⟨n, rfl⟩
    exact le_of_lt (gap9 a x ha hx (n + 1) (by omega))
  have hy_lim :
      Filter.Tendsto y Filter.atTop
        (nhds (⨆ n : ℕ, y n)) :=
    tendsto_atTop_ciSup hy_strict.monotone hy_bdd
  have hpred :
      Filter.Tendsto (fun n : ℕ => n - 1) Filter.atTop Filter.atTop := by
    refine Filter.tendsto_atTop.2 (fun b => ?_)
    filter_upwards [Filter.eventually_ge_atTop (b + 1)] with n hn
    omega
  refine ⟨⨆ n : ℕ, y n, (hy_lim.comp hpred).congr' ?_⟩
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  simp [y, Nat.sub_add_cancel hn]

/-- Source: `proof_gap/exercise_637/12.txt`. -/
theorem gap12 (a : ℝ) (x : ℕ → ℝ) (ha : 0 < a)
    (hx : Recurrence a x) :
    ∃ l, l ^ 2 = a + l := by
  refine ⟨(1 + Real.sqrt (1 + 4 * a)) / 2, ?_⟩
  have hdisc : 0 ≤ 1 + 4 * a := by linarith
  have hs := Real.sq_sqrt hdisc
  nlinarith

/-- Source: `proof_gap/exercise_637/13.txt`; replace the informal `±` by the two roots. -/
theorem gap13 (a l : ℝ) (ha : 0 ≤ a) :
    l ^ 2 = a + l ↔
      l = (1 + Real.sqrt (1 + 4 * a)) / 2 ∨
      l = (1 - Real.sqrt (1 + 4 * a)) / 2 := by
  have hdisc : 0 ≤ 1 + 4 * a := by linarith
  have hs : (Real.sqrt (1 + 4 * a)) ^ 2 = 1 + 4 * a :=
    Real.sq_sqrt hdisc
  constructor
  · intro hl
    have hfac :
        (2 * l - 1 - Real.sqrt (1 + 4 * a)) *
          (2 * l - 1 + Real.sqrt (1 + 4 * a)) = 0 := by
      nlinarith
    rcases mul_eq_zero.mp hfac with hplus | hminus
    · left
      nlinarith
    · right
      nlinarith
  · intro hl
    rcases hl with hl | hl
    · nlinarith
    · nlinarith

/-- Source: `proof_gap/exercise_637/14.txt`; restrict to the positive root. -/
theorem gap14 (a l : ℝ) (ha : 0 < a) (hl : 0 < l) :
    l ^ 2 = a + l ↔
      l = (1 + Real.sqrt (1 + 4 * a)) / 2 := by
  constructor
  · intro heq
    rcases (gap13 a l (le_of_lt ha)).mp heq with hposroot | hnegroot
    · exact hposroot
    · have hdisc : 0 ≤ 1 + 4 * a := by linarith
      have hs : (Real.sqrt (1 + 4 * a)) ^ 2 = 1 + 4 * a :=
        Real.sq_sqrt hdisc
      have hsnonneg := Real.sqrt_nonneg (1 + 4 * a)
      have hsone : 1 < Real.sqrt (1 + 4 * a) := by
        nlinarith
      nlinarith
  · intro hroot
    apply (gap13 a l (le_of_lt ha)).2
    exact Or.inl hroot

/-- Source: `proof_gap/exercise_637/15.txt`. -/
theorem gap15 (a : ℝ) (x : ℕ → ℝ) (ha : 0 < a)
    (hx : Recurrence a x) :
    Filter.Tendsto x Filter.atTop
      (nhds ((1 + Real.sqrt (1 + 4 * a)) / 2)) := by
  obtain ⟨l, hlim⟩ := gap11 a x ha hx
  have hlower : Real.sqrt a ≤ l := by
    have hneg_bound : -l ≤ -Real.sqrt a := by
      apply le_of_tendsto hlim.neg
      filter_upwards [Filter.eventually_ge_atTop 2] with n hn
      have hxn := gap8 a x ha hx n hn
      linarith
    linarith
  have hl : 0 < l := lt_of_lt_of_le (Real.sqrt_pos.2 ha) hlower
  have hshift :
      Filter.Tendsto (fun n : ℕ => n + 1) Filter.atTop Filter.atTop := by
    refine Filter.tendsto_atTop.2 (fun b => ?_)
    filter_upwards [Filter.eventually_ge_atTop b] with n hn
    omega
  have hlim_shift :
      Filter.Tendsto (fun n : ℕ => x (n + 1)) Filter.atTop (nhds l) :=
    hlim.comp hshift
  have hsq_lim :
      Filter.Tendsto (fun n : ℕ => x (n + 1) ^ 2) Filter.atTop
        (nhds (l ^ 2)) :=
    hlim_shift.pow 2
  have hevent :
      (fun n : ℕ => x (n + 1) ^ 2) =ᶠ[Filter.atTop]
        (fun n : ℕ => a + x n) := by
    filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    simpa using gap2 a x ha hx (n + 1) (by omega)
  have hrhs_lim :
      Filter.Tendsto (fun n : ℕ => a + x n) Filter.atTop
        (nhds (a + l)) :=
    tendsto_const_nhds.add hlim
  have hfix : l ^ 2 = a + l :=
    tendsto_nhds_unique (hsq_lim.congr' hevent) hrhs_lim
  have hroot := (gap14 a l ha hl).mp hfix
  simpa [hroot] using hlim

end

end ProofGap.Exercise637
