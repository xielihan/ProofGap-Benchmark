import ProofGapLean.Prelude.Analysis
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

namespace ProofGap.Exercise639

noncomputable section

def Recurrence (x : ℝ) (y : ℕ → ℝ) : Prop :=
  y 1 = x / 2 ∧
    ∀ n ≥ 2, y n = x / 2 + y (n - 1) ^ 2 / 2

/-- Source: `proof_gap/exercise_639/1.txt`; strictness requires `x>0`, not merely `x≥0`. -/
theorem gap1 (x : ℝ) (y : ℕ → ℝ) (hx0 : 0 < x) (hx1 : x ≤ 1)
    (hy : Recurrence x y) :
    y 1 < y 2 := by
  have hbase := hy.1
  have hstep : y 2 = x / 2 + y 1 ^ 2 / 2 := by
    simpa using hy.2 2 (by omega)
  nlinarith [sq_nonneg (y 1)]

/-- Source: `proof_gap/exercise_639/2.txt`; add the recurrence range `n≥2`. -/
theorem gap2 (x : ℝ) (y : ℕ → ℝ) (n : ℕ) (hn : 2 ≤ n)
    (hy : Recurrence x y) (hmono : y (n - 1) ≤ y n) :
    y (n + 1) - y n = (y n ^ 2 - y (n - 1) ^ 2) / 2 := by
  have hnext : y (n + 1) = x / 2 + y n ^ 2 / 2 := by
    simpa using hy.2 (n + 1) (by omega)
  have hcur : y n = x / 2 + y (n - 1) ^ 2 / 2 := hy.2 n hn
  rw [hnext, hcur]
  ring

/-- Source: `proof_gap/exercise_639/3.txt`; add the recurrence range `n≥2`. -/
theorem gap3 (x : ℝ) (y : ℕ → ℝ) (n : ℕ) (hn : 2 ≤ n)
    (hy : Recurrence x y) (hnonneg : 0 ≤ y (n - 1))
    (hmono : y (n - 1) ≤ y n) :
    y n ≤ y (n + 1) := by
  have hdiff := gap2 x y n hn hy hmono
  have hynonneg : 0 ≤ y n := hnonneg.trans hmono
  nlinarith [sq_nonneg (y n - y (n - 1))]

/-- Source: `proof_gap/exercise_639/4.txt`. -/
theorem gap4 (x : ℝ) (y : ℕ → ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hy : Recurrence x y) :
    MonotoneOn y (Set.Ici 1) := by
  have hpair : ∀ n, 1 ≤ n → 0 ≤ y n ∧ y n ≤ y (n + 1) := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base =>
        have hbase := hy.1
        have hstep : y 2 = x / 2 + y 1 ^ 2 / 2 := by
          simpa using hy.2 2 (by omega)
        constructor
        · nlinarith
        · nlinarith [sq_nonneg (y 1)]
    | succ n hn ih =>
        have hnext : y (n + 1) ≤ y ((n + 1) + 1) :=
          gap3 x y (n + 1) (by omega) hy
            (by simpa using ih.1) (by simpa using ih.2)
        exact ⟨ih.1.trans ih.2, hnext⟩
  intro a ha b hb hab
  have ha' : 1 ≤ a := ha
  induction b, hab using Nat.le_induction with
  | base => exact le_rfl
  | succ b hab ih =>
      exact (ih (ha'.trans hab)).trans (hpair b (ha'.trans hab)).2

/-- Source: `proof_gap/exercise_639/5.txt`. -/
theorem gap5 (x : ℝ) (y : ℕ → ℝ) (hx0 : 0 ≤ x)
    (hy : Recurrence x y) :
    0 ≤ y 1 := by
  rw [hy.1]
  linarith

/-- Source: `proof_gap/exercise_639/6.txt`. -/
theorem gap6 (x : ℝ) (y : ℕ → ℝ) (hx1 : x ≤ 1)
    (hy : Recurrence x y) :
    y 1 < 1 := by
  rw [hy.1]
  linarith

/-- Source: `proof_gap/exercise_639/7.txt`. -/
theorem gap7 : (0 : ℝ) < 1 := by
  exact zero_lt_one

/-- Source: `proof_gap/exercise_639/8.txt`. -/
theorem gap8 (y : ℕ → ℝ) (k : ℕ) (h0 : 0 ≤ y k) (h1 : y k < 1) :
    0 ≤ y k ^ 2 := by
  exact sq_nonneg (y k)

/-- Source: `proof_gap/exercise_639/9.txt`. -/
theorem gap9 (y : ℕ → ℝ) (k : ℕ) (h0 : 0 ≤ y k) (h1 : y k < 1) :
    y k ^ 2 < 1 := by
  nlinarith [sq_nonneg (y k)]

/-- Source: `proof_gap/exercise_639/10.txt`. -/
theorem gap10 (y : ℕ → ℝ) (k : ℕ) (h0 : 0 ≤ y k) (h1 : y k < 1) :
    (0 : ℝ) < 1 := by
  exact gap7

/-- Source: `proof_gap/exercise_639/11.txt`; bind the recurrence step. -/
theorem gap11 (x : ℝ) (y : ℕ → ℝ) (k : ℕ) (hk : 1 ≤ k)
    (hx0 : 0 ≤ x) (hy : Recurrence x y)
    (h0 : 0 ≤ y k) (h1 : y k < 1) :
    0 ≤ y (k + 1) := by
  have hstep : y (k + 1) = x / 2 + y k ^ 2 / 2 := by
    simpa using hy.2 (k + 1) (by omega)
  nlinarith [sq_nonneg (y k)]

/-- Source: `proof_gap/exercise_639/12.txt`; bind the recurrence step and `x≤1`. -/
theorem gap12 (x : ℝ) (y : ℕ → ℝ) (k : ℕ) (hk : 1 ≤ k)
    (hx1 : x ≤ 1) (hy : Recurrence x y)
    (h0 : 0 ≤ y k) (h1 : y k < 1) :
    y (k + 1) < 1 := by
  have hstep : y (k + 1) = x / 2 + y k ^ 2 / 2 := by
    simpa using hy.2 (k + 1) (by omega)
  have hsq : y k ^ 2 < 1 := gap9 y k h0 h1
  nlinarith

/-- Source: `proof_gap/exercise_639/13.txt`. -/
theorem gap13 (y : ℕ → ℝ) (k : ℕ) (h0 : 0 ≤ y k) (h1 : y k < 1) :
    (0 : ℝ) < 1 := by
  exact gap7

/-- Source: `proof_gap/exercise_639/14.txt`. -/
theorem gap14 (x : ℝ) (y : ℕ → ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hy : Recurrence x y) :
    ∃ M, ∀ n, |y n| ≤ M := by
  have hbounds : ∀ n, 1 ≤ n → 0 ≤ y n ∧ y n < 1 := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base =>
        exact ⟨gap5 x y hx0 hy, gap6 x y hx1 hy⟩
    | succ n hn ih =>
        exact
          ⟨gap11 x y n hn hx0 hy ih.1 ih.2,
            gap12 x y n hn hx1 hy ih.1 ih.2⟩
  refine ⟨max |y 0| 1, ?_⟩
  intro n
  by_cases hn : n = 0
  · subst n
    exact le_max_left _ _
  · have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
    have hb := hbounds n hn1
    rw [abs_of_nonneg hb.1]
    exact hb.2.le.trans (le_max_right _ _)

/-- Source: `proof_gap/exercise_639/15.txt`. -/
theorem gap15 (x : ℝ) (y : ℕ → ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hy : Recurrence x y) :
    ∃ l, Filter.Tendsto y Filter.atTop (nhds l) ∧ 0 ≤ l ∧ l ≤ 1 := by
  have hbounds : ∀ n, 1 ≤ n → 0 ≤ y n ∧ y n < 1 := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base =>
        exact ⟨gap5 x y hx0 hy, gap6 x y hx1 hy⟩
    | succ n hn ih =>
        exact
          ⟨gap11 x y n hn hx0 hy ih.1 ih.2,
            gap12 x y n hn hx1 hy ih.1 ih.2⟩
  let z : ℕ → ℝ := fun n => if n = 0 then y 1 else y n
  have hzmono : Monotone z := by
    intro a b hab
    by_cases ha : a = 0
    · subst a
      by_cases hb : b = 0
      · subst b
        rfl
      · simp only [z, if_pos, if_neg hb]
        have hb1 : 1 ≤ b := Nat.one_le_iff_ne_zero.mpr hb
        exact gap4 x y hx0 hx1 hy (by simp) hb1 hb1
    · have hb : b ≠ 0 := by omega
      simp only [z, if_neg ha, if_neg hb]
      exact gap4 x y hx0 hx1 hy
        (Nat.one_le_iff_ne_zero.mpr ha)
        (Nat.one_le_iff_ne_zero.mpr hb) hab
  have hzmem : ∀ n, z n ∈ Set.Icc (0 : ℝ) 1 := by
    intro n
    by_cases hn : n = 0
    · simp only [z, if_pos hn]
      exact ⟨(hbounds 1 (by omega)).1, (hbounds 1 (by omega)).2.le⟩
    · simp only [z, if_neg hn]
      have hb := hbounds n (Nat.one_le_iff_ne_zero.mpr hn)
      exact ⟨hb.1, hb.2.le⟩
  have hzbdd : BddAbove (Set.range z) := by
    refine ⟨1, ?_⟩
    rintro _ ⟨n, rfl⟩
    exact (hzmem n).2
  have hzlim : Filter.Tendsto z Filter.atTop (nhds (⨆ n, z n)) := by
    apply tendsto_atTop_ciSup <;> assumption
  have hlbounds : (⨆ n, z n) ∈ Set.Icc (0 : ℝ) 1 :=
    isClosed_Icc.mem_of_tendsto hzlim
      (Filter.Eventually.of_forall hzmem)
  have hzy : z =ᶠ[Filter.atTop] y := by
    refine Filter.eventually_atTop.2 ⟨1, ?_⟩
    intro n hn
    have hn0 : n ≠ 0 := by omega
    simp [z, hn0]
  exact ⟨⨆ n, z n, hzlim.congr' hzy, hlbounds.1, hlbounds.2⟩

/-- Source: `proof_gap/exercise_639/16.txt`. -/
theorem gap16 (x : ℝ) (y : ℕ → ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hy : Recurrence x y) :
    ∃ l, l = x / 2 + l ^ 2 / 2 := by
  refine ⟨1 - Real.sqrt (1 - x), ?_⟩
  have hnonneg : 0 ≤ 1 - x := sub_nonneg.mpr hx1
  have hsqrt := Real.sq_sqrt hnonneg
  nlinarith

/-- Source: `proof_gap/exercise_639/17.txt`; replace `±` by the two roots. -/
theorem gap17 (x l : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    l = x / 2 + l ^ 2 / 2 ↔
      l = 1 - Real.sqrt (1 - x) ∨ l = 1 + Real.sqrt (1 - x) := by
  have hnonneg : 0 ≤ 1 - x := sub_nonneg.mpr hx1
  have hsqrt := Real.sq_sqrt hnonneg
  constructor
  · intro h
    have hprod :
        (l - (1 - Real.sqrt (1 - x))) *
            (l - (1 + Real.sqrt (1 - x))) = 0 := by
      nlinarith
    rcases mul_eq_zero.mp hprod with hminus | hplus
    · left
      linarith
    · right
      linarith
  · intro h
    rcases h with hminus | hplus
    · rw [hminus]
      nlinarith
    · rw [hplus]
      nlinarith

/-- Source: `proof_gap/exercise_639/18.txt`; select the root lying in `[0,1]`. -/
theorem gap18 (x l : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hl0 : 0 ≤ l) (hl1 : l ≤ 1) :
    l = x / 2 + l ^ 2 / 2 ↔
      l = 1 - Real.sqrt (1 - x) := by
  constructor
  · intro h
    rcases (gap17 x l hx0 hx1).mp h with hminus | hplus
    · exact hminus
    · have hsqrt_nonneg : 0 ≤ Real.sqrt (1 - x) := Real.sqrt_nonneg _
      nlinarith
  · intro h
    exact (gap17 x l hx0 hx1).mpr (Or.inl h)

/-- Source: `proof_gap/exercise_639/19.txt`. -/
theorem gap19 (x : ℝ) (y : ℕ → ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hy : Recurrence x y) :
    Filter.Tendsto y Filter.atTop
      (nhds (1 - Real.sqrt (1 - x))) := by
  obtain ⟨l, hlim, hl0, hl1⟩ := gap15 x y hx0 hx1 hy
  have hadd : Filter.Tendsto (fun n : ℕ => n + 1)
      Filter.atTop Filter.atTop := by
    refine Filter.tendsto_atTop.2 ?_
    intro b
    exact Filter.eventually_atTop.2 ⟨b, by
      intro a ha
      omega⟩
  have hshift : Filter.Tendsto (fun n => y (n + 1))
      Filter.atTop (nhds l) := by
    simpa [Function.comp_def] using hlim.comp hadd
  have hrec :
      (fun n => y (n + 1)) =ᶠ[Filter.atTop]
        (fun n => x / 2 + y n ^ 2 / 2) := by
    refine Filter.eventually_atTop.2 ⟨1, ?_⟩
    intro n hn
    simpa using hy.2 (n + 1) (by omega)
  have hrhs_l : Filter.Tendsto (fun n => x / 2 + y n ^ 2 / 2)
      Filter.atTop (nhds l) := hshift.congr' hrec
  have hrhs_fixed : Filter.Tendsto (fun n => x / 2 + y n ^ 2 / 2)
      Filter.atTop (nhds (x / 2 + l ^ 2 / 2)) :=
    tendsto_const_nhds.add ((hlim.pow 2).div_const 2)
  have hfixed : l = x / 2 + l ^ 2 / 2 :=
    tendsto_nhds_unique hrhs_l hrhs_fixed
  have hlroot := (gap18 x l hx0 hx1 hl0 hl1).mp hfixed
  simpa [hlroot] using hlim

end

end ProofGap.Exercise639
