import ProofGapLean.Prelude.Sequences
import ProofGapLean.Prelude.Discrete
import Mathlib.Tactic.Positivity

namespace ProofGap.Exercise607

noncomputable section

def φ (x : ℝ) : ℝ := by
  classical
  exact if Irrational x then 0 else |x|
def ψ (x : ℝ) : ℝ := if x = 0 then 0 else 1
def rationalSeq (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)
def HasLimitAt (f : ℝ → ℝ) (a L : ℝ) : Prop :=
  Filter.Tendsto f (nhdsWithin a ({a} : Set ℝ)ᶜ) (nhds L)

/-- Exercise 607, gap 1; replace the non-functional arbitrary rational representation by a well-defined equivalent counterexample. -/
theorem gap1 : HasLimitAt φ 0 0 := by
  unfold HasLimitAt
  refine Metric.tendsto_nhds.2 ?_
  intro ε hε
  have hid0 :
      Filter.Tendsto (fun x : ℝ => x) (nhds 0) (nhds 0) := by
    refine Metric.tendsto_nhds.2 ?_
    intro δ hδ
    simpa only [Metric.mem_ball] using (Metric.ball_mem_nhds 0 hδ)
  have hid :
      Filter.Tendsto (fun x : ℝ => x)
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 0) :=
    hid0.mono_left inf_le_left
  have hevent :
      ∀ᶠ x in nhdsWithin 0 ({0} : Set ℝ)ᶜ, dist x 0 < ε :=
    (Metric.tendsto_nhds.1 hid) ε hε
  filter_upwards [hevent] with x hx
  by_cases h : Irrational x
  · simp [φ, h, hε]
  · simpa [φ, h, Real.dist_eq] using hx

/-- Exercise 607, gap 2; use the same well-defined counterexample. -/
theorem gap2 : HasLimitAt ψ 0 1 := by
  unfold HasLimitAt
  have hc :
      Filter.Tendsto (fun _ : ℝ => (1 : ℝ))
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1) :=
    tendsto_const_nhds
  refine hc.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hx0 : x ≠ 0 := by
    simpa using hx
  simp [ψ, hx0]

/-- Exercise 607, gap 3; bind one irrational sequence instead of shadowing `x,n`. -/
theorem gap3 (u : ℕ → ℝ) (hu : Filter.Tendsto u Filter.atTop (nhds 0))
    (hirr : ∀ n, Irrational (u n)) :
    ∀ n, φ (u n) = 0 := by
  intro n
  simp [φ, hirr n]

/-- Exercise 607, gap 4. -/
theorem gap4 (u : ℕ → ℝ) (hu : Filter.Tendsto u Filter.atTop (nhds 0))
    (hirr : ∀ n, Irrational (u n)) :
    ∀ n, ψ (φ (u n)) = 0 := by
  intro n
  rw [gap3 u hu hirr n]
  simp [ψ]

/-- Exercise 607, gap 5; use an explicit nonzero rational sequence. -/
theorem gap5 :
    Filter.Tendsto rationalSeq Filter.atTop (nhds 0) ∧
      ∀ n, φ (rationalSeq n) ≠ 0 := by
  constructor
  · refine Metric.tendsto_atTop.2 ?_
    intro ε hε
    rcases exists_nat_gt (1 / ε) with ⟨N, hN⟩
    refine ⟨N, ?_⟩
    intro n hn
    have hcast : (N : ℝ) ≤ (n : ℝ) := Nat.cast_le.2 hn
    have hbase : 1 < (N : ℝ) * ε :=
      (div_lt_iff₀ hε).mp hN
    have hmul : (N : ℝ) * ε ≤ (n : ℝ) * ε :=
      mul_le_mul_of_nonneg_right hcast hε.le
    have hnlt : (n : ℝ) < (n : ℝ) + 1 :=
      lt_add_of_pos_right _ zero_lt_one
    have hstep : (n : ℝ) * ε < ((n : ℝ) + 1) * ε :=
      mul_lt_mul_of_pos_right hnlt hε
    have hprod : 1 < ((n : ℝ) + 1) * ε :=
      (lt_of_lt_of_le hbase hmul).trans hstep
    have hden : 0 < (n : ℝ) + 1 := by
      positivity
    have hdiv : 1 / ((n : ℝ) + 1) < ε :=
      (div_lt_iff₀ hden).2 (by simpa [mul_comm] using hprod)
    rw [Real.dist_eq]
    change |1 / ((n : ℝ) + 1) - 0| < ε
    rw [sub_zero, abs_of_pos (one_div_pos.mpr hden)]
    exact hdiv
  · intro n
    have hpos : 0 < rationalSeq n := by
      unfold rationalSeq
      positivity
    have hrat : ¬ Irrational (rationalSeq n) := by
      intro hi
      apply hi
      refine ⟨(1 / ((n : ℚ) + 1) : ℚ), ?_⟩
      simp [rationalSeq]
    simpa [φ, hrat, abs_of_pos hpos] using hpos.ne'

/-- Exercise 607, gap 6; use the explicit rational sequence. -/
theorem gap6 : ∀ n, ψ (φ (rationalSeq n)) = 1 := by
  intro n
  simp [ψ, gap5.2 n]

/-- Exercise 607, gap 7. -/
theorem gap7 : ¬ ∃ L : ℝ, HasLimitAt (fun x => ψ (φ x)) 0 L := by
  rintro ⟨L, hL⟩
  have hrne : ∀ n, rationalSeq n ≠ 0 := by
    intro n
    unfold rationalSeq
    positivity
  have hrwithin :
      Filter.Tendsto rationalSeq Filter.atTop
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) := by
    refine tendsto_nhdsWithin_iff.2 ⟨gap5.1, ?_⟩
    exact Filter.Eventually.of_forall (fun n => by simpa using hrne n)
  have hratL :
      Filter.Tendsto (fun n => ψ (φ (rationalSeq n))) Filter.atTop (nhds L) :=
    hL.comp hrwithin
  have hrat1 :
      Filter.Tendsto (fun n => ψ (φ (rationalSeq n))) Filter.atTop (nhds 1) := by
    simpa only [gap6] using
      (tendsto_const_nhds :
        Filter.Tendsto (fun _ : ℕ => (1 : ℝ)) Filter.atTop (nhds 1))
  have hLone : L = 1 := tendsto_nhds_unique hratL hrat1
  let u : ℕ → ℝ := fun n => Real.sqrt 2 / ((n : ℝ) + 1)
  have hu : Filter.Tendsto u Filter.atTop (nhds 0) := by
    have hmul :
        Filter.Tendsto (fun n : ℕ => Real.sqrt 2 * rationalSeq n)
          Filter.atTop (nhds (Real.sqrt 2 * 0)) :=
      (tendsto_const_nhds :
        Filter.Tendsto (fun _ : ℕ => Real.sqrt 2) Filter.atTop
          (nhds (Real.sqrt 2))).mul gap5.1
    simpa [u, rationalSeq, div_eq_mul_inv] using hmul
  have hirr : ∀ n, Irrational (u n) := by
    intro n
    intro hx
    rcases hx with ⟨q, hq⟩
    have hd : (n : ℝ) + 1 ≠ 0 := by positivity
    change (q : ℝ) = Real.sqrt 2 / ((n : ℝ) + 1) at hq
    apply irrational_sqrt_two
    refine ⟨q * ((n : ℚ) + 1), ?_⟩
    simpa [hq] using (div_mul_cancel₀ (Real.sqrt 2) hd)
  have hune : ∀ n, u n ≠ 0 := by
    intro n
    dsimp [u]
    positivity
  have huwithin :
      Filter.Tendsto u Filter.atTop (nhdsWithin 0 ({0} : Set ℝ)ᶜ) := by
    refine tendsto_nhdsWithin_iff.2 ⟨hu, ?_⟩
    exact Filter.Eventually.of_forall (fun n => by simpa using hune n)
  have hirrL :
      Filter.Tendsto (fun n => ψ (φ (u n))) Filter.atTop (nhds L) :=
    hL.comp huwithin
  have hirr0 :
      Filter.Tendsto (fun n => ψ (φ (u n))) Filter.atTop (nhds 0) := by
    simpa only [gap4 u hu hirr] using
      (tendsto_const_nhds :
        Filter.Tendsto (fun _ : ℕ => (0 : ℝ)) Filter.atTop (nhds 0))
  have hLzero : L = 0 := tendsto_nhds_unique hirrL hirr0
  exact zero_ne_one (hLzero.symm.trans hLone)

/-- Exercise 607, gap 8; state the composition counterexample with fixed witnesses. -/
theorem gap8 :
    ∃ (a A B : ℝ) (p q : ℝ → ℝ),
      HasLimitAt p a A ∧ HasLimitAt q A B ∧
        ¬ HasLimitAt (fun x => q (p x)) a B := by
  refine ⟨0, 0, 1, φ, ψ, gap1, gap2, ?_⟩
  intro hcomp
  exact gap7 ⟨1, hcomp⟩

end

end ProofGap.Exercise607
