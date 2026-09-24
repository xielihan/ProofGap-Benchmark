import ProofGapLean.Prelude.Analysis

open Filter Topology

namespace ProofGap.Exercise149

noncomputable section

def newtonRecurrence (a : ℝ) (x : ℕ → ℝ) : Prop :=
  ∀ n, x (n + 1) = (x n + a / x n) / 2

/-- Exercise 149, gap 1; positivity is needed for the square-root identity. -/
theorem gap1 (a : ℝ) (x : ℕ → ℝ)
    (ha : 0 < a) (hx : ∀ n, 0 < x n) (hrec : newtonRecurrence a x) :
    ∀ n, x (n + 1) =
      ((Real.sqrt (x n) - Real.sqrt a / Real.sqrt (x n)) ^ 2) / 2 +
        Real.sqrt a := by
  intro n
  have hsx : Real.sqrt (x n) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (hx n))
  have hsqx : (Real.sqrt (x n)) ^ 2 = x n :=
    Real.sq_sqrt (le_of_lt (hx n))
  have hsqa : (Real.sqrt a) ^ 2 = a := Real.sq_sqrt (le_of_lt ha)
  rw [hrec n]
  calc
    (x n + a / x n) / 2 =
        ((Real.sqrt (x n)) ^ 2 +
          (Real.sqrt a) ^ 2 / (Real.sqrt (x n)) ^ 2) / 2 := by
            rw [hsqx, hsqa]
    _ = ((Real.sqrt (x n) - Real.sqrt a / Real.sqrt (x n)) ^ 2) / 2 +
          Real.sqrt a := by
            field_simp [hsx]
            <;> ring

/-- Exercise 149, gap 2. -/
theorem gap2 (a : ℝ) (x : ℕ → ℝ) :
    ∀ n, ((Real.sqrt (x n) - Real.sqrt a / Real.sqrt (x n)) ^ 2) / 2 +
      Real.sqrt a ≥ Real.sqrt a := by
  intro n
  nlinarith [sq_nonneg (Real.sqrt (x n) - Real.sqrt a / Real.sqrt (x n))]

/-- Exercise 149, gap 3. -/
theorem gap3 (a : ℝ) (x : ℕ → ℝ)
    (ha : 0 < a) (hx : ∀ n, 0 < x n) (hrec : newtonRecurrence a x) :
    ∀ n, x (n + 1) ≥ Real.sqrt a := by
  intro n
  rw [gap1 a x ha hx hrec n]
  exact gap2 a x n

/-- Exercise 149, gap 4. -/
theorem gap4 (a : ℝ) (x : ℕ → ℝ) (hrec : newtonRecurrence a x) :
    ∀ n, x (n + 1) - x n = (a / x n - x n) / 2 := by
  intro n
  rw [hrec n]
  ring

/-- Exercise 149, gap 5; decrease starts after the first Newton step. -/
theorem gap5 (a : ℝ) (x : ℕ → ℝ)
    (ha : 0 < a) (hx : ∀ n, 0 < x n) (hrec : newtonRecurrence a x) :
    ∀ n, (a / x (n + 1) - x (n + 1)) / 2 ≤ 0 := by
  intro n
  have hsqa : (Real.sqrt a) ^ 2 = a := Real.sq_sqrt (le_of_lt ha)
  have hbound := gap3 a x ha hx hrec n
  have hsq : a ≤ x (n + 1) * x (n + 1) := by
    nlinarith [Real.sqrt_nonneg a]
  have hdiv : a / x (n + 1) ≤ x (n + 1) :=
    (div_le_iff₀ (hx (n + 1))).2 hsq
  linarith

/-- Exercise 149, gap 6; decrease starts after the first Newton step. -/
theorem gap6 (a : ℝ) (x : ℕ → ℝ)
    (ha : 0 < a) (hx : ∀ n, 0 < x n) (hrec : newtonRecurrence a x) :
    ∀ n, x (n + 2) - x (n + 1) ≤ 0 := by
  intro n
  rw [gap4 a x hrec (n + 1)]
  simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
    gap5 a x ha hx hrec n

/-- Exercise 149, gap 7; formalize monotonicity of the shifted tail. -/
theorem gap7 (a : ℝ) (x : ℕ → ℝ)
    (ha : 0 < a) (hx : ∀ n, 0 < x n) (hrec : newtonRecurrence a x) :
    Antitone (fun n => x (n + 1)) := by
  apply antitone_nat_of_succ_le
  intro n
  have h := gap6 a x ha hx hrec n
  simpa only [Nat.succ_eq_add_one, Nat.add_assoc] using sub_nonpos.mp h

/-- Exercise 149, gap 8; the shifted tail is bounded below. -/
theorem gap8 (a : ℝ) (x : ℕ → ℝ)
    (ha : 0 < a) (hx : ∀ n, 0 < x n) (hrec : newtonRecurrence a x) :
    BddBelow (Set.range (fun n => x (n + 1))) := by
  refine ⟨Real.sqrt a, ?_⟩
  rintro _ ⟨n, rfl⟩
  exact gap3 a x ha hx hrec n

/-- Exercise 149, gap 9. -/
theorem gap9 (a : ℝ) (x : ℕ → ℝ)
    (ha : 0 < a) (hx : ∀ n, 0 < x n) (hrec : newtonRecurrence a x) :
    ProofGap.ConvergentSeq x := by
  refine ⟨sInf (Set.range (fun n => x (n + 1))), ?_⟩
  apply (Filter.tendsto_add_atTop_iff_nat 1).1
  exact tendsto_atTop_ciInf
    (gap7 a x ha hx hrec) (gap8 a x ha hx hrec)

/-- Exercise 149, gap 10. -/
theorem gap10 (a l : ℝ) (x : ℕ → ℝ)
    (ha : 0 < a) (hbound : ∀ n, x (n + 1) ≥ Real.sqrt a)
    (hl : Tendsto x atTop (𝓝 l)) :
    l ≥ Real.sqrt a := by
  have hshift : Tendsto (fun n => x (n + 1)) atTop (𝓝 l) :=
    (Filter.tendsto_add_atTop_iff_nat 1).2 hl
  exact ge_of_tendsto hshift (Filter.Eventually.of_forall hbound)

/-- Exercise 149, gap 11. -/
theorem gap11 (a : ℝ) (ha : 0 < a) : Real.sqrt a > 0 := by
  exact Real.sqrt_pos.2 ha

/-- Exercise 149, gap 12. -/
theorem gap12 (a l : ℝ) (ha : 0 < a)
    (hlower : l ≥ Real.sqrt a) : 0 < l := by
  exact lt_of_lt_of_le (gap11 a ha) hlower

/-- Exercise 149, gap 13; take limits in the recurrence. -/
theorem gap13 (a l : ℝ) (x : ℕ → ℝ)
    (hl0 : 0 < l) (hrec : newtonRecurrence a x)
    (hl : Tendsto x atTop (𝓝 l)) :
    l = (l + a / l) / 2 := by
  have hshift : Tendsto (fun n => x (n + 1)) atTop (𝓝 l) :=
    (Filter.tendsto_add_atTop_iff_nat 1).2 hl
  have hrhs : Tendsto (fun n => (x n + a / x n) / 2) atTop
      (𝓝 ((l + a / l) / 2)) :=
    (hl.add (tendsto_const_nhds.div hl (ne_of_gt hl0))).div_const 2
  have hshift' : Tendsto (fun n => x (n + 1)) atTop
      (𝓝 ((l + a / l) / 2)) :=
    hrhs.congr' (Filter.Eventually.of_forall fun n => (hrec n).symm)
  exact tendsto_nhds_unique hshift hshift'

/-- Exercise 149, gap 14; positivity selects the positive root. -/
theorem gap14 (a l : ℝ) (ha : 0 < a) (hl0 : 0 < l)
    (heq : l = (l + a / l) / 2) :
    l = Real.sqrt a := by
  have hlne : l ≠ 0 := ne_of_gt hl0
  have hsq : l ^ 2 = a := by
    field_simp [hlne] at heq
    nlinarith
  have hsqa : (Real.sqrt a) ^ 2 = a := Real.sq_sqrt (le_of_lt ha)
  nlinarith [Real.sqrt_nonneg a]

/-- Exercise 149, gap 15. -/
theorem gap15 (a : ℝ) (x : ℕ → ℝ)
    (ha : 0 < a) (hx : ∀ n, 0 < x n) (hrec : newtonRecurrence a x) :
    Tendsto x atTop (𝓝 (Real.sqrt a)) := by
  obtain ⟨l, hl⟩ := gap9 a x ha hx hrec
  have hlower : l ≥ Real.sqrt a :=
    gap10 a l x ha (gap3 a x ha hx hrec) hl
  have hl0 : 0 < l := gap12 a l ha hlower
  have heq : l = (l + a / l) / 2 := gap13 a l x hl0 hrec hl
  have hlsqrt : l = Real.sqrt a := gap14 a l ha hl0 heq
  simpa [hlsqrt] using hl

/-- Exercise 149, gap 16. -/
theorem gap16 (a : ℝ) (x : ℕ → ℝ)
    (ha : 0 < a) (hx : ∀ n, 0 < x n) (hrec : newtonRecurrence a x) :
    Tendsto x atTop (𝓝 (Real.sqrt a)) := by
  exact gap15 a x ha hx hrec

end

end ProofGap.Exercise149
