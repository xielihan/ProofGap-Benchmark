import ProofGapLean.Prelude.Analysis
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

namespace ProofGap.Exercise744_2

noncomputable section

def signFn (x : ℝ) : ℝ := Real.sign x
def cubicLike (x : ℝ) : ℝ := x * (1 - x ^ 2)
def signComposition (x : ℝ) : ℝ :=
  if x < -1 then 1
  else if x = -1 then 0
  else if x < 0 then -1
  else if x = 0 then 0
  else if x < 1 then 1
  else if x = 1 then 0
  else -1

/-- Exercise 744_2, gap 1; add the two intervals on which
`x(1-x²)` is positive. -/
theorem gap1 :
    ∀ x, (x < -1 ∨ (0 < x ∧ x < 1)) → 0 < cubicLike x := by
  intro x hx
  unfold cubicLike
  rcases hx with hx | hx
  · have hx0 : x < 0 := by linarith
    have hfac : 1 - x ^ 2 < 0 := by
      calc
        1 - x ^ 2 = (1 - x) * (1 + x) := by ring
        _ < 0 := mul_neg_of_pos_of_neg (by linarith) (by linarith)
    exact mul_pos_of_neg_of_neg hx0 hfac
  · have hfac : 0 < 1 - x ^ 2 := by
      calc
        0 < (1 - x) * (1 + x) := mul_pos (by linarith) (by linarith)
        _ = 1 - x ^ 2 := by ring
    exact mul_pos hx.1 hfac

/-- Exercise 744_2, gap 2; add the two intervals on which
`x(1-x²)` is negative. -/
theorem gap2 :
    ∀ x, ((-1 < x ∧ x < 0) ∨ 1 < x) → cubicLike x < 0 := by
  intro x hx
  unfold cubicLike
  rcases hx with hx | hx
  · have hfac : 0 < 1 - x ^ 2 := by
      calc
        0 < (1 - x) * (1 + x) := mul_pos (by linarith) (by linarith)
        _ = 1 - x ^ 2 := by ring
    exact mul_neg_of_neg_of_pos hx.2 hfac
  · have hx0 : 0 < x := by linarith
    have hfac : 1 - x ^ 2 < 0 := by
      calc
        1 - x ^ 2 = (1 - x) * (1 + x) := by ring
        _ < 0 := mul_neg_of_neg_of_pos (by linarith) (by linarith)
    exact mul_neg_of_pos_of_neg hx0 hfac

/-- Exercise 744_2, gap 3. -/
theorem gap3 : ∀ x, signFn (cubicLike x) = signComposition x := by
  intro x
  by_cases hltm1 : x < -1
  · have hc : 0 < cubicLike x := gap1 x (Or.inl hltm1)
    have hs : signFn (cubicLike x) = 1 := by
      simpa [signFn] using Real.sign_of_pos hc
    simpa [signComposition, hltm1] using hs
  by_cases heqm1 : x = -1
  · subst x
    norm_num [signFn, cubicLike, signComposition]
  by_cases hlt0 : x < 0
  · have hm1lt : -1 < x :=
      lt_of_le_of_ne (le_of_not_gt hltm1) (Ne.symm heqm1)
    have hc : cubicLike x < 0 := gap2 x (Or.inl ⟨hm1lt, hlt0⟩)
    have hs : signFn (cubicLike x) = -1 := by
      simpa [signFn] using Real.sign_of_neg hc
    simpa [signComposition, hltm1, heqm1, hlt0] using hs
  by_cases heq0 : x = 0
  · subst x
    norm_num [signFn, cubicLike, signComposition]
  by_cases hlt1 : x < 1
  · have h0lt : 0 < x :=
      lt_of_le_of_ne (le_of_not_gt hlt0) (Ne.symm heq0)
    have hc : 0 < cubicLike x := gap1 x (Or.inr ⟨h0lt, hlt1⟩)
    have hs : signFn (cubicLike x) = 1 := by
      simpa [signFn] using Real.sign_of_pos hc
    simpa [signComposition, hltm1, heqm1, hlt0, heq0, hlt1] using hs
  by_cases heq1 : x = 1
  · subst x
    norm_num [signFn, cubicLike, signComposition]
  · have h1lt : 1 < x :=
      lt_of_le_of_ne (le_of_not_gt hlt1) (Ne.symm heq1)
    have hc : cubicLike x < 0 := gap2 x (Or.inr h1lt)
    have hs : signFn (cubicLike x) = -1 := by
      simpa [signFn] using Real.sign_of_neg hc
    simpa [signComposition, hltm1, heqm1, hlt0, heq0, hlt1, heq1] using hs

/-- Exercise 744_2, gap 4. -/
theorem gap4 : ¬ContinuousAt (fun x => signFn (cubicLike x)) (-1) := by
  intro h
  rw [Metric.continuousAt_iff] at h
  obtain ⟨δ, hδ, hmap⟩ := h 1 (by norm_num)
  let y : ℝ := -1 - δ / 2
  have hy : y < -1 := by
    dsimp [y]
    linarith
  have hydist : dist y (-1 : ℝ) < δ := by
    have heq : y - (-1 : ℝ) = -(δ / 2) := by
      dsimp [y]
      ring
    have hhalf : 0 < δ / 2 := by linarith
    rw [Real.dist_eq, heq, abs_neg, abs_of_pos hhalf]
    linarith
  have hout := hmap (x := y) hydist
  have hyval : signFn (cubicLike y) = 1 := by
    rw [gap3 y]
    simp [signComposition, hy]
  have haval : signFn (cubicLike (-1 : ℝ)) = 0 := by
    rw [gap3 (-1 : ℝ)]
    norm_num [signComposition]
  rw [hyval, haval] at hout
  norm_num [Real.dist_eq] at hout

/-- Exercise 744_2, gap 5. -/
theorem gap5 : ¬ContinuousAt (fun x => signFn (cubicLike x)) 0 := by
  intro h
  rw [Metric.continuousAt_iff] at h
  obtain ⟨δ, hδ, hmap⟩ := h 1 (by norm_num)
  let d : ℝ := min δ 1
  have hd : 0 < d := by
    dsimp [d]
    exact lt_min hδ (by norm_num)
  have hdδ : d ≤ δ := by
    dsimp [d]
    exact min_le_left δ 1
  have hd1 : d ≤ 1 := by
    dsimp [d]
    exact min_le_right δ 1
  let y : ℝ := d / 2
  have hypos : 0 < y := by
    dsimp [y]
    linarith
  have hylt : y < 1 := by
    dsimp [y]
    linarith
  have hydist : dist y (0 : ℝ) < δ := by
    have heq : y - (0 : ℝ) = d / 2 := by
      dsimp [y]
      ring
    have hhalf : 0 < d / 2 := by linarith
    rw [Real.dist_eq, heq, abs_of_pos hhalf]
    linarith
  have hout := hmap (x := y) hydist
  have hnm1 : ¬y < -1 := by linarith
  have hnem1 : y ≠ -1 := by linarith
  have hn0 : ¬y < 0 := by linarith
  have hne0 : y ≠ 0 := ne_of_gt hypos
  have hyval : signFn (cubicLike y) = 1 := by
    rw [gap3 y]
    simp [signComposition, hnm1, hnem1, hn0, hne0, hylt]
  have h0val : signFn (cubicLike (0 : ℝ)) = 0 := by
    rw [gap3 (0 : ℝ)]
    norm_num [signComposition]
  rw [hyval, h0val] at hout
  norm_num [Real.dist_eq] at hout

/-- Exercise 744_2, gap 6. -/
theorem gap6 : ¬ContinuousAt (fun x => signFn (cubicLike x)) 1 := by
  intro h
  rw [Metric.continuousAt_iff] at h
  obtain ⟨δ, hδ, hmap⟩ := h 1 (by norm_num)
  let d : ℝ := min δ 1
  have hd : 0 < d := by
    dsimp [d]
    exact lt_min hδ (by norm_num)
  have hdδ : d ≤ δ := by
    dsimp [d]
    exact min_le_left δ 1
  let y : ℝ := 1 + d / 2
  have hygt : 1 < y := by
    dsimp [y]
    linarith
  have hydist : dist y (1 : ℝ) < δ := by
    have heq : y - (1 : ℝ) = d / 2 := by
      dsimp [y]
      ring
    have hhalf : 0 < d / 2 := by linarith
    rw [Real.dist_eq, heq, abs_of_pos hhalf]
    linarith
  have hout := hmap (x := y) hydist
  have hnm1 : ¬y < -1 := by linarith
  have hnem1 : y ≠ -1 := by linarith
  have hn0 : ¬y < 0 := by linarith
  have hne0 : y ≠ 0 := by linarith
  have hn1 : ¬y < 1 := by linarith
  have hne1 : y ≠ 1 := by linarith
  have hyval : signFn (cubicLike y) = -1 := by
    rw [gap3 y]
    simp [signComposition, hnm1, hnem1, hn0, hne0, hn1, hne1]
  have h1val : signFn (cubicLike (1 : ℝ)) = 0 := by
    rw [gap3 (1 : ℝ)]
    norm_num [signComposition]
  rw [hyval, h1val] at hout
  norm_num [Real.dist_eq] at hout

/-- Exercise 744_2, gap 7. -/
theorem gap7 : ∀ x, cubicLike (signFn x) = 0 := by
  intro x
  rcases lt_trichotomy x 0 with hx | hx | hx
  · have hs : signFn x = -1 := by
      simpa [signFn] using Real.sign_of_neg hx
    rw [hs]
    norm_num [cubicLike]
  · subst x
    norm_num [signFn, cubicLike]
  · have hs : signFn x = 1 := by
      simpa [signFn] using Real.sign_of_pos hx
    rw [hs]
    norm_num [cubicLike]

/-- Exercise 744_2, gap 8. -/
theorem gap8 : Continuous (fun x => cubicLike (signFn x)) := by
  have hzero :
      (fun x : ℝ => cubicLike (signFn x)) = (fun _ : ℝ => (0 : ℝ)) := by
    funext x
    exact gap7 x
  rw [hzero]
  exact continuous_const

end

end ProofGap.Exercise744_2
