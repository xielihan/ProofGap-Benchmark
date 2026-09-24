import ProofGapLean.Prelude.Sequences
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

namespace ProofGap.Exercise820

noncomputable section

def diff (f : ℝ → ℝ) (h x : ℝ) : ℝ := f (x + h) - f x
def HasZeroSecondDifferences (f : ℝ → ℝ) : Prop :=
  ∀ x h₁ h₂, f (x + h₁ + h₂) - f (x + h₂) = f (x + h₁) - f x

theorem gap1 (f : ℝ → ℝ) (h : HasZeroSecondDifferences f) (x Δ₁ Δ₂ : ℝ) :
    f (x + Δ₁ + Δ₂) - f (x + Δ₂) = f (x + Δ₁) - f x := by
  exact h x Δ₁ Δ₂
theorem gap2 (f : ℝ → ℝ) (h : HasZeroSecondDifferences f) (Δ₁ Δ₂ : ℝ) :
    f (Δ₁ + Δ₂) - f Δ₂ = f Δ₁ - f 0 := by
  simpa using h 0 Δ₁ Δ₂
theorem gap3 (f : ℝ → ℝ) (h : HasZeroSecondDifferences f) (n : ℕ) (Δ₁ : ℝ) :
    f ((n + 1) * Δ₁) - f (n * Δ₁) = f Δ₁ - f 0 := by
  simpa [Nat.cast_add, Nat.cast_one, add_mul, add_comm] using
    (gap2 f h Δ₁ ((n : ℝ) * Δ₁))
theorem gap4 (f : ℝ → ℝ) (h : HasZeroSecondDifferences f) (n : ℕ) (Δ₁ : ℝ) :
    f ((n + 1) * Δ₁) - f 0 = (n + 1 : ℝ) * (f Δ₁ - f 0) := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hs := gap3 f h (n + 1) Δ₁
      simp only [Nat.cast_add, Nat.cast_one, add_mul, one_mul] at ih hs ⊢
      linarith
theorem gap5 (f : ℝ → ℝ) (h : HasZeroSecondDifferences f) (n : ℕ)
    (hn : 0 < n) (Δ₁ : ℝ) :
    f Δ₁ - f 0 = 1 / (n : ℝ) * (f (n * Δ₁) - f 0) := by
  have hg := gap4 f h (n - 1) Δ₁
  have hpred : n - 1 + 1 = n := Nat.sub_add_cancel hn
  have hcast : ((n - 1 : ℕ) : ℝ) + 1 = (n : ℝ) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      congrArg (fun k : ℕ => (k : ℝ)) hpred
  rw [hcast] at hg
  have hn0 : (n : ℝ) ≠ 0 := by
    simp [Nat.ne_of_gt hn]
  rw [hg]
  field_simp [hn0]
theorem gap6 (f : ℝ → ℝ) (h : HasZeroSecondDifferences f) (m : ℤ)
    (n : ℕ) (hn : 0 < n) :
    f ((m : ℝ) / n) - f 0 = (m : ℝ) / n * (f 1 - f 0) := by
  have hnat (k : ℕ) :
      f (k : ℝ) - f 0 = (k : ℝ) * (f 1 - f 0) := by
    cases k with
    | zero => simp
    | succ k =>
        simpa [Nat.cast_add, Nat.cast_one] using (gap4 f h k 1)
  have hm : f (m : ℝ) - f 0 = (m : ℝ) * (f 1 - f 0) := by
    cases m with
    | ofNat k =>
        exact hnat k
    | negSucc k =>
        have hp :
            f (((k + 1 : ℕ) : ℝ)) - f 0 =
              (((k + 1 : ℕ) : ℝ)) * (f 1 - f 0) :=
          hnat (k + 1)
        have hz :
            f 0 - f (((k + 1 : ℕ) : ℝ)) =
              f (-(((k + 1 : ℕ) : ℝ))) - f 0 := by
          simpa using
            (gap2 f h (-(((k + 1 : ℕ) : ℝ))) (((k + 1 : ℕ) : ℝ)))
        have hneg :
            f (-(((k + 1 : ℕ) : ℝ))) - f 0 =
              (-(((k + 1 : ℕ) : ℝ))) * (f 1 - f 0) := by
          linarith
        simpa using hneg
  have hn0 : (n : ℝ) ≠ 0 := by
    simp [Nat.ne_of_gt hn]
  have hmul :
      (n : ℝ) * ((m : ℝ) / (n : ℝ)) = (m : ℝ) := by
    field_simp [hn0]
  have hs := gap5 f h n hn ((m : ℝ) / (n : ℝ))
  rw [hmul, hm] at hs
  calc
    f ((m : ℝ) / n) - f 0 =
        1 / (n : ℝ) * ((m : ℝ) * (f 1 - f 0)) := hs
    _ = (m : ℝ) / n * (f 1 - f 0) := by
      field_simp [hn0]
theorem gap7 (f : ℝ → ℝ) (h : HasZeroSecondDifferences f) (m : ℤ)
    (n : ℕ) (hn : 0 < n) :
    f ((m : ℝ) / n) = (f 1 - f 0) * ((m : ℝ) / n) + f 0 := by
  have hg := gap6 f h m n hn
  calc
    f ((m : ℝ) / n) =
        (m : ℝ) / n * (f 1 - f 0) + f 0 := sub_eq_iff_eq_add.mp hg
    _ = (f 1 - f 0) * ((m : ℝ) / n) + f 0 := by
      rw [mul_comm]
theorem gap8 (f : ℝ → ℝ) (h : HasZeroSecondDifferences f) (q : ℚ) :
    f q = (f 1 - f 0) * q + f 0 := by
  simpa [Rat.cast_def] using
    (gap7 f h q.num q.den q.den_pos)
theorem gap9 (x : ℝ) :
    ∃ q : ℕ → ℚ, Filter.Tendsto (fun n => (q n : ℝ)) Filter.atTop (nhds x) := by
  have hd : DenseRange ((↑) : ℚ → ℝ) := by
    apply Metric.dense_iff.2
    intro y ε hε
    obtain ⟨q, hql, hqu⟩ :=
      exists_rat_btwn (show y - ε < y + ε by linarith)
    refine ⟨(q : ℝ), ?_, ?_⟩
    · change dist (q : ℝ) y < ε
      rw [Real.dist_eq]
      exact abs_lt.2 ⟨by linarith, by linarith⟩
    · exact ⟨q, rfl⟩
  rcases mem_closure_iff_seq_limit.mp (hd x) with ⟨u, hu, hux⟩
  choose q hq using hu
  refine ⟨q, ?_⟩
  simpa only [hq] using hux
theorem gap10 (x : ℝ) :
    ∃ q : ℕ → ℚ, Filter.Tendsto (fun n => (q n : ℝ)) Filter.atTop (nhds x) := by
  exact gap9 x
theorem gap11 (f : ℝ → ℝ) (hf : Continuous f) (x : ℝ)
    (q : ℕ → ℚ) (hq : Filter.Tendsto (fun n => (q n : ℝ)) Filter.atTop (nhds x)) :
    Filter.Tendsto (fun n => f (q n)) Filter.atTop (nhds (f x)) := by
  simpa only [Function.comp_apply] using
    hf.continuousAt.tendsto.comp hq
theorem gap12 (f : ℝ → ℝ) (q : ℕ → ℚ) (a b x : ℝ)
    (h : ∀ r : ℚ, f r = a * r + b) :
    (fun n => f (q n)) = (fun n => a * (q n : ℝ) + b) := by
  funext n
  exact h (q n)
theorem gap13 (q : ℕ → ℚ) (a b x : ℝ)
    (hq : Filter.Tendsto (fun n => (q n : ℝ)) Filter.atTop (nhds x)) :
    Filter.Tendsto (fun n => a * (q n : ℝ) + b) Filter.atTop (nhds (a * x + b)) := by
  have ha :
      Filter.Tendsto (fun _ : ℕ => a) Filter.atTop (nhds a) :=
    tendsto_const_nhds
  have hb :
      Filter.Tendsto (fun _ : ℕ => b) Filter.atTop (nhds b) :=
    tendsto_const_nhds
  exact (ha.mul hq).add hb
theorem gap14 (f : ℝ → ℝ) (q : ℕ → ℚ) (a b x : ℝ)
    (h : ∀ r : ℚ, f r = a * r + b)
    (hq : Filter.Tendsto (fun n => (q n : ℝ)) Filter.atTop (nhds x)) :
    Filter.Tendsto (fun n => f (q n)) Filter.atTop (nhds (a * x + b)) := by
  rw [gap12 f q a b x h]
  exact gap13 q a b x hq
theorem gap15 (f : ℝ → ℝ) (hf : Continuous f) (h : HasZeroSecondDifferences f)
    (x : ℝ) : f x = (f 1 - f 0) * x + f 0 := by
  rcases gap10 x with ⟨q, hq⟩
  have hfq := gap11 f hf x q hq
  have haq :=
    gap14 f q (f 1 - f 0) (f 0) x (gap8 f h) hq
  exact tendsto_nhds_unique hfq haq
theorem gap16 (f : ℝ → ℝ) (hf : Continuous f) (h : HasZeroSecondDifferences f)
    (x : ℝ) : f x = (f 1 - f 0) * x + f 0 := by
  exact gap15 f hf h x
theorem gap17 (f : ℝ → ℝ) (hf : Continuous f) (h : HasZeroSecondDifferences f) :
    ∃ a b : ℝ, ∀ x, f x = a * x + b := by
  refine ⟨f 1 - f 0, f 0, ?_⟩
  intro x
  exact gap16 f hf h x

end
end ProofGap.Exercise820
