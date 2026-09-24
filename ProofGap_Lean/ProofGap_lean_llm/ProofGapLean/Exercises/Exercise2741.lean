import ProofGapLean.Prelude.Analysis
import Mathlib.Order.Filter.AtTopBot.Defs

namespace ProofGap.Exercise2741

noncomputable section

open Filter

def UniformlyConvergesOn
    (f : ℕ → ℝ → ℝ) (F : ℝ → ℝ) (X : Set ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ N : ℕ, ∀ n : ℕ, N < n → ∀ x ∈ X, |f n x - F x| < ε

def errorSet
    (f : ℕ → ℝ → ℝ) (F : ℝ → ℝ) (X : Set ℝ) (n : ℕ) : Set ℝ :=
  {r : ℝ | ∃ x ∈ X, r = |f n x - F x|}

def uniformError
    (f : ℕ → ℝ → ℝ) (F : ℝ → ℝ) (X : Set ℝ) (n : ℕ) : ℝ :=
  sSup (errorSet f F X n)

theorem gap1 (f : ℕ → ℝ → ℝ) (F : ℝ → ℝ) (X : Set ℝ)
    (h : UniformlyConvergesOn f F X) :
    ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, ∀ n : ℕ, N < n → ∀ x ∈ X, |f n x - F x| < ε := by
  exact h

theorem gap2 (f : ℕ → ℝ → ℝ) (F : ℝ → ℝ) (X : Set ℝ)
    (h : UniformlyConvergesOn f F X) :
    ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, ∀ n : ℕ, N < n → ∀ x ∈ X, |f n x - F x| < ε := by
  exact gap1 f F X h

theorem gap3 (f : ℕ → ℝ → ℝ) (F : ℝ → ℝ) (X : Set ℝ)
    (hne : X.Nonempty) (hb : ∀ n, BddAbove (errorSet f F X n))
    (h : UniformlyConvergesOn f F X) :
    ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, ∀ n : ℕ, N < n → uniformError f F X n ≤ ε := by
  intro ε hε
  obtain ⟨N, hN⟩ := h ε hε
  refine ⟨N, ?_⟩
  intro n hn
  unfold uniformError
  apply csSup_le
  · rcases hne with ⟨x, hx⟩
    exact ⟨|f n x - F x|, x, hx, rfl⟩
  · intro r hr
    rcases hr with ⟨x, hx, rfl⟩
    exact le_of_lt (hN n hn x hx)

theorem gap4 (f : ℕ → ℝ → ℝ) (F : ℝ → ℝ) (X : Set ℝ)
    (hne : X.Nonempty) (hb : ∀ n, BddAbove (errorSet f F X n))
    (h : UniformlyConvergesOn f F X) :
    Tendsto (uniformError f F X) atTop (nhds 0) := by
  obtain ⟨x, hx⟩ := hne
  apply tendsto_order.2
  constructor
  · intro a ha
    refine Filter.Eventually.of_forall ?_
    intro n
    have hmem : |f n x - F x| ∈ errorSet f F X n := ⟨x, hx, rfl⟩
    have hle : |f n x - F x| ≤ uniformError f F X n := by
      unfold uniformError
      exact le_csSup (hb n) hmem
    exact lt_of_lt_of_le ha (le_trans (abs_nonneg _) hle)
  · intro b hb0
    obtain ⟨N, hN⟩ := gap3 f F X ⟨x, hx⟩ hb h (b / 2) (half_pos hb0)
    filter_upwards [eventually_gt_atTop N] with n hn
    exact lt_of_le_of_lt (hN n hn) (half_lt_self hb0)

theorem gap5 (f : ℕ → ℝ → ℝ) (F : ℝ → ℝ) (X : Set ℝ)
    (hne : X.Nonempty) (hb : ∀ n, BddAbove (errorSet f F X n))
    (h : UniformlyConvergesOn f F X) :
    Tendsto (uniformError f F X) atTop (nhds 0) := by
  exact gap4 f F X hne hb h

theorem gap6 (f : ℕ → ℝ → ℝ) (F : ℝ → ℝ) (X : Set ℝ)
    (h : Tendsto (uniformError f F X) atTop (nhds 0)) :
    ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, ∀ n : ℕ, N < n → uniformError f F X n < ε := by
  intro ε hε
  have hev : ∀ᶠ n : ℕ in atTop, uniformError f F X n < ε :=
    (tendsto_order.1 h).2 ε hε
  rcases (eventually_atTop.1 hev) with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn
  exact hN n (Nat.le_of_lt hn)

theorem gap7 (f : ℕ → ℝ → ℝ) (F : ℝ → ℝ) (X : Set ℝ)
    (h : Tendsto (uniformError f F X) atTop (nhds 0)) :
    ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, ∀ n : ℕ, N < n → uniformError f F X n < ε := by
  exact gap6 f F X h

theorem gap8 (f : ℕ → ℝ → ℝ) (F : ℝ → ℝ) (X : Set ℝ)
    (hne : X.Nonempty) (hb : ∀ n, BddAbove (errorSet f F X n))
    (h : Tendsto (uniformError f F X) atTop (nhds 0)) :
    ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, ∀ n : ℕ, N < n → ∀ x ∈ X, |f n x - F x| < ε := by
  intro ε hε
  obtain ⟨N, hN⟩ := gap6 f F X h ε hε
  refine ⟨N, ?_⟩
  intro n hn x hx
  have hmem : |f n x - F x| ∈ errorSet f F X n := ⟨x, hx, rfl⟩
  have hle : |f n x - F x| ≤ uniformError f F X n := by
    unfold uniformError
    exact le_csSup (hb n) hmem
  exact lt_of_le_of_lt hle (hN n hn)

theorem gap9 (f : ℕ → ℝ → ℝ) (F : ℝ → ℝ) (X : Set ℝ)
    (hne : X.Nonempty) (hb : ∀ n, BddAbove (errorSet f F X n))
    (h : Tendsto (uniformError f F X) atTop (nhds 0)) :
    UniformlyConvergesOn f F X := by
  exact gap8 f F X hne hb h

theorem gap10 (f : ℕ → ℝ → ℝ) (F : ℝ → ℝ) (X : Set ℝ)
    (hne : X.Nonempty) (hb : ∀ n, BddAbove (errorSet f F X n))
    (h : Tendsto (uniformError f F X) atTop (nhds 0)) :
    UniformlyConvergesOn f F X := by
  exact gap9 f F X hne hb h

theorem gap11 (f : ℕ → ℝ → ℝ) (F : ℝ → ℝ) (X : Set ℝ)
    (hne : X.Nonempty) (hb : ∀ n, BddAbove (errorSet f F X n)) :
    UniformlyConvergesOn f F X ↔
      Tendsto (uniformError f F X) atTop (nhds 0) := by
  constructor
  · intro h
    exact gap4 f F X hne hb h
  · intro h
    exact gap9 f F X hne hb h

theorem gap12 (f : ℕ → ℝ → ℝ) (F : ℝ → ℝ) (X : Set ℝ)
    (hne : X.Nonempty) (hb : ∀ n, BddAbove (errorSet f F X n)) :
    UniformlyConvergesOn f F X ↔
      Tendsto (uniformError f F X) atTop (nhds 0) := by
  exact gap11 f F X hne hb

end

end ProofGap.Exercise2741
