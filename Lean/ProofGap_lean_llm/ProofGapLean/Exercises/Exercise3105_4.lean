import ProofGapLean.Prelude.Discrete
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise3105_4

noncomputable section

/-- Exercise 3105_4, gap 1; the recurrence first applies at `n=2`. -/
theorem gap1 (Gamma : ℝ → ℝ)
    (hrec : ∀ x : ℝ, 0 < x → Gamma (x + 1) = x * Gamma x) :
    ∀ n : ℕ, 2 ≤ n →
      Gamma n = (n - 1 : ℕ) * Gamma (n - 1) := by
  intro n hn
  have hn1 : 1 ≤ n := by omega
  have hnsub : 0 < n - 1 := by omega
  have h := hrec ((n - 1 : ℕ) : ℝ) (Nat.cast_pos.mpr hnsub)
  simpa [Nat.cast_sub hn1] using h

/-- Exercise 3105_4, gap 2; two recurrence steps require `n≥3`. -/
theorem gap2 (Gamma : ℝ → ℝ)
    (hrec : ∀ x : ℝ, 0 < x → Gamma (x + 1) = x * Gamma x) :
    ∀ n : ℕ, 3 ≤ n →
      Gamma n =
        (n - 1 : ℕ) * (n - 2 : ℕ) * Gamma (n - 2) := by
  intro n hn
  have hfirst := gap1 Gamma hrec n (by omega)
  have hcast2 : ((n - 2 : ℕ) : ℝ) = (n : ℝ) - 2 := by
    rw [Nat.cast_sub (by omega : 2 ≤ n)]
    norm_num
  have hx : 0 < (n : ℝ) - 2 := by
    rw [← hcast2]
    exact Nat.cast_pos.mpr (by omega)
  have hsecond :
      Gamma ((n : ℝ) - 1) =
        ((n - 2 : ℕ) : ℝ) * Gamma ((n : ℝ) - 2) := by
    calc
      Gamma ((n : ℝ) - 1) =
          Gamma (((n : ℝ) - 2) + 1) := by
            congr 1
            ring
      _ = ((n : ℝ) - 2) * Gamma ((n : ℝ) - 2) :=
        hrec ((n : ℝ) - 2) hx
      _ = ((n - 2 : ℕ) : ℝ) * Gamma ((n : ℝ) - 2) := by
        rw [hcast2]
  calc
    Gamma n =
        ((n - 1 : ℕ) : ℝ) * Gamma ((n : ℝ) - 1) := hfirst
    _ = ((n - 1 : ℕ) : ℝ) *
        (((n - 2 : ℕ) : ℝ) * Gamma ((n : ℝ) - 2)) := by
      rw [hsecond]
    _ = ((n - 1 : ℕ) : ℝ) * ((n - 2 : ℕ) : ℝ) *
        Gamma ((n : ℝ) - 2) := by
      ring

/--
Exercise 3105_4, gap 3; replace the ellipsis by the exact
finite recurrence chain ending at `Gamma 1`.
-/
theorem gap3 (Gamma : ℝ → ℝ)
    (hrec : ∀ x : ℝ, 0 < x → Gamma (x + 1) = x * Gamma x) :
    ∀ n : ℕ, 1 ≤ n →
      Gamma n = (Nat.factorial (n - 1) : ℝ) * Gamma 1 := by
  intro n hn
  have h : ∀ k : ℕ,
      Gamma ((k : ℝ) + 1) =
        (Nat.factorial k : ℝ) * Gamma 1 := by
    intro k
    induction k with
    | zero => norm_num
    | succ k ih =>
        have hstep :
            Gamma (((Nat.succ k : ℕ) : ℝ) + 1) =
              ((Nat.succ k : ℕ) : ℝ) *
                Gamma ((Nat.succ k : ℕ) : ℝ) :=
          hrec ((Nat.succ k : ℕ) : ℝ)
            (Nat.cast_pos.mpr (Nat.succ_pos k))
        have ih' :
            Gamma ((Nat.succ k : ℕ) : ℝ) =
              (Nat.factorial k : ℝ) * Gamma 1 := by
          simpa only [Nat.cast_succ] using ih
        calc
          Gamma (((Nat.succ k : ℕ) : ℝ) + 1) =
              ((Nat.succ k : ℕ) : ℝ) *
                Gamma ((Nat.succ k : ℕ) : ℝ) := hstep
          _ = (Nat.factorial (Nat.succ k) : ℝ) * Gamma 1 := by
            rw [ih', Nat.factorial_succ, Nat.cast_mul]
            ring
  have hcast : (((n - 1 : ℕ) : ℝ) + 1) = (n : ℝ) := by
    rw [Nat.cast_sub hn]
    norm_num
  have hs := h (n - 1)
  rw [hcast] at hs
  exact hs

/-- Exercise 3105_4, gap 4; the terminal value `Gamma 1 = 1` is explicit. -/
theorem gap4 (Gamma : ℝ → ℝ)
    (hrec : ∀ x : ℝ, 0 < x → Gamma (x + 1) = x * Gamma x)
    (hGammaOne : Gamma 1 = 1) :
    ∀ n : ℕ, 1 ≤ n →
      Gamma n = (Nat.factorial (n - 1) : ℝ) := by
  intro n hn
  simpa [hGammaOne] using gap3 Gamma hrec n hn

end

end ProofGap.Exercise3105_4
