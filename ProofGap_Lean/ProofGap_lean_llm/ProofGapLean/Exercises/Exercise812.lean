import ProofGapLean.Prelude.Analysis
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

namespace ProofGap.Exercise812

noncomputable section

variable (f : ℝ → ℝ)

def MultiplicativeCauchy : Prop := ∀ x y, f (x + y) = f x * f y

private theorem multiplicative_nat_mul_pos
    (f : ℝ → ℝ) (h : MultiplicativeCauchy f) (x : ℝ) :
    ∀ n : ℕ, 0 < n → f ((n : ℝ) * x) = (f x) ^ n := by
  intro n hn
  induction n with
  | zero => omega
  | succ n ih =>
      by_cases hn0 : n = 0
      · subst n
        simp
      · have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
        have harg : ((Nat.succ n : ℕ) : ℝ) * x = (n : ℝ) * x + x := by
          simp only [Nat.cast_succ]
          ring
        calc
          f ((Nat.succ n : ℕ) * x) = f ((n : ℝ) * x + x) := by rw [harg]
          _ = f ((n : ℝ) * x) * f x := h ((n : ℝ) * x) x
          _ = (f x) ^ n * f x := by rw [ih hnpos]
          _ = (f x) ^ (Nat.succ n) := by rw [pow_succ]

theorem gap1 (x : ℝ) : f x = f (x / 2 + x / 2) := by
  apply congrArg f
  ring
theorem gap2 (h : MultiplicativeCauchy f) (x : ℝ) :
    f (x / 2 + x / 2) = (f (x / 2)) ^ 2 := by
  simpa [pow_two] using h (x / 2) (x / 2)
theorem gap3 (h : MultiplicativeCauchy f) (x : ℝ) :
    f x = (f (x / 2)) ^ 2 := by
  calc
    f x = f (x / 2 + x / 2) := gap1 f x
    _ = (f (x / 2)) ^ 2 := gap2 f h x
theorem gap4 (h : MultiplicativeCauchy f) (x : ℝ) : 0 ≤ f x := by
  rw [gap3 f h x]
  exact sq_nonneg (f (x / 2))
theorem gap5 (h : MultiplicativeCauchy f) (h0 : ∃ x, f x ≠ 0) :
    ∃ x₀, 0 < f x₀ := by
  rcases h0 with ⟨x, hx⟩
  exact ⟨x, lt_of_le_of_ne (gap4 f h x) (Ne.symm hx)⟩
theorem gap6 (h : MultiplicativeCauchy f) (x₀ : ℝ) :
    f x₀ = f x₀ * f 0 := by
  simpa using h x₀ 0
theorem gap7 (h : MultiplicativeCauchy f) (h0 : ∃ x, f x ≠ 0) : f 0 = 1 := by
  rcases h0 with ⟨x, hx⟩
  have heq := gap6 f h x
  have hz : f x * (1 - f 0) = 0 := by
    nlinarith
  rcases mul_eq_zero.mp hz with hfx | hz
  · exact (hx hfx).elim
  · nlinarith
theorem gap8 (h : MultiplicativeCauchy f) (h0 : ∃ x, f x ≠ 0) : 1 = f 0 := by
  exact (gap7 f h h0).symm
theorem gap9 (h : MultiplicativeCauchy f) (x : ℝ) : f 0 = f x * f (-x) := by
  simpa using h x (-x)
theorem gap10 (h : MultiplicativeCauchy f) (h0 : ∃ x, f x ≠ 0) (x : ℝ) :
    1 = f x * f (-x) := by
  calc
    1 = f 0 := gap8 f h h0
    _ = f x * f (-x) := gap9 f h x
theorem gap11 (h : MultiplicativeCauchy f) (h0 : ∃ x, f x ≠ 0) (x : ℝ) :
    f x ≠ 0 := by
  intro hx
  have hp := gap10 f h h0 x
  rw [hx] at hp
  norm_num at hp
theorem gap12 (h : MultiplicativeCauchy f) (h0 : ∃ x, f x ≠ 0) (x : ℝ) :
    0 < f x := by
  exact lt_of_le_of_ne (gap4 f h x) (Ne.symm (gap11 f h h0 x))
theorem gap13 (h : MultiplicativeCauchy f) (x : ℝ) (m : ℕ) (hm : 0 < m) :
    f (m * x) = f ((m - 1) * x + x) := by
  apply congrArg f
  ring
theorem gap14 (h : MultiplicativeCauchy f) (x : ℝ) (m : ℕ) (hm : 0 < m) :
    f ((m - 1) * x + x) = f ((m - 1) * x) * f x := by
  exact h ((m - 1) * x) x
theorem gap15 (h : MultiplicativeCauchy f) (x : ℝ) (m : ℕ) (hm : 1 < m) :
    f ((m - 1) * x) * f x = f ((m - 2) * x) * f x * f x := by
  have harg : ((m : ℝ) - 1) * x = ((m : ℝ) - 2) * x + x := by
    ring
  calc
    f ((m - 1) * x) * f x = f (((m : ℝ) - 2) * x + x) * f x := by
      rw [harg]
    _ = (f (((m : ℝ) - 2) * x) * f x) * f x := by
      rw [h (((m : ℝ) - 2) * x) x]
theorem gap16 (h : MultiplicativeCauchy f) (x : ℝ) (m : ℕ) (hm : 1 < m) :
    f ((m - 2) * x) * f x * f x = f ((m - 2) * x) * (f x) ^ 2 := by
  ring
theorem gap17 (h : MultiplicativeCauchy f) (h0 : ∃ x, f x ≠ 0)
    (x : ℝ) (m : ℕ) :
    f (m * x) = (f x) ^ m := by
  cases m with
  | zero => simpa using gap7 f h h0
  | succ m =>
      exact multiplicative_nat_mul_pos f h x (m + 1) (Nat.succ_pos m)
theorem gap18 (h : MultiplicativeCauchy f) (h0 : ∃ x, f x ≠ 0)
    (x : ℝ) (m : ℕ) :
    f (m * x) = (f x) ^ m := by
  exact gap17 f h h0 x m
theorem gap19 (x : ℝ) (n : ℕ) (hn : 0 < n) :
    f x = f (n * (x / n)) := by
  have hn0 : n ≠ 0 := Nat.ne_of_gt hn
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn0
  apply congrArg f
  field_simp [hn']
theorem gap20 (h : MultiplicativeCauchy f) (h0 : ∃ x, f x ≠ 0)
    (x : ℝ) (n : ℕ) :
    f (n * (x / n)) = (f (x / n)) ^ n := by
  exact gap18 f h h0 (x / n) n
theorem gap21 (h : MultiplicativeCauchy f) (x : ℝ) (n : ℕ) (hn : 0 < n) :
    f x = (f (x / n)) ^ n := by
  calc
    f x = f (n * (x / n)) := gap19 f x n hn
    _ = (f (x / n)) ^ n := multiplicative_nat_mul_pos f h (x / n) n hn
theorem gap22 (h : MultiplicativeCauchy f) (h0 : ∃ x, f x ≠ 0)
    (x : ℝ) (n : ℕ) (hn : 0 < n) :
    f (x / n) = Real.rpow (f x) (1 / (n : ℝ)) := by
  have hy : 0 < f (x / n) := gap12 f h h0 (x / n)
  have hn0 : n ≠ 0 := Nat.ne_of_gt hn
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn0
  have hp := gap21 f h x n hn
  calc
    f (x / n) = Real.rpow (f (x / n)) 1 := by
      symm
      exact Real.rpow_one (f (x / n))
    _ = Real.rpow (f (x / n)) ((n : ℝ) * (1 / (n : ℝ))) := by
      congr 1
      field_simp [hn']
    _ = Real.rpow (Real.rpow (f (x / n)) (n : ℝ)) (1 / (n : ℝ)) := by
      change (f (x / n) ^ ((n : ℝ) * (1 / (n : ℝ)))) =
        ((f (x / n) ^ (n : ℝ)) ^ (1 / (n : ℝ)))
      exact Real.rpow_mul (le_of_lt hy) (n : ℝ) (1 / (n : ℝ))
    _ = Real.rpow ((f (x / n)) ^ n) (1 / (n : ℝ)) := by
      exact congrArg (fun z : ℝ => Real.rpow z (1 / (n : ℝ)))
        (Real.rpow_natCast (f (x / n)) n)
    _ = Real.rpow (f x) (1 / (n : ℝ)) := by
      rw [← hp]
theorem gap23 (h : MultiplicativeCauchy f) (h0 : ∃ x, f x ≠ 0)
    (x : ℝ) (m n : ℕ) (hn : 0 < n) :
    f ((m : ℝ) / n * x) = (f (x / n)) ^ m := by
  calc
    f ((m : ℝ) / n * x) = f ((m : ℝ) * (x / n)) := by
      apply congrArg f
      ring
    _ = (f (x / n)) ^ m := gap17 f h h0 (x / n) m
theorem gap24 (h : MultiplicativeCauchy f) (h0 : ∃ x, f x ≠ 0)
    (x : ℝ) (m n : ℕ) (hn : 0 < n) :
    (f (x / n)) ^ m = Real.rpow (f x) ((m : ℝ) / n) := by
  have hx : 0 < f x := gap12 f h h0 x
  rw [gap22 f h h0 x n hn]
  calc
    (Real.rpow (f x) (1 / (n : ℝ))) ^ m =
        Real.rpow (Real.rpow (f x) (1 / (n : ℝ))) (m : ℝ) := by
      exact (Real.rpow_natCast (Real.rpow (f x) (1 / (n : ℝ))) m).symm
    _ = Real.rpow (f x) ((1 / (n : ℝ)) * (m : ℝ)) := by
      simpa only using
        (Real.rpow_mul (le_of_lt hx) (1 / (n : ℝ)) (m : ℝ)).symm
    _ = Real.rpow (f x) ((m : ℝ) / n) := by
      congr 1
      ring_nf
theorem gap25 (h : MultiplicativeCauchy f) (h0 : ∃ x, f x ≠ 0)
    (x : ℝ) (m n : ℕ) (hn : 0 < n) :
    f ((m : ℝ) / n * x) = Real.rpow (f x) ((m : ℝ) / n) := by
  have hmul : f ((m : ℝ) * (x / n)) = (f (x / n)) ^ m := by
    cases m with
    | zero =>
        simpa using gap7 f h h0
    | succ m =>
        exact multiplicative_nat_mul_pos f h (x / n) (m + 1) (Nat.succ_pos m)
  calc
    f ((m : ℝ) / n * x) = f ((m : ℝ) * (x / n)) := by
      apply congrArg f
      ring
    _ = (f (x / n)) ^ m := hmul
    _ = Real.rpow (f x) ((m : ℝ) / n) := gap24 f h h0 x m n hn
theorem gap26 (h : MultiplicativeCauchy f) (h0 : ∃ x, f x ≠ 0)
    (x : ℝ) (m n : ℕ) (hn : 0 < n) :
    f (-((m : ℝ) / n) * x) = Real.rpow (f (-x)) ((m : ℝ) / n) := by
  convert gap25 f h h0 (-x) m n hn using 1 <;> ring
theorem gap27 (h : MultiplicativeCauchy f) (h0 : ∃ x, f x ≠ 0)
    (x : ℝ) (m n : ℕ) (hn : 0 < n) :
    Real.rpow (f (-x)) ((m : ℝ) / n) =
      Real.rpow (f x) (-((m : ℝ) / n)) := by
  have hxne : f x ≠ 0 := gap11 f h h0 x
  have hx : 0 < f x := gap12 f h h0 x
  have hinv : f (-x) = (f x)⁻¹ := by
    apply mul_left_cancel₀ hxne
    simpa [hxne] using (gap10 f h h0 x).symm
  rw [hinv]
  calc
    Real.rpow ((f x)⁻¹) ((m : ℝ) / n) =
        (Real.rpow (f x) ((m : ℝ) / n))⁻¹ := by
      exact Real.inv_rpow (le_of_lt hx) ((m : ℝ) / n)
    _ = Real.rpow (f x) (-((m : ℝ) / n)) := by
      exact (Real.rpow_neg (le_of_lt hx) ((m : ℝ) / n)).symm
theorem gap28 (h : MultiplicativeCauchy f) (h0 : ∃ x, f x ≠ 0)
    (x : ℝ) (m n : ℕ) (hn : 0 < n) :
    f (-((m : ℝ) / n) * x) = Real.rpow (f x) (-((m : ℝ) / n)) := by
  calc
    f (-((m : ℝ) / n) * x) = Real.rpow (f (-x)) ((m : ℝ) / n) :=
      gap26 f h h0 x m n hn
    _ = Real.rpow (f x) (-((m : ℝ) / n)) := gap27 f h h0 x m n hn
theorem gap29 (h : MultiplicativeCauchy f) (h0 : ∃ x, f x ≠ 0)
    (x : ℝ) (c : ℚ) :
    f ((c : ℝ) * x) = Real.rpow (f x) (c : ℝ) := by
  have hn : 0 < c.den := Nat.pos_of_ne_zero c.den_nz
  cases hnum : c.num with
  | ofNat m =>
      have hcr : (c : ℝ) = (m : ℝ) / (c.den : ℝ) := by
        norm_num [Rat.cast_def, hnum] <;> ring
      rw [hcr]
      exact gap25 f h h0 x m c.den hn
  | negSucc m =>
      have hcr : (c : ℝ) = -(((m + 1 : ℕ) : ℝ) / (c.den : ℝ)) := by
        norm_num [Rat.cast_def, hnum] <;> ring
      rw [hcr]
      exact gap28 f h h0 x (m + 1) c.den hn
theorem gap30 (h : MultiplicativeCauchy f) (h0 : ∃ x, f x ≠ 0)
    (hc : Continuous f) (x c : ℝ) :
    f (c * x) = Real.rpow (f x) c := by
  have hx : 0 < f x := gap12 f h h0 x
  have hleft : Continuous (fun y : ℝ => f (y * x)) := by
    have hmul : Continuous (fun y : ℝ => y * x) := continuous_id.mul continuous_const
    exact hc.comp hmul
  have hright : Continuous (fun y : ℝ => Real.rpow (f x) y) := by
    have hlogmul : Continuous (fun y : ℝ => Real.log (f x) * y) :=
      continuous_const.mul continuous_id
    have heq : (fun y : ℝ => Real.rpow (f x) y) =
        (fun y : ℝ => Real.exp (Real.log (f x) * y)) := by
      funext y
      change (f x) ^ y = Real.exp (Real.log (f x) * y)
      exact Real.rpow_def_of_pos (y := y) hx
    rw [heq]
    exact Real.continuous_exp.comp hlogmul
  let S : Set ℝ := Set.range (fun q : ℚ => (q : ℝ))
  have hSdense : Dense S := by
    simpa [S] using (Rat.denseRange_cast : DenseRange (fun q : ℚ => (q : ℝ)))
  have hclosed : IsClosed {y : ℝ | f (y * x) = Real.rpow (f x) y} :=
    isClosed_eq hleft hright
  have hsub : S ⊆ {y : ℝ | f (y * x) = Real.rpow (f x) y} := by
    rintro _ ⟨q, rfl⟩
    exact gap29 f h h0 x q
  have hmem : c ∈ closure S := by
    rw [hSdense.closure_eq]
    exact Set.mem_univ c
  exact (closure_minimal hsub hclosed) hmem
theorem gap31 (x : ℝ) : f x = f (x * 1) := by
  simp
theorem gap32 (h : MultiplicativeCauchy f) (h0 : ∃ x, f x ≠ 0)
    (hc : Continuous f) (x : ℝ) :
    f (x * 1) = Real.rpow (f 1) x := by
  exact gap30 f h h0 hc 1 x
theorem gap33 (a x : ℝ) (ha : a = f 1) : Real.rpow (f 1) x = Real.rpow a x := by
  simpa [ha]
theorem gap34 (h : MultiplicativeCauchy f) (h0 : ∃ x, f x ≠ 0)
    (hc : Continuous f) (x : ℝ) :
    f x = Real.rpow (f 1) x := by
  calc
    f x = f (x * 1) := gap31 f x
    _ = Real.rpow (f 1) x := gap32 f h h0 hc x
theorem gap35 (h : MultiplicativeCauchy f) (h0 : ∃ x, f x ≠ 0) : 0 < f 1 := by
  exact gap12 f h h0 1
theorem gap36 (h : MultiplicativeCauchy f) (h0 : ∃ x, f x ≠ 0)
    (hc : Continuous f) :
    ∃ a > 0, a = f 1 ∧ ∀ x, f x = Real.rpow a x := by
  refine ⟨f 1, gap35 f h h0, rfl, ?_⟩
  intro x
  exact gap34 f h h0 hc x

end
end ProofGap.Exercise812
