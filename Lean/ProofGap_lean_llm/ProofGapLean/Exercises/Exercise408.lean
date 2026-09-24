import ProofGapLean.Prelude.Finite
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Lean.Elab.Tactic.Omega

namespace ProofGap.Exercise408

open scoped BigOperators

noncomputable section

def p (n : ℕ) (a : ℕ → ℝ) (x : ℝ) : ℝ :=
  (Finset.range (n + 1)).sum (fun i => a i * x ^ (n - i))

def normalizedTail (n : ℕ) (a : ℕ → ℝ) (x : ℝ) : ℝ :=
  (Finset.Icc 1 n).sum (fun i => |a i| / |a 0| * (1 / |x| ^ i))

def AbsTendsToInfinity (f : ℝ → ℝ) : Prop :=
  ∀ M > 0, ∃ E > 0, ∀ x, E < |x| → M < |f x|

/-- Exercise 408, gap 1; exclude `x=0` before using reciprocal powers. -/
private lemma real_sum_nonneg (s : Finset ℕ) (f : ℕ → ℝ) :
    (∀ i ∈ s, 0 ≤ f i) → 0 ≤ s.sum f := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      intro h
      rw [Finset.sum_insert hi]
      exact add_nonneg (h i (by simp)) (ih (by
        intro j hj
        exact h j (by simp [hj])))

private lemma real_sum_le_sum (s : Finset ℕ) (f g : ℕ → ℝ) :
    (∀ i ∈ s, f i ≤ g i) → s.sum f ≤ s.sum g := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      intro h
      rw [Finset.sum_insert hi, Finset.sum_insert hi]
      exact add_le_add (h i (by simp)) (ih (by
        intro j hj
        exact h j (by simp [hj])))

private lemma real_abs_add_le (u v : ℝ) : |u + v| ≤ |u| + |v| := by
  apply (abs_le).2
  constructor
  · have hu : -u ≤ |u| := neg_le_abs u
    have hv : -v ≤ |v| := neg_le_abs v
    linarith
  · have hu : u ≤ |u| := le_abs_self u
    have hv : v ≤ |v| := le_abs_self v
    linarith

private lemma real_abs_sum_le_sum_abs (s : Finset ℕ) (f : ℕ → ℝ) :
    |s.sum f| ≤ s.sum (fun i => |f i|) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi]
      exact le_trans (real_abs_add_le (f i) (s.sum f))
        (add_le_add (le_refl |f i|) ih)

private lemma real_sum_mul (s : Finset ℕ) (f : ℕ → ℝ) (c : ℝ) :
    s.sum (fun i => f i * c) = s.sum f * c := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      simp [hi, ih, add_mul]

private lemma real_mul_sum (s : Finset ℕ) (f : ℕ → ℝ) (c : ℝ) :
    c * s.sum f = s.sum (fun i => c * f i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      simp [hi, ih, mul_add]

private lemma le_pow_of_one_le (y : ℝ) (hy : 1 ≤ y) :
    ∀ i : ℕ, 1 ≤ i → y ≤ y ^ i := by
  intro i
  induction i with
  | zero =>
      intro hi
      omega
  | succ i ih =>
      intro hi
      by_cases h : i = 0
      · subst i
        simp
      · have hi' : 1 ≤ i := by omega
        have hp := ih hi'
        calc
          y = y * 1 := by ring
          _ ≤ y * y ^ i :=
            mul_le_mul_of_nonneg_left (hy.trans hp) (le_trans zero_le_one hy)
          _ = y ^ (Nat.succ i) := by
            rw [pow_succ]
            ring

private lemma one_div_pow_le_one_div (y : ℝ) (hy : 1 ≤ y)
    (i : ℕ) (hi : 1 ≤ i) :
    1 / y ^ i ≤ 1 / y := by
  have hypos : 0 < y := lt_of_lt_of_le zero_lt_one hy
  exact one_div_le_one_div_of_le hypos (le_pow_of_one_le y hy i hi)

private lemma normalizedTail_lt_half (n : ℕ) (a : ℕ → ℝ)
    (ha : a 0 ≠ 0) :
    ∃ E > 0, ∀ x : ℝ, E < |x| →
      normalizedTail n a x < (1 / 2 : ℝ) := by
  let C : ℝ := (Finset.Icc 1 n).sum (fun i => |a i| / |a 0|)
  have hC : 0 ≤ C := by
    dsimp [C]
    exact real_sum_nonneg (Finset.Icc 1 n)
      (fun i => |a i| / |a 0|) (by
        intro i hi
        exact div_nonneg (abs_nonneg _) (abs_nonneg _))
  refine ⟨2 * C + 1, by linarith, ?_⟩
  intro x hx
  have hx1 : 1 < |x| := by
    nlinarith
  have hxpos : 0 < |x| := lt_trans zero_lt_one hx1
  have hsum : normalizedTail n a x ≤ C * (1 / |x|) := by
    rw [normalizedTail]
    calc
      (Finset.Icc 1 n).sum
          (fun i => |a i| / |a 0| * (1 / |x| ^ i)) ≤
          (Finset.Icc 1 n).sum
          (fun i => |a i| / |a 0| * (1 / |x|)) := by
            exact real_sum_le_sum (Finset.Icc 1 n)
              (fun i => |a i| / |a 0| * (1 / |x| ^ i))
              (fun i => |a i| / |a 0| * (1 / |x|)) (by
                intro i hi
                apply mul_le_mul_of_nonneg_left
                · exact one_div_pow_le_one_div |x| (le_of_lt hx1) i
                    (Finset.mem_Icc.mp hi).1
                · exact div_nonneg (abs_nonneg _) (abs_nonneg _))
      _ = C * (1 / |x|) := by
        dsimp [C]
        exact real_sum_mul (Finset.Icc 1 n)
          (fun i => |a i| / |a 0|) (1 / |x|)
  have hCdiv : C * (1 / |x|) < (1 / 2 : ℝ) := by
    calc
      C * (1 / |x|) = C / |x| := by
        simp [div_eq_mul_inv]
      _ < (1 / 2 : ℝ) := by
        apply (div_lt_iff₀ hxpos).2
        nlinarith
  exact lt_of_le_of_lt hsum hCdiv

private lemma polynomial_lower_bound (n : ℕ) (a : ℕ → ℝ)
    (ha : a 0 ≠ 0) (x : ℝ) (hx : x ≠ 0) :
    |a 0| * |x| ^ n * (1 - normalizedTail n a x) ≤ |p n a x| := by
  let s : Finset ℕ := Finset.Icc 1 n
  have hrange : Finset.range (n + 1) = insert 0 s := by
    ext i
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc, s]
    omega
  have hzero : 0 ∉ s := by
    simp [s]
  have hp :
      p n a x = a 0 * x ^ n + s.sum (fun i => a i * x ^ (n - i)) := by
    rw [p, hrange, Finset.sum_insert hzero]
    simp
  have hA0 : |a 0| ≠ 0 := abs_ne_zero.mpr ha
  have hxabs : |x| ≠ 0 := abs_ne_zero.mpr hx
  have hterm : ∀ i ∈ s,
      |a 0| * |x| ^ n * (|a i| / |a 0| * (1 / |x| ^ i)) =
        |a i| * |x| ^ (n - i) := by
    intro i hi
    have hin : i ≤ n := (Finset.mem_Icc.mp hi).2
    have hpow : |x| ^ n = |x| ^ (n - i) * |x| ^ i := by
      calc
        |x| ^ n = |x| ^ (n - i + i) := by
          rw [Nat.sub_add_cancel hin]
        _ = |x| ^ (n - i) * |x| ^ i := by
          rw [pow_add]
    rw [hpow]
    field_simp [hA0, hxabs]
    <;> ring
  have hfactor :
      |a 0| * |x| ^ n * normalizedTail n a x =
        s.sum (fun i => |a i| * |x| ^ (n - i)) := by
    rw [normalizedTail]
    rw [real_mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    exact hterm i hi
  have hsum :
      |s.sum (fun i => a i * x ^ (n - i))| ≤
        s.sum (fun i => |a i| * |x| ^ (n - i)) := by
    calc
      |s.sum (fun i => a i * x ^ (n - i))| ≤
          s.sum (fun i => |a i * x ^ (n - i)|) :=
        real_abs_sum_le_sum_abs s (fun i => a i * x ^ (n - i))
      _ = s.sum (fun i => |a i| * |x| ^ (n - i)) := by
        apply Finset.sum_congr rfl
        intro i hi
        simp only [abs_mul, abs_pow]
  have hlead : |a 0 * x ^ n| = |a 0| * |x| ^ n := by
    simp only [abs_mul, abs_pow]
  have htri :
      |a 0 * x ^ n| ≤
        |p n a x| + |s.sum (fun i => a i * x ^ (n - i))| := by
    apply (abs_le).2
    constructor
    · have hpneg : -(p n a x) ≤ |p n a x| := neg_le_abs _
      have hrle : s.sum (fun i => a i * x ^ (n - i)) ≤
          |s.sum (fun i => a i * x ^ (n - i))| := le_abs_self _
      linarith [hp]
    · have hple : p n a x ≤ |p n a x| := le_abs_self _
      have hrneg : -(s.sum (fun i => a i * x ^ (n - i))) ≤
          |s.sum (fun i => a i * x ^ (n - i))| := neg_le_abs _
      linarith [hp]
  calc
    |a 0| * |x| ^ n * (1 - normalizedTail n a x) =
        |a 0| * |x| ^ n -
          |a 0| * |x| ^ n * normalizedTail n a x := by ring
    _ = |a 0| * |x| ^ n -
          s.sum (fun i => |a i| * |x| ^ (n - i)) := by rw [hfactor]
    _ ≤ |a 0| * |x| ^ n -
          |s.sum (fun i => a i * x ^ (n - i))| :=
      sub_le_sub_left hsum _
    _ = |a 0 * x ^ n| -
          |s.sum (fun i => a i * x ^ (n - i))| := by rw [hlead]
    _ ≤ |p n a x| := by linarith

theorem gap1 (n : ℕ) (a : ℕ → ℝ) (ha : a 0 ≠ 0) :
    ∀ x, x ≠ 0 →
      |p n a x| ≥
        |a 0| * |x| ^ n * (1 - normalizedTail n a x) := by
  intro x hx
  exact polynomial_lower_bound n a ha x hx

/-- Exercise 408, gap 2. -/
theorem gap2 (n : ℕ) : ∀ i ∈ Finset.Icc 1 n,
    ∀ ε > 0, ∃ E > 0, ∀ x : ℝ, E < |x| →
      1 / |x| ^ i < ε := by
  intro i hi ε hε
  have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
  refine ⟨max 1 (1 / ε), ?_, ?_⟩
  · exact lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  · intro x hx
    have hx1 : 1 < |x| :=
      lt_of_le_of_lt (le_max_left (1 : ℝ) (1 / ε)) hx
    have hxε : 1 / ε < |x| :=
      lt_of_le_of_lt (le_max_right (1 : ℝ) (1 / ε)) hx
    have hxpos : 0 < |x| := lt_trans zero_lt_one hx1
    have hpow :=
      one_div_pow_le_one_div |x| (le_of_lt hx1) i hi1
    have hsmall : 1 / |x| < ε := by
      have hone : 1 < |x| * ε := (div_lt_iff₀ hε).1 hxε
      apply (div_lt_iff₀ hxpos).2
      nlinarith
    exact lt_of_le_of_lt hpow hsmall

/-- Exercise 408, gap 3; bind the large-radius threshold once. -/
theorem gap3 (n : ℕ) (a : ℕ → ℝ) (ha : a 0 ≠ 0) :
    ∃ E₁ > 0, ∀ x, E₁ < |x| →
      1 / 2 < |1 - normalizedTail n a x| := by
  obtain ⟨E₁, hE₁, htail⟩ := normalizedTail_lt_half n a ha
  refine ⟨E₁, hE₁, ?_⟩
  intro x hx
  have ht := htail x hx
  have hone : 0 ≤ 1 - normalizedTail n a x := by
    linarith
  rw [abs_of_nonneg hone]
  linarith

/-- Exercise 408, gap 4; include the threshold supplied by the tail estimate. -/
theorem gap4 (n : ℕ) (a : ℕ → ℝ) (ha : a 0 ≠ 0) :
    ∃ E₁ > 0, ∀ x, E₁ < |x| →
      (1 / 2 : ℝ) * |a 0| * |x| ^ n < |p n a x| := by
  obtain ⟨E₁, hE₁, htail⟩ := normalizedTail_lt_half n a ha
  refine ⟨E₁, hE₁, ?_⟩
  intro x hx
  have hxpos : 0 < |x| := lt_trans hE₁ hx
  have hx0 : x ≠ 0 := abs_pos.mp hxpos
  have hlead : 0 < |a 0| * |x| ^ n :=
    mul_pos (abs_pos.mpr ha) (pow_pos hxpos n)
  have htail' : (1 / 2 : ℝ) < 1 - normalizedTail n a x := by
    have := htail x hx
    linarith
  have hscaled := mul_lt_mul_of_pos_left htail' hlead
  have hlower := polynomial_lower_bound n a ha x hx0
  calc
    (1 / 2 : ℝ) * |a 0| * |x| ^ n =
        (|a 0| * |x| ^ n) * (1 / 2) := by ring
    _ < (|a 0| * |x| ^ n) * (1 - normalizedTail n a x) := hscaled
    _ ≤ |p n a x| := hlower

/-- Exercise 408, gap 5; choose `E` after the requested bound `M`. -/
theorem gap5 (n : ℕ) (hn : 0 < n) (a : ℕ → ℝ) (ha : a 0 ≠ 0) :
    ∀ M > 0, ∃ E > 0, ∀ x, E < |x| → M < |p n a x| := by
  intro M hM
  obtain ⟨E₁, hE₁, hp⟩ := gap4 n a ha
  let A : ℝ := |a 0|
  have hA : 0 < A := by
    exact abs_pos.mpr ha
  refine ⟨max E₁ (max 1 ((2 * M) / A)), ?_, ?_⟩
  · exact lt_of_lt_of_le hE₁ (le_max_left _ _)
  · intro x hx
    have hxE₁ : E₁ < |x| :=
      lt_of_le_of_lt (le_max_left E₁ (max 1 ((2 * M) / A))) hx
    have hxrest : max 1 ((2 * M) / A) < |x| :=
      lt_of_le_of_lt (le_max_right E₁ (max 1 ((2 * M) / A))) hx
    have hx1 : 1 < |x| :=
      lt_of_le_of_lt (le_max_left (1 : ℝ) ((2 * M) / A)) hxrest
    have hxM : (2 * M) / A < |x| :=
      lt_of_le_of_lt (le_max_right (1 : ℝ) ((2 * M) / A)) hxrest
    have hpow : |x| ≤ |x| ^ n :=
      le_pow_of_one_le |x| (le_of_lt hx1) n (by omega)
    have hmul : 2 * M < |x| * A :=
      (div_lt_iff₀ hA).1 hxM
    have hApow : A * |x| ≤ A * |x| ^ n :=
      mul_le_mul_of_nonneg_left hpow (le_of_lt hA)
    have hMpow : M < (1 / 2 : ℝ) * A * |x| ^ n := by
      nlinarith
    exact lt_trans hMpow (hp x hxE₁)

/-- Exercise 408, gap 6. -/
theorem gap6 (n : ℕ) (hn : 0 < n) (a : ℕ → ℝ) (ha : a 0 ≠ 0) :
    AbsTendsToInfinity (p n a) := by
  simpa [AbsTendsToInfinity] using (gap5 n hn a ha)

/-- Exercise 408, gap 7; retain the missing nonzero leading coefficient and positive degree. -/
theorem gap7 (n : ℕ) (hn : 0 < n) (a : ℕ → ℝ) (ha : a 0 ≠ 0) :
    AbsTendsToInfinity (p n a) := by
  exact gap6 n hn a ha

end

end ProofGap.Exercise408
