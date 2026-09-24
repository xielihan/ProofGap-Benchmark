import ProofGapLean.Prelude.Analysis
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

namespace ProofGap.Exercise638

noncomputable section

def Recurrence (x : ℝ) (y : ℕ → ℝ) : Prop :=
  y 1 = x / 2 ∧
    ∀ n ≥ 2, y n = x / 2 - y (n - 1) ^ 2 / 2
def oddSubseq (y : ℕ → ℝ) (n : ℕ) : ℝ := y (2 * n + 1)
def evenSubseq (y : ℕ → ℝ) (n : ℕ) : ℝ := y (2 * n + 2)

/-- Exercise 638, gap 1. -/
private theorem recurrence_positive_bounded
    (x : ℝ) (y : ℕ → ℝ) (hx0 : 0 < x) (hx1 : x ≤ 1)
    (hy : Recurrence x y) :
    ∀ n ≥ 1, 0 < y n ∧ y n ≤ x / 2 := by
  intro n hn
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases h1 : n = 1
      · subst n
        rw [hy.1]
        constructor <;> linarith
      · have hn2 : 2 ≤ n := by omega
        have hprev := ih (n - 1) (by omega) (by omega)
        rcases hprev with ⟨hp0, hpub⟩
        have hsqbound : 0 ≤ (x / 2 - y (n - 1)) *
            (x / 2 + y (n - 1)) :=
          mul_nonneg (sub_nonneg.mpr hpub) (by linarith)
        have hxbound : 0 ≤ x * (1 - x) :=
          mul_nonneg (le_of_lt hx0) (sub_nonneg.mpr hx1)
        have hsqpos : 0 < y (n - 1) * y (n - 1) :=
          mul_pos hp0 hp0
        rw [hy.2 n hn2]
        constructor <;> nlinarith

private theorem monotone_bddAbove_has_limit
    (u : ℕ → ℝ) (hmono : Monotone u)
    (hbdd : BddAbove (Set.range u)) :
    ∃ A, Filter.Tendsto u Filter.atTop (nhds A) := by
  refine ⟨sSup (Set.range u), tendsto_order.2 ⟨?_, ?_⟩⟩
  · intro a ha
    have hex : ∃ N, a < u N := by
      by_contra h
      have hall : ∀ N, u N ≤ a := by
        intro N
        exact le_of_not_gt (fun hN => h ⟨N, hN⟩)
      have hsle : sSup (Set.range u) ≤ a := by
        apply csSup_le (Set.range_nonempty u)
        rintro z ⟨N, rfl⟩
        exact hall N
      exact (not_le_of_gt ha) hsle
    obtain ⟨N, hN⟩ := hex
    exact Filter.eventually_atTop.2
      ⟨N, fun n hn => lt_of_lt_of_le hN (hmono hn)⟩
  · intro b hb
    exact Filter.Eventually.of_forall fun n =>
      lt_of_le_of_lt (le_csSup hbdd ⟨n, rfl⟩) hb

private theorem tendsto_of_odd_even
    (y : ℕ → ℝ) (A : ℝ)
    (hodd : Filter.Tendsto (oddSubseq y) Filter.atTop (nhds A))
    (heven : Filter.Tendsto (evenSubseq y) Filter.atTop (nhds A)) :
    Filter.Tendsto y Filter.atTop (nhds A) := by
  rw [Metric.tendsto_atTop] at hodd heven ⊢
  intro ε hε
  obtain ⟨No, hNo⟩ := hodd ε hε
  obtain ⟨Ne, hNe⟩ := heven ε hε
  refine ⟨2 * max No Ne + 2, ?_⟩
  intro n hn
  by_cases hp : n % 2 = 0
  · have hk : Ne ≤ n / 2 - 1 := by omega
    have hd := hNe (n / 2 - 1) hk
    have heq : 2 * (n / 2 - 1) + 2 = n := by omega
    simpa [evenSubseq, heq] using hd
  · have hmod : n % 2 = 1 := by omega
    have hk : No ≤ n / 2 := by omega
    have hd := hNo (n / 2) hk
    have heq : 2 * (n / 2) + 1 = n := by omega
    simpa [oddSubseq, heq] using hd

theorem gap1 (x : ℝ) (y : ℕ → ℝ) (hx : x = 0)
    (hy : Recurrence x y) :
    ∀ n ≥ 1, y n = 0 := by
  rcases hy with ⟨hy1, hyrec⟩
  intro n hn
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases h1 : n = 1
      · subst n
        simpa [hx] using hy1
      · have hn2 : 2 ≤ n := by omega
        have hprev : y (n - 1) = 0 := ih (n - 1) (by omega) (by omega)
        rw [hyrec n hn2, hx, hprev]
        simp

/-- Exercise 638, gap 2. -/
theorem gap2 (x : ℝ) (y : ℕ → ℝ) (hx : x = 0)
    (hy : Recurrence x y) :
    Filter.Tendsto y Filter.atTop (nhds 0) := by
  have hEq : y =ᶠ[Filter.atTop] (fun _ => (0 : ℝ)) :=
    Filter.eventually_atTop.2 ⟨1, fun n hn => gap1 x y hx hy n hn⟩
  exact tendsto_const_nhds.congr' hEq.symm

/-- Exercise 638, gap 3. -/
theorem gap3 (x : ℝ) (y : ℕ → ℝ) (hx0 : 0 < x) (hx1 : x ≤ 1)
    (hy : Recurrence x y) :
    ∀ n ≥ 1, 0 < y n := by
  intro n hn
  exact (recurrence_positive_bounded x y hx0 hx1 hy n hn).1

/-- Exercise 638, gap 4; add `n≥1` to the source parity indices. -/
theorem gap4 (x : ℝ) (y : ℕ → ℝ) (hx0 : 0 < x) (hx1 : x ≤ 1)
    (hy : Recurrence x y) :
    ∀ n ≥ 1, y (2 * n) < y (2 * n + 2) := by
  intro n hn
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases hbase : n = 1
      · subst n
        have hp1 := (recurrence_positive_bounded x y hx0 hx1 hy 1 (by omega)).1
        have hp2 := (recurrence_positive_bounded x y hx0 hx1 hy 2 (by omega)).1
        have hp3 := (recurrence_positive_bounded x y hx0 hx1 hy 3 (by omega)).1
        have h2 : y 2 = x / 2 - y 1 ^ 2 / 2 := by
          simpa using hy.2 2 (by omega)
        have h3 : y 3 = x / 2 - y 2 ^ 2 / 2 := by
          simpa using hy.2 3 (by omega)
        have h4 : y 4 = x / 2 - y 3 ^ 2 / 2 := by
          simpa using hy.2 4 (by omega)
        have h31 : y 3 < y 1 := by
          have hs : 0 < y 2 * y 2 := mul_pos hp2 hp2
          nlinarith [hy.1]
        have hs : 0 < (y 1 - y 3) * (y 1 + y 3) :=
          mul_pos (sub_pos.mpr h31) (add_pos hp1 hp3)
        nlinarith
      · have hn2 : 2 ≤ n := by omega
        have hprev0 := ih (n - 1) (by omega) (by omega)
        have hiA : 2 * (n - 1) = 2 * n - 2 := by omega
        have hiB : 2 * (n - 1) + 2 = 2 * n := by omega
        have hprev : y (2 * n - 2) < y (2 * n) := by
          rw [← hiA, ← hiB]
          exact hprev0
        have hpA := (recurrence_positive_bounded x y hx0 hx1 hy (2 * n - 2) (by omega)).1
        have hpB := (recurrence_positive_bounded x y hx0 hx1 hy (2 * n) (by omega)).1
        have hpC := (recurrence_positive_bounded x y hx0 hx1 hy (2 * n - 1) (by omega)).1
        have hpD := (recurrence_positive_bounded x y hx0 hx1 hy (2 * n + 1) (by omega)).1
        have hOddA : y (2 * n - 1) = x / 2 - y (2 * n - 2) ^ 2 / 2 := by
          have hrec := hy.2 (2 * n - 1) (by omega)
          have hidx : (2 * n - 1) - 1 = 2 * n - 2 := by omega
          rw [hidx] at hrec
          exact hrec
        have hOddB : y (2 * n + 1) = x / 2 - y (2 * n) ^ 2 / 2 := by
          have hrec := hy.2 (2 * n + 1) (by omega)
          have hidx : (2 * n + 1) - 1 = 2 * n := by omega
          rw [hidx] at hrec
          exact hrec
        have hs1 : 0 < (y (2 * n) - y (2 * n - 2)) *
            (y (2 * n) + y (2 * n - 2)) :=
          mul_pos (sub_pos.mpr hprev) (add_pos hpB hpA)
        have hOdd : y (2 * n + 1) < y (2 * n - 1) := by
          nlinarith
        have hEvenA : y (2 * n) = x / 2 - y (2 * n - 1) ^ 2 / 2 := by
          exact hy.2 (2 * n) (by omega)
        have hEvenB : y (2 * n + 2) = x / 2 - y (2 * n + 1) ^ 2 / 2 := by
          have hrec := hy.2 (2 * n + 2) (by omega)
          have hidx : (2 * n + 2) - 1 = 2 * n + 1 := by omega
          rw [hidx] at hrec
          exact hrec
        have hs2 : 0 < (y (2 * n - 1) - y (2 * n + 1)) *
            (y (2 * n - 1) + y (2 * n + 1)) :=
          mul_pos (sub_pos.mpr hOdd) (add_pos hpC hpD)
        nlinarith

/-- Exercise 638, gap 5; add `n≥1` before using `2*n-1`. -/
theorem gap5 (x : ℝ) (y : ℕ → ℝ) (hx0 : 0 < x) (hx1 : x ≤ 1)
    (hy : Recurrence x y) :
    ∀ n ≥ 1, y (2 * n + 1) < y (2 * n - 1) := by
  intro n hn
  by_cases hbase : n = 1
  · subst n
    have hp2 := (recurrence_positive_bounded x y hx0 hx1 hy 2 (by omega)).1
    have h3 : y 3 = x / 2 - y 2 ^ 2 / 2 := by
      simpa using hy.2 3 (by omega)
    have hs : 0 < y 2 * y 2 := mul_pos hp2 hp2
    nlinarith [hy.1]
  · have hn2 : 2 ≤ n := by omega
    have heven0 := gap4 x y hx0 hx1 hy (n - 1) (by omega)
    have hiA : 2 * (n - 1) = 2 * n - 2 := by omega
    have hiB : 2 * (n - 1) + 2 = 2 * n := by omega
    have heven : y (2 * n - 2) < y (2 * n) := by
      rw [← hiA, ← hiB]
      exact heven0
    have hpA := (recurrence_positive_bounded x y hx0 hx1 hy (2 * n - 2) (by omega)).1
    have hpB := (recurrence_positive_bounded x y hx0 hx1 hy (2 * n) (by omega)).1
    have hleft : y (2 * n + 1) = x / 2 - y (2 * n) ^ 2 / 2 := by
      have hrec := hy.2 (2 * n + 1) (by omega)
      have hidx : (2 * n + 1) - 1 = 2 * n := by omega
      rw [hidx] at hrec
      exact hrec
    have hright : y (2 * n - 1) = x / 2 - y (2 * n - 2) ^ 2 / 2 := by
      have hrec := hy.2 (2 * n - 1) (by omega)
      have hidx : (2 * n - 1) - 1 = 2 * n - 2 := by omega
      rw [hidx] at hrec
      exact hrec
    have hs : 0 < (y (2 * n) - y (2 * n - 2)) *
        (y (2 * n) + y (2 * n - 2)) :=
      mul_pos (sub_pos.mpr heven) (add_pos hpB hpA)
    nlinarith

/-- Exercise 638, gap 6. -/
theorem gap6 (x : ℝ) (y : ℕ → ℝ) (hy : Recurrence x y) :
    x / 2 = y 1 := by
  exact hy.1.symm

/-- Exercise 638, gap 7. -/
theorem gap7 (x : ℝ) (y : ℕ → ℝ) (hx0 : 0 < x) (hx1 : x ≤ 1)
    (hy : Recurrence x y) :
    y 3 < y 1 := by
  have hp2 := (recurrence_positive_bounded x y hx0 hx1 hy 2 (by omega)).1
  have h3 : y 3 = x / 2 - y 2 ^ 2 / 2 := by
    simpa using hy.2 3 (by omega)
  have hs : 0 < y 2 * y 2 := mul_pos hp2 hp2
  nlinarith [hy.1]

/-- Exercise 638, gap 8; replace the ellipsis by strict decrease of the odd subsequence. -/
theorem gap8 (x : ℝ) (y : ℕ → ℝ) (hx0 : 0 < x) (hx1 : x ≤ 1)
    (hy : Recurrence x y) :
    StrictAnti (oddSubseq y) := by
  refine strictAnti_nat_of_succ_lt ?_
  intro n
  unfold oddSubseq
  convert gap5 x y hx0 hx1 hy (n + 1) (by omega) using 1 <;> omega

/-- Exercise 638, gap 9; replace the ellipsis by the positive lower bound. -/
theorem gap9 (x : ℝ) (y : ℕ → ℝ) (hx0 : 0 < x) (hx1 : x ≤ 1)
    (hy : Recurrence x y) :
    ∀ n, 0 < oddSubseq y n := by
  intro n
  unfold oddSubseq
  exact (recurrence_positive_bounded x y hx0 hx1 hy (2 * n + 1) (by omega)).1

/-- Exercise 638, gap 10. -/
theorem gap10 (x : ℝ) (hx0 : 0 < x) : 0 < x / 2 := by
  linarith

/-- Exercise 638, gap 11. -/
theorem gap11 (x : ℝ) (y : ℕ → ℝ) (hx0 : 0 < x) (hx1 : x ≤ 1)
    (hy : Recurrence x y) :
    0 < y 2 := by
  exact (recurrence_positive_bounded x y hx0 hx1 hy 2 (by omega)).1

/-- Exercise 638, gap 12. -/
theorem gap12 (x : ℝ) (y : ℕ → ℝ) (hx0 : 0 < x) (hx1 : x ≤ 1)
    (hy : Recurrence x y) :
    y 2 < y 4 := by
  convert gap4 x y hx0 hx1 hy 1 (by omega) using 1 <;> omega

/-- Exercise 638, gap 13; replace the ellipsis by strict increase of the even subsequence. -/
theorem gap13 (x : ℝ) (y : ℕ → ℝ) (hx0 : 0 < x) (hx1 : x ≤ 1)
    (hy : Recurrence x y) :
    StrictMono (evenSubseq y) := by
  refine strictMono_nat_of_lt_succ ?_
  intro n
  unfold evenSubseq
  convert gap4 x y hx0 hx1 hy (n + 1) (by omega) using 1 <;> omega

/-- Exercise 638, gap 14; replace the ellipsis by the common upper bound. -/
theorem gap14 (x : ℝ) (y : ℕ → ℝ) (hx0 : 0 < x) (hx1 : x ≤ 1)
    (hy : Recurrence x y) :
    ∀ n, evenSubseq y n < x / 2 := by
  intro n
  unfold evenSubseq
  have hp := (recurrence_positive_bounded x y hx0 hx1 hy (2 * n + 1) (by omega)).1
  have hrec : y (2 * n + 2) = x / 2 - y (2 * n + 1) ^ 2 / 2 := by
    convert hy.2 (2 * n + 2) (by omega) using 1 <;> omega
  have hs : 0 < y (2 * n + 1) * y (2 * n + 1) := mul_pos hp hp
  nlinarith

/-- Exercise 638, gap 15. -/
theorem gap15 (x : ℝ) (hx0 : 0 < x) : 0 < x / 2 := by
  linarith

/-- Exercise 638, gap 16; use the explicit odd subsequence. -/
theorem gap16 (x : ℝ) (y : ℕ → ℝ) (hx0 : 0 < x) (hx1 : x ≤ 1)
    (hy : Recurrence x y) :
    ∃ A₁, Filter.Tendsto (oddSubseq y) Filter.atTop (nhds A₁) := by
  have hmono : Monotone (fun n => -oddSubseq y n) := by
    intro a b hab
    exact neg_le_neg ((gap8 x y hx0 hx1 hy).antitone hab)
  have hbdd : BddAbove (Set.range (fun n => -oddSubseq y n)) := by
    refine ⟨0, ?_⟩
    rintro z ⟨n, rfl⟩
    exact neg_nonpos.mpr (le_of_lt (gap9 x y hx0 hx1 hy n))
  obtain ⟨B, hB⟩ := monotone_bddAbove_has_limit
    (fun n => -oddSubseq y n) hmono hbdd
  refine ⟨-B, ?_⟩
  simpa only [neg_neg] using hB.neg

/-- Exercise 638, gap 17; use the explicit even subsequence. -/
theorem gap17 (x : ℝ) (y : ℕ → ℝ) (hx0 : 0 < x) (hx1 : x ≤ 1)
    (hy : Recurrence x y) :
    ∃ A₂, Filter.Tendsto (evenSubseq y) Filter.atTop (nhds A₂) := by
  have hmono : Monotone (evenSubseq y) :=
    (gap13 x y hx0 hx1 hy).monotone
  have hbdd : BddAbove (Set.range (evenSubseq y)) := by
    refine ⟨x / 2, ?_⟩
    rintro z ⟨n, rfl⟩
    exact le_of_lt (gap14 x y hx0 hx1 hy n)
  exact monotone_bddAbove_has_limit (evenSubseq y) hmono hbdd

/-- Exercise 638, gap 18; bind the two subsequential limits. -/
theorem gap18 (x A₁ A₂ : ℝ) (y : ℕ → ℝ)
    (hodd : Filter.Tendsto (oddSubseq y) Filter.atTop (nhds A₁))
    (heven : Filter.Tendsto (evenSubseq y) Filter.atTop (nhds A₂))
    (hy : Recurrence x y) :
    A₂ = x / 2 - A₁ ^ 2 / 2 := by
  have hEq : evenSubseq y =
      (fun n => x / 2 - oddSubseq y n ^ 2 / 2) := by
    funext n
    unfold evenSubseq oddSubseq
    convert hy.2 (2 * n + 2) (by omega) using 1 <;> omega
  have hcalc : Filter.Tendsto
      (fun n => x / 2 - oddSubseq y n ^ 2 / 2)
      Filter.atTop (nhds (x / 2 - A₁ ^ 2 / 2)) := by
    simpa [div_eq_mul_inv] using
      (tendsto_const_nhds.sub ((hodd.pow 2).mul_const (1 / 2 : ℝ)))
  have heven' : Filter.Tendsto (evenSubseq y) Filter.atTop
      (nhds (x / 2 - A₁ ^ 2 / 2)) := by
    rw [hEq]
    exact hcalc
  exact tendsto_nhds_unique heven heven'

/-- Exercise 638, gap 19; bind the two subsequential limits. -/
theorem gap19 (x A₁ A₂ : ℝ) (y : ℕ → ℝ)
    (hodd : Filter.Tendsto (oddSubseq y) Filter.atTop (nhds A₁))
    (heven : Filter.Tendsto (evenSubseq y) Filter.atTop (nhds A₂))
    (hy : Recurrence x y) :
    A₁ = x / 2 - A₂ ^ 2 / 2 := by
  have hshift : Filter.Tendsto (fun n : ℕ => n + 1)
      Filter.atTop Filter.atTop := by
    refine Filter.tendsto_atTop.2 ?_
    intro b
    exact Filter.eventually_atTop.2 ⟨b, fun n hn => by omega⟩
  have hoddShift : Filter.Tendsto (fun n => oddSubseq y (n + 1))
      Filter.atTop (nhds A₁) := hodd.comp hshift
  have hEq : (fun n => oddSubseq y (n + 1)) =
      (fun n => x / 2 - evenSubseq y n ^ 2 / 2) := by
    funext n
    unfold oddSubseq evenSubseq
    convert hy.2 (2 * n + 3) (by omega) using 1 <;> omega
  have hcalc : Filter.Tendsto
      (fun n => x / 2 - evenSubseq y n ^ 2 / 2)
      Filter.atTop (nhds (x / 2 - A₂ ^ 2 / 2)) := by
    simpa [div_eq_mul_inv] using
      (tendsto_const_nhds.sub ((heven.pow 2).mul_const (1 / 2 : ℝ)))
  have hoddShift' : Filter.Tendsto (fun n => oddSubseq y (n + 1))
      Filter.atTop (nhds (x / 2 - A₂ ^ 2 / 2)) := by
    rw [hEq]
    exact hcalc
  exact tendsto_nhds_unique hoddShift hoddShift'

/-- Exercise 638, gap 20; bind the coupled limit equations. -/
theorem gap20 (x A₁ A₂ : ℝ)
    (h₁ : A₁ = x / 2 - A₂ ^ 2 / 2)
    (h₂ : A₂ = x / 2 - A₁ ^ 2 / 2) :
    A₁ - A₂ = (A₁ - A₂) * ((A₁ + A₂) / 2) := by
  nlinarith

/-- Exercise 638, gap 21; bind the odd limit. -/
theorem gap21 (x A₁ : ℝ) (y : ℕ → ℝ)
    (hpos : ∀ n, 0 < oddSubseq y n)
    (hlim : Filter.Tendsto (oddSubseq y) Filter.atTop (nhds A₁)) :
    0 ≤ A₁ := by
  exact ge_of_tendsto hlim
    (Filter.Eventually.of_forall fun n => le_of_lt (hpos n))

/-- Exercise 638, gap 22; bind the odd limit and upper bound. -/
theorem gap22 (x A₁ : ℝ) (y : ℕ → ℝ)
    (hub : ∀ n, oddSubseq y n ≤ x / 2)
    (hlim : Filter.Tendsto (oddSubseq y) Filter.atTop (nhds A₁)) :
    A₁ ≤ x / 2 := by
  exact le_of_tendsto hlim
    (Filter.Eventually.of_forall fun n => hub n)

/-- Exercise 638, gap 23. -/
theorem gap23 (x : ℝ) (hx : x ≤ 1) : x / 2 ≤ (1 / 2 : ℝ) := by
  linarith

/-- Exercise 638, gap 24; bind the even limit. -/
theorem gap24 (A₂ : ℝ) (y : ℕ → ℝ)
    (hpos : ∀ n, 0 < evenSubseq y n)
    (hlim : Filter.Tendsto (evenSubseq y) Filter.atTop (nhds A₂)) :
    0 ≤ A₂ := by
  exact ge_of_tendsto hlim
    (Filter.Eventually.of_forall fun n => le_of_lt (hpos n))

/-- Exercise 638, gap 25; bind the even limit and upper bound. -/
theorem gap25 (x A₂ : ℝ) (y : ℕ → ℝ)
    (hub : ∀ n, evenSubseq y n ≤ x / 2)
    (hlim : Filter.Tendsto (evenSubseq y) Filter.atTop (nhds A₂)) :
    A₂ ≤ x / 2 := by
  exact le_of_tendsto hlim
    (Filter.Eventually.of_forall fun n => hub n)

/-- Exercise 638, gap 26. -/
theorem gap26 (x : ℝ) (hx : x ≤ 1) : x / 2 ≤ (1 / 2 : ℝ) := by
  linarith

/-- Exercise 638, gap 27; bind both limits and their equations. -/
theorem gap27 (x A₁ A₂ : ℝ)
    (hx0 : 0 < x) (hx1 : x ≤ 1)
    (h₁ : A₁ = x / 2 - A₂ ^ 2 / 2)
    (h₂ : A₂ = x / 2 - A₁ ^ 2 / 2)
    (hb₁ : 0 ≤ A₁ ∧ A₁ ≤ x / 2)
    (hb₂ : 0 ≤ A₂ ∧ A₂ ≤ x / 2) :
    A₁ = A₂ := by
  have hd := gap20 x A₁ A₂ h₁ h₂
  rcases hb₁ with ⟨hA₁0, hA₁x⟩
  rcases hb₂ with ⟨hA₂0, hA₂x⟩
  nlinarith

/-- Exercise 638, gap 28; bind the common limit. -/
theorem gap28 (x A : ℝ) (hx0 : 0 < x) (hx1 : x ≤ 1)
    (hA : A = x / 2 - A ^ 2 / 2) :
    A = x / 2 - A ^ 2 / 2 := by
  exact hA

/-- Exercise 638, gap 29; select the nonnegative root. -/
theorem gap29 (x A : ℝ) (hx0 : 0 < x) (hx1 : x ≤ 1)
    (hA : A = x / 2 - A ^ 2 / 2) (hAnonneg : 0 ≤ A) :
    A = Real.sqrt (1 + x) - 1 := by
  have hs0 : 0 ≤ 1 + x := by linarith
  have hs := Real.sq_sqrt hs0
  have hsnonneg := Real.sqrt_nonneg (1 + x)
  have hAplus : 0 ≤ A + 1 := by linarith
  nlinarith

/-- Exercise 638, gap 30. -/
theorem gap30 (x : ℝ) (y : ℕ → ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hy : Recurrence x y) :
    Filter.Tendsto y Filter.atTop (nhds (Real.sqrt (1 + x) - 1)) := by
  by_cases hx : x = 0
  · simpa [hx] using gap2 x y hx hy
  · have hxpos : 0 < x := lt_of_le_of_ne hx0 (Ne.symm hx)
    obtain ⟨A₁, hodd⟩ := gap16 x y hxpos hx1 hy
    obtain ⟨A₂, heven⟩ := gap17 x y hxpos hx1 hy
    have h₂ : A₂ = x / 2 - A₁ ^ 2 / 2 :=
      gap18 x A₁ A₂ y hodd heven hy
    have h₁ : A₁ = x / 2 - A₂ ^ 2 / 2 :=
      gap19 x A₁ A₂ y hodd heven hy
    have hoddpos : ∀ n, 0 < oddSubseq y n :=
      gap9 x y hxpos hx1 hy
    have hevenpos : ∀ n, 0 < evenSubseq y n := by
      intro n
      unfold evenSubseq
      exact (recurrence_positive_bounded x y hxpos hx1 hy (2 * n + 2) (by omega)).1
    have hoddub : ∀ n, oddSubseq y n ≤ x / 2 := by
      intro n
      unfold oddSubseq
      exact (recurrence_positive_bounded x y hxpos hx1 hy (2 * n + 1) (by omega)).2
    have hevenub : ∀ n, evenSubseq y n ≤ x / 2 := by
      intro n
      unfold evenSubseq
      exact (recurrence_positive_bounded x y hxpos hx1 hy (2 * n + 2) (by omega)).2
    have hb₁ : 0 ≤ A₁ ∧ A₁ ≤ x / 2 :=
      ⟨gap21 x A₁ y hoddpos hodd,
        gap22 x A₁ y hoddub hodd⟩
    have hb₂ : 0 ≤ A₂ ∧ A₂ ≤ x / 2 :=
      ⟨gap24 A₂ y hevenpos heven,
        gap25 x A₂ y hevenub heven⟩
    have hEq : A₁ = A₂ :=
      gap27 x A₁ A₂ hxpos hx1 h₁ h₂ hb₁ hb₂
    have hfix : A₁ = x / 2 - A₁ ^ 2 / 2 := hEq.trans h₂
    have hroot : A₁ = Real.sqrt (1 + x) - 1 :=
      gap29 x A₁ hxpos hx1 hfix hb₁.1
    have hroot₂ : A₂ = Real.sqrt (1 + x) - 1 := hEq.symm.trans hroot
    apply tendsto_of_odd_even y (Real.sqrt (1 + x) - 1)
    · simpa [hroot] using hodd
    · simpa [hroot₂] using heven

end

end ProofGap.Exercise638
