import ProofGapLean.Prelude.Analysis
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise2204
noncomputable section

open Filter MeasureTheory
open scoped BigOperators Interval

def translationError (f : ℝ → ℝ) (a b h : ℝ) : ℝ :=
  ∫ x in a..b, |f (x + h) - f x|

def oscillationOn (g : ℝ → ℝ) (I : Set ℝ) : ℝ :=
  sSup {r : ℝ | ∃ u ∈ I, ∃ v ∈ I, r = |g u - g v|}

def IsPartitionOn (a b : ℝ) (n : ℕ) (x : ℕ → ℝ) : Prop :=
  x 0 = a ∧ x n = b ∧ ∀ i < n, x i < x (i + 1)

def width (x : ℕ → ℝ) (i : ℕ) : ℝ := x (i + 1) - x i

def Fine (n : ℕ) (x : ℕ → ℝ) (δ : ℝ) : Prop :=
  ∀ i < n, width x i < δ

def omega (g : ℝ → ℝ) (x : ℕ → ℝ) (i : ℕ) : ℝ :=
  oscillationOn g (Set.Icc (x i) (x (i + 1)))

def oscillationSum (g : ℝ → ℝ) (n : ℕ) (x : ℕ → ℝ) : ℝ :=
  ∑ i ∈ Finset.range n, omega g x i * width x i

def RiemannIntegrableOn (g : ℝ → ℝ) (a b : ℝ) : Prop :=
  Bornology.IsBounded (g '' Set.Icc a b) ∧
    ∀ ε > 0, ∃ δ > 0, ∀ n : ℕ, ∀ x : ℕ → ℝ,
      IsPartitionOn a b n x → Fine n x δ →
        oscillationSum g n x < ε

def omegaH (f : ℝ → ℝ) (a h : ℝ) (i : ℕ) : ℝ :=
  oscillationOn f
    (Set.Icc (a + (i : ℝ) * h) (a + ((i : ℝ) + 2) * h))

def evenOscSum (f : ℝ → ℝ) (a h : ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range n, omegaH f a h (2 * i) * (2 * h)

def oddOscSum (f : ℝ → ℝ) (a h : ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range n, omegaH f a h (2 * i + 1) * (2 * h)

private theorem sum_range_even_odd_pairs (F : ℕ → ℝ) :
    ∀ n : ℕ,
      (∑ i ∈ Finset.range (2 * n), F i) =
        ∑ i ∈ Finset.range n, (F (2 * i) + F (2 * i + 1)) := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      calc
        (∑ i ∈ Finset.range (2 * (n + 1)), F i) =
            (∑ i ∈ Finset.range (2 * n), F i) + F (2 * n) + F (2 * n + 1) := by
          rw [show 2 * (n + 1) = 2 * n + 2 by omega,
            Finset.sum_range_succ, Finset.sum_range_succ]
        _ = (∑ i ∈ Finset.range n, (F (2 * i) + F (2 * i + 1))) +
              F (2 * n) + F (2 * n + 1) := by rw [ih]
        _ = ∑ i ∈ Finset.range (n + 1), (F (2 * i) + F (2 * i + 1)) := by
          rw [Finset.sum_range_succ]
          ring

private theorem abs_sub_le_oscillationOn (g : ℝ → ℝ) (I J : Set ℝ)
    (hIJ : I ⊆ J) (hbounded : Bornology.IsBounded (g '' J))
    {u v : ℝ} (hu : u ∈ I) (hv : v ∈ I) :
    |g u - g v| ≤ oscillationOn g I := by
  unfold oscillationOn
  apply le_csSup
  · rcases hbounded.bddBelow with ⟨m, hm⟩
    rcases hbounded.bddAbove with ⟨M, hM⟩
    refine ⟨M - m, ?_⟩
    rintro r ⟨u', hu', v', hv', rfl⟩
    have huM : g u' ≤ M := hM ⟨u', hIJ hu', rfl⟩
    have hum : m ≤ g u' := hm ⟨u', hIJ hu', rfl⟩
    have hvM : g v' ≤ M := hM ⟨v', hIJ hv', rfl⟩
    have hvm : m ≤ g v' := hm ⟨v', hIJ hv', rfl⟩
    rw [abs_le]
    constructor <;> linarith
  · exact ⟨u, hu, v, hv, rfl⟩

private theorem partition_mono {a b : ℝ} {n : ℕ} {x : ℕ → ℝ}
    (hx : IsPartitionOn a b n x) {i j : ℕ} (hij : i ≤ j) (hj : j ≤ n) :
    x i ≤ x j := by
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ j hij ih =>
      exact le_trans (ih (by omega)) (le_of_lt (hx.2.2 j (by omega)))

private theorem partition_point_mem {a b : ℝ} {n : ℕ} {x : ℕ → ℝ}
    (hx : IsPartitionOn a b n x) {i : ℕ} (hi : i ≤ n) :
    x i ∈ Set.Icc a b := by
  constructor
  · rw [← hx.1]
    exact partition_mono hx (Nat.zero_le i) hi
  · rw [← hx.2.1]
    exact partition_mono hx hi le_rfl

private theorem partition_cell_subset {a b : ℝ} {n : ℕ} {x : ℕ → ℝ}
    (hx : IsPartitionOn a b n x) {i : ℕ} (hi : i < n) :
    Set.Icc (x i) (x (i + 1)) ⊆ Set.Icc a b := by
  exact Set.Icc_subset_Icc
    (partition_point_mem hx (Nat.le_of_lt hi)).1
    (partition_point_mem hx (Nat.succ_le_iff.mpr hi)).2

private theorem oscillation_term_nonneg {g : ℝ → ℝ} {a b : ℝ}
    {n : ℕ} {x : ℕ → ℝ} (hbounded : Bornology.IsBounded (g '' Set.Icc a b))
    (hx : IsPartitionOn a b n x) {i : ℕ} (hi : i < n) :
    0 ≤ omega g x i * width x i := by
  have hxi : x i ≤ x (i + 1) := le_of_lt (hx.2.2 i hi)
  have hω : 0 ≤ omega g x i := by
    have hosc := abs_sub_le_oscillationOn g
      (Set.Icc (x i) (x (i + 1))) (Set.Icc a b)
      (partition_cell_subset hx hi) hbounded
      (u := x i) (v := x i) ⟨le_rfl, hxi⟩ ⟨le_rfl, hxi⟩
    simpa [omega] using hosc
  have hw : 0 ≤ width x i := by
    unfold width
    exact sub_nonneg.mpr hxi
  exact mul_nonneg hω hw

private theorem extend_partition_right (g : ℝ → ℝ) (a b B δ : ℝ)
    (n : ℕ) (x : ℕ → ℝ) (hbB : b < B) (hδ : 0 < δ)
    (hbounded : Bornology.IsBounded (g '' Set.Icc a B))
    (hx : IsPartitionOn a b n x) (hfine : Fine n x δ) :
    ∃ N : ℕ, ∃ y : ℕ → ℝ,
      IsPartitionOn a B N y ∧ Fine N y δ ∧
        oscillationSum g n x ≤ oscillationSum g N y := by
  obtain ⟨k, hk⟩ := exists_nat_gt ((B - b) / δ)
  have hqpos : 0 < (B - b) / δ := div_pos (sub_pos.mpr hbB) hδ
  have hkpos : 0 < k := by
    have : 0 < (k : ℝ) := lt_trans hqpos hk
    exact_mod_cast this
  have hkRpos : 0 < (k : ℝ) := by exact_mod_cast hkpos
  let step : ℝ := (B - b) / (k : ℝ)
  have hstepPos : 0 < step := div_pos (sub_pos.mpr hbB) hkRpos
  have hstepLt : step < δ := by
    apply (div_lt_iff₀ hkRpos).2
    have hmul := (div_lt_iff₀ hδ).1 hk
    nlinarith
  let N : ℕ := n + k
  let y : ℕ → ℝ := fun j =>
    if j ≤ n then x j else b + ((j - n : ℕ) : ℝ) * step
  have hyRight : ∀ {j : ℕ}, n ≤ j →
      y j = b + ((j - n : ℕ) : ℝ) * step := by
    intro j hj
    by_cases hle : j ≤ n
    · have hjeq : j = n := le_antisymm hle hj
      subst j
      simp [y, hx.2.1]
    · simp [y, hle]
  have hyPreserve : ∀ {i : ℕ}, i < n →
      y i = x i ∧ y (i + 1) = x (i + 1) := by
    intro i hi
    constructor
    · simp [y, Nat.le_of_lt hi]
    · simp [y, Nat.succ_le_iff.mpr hi]
  have hyPart : IsPartitionOn a B N y := by
    refine ⟨?_, ?_, ?_⟩
    · simp [y, hx.1]
    · have hnN : n ≤ N := by simp [N]
      rw [hyRight hnN]
      have hsub : N - n = k := by simp [N]
      rw [hsub]
      dsimp [step]
      field_simp [ne_of_gt hkRpos]
      ring
    · intro i hi
      by_cases hin : i < n
      · rcases hyPreserve hin with ⟨hi0, hi1⟩
        rw [hi0, hi1]
        exact hx.2.2 i hin
      · have hni : n ≤ i := Nat.le_of_not_gt hin
        rw [hyRight hni, hyRight (by omega)]
        have hsub : i + 1 - n = (i - n) + 1 := by omega
        rw [hsub]
        push_cast
        linarith
  have hyFine : Fine N y δ := by
    intro i hi
    by_cases hin : i < n
    · rcases hyPreserve hin with ⟨hi0, hi1⟩
      simpa [width, hi0, hi1] using hfine i hin
    · have hni : n ≤ i := Nat.le_of_not_gt hin
      rw [show width y i = step by
        unfold width
        rw [hyRight hni, hyRight (by omega)]
        have hsub : i + 1 - n = (i - n) + 1 := by omega
        rw [hsub]
        push_cast
        ring]
      exact hstepLt
  refine ⟨N, y, hyPart, hyFine, ?_⟩
  unfold oscillationSum
  calc
    (∑ i ∈ Finset.range n, omega g x i * width x i) =
        ∑ i ∈ Finset.range n, omega g y i * width y i := by
      apply Finset.sum_congr rfl
      intro i hi
      rcases hyPreserve (Finset.mem_range.mp hi) with ⟨hi0, hi1⟩
      simp [omega, width, hi0, hi1]
    _ ≤ ∑ i ∈ Finset.range N, omega g y i * width y i := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact Finset.range_mono (by simp [N])
      · intro i hiN hin
        exact oscillation_term_nonneg hbounded hyPart (Finset.mem_range.mp hiN)

private theorem extend_partition_left (g : ℝ → ℝ) (A a b δ : ℝ)
    (n : ℕ) (x : ℕ → ℝ) (hAa : A < a) (hδ : 0 < δ)
    (hbounded : Bornology.IsBounded (g '' Set.Icc A b))
    (hx : IsPartitionOn a b n x) (hfine : Fine n x δ) :
    ∃ N : ℕ, ∃ y : ℕ → ℝ,
      IsPartitionOn A b N y ∧ Fine N y δ ∧
        oscillationSum g n x ≤ oscillationSum g N y := by
  obtain ⟨m, hm⟩ := exists_nat_gt ((a - A) / δ)
  have hqpos : 0 < (a - A) / δ := div_pos (sub_pos.mpr hAa) hδ
  have hmpos : 0 < m := by
    have : 0 < (m : ℝ) := lt_trans hqpos hm
    exact_mod_cast this
  have hmRpos : 0 < (m : ℝ) := by exact_mod_cast hmpos
  let step : ℝ := (a - A) / (m : ℝ)
  have hstepPos : 0 < step := div_pos (sub_pos.mpr hAa) hmRpos
  have hstepLt : step < δ := by
    apply (div_lt_iff₀ hmRpos).2
    have hmul := (div_lt_iff₀ hδ).1 hm
    nlinarith
  let N : ℕ := m + n
  let y : ℕ → ℝ := fun j =>
    if j ≤ m then A + (j : ℝ) * step else x (j - m)
  have hyMiddle : ∀ {j : ℕ}, m ≤ j → y j = x (j - m) := by
    intro j hj
    by_cases hle : j ≤ m
    · have hjeq : j = m := le_antisymm hle hj
      subst j
      simp [y, hx.1, step, ne_of_gt hmRpos]
      field_simp [ne_of_gt hmRpos]
      ring
    · simp [y, hle]
  have hyPreserve : ∀ {i : ℕ}, i < n →
      y (m + i) = x i ∧ y (m + i + 1) = x (i + 1) := by
    intro i hi
    constructor
    · rw [hyMiddle (by omega)]
      congr 1
      omega
    · rw [hyMiddle (by omega)]
      congr 1
      omega
  have hyPart : IsPartitionOn A b N y := by
    refine ⟨?_, ?_, ?_⟩
    · simp [y]
    · have hmN : m ≤ N := by simp [N]
      rw [hyMiddle hmN]
      have hsub : N - m = n := by simp [N]
      rw [hsub, hx.2.1]
    · intro i hi
      by_cases him : i < m
      · have hi0 : i ≤ m := Nat.le_of_lt him
        have hi1 : i + 1 ≤ m := Nat.succ_le_iff.mpr him
        simp only [y, if_pos hi0, if_pos hi1]
        push_cast
        linarith
      · have hmi : m ≤ i := Nat.le_of_not_gt him
        rw [hyMiddle hmi, hyMiddle (by omega)]
        have hsub : i + 1 - m = (i - m) + 1 := by omega
        rw [hsub]
        apply hx.2.2
        dsimp [N] at hi
        omega
  have hyFine : Fine N y δ := by
    intro i hi
    by_cases him : i < m
    · have hi0 : i ≤ m := Nat.le_of_lt him
      have hi1 : i + 1 ≤ m := Nat.succ_le_iff.mpr him
      have hwidth : width y i = step := by
        unfold width
        simp only [y, if_pos hi0, if_pos hi1]
        push_cast
        ring
      rw [hwidth]
      exact hstepLt
    · have hmi : m ≤ i := Nat.le_of_not_gt him
      have hsub : i + 1 - m = (i - m) + 1 := by omega
      have hi' : i - m < n := by
        dsimp [N] at hi
        omega
      unfold width
      rw [hyMiddle hmi, hyMiddle (by omega), hsub]
      exact hfine (i - m) hi'
  refine ⟨N, y, hyPart, hyFine, ?_⟩
  unfold oscillationSum
  let s : Finset ℕ := (Finset.range n).image (fun i => m + i)
  have hsumEq :
      (∑ i ∈ Finset.range n, omega g x i * width x i) =
        ∑ j ∈ s, omega g y j * width y j := by
    calc
      (∑ i ∈ Finset.range n, omega g x i * width x i) =
          ∑ i ∈ Finset.range n,
            omega g y (m + i) * width y (m + i) := by
        apply Finset.sum_congr rfl
        intro i hi
        rcases hyPreserve (Finset.mem_range.mp hi) with ⟨hi0, hi1⟩
        simp [omega, width, hi0, hi1]
      _ = ∑ j ∈ s, omega g y j * width y j := by
        dsimp [s]
        rw [Finset.sum_image]
        intro i hi j hj hij
        exact Nat.add_left_cancel hij
  rw [hsumEq]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro j hj
    rcases Finset.mem_image.mp hj with ⟨i, hi, rfl⟩
    simp only [Finset.mem_range] at hi ⊢
    dsimp [N]
    omega
  · intro i hiN his
    exact oscillation_term_nonneg hbounded hyPart (Finset.mem_range.mp hiN)

theorem gap1 (f : ℝ → ℝ) (A B a b : ℝ)
    (hAa : A < a) (hbB : b < B) (hf : RiemannIntegrableOn f A B) :
    ∀ ε > 0, ∃ η > 0, ∀ n : ℕ, ∀ x : ℕ → ℝ,
      IsPartitionOn a b n x → Fine n x η →
        oscillationSum f n x < ε := by
  intro ε hε
  rcases hf.2 ε hε with ⟨η, hη, hfull⟩
  refine ⟨η, hη, ?_⟩
  intro n x hx hxfine
  have hAbounded : Bornology.IsBounded (f '' Set.Icc A b) :=
    hf.1.subset (Set.image_mono (Set.Icc_subset_Icc le_rfl (le_of_lt hbB)))
  rcases extend_partition_left f A a b η n x hAa hη hAbounded hx hxfine with
    ⟨N₁, y₁, hy₁, hfy₁, hsum₁⟩
  rcases extend_partition_right f A b B η N₁ y₁ hbB hη hf.1 hy₁ hfy₁ with
    ⟨N₂, y₂, hy₂, hfy₂, hsum₂⟩
  exact lt_of_le_of_lt (le_trans hsum₁ hsum₂) (hfull N₂ y₂ hy₂ hfy₂)

theorem gap2 (f : ℝ → ℝ) (A B : ℝ)
    (hf : RiemannIntegrableOn f A B) :
    ∀ ε > 0, ∃ η > 0, ∀ A' B' : ℝ, ∀ n : ℕ, ∀ x : ℕ → ℝ,
      Set.Icc A' B' ⊆ Set.Icc A B →
      IsPartitionOn A' B' n x → Fine n x η →
        oscillationSum f n x < ε := by
  intro ε hε
  rcases hf.2 ε hε with ⟨η, hη, hfull⟩
  refine ⟨η, hη, ?_⟩
  intro A' B' n x hsubset hx hxfine
  have hA'B' : A' ≤ B' := by
    rw [← hx.1, ← hx.2.1]
    exact partition_mono hx (Nat.zero_le n) le_rfl
  have hleft : A ≤ A' := (hsubset ⟨le_rfl, hA'B'⟩).1
  have hright : B' ≤ B := (hsubset ⟨hA'B', le_rfl⟩).2
  by_cases hAA' : A' = A
  · subst A'
    by_cases hB'B : B' = B
    · subst B'
      exact hfull n x hx hxfine
    · have hB'Blt : B' < B := lt_of_le_of_ne hright hB'B
      rcases extend_partition_right f A B' B η n x hB'Blt hη hf.1 hx hxfine with
        ⟨N, y, hy, hfy, hsum⟩
      exact lt_of_le_of_lt hsum (hfull N y hy hfy)
  · have hAA'lt : A < A' := lt_of_le_of_ne hleft (Ne.symm hAA')
    by_cases hB'B : B' = B
    · subst B'
      rcases extend_partition_left f A A' B η n x hAA'lt hη hf.1 hx hxfine with
        ⟨N, y, hy, hfy, hsum⟩
      exact lt_of_le_of_lt hsum (hfull N y hy hfy)
    · have hB'Blt : B' < B := lt_of_le_of_ne hright hB'B
      have hAB'bounded : Bornology.IsBounded (f '' Set.Icc A B') :=
        hf.1.subset (Set.image_mono (Set.Icc_subset_Icc le_rfl hright))
      rcases extend_partition_left f A A' B' η n x hAA'lt hη
          hAB'bounded hx hxfine with
        ⟨N₁, y₁, hy₁, hfy₁, hsum₁⟩
      rcases extend_partition_right f A B' B η N₁ y₁ hB'Blt hη hf.1 hy₁ hfy₁ with
        ⟨N₂, y₂, hy₂, hfy₂, hsum₂⟩
      exact lt_of_le_of_lt (le_trans hsum₁ hsum₂) (hfull N₂ y₂ hy₂ hfy₂)

theorem gap3 (A B a b : ℝ) (hAa : A < a) (hab : a < b) (hbB : b < B) :
    ∃ δ > 0, ∀ h, 0 < h → h < δ →
      ∃ n : ℕ, 0 < n ∧
        a + (2 * (n : ℝ) - 2) * h < b ∧
        b ≤ a + 2 * (n : ℝ) * h ∧
        a + (2 * (n : ℝ) + 1) * h < B := by
  refine ⟨(B - b) / 4, div_pos (sub_pos.mpr hbB) (by norm_num), ?_⟩
  intro h hhpos hhδ
  let q : ℝ := (b - a) / (2 * h)
  have hden : 0 < 2 * h := by positivity
  have hqpos : 0 < q := by
    dsimp [q]
    exact div_pos (sub_pos.mpr hab) hden
  let n : ℕ := Nat.ceil q
  have hqle : q ≤ (n : ℝ) := Nat.le_ceil q
  have hnlt : (n : ℝ) < q + 1 := Nat.ceil_lt_add_one hqpos.le
  have hnpos : 0 < n := by
    have : 0 < (n : ℝ) := lt_of_lt_of_le hqpos hqle
    exact_mod_cast this
  have hcover : b ≤ a + 2 * (n : ℝ) * h := by
    have hmul := (div_le_iff₀ hden).mp hqle
    nlinarith
  have hprevious : a + (2 * (n : ℝ) - 2) * h < b := by
    have hnlt' : (n : ℝ) - 1 < q := by linarith
    have hmul := (lt_div_iff₀ hden).mp hnlt'
    nlinarith
  have houter : a + (2 * (n : ℝ) + 1) * h < B := by
    have hnlt' : (n : ℝ) - 1 < q := by linarith
    have hmul := (lt_div_iff₀ hden).mp hnlt'
    have hsmall : 4 * h < B - b := by
      nlinarith
    nlinarith
  exact ⟨n, hnpos, hprevious, hcover, houter⟩

theorem gap4 (f : ℝ → ℝ) (a b h : ℝ) (n : ℕ)
    (hab : a ≤ b) (hcover : b ≤ a + 2 * (n : ℝ) * h)
    (hint : IntervalIntegrable (fun x => |f (x + h) - f x|)
      volume a (a + 2 * (n : ℝ) * h)) :
    translationError f a b h ≤
      ∫ x in a..(a + 2 * (n : ℝ) * h), |f (x + h) - f x| := by
  unfold translationError
  exact intervalIntegral.integral_mono_interval le_rfl hab hcover
    (Filter.Eventually.of_forall fun x => abs_nonneg _) hint

theorem gap5 (f : ℝ → ℝ) (a h : ℝ) (n : ℕ)
    (hh : 0 < h)
    (hbounded : Bornology.IsBounded
      (f '' Set.Icc a (a + (2 * (n : ℝ) + 1) * h)))
    (hint : IntervalIntegrable (fun x => |f (x + h) - f x|)
      volume a (a + 2 * (n : ℝ) * h)) :
    (∫ x in a..(a + 2 * (n : ℝ) * h), |f (x + h) - f x|) ≤
      ∑ i ∈ Finset.range (2 * n), omegaH f a h i * h := by
  let G : ℝ → ℝ := fun x => |f (x + h) - f x|
  let p : ℕ → ℝ := fun i => a + (i : ℝ) * h
  have hwhole : a ≤ a + 2 * (n : ℝ) * h := by
    exact le_add_of_nonneg_right
      (mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg n)) hh.le)
  have hcellInt :
      ∀ i < 2 * n, IntervalIntegrable G volume (p i) (p (i + 1)) := by
    intro i hi
    apply hint.mono_set
    have hcell : p i ≤ p (i + 1) := by
      dsimp [p]
      have hiR : (i : ℝ) ≤ ((i + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ i
      simpa [add_comm] using
        (add_le_add_left (mul_le_mul_of_nonneg_right hiR hh.le) a)
    have hlast : p (i + 1) ≤ a + 2 * (n : ℝ) * h := by
      have hi : i + 1 ≤ 2 * n := by omega
      have hiR : (i + 1 : ℕ) ≤ 2 * n := hi
      dsimp [p]
      push_cast
      have hiR' : ((i + 1 : ℕ) : ℝ) ≤ ((2 * n : ℕ) : ℝ) := by exact_mod_cast hiR
      push_cast at hiR'
      simpa [add_comm] using
        (add_le_add_left (mul_le_mul_of_nonneg_right hiR' hh.le) a)
    rw [Set.uIcc_of_le hcell, Set.uIcc_of_le hwhole]
    exact Set.Icc_subset_Icc (by
      dsimp [p]
      exact le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg i) hh.le)) hlast
  have hdecomp :
      (∑ i ∈ Finset.range (2 * n), ∫ x in p i..p (i + 1), G x) =
        ∫ x in a..a + 2 * (n : ℝ) * h, G x := by
    have hsum := intervalIntegral.sum_integral_adjacent_intervals
      (μ := volume) (f := G) (a := p) hcellInt
    simpa [p] using hsum
  have hcellBound :
      ∀ i < 2 * n,
        (∫ x in p i..p (i + 1), G x) ≤ omegaH f a h i * h := by
    intro i hi
    have hcell : p i ≤ p (i + 1) := by
      dsimp [p]
      have hiR : (i : ℝ) ≤ ((i + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ i
      simpa [add_comm] using
        (add_le_add_left (mul_le_mul_of_nonneg_right hiR hh.le) a)
    have hlocalGlobal :
        Set.Icc (a + (i : ℝ) * h) (a + ((i : ℝ) + 2) * h) ⊆
          Set.Icc a (a + (2 * (n : ℝ) + 1) * h) := by
      intro y hy
      have hiNat : i + 2 ≤ 2 * n + 1 := by omega
      have hiR : (i : ℝ) + 2 ≤ 2 * (n : ℝ) + 1 := by exact_mod_cast hiNat
      constructor
      · have hi0 : 0 ≤ (i : ℝ) := Nat.cast_nonneg i
        exact le_trans (le_add_of_nonneg_right (mul_nonneg hi0 hh.le)) hy.1
      · exact le_trans hy.2 (by
          simpa [add_comm] using
            (add_le_add_left (mul_le_mul_of_nonneg_right hiR hh.le) a))
    have hpointwise :
        ∀ x ∈ Set.Icc (p i) (p (i + 1)), G x ≤ omegaH f a h i := by
      intro x hx
      have hxlocal :
          x ∈ Set.Icc (a + (i : ℝ) * h) (a + ((i : ℝ) + 2) * h) := by
        dsimp [p] at hx
        constructor
        · exact hx.1
        · have hiR : (i : ℝ) + 1 ≤ (i : ℝ) + 2 := by linarith
          exact le_trans hx.2 (by
            simpa [add_comm] using
              (add_le_add_left (mul_le_mul_of_nonneg_right hiR hh.le) a))
      have hxshift :
          x + h ∈ Set.Icc (a + (i : ℝ) * h) (a + ((i : ℝ) + 2) * h) := by
        dsimp [p] at hx
        push_cast at hx
        constructor
        · exact le_trans hx.1 (le_add_of_nonneg_right hh.le)
        · calc
            x + h ≤ (a + ((i : ℝ) + 1) * h) + h := by
              simpa [add_comm] using add_le_add_right hx.2 h
            _ = a + ((i : ℝ) + 2) * h := by ring
      have hosc := abs_sub_le_oscillationOn f
        (Set.Icc (a + (i : ℝ) * h) (a + ((i : ℝ) + 2) * h))
        (Set.Icc a (a + (2 * (n : ℝ) + 1) * h))
        hlocalGlobal hbounded hxshift hxlocal
      simpa [G, omegaH] using hosc
    calc
      (∫ x in p i..p (i + 1), G x) ≤
          ∫ _x in p i..p (i + 1), omegaH f a h i :=
        intervalIntegral.integral_mono_on hcell (hcellInt i hi)
          intervalIntegrable_const hpointwise
      _ = omegaH f a h i * h := by
        simp [p]
        ring
  rw [← hdecomp]
  exact Finset.sum_le_sum fun i hi => hcellBound i (Finset.mem_range.mp hi)

theorem gap6 (f : ℝ → ℝ) (a h : ℝ) (n : ℕ) :
    (∑ i ∈ Finset.range (2 * n), omegaH f a h i * h) =
      (1 / 2 : ℝ) * evenOscSum f a h n +
        (1 / 2 : ℝ) * oddOscSum f a h n := by
  have heven :
      (∑ i ∈ Finset.range n, omegaH f a h (2 * i) * (2 * h)) =
        2 * ∑ i ∈ Finset.range n, omegaH f a h (2 * i) * h := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hodd :
      (∑ i ∈ Finset.range n, omegaH f a h (2 * i + 1) * (2 * h)) =
        2 * ∑ i ∈ Finset.range n, omegaH f a h (2 * i + 1) * h := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [sum_range_even_odd_pairs]
  simp only [Finset.sum_add_distrib, evenOscSum, oddOscSum]
  rw [heven, hodd]
  ring

theorem gap7 (f : ℝ → ℝ) (a h ε : ℝ) (n : ℕ)
    (heven : evenOscSum f a h n < ε) :
    evenOscSum f a h n < ε := by
  exact heven

theorem gap8 (f : ℝ → ℝ) (a h ε : ℝ) (n : ℕ)
    (hodd : oddOscSum f a h n < ε) :
    oddOscSum f a h n < ε := by
  exact hodd

theorem gap9 (f : ℝ → ℝ) (a b h ε : ℝ)
    (hε : 0 < ε)
    (hbound : translationError f a b h < ε / 2 + ε / 2) :
    translationError f a b h < ε / 2 + ε / 2 := by
  exact hbound

theorem gap10 (ε : ℝ) :
    ε / 2 + ε / 2 = ε := by
  ring

theorem gap11 (f : ℝ → ℝ) (a b h ε : ℝ)
    (hbound : translationError f a b h < ε / 2 + ε / 2) :
    translationError f a b h < ε := by
  simpa [gap10 ε] using hbound

private theorem translationError_le_grid (f : ℝ → ℝ) (a b h : ℝ) (n : ℕ)
    (hab : a ≤ b) (hh : 0 < h) (hcover : b ≤ a + 2 * (n : ℝ) * h)
    (hbounded : Bornology.IsBounded
      (f '' Set.Icc a (a + (2 * (n : ℝ) + 1) * h))) :
    translationError f a b h ≤
      ∑ i ∈ Finset.range (2 * n), omegaH f a h i * h := by
  let G : ℝ → ℝ := fun x => |f (x + h) - f x|
  have hterm_nonneg :
      ∀ i < 2 * n, 0 ≤ omegaH f a h i * h := by
    intro i hi
    have hlocalGlobal :
        Set.Icc (a + (i : ℝ) * h) (a + ((i : ℝ) + 2) * h) ⊆
          Set.Icc a (a + (2 * (n : ℝ) + 1) * h) := by
      intro y hy
      have hiNat : i + 2 ≤ 2 * n + 1 := by omega
      have hiR : (i : ℝ) + 2 ≤ 2 * (n : ℝ) + 1 := by exact_mod_cast hiNat
      constructor
      · exact le_trans
          (le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg i) hh.le)) hy.1
      · exact le_trans hy.2 (by
          simpa [add_comm] using
            (add_le_add_left (mul_le_mul_of_nonneg_right hiR hh.le) a))
    have horder :
        a + (i : ℝ) * h ≤ a + ((i : ℝ) + 2) * h := by
      have : (i : ℝ) ≤ (i : ℝ) + 2 := by linarith
      simpa [add_comm] using
        (add_le_add_left (mul_le_mul_of_nonneg_right this hh.le) a)
    have hosc := abs_sub_le_oscillationOn f
      (Set.Icc (a + (i : ℝ) * h) (a + ((i : ℝ) + 2) * h))
      (Set.Icc a (a + (2 * (n : ℝ) + 1) * h))
      hlocalGlobal hbounded
      (u := a + (i : ℝ) * h) (v := a + (i : ℝ) * h)
      ⟨le_rfl, horder⟩ ⟨le_rfl, horder⟩
    have hω : 0 ≤ omegaH f a h i := by simpa [omegaH] using hosc
    exact mul_nonneg hω hh.le
  by_cases hint : IntervalIntegrable G volume a b
  · let q : ℕ → ℝ := fun i => min (a + (i : ℝ) * h) b
    have hqzero : q 0 = a := by simp [q, min_eq_left hab]
    have hqend : q (2 * n) = b := by
      have hqform : q (2 * n) = min (a + 2 * (n : ℝ) * h) b := by
        simp [q]
      rw [hqform]
      exact min_eq_right hcover
    have hqmono : ∀ i, q i ≤ q (i + 1) := by
      intro i
      apply min_le_min
      · have hiR : (i : ℝ) ≤ ((i + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ i
        simpa [add_comm] using
          (add_le_add_left (mul_le_mul_of_nonneg_right hiR hh.le) a)
      · exact le_rfl
    have hqmem : ∀ i ≤ 2 * n, q i ∈ Set.Icc a b := by
      intro i hi
      constructor
      · apply le_min
        · exact le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg i) hh.le)
        · exact hab
      · exact min_le_right _ _
    have hcellInt :
        ∀ i < 2 * n, IntervalIntegrable G volume (q i) (q (i + 1)) := by
      intro i hi
      apply hint.mono_set
      rw [Set.uIcc_of_le (hqmono i), Set.uIcc_of_le hab]
      exact Set.Icc_subset_Icc (hqmem i (Nat.le_of_lt hi)).1
        (hqmem (i + 1) (Nat.succ_le_iff.mpr hi)).2
    have hdecomp :
        (∑ i ∈ Finset.range (2 * n), ∫ x in q i..q (i + 1), G x) =
          ∫ x in a..b, G x := by
      have hsum := intervalIntegral.sum_integral_adjacent_intervals
        (μ := volume) (f := G) (a := q) hcellInt
      simpa [hqzero, hqend] using hsum
    have hcellBound :
        ∀ i < 2 * n,
          (∫ x in q i..q (i + 1), G x) ≤ omegaH f a h i * h := by
      intro i hi
      by_cases hactive : a + (i : ℝ) * h < b
      · have hqi : q i = a + (i : ℝ) * h := min_eq_left hactive.le
        have hqnext : q (i + 1) ≤ a + ((i : ℝ) + 1) * h := by
          dsimp [q]
          push_cast
          exact min_le_left _ _
        have hstep : q (i + 1) - q i ≤ h := by
          rw [hqi]
          linarith
        have hlocalGlobal :
            Set.Icc (a + (i : ℝ) * h) (a + ((i : ℝ) + 2) * h) ⊆
              Set.Icc a (a + (2 * (n : ℝ) + 1) * h) := by
          intro y hy
          have hiNat : i + 2 ≤ 2 * n + 1 := by omega
          have hiR : (i : ℝ) + 2 ≤ 2 * (n : ℝ) + 1 := by exact_mod_cast hiNat
          constructor
          · exact le_trans
              (le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg i) hh.le)) hy.1
          · exact le_trans hy.2 (by
              simpa [add_comm] using
                (add_le_add_left (mul_le_mul_of_nonneg_right hiR hh.le) a))
        have hpointwise :
            ∀ x ∈ Set.Icc (q i) (q (i + 1)), G x ≤ omegaH f a h i := by
          intro x hx
          have hxlocal :
              x ∈ Set.Icc (a + (i : ℝ) * h) (a + ((i : ℝ) + 2) * h) := by
            constructor
            · simpa [hqi] using hx.1
            · exact le_trans hx.2 (le_trans hqnext (by
                have hiR : (i : ℝ) + 1 ≤ (i : ℝ) + 2 := by linarith
                simpa [add_comm] using
                  (add_le_add_left (mul_le_mul_of_nonneg_right hiR hh.le) a)))
          have hxshift :
              x + h ∈ Set.Icc (a + (i : ℝ) * h) (a + ((i : ℝ) + 2) * h) := by
            constructor
            · exact le_trans hxlocal.1 (le_add_of_nonneg_right hh.le)
            · calc
                x + h ≤ (a + ((i : ℝ) + 1) * h) + h := by
                  simpa [add_comm] using add_le_add_right (le_trans hx.2 hqnext) h
                _ = a + ((i : ℝ) + 2) * h := by ring
          have hosc := abs_sub_le_oscillationOn f
            (Set.Icc (a + (i : ℝ) * h) (a + ((i : ℝ) + 2) * h))
            (Set.Icc a (a + (2 * (n : ℝ) + 1) * h))
            hlocalGlobal hbounded hxshift hxlocal
          simpa [G, omegaH] using hosc
        have hω : 0 ≤ omegaH f a h i := by
          have := hterm_nonneg i hi
          nlinarith
        calc
          (∫ x in q i..q (i + 1), G x) ≤
              ∫ _x in q i..q (i + 1), omegaH f a h i :=
            intervalIntegral.integral_mono_on (hqmono i) (hcellInt i hi)
              intervalIntegrable_const hpointwise
          _ = omegaH f a h i * (q (i + 1) - q i) := by simp [mul_comm]
          _ ≤ omegaH f a h i * h := mul_le_mul_of_nonneg_left hstep hω
      · have hqi : q i = b := min_eq_right (le_of_not_gt hactive)
        have hqnext : q (i + 1) = b := by
          apply min_eq_right
          have hraw : a + (i : ℝ) * h ≤ a + ((i + 1 : ℕ) : ℝ) * h := by
            have hiR : (i : ℝ) ≤ ((i + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ i
            simpa [add_comm] using
              (add_le_add_left (mul_le_mul_of_nonneg_right hiR hh.le) a)
          exact le_trans (le_of_not_gt hactive) hraw
        rw [hqi, hqnext]
        simp only [intervalIntegral.integral_same]
        exact hterm_nonneg i hi
    unfold translationError
    change (∫ x in a..b, G x) ≤ _
    rw [← hdecomp]
    exact Finset.sum_le_sum fun i hi => hcellBound i (Finset.mem_range.mp hi)
  · unfold translationError
    change (∫ x in a..b, G x) ≤ _
    rw [intervalIntegral.integral_undef hint]
    exact Finset.sum_nonneg fun i hi => hterm_nonneg i (Finset.mem_range.mp hi)

private theorem translationError_lt_of_grid (f : ℝ → ℝ) (A B c d h ε η : ℝ)
    (n : ℕ) (hf : RiemannIntegrableOn f A B)
    (hosc : ∀ A' B' : ℝ, ∀ m : ℕ, ∀ x : ℕ → ℝ,
      Set.Icc A' B' ⊆ Set.Icc A B →
      IsPartitionOn A' B' m x → Fine m x η →
        oscillationSum f m x < ε)
    (hAc : A < c) (hcd : c ≤ d)
    (hh : 0 < h) (hwidth : 2 * h < η)
    (hcover : d ≤ c + 2 * (n : ℝ) * h)
    (houter : c + (2 * (n : ℝ) + 1) * h < B) :
    translationError f c d h < ε := by
  let xe : ℕ → ℝ := fun i => c + 2 * (i : ℝ) * h
  let xo : ℕ → ℝ := fun i => c + (2 * (i : ℝ) + 1) * h
  have hxe : IsPartitionOn c (c + 2 * (n : ℝ) * h) n xe := by
    refine ⟨?_, ?_, ?_⟩
    · simp [xe]
    · simp [xe]
    · intro i hi
      dsimp [xe]
      push_cast
      nlinarith
  have hxo : IsPartitionOn (c + h) (c + (2 * (n : ℝ) + 1) * h) n xo := by
    refine ⟨?_, ?_, ?_⟩
    · simp [xo]
    · simp [xo]
    · intro i hi
      dsimp [xo]
      push_cast
      nlinarith
  have hxeFine : Fine n xe η := by
    intro i hi
    dsimp [width, xe]
    push_cast
    nlinarith
  have hxoFine : Fine n xo η := by
    intro i hi
    dsimp [width, xo]
    push_cast
    nlinarith
  have heUpper : c + 2 * (n : ℝ) * h < B := by nlinarith
  have hxeSub : Set.Icc c (c + 2 * (n : ℝ) * h) ⊆ Set.Icc A B := by
    intro x hx
    exact ⟨le_trans hAc.le hx.1, le_trans hx.2 heUpper.le⟩
  have hxoSub :
      Set.Icc (c + h) (c + (2 * (n : ℝ) + 1) * h) ⊆ Set.Icc A B := by
    intro x hx
    constructor
    · exact le_trans (by linarith : A ≤ c + h) hx.1
    · exact le_trans hx.2 houter.le
  have heEq : oscillationSum f n xe = evenOscSum f c h n := by
    unfold oscillationSum evenOscSum
    apply Finset.sum_congr rfl
    intro i hi
    simp only [omega, omegaH, width]
    dsimp [xe]
    push_cast
    congr 2 <;> ring_nf
  have hoEq : oscillationSum f n xo = oddOscSum f c h n := by
    unfold oscillationSum oddOscSum
    apply Finset.sum_congr rfl
    intro i hi
    simp only [omega, omegaH, width]
    dsimp [xo]
    push_cast
    congr 2 <;> ring_nf
  have he : evenOscSum f c h n < ε := by
    rw [← heEq]
    exact hosc c (c + 2 * (n : ℝ) * h) n xe hxeSub hxe hxeFine
  have ho : oddOscSum f c h n < ε := by
    rw [← hoEq]
    exact hosc (c + h) (c + (2 * (n : ℝ) + 1) * h) n xo hxoSub hxo hxoFine
  have hbounded : Bornology.IsBounded
      (f '' Set.Icc c (c + (2 * (n : ℝ) + 1) * h)) :=
    hf.1.subset (Set.image_mono (Set.Icc_subset_Icc hAc.le houter.le))
  have herr := translationError_le_grid f c d h n hcd hh hcover hbounded
  have hsum :
      (∑ i ∈ Finset.range (2 * n), omegaH f c h i * h) < ε := by
    rw [gap6]
    nlinarith
  exact lt_of_le_of_lt herr hsum

private theorem exists_grid_of_four_mul_lt (c d B h : ℝ)
    (hcd : c < d) (hh : 0 < h) (hsmall : 4 * h < B - d) :
    ∃ n : ℕ, 0 < n ∧
      c + (2 * (n : ℝ) - 2) * h < d ∧
      d ≤ c + 2 * (n : ℝ) * h ∧
      c + (2 * (n : ℝ) + 1) * h < B := by
  let q : ℝ := (d - c) / (2 * h)
  have hden : 0 < 2 * h := by positivity
  have hqpos : 0 < q := by
    dsimp [q]
    exact div_pos (sub_pos.mpr hcd) hden
  let n : ℕ := Nat.ceil q
  have hqle : q ≤ (n : ℝ) := Nat.le_ceil q
  have hnlt : (n : ℝ) < q + 1 := Nat.ceil_lt_add_one hqpos.le
  have hnpos : 0 < n := by
    have : 0 < (n : ℝ) := lt_of_lt_of_le hqpos hqle
    exact_mod_cast this
  have hcover : d ≤ c + 2 * (n : ℝ) * h := by
    have hmul := (div_le_iff₀ hden).mp hqle
    nlinarith
  have hprevious : c + (2 * (n : ℝ) - 2) * h < d := by
    have hnlt' : (n : ℝ) - 1 < q := by linarith
    have hmul := (lt_div_iff₀ hden).mp hnlt'
    nlinarith
  have houter : c + (2 * (n : ℝ) + 1) * h < B := by
    have hnlt' : (n : ℝ) - 1 < q := by linarith
    have hmul := (lt_div_iff₀ hden).mp hnlt'
    nlinarith
  exact ⟨n, hnpos, hprevious, hcover, houter⟩

private theorem translationError_shift_to_positive (f : ℝ → ℝ) (a b h : ℝ) :
    translationError f a b h = translationError f (a + h) (b + h) (-h) := by
  unfold translationError
  rw [← intervalIntegral.integral_comp_add_right
    (f := fun y => |f (y + -h) - f y|) h]
  apply intervalIntegral.integral_congr
  intro x hx
  change |f (x + h) - f x| = |f (x + h + -h) - f (x + h)|
  rw [show x + h + -h = x by ring, abs_sub_comm]

theorem gap12 (f : ℝ → ℝ) (A B a b : ℝ)
    (hAa : A < a) (hab : a < b) (hbB : b < B)
    (hf : RiemannIntegrableOn f A B) :
    Tendsto (translationError f a b)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (0 : ℝ)) := by
  refine Metric.tendsto_nhdsWithin_nhds.2 ?_
  intro ε hε
  rcases gap2 f A B hf ε hε with ⟨η, hη, hosc⟩
  rcases gap3 A B a b hAa hab hbB with ⟨δ, hδ, hgrid⟩
  refine ⟨min (η / 2) δ, lt_min (half_pos hη) hδ, ?_⟩
  intro h hh hdist
  have hhpos : 0 < h := hh
  have hhmin : h < min (η / 2) δ := by
    simpa [Real.dist_eq, abs_of_pos hhpos] using hdist
  have hhη : 2 * h < η := by
    have := lt_of_lt_of_le hhmin (min_le_left _ _)
    linarith
  have hhδ : h < δ := lt_of_lt_of_le hhmin (min_le_right _ _)
  rcases hgrid h hhpos hhδ with ⟨n, hn, hprevious, hcover, houter⟩
  have herr := translationError_lt_of_grid f A B a b h ε η n hf hosc
    hAa hab.le hhpos hhη hcover houter
  have hnonneg : 0 ≤ translationError f a b h := by
    unfold translationError
    exact intervalIntegral.integral_nonneg hab.le (fun x hx => abs_nonneg _)
  simpa [Real.dist_eq, abs_of_nonneg hnonneg] using herr

theorem gap13 (f : ℝ → ℝ) (A B a b : ℝ)
    (hAa : A < a) (hab : a < b) (hbB : b < B)
    (hf : RiemannIntegrableOn f A B) :
    Tendsto (translationError f a b)
      (nhdsWithin 0 (Set.Iio 0)) (nhds (0 : ℝ)) := by
  refine Metric.tendsto_nhdsWithin_nhds.2 ?_
  intro ε hε
  rcases gap2 f A B hf ε hε with ⟨η, hη, hosc⟩
  have hleft : 0 < a - A := sub_pos.mpr hAa
  have hright : 0 < (B - b) / 4 := div_pos (sub_pos.mpr hbB) (by norm_num)
  let ρ := min (η / 2) (min (a - A) ((B - b) / 4))
  have hρ : 0 < ρ := lt_min (half_pos hη) (lt_min hleft hright)
  refine ⟨ρ, hρ, ?_⟩
  intro h hh hdist
  have hhneg : h < 0 := hh
  let t : ℝ := -h
  have htpos : 0 < t := by dsimp [t]; linarith
  have htρ : t < ρ := by
    have habs : |h| < ρ := by simpa [Real.dist_eq] using hdist
    simpa [t, abs_of_neg hhneg] using habs
  have htη : 2 * t < η := by
    have := lt_of_lt_of_le htρ (min_le_left _ _)
    linarith
  have htleft : t < a - A :=
    lt_of_lt_of_le htρ (le_trans (min_le_right _ _) (min_le_left _ _))
  have htright : t < (B - b) / 4 :=
    lt_of_lt_of_le htρ (le_trans (min_le_right _ _) (min_le_right _ _))
  let c : ℝ := a + h
  let d : ℝ := b + h
  have hAc : A < c := by dsimp [c, t] at htleft ⊢; linarith
  have hcd : c < d := by dsimp [c, d]; linarith
  have hsmall : 4 * t < B - d := by
    dsimp [d, t]
    have : 4 * (-h) < B - b := by
      have hfour : (0 : ℝ) < 4 := by norm_num
      simpa [t, mul_comm] using (lt_div_iff₀ hfour).mp htright
    linarith
  rcases exists_grid_of_four_mul_lt c d B t hcd htpos hsmall with
    ⟨n, hn, hprevious, hcover, houter⟩
  have hpositive := translationError_lt_of_grid f A B c d t ε η n hf hosc
    hAc hcd.le htpos htη hcover houter
  have herr : translationError f a b h < ε := by
    rw [translationError_shift_to_positive]
    simpa [c, d, t] using hpositive
  have hnonneg : 0 ≤ translationError f a b h := by
    unfold translationError
    exact intervalIntegral.integral_nonneg hab.le (fun x hx => abs_nonneg _)
  simpa [Real.dist_eq, abs_of_nonneg hnonneg] using herr

theorem gap14 (f : ℝ → ℝ) (A B a b : ℝ)
    (hAa : A < a) (hab : a < b) (hbB : b < B)
    (hf : RiemannIntegrableOn f A B) :
    Tendsto (translationError f a b) (nhds 0) (nhds (0 : ℝ)) := by
  have hright := gap12 f A B a b hAa hab hbB hf
  have hleft := gap13 f A B a b hAa hab hbB hf
  have hzero : translationError f a b 0 = 0 := by
    simp [translationError]
  have hpoint :
      Tendsto (translationError f a b) (nhdsWithin 0 ({0} : Set ℝ))
        (nhds (0 : ℝ)) := by
    rw [nhdsWithin_singleton]
    simpa [hzero] using tendsto_pure_nhds (translationError f a b) 0
  have hrightClosed :
      Tendsto (translationError f a b) (nhdsWithin 0 (Set.Ici 0))
        (nhds (0 : ℝ)) := by
    rw [← nhdsGT_sup_nhdsWithin_singleton]
    exact tendsto_sup.mpr ⟨hright, hpoint⟩
  have hsup :
      Tendsto (translationError f a b)
        (nhdsWithin 0 (Set.Iio 0) ⊔ nhdsWithin 0 (Set.Ici 0))
        (nhds (0 : ℝ)) :=
    tendsto_sup.mpr ⟨hleft, hrightClosed⟩
  simpa only [nhdsLT_sup_nhdsGE] using hsup

theorem gap15 (f : ℝ → ℝ) (A B ε : ℝ)
    (hAB : A ≤ B) (hε : 0 < ε)
    (hf : IntervalIntegrable f volume A B) :
    ∃ φ : ℝ → ℝ, ContinuousOn φ (Set.Icc A B) ∧
      (∫ x in A..B, |f x - φ x|) < ε / 4 := by
  have hf' : Integrable f (volume.restrict (Set.Ioc A B)) := hf.1
  have heighth : 0 < ε / 8 := by linarith
  rcases hf'.exists_boundedContinuous_integral_sub_le heighth with
    ⟨φ, hφ, hφint⟩
  refine ⟨φ, φ.continuous.continuousOn, ?_⟩
  have hstrict :
      (∫ x, ‖f x - φ x‖ ∂volume.restrict (Set.Ioc A B)) < ε / 4 := by
    exact lt_of_le_of_lt hφ (by linarith)
  rw [intervalIntegral.integral_of_le hAB]
  simpa [Real.norm_eq_abs] using hstrict

theorem gap16 (φ : ℝ → ℝ) (A B ε : ℝ)
    (hφ : ContinuousOn φ (Set.Icc A B)) (hε : 0 < ε) :
    UniformContinuousOn φ (Set.Icc A B) := by
  exact (isCompact_Icc.uniformContinuousOn_of_continuous hφ)

theorem gap17 (φ : ℝ → ℝ) (A B a b ε : ℝ)
    (hab : a < b)
    (hφ : UniformContinuousOn φ (Set.Icc A B)) (hε : 0 < ε) :
    ∃ δ > 0, ∀ x' ∈ Set.Icc A B, ∀ x'' ∈ Set.Icc A B,
      |x' - x''| < δ →
        |φ x' - φ x''| < ε / (2 * (b - a)) := by
  have htarget : 0 < ε / (2 * (b - a)) := by
    exact div_pos hε (mul_pos (by norm_num) (sub_pos.mpr hab))
  rcases Metric.uniformContinuousOn_iff.mp hφ
      (ε / (2 * (b - a))) htarget with ⟨δ, hδ, hmod⟩
  refine ⟨δ, hδ, ?_⟩
  intro x' hx' x'' hx'' hxx
  have hdist : dist x' x'' < δ := by simpa [Real.dist_eq] using hxx
  have := hmod x' hx' x'' hx'' hdist
  simpa [Real.dist_eq] using this

theorem gap18 (f φ : ℝ → ℝ) (a b h : ℝ) (hab : a ≤ b)
    (hint0 : IntervalIntegrable (fun x => |f (x + h) - f x|) volume a b)
    (hint1 : IntervalIntegrable (fun x => |f (x + h) - φ (x + h)|) volume a b)
    (hint2 : IntervalIntegrable (fun x => |φ (x + h) - φ x|) volume a b)
    (hint3 : IntervalIntegrable (fun x => |f x - φ x|) volume a b) :
    translationError f a b h ≤
      (∫ x in a..b, |f (x + h) - φ (x + h)|) +
      (∫ x in a..b, |φ (x + h) - φ x|) +
      (∫ x in a..b, |f x - φ x|) := by
  unfold translationError
  rw [← intervalIntegral.integral_add hint1 hint2,
    ← intervalIntegral.integral_add (hint1.add hint2) hint3]
  apply intervalIntegral.integral_mono_on hab hint0 ((hint1.add hint2).add hint3)
  intro x hx
  have hfirst := abs_add_le (f (x + h) - φ (x + h)) (φ (x + h) - φ x)
  have hsecond := abs_add_le
    ((f (x + h) - φ (x + h)) + (φ (x + h) - φ x)) (φ x - f x)
  calc
    |f (x + h) - f x| =
        |(f (x + h) - φ (x + h)) + (φ (x + h) - φ x) + (φ x - f x)| := by
          congr 1
          ring
    _ ≤ |f (x + h) - φ (x + h)| + |φ (x + h) - φ x| + |φ x - f x| := by
      linarith
    _ = |f (x + h) - φ (x + h)| + |φ (x + h) - φ x| + |f x - φ x| := by
      rw [abs_sub_comm (φ x) (f x)]

theorem gap19 (f φ : ℝ → ℝ) (A B a b h : ℝ)
    (hAa : A < a) (hab : a ≤ b) (hbB : b < B)
    (hh : |h| < min (a - A) (B - b))
    (hφ : ContinuousOn φ (Set.Icc A B))
    (hint : IntervalIntegrable (fun x => |f x - φ x|) volume A B) :
    translationError f a b h ≤
      2 * (∫ x in A..B, |f x - φ x|) +
        ∫ x in a..b, |φ (x + h) - φ x| := by
  let g : ℝ → ℝ := fun x => |f x - φ x|
  have hAB : A ≤ B := by linarith
  have hhhleft : |h| < a - A := lt_of_lt_of_le hh (min_le_left _ _)
  have hhhright : |h| < B - b := lt_of_lt_of_le hh (min_le_right _ _)
  have hAshift : A ≤ a + h := by
    linarith [neg_abs_le h]
  have hshiftB : b + h ≤ B := by
    linarith [le_abs_self h]
  have habshift : a + h ≤ b + h := by linarith
  have hsub :
      ∀ c d : ℝ, A ≤ c → c ≤ d → d ≤ B →
        IntervalIntegrable g volume c d := by
    intro c d hAc hcd hdB
    apply hint.mono_set
    rw [Set.uIcc_of_le hcd, Set.uIcc_of_le hAB]
    exact Set.Icc_subset_Icc hAc hdB
  have hg_ab : IntervalIntegrable g volume a b :=
    hsub a b (le_of_lt hAa) hab (le_of_lt hbB)
  have hg_shift_base :
      IntervalIntegrable g volume (a + h) (b + h) :=
    hsub (a + h) (b + h) hAshift habshift hshiftB
  have hg_shift :
      IntervalIntegrable (fun x => g (x + h)) volume a b := by
    simpa using hg_shift_base.comp_add_right h
  have hφAB : IntervalIntegrable φ volume A B := by
    apply ContinuousOn.intervalIntegrable
    simpa [Set.uIcc_of_le hAB] using hφ
  have hφ_ab : IntervalIntegrable φ volume a b := by
    apply hφAB.mono_set
    rw [Set.uIcc_of_le hab, Set.uIcc_of_le hAB]
    exact Set.Icc_subset_Icc (le_of_lt hAa) (le_of_lt hbB)
  have hφ_shift_base :
      IntervalIntegrable φ volume (a + h) (b + h) := by
    apply hφAB.mono_set
    rw [Set.uIcc_of_le habshift, Set.uIcc_of_le hAB]
    exact Set.Icc_subset_Icc hAshift hshiftB
  have hφ_shift :
      IntervalIntegrable (fun x => φ (x + h)) volume a b := by
    simpa using hφ_shift_base.comp_add_right h
  have hmiddle :
      IntervalIntegrable (fun x => |φ (x + h) - φ x|) volume a b :=
    (hφ_shift.sub hφ_ab).abs
  have hfirst_bound :
      (∫ x in a..b, g (x + h)) ≤ ∫ x in A..B, g x := by
    calc
      (∫ x in a..b, g (x + h)) = ∫ x in a + h..b + h, g x := by
        rw [intervalIntegral.integral_comp_add_right]
      _ ≤ ∫ x in A..B, g x :=
        intervalIntegral.integral_mono_interval hAshift
          habshift hshiftB
          (Filter.Eventually.of_forall fun x => abs_nonneg _) hint
  have hthird_bound :
      (∫ x in a..b, g x) ≤ ∫ x in A..B, g x :=
    intervalIntegral.integral_mono_interval (le_of_lt hAa) hab (le_of_lt hbB)
      (Filter.Eventually.of_forall fun x => abs_nonneg _) hint
  by_cases htrans :
      IntervalIntegrable (fun x => |f (x + h) - f x|) volume a b
  · have htri := gap18 f φ a b h hab htrans
        (by simpa [g] using hg_shift) hmiddle (by simpa [g] using hg_ab)
    dsimp [g] at hfirst_bound hthird_bound
    linarith
  · unfold translationError
    rw [intervalIntegral.integral_undef htrans]
    have hg_nonneg : 0 ≤ ∫ x in A..B, g x :=
      intervalIntegral.integral_nonneg hAB (fun x hx => abs_nonneg _)
    have hm_nonneg : 0 ≤ ∫ x in a..b, |φ (x + h) - φ x| :=
      intervalIntegral.integral_nonneg hab (fun x hx => abs_nonneg _)
    dsimp [g] at hg_nonneg
    linarith

theorem gap20 (f φ : ℝ → ℝ) (A B a b h ε : ℝ)
    (hAB : A ≤ B) (hab : a < b)
    (happrox : (∫ x in A..B, |f x - φ x|) < ε / 4)
    (hint : IntervalIntegrable (fun x => |φ (x + h) - φ x|) volume a b)
    (hmod : ∀ x ∈ Set.Icc a b,
      |φ (x + h) - φ x| < ε / (2 * (b - a))) :
    2 * (∫ x in A..B, |f x - φ x|) +
        (∫ x in a..b, |φ (x + h) - φ x|) <
      2 * (ε / 4) + ε / (2 * (b - a)) * (b - a) := by
  let c : ℝ := ε / (2 * (b - a))
  have hconst : IntervalIntegrable (fun _ : ℝ => c) volume a b :=
    intervalIntegrable_const
  have hle :
      (fun x => |φ (x + h) - φ x|) ≤ᵐ[volume.restrict (Set.Ioc a b)]
        (fun _ => c) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    exact le_of_lt (hmod x (Set.Ioc_subset_Icc_self hx))
  have hsubset :
      Set.Ioc a b ⊆ {x : ℝ | |φ (x + h) - φ x| < c} := by
    intro x hx
    exact hmod x (Set.Ioc_subset_Icc_self hx)
  have hmeasure :
      volume.restrict (Set.Ioc a b)
        {x : ℝ | |φ (x + h) - φ x| < c} ≠ 0 := by
    intro hzero
    have hmono :
        volume.restrict (Set.Ioc a b) (Set.Ioc a b) ≤
          volume.restrict (Set.Ioc a b)
            {x : ℝ | |φ (x + h) - φ x| < c} :=
      measure_mono hsubset
    rw [hzero] at hmono
    have hsource : volume.restrict (Set.Ioc a b) (Set.Ioc a b) ≠ 0 := by
      rw [Measure.restrict_apply measurableSet_Ioc, Set.inter_self]
      simp [hab]
    exact hsource (bot_unique hmono)
  have hintegral :
      (∫ x in a..b, |φ (x + h) - φ x|) <
        ∫ _x in a..b, c :=
    intervalIntegral.integral_lt_integral_of_ae_le_of_measure_setOf_lt_ne_zero
      hab.le hint hconst hle hmeasure
  have hintegral' :
      (∫ x in a..b, |φ (x + h) - φ x|) < c * (b - a) := by
    simpa [mul_comm] using hintegral
  have happ' :
      2 * (∫ x in A..B, |f x - φ x|) < 2 * (ε / 4) :=
    mul_lt_mul_of_pos_left happrox (by norm_num)
  dsimp [c] at hintegral'
  exact add_lt_add happ' hintegral'

theorem gap21 (a b ε : ℝ) (hab : a < b) :
    2 * (ε / 4) + ε / (2 * (b - a)) * (b - a) = ε := by
  have hba : b - a ≠ 0 := ne_of_gt (sub_pos.mpr hab)
  field_simp [hba]
  ring

theorem gap22 (f : ℝ → ℝ) (a b h ε : ℝ)
    (hbound : translationError f a b h <
      2 * (ε / 4) + ε / (2 * (b - a)) * (b - a))
    (hab : a < b) :
    translationError f a b h < ε := by
  simpa [gap21 a b ε hab] using hbound

theorem gap23 (f : ℝ → ℝ) (A B a b : ℝ)
    (hAa : A < a) (hab : a < b) (hbB : b < B)
    (hf : IntervalIntegrable f volume A B) :
    Tendsto (translationError f a b) (nhds 0) (nhds (0 : ℝ)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hAB : A ≤ B := by linarith
  rcases gap15 f A B ε hAB hε hf with ⟨φ, hφ, happrox⟩
  have huniform := gap16 φ A B ε hφ hε
  rcases gap17 φ A B a b ε hab huniform hε with ⟨δ, hδ, hmodδ⟩
  let ρ : ℝ := min δ (min (a - A) (B - b))
  have hmargin : 0 < min (a - A) (B - b) := by
    exact lt_min (sub_pos.mpr hAa) (sub_pos.mpr hbB)
  have hρ : 0 < ρ := lt_min hδ hmargin
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hρ] with h hh
  have hhρ : |h| < ρ := by
    simpa [Metric.mem_ball, Real.dist_eq] using hh
  have hhδ : |h| < δ := lt_of_lt_of_le hhρ (min_le_left _ _)
  have hhmargin : |h| < min (a - A) (B - b) :=
    lt_of_lt_of_le hhρ (min_le_right _ _)
  have hAshift : A ≤ a + h := by
    have hhleft : |h| < a - A :=
      lt_of_lt_of_le hhmargin (min_le_left _ _)
    linarith [neg_abs_le h]
  have hshiftB : b + h ≤ B := by
    have hhright : |h| < B - b :=
      lt_of_lt_of_le hhmargin (min_le_right _ _)
    linarith [le_abs_self h]
  have habshift : a + h ≤ b + h := by linarith
  have hφAB : IntervalIntegrable φ volume A B := by
    apply ContinuousOn.intervalIntegrable
    simpa [Set.uIcc_of_le hAB] using hφ
  have hφ_ab : IntervalIntegrable φ volume a b := by
    apply hφAB.mono_set
    rw [Set.uIcc_of_le (le_of_lt hab), Set.uIcc_of_le hAB]
    exact Set.Icc_subset_Icc (le_of_lt hAa) (le_of_lt hbB)
  have hφ_shift_base :
      IntervalIntegrable φ volume (a + h) (b + h) := by
    apply hφAB.mono_set
    rw [Set.uIcc_of_le habshift, Set.uIcc_of_le hAB]
    exact Set.Icc_subset_Icc hAshift hshiftB
  have hφ_shift :
      IntervalIntegrable (fun x => φ (x + h)) volume a b := by
    simpa using hφ_shift_base.comp_add_right h
  have hmiddle :
      IntervalIntegrable (fun x => |φ (x + h) - φ x|) volume a b :=
    (hφ_shift.sub hφ_ab).abs
  have happroxInt :
      IntervalIntegrable (fun x => |f x - φ x|) volume A B :=
    (hf.sub hφAB).abs
  have hmod :
      ∀ x ∈ Set.Icc a b,
        |φ (x + h) - φ x| < ε / (2 * (b - a)) := by
    intro x hx
    have hx' : x ∈ Set.Icc A B :=
      ⟨le_trans (le_of_lt hAa) hx.1, le_trans hx.2 (le_of_lt hbB)⟩
    have hxh' : x + h ∈ Set.Icc A B := by
      constructor
      · linarith [hx.1]
      · linarith [hx.2]
    apply hmodδ (x + h) hxh' x hx'
    simpa [Real.dist_eq] using hhδ
  have houter := gap19 f φ A B a b h hAa (le_of_lt hab) hbB
    hhmargin hφ happroxInt
  have hinner := gap20 f φ A B a b h ε hAB hab happrox hmiddle hmod
  have hbound :
      translationError f a b h <
        2 * (ε / 4) + ε / (2 * (b - a)) * (b - a) :=
    lt_of_le_of_lt houter hinner
  have herrlt : translationError f a b h < ε :=
    gap22 f a b h ε hbound hab
  have herrnonneg : 0 ≤ translationError f a b h := by
    unfold translationError
    exact intervalIntegral.integral_nonneg (le_of_lt hab) (fun x hx => abs_nonneg _)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg herrnonneg]
  exact herrlt

theorem gap24 (f : ℝ → ℝ) (A B a b : ℝ)
    (hAa : A < a) (hab : a < b) (hbB : b < B)
    (hf : IntervalIntegrable f volume A B) :
    Tendsto (translationError f a b) (nhds 0) (nhds (0 : ℝ)) := by
  exact gap23 f A B a b hAa hab hbB hf

end
end ProofGap.Exercise2204
