import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

namespace ProofGap.Exercise606

noncomputable section

def TailAntitone (s : ℕ → ℝ) : Prop :=
  ∀ m n : ℕ, 1 ≤ m → m ≤ n → s n ≤ s m
def BoundedSeq (s : ℕ → ℝ) : Prop :=
  ∃ M : ℝ, ∀ n : ℕ, |s n| ≤ M

/-- Source: `proof_gap/exercise_606/1.txt`. -/
private lemma one_le_pi_for_iteration : (1 : ℝ) ≤ Real.pi := by
  have hpi2 : 0 ≤ Real.pi / 2 := by
    apply div_nonneg
    · exact Real.pi_pos.le
    · linarith
  have hbound : |Real.sin (Real.pi / 2)| ≤ |Real.pi / 2| := by
    exact Real.abs_sin_le_abs
  have hhalf : (1 : ℝ) ≤ Real.pi / 2 := by
    simpa [Real.sin_pi_div_two, abs_of_nonneg hpi2] using hbound
  linarith

theorem gap1 (x : ℝ) (hx0 : 0 ≤ x) (hxπ : x ≤ Real.pi) :
    0 ≤ Real.sin x := by
  exact Real.sin_nonneg_of_nonneg_of_le_pi hx0 hxπ

/-- Source: `proof_gap/exercise_606/2.txt`. -/
theorem gap2 (x : ℝ) (hx0 : 0 ≤ x) (hxπ : x ≤ Real.pi) :
    Real.sin x ≤ x := by
  calc
    Real.sin x ≤ |Real.sin x| := le_abs_self _
    _ ≤ |x| := by exact Real.abs_sin_le_abs
    _ = x := abs_of_nonneg hx0

/-- Source: `proof_gap/exercise_606/3.txt`. -/
theorem gap3 (x : ℝ) (hx0 : 0 ≤ x) (hxπ : x ≤ Real.pi) :
    0 ≤ Real.sin (Real.sin x) := by
  apply gap1 (Real.sin x)
  · exact gap1 x hx0 hxπ
  · exact (gap2 x hx0 hxπ).trans hxπ

/-- Source: `proof_gap/exercise_606/4.txt`. -/
theorem gap4 (x : ℝ) (hx0 : 0 ≤ x) (hxπ : x ≤ Real.pi) :
    Real.sin (Real.sin x) ≤ Real.sin x := by
  apply gap2 (Real.sin x)
  · exact gap1 x hx0 hxπ
  · exact (gap2 x hx0 hxπ).trans hxπ

/-- Source: `proof_gap/exercise_606/5.txt`. -/
theorem gap5 (s : ℕ → ℝ) (x : ℝ) (hx0 : 0 ≤ x) (hxπ : x ≤ Real.pi)
    (h1 : s 1 = Real.sin x) (hrec : ∀ n, s (n + 1) = Real.sin (s n)) :
    ∀ n : ℕ, 1 < n → 0 ≤ s n ∧ s n ≤ s (n - 1) := by
  have hrange : ∀ n : ℕ, 0 ≤ s (n + 1) ∧ s (n + 1) ≤ 1 := by
    intro n
    induction n with
    | zero =>
        constructor
        · simpa [h1] using gap1 x hx0 hxπ
        · simpa [h1] using Real.sin_le_one x
    | succ n ih =>
        rw [hrec (n + 1)]
        constructor
        · apply gap1 (s (n + 1)) ih.1
          exact ih.2.trans one_le_pi_for_iteration
        · exact Real.sin_le_one (s (n + 1))
  intro n hn
  have hn1 : 1 ≤ n := by omega
  have hprev := hrange (n - 2)
  have hprev_idx : n - 2 + 1 = n - 1 := by omega
  rw [hprev_idx] at hprev
  have hn_idx : n - 1 + 1 = n := Nat.sub_add_cancel hn1
  rw [← hn_idx, hrec (n - 1)]
  exact ⟨gap1 (s (n - 1)) hprev.1
      (hprev.2.trans one_le_pi_for_iteration),
    gap2 (s (n - 1)) hprev.1
      (hprev.2.trans one_le_pi_for_iteration)⟩

/-- Source: `proof_gap/exercise_606/6.txt`; monotonicity starts at index `1` because `s 0` is unconstrained. -/
theorem gap6 (s : ℕ → ℝ) (x : ℝ) (hx0 : 0 ≤ x) (hxπ : x ≤ Real.pi)
    (h1 : s 1 = Real.sin x) (hrec : ∀ n, s (n + 1) = Real.sin (s n)) :
    TailAntitone s := by
  have hrange : ∀ n : ℕ, 0 ≤ s (n + 1) ∧ s (n + 1) ≤ 1 := by
    intro n
    induction n with
    | zero =>
        constructor
        · simpa [h1] using gap1 x hx0 hxπ
        · simpa [h1] using Real.sin_le_one x
    | succ n ih =>
        rw [hrec (n + 1)]
        constructor
        · apply gap1 (s (n + 1)) ih.1
          exact ih.2.trans one_le_pi_for_iteration
        · exact Real.sin_le_one (s (n + 1))
  have hadj : ∀ n : ℕ, 1 ≤ n → s (n + 1) ≤ s n := by
    intro n hn
    have hnrange := hrange (n - 1)
    have hidx : n - 1 + 1 = n := Nat.sub_add_cancel hn
    rw [hidx] at hnrange
    rw [hrec n]
    exact gap2 (s n) hnrange.1 (hnrange.2.trans one_le_pi_for_iteration)
  unfold TailAntitone
  intro m n hm hmn
  induction n, hmn using Nat.le_induction with
  | base => exact le_rfl
  | succ n hmn ih =>
      exact (hadj n (by omega)).trans ih

/-- Source: `proof_gap/exercise_606/7.txt`. -/
theorem gap7 (s : ℕ → ℝ) (x : ℝ) (hx0 : 0 ≤ x) (hxπ : x ≤ Real.pi)
    (h1 : s 1 = Real.sin x) (hrec : ∀ n, s (n + 1) = Real.sin (s n)) :
    BoundedSeq s := by
  unfold BoundedSeq
  refine ⟨max |s 0| 1, ?_⟩
  intro n
  by_cases hn : n = 0
  · subst n
    exact le_max_left _ _
  · have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
    have hidx : n - 1 + 1 = n := Nat.sub_add_cancel hn1
    have hs : s n = Real.sin (s (n - 1)) := by
      rw [← hidx]
      exact hrec (n - 1)
    rw [hs]
    exact
      (abs_le.2 ⟨Real.neg_one_le_sin (s (n - 1)), Real.sin_le_one (s (n - 1))⟩).trans
        (le_max_right _ _)

/-- Source: `proof_gap/exercise_606/8.txt`. -/
theorem gap8 (s : ℕ → ℝ) (x : ℝ) (hx0 : 0 ≤ x) (hxπ : x ≤ Real.pi)
    (h1 : s 1 = Real.sin x) (hrec : ∀ n, s (n + 1) = Real.sin (s n)) :
    ∃ μ : ℝ, Filter.Tendsto s Filter.atTop (nhds μ) ∧ 0 ≤ μ ∧ μ ≤ 1 := by
  have hrange : ∀ n : ℕ, 0 ≤ s (n + 1) ∧ s (n + 1) ≤ 1 := by
    intro n
    induction n with
    | zero =>
        constructor
        · simpa [h1] using gap1 x hx0 hxπ
        · simpa [h1] using Real.sin_le_one x
    | succ n ih =>
        rw [hrec (n + 1)]
        constructor
        · apply gap1 (s (n + 1)) ih.1
          exact ih.2.trans one_le_pi_for_iteration
        · exact Real.sin_le_one (s (n + 1))
  let t : ℕ → ℝ := fun n => s (n + 1)
  have htanti : Antitone t := by
    intro m n hmn
    dsimp [t]
    exact gap6 s x hx0 hxπ h1 hrec (m + 1) (n + 1) (by omega) (by omega)
  have htbound : BddBelow (Set.range t) := by
    refine ⟨0, ?_⟩
    rintro y ⟨n, rfl⟩
    exact (hrange n).1
  have htlim :
      Filter.Tendsto t Filter.atTop (nhds (sInf (Set.range t))) :=
    tendsto_atTop_ciInf htanti htbound
  refine ⟨sInf (Set.range t), ?_, ?_, ?_⟩
  · rw [← Filter.tendsto_add_atTop_iff_nat 1]
    simpa [t, Nat.add_comm] using htlim
  · refine le_csInf (Set.range_nonempty t) ?_
    intro y hy
    rcases hy with ⟨n, rfl⟩
    exact (hrange n).1
  · calc
      sInf (Set.range t) ≤ t 0 := csInf_le htbound (Set.mem_range_self 0)
      _ ≤ 1 := (hrange 0).2

/-- Source: `proof_gap/exercise_606/9.txt`; express the shifted sequence limit explicitly. -/
theorem gap9 (s : ℕ → ℝ) (μ : ℝ)
    (hlim : Filter.Tendsto s Filter.atTop (nhds μ))
    (hrec : ∀ n, s (n + 1) = Real.sin (s n)) :
    Real.sin μ = μ := by
  have hsin :
      Filter.Tendsto (fun n : ℕ => Real.sin (s n)) Filter.atTop
        (nhds (Real.sin μ)) :=
    (Real.continuous_sin.tendsto μ).comp hlim
  have hsame :
      (fun n : ℕ => Real.sin (s n)) =ᶠ[Filter.atTop]
        (fun n : ℕ => s (n + 1)) :=
    Filter.Eventually.of_forall fun n => (hrec n).symm
  have hshift_sin :
      Filter.Tendsto (fun n : ℕ => s (n + 1)) Filter.atTop
        (nhds (Real.sin μ)) :=
    hsin.congr' hsame
  have hshift_mu :
      Filter.Tendsto (fun n : ℕ => s (n + 1)) Filter.atTop (nhds μ) := by
    simpa [Nat.add_comm] using
      ((Filter.tendsto_add_atTop_iff_nat 1).2 hlim)
  exact tendsto_nhds_unique hshift_sin hshift_mu

/-- Source: `proof_gap/exercise_606/10.txt`. -/
theorem gap10 (x : ℝ) (hx0 : 0 ≤ x) (hxπ : x ≤ Real.pi) :
    ∃ μ : ℝ, Real.sin μ = μ := by
  exact ⟨0, Real.sin_zero⟩

/-- Source: `proof_gap/exercise_606/11.txt`. -/
theorem gap11 (μ : ℝ) (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1)
    (hfix : Real.sin μ = μ) : μ = 0 := by
  apply le_antisymm ?_ hμ0
  by_contra hle
  have hne : μ ≠ 0 := by
    intro hzero
    apply hle
    rw [hzero]
  have hstrict := Real.abs_sin_lt_abs hne
  rw [hfix] at hstrict
  exact (lt_irrefl |μ|) hstrict

/-- Source: `proof_gap/exercise_606/12.txt`. -/
theorem gap12 (s : ℕ → ℝ) (x : ℝ) (hxπ : Real.pi < x)
    (hx2π : x ≤ 2 * Real.pi) (h1 : s 1 = Real.sin x)
    (hrec : ∀ n, s (n + 1) = Real.sin (s n)) :
    Filter.Tendsto s Filter.atTop (nhds 0) := by
  let t : ℕ → ℝ := fun n => -s n
  let y : ℝ := 2 * Real.pi - x
  have hy0 : 0 ≤ y := by
    dsimp [y]
    exact sub_nonneg.mpr hx2π
  have hyπ : y ≤ Real.pi := by
    dsimp [y]
    linarith
  have ht1 : t 1 = Real.sin y := by
    dsimp [t, y]
    rw [h1, Real.sin_sub, Real.sin_two_pi, Real.cos_two_pi]
    ring
  have htrec : ∀ n, t (n + 1) = Real.sin (t n) := by
    intro n
    dsimp [t]
    rw [hrec n, Real.sin_neg]
  obtain ⟨μ, hlim, hμ0, hμ1⟩ := gap8 t y hy0 hyπ ht1 htrec
  have hfix : Real.sin μ = μ := gap9 t μ hlim htrec
  have hzero : μ = 0 := gap11 μ hμ0 hμ1 hfix
  subst μ
  simpa only [t, neg_neg, neg_zero] using hlim.neg

/-- Source: `proof_gap/exercise_606/13.txt`; iteration of sine converges to its unique fixed point. -/
theorem gap13 (s : ℕ → ℝ) (x : ℝ) (h1 : s 1 = Real.sin x)
    (hrec : ∀ n, s (n + 1) = Real.sin (s n)) :
    Filter.Tendsto s Filter.atTop (nhds 0) := by
  have hs1le : s 1 ≤ 1 := by
    rw [h1]
    exact Real.sin_le_one x
  have hs1ge : -1 ≤ s 1 := by
    rw [h1]
    exact Real.neg_one_le_sin x
  by_cases hs : 0 ≤ s 1
  · let t : ℕ → ℝ := fun n => s (n + 1)
    have hsπ : s 1 ≤ Real.pi := hs1le.trans one_le_pi_for_iteration
    have ht1 : t 1 = Real.sin (s 1) := by
      dsimp [t]
      simpa using hrec 1
    have htrec : ∀ n, t (n + 1) = Real.sin (t n) := by
      intro n
      dsimp [t]
      simpa [Nat.add_assoc] using hrec (n + 1)
    obtain ⟨μ, hlim, hμ0, hμ1⟩ := gap8 t (s 1) hs hsπ ht1 htrec
    have hfix : Real.sin μ = μ := gap9 t μ hlim htrec
    have hzero : μ = 0 := gap11 μ hμ0 hμ1 hfix
    subst μ
    have hshift :
        Filter.Tendsto (fun n => s (n + 1)) Filter.atTop (nhds 0) := by
      simpa [t] using hlim
    rw [← Filter.tendsto_add_atTop_iff_nat 1]
    simpa [Nat.add_comm] using hshift
  · let t : ℕ → ℝ := fun n => -s (n + 1)
    have hp0 : 0 ≤ -s 1 := by linarith
    have hp1 : -s 1 ≤ 1 := by linarith
    have hpπ : -s 1 ≤ Real.pi := hp1.trans one_le_pi_for_iteration
    have ht1 : t 1 = Real.sin (-s 1) := by
      dsimp [t]
      rw [hrec 1, Real.sin_neg]
    have htrec : ∀ n, t (n + 1) = Real.sin (t n) := by
      intro n
      dsimp [t]
      rw [hrec (n + 1), Real.sin_neg]
    obtain ⟨μ, hlim, hμ0, hμ1⟩ := gap8 t (-s 1) hp0 hpπ ht1 htrec
    have hfix : Real.sin μ = μ := gap9 t μ hlim htrec
    have hzero : μ = 0 := gap11 μ hμ0 hμ1 hfix
    subst μ
    have hshift :
        Filter.Tendsto (fun n => s (n + 1)) Filter.atTop (nhds 0) := by
      simpa only [t, neg_neg, neg_zero] using hlim.neg
    rw [← Filter.tendsto_add_atTop_iff_nat 1]
    simpa [Nat.add_comm] using hshift

end

end ProofGap.Exercise606
