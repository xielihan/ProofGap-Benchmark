import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum

namespace ProofGap.Exercise1254

noncomputable section

def BoundedOn (u : ℝ → ℝ) (s : Set ℝ) : Prop :=
  ∃ M : ℝ, ∀ x ∈ s, |u x| ≤ M

def g (x : ℝ) : ℝ := Real.sin (1 / x)

private theorem deriv_g_of_ne_aux_1254 (x : ℝ) (hx : x ≠ 0) :
    deriv g x = Real.cos (1 / x) * (-1 / x ^ 2) := by
  have hinv : HasDerivAt (fun y : ℝ => 1 / y) (-1 / x ^ 2) x := by
    simpa [one_div] using (hasDerivAt_id x).inv hx
  simpa [g] using
    ((Real.hasDerivAt_sin (1 / x)).comp x hinv).deriv

private theorem cos_multiple_two_pi_aux_1254 (n : ℕ) :
    Real.cos ((n : ℝ) * (2 * Real.pi)) = 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
      simp [Nat.cast_succ, add_mul, Real.cos_add, ih]

theorem gap1 (f : ℝ → ℝ) (a b : ℝ) (hab : a < b)
    (hf : DifferentiableOn ℝ f (Set.Ioo a b)) :
    ContinuousOn f (Set.Ioo a b) := by
  exact hf.continuousOn

theorem gap2 (f : ℝ → ℝ) (a b : ℝ)
    (hbd : BoundedOn (deriv f) (Set.Ioo a b)) :
    ∃ N, ∀ x ∈ Set.Ioo a b, |deriv f x| < N := by
  rcases hbd with ⟨M, hM⟩
  refine ⟨M + 1, ?_⟩
  intro x hx
  linarith [hM x hx]

theorem gap3 (f : ℝ → ℝ) (a b c x : ℝ)
    (hc : c ∈ Set.Ioo a b) (hx : x ∈ Set.Ioo a b)
    (hxne : x ≠ c)
    (hf : DifferentiableOn ℝ f (Set.Ioo a b)) :
    ∃ ξ ∈ Set.Ioo (min c x) (max c x),
      |f x - f c| = |x - c| * |deriv f ξ| := by
  rcases lt_or_gt_of_ne hxne with hxc | hcx
  · have hsubcc : Set.Icc x c ⊆ Set.Ioo a b := by
      rintro y ⟨hxy, hyc⟩
      exact ⟨lt_of_lt_of_le hx.1 hxy, lt_of_le_of_lt hyc hc.2⟩
    have hsuboo : Set.Ioo x c ⊆ Set.Ioo a b := by
      intro y hy
      exact hsubcc ⟨le_of_lt hy.1, le_of_lt hy.2⟩
    have hcont : ContinuousOn f (Set.Icc x c) :=
      (hf.mono hsubcc).continuousOn
    have hdiff : DifferentiableOn ℝ f (Set.Ioo x c) := hf.mono hsuboo
    obtain ⟨ξ, hξ, hξder⟩ :=
      exists_deriv_eq_slope (f := f) hxc hcont hdiff
    have hden : c - x ≠ 0 := sub_ne_zero.mpr (ne_of_gt hxc)
    have heq : f x - f c = (x - c) * deriv f ξ := by
      rw [hξder]
      field_simp [hden] <;> ring
    refine ⟨ξ, ?_, ?_⟩
    · simpa [min_eq_right (le_of_lt hxc), max_eq_left (le_of_lt hxc)] using hξ
    · calc
        |f x - f c| = |(x - c) * deriv f ξ| := congrArg abs heq
        _ = |x - c| * |deriv f ξ| := abs_mul _ _
  · have hsubcc : Set.Icc c x ⊆ Set.Ioo a b := by
      rintro y ⟨hcy, hyx⟩
      exact ⟨lt_of_lt_of_le hc.1 hcy, lt_of_le_of_lt hyx hx.2⟩
    have hsuboo : Set.Ioo c x ⊆ Set.Ioo a b := by
      intro y hy
      exact hsubcc ⟨le_of_lt hy.1, le_of_lt hy.2⟩
    have hcont : ContinuousOn f (Set.Icc c x) :=
      (hf.mono hsubcc).continuousOn
    have hdiff : DifferentiableOn ℝ f (Set.Ioo c x) := hf.mono hsuboo
    obtain ⟨ξ, hξ, hξder⟩ :=
      exists_deriv_eq_slope (f := f) hcx hcont hdiff
    have hden : x - c ≠ 0 := sub_ne_zero.mpr (ne_of_gt hcx)
    have heq : f x - f c = (x - c) * deriv f ξ := by
      rw [hξder]
      field_simp [hden] <;> ring
    refine ⟨ξ, ?_, ?_⟩
    · simpa [min_eq_left (le_of_lt hcx), max_eq_right (le_of_lt hcx)] using hξ
    · calc
        |f x - f c| = |(x - c) * deriv f ξ| := congrArg abs heq
        _ = |x - c| * |deriv f ξ| := abs_mul _ _

theorem gap4 (f : ℝ → ℝ) (a b c : ℝ) (hab : a < b)
    (hc : c ∈ Set.Ioo a b) (hf : DifferentiableOn ℝ f (Set.Ioo a b))
    (hbd : BoundedOn (deriv f) (Set.Ioo a b)) :
    ∃ N, ∀ x ∈ Set.Ioo a b, |f x - f c| < N * (b - a) := by
  rcases gap2 f a b hbd with ⟨N, hN⟩
  have hNpos : 0 < N :=
    lt_of_le_of_lt (abs_nonneg (deriv f c)) (hN c hc)
  refine ⟨N, ?_⟩
  intro x hx
  by_cases hxc : x = c
  · subst x
    simpa using mul_pos hNpos (sub_pos.mpr hab)
  · obtain ⟨ξ, hξ, heq⟩ := gap3 f a b c x hc hx hxc hf
    have hξab : ξ ∈ Set.Ioo a b := by
      constructor
      · exact lt_trans (lt_min hc.1 hx.1) hξ.1
      · exact lt_trans hξ.2 (max_lt hc.2 hx.2)
    have hdist : |x - c| < b - a := by
      apply (abs_lt).2
      constructor <;> linarith [hx.1, hx.2, hc.1, hc.2]
    have habspos : 0 < |x - c| := abs_pos.mpr (sub_ne_zero.mpr hxc)
    calc
      |f x - f c| = |x - c| * |deriv f ξ| := heq
      _ < |x - c| * N := mul_lt_mul_of_pos_left (hN ξ hξab) habspos
      _ < (b - a) * N := mul_lt_mul_of_pos_right hdist hNpos
      _ = N * (b - a) := by ring

theorem gap5 (f : ℝ → ℝ) (a b c : ℝ) (hab : a < b)
    (hc : c ∈ Set.Ioo a b) (hf : DifferentiableOn ℝ f (Set.Ioo a b))
    (hbd : BoundedOn (deriv f) (Set.Ioo a b)) :
    ∃ N, ∀ x ∈ Set.Ioo a b, |f x - f c| < N * (b - a) := by
  exact gap4 f a b c hab hc hf hbd

theorem gap6 (f : ℝ → ℝ) (c x : ℝ) :
    |f x - f c| ≥ |f x| - |f c| := by
  have h := abs_add_le (f x - f c) (f c)
  rw [sub_add_cancel] at h
  linarith

theorem gap7 (f : ℝ → ℝ) (a b c : ℝ) (hab : a < b)
    (hc : c ∈ Set.Ioo a b) (hf : DifferentiableOn ℝ f (Set.Ioo a b))
    (hbd : BoundedOn (deriv f) (Set.Ioo a b)) :
    ∃ N, ∀ x ∈ Set.Ioo a b, |f x| < |f c| + N * (b - a) := by
  rcases gap4 f a b c hab hc hf hbd with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro x hx
  have hrev := gap6 f c x
  have hdiff := hN x hx
  linarith

theorem gap8 (f : ℝ → ℝ) (a b : ℝ) (hab : a < b)
    (hf : DifferentiableOn ℝ f (Set.Ioo a b))
    (hunbd : ¬BoundedOn f (Set.Ioo a b))
    (hbd : BoundedOn (deriv f) (Set.Ioo a b)) :
    False := by
  let c : ℝ := (a + b) / 2
  have hc : c ∈ Set.Ioo a b := by
    dsimp [c]
    constructor <;> linarith
  rcases gap7 f a b c hab hc hf hbd with ⟨N, hN⟩
  apply hunbd
  refine ⟨|f c| + N * (b - a), ?_⟩
  intro x hx
  exact le_of_lt (hN x hx)

theorem gap9 (f : ℝ → ℝ) (a b : ℝ) (hab : a < b)
    (hf : DifferentiableOn ℝ f (Set.Ioo a b))
    (hunbd : ¬BoundedOn f (Set.Ioo a b)) :
    ¬BoundedOn (deriv f) (Set.Ioo a b) := by
  intro hbd
  exact gap8 f a b hab hf hunbd hbd

theorem gap10 :
    BoundedOn g (Set.Ioo (0 : ℝ) (1 / 2)) := by
  refine ⟨1, ?_⟩
  intro x hx
  simpa [g] using Real.abs_sin_le_one (1 / x)

theorem gap11 :
    ¬BoundedOn (deriv g) (Set.Ioo (0 : ℝ) (1 / 2)) := by
  intro hbd
  rcases hbd with ⟨M, hM⟩
  obtain ⟨n : ℕ, hn⟩ := exists_nat_gt (max M 1)
  have hMn : M < (n : ℝ) :=
    lt_of_le_of_lt (le_max_left M 1) hn
  have hn_one : (1 : ℝ) < (n : ℝ) :=
    lt_of_le_of_lt (le_max_right M 1) hn
  have hnpos : 0 < (n : ℝ) := lt_trans zero_lt_one hn_one
  let T : ℝ := (n : ℝ) * (2 * Real.pi)
  have hfacpos : 0 < 2 * Real.pi := by
    nlinarith [Real.pi_gt_three]
  have hfacgt : 1 < 2 * Real.pi := by
    nlinarith [Real.pi_gt_three]
  have hbase : 2 * Real.pi < T := by
    have ht := mul_lt_mul_of_pos_right hn_one hfacpos
    simpa [T] using ht
  have hTtwo : 2 < T := by
    nlinarith [Real.pi_gt_three, hbase]
  have hTpos : 0 < T := lt_trans (by norm_num) hTtwo
  have hTne : T ≠ 0 := ne_of_gt hTpos
  have hTn : (n : ℝ) < T := by
    have ht := mul_lt_mul_of_pos_left hfacgt hnpos
    simpa [T] using ht
  have hTsq : T < T ^ 2 := by
    have ht := mul_lt_mul_of_pos_left (show (1 : ℝ) < T by linarith) hTpos
    simpa [pow_two] using ht
  let x : ℝ := 1 / T
  have hx : x ∈ Set.Ioo (0 : ℝ) (1 / 2) := by
    constructor
    · dsimp [x]
      exact div_pos (by norm_num) hTpos
    · dsimp [x]
      apply (div_lt_iff₀ hTpos).2
      nlinarith
  have hxne : x ≠ 0 := by
    dsimp [x]
    exact div_ne_zero one_ne_zero hTne
  have hinv : 1 / x = T := by
    dsimp [x]
    field_simp [hTne]
  have hcos : Real.cos T = 1 := by
    dsimp [T]
    exact cos_multiple_two_pi_aux_1254 n
  have hderval : deriv g x = -(T ^ 2) := by
    rw [deriv_g_of_ne_aux_1254 x hxne, hinv, hcos]
    dsimp [x]
    field_simp [hTne] <;> ring
  have hderabs : |deriv g x| = T ^ 2 := by
    rw [hderval, abs_neg, abs_of_nonneg (sq_nonneg T)]
  have hbound := hM x hx
  rw [hderabs] at hbound
  linarith

theorem gap12 (f : ℝ → ℝ) (a b : ℝ) (hab : a < b)
    (hf : DifferentiableOn ℝ f (Set.Ioo a b))
    (hunbd : ¬BoundedOn f (Set.Ioo a b)) :
    ¬BoundedOn (deriv f) (Set.Ioo a b) ∧
      BoundedOn g (Set.Ioo (0 : ℝ) (1 / 2)) ∧
      ¬BoundedOn (deriv g) (Set.Ioo (0 : ℝ) (1 / 2)) := by
  exact ⟨gap9 f a b hab hf hunbd, gap10, gap11⟩

end

end ProofGap.Exercise1254
