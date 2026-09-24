import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Topology.Neighborhoods
import Mathlib.Topology.Order.OrderClosed

namespace ProofGap.Exercise1257

noncomputable section

open Filter

def LittleOAtTop (f : ℝ → ℝ) : Prop :=
  Tendsto (fun x => f x / x) atTop (nhds 0)

def DerivZeroSubsequence (f : ℝ → ℝ) : Prop :=
  ∃ x : ℕ → ℝ, Tendsto x atTop atTop ∧
    Tendsto (fun n => |deriv f (x n)|) atTop (nhds 0)

private theorem exists_deriv_eq_slope
    {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hcont : ContinuousOn f (Set.Icc a b))
    (hdiff : DifferentiableOn ℝ f (Set.Ioo a b)) :
    ∃ c ∈ Set.Ioo a b,
      deriv f c = (f b - f a) / (b - a) := by
  refine exists_hasDerivAt_eq_slope f (deriv f) hab hcont ?_
  intro x hx
  exact ((hdiff x hx).differentiableAt (isOpen_Ioo.mem_nhds hx)).hasDerivAt

theorem gap1 (f : ℝ → ℝ) (hsmall : LittleOAtTop f) :
    Tendsto (fun x => f x / x) atTop (nhds 0) := by
  exact hsmall

theorem gap2 (f : ℝ → ℝ) (a : ℝ) :
    Tendsto (fun x => (f x - f a) / (x - a)) atTop (nhds 0) ↔
      Tendsto (fun x => f x / x * (1 + a / (x - a)) - f a / (x - a))
        atTop (nhds 0) := by
  have heq :
      (fun x => (f x - f a) / (x - a)) =ᶠ[atTop]
        (fun x => f x / x * (1 + a / (x - a)) - f a / (x - a)) := by
    filter_upwards [eventually_gt_atTop (max a 0)] with x hx
    have hxa : x - a ≠ 0 := by
      apply ne_of_gt
      exact sub_pos.mpr (lt_of_le_of_lt (le_max_left a 0) hx)
    have hx0 : x ≠ 0 := by
      exact ne_of_gt (lt_of_le_of_lt (le_max_right a 0) hx)
    field_simp [hx0, hxa] <;> ring
  exact tendsto_congr' heq

theorem gap3 (f : ℝ → ℝ) (a : ℝ) (hsmall : LittleOAtTop f) :
    Tendsto (fun x => f x / x * (1 + a / (x - a)) - f a / (x - a))
      atTop (nhds 0) := by
  change Tendsto (fun x => f x / x) atTop (nhds 0) at hsmall
  have hshift : Tendsto (fun x : ℝ => x - a) atTop atTop := by
    refine tendsto_atTop.2 ?_
    intro c
    filter_upwards [eventually_ge_atTop (c + a)] with x hx
    linarith
  have hinv : Tendsto (fun x : ℝ => (x - a)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp hshift
  have ha : Tendsto (fun x : ℝ => a / (x - a)) atTop (nhds 0) := by
    simpa [div_eq_mul_inv] using
      ((tendsto_const_nhds :
          Tendsto (fun _ : ℝ => a) atTop (nhds a)).mul hinv)
  have hfa : Tendsto (fun x : ℝ => f a / (x - a)) atTop (nhds 0) := by
    simpa [div_eq_mul_inv] using
      ((tendsto_const_nhds :
          Tendsto (fun _ : ℝ => f a) atTop (nhds (f a))).mul hinv)
  have hone :
      Tendsto (fun x : ℝ => 1 + a / (x - a)) atTop (nhds 1) := by
    simpa using
      ((tendsto_const_nhds :
          Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (nhds 1)).add ha)
  simpa using (hsmall.mul hone).sub hfa

theorem gap4 (f : ℝ → ℝ) (a : ℝ) (hsmall : LittleOAtTop f) :
    Tendsto (fun x => (f x - f a) / (x - a)) atTop (nhds 0) := by
  exact (gap2 f a).2 (gap3 f a hsmall)

theorem gap5 (f : ℝ → ℝ) (a : ℕ → ℝ) (ε : ℕ → ℝ)
    (hsec : ∀ n, 1 ≤ n → ∃ b > a n,
      |(f b - f (a n)) / (b - a n)| < ε n) :
    ∀ n, 1 ≤ n → ∃ b > a n,
      |(f b - f (a n)) / (b - a n)| < ε n := by
  exact hsec

theorem gap6 (f : ℝ → ℝ) (a b : ℕ → ℝ) (ε : ℕ → ℝ)
    (hf : ∀ n, DifferentiableOn ℝ f (Set.Icc (a n) (b n)))
    (hab : ∀ n, a n < b n)
    (hsec : ∀ n, |(f (b n) - f (a n)) / (b n - a n)| < ε n) :
    ∃ x : ℕ → ℝ, ∀ n, x n ∈ Set.Ioo (a n) (b n) ∧
      deriv f (x n) = (f (b n) - f (a n)) / (b n - a n) ∧
      |deriv f (x n)| < ε n := by
  have hmvt : ∀ n, ∃ c ∈ Set.Ioo (a n) (b n),
      deriv f c = (f (b n) - f (a n)) / (b n - a n) := by
    intro n
    have hsub : Set.Ioo (a n) (b n) ⊆ Set.Icc (a n) (b n) := by
      intro y hy
      exact ⟨le_of_lt hy.1, le_of_lt hy.2⟩
    exact exists_deriv_eq_slope (f := f) (a := a n) (b := b n)
      (hab n) (hf n).continuousOn ((hf n).mono hsub)
  choose x hx hderiv using hmvt
  refine ⟨x, ?_⟩
  intro n
  refine ⟨hx n, hderiv n, ?_⟩
  rw [hderiv n]
  exact hsec n

theorem gap7 (f : ℝ → ℝ) (x : ℕ → ℝ)
    (hlim : Tendsto (fun n => |deriv f (x n)|) atTop (nhds 0)) :
    Tendsto (fun n => |deriv f (x n)|) atTop (nhds 0) := by
  exact hlim

theorem gap8 (a x : ℕ → ℝ) (hax : ∀ n, a n < x n) :
    ∀ n, a n < x n := by
  exact hax

theorem gap9 (a : ℕ → ℝ) (ha : ∀ n : ℕ, (n : ℝ) ≤ a n) :
    ∀ n : ℕ, (n : ℝ) ≤ a n := by
  exact ha

theorem gap10 (x : ℕ → ℝ) (hx : ∀ n : ℕ, (n : ℝ) < x n) :
    ∀ n : ℕ, (n : ℝ) < x n := by
  exact hx

theorem gap11 (x : ℕ → ℝ) (hx : ∀ n : ℕ, (n : ℝ) < x n) :
    Tendsto x atTop atTop := by
  refine tendsto_atTop.2 ?_
  intro b
  obtain ⟨N : ℕ, hN⟩ := exists_nat_gt b
  filter_upwards [eventually_ge_atTop N] with n hn
  calc
    b ≤ (N : ℝ) := le_of_lt hN
    _ ≤ (n : ℝ) := (Nat.cast_le).2 hn
    _ ≤ x n := le_of_lt (hx n)

theorem gap12 (f : ℝ → ℝ) (x₀ : ℝ)
    (hf : DifferentiableOn ℝ f (Set.Ioi x₀))
    (hsmall : LittleOAtTop f) :
    DerivZeroSubsequence f := by
  let a : ℕ → ℝ := fun n => max (x₀ + 1) (n : ℝ)
  let ε : ℕ → ℝ := fun n => (((n + 1 : ℕ) : ℝ))⁻¹
  have ha0 : ∀ n, x₀ < a n := by
    intro n
    dsimp [a]
    exact lt_of_lt_of_le (by linarith) (le_max_left (x₀ + 1) (n : ℝ))
  have han : ∀ n : ℕ, (n : ℝ) ≤ a n := by
    intro n
    exact le_max_right (x₀ + 1) (n : ℝ)
  have hepos : ∀ n, 0 < ε n := by
    intro n
    dsimp [ε]
    positivity
  have hb_exists : ∀ n, ∃ b > a n,
      |(f b - f (a n)) / (b - a n)| < ε n := by
    intro n
    have ht := gap4 f (a n) hsmall
    rcases (Metric.tendsto_atTop.1 ht) (ε n) (hepos n) with ⟨B, hB⟩
    refine ⟨max (a n + 1) B, ?_, ?_⟩
    · exact lt_of_lt_of_le (by linarith) (le_max_left (a n + 1) B)
    · have hdist := hB (max (a n + 1) B) (le_max_right (a n + 1) B)
      rw [Real.dist_eq] at hdist
      rw [sub_zero] at hdist
      exact hdist
  choose b hab hsec using hb_exists
  have hdiff : ∀ n, DifferentiableOn ℝ f (Set.Icc (a n) (b n)) := by
    intro n
    apply hf.mono
    intro y hy
    exact lt_of_lt_of_le (ha0 n) hy.1
  rcases gap6 f a b ε hdiff hab hsec with ⟨x, hx⟩
  refine ⟨x, ?_, ?_⟩
  · apply gap11
    intro n
    exact lt_of_le_of_lt (han n) (hx n).1.1
  · have hden :
        Tendsto (fun n : ℕ => (((n + 1 : ℕ) : ℝ))) atTop atTop := by
      apply gap11
      intro n
      exact (Nat.cast_lt).2 (Nat.lt_succ_self n)
    have heps : Tendsto ε atTop (nhds 0) := by
      dsimp [ε]
      exact tendsto_inv_atTop_zero.comp hden
    exact squeeze_zero'
      (Filter.Eventually.of_forall (fun n => abs_nonneg (deriv f (x n))))
      (Filter.Eventually.of_forall (fun n => le_of_lt (hx n).2.2))
      heps

theorem gap13 (f : ℝ → ℝ) (x₀ : ℝ)
    (hf : DifferentiableOn ℝ f (Set.Ioi x₀))
    (hsmall : LittleOAtTop f) :
    DerivZeroSubsequence f := by
  exact gap12 f x₀ hf hsmall

end

end ProofGap.Exercise1257
