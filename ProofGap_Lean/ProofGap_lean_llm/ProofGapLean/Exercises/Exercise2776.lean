import ProofGapLean.Prelude.Analysis
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

namespace ProofGap.Exercise2776

noncomputable section

open scoped BigOperators

def term (n : ℕ) (x : ℝ) : ℝ :=
  (2 : ℝ) ^ n * Real.sin (1 / ((3 : ℝ) ^ n * x))

def badPoint (N : ℕ) : ℝ :=
  2 / ((3 : ℝ) ^ (N + 1) * Real.pi)

def SeriesUniformlyConvergesOn
    (u : ℕ → ℝ → ℝ) (s : Set ℝ) (f : ℝ → ℝ) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ x ∈ s,
    |(∑ k ∈ Finset.range (n + 1), u k x) - f x| < ε

def UniformCauchyOn (u : ℕ → ℝ → ℝ) (s : Set ℝ) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ p : ℕ, ∀ x ∈ s,
    |∑ j ∈ Finset.range p, u (n + j) x| < ε

theorem gap1 (n : ℕ) (x : ℝ) (hx : 0 < x) :
    |term n x| ≤ (2 : ℝ) ^ n / ((3 : ℝ) ^ n * x) := by
  unfold term
  rw [abs_mul]
  have h2 : 0 ≤ (2 : ℝ) ^ n := by positivity
  rw [abs_of_nonneg h2]
  calc
    (2 : ℝ) ^ n * |Real.sin (1 / ((3 : ℝ) ^ n * x))| ≤
        (2 : ℝ) ^ n * |1 / ((3 : ℝ) ^ n * x)| := by
      apply mul_le_mul_of_nonneg_left
      · exact Real.abs_sin_le_abs
      · exact h2
    _ = (2 : ℝ) ^ n / ((3 : ℝ) ^ n * x) := by
      rw [abs_of_pos (by positivity : 0 < (1 : ℝ) / ((3 : ℝ) ^ n * x))]
      simp only [div_eq_mul_inv, one_mul]

theorem gap2 (n : ℕ) (x : ℝ) (hx : 0 < x) :
    (2 : ℝ) ^ n / ((3 : ℝ) ^ n * x) =
      (1 / x) * (2 / 3 : ℝ) ^ n := by
  have hx0 : x ≠ 0 := ne_of_gt hx
  have h3 : (3 : ℝ) ≠ 0 := by norm_num
  rw [div_pow]
  field_simp [hx0, h3] <;> ring

theorem gap3 (n : ℕ) (x : ℝ) (hx : 0 < x) :
    |term n x| ≤ (1 / x) * (2 / 3 : ℝ) ^ n := by
  calc
    |term n x| ≤ (2 : ℝ) ^ n / ((3 : ℝ) ^ n * x) := gap1 n x hx
    _ = (1 / x) * (2 / 3 : ℝ) ^ n := gap2 n x hx

theorem gap4 (x : ℝ) (hx : 0 < x) :
    Summable (fun n : ℕ => (1 / x) * (2 / 3 : ℝ) ^ (n + 1)) := by
  have hq : Summable (fun n : ℕ => (2 / 3 : ℝ) ^ n) :=
    summable_geometric_of_norm_lt_one (by norm_num)
  simpa [pow_succ, mul_assoc, mul_left_comm, mul_comm] using
    hq.mul_left ((1 / x) * (2 / 3 : ℝ))

theorem gap5 (x : ℝ) (hx : 0 < x) :
    Summable (fun n : ℕ => |term (n + 1) x|) := by
  apply Summable.of_norm_bounded (gap4 x hx)
  intro n
  simpa [Real.norm_eq_abs] using gap3 (n + 1) x hx

theorem gap6
    (huniform : SeriesUniformlyConvergesOn
      (fun n x => term (n + 1) x)
      (Set.Ioi (0 : ℝ))
      (fun x => ∑' n : ℕ, term (n + 1) x)) :
    UniformCauchyOn
      (fun n x => term (n + 1) x)
      (Set.Ioi (0 : ℝ)) := by
  unfold SeriesUniformlyConvergesOn at huniform
  unfold UniformCauchyOn
  intro ε hε
  obtain ⟨N, hN⟩ := huniform (ε / 2) (by linarith)
  refine ⟨N + 1, ?_⟩
  intro n hn p x hx
  cases p with
  | zero => simpa using hε
  | succ p =>
      have hnpos : 0 < n :=
        lt_of_lt_of_le (Nat.zero_lt_succ N) hn
      have hnlow : N ≤ n - 1 := by
        exact Nat.le_sub_of_add_le hn
      have hNle_n : N ≤ n :=
        le_trans (Nat.le_succ N) hn
      have hnhigh : N ≤ n + p :=
        le_trans hNle_n (Nat.le_add_right n p)
      have hlow := hN (n - 1) hnlow x hx
      have hhigh := hN (n + p) hnhigh x hx
      change |∑ j ∈ Finset.range (Nat.succ p), term ((n + j) + 1) x| < ε
      have hnsub : n - 1 + 1 = n :=
        Nat.sub_add_cancel (Nat.succ_le_iff.mpr hnpos)
      have hsum :
          (∑ k ∈ Finset.range ((n + p) + 1), term (k + 1) x) =
            (∑ k ∈ Finset.range ((n - 1) + 1), term (k + 1) x) +
              ∑ j ∈ Finset.range (Nat.succ p), term ((n + j) + 1) x := by
        have hs := Finset.sum_range_add
          (fun k => term (k + 1) x) n (Nat.succ p)
        simpa [Nat.add_assoc, hnsub] using hs
      have htail :
          (∑ j ∈ Finset.range (Nat.succ p), term ((n + j) + 1) x) =
            (∑ k ∈ Finset.range ((n + p) + 1), term (k + 1) x) -
              (∑ k ∈ Finset.range ((n - 1) + 1), term (k + 1) x) := by
        linarith [hsum]
      have hrearr :
          (∑ k ∈ Finset.range ((n + p) + 1), term (k + 1) x) -
              (∑ k ∈ Finset.range ((n - 1) + 1), term (k + 1) x) =
            ((∑ k ∈ Finset.range ((n + p) + 1), term (k + 1) x) -
                ∑' k : ℕ, term (k + 1) x) -
              ((∑ k ∈ Finset.range ((n - 1) + 1), term (k + 1) x) -
                ∑' k : ℕ, term (k + 1) x) := by
        ring
      rw [htail, hrearr]
      calc
        |((∑ k ∈ Finset.range ((n + p) + 1), term (k + 1) x) -
              ∑' k : ℕ, term (k + 1) x) -
            ((∑ k ∈ Finset.range ((n - 1) + 1), term (k + 1) x) -
              ∑' k : ℕ, term (k + 1) x)| ≤
            |(∑ k ∈ Finset.range ((n + p) + 1), term (k + 1) x) -
              ∑' k : ℕ, term (k + 1) x| +
            |(∑ k ∈ Finset.range ((n - 1) + 1), term (k + 1) x) -
              ∑' k : ℕ, term (k + 1) x| := by
          simpa only [sub_eq_add_neg, abs_neg, neg_neg] using
            abs_add_le
              ((∑ k ∈ Finset.range ((n + p) + 1), term (k + 1) x) -
                ∑' k : ℕ, term (k + 1) x)
              (-((∑ k ∈ Finset.range ((n - 1) + 1), term (k + 1) x) -
                ∑' k : ℕ, term (k + 1) x))
        _ < ε := by linarith

theorem gap7
    (huniform : SeriesUniformlyConvergesOn
      (fun n x => term (n + 1) x)
      (Set.Ioi (0 : ℝ))
      (fun x => ∑' n : ℕ, term (n + 1) x)) :
    ∃ N : ℕ, ∀ x ∈ Set.Ioi (0 : ℝ), |term (N + 1) x| < 1 := by
  have hc := gap6 huniform
  unfold UniformCauchyOn at hc
  obtain ⟨N, hN⟩ := hc 1 (by norm_num)
  refine ⟨N, ?_⟩
  intro x hx
  simpa using hN N le_rfl 1 x hx

theorem gap8 (N : ℕ) :
    badPoint N ∈ Set.Ioi (0 : ℝ) := by
  unfold badPoint
  change 0 < (2 : ℝ) / ((3 : ℝ) ^ (N + 1) * Real.pi)
  positivity

theorem gap9
    (huniform : SeriesUniformlyConvergesOn
      (fun n x => term (n + 1) x)
      (Set.Ioi (0 : ℝ))
      (fun x => ∑' n : ℕ, term (n + 1) x)) :
    ∃ N : ℕ, |term (N + 1) (badPoint N)| < 1 := by
  obtain ⟨N, hN⟩ := gap7 huniform
  exact ⟨N, hN (badPoint N) (gap8 N)⟩

theorem gap10 (N : ℕ) :
    term (N + 1) (badPoint N) =
      (2 : ℝ) ^ (N + 1) *
        Real.sin (1 / ((3 : ℝ) ^ (N + 1) * badPoint N)) := by
  rfl

theorem gap11 (N : ℕ) :
    (2 : ℝ) ^ (N + 1) *
        Real.sin (1 / ((3 : ℝ) ^ (N + 1) * badPoint N)) =
      (2 : ℝ) ^ (N + 1) * Real.sin (Real.pi / 2) := by
  have h3 : (3 : ℝ) ^ (N + 1) ≠ 0 := by positivity
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  have harg :
      1 / ((3 : ℝ) ^ (N + 1) * badPoint N) = Real.pi / 2 := by
    unfold badPoint
    field_simp [h3, hpi] <;> ring
  rw [harg]

theorem gap12 (N : ℕ) :
    (2 : ℝ) ^ (N + 1) * Real.sin (Real.pi / 2) =
      (2 : ℝ) ^ (N + 1) := by
  rw [Real.sin_pi_div_two, mul_one]

theorem gap13 (N : ℕ) :
    (2 : ℝ) ^ (N + 1) > 1 := by
  induction N with
  | zero => norm_num
  | succ N ih =>
      calc
        (2 : ℝ) ^ (Nat.succ N + 1) =
            (2 : ℝ) ^ (N + 1) * 2 := by
          rw [show Nat.succ N + 1 = (N + 1) + 1 by omega, pow_succ]
        _ > 1 := by nlinarith

theorem gap14 (N : ℕ) :
    term (N + 1) (badPoint N) > 1 := by
  calc
    term (N + 1) (badPoint N) =
        (2 : ℝ) ^ (N + 1) *
          Real.sin (1 / ((3 : ℝ) ^ (N + 1) * badPoint N)) := gap10 N
    _ = (2 : ℝ) ^ (N + 1) * Real.sin (Real.pi / 2) := gap11 N
    _ = (2 : ℝ) ^ (N + 1) := gap12 N
    _ > 1 := gap13 N

theorem gap15 :
    SeriesUniformlyConvergesOn
      (fun n x => term (n + 1) x)
      (Set.Ioi (0 : ℝ))
      (fun x => ∑' n : ℕ, term (n + 1) x) →
    False := by
  intro huniform
  obtain ⟨N, hlt⟩ := gap9 huniform
  have hgt := gap14 N
  have hpos : 0 < term (N + 1) (badPoint N) := by
    linarith
  rw [abs_of_pos hpos] at hlt
  linarith

theorem gap16 :
    ¬ SeriesUniformlyConvergesOn
      (fun n x => term (n + 1) x)
      (Set.Ioi (0 : ℝ))
      (fun x => ∑' n : ℕ, term (n + 1) x) := by
  exact gap15

theorem gap17 :
    (∀ x ∈ Set.Ioi (0 : ℝ),
      Summable (fun n : ℕ => term (n + 1) x)) ∧
    ¬ SeriesUniformlyConvergesOn
      (fun n x => term (n + 1) x)
      (Set.Ioi (0 : ℝ))
      (fun x => ∑' n : ℕ, term (n + 1) x) := by
  refine ⟨?_, gap16⟩
  intro x hx
  apply Summable.of_norm
  simpa [Real.norm_eq_abs] using gap5 x hx

end

end ProofGap.Exercise2776
