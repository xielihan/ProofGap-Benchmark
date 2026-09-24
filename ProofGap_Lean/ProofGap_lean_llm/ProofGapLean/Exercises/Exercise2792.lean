import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Topology.MetricSpace.Pseudo.Basic

namespace ProofGap.Exercise2792

noncomputable section

open scoped BigOperators

def term (n : ℕ) (x : ℝ) : ℝ :=
  Real.sin ((n : ℝ) * x) / (n : ℝ) ^ 3

def derivativeTerm (n : ℕ) (x : ℝ) : ℝ :=
  Real.cos ((n : ℝ) * x) / (n : ℝ) ^ 2

def f (x : ℝ) : ℝ :=
  ∑' n : ℕ, term (n + 1) x

def derivativeSum (x : ℝ) : ℝ :=
  ∑' n : ℕ, derivativeTerm (n + 1) x

def SeriesUniformlyConvergesOn
    (u : ℕ → ℝ → ℝ) (s : Set ℝ) (g : ℝ → ℝ) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ x ∈ s,
    |(∑ k ∈ Finset.range (n + 1), u k x) - g x| < ε

theorem gap1 (n : ℕ) (x : ℝ) (hn : 1 ≤ n) :
    |term n x| ≤ 1 / (n : ℝ) ^ 3 := by
  have hnpos : (0 : ℝ) < n := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have habs : |(n : ℝ)| = (n : ℝ) := abs_of_nonneg (Nat.cast_nonneg n)
  rw [term, abs_div, abs_pow, habs]
  exact (div_le_div_iff_of_pos_right (pow_pos hnpos 3)).2 (Real.abs_sin_le_one _)

theorem gap2 :
    Summable (fun n : ℕ => 1 / (((n + 1 : ℕ) : ℝ) ^ 3)) := by
  simpa using
    ((summable_nat_add_iff 1).2
      (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < (3 : ℕ))))

theorem gap3 :
    SeriesUniformlyConvergesOn
      (fun n x => term (n + 1) x) Set.univ f := by
  have hconv :
      TendstoUniformlyOn
        (fun N x => ∑ n ∈ Finset.range N, term (n + 1) x)
        f Filter.atTop Set.univ := by
    simpa [f] using
      (tendstoUniformlyOn_tsum_nat gap2
        (fun n x _ => by
          simpa [Real.norm_eq_abs] using
            gap1 (n + 1) x (Nat.succ_le_succ (Nat.zero_le n))))
  intro ε hε
  rcases Filter.eventually_atTop.1 ((Metric.tendstoUniformlyOn_iff.mp hconv) ε hε) with
    ⟨N, hN⟩
  refine ⟨N, fun n hn x hx => ?_⟩
  simpa [Real.dist_eq, abs_sub_comm] using
    hN (n + 1) (hn.trans (Nat.le_succ n)) x hx

theorem gap4 (n : ℕ) :
    ContinuousOn (term n) Set.univ := by
  unfold term
  fun_prop

theorem gap5 :
    ContinuousOn f Set.univ := by
  unfold f
  refine continuousOn_tsum (fun n => gap4 (n + 1)) gap2 ?_
  intro n x _
  simpa [Real.norm_eq_abs] using
    gap1 (n + 1) x (Nat.succ_le_succ (Nat.zero_le n))

theorem gap6 (n : ℕ) (x : ℝ) :
    HasDerivAt (term n) (derivativeTerm n x) x := by
  rcases eq_or_ne n 0 with rfl | hn
  · have hterm : term 0 = fun _ : ℝ => 0 := by
      funext y
      simp [term]
    rw [hterm]
    simpa [derivativeTerm] using (hasDerivAt_const x (0 : ℝ))
  · unfold term derivativeTerm
    convert (((hasDerivAt_id x).const_mul (n : ℝ)).sin.div_const ((n : ℝ) ^ 3)) using 1
    field_simp [Nat.cast_ne_zero.mpr hn] <;> simp

theorem gap7 (n : ℕ) :
    ContinuousOn (derivativeTerm n) Set.univ := by
  unfold derivativeTerm
  fun_prop

theorem gap8 :
    SeriesUniformlyConvergesOn
      (fun n x => derivativeTerm (n + 1) x)
      Set.univ derivativeSum := by
  have hsum : Summable (fun n : ℕ => 1 / (((n + 1 : ℕ) : ℝ) ^ 2)) := by
    simpa using
      ((summable_nat_add_iff 1).2
        (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < (2 : ℕ))))
  have hbound (n : ℕ) (x : ℝ) :
      ‖derivativeTerm (n + 1) x‖ ≤ 1 / (((n + 1 : ℕ) : ℝ) ^ 2) := by
    have hnpos : (0 : ℝ) < (n + 1 : ℕ) := by positivity
    have habs : |((n + 1 : ℕ) : ℝ)| = ((n + 1 : ℕ) : ℝ) :=
      abs_of_nonneg (Nat.cast_nonneg (n + 1))
    rw [derivativeTerm, Real.norm_eq_abs, abs_div, abs_pow, habs]
    exact (div_le_div_iff_of_pos_right (pow_pos hnpos 2)).2 (Real.abs_cos_le_one _)
  have hconv :
      TendstoUniformlyOn
        (fun N x => ∑ n ∈ Finset.range N, derivativeTerm (n + 1) x)
        derivativeSum Filter.atTop Set.univ := by
    simpa [derivativeSum] using
      (tendstoUniformlyOn_tsum_nat hsum (fun n x _ => hbound n x))
  intro ε hε
  rcases Filter.eventually_atTop.1 ((Metric.tendstoUniformlyOn_iff.mp hconv) ε hε) with
    ⟨N, hN⟩
  refine ⟨N, fun n hn x hx => ?_⟩
  simpa [Real.dist_eq, abs_sub_comm] using
    hN (n + 1) (hn.trans (Nat.le_succ n)) x hx

theorem gap9 :
    ContinuousOn derivativeSum Set.univ := by
  have hsum : Summable (fun n : ℕ => 1 / (((n + 1 : ℕ) : ℝ) ^ 2)) := by
    simpa using
      ((summable_nat_add_iff 1).2
        (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < (2 : ℕ))))
  have hbound (n : ℕ) (x : ℝ) :
      ‖derivativeTerm (n + 1) x‖ ≤ 1 / (((n + 1 : ℕ) : ℝ) ^ 2) := by
    have hnpos : (0 : ℝ) < (n + 1 : ℕ) := by positivity
    have habs : |((n + 1 : ℕ) : ℝ)| = ((n + 1 : ℕ) : ℝ) :=
      abs_of_nonneg (Nat.cast_nonneg (n + 1))
    rw [derivativeTerm, Real.norm_eq_abs, abs_div, abs_pow, habs]
    exact (div_le_div_iff_of_pos_right (pow_pos hnpos 2)).2 (Real.abs_cos_le_one _)
  unfold derivativeSum
  exact continuousOn_tsum (fun n => gap7 (n + 1)) hsum (fun n x _ => hbound n x)

theorem gap10 (x : ℝ) :
    HasDerivAt f (derivativeSum x) x := by
  have hsum : Summable (fun n : ℕ => 1 / (((n + 1 : ℕ) : ℝ) ^ 2)) := by
    simpa using
      ((summable_nat_add_iff 1).2
        (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < (2 : ℕ))))
  have hbound (n : ℕ) (y : ℝ) :
      ‖derivativeTerm (n + 1) y‖ ≤ 1 / (((n + 1 : ℕ) : ℝ) ^ 2) := by
    have hnpos : (0 : ℝ) < (n + 1 : ℕ) := by positivity
    have habs : |((n + 1 : ℕ) : ℝ)| = ((n + 1 : ℕ) : ℝ) :=
      abs_of_nonneg (Nat.cast_nonneg (n + 1))
    rw [derivativeTerm, Real.norm_eq_abs, abs_div, abs_pow, habs]
    exact (div_le_div_iff_of_pos_right (pow_pos hnpos 2)).2 (Real.abs_cos_le_one _)
  unfold f derivativeSum
  refine hasDerivAt_tsum (y₀ := 0) hsum
    (fun n y => gap6 (n + 1) y) hbound ?_ x
  simpa [term] using (summable_zero : Summable (fun _ : ℕ => (0 : ℝ)))

theorem gap11 :
    ContinuousOn derivativeSum Set.univ := gap9

theorem gap12 :
    ContinuousOn f Set.univ ∧ ContinuousOn derivativeSum Set.univ := ⟨gap5, gap11⟩

end

end ProofGap.Exercise2792
