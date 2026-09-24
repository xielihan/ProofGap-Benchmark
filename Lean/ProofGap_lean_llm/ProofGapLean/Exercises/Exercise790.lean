import ProofGapLean.Prelude.Analysis
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

namespace ProofGap.Exercise790

noncomputable section

def f (x : ℝ) : ℝ := Real.sin (x ^ 2)

def sample (n : ℕ) : ℝ := Real.sqrt ((n : ℝ) * Real.pi / 2)

/-- Source: `proof_gap/exercise_790/1.txt`. -/
theorem gap1 : Continuous f := by
  unfold f
  exact Real.continuous_sin.comp (continuous_id.pow 2)

/-- Source: `proof_gap/exercise_790/2.txt`. -/
theorem gap2 : ∃ C : ℝ, ∀ x, |f x| ≤ C := by
  refine ⟨1, ?_⟩
  intro x
  simpa [f] using Real.abs_sin_le_one (x ^ 2)

/-- Source: `proof_gap/exercise_790/3.txt`; interpret the malformed `FunDeri(x,1,1)(n)` as the next sequence term. -/
theorem gap3 (n : ℕ) :
    |sample n - sample (n + 1)| =
      (Real.pi / 2) /
        (Real.sqrt ((n : ℝ) * Real.pi / 2) +
          Real.sqrt (((n + 1 : ℕ) : ℝ) * Real.pi / 2)) := by
  have ha_sq : sample n ^ 2 = (n : ℝ) * Real.pi / 2 := by
    unfold sample
    rw [Real.sq_sqrt]
    positivity
  have hb_sq : sample (n + 1) ^ 2 = ((n + 1 : ℕ) : ℝ) * Real.pi / 2 := by
    unfold sample
    rw [Real.sq_sqrt]
    positivity
  have ha0 : 0 ≤ sample n := by
    unfold sample
    exact Real.sqrt_nonneg _
  have hb0 : 0 ≤ sample (n + 1) := by
    unfold sample
    exact Real.sqrt_nonneg _
  have hdiff_sq : sample (n + 1) ^ 2 - sample n ^ 2 = Real.pi / 2 := by
    rw [hb_sq, ha_sq]
    simp only [Nat.cast_add, Nat.cast_one]
    ring
  have hab : sample n < sample (n + 1) := by
    by_contra h
    have hba : sample (n + 1) ≤ sample n := le_of_not_gt h
    have hp : 0 ≤ (sample n - sample (n + 1)) * (sample n + sample (n + 1)) :=
      mul_nonneg (sub_nonneg.mpr hba) (add_nonneg ha0 hb0)
    nlinarith [hdiff_sq, hp, Real.pi_pos]
  rw [abs_of_nonpos (sub_nonpos.mpr hab.le), neg_sub]
  change sample (n + 1) - sample n =
    (Real.pi / 2) / (sample n + sample (n + 1))
  have hsumpos : 0 < sample n + sample (n + 1) := by
    linarith
  apply (eq_div_iff (ne_of_gt hsumpos)).2
  nlinarith [hdiff_sq]

/-- Source: `proof_gap/exercise_790/4.txt`; replace `BigEnough(n)` by an eventual quantifier. -/
theorem gap4 :
    Filter.Tendsto (fun n : ℕ => (Real.pi / 2) /
      (Real.sqrt ((n : ℝ) * Real.pi / 2) +
        Real.sqrt (((n + 1 : ℕ) : ℝ) * Real.pi / 2)))
      Filter.atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hc : 0 < Real.pi / 2 := by
    positivity
  have hratio0 : 0 < (Real.pi / 2) / ε :=
    div_pos hc hε
  obtain ⟨N, hN⟩ := exists_nat_gt
    ((((Real.pi / 2) / ε) ^ 2) / (Real.pi / 2))
  refine ⟨N, ?_⟩
  intro n hn
  have hn' : (N : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast hn
  have hNc : ((Real.pi / 2) / ε) ^ 2 < (N : ℝ) * (Real.pi / 2) :=
    (div_lt_iff₀ hc).1 hN
  have hscale : (N : ℝ) * (Real.pi / 2) ≤
      (n : ℝ) * (Real.pi / 2) :=
    mul_le_mul_of_nonneg_right hn' hc.le
  have hscale' : (N : ℝ) * (Real.pi / 2) ≤
      (n : ℝ) * Real.pi / 2 := by
    calc
      (N : ℝ) * (Real.pi / 2) ≤ (n : ℝ) * (Real.pi / 2) := hscale
      _ = (n : ℝ) * Real.pi / 2 := by ring
  have hrad : ((Real.pi / 2) / ε) ^ 2 < (n : ℝ) * Real.pi / 2 :=
    lt_of_lt_of_le hNc hscale'
  have hx0 : 0 ≤ (n : ℝ) * Real.pi / 2 := by
    positivity
  have hsqrt_sq := Real.sq_sqrt hx0
  have hsqrt0 := Real.sqrt_nonneg ((n : ℝ) * Real.pi / 2)
  have hsqrt_gt : (Real.pi / 2) / ε < Real.sqrt ((n : ℝ) * Real.pi / 2) := by
    nlinarith
  have hden : (Real.pi / 2) / ε <
      Real.sqrt ((n : ℝ) * Real.pi / 2) +
        Real.sqrt (((n + 1 : ℕ) : ℝ) * Real.pi / 2) := by
    have hsecond := Real.sqrt_nonneg (((n + 1 : ℕ) : ℝ) * Real.pi / 2)
    linarith
  have hden0 : 0 <
      Real.sqrt ((n : ℝ) * Real.pi / 2) +
        Real.sqrt (((n + 1 : ℕ) : ℝ) * Real.pi / 2) :=
    lt_trans hratio0 hden
  have hcross : Real.pi / 2 <
      (Real.sqrt ((n : ℝ) * Real.pi / 2) +
        Real.sqrt (((n + 1 : ℕ) : ℝ) * Real.pi / 2)) * ε :=
    (div_lt_iff₀ hε).1 hden
  have hq : (Real.pi / 2) /
      (Real.sqrt ((n : ℝ) * Real.pi / 2) +
        Real.sqrt (((n + 1 : ℕ) : ℝ) * Real.pi / 2)) < ε := by
    apply (div_lt_iff₀ hden0).2
    simpa [mul_comm] using hcross
  have hqpos : 0 < (Real.pi / 2) /
      (Real.sqrt ((n : ℝ) * Real.pi / 2) +
        Real.sqrt (((n + 1 : ℕ) : ℝ) * Real.pi / 2)) :=
    div_pos hc hden0
  rw [Real.dist_eq, sub_zero, abs_of_pos hqpos]
  exact hq

/-- Source: `proof_gap/exercise_790/5.txt`; replace `BigEnough(n)` by convergence. -/
theorem gap5 :
    Filter.Tendsto (fun n => |sample n - sample (n + 1)|)
      Filter.atTop (nhds 0) := by
  simpa only [gap3] using gap4

/-- Source: `proof_gap/exercise_790/6.txt`; interpret the malformed derivative notation as the next term. -/
theorem gap6 (n : ℕ) :
    |f (sample n) - f (sample (n + 1))| = 1 := by
  have hsamp_sq (k : ℕ) : sample k ^ 2 = (k : ℝ) * Real.pi / 2 := by
    unfold sample
    rw [Real.sq_sqrt]
    positivity
  let x : ℝ := (n : ℝ) * Real.pi / 2
  have hnext_arg : ((n + 1 : ℕ) : ℝ) * Real.pi / 2 = x + Real.pi / 2 := by
    dsimp [x]
    simp only [Nat.cast_add, Nat.cast_one]
    ring
  have hnext_sin :
      Real.sin (((n + 1 : ℕ) : ℝ) * Real.pi / 2) = Real.cos x := by
    rw [hnext_arg, Real.sin_add, Real.sin_pi_div_two, Real.cos_pi_div_two]
    ring
  have hnatpi : ∀ k : ℕ, Real.sin ((k : ℝ) * Real.pi) = 0 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        rw [Nat.cast_succ]
        rw [show ((k : ℝ) + 1) * Real.pi = (k : ℝ) * Real.pi + Real.pi by ring]
        rw [Real.sin_add, ih, Real.sin_pi, Real.cos_pi]
        ring
  have hdouble : Real.sin (x + x) = 0 := by
    rw [show x + x = (n : ℝ) * Real.pi by dsimp [x]; ring]
    exact hnatpi n
  have hprod : Real.sin x * Real.cos x = 0 := by
    rw [Real.sin_add] at hdouble
    nlinarith
  have htrig := Real.sin_sq_add_cos_sq x
  have hsquare : (Real.sin x - Real.cos x) ^ 2 = 1 := by
    nlinarith
  change |Real.sin (sample n ^ 2) - Real.sin (sample (n + 1) ^ 2)| = 1
  rw [hsamp_sq n, hsamp_sq (n + 1), show (n : ℝ) * Real.pi / 2 = x by rfl,
    hnext_sin]
  have habssquare : |Real.sin x - Real.cos x| ^ 2 = 1 := by
    simpa only [sq_abs] using hsquare
  nlinarith [abs_nonneg (Real.sin x - Real.cos x)]

/-- Source: `proof_gap/exercise_790/7.txt`; remove the irrelevant eventual and δ quantifiers. -/
theorem gap7 (ε₀ : ℝ) (hε0 : 0 < ε₀) (hε1 : ε₀ < 1) : 1 > ε₀ := by
  exact hε1

/-- Source: `proof_gap/exercise_790/8.txt`; state the eventual counterexample sequence. -/
theorem gap8 (ε₀ : ℝ) (hε0 : 0 < ε₀) (hε1 : ε₀ < 1) :
    ∀ δ > 0, ∃ n,
      |sample n - sample (n + 1)| < δ ∧
      |f (sample n) - f (sample (n + 1))| > ε₀ := by
  intro δ hδ
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.1 gap5) δ hδ
  refine ⟨N, ?_, ?_⟩
  · have hclose := hN N le_rfl
    simpa [Real.dist_eq] using hclose
  · simpa [gap6 N] using hε1

/-- Source: `proof_gap/exercise_790/9.txt`. -/
theorem gap9 : ¬ UniformContinuous f := by
  intro huc
  rw [Metric.uniformContinuous_iff] at huc
  obtain ⟨δ, hδ, hmod⟩ := huc (1 / 2 : ℝ) (by norm_num)
  obtain ⟨n, hnclose, hnfar⟩ := gap8 (1 / 2 : ℝ) (by norm_num) (by norm_num) δ hδ
  have hinput : dist (sample n) (sample (n + 1)) < δ := by
    simpa [Real.dist_eq] using hnclose
  have hsmall := hmod hinput
  have hsmall' : |f (sample n) - f (sample (n + 1))| < (1 / 2 : ℝ) := by
    simpa [Real.dist_eq] using hsmall
  linarith

/-- Source: `proof_gap/exercise_790/10.txt`. -/
theorem gap10 :
    Continuous f ∧ (∃ C : ℝ, ∀ x, |f x| ≤ C) ∧ ¬ UniformContinuous f := by
  exact ⟨gap1, gap2, gap9⟩

end

end ProofGap.Exercise790
