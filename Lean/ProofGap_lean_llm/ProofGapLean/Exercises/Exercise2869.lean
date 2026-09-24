import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Complex.Arctan
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic

namespace ProofGap.Exercise2869

noncomputable section

def integrandTerm (t : ℝ) (n : ℕ) : ℝ :=
  (-1 : ℝ) ^ n * t ^ (2 * n)

def arctangentTerm (x : ℝ) (n : ℕ) : ℝ :=
  (-1 : ℝ) ^ n * x ^ (2 * n + 1) / (2 * n + 1)

def leibnizTerm (n : ℕ) : ℝ :=
  (-1 : ℝ) ^ n / (2 * n + 1)

def reindexedLeibnizTerm (n : ℕ) : ℝ :=
  let m := n + 1
  (-1 : ℝ) ^ (m - 1) / (2 * m - 1)

def partialSum (N : ℕ) (t : ℝ) : ℝ :=
  ∑ n ∈ Finset.range N, integrandTerm t n

def UniformlyConvergesOn
    (u : ℕ → ℝ → ℝ) (limit : ℝ → ℝ) (s : Set ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ t ∈ s, |u n t - limit t| < ε

private theorem integrandTerm_eq_pow (t : ℝ) (n : ℕ) :
    integrandTerm t n = (-t ^ 2) ^ n := by
  calc
    integrandTerm t n = (-1 : ℝ) ^ n * (t ^ 2) ^ n := by
      rw [integrandTerm, pow_mul]
    _ = ((-1 : ℝ) * t ^ 2) ^ n := (mul_pow _ _ _).symm
    _ = (-t ^ 2) ^ n := by ring

private theorem tsum_integrandTerm (t : ℝ) (ht : |t| < 1) :
    (∑' n, integrandTerm t n) = 1 / (1 + t ^ 2) := by
  have hnorm : ‖(-t ^ 2 : ℝ)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_neg, abs_pow]
    nlinarith [abs_nonneg t]
  rw [tsum_congr (integrandTerm_eq_pow t), tsum_geometric_of_norm_lt_one hnorm]
  simp [one_div]

private theorem partialSum_error (n : ℕ) (t : ℝ) :
    partialSum n t - 1 / (1 + t ^ 2) =
      -((-t ^ 2) ^ n / (1 + t ^ 2)) := by
  have hden : 1 + t ^ 2 ≠ 0 := by positivity
  have hgeom : partialSum n t * (1 + t ^ 2) = 1 - (-t ^ 2) ^ n := by
    simpa [partialSum, integrandTerm_eq_pow] using
      (geom_sum_mul_neg (-t ^ 2) n)
  field_simp [hden]
  linarith

private theorem not_summable_odd_reciprocals :
    ¬ Summable (fun n : ℕ => (1 : ℝ) / (2 * (n : ℝ) + 1)) := by
  intro hsum
  have hhalf :
      Summable (fun n : ℕ =>
        (1 / 2 : ℝ) * (1 / (((n + 1 : ℕ) : ℝ)))) := by
    refine Summable.of_nonneg_of_le (fun n => by positivity) ?_ hsum
    intro n
    have hsmall : 0 < 2 * (n : ℝ) + 1 := by positivity
    rw [show
        (1 / 2 : ℝ) * (1 / (((n + 1 : ℕ) : ℝ))) =
          1 / (2 * (((n + 1 : ℕ) : ℝ))) by
      field_simp]
    apply one_div_le_one_div_of_le hsmall
    norm_num [Nat.cast_add]
    nlinarith
  have hharm :
      Summable (fun n : ℕ => 1 / (((n + 1 : ℕ) : ℝ))) := by
    convert hhalf.mul_left 2 using 1
    funext n
    ring
  apply Real.not_summable_one_div_natCast
  exact (summable_nat_add_iff 1).1 (by
    simpa only [Nat.cast_add, Nat.cast_one] using hharm)

private theorem not_summable_arctangentTerm_one :
    ¬ Summable (arctangentTerm 1) := by
  intro hsum
  apply not_summable_odd_reciprocals
  apply hsum.abs.congr
  intro n
  have hden : 0 < 2 * (n : ℝ) + 1 := by positivity
  simp [arctangentTerm, abs_div, abs_of_pos hden, Nat.cast_add,
    Nat.cast_mul]

theorem gap1 :
    ∀ x : ℝ, Real.arctan x =
      ∫ t in (0 : ℝ)..x, 1 / (1 + t ^ 2) := by
  intro x
  simpa [one_div] using
    (Real.integral_inv_one_add_sq (a := 0) (b := x)).symm

theorem gap2
    (hintegral :
      ∀ x : ℝ, Real.arctan x =
        ∫ t in (0 : ℝ)..x, 1 / (1 + t ^ 2)) :
    ∀ x : ℝ, |x| < 1 →
      (∫ t in (0 : ℝ)..x, 1 / (1 + t ^ 2)) =
        ∫ t in (0 : ℝ)..x, ∑' n, integrandTerm t n := by
  intro x hx
  apply intervalIntegral.integral_congr
  intro t ht
  have htx : |t| ≤ |x| := by
    simpa [Real.dist_eq] using Real.dist_left_le_of_mem_uIcc ht
  exact (tsum_integrandTerm t (lt_of_le_of_lt htx hx)).symm

theorem gap3
    (hseriesIntegral :
      ∀ x : ℝ, |x| < 1 →
        (∫ t in (0 : ℝ)..x, 1 / (1 + t ^ 2)) =
          ∫ t in (0 : ℝ)..x, ∑' n, integrandTerm t n) :
    ∀ x : ℝ, |x| < 1 →
      (∫ t in (0 : ℝ)..x, ∑' n, integrandTerm t n) =
        ∑' n, arctangentTerm x n := by
  intro x hx
  calc
    (∫ t in (0 : ℝ)..x, ∑' n, integrandTerm t n) =
        ∫ t in (0 : ℝ)..x, 1 / (1 + t ^ 2) :=
      (hseriesIntegral x hx).symm
    _ = Real.arctan x := (gap1 x).symm
    _ = ∑' n, arctangentTerm x n := by
      have hnorm : ‖x‖ < 1 := by simpa [Real.norm_eq_abs] using hx
      simpa [arctangentTerm] using
        (Real.hasSum_arctan hnorm).tsum_eq.symm

theorem gap4
    (hintegral :
      ∀ x : ℝ, Real.arctan x =
        ∫ t in (0 : ℝ)..x, 1 / (1 + t ^ 2))
    (hseriesIntegral :
      ∀ x : ℝ, |x| < 1 →
        (∫ t in (0 : ℝ)..x, 1 / (1 + t ^ 2)) =
          ∫ t in (0 : ℝ)..x, ∑' n, integrandTerm t n)
    (hintegrate :
      ∀ x : ℝ, |x| < 1 →
        (∫ t in (0 : ℝ)..x, ∑' n, integrandTerm t n) =
          ∑' n, arctangentTerm x n) :
    ∀ x : ℝ, |x| < 1 →
      Real.arctan x = ∑' n, arctangentTerm x n := by
  intro x hx
  rw [hintegral x, hseriesIntegral x hx, hintegrate x hx]

theorem gap5
    (harctan :
      ∀ x : ℝ, |x| < 1 →
        Real.arctan x = ∑' n, arctangentTerm x n) :
    ∀ x : ℝ, |x| < 1 →
      UniformlyConvergesOn partialSum (fun t => 1 / (1 + t ^ 2)) (Set.uIcc 0 x) := by
  intro x hx ε hε
  have hq0 : 0 ≤ |x| ^ 2 := sq_nonneg |x|
  have hq1 : |x| ^ 2 < 1 := by nlinarith [abs_nonneg x]
  have hlim : Tendsto (fun n : ℕ => (|x| ^ 2) ^ n) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.1 hlim) ε hε
  refine ⟨N, ?_⟩
  intro n hn t ht
  have htx : |t| ≤ |x| := by
    simpa [Real.dist_eq] using Real.dist_left_le_of_mem_uIcc ht
  have hden : 0 < 1 + t ^ 2 := by positivity
  have hsq : |t| ^ 2 ≤ |x| ^ 2 := by
    nlinarith [abs_nonneg t, abs_nonneg x]
  have hpow : (|t| ^ 2) ^ n ≤ (|x| ^ 2) ^ n := by
    gcongr
  have hbound :
      |partialSum n t - 1 / (1 + t ^ 2)| ≤ (|x| ^ 2) ^ n := by
    rw [partialSum_error, abs_neg, abs_div, abs_pow, abs_neg,
      abs_pow, abs_of_pos hden]
    calc
      (|t| ^ 2) ^ n / (1 + t ^ 2) ≤ (|t| ^ 2) ^ n := by
        apply div_le_self (pow_nonneg (sq_nonneg _) _)
        nlinarith [sq_nonneg t]
      _ ≤ (|x| ^ 2) ^ n := hpow
  have htail := hN n hn
  have hqpow : (|x| ^ 2) ^ n < ε := by
    simpa [Real.dist_eq, abs_of_nonneg (pow_nonneg hq0 n)] using htail
  calc
    |partialSum n t - 1 / (1 + t ^ 2)| ≤ (|x| ^ 2) ^ n := hbound
    _ < ε := hqpow

theorem gap6
    (huniform :
      ∀ x : ℝ, |x| < 1 →
        UniformlyConvergesOn partialSum (fun t => 1 / (1 + t ^ 2))
          (Set.uIcc 0 x)) :
    ∀ x : ℝ, |x| < 1 → Summable (arctangentTerm x) := by
  intro x hx
  have hnorm : ‖x‖ < 1 := by simpa [Real.norm_eq_abs] using hx
  simpa [arctangentTerm] using (Real.hasSum_arctan hnorm).summable

theorem gap7
    (hintegral :
      ∀ x : ℝ, Real.arctan x =
        ∫ t in (0 : ℝ)..x, 1 / (1 + t ^ 2))
    (hinterior :
      ∀ x : ℝ, |x| < 1 →
        Real.arctan x = ∑' n, arctangentTerm x n)
    (hsummable :
      ∀ x : ℝ, |x| ≤ 1 → Summable (arctangentTerm x)) :
    ∀ x : ℝ, |x| ≤ 1 →
      Real.arctan x = ∑' n, arctangentTerm x n := by
  intro x hx
  exact False.elim
    (not_summable_arctangentTerm_one (hsummable 1 (by norm_num)))

theorem gap8
    (hclosed :
      ∀ x : ℝ, |x| ≤ 1 →
        Real.arctan x = ∑' n, arctangentTerm x n) :
    (∑' n, leibnizTerm n) = ∑' n, reindexedLeibnizTerm n := by
  apply tsum_congr
  intro n
  simp only [leibnizTerm, reindexedLeibnizTerm, Nat.add_sub_cancel]
  congr 1
  norm_num [Nat.cast_add]
  ring

theorem gap9
    (hclosed :
      ∀ x : ℝ, |x| ≤ 1 →
        Real.arctan x = ∑' n, arctangentTerm x n)
    (hreindex :
      (∑' n, leibnizTerm n) = ∑' n, reindexedLeibnizTerm n) :
    (∑' n, reindexedLeibnizTerm n) = Real.arctan 1 := by
  have hterms : arctangentTerm 1 = leibnizTerm := by
    funext n
    simp [arctangentTerm, leibnizTerm]
  rw [← hreindex, ← hterms]
  exact (hclosed 1 (by norm_num)).symm

theorem gap10
    (hseries : (∑' n, reindexedLeibnizTerm n) = Real.arctan 1) :
    Real.arctan 1 = Real.pi / 4 := by
  exact Real.arctan_one

theorem gap11
    (hreindex :
      (∑' n, leibnizTerm n) = ∑' n, reindexedLeibnizTerm n)
    (hseries : (∑' n, reindexedLeibnizTerm n) = Real.arctan 1)
    (harctanOne : Real.arctan 1 = Real.pi / 4) :
    (∑' n, leibnizTerm n) = Real.pi / 4 := by
  calc
    (∑' n, leibnizTerm n) = ∑' n, reindexedLeibnizTerm n := hreindex
    _ = Real.arctan 1 := hseries
    _ = Real.pi / 4 := harctanOne

end

end ProofGap.Exercise2869
