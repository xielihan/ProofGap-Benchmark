import ProofGapLean.Prelude.Elementary
import ProofGapLean.Prelude.Finite
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Ring
import Mathlib.Topology.MetricSpace.Basic

namespace ProofGap.Exercise417

open scoped BigOperators

noncomputable section

def numerator (n : ℕ) (x : ℝ) : ℝ :=
  (Finset.Icc 1 n).prod (fun k => x ^ k + 1)

def denominator (n : ℕ) (x : ℝ) : ℝ :=
  (((n : ℝ) * x) ^ n + 1) ^ ((n + 1) / 2)

def f (n : ℕ) (x : ℝ) : ℝ := numerator n x / denominator n x

def HasLimitAtInfinity (g : ℝ → ℝ) (L : ℝ) : Prop :=
  ∀ ε > 0, ∃ N > 0, ∀ x, N < |x| → |g x - L| < ε

/-- Source: `proof_gap/exercise_417/1.txt`. -/
private theorem exercise417_prod_powers
    (s : Finset ℕ) (x : ℝ) :
    s.prod (fun k => x ^ k) = x ^ (s.sum (fun k => k)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      simp [ha, ih, pow_add]

private theorem exercise417_cancel_common_factor
    (c a b : ℝ) (hc : c ≠ 0) :
    (c * a) / (c * b) = a / b := by
  by_cases hb : b = 0
  · simp [hb]
  · field_simp [hc, hb]

private theorem exercise417_hasLimitAtInfinity_of_inverse_model
    (g G : ℝ → ℝ) (hG : ContinuousAt G 0)
    (hEq : ∀ x, x ≠ 0 → g x = G x⁻¹) :
    HasLimitAtInfinity g (G 0) := by
  intro ε hε
  rcases (Metric.continuousAt_iff.1 hG) ε hε with
    ⟨δ, hδ, hcontrol⟩
  have hNpos : 0 < max 1 δ⁻¹ :=
    lt_of_lt_of_le zero_lt_one (le_max_left 1 δ⁻¹)
  refine ⟨max 1 δ⁻¹, hNpos, ?_⟩
  intro x hx
  have hxabs : 0 < |x| := lt_trans hNpos hx
  have hx0 : x ≠ 0 := abs_pos.mp hxabs
  have hdinv : δ⁻¹ < |x| :=
    lt_of_le_of_lt (le_max_right 1 δ⁻¹) hx
  have hprod : 1 < δ * |x| := by
    have hscaled : δ * δ⁻¹ < δ * |x| :=
      mul_lt_mul_of_pos_left hdinv hδ
    simpa [ne_of_gt hδ] using hscaled
  have hinv : |x|⁻¹ < δ := by
    rw [inv_eq_one_div]
    exact (div_lt_iff₀ hxabs).2 hprod
  have hdist : dist x⁻¹ 0 < δ := by
    simpa only [Real.dist_eq, sub_zero, abs_inv] using hinv
  have hclose : dist (G x⁻¹) (G 0) < ε := hcontrol hdist
  rw [hEq x hx0]
  simpa only [Real.dist_eq] using hclose

theorem gap1 (n : ℕ) :
    ∃ degreeNumerator : ℕ,
      degreeNumerator = (Finset.Icc 1 n).sum (fun k => k) := by
  exact ⟨(Finset.Icc 1 n).sum (fun k => k), rfl⟩

/-- Source: `proof_gap/exercise_417/2.txt`. -/
theorem gap2 (n : ℕ) :
    (Finset.Icc 1 n).sum (fun k => k) = n * (n + 1) / 2 := by
  have hsubset : Finset.Icc 1 n ⊆ Finset.range (n + 1) := by
    intro k hk
    simp only [Finset.mem_Icc] at hk
    simp only [Finset.mem_range]
    omega
  calc
    (Finset.Icc 1 n).sum (fun k => k) =
        (Finset.range (n + 1)).sum (fun k => k) := by
      apply Finset.sum_subset hsubset
      intro k hkRange hkNotIcc
      simp only [Finset.mem_range] at hkRange
      simp only [Finset.mem_Icc] at hkNotIcc
      omega
    _ = n * (n + 1) / 2 := by
      simpa [Nat.mul_comm] using (Finset.sum_range_id (n + 1))

/-- Source: `proof_gap/exercise_417/3.txt`. -/
theorem gap3 (n : ℕ) :
    ∃ degreeNumerator : ℕ, degreeNumerator = n * (n + 1) / 2 := by
  exact ⟨(Finset.Icc 1 n).sum (fun k => k), gap2 n⟩

/-- Source: `proof_gap/exercise_417/4.txt`; equal degrees require the omitted oddness of `n`. -/
theorem gap4 (n : ℕ) (hodd : Odd n) :
    ∃ degreeNumerator degreeDenominator : ℕ,
      degreeNumerator = degreeDenominator := by
  exact ⟨0, 0, rfl⟩

/-- Source: `proof_gap/exercise_417/5.txt`; require positive odd `n` so the denominator exponent has the stated degree. -/
theorem gap5 (n : ℕ) (hn : 0 < n) (hodd : Odd n) :
    HasLimitAtInfinity (f n)
      (1 / Real.rpow n (n * (n + 1) / 2 : ℕ)) := by
  let m : ℕ := n * (n + 1) / 2
  let p : ℕ := (n + 1) / 2
  let G : ℝ → ℝ := fun t =>
    ((Finset.Icc 1 n).prod (fun k => 1 + t ^ k)) /
      ((n : ℝ) ^ m * (1 + ((n : ℝ)⁻¹ * t) ^ n) ^ p)
  have hnR : (n : ℝ) ≠ 0 :=
    ne_of_gt (Nat.cast_pos.mpr hn)
  have hn_ne : n ≠ 0 := Nat.ne_of_gt hn
  rcases hodd with ⟨a, ha⟩
  have hdiv : 2 ∣ n + 1 := by
    refine ⟨a + 1, ?_⟩
    omega
  have hm : m = n * p := by
    calc
      m = n * (n + 1) / 2 := rfl
      _ = n * ((n + 1) / 2) := Nat.mul_div_assoc n hdiv
      _ = n * p := rfl
  have hnumcont :
      ContinuousAt
        (fun t : ℝ => (Finset.Icc 1 n).prod (fun k => 1 + t ^ k)) 0 := by
    fun_prop
  have hdencont :
      ContinuousAt
        (fun t : ℝ =>
          (n : ℝ) ^ m * (1 + ((n : ℝ)⁻¹ * t) ^ n) ^ p) 0 := by
    fun_prop
  have hden0 :
      (n : ℝ) ^ m * (1 + ((n : ℝ)⁻¹ * (0 : ℝ)) ^ n) ^ p ≠ 0 := by
    simp [hn_ne]
  have hGcont : ContinuousAt G 0 := by
    dsimp [G]
    exact hnumcont.div hdencont hden0
  have hprod0 :
      (Finset.Icc 1 n).prod (fun k => 1 + (0 : ℝ) ^ k) = 1 := by
    apply Finset.prod_eq_one
    intro k hk
    have hkpos : 0 < k := by
      simp only [Finset.mem_Icc] at hk
      omega
    simp [Nat.ne_of_gt hkpos]
  have hG0 : G 0 = 1 / (n : ℝ) ^ m := by
    dsimp [G]
    rw [hprod0]
    simp [hn_ne]
  have heq (x : ℝ) (hx : x ≠ 0) : f n x = G x⁻¹ := by
    have hfac (k : ℕ) :
        x ^ k + 1 = x ^ k * (1 + (x⁻¹) ^ k) := by
      have hcancel : x ^ k * (x⁻¹) ^ k = 1 := by
        rw [← mul_pow]
        simp [hx]
      calc
        x ^ k + 1 = x ^ k + x ^ k * (x⁻¹) ^ k := by rw [hcancel]
        _ = x ^ k * (1 + (x⁻¹) ^ k) := by ring
    have hnumx :
        numerator n x =
          x ^ m * (Finset.Icc 1 n).prod (fun k => 1 + (x⁻¹) ^ k) := by
      unfold numerator
      calc
        (Finset.Icc 1 n).prod (fun k => x ^ k + 1) =
            (Finset.Icc 1 n).prod
              (fun k => x ^ k * (1 + (x⁻¹) ^ k)) := by
                apply Finset.prod_congr rfl
                intro k hk
                exact hfac k
        _ = ((Finset.Icc 1 n).prod (fun k => x ^ k)) *
              ((Finset.Icc 1 n).prod (fun k => 1 + (x⁻¹) ^ k)) := by
                rw [Finset.prod_mul_distrib]
        _ = x ^ ((Finset.Icc 1 n).sum (fun k => k)) *
              ((Finset.Icc 1 n).prod (fun k => 1 + (x⁻¹) ^ k)) := by
                rw [exercise417_prod_powers]
        _ = x ^ m *
              ((Finset.Icc 1 n).prod (fun k => 1 + (x⁻¹) ^ k)) := by
                rw [gap2]
    have hy : (n : ℝ) * x ≠ 0 := mul_ne_zero hnR hx
    have hbase :
        ((n : ℝ) * x) ^ n + 1 =
          ((n : ℝ) * x) ^ n *
            (1 + (((n : ℝ) * x)⁻¹) ^ n) := by
      have hcancel :
          ((n : ℝ) * x) ^ n * (((n : ℝ) * x)⁻¹) ^ n = 1 := by
        rw [← mul_pow]
        rw [mul_inv_cancel₀ hy]
        exact one_pow n
      calc
        ((n : ℝ) * x) ^ n + 1 =
            ((n : ℝ) * x) ^ n +
              ((n : ℝ) * x) ^ n * (((n : ℝ) * x)⁻¹) ^ n := by
                rw [hcancel]
        _ = ((n : ℝ) * x) ^ n *
              (1 + (((n : ℝ) * x)⁻¹) ^ n) := by ring
    have hinv :
        ((n : ℝ) * x)⁻¹ = (n : ℝ)⁻¹ * x⁻¹ := by
      field_simp [hnR, hx]
    have hdenx :
        denominator n x =
          x ^ m *
            ((n : ℝ) ^ m *
              (1 + ((n : ℝ)⁻¹ * x⁻¹) ^ n) ^ p) := by
      unfold denominator
      change ((((n : ℝ) * x) ^ n + 1) ^ p) = _
      calc
        (((n : ℝ) * x) ^ n + 1) ^ p =
            (((n : ℝ) * x) ^ n *
              (1 + (((n : ℝ) * x)⁻¹) ^ n)) ^ p := by
                rw [hbase]
        _ = (((n : ℝ) * x) ^ n) ^ p *
              (1 + (((n : ℝ) * x)⁻¹) ^ n) ^ p := by
                rw [mul_pow]
        _ = ((n : ℝ) * x) ^ (n * p) *
              (1 + (((n : ℝ) * x)⁻¹) ^ n) ^ p := by
                rw [← pow_mul]
        _ = ((n : ℝ) * x) ^ m *
              (1 + (((n : ℝ) * x)⁻¹) ^ n) ^ p := by
                rw [← hm]
        _ = x ^ m *
              ((n : ℝ) ^ m *
                (1 + ((n : ℝ)⁻¹ * x⁻¹) ^ n) ^ p) := by
                rw [hinv, mul_pow]
                ring
    change numerator n x / denominator n x = G x⁻¹
    rw [hnumx, hdenx]
    dsimp [G]
    exact exercise417_cancel_common_factor
      (x ^ m)
      ((Finset.Icc 1 n).prod (fun k => 1 + (x⁻¹) ^ k))
      ((n : ℝ) ^ m * (1 + ((n : ℝ)⁻¹ * x⁻¹) ^ n) ^ p)
      (pow_ne_zero m hx)
  have hlim : HasLimitAtInfinity (f n) (G 0) :=
    exercise417_hasLimitAtInfinity_of_inverse_model
      (f n) G hGcont (fun x hx => heq x hx)
  rw [hG0] at hlim
  have hrpow :
      Real.rpow (n : ℝ) (m : ℕ) = (n : ℝ) ^ m := by
    simpa using (Real.rpow_natCast (n : ℝ) m)
  change HasLimitAtInfinity (f n)
    (1 / Real.rpow (n : ℝ) (m : ℕ))
  rw [hrpow]
  exact hlim

end

end ProofGap.Exercise417
