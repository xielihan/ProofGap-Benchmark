import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise4204

noncomputable section

open MeasureTheory
open scoped Interval

def unitCube (n : ℕ) : Set (Fin n → ℝ) :=
  {x | ∀ i, x i ∈ Set.Icc (0 : ℝ) 1}

def sumSquares {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  ∑ i, (x i) ^ 2

def sumCoordinates {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  ∑ i, x i

def squareMoment (n : ℕ) : ℝ :=
  ∫ x in unitCube n, sumSquares x

def squaredSumMoment (n : ℕ) : ℝ :=
  ∫ x in unitCube n, (sumCoordinates x) ^ 2

def crossTermMoment (n : ℕ) : ℝ :=
  (n : ℝ) * (n - 1 : ℕ) / 8

theorem gap1 (c : ℝ) :
    (∫ t in (0 : ℝ)..1, c + t ^ 2) = c + 1 / 3 := by
  have hc :
      IntervalIntegrable (fun _t : ℝ => c) MeasureTheory.volume 0 1 :=
    continuous_const.intervalIntegrable 0 1
  have ht :
      IntervalIntegrable (fun t : ℝ => t ^ 2) MeasureTheory.volume 0 1 :=
    (continuous_id.pow 2).intervalIntegrable 0 1
  rw [intervalIntegral.integral_add hc ht]
  have hpow :
      (∫ t in (0 : ℝ)..1, t ^ 2) = (1 / 3 : ℝ) := by
    let F : ℝ → ℝ := fun t => t ^ 3 / 3
    have hd : ∀ t : ℝ, HasDerivAt F (t ^ 2) t := by
      intro t
      dsimp [F]
      convert ((hasDerivAt_id t).pow 3).div_const 3 using 1 <;>
        simp [Function.id_def] <;> ring
    have heq := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t _ => hd t) ht
    calc
      (∫ t in (0 : ℝ)..1, t ^ 2) = F 1 - F 0 := heq
      _ = (1 / 3 : ℝ) := by norm_num [F]
  rw [hpow]
  norm_num

private theorem unitCube_eq_pi (n : ℕ) :
    unitCube n =
      Set.univ.pi (fun _i : Fin n => Set.Icc (0 : ℝ) 1) := by
  ext x
  unfold unitCube
  simp only [Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ, true_implies,
    Set.mem_Icc]

private theorem unitCube_integral_eq_pi
    (n : ℕ) (f : (Fin n → ℝ) → ℝ) :
    (∫ x in unitCube n, f x) =
      ∫ x, f x ∂Measure.pi
        (fun _i : Fin n =>
          (MeasureTheory.volume : Measure ℝ).restrict (Set.Icc 0 1)) := by
  change (∫ x, f x ∂MeasureTheory.volume.restrict (unitCube n)) = _
  rw [unitCube_eq_pi, MeasureTheory.volume_pi, Measure.restrict_pi_pi]

private theorem restricted_integral_one :
    (∫ _t : ℝ, (1 : ℝ)
      ∂(MeasureTheory.volume : Measure ℝ).restrict (Set.Icc 0 1)) = 1 := by
  rw [MeasureTheory.integral_const]
  norm_num [Measure.real, Real.volume_Icc]

private theorem restricted_integral_id :
    (∫ t : ℝ, t
      ∂(MeasureTheory.volume : Measure ℝ).restrict (Set.Icc 0 1)) =
      (1 / 2 : ℝ) := by
  change (∫ t in Set.Icc (0 : ℝ) 1, t) = (1 / 2 : ℝ)
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  have h :
      (∫ t in (0 : ℝ)..1, t) = (1 / 2 : ℝ) := by
    let F : ℝ → ℝ := fun t => t ^ 2 / 2
    have hd : ∀ t : ℝ, HasDerivAt F t t := by
      intro t
      dsimp [F]
      convert ((hasDerivAt_id t).pow 2).div_const 2 using 1 <;>
        simp [Function.id_def] <;> ring
    have hi :
        IntervalIntegrable (fun t : ℝ => t) MeasureTheory.volume 0 1 :=
      continuous_id.intervalIntegrable 0 1
    have heq := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t _ => hd t) hi
    calc
      (∫ t in (0 : ℝ)..1, t) = F 1 - F 0 := heq
      _ = (1 / 2 : ℝ) := by norm_num [F]
  exact h

private theorem restricted_integral_sq :
    (∫ t : ℝ, t ^ 2
      ∂(MeasureTheory.volume : Measure ℝ).restrict (Set.Icc 0 1)) =
      (1 / 3 : ℝ) := by
  change (∫ t in Set.Icc (0 : ℝ) 1, t ^ 2) = (1 / 3 : ℝ)
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  simpa using gap1 (0 : ℝ)

private theorem restricted_integrable_one :
    Integrable (fun _t : ℝ => (1 : ℝ))
      ((MeasureTheory.volume : Measure ℝ).restrict (Set.Icc 0 1)) :=
  continuous_const.integrableOn_Icc

private theorem restricted_integrable_id :
    Integrable (fun t : ℝ => t)
      ((MeasureTheory.volume : Measure ℝ).restrict (Set.Icc 0 1)) :=
  continuous_id.integrableOn_Icc

private theorem restricted_integrable_sq :
    Integrable (fun t : ℝ => t ^ 2)
      ((MeasureTheory.volume : Measure ℝ).restrict (Set.Icc 0 1)) :=
  (continuous_id.pow 2).integrableOn_Icc

private theorem unitCube_integral_sq
    (n : ℕ) (i : Fin n) :
    (∫ x in unitCube n, (x i) ^ 2) = (1 / 3 : ℝ) := by
  rw [unitCube_integral_eq_pi]
  let μ : Fin n → Measure ℝ :=
    fun _i => (MeasureTheory.volume : Measure ℝ).restrict (Set.Icc 0 1)
  let f : (j : Fin n) → ℝ → ℝ :=
    fun j t => if j = i then t ^ 2 else 1
  have hprod : ∀ x : Fin n → ℝ, (x i) ^ 2 = ∏ j, f j (x j) := by
    intro x
    classical
    simp [f]
  simp_rw [hprod]
  change (∫ x : Fin n → ℝ, ∏ j, f j (x j) ∂Measure.pi μ) = _
  rw [MeasureTheory.integral_fintype_prod_eq_prod]
  classical
  have hint : ∀ j : Fin n,
      (∫ t : ℝ, f j t ∂μ j) =
        if j = i then (1 / 3 : ℝ) else 1 := by
    intro j
    by_cases hji : j = i
    · subst j
      simpa [f, μ] using restricted_integral_sq
    · simpa [f, μ, hji] using restricted_integral_one
  rw [Finset.prod_congr rfl (fun j _ => hint j)]
  simp

private theorem unitCube_integrable_sq
    (n : ℕ) (i : Fin n) :
    IntegrableOn (fun x : Fin n → ℝ => (x i) ^ 2) (unitCube n) := by
  change Integrable (fun x : Fin n → ℝ => (x i) ^ 2)
    (MeasureTheory.volume.restrict (unitCube n))
  rw [unitCube_eq_pi, MeasureTheory.volume_pi, Measure.restrict_pi_pi]
  exact MeasureTheory.integrable_comp_eval
    (μ := fun _j : Fin n =>
      (MeasureTheory.volume : Measure ℝ).restrict (Set.Icc 0 1))
    (i := i) restricted_integrable_sq

theorem gap2 (n : ℕ) :
    squareMoment n = (n : ℝ) / 3 := by
  unfold squareMoment sumSquares
  calc
    (∫ x in unitCube n, ∑ i, (x i) ^ 2) =
        ∑ i : Fin n, ∫ x in unitCube n, (x i) ^ 2 := by
      apply MeasureTheory.integral_finset_sum
      intro i hi
      exact unitCube_integrable_sq n i
    _ = ∑ _i : Fin n, (1 / 3 : ℝ) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact unitCube_integral_sq n i
    _ = (n : ℝ) / 3 := by simp [div_eq_mul_inv]

theorem gap3 {n : ℕ} (x : Fin n → ℝ) :
    (sumCoordinates x) ^ 2 =
      sumSquares x +
        2 * ∑ i, ∑ j ∈ Finset.univ.filter (fun j : Fin n => i < j),
          x i * x j := by
  induction n with
  | zero =>
      simp [sumCoordinates, sumSquares]
  | succ n ih =>
      let y : Fin n → ℝ := fun i => x i.succ
      have hih := ih y
      simp only [sumCoordinates, sumSquares] at hih ⊢
      simp only [Fin.sum_univ_succ, Finset.sum_filter] at hih ⊢
      simp only [Fin.succ_lt_succ_iff] at hih ⊢
      simp at ⊢
      dsimp [y] at hih
      have hcross :
          (∑ i : Fin n, x 0 * x i.succ) =
            x 0 * ∑ i : Fin n, x i.succ := by
        rw [Finset.mul_sum]
      rw [hcross]
      ring_nf at hih ⊢
      linarith

private theorem prod_ite_eq_eval
    {n : ℕ} (i : Fin n) (x : Fin n → ℝ) :
    (∏ k : Fin n, if k = i then x k else 1) = x i := by
  have h := Finset.prod_ite_eq (Finset.univ : Finset (Fin n)) i x
  simpa [eq_comm] using h

private theorem prod_ite_eq_value
    {n : ℕ} (i : Fin n) (v : ℝ) :
    (∏ k : Fin n, if k = i then v else 1) = v := by
  simpa using prod_ite_eq_eval i (fun _k => v)

private theorem unitCube_integral_mul
    (n : ℕ) (i j : Fin n) (hij : i ≠ j) :
    (∫ x in unitCube n, x i * x j) = (1 / 4 : ℝ) := by
  rw [unitCube_integral_eq_pi]
  let μ : Fin n → Measure ℝ :=
    fun _k => (MeasureTheory.volume : Measure ℝ).restrict (Set.Icc 0 1)
  let f : (k : Fin n) → ℝ → ℝ :=
    fun k t =>
      (if k = i then t else 1) * (if k = j then t else 1)
  have hprod : ∀ x : Fin n → ℝ, x i * x j = ∏ k, f k (x k) := by
    intro x
    classical
    change x i * x j =
      ∏ k : Fin n,
        (if k = i then x k else 1) * (if k = j then x k else 1)
    rw [Finset.prod_mul_distrib, prod_ite_eq_eval, prod_ite_eq_eval]
  simp_rw [hprod]
  change (∫ x : Fin n → ℝ, ∏ k, f k (x k) ∂Measure.pi μ) = _
  rw [MeasureTheory.integral_fintype_prod_eq_prod]
  classical
  have hint : ∀ k : Fin n,
      (∫ t : ℝ, f k t ∂μ k) =
        (if k = i then (1 / 2 : ℝ) else 1) *
          (if k = j then (1 / 2 : ℝ) else 1) := by
    intro k
    by_cases hki : k = i
    · subst k
      simpa [f, μ, hij] using restricted_integral_id
    · by_cases hkj : k = j
      · subst k
        simpa [f, μ, hki] using restricted_integral_id
      · simpa [f, μ, hki, hkj] using restricted_integral_one
  rw [Finset.prod_congr rfl (fun k _ => hint k)]
  rw [Finset.prod_mul_distrib, prod_ite_eq_value, prod_ite_eq_value]
  norm_num

private theorem unitCube_integrable_mul
    (n : ℕ) (i j : Fin n) (hij : i ≠ j) :
    IntegrableOn (fun x : Fin n → ℝ => x i * x j) (unitCube n) := by
  change Integrable (fun x : Fin n → ℝ => x i * x j)
    (MeasureTheory.volume.restrict (unitCube n))
  rw [unitCube_eq_pi, MeasureTheory.volume_pi, Measure.restrict_pi_pi]
  let μ : Fin n → Measure ℝ :=
    fun _k => (MeasureTheory.volume : Measure ℝ).restrict (Set.Icc 0 1)
  let f : (k : Fin n) → ℝ → ℝ :=
    fun k t =>
      (if k = i then t else 1) * (if k = j then t else 1)
  have hf : ∀ k : Fin n, Integrable (f k) (μ k) := by
    intro k
    by_cases hki : k = i
    · subst k
      simpa [f, μ, hij] using restricted_integrable_id
    · by_cases hkj : k = j
      · subst k
        simpa [f, μ, hki] using restricted_integrable_id
      · simpa [f, μ, hki, hkj] using restricted_integrable_one
  have hp :
      Integrable (fun x : Fin n → ℝ => ∏ k, f k (x k))
        (Measure.pi μ) :=
    MeasureTheory.Integrable.fintype_prod hf
  have hfun :
      (fun x : Fin n → ℝ => x i * x j) =
        fun x => ∏ k, f k (x k) := by
    funext x
    classical
    change x i * x j =
      ∏ k : Fin n,
        (if k = i then x k else 1) * (if k = j then x k else 1)
    rw [Finset.prod_mul_distrib, prod_ite_eq_eval, prod_ite_eq_eval]
  rw [hfun]
  exact hp

private def upperCrossSum {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  ∑ i, ∑ j ∈ Finset.univ.filter (fun j : Fin n => i < j), x i * x j

private theorem unitCube_integrable_sumSquares (n : ℕ) :
    IntegrableOn (fun x : Fin n → ℝ => sumSquares x) (unitCube n) := by
  unfold sumSquares
  apply MeasureTheory.integrable_finset_sum Finset.univ
  intro i hi
  exact unitCube_integrable_sq n i

private theorem unitCube_integrable_upperCrossSum (n : ℕ) :
    IntegrableOn (fun x : Fin n → ℝ => upperCrossSum x) (unitCube n) := by
  unfold upperCrossSum
  apply MeasureTheory.integrable_finset_sum Finset.univ
  intro i hi
  apply MeasureTheory.integrable_finset_sum
    (Finset.univ.filter (fun j : Fin n => i < j))
  intro j hj
  exact unitCube_integrable_mul n i j
    (ne_of_lt (Finset.mem_filter.mp hj).2)

private theorem upperPairQuarterSum (n : ℕ) :
    (∑ i : Fin n,
      ∑ _j ∈ Finset.univ.filter (fun j : Fin n => i < j),
        (1 / 4 : ℝ)) =
      crossTermMoment n := by
  induction n with
  | zero =>
      simp [crossTermMoment]
  | succ n ih =>
      simp only [Fin.sum_univ_succ, Finset.sum_filter] at ih ⊢
      simp only [Fin.succ_lt_succ_iff] at ih ⊢
      simp at ⊢
      norm_num only [one_div] at ih ⊢
      rw [ih]
      by_cases hn : n = 0
      · subst n
        norm_num [crossTermMoment]
      · have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
        simp [crossTermMoment, Nat.succ_sub_one]
        push_cast [Nat.cast_sub hn1]
        ring

private theorem unitCube_integral_upperCrossSum (n : ℕ) :
    (∫ x in unitCube n, upperCrossSum x) = crossTermMoment n := by
  unfold upperCrossSum
  calc
    (∫ x in unitCube n,
        ∑ i, ∑ j ∈ Finset.univ.filter (fun j : Fin n => i < j),
          x i * x j) =
        ∑ i : Fin n,
          ∫ x in unitCube n,
            ∑ j ∈ Finset.univ.filter (fun j : Fin n => i < j),
              x i * x j := by
      apply MeasureTheory.integral_finset_sum
      intro i hi
      apply MeasureTheory.integrable_finset_sum
        (Finset.univ.filter (fun j : Fin n => i < j))
      intro j hj
      exact unitCube_integrable_mul n i j
        (ne_of_lt (Finset.mem_filter.mp hj).2)
    _ = ∑ i : Fin n,
          ∑ j ∈ Finset.univ.filter (fun j : Fin n => i < j),
            ∫ x in unitCube n, x i * x j := by
      apply Finset.sum_congr rfl
      intro i hi
      apply MeasureTheory.integral_finset_sum
      intro j hj
      exact unitCube_integrable_mul n i j
        (ne_of_lt (Finset.mem_filter.mp hj).2)
    _ = ∑ i : Fin n,
          ∑ _j ∈ Finset.univ.filter (fun j : Fin n => i < j),
            (1 / 4 : ℝ) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      exact unitCube_integral_mul n i j
        (ne_of_lt (Finset.mem_filter.mp hj).2)
    _ = crossTermMoment n := upperPairQuarterSum n

theorem gap4 (n : ℕ) :
    squaredSumMoment n =
      (n : ℝ) / 3 + 2 * crossTermMoment n := by
  unfold squaredSumMoment
  calc
    (∫ x in unitCube n, (sumCoordinates x) ^ 2) =
        ∫ x in unitCube n,
          sumSquares x + 2 * upperCrossSum x := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards with x
      simpa [upperCrossSum] using gap3 x
    _ = (∫ x in unitCube n, sumSquares x) +
          ∫ x in unitCube n, 2 * upperCrossSum x := by
      rw [MeasureTheory.integral_add
        (unitCube_integrable_sumSquares n)
        ((unitCube_integrable_upperCrossSum n).const_mul 2)]
    _ = squareMoment n +
          2 * (∫ x in unitCube n, upperCrossSum x) := by
      rw [MeasureTheory.integral_const_mul]
      rfl
    _ = (n : ℝ) / 3 + 2 * crossTermMoment n := by
      rw [gap2 n, unitCube_integral_upperCrossSum n]

theorem gap5 (n : ℕ) :
    squaredSumMoment n =
      (n : ℝ) * (3 * (n : ℝ) + 1) / 12 := by
  rw [gap4 n]
  unfold crossTermMoment
  cases n with
  | zero => norm_num
  | succ k =>
      simp only [Nat.succ_sub_one, Nat.cast_succ]
      push_cast
      ring

end

end ProofGap.Exercise4204

