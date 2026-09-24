import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.MeanInequalities
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise3648

open scoped BigOperators

noncomputable section

def weight {n : ℕ} (i : Fin n) : ℝ :=
  (i.val + 1 : ℕ)

def weightedSum {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  ∑ i, weight i * x i

def u (n : ℕ) (x : Fin n → ℝ) : ℝ :=
  (∏ i, x i ^ (i.val + 1)) * (1 - weightedSum x)

def positiveOrthant (n : ℕ) : Set (Fin n → ℝ) :=
  {x | ∀ i, 0 < x i}

def partialCoord {n : ℕ} (f : (Fin n → ℝ) → ℝ)
    (x : Fin n → ℝ) (i : Fin n) : ℝ :=
  deriv (fun t => f (Function.update x i t)) (x i)

def Stationary (n : ℕ) (x : Fin n → ℝ) : Prop :=
  ∀ i, partialCoord (u n) x i = 0

def triangular (n : ℕ) : ℕ :=
  n * (n + 1) / 2

def x₀ (n : ℕ) : ℝ :=
  2 / ((n : ℝ) ^ 2 + n + 2)

def p₀ (n : ℕ) : Fin n → ℝ :=
  fun _ => x₀ n

def IsLocalMaximumOn (n : ℕ) (p : Fin n → ℝ) : Prop :=
  p ∈ positiveOrthant n ∧
    ∃ ε : ℝ, 0 < ε ∧
      ∀ q ∈ positiveOrthant n, dist q p < ε → u n q ≤ u n p

def IsLocalMinimumOn (n : ℕ) (p : Fin n → ℝ) : Prop :=
  p ∈ positiveOrthant n ∧
    ∃ ε : ℝ, 0 < ε ∧
      ∀ q ∈ positiveOrthant n, dist q p < ε → u n p ≤ u n q

def secondVariationAtP₀ (n : ℕ) (v : Fin n → ℝ) : ℝ :=
  -(x₀ n) ^ (triangular n - 1) *
    ((∑ i, weight i * (v i) ^ 2) + (∑ i, weight i * v i) ^ 2)

def NegativeDefiniteAtP₀ (n : ℕ) : Prop :=
  ∀ v : Fin n → ℝ, v ≠ 0 → secondVariationAtP₀ n v < 0

def IsUniqueGlobalMaximizerOn (n : ℕ) (p : Fin n → ℝ) : Prop :=
  p ∈ positiveOrthant n ∧
    (∀ q ∈ positiveOrthant n, u n q ≤ u n p) ∧
    (∀ q ∈ positiveOrthant n, u n q = u n p → q = p)

def maximumPointsOn (n : ℕ) : Set (Fin n → ℝ) :=
  {p | p ∈ positiveOrthant n ∧
    ∀ q ∈ positiveOrthant n, u n q ≤ u n p}

private lemma sum_weights_eq_triangular (n : ℕ) :
    (∑ i : Fin n, (i.val + 1)) = triangular n := by
  have hshift :
      (∑ i ∈ Finset.range n, (i + 1)) =
        ∑ i ∈ Finset.range (n + 1), i := by
    rw [Finset.sum_range_succ]
    rw [Finset.sum_add_distrib]
    simp
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => i + 1) n]
  change (∑ i ∈ Finset.range n, (i + 1)) = triangular n
  rw [hshift, Finset.sum_range_id]
  simp only [Nat.add_sub_cancel, triangular]
  rw [mul_comm]

private lemma two_mul_triangular (n : ℕ) :
    2 * triangular n = n * (n + 1) := by
  unfold triangular
  exact Nat.mul_div_cancel' (Nat.even_mul_succ_self n).two_dvd

private lemma two_mul_triangular_add_one (n : ℕ) :
    2 * (triangular n + 1) = n ^ 2 + n + 2 := by
  rw [mul_add, two_mul_triangular]
  ring

private lemma x₀_eq_inv (n : ℕ) :
    x₀ n = 1 / ((triangular n + 1 : ℕ) : ℝ) := by
  unfold x₀
  have hden :
      ((n : ℝ) ^ 2 + n + 2) =
        2 * ((triangular n + 1 : ℕ) : ℝ) := by
    exact_mod_cast (two_mul_triangular_add_one n).symm
  rw [hden]
  have hpos : (0 : ℝ) < (triangular n + 1 : ℕ) := by positivity
  field_simp

private lemma sum_weights_real (n : ℕ) :
    (∑ i : Fin n, weight i) = (triangular n : ℝ) := by
  unfold weight
  exact_mod_cast sum_weights_eq_triangular n

private lemma x₀_pos (n : ℕ) : 0 < x₀ n := by
  rw [x₀_eq_inv]
  positivity

private lemma p₀_positive (n : ℕ) :
    p₀ n ∈ positiveOrthant n := by
  intro i
  exact x₀_pos n

private lemma weightedSum_p₀ (n : ℕ) :
    weightedSum (p₀ n) = (triangular n : ℝ) * x₀ n := by
  unfold weightedSum p₀
  rw [← Finset.sum_mul]
  rw [sum_weights_real]

private lemma slack_p₀ (n : ℕ) :
    1 - weightedSum (p₀ n) = x₀ n := by
  rw [weightedSum_p₀, x₀_eq_inv]
  have hne : ((triangular n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp [hne]
  norm_num

private lemma weightedSum_update {n : ℕ} (x : Fin n → ℝ)
    (i : Fin n) (t : ℝ) :
    weightedSum (Function.update x i t) =
      weightedSum x + weight i * (t - x i) := by
  classical
  unfold weightedSum
  rw [← Finset.add_sum_erase (s := Finset.univ)
      (f := fun j : Fin n => weight j * Function.update x i t j)
      (Finset.mem_univ i)]
  rw [← Finset.add_sum_erase (s := Finset.univ)
      (f := fun j : Fin n => weight j * x j)
      (Finset.mem_univ i)]
  simp only [Function.update_self]
  have htail :
      (∑ j ∈ Finset.univ.erase i,
          weight j * Function.update x i t j) =
        ∑ j ∈ Finset.univ.erase i, weight j * x j := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
  rw [htail]
  ring

private lemma value_p₀ (n : ℕ) :
    u n (p₀ n) = (x₀ n) ^ (triangular n + 1) := by
  unfold u
  rw [slack_p₀]
  have hprod :
      (∏ i : Fin n, p₀ n i ^ (i.val + 1)) =
        (x₀ n) ^ triangular n := by
    simp only [p₀]
    rw [Finset.prod_pow_eq_pow_sum]
    congr 1
    exact sum_weights_eq_triangular n
  rw [hprod]
  exact pow_succ _ _

theorem gap1 (n : ℕ) (hn : 0 < n) :
    ∀ x ∈ positiveOrthant n, 1 - weightedSum x = 0 →
      ¬ IsLocalMaximumOn n x ∧ ¬ IsLocalMinimumOn n x := by
  intro x hx hzero
  classical
  let i : Fin n := ⟨0, hn⟩
  have hxi : 0 < x i := hx i
  constructor
  · rintro ⟨hxp, ε, hε, hmax⟩
    let δ : ℝ := min (x i / 2) (ε / 2)
    have hδ : 0 < δ := by
      dsimp [δ]
      exact lt_min (half_pos hxi) (half_pos hε)
    have hδx : δ < x i := by
      have hle : δ ≤ x i / 2 := min_le_left _ _
      linarith
    have hδε : δ < ε := by
      have hle : δ ≤ ε / 2 := min_le_right _ _
      linarith
    let q : Fin n → ℝ := Function.update x i (x i - δ)
    have hq : q ∈ positiveOrthant n := by
      intro j
      by_cases hji : j = i
      · subst j
        simp only [q, Function.update_self]
        linarith
      · simp only [q, Function.update_of_ne hji]
        exact hx j
    have hdist : dist q x < ε := by
      apply (dist_pi_lt_iff hε).2
      intro j
      by_cases hji : j = i
      · subst j
        simp only [q, Function.update_self, Real.dist_eq]
        rw [show x i - δ - x i = -δ by ring, abs_neg]
        rw [abs_of_nonneg hδ.le]
        exact hδε
      · simp only [q, Function.update_of_ne hji, dist_self]
        exact hε
    have hslackq : 0 < 1 - weightedSum q := by
      simp only [q, weightedSum_update]
      have hw : 0 < weight i := by
        unfold weight
        positivity
      nlinarith
    have hprodq : 0 < ∏ j : Fin n, q j ^ (j.val + 1) :=
      Finset.prod_pos fun j _ => pow_pos (hq j) _
    have huq : 0 < u n q := by
      unfold u
      exact mul_pos hprodq hslackq
    have hux : u n x = 0 := by
      unfold u
      rw [hzero, mul_zero]
    have hcontra := hmax q hq hdist
    rw [hux] at hcontra
    linarith
  · rintro ⟨hxp, ε, hε, hmin⟩
    let δ : ℝ := min (x i / 2) (ε / 2)
    have hδ : 0 < δ := by
      dsimp [δ]
      exact lt_min (half_pos hxi) (half_pos hε)
    have hδε : δ < ε := by
      have hle : δ ≤ ε / 2 := min_le_right _ _
      linarith
    let q : Fin n → ℝ := Function.update x i (x i + δ)
    have hq : q ∈ positiveOrthant n := by
      intro j
      by_cases hji : j = i
      · subst j
        simp only [q, Function.update_self]
        linarith
      · simp only [q, Function.update_of_ne hji]
        exact hx j
    have hdist : dist q x < ε := by
      apply (dist_pi_lt_iff hε).2
      intro j
      by_cases hji : j = i
      · subst j
        simp only [q, Function.update_self, Real.dist_eq]
        rw [show x i + δ - x i = δ by ring]
        rw [abs_of_nonneg hδ.le]
        exact hδε
      · simp only [q, Function.update_of_ne hji, dist_self]
        exact hε
    have hslackq : 1 - weightedSum q < 0 := by
      simp only [q, weightedSum_update]
      have hw : 0 < weight i := by
        unfold weight
        positivity
      nlinarith
    have hprodq : 0 < ∏ j : Fin n, q j ^ (j.val + 1) :=
      Finset.prod_pos fun j _ => pow_pos (hq j) _
    have huq : u n q < 0 := by
      unfold u
      exact mul_neg_of_pos_of_neg hprodq hslackq
    have hux : u n x = 0 := by
      unfold u
      rw [hzero, mul_zero]
    have hcontra := hmin q hq hdist
    rw [hux] at hcontra
    linarith

theorem gap2 (n : ℕ) :
    ∀ x ∈ positiveOrthant n, 1 - weightedSum x ≠ 0 →
      ∀ i,
        partialCoord (u n) x i =
          u n x *
            (weight i / x i - weight i / (1 - weightedSum x)) := by
  intro x hx hslack i
  classical
  let P : ℝ := (∏ j ∈ Finset.univ.erase i, x j ^ (j.val + 1))
  let S : ℝ := (∑ j ∈ Finset.univ.erase i, weight j * x j)
  have hprod (t : ℝ) :
      (∏ j : Fin n, (Function.update x i t j) ^ (j.val + 1)) =
        t ^ (i.val + 1) * P := by
    rw [← Finset.mul_prod_erase (s := Finset.univ)
      (f := fun j : Fin n => (Function.update x i t j) ^ (j.val + 1))
      (Finset.mem_univ i)]
    simp only [Function.update_self]
    congr 1
    apply Finset.prod_congr rfl
    intro j hj
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
  have hsum (t : ℝ) :
      weightedSum (Function.update x i t) = weight i * t + S := by
    unfold weightedSum
    rw [← Finset.add_sum_erase (s := Finset.univ)
      (f := fun j : Fin n => weight j * Function.update x i t j)
      (Finset.mem_univ i)]
    simp only [Function.update_self]
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
  have heq :
      (fun t => u n (Function.update x i t)) =
        (fun t => t ^ (i.val + 1) * P *
          (1 - (weight i * t + S))) := by
    funext t
    simp only [u, hprod, hsum]
  have hpow :
      HasDerivAt (fun t : ℝ => t ^ (i.val + 1))
        ((i.val + 1 : ℕ) * (x i) ^ i.val) (x i) := by
    convert (hasDerivAt_id (x i)).pow (i.val + 1) using 1 <;>
      norm_num
  have hlin :
      HasDerivAt (fun t : ℝ => 1 - (weight i * t + S))
        (-weight i) (x i) := by
    convert (hasDerivAt_const (x i) 1).sub
      (((hasDerivAt_id (x i)).const_mul (weight i)).add_const S)
      using 1 <;> simp <;> ring
  have hderiv :=
    (hpow.mul_const P).mul hlin
  unfold partialCoord
  rw [heq]
  change
    deriv
      ((fun t : ℝ => t ^ (i.val + 1) * P) *
        fun t : ℝ => 1 - (weight i * t + S)) (x i) = _
  rw [hderiv.deriv]
  have hxi : x i ≠ 0 := ne_of_gt (hx i)
  have hw :
      weight i = ((i.val + 1 : ℕ) : ℝ) := rfl
  have hprodX :
      (∏ j : Fin n, x j ^ (j.val + 1)) =
        x i ^ (i.val + 1) * P := by
    rw [← Finset.mul_prod_erase (s := Finset.univ)
      (f := fun j : Fin n => x j ^ (j.val + 1))
      (Finset.mem_univ i)]
  have hsumX : weightedSum x = weight i * x i + S := by
    unfold weightedSum
    rw [← Finset.add_sum_erase (s := Finset.univ)
      (f := fun j : Fin n => weight j * x j)
      (Finset.mem_univ i)]
  have hden : 1 - (weight i * x i + S) ≠ 0 := by
    rwa [hsumX] at hslack
  have hden' :
      1 - (((i.val + 1 : ℕ) : ℝ) * x i + S) ≠ 0 := by
    simpa only [hw] using hden
  unfold u
  rw [hprodX, hsumX]
  rw [hw]
  field_simp [hxi, hden']
  ring

theorem gap3 (n : ℕ) (hn : 0 < n) :
    ∀ x ∈ positiveOrthant n, 1 - weightedSum x ≠ 0 →
      (Stationary n x ↔ x = p₀ n) := by
  intro x hx hslack
  constructor
  · intro hstat
    have hprodPos : 0 < ∏ i : Fin n, x i ^ (i.val + 1) :=
      Finset.prod_pos fun i _ => pow_pos (hx i) _
    have hu_ne : u n x ≠ 0 := by
      unfold u
      exact mul_ne_zero hprodPos.ne' hslack
    have hcoord (i : Fin n) :
        x i = 1 - weightedSum x := by
      have hi := hstat i
      rw [gap2 n x hx hslack i] at hi
      have hbracket :
          weight i / x i - weight i / (1 - weightedSum x) = 0 :=
        (mul_eq_zero.mp hi).resolve_left hu_ne
      have hxi : x i ≠ 0 := (hx i).ne'
      have hw : 0 < weight i := by
        unfold weight
        positivity
      field_simp [hxi, hslack] at hbracket
      nlinarith
    let c : ℝ := 1 - weightedSum x
    have hsum :
        weightedSum x = (triangular n : ℝ) * c := by
      unfold weightedSum
      simp_rw [hcoord]
      rw [← Finset.sum_mul, sum_weights_real]
    have hcrel : c = 1 - (triangular n : ℝ) * c := by
      calc
        c = 1 - weightedSum x := rfl
        _ = 1 - (triangular n : ℝ) * c :=
          congrArg (fun z : ℝ => 1 - z) hsum
    have hc_mul :
        c * ((triangular n : ℝ) + 1) = 1 := by
      calc
        c * ((triangular n : ℝ) + 1) =
            (triangular n : ℝ) * c + c := by ring
        _ = 1 := by linarith
    have hc : c = x₀ n := by
      rw [x₀_eq_inv]
      exact (eq_div_iff (by positivity :
        ((triangular n + 1 : ℕ) : ℝ) ≠ 0)).2 (by
          norm_num at hc_mul ⊢
          exact hc_mul)
    funext i
    rw [hcoord]
    exact hc
  · rintro rfl
    intro i
    rw [gap2 n (p₀ n) (p₀_positive n)
      (by rw [slack_p₀]; exact (x₀_pos n).ne') i]
    rw [slack_p₀]
    simp only [p₀]
    ring

theorem gap4 (n : ℕ) :
    x₀ n = 2 / ((n : ℝ) ^ 2 + n + 2) := by
  rfl

theorem gap5 (n : ℕ) (hn : 0 < n) :
    p₀ n ∈ positiveOrthant n ∧ Stationary n (p₀ n) := by
  refine ⟨p₀_positive n, ?_⟩
  exact (gap3 n hn (p₀ n) (p₀_positive n)
    (by rw [slack_p₀]; exact (x₀_pos n).ne')).2 rfl

theorem gap6 (n : ℕ) :
    ∀ v : Fin n → ℝ,
      secondVariationAtP₀ n v =
        -(x₀ n) ^ (triangular n - 1) *
          ((∑ i, weight i * (v i) ^ 2) +
            (∑ i, weight i * v i) ^ 2) := by
  intro v
  rfl

theorem gap7 (n : ℕ) (hn : 0 < n) :
    ∀ v : Fin n → ℝ, v ≠ 0 →
      -(x₀ n) ^ (triangular n - 1) *
        ((∑ i, weight i * (v i) ^ 2) +
          (∑ i, weight i * v i) ^ 2) < 0 := by
  intro v hv
  have hex : ∃ i : Fin n, v i ≠ 0 := by
    by_contra h
    push_neg at h
    exact hv (funext h)
  obtain ⟨i, hi⟩ := hex
  have hwpos (j : Fin n) : 0 < weight j := by
    unfold weight
    positivity
  have hterms (j : Fin n) : 0 ≤ weight j * (v j) ^ 2 :=
    mul_nonneg (hwpos j).le (sq_nonneg _)
  have hiterm : 0 < weight i * (v i) ^ 2 :=
    mul_pos (hwpos i) (sq_pos_of_ne_zero hi)
  have hsumpos : 0 < ∑ j : Fin n, weight j * (v j) ^ 2 := by
    exact Finset.sum_pos' (fun j _ => hterms j)
      ⟨i, Finset.mem_univ i, hiterm⟩
  have hbracket :
      0 < (∑ j : Fin n, weight j * (v j) ^ 2) +
        (∑ j : Fin n, weight j * v j) ^ 2 :=
    add_pos_of_pos_of_nonneg hsumpos (sq_nonneg _)
  have hpow : 0 < (x₀ n) ^ (triangular n - 1) :=
    pow_pos (x₀_pos n) _
  exact mul_neg_of_neg_of_pos (neg_neg_of_pos hpow) hbracket

theorem gap8 (n : ℕ) (hn : 0 < n) :
    NegativeDefiniteAtP₀ n := by
  intro v hv
  unfold secondVariationAtP₀
  exact gap7 n hn v hv

private lemma nonnegative_slack_bound (n : ℕ) (hn : 0 < n)
    (x : Fin n → ℝ) (hx : x ∈ positiveOrthant n)
    (hslack : 0 ≤ 1 - weightedSum x) :
    u n x ≤ u n (p₀ n) ∧
      (u n x = u n (p₀ n) → x = p₀ n) := by
  let E : ℕ := triangular n + 1
  have hEne : E ≠ 0 := by
    dsimp only [E]
    omega
  have hEpos : (0 : ℝ) < E := by positivity
  have hcoord : x₀ n = 1 / (E : ℝ) := by
    simpa only [E] using x₀_eq_inv n
  have hmax : u n (p₀ n) = (1 / (E : ℝ)) ^ E := by
    rw [value_p₀ n, hcoord]
  let w : Option (Fin n) → ℝ
    | none => 1
    | some i => weight i
  let v : Option (Fin n) → ℝ
    | none => 1 - weightedSum x
    | some i => x i
  have hsumw :
      ∑ i ∈ (Finset.univ : Finset (Option (Fin n))), w i = (E : ℝ) := by
    change (∑ i : Option (Fin n), w i) = (E : ℝ)
    rw [Fintype.sum_option]
    change 1 + ∑ i : Fin n, weight i = (E : ℝ)
    rw [sum_weights_real]
    dsimp only [E]
    norm_num
    ring
  have hsumwv :
      ∑ i ∈ (Finset.univ : Finset (Option (Fin n))), w i * v i = 1 := by
    change (∑ i : Option (Fin n), w i * v i) = 1
    rw [Fintype.sum_option]
    simp only [w, v, one_mul]
    unfold weightedSum
    ring
  have hprod :
      ∏ i ∈ (Finset.univ : Finset (Option (Fin n))), v i ^ w i = u n x := by
    change (∏ i : Option (Fin n), v i ^ w i) = u n x
    rw [Fintype.prod_option]
    simp only [v, w, Real.rpow_one]
    simp_rw [weight, Real.rpow_natCast]
    unfold u
    ring
  have hw : ∀ i ∈ (Finset.univ : Finset (Option (Fin n))), 0 ≤ w i := by
    intro i hi
    cases i with
    | none => simp [w]
    | some i =>
        simp only [w]
        unfold weight
        positivity
  have hwpos :
      0 < ∑ i ∈ (Finset.univ : Finset (Option (Fin n))), w i := by
    rw [hsumw]
    exact hEpos
  have hv : ∀ i ∈ (Finset.univ : Finset (Option (Fin n))), 0 ≤ v i := by
    intro i hi
    cases i with
    | none => simpa [v] using hslack
    | some i => exact (hx i).le
  have hamgm := Real.geom_mean_le_arith_mean
    (Finset.univ : Finset (Option (Fin n))) w v hw hwpos hv
  rw [hprod, hsumw, hsumwv] at hamgm
  have hu_nonneg : 0 ≤ u n x := by
    unfold u
    exact mul_nonneg
      (Finset.prod_nonneg fun i _ => pow_nonneg (hx i).le _)
      hslack
  have hroot_nonneg : 0 ≤ u n x ^ ((E : ℝ)⁻¹) :=
    Real.rpow_nonneg hu_nonneg _
  have hpow := pow_le_pow_left₀ hroot_nonneg hamgm E
  rw [Real.rpow_inv_natCast_pow hu_nonneg hEne] at hpow
  have hle : u n x ≤ u n (p₀ n) := by
    rw [hmax]
    exact hpow
  refine ⟨hle, ?_⟩
  intro heq
  have hrootEq :
      u n x ^ ((E : ℝ)⁻¹) = 1 / (E : ℝ) := by
    rw [heq, hmax]
    exact Real.pow_rpow_inv_natCast (by positivity) hEne
  let wn : Option (Fin n) → ℝ := fun i => w i / (E : ℝ)
  have hwnpos :
      ∀ i ∈ (Finset.univ : Finset (Option (Fin n))), 0 < wn i := by
    intro i hi
    unfold wn
    apply div_pos _ hEpos
    cases i with
    | none => simp [w]
    | some i =>
        simp only [w]
        unfold weight
        positivity
  have hsumwn :
      ∑ i ∈ (Finset.univ : Finset (Option (Fin n))), wn i = 1 := by
    simp_rw [wn, div_eq_mul_inv, ← Finset.sum_mul]
    rw [hsumw]
    field_simp
  have hsumwnv :
      ∑ i ∈ (Finset.univ : Finset (Option (Fin n))), wn i * v i =
        1 / (E : ℝ) := by
    calc
      ∑ i ∈ (Finset.univ : Finset (Option (Fin n))), wn i * v i =
          (∑ i ∈ (Finset.univ : Finset (Option (Fin n))), w i * v i) /
            (E : ℝ) := by
              calc
                (∑ i : Option (Fin n), wn i * v i) =
                    ∑ i : Option (Fin n), (w i * v i) / (E : ℝ) := by
                      apply Finset.sum_congr rfl
                      intro i hi
                      unfold wn
                      ring
                _ = (∑ i : Option (Fin n), w i * v i) / (E : ℝ) := by
                      rw [Finset.sum_div]
      _ = 1 / (E : ℝ) := by rw [hsumwv]
  have hprodNorm :
      (∏ i ∈ (Finset.univ : Finset (Option (Fin n))), v i ^ wn i) =
        u n x ^ ((E : ℝ)⁻¹) := by
    calc
      (∏ i ∈ (Finset.univ : Finset (Option (Fin n))), v i ^ wn i) =
          ∏ i ∈ (Finset.univ : Finset (Option (Fin n))),
            (v i ^ w i) ^ ((E : ℝ)⁻¹) := by
              apply Finset.prod_congr rfl
              intro i hi
              rw [← Real.rpow_mul (hv i hi)]
              unfold wn
              congr 1
      _ = (∏ i ∈ (Finset.univ : Finset (Option (Fin n))), v i ^ w i) ^
            ((E : ℝ)⁻¹) := by
              rw [Real.finset_prod_rpow]
              intro i hi
              exact Real.rpow_nonneg (hv i hi) _
      _ = u n x ^ ((E : ℝ)⁻¹) := by rw [hprod]
  have hgeomEq :
      (∏ i ∈ (Finset.univ : Finset (Option (Fin n))), v i ^ wn i) =
        ∑ i ∈ (Finset.univ : Finset (Option (Fin n))), wn i * v i := by
    rw [hprodNorm, hrootEq, hsumwnv]
  have hallv :=
    (Real.geom_mean_eq_arith_mean_weighted_iff'
      (Finset.univ : Finset (Option (Fin n))) wn v hwnpos hsumwn hv).mp hgeomEq
  funext i
  have hi := hallv (some i) (Finset.mem_univ _)
  rw [hsumwnv] at hi
  simpa only [v, p₀, hcoord] using hi

private lemma global_bound (n : ℕ) (hn : 0 < n)
    (x : Fin n → ℝ) (hx : x ∈ positiveOrthant n) :
    u n x ≤ u n (p₀ n) ∧
      (u n x = u n (p₀ n) → x = p₀ n) := by
  by_cases hslack : 0 ≤ 1 - weightedSum x
  · exact nonnegative_slack_bound n hn x hx hslack
  · have hslackNeg : 1 - weightedSum x < 0 := lt_of_not_ge hslack
    have hprodPos : 0 < ∏ i : Fin n, x i ^ (i.val + 1) :=
      Finset.prod_pos fun i _ => pow_pos (hx i) _
    have huNeg : u n x < 0 := by
      unfold u
      exact mul_neg_of_pos_of_neg hprodPos hslackNeg
    have hmaxPos : 0 < u n (p₀ n) := by
      rw [value_p₀ n]
      exact pow_pos (x₀_pos n) _
    refine ⟨le_of_lt (huNeg.trans hmaxPos), ?_⟩
    intro heq
    exfalso
    linarith

theorem gap9 (n : ℕ) (hn : 0 < n) :
    IsUniqueGlobalMaximizerOn n (p₀ n) := by
  refine ⟨p₀_positive n, ?_, ?_⟩
  · intro q hq
    exact (global_bound n hn q hq).1
  · intro q hq heq
    exact (global_bound n hn q hq).2 heq

theorem gap10 (n : ℕ) (hn : 0 < n) :
    u n (p₀ n) = (x₀ n) ^ (triangular n + 1) := by
  exact value_p₀ n

theorem gap11 (n : ℕ) (hn : 0 < n) :
    maximumPointsOn n = {p₀ n} := by
  ext p
  constructor
  · intro hp
    have hp' :
        p ∈ positiveOrthant n ∧
          ∀ q ∈ positiveOrthant n, u n q ≤ u n p := hp
    have hle := (global_bound n hn p hp'.1).1
    have hge := hp'.2 (p₀ n) (p₀_positive n)
    have heq : u n p = u n (p₀ n) := le_antisymm hle hge
    have hp0 := (global_bound n hn p hp'.1).2 heq
    simpa only [Set.mem_singleton_iff] using hp0
  · intro hp
    have hp0 : p = p₀ n := by
      simpa only [Set.mem_singleton_iff] using hp
    subst p
    exact ⟨p₀_positive n, fun q hq => (global_bound n hn q hq).1⟩

end

end ProofGap.Exercise3648
