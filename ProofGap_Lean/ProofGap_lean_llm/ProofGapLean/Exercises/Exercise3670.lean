import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

namespace ProofGap.Exercise3670

noncomputable section

open scoped BigOperators

def objective {n : ℕ} (alpha x : Fin n → ℝ) : ℝ :=
  ∏ i, Real.rpow (x i) (alpha i)

def constraint {n : ℕ} (a : ℝ) : Set (Fin n → ℝ) :=
  {x | (∀ i, 0 < x i) ∧ ∑ i, x i = a}

def logObjective {n : ℕ} (alpha x : Fin n → ℝ) : ℝ :=
  Real.log (objective alpha x)

def lagrangian {n : ℕ}
    (alpha : Fin n → ℝ) (a lambda : ℝ) (x : Fin n → ℝ) : ℝ :=
  logObjective alpha x - 1 / lambda * (∑ i, x i - a)

def critical {n : ℕ}
    (alpha : Fin n → ℝ) (a : ℝ) (x : Fin n → ℝ) (lambda : ℝ) : Prop :=
  (∀ i, alpha i / x i - 1 / lambda = 0) ∧ x ∈ constraint a

def exponentSum {n : ℕ} (alpha : Fin n → ℝ) : ℝ :=
  ∑ i, alpha i

def candidate {n : ℕ} (alpha : Fin n → ℝ) (a : ℝ) : Fin n → ℝ :=
  fun i => a * alpha i / exponentSum alpha

def logSecondVariation {n : ℕ}
    (alpha x dx : Fin n → ℝ) : ℝ :=
  -(∑ i, alpha i / x i ^ 2 * dx i ^ 2)

def maximizers {n : ℕ}
    (alpha : Fin n → ℝ) (a : ℝ) : Set (Fin n → ℝ) :=
  {x | x ∈ constraint a ∧
    ∀ y ∈ constraint a, objective alpha y ≤ objective alpha x}

private theorem log_prod_rpow_aux {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (p z : ι → ℝ) (hz : ∀ i, 0 < z i) :
    Real.log (s.prod (fun i => Real.rpow (z i) (p i))) =
      s.sum (fun i => p i * Real.log (z i)) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
      rw [Finset.prod_insert hi, Finset.sum_insert hi]
      have hzi : 0 < Real.rpow (z i) (p i) :=
        Real.rpow_pos_of_pos (hz i) (p i)
      have hs : 0 < s.prod (fun j => Real.rpow (z j) (p j)) :=
        Finset.prod_pos (fun j _ => Real.rpow_pos_of_pos (hz j) (p j))
      have hlogi :
          Real.log (Real.rpow (z i) (p i)) = p i * Real.log (z i) := by
        change Real.log ((z i) ^ (p i : ℝ)) = p i * Real.log (z i)
        exact Real.log_rpow (hz i) (p i)
      calc
        Real.log
            (Real.rpow (z i) (p i) *
              s.prod (fun j => Real.rpow (z j) (p j))) =
            Real.log (Real.rpow (z i) (p i)) +
              Real.log (s.prod (fun j => Real.rpow (z j) (p j))) := by
          exact Real.log_mul (ne_of_gt hzi) (ne_of_gt hs)
        _ = p i * Real.log (z i) +
              s.sum (fun j => p j * Real.log (z j)) := by
          rw [hlogi, ih]

private theorem prod_rpow_const_aux {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (c : ℝ) (hc : 0 < c) (p : ι → ℝ) :
    s.prod (fun i => Real.rpow c (p i)) = Real.rpow c (s.sum p) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
      rw [Finset.prod_insert hi, Finset.sum_insert hi, ih]
      exact (Real.rpow_add hc (p i) (s.sum p)).symm

private theorem candidateFacts {n : ℕ} (hn : 0 < n)
    (alpha : Fin n → ℝ) (a : ℝ) (halpha : ∀ i, alpha i > 1) (ha : a > 0) :
    0 < exponentSum alpha ∧
      candidate alpha a ∈ constraint a ∧
      ∀ y ∈ constraint a, y ≠ candidate alpha a →
        objective alpha y < objective alpha (candidate alpha a) := by
  classical
  have hS : 0 < exponentSum alpha := by
    unfold exponentSum
    apply Finset.sum_pos'
    · intro i _
      exact le_of_lt (lt_trans zero_lt_one (halpha i))
    · let i : Fin n := ⟨0, hn⟩
      exact ⟨i, Finset.mem_univ i, lt_trans zero_lt_one (halpha i)⟩
  have hcpos : ∀ i, 0 < candidate alpha a i := by
    intro i
    unfold candidate
    exact div_pos (mul_pos ha (lt_trans zero_lt_one (halpha i))) hS
  have hcand : candidate alpha a ∈ constraint a := by
    change (∀ i, 0 < candidate alpha a i) ∧
      ∑ i, candidate alpha a i = a
    refine ⟨hcpos, ?_⟩
    calc
      (∑ i, candidate alpha a i) =
          a / exponentSum alpha * ∑ i, alpha i := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        unfold candidate
        ring
      _ = a := by
        unfold exponentSum
        exact div_mul_cancel₀ a (ne_of_gt hS)
  refine ⟨hS, hcand, ?_⟩
  intro y hy hne
  rcases hy with ⟨hypos, hysum⟩
  have hratio_pos : ∀ i, 0 < y i / candidate alpha a i := by
    intro i
    exact div_pos (hypos i) (hcpos i)
  have hex : ∃ i, y i / candidate alpha a i ≠ 1 := by
    by_contra h
    apply hne
    funext i
    by_contra hi
    apply h
    refine ⟨i, ?_⟩
    intro hratio
    apply hi
    field_simp [ne_of_gt (hcpos i)] at hratio
    exact hratio
  have hle : ∀ i,
      alpha i * Real.log (y i) -
          alpha i * Real.log (candidate alpha a i) ≤
        exponentSum alpha / a * y i - alpha i := by
    intro i
    have hai : 0 < alpha i := lt_trans zero_lt_one (halpha i)
    calc
      alpha i * Real.log (y i) -
          alpha i * Real.log (candidate alpha a i) =
          alpha i * Real.log (y i / candidate alpha a i) := by
        rw [Real.log_div (ne_of_gt (hypos i)) (ne_of_gt (hcpos i))]
        ring
      _ ≤ alpha i * (y i / candidate alpha a i - 1) :=
        mul_le_mul_of_nonneg_left
          (Real.log_le_sub_one_of_pos (hratio_pos i)) (le_of_lt hai)
      _ = exponentSum alpha / a * y i - alpha i := by
        unfold candidate
        field_simp [ne_of_gt ha, ne_of_gt hS, ne_of_gt hai] <;> ring
  rcases hex with ⟨i, hi⟩
  have hlt :
      alpha i * Real.log (y i) -
          alpha i * Real.log (candidate alpha a i) <
        exponentSum alpha / a * y i - alpha i := by
    have hai : 0 < alpha i := lt_trans zero_lt_one (halpha i)
    calc
      alpha i * Real.log (y i) -
          alpha i * Real.log (candidate alpha a i) =
          alpha i * Real.log (y i / candidate alpha a i) := by
        rw [Real.log_div (ne_of_gt (hypos i)) (ne_of_gt (hcpos i))]
        ring
      _ < alpha i * (y i / candidate alpha a i - 1) :=
        mul_lt_mul_of_pos_left
          (Real.log_lt_sub_one_of_pos (hratio_pos i) hi) hai
      _ = exponentSum alpha / a * y i - alpha i := by
        unfold candidate
        field_simp [ne_of_gt ha, ne_of_gt hS, ne_of_gt hai] <;> ring
  have hsumlt :
      (∑ i, (alpha i * Real.log (y i) -
        alpha i * Real.log (candidate alpha a i))) <
      ∑ i, (exponentSum alpha / a * y i - alpha i) := by
    apply Finset.sum_lt_sum
    · intro j _
      exact hle j
    · exact ⟨i, Finset.mem_univ i, hlt⟩
  have hrhs :
      (∑ i, (exponentSum alpha / a * y i - alpha i)) = 0 := by
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hysum]
    change exponentSum alpha / a * a - exponentSum alpha = 0
    apply sub_eq_zero.mpr
    exact div_mul_cancel₀ (exponentSum alpha) (ne_of_gt ha)
  have hlogobj (z : Fin n → ℝ) (hz : ∀ i, 0 < z i) :
      Real.log (objective alpha z) =
        ∑ i, alpha i * Real.log (z i) := by
    unfold objective
    exact log_prod_rpow_aux Finset.univ alpha z hz
  have hloglt :
      Real.log (objective alpha y) <
        Real.log (objective alpha (candidate alpha a)) := by
    rw [hlogobj y hypos, hlogobj (candidate alpha a) hcpos]
    rw [Finset.sum_sub_distrib] at hsumlt
    rw [hrhs] at hsumlt
    linarith
  have hyobj : 0 < objective alpha y := by
    unfold objective
    exact Finset.prod_pos
      (fun i _ => Real.rpow_pos_of_pos (hypos i) (alpha i))
  have hcobj : 0 < objective alpha (candidate alpha a) := by
    unfold objective
    exact Finset.prod_pos
      (fun i _ => Real.rpow_pos_of_pos (hcpos i) (alpha i))
  calc
    objective alpha y = Real.exp (Real.log (objective alpha y)) :=
      (Real.exp_log hyobj).symm
    _ < Real.exp (Real.log (objective alpha (candidate alpha a))) :=
      Real.exp_lt_exp.mpr hloglt
    _ = objective alpha (candidate alpha a) := Real.exp_log hcobj

theorem gap1 {n : ℕ} (alpha x : Fin n → ℝ) (a lambda : ℝ)
    (hx : x ∈ constraint a) :
    lagrangian alpha a lambda x =
      (∑ i, (alpha i * Real.log (x i) - x i / lambda)) +
        a / lambda := by
  rcases hx with ⟨hxpos, hxsum⟩
  have hdiv : (∑ i, x i / lambda) = a / lambda := by
    simp_rw [div_eq_mul_inv]
    rw [← Finset.sum_mul, hxsum]
  unfold lagrangian logObjective objective
  rw [log_prod_rpow_aux Finset.univ alpha x hxpos]
  rw [hxsum, Finset.sum_sub_distrib, hdiv]
  ring

theorem gap2 {n : ℕ} (hn : 0 < n) (alpha x : Fin n → ℝ)
    (a lambda : ℝ) (halpha : ∀ i, alpha i > 1) (ha : a > 0)
    (hcrit : critical alpha a x lambda) :
    ∀ i, x i = candidate alpha a i := by
  rcases hcrit with ⟨hstation, hxpos, hxsum⟩
  have hfacts := candidateFacts hn alpha a halpha ha
  have hS : 0 < exponentSum alpha := hfacts.1
  let i0 : Fin n := ⟨0, hn⟩
  have hrecip : 0 < 1 / lambda := by
    have hq : 0 < alpha i0 / x i0 :=
      div_pos (lt_trans zero_lt_one (halpha i0)) (hxpos i0)
    linarith [hstation i0]
  have hlambda : 0 < lambda := one_div_pos.mp hrecip
  have hrel : ∀ i, alpha i * lambda = x i := by
    intro i
    have heq : alpha i / x i = 1 / lambda := sub_eq_zero.mp (hstation i)
    have hcross :=
      (div_eq_div_iff (ne_of_gt (hxpos i)) (ne_of_gt hlambda)).mp heq
    simpa using hcross
  have hsumrel : exponentSum alpha * lambda = a := by
    calc
      exponentSum alpha * lambda = ∑ i, alpha i * lambda := by
        unfold exponentSum
        rw [Finset.sum_mul]
      _ = ∑ i, x i := Finset.sum_congr rfl (fun i _ => hrel i)
      _ = a := hxsum
  intro i
  calc
    x i = alpha i * lambda := (hrel i).symm
    _ = a * alpha i / exponentSum alpha := by
      field_simp [ne_of_gt hS]
      rw [← hsumrel]
      ring
    _ = candidate alpha a i := by rfl

theorem gap3 {n : ℕ} (hn : 0 < n) (alpha : Fin n → ℝ) (a : ℝ)
    (halpha : ∀ i, alpha i > 1) (ha : a > 0) :
    {x | ∃ lambda, critical alpha a x lambda} =
      ({candidate alpha a} : Set (Fin n → ℝ)) := by
  ext x
  constructor
  · rintro ⟨lambda, hcrit⟩
    have hx : x = candidate alpha a := by
      funext i
      exact gap2 hn alpha x a lambda halpha ha hcrit i
    simpa only [Set.mem_singleton_iff] using hx
  · intro hx
    have hx' : x = candidate alpha a := by
      simpa only [Set.mem_singleton_iff] using hx
    subst x
    have hfacts := candidateFacts hn alpha a halpha ha
    have hS : 0 < exponentSum alpha := hfacts.1
    refine ⟨a / exponentSum alpha, ?_⟩
    constructor
    · intro i
      have hai : 0 < alpha i := lt_trans zero_lt_one (halpha i)
      change alpha i / (a * alpha i / exponentSum alpha) -
          1 / (a / exponentSum alpha) = 0
      field_simp [ne_of_gt ha, ne_of_gt hS, ne_of_gt hai] <;> ring
    · exact hfacts.2.1

theorem gap4 {n : ℕ} (alpha x dx : Fin n → ℝ) :
    logSecondVariation alpha x dx =
      -(∑ i, alpha i / x i ^ 2 * dx i ^ 2) := by
  rfl

theorem gap5 {n : ℕ} (alpha x dx : Fin n → ℝ)
    (halpha : ∀ i, alpha i > 1) (hx : ∀ i, 0 < x i)
    (hdx : dx ≠ 0) :
    -(∑ i, alpha i / x i ^ 2 * dx i ^ 2) < 0 := by
  have hnonneg : ∀ i, 0 ≤ alpha i / x i ^ 2 * dx i ^ 2 := by
    intro i
    exact mul_nonneg
      (div_nonneg (le_of_lt (lt_trans zero_lt_one (halpha i))) (sq_nonneg (x i)))
      (sq_nonneg (dx i))
  have hex : ∃ i, dx i ≠ 0 := by
    by_contra h
    apply hdx
    funext i
    by_contra hi
    apply h
    exact ⟨i, hi⟩
  rcases hex with ⟨i, hi⟩
  have hstrict : 0 < alpha i / x i ^ 2 * dx i ^ 2 := by
    have hai : 0 < alpha i := lt_trans zero_lt_one (halpha i)
    have hxisq : 0 < x i ^ 2 := pow_pos (hx i) 2
    have hdxsq : 0 < dx i ^ 2 := by
      simpa [pow_two] using (mul_self_pos.mpr hi)
    exact mul_pos (div_pos hai hxisq) hdxsq
  have hsum : 0 < ∑ i, alpha i / x i ^ 2 * dx i ^ 2 := by
    apply Finset.sum_pos'
    · intro j _
      exact hnonneg j
    · exact ⟨i, Finset.mem_univ i, hstrict⟩
  exact neg_lt_zero.mpr hsum

theorem gap6 {n : ℕ} (alpha x dx : Fin n → ℝ)
    (halpha : ∀ i, alpha i > 1) (hx : ∀ i, 0 < x i)
    (hdx : dx ≠ 0) :
    logSecondVariation alpha x dx < 0 := by
  rw [gap4]
  exact gap5 alpha x dx halpha hx hdx

theorem gap7 {n : ℕ} (hn : 0 < n) (alpha : Fin n → ℝ) (a : ℝ)
    (halpha : ∀ i, alpha i > 1) (ha : a > 0) :
    maximizers alpha a =
      ({candidate alpha a} : Set (Fin n → ℝ)) := by
  ext x
  constructor
  · intro hx
    have hfacts := candidateFacts hn alpha a halpha ha
    have hcand := hfacts.2.1
    have hstrict := hfacts.2.2
    have heq : x = candidate alpha a := by
      by_contra hne
      have hlt := hstrict x hx.1 hne
      have hge := hx.2 (candidate alpha a) hcand
      linarith
    simpa only [Set.mem_singleton_iff] using heq
  · intro hx
    have hx' : x = candidate alpha a := by
      simpa only [Set.mem_singleton_iff] using hx
    subst x
    have hfacts := candidateFacts hn alpha a halpha ha
    refine ⟨hfacts.2.1, ?_⟩
    intro y hy
    by_cases heq : y = candidate alpha a
    · subst y
      exact le_rfl
    · exact (hfacts.2.2 y hy heq).le

theorem gap8 {n : ℕ} (hn : 0 < n) (alpha : Fin n → ℝ) (a : ℝ)
    (halpha : ∀ i, alpha i > 1) (ha : a > 0) :
    objective alpha (candidate alpha a) =
      Real.rpow (a / exponentSum alpha) (exponentSum alpha) *
        ∏ i, Real.rpow (alpha i) (alpha i) := by
  classical
  have hfacts := candidateFacts hn alpha a halpha ha
  have hS : 0 < exponentSum alpha := hfacts.1
  have hc : 0 < a / exponentSum alpha := div_pos ha hS
  unfold objective candidate
  calc
    (∏ i, Real.rpow (a * alpha i / exponentSum alpha) (alpha i)) =
        ∏ i, Real.rpow ((a / exponentSum alpha) * alpha i) (alpha i) := by
      apply Finset.prod_congr rfl
      intro i _
      congr 1
      ring
    _ = ∏ i, (Real.rpow (a / exponentSum alpha) (alpha i) *
        Real.rpow (alpha i) (alpha i)) := by
      apply Finset.prod_congr rfl
      intro i _
      have hai : 0 < alpha i := lt_trans zero_lt_one (halpha i)
      exact Real.mul_rpow (le_of_lt hc) (le_of_lt hai)
    _ = (∏ i, Real.rpow (a / exponentSum alpha) (alpha i)) *
        ∏ i, Real.rpow (alpha i) (alpha i) := by
      rw [Finset.prod_mul_distrib]
    _ = Real.rpow (a / exponentSum alpha) (exponentSum alpha) *
        ∏ i, Real.rpow (alpha i) (alpha i) := by
      rw [prod_rpow_const_aux Finset.univ (a / exponentSum alpha) hc alpha]
      rfl

end

end ProofGap.Exercise3670
