import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise3668

noncomputable section

open scoped BigOperators

def objective {n : ℕ} (p : ℝ) (x : Fin n → ℝ) : ℝ :=
  ∑ i, Real.rpow |x i| p

def constraint {n : ℕ} (a : ℝ) : Set (Fin n → ℝ) :=
  {x | ∑ i, x i = a}

def positiveCritical {n : ℕ} (p a : ℝ)
    (x : Fin n → ℝ) (lambda : ℝ) : Prop :=
  (∀ i, 0 < x i ∧ p * Real.rpow (x i) (p - 1) + lambda = 0) ∧
    x ∈ constraint a

def candidate (n : ℕ) (a : ℝ) : Fin n → ℝ :=
  fun _ => a / (n : ℝ)

def secondVariation {n : ℕ} (p a : ℝ) (dx : Fin n → ℝ) : ℝ :=
  p * (p - 1) *
    ∑ i, Real.rpow (a / (n : ℝ)) (p - 2) * dx i ^ 2

def minimizers {n : ℕ} (p a : ℝ) : Set (Fin n → ℝ) :=
  {x | x ∈ constraint a ∧
    ∀ y : Fin n → ℝ, y ∈ constraint a → objective p x ≤ objective p y}

private theorem objective_candidate_le {n : ℕ} (hn : 0 < n)
    (p a : ℝ) (hp : 1 < p) (ha : 0 < a)
    (y : Fin n → ℝ) (hy : y ∈ constraint a) :
    objective p (candidate n a) ≤ objective p y := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hsum : ∑ i, y i = a := hy
  have habs : a ≤ ∑ i, |y i| := by
    calc
      a = |∑ i, y i| := by rw [hsum, abs_of_pos ha]
      _ ≤ ∑ i, |y i| := Finset.abs_sum_le_sum_abs _ _
  let w : Fin n → ℝ := fun _ => 1 / (n : ℝ)
  have hw0 : ∀ i ∈ (Finset.univ : Finset (Fin n)), 0 ≤ w i := by
    intro i _
    unfold w
    positivity
  have hw1 : ∑ i ∈ (Finset.univ : Finset (Fin n)), w i = 1 := by
    simp [w]
    field_simp [hnR.ne']
  have hz : ∀ i ∈ (Finset.univ : Finset (Fin n)), 0 ≤ |y i| := by
    intro i _
    exact abs_nonneg _
  have hJ := Real.rpow_arith_mean_le_arith_mean_rpow
    (Finset.univ : Finset (Fin n)) w (fun i => |y i|)
    hw0 hw1 hz hp.le
  have hleft :
      (∑ i, w i * |y i|) = (∑ i, |y i|) / (n : ℝ) := by
    simp only [w, one_div]
    rw [← Finset.mul_sum]
    ring
  have hright :
      (∑ i, w i * Real.rpow |y i| p) =
        objective p y / (n : ℝ) := by
    simp only [w, one_div, objective]
    rw [← Finset.mul_sum]
    ring
  have hJ' :
      Real.rpow ((∑ i, |y i|) / (n : ℝ)) p ≤
        objective p y / (n : ℝ) := by
    change
      Real.rpow (∑ i, w i * |y i|) p ≤
        ∑ i, w i * Real.rpow |y i| p at hJ
    rw [hleft, hright] at hJ
    exact hJ
  have hmean :
      a / (n : ℝ) ≤ (∑ i, |y i|) / (n : ℝ) :=
    div_le_div_of_nonneg_right habs hnR.le
  have hrpow :
      Real.rpow (a / (n : ℝ)) p ≤
        Real.rpow ((∑ i, |y i|) / (n : ℝ)) p := by
    simpa only [Real.rpow_eq_pow] using
      Real.rpow_le_rpow (div_nonneg ha.le hnR.le) hmean (by linarith)
  have hquot : 0 < a / (n : ℝ) := div_pos ha hnR
  calc
    objective p (candidate n a) =
        (n : ℝ) * Real.rpow (a / (n : ℝ)) p := by
      simp [objective, candidate, abs_of_pos hquot]
    _ ≤ (n : ℝ) *
        Real.rpow ((∑ i, |y i|) / (n : ℝ)) p :=
      mul_le_mul_of_nonneg_left hrpow hnR.le
    _ ≤ (n : ℝ) * (objective p y / (n : ℝ)) :=
      mul_le_mul_of_nonneg_left hJ' hnR.le
    _ = objective p y := by field_simp [hnR.ne']

theorem gap1 {n : ℕ} (hn : 0 < n) (p a lambda : ℝ)
    (hp : p > 1) (ha : a > 0) (x : Fin n → ℝ)
    (hcrit : positiveCritical p a x lambda) :
    ∀ i, x i = candidate n a i := by
  have hp0 : 0 < p := by linarith
  have hexp : p - 1 ≠ 0 := ne_of_gt (sub_pos.mpr hp)
  have hall : ∀ i j, x i = x j := by
    intro i j
    have hi := (hcrit.1 i).2
    have hj := (hcrit.1 j).2
    have hr :
        Real.rpow (x i) (p - 1) =
          Real.rpow (x j) (p - 1) := by
      have hm :
          p * Real.rpow (x i) (p - 1) =
            p * Real.rpow (x j) (p - 1) := by
        linarith
      exact mul_left_cancel₀ hp0.ne' hm
    exact (Real.rpow_left_inj
      (hcrit.1 i).1.le (hcrit.1 j).1.le hexp).mp hr
  have hsum : ∑ i, x i = a := hcrit.2
  intro i
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hnx : (n : ℝ) * x i = a := by
    calc
      (n : ℝ) * x i = ∑ j : Fin n, x i := by simp
      _ = ∑ j : Fin n, x j := by
        apply Finset.sum_congr rfl
        intro j _
        exact hall i j
      _ = a := hsum
  unfold candidate
  field_simp [hnR]
  simpa [mul_comm] using hnx

theorem gap2 {n : ℕ} (hn : 0 < n) (p a : ℝ)
    (hp : p > 1) (ha : a > 0) :
    {x | ∃ lambda, positiveCritical p a x lambda} =
      ({candidate n a} : Set (Fin n → ℝ)) := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨lambda, hcrit⟩
    funext i
    exact gap1 hn p a lambda hp ha x hcrit i
  · intro hx
    subst x
    let lambda :=
      -(p * Real.rpow (a / (n : ℝ)) (p - 1))
    refine ⟨lambda, ?_⟩
    constructor
    · intro i
      constructor
      · unfold candidate
        positivity
      · simp [candidate, lambda]
    · have hnR : (n : ℝ) ≠ 0 := by
        exact_mod_cast (Nat.ne_of_gt hn)
      unfold constraint candidate
      simp only [Set.mem_setOf_eq, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
      field_simp [hnR]

theorem gap3 {n : ℕ} (p a : ℝ) (dx : Fin n → ℝ) :
    secondVariation p a dx =
      p * (p - 1) *
        ∑ i, Real.rpow (a / (n : ℝ)) (p - 2) * dx i ^ 2 := rfl

theorem gap4 {n : ℕ} (hn : 0 < n) (p a : ℝ)
    (hp : p > 1) (ha : a > 0) (dx : Fin n → ℝ) (hdx : dx ≠ 0) :
    secondVariation p a dx > 0 := by
  have hbase : 0 < a / (n : ℝ) := by positivity
  have hrpow : 0 < Real.rpow (a / (n : ℝ)) (p - 2) :=
    Real.rpow_pos_of_pos hbase _
  have hex : ∃ i : Fin n, dx i ≠ 0 := by
    by_contra h
    push_neg at h
    apply hdx
    funext i
    exact h i
  have hsum :
      0 < ∑ i, Real.rpow (a / (n : ℝ)) (p - 2) * dx i ^ 2 := by
    apply Finset.sum_pos'
    · intro i _
      exact mul_nonneg hrpow.le (sq_nonneg _)
    · obtain ⟨i, hi⟩ := hex
      exact ⟨i, Finset.mem_univ i,
        mul_pos hrpow (sq_pos_of_ne_zero hi)⟩
  unfold secondVariation
  exact mul_pos (mul_pos (by linarith) (sub_pos.mpr hp)) hsum

theorem gap5 {n : ℕ} (hn : 0 < n) (p a : ℝ)
    (hp : p > 1) (ha : a > 0) :
    ∃ dx : Fin n → ℝ, secondVariation p a dx > 0 := by
  let dx : Fin n → ℝ := fun _ => 1
  have hdx : dx ≠ 0 := by
    intro h
    let i : Fin n := ⟨0, hn⟩
    have hi := congrFun h i
    simp [dx] at hi
  exact ⟨dx, gap4 hn p a hp ha dx hdx⟩

theorem gap6 {n : ℕ} (hn : 0 < n) (p a : ℝ)
    (hp : p > 1) (ha : a > 0) :
    minimizers p a = ({candidate n a} : Set (Fin n → ℝ)) := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hquot : 0 < a / (n : ℝ) := div_pos ha hnR
  have hcandMem : candidate n a ∈ constraint a := by
    unfold constraint candidate
    simp only [Set.mem_setOf_eq, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    field_simp [hnR.ne']
  have hcandObj :
      objective p (candidate n a) =
        (n : ℝ) * Real.rpow (a / (n : ℝ)) p := by
    simp [objective, candidate, abs_of_pos hquot]
  ext x
  simp only [Set.mem_singleton_iff]
  constructor
  · intro hx
    have hxmem : x ∈ constraint a := hx.1
    have hxle :
        objective p x ≤ objective p (candidate n a) :=
      hx.2 (candidate n a) hcandMem
    have hcx :
        objective p (candidate n a) ≤ objective p x :=
      objective_candidate_le hn p a hp ha x hxmem
    have hobj :
        objective p x = objective p (candidate n a) :=
      le_antisymm hxle hcx
    have hsum : ∑ i, x i = a := hxmem
    have habs : a ≤ ∑ i, |x i| := by
      calc
        a = |∑ i, x i| := by rw [hsum, abs_of_pos ha]
        _ ≤ ∑ i, |x i| := Finset.abs_sum_le_sum_abs _ _
    let w : Fin n → ℝ := fun _ => 1 / (n : ℝ)
    have hwpos :
        ∀ i ∈ (Finset.univ : Finset (Fin n)), 0 < w i := by
      intro i _
      unfold w
      positivity
    have hw1 : ∑ i ∈ (Finset.univ : Finset (Fin n)), w i = 1 := by
      simp [w]
      field_simp [hnR.ne']
    have hz :
        ∀ i ∈ (Finset.univ : Finset (Fin n)), 0 ≤ |x i| := by
      intro i _
      exact abs_nonneg _
    have hleft :
        (∑ i, w i * |x i|) = (∑ i, |x i|) / (n : ℝ) := by
      simp only [w, one_div]
      rw [← Finset.mul_sum]
      ring
    have hright :
        (∑ i, w i * Real.rpow |x i| p) =
          objective p x / (n : ℝ) := by
      simp only [w, one_div, objective]
      rw [← Finset.mul_sum]
      ring
    have hJraw := Real.rpow_arith_mean_le_arith_mean_rpow
      (Finset.univ : Finset (Fin n)) w (fun i => |x i|)
      (fun i hi => (hwpos i hi).le) hw1 hz hp.le
    have hJ :
        Real.rpow ((∑ i, |x i|) / (n : ℝ)) p ≤
          objective p x / (n : ℝ) := by
      change
        Real.rpow (∑ i, w i * |x i|) p ≤
          ∑ i, w i * Real.rpow |x i| p at hJraw
      rw [hleft, hright] at hJraw
      exact hJraw
    have hmean :
        a / (n : ℝ) ≤ (∑ i, |x i|) / (n : ℝ) :=
      div_le_div_of_nonneg_right habs hnR.le
    have hpow :
        Real.rpow (a / (n : ℝ)) p ≤
          Real.rpow ((∑ i, |x i|) / (n : ℝ)) p := by
      simpa only [Real.rpow_eq_pow] using
        Real.rpow_le_rpow (div_nonneg ha.le hnR.le) hmean (by linarith)
    have hobjNorm :
        objective p x / (n : ℝ) =
          Real.rpow (a / (n : ℝ)) p := by
      rw [hobj, hcandObj]
      field_simp [hnR.ne']
    have hJeq :
        Real.rpow ((∑ i, |x i|) / (n : ℝ)) p =
          objective p x / (n : ℝ) :=
      le_antisymm hJ (by rw [hobjNorm]; exact hpow)
    have hpoweq :
        Real.rpow (a / (n : ℝ)) p =
          Real.rpow ((∑ i, |x i|) / (n : ℝ)) p := by
      rw [hJeq, hobjNorm]
    have hmeanEq :
        a / (n : ℝ) = (∑ i, |x i|) / (n : ℝ) :=
      (Real.rpow_left_inj
        (div_nonneg ha.le hnR.le)
        (div_nonneg (Finset.sum_nonneg fun i _ => abs_nonneg _) hnR.le)
        (by linarith : p ≠ 0)).mp hpoweq
    have hrawEq :
        Real.rpow (∑ i, w i * |x i|) p =
          ∑ i, w i * Real.rpow |x i| p := by
      rw [hleft, hright]
      exact hJeq
    have hrawEq' :
        (∑ i, w i * |x i|) ^ p =
          ∑ i, w i * (|x i| ^ p) := by
      simpa only [Real.rpow_eq_pow] using hrawEq
    have habsCenter :
        ∀ i : Fin n, |x i| = ∑ j, w j * |x j| := by
      have heqcase :=
        ((strictConvexOn_rpow hp).map_sum_eq_iff
          hwpos hw1 hz).mp hrawEq'
      intro i
      exact heqcase i (Finset.mem_univ i)
    have habsi : ∀ i : Fin n, |x i| = a / (n : ℝ) := by
      intro i
      calc
        |x i| = ∑ j, w j * |x j| := habsCenter i
        _ = (∑ j, |x j|) / (n : ℝ) := hleft
        _ = a / (n : ℝ) := hmeanEq.symm
    have hsumAbs : ∑ i, |x i| = a := by
      calc
        ∑ i, |x i| = ∑ i : Fin n, a / (n : ℝ) := by
          apply Finset.sum_congr rfl
          intro i _
          exact habsi i
        _ = a := by
          simp only [Finset.sum_const, Finset.card_univ,
            Fintype.card_fin, nsmul_eq_mul]
          field_simp [hnR.ne']
    funext i
    have hxi : 0 ≤ x i := by
      by_contra hneg
      have hlt : x i < |x i| := by
        rw [abs_of_neg (lt_of_not_ge hneg)]
        linarith
      have hsumlt : (∑ j, x j) < ∑ j, |x j| := by
        apply Finset.sum_lt_sum
        · intro j _
          exact le_abs_self (x j)
        · exact ⟨i, Finset.mem_univ i, hlt⟩
      rw [hsum, hsumAbs] at hsumlt
      exact (lt_irrefl a) hsumlt
    unfold candidate
    rw [← habsi i, abs_of_nonneg hxi]
  · intro hx
    subst x
    exact ⟨hcandMem, fun y hy =>
      objective_candidate_le hn p a hp ha y hy⟩

theorem gap7 {n : ℕ} (hn : 0 < n) (p a : ℝ)
    (hp : p > 1) (ha : a > 0) :
    objective p (candidate n a) =
      Real.rpow a p / Real.rpow (n : ℝ) (p - 1) := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hquot : 0 < a / (n : ℝ) := div_pos ha hnR
  calc
    objective p (candidate n a) =
        (n : ℝ) * Real.rpow (a / (n : ℝ)) p := by
      simp [objective, candidate, abs_of_pos hquot]
    _ = (n : ℝ) *
        (Real.rpow a p / Real.rpow (n : ℝ) p) := by
      rw [show Real.rpow (a / (n : ℝ)) p =
        Real.rpow a p / Real.rpow (n : ℝ) p by
          simpa only [Real.rpow_eq_pow] using
            (Real.div_rpow ha.le hnR.le p)]
    _ = Real.rpow a p / Real.rpow (n : ℝ) (p - 1) := by
      rw [show Real.rpow (n : ℝ) (p - 1) =
        Real.rpow (n : ℝ) p / (n : ℝ) by
          simpa only [Real.rpow_eq_pow, Real.rpow_one] using
            (Real.rpow_sub hnR p 1)]
      field_simp [(Real.rpow_pos_of_pos hnR p).ne', hnR.ne']

theorem gap8 {n : ℕ} (hn : 0 < n) (a : ℝ) (ha : a > 0) :
    ∀ i, candidate n a i > 0 := by
  intro i
  unfold candidate
  positivity

end

end ProofGap.Exercise3668
