import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace ProofGap.Exercise3649

open scoped BigOperators

noncomputable section

def dim (m : ℕ) : ℕ :=
  m + 1

def positiveOrthant (m : ℕ) : Set (Fin (m + 1) → ℝ) :=
  {x | ∀ i, 0 < x i}

def yCoord (m : ℕ) (x : Fin (m + 1) → ℝ) : Fin (m + 1) → ℝ :=
  Fin.cases (x 0) (fun i => x i.succ / x i.castSucc)

def productY (m : ℕ) (x : Fin (m + 1) → ℝ) : ℝ :=
  ∏ i, yCoord m x i

def u (m : ℕ) (x : Fin (m + 1) → ℝ) : ℝ :=
  x 0 + (∑ i : Fin m, x i.succ / x i.castSucc) +
    2 / x (Fin.last m)

def transformedU (m : ℕ) (y : Fin (m + 1) → ℝ) : ℝ :=
  (∑ i, y i) + 2 / ∏ i, y i

def partialY (m : ℕ) (y : Fin (m + 1) → ℝ)
    (i : Fin (m + 1)) : ℝ :=
  deriv (fun t => transformedU m (Function.update y i t)) (y i)

def StationaryY (m : ℕ) (y : Fin (m + 1) → ℝ) : Prop :=
  ∀ i, partialY m y i = 0

def root (m : ℕ) : ℝ :=
  Real.rpow 2 (1 / ((m + 2 : ℕ) : ℝ))

def yStar (m : ℕ) : Fin (m + 1) → ℝ :=
  fun _ => root m

def xStar (m : ℕ) : Fin (m + 1) → ℝ :=
  fun i => Real.rpow 2
    (((i.val + 1 : ℕ) : ℝ) / ((m + 2 : ℕ) : ℝ))

def secondVariationAtYStar
    (m : ℕ) (v : Fin (m + 1) → ℝ) : ℝ :=
  1 / root m * ((∑ i, (v i) ^ 2) + (∑ i, v i) ^ 2)

def PositiveDefiniteAtYStar (m : ℕ) : Prop :=
  ∀ v : Fin (m + 1) → ℝ, v ≠ 0 →
    0 < secondVariationAtYStar m v

def IsUniqueGlobalMinimizerOn
    (m : ℕ) (p : Fin (m + 1) → ℝ) : Prop :=
  p ∈ positiveOrthant m ∧
    (∀ q ∈ positiveOrthant m, u m p ≤ u m q) ∧
    (∀ q ∈ positiveOrthant m, u m q = u m p → q = p)

def minimumPointsOn (m : ℕ) : Set (Fin (m + 1) → ℝ) :=
  {p | p ∈ positiveOrthant m ∧
    ∀ q ∈ positiveOrthant m, u m p ≤ u m q}

private theorem root_pos (m : ℕ) : 0 < root m := by
  unfold root
  exact Real.rpow_pos_of_pos (by norm_num) _

private theorem root_pow (m : ℕ) :
    root m ^ (m + 2) = 2 := by
  let n : ℕ := m + 2
  have hn : (0 : ℝ) < (n : ℝ) := by
    dsimp [n]
    positivity
  calc
    root m ^ (m + 2) =
        Real.rpow (Real.rpow 2 (1 / (n : ℝ))) (n : ℝ) := by
          simpa only [root, n] using
            (Real.rpow_natCast (root m) (m + 2)).symm
    _ = Real.rpow 2 ((1 / (n : ℝ)) * (n : ℝ)) :=
      (Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2) _ _).symm
    _ = Real.rpow 2 1 := by
      rw [show (1 / (n : ℝ)) * (n : ℝ) = 1 by field_simp]
    _ = 2 := Real.rpow_one 2

theorem gap1 (m : ℕ) :
    ∀ x ∈ positiveOrthant m, productY m x = x (Fin.last m) := by
  intro x hx
  unfold productY
  rw [Fin.prod_univ_succ]
  simp only [yCoord, Fin.cases_zero, Fin.cases_succ]
  rw [Finset.prod_div_distrib]
  have hden : (∏ i : Fin m, x i.castSucc) ≠ 0 := by
    exact Finset.prod_ne_zero_iff.mpr
      (fun i hi => ne_of_gt (hx i.castSucc))
  field_simp [hden]
  calc
    x 0 * ∏ i : Fin m, x i.succ =
        ∏ i : Fin (m + 1), x i := (Fin.prod_univ_succ x).symm
    _ = (∏ i : Fin m, x i.castSucc) * x (Fin.last m) :=
      Fin.prod_univ_castSucc x

theorem gap2 (m : ℕ) :
    ∀ x ∈ positiveOrthant m,
      u m x = transformedU m (yCoord m x) := by
  intro x hx
  unfold u transformedU
  rw [show (∏ i, yCoord m x i) = x (Fin.last m) by
    exact gap1 m x hx]
  rw [Fin.sum_univ_succ]
  simp only [yCoord, Fin.cases_zero, Fin.cases_succ]

private theorem sum_update
    (m : ℕ) (y : Fin (m + 1) → ℝ) (i : Fin (m + 1)) (t : ℝ) :
    ∑ j, Function.update y i t j = t +
      ∑ j ∈ Finset.univ.erase i, y j := by
  rw [← Finset.add_sum_erase (s := Finset.univ)
    (f := Function.update y i t) (Finset.mem_univ i)]
  simp only [Function.update_self]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]

private theorem prod_update
    (m : ℕ) (y : Fin (m + 1) → ℝ) (i : Fin (m + 1)) (t : ℝ) :
    ∏ j, Function.update y i t j = t *
      ∏ j ∈ Finset.univ.erase i, y j := by
  rw [← Finset.mul_prod_erase (s := Finset.univ)
    (f := Function.update y i t) (Finset.mem_univ i)]
  simp only [Function.update_self]
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]

private theorem partialY_formula_of_ne
    (m : ℕ) (y : Fin (m + 1) → ℝ)
    (hy : ∀ i, y i ≠ 0) (i : Fin (m + 1)) :
    partialY m y i =
      1 - 2 / ((∏ j, y j) * y i) := by
  let P : ℝ := ∏ j ∈ Finset.univ.erase i, y j
  let S : ℝ := ∑ j ∈ Finset.univ.erase i, y j
  have hP : P ≠ 0 := by
    dsimp [P]
    exact Finset.prod_ne_zero_iff.mpr (fun j hj => hy j)
  have hyi : y i ≠ 0 := hy i
  have hprod : (∏ j, y j) = y i * P := by
    rw [← Finset.mul_prod_erase (s := Finset.univ) (f := y)
      (Finset.mem_univ i)]
  have heq :
      (fun t => transformedU m (Function.update y i t)) =
        (fun t => t + S + 2 / (t * P)) := by
    funext t
    unfold transformedU
    rw [sum_update m y i t, prod_update m y i t]
  have hlin :
      HasDerivAt (fun t : ℝ => t + S) 1 (y i) := by
    convert (hasDerivAt_id (y i)).add_const S using 1 <;> norm_num
  have hden :
      HasDerivAt (fun t : ℝ => t * P) P (y i) := by
    convert (hasDerivAt_id (y i)).mul_const P using 1 <;> ring
  have hinv :=
    (hden.inv (mul_ne_zero hyi hP)).const_mul 2
  have hder := hlin.add hinv
  have hder' :
      HasDerivAt (fun t : ℝ => t + S + 2 / (t * P))
        (1 + 2 * (-P / (y i * P) ^ 2)) (y i) := by
    convert hder using 1 <;> simp [div_eq_mul_inv]
  unfold partialY
  rw [heq, hder'.deriv, hprod]
  field_simp [hyi, hP]
  ring

theorem gap3 (m : ℕ) :
    ∀ y : Fin (m + 1) → ℝ, (∀ i, 0 < y i) →
      ∀ i,
        partialY m y i =
          1 - 2 / ((∏ j, y j) * y i) := by
  intro y hy i
  exact partialY_formula_of_ne m y (fun j => ne_of_gt (hy j)) i

private theorem partialY_eq_one_of_other_zero
    (m : ℕ) (y : Fin (m + 1) → ℝ)
    (i j : Fin (m + 1)) (hij : i ≠ j) (hj : y j = 0) :
    partialY m y i = 1 := by
  let P : ℝ := ∏ k ∈ Finset.univ.erase i, y k
  let S : ℝ := ∑ k ∈ Finset.univ.erase i, y k
  have hjmem : j ∈ (Finset.univ.erase i : Finset (Fin (m + 1))) :=
    Finset.mem_erase.mpr ⟨Ne.symm hij, Finset.mem_univ j⟩
  have hP : P = 0 := by
    dsimp [P]
    exact Finset.prod_eq_zero hjmem hj
  have heq :
      (fun t => transformedU m (Function.update y i t)) =
        (fun t => t + S) := by
    funext t
    unfold transformedU
    rw [sum_update m y i t, prod_update m y i t]
    change (∏ k ∈ Finset.univ.erase i, y k) = 0 at hP
    rw [hP]
    simp [S]
  unfold partialY
  rw [heq]
  convert ((hasDerivAt_id (y i)).add_const S).deriv using 1 <;> norm_num

private theorem stationary_coordinates_ne_zero
    (m : ℕ) (hm : 0 < m) (y : Fin (m + 1) → ℝ)
    (hs : StationaryY m y) :
    ∀ j, y j ≠ 0 := by
  intro j hj
  let one : Fin (m + 1) := ⟨1, Nat.succ_lt_succ hm⟩
  by_cases hj0 : j = 0
  · have hone : one ≠ j := by
      rw [hj0]
      simp [one]
    have hp := partialY_eq_one_of_other_zero m y one j hone hj
    have hsone := hs one
    linarith
  · have hzero : (0 : Fin (m + 1)) ≠ j := by
      intro h
      exact hj0 h.symm
    have hp := partialY_eq_one_of_other_zero m y 0 j hzero hj
    have hszero := hs 0
    linarith

private theorem stationary_all_equal
    (m : ℕ) (y : Fin (m + 1) → ℝ) (hs : StationaryY m y) :
    ∀ i, y i = y (Fin.last m) := by
  by_cases hm : m = 0
  · subst m
    intro i
    have hi : i = 0 := Fin.eq_zero i
    have hl : (Fin.last 0 : Fin 1) = 0 := Fin.eq_zero _
    rw [hi, hl]
  · have hmpos : 0 < m := Nat.pos_of_ne_zero hm
    have hyne := stationary_coordinates_ne_zero m hmpos y hs
    have hP : (∏ j, y j) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr (fun j hj => hyne j)
    intro i
    have hi := hs i
    have hl := hs (Fin.last m)
    rw [partialY_formula_of_ne m y hyne i] at hi
    rw [partialY_formula_of_ne m y hyne (Fin.last m)] at hl
    have hdi : (∏ j, y j) * y i ≠ 0 :=
      mul_ne_zero hP (hyne i)
    have hdl : (∏ j, y j) * y (Fin.last m) ≠ 0 :=
      mul_ne_zero hP (hyne (Fin.last m))
    have hiDiv : 2 / ((∏ j, y j) * y i) = 1 := by linarith
    have hlDiv : 2 / ((∏ j, y j) * y (Fin.last m)) = 1 := by linarith
    have hiMul : (∏ j, y j) * y i = 2 := by
      have := (div_eq_iff hdi).mp hiDiv
      linarith
    have hlMul : (∏ j, y j) * y (Fin.last m) = 2 := by
      have := (div_eq_iff hdl).mp hlDiv
      linarith
    exact mul_left_cancel₀ hP (hiMul.trans hlMul.symm)

theorem gap4 (m : ℕ) (hm : 0 < m) :
    ∀ y : Fin (m + 1) → ℝ, StationaryY m y →
      y 0 = y ⟨1, Nat.succ_lt_succ hm⟩ := by
  intro y hs
  have hall := stationary_all_equal m y hs
  exact (hall 0).trans (hall ⟨1, Nat.succ_lt_succ hm⟩).symm

theorem gap5 (m : ℕ) :
    ∀ y : Fin (m + 1) → ℝ, StationaryY m y →
      ∀ i, y i = y (Fin.last m) := by
  intro y hs
  exact stationary_all_equal m y hs

theorem gap6 (m : ℕ) :
    ∀ y : Fin (m + 1) → ℝ, (∀ i, 0 < y i) →
      StationaryY m y → y (Fin.last m) = root m := by
  intro y hy hs
  let r : ℝ := y (Fin.last m)
  have hr : 0 < r := hy (Fin.last m)
  have hall := stationary_all_equal m y hs
  have hprod : (∏ i, y i) = r ^ (m + 1) := by
    simp_rw [hall]
    simp [r]
  have hstat := hs (Fin.last m)
  rw [gap3 m y hy (Fin.last m), hprod] at hstat
  have hden : r ^ (m + 1) * r ≠ 0 := by positivity
  have hdiv : 2 / (r ^ (m + 1) * r) = 1 := by linarith
  have hpow : r ^ (m + 2) = 2 := by
    have hmul := (div_eq_iff hden).mp hdiv
    rw [show r ^ (m + 2) = r ^ (m + 1) * r by
      simpa [pow_succ, mul_comm] using (pow_succ r (m + 1))] 
    linarith
  have hn : (m + 2 : ℕ) ≠ 0 := by omega
  calc
    y (Fin.last m) = r := rfl
    _ = Real.rpow (r ^ (m + 2)) (((m + 2 : ℕ) : ℝ)⁻¹) :=
      (Real.pow_rpow_inv_natCast hr.le hn).symm
    _ = Real.rpow 2 (((m + 2 : ℕ) : ℝ)⁻¹) := by rw [hpow]
    _ = root m := by
      unfold root
      congr 1
      field_simp

theorem gap7 (m : ℕ) :
    ∀ y : Fin (m + 1) → ℝ, (∀ i, 0 < y i) →
      StationaryY m y → y 0 = root m := by
  intro y hy hs
  rw [stationary_all_equal m y hs 0]
  exact gap6 m y hy hs

theorem gap8 (m : ℕ) :
    StationaryY m (yStar m) := by
  intro i
  have hypos : ∀ j : Fin (m + 1), 0 < yStar m j :=
    fun j => root_pos m
  rw [gap3 m (yStar m) hypos i]
  have hprod :
      (∏ j : Fin (m + 1), yStar m j) = root m ^ (m + 1) := by
    simp [yStar]
  rw [hprod]
  simp only [yStar]
  have hden : root m ^ (m + 1) * root m = 2 := by
    calc
      root m ^ (m + 1) * root m = root m ^ (m + 2) := by
        simpa only [Nat.add_assoc] using (pow_succ (root m) (m + 1)).symm
      _ = 2 := root_pow m
  rw [hden]
  norm_num

theorem gap9 (m : ℕ) :
    ∀ i : Fin (m + 1),
      xStar m i =
        Real.rpow 2
          (((i.val + 1 : ℕ) : ℝ) / ((m + 2 : ℕ) : ℝ)) := by
  intro i
  rfl

theorem gap10 (m : ℕ) :
    ∀ v : Fin (m + 1) → ℝ,
      secondVariationAtYStar m v =
        1 / root m * ((∑ i, (v i) ^ 2) + (∑ i, v i) ^ 2) := by
  intro v
  rfl

theorem gap11 (m : ℕ) :
    ∀ v : Fin (m + 1) → ℝ, v ≠ 0 →
      0 < 1 / root m *
        ((∑ i, (v i) ^ 2) + (∑ i, v i) ^ 2) := by
  intro v hv
  have hex : ∃ i : Fin (m + 1), v i ≠ 0 := by
    by_contra h
    push_neg at h
    exact hv (funext h)
  obtain ⟨i, hi⟩ := hex
  have hsum : 0 < ∑ j : Fin (m + 1), (v j) ^ 2 := by
    exact Finset.sum_pos' (fun j hj => sq_nonneg (v j))
      ⟨i, Finset.mem_univ i, sq_pos_of_ne_zero hi⟩
  have hbracket :
      0 < (∑ j : Fin (m + 1), (v j) ^ 2) +
        (∑ j : Fin (m + 1), v j) ^ 2 :=
    add_pos_of_pos_of_nonneg hsum (sq_nonneg _)
  exact mul_pos (one_div_pos.mpr (root_pos m)) hbracket

theorem gap12 (m : ℕ) :
    PositiveDefiniteAtYStar m := by
  intro v hv
  rw [gap10 m v]
  exact gap11 m v hv

private theorem yCoord_positive
    (m : ℕ) (x : Fin (m + 1) → ℝ) (hx : x ∈ positiveOrthant m) :
    yCoord m x ∈ positiveOrthant m := by
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa only [yCoord, Fin.cases_zero] using hx 0
  · simp only [yCoord, Fin.cases_succ]
    exact div_pos (hx j.succ) (hx j.castSucc)

private theorem xStar_positive (m : ℕ) :
    xStar m ∈ positiveOrthant m := by
  intro i
  unfold xStar
  exact Real.rpow_pos_of_pos (by norm_num) _

private theorem yCoord_xStar (m : ℕ) :
    yCoord m (xStar m) = yStar m := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [yCoord, Fin.cases_zero, xStar, yStar, root, Fin.val_zero]
    congr 1
    norm_num
  · simp only [yCoord, Fin.cases_succ, xStar, yStar, root,
      Fin.val_succ, Fin.val_castSucc]
    calc
      Real.rpow 2
            (((j.succ.val + 1 : ℕ) : ℝ) / ((m + 2 : ℕ) : ℝ)) /
          Real.rpow 2
            (((j.castSucc.val + 1 : ℕ) : ℝ) / ((m + 2 : ℕ) : ℝ)) =
          Real.rpow 2
            ((((j.succ.val + 1 : ℕ) : ℝ) / ((m + 2 : ℕ) : ℝ)) -
              (((j.castSucc.val + 1 : ℕ) : ℝ) / ((m + 2 : ℕ) : ℝ))) :=
        (Real.rpow_sub (by norm_num : (0 : ℝ) < 2) _ _).symm
      _ = Real.rpow 2 (1 / ((m + 2 : ℕ) : ℝ)) := by
        congr 1
        have hn : (0 : ℝ) < ((m + 2 : ℕ) : ℝ) := by positivity
        field_simp
        norm_num

private theorem yCoord_injective_on_positive
    (m : ℕ) (x q : Fin (m + 1) → ℝ)
    (hx : x ∈ positiveOrthant m) (hq : q ∈ positiveOrthant m)
    (heq : yCoord m x = yCoord m q) :
    x = q := by
  funext i
  induction i using Fin.induction with
  | zero =>
      have h := congrFun heq 0
      simpa only [yCoord, Fin.cases_zero] using h
  | succ i ih =>
      have h := congrFun heq i.succ
      simp only [yCoord, Fin.cases_succ] at h
      rw [ih] at h
      exact (div_left_inj' (ne_of_gt (hq i.castSucc))).mp h

private theorem transformed_yStar_value (m : ℕ) :
    transformedU m (yStar m) = ((m + 2 : ℕ) : ℝ) * root m := by
  have hrne : root m ≠ 0 := ne_of_gt (root_pos m)
  have hprod :
      (∏ i : Fin (m + 1), yStar m i) = root m ^ (m + 1) := by
    simp [yStar]
  have hquot : 2 / root m ^ (m + 1) = root m := by
    apply (div_eq_iff (pow_ne_zero _ hrne)).2
    calc
      2 = root m ^ (m + 2) := (root_pow m).symm
      _ = root m * root m ^ (m + 1) := by
        rw [pow_succ]
        ring
  unfold transformedU
  rw [hprod, hquot]
  simp only [yStar, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  norm_num
  ring

private theorem transformed_global_bound
    (m : ℕ) (y : Fin (m + 1) → ℝ)
    (hy : y ∈ positiveOrthant m) :
    ((m + 2 : ℕ) : ℝ) * root m ≤ transformedU m y ∧
      (transformedU m y = ((m + 2 : ℕ) : ℝ) * root m →
        y = yStar m) := by
  let N : ℕ := m + 2
  let P : ℝ := ∏ i, y i
  have hPpos : 0 < P := by
    dsimp [P]
    exact Finset.prod_pos (fun i hi => hy i)
  have hP : P ≠ 0 := ne_of_gt hPpos
  have hN : (0 : ℝ) < (N : ℝ) := by
    dsimp [N]
    positivity
  let w : Option (Fin (m + 1)) → ℝ := fun _ => 1
  let v : Option (Fin (m + 1)) → ℝ
    | none => 2 / P
    | some i => y i
  have hsumw :
      ∑ i ∈ (Finset.univ : Finset (Option (Fin (m + 1)))), w i =
        (N : ℝ) := by
    simp [w, N]
    ring
  have hsumwv :
      ∑ i ∈ (Finset.univ : Finset (Option (Fin (m + 1)))), w i * v i =
        transformedU m y := by
    change (∑ i : Option (Fin (m + 1)), w i * v i) = _
    rw [Fintype.sum_option]
    simp only [w, v, one_mul]
    unfold transformedU
    dsimp [P]
    ring
  have hprod :
      ∏ i ∈ (Finset.univ : Finset (Option (Fin (m + 1)))), v i ^ w i =
        2 := by
    change (∏ i : Option (Fin (m + 1)), v i ^ w i) = 2
    rw [Fintype.prod_option]
    simp only [w, v, Real.rpow_one]
    dsimp [P] at hP ⊢
    field_simp [hP]
  have hw :
      ∀ i ∈ (Finset.univ : Finset (Option (Fin (m + 1)))), 0 ≤ w i := by
    intro i hi
    simp [w]
  have hv :
      ∀ i ∈ (Finset.univ : Finset (Option (Fin (m + 1)))), 0 ≤ v i := by
    intro i hi
    cases i with
    | none =>
        simp only [v]
        exact div_nonneg (by norm_num) hPpos.le
    | some i =>
        simp only [v]
        exact (hy i).le
  have hsumwpos :
      0 < ∑ i ∈ (Finset.univ : Finset (Option (Fin (m + 1)))), w i := by
    rw [hsumw]
    exact hN
  have hamgm :=
    Real.geom_mean_le_arith_mean
      (Finset.univ : Finset (Option (Fin (m + 1)))) w v
      hw hsumwpos hv
  rw [hprod, hsumw, hsumwv] at hamgm
  have hroot :
      root m = Real.rpow 2 ((N : ℝ)⁻¹) := by
    unfold root
    congr 1
    dsimp [N]
    field_simp
  change Real.rpow 2 ((N : ℝ)⁻¹) ≤ transformedU m y / (N : ℝ) at hamgm
  rw [← hroot] at hamgm
  have hle : (N : ℝ) * root m ≤ transformedU m y := by
    simpa only [mul_comm] using (le_div_iff₀ hN).mp hamgm
  constructor
  · simpa only [N] using hle
  · intro heq
    let wn : Option (Fin (m + 1)) → ℝ := fun _ => 1 / (N : ℝ)
    have hwnpos :
        ∀ i ∈ (Finset.univ : Finset (Option (Fin (m + 1)))),
          0 < wn i := by
      intro i hi
      simp [wn, hN]
    have hsumwn :
        ∑ i ∈ (Finset.univ : Finset (Option (Fin (m + 1)))), wn i = 1 := by
      simp only [wn, Finset.sum_const, Finset.card_univ,
        Fintype.card_option, Fintype.card_fin, nsmul_eq_mul]
      dsimp [N]
      field_simp
    have hsumwnv :
        ∑ i ∈ (Finset.univ : Finset (Option (Fin (m + 1)))), wn i * v i =
          root m := by
      calc
        (∑ i : Option (Fin (m + 1)), wn i * v i) =
            (∑ i : Option (Fin (m + 1)), w i * v i) / (N : ℝ) := by
              rw [Finset.sum_div]
              apply Finset.sum_congr rfl
              intro i hi
              simp only [wn, w]
              ring
        _ = transformedU m y / (N : ℝ) := by rw [hsumwv]
        _ = root m := by
          rw [heq]
          dsimp [N]
          field_simp
    have hprodwn :
        (∏ i ∈ (Finset.univ : Finset (Option (Fin (m + 1)))), v i ^ wn i) =
          root m := by
      rw [Real.finset_prod_rpow
        (Finset.univ : Finset (Option (Fin (m + 1)))) v hv]
      have hraw :
          (∏ i ∈ (Finset.univ : Finset (Option (Fin (m + 1)))), v i) = 2 := by
        change (∏ i : Option (Fin (m + 1)), v i) = 2
        rw [Fintype.prod_option]
        simp only [v]
        dsimp [P] at hP ⊢
        field_simp [hP]
      rw [hraw]
      change Real.rpow 2 (1 / (N : ℝ)) = root m
      rw [show (1 / (N : ℝ)) = (N : ℝ)⁻¹ by simp]
      exact hroot.symm
    have hgeomEq :
        (∏ i ∈ (Finset.univ : Finset (Option (Fin (m + 1)))), v i ^ wn i) =
          ∑ i ∈ (Finset.univ : Finset (Option (Fin (m + 1)))), wn i * v i := by
      rw [hprodwn, hsumwnv]
    have hall :=
      (Real.geom_mean_eq_arith_mean_weighted_iff'
        (Finset.univ : Finset (Option (Fin (m + 1)))) wn v
        hwnpos hsumwn hv).mp hgeomEq
    funext i
    have hi := hall (some i) (Finset.mem_univ _)
    rw [hsumwnv] at hi
    simpa only [v, yStar] using hi

private theorem xStar_value (m : ℕ) :
    u m (xStar m) = ((m + 2 : ℕ) : ℝ) * root m := by
  rw [gap2 m (xStar m) (xStar_positive m)]
  rw [yCoord_xStar m]
  exact transformed_yStar_value m

theorem gap13 (m : ℕ) :
    IsUniqueGlobalMinimizerOn m (xStar m) := by
  refine ⟨xStar_positive m, ?_, ?_⟩
  · intro q hq
    rw [xStar_value m]
    rw [gap2 m q hq]
    exact (transformed_global_bound m (yCoord m q)
      (yCoord_positive m q hq)).1
  · intro q hq heq
    have hyEq : yCoord m q = yStar m := by
      apply (transformed_global_bound m (yCoord m q)
        (yCoord_positive m q hq)).2
      rw [← gap2 m q hq, heq, xStar_value m]
    apply yCoord_injective_on_positive m q (xStar m) hq (xStar_positive m)
    rw [hyEq, yCoord_xStar m]

theorem gap14 (m : ℕ) :
    u m (xStar m) = ((m + 2 : ℕ) : ℝ) * root m := by
  exact xStar_value m

theorem gap15 (m : ℕ) :
    minimumPointsOn m = {xStar m} := by
  ext p
  constructor
  · intro hp
    have hp' :
        p ∈ positiveOrthant m ∧
          ∀ q ∈ positiveOrthant m, u m p ≤ u m q := hp
    have hlow := (gap13 m).2.1 p hp'.1
    have hupp := hp'.2 (xStar m) (gap13 m).1
    have heq : u m p = u m (xStar m) := le_antisymm hupp hlow
    have hpstar := (gap13 m).2.2 p hp'.1 heq
    simpa only [Set.mem_singleton_iff] using hpstar
  · intro hp
    have hpstar : p = xStar m := by
      simpa only [Set.mem_singleton_iff] using hp
    subst p
    exact ⟨(gap13 m).1, (gap13 m).2.1⟩

end

end ProofGap.Exercise3649
