import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

namespace ProofGap.Exercise3702

noncomputable section

def determinant (A B C : ℝ) : ℝ :=
  A * C - B ^ 2

def discriminant (A B C : ℝ) : ℝ :=
  (A + C) ^ 2 - 4 * determinant A B C

def quadraticForm (A B C : ℝ) (p : ℝ × ℝ) : ℝ :=
  A * p.1 ^ 2 + 2 * B * p.1 * p.2 + C * p.2 ^ 2

def conic (A B C : ℝ) : Set (ℝ × ℝ) :=
  {p | quadraticForm A B C p = 1}

def distanceSq (p : ℝ × ℝ) : ℝ :=
  p.1 ^ 2 + p.2 ^ 2

def characteristic (A B C lam : ℝ) : Prop :=
  (lam * A - 1) * (lam * C - 1) - lam ^ 2 * B ^ 2 = 0

def critical (A B C : ℝ) (p : ℝ × ℝ) (lam : ℝ) : Prop :=
  (lam * A - 1) * p.1 + lam * B * p.2 = 0 ∧
    lam * B * p.1 + (lam * C - 1) * p.2 = 0 ∧
    quadraticForm A B C p = 1

def rootPlus (A B C : ℝ) : ℝ :=
  (A + C + Real.sqrt (discriminant A B C)) /
    (2 * determinant A B C)

def rootMinus (A B C : ℝ) : ℝ :=
  (A + C - Real.sqrt (discriminant A B C)) /
    (2 * determinant A B C)

def lambdaHigh (A B C : ℝ) : ℝ :=
  max (rootPlus A B C) (rootMinus A B C)

def lambdaLow (A B C : ℝ) : ℝ :=
  min (rootPlus A B C) (rootMinus A B C)

private theorem discriminant_nonneg (A B C : ℝ) :
    0 ≤ discriminant A B C := by
  unfold discriminant determinant
  nlinarith [sq_nonneg (A - C), sq_nonneg B]

private theorem discriminant_factorization (A B C : ℝ) :
    (A + C + Real.sqrt (discriminant A B C)) *
        (A + C - Real.sqrt (discriminant A B C)) =
      4 * determinant A B C := by
  have hs := Real.sq_sqrt (discriminant_nonneg A B C)
  calc
    (A + C + Real.sqrt (discriminant A B C)) *
          (A + C - Real.sqrt (discriminant A B C)) =
        (A + C) ^ 2 - (Real.sqrt (discriminant A B C)) ^ 2 := by ring
    _ = 4 * determinant A B C := by
      rw [hs]
      unfold discriminant
      ring

private theorem characteristic_rootPlus (A B C : ℝ)
    (hdet : determinant A B C ≠ 0) :
    characteristic A B C (rootPlus A B C) := by
  have hD : A * C - B ^ 2 ≠ 0 := by
    simpa [determinant] using hdet
  have hs := Real.sq_sqrt (discriminant_nonneg A B C)
  unfold discriminant determinant at hs
  unfold characteristic rootPlus discriminant determinant
  field_simp [hD]
  nlinarith [hs]

private theorem characteristic_rootMinus (A B C : ℝ)
    (hdet : determinant A B C ≠ 0) :
    characteristic A B C (rootMinus A B C) := by
  have hD : A * C - B ^ 2 ≠ 0 := by
    simpa [determinant] using hdet
  have hs := Real.sq_sqrt (discriminant_nonneg A B C)
  unfold discriminant determinant at hs
  unfold characteristic rootMinus discriminant determinant
  field_simp [hD]
  nlinarith [hs]

private theorem exists_critical_of_characteristic_pos
    (A B C lam : ℝ) (hchar : characteristic A B C lam) (hlam : 0 < lam) :
    ∃ p : ℝ × ℝ, critical A B C p lam ∧ distanceSq p = lam := by
  let a : ℝ := lam * A - 1
  let b : ℝ := lam * B
  let c : ℝ := lam * C - 1
  have hdetlin : a * c - b ^ 2 = 0 := by
    unfold characteristic at hchar
    dsimp [a, b, c]
    nlinarith [hchar]
  obtain ⟨x, y, hlin₁, hlin₂, hrpos⟩ :
      ∃ x y : ℝ, a * x + b * y = 0 ∧ b * x + c * y = 0 ∧
        0 < x ^ 2 + y ^ 2 := by
    by_cases hz : a = 0 ∧ b = 0
    · refine ⟨1, 0, ?_, ?_, ?_⟩
      · simp [hz.1, hz.2]
      · simp [hz.2]
      · norm_num
    · refine ⟨b, -a, ?_, ?_, ?_⟩
      · ring
      · nlinarith [hdetlin]
      · by_cases ha : a = 0
        · have hb : b ≠ 0 := by
            intro hb
            exact hz ⟨ha, hb⟩
          have hbpos : 0 < b * b := mul_self_pos.mpr hb
          nlinarith [sq_nonneg a]
        · have hapos : 0 < a * a := mul_self_pos.mpr ha
          nlinarith [sq_nonneg b]
  let q : ℝ := x ^ 2 + y ^ 2
  have hqpos : 0 < q := by simpa [q] using hrpos
  let t : ℝ := Real.sqrt (lam / q)
  have ht : t ^ 2 = lam / q := by
    dsimp [t]
    exact Real.sq_sqrt (le_of_lt (div_pos hlam hqpos))
  have hp₁ : a * (t * x) + b * (t * y) = 0 := by
    calc
      a * (t * x) + b * (t * y) = t * (a * x + b * y) := by ring
      _ = 0 := by rw [hlin₁]; ring
  have hp₂ : b * (t * x) + c * (t * y) = 0 := by
    calc
      b * (t * x) + c * (t * y) = t * (b * x + c * y) := by ring
      _ = 0 := by rw [hlin₂]; ring
  have hp₁' :
      (lam * A - 1) * (t * x) + lam * B * (t * y) = 0 := by
    simpa [a, b] using hp₁
  have hp₂' :
      lam * B * (t * x) + (lam * C - 1) * (t * y) = 0 := by
    simpa [b, c] using hp₂
  have hdist : distanceSq (t * x, t * y) = lam := by
    unfold distanceSq
    dsimp
    calc
      (t * x) ^ 2 + (t * y) ^ 2 = t ^ 2 * q := by
        dsimp [q]
        ring
      _ = (lam / q) * q := by rw [ht]
      _ = lam := by field_simp [ne_of_gt hqpos]
  have hrel :
      lam * quadraticForm A B C (t * x, t * y) =
        distanceSq (t * x, t * y) := by
    unfold quadraticForm distanceSq
    dsimp
    linear_combination (t * x) * hp₁' + (t * y) * hp₂'
  have hform : quadraticForm A B C (t * x, t * y) = 1 := by
    nlinarith [hrel, hdist]
  refine ⟨(t * x, t * y), ?_, hdist⟩
  exact ⟨hp₁', hp₂', hform⟩

private theorem rootPlus_pos_of_det_pos_trace_pos (A B C : ℝ)
    (hdet : 0 < determinant A B C) (htrace : 0 < A + C) :
    0 < rootPlus A B C := by
  have hs0 := Real.sqrt_nonneg (discriminant A B C)
  have hnum : 0 < A + C + Real.sqrt (discriminant A B C) := by
    linarith
  have hden : 0 < 2 * determinant A B C := by nlinarith
  unfold rootPlus
  exact div_pos hnum hden

private theorem rootMinus_pos_of_det_pos_trace_pos (A B C : ℝ)
    (hdet : 0 < determinant A B C) (htrace : 0 < A + C) :
    0 < rootMinus A B C := by
  have hs0 := Real.sqrt_nonneg (discriminant A B C)
  have hprod := discriminant_factorization A B C
  have hplus : 0 < A + C + Real.sqrt (discriminant A B C) := by
    linarith
  have hnum : 0 < A + C - Real.sqrt (discriminant A B C) := by
    by_contra hn
    have hle : A + C - Real.sqrt (discriminant A B C) ≤ 0 :=
      le_of_not_gt hn
    have hmul :
        (A + C + Real.sqrt (discriminant A B C)) *
            (A + C - Real.sqrt (discriminant A B C)) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (le_of_lt hplus) hle
    nlinarith
  have hden : 0 < 2 * determinant A B C := by nlinarith
  unfold rootMinus
  exact div_pos hnum hden

private theorem rootPlus_neg_of_det_pos_trace_neg (A B C : ℝ)
    (hdet : 0 < determinant A B C) (htrace : A + C < 0) :
    rootPlus A B C < 0 := by
  have hs0 := Real.sqrt_nonneg (discriminant A B C)
  have hprod := discriminant_factorization A B C
  have hminus : A + C - Real.sqrt (discriminant A B C) < 0 := by
    linarith
  have hnum : A + C + Real.sqrt (discriminant A B C) < 0 := by
    by_contra hn
    have hge : 0 ≤ A + C + Real.sqrt (discriminant A B C) :=
      le_of_not_gt hn
    have hmul :
        (A + C + Real.sqrt (discriminant A B C)) *
            (A + C - Real.sqrt (discriminant A B C)) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hge (le_of_lt hminus)
    nlinarith
  have hden : 0 < 2 * determinant A B C := by nlinarith
  unfold rootPlus
  exact div_neg_of_neg_of_pos hnum hden

private theorem rootMinus_neg_of_det_pos_trace_neg (A B C : ℝ)
    (hdet : 0 < determinant A B C) (htrace : A + C < 0) :
    rootMinus A B C < 0 := by
  have hs0 := Real.sqrt_nonneg (discriminant A B C)
  have hnum : A + C - Real.sqrt (discriminant A B C) < 0 := by
    linarith
  have hden : 0 < 2 * determinant A B C := by nlinarith
  unfold rootMinus
  exact div_neg_of_neg_of_pos hnum hden

private theorem rootPlus_neg_of_det_neg (A B C : ℝ)
    (hdet : determinant A B C < 0) :
    rootPlus A B C < 0 := by
  have hs0 := Real.sqrt_nonneg (discriminant A B C)
  have hprod := discriminant_factorization A B C
  have hnum : 0 < A + C + Real.sqrt (discriminant A B C) := by
    by_contra hn
    have hplus : A + C + Real.sqrt (discriminant A B C) ≤ 0 :=
      le_of_not_gt hn
    have hminus : A + C - Real.sqrt (discriminant A B C) ≤ 0 := by
      linarith
    have hmul :
        0 ≤ (A + C + Real.sqrt (discriminant A B C)) *
          (A + C - Real.sqrt (discriminant A B C)) :=
      mul_nonneg_of_nonpos_of_nonpos hplus hminus
    nlinarith
  have hden : 2 * determinant A B C < 0 := by nlinarith
  unfold rootPlus
  exact div_neg_of_pos_of_neg hnum hden

private theorem rootMinus_pos_of_det_neg (A B C : ℝ)
    (hdet : determinant A B C < 0) :
    0 < rootMinus A B C := by
  have hs0 := Real.sqrt_nonneg (discriminant A B C)
  have hprod := discriminant_factorization A B C
  have hnum : A + C - Real.sqrt (discriminant A B C) < 0 := by
    by_contra hn
    have hminus : 0 ≤ A + C - Real.sqrt (discriminant A B C) :=
      le_of_not_gt hn
    have hplus : 0 ≤ A + C + Real.sqrt (discriminant A B C) := by
      linarith
    have hmul :
        0 ≤ (A + C + Real.sqrt (discriminant A B C)) *
          (A + C - Real.sqrt (discriminant A B C)) :=
      mul_nonneg hplus hminus
    nlinarith
  have hden : 2 * determinant A B C < 0 := by nlinarith
  unfold rootMinus
  exact div_pos_of_neg_of_neg hnum hden

private theorem quadraticForm_le_top_eigenvalue (A B C : ℝ) (p : ℝ × ℝ) :
    quadraticForm A B C p ≤
      ((A + C + Real.sqrt (discriminant A B C)) / 2) * distanceSq p := by
  let s : ℝ := Real.sqrt (discriminant A B C)
  let u : ℝ := A - C
  let v : ℝ := 2 * B
  let X : ℝ := p.1 ^ 2 - p.2 ^ 2
  let Y : ℝ := 2 * p.1 * p.2
  let r : ℝ := p.1 ^ 2 + p.2 ^ 2
  let z : ℝ := u * X + v * Y
  have hs0 : 0 ≤ s := by
    dsimp [s]
    exact Real.sqrt_nonneg _
  have hr0 : 0 ≤ r := by
    dsimp [r]
    positivity
  have hs2raw := Real.sq_sqrt (discriminant_nonneg A B C)
  have huv : u ^ 2 + v ^ 2 = s ^ 2 := by
    dsimp [u, v, s]
    rw [hs2raw]
    unfold discriminant determinant
    ring
  have hXY : X ^ 2 + Y ^ 2 = r ^ 2 := by
    dsimp [X, Y, r]
    ring
  have hid :
      z ^ 2 + (u * Y - v * X) ^ 2 =
        (u ^ 2 + v ^ 2) * (X ^ 2 + Y ^ 2) := by
    dsimp [z]
    ring
  have hzsq : z ^ 2 ≤ (s * r) ^ 2 := by
    rw [huv, hXY] at hid
    nlinarith [sq_nonneg (u * Y - v * X)]
  have hsr0 : 0 ≤ s * r := mul_nonneg hs0 hr0
  have hz : z ≤ s * r := by
    by_contra hn
    have hlt : s * r < z := lt_of_not_ge hn
    have hdiff : 0 < z - s * r := by linarith
    have hsum : 0 < z + s * r := by linarith
    have hmul : 0 < (z - s * r) * (z + s * r) :=
      mul_pos hdiff hsum
    nlinarith
  change
    (A - C) * (p.1 ^ 2 - p.2 ^ 2) +
        (2 * B) * (2 * p.1 * p.2) ≤
      Real.sqrt (discriminant A B C) * (p.1 ^ 2 + p.2 ^ 2) at hz
  unfold quadraticForm distanceSq
  nlinarith

private theorem distance_ge_lambdaHigh_of_det_neg
    (A B C : ℝ) (hdet : determinant A B C < 0) (p : ℝ × ℝ)
    (hp : p ∈ conic A B C) :
    lambdaHigh A B C ≤ distanceSq p := by
  have hpform : quadraticForm A B C p = 1 := by
    exact hp
  have hs0 := Real.sqrt_nonneg (discriminant A B C)
  have hprod := discriminant_factorization A B C
  have hsum : 0 < A + C + Real.sqrt (discriminant A B C) := by
    by_contra hn
    have hplus : A + C + Real.sqrt (discriminant A B C) ≤ 0 :=
      le_of_not_gt hn
    have hminus : A + C - Real.sqrt (discriminant A B C) ≤ 0 := by
      linarith
    have hmul :
        0 ≤ (A + C + Real.sqrt (discriminant A B C)) *
          (A + C - Real.sqrt (discriminant A B C)) :=
      mul_nonneg_of_nonpos_of_nonpos hplus hminus
    nlinarith
  have hplusneg := rootPlus_neg_of_det_neg A B C hdet
  have hminuspos := rootMinus_pos_of_det_neg A B C hdet
  have horder : rootPlus A B C ≤ rootMinus A B C := by linarith
  have hhigh : lambdaHigh A B C = rootMinus A B C := by
    simp [lambdaHigh, max_eq_right horder]
  have hroot :
      rootMinus A B C =
        2 / (A + C + Real.sqrt (discriminant A B C)) := by
    unfold rootMinus
    field_simp [ne_of_lt hdet, ne_of_gt hsum]
    nlinarith [hprod]
  have hbound := quadraticForm_le_top_eigenvalue A B C p
  rw [hpform] at hbound
  rw [hhigh, hroot]
  apply (div_le_iff₀ hsum).2
  nlinarith

theorem gap1 (A B C lam : ℝ) (p : ℝ × ℝ)
    (hcrit : critical A B C p lam) :
    characteristic A B C lam := by
  rcases hcrit with ⟨h₁, h₂, hq⟩
  unfold characteristic
  by_contra hne
  have hxprod :
      (((lam * A - 1) * (lam * C - 1) - lam ^ 2 * B ^ 2) * p.1) = 0 := by
    linear_combination (lam * C - 1) * h₁ - (lam * B) * h₂
  have hyprod :
      (((lam * A - 1) * (lam * C - 1) - lam ^ 2 * B ^ 2) * p.2) = 0 := by
    linear_combination (lam * A - 1) * h₂ - (lam * B) * h₁
  have hx : p.1 = 0 := (mul_eq_zero.mp hxprod).resolve_left hne
  have hy : p.2 = 0 := (mul_eq_zero.mp hyprod).resolve_left hne
  unfold quadraticForm at hq
  simp [hx, hy] at hq

theorem gap2 (A B C lam : ℝ) (p : ℝ × ℝ)
    (hcrit : critical A B C p lam) :
    (lam * A - 1) * p.1 + lam * B * p.2 = 0 ∧
      lam * B * p.1 + (lam * C - 1) * p.2 = 0 ∧
      p ∈ conic A B C := by
  simpa [critical, conic] using hcrit

theorem gap3 (A B C : ℝ) (hdet : determinant A B C ≠ 0) :
    determinant A B C ≠ 0 := by
  exact hdet

theorem gap4 (A B C : ℝ) (hdet : determinant A B C ≠ 0) :
    characteristic A B C (lambdaHigh A B C) := by
  rcases le_total (rootPlus A B C) (rootMinus A B C) with h | h
  · simpa [lambdaHigh, max_eq_right h] using
      characteristic_rootMinus A B C hdet
  · simpa [lambdaHigh, max_eq_left h] using
      characteristic_rootPlus A B C hdet

theorem gap5 (A B C : ℝ) (hdet : determinant A B C ≠ 0) :
    characteristic A B C (lambdaLow A B C) := by
  rcases le_total (rootPlus A B C) (rootMinus A B C) with h | h
  · simpa [lambdaLow, min_eq_left h] using
      characteristic_rootPlus A B C hdet
  · simpa [lambdaLow, min_eq_right h] using
      characteristic_rootMinus A B C hdet

theorem gap6 (A B C : ℝ) :
    lambdaHigh A B C ≥ lambdaLow A B C := by
  unfold lambdaHigh lambdaLow
  exact min_le_max

theorem gap7 (A B C : ℝ) (hdet : determinant A B C ≠ 0)
    (hpos : 0 < lambdaHigh A B C) :
    ∃ p : ℝ × ℝ, critical A B C p (lambdaHigh A B C) ∧
      distanceSq p = lambdaHigh A B C := by
  exact exists_critical_of_characteristic_pos A B C (lambdaHigh A B C)
    (gap4 A B C hdet) hpos

theorem gap8 (A B C : ℝ) (hdet : determinant A B C ≠ 0)
    (hpos : 0 < lambdaLow A B C) :
    ∃ p : ℝ × ℝ, critical A B C p (lambdaLow A B C) ∧
      distanceSq p = lambdaLow A B C := by
  exact exists_critical_of_characteristic_pos A B C (lambdaLow A B C)
    (gap5 A B C hdet) hpos

theorem gap9 (A B C : ℝ) :
    ({lambdaHigh A B C, lambdaLow A B C} : Set ℝ) =
      ({rootPlus A B C, rootMinus A B C} : Set ℝ) := by
  ext x
  rcases le_total (rootPlus A B C) (rootMinus A B C) with h | h
  · simp [lambdaHigh, lambdaLow, max_eq_right h, min_eq_left h, or_comm]
  · simp [lambdaHigh, lambdaLow, max_eq_left h, min_eq_right h, or_comm]

theorem gap10 (A B C : ℝ) (hdet : 0 < determinant A B C)
    (htrace : 0 < A + C) :
    lambdaHigh A B C ≥ lambdaLow A B C := by
  exact gap6 A B C

theorem gap11 (A B C : ℝ) (hdet : 0 < determinant A B C)
    (htrace : 0 < A + C) :
    0 < lambdaLow A B C := by
  exact lt_min (rootPlus_pos_of_det_pos_trace_pos A B C hdet htrace)
    (rootMinus_pos_of_det_pos_trace_pos A B C hdet htrace)

theorem gap12 (A B C : ℝ) (hdet : 0 < determinant A B C)
    (htrace : 0 < A + C) :
    0 < lambdaHigh A B C := by
  exact lt_max_of_lt_left
    (rootPlus_pos_of_det_pos_trace_pos A B C hdet htrace)

theorem gap13 (A B C : ℝ) (hdet : 0 < determinant A B C)
    (htrace : 0 < A + C) :
    ∃ a₀ : ℝ, 0 ≤ a₀ ∧ a₀ ^ 2 = lambdaHigh A B C := by
  refine ⟨Real.sqrt (lambdaHigh A B C), Real.sqrt_nonneg _, ?_⟩
  exact Real.sq_sqrt (le_of_lt (gap12 A B C hdet htrace))

theorem gap14 (A B C : ℝ) (hdet : 0 < determinant A B C)
    (htrace : 0 < A + C) :
    ∃ b₀ : ℝ, 0 ≤ b₀ ∧ b₀ ^ 2 = lambdaLow A B C := by
  refine ⟨Real.sqrt (lambdaLow A B C), Real.sqrt_nonneg _, ?_⟩
  exact Real.sq_sqrt (le_of_lt (gap11 A B C hdet htrace))

theorem gap15 (A B C : ℝ) (hdet : 0 < determinant A B C)
    (htrace : A + C < 0) :
    lambdaHigh A B C < 0 := by
  unfold lambdaHigh
  exact max_lt
    (rootPlus_neg_of_det_pos_trace_neg A B C hdet htrace)
    (rootMinus_neg_of_det_pos_trace_neg A B C hdet htrace)

theorem gap16 (A B C : ℝ) (hdet : 0 < determinant A B C)
    (htrace : A + C < 0) :
    lambdaLow A B C < 0 := by
  unfold lambdaLow
  exact min_lt_of_left_lt
    (rootPlus_neg_of_det_pos_trace_neg A B C hdet htrace)

theorem gap17 (A B C : ℝ) (hdet : 0 < determinant A B C)
    (htrace : A + C < 0) :
    conic A B C = ∅ := by
  ext p
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hp
  change quadraticForm A B C p = 1 at hp
  have hA : A < 0 := by
    by_contra hn
    have hAnonneg : 0 ≤ A := le_of_not_gt hn
    have hCneg : C < 0 := by linarith
    have hAC : A * C ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hAnonneg (le_of_lt hCneg)
    unfold determinant at hdet
    nlinarith [sq_nonneg B]
  have hid :
      A * quadraticForm A B C p =
        (A * p.1 + B * p.2) ^ 2 + determinant A B C * p.2 ^ 2 := by
    unfold quadraticForm determinant
    ring
  have hrhs :
      0 ≤ (A * p.1 + B * p.2) ^ 2 + determinant A B C * p.2 ^ 2 := by
    positivity
  nlinarith

theorem gap18 (A B C : ℝ) (hdet : determinant A B C < 0) :
    0 < lambdaHigh A B C := by
  unfold lambdaHigh
  exact lt_max_of_lt_right (rootMinus_pos_of_det_neg A B C hdet)

theorem gap19 (A B C : ℝ) (hdet : determinant A B C < 0) :
    lambdaLow A B C < 0 := by
  unfold lambdaLow
  exact min_lt_of_left_lt (rootPlus_neg_of_det_neg A B C hdet)

theorem gap20 (A B C : ℝ) (hdet : determinant A B C < 0) :
    sInf (distanceSq '' conic A B C) = lambdaHigh A B C := by
  have hne : determinant A B C ≠ 0 := ne_of_lt hdet
  rcases gap7 A B C hne (gap18 A B C hdet) with ⟨p₀, hp₀, hd₀⟩
  have hp₀conic : p₀ ∈ conic A B C := by
    exact (gap2 A B C (lambdaHigh A B C) p₀ hp₀).2.2
  apply le_antisymm
  · apply csInf_le
    · refine ⟨lambdaHigh A B C, ?_⟩
      rintro z ⟨p, hp, rfl⟩
      exact distance_ge_lambdaHigh_of_det_neg A B C hdet p hp
    · exact ⟨p₀, hp₀conic, hd₀⟩
  · apply le_csInf
    · exact ⟨distanceSq p₀, ⟨p₀, hp₀conic, rfl⟩⟩
    · intro z hz
      rcases hz with ⟨p, hp, rfl⟩
      exact distance_ge_lambdaHigh_of_det_neg A B C hdet p hp

theorem gap21 (A B C : ℝ) (hdet : determinant A B C < 0) :
    ¬ ∃ b₀ : ℝ, b₀ ^ 2 = lambdaLow A B C := by
  rintro ⟨b₀, hb₀⟩
  have hsquare : 0 ≤ b₀ ^ 2 := sq_nonneg b₀
  have hlow : lambdaLow A B C < 0 := gap19 A B C hdet
  nlinarith

theorem gap22 (A B C : ℝ) (hdet : determinant A B C < 0) :
    (Real.sqrt (lambdaHigh A B C)) ^ 2 = lambdaHigh A B C := by
  exact Real.sq_sqrt (le_of_lt (gap18 A B C hdet))

theorem gap23 (A B C : ℝ) (hdet : determinant A B C < 0) :
    ¬ ∃ b₀ : ℝ, 0 ≤ b₀ ∧ b₀ = Real.sqrt (lambdaLow A B C) ∧
      b₀ ^ 2 = lambdaLow A B C := by
  rintro ⟨b₀, hbnonneg, hbsqrt, hbsq⟩
  have hsquare : 0 ≤ b₀ ^ 2 := sq_nonneg b₀
  have hlow : lambdaLow A B C < 0 := gap19 A B C hdet
  nlinarith

end

end ProofGap.Exercise3702
