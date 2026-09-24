import ProofGapLean.Prelude.Analysis
import Mathlib.Data.Complex.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Positivity

namespace ProofGap.Exercise2862

noncomputable section

def upperRootFactor : ℂ :=
  ((1 : ℂ) + Complex.I * Real.sqrt 3) / 2

def lowerRootFactor : ℂ :=
  ((1 : ℂ) - Complex.I * Real.sqrt 3) / 2

def complexCoefficientTerm (x : ℝ) (n : ℕ) : ℂ :=
  (-1 : ℂ) ^ n *
      (upperRootFactor ^ (n + 1) - lowerRootFactor ^ (n + 1)) *
    (x : ℂ) ^ n

def realCoefficientTerm (x : ℝ) (n : ℕ) : ℝ :=
  x ^ n * Real.sin ((2 * (n + 1) : ℝ) / 3 * Real.pi)

private theorem rootFactor_facts :
    lowerRootFactor + upperRootFactor = 1 ∧
    lowerRootFactor * upperRootFactor = 1 ∧
    upperRootFactor - lowerRootFactor = Complex.I * Real.sqrt 3 ∧
    upperRootFactor ^ 3 = -1 ∧
    lowerRootFactor ^ 3 = -1 ∧
    ‖upperRootFactor‖ = 1 ∧
    ‖lowerRootFactor‖ = 1 := by
  have hsR : Real.sqrt 3 * Real.sqrt 3 = (3 : ℝ) := by
    simpa [pow_two] using
      (Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3))
  have hsC : ((Real.sqrt 3 : ℂ) ^ 2) = 3 := by
    apply Complex.ext <;> norm_num [pow_two, hsR]
  have hI : (Complex.I : ℂ) ^ 2 = -1 := by norm_num
  have hsum : lowerRootFactor + upperRootFactor = 1 := by
    unfold lowerRootFactor upperRootFactor
    ring
  have hprod : lowerRootFactor * upperRootFactor = 1 := by
    unfold lowerRootFactor upperRootFactor
    calc
      (((1 : ℂ) - Complex.I * Real.sqrt 3) / 2) *
          (((1 : ℂ) + Complex.I * Real.sqrt 3) / 2) =
        (1 - (Complex.I * (Real.sqrt 3 : ℂ)) ^ 2) / 4 := by ring
      _ = 1 := by rw [mul_pow, hI, hsC]; norm_num
  have hdiff :
      upperRootFactor - lowerRootFactor = Complex.I * Real.sqrt 3 := by
    unfold upperRootFactor lowerRootFactor
    ring
  have hupperQuad : upperRootFactor ^ 2 - upperRootFactor + 1 = 0 := by
    unfold upperRootFactor
    calc
      (((1 : ℂ) + Complex.I * Real.sqrt 3) / 2) ^ 2 -
          ((1 + Complex.I * Real.sqrt 3) / 2) + 1 =
        (3 + (Complex.I * (Real.sqrt 3 : ℂ)) ^ 2) / 4 := by ring
      _ = 0 := by rw [mul_pow, hI, hsC]; norm_num
  have hlowerQuad : lowerRootFactor ^ 2 - lowerRootFactor + 1 = 0 := by
    unfold lowerRootFactor
    calc
      (((1 : ℂ) - Complex.I * Real.sqrt 3) / 2) ^ 2 -
          ((1 - Complex.I * Real.sqrt 3) / 2) + 1 =
        (3 + (Complex.I * (Real.sqrt 3 : ℂ)) ^ 2) / 4 := by ring
      _ = 0 := by rw [mul_pow, hI, hsC]; norm_num
  have hupperSq : upperRootFactor ^ 2 = upperRootFactor - 1 := by
    calc
      upperRootFactor ^ 2 =
          (upperRootFactor ^ 2 - upperRootFactor + 1) +
            upperRootFactor - 1 := by ring
      _ = upperRootFactor - 1 := by rw [hupperQuad]; ring
  have hlowerSq : lowerRootFactor ^ 2 = lowerRootFactor - 1 := by
    calc
      lowerRootFactor ^ 2 =
          (lowerRootFactor ^ 2 - lowerRootFactor + 1) +
            lowerRootFactor - 1 := by ring
      _ = lowerRootFactor - 1 := by rw [hlowerQuad]; ring
  have hupper3 : upperRootFactor ^ 3 = -1 := by
    calc
      upperRootFactor ^ 3 = upperRootFactor * upperRootFactor ^ 2 := by ring
      _ = upperRootFactor * (upperRootFactor - 1) := by rw [hupperSq]
      _ = upperRootFactor ^ 2 - upperRootFactor := by ring
      _ = -1 := by rw [hupperSq]; ring
  have hlower3 : lowerRootFactor ^ 3 = -1 := by
    calc
      lowerRootFactor ^ 3 = lowerRootFactor * lowerRootFactor ^ 2 := by ring
      _ = lowerRootFactor * (lowerRootFactor - 1) := by rw [hlowerSq]
      _ = lowerRootFactor ^ 2 - lowerRootFactor := by ring
      _ = -1 := by rw [hlowerSq]; ring
  have hstar : star upperRootFactor = lowerRootFactor := by
    apply Complex.ext <;>
      norm_num [upperRootFactor, lowerRootFactor]
  have hnormEq : ‖lowerRootFactor‖ = ‖upperRootFactor‖ := by
    rw [← hstar]
    simp
  have hnormProd : ‖lowerRootFactor‖ * ‖upperRootFactor‖ = 1 := by
    calc
      ‖lowerRootFactor‖ * ‖upperRootFactor‖ =
          ‖lowerRootFactor * upperRootFactor‖ := (norm_mul _ _).symm
      _ = 1 := by rw [hprod]; norm_num
  have hnormUpper : ‖upperRootFactor‖ = 1 := by
    rw [hnormEq] at hnormProd
    nlinarith [norm_nonneg upperRootFactor]
  have hnormLower : ‖lowerRootFactor‖ = 1 := by
    rw [hnormEq, hnormUpper]
  exact ⟨hsum, hprod, hdiff, hupper3, hlower3, hnormUpper, hnormLower⟩

theorem gap1 :
    ∀ x : ℝ, ((1 / (1 + x + x ^ 2) : ℝ) : ℂ) =
      1 / (Complex.I * Real.sqrt 3) *
        (1 / ((x : ℂ) + lowerRootFactor) -
          1 / ((x : ℂ) + upperRootFactor)) := by
  intro x
  rcases rootFactor_facts with
    ⟨hsum, hprod, hdiff, hupper3, hlower3, hnormUpper, hnormLower⟩
  let q : ℝ := 1 + x + x ^ 2
  have hqpos : 0 < q := by
    dsimp [q]
    nlinarith [sq_nonneg (2 * x + 1)]
  have hq : q ≠ 0 := ne_of_gt hqpos
  have hdenprod :
      ((x : ℂ) + lowerRootFactor) * ((x : ℂ) + upperRootFactor) = (q : ℂ) := by
    calc
      ((x : ℂ) + lowerRootFactor) * ((x : ℂ) + upperRootFactor) =
          (x : ℂ) ^ 2 + (x : ℂ) * (lowerRootFactor + upperRootFactor) +
            lowerRootFactor * upperRootFactor := by ring
      _ = (x : ℂ) ^ 2 + (x : ℂ) + 1 := by rw [hsum, hprod]; ring
      _ = (q : ℂ) := by
        dsimp [q]
        norm_num
        ring
  have hden : (q : ℂ) ≠ 0 := by
    intro h
    apply hq
    exact Complex.ofReal_injective h
  have hlower : (x : ℂ) + lowerRootFactor ≠ 0 := by
    intro h
    apply hden
    rw [← hdenprod, h]
    simp
  have hupper : (x : ℂ) + upperRootFactor ≠ 0 := by
    intro h
    apply hden
    rw [← hdenprod, h]
    simp
  have hsqrt : (Real.sqrt 3 : ℂ) ≠ 0 := by
    norm_num
  have hIroot : Complex.I * (Real.sqrt 3 : ℂ) ≠ 0 :=
    mul_ne_zero (by norm_num) hsqrt
  have hfrac :
      1 / ((x : ℂ) + lowerRootFactor) -
          1 / ((x : ℂ) + upperRootFactor) =
        (upperRootFactor - lowerRootFactor) /
          (((x : ℂ) + lowerRootFactor) * ((x : ℂ) + upperRootFactor)) := by
    field_simp [hlower, hupper] <;> ring
  have hcast : ((1 / q : ℝ) : ℂ) = 1 / (q : ℂ) := by norm_cast
  change ((1 / q : ℝ) : ℂ) = _
  rw [hcast, hfrac, hdiff, hdenprod]
  field_simp [hden, hIroot] <;> ring

theorem gap2
    (hpartial :
      ∀ x : ℝ, ((1 / (1 + x + x ^ 2) : ℝ) : ℂ) =
        1 / (Complex.I * Real.sqrt 3) *
          (1 / ((x : ℂ) + lowerRootFactor) -
            1 / ((x : ℂ) + upperRootFactor))) :
    ∀ x : ℝ, ((1 / (1 + x + x ^ 2) : ℝ) : ℂ) =
      1 / (Complex.I * Real.sqrt 3) *
        (upperRootFactor * (1 + upperRootFactor * (x : ℂ))⁻¹ -
          lowerRootFactor * (1 + lowerRootFactor * (x : ℂ))⁻¹) := by
  intro x
  rcases rootFactor_facts with
    ⟨hsum, hprod, hdiff, hupper3, hlower3, hnormUpper, hnormLower⟩
  let q : ℝ := 1 + x + x ^ 2
  have hqpos : 0 < q := by
    dsimp [q]
    nlinarith [sq_nonneg (2 * x + 1)]
  have hq : q ≠ 0 := ne_of_gt hqpos
  have hdenprod :
      ((x : ℂ) + lowerRootFactor) * ((x : ℂ) + upperRootFactor) = (q : ℂ) := by
    calc
      ((x : ℂ) + lowerRootFactor) * ((x : ℂ) + upperRootFactor) =
          (x : ℂ) ^ 2 + (x : ℂ) * (lowerRootFactor + upperRootFactor) +
            lowerRootFactor * upperRootFactor := by ring
      _ = (x : ℂ) ^ 2 + (x : ℂ) + 1 := by rw [hsum, hprod]; ring
      _ = (q : ℂ) := by
        dsimp [q]
        norm_num
        ring
  have hden : (q : ℂ) ≠ 0 := by
    intro h
    apply hq
    exact Complex.ofReal_injective h
  have hlower : (x : ℂ) + lowerRootFactor ≠ 0 := by
    intro h
    apply hden
    rw [← hdenprod, h]
    simp
  have hupper : (x : ℂ) + upperRootFactor ≠ 0 := by
    intro h
    apply hden
    rw [← hdenprod, h]
    simp
  have hupper_ne : upperRootFactor ≠ 0 := by
    intro h
    rw [h, norm_zero] at hnormUpper
    norm_num at hnormUpper
  have hlower_ne : lowerRootFactor ≠ 0 := by
    intro h
    rw [h, norm_zero] at hnormLower
    norm_num at hnormLower
  have hUL : upperRootFactor * lowerRootFactor = 1 := by
    simpa [mul_comm] using hprod
  have hUpperDen :
      1 + upperRootFactor * (x : ℂ) =
        upperRootFactor * ((x : ℂ) + lowerRootFactor) := by
    calc
      1 + upperRootFactor * (x : ℂ) =
          upperRootFactor * lowerRootFactor + upperRootFactor * (x : ℂ) := by rw [hUL]
      _ = upperRootFactor * ((x : ℂ) + lowerRootFactor) := by ring
  have hLowerDen :
      1 + lowerRootFactor * (x : ℂ) =
        lowerRootFactor * ((x : ℂ) + upperRootFactor) := by
    calc
      1 + lowerRootFactor * (x : ℂ) =
          lowerRootFactor * upperRootFactor + lowerRootFactor * (x : ℂ) := by rw [hprod]
      _ = lowerRootFactor * ((x : ℂ) + upperRootFactor) := by ring
  have hleft :
      1 / ((x : ℂ) + lowerRootFactor) =
        upperRootFactor * (1 + upperRootFactor * (x : ℂ))⁻¹ := by
    calc
      1 / ((x : ℂ) + lowerRootFactor) =
          upperRootFactor /
            (upperRootFactor * ((x : ℂ) + lowerRootFactor)) := by
              field_simp [hlower, hupper_ne] <;> ring
      _ = upperRootFactor * (1 + upperRootFactor * (x : ℂ))⁻¹ := by
        rw [← hUpperDen]
        rfl
  have hright :
      1 / ((x : ℂ) + upperRootFactor) =
        lowerRootFactor * (1 + lowerRootFactor * (x : ℂ))⁻¹ := by
    calc
      1 / ((x : ℂ) + upperRootFactor) =
          lowerRootFactor /
            (lowerRootFactor * ((x : ℂ) + upperRootFactor)) := by
              field_simp [hupper, hlower_ne] <;> ring
      _ = lowerRootFactor * (1 + lowerRootFactor * (x : ℂ))⁻¹ := by
        rw [← hLowerDen]
        rfl
  simpa [hleft, hright] using hpartial x

theorem gap3
    (hgeometricForm :
      ∀ x : ℝ, ((1 / (1 + x + x ^ 2) : ℝ) : ℂ) =
        1 / (Complex.I * Real.sqrt 3) *
          (upperRootFactor * (1 + upperRootFactor * (x : ℂ))⁻¹ -
            lowerRootFactor * (1 + lowerRootFactor * (x : ℂ))⁻¹)) :
    ∀ x : ℝ, |x| < 1 →
      ((1 / (1 + x + x ^ 2) : ℝ) : ℂ) =
        1 / (Complex.I * Real.sqrt 3) *
          (∑' n, complexCoefficientTerm x n) := by
  intro x hx
  rcases rootFactor_facts with
    ⟨hsum, hprod, hdiff, hupper3, hlower3, hnormUpper, hnormLower⟩
  have hxnorm : ‖(x : ℂ)‖ < 1 := by
    simpa [Complex.norm_real, Real.norm_eq_abs] using hx
  have hUpperRatio : ‖-upperRootFactor * (x : ℂ)‖ < 1 := by
    rw [norm_mul, norm_neg, hnormUpper, one_mul]
    exact hxnorm
  have hLowerRatio : ‖-lowerRootFactor * (x : ℂ)‖ < 1 := by
    rw [norm_mul, norm_neg, hnormLower, one_mul]
    exact hxnorm
  have hUpperSum :
      HasSum (fun n : ℕ => upperRootFactor * (-upperRootFactor * (x : ℂ)) ^ n)
        (upperRootFactor * (1 + upperRootFactor * (x : ℂ))⁻¹) := by
    simpa [sub_eq_add_neg] using
      (hasSum_geometric_of_norm_lt_one hUpperRatio).mul_left upperRootFactor
  have hLowerSum :
      HasSum (fun n : ℕ => lowerRootFactor * (-lowerRootFactor * (x : ℂ)) ^ n)
        (lowerRootFactor * (1 + lowerRootFactor * (x : ℂ))⁻¹) := by
    simpa [sub_eq_add_neg] using
      (hasSum_geometric_of_norm_lt_one hLowerRatio).mul_left lowerRootFactor
  have hsumTerms :
      HasSum
        (fun n : ℕ =>
          upperRootFactor * (-upperRootFactor * (x : ℂ)) ^ n -
            lowerRootFactor * (-lowerRootFactor * (x : ℂ)) ^ n)
        (upperRootFactor * (1 + upperRootFactor * (x : ℂ))⁻¹ -
          lowerRootFactor * (1 + lowerRootFactor * (x : ℂ))⁻¹) :=
    hUpperSum.sub hLowerSum
  have hterm : ∀ n : ℕ,
      complexCoefficientTerm x n =
        upperRootFactor * (-upperRootFactor * (x : ℂ)) ^ n -
          lowerRootFactor * (-lowerRootFactor * (x : ℂ)) ^ n := by
    intro n
    simp [complexCoefficientTerm, pow_succ]
    ring
  rw [hgeometricForm x]
  congr 1
  rw [← hsumTerms.tsum_eq]
  apply tsum_congr
  intro n
  exact (hterm n).symm

theorem gap4
    (hseries :
      ∀ x : ℝ, |x| < 1 →
        ((1 / (1 + x + x ^ 2) : ℝ) : ℂ) =
          1 / (Complex.I * Real.sqrt 3) *
            (∑' n, complexCoefficientTerm x n)) :
    ∀ n : ℕ,
      (-1 : ℂ) ^ n *
          (upperRootFactor ^ (n + 1) - lowerRootFactor ^ (n + 1)) =
        2 * Complex.I *
          (Real.sin ((2 * (n + 1) : ℝ) / 3 * Real.pi) : ℂ) := by
  intro n
  rcases rootFactor_facts with
    ⟨hsum, hprod, hdiff, hupper3, hlower3, hnormUpper, hnormLower⟩
  let P : ℕ → Prop := fun k =>
    (-1 : ℂ) ^ k *
        (upperRootFactor ^ (k + 1) - lowerRootFactor ^ (k + 1)) =
      2 * Complex.I *
        (Real.sin ((2 * (k + 1) : ℝ) / 3 * Real.pi) : ℂ)
  have hsum' : upperRootFactor + lowerRootFactor = 1 := by
    simpa [add_comm] using hsum
  have p0 : P 0 := by
    dsimp [P]
    have hangle0 :
        2 * (((0 : ℕ) : ℝ) + 1) / 3 * Real.pi =
          Real.pi - Real.pi / 3 := by
      norm_num
      ring
    rw [hangle0, Real.sin_pi_sub, Real.sin_pi_div_three]
    simp only [pow_zero, one_mul, pow_one]
    rw [hdiff]
    norm_num <;> ring
  have p1 : P 1 := by
    dsimp [P]
    have hangle1 :
        2 * (((1 : ℕ) : ℝ) + 1) / 3 * Real.pi =
          Real.pi / 3 + Real.pi := by
      norm_num
      ring
    rw [hangle1, Real.sin_add_pi, Real.sin_pi_div_three]
    simp only [pow_one]
    rw [show upperRootFactor ^ 2 - lowerRootFactor ^ 2 =
      (upperRootFactor - lowerRootFactor) *
        (upperRootFactor + lowerRootFactor) by ring]
    rw [hdiff, hsum']
    norm_num <;> ring
  have p2 : P 2 := by
    norm_num [P, hupper3, hlower3, Real.sin_two_pi]
  have hperiod : ∀ k : ℕ, P (k + 3) ↔ P k := by
    intro k
    dsimp [P]
    have hexp : k + 3 + 1 = (k + 1) + 3 := by omega
    have hangle :
        2 * (((k + 3 : ℕ) : ℝ) + 1) / 3 * Real.pi =
          2 * ((k : ℝ) + 1) / 3 * Real.pi + 2 * Real.pi := by
      norm_num [Nat.cast_add]
      ring
    rw [hexp, hangle, Real.sin_add_two_pi]
    simp [pow_add, hupper3, hlower3]
    ring
  change P n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases hn0 : n = 0
      · simpa [hn0] using p0
      by_cases hn1 : n = 1
      · simpa [hn1] using p1
      by_cases hn2 : n = 2
      · simpa [hn2] using p2
      have hn3 : 3 ≤ n := by omega
      have hlt : n - 3 < n := by omega
      have heq : (n - 3) + 3 = n := by omega
      rw [← heq]
      exact (hperiod (n - 3)).2 (ih (n - 3) hlt)

theorem gap5
    (hseries :
      ∀ x : ℝ, |x| < 1 →
        ((1 / (1 + x + x ^ 2) : ℝ) : ℂ) =
          1 / (Complex.I * Real.sqrt 3) *
            (∑' n, complexCoefficientTerm x n))
    (hcoeff :
      ∀ n : ℕ,
        (-1 : ℂ) ^ n *
            (upperRootFactor ^ (n + 1) - lowerRootFactor ^ (n + 1)) =
          2 * Complex.I *
            (Real.sin ((2 * (n + 1) : ℝ) / 3 * Real.pi) : ℂ)) :
    ∀ x : ℝ, |x| < 1 →
      1 / (1 + x + x ^ 2) =
        2 / Real.sqrt 3 * (∑' n, realCoefficientTerm x n) := by
  intro x hx
  have hgeomAbs : Summable (fun n : ℕ => |x| ^ n) := by
    apply summable_geometric_of_norm_lt_one
    simpa [Real.norm_eq_abs] using hx
  have hrealSummable : Summable (fun n : ℕ => realCoefficientTerm x n) := by
    apply Summable.of_norm_bounded hgeomAbs
    intro n
    calc
      ‖realCoefficientTerm x n‖ =
          |x| ^ n * |Real.sin ((2 * (n + 1) : ℝ) / 3 * Real.pi)| := by
            simp [realCoefficientTerm, Real.norm_eq_abs, abs_mul, abs_pow]
      _ ≤ |x| ^ n * 1 :=
        mul_le_mul_of_nonneg_left (Real.abs_sin_le_one _)
          (pow_nonneg (abs_nonneg x) n)
      _ = |x| ^ n := by simp
  have hterm : ∀ n : ℕ,
      complexCoefficientTerm x n =
        (2 * Complex.I) * (realCoefficientTerm x n : ℂ) := by
    intro n
    rw [complexCoefficientTerm, hcoeff n]
    simp [realCoefficientTerm]
    ring
  have hcast :
      ((∑' n, realCoefficientTerm x n : ℝ) : ℂ) =
        ∑' n, (realCoefficientTerm x n : ℂ) := by
    simpa using Complex.ofRealCLM.map_tsum hrealSummable
  have hcomplexTsum :
      (∑' n, complexCoefficientTerm x n) =
        (2 * Complex.I) * ((∑' n, realCoefficientTerm x n : ℝ) : ℂ) := by
    calc
      (∑' n, complexCoefficientTerm x n) =
          ∑' n, (2 * Complex.I) * (realCoefficientTerm x n : ℂ) :=
        tsum_congr hterm
      _ = (2 * Complex.I) * ∑' n, (realCoefficientTerm x n : ℂ) :=
        tsum_mul_left
      _ = (2 * Complex.I) * ((∑' n, realCoefficientTerm x n : ℝ) : ℂ) := by
        rw [← hcast]
  have hsqrt : Real.sqrt 3 ≠ 0 := by positivity
  have hsqrtC : (Real.sqrt 3 : ℂ) ≠ 0 := by
    intro h
    apply hsqrt
    exact Complex.ofReal_injective h
  have hI : (Complex.I : ℂ) ^ 2 = -1 := by norm_num
  apply Complex.ofReal_injective
  calc
    ((1 / (1 + x + x ^ 2) : ℝ) : ℂ) =
        1 / (Complex.I * Real.sqrt 3) *
          (∑' n, complexCoefficientTerm x n) := hseries x hx
    _ = 1 / (Complex.I * Real.sqrt 3) *
        ((2 * Complex.I) * ((∑' n, realCoefficientTerm x n : ℝ) : ℂ)) := by
          rw [hcomplexTsum]
    _ = ((2 / Real.sqrt 3 * (∑' n, realCoefficientTerm x n) : ℝ) : ℂ) := by
      norm_num
      field_simp [hsqrt, hsqrtC]
      rw [hI]
      ring

end

end ProofGap.Exercise2862
