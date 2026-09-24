import ProofGapLean.Prelude.Analysis
import Mathlib.Data.Complex.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

namespace ProofGap.Exercise2864

noncomputable section

def upperUnit (α : ℝ) : ℂ :=
  (Real.cos α : ℂ) + Complex.I * Real.sin α

def lowerUnit (α : ℝ) : ℂ :=
  (Real.cos α : ℂ) - Complex.I * Real.sin α

def upperSineGeometricTerm (x α : ℝ) (n : ℕ) : ℂ :=
  (x : ℂ) ^ n * upperUnit α ^ (n + 1)

def lowerSineGeometricTerm (x α : ℝ) (n : ℕ) : ℂ :=
  (x : ℂ) ^ n * lowerUnit α ^ (n + 1)

def pairedSineTerm (x α : ℝ) (n : ℕ) : ℂ :=
  (x : ℂ) ^ n *
    (-(Real.cos ((n + 1) * α) : ℂ) -
      Complex.I * Real.sin ((n + 1) * α) +
      (Real.cos ((n + 1) * α) : ℂ) -
      Complex.I * Real.sin ((n + 1) * α))

def shiftedSineTerm (x α : ℝ) (n : ℕ) : ℝ :=
  x ^ (n + 1) * Real.sin ((n + 1) * α)

def unshiftedSineTerm (x α : ℝ) (n : ℕ) : ℝ :=
  x ^ n * Real.sin (n * α)

private theorem upper_mul_lower (α : ℝ) :
    upperUnit α * lowerUnit α = 1 := by
  unfold upperUnit lowerUnit
  calc
    ((Real.cos α : ℂ) + Complex.I * Real.sin α) *
          ((Real.cos α : ℂ) - Complex.I * Real.sin α) =
        (Real.cos α : ℂ) ^ 2 -
          (Complex.I * (Real.sin α : ℂ)) ^ 2 := by ring
    _ = (((Real.cos α) ^ 2 + (Real.sin α) ^ 2 : ℝ) : ℂ) := by
      rw [mul_pow, pow_two Complex.I, Complex.I_mul_I]
      norm_num
    _ = 1 := by
      rw [add_comm, Real.sin_sq_add_cos_sq]
      norm_num

private theorem complex_denominator_factor (x α : ℝ) :
    ((x : ℂ) - lowerUnit α) * ((x : ℂ) - upperUnit α) =
      ((1 - 2 * x * Real.cos α + x ^ 2 : ℝ) : ℂ) := by
  let X : ℂ := (x : ℂ)
  have hsum : lowerUnit α + upperUnit α =
      2 * (Real.cos α : ℂ) := by
    unfold lowerUnit upperUnit
    ring
  have hprod : lowerUnit α * upperUnit α = 1 := by
    rw [mul_comm]
    exact upper_mul_lower α
  calc
    (X - lowerUnit α) * (X - upperUnit α) =
        X ^ 2 - X * (lowerUnit α + upperUnit α) +
          lowerUnit α * upperUnit α := by ring
    _ = X ^ 2 - X * (2 * (Real.cos α : ℂ)) + 1 := by
      rw [hsum, hprod]
    _ = ((1 - 2 * x * Real.cos α + x ^ 2 : ℝ) : ℂ) := by
      dsimp [X]
      norm_cast <;> ring

private theorem lower_sub_upper (α : ℝ) :
    lowerUnit α - upperUnit α =
      -2 * Complex.I * (Real.sin α : ℂ) := by
  unfold lowerUnit upperUnit
  ring

private theorem norm_upperUnit (α : ℝ) : ‖upperUnit α‖ = 1 := by
  rw [Complex.norm_def]
  have hsq : Complex.normSq (upperUnit α) = 1 := by
    rw [Complex.normSq_apply]
    have hre : (upperUnit α).re = Real.cos α := by
      norm_num only [upperUnit, Complex.add_re, Complex.mul_re,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I]
      ring
    have him : (upperUnit α).im = Real.sin α := by
      norm_num only [upperUnit, Complex.add_im, Complex.mul_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I]
      ring
    rw [hre, him]
    calc
      Real.cos α * Real.cos α + Real.sin α * Real.sin α =
          Real.sin α ^ 2 + Real.cos α ^ 2 := by ring
      _ = 1 := Real.sin_sq_add_cos_sq α
  rw [hsq]
  norm_num

private theorem norm_lowerUnit (α : ℝ) : ‖lowerUnit α‖ = 1 := by
  rw [Complex.norm_def]
  have hsq : Complex.normSq (lowerUnit α) = 1 := by
    rw [Complex.normSq_apply]
    have hre : (lowerUnit α).re = Real.cos α := by
      norm_num only [lowerUnit, Complex.sub_re, Complex.mul_re,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I]
      ring
    have him : (lowerUnit α).im = -Real.sin α := by
      norm_num only [lowerUnit, Complex.sub_im, Complex.mul_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I]
      ring
    rw [hre, him]
    calc
      Real.cos α * Real.cos α + (-Real.sin α) * (-Real.sin α) =
          Real.sin α ^ 2 + Real.cos α ^ 2 := by ring
      _ = 1 := Real.sin_sq_add_cos_sq α
  rw [hsq]
  norm_num

private theorem upperUnit_pow (α : ℝ) : ∀ n : ℕ,
    upperUnit α ^ n =
      (Real.cos ((n : ℝ) * α) : ℂ) +
        Complex.I * Real.sin ((n : ℝ) * α)
  | 0 => by norm_num [upperUnit]
  | n + 1 => by
      rw [pow_succ, upperUnit_pow]
      have hang : (((n + 1 : ℕ) : ℝ) * α) = (n : ℝ) * α + α := by
        norm_num only [Nat.cast_add, Nat.cast_one]
        ring
      rw [hang, Real.cos_add, Real.sin_add]
      apply Complex.ext <;> simp [upperUnit] <;> ring

private theorem lowerUnit_pow (α : ℝ) : ∀ n : ℕ,
    lowerUnit α ^ n =
      (Real.cos ((n : ℝ) * α) : ℂ) -
        Complex.I * Real.sin ((n : ℝ) * α)
  | 0 => by norm_num [lowerUnit]
  | n + 1 => by
      rw [pow_succ, lowerUnit_pow]
      have hang : (((n + 1 : ℕ) : ℝ) * α) = (n : ℝ) * α + α := by
        norm_num only [Nat.cast_add, Nat.cast_one]
        ring
      rw [hang, Real.cos_add, Real.sin_add]
      apply Complex.ext <;> simp [lowerUnit] <;> ring

private theorem hasSum_upper_terms (x α : ℝ) (hx : |x| < 1) :
    HasSum (upperSineGeometricTerm x α)
      (upperUnit α / (1 - (x : ℂ) * upperUnit α)) := by
  have hr : ‖(x : ℂ) * upperUnit α‖ < 1 := by
    rw [norm_mul, norm_upperUnit]
    simpa using hx
  have hg := (hasSum_geometric_of_norm_lt_one hr).mul_left (upperUnit α)
  convert hg using 1
  funext n
  simp only [upperSineGeometricTerm, mul_pow, pow_succ]
  ring

private theorem hasSum_lower_terms (x α : ℝ) (hx : |x| < 1) :
    HasSum (lowerSineGeometricTerm x α)
      (lowerUnit α / (1 - (x : ℂ) * lowerUnit α)) := by
  have hr : ‖(x : ℂ) * lowerUnit α‖ < 1 := by
    rw [norm_mul, norm_lowerUnit]
    simpa using hx
  have hg := (hasSum_geometric_of_norm_lt_one hr).mul_left (lowerUnit α)
  convert hg using 1
  funext n
  simp only [lowerSineGeometricTerm, mul_pow, pow_succ]
  ring

private theorem paired_term_eq (x α : ℝ) (n : ℕ) :
    pairedSineTerm x α n =
      -upperSineGeometricTerm x α n + lowerSineGeometricTerm x α n := by
  unfold upperSineGeometricTerm lowerSineGeometricTerm
  have hu := upperUnit_pow α (n + 1)
  have hl := lowerUnit_pow α (n + 1)
  rw [hu, hl]
  unfold pairedSineTerm
  norm_num only [Nat.cast_add, Nat.cast_one]
  ring

private theorem paired_term_simplified (x α : ℝ) (n : ℕ) :
    pairedSineTerm x α n =
      -2 * Complex.I *
        ((x : ℂ) ^ n * (Real.sin ((n + 1) * α) : ℂ)) := by
  unfold pairedSineTerm
  norm_num only [Nat.cast_add, Nat.cast_one]
  ring

private theorem scaled_paired_term (x α : ℝ) (n : ℕ) :
    Complex.I * (x : ℂ) / 2 * pairedSineTerm x α n =
      (shiftedSineTerm x α n : ℂ) := by
  rw [paired_term_simplified]
  calc
    Complex.I * (x : ℂ) / 2 *
          (-2 * Complex.I *
            ((x : ℂ) ^ n * (Real.sin ((n + 1) * α) : ℂ))) =
        -(Complex.I * Complex.I) * (x : ℂ) *
          ((x : ℂ) ^ n * (Real.sin ((n + 1) * α) : ℂ)) := by ring
    _ = (x : ℂ) ^ (n + 1) *
          (Real.sin ((n + 1) * α) : ℂ) := by
      rw [Complex.I_mul_I, pow_succ]
      ring
    _ = (shiftedSineTerm x α n : ℂ) := by
      unfold shiftedSineTerm
      norm_cast

private theorem summable_unshifted_terms (x α : ℝ) (hx : |x| < 1) :
    Summable (unshiftedSineTerm x α) := by
  have hr : ‖(|x| : ℝ)‖ < 1 := by
    simpa using hx
  have hg : Summable (fun n : ℕ => (|x| : ℝ) ^ n) :=
    (hasSum_geometric_of_norm_lt_one hr).summable
  refine Summable.of_norm_bounded hg ?_
  intro n
  simp only [unshiftedSineTerm, Real.norm_eq_abs, abs_mul, abs_pow,
    abs_abs]
  calc
    |x| ^ n * |Real.sin ((n : ℝ) * α)| ≤ |x| ^ n * 1 :=
      mul_le_mul_of_nonneg_left (Real.abs_sin_le_one _)
        (pow_nonneg (abs_nonneg x) n)
    _ = |x| ^ n := mul_one _

theorem gap1 :
    ∀ x α : ℝ, 1 - 2 * x * Real.cos α + x ^ 2 ≠ 0 →
      (((x * Real.sin α) / (1 - 2 * x * Real.cos α + x ^ 2) : ℝ) : ℂ) =
        Complex.I * (x : ℂ) / 2 *
          (1 / ((x : ℂ) - lowerUnit α) -
            1 / ((x : ℂ) - upperUnit α)) := by
  intro x α hden
  let X : ℂ := (x : ℂ)
  have hc : (((1 - 2 * x * Real.cos α + x ^ 2 : ℝ) : ℂ)) ≠ 0 := by
    norm_cast
  have hm : (X - lowerUnit α) * (X - upperUnit α) ≠ 0 := by
    rw [complex_denominator_factor]
    exact hc
  have hlow : X - lowerUnit α ≠ 0 := (mul_ne_zero_iff.mp hm).1
  have hupp : X - upperUnit α ≠ 0 := (mul_ne_zero_iff.mp hm).2
  have hnum : Complex.I * X / 2 *
      (-2 * Complex.I * (Real.sin α : ℂ)) =
      ((x * Real.sin α : ℝ) : ℂ) := by
    calc
      Complex.I * X / 2 * (-2 * Complex.I * (Real.sin α : ℂ)) =
          -(Complex.I * Complex.I) * X * (Real.sin α : ℂ) := by ring
      _ = X * (Real.sin α : ℂ) := by
        rw [Complex.I_mul_I]
        ring
      _ = ((x * Real.sin α : ℝ) : ℂ) := by
        dsimp [X]
        norm_cast
  symm
  calc
    Complex.I * X / 2 *
          (1 / (X - lowerUnit α) - 1 / (X - upperUnit α)) =
        Complex.I * X / 2 *
          ((lowerUnit α - upperUnit α) /
            ((X - lowerUnit α) * (X - upperUnit α))) := by
      field_simp [hlow, hupp]
      ring
    _ = Complex.I * X / 2 *
          ((-2 * Complex.I * (Real.sin α : ℂ)) /
            (((1 - 2 * x * Real.cos α + x ^ 2 : ℝ) : ℂ))) := by
      rw [lower_sub_upper, complex_denominator_factor]
    _ = (Complex.I * X / 2 *
          (-2 * Complex.I * (Real.sin α : ℂ))) /
            (((1 - 2 * x * Real.cos α + x ^ 2 : ℝ) : ℂ)) := by ring
    _ = (((x * Real.sin α : ℝ) : ℂ)) /
            (((1 - 2 * x * Real.cos α + x ^ 2 : ℝ) : ℂ)) := by
      rw [hnum]
    _ = (((x * Real.sin α) /
          (1 - 2 * x * Real.cos α + x ^ 2) : ℝ) : ℂ) := by
      norm_cast

theorem gap2
    (hpartial :
      ∀ x α : ℝ, 1 - 2 * x * Real.cos α + x ^ 2 ≠ 0 →
        (((x * Real.sin α) / (1 - 2 * x * Real.cos α + x ^ 2) : ℝ) : ℂ) =
          Complex.I * (x : ℂ) / 2 *
            (1 / ((x : ℂ) - lowerUnit α) -
              1 / ((x : ℂ) - upperUnit α))) :
    ∀ x α : ℝ, 1 - 2 * x * Real.cos α + x ^ 2 ≠ 0 →
      (((x * Real.sin α) / (1 - 2 * x * Real.cos α + x ^ 2) : ℝ) : ℂ) =
        Complex.I * (x : ℂ) / 2 *
          (-(upperUnit α / (1 - (x : ℂ) * upperUnit α)) +
            lowerUnit α / (1 - (x : ℂ) * lowerUnit α)) := by
  intro x α hden
  let X : ℂ := (x : ℂ)
  have hc : (((1 - 2 * x * Real.cos α + x ^ 2 : ℝ) : ℂ)) ≠ 0 := by
    norm_cast
  have hm : (X - lowerUnit α) * (X - upperUnit α) ≠ 0 := by
    rw [complex_denominator_factor]
    exact hc
  have hlow : X - lowerUnit α ≠ 0 := (mul_ne_zero_iff.mp hm).1
  have hupp : X - upperUnit α ≠ 0 := (mul_ne_zero_iff.mp hm).2
  have hu0 : upperUnit α ≠ 0 := by
    intro hz
    have h := upper_mul_lower α
    rw [hz, zero_mul] at h
    exact zero_ne_one h
  have hl0 : lowerUnit α ≠ 0 := by
    intro hz
    have h := upper_mul_lower α
    rw [hz, mul_zero] at h
    exact zero_ne_one h
  have hdu_id : 1 - X * upperUnit α =
      (-upperUnit α) * (X - lowerUnit α) := by
    rw [← upper_mul_lower α]
    ring
  have hdl_id : 1 - X * lowerUnit α =
      (-lowerUnit α) * (X - upperUnit α) := by
    rw [← upper_mul_lower α]
    ring
  have hdu : 1 - X * upperUnit α ≠ 0 := by
    rw [hdu_id]
    exact mul_ne_zero (neg_ne_zero.mpr hu0) hlow
  have hdl : 1 - X * lowerUnit α ≠ 0 := by
    rw [hdl_id]
    exact mul_ne_zero (neg_ne_zero.mpr hl0) hupp
  have heqU : 1 / (X - lowerUnit α) =
      -(upperUnit α / (1 - X * upperUnit α)) := by
    field_simp [hlow, hdu]
    rw [← upper_mul_lower α]
    ring
  have heqL : 1 / (X - upperUnit α) =
      -(lowerUnit α / (1 - X * lowerUnit α)) := by
    field_simp [hupp, hdl]
    rw [← upper_mul_lower α]
    ring
  rw [hpartial x α hden]
  change Complex.I * X / 2 *
      (1 / (X - lowerUnit α) - 1 / (X - upperUnit α)) = _
  rw [heqU, heqL]
  ring

theorem gap3
    (hgeometricForm :
      ∀ x α : ℝ, 1 - 2 * x * Real.cos α + x ^ 2 ≠ 0 →
        (((x * Real.sin α) / (1 - 2 * x * Real.cos α + x ^ 2) : ℝ) : ℂ) =
          Complex.I * (x : ℂ) / 2 *
            (-(upperUnit α / (1 - (x : ℂ) * upperUnit α)) +
              lowerUnit α / (1 - (x : ℂ) * lowerUnit α))) :
    ∀ x α : ℝ, |x| < 1 →
      (((x * Real.sin α) / (1 - 2 * x * Real.cos α + x ^ 2) : ℝ) : ℂ) =
        Complex.I * (x : ℂ) / 2 *
          (-(∑' n, upperSineGeometricTerm x α n) +
            (∑' n, lowerSineGeometricTerm x α n)) := by
  intro x α hx
  have hx' := abs_lt.mp hx
  have hdenpos : 0 < 1 - 2 * x * Real.cos α + x ^ 2 := by
    by_cases hx0 : 0 ≤ x
    · have hc : 0 ≤ 1 - Real.cos α :=
        sub_nonneg.mpr (Real.cos_le_one α)
      have hmul : 0 ≤ x * (1 - Real.cos α) := mul_nonneg hx0 hc
      have hsq : 0 < (1 - x) ^ 2 :=
        sq_pos_of_pos (sub_pos.mpr hx'.2)
      nlinarith
    · have hxnonpos : x ≤ 0 := le_of_not_ge hx0
      have hc : 0 ≤ Real.cos α + 1 := by
        linarith [Real.neg_one_le_cos α]
      have hmul : x * (Real.cos α + 1) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg hxnonpos hc
      have hsq : 0 < (1 + x) ^ 2 :=
        sq_pos_of_pos (by linarith [hx'.1])
      nlinarith
  rw [hgeometricForm x α (ne_of_gt hdenpos)]
  rw [(hasSum_upper_terms x α hx).tsum_eq,
    (hasSum_lower_terms x α hx).tsum_eq]

theorem gap4
    (hcomplexSeries :
      ∀ x α : ℝ, |x| < 1 →
        (((x * Real.sin α) / (1 - 2 * x * Real.cos α + x ^ 2) : ℝ) : ℂ) =
          Complex.I * (x : ℂ) / 2 *
            (-(∑' n, upperSineGeometricTerm x α n) +
              (∑' n, lowerSineGeometricTerm x α n))) :
    ∀ x α : ℝ, |x| < 1 →
      (((x * Real.sin α) / (1 - 2 * x * Real.cos α + x ^ 2) : ℝ) : ℂ) =
        Complex.I * (x : ℂ) / 2 * (∑' n, pairedSineTerm x α n) := by
  intro x α hx
  rw [hcomplexSeries x α hx]
  congr 1
  have hu := hasSum_upper_terms x α hx
  have hl := hasSum_lower_terms x α hx
  have hterms :
      (fun n : ℕ =>
        -upperSineGeometricTerm x α n +
          lowerSineGeometricTerm x α n) =
        pairedSineTerm x α := by
    funext n
    exact (paired_term_eq x α n).symm
  have hp : HasSum
      (fun n : ℕ =>
        -upperSineGeometricTerm x α n +
          lowerSineGeometricTerm x α n)
      (-(upperUnit α / (1 - (x : ℂ) * upperUnit α)) +
        lowerUnit α / (1 - (x : ℂ) * lowerUnit α)) :=
    hu.neg.add hl
  rw [hterms] at hp
  calc
    -(∑' n, upperSineGeometricTerm x α n) +
          ∑' n, lowerSineGeometricTerm x α n =
        -(upperUnit α / (1 - (x : ℂ) * upperUnit α)) +
          lowerUnit α / (1 - (x : ℂ) * lowerUnit α) := by
      rw [hu.tsum_eq, hl.tsum_eq]
    _ = ∑' n, pairedSineTerm x α n := hp.tsum_eq.symm

theorem gap5
    (hpaired :
      ∀ x α : ℝ, |x| < 1 →
        (((x * Real.sin α) / (1 - 2 * x * Real.cos α + x ^ 2) : ℝ) : ℂ) =
          Complex.I * (x : ℂ) / 2 * (∑' n, pairedSineTerm x α n)) :
    ∀ x α : ℝ, |x| < 1 →
      (x * Real.sin α) / (1 - 2 * x * Real.cos α + x ^ 2) =
        ∑' n, shiftedSineTerm x α n := by
  intro x α hx
  have hu := hasSum_upper_terms x α hx
  have hl := hasSum_lower_terms x α hx
  have hterms :
      (fun n : ℕ =>
        -upperSineGeometricTerm x α n +
          lowerSineGeometricTerm x α n) =
        pairedSineTerm x α := by
    funext n
    exact (paired_term_eq x α n).symm
  have hp : HasSum
      (fun n : ℕ =>
        -upperSineGeometricTerm x α n +
          lowerSineGeometricTerm x α n)
      (-(upperUnit α / (1 - (x : ℂ) * upperUnit α)) +
        lowerUnit α / (1 - (x : ℂ) * lowerUnit α)) :=
    hu.neg.add hl
  rw [hterms] at hp
  let c : ℂ := Complex.I * (x : ℂ) / 2
  have hs := hp.mul_left c
  have hsum : c *
      (-(upperUnit α / (1 - (x : ℂ) * upperUnit α)) +
        lowerUnit α / (1 - (x : ℂ) * lowerUnit α)) =
      (((x * Real.sin α) /
        (1 - 2 * x * Real.cos α + x ^ 2) : ℝ) : ℂ) := by
    calc
      c * (-(upperUnit α / (1 - (x : ℂ) * upperUnit α)) +
          lowerUnit α / (1 - (x : ℂ) * lowerUnit α)) =
          c * (∑' n, pairedSineTerm x α n) := by
            rw [hp.tsum_eq]
      _ = (((x * Real.sin α) /
          (1 - 2 * x * Real.cos α + x ^ 2) : ℝ) : ℂ) := by
            simpa [c] using (hpaired x α hx).symm
  have hs' : HasSum (fun n => c * pairedSineTerm x α n)
      (((x * Real.sin α) /
        (1 - 2 * x * Real.cos α + x ^ 2) : ℝ) : ℂ) := by
    rw [hsum] at hs
    exact hs
  have hc : HasSum (fun n => (shiftedSineTerm x α n : ℂ))
      (((x * Real.sin α) /
        (1 - 2 * x * Real.cos α + x ^ 2) : ℝ) : ℂ) := by
    simpa only [c, scaled_paired_term] using hs'
  have hr : HasSum (shiftedSineTerm x α)
      ((x * Real.sin α) /
        (1 - 2 * x * Real.cos α + x ^ 2)) := by
    unfold HasSum at hc ⊢
    have ht := Complex.continuous_re.continuousAt.tendsto.comp hc
    have hfun :
        (Complex.re ∘ fun s : Finset ℕ =>
          ∑ n ∈ s, (shiftedSineTerm x α n : ℂ)) =
        (fun s : Finset ℕ => ∑ n ∈ s, shiftedSineTerm x α n) := by
      funext s
      induction s using Finset.induction_on with
      | empty => simp [Function.comp_apply]
      | @insert a s ha ih =>
          simp [Function.comp_apply, ha, ih]
    have hlim :
        ((((x * Real.sin α) /
          (1 - 2 * x * Real.cos α + x ^ 2) : ℝ) : ℂ)).re =
          (x * Real.sin α) /
            (1 - 2 * x * Real.cos α + x ^ 2) := by
      simp only [Complex.ofReal_re]
    rw [hfun, hlim] at ht
    exact ht
  exact hr.tsum_eq.symm

theorem gap6
    (hshifted :
      ∀ x α : ℝ, |x| < 1 →
        (x * Real.sin α) / (1 - 2 * x * Real.cos α + x ^ 2) =
          ∑' n, shiftedSineTerm x α n) :
    ∀ x α : ℝ, |x| < 1 →
      (∑' n, shiftedSineTerm x α n) =
        ∑' n, unshiftedSineTerm x α n := by
  intro x α hx
  have hs := summable_unshifted_terms x α hx
  have htail :
      unshiftedSineTerm x α 0 +
          ∑' n, unshiftedSineTerm x α (n + 1) =
        ∑' n, unshiftedSineTerm x α n := by
    simpa [Nat.add_comm] using hs.sum_add_tsum_nat_add 1
  calc
    (∑' n, shiftedSineTerm x α n) =
        ∑' n, unshiftedSineTerm x α (n + 1) := by
      apply tsum_congr
      intro n
      simp only [shiftedSineTerm, unshiftedSineTerm, Nat.cast_add,
        Nat.cast_one]
    _ = ∑' n, unshiftedSineTerm x α n := by
      simpa [unshiftedSineTerm] using htail

theorem gap7
    (hshifted :
      ∀ x α : ℝ, |x| < 1 →
        (x * Real.sin α) / (1 - 2 * x * Real.cos α + x ^ 2) =
          ∑' n, shiftedSineTerm x α n)
    (hreindex :
      ∀ x α : ℝ, |x| < 1 →
        (∑' n, shiftedSineTerm x α n) =
          ∑' n, unshiftedSineTerm x α n) :
    ∀ x α : ℝ, |x| < 1 →
      (x * Real.sin α) / (1 - 2 * x * Real.cos α + x ^ 2) =
        ∑' n, unshiftedSineTerm x α n := by
  intro x α hx
  calc
    (x * Real.sin α) / (1 - 2 * x * Real.cos α + x ^ 2) =
        ∑' n, shiftedSineTerm x α n := hshifted x α hx
    _ = ∑' n, unshiftedSineTerm x α n := hreindex x α hx

end

end ProofGap.Exercise2864
