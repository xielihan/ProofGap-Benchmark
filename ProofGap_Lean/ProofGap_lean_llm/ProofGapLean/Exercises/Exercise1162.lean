import ProofGapLean.Prelude.Elementary
import ProofGapLean.Prelude.Finite
import ProofGapLean.Prelude.Discrete
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.Neighborhoods
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

namespace ProofGap.Exercise1162

open scoped BigOperators

noncomputable section

def nthDeriv : ℕ → (ℝ → ℝ) → ℝ → ℝ
  | 0, f => f
  | n + 1, f => deriv (nthDeriv n f)

def y (x : ℝ) : ℝ := Real.exp x / x
def recip (x : ℝ) : ℝ := 1 / x
def permCoeff (i : ℕ) : ℕ :=
  Nat.factorial 10 / Nat.factorial (10 - i)
def fallingProduct (i : ℕ) : ℕ := ∏ k ∈ Finset.range i, (10 - k)

def leibniz10 (x : ℝ) : ℝ :=
  ∑ i ∈ Finset.range 11,
    (Nat.choose 10 i : ℝ) * Real.exp x * nthDeriv (10 - i) recip x

def final10 (x : ℝ) : ℝ :=
  Real.exp x *
    ∑ i ∈ Finset.range 11,
      (-1 : ℝ) ^ i * (permCoeff i : ℝ) / x ^ (i + 1)

private def closedForm (n : ℕ) (x : ℝ) : ℝ :=
  Real.exp x *
    ∑ i ∈ Finset.range (n + 1),
      (-1 : ℝ) ^ i *
        ((Nat.factorial n / Nat.factorial (n - i) : ℕ) : ℝ) /
          x ^ (i + 1)

private def closedFormSlope (n : ℕ) (x : ℝ) : ℝ :=
  Real.exp x *
      (∑ i ∈ Finset.range (n + 1),
        (-1 : ℝ) ^ i *
          ((Nat.factorial n / Nat.factorial (n - i) : ℕ) : ℝ) /
            x ^ (i + 1)) +
    Real.exp x *
      (∑ i ∈ Finset.range (n + 1),
        -((i + 1 : ℕ) : ℝ) *
            ((-1 : ℝ) ^ i *
              ((Nat.factorial n / Nat.factorial (n - i) : ℕ) : ℝ)) /
          x ^ (i + 2))

private theorem hasDerivAt_const_div_pow
    (c : ℝ) (n : ℕ) (x : ℝ) (hx : x ≠ 0) :
    HasDerivAt (fun z : ℝ => c / z ^ (n + 1))
      (-((n + 1 : ℕ) : ℝ) * c / x ^ (n + 2)) x := by
  have h :=
    (((hasDerivAt_id x).pow (n + 1)).inv
      (pow_ne_zero (n + 1) hx)).const_mul c
  convert h using 1 <;>
    simp [div_eq_mul_inv, pow_succ] <;>
    field_simp [hx] <;>
    ring

private theorem closedForm_raw_hasDerivAt
    (n : ℕ) (x : ℝ) (hx : x ≠ 0) :
    HasDerivAt (closedForm n) (closedFormSlope n x) x := by
  unfold closedForm closedFormSlope
  have hs0 :
      HasDerivAt
        (∑ i ∈ Finset.range (n + 1),
          fun z : ℝ =>
            (-1 : ℝ) ^ i *
              ((Nat.factorial n / Nat.factorial (n - i) : ℕ) : ℝ) /
                z ^ (i + 1))
        (∑ i ∈ Finset.range (n + 1),
          -((i + 1 : ℕ) : ℝ) *
              ((-1 : ℝ) ^ i *
                ((Nat.factorial n / Nat.factorial (n - i) : ℕ) : ℝ)) /
            x ^ (i + 2)) x := by
    apply HasDerivAt.sum
    intro i hi
    exact hasDerivAt_const_div_pow
      ((-1 : ℝ) ^ i *
        ((Nat.factorial n / Nat.factorial (n - i) : ℕ) : ℝ))
      i x hx
  have hsumfun :
      (∑ i ∈ Finset.range (n + 1),
        fun z : ℝ =>
          (-1 : ℝ) ^ i *
            ((Nat.factorial n / Nat.factorial (n - i) : ℕ) : ℝ) /
              z ^ (i + 1)) =
        (fun z : ℝ =>
          ∑ i ∈ Finset.range (n + 1),
            (-1 : ℝ) ^ i *
              ((Nat.factorial n / Nat.factorial (n - i) : ℕ) : ℝ) /
                z ^ (i + 1)) := by
    funext z
    simp only [Finset.sum_apply]
  rw [hsumfun] at hs0
  simpa only using (Real.hasDerivAt_exp x).mul hs0

private theorem closedFormSlope_eq_succ_0 (x : ℝ) (hx : x ≠ 0) :
    closedFormSlope 0 x = closedForm 1 x := by
  norm_num [closedFormSlope, closedForm, Finset.sum_range_succ] <;>
    field_simp [hx] <;> ring

private theorem closedFormSlope_eq_succ_1 (x : ℝ) (hx : x ≠ 0) :
    closedFormSlope 1 x = closedForm 2 x := by
  norm_num [closedFormSlope, closedForm, Finset.sum_range_succ] <;>
    field_simp [hx] <;> ring

private theorem closedFormSlope_eq_succ_2 (x : ℝ) (hx : x ≠ 0) :
    closedFormSlope 2 x = closedForm 3 x := by
  norm_num [closedFormSlope, closedForm, Finset.sum_range_succ] <;>
    field_simp [hx] <;> ring

private theorem closedFormSlope_eq_succ_3 (x : ℝ) (hx : x ≠ 0) :
    closedFormSlope 3 x = closedForm 4 x := by
  norm_num [closedFormSlope, closedForm, Finset.sum_range_succ] <;>
    field_simp [hx] <;> ring

private theorem closedFormSlope_eq_succ_4 (x : ℝ) (hx : x ≠ 0) :
    closedFormSlope 4 x = closedForm 5 x := by
  norm_num [closedFormSlope, closedForm, Finset.sum_range_succ] <;>
    field_simp [hx] <;> ring

private theorem closedFormSlope_eq_succ_5 (x : ℝ) (hx : x ≠ 0) :
    closedFormSlope 5 x = closedForm 6 x := by
  norm_num [closedFormSlope, closedForm, Finset.sum_range_succ] <;>
    field_simp [hx] <;> ring

private theorem closedFormSlope_eq_succ_6 (x : ℝ) (hx : x ≠ 0) :
    closedFormSlope 6 x = closedForm 7 x := by
  norm_num [closedFormSlope, closedForm, Finset.sum_range_succ] <;>
    field_simp [hx] <;> ring

private theorem closedFormSlope_eq_succ_7 (x : ℝ) (hx : x ≠ 0) :
    closedFormSlope 7 x = closedForm 8 x := by
  norm_num [closedFormSlope, closedForm, Finset.sum_range_succ] <;>
    field_simp [hx] <;> ring

private theorem closedFormSlope_eq_succ_8 (x : ℝ) (hx : x ≠ 0) :
    closedFormSlope 8 x = closedForm 9 x := by
  norm_num [closedFormSlope, closedForm, Finset.sum_range_succ] <;>
    field_simp [hx] <;> ring

private theorem closedFormSlope_eq_succ_9 (x : ℝ) (hx : x ≠ 0) :
    closedFormSlope 9 x = closedForm 10 x := by
  norm_num [closedFormSlope, closedForm, Finset.sum_range_succ] <;>
    field_simp [hx] <;> ring

private theorem closedFormSlope_eq_succ
    (n : ℕ) (hn : n ≤ 9) (x : ℝ) (hx : x ≠ 0) :
    closedFormSlope n x = closedForm (n + 1) x := by
  interval_cases n
  · exact closedFormSlope_eq_succ_0 x hx
  · exact closedFormSlope_eq_succ_1 x hx
  · exact closedFormSlope_eq_succ_2 x hx
  · exact closedFormSlope_eq_succ_3 x hx
  · exact closedFormSlope_eq_succ_4 x hx
  · exact closedFormSlope_eq_succ_5 x hx
  · exact closedFormSlope_eq_succ_6 x hx
  · exact closedFormSlope_eq_succ_7 x hx
  · exact closedFormSlope_eq_succ_8 x hx
  · exact closedFormSlope_eq_succ_9 x hx

private theorem closedForm_hasDerivAt
    (n : ℕ) (hn : n ≤ 9) (x : ℝ) (hx : x ≠ 0) :
    HasDerivAt (closedForm n) (closedForm (n + 1) x) x := by
  have h := closedForm_raw_hasDerivAt n x hx
  rw [closedFormSlope_eq_succ n hn x hx] at h
  exact h

private theorem nthDeriv_y_closed :
    ∀ n : ℕ, n ≤ 10 → ∀ x : ℝ, x ≠ 0 →
      nthDeriv n y x = closedForm n x
  | 0, _, x, _ => by
      norm_num [nthDeriv, y, closedForm, Finset.sum_range_succ,
        div_eq_mul_inv]
  | n + 1, hn, x, hx => by
      rw [nthDeriv]
      have heq :
          nthDeriv n y =ᶠ[nhds x] closedForm n := by
        filter_upwards [eventually_ne_nhds hx] with z hz
        exact nthDeriv_y_closed n (by omega) z hz
      rw [heq.deriv_eq]
      exact (closedForm_hasDerivAt n (by omega) x hx).deriv

private theorem nthDeriv_recip_formula :
    ∀ n : ℕ, ∀ x : ℝ, x ≠ 0 →
      nthDeriv n recip x =
        (-1 : ℝ) ^ n * (Nat.factorial n : ℝ) / x ^ (n + 1)
  | 0, x, _ => by
      simp [nthDeriv, recip]
  | n + 1, x, hx => by
      rw [nthDeriv]
      have heq :
          nthDeriv n recip =ᶠ[nhds x]
            fun z : ℝ =>
              (-1 : ℝ) ^ n * (Nat.factorial n : ℝ) / z ^ (n + 1) := by
        filter_upwards [eventually_ne_nhds hx] with z hz
        exact nthDeriv_recip_formula n z hz
      rw [heq.deriv_eq]
      have h := hasDerivAt_const_div_pow
        ((-1 : ℝ) ^ n * (Nat.factorial n : ℝ)) n x hx
      convert h.deriv using 1 <;>
        norm_num [Nat.factorial_succ, pow_succ] <;>
        field_simp [hx] <;>
        ring

private theorem leibniz_eq_final (x : ℝ) (hx : x ≠ 0) :
    leibniz10 x = final10 x := by
  unfold leibniz10 final10
  have hr : ∀ n : ℕ,
      nthDeriv n recip x =
        (-1 : ℝ) ^ n * (Nat.factorial n : ℝ) / x ^ (n + 1) :=
    fun n => nthDeriv_recip_formula n x hx
  simp_rw [hr]
  norm_num [Nat.choose, permCoeff, Finset.sum_range_succ]
  field_simp [hx]
  ring

theorem gap1 (x : ℝ) (hx : x ≠ 0) :
    nthDeriv 10 y x = leibniz10 x := by
  calc
    nthDeriv 10 y x = final10 x := by
      simpa [closedForm, final10, permCoeff] using
        nthDeriv_y_closed 10 (by omega) x hx
    _ = leibniz10 x := (leibniz_eq_final x hx).symm

theorem gap2 (x : ℝ) (hx : x ≠ 0) :
    leibniz10 x = final10 x := by
  exact leibniz_eq_final x hx

theorem gap3 (x : ℝ) (hx : x ≠ 0) :
    nthDeriv 10 y x = final10 x := by
  simpa [closedForm, final10, permCoeff] using
    nthDeriv_y_closed 10 (by omega) x hx

theorem gap4 (i : ℕ) (hi : i ≤ 10) :
    permCoeff i = fallingProduct i := by
  interval_cases i <;>
    norm_num [permCoeff, fallingProduct, Finset.prod_range_succ]

theorem gap5 : permCoeff 0 = 1 := by
  norm_num [permCoeff]

end

end ProofGap.Exercise1162
