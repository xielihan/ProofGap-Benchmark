import ProofGapLean.Prelude.Analysis
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise2865

noncomputable section

def negativeExponentialTerm (x α : ℝ) (n : ℕ) : ℝ :=
  x ^ n * Real.exp (-(n : ℝ) * α)

def positiveExponentialTerm (x α : ℝ) (n : ℕ) : ℝ :=
  x ^ n * Real.exp ((n : ℝ) * α)

def hyperbolicSineTerm (x α : ℝ) (n : ℕ) : ℝ :=
  x ^ n * Real.sinh ((n : ℝ) * α)

private theorem expHyperbolicIdentitiesAux (α : ℝ) :
    Real.exp α = Real.cosh α + Real.sinh α ∧
      Real.exp (-α) = Real.cosh α - Real.sinh α := by
  have hreal (t : ℝ) :
      Real.exp t = (Complex.exp (t : ℂ)).re := by
    change Complex.re (Real.exp t : ℂ) =
      Complex.re (Complex.exp (t : ℂ))
    exact congrArg Complex.re (Complex.ofReal_exp t)
  constructor
  · rw [hreal α]
    simp [Real.cosh, Real.sinh, Complex.cosh, Complex.sinh] <;> ring
  · rw [hreal (-α)]
    simp [Real.cosh, Real.sinh, Complex.cosh, Complex.sinh] <;> ring

private theorem exponentialSeriesData (x α : ℝ)
    (hx : |x| < Real.exp (-|α|)) :
    (|x * Real.exp (-α)| < 1 ∧ |x * Real.exp α| < 1) ∧
      (HasSum (negativeExponentialTerm x α)
          (1 / (1 - x * Real.exp (-α))) ∧
        HasSum (positiveExponentialTerm x α)
          (1 / (1 - x * Real.exp α))) := by
  have hcancel : Real.exp (-|α|) * Real.exp |α| = 1 := by
    calc
      Real.exp (-|α|) * Real.exp |α| =
          Real.exp (-|α| + |α|) := (Real.exp_add (-|α|) |α|).symm
      _ = 1 := by simp
  have hnegAbs : |x * Real.exp (-α)| < 1 := by
    rw [abs_mul, abs_of_pos (Real.exp_pos (-α))]
    calc
      |x| * Real.exp (-α) ≤ |x| * Real.exp |α| :=
        mul_le_mul_of_nonneg_left
          (Real.exp_le_exp.mpr (neg_le_abs α)) (abs_nonneg x)
      _ < Real.exp (-|α|) * Real.exp |α| :=
        mul_lt_mul_of_pos_right hx (Real.exp_pos |α|)
      _ = 1 := hcancel
  have hposAbs : |x * Real.exp α| < 1 := by
    rw [abs_mul, abs_of_pos (Real.exp_pos α)]
    calc
      |x| * Real.exp α ≤ |x| * Real.exp |α| :=
        mul_le_mul_of_nonneg_left
          (Real.exp_le_exp.mpr (le_abs_self α)) (abs_nonneg x)
      _ < Real.exp (-|α|) * Real.exp |α| :=
        mul_lt_mul_of_pos_right hx (Real.exp_pos |α|)
      _ = 1 := hcancel
  have hnegNorm : ‖x * Real.exp (-α)‖ < 1 := by
    simpa [Real.norm_eq_abs] using hnegAbs
  have hposNorm : ‖x * Real.exp α‖ < 1 := by
    simpa [Real.norm_eq_abs] using hposAbs
  have hnegTerm : ∀ n : ℕ,
      negativeExponentialTerm x α n =
        (x * Real.exp (-α)) ^ n := by
    intro n
    unfold negativeExponentialTerm
    rw [show -(n : ℝ) * α = (n : ℝ) * (-α) by ring,
      Real.exp_nat_mul, mul_pow]
  have hposTerm : ∀ n : ℕ,
      positiveExponentialTerm x α n =
        (x * Real.exp α) ^ n := by
    intro n
    unfold positiveExponentialTerm
    rw [Real.exp_nat_mul, mul_pow]
  have hnegGeom :
      HasSum (fun n : ℕ => (x * Real.exp (-α)) ^ n)
        (1 / (1 - x * Real.exp (-α))) := by
    simpa [div_eq_mul_inv] using
      hasSum_geometric_of_norm_lt_one hnegNorm
  have hposGeom :
      HasSum (fun n : ℕ => (x * Real.exp α) ^ n)
        (1 / (1 - x * Real.exp α)) := by
    simpa [div_eq_mul_inv] using
      hasSum_geometric_of_norm_lt_one hposNorm
  have hnegFun :
      negativeExponentialTerm x α =
        (fun n : ℕ => (x * Real.exp (-α)) ^ n) := by
    funext n
    exact hnegTerm n
  have hposFun :
      positiveExponentialTerm x α =
        (fun n : ℕ => (x * Real.exp α) ^ n) := by
    funext n
    exact hposTerm n
  refine ⟨⟨hnegAbs, hposAbs⟩, ?_, ?_⟩
  · rw [hnegFun]
    exact hnegGeom
  · rw [hposFun]
    exact hposGeom

theorem gap1 :
    ∀ x α : ℝ, 1 - 2 * x * Real.cosh α + x ^ 2 ≠ 0 →
      x * Real.sinh α / (1 - 2 * x * Real.cosh α + x ^ 2) =
        (1 / 2 : ℝ) *
          ((Real.cosh α + Real.sinh α) /
              (x - (Real.cosh α + Real.sinh α)) -
            (Real.cosh α - Real.sinh α) /
              (x - (Real.cosh α - Real.sinh α))) := by
  intro x α hden
  have hhyper := Real.cosh_sq_sub_sinh_sq α
  have hfactor :
      (x - (Real.cosh α + Real.sinh α)) *
          (x - (Real.cosh α - Real.sinh α)) =
        1 - 2 * x * Real.cosh α + x ^ 2 := by
    nlinarith
  have hfactor_ne :
      (x - (Real.cosh α + Real.sinh α)) *
          (x - (Real.cosh α - Real.sinh α)) ≠ 0 := by
    intro hz
    apply hden
    rw [← hfactor]
    exact hz
  have hleft : x - (Real.cosh α + Real.sinh α) ≠ 0 :=
    (mul_ne_zero_iff.mp hfactor_ne).1
  have hright : x - (Real.cosh α - Real.sinh α) ≠ 0 :=
    (mul_ne_zero_iff.mp hfactor_ne).2
  rw [← hfactor]
  field_simp [hleft, hright] <;> ring

theorem gap2
    (hpartial :
      ∀ x α : ℝ, 1 - 2 * x * Real.cosh α + x ^ 2 ≠ 0 →
        x * Real.sinh α / (1 - 2 * x * Real.cosh α + x ^ 2) =
          (1 / 2 : ℝ) *
            ((Real.cosh α + Real.sinh α) /
                (x - (Real.cosh α + Real.sinh α)) -
              (Real.cosh α - Real.sinh α) /
                (x - (Real.cosh α - Real.sinh α)))) :
    ∀ x α : ℝ, 1 - 2 * x * Real.cosh α + x ^ 2 ≠ 0 →
      x * Real.sinh α / (1 - 2 * x * Real.cosh α + x ^ 2) =
        (1 / 2 : ℝ) *
          (Real.exp α / (x - Real.exp α) -
            Real.exp (-α) / (x - Real.exp (-α))) := by
  intro x α hden
  have hids := expHyperbolicIdentitiesAux α
  have hplus : Real.cosh α + Real.sinh α = Real.exp α := hids.1.symm
  have hminus : Real.cosh α - Real.sinh α = Real.exp (-α) := hids.2.symm
  have hp := hpartial x α hden
  rw [hplus, hminus] at hp
  exact hp

theorem gap3
    (hexponential :
      ∀ x α : ℝ, 1 - 2 * x * Real.cosh α + x ^ 2 ≠ 0 →
        x * Real.sinh α / (1 - 2 * x * Real.cosh α + x ^ 2) =
          (1 / 2 : ℝ) *
            (Real.exp α / (x - Real.exp α) -
              Real.exp (-α) / (x - Real.exp (-α)))) :
    ∀ x α : ℝ, 1 - 2 * x * Real.cosh α + x ^ 2 ≠ 0 →
      (1 / 2 : ℝ) *
          (Real.exp α / (x - Real.exp α) -
            Real.exp (-α) / (x - Real.exp (-α))) =
        (1 / 2 : ℝ) *
          (-(1 / (1 - x * Real.exp (-α))) +
            1 / (1 - x * Real.exp α)) := by
  intro x α hden
  have hhyper := Real.cosh_sq_sub_sinh_sq α
  have hids := expHyperbolicIdentitiesAux α
  have hplus : Real.cosh α + Real.sinh α = Real.exp α := hids.1.symm
  have hminus : Real.cosh α - Real.sinh α = Real.exp (-α) := hids.2.symm
  have hfactor :
      (x - Real.exp α) * (x - Real.exp (-α)) =
        1 - 2 * x * Real.cosh α + x ^ 2 := by
    rw [← hplus, ← hminus]
    nlinarith
  have hfactor_ne :
      (x - Real.exp α) * (x - Real.exp (-α)) ≠ 0 := by
    intro hz
    apply hden
    rw [← hfactor]
    exact hz
  have hxa : x - Real.exp α ≠ 0 :=
    (mul_ne_zero_iff.mp hfactor_ne).1
  have hxb : x - Real.exp (-α) ≠ 0 :=
    (mul_ne_zero_iff.mp hfactor_ne).2
  have ha : Real.exp α ≠ 0 := Real.exp_ne_zero α
  rw [Real.exp_neg] at hxb ⊢
  have hrel₁ :
      1 - x * (Real.exp α)⁻¹ =
        -(x - Real.exp α) * (Real.exp α)⁻¹ := by
    field_simp [ha] <;> ring
  have hrel₂ :
      1 - x * Real.exp α =
        -(x - (Real.exp α)⁻¹) * Real.exp α := by
    field_simp [ha] <;> ring
  rw [hrel₁, hrel₂]
  field_simp [hxa, hxb, ha] <;> ring

theorem gap4
    (hexponential :
      ∀ x α : ℝ, 1 - 2 * x * Real.cosh α + x ^ 2 ≠ 0 →
        x * Real.sinh α / (1 - 2 * x * Real.cosh α + x ^ 2) =
          (1 / 2 : ℝ) *
            (Real.exp α / (x - Real.exp α) -
              Real.exp (-α) / (x - Real.exp (-α))))
    (hrewrite :
      ∀ x α : ℝ, 1 - 2 * x * Real.cosh α + x ^ 2 ≠ 0 →
        (1 / 2 : ℝ) *
            (Real.exp α / (x - Real.exp α) -
              Real.exp (-α) / (x - Real.exp (-α))) =
          (1 / 2 : ℝ) *
            (-(1 / (1 - x * Real.exp (-α))) +
              1 / (1 - x * Real.exp α))) :
    ∀ x α : ℝ, 1 - 2 * x * Real.cosh α + x ^ 2 ≠ 0 →
      x * Real.sinh α / (1 - 2 * x * Real.cosh α + x ^ 2) =
        (1 / 2 : ℝ) *
          (-(1 / (1 - x * Real.exp (-α))) +
            1 / (1 - x * Real.exp α)) := by
  intro x α hden
  calc
    x * Real.sinh α / (1 - 2 * x * Real.cosh α + x ^ 2) =
        (1 / 2 : ℝ) *
          (Real.exp α / (x - Real.exp α) -
            Real.exp (-α) / (x - Real.exp (-α))) :=
      hexponential x α hden
    _ = (1 / 2 : ℝ) *
          (-(1 / (1 - x * Real.exp (-α))) +
            1 / (1 - x * Real.exp α)) :=
      hrewrite x α hden

theorem gap5
    (hgeometricForm :
      ∀ x α : ℝ, 1 - 2 * x * Real.cosh α + x ^ 2 ≠ 0 →
        x * Real.sinh α / (1 - 2 * x * Real.cosh α + x ^ 2) =
          (1 / 2 : ℝ) *
            (-(1 / (1 - x * Real.exp (-α))) +
              1 / (1 - x * Real.exp α))) :
    ∀ x α : ℝ, |x| < Real.exp (-|α|) →
      x * Real.sinh α / (1 - 2 * x * Real.cosh α + x ^ 2) =
        (1 / 2 : ℝ) *
          (-(∑' n, negativeExponentialTerm x α n) +
            (∑' n, positiveExponentialTerm x α n)) := by
  intro x α hx
  obtain ⟨⟨hnegAbs, hposAbs⟩, hneg, hpos⟩ :=
    exponentialSeriesData x α hx
  have hdenNeg : 1 - x * Real.exp (-α) ≠ 0 := by
    intro hz
    have hr : x * Real.exp (-α) = 1 := by
      linarith
    simpa [hr] using hnegAbs
  have hdenPos : 1 - x * Real.exp α ≠ 0 := by
    intro hz
    have hr : x * Real.exp α = 1 := by
      linarith
    simpa [hr] using hposAbs
  have hexpmul : Real.exp (-α) * Real.exp α = 1 := by
    calc
      Real.exp (-α) * Real.exp α = Real.exp (-α + α) :=
        (Real.exp_add (-α) α).symm
      _ = 1 := by simp
  have hids := expHyperbolicIdentitiesAux α
  have hplus : Real.cosh α + Real.sinh α = Real.exp α := hids.1.symm
  have hminus : Real.cosh α - Real.sinh α = Real.exp (-α) := hids.2.symm
  have hexpsum : Real.exp (-α) + Real.exp α = 2 * Real.cosh α := by
    rw [← hminus, ← hplus]
    ring
  have hfactor :
      (1 - x * Real.exp (-α)) * (1 - x * Real.exp α) =
        1 - 2 * x * Real.cosh α + x ^ 2 := by
    calc
      (1 - x * Real.exp (-α)) * (1 - x * Real.exp α) =
          1 - x * (Real.exp (-α) + Real.exp α) +
            x ^ 2 * (Real.exp (-α) * Real.exp α) := by ring
      _ = 1 - 2 * x * Real.cosh α + x ^ 2 := by
        rw [hexpmul, hexpsum]
        ring
  have hden : 1 - 2 * x * Real.cosh α + x ^ 2 ≠ 0 := by
    rw [← hfactor]
    exact mul_ne_zero hdenNeg hdenPos
  calc
    x * Real.sinh α / (1 - 2 * x * Real.cosh α + x ^ 2) =
        (1 / 2 : ℝ) *
          (-(1 / (1 - x * Real.exp (-α))) +
            1 / (1 - x * Real.exp α)) :=
      hgeometricForm x α hden
    _ = (1 / 2 : ℝ) *
          (-(∑' n, negativeExponentialTerm x α n) +
            (∑' n, positiveExponentialTerm x α n)) := by
      rw [hneg.tsum_eq, hpos.tsum_eq]

theorem gap6
    (hexponentialSeries :
      ∀ x α : ℝ, |x| < Real.exp (-|α|) →
        x * Real.sinh α / (1 - 2 * x * Real.cosh α + x ^ 2) =
          (1 / 2 : ℝ) *
            (-(∑' n, negativeExponentialTerm x α n) +
              (∑' n, positiveExponentialTerm x α n))) :
    ∀ x α : ℝ, |x| < Real.exp (-|α|) →
      (1 / 2 : ℝ) *
          (-(∑' n, negativeExponentialTerm x α n) +
            (∑' n, positiveExponentialTerm x α n)) =
        ∑' n, hyperbolicSineTerm x α n := by
  intro x α hx
  obtain ⟨_, hneg, hpos⟩ := exponentialSeriesData x α hx
  have hcombined :
      HasSum
        (fun n => (1 / 2 : ℝ) *
          (-negativeExponentialTerm x α n +
            positiveExponentialTerm x α n))
        ((1 / 2 : ℝ) *
          (-(∑' n, negativeExponentialTerm x α n) +
            (∑' n, positiveExponentialTerm x α n))) := by
    exact
      (hneg.summable.hasSum.neg.add hpos.summable.hasSum).mul_left
        (1 / 2 : ℝ)
  have hterm : ∀ n : ℕ,
      (1 / 2 : ℝ) *
          (-negativeExponentialTerm x α n +
            positiveExponentialTerm x α n) =
        hyperbolicSineTerm x α n := by
    intro n
    have hids := expHyperbolicIdentitiesAux ((n : ℝ) * α)
    have hplus := hids.1
    have hminus := hids.2
    have hsinh :
        Real.sinh ((n : ℝ) * α) =
          (1 / 2 : ℝ) *
            (Real.exp ((n : ℝ) * α) -
              Real.exp (-((n : ℝ) * α))) := by
      linarith
    unfold negativeExponentialTerm positiveExponentialTerm
      hyperbolicSineTerm
    rw [show -(n : ℝ) * α = -((n : ℝ) * α) by ring, hsinh]
    ring
  calc
    (1 / 2 : ℝ) *
          (-(∑' n, negativeExponentialTerm x α n) +
            (∑' n, positiveExponentialTerm x α n)) =
        ∑' n, (1 / 2 : ℝ) *
          (-negativeExponentialTerm x α n +
            positiveExponentialTerm x α n) :=
      hcombined.tsum_eq.symm
    _ = ∑' n, hyperbolicSineTerm x α n :=
      tsum_congr hterm

theorem gap7
    (hexponentialSeries :
      ∀ x α : ℝ, |x| < Real.exp (-|α|) →
        x * Real.sinh α / (1 - 2 * x * Real.cosh α + x ^ 2) =
          (1 / 2 : ℝ) *
            (-(∑' n, negativeExponentialTerm x α n) +
              (∑' n, positiveExponentialTerm x α n)))
    (hcombine :
      ∀ x α : ℝ, |x| < Real.exp (-|α|) →
        (1 / 2 : ℝ) *
            (-(∑' n, negativeExponentialTerm x α n) +
              (∑' n, positiveExponentialTerm x α n)) =
          ∑' n, hyperbolicSineTerm x α n) :
    ∀ x α : ℝ, |x| < Real.exp (-|α|) →
      x * Real.sinh α / (1 - 2 * x * Real.cosh α + x ^ 2) =
        ∑' n, hyperbolicSineTerm x α n := by
  intro x α hx
  calc
    x * Real.sinh α / (1 - 2 * x * Real.cosh α + x ^ 2) =
        (1 / 2 : ℝ) *
          (-(∑' n, negativeExponentialTerm x α n) +
            (∑' n, positiveExponentialTerm x α n)) :=
      hexponentialSeries x α hx
    _ = ∑' n, hyperbolicSineTerm x α n :=
      hcombine x α hx

end

end ProofGap.Exercise2865
