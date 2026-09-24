import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise559

noncomputable section

def original (a b x : ℝ) : ℝ :=
  (Real.rpow a (x ^ 2) - Real.rpow b (x ^ 2)) /
    (Real.rpow a x - Real.rpow b x) ^ 2
def normalized (a b x : ℝ) : ℝ :=
  ((Real.rpow a (x ^ 2) - 1) / x ^ 2 -
    (Real.rpow b (x ^ 2) - 1) / x ^ 2) *
    (1 / (((Real.rpow a x - 1) / x - (Real.rpow b x - 1) / x) ^ 2))
def HasLimitAtZero (f : ℝ → ℝ) (L : ℝ) : Prop :=
  Filter.Tendsto f (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds L)

/-- Exercise 559, gap 1; require `a≠b` so the denominator is not identically zero. -/
theorem gap1 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a ≠ b) (L : ℝ) :
    HasLimitAtZero (original a b) L ↔ HasLimitAtZero (normalized a b) L := by
  unfold HasLimitAtZero
  have hpoint : ∀ x : ℝ, x ≠ 0 → original a b x = normalized a b x := by
    intro x hx
    unfold original normalized
    have hnum :
        (Real.rpow a (x ^ 2) - 1) / x ^ 2 -
            (Real.rpow b (x ^ 2) - 1) / x ^ 2 =
          (Real.rpow a (x ^ 2) - Real.rpow b (x ^ 2)) / x ^ 2 := by
      ring
    have hden :
        (Real.rpow a x - 1) / x - (Real.rpow b x - 1) / x =
          (Real.rpow a x - Real.rpow b x) / x := by
      ring
    rw [hnum, hden]
    by_cases hq : Real.rpow a x - Real.rpow b x = 0
    · have heq : Real.rpow a x = Real.rpow b x := sub_eq_zero.mp hq
      rw [heq]
      simp
    · field_simp [hx, hq] <;> ring
  have heq :
      original a b =ᶠ[nhdsWithin 0 ({0} : Set ℝ)ᶜ] normalized a b := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact hpoint x (by simpa using hx)
  constructor
  · intro h
    exact h.congr' heq
  · intro h
    exact h.congr' heq.symm

/-- Exercise 559, gap 2; require `a≠b`. -/
theorem gap2 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a ≠ b) :
    HasLimitAtZero (normalized a b)
      ((Real.log a - Real.log b) * (1 / (Real.log a - Real.log b) ^ 2)) := by
  unfold HasLimitAtZero
  have hlogeq : Real.log a ≠ Real.log b := by
    intro h
    apply hab
    calc
      a = Real.exp (Real.log a) := (Real.exp_log ha).symm
      _ = Real.exp (Real.log b) := congrArg Real.exp h
      _ = b := Real.exp_log hb
  have hlog : Real.log a - Real.log b ≠ 0 := sub_ne_zero.mpr hlogeq
  have slope_limit (c : ℝ) (hc : 0 < c) :
      Filter.Tendsto (fun x : ℝ => (Real.rpow c x - 1) / x)
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds (Real.log c)) := by
    have hderivExp :
        HasDerivAt (fun x : ℝ => Real.exp (Real.log c * x))
          (Real.log c) 0 := by
      simpa using
        ((Real.hasDerivAt_exp (Real.log c * 0)).comp 0
          ((hasDerivAt_id 0).const_mul (Real.log c)))
    have hrpow_eq :
        (fun x : ℝ => Real.rpow c x) =
          (fun x : ℝ => Real.exp (Real.log c * x)) := by
      funext x
      exact Real.rpow_def_of_pos hc x
    have hderiv :
        HasDerivAt (fun x : ℝ => Real.rpow c x) (Real.log c) 0 := by
      rw [hrpow_eq]
      exact hderivExp
    simpa [inv_mul_eq_div] using hderiv.tendsto_slope_zero
  have haSlope := slope_limit a ha
  have hbSlope := slope_limit b hb
  have hsquare :
      Filter.Tendsto (fun x : ℝ => x ^ 2)
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ)
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have hid_full :
          Filter.Tendsto (fun x : ℝ => x) (nhds 0) (nhds 0) :=
        continuousAt_id
      have hid :
          Filter.Tendsto (fun x : ℝ => x)
            (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 0) :=
        hid_full.mono_left inf_le_left
      simpa using hid.pow 2
    · filter_upwards [self_mem_nhdsWithin] with x hx
      have hx0 : x ≠ 0 := by simpa using hx
      simpa using (pow_ne_zero 2 hx0)
  have haSquare :
      Filter.Tendsto (fun x : ℝ => (Real.rpow a (x ^ 2) - 1) / x ^ 2)
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds (Real.log a)) := by
    simpa only [Function.comp_apply] using haSlope.comp hsquare
  have hbSquare :
      Filter.Tendsto (fun x : ℝ => (Real.rpow b (x ^ 2) - 1) / x ^ 2)
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds (Real.log b)) := by
    simpa only [Function.comp_apply] using hbSlope.comp hsquare
  have hnum :
      Filter.Tendsto
        (fun x : ℝ =>
          (Real.rpow a (x ^ 2) - 1) / x ^ 2 -
            (Real.rpow b (x ^ 2) - 1) / x ^ 2)
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ)
        (nhds (Real.log a - Real.log b)) :=
    haSquare.sub hbSquare
  have hden :
      Filter.Tendsto
        (fun x : ℝ =>
          (Real.rpow a x - 1) / x - (Real.rpow b x - 1) / x)
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ)
        (nhds (Real.log a - Real.log b)) :=
    haSlope.sub hbSlope
  have hrecip :
      Filter.Tendsto
        (fun x : ℝ =>
          1 / (((Real.rpow a x - 1) / x - (Real.rpow b x - 1) / x) ^ 2))
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ)
        (nhds (1 / (Real.log a - Real.log b) ^ 2)) := by
    simpa only [one_div] using
      (hden.pow 2).inv₀ (pow_ne_zero 2 hlog)
  unfold normalized
  exact hnum.mul hrecip

/-- Exercise 559, gap 3; require `a≠b`. -/
theorem gap3 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a ≠ b) :
    (Real.log a - Real.log b) * (1 / (Real.log a - Real.log b) ^ 2) =
      1 / (Real.log a - Real.log b) := by
  have hlogeq : Real.log a ≠ Real.log b := by
    intro h
    apply hab
    calc
      a = Real.exp (Real.log a) := (Real.exp_log ha).symm
      _ = Real.exp (Real.log b) := congrArg Real.exp h
      _ = b := Real.exp_log hb
  have hlog : Real.log a - Real.log b ≠ 0 := sub_ne_zero.mpr hlogeq
  field_simp [hlog]

/-- Exercise 559, gap 4; require `a≠b`. -/
theorem gap4 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a ≠ b) :
    1 / (Real.log a - Real.log b) = (Real.log (a / b))⁻¹ := by
  rw [Real.log_div ha.ne' hb.ne']
  simp only [one_div]

/-- Exercise 559, gap 5; require `a≠b`. -/
theorem gap5 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a ≠ b) :
    HasLimitAtZero (normalized a b) (Real.log (a / b))⁻¹ := by
  have h := gap2 a b ha hb hab
  rw [gap3 a b ha hb hab, gap4 a b ha hb hab] at h
  exact h

end

end ProofGap.Exercise559
