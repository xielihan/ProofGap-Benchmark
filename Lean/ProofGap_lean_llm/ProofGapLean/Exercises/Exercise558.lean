import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

namespace ProofGap.Exercise558

noncomputable section

def original (a b x : ℝ) : ℝ :=
  Real.rpow
    ((Real.rpow a (x ^ 2) + Real.rpow b (x ^ 2)) /
      (Real.rpow a x + Real.rpow b x)) (1 / x)
def rewritten (a b x : ℝ) : ℝ :=
  Real.rpow
    (1 + (Real.rpow a (x ^ 2) + Real.rpow b (x ^ 2) -
      Real.rpow a x - Real.rpow b x) /
      (Real.rpow a x + Real.rpow b x)) (1 / x)
def exponentialForm (a b x : ℝ) : ℝ :=
  let d := Real.rpow a (x ^ 2) + Real.rpow b (x ^ 2) -
    Real.rpow a x - Real.rpow b x
  Real.rpow (1 + 1 / ((Real.rpow a x + Real.rpow b x) / d))
    (((Real.rpow a x + Real.rpow b x) / d) *
      (((Real.rpow a (x ^ 2) - 1) / x ^ 2) * x +
        ((Real.rpow b (x ^ 2) - 1) / x ^ 2) * x -
        (Real.rpow a x - 1) / x - (Real.rpow b x - 1) / x) /
          (Real.rpow a x + Real.rpow b x))
def HasLimitAtZero (f : ℝ → ℝ) (L : ℝ) : Prop :=
  Filter.Tendsto f (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds L)

private theorem original_limit_exp (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    HasLimitAtZero (original a b)
      (Real.exp (-(1 / 2 : ℝ) * (Real.log a + Real.log b))) := by
  let N : ℝ → ℝ := fun x =>
    Real.rpow a (x ^ 2) + Real.rpow b (x ^ 2)
  let D : ℝ → ℝ := fun x =>
    Real.rpow a x + Real.rpow b x
  let R : ℝ → ℝ := fun x => N x / D x
  have hsq : HasDerivAt (fun x : ℝ => x ^ 2) 0 0 := by
    convert (hasDerivAt_id (0 : ℝ)).pow 2 using 1 <;> norm_num
  have ha_sq :
      HasDerivAt (fun x : ℝ => Real.rpow a (x ^ 2)) 0 0 := by
    simpa using hsq.const_rpow ha
  have hb_sq :
      HasDerivAt (fun x : ℝ => Real.rpow b (x ^ 2)) 0 0 := by
    simpa using hsq.const_rpow hb
  have hN : HasDerivAt N 0 0 := by
    simpa [N] using ha_sq.add hb_sq
  have ha_id :
      HasDerivAt (fun x : ℝ => Real.rpow a x) (Real.log a) 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).const_rpow ha
  have hb_id :
      HasDerivAt (fun x : ℝ => Real.rpow b x) (Real.log b) 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).const_rpow hb
  have hD : HasDerivAt D (Real.log a + Real.log b) 0 := by
    simpa [D] using ha_id.add hb_id
  have hR :
      HasDerivAt R (-(1 / 2 : ℝ) * (Real.log a + Real.log b)) 0 := by
    have hraw := hN.div hD (by simp [D])
    convert hraw using 1 <;> norm_num [N, D, R] <;> ring
  have hlog :
      HasDerivAt (fun x => Real.log (R x))
        (-(1 / 2 : ℝ) * (Real.log a + Real.log b)) 0 := by
    have hraw := hR.log (by simp [R, N, D])
    simpa [R, N, D] using hraw
  have hslope := hlog.tendsto_slope_zero
  have hlog_div :
      Filter.Tendsto (fun x => Real.log (R x) / x)
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ)
        (nhds (-(1 / 2 : ℝ) * (Real.log a + Real.log b))) := by
    apply hslope.congr'
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hx0 : x ≠ 0 := by simpa using hx
    simp [R, N, D, smul_eq_mul, hx0]
    field_simp [hx0]
  have hexp :=
    (Real.continuous_exp.tendsto
      (-(1 / 2 : ℝ) * (Real.log a + Real.log b))).comp hlog_div
  unfold HasLimitAtZero original
  apply hexp.congr'
  filter_upwards with x
  have hRpos : 0 < R x := by
    exact div_pos
      (add_pos (Real.rpow_pos_of_pos ha _) (Real.rpow_pos_of_pos hb _))
      (add_pos (Real.rpow_pos_of_pos ha _) (Real.rpow_pos_of_pos hb _))
  change Real.exp (Real.log (R x) / x) = Real.rpow (R x) (1 / x)
  rw [Real.rpow_eq_pow, Real.rpow_def_of_pos hRpos]
  congr 1
  ring

/-- Source: `proof_gap/exercise_558/1.txt`. -/
theorem gap1 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (L : ℝ) :
    HasLimitAtZero (original a b) L ↔ HasLimitAtZero (rewritten a b) L := by
  have hfun : original a b = rewritten a b := by
    funext x
    unfold original rewritten
    apply congrArg (fun y : ℝ => Real.rpow y (1 / x))
    have hden : Real.rpow a x + Real.rpow b x ≠ 0 :=
      ne_of_gt
        (add_pos (Real.rpow_pos_of_pos ha x) (Real.rpow_pos_of_pos hb x))
    field_simp [hden] <;> ring
  rw [hfun]

private theorem exponential_eq_original_eventually
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    ∀ᶠ x in nhdsWithin 0 ({0} : Set ℝ)ᶜ,
      exponentialForm a b x = original a b x := by
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hx0 : x ≠ 0 := by simpa using hx
  let A₂ : ℝ := a ^ (x ^ 2)
  let B₂ : ℝ := b ^ (x ^ 2)
  let A : ℝ := a ^ x
  let B : ℝ := b ^ x
  let S := A + B
  let d := A₂ + B₂ - A - B
  let Q :=
    ((A₂ - 1) / x ^ 2) * x + ((B₂ - 1) / x ^ 2) * x -
      (A - 1) / x - (B - 1) / x
  have hSpos : 0 < S := by
    exact add_pos (Real.rpow_pos_of_pos ha _) (Real.rpow_pos_of_pos hb _)
  have hS : S ≠ 0 := ne_of_gt hSpos
  have hQ : Q = d / x := by
    dsimp [Q, d]
    field_simp [hx0]
    ring
  have hnum : A₂ + B₂ = S + d := by
    dsimp [S, d]
    ring
  unfold exponentialForm original
  dsimp
  change (1 + 1 / (S / d)) ^ (((S / d) * Q) / S) =
    ((A₂ + B₂) / S) ^ (1 / x)
  rw [hQ, hnum]
  by_cases hd : d = 0
  · simp [hd, hS, Real.rpow_eq_pow]
  · congr 1
    · field_simp [hS, hd]
    · field_simp [hS, hd, hx0]

/-- Source: `proof_gap/exercise_558/2.txt`. -/
theorem gap2 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    HasLimitAtZero (exponentialForm a b)
      (Real.exp (-((1 / 2 : ℝ) * Real.log a + (1 / 2 : ℝ) * Real.log b))) := by
  have horiginal := original_limit_exp a b ha hb
  have hrewritten :
      HasLimitAtZero (exponentialForm a b)
        (Real.exp (-(1 / 2 : ℝ) * (Real.log a + Real.log b))) := by
    unfold HasLimitAtZero at horiginal ⊢
    exact horiginal.congr'
      ((exponential_eq_original_eventually a b ha hb).mono fun _ hx => hx.symm)
  convert hrewritten using 1
  apply congrArg Real.exp
  ring

/-- Source: `proof_gap/exercise_558/3.txt`. -/
theorem gap3 (a b : ℝ) :
    Real.exp (-((1 / 2 : ℝ) * Real.log a + (1 / 2 : ℝ) * Real.log b)) =
      Real.exp (-(1 / 2 : ℝ) * (Real.log a + Real.log b)) := by
  apply congrArg Real.exp
  ring

/-- Source: `proof_gap/exercise_558/4.txt`. -/
theorem gap4 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    Real.exp (-(1 / 2 : ℝ) * (Real.log a + Real.log b)) =
      1 / Real.sqrt (a * b) := by
  have hc : 0 < a * b := mul_pos ha hb
  have hlog : Real.log (a * b) = Real.log a + Real.log b :=
    Real.log_mul ha.ne' hb.ne'
  rw [← hlog]
  have hspos : 0 < Real.sqrt (a * b) := Real.sqrt_pos.2 hc
  have hsquare :
      Real.sqrt (a * b) * Real.sqrt (a * b) = a * b := by
    simpa [pow_two] using Real.sq_sqrt hc.le
  have hmul :
      Real.log (Real.sqrt (a * b) * Real.sqrt (a * b)) =
        Real.log (Real.sqrt (a * b)) + Real.log (Real.sqrt (a * b)) :=
    Real.log_mul hspos.ne' hspos.ne'
  rw [hsquare] at hmul
  have hlogsqrt :
      Real.log (Real.sqrt (a * b)) =
        (1 / 2 : ℝ) * Real.log (a * b) := by
    linarith
  calc
    Real.exp (-(1 / 2 : ℝ) * Real.log (a * b)) =
        Real.exp (-Real.log (Real.sqrt (a * b))) := by
      apply congrArg Real.exp
      rw [hlogsqrt]
      ring
    _ = (Real.exp (Real.log (Real.sqrt (a * b))))⁻¹ := by
      rw [Real.exp_neg]
    _ = (Real.sqrt (a * b))⁻¹ := by
      rw [Real.exp_log hspos]
    _ = 1 / Real.sqrt (a * b) := by
      exact (one_div _).symm

/-- Source: `proof_gap/exercise_558/5.txt`. -/
theorem gap5 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    HasLimitAtZero (exponentialForm a b) (1 / Real.sqrt (a * b)) := by
  rw [← gap4 a b ha hb, ← gap3 a b]
  exact gap2 a b ha hb

end

end ProofGap.Exercise558
