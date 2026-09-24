import ProofGapLean.Prelude.Analysis
import ProofGapLean.Prelude.Discrete
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise734

noncomputable section

def IsRational (x : ℝ) : Prop :=
  ∃ q : ℤ, ∃ p : ℕ, 0 < p ∧ x = (q : ℝ) / (p : ℝ)

/-- The source's `(π*m)!` has no real-factorial meaning.  The intended
expression is `π * m! * x`.  The exponent is made even so that rational
points producing cosine `-1` do not create the divergent sequence
`(-1)^n`. -/
def kernel (x : ℝ) (m n : ℕ) : ℝ :=
  (Real.cos (Real.pi * (m.factorial : ℝ) * x)) ^ (2 * n)

def HasIteratedLimit (x L : ℝ) : Prop :=
  ∃ inner : ℕ → ℝ,
    (∀ m : ℕ,
      Filter.Tendsto (fun n : ℕ => kernel x m n) Filter.atTop (nhds (inner m))) ∧
    Filter.Tendsto inner Filter.atTop (nhds L)

noncomputable def χ (x : ℝ) : ℝ := by
  classical
  exact if IsRational x then 1 else 0

/-- Source: `proof_gap/exercise_734/1.txt`; add the missing nonzero
denominator condition by choosing a positive natural denominator. -/
private theorem absCosLeOne (a : ℝ) : |Real.cos a| ≤ 1 := by
  rw [abs_le]
  have h := Real.sin_sq_add_cos_sq a
  constructor <;>
    nlinarith [sq_nonneg (Real.sin a),
      sq_nonneg (Real.cos a - 1), sq_nonneg (Real.cos a + 1)]

private theorem evenPowersTendsto (c : ℝ) (hc : |c| ≤ 1) :
    Filter.Tendsto (fun n : ℕ => c ^ (2 * n)) Filter.atTop
      (nhds (if |c| = 1 then 1 else 0)) := by
  by_cases h : |c| = 1
  · have hc2 : c ^ 2 = 1 := by
      nlinarith [sq_abs c]
    simp [h, pow_mul, hc2]
  · have hlt : |c| < 1 := lt_of_le_of_ne hc h
    have hc2lt : c ^ 2 < 1 := by
      nlinarith [sq_abs c, abs_nonneg c]
    have ht := tendsto_pow_atTop_nhds_zero_of_lt_one
      (sq_nonneg c) hc2lt
    simpa [h, pow_mul] using ht

theorem gap1 (x : ℝ) (hx : IsRational x) :
    ∃ q : ℤ, ∃ p : ℕ, 0 < p ∧ x = (q : ℝ) / (p : ℝ) := by
  exact hx

/-- Source: `proof_gap/exercise_734/2.txt`; bind `m,n`, replace the malformed
factorial, and use the corrected even exponent. -/
theorem gap2 (x : ℝ) (hx : IsRational x) :
    ∃ p : ℕ, 0 < p ∧
      ∀ m : ℕ, p ≤ m → ∀ n : ℕ, kernel x m n = 1 := by
  rcases hx with ⟨q, p, hp, hx⟩
  refine ⟨p, hp, ?_⟩
  intro m hm n
  have hpdvd : p ∣ m.factorial := Nat.dvd_factorial hp hm
  rcases hpdvd with ⟨k, hk⟩
  have hp0 : (p : ℝ) ≠ 0 := by positivity
  have harg :
      Real.pi * (m.factorial : ℝ) * x =
        (q : ℝ) * (k : ℝ) * Real.pi := by
    rw [hx, hk, Nat.cast_mul]
    field_simp [hp0]
  have hsin :
      Real.sin ((q : ℝ) * (k : ℝ) * Real.pi) = 0 := by
    simpa [mul_assoc] using Real.sin_int_mul_pi (q * (k : ℤ))
  have hc2 :
      Real.cos ((q : ℝ) * (k : ℝ) * Real.pi) ^ 2 = 1 := by
    nlinarith [Real.sin_sq_add_cos_sq
      ((q : ℝ) * (k : ℝ) * Real.pi)]
  unfold kernel
  rw [harg, pow_mul, hc2]
  simp

/-- Source: `proof_gap/exercise_734/3.txt`; state the iterated sequential
limit represented by the source's nested limits. -/
theorem gap3 (x : ℝ) (hx : IsRational x) :
    HasIteratedLimit x 1 := by
  classical
  let inner : ℕ → ℝ := fun m =>
    if |Real.cos (Real.pi * (m.factorial : ℝ) * x)| = 1 then 1 else 0
  refine ⟨inner, ?_, ?_⟩
  · intro m
    simpa [inner, kernel] using
      evenPowersTendsto
        (Real.cos (Real.pi * (m.factorial : ℝ) * x))
        (absCosLeOne (Real.pi * (m.factorial : ℝ) * x))
  · rcases gap2 x hx with ⟨p, hp, hpm⟩
    have hev : ∀ᶠ m in Filter.atTop, inner m = 1 := by
      filter_upwards [Filter.eventually_ge_atTop p] with m hm
      have hc2 :
          Real.cos (Real.pi * (m.factorial : ℝ) * x) ^ 2 = 1 := by
        simpa [kernel] using hpm m hm 1
      have habs :
          |Real.cos (Real.pi * (m.factorial : ℝ) * x)| = 1 := by
        nlinarith [sq_abs
          (Real.cos (Real.pi * (m.factorial : ℝ) * x)),
          abs_nonneg (Real.cos
            (Real.pi * (m.factorial : ℝ) * x))]
      simp [inner, habs]
    refine Filter.tendsto_def.2 ?_
    intro s hs
    have h1 : (1 : ℝ) ∈ s := mem_of_mem_nhds hs
    filter_upwards [hev] with m hm
    simpa [hm] using h1

/-- Source: `proof_gap/exercise_734/4.txt`; use natural `m` and the corrected
argument `π * m! * x`. -/
theorem gap4 (x : ℝ) (hx : ¬ IsRational x) :
    ∀ m : ℕ,
      |Real.cos (Real.pi * (m.factorial : ℝ) * x)| < 1 := by
  intro m
  let a : ℝ := Real.pi * (m.factorial : ℝ) * x
  have hle : |Real.cos a| ≤ 1 := absCosLeOne a
  by_contra hlt
  have habs : |Real.cos a| = 1 :=
    le_antisymm hle (not_lt.mp hlt)
  have hc2 : Real.cos a ^ 2 = 1 := by
    nlinarith [sq_abs (Real.cos a)]
  have hsin : Real.sin a = 0 := by
    nlinarith [Real.sin_sq_add_cos_sq a]
  rcases Real.sin_eq_zero_iff.mp hsin with ⟨q, hq⟩
  apply hx
  refine ⟨q, m.factorial, Nat.factorial_pos m, ?_⟩
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  have hmf : (m.factorial : ℝ) ≠ 0 := by positivity
  have hq' : (q : ℝ) = (m.factorial : ℝ) * x := by
    calc
      (q : ℝ) = ((q : ℝ) * Real.pi) / Real.pi := by
        field_simp [hpi]
      _ = a / Real.pi := by rw [hq]
      _ = (m.factorial : ℝ) * x := by
        dsimp [a]
        field_simp [hpi]
  exact (eq_div_iff hmf).2 (by
    simpa [mul_comm] using hq'.symm)

/-- Source: `proof_gap/exercise_734/5.txt`; bind both sequence indices. -/
theorem gap5 (x : ℝ) (hx : ¬ IsRational x) :
    ∀ m : ℕ,
      Filter.Tendsto (fun n : ℕ => kernel x m n) Filter.atTop (nhds 0) := by
  intro m
  have hbound :=
    evenPowersTendsto
      (Real.cos (Real.pi * (m.factorial : ℝ) * x))
      (absCosLeOne (Real.pi * (m.factorial : ℝ) * x))
  have hne :
      |Real.cos (Real.pi * (m.factorial : ℝ) * x)| ≠ 1 :=
    ne_of_lt (gap4 x hx m)
  simpa [kernel, hne] using hbound

/-- Source: `proof_gap/exercise_734/6.txt`; state the corrected nested
sequence limit at an irrational point. -/
theorem gap6 (x : ℝ) (hx : ¬ IsRational x) :
    HasIteratedLimit x 0 := by
  refine ⟨fun _ => 0, ?_, tendsto_const_nhds⟩
  intro m
  exact gap5 x hx m

/-- Source: `proof_gap/exercise_734/7.txt`; identify the iterated limit with
the rational characteristic function. -/
theorem gap7 (x : ℝ) :
    HasIteratedLimit x (χ x) ∧
      (χ x = 1 ↔ IsRational x) := by
  classical
  by_cases hx : IsRational x
  · constructor
    · simpa [χ, hx] using gap3 x hx
    · simp [χ, hx]
  · constructor
    · simpa [χ, hx] using gap6 x hx
    · simp [χ, hx]

/-- Source: `proof_gap/exercise_734/8.txt`; quantify all variables and retain
the local radius condition. -/
theorem gap8 :
    ∀ x : ℝ, ∀ δ : ℝ, 0 < δ →
      ∃ r s : ℝ,
        IsRational r ∧ ¬ IsRational s ∧
        |r - x| < δ ∧ |s - x| < δ := by
  intro x δ hδ
  have hinterval : x - δ < x + δ := by linarith
  rcases exists_rat_btwn hinterval with ⟨r, hr₁, hr₂⟩
  rcases exists_irrational_btwn hinterval with
    ⟨s, hsirr, hs₁, hs₂⟩
  refine ⟨(r : ℝ), s, ?_, ?_, ?_, ?_⟩
  · refine ⟨r.num, r.den, r.den_pos, ?_⟩
    exact Rat.cast_def r
  · rintro ⟨q, p, hp, hs⟩
    apply hsirr
    refine ⟨(q : ℚ) / (p : ℚ), ?_⟩
    simpa using hs.symm
  · rw [abs_lt]
    constructor <;> linarith
  · rw [abs_lt]
    constructor <;> linarith

/-- Source: `proof_gap/exercise_734/9.txt`; the source dropped both `δ` and
the requirement that the rational witness be near `x`; restore them. -/
theorem gap9 :
    ∀ x : ℝ, ∀ δ : ℝ, 0 < δ →
      ∃ r : ℝ, IsRational r ∧ |r - x| < δ ∧ χ r = 1 := by
  classical
  intro x δ hδ
  rcases gap8 x δ hδ with ⟨r, s, hr, hs, hrx, hsx⟩
  refine ⟨r, hr, hrx, ?_⟩
  simp [χ, hr]

/-- Source: `proof_gap/exercise_734/10.txt`; restore the missing radius and
proximity condition for the irrational witness. -/
theorem gap10 :
    ∀ x : ℝ, ∀ δ : ℝ, 0 < δ →
      ∃ s : ℝ, ¬ IsRational s ∧ |s - x| < δ ∧ χ s = 0 := by
  classical
  intro x δ hδ
  rcases gap8 x δ hδ with ⟨r, s, hr, hs, hrx, hsx⟩
  refine ⟨s, hs, hsx, ?_⟩
  simp [χ, hs]

/-- Source: `proof_gap/exercise_734/11.txt`; bind the candidate limit. -/
theorem gap11 (x : ℝ) :
    ¬ ∃ L : ℝ, Filter.Tendsto χ (nhds x) (nhds L) := by
  rintro ⟨L, hL⟩
  have he :
      ∀ᶠ y in nhds x, dist (χ y) L < (1 / 3 : ℝ) :=
    (Metric.tendsto_nhds.mp hL) (1 / 3 : ℝ) (by norm_num)
  rcases Metric.eventually_nhds_iff.mp he with
    ⟨δ, hδ, heδ⟩
  rcases gap9 x δ hδ with ⟨r, hr, hrx, hχr⟩
  rcases gap10 x δ hδ with ⟨s, hs, hsx, hχs⟩
  have hrL := heδ (y := r) (by
    simpa [Real.dist_eq] using hrx)
  have hsL := heδ (y := s) (by
    simpa [Real.dist_eq] using hsx)
  have hrL' : |(1 : ℝ) - L| < 1 / 3 := by
    simpa [Real.dist_eq, hχr] using hrL
  have hsL' : |L| < 1 / 3 := by
    simpa [Real.dist_eq, hχs, abs_neg] using hsL
  nlinarith [le_abs_self ((1 : ℝ) - L), le_abs_self L]

/-- Source: `proof_gap/exercise_734/12.txt`. -/
theorem gap12 (x : ℝ) : ¬ ContinuousAt χ x := by
  intro h
  exact gap11 x ⟨χ x, h⟩

/-- Source: `proof_gap/exercise_734/13.txt`; retain the duplicated final
conclusion from the source as its own canonical gap. -/
theorem gap13 (x : ℝ) : ¬ ContinuousAt χ x := by
  exact gap12 x

end

end ProofGap.Exercise734
