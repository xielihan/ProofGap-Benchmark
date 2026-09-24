import ProofGapLean.Prelude.Analysis
import Mathlib.Tactic.FieldSimp
import Mathlib.Topology.Defs.Filter

namespace ProofGap.Exercise2737

noncomputable section

def positiveTerm (a : ℤ → ℝ) (x : ℝ) (n : ℕ) : ℝ :=
  a n * x ^ n

def negativeTerm (a : ℤ → ℝ) (x : ℝ) (n : ℕ) : ℝ :=
  a (-((n + 1 : ℕ) : ℤ)) / x ^ (n + 1)

def LaurentSummableAt (a : ℤ → ℝ) (x : ℝ) : Prop :=
  Summable (positiveTerm a x) ∧ Summable (negativeTerm a x)

private theorem summable_mul_pow_lt_one {u : ℕ → ℝ} {q : ℝ}
    (hu : Summable u) (hq : ‖q‖ < 1) :
    Summable (fun n => u n * q ^ n) := by
  have hqnorm : ‖(‖q‖ : ℝ)‖ < 1 := by
    simpa [Real.norm_eq_abs] using hq
  have hgeom : Summable (fun n : ℕ => ‖q‖ ^ n) :=
    summable_geometric_of_norm_lt_one hqnorm
  have hzero : Tendsto u Filter.cofinite (nhds 0) :=
    hu.tendsto_cofinite_zero
  have hsmall : ∀ᶠ n : ℕ in Filter.cofinite, dist (u n) 0 < 1 :=
    (Metric.tendsto_nhds.1 hzero) 1 zero_lt_one
  refine Summable.of_norm_bounded_eventually hgeom ?_
  refine hsmall.mono ?_
  intro n hn
  have hu_le : ‖u n‖ ≤ 1 := by
    exact le_of_lt (by simpa [dist_eq_norm] using hn)
  simpa only [norm_mul, norm_pow] using
    mul_le_of_le_one_left (pow_nonneg (norm_nonneg q) n) hu_le

theorem gap1 (a : ℤ → ℝ) (x₁ : ℝ) (h : LaurentSummableAt a x₁) :
    Summable (positiveTerm a x₁) := by
  exact h.1

theorem gap2 (a : ℤ → ℝ) (x₁ : ℝ) (h : LaurentSummableAt a x₁) :
    Summable (negativeTerm a x₁) := by
  exact h.2

theorem gap3 (a : ℤ → ℝ) (x₂ : ℝ) (h : LaurentSummableAt a x₂) :
    Summable (positiveTerm a x₂) := by
  exact h.1

theorem gap4 (a : ℤ → ℝ) (x₂ : ℝ) (h : LaurentSummableAt a x₂) :
    Summable (negativeTerm a x₂) := by
  exact h.2

theorem gap5 (a : ℤ → ℝ) (x x₂ : ℝ)
    (h₂ : Summable (positiveTerm a x₂)) (hxx : |x| < |x₂|) :
    Summable (positiveTerm a x) := by
  have hx₂ : x₂ ≠ 0 :=
    abs_pos.mp (lt_of_le_of_lt (abs_nonneg x) hxx)
  have hratio : ‖x / x₂‖ < 1 := by
    rw [Real.norm_eq_abs, abs_div]
    exact (div_lt_one (abs_pos.mpr hx₂)).2 hxx
  have hs := summable_mul_pow_lt_one h₂ hratio
  refine hs.congr ?_
  intro n
  simp only [positiveTerm, div_pow]
  field_simp [hx₂]

theorem gap6 (a : ℤ → ℝ) (x₁ x : ℝ)
    (h₁ : Summable (negativeTerm a x₁))
    (hx₁ : x₁ ≠ 0) (hx : x ≠ 0) (hxx : |x₁| < |x|) :
    Summable (negativeTerm a x) := by
  have hratio : ‖x₁ / x‖ < 1 := by
    rw [Real.norm_eq_abs, abs_div]
    exact (div_lt_one (abs_pos.mpr hx)).2 hxx
  have hscaled :
      Summable (fun n => negativeTerm a x₁ n * (x₁ / x)) :=
    h₁.mul_right (x₁ / x)
  have hs := summable_mul_pow_lt_one hscaled hratio
  refine hs.congr ?_
  intro n
  simp only [negativeTerm, div_pow, pow_succ]
  field_simp [hx₁, hx]

theorem gap7 (a : ℤ → ℝ) (x₁ x : ℝ)
    (h₁ : Summable (negativeTerm a x₁))
    (hx₁ : x₁ ≠ 0) (hx : x ≠ 0) (hxx : |x₁| < |x|) :
    Summable (negativeTerm a x) := by
  exact gap6 a x₁ x h₁ hx₁ hx hxx

theorem gap8 (a : ℤ → ℝ) (x₁ x x₂ : ℝ)
    (h₁ : LaurentSummableAt a x₁) (h₂ : LaurentSummableAt a x₂)
    (hx₁ : x₁ ≠ 0) (hx : x ≠ 0)
    (hleft : |x₁| < |x|) (hright : |x| < |x₂|) :
    Summable (positiveTerm a x) ∧ Summable (negativeTerm a x) := by
  constructor
  · exact gap5 a x x₂ (gap3 a x₂ h₂) hright
  · exact gap6 a x₁ x (gap2 a x₁ h₁) hx₁ hx hleft

theorem gap9 (a : ℤ → ℝ) (x₁ x x₂ : ℝ)
    (h₁ : LaurentSummableAt a x₁) (h₂ : LaurentSummableAt a x₂)
    (hx₁ : x₁ ≠ 0) (hx : x ≠ 0)
    (hleft : |x₁| < |x|) (hright : |x| < |x₂|) :
    LaurentSummableAt a x := by
  exact gap8 a x₁ x x₂ h₁ h₂ hx₁ hx hleft hright

theorem gap10 (a : ℤ → ℝ) (x₁ x x₂ : ℝ)
    (h₁ : LaurentSummableAt a x₁) (h₂ : LaurentSummableAt a x₂)
    (hx₁ : x₁ ≠ 0) (hx : x ≠ 0)
    (hleft : |x₁| < |x|) (hright : |x| < |x₂|) :
    LaurentSummableAt a x := by
  exact gap9 a x₁ x x₂ h₁ h₂ hx₁ hx hleft hright

end

end ProofGap.Exercise2737
