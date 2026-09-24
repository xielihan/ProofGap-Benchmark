import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise497

noncomputable section

def original (a x : ℝ) : ℝ :=
  (Real.tan (a + x) * Real.tan (a - x) - Real.tan a ^ 2) / x ^ 2
def additionForm (a x : ℝ) : ℝ :=
  (((Real.tan a + Real.tan x) / (1 - Real.tan a * Real.tan x)) *
    ((Real.tan a - Real.tan x) / (1 + Real.tan a * Real.tan x)) -
    Real.tan a ^ 2) / x ^ 2
def normalized (a x : ℝ) : ℝ :=
  (Real.tan x ^ 2 * (Real.tan a ^ 4 - 1)) /
    (x ^ 2 * (1 - Real.tan a ^ 2 * Real.tan x ^ 2))
def HasLimitAtZero (f : ℝ → ℝ) (L : ℝ) : Prop :=
  Filter.Tendsto f (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds L)

/-- Source: `proof_gap/exercise_497/1.txt`; require `cos a≠0`. -/
private theorem tendstoTanZero :
    Filter.Tendsto Real.tan (nhds (0 : ℝ)) (nhds 0) := by
  have hsin : ContinuousAt Real.sin 0 :=
    Real.continuous_sin.continuousAt
  have hcos : ContinuousAt Real.cos 0 :=
    Real.continuous_cos.continuousAt
  have hquotAt : ContinuousAt (fun x : ℝ => Real.sin x / Real.cos x) 0 :=
    hsin.div hcos (by norm_num : Real.cos (0 : ℝ) ≠ 0)
  have hquot :
      Filter.Tendsto (fun x : ℝ => Real.sin x / Real.cos x)
        (nhds 0) (nhds 0) := by
    change Filter.Tendsto (fun x : ℝ => Real.sin x / Real.cos x)
      (nhds 0) (nhds ((fun x : ℝ => Real.sin x / Real.cos x) 0)) at hquotAt
    simpa using hquotAt
  refine hquot.congr' (Filter.Eventually.of_forall ?_)
  intro x
  rw [Real.tan_eq_sin_div_cos]

theorem gap1 (a : ℝ) (ha : Real.cos a ≠ 0) (L : ℝ) :
    HasLimitAtZero (original a) L ↔ HasLimitAtZero (additionForm a) L := by
  have hcosAt : ContinuousAt Real.cos 0 :=
    Real.continuous_cos.continuousAt
  change Filter.Tendsto Real.cos (nhds 0) (nhds (Real.cos 0)) at hcosAt
  have hcos0 :
      Filter.Tendsto Real.cos (nhds 0) (nhds 1) := by
    simpa using hcosAt
  have hcos :
      Filter.Tendsto Real.cos
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1) :=
    hcos0.mono_left inf_le_left
  have hcos_ne :
      ∀ᶠ x in nhdsWithin 0 ({0} : Set ℝ)ᶜ, Real.cos x ≠ 0 :=
    hcos.eventually
      (eventually_ne_nhds (by norm_num : (1 : ℝ) ≠ 0))
  have heq :
      original a =ᶠ[nhdsWithin 0 ({0} : Set ℝ)ᶜ] additionForm a := by
    filter_upwards [hcos_ne] with x hx
    have hregular (y : ℝ) (hy : Real.cos y ≠ 0) :
        ∀ k : ℤ, y ≠ (2 * (k : ℝ) + 1) * Real.pi / 2 := by
      intro k hk
      apply hy
      exact Real.cos_eq_zero_iff.mpr ⟨k, hk⟩
    have hcond :
        ((∀ k : ℤ, a ≠ (2 * (k : ℝ) + 1) * Real.pi / 2) ∧
          ∀ l : ℤ, x ≠ (2 * (l : ℝ) + 1) * Real.pi / 2) ∨
        ((∃ k : ℤ, a = (2 * (k : ℝ) + 1) * Real.pi / 2) ∧
          ∃ l : ℤ, x = (2 * (l : ℝ) + 1) * Real.pi / 2) :=
      Or.inl ⟨hregular a ha, hregular x hx⟩
    unfold original additionForm
    rw [Real.tan_add (x := a) (y := x) hcond,
      Real.tan_sub (x := a) (y := x) hcond]
  constructor
  · intro h
    unfold HasLimitAtZero at h ⊢
    exact h.congr' heq
  · intro h
    unfold HasLimitAtZero at h ⊢
    exact h.congr' heq.symm

/-- Source: `proof_gap/exercise_497/2.txt`; require `cos a≠0`. -/
theorem gap2 (a : ℝ) (ha : Real.cos a ≠ 0) (L : ℝ) :
    HasLimitAtZero (original a) L ↔ HasLimitAtZero (normalized a) L := by
  let F := nhdsWithin 0 ({0} : Set ℝ)ᶜ
  have htan : Filter.Tendsto Real.tan F (nhds 0) :=
    tendstoTanZero.mono_left inf_le_left
  have hone :
      Filter.Tendsto (fun _ : ℝ => (1 : ℝ)) F (nhds 1) :=
    tendsto_const_nhds
  have ha_const :
      Filter.Tendsto (fun _ : ℝ => Real.tan a) F (nhds (Real.tan a)) :=
    tendsto_const_nhds
  have hminus :
      Filter.Tendsto (fun x : ℝ => 1 - Real.tan a * Real.tan x)
        F (nhds 1) := by
    simpa using hone.sub (ha_const.mul htan)
  have hplus :
      Filter.Tendsto (fun x : ℝ => 1 + Real.tan a * Real.tan x)
        F (nhds 1) := by
    simpa using hone.add (ha_const.mul htan)
  have hminus_ne :
      ∀ᶠ x in F, 1 - Real.tan a * Real.tan x ≠ 0 :=
    hminus.eventually
      (eventually_ne_nhds (by norm_num : (1 : ℝ) ≠ 0))
  have hplus_ne :
      ∀ᶠ x in F, 1 + Real.tan a * Real.tan x ≠ 0 :=
    hplus.eventually
      (eventually_ne_nhds (by norm_num : (1 : ℝ) ≠ 0))
  have heq : additionForm a =ᶠ[F] normalized a := by
    filter_upwards [hminus_ne, hplus_ne, self_mem_nhdsWithin] with x hm hp hx
    have hx0 : x ≠ 0 := by
      simpa using hx
    have hfactor :
        1 - Real.tan a ^ 2 * Real.tan x ^ 2 =
          (1 - Real.tan a * Real.tan x) *
            (1 + Real.tan a * Real.tan x) := by
      ring
    have hden : 1 - Real.tan a ^ 2 * Real.tan x ^ 2 ≠ 0 := by
      rw [hfactor]
      exact mul_ne_zero hm hp
    unfold additionForm normalized
    field_simp [hx0, hm, hp, hden] <;> ring
  constructor
  · intro h
    have hadd : HasLimitAtZero (additionForm a) L :=
      (gap1 a ha L).mp h
    unfold HasLimitAtZero at hadd ⊢
    exact hadd.congr' heq
  · intro h
    have hadd : HasLimitAtZero (additionForm a) L := by
      unfold HasLimitAtZero at h ⊢
      exact h.congr' heq.symm
    exact (gap1 a ha L).mpr hadd

/-- Source: `proof_gap/exercise_497/3.txt`; require `cos a≠0`. -/
theorem gap3 (a : ℝ) (ha : Real.cos a ≠ 0) :
    HasLimitAtZero (normalized a) (Real.tan a ^ 4 - 1) := by
  let F := nhdsWithin 0 ({0} : Set ℝ)ᶜ
  have hcosAt : ContinuousAt Real.cos 0 :=
    Real.continuous_cos.continuousAt
  change Filter.Tendsto Real.cos (nhds 0) (nhds (Real.cos 0)) at hcosAt
  have hcos0 :
      Filter.Tendsto Real.cos (nhds 0) (nhds 1) := by
    simpa using hcosAt
  have hcos :
      Filter.Tendsto Real.cos F (nhds 1) :=
    hcos0.mono_left inf_le_left
  have hslope :
      Filter.Tendsto (fun x : ℝ => x⁻¹ * Real.sin x) F (nhds 1) := by
    simpa [F] using
      (Real.hasDerivAt_sin (0 : ℝ)).tendsto_slope_zero
  have hsinratio :
      Filter.Tendsto (fun x : ℝ => Real.sin x / x) F (nhds 1) := by
    refine hslope.congr' (Filter.Eventually.of_forall ?_)
    intro x
    simp only [div_eq_mul_inv]
    exact mul_comm x⁻¹ (Real.sin x)
  have hraw :
      Filter.Tendsto
        ((fun x : ℝ => Real.sin x / x) / Real.cos)
        F (nhds ((1 : ℝ) / 1)) :=
    hsinratio.div hcos (by norm_num : (1 : ℝ) ≠ 0)
  have hraw1 :
      Filter.Tendsto
        ((fun x : ℝ => Real.sin x / x) / Real.cos)
        F (nhds 1) := by
    simpa only [div_one] using hraw
  have hratio :
      Filter.Tendsto (fun x : ℝ => Real.tan x / x) F (nhds 1) := by
    refine hraw1.congr' (Filter.Eventually.of_forall ?_)
    intro x
    change Real.sin x / x / Real.cos x = Real.tan x / x
    rw [Real.tan_eq_sin_div_cos]
    ring
  have htan : Filter.Tendsto Real.tan F (nhds 0) :=
    tendstoTanZero.mono_left inf_le_left
  have hconst :
      Filter.Tendsto
        (fun _ : ℝ => Real.tan a ^ 4 - 1) F
        (nhds (Real.tan a ^ 4 - 1)) :=
    tendsto_const_nhds
  have hnum :
      Filter.Tendsto
        (fun x : ℝ => (Real.tan x / x) ^ 2 * (Real.tan a ^ 4 - 1))
        F (nhds (Real.tan a ^ 4 - 1)) := by
    simpa using (hratio.pow 2).mul hconst
  have hone :
      Filter.Tendsto (fun _ : ℝ => (1 : ℝ)) F (nhds 1) :=
    tendsto_const_nhds
  have ha_const :
      Filter.Tendsto (fun _ : ℝ => Real.tan a ^ 2) F
        (nhds (Real.tan a ^ 2)) :=
    tendsto_const_nhds
  have hden :
      Filter.Tendsto
        (fun x : ℝ => 1 - Real.tan a ^ 2 * Real.tan x ^ 2)
        F (nhds 1) := by
    simpa using hone.sub (ha_const.mul (htan.pow 2))
  have hquot :
      Filter.Tendsto
        (fun x : ℝ =>
          ((Real.tan x / x) ^ 2 * (Real.tan a ^ 4 - 1)) /
            (1 - Real.tan a ^ 2 * Real.tan x ^ 2))
        F (nhds (Real.tan a ^ 4 - 1)) := by
    simpa using
      hnum.div hden (by norm_num : (1 : ℝ) ≠ 0)
  unfold HasLimitAtZero
  refine hquot.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hx0 : x ≠ 0 := by
    simpa using hx
  unfold normalized
  by_cases hd : 1 - Real.tan a ^ 2 * Real.tan x ^ 2 = 0
  · simp [hd]
  · field_simp [hx0, hd] <;> ring

/-- Source: `proof_gap/exercise_497/4.txt`; require `cos a≠0`. -/
theorem gap4 (a : ℝ) (ha : Real.cos a ≠ 0) :
    HasLimitAtZero (original a) (Real.tan a ^ 4 - 1) := by
  exact
    (gap2 a ha (Real.tan a ^ 4 - 1)).mpr (gap3 a ha)

/-- Source: `proof_gap/exercise_497/5.txt`; require `cos a≠0`. -/
theorem gap5 (a : ℝ) (ha : Real.cos a ≠ 0) :
    Real.tan a ^ 4 - 1 = -Real.cos (2 * a) / Real.cos a ^ 4 := by
  rw [Real.tan_eq_sin_div_cos]
  field_simp [ha]
  rw [Real.cos_two_mul]
  calc
    Real.sin a ^ 4 - Real.cos a ^ 4 =
        (Real.sin a ^ 2 - Real.cos a ^ 2) *
          (Real.sin a ^ 2 + Real.cos a ^ 2) := by
      ring
    _ = Real.sin a ^ 2 - Real.cos a ^ 2 := by
      rw [Real.sin_sq_add_cos_sq]
      ring
    _ = -(2 * Real.cos a ^ 2 - 1) := by
      nlinarith [Real.sin_sq_add_cos_sq a]

end

end ProofGap.Exercise497
