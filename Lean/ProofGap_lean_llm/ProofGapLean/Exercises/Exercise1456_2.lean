import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

namespace ProofGap.Exercise1456_2

noncomputable section

def f (p x : ℝ) : ℝ := Real.rpow x p + Real.rpow (1 - x) p
def domain : Set ℝ := Set.Icc 0 1

theorem gap1 (p : ℝ) (hp : 1 < p) :
    IsMinOn (f p) domain (1 / 2) := by
  rw [isMinOn_iff]
  intro x hx
  change x ∈ Set.Icc (0 : ℝ) 1 at hx
  have hconv := convexOn_rpow hp.le
  have hj := hconv.2 hx.1 (sub_nonneg.mpr hx.2)
    (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    (show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num)
  have hmid :
      (1 / 2 : ℝ) * x + 1 / 2 * (1 - x) = 1 / 2 := by
    ring
  simp only [smul_eq_mul] at hj
  rw [hmid] at hj
  unfold f
  norm_num at hj ⊢
  nlinarith

theorem gap2 (p : ℝ) :
    f p (1 / 2) = 1 / Real.rpow 2 (p - 1) := by
  unfold f
  rw [show 1 - (1 / 2 : ℝ) = 1 / 2 by norm_num]
  change (1 / 2 : ℝ) ^ p + (1 / 2 : ℝ) ^ p =
    1 / (2 : ℝ) ^ (p - 1)
  rw [Real.div_rpow (by norm_num) (by norm_num) p]
  simp only [Real.one_rpow]
  rw [Real.rpow_sub (by norm_num : (0 : ℝ) < 2), Real.rpow_one]
  have hpow : 0 < Real.rpow 2 p :=
    Real.rpow_pos_of_pos (by norm_num) p
  field_simp [hpow.ne']
  ring

theorem gap3 (p : ℝ) (hp : 1 < p) : f p 0 = f p 1 := by
  simp [f, Real.zero_rpow (by linarith : p ≠ 0)]

theorem gap4 (p : ℝ) (hp : 1 < p) : f p 1 = 1 := by
  simp [f, Real.zero_rpow (by linarith : p ≠ 0)]

theorem gap5 (p : ℝ) (hp : 1 < p) : f p 0 = 1 := by
  simp [f, Real.zero_rpow (by linarith : p ≠ 0)]

theorem gap6 (p x : ℝ) (hp : 1 < p) (hx : x ∈ domain) :
    1 / Real.rpow 2 (p - 1) ≤ f p x := by
  rw [← gap2 p]
  exact (isMinOn_iff.mp (gap1 p hp)) x hx

theorem gap7 (p x : ℝ) (hp : 1 < p) (hx : x ∈ domain) :
    f p x ≤ 1 := by
  change x ∈ Set.Icc (0 : ℝ) 1 at hx
  unfold f
  have hxpow : Real.rpow x p ≤ x :=
    Real.rpow_le_self_of_le_one hx.1 hx.2 hp.le
  have hupow : Real.rpow (1 - x) p ≤ 1 - x :=
    Real.rpow_le_self_of_le_one
      (sub_nonneg.mpr hx.2) (by linarith [hx.1]) hp.le
  linarith

theorem gap8 (p : ℝ) (hp : 1 < p) :
    1 / Real.rpow 2 (p - 1) ≤ 1 := by
  have hpowpos : 0 < Real.rpow 2 (p - 1) :=
    Real.rpow_pos_of_pos (by norm_num) _
  apply (div_le_iff₀ hpowpos).2
  simpa using
    (Real.one_le_rpow (show (1 : ℝ) ≤ 2 by norm_num)
      (show (0 : ℝ) ≤ p - 1 by linarith))

theorem gap9 (p x : ℝ) (hp : 1 < p) (hx₀ : 0 ≤ x) (hx₁ : x ≤ 1) :
    1 / Real.rpow 2 (p - 1) ≤ f p x ∧ f p x ≤ 1 := by
  have hx : x ∈ domain := by
    exact ⟨hx₀, hx₁⟩
  exact ⟨gap6 p x hp hx, gap7 p x hp hx⟩

end
end ProofGap.Exercise1456_2
