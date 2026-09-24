import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Topology.Neighborhoods
import Mathlib.Topology.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1439

noncomputable section

def y (x : ℝ) : ℝ := Real.log x ^ 2 / x
def domain : Set ℝ := Set.Ioi 0
def Approx (a b ε : ℝ) : Prop := |a - b| < ε

private theorem exp_double_upper (x a b : ℝ)
    (ha : Real.exp x < a) (ha0 : 0 < a) (hab : a * a < b) :
    Real.exp (x + x) < b := by
  rw [Real.exp_add]
  have hp : 0 < (a - Real.exp x) * (a + Real.exp x) :=
    mul_pos (sub_pos.mpr ha) (add_pos ha0 (Real.exp_pos x))
  have hs : Real.exp x * Real.exp x < a * a := by
    nlinarith
  exact lt_trans hs hab

private theorem exp_double_lower (x a b : ℝ)
    (ha : a < Real.exp x) (ha0 : 0 < a) (hab : b < a * a) :
    b < Real.exp (x + x) := by
  rw [Real.exp_add]
  have hp : 0 < (Real.exp x - a) * (Real.exp x + a) :=
    mul_pos (sub_pos.mpr ha) (add_pos (Real.exp_pos x) ha0)
  have hs : a * a < Real.exp x * Real.exp x := by
    nlinarith
  exact lt_trans hab hs

theorem gap1 (x : ℝ) (hx : 0 < x) :
    deriv y x = (2 * Real.log x - Real.log x ^ 2) / x ^ 2 := by
  unfold y
  have hx0 : x ≠ 0 := ne_of_gt hx
  have hderiv :=
    ((Real.hasDerivAt_log hx0).pow 2).div (hasDerivAt_id x) hx0
  convert hderiv.deriv using 1 <;>
    simp [id, hx0] <;>
    field_simp [hx0] <;>
    ring

theorem gap2 (x : ℝ) (hx : x = 1 ∨ x = Real.exp 2) :
    deriv y x = 0 := by
  rcases hx with hx | hx
  · subst x
    rw [gap1 1 zero_lt_one]
    norm_num
  · subst x
    rw [gap1 (Real.exp 2) (Real.exp_pos 2), Real.log_exp]
    ring

theorem gap3 (x : ℝ) (h₁ : 0 < x) (h₂ : x < 1) :
    deriv y x < 0 := by
  rw [gap1 x h₁]
  have hlog : Real.log x < 0 := Real.log_neg h₁ h₂
  have hden : 0 < x ^ 2 := pow_pos h₁ 2
  apply div_neg_of_neg_of_pos _ hden
  nlinarith [sq_nonneg (Real.log x)]

theorem gap4 (x : ℝ) (h₁ : 1 < x) (h₂ : x < Real.exp 2) :
    0 < deriv y x := by
  rw [gap1 x (lt_trans zero_lt_one h₁)]
  have hxpos : 0 < x := lt_trans zero_lt_one h₁
  have hlog_pos : 0 < Real.log x := Real.log_pos h₁
  have hlog_lt : Real.log x < 2 := by
    rw [← Real.exp_lt_exp, Real.exp_log hxpos]
    exact h₂
  have hprod : 0 < Real.log x * (2 - Real.log x) :=
    mul_pos hlog_pos (sub_pos.mpr hlog_lt)
  have hnum : 0 < 2 * Real.log x - Real.log x ^ 2 := by
    nlinarith
  exact div_pos hnum (pow_pos hxpos 2)

theorem gap5 (x : ℝ) (hx : Real.exp 2 < x) :
    deriv y x < 0 := by
  have hxpos : 0 < x := lt_trans (Real.exp_pos 2) hx
  rw [gap1 x hxpos]
  have hlog_gt : 2 < Real.log x := by
    rw [← Real.exp_lt_exp, Real.exp_log hxpos]
    exact hx
  have hlog_pos : 0 < Real.log x := lt_trans (by norm_num) hlog_gt
  have hprod : 0 < Real.log x * (Real.log x - 2) :=
    mul_pos hlog_pos (sub_pos.mpr hlog_gt)
  have hnum : 2 * Real.log x - Real.log x ^ 2 < 0 := by
    nlinarith
  exact div_neg_of_neg_of_pos hnum (pow_pos hxpos 2)

theorem gap6 : IsMinOn y domain 1 := by
  intro x hx
  change 0 < x at hx
  rw [show y 1 = 0 by norm_num [y]]
  unfold y
  exact div_nonneg (sq_nonneg (Real.log x)) (le_of_lt hx)

theorem gap7 : y 1 = 0 := by
  norm_num [y]

theorem gap8 : IsLocalMax y (Real.exp 2) := by
  change ∀ᶠ x in nhds (Real.exp 2), y x ≤ y (Real.exp 2)
  have hc : (1 : ℝ) < Real.exp 2 := by
    have h := Real.add_one_le_exp (2 : ℝ)
    norm_num at h ⊢
  filter_upwards [Ioi_mem_nhds hc] with x hx
  have hxpos : 0 < x := lt_trans zero_lt_one hx
  have hlog_pos : 0 < Real.log x := Real.log_pos hx
  let u : ℝ := (Real.log x - 2) / 2
  have hlin : Real.log x / 2 ≤ Real.exp u := by
    have h := Real.add_one_le_exp u
    dsimp [u] at h ⊢
    nlinarith
  have hmul :
      0 ≤ (Real.exp u - Real.log x / 2) *
        (Real.exp u + Real.log x / 2) := by
    apply mul_nonneg
    · exact sub_nonneg.mpr hlin
    · exact add_nonneg (le_of_lt (Real.exp_pos u))
        (le_of_lt (div_pos hlog_pos (by norm_num)))
  have hsq : (Real.log x / 2) ^ 2 ≤ Real.exp u ^ 2 := by
    nlinarith
  have hexpsq : Real.exp u ^ 2 = Real.exp (Real.log x - 2) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    dsimp [u]
    ring
  rw [hexpsq] at hsq
  have hsq' : Real.log x ^ 2 ≤ 4 * Real.exp (Real.log x - 2) := by
    nlinarith
  have hexpmul :
      Real.exp (Real.log x - 2) * Real.exp 2 = Real.exp (Real.log x) := by
    rw [← Real.exp_add]
    congr 1
    ring
  unfold y
  rw [Real.log_exp]
  apply (div_le_div_iff₀ hxpos (Real.exp_pos 2)).2
  calc
    Real.log x ^ 2 * Real.exp 2 ≤
        (4 * Real.exp (Real.log x - 2)) * Real.exp 2 :=
      mul_le_mul_of_nonneg_right hsq' (le_of_lt (Real.exp_pos 2))
    _ = 4 * Real.exp (Real.log x) := by rw [mul_assoc, hexpmul]
    _ = 2 ^ 2 * x := by
      rw [Real.exp_log hxpos]
      norm_num

theorem gap9 : y (Real.exp 2) = 4 / Real.exp 2 := by
  unfold y
  rw [Real.log_exp]
  norm_num

theorem gap10 : Approx (4 / Real.exp 2) 0.541 0.001 := by
  have hbaseUpper : Real.exp (1 / 512 : ℝ) < 1.001957 := by
    calc
      Real.exp (1 / 512 : ℝ) ≤ 1 / (1 - (1 / 512 : ℝ)) :=
        Real.exp_bound_div_one_sub_of_interval (by norm_num) (by norm_num)
      _ < 1.001957 := by norm_num
  have hu1 : Real.exp (1 / 256 : ℝ) < 1.003918 := by
    convert exp_double_upper (1 / 512 : ℝ) 1.001957 1.003918
      hbaseUpper (by norm_num) (by norm_num) using 1 <;> norm_num
  have hu2 : Real.exp (1 / 128 : ℝ) < 1.0078514 := by
    convert exp_double_upper (1 / 256 : ℝ) 1.003918 1.0078514
      hu1 (by norm_num) (by norm_num) using 1 <;> norm_num
  have hu3 : Real.exp (1 / 64 : ℝ) < 1.0157645 := by
    convert exp_double_upper (1 / 128 : ℝ) 1.0078514 1.0157645
      hu2 (by norm_num) (by norm_num) using 1 <;> norm_num
  have hu4 : Real.exp (1 / 32 : ℝ) < 1.0317776 := by
    convert exp_double_upper (1 / 64 : ℝ) 1.0157645 1.0317776
      hu3 (by norm_num) (by norm_num) using 1 <;> norm_num
  have hu5 : Real.exp (1 / 16 : ℝ) < 1.0645651 := by
    convert exp_double_upper (1 / 32 : ℝ) 1.0317776 1.0645651
      hu4 (by norm_num) (by norm_num) using 1 <;> norm_num
  have hu6 : Real.exp (1 / 8 : ℝ) < 1.133299 := by
    convert exp_double_upper (1 / 16 : ℝ) 1.0645651 1.133299
      hu5 (by norm_num) (by norm_num) using 1 <;> norm_num
  have hu7 : Real.exp (1 / 4 : ℝ) < 1.2843667 := by
    convert exp_double_upper (1 / 8 : ℝ) 1.133299 1.2843667
      hu6 (by norm_num) (by norm_num) using 1 <;> norm_num
  have hu8 : Real.exp (1 / 2 : ℝ) < 1.649598 := by
    convert exp_double_upper (1 / 4 : ℝ) 1.2843667 1.649598
      hu7 (by norm_num) (by norm_num) using 1 <;> norm_num
  have hu9 : Real.exp (1 : ℝ) < 2.721174 := by
    convert exp_double_upper (1 / 2 : ℝ) 1.649598 2.721174
      hu8 (by norm_num) (by norm_num) using 1 <;> norm_num
  have hu10 : Real.exp (2 : ℝ) < 7.404788 := by
    convert exp_double_upper (1 : ℝ) 2.721174 7.404788
      hu9 (by norm_num) (by norm_num) using 1 <;> norm_num
  have hbaseLower : (1.0009765 : ℝ) < Real.exp (1 / 1024 : ℝ) := by
    calc
      (1.0009765 : ℝ) < 1 + (1 / 1024 : ℝ) := by norm_num
      _ ≤ Real.exp (1 / 1024 : ℝ) := by
        simpa [add_comm] using
          (Real.add_one_le_exp (1 / 1024 : ℝ))
  have hl1 : (1.0019539 : ℝ) < Real.exp (1 / 512 : ℝ) := by
    convert exp_double_lower (1 / 1024 : ℝ) 1.0009765 1.0019539
      hbaseLower (by norm_num) (by norm_num) using 1 <;> norm_num
  have hl2 : (1.0039116 : ℝ) < Real.exp (1 / 256 : ℝ) := by
    convert exp_double_lower (1 / 512 : ℝ) 1.0019539 1.0039116
      hl1 (by norm_num) (by norm_num) using 1 <;> norm_num
  have hl3 : (1.0078385 : ℝ) < Real.exp (1 / 128 : ℝ) := by
    convert exp_double_lower (1 / 256 : ℝ) 1.0039116 1.0078385
      hl2 (by norm_num) (by norm_num) using 1 <;> norm_num
  have hl4 : (1.0157384 : ℝ) < Real.exp (1 / 64 : ℝ) := by
    convert exp_double_lower (1 / 128 : ℝ) 1.0078385 1.0157384
      hl3 (by norm_num) (by norm_num) using 1 <;> norm_num
  have hl5 : (1.0317244 : ℝ) < Real.exp (1 / 32 : ℝ) := by
    convert exp_double_lower (1 / 64 : ℝ) 1.0157384 1.0317244
      hl4 (by norm_num) (by norm_num) using 1 <;> norm_num
  have hl6 : (1.0644552 : ℝ) < Real.exp (1 / 16 : ℝ) := by
    convert exp_double_lower (1 / 32 : ℝ) 1.0317244 1.0644552
      hl5 (by norm_num) (by norm_num) using 1 <;> norm_num
  have hl7 : (1.1330648 : ℝ) < Real.exp (1 / 8 : ℝ) := by
    convert exp_double_lower (1 / 16 : ℝ) 1.0644552 1.1330648
      hl6 (by norm_num) (by norm_num) using 1 <;> norm_num
  have hl8 : (1.2838358 : ℝ) < Real.exp (1 / 4 : ℝ) := by
    convert exp_double_lower (1 / 8 : ℝ) 1.1330648 1.2838358
      hl7 (by norm_num) (by norm_num) using 1 <;> norm_num
  have hl9 : (1.6482343 : ℝ) < Real.exp (1 / 2 : ℝ) := by
    convert exp_double_lower (1 / 4 : ℝ) 1.2838358 1.6482343
      hl8 (by norm_num) (by norm_num) using 1 <;> norm_num
  have hl10 : (2.7166763 : ℝ) < Real.exp (1 : ℝ) := by
    convert exp_double_lower (1 / 2 : ℝ) 1.6482343 2.7166763
      hl9 (by norm_num) (by norm_num) using 1 <;> norm_num
  have hl11 : (7.38033 : ℝ) < Real.exp (2 : ℝ) := by
    convert exp_double_lower (1 : ℝ) 2.7166763 7.38033
      hl10 (by norm_num) (by norm_num) using 1 <;> norm_num
  have hlower : (2000 / 271 : ℝ) < Real.exp 2 :=
    lt_trans (by norm_num) hl11
  have hupper : Real.exp 2 < (200 / 27 : ℝ) :=
    lt_trans hu10 (by norm_num)
  have hE : 0 < Real.exp 2 := Real.exp_pos 2
  have hleft : (27 / 50 : ℝ) < 4 / Real.exp 2 := by
    apply (div_lt_div_iff₀ (by norm_num : (0 : ℝ) < 50) hE).2
    nlinarith [hupper]
  have hright : 4 / Real.exp 2 < (271 / 500 : ℝ) := by
    apply (div_lt_div_iff₀ hE (by norm_num : (0 : ℝ) < 500)).2
    nlinarith [hlower]
  unfold Approx
  rw [abs_lt]
  constructor
  · norm_num at hleft ⊢
    linarith
  · norm_num at hright ⊢
    linarith

end
end ProofGap.Exercise1439
