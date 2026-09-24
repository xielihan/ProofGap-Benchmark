import ProofGapLean.Prelude.Sequences
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise469

noncomputable section

def f (a b x : ℝ) : ℝ := (x ^ 2 + 1) / (x + 1) - a * x - b
def expanded (a b x : ℝ) : ℝ :=
  ((1 - a) * x ^ 2 - (a + b) * x + 1 - b) / (x + 1)
def HasLimitZero (a b : ℝ) : Prop :=
  Filter.Tendsto (f a b) Filter.atTop (nhds 0)

/-- Source: `proof_gap/exercise_469/1.txt`; remove the malformed quantifier/limit biconditional and state the algebraic identity on its domain. -/
private theorem limit_coefficients_characterization (a b : ℝ) :
    HasLimitZero a b ↔ a = 1 ∧ a + b = 0 := by
  have h_add : Filter.Tendsto (fun x : ℝ => x + 1) Filter.atTop Filter.atTop := by
    refine Filter.tendsto_atTop.2 ?_
    intro r
    filter_upwards [Filter.eventually_ge_atTop (r - 1)] with x hx
    linarith
  have h_inv_x :
      Filter.Tendsto (fun x : ℝ => x⁻¹) Filter.atTop (nhds 0) :=
    tendsto_inv_atTop_zero
  have h_inv_shift :
      Filter.Tendsto (fun x : ℝ => (x + 1)⁻¹) Filter.atTop (nhds 0) :=
    h_inv_x.comp h_add
  have h_rem :
      Filter.Tendsto (fun x : ℝ => 2 / (x + 1)) Filter.atTop (nhds 0) := by
    simpa [div_eq_mul_inv] using
      ((tendsto_const_nhds :
          Filter.Tendsto (fun _ : ℝ => (2 : ℝ)) Filter.atTop (nhds 2)).mul
        h_inv_shift)
  constructor
  · intro h
    change Filter.Tendsto (f a b) Filter.atTop (nhds 0) at h
    have h_scaled_zero :
        Filter.Tendsto (fun x : ℝ => f a b x * x⁻¹)
          Filter.atTop (nhds 0) := by
      simpa using h.mul h_inv_x
    have h_const_inv :
        Filter.Tendsto (fun x : ℝ => (-(1 + b)) * x⁻¹)
          Filter.atTop (nhds 0) := by
      simpa using
        ((tendsto_const_nhds :
            Filter.Tendsto (fun _ : ℝ => -(1 + b)) Filter.atTop
              (nhds (-(1 + b)))).mul h_inv_x)
    have h_rem_inv :
        Filter.Tendsto (fun x : ℝ => (2 / (x + 1)) * x⁻¹)
          Filter.atTop (nhds 0) := by
      simpa using h_rem.mul h_inv_x
    have h_linear_limit :
        Filter.Tendsto
          (fun x : ℝ =>
            (1 - a) + ((-(1 + b)) * x⁻¹ + (2 / (x + 1)) * x⁻¹))
          Filter.atTop (nhds (1 - a)) := by
      simpa using
        ((tendsto_const_nhds :
            Filter.Tendsto (fun _ : ℝ => 1 - a) Filter.atTop
              (nhds (1 - a))).add (h_const_inv.add h_rem_inv))
    have h_eq_scaled :
        (fun x : ℝ => f a b x * x⁻¹) =ᶠ[Filter.atTop]
          (fun x : ℝ =>
            (1 - a) + ((-(1 + b)) * x⁻¹ + (2 / (x + 1)) * x⁻¹)) := by
      filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with x hx
      have hx0 : x ≠ 0 := by
        linarith
      have hx1 : x + 1 ≠ 0 := by
        linarith
      unfold f
      field_simp [hx0, hx1]
      <;> ring
    have h_scaled_coeff :
        Filter.Tendsto (fun x : ℝ => f a b x * x⁻¹)
          Filter.atTop (nhds (1 - a)) :=
      h_linear_limit.congr' h_eq_scaled.symm
    have hcoeff : (0 : ℝ) = 1 - a :=
      tendsto_nhds_unique h_scaled_zero h_scaled_coeff
    have ha : a = 1 := by
      linarith
    subst a
    have h_const_limit :
        Filter.Tendsto (fun x : ℝ => -(1 + b) + 2 / (x + 1))
          Filter.atTop (nhds (-(1 + b))) := by
      simpa using
        ((tendsto_const_nhds :
            Filter.Tendsto (fun _ : ℝ => -(1 + b)) Filter.atTop
              (nhds (-(1 + b)))).add h_rem)
    have h_eq_const :
        (fun x : ℝ => f 1 b x) =ᶠ[Filter.atTop]
          (fun x : ℝ => -(1 + b) + 2 / (x + 1)) := by
      filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with x hx
      have hx1 : x + 1 ≠ 0 := by
        linarith
      unfold f
      field_simp [hx1]
      <;> ring
    have h_f_const :
        Filter.Tendsto (f 1 b) Filter.atTop (nhds (-(1 + b))) :=
      h_const_limit.congr' h_eq_const.symm
    have hb : (0 : ℝ) = -(1 + b) :=
      tendsto_nhds_unique h h_f_const
    exact ⟨rfl, by linarith⟩
  · rintro ⟨ha, hab⟩
    subst a
    have hb : b = -1 := by
      linarith
    subst b
    change Filter.Tendsto (f 1 (-1)) Filter.atTop (nhds 0)
    have h_eq_final :
        (fun x : ℝ => f 1 (-1) x) =ᶠ[Filter.atTop]
          (fun x : ℝ => 2 / (x + 1)) := by
      filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with x hx
      have hx1 : x + 1 ≠ 0 := by
        linarith
      unfold f
      field_simp [hx1]
      <;> ring
    exact h_rem.congr' h_eq_final.symm

theorem gap1 (a b x : ℝ) (hx : x ≠ -1) : f a b x = expanded a b x := by
  have hden : x + 1 ≠ 0 := by
    intro h
    apply hx
    calc
      x = (x + 1) - 1 := by ring
      _ = 0 - 1 := by rw [h]
      _ = -1 := by ring
  unfold f expanded
  field_simp [hden]
  <;> ring

/-- Source: `proof_gap/exercise_469/2.txt`; the coefficient condition is necessary, not by itself equivalent. -/
theorem gap2 (a b : ℝ) : HasLimitZero a b → 1 - a = 0 := by
  intro h
  have ha : a = 1 := ((limit_coefficients_characterization a b).1 h).1
  linarith

/-- Source: `proof_gap/exercise_469/3.txt`; the second coefficient condition is also necessary. -/
theorem gap3 (a b : ℝ) : HasLimitZero a b → a + b = 0 := by
  intro h
  exact ((limit_coefficients_characterization a b).1 h).2

/-- Source: `proof_gap/exercise_469/4.txt`; retain both coefficient conditions in the exact characterization. -/
theorem gap4 (a b : ℝ) : HasLimitZero a b ↔ a = 1 ∧ a + b = 0 := by
  exact limit_coefficients_characterization a b

/-- Source: `proof_gap/exercise_469/5.txt`; retain both coefficient conditions in the exact characterization. -/
theorem gap5 (a b : ℝ) : HasLimitZero a b ↔ a = 1 ∧ b = -1 := by
  constructor
  · intro h
    have hc : a = 1 ∧ a + b = 0 := (gap4 a b).1 h
    exact ⟨hc.1, by linarith [hc.2]⟩
  · rintro ⟨ha, hb⟩
    apply (gap4 a b).2
    exact ⟨ha, by linarith⟩

/-- Source: `proof_gap/exercise_469/6.txt`. -/
theorem gap6 (a b : ℝ) (hab : (a, b) = (1, -1)) : HasLimitZero a b := by
  have ha : a = 1 := congrArg Prod.fst hab
  have hb : b = -1 := congrArg Prod.snd hab
  exact (gap5 a b).2 ⟨ha, hb⟩

end

end ProofGap.Exercise469
