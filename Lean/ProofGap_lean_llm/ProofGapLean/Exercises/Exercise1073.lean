import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1073

noncomputable section

def parabola (a x : ℝ) : ℝ := a * x ^ 2

def curvesTangent (a : ℝ) : Prop :=
  ∃ x, 0 < x ∧ parabola a x = Real.log x ∧
    deriv (parabola a) x = deriv Real.log x

private theorem tangent_data (a : ℝ) (htan : curvesTangent a) :
    ∃ x, 0 < x ∧ parabola a x = Real.log x ∧ 2 * a * x ^ 2 = 1 := by
  rcases htan with ⟨x, hx, hvalue, hderiv⟩
  have hparabola : HasDerivAt (parabola a) (2 * a * x) x := by
    convert ((hasDerivAt_const (x := x) (c := a)).mul
      ((hasDerivAt_id x).pow 2)) using 1 <;>
      simp [parabola] <;> ring
  have hlog : HasDerivAt Real.log x⁻¹ x :=
    Real.hasDerivAt_log hx.ne'
  have hderiv' : 2 * a * x = x⁻¹ := by
    rw [hparabola.deriv, hlog.deriv] at hderiv
    exact hderiv
  have hproduct : 2 * a * x ^ 2 = 1 := by
    calc
      2 * a * x ^ 2 = (2 * a * x) * x := by ring
      _ = x⁻¹ * x := by rw [hderiv']
      _ = 1 := by simp [hx.ne']
  exact ⟨x, hx, hvalue, hproduct⟩

theorem gap1 (a : ℝ) (htan : curvesTangent a) :
    ∃ x, 0 < x ∧ deriv (parabola a) x = deriv Real.log x := by
  rcases htan with ⟨x, hx, _, hderiv⟩
  exact ⟨x, hx, hderiv⟩

theorem gap2 (a : ℝ) (htan : curvesTangent a) :
    ∃ x, 0 < x ∧ x ^ 2 = 1 / (2 * a) := by
  rcases tangent_data a htan with ⟨x, hx, _, hproduct⟩
  have ha : a ≠ 0 := by
    intro ha
    subst a
    norm_num at hproduct
  refine ⟨x, hx, ?_⟩
  apply (eq_div_iff (mul_ne_zero (by norm_num) ha)).2
  nlinarith [hproduct]

theorem gap3 (a : ℝ) (htan : curvesTangent a) :
    ∃ y : ℝ, y = a * (1 / (2 * a)) := by
  exact ⟨a * (1 / (2 * a)), rfl⟩

theorem gap4 (a : ℝ) (ha : a ≠ 0) :
    a * (1 / (2 * a)) = 1 / 2 := by
  field_simp [ha] <;> ring

theorem gap5 : ∃ y : ℝ, y = 1 / 2 := by
  exact ⟨1 / 2, rfl⟩

theorem gap6 :
    ∃ x : ℝ, 0 < x ∧ Real.log x = 1 / 2 := by
  refine ⟨Real.exp (1 / 2 : ℝ), Real.exp_pos _, ?_⟩
  rw [Real.log_exp]

theorem gap7 :
    ∃ x : ℝ, x = Real.sqrt (Real.exp 1) := by
  exact ⟨Real.sqrt (Real.exp 1), rfl⟩

theorem gap8 (a : ℝ) (htan : curvesTangent a) :
    ∃ x, 0 < x ∧ a = 1 / (2 * x ^ 2) := by
  rcases tangent_data a htan with ⟨x, hx, _, hproduct⟩
  have hxne : x ≠ 0 := hx.ne'
  refine ⟨x, hx, ?_⟩
  apply (eq_div_iff (mul_ne_zero (by norm_num) (pow_ne_zero 2 hxne))).2
  nlinarith [hproduct]

theorem gap9 :
    1 / (2 * (Real.sqrt (Real.exp 1)) ^ 2) =
      1 / (2 * Real.exp 1) := by
  rw [Real.sq_sqrt (le_of_lt (Real.exp_pos 1))]

theorem gap10 (a : ℝ) (htan : curvesTangent a) :
    a = 1 / (2 * Real.exp 1) := by
  rcases tangent_data a htan with ⟨x, hx, hvalue, hproduct⟩
  have hvalue' : a * x ^ 2 = Real.log x := by
    simpa [parabola] using hvalue
  have hlog : Real.log x = 1 / 2 := by
    nlinarith [hvalue', hproduct]
  have hxexp : x = Real.exp (1 / 2 : ℝ) := by
    calc
      x = Real.exp (Real.log x) := (Real.exp_log hx).symm
      _ = Real.exp (1 / 2 : ℝ) := by rw [hlog]
  have hx2 : x ^ 2 = Real.exp 1 := by
    rw [hxexp, pow_two, ← Real.exp_add]
    norm_num
  apply (eq_div_iff (mul_ne_zero (by norm_num) (ne_of_gt (Real.exp_pos 1)))).2
  rw [← hx2]
  nlinarith [hproduct]

theorem gap11 (a : ℝ) :
    a ∈ ({1 / (2 * Real.exp 1)} : Set ℝ) ↔ curvesTangent a := by
  constructor
  · intro ha
    have ha' : a = 1 / (2 * Real.exp 1) := by
      simpa using ha
    subst a
    let x : ℝ := Real.exp (1 / 2 : ℝ)
    have hx : 0 < x := by
      dsimp [x]
      exact Real.exp_pos _
    have he : Real.exp 1 ≠ 0 := ne_of_gt (Real.exp_pos 1)
    have hx2 : x ^ 2 = Real.exp 1 := by
      dsimp [x]
      rw [pow_two, ← Real.exp_add]
      norm_num
    have hproduct : 2 * (1 / (2 * Real.exp 1)) * x ^ 2 = 1 := by
      rw [hx2]
      field_simp [he] <;> ring
    refine ⟨x, hx, ?_, ?_⟩
    · have hlogvalue : Real.log x = 1 / 2 := by
        dsimp [x]
        rw [Real.log_exp]
      change (1 / (2 * Real.exp 1)) * x ^ 2 = Real.log x
      nlinarith [hproduct, hlogvalue]
    · have hparabola :
          HasDerivAt (parabola (1 / (2 * Real.exp 1)))
            (2 * (1 / (2 * Real.exp 1)) * x) x := by
        convert ((hasDerivAt_const (x := x) (c := (1 / (2 * Real.exp 1)))).mul
          ((hasDerivAt_id x).pow 2)) using 1 <;>
          simp [parabola] <;> ring
      have hlogderiv : HasDerivAt Real.log x⁻¹ x :=
        Real.hasDerivAt_log hx.ne'
      rw [hparabola.deriv, hlogderiv.deriv]
      field_simp [hx.ne', he] <;> nlinarith [hx2]
  · intro htan
    simpa using (gap10 a htan)

end

end ProofGap.Exercise1073
