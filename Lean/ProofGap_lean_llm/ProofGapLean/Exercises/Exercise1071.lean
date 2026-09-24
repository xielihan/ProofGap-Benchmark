import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1071

noncomputable section

def quadratic (a b c x : ℝ) : ℝ := a * x ^ 2 + b * x + c

def tangentToXAxis (a b c : ℝ) : Prop :=
  ∃ x, deriv (quadratic a b c) x = 0 ∧ quadratic a b c x = 0

private theorem quadratic_discriminant_identity (a b c x : ℝ) :
    (4 * a) * quadratic a b c x + (b ^ 2 - 4 * a * c) =
      (2 * a * x + b) ^ 2 := by
  unfold quadratic
  ring

theorem gap1 (a b c x : ℝ) :
    HasDerivAt (quadratic a b c) (2 * a * x + b) x := by
  change HasDerivAt
    (fun y : ℝ => a * y ^ 2 + b * y + c) (2 * a * x + b) x
  have hid : HasDerivAt (fun y : ℝ => y) 1 x := hasDerivAt_id x
  have hsq : HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by
    simpa [pow_two, two_mul] using (hid.mul hid)
  have hquad :
      HasDerivAt (fun y : ℝ => a * y ^ 2) (a * (2 * x)) x :=
    hsq.const_mul a
  have hlin : HasDerivAt (fun y : ℝ => b * y) b x := by
    simpa using (hid.const_mul b)
  have hfull :
      HasDerivAt (fun y : ℝ => a * y ^ 2 + b * y + c)
        (a * (2 * x) + b) x :=
    (hquad.add hlin).add_const c
  convert hfull using 1 <;> ring

theorem gap2 (a b c : ℝ) (htan : tangentToXAxis a b c) :
    ∃ x, 2 * a * x + b = 0 ∧ quadratic a b c x = 0 := by
  unfold tangentToXAxis at htan
  rcases htan with ⟨x, hderiv, hzero⟩
  refine ⟨x, ?_, hzero⟩
  calc
    2 * a * x + b = deriv (quadratic a b c) x := (gap1 a b c x).deriv.symm
    _ = 0 := hderiv

theorem gap3 (a b c x : ℝ) (hcrit : 2 * a * x + b = 0) :
    deriv (quadratic a b c) x = 0 := by
  calc
    deriv (quadratic a b c) x = 2 * a * x + b := (gap1 a b c x).deriv
    _ = 0 := hcrit

theorem gap4 (a b c : ℝ)
    (hcommon : ∃ x, 2 * a * x + b = 0 ∧ quadratic a b c x = 0) :
    tangentToXAxis a b c := by
  unfold tangentToXAxis
  rcases hcommon with ⟨x, hcrit, hzero⟩
  exact ⟨x, gap3 a b c x hcrit, hzero⟩

theorem gap5 (a b : ℝ) (ha : a ≠ 0) :
    ∃ x : ℝ, x = -b / (2 * a) := by
  exact ⟨-b / (2 * a), rfl⟩

theorem gap6 (a b c : ℝ) (htan : tangentToXAxis a b c) :
    ∃ x : ℝ, quadratic a b c x = 0 := by
  unfold tangentToXAxis at htan
  rcases htan with ⟨x, _, hzero⟩
  exact ⟨x, hzero⟩

theorem gap7 (a b c : ℝ) (ha : a ≠ 0)
    (hdisc : 0 ≤ b ^ 2 - 4 * a * c) :
    ∃ x : ℝ, quadratic a b c x = 0 ∧
      (x = -b / (2 * a) + Real.sqrt (b ^ 2 - 4 * a * c) / (2 * a) ∨
       x = -b / (2 * a) - Real.sqrt (b ^ 2 - 4 * a * c) / (2 * a)) := by
  let x : ℝ :=
    -b / (2 * a) + Real.sqrt (b ^ 2 - 4 * a * c) / (2 * a)
  have hden : 2 * a ≠ 0 := mul_ne_zero (by norm_num) ha
  have hfour : 4 * a ≠ 0 := mul_ne_zero (by norm_num) ha
  have hlinear :
      2 * a * x + b = Real.sqrt (b ^ 2 - 4 * a * c) := by
    dsimp [x]
    field_simp [hden]
    ring
  have hsqrt :
      Real.sqrt (b ^ 2 - 4 * a * c) ^ 2 = b ^ 2 - 4 * a * c :=
    Real.sq_sqrt hdisc
  have hid := quadratic_discriminant_identity a b c x
  rw [hlinear, hsqrt] at hid
  have hmul : (4 * a) * quadratic a b c x = 0 := by
    nlinarith [hid]
  have hroot : quadratic a b c x = 0 :=
    (mul_eq_zero.mp hmul).resolve_left hfour
  refine ⟨x, hroot, ?_⟩
  exact Or.inl rfl

theorem gap8 (a b c : ℝ) (htan : tangentToXAxis a b c) :
    b ^ 2 - 4 * a * c = 0 := by
  rcases gap2 a b c htan with ⟨x, hcrit, hroot⟩
  have hid := quadratic_discriminant_identity a b c x
  rw [hroot, hcrit] at hid
  simpa using hid

theorem gap9 (a b c : ℝ) (ha : a ≠ 0) :
    (a, b, c) ∈ {p : ℝ × ℝ × ℝ | p.2.1 ^ 2 - 4 * p.1 * p.2.2 = 0} ↔
      ∃ x, 2 * a * x + b = 0 ∧ quadratic a b c x = 0 := by
  constructor
  · intro hdisc
    change b ^ 2 - 4 * a * c = 0 at hdisc
    let x : ℝ := -b / (2 * a)
    have hden : 2 * a ≠ 0 := mul_ne_zero (by norm_num) ha
    have hfour : 4 * a ≠ 0 := mul_ne_zero (by norm_num) ha
    have hcrit : 2 * a * x + b = 0 := by
      dsimp [x]
      field_simp [hden]
      ring
    have hid := quadratic_discriminant_identity a b c x
    rw [hcrit, hdisc] at hid
    have hmul : (4 * a) * quadratic a b c x = 0 := by
      simpa using hid
    have hroot : quadratic a b c x = 0 :=
      (mul_eq_zero.mp hmul).resolve_left hfour
    exact ⟨x, hcrit, hroot⟩
  · intro hcommon
    change b ^ 2 - 4 * a * c = 0
    exact gap8 a b c (gap4 a b c hcommon)

end

end ProofGap.Exercise1071
