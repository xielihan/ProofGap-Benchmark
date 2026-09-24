import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

namespace ProofGap.Exercise1446

noncomputable section

def f (x : ℝ) : ℝ := x ^ 2 - 4 * x + 6
def domain : Set ℝ := Set.Icc (-3) 10

theorem gap1 (x : ℝ) : deriv f x = 2 * x - 4 := by
  have hsquare : HasDerivAt (fun y : ℝ => y * y) (x + x) x := by
    simpa using (hasDerivAt_id x).mul (hasDerivAt_id x)
  have hlinear : HasDerivAt (fun y : ℝ => 4 * y) 4 x := by
    simpa using (hasDerivAt_id x).const_mul 4
  have hraw := (hsquare.sub hlinear).add (hasDerivAt_const x 6)
  have hfun :
      ((fun y : ℝ => y * y) - (fun y : ℝ => 4 * y) + (fun _ : ℝ => 6)) = f := by
    funext y
    simp [f, pow_two]
  rw [← hfun]
  simpa [two_mul] using hraw.deriv

theorem gap2 (x : ℝ) : deriv (deriv f) x = 2 := by
  have hf : deriv f = fun y : ℝ => 2 * y - 4 := by
    funext y
    exact gap1 y
  have hlinear : HasDerivAt (fun y : ℝ => 2 * y) 2 x := by
    convert (hasDerivAt_id x).const_mul 2 using 1 <;> norm_num
  have haffine : HasDerivAt (fun y : ℝ => 2 * y - 4) 2 x := by
    exact hlinear.sub_const 4
  have hderiv : HasDerivAt (deriv f) 2 x := by
    rw [hf]
    exact haffine
  exact hderiv.deriv

theorem gap3 : deriv f 2 = 0 := by
  rw [gap1]
  norm_num

theorem gap4 : deriv (deriv f) 2 = 2 := by
  exact gap2 2

theorem gap5 : (2 : ℝ) > 0 := by
  norm_num

theorem gap6 : 0 < deriv (deriv f) 2 := by
  rw [gap4]
  norm_num

theorem gap7 : IsMinOn f Set.univ 2 := by
  intro x hx
  dsimp [f]
  nlinarith [sq_nonneg (x - 2)]

theorem gap8 : f 2 = 2 := by
  norm_num [f]

theorem gap9 : sInf (f '' domain) = 2 := by
  have hmem : (2 : ℝ) ∈ f '' domain := by
    refine ⟨2, ?_, ?_⟩
    · norm_num [domain]
    · exact gap8
  have hlower : ∀ y ∈ f '' domain, (2 : ℝ) ≤ y := by
    rintro y ⟨x, hx, rfl⟩
    calc
      (2 : ℝ) = f 2 := gap8.symm
      _ ≤ f x := gap7 (by simp)
  have hbdd : BddBelow (f '' domain) := by
    refine ⟨2, ?_⟩
    intro y hy
    exact hlower y hy
  apply le_antisymm
  · exact csInf_le hbdd hmem
  · exact le_csInf ⟨2, hmem⟩ hlower

theorem gap10 (x : ℝ) : 0 < deriv (deriv f) x := by
  rw [gap2]
  norm_num

theorem gap11 : sSup (f '' domain) = max (f (-3)) (f 10) := by
  have hmax : max (f (-3)) (f 10) = (66 : ℝ) := by
    norm_num [f, max_eq_right]
  have hupper : ∀ y ∈ f '' domain, y ≤ (66 : ℝ) := by
    rintro y ⟨x, hx, rfl⟩
    have hx' : (-3 : ℝ) ≤ x ∧ x ≤ 10 := by
      simpa [domain] using hx
    have hprod : (x - 10) * (x + 6) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith [hx'.2]) (by linarith [hx'.1])
    dsimp [f]
    nlinarith [hprod]
  have hbdd : BddAbove (f '' domain) := by
    refine ⟨66, ?_⟩
    intro y hy
    exact hupper y hy
  have hne : (f '' domain).Nonempty := by
    refine ⟨f 10, ?_⟩
    exact ⟨10, by norm_num [domain], rfl⟩
  rw [hmax]
  apply le_antisymm
  · exact csSup_le hne hupper
  · apply le_csSup hbdd
    refine ⟨10, ?_, ?_⟩
    · norm_num [domain]
    · norm_num [f]

theorem gap12 : max (f (-3)) (f 10) = 66 := by
  norm_num [f, max_eq_right]

theorem gap13 : sSup (f '' domain) = 66 := by
  calc
    sSup (f '' domain) = max (f (-3)) (f 10) := gap11
    _ = 66 := gap12

end
end ProofGap.Exercise1446
