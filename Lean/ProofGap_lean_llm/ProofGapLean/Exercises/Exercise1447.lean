import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Topology.Neighborhoods
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Topology.Order.OrderClosed

namespace ProofGap.Exercise1447

noncomputable section

def p (x : ℝ) : ℝ := x ^ 2 - 3 * x + 2
def f (x : ℝ) : ℝ := |p x|
def domain : Set ℝ := Set.Icc (-10) 10

private theorem Real.hasDerivAt_abs {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (fun y : ℝ => |y|) (Real.sign x) x := by
  rcases lt_or_gt_of_ne hx with hneg | hpos
  · simpa [Real.sign_of_neg hneg, hneg] using (_root_.hasDerivAt_abs hx)
  · simpa [Real.sign_of_pos hpos, hpos] using (_root_.hasDerivAt_abs hx)

theorem gap1 (x : ℝ) : 0 ≤ f x := by
  exact abs_nonneg (p x)

theorem gap2 (x : ℝ) (hx : x = 1 ∨ x = 2) : p x = 0 := by
  rcases hx with rfl | rfl <;> norm_num [p]

theorem gap3 : sInf (f '' domain) = 0 := by
  have hzero : (0 : ℝ) ∈ f '' domain := by
    refine ⟨1, ?_, ?_⟩
    · norm_num [domain]
    · norm_num [f, p]
  have hnonneg : ∀ y ∈ f '' domain, (0 : ℝ) ≤ y := by
    rintro y ⟨x, -, rfl⟩
    exact gap1 x
  apply le_antisymm
  · exact csInf_le ⟨0, hnonneg⟩ hzero
  · exact le_csInf ⟨0, hzero⟩ hnonneg

theorem gap4 : f 1 = 0 := by
  norm_num [f, p]

theorem gap5 : f 2 = 0 := by
  norm_num [f, p]

theorem gap6 (x : ℝ) (hx : p x ≠ 0) :
    deriv f x = (2 * x - 3) * Real.sign (p x) := by
  have hp : HasDerivAt p (2 * x - 3) x := by
    simpa [p] using
      ((((hasDerivAt_id x).pow 2).sub
        ((hasDerivAt_const x (3 : ℝ)).mul (hasDerivAt_id x))).add
        (hasDerivAt_const x (2 : ℝ)))
  have ha : HasDerivAt (fun y : ℝ => |y|) (Real.sign (p x)) (p x) :=
    Real.hasDerivAt_abs (x := p x) hx
  simpa [f, Function.comp_def, mul_comm] using (ha.comp x hp).deriv

theorem gap7 (x : ℝ) (h₁ : 1 < x) (h₂ : x < 3 / 2) :
    0 < deriv f x := by
  have hx2 : x < 2 := by
    nlinarith
  have hprod : (x - 1) * (x - 2) < 0 :=
    mul_neg_of_pos_of_neg (sub_pos.mpr h₁) (sub_neg.mpr hx2)
  have hp : p x < 0 := by
    unfold p
    nlinarith [hprod]
  rw [gap6 x (ne_of_lt hp), Real.sign_of_neg hp]
  nlinarith

theorem gap8 (x : ℝ) (h₁ : 3 / 2 < x) (h₂ : x < 2) :
    deriv f x < 0 := by
  have hx1 : 1 < x := by
    nlinarith
  have hprod : (x - 1) * (x - 2) < 0 :=
    mul_neg_of_pos_of_neg (sub_pos.mpr hx1) (sub_neg.mpr h₂)
  have hp : p x < 0 := by
    unfold p
    nlinarith [hprod]
  rw [gap6 x (ne_of_lt hp), Real.sign_of_neg hp]
  nlinarith

theorem gap9 : IsLocalMax f (3 / 2) := by
  change {x : ℝ | f x ≤ f (3 / 2)} ∈ nhds (3 / 2)
  have hmem : Set.Ioo (1 : ℝ) 2 ∈ nhds (3 / 2) :=
    Ioo_mem_nhds (by norm_num) (by norm_num)
  refine Filter.mem_of_superset hmem ?_
  intro x hx
  change f x ≤ f (3 / 2)
  have hprod : (x - 1) * (x - 2) < 0 :=
    mul_neg_of_pos_of_neg (sub_pos.mpr hx.1) (sub_neg.mpr hx.2)
  have hp : p x < 0 := by
    unfold p
    nlinarith [hprod]
  have hfx : f x = -(p x) := by
    rw [f, abs_of_neg hp]
  have hmid : f (3 / 2) = (1 / 4 : ℝ) := by
    norm_num [f, p]
  rw [hfx, hmid]
  unfold p
  nlinarith [sq_nonneg (x - (3 / 2 : ℝ))]

theorem gap10 : f (3 / 2) = 1 / 4 := by
  norm_num [f, p]

theorem gap11 :
    sSup (f '' domain) = max (f (3 / 2)) (max (f (-10)) (f 10)) := by
  have hbound : ∀ x ∈ domain, f x ≤ (132 : ℝ) := by
    intro x hx
    change (-10 : ℝ) ≤ x ∧ x ≤ 10 at hx
    rcases hx with ⟨hxlo, hxhi⟩
    have hfac : 0 ≤ (13 - x) * (x + 10) :=
      mul_nonneg (by linarith) (by linarith)
    have hsq : 0 ≤ (x - (3 / 2 : ℝ)) ^ 2 := sq_nonneg _
    have hpupper : p x ≤ (132 : ℝ) := by
      unfold p
      nlinarith [hfac]
    have hplower : -(132 : ℝ) ≤ p x := by
      unfold p
      nlinarith [hsq]
    unfold f
    exact abs_le.2 ⟨hplower, hpupper⟩
  have hne : (f '' domain).Nonempty := by
    refine ⟨f (-10), -10, ?_, rfl⟩
    norm_num [domain]
  have hbdd : BddAbove (f '' domain) := by
    refine ⟨132, ?_⟩
    rintro y ⟨x, hx, rfl⟩
    exact hbound x hx
  have hmem : (132 : ℝ) ∈ f '' domain := by
    refine ⟨-10, ?_, ?_⟩
    · norm_num [domain]
    · norm_num [f, p]
  have hsup : sSup (f '' domain) = (132 : ℝ) := by
    apply le_antisymm
    · refine csSup_le hne ?_
      rintro y ⟨x, hx, rfl⟩
      exact hbound x hx
    · exact le_csSup hbdd hmem
  calc
    sSup (f '' domain) = 132 := hsup
    _ = max (f (3 / 2)) (max (f (-10)) (f 10)) := by
      norm_num [f, p]

theorem gap12 :
    max (f (3 / 2)) (max (f (-10)) (f 10)) = 132 := by
  norm_num [f, p]

theorem gap13 : sSup (f '' domain) = 132 := by
  rw [gap11, gap12]

end
end ProofGap.Exercise1447
