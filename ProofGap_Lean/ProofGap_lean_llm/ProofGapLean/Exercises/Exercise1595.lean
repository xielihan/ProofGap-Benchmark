import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

namespace ProofGap.Exercise1595

noncomputable section

def curve (x : ℝ) := 1 / x
def powThreeHalves (u : ℝ) := u * Real.sqrt u
def curvatureRadius (x : ℝ) :=
  powThreeHalves (1 + (deriv curve x) ^ 2) / |deriv (deriv curve) x|
def centerX (x : ℝ) :=
  x - deriv curve x * (1 + (deriv curve x) ^ 2) / deriv (deriv curve) x
def centerY (x : ℝ) :=
  curve x + (1 + (deriv curve x) ^ 2) / deriv (deriv curve) x
def curvatureCenter (x : ℝ) := (centerX x, centerY x)
def Approx (actual expected tolerance : ℝ) : Prop :=
  |actual - expected| < tolerance
def ApproxPoint (actual expected : ℝ × ℝ) (tolerance : ℝ) : Prop :=
  Approx actual.1 expected.1 tolerance ∧ Approx actual.2 expected.2 tolerance

private theorem deriv_zero_of_large_near_zero
    (f : ℝ → ℝ)
    (hlarge : ∀ δ > 0, ∃ y, dist y 0 < δ ∧ 1 ≤ dist (f y) (f 0)) :
    deriv f 0 = 0 := by
  apply deriv_zero_of_not_differentiableAt
  intro hd
  obtain ⟨δ, hδ, hclose⟩ :=
    (Metric.continuousAt_iff.mp hd.continuousAt) 1 zero_lt_one
  obtain ⟨y, hyδ, hylarge⟩ := hlarge δ hδ
  have hysmall : dist (f y) (f 0) < 1 := hclose hyδ
  linarith

theorem gap1 (x : ℝ) (hx : x ≠ 0) : curve x = 1 / x := by
  rfl
theorem gap2 (x : ℝ) : deriv curve x = -1 / x ^ 2 := by
  by_cases hx : x = 0
  · subst x
    have hzero : deriv curve 0 = 0 := by
      apply deriv_zero_of_large_near_zero
      intro δ hδ
      let y : ℝ := min (δ / 2) (1 / 2)
      have hypos : 0 < y := by
        dsimp [y]
        exact lt_min (by linarith) (by norm_num)
      have hyδ : y < δ := by
        have hyle : y ≤ δ / 2 := by
          dsimp [y]
          exact min_le_left _ _
        linarith
      have hyone : y ≤ 1 := by
        have hyle : y ≤ 1 / 2 := by
          dsimp [y]
          exact min_le_right _ _
        linarith
      refine ⟨y, ?_, ?_⟩
      · simpa [Real.dist_eq, abs_of_pos hypos] using hyδ
      · have hinv : 1 ≤ 1 / y :=
          (le_div_iff₀ hypos).2 (by simpa using hyone)
        rw [Real.dist_eq]
        have hpos : 0 < curve y - curve 0 := by
          simpa [curve] using (one_div_pos.mpr hypos)
        rw [abs_of_pos hpos]
        simpa [curve] using hinv
    simpa using hzero
  · have hnum : HasDerivAt (fun _ : ℝ => (1 : ℝ)) 0 x :=
      hasDerivAt_const (x := x) (1 : ℝ)
    have hquot := hnum.div (hasDerivAt_id x) hx
    simpa [curve] using hquot.deriv
theorem gap3 (x : ℝ) : deriv (deriv curve) x = 2 / x ^ 3 := by
  rw [show deriv curve = fun y : ℝ => -1 / y ^ 2 by
    funext y
    exact gap2 y]
  by_cases hx : x = 0
  · subst x
    have hzero : deriv (fun y : ℝ => -1 / y ^ 2) 0 = 0 := by
      apply deriv_zero_of_large_near_zero
      intro δ hδ
      let y : ℝ := min (δ / 2) (1 / 2)
      have hypos : 0 < y := by
        dsimp [y]
        exact lt_min (by linarith) (by norm_num)
      have hyδ : y < δ := by
        have hyle : y ≤ δ / 2 := by
          dsimp [y]
          exact min_le_left _ _
        linarith
      have hyhalf : y ≤ 1 / 2 := by
        dsimp [y]
        exact min_le_right _ _
      have hy_sq_pos : 0 < y ^ 2 := sq_pos_of_pos hypos
      have hy_sq_le : y ^ 2 ≤ 1 := by
        nlinarith
      refine ⟨y, ?_, ?_⟩
      · simpa [Real.dist_eq, abs_of_pos hypos] using hyδ
      · have hinv : 1 ≤ 1 / y ^ 2 :=
          (le_div_iff₀ hy_sq_pos).2 (by simpa using hy_sq_le)
        have hneg : -1 / y ^ 2 < 0 :=
          div_neg_of_neg_of_pos (by norm_num) hy_sq_pos
        rw [Real.dist_eq]
        have hdiffneg :
            (-1 / y ^ 2) - (-1 / (0 : ℝ) ^ 2) < 0 := by
          simpa using hneg
        rw [abs_of_neg hdiffneg]
        have hquot : -(-1 / y ^ 2) = 1 / y ^ 2 := by
          ring
        have hbound : 1 ≤ -(-1 / y ^ 2) := by
          rw [hquot]
          exact hinv
        simpa using hbound
    simpa using hzero
  · have hnum : HasDerivAt (fun _ : ℝ => (-1 : ℝ)) 0 x :=
      hasDerivAt_const (x := x) (-1 : ℝ)
    have hden : HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by
      simpa [pow_two, two_mul] using
        (hasDerivAt_id x).mul (hasDerivAt_id x)
    have hquot := hnum.div hden (pow_ne_zero 2 hx)
    convert hquot.deriv using 1 <;> field_simp [hx] <;> ring
theorem gap4 (x : ℝ) :
    (x, curve x) = ((1 : ℝ), 1) → curve x = 1 := by
  intro h
  simpa using congrArg Prod.snd h
theorem gap5 (x : ℝ) :
    (x, curve x) = ((1 : ℝ), 1) → deriv curve x = -1 := by
  intro h
  have hx : x = 1 := by
    simpa using congrArg Prod.fst h
  subst x
  norm_num [gap2]
theorem gap6 (x : ℝ) :
    (x, curve x) = ((1 : ℝ), 1) → deriv (deriv curve) x = 2 := by
  intro h
  have hx : x = 1 := by
    simpa using congrArg Prod.fst h
  subst x
  norm_num [gap3]
theorem gap7 (x : ℝ) :
    (x, curve x) = ((1 : ℝ), 1) →
      curvatureRadius x = powThreeHalves (1 + (-1 : ℝ) ^ 2) / 2 := by
  intro h
  have hx : x = 1 := by
    simpa using congrArg Prod.fst h
  subst x
  norm_num [curvatureRadius, gap2, gap3]
theorem gap8 (x : ℝ) :
    (x, curve x) = ((1 : ℝ), 1) →
      powThreeHalves (1 + (-1 : ℝ) ^ 2) / 2 = Real.sqrt 2 := by
  intro _
  norm_num [powThreeHalves]
theorem gap9 (x : ℝ) :
    (x, curve x) = ((1 : ℝ), 1) → curvatureRadius x = Real.sqrt 2 := by
  intro h
  exact (gap7 x h).trans (gap8 x h)
theorem gap10 (x : ℝ) :
    (x, curve x) = ((1 : ℝ), 1) →
      centerX x =
        x - deriv curve x * (1 + (deriv curve x) ^ 2) / deriv (deriv curve) x := by
  intro _
  rfl
theorem gap11 (x : ℝ) :
    (x, curve x) = ((1 : ℝ), 1) →
      x - deriv curve x * (1 + (deriv curve x) ^ 2) / deriv (deriv curve) x =
        1 - (-1 : ℝ) * (1 + 1) / 2 := by
  intro h
  have hx : x = 1 := by
    simpa using congrArg Prod.fst h
  subst x
  norm_num [gap2, gap3]
theorem gap12 (x : ℝ) :
    (x, curve x) = ((1 : ℝ), 1) →
      1 - (-1 : ℝ) * (1 + 1) / 2 = 2 := by
  intro _
  norm_num
theorem gap13 (x : ℝ) :
    (x, curve x) = ((1 : ℝ), 1) → centerX x = 2 := by
  intro h
  calc
    centerX x =
        x - deriv curve x * (1 + (deriv curve x) ^ 2) /
          deriv (deriv curve) x := gap10 x h
    _ = 1 - (-1 : ℝ) * (1 + 1) / 2 := gap11 x h
    _ = 2 := gap12 x h
theorem gap14 (x : ℝ) :
    (x, curve x) = ((1 : ℝ), 1) →
      centerY x =
        curve x + (1 + (deriv curve x) ^ 2) / deriv (deriv curve) x := by
  intro _
  rfl
theorem gap15 (x : ℝ) :
    (x, curve x) = ((1 : ℝ), 1) →
      curve x + (1 + (deriv curve x) ^ 2) / deriv (deriv curve) x =
        1 + (2 : ℝ) / 2 := by
  intro h
  have hx : x = 1 := by
    simpa using congrArg Prod.fst h
  subst x
  norm_num [curve, gap2, gap3]
theorem gap16 (x : ℝ) :
    (x, curve x) = ((1 : ℝ), 1) → 1 + (2 : ℝ) / 2 = 2 := by
  intro _
  norm_num
theorem gap17 (x : ℝ) :
    (x, curve x) = ((1 : ℝ), 1) → centerY x = 2 := by
  intro h
  calc
    centerY x =
        curve x + (1 + (deriv curve x) ^ 2) /
          deriv (deriv curve) x := gap14 x h
    _ = 1 + (2 : ℝ) / 2 := gap15 x h
    _ = 2 := gap16 x h
theorem gap18 (x : ℝ) :
    (x, curve x) = ((100 : ℝ), 0.01) → curve x = 0.01 := by
  intro h
  simpa using congrArg Prod.snd h
theorem gap19 (x : ℝ) :
    (x, curve x) = ((100 : ℝ), 0.01) → deriv curve x = -0.0001 := by
  intro h
  have hx : x = 100 := by
    simpa using congrArg Prod.fst h
  subst x
  norm_num [gap2]
theorem gap20 (x : ℝ) :
    (x, curve x) = ((100 : ℝ), 0.01) →
      deriv (deriv curve) x = 0.000002 := by
  intro h
  have hx : x = 100 := by
    simpa using congrArg Prod.fst h
  subst x
  norm_num [gap3]
theorem gap21 : Approx (curvatureRadius 100) 500000 (1 / 100) := by
  let q : ℝ := (100000001 : ℝ) / 100000000
  have hq : 0 ≤ q := by
    dsimp [q]
    norm_num
  have hs0 : 0 ≤ Real.sqrt q := Real.sqrt_nonneg q
  have hs2 : (Real.sqrt q) ^ 2 = q := Real.sq_sqrt hq
  have hslo : 1 ≤ Real.sqrt q := by
    dsimp [q] at hs2 ⊢
    nlinarith
  have hshi : Real.sqrt q < (200000001 : ℝ) / 200000000 := by
    dsimp [q] at hs2 ⊢
    nlinarith
  have hradius :
      curvatureRadius 100 = 500000 * (q * Real.sqrt q) := by
    dsimp [q]
    norm_num [curvatureRadius, powThreeHalves, gap2, gap3] <;> ring
  rw [hradius]
  unfold Approx
  have hdiff : 0 ≤ 500000 * (q * Real.sqrt q) - 500000 := by
    dsimp [q]
    nlinarith
  rw [abs_of_nonneg hdiff]
  dsimp [q] at hshi ⊢
  nlinarith
theorem gap22 :
    ApproxPoint (curvatureCenter 100) ((150 : ℝ), 500000) (1 / 50) := by
  norm_num [ApproxPoint, Approx, curvatureCenter, centerX, centerY,
    curve, gap2, gap3]

end
end ProofGap.Exercise1595
