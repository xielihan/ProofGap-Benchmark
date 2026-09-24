import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise1776

noncomputable section

def subst (x : ℝ) : ℝ := Real.sqrt (1 + Real.exp x)
def integrand (x : ℝ) : ℝ := 1 / subst x
def intermediate (x : ℝ) : ℝ :=
  Real.log ((subst x - 1) / (subst x + 1))
def primitive (x : ℝ) : ℝ :=
  x - 2 * Real.log (1 + Real.sqrt (1 + Real.exp x))
def IsAntiderivative (F f : ℝ → ℝ) : Prop := ∀ x, HasDerivAt F (f x) x
def Family (f : ℝ → ℝ) : Set (ℝ → ℝ) := {F | IsAntiderivative F f}
def Translates (P : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C, ∀ x, F x = P x + C}

private theorem eq_const_of_deriv_eq_zero
    (f : ℝ → ℝ) (hzero : ∀ x, HasDerivAt f 0 x) (x : ℝ) :
    f x = f 0 := by
  have hdiff : Differentiable ℝ f :=
    fun y => (hzero y).differentiableAt
  exact is_const_of_deriv_eq_zero hdiff (fun y => (hzero y).deriv) x 0

theorem gap1 (x : ℝ) :
    x = Real.log (subst x ^ 2 - 1) := by
  have h : 0 ≤ 1 + Real.exp x := by positivity
  simp [subst, Real.sq_sqrt h]

theorem gap2 (x : ℝ) :
    1 = 2 * subst x / (subst x ^ 2 - 1) * deriv subst x := by
  have hspos : 0 < subst x := by
    unfold subst
    positivity
  have hinner :
      HasDerivAt (fun y : ℝ => 1 + Real.exp y) (Real.exp x) x := by
    simpa only [zero_add] using (Real.hasDerivAt_exp x).const_add 1
  have hs :
      HasDerivAt subst (Real.exp x / (2 * subst x)) x := by
    simpa [subst, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      (Real.hasDerivAt_sqrt
        (by positivity : (1 + Real.exp x) ≠ 0)).comp x hinner
  have hs_sq : subst x ^ 2 = 1 + Real.exp x := by
    unfold subst
    exact Real.sq_sqrt (by positivity)
  have hden : subst x ^ 2 - 1 = Real.exp x := by
    rw [hs_sq]
    ring
  rw [hs.deriv, hden]
  field_simp [ne_of_gt hspos, ne_of_gt (Real.exp_pos x)]

theorem gap3 (x : ℝ) :
    integrand x = 2 / (subst x ^ 2 - 1) * deriv subst x := by
  have hspos : 0 < subst x := by
    unfold subst
    positivity
  have hs_sq : subst x ^ 2 = 1 + Real.exp x := by
    unfold subst
    exact Real.sq_sqrt (by positivity)
  have hden : subst x ^ 2 - 1 ≠ 0 := by
    rw [hs_sq]
    have : 0 < Real.exp x := Real.exp_pos x
    nlinarith
  unfold integrand
  calc
    1 / subst x =
        (2 * subst x / (subst x ^ 2 - 1) * deriv subst x) / subst x := by
          rw [← gap2 x]
    _ = 2 / (subst x ^ 2 - 1) * deriv subst x := by
      field_simp [ne_of_gt hspos, hden]

theorem gap4 (x : ℝ) :
    HasDerivAt intermediate (integrand x) x := by
  have hinner :
      HasDerivAt (fun y : ℝ => 1 + Real.exp y) (Real.exp x) x := by
    simpa only [zero_add] using (Real.hasDerivAt_exp x).const_add 1
  have hs :
      HasDerivAt subst (Real.exp x / (2 * subst x)) x := by
    simpa [subst, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      (Real.hasDerivAt_sqrt
        (by positivity : (1 + Real.exp x) ≠ 0)).comp x hinner
  have hs' : HasDerivAt subst (deriv subst x) x := by
    simpa only [hs.deriv] using hs
  have hsnonneg : 0 ≤ subst x := by
    unfold subst
    exact Real.sqrt_nonneg _
  have hs_sq : subst x ^ 2 = 1 + Real.exp x := by
    unfold subst
    exact Real.sq_sqrt (by positivity)
  have hsone : 1 < subst x := by
    nlinarith [Real.exp_pos x]
  have hm : subst x - 1 ≠ 0 := by nlinarith
  have hp : subst x + 1 ≠ 0 := by nlinarith
  have hd : subst x ^ 2 - 1 ≠ 0 := by
    rw [hs_sq]
    have : 0 < Real.exp x := Real.exp_pos x
    nlinarith
  have hq : (subst x - 1) / (subst x + 1) ≠ 0 :=
    div_ne_zero hm hp
  have hratio :=
    (hs'.sub_const 1).div (hs'.add_const 1) hp
  have hlog := (Real.hasDerivAt_log hq).comp x hratio
  unfold intermediate
  convert hlog using 1
  rw [gap3 x]
  field_simp [hm, hp, hd] <;> ring

theorem gap5 (x : ℝ) :
    HasDerivAt
      (fun y => Real.log ((Real.sqrt (1 + Real.exp y) - 1) /
        (Real.sqrt (1 + Real.exp y) + 1))) (integrand x) x := by
  simpa [intermediate, subst] using gap4 x

theorem gap6 (x : ℝ) :
    intermediate x =
      Real.log ((Real.sqrt (1 + Real.exp x) - 1) /
        (Real.sqrt (1 + Real.exp x) + 1)) := by
  rfl

theorem gap7 (x : ℝ) :
    intermediate x = primitive x := by
  let s : ℝ := subst x
  have hsnonneg : 0 ≤ s := by
    dsimp [s, subst]
    exact Real.sqrt_nonneg _
  have hs_sq : s ^ 2 = 1 + Real.exp x := by
    dsimp [s, subst]
    exact Real.sq_sqrt (by positivity)
  have hsone : 1 < s := by
    nlinarith [Real.exp_pos x]
  have hm : s - 1 ≠ 0 := by nlinarith
  have hp : s + 1 ≠ 0 := by nlinarith
  have hx : x = Real.log (s ^ 2 - 1) := by
    simpa [s] using gap1 x
  have hfactor : s ^ 2 - 1 = (s - 1) * (s + 1) := by ring
  have hadd : 1 + s = s + 1 := by ring
  unfold intermediate primitive
  change Real.log ((s - 1) / (s + 1)) =
    x - 2 * Real.log (1 + s)
  rw [Real.log_div hm hp, hx, hfactor, Real.log_mul hm hp, hadd]
  ring

theorem gap8 :
    Family integrand = Translates primitive := by
  have heq : intermediate = primitive := by
    funext x
    exact gap7 x
  have hprim : ∀ x, HasDerivAt primitive (integrand x) x := by
    intro x
    rw [← heq]
    exact gap4 x
  ext F
  constructor
  · intro hF
    change IsAntiderivative F integrand at hF
    change ∃ C, ∀ x, F x = primitive x + C
    have hzero :
        ∀ x, HasDerivAt (fun y => F y - primitive y) 0 x := by
      intro x
      simpa using (hF x).sub (hprim x)
    refine ⟨F 0 - primitive 0, ?_⟩
    intro x
    have hc :
        (fun y => F y - primitive y) x =
          (fun y => F y - primitive y) 0 :=
      eq_const_of_deriv_eq_zero
        (fun y => F y - primitive y) hzero x
    dsimp only at hc
    linarith
  · intro hF
    rcases hF with ⟨C, hC⟩
    change IsAntiderivative F integrand
    have hfun : F = fun y => primitive y + C := by
      funext y
      exact hC y
    intro x
    rw [hfun]
    simpa using (hprim x).add_const C

end

end ProofGap.Exercise1776
