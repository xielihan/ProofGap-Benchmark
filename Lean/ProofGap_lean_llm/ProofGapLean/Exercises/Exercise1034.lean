import ProofGapLean.Prelude.Core
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow

namespace ProofGap.Exercise1034

noncomputable section

def f (y : ℝ) : ℝ := y ^ 3 + 3 * y
def inverse (x : ℝ) : ℝ := Function.invFun f x

def IsTwoSidedInverse (g h : ℝ → ℝ) : Prop :=
  Function.LeftInverse g h ∧ Function.RightInverse g h

private theorem f_continuous : Continuous f := by
  unfold f
  exact (continuous_id.pow 3).add (continuous_const.mul continuous_id)

private theorem f_surjective : Function.Surjective f := by
  intro z
  rcases le_total 0 z with hz | hz
  · have hfactor : 0 ≤ z * (z ^ 2 + 2) :=
      mul_nonneg hz (by nlinarith [sq_nonneg z])
    have hfz : z ≤ f z := by
      unfold f
      nlinarith
    have hzmem : z ∈ Set.Icc (f 0) (f z) := by
      constructor
      · simpa [f] using hz
      · exact hfz
    rcases intermediate_value_Icc hz f_continuous.continuousOn hzmem with
      ⟨y, hy, hfy⟩
    exact ⟨y, hfy⟩
  · have hfactor : z * (z ^ 2 + 2) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hz (by nlinarith [sq_nonneg z])
    have hfz : f z ≤ z := by
      unfold f
      nlinarith
    have hzmem : z ∈ Set.Icc (f z) (f 0) := by
      constructor
      · exact hfz
      · simpa [f] using hz
    rcases intermediate_value_Icc hz f_continuous.continuousOn hzmem with
      ⟨y, hy, hfy⟩
    exact ⟨y, hfy⟩

theorem gap1 (y : ℝ) :
    HasDerivAt f (3 * y ^ 2 + 3) y := by
  unfold f
  convert ((hasDerivAt_id y).pow 3).add ((hasDerivAt_id y).const_mul 3)
    using 1 <;> simp <;> ring

theorem gap2 (y : ℝ) :
    3 * y ^ 2 + 3 = 3 * (y ^ 2 + 1) := by
  ring

theorem gap3 (y : ℝ) :
    0 < 3 * (y ^ 2 + 1) := by
  positivity

theorem gap4 (y : ℝ) :
    0 < deriv f y := by
  rw [(gap1 y).deriv, gap2]
  exact gap3 y

theorem gap5 : StrictMono f := by
  exact strictMono_of_deriv_pos gap4

theorem gap6 : IsTwoSidedInverse inverse f := by
  exact
    ⟨Function.leftInverse_invFun gap5.injective,
      Function.rightInverse_invFun f_surjective⟩

theorem gap7 (x : ℝ) :
    HasDerivAt inverse (1 / deriv f (inverse x)) x := by
  let e : ℝ ≃o ℝ := gap5.orderIsoOfSurjective f f_surjective
  have he : inverse = e.symm := by
    funext z
    apply gap5.injective
    rw [gap6.2 z]
    exact
      (StrictMono.orderIsoOfSurjective_self_symm_apply
        f gap5 f_surjective z).symm
  have hinv_cont : Continuous inverse := by
    rw [he]
    exact e.toHomeomorph.continuous_invFun
  have hne : 3 * inverse x ^ 2 + 3 ≠ 0 := by
    nlinarith [sq_nonneg (inverse x)]
  rw [(gap1 (inverse x)).deriv]
  simpa [one_div] using
    (gap1 (inverse x)).of_local_left_inverse hinv_cont.continuousAt hne
      (Filter.Eventually.of_forall gap6.2)

theorem gap8 (x : ℝ) :
    1 / deriv f (inverse x) =
      1 / (3 * (inverse x ^ 2 + 1)) := by
  rw [(gap1 (inverse x)).deriv, gap2]

theorem gap9 (x : ℝ) :
    HasDerivAt inverse (1 / (3 * (inverse x ^ 2 + 1))) x := by
  rw [← gap8 x]
  exact gap7 x

theorem gap10 :
    IsTwoSidedInverse inverse f ∧
      ∀ x : ℝ,
        f (inverse x) = x ∧
          HasDerivAt inverse (1 / (3 * (inverse x ^ 2 + 1))) x := by
  refine ⟨gap6, ?_⟩
  intro x
  exact ⟨gap6.2 x, gap9 x⟩

end

end ProofGap.Exercise1034
