import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise2170

open Filter

noncomputable section

def nonnegative : Set ℝ := Set.Ioi 0
def negative : Set ℝ := Set.Iio 0
def AntiderivativesOn (s : Set ℝ) (f : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∀ x ∈ s, HasDerivAt F (f x) x}
def PrimitiveFamilyOn (s : Set ℝ) (p : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x ∈ s, F x = p x + C}
def Antiderivatives (f : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∀ x, HasDerivAt F (f x) x}
def PrimitiveFamily (p : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x, F x = p x + C}
def integrand (x : ℝ) := Real.exp (-|x|)
def normalizedPrimitive (x : ℝ) :=
  if 0 ≤ x then 1 - Real.exp (-x) else Real.exp x - 1

private theorem antiderivativesOn_eq_primitiveFamilyOn_of_open
    (s : Set ℝ) (hs : IsOpen s) (hconn : IsPreconnected s)
    (hne : s.Nonempty) (f p : ℝ → ℝ)
    (hp : ∀ x, HasDerivAt p (f x) x) :
    AntiderivativesOn s f = PrimitiveFamilyOn s p := by
  apply Set.ext
  intro F
  simp only [AntiderivativesOn, PrimitiveFamilyOn, Set.mem_setOf_eq]
  constructor
  · intro hF
    rcases hne with ⟨a, ha⟩
    let g := fun x => F x - p x
    have hg : ∀ x ∈ s, HasDerivAt g 0 x := by
      intro x hx
      dsimp [g]
      convert (hF x hx).sub (hp x) using 1 <;> ring
    have hgd : DifferentiableOn ℝ g s :=
      fun x hx => (hg x hx).differentiableAt.differentiableWithinAt
    have hg0 : ∀ x ∈ s, deriv g x = 0 :=
      fun x hx => (hg x hx).deriv
    refine ⟨F a - p a, ?_⟩
    intro x hx
    have heq : g x = g a :=
      hs.is_const_of_deriv_eq_zero hconn hgd hg0 hx ha
    dsimp [g] at heq
    linarith
  · rintro ⟨C, hC⟩ x hx
    have hw : HasDerivWithinAt F (f x) s x := by
      apply ((hp x).add_const C).hasDerivWithinAt.congr
      · intro y hy
        exact hC y hy
      · exact hC x hx
    exact hw.hasDerivAt (hs.mem_nhds hx)

private theorem normalizedPrimitive_hasDerivAt (x : ℝ) :
    HasDerivAt normalizedPrimitive (integrand x) x := by
  rcases lt_trichotomy x 0 with hx | hx | hx
  · have hb : HasDerivAt (fun y : ℝ => Real.exp y - 1) (Real.exp x) x :=
      (Real.hasDerivAt_exp x).sub_const 1
    have hw : HasDerivWithinAt normalizedPrimitive (Real.exp x) (Set.Iio 0) x := by
      apply hb.hasDerivWithinAt.congr
      · intro y hy
        change y < 0 at hy
        simp only [normalizedPrimitive, if_neg (not_le_of_gt hy)]
      · simp only [normalizedPrimitive, if_neg (not_le_of_gt hx)]
    have ha := hw.hasDerivAt (Iio_mem_nhds hx)
    simpa [integrand, abs_of_neg hx] using ha
  · subst x
    have hp : HasDerivAt (fun y : ℝ => 1 - Real.exp (-y)) 1 0 := by
      convert ((Real.hasDerivAt_exp (-(0 : ℝ))).comp 0 (hasDerivAt_neg 0)).const_sub 1 using 1 <;>
        norm_num
    have hn : HasDerivAt (fun y : ℝ => Real.exp y - 1) 1 0 := by
      simpa using (Real.hasDerivAt_exp 0).sub_const 1
    have hpw : HasDerivWithinAt normalizedPrimitive 1 (Set.Ici 0) 0 := by
      apply hp.hasDerivWithinAt.congr
      · intro y hy
        change 0 ≤ y at hy
        simp only [normalizedPrimitive, if_pos hy]
      · simp [normalizedPrimitive]
    have hnw : HasDerivWithinAt normalizedPrimitive 1 (Set.Iic 0) 0 := by
      apply hn.hasDerivWithinAt.congr
      · intro y hy
        change y ≤ 0 at hy
        rcases lt_or_eq_of_le hy with hlt | heq
        · simp only [normalizedPrimitive, if_neg (not_le_of_gt hlt)]
        · subst y
          simp [normalizedPrimitive]
      · simp [normalizedPrimitive]
    have hboth := hnw.union hpw
    have hu : Set.Iic (0 : ℝ) ∪ Set.Ici 0 = Set.univ := by
      ext y
      simp only [Set.mem_union, Set.mem_Iic, Set.mem_Ici, Set.mem_univ, iff_true]
      exact le_total y 0
    rw [hu] at hboth
    have hz : HasDerivAt normalizedPrimitive 1 0 := by
      simpa only [hasDerivWithinAt_univ] using hboth
    simpa [integrand] using hz
  · have hb :
        HasDerivAt (fun y : ℝ => 1 - Real.exp (-y)) (Real.exp (-x)) x := by
      convert ((Real.hasDerivAt_exp (-x)).comp x (hasDerivAt_neg x)).const_sub 1 using 1 <;>
        ring
    have hw :
        HasDerivWithinAt normalizedPrimitive (Real.exp (-x)) (Set.Ioi 0) x := by
      apply hb.hasDerivWithinAt.congr
      · intro y hy
        change 0 < y at hy
        simp only [normalizedPrimitive, if_pos (le_of_lt hy)]
      · simp only [normalizedPrimitive, if_pos (le_of_lt hx)]
    have ha := hw.hasDerivAt (Ioi_mem_nhds hx)
    simpa [integrand, abs_of_pos hx] using ha

theorem gap1 :
    AntiderivativesOn nonnegative integrand =
      AntiderivativesOn nonnegative (fun x => Real.exp (-x)) := by
  apply Set.ext
  intro F
  simp only [AntiderivativesOn, Set.mem_setOf_eq]
  constructor
  · intro h x hx
    change 0 < x at hx
    simpa [integrand, abs_of_pos hx] using h x hx
  · intro h x hx
    change 0 < x at hx
    simpa [integrand, abs_of_pos hx] using h x hx
theorem gap2 :
    AntiderivativesOn nonnegative (fun x => Real.exp (-x)) =
      PrimitiveFamilyOn nonnegative (fun x => -Real.exp (-x)) := by
  simpa [nonnegative] using
    (antiderivativesOn_eq_primitiveFamilyOn_of_open
      (Set.Ioi (0 : ℝ)) isOpen_Ioi isPreconnected_Ioi
      (show (Set.Ioi (0 : ℝ)).Nonempty by exact ⟨1, by norm_num⟩)
      (fun x : ℝ => Real.exp (-x)) (fun x : ℝ => -Real.exp (-x))
      (by
        intro x
        convert (((Real.hasDerivAt_exp (-x)).comp x (hasDerivAt_neg x)).neg) using 1 <;>
          ring))
theorem gap3 :
    AntiderivativesOn nonnegative integrand =
      PrimitiveFamilyOn nonnegative (fun x => -Real.exp (-x)) := by
  exact gap1.trans gap2
theorem gap4 :
    AntiderivativesOn negative integrand =
      AntiderivativesOn negative Real.exp := by
  apply Set.ext
  intro F
  simp only [AntiderivativesOn, Set.mem_setOf_eq]
  constructor
  · intro h x hx
    change x < 0 at hx
    simpa [integrand, abs_of_neg hx] using h x hx
  · intro h x hx
    change x < 0 at hx
    simpa [integrand, abs_of_neg hx] using h x hx
theorem gap5 :
    AntiderivativesOn negative Real.exp =
      PrimitiveFamilyOn negative Real.exp := by
  simpa [negative] using
    (antiderivativesOn_eq_primitiveFamilyOn_of_open
      (Set.Iio (0 : ℝ)) isOpen_Iio isPreconnected_Iio
      (show (Set.Iio (0 : ℝ)).Nonempty by exact ⟨-1, by norm_num⟩)
      Real.exp Real.exp (fun x => Real.hasDerivAt_exp x))
theorem gap6 :
    AntiderivativesOn negative integrand =
      PrimitiveFamilyOn negative Real.exp := by
  exact gap4.trans gap5
theorem gap7 :
    Continuous integrand := by
  unfold integrand
  exact Real.continuous_exp.comp continuous_abs.neg
theorem gap8 :
    ∃ F : ℝ → ℝ, Differentiable ℝ F ∧ Continuous (deriv F) ∧
      ∀ x, HasDerivAt F (integrand x) x := by
  refine ⟨normalizedPrimitive, ?_, ?_, normalizedPrimitive_hasDerivAt⟩
  · intro x
    exact (normalizedPrimitive_hasDerivAt x).differentiableAt
  · have hderiv : deriv normalizedPrimitive = integrand := by
      funext x
      exact (normalizedPrimitive_hasDerivAt x).deriv
    rw [hderiv]
    exact gap7
theorem gap9 :
    normalizedPrimitive 0 = 0 := by
  norm_num [normalizedPrimitive]
theorem gap10 :
    Tendsto normalizedPrimitive (nhdsWithin 0 (Set.Iio 0))
      (nhds (normalizedPrimitive 0)) := by
  exact (normalizedPrimitive_hasDerivAt 0).continuousAt.continuousWithinAt
theorem gap11 :
    Tendsto normalizedPrimitive (nhdsWithin 0 (Set.Iio 0)) (nhds 0) := by
  simpa only [gap9] using gap10
theorem gap12 :
    ∃ C₁ : ℝ, 0 = -1 + C₁ := by
  exact ⟨1, by norm_num⟩
theorem gap13 :
    ∃ C₁ C₂ : ℝ, -1 + C₁ = 1 + C₂ := by
  exact ⟨1, -1, by norm_num⟩
theorem gap14 :
    ∃ C₂ : ℝ, 0 = 1 + C₂ := by
  exact ⟨-1, by norm_num⟩
theorem gap15 :
    ∃ C₁ : ℝ, C₁ = 1 := by
  exact ⟨1, rfl⟩
theorem gap16 :
    ∃ C₂ : ℝ, C₂ = -1 := by
  exact ⟨-1, rfl⟩
theorem gap17 :
    ∀ x, normalizedPrimitive x =
      if 0 ≤ x then 1 - Real.exp (-x) else Real.exp x - 1 := by
  intro x
  rfl
theorem gap18 :
    Antiderivatives integrand = PrimitiveFamily normalizedPrimitive := by
  simpa [Antiderivatives, PrimitiveFamily, AntiderivativesOn, PrimitiveFamilyOn] using
    (antiderivativesOn_eq_primitiveFamilyOn_of_open
      (Set.univ : Set ℝ) isOpen_univ isPreconnected_univ Set.univ_nonempty
      integrand normalizedPrimitive normalizedPrimitive_hasDerivAt)

end
end ProofGap.Exercise2170
