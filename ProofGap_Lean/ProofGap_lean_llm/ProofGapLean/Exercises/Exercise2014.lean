import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise2014
noncomputable section

def integrand (x : ℝ) := Real.cos x * Real.cos (2 * x) * Real.cos (3 * x)
def firstReduced (x : ℝ) := Real.cos (2 * x) *
  (Real.cos (4 * x) + Real.cos (2 * x))
def leftReduced (x : ℝ) := Real.cos (6 * x) + Real.cos (2 * x)
def rightReduced (x : ℝ) := 1 + Real.cos (4 * x)
def primitive (x : ℝ) := (1 / 24 : ℝ) * Real.sin (6 * x) +
  (1 / 8 : ℝ) * Real.sin (2 * x) + (1 / 16 : ℝ) * Real.sin (4 * x) + x / 4
def Family (f : ℝ → ℝ) := {F : ℝ → ℝ | ∀ x, HasDerivAt F (f x) x}
def ScaledFamily (f : ℝ → ℝ) (c : ℝ) :=
  {F : ℝ → ℝ | ∃ G ∈ Family f, ∀ x, F x = c * G x}
def PairFamily (f g : ℝ → ℝ) :=
  {F : ℝ → ℝ | ∃ P ∈ Family f, ∃ Q ∈ Family g,
    ∀ x, F x = (1 / 4 : ℝ) * P x + (1 / 4 : ℝ) * Q x}
def Translates (p : ℝ → ℝ) :=
  {F : ℝ → ℝ | ∃ C, ∀ x, F x = p x + C}

private theorem trig_reductions (x : ℝ) :
    integrand x = (1 / 2 : ℝ) * firstReduced x ∧
      integrand x = (1 / 4 : ℝ) * leftReduced x +
        (1 / 4 : ℝ) * rightReduced x := by
  have h13 :
      2 * Real.cos x * Real.cos (3 * x) =
        Real.cos (4 * x) + Real.cos (2 * x) := by
    calc
      2 * Real.cos x * Real.cos (3 * x) =
          Real.cos (3 * x + x) + Real.cos (3 * x - x) := by
            rw [Real.cos_add, Real.cos_sub]
            ring
      _ = Real.cos (4 * x) + Real.cos (2 * x) := by ring_nf
  have h24 :
      2 * Real.cos (2 * x) * Real.cos (4 * x) =
        Real.cos (6 * x) + Real.cos (2 * x) := by
    calc
      2 * Real.cos (2 * x) * Real.cos (4 * x) =
          Real.cos (4 * x + 2 * x) + Real.cos (4 * x - 2 * x) := by
            rw [Real.cos_add, Real.cos_sub]
            ring
      _ = Real.cos (6 * x) + Real.cos (2 * x) := by ring_nf
  have h22 :
      2 * Real.cos (2 * x) * Real.cos (2 * x) =
        1 + Real.cos (4 * x) := by
    calc
      2 * Real.cos (2 * x) * Real.cos (2 * x) =
          Real.cos (2 * x + 2 * x) + Real.cos (2 * x - 2 * x) := by
            rw [Real.cos_add, Real.cos_sub]
            ring
      _ = 1 + Real.cos (4 * x) := by
        ring_nf
        rw [Real.cos_zero]
        ring
  have hfirst : integrand x = (1 / 2 : ℝ) * firstReduced x := by
    unfold integrand firstReduced
    rw [← h13]
    ring
  constructor
  · exact hfirst
  · calc
      integrand x = (1 / 2 : ℝ) * firstReduced x := hfirst
      _ = (1 / 4 : ℝ) * leftReduced x +
          (1 / 4 : ℝ) * rightReduced x := by
        unfold firstReduced leftReduced rightReduced
        rw [← h24, ← h22]
        ring

private def rightPrimitive (x : ℝ) :=
  x + (1 / 4 : ℝ) * Real.sin (4 * x)

private theorem rightPrimitive_hasDerivAt (x : ℝ) :
    HasDerivAt rightPrimitive (rightReduced x) x := by
  have h4 : HasDerivAt (fun y => (1 / 4 : ℝ) * Real.sin (4 * y))
      (Real.cos (4 * x)) x := by
    convert (((hasDerivAt_id x).const_mul 4).sin.const_mul (1 / 4 : ℝ)) using 1 <;>
      simp only [id] <;> ring_nf
  unfold rightPrimitive rightReduced
  exact (hasDerivAt_id x).add h4

private theorem primitive_hasDerivAt (x : ℝ) :
    HasDerivAt primitive (integrand x) x := by
  have h6 : HasDerivAt (fun y => (1 / 24 : ℝ) * Real.sin (6 * y))
      ((1 / 4 : ℝ) * Real.cos (6 * x)) x := by
    convert (((hasDerivAt_id x).const_mul 6).sin.const_mul (1 / 24 : ℝ)) using 1 <;>
      simp only [id] <;> ring_nf
  have h2 : HasDerivAt (fun y => (1 / 8 : ℝ) * Real.sin (2 * y))
      ((1 / 4 : ℝ) * Real.cos (2 * x)) x := by
    convert (((hasDerivAt_id x).const_mul 2).sin.const_mul (1 / 8 : ℝ)) using 1 <;>
      simp only [id] <;> ring_nf
  have h4 : HasDerivAt (fun y => (1 / 16 : ℝ) * Real.sin (4 * y))
      ((1 / 4 : ℝ) * Real.cos (4 * x)) x := by
    convert (((hasDerivAt_id x).const_mul 4).sin.const_mul (1 / 16 : ℝ)) using 1 <;>
      simp only [id] <;> ring_nf
  have hx : HasDerivAt (fun y : ℝ => y / 4) (1 / 4 : ℝ) x := by
    simpa using (hasDerivAt_id x).div_const 4
  have hbase : HasDerivAt primitive
      ((1 / 4 : ℝ) * Real.cos (6 * x) +
        (1 / 4 : ℝ) * Real.cos (2 * x) +
        (1 / 4 : ℝ) * Real.cos (4 * x) + (1 / 4 : ℝ)) x := by
    unfold primitive
    exact (((h6.add h2).add h4).add hx)
  have hr := (trig_reductions x).2
  unfold leftReduced rightReduced at hr
  convert hbase using 1
  rw [hr]
  ring

theorem gap1 : Family integrand = ScaledFamily firstReduced (1 / 2) := by
  ext F
  change (∀ x, HasDerivAt F (integrand x) x) ↔
    ∃ G, (∀ x, HasDerivAt G (firstReduced x) x) ∧
      ∀ x, F x = (1 / 2 : ℝ) * G x
  constructor
  · intro hF
    refine ⟨fun y => 2 * F y, ?_, ?_⟩
    · intro x
      have hd : HasDerivAt (fun y => 2 * F y) (2 * integrand x) x :=
        (hF x).const_mul 2
      convert hd using 1
      rw [(trig_reductions x).1]
      ring
    · intro x
      ring
  · rintro ⟨G, hG, hFG⟩
    have hfun : F = fun y => (1 / 2 : ℝ) * G y := funext hFG
    intro x
    rw [hfun]
    have hd : HasDerivAt (fun y => (1 / 2 : ℝ) * G y)
        ((1 / 2 : ℝ) * firstReduced x) x :=
      (hG x).const_mul (1 / 2 : ℝ)
    simpa only [(trig_reductions x).1] using hd
theorem gap2 : Family integrand = PairFamily leftReduced rightReduced := by
  ext F
  change (∀ x, HasDerivAt F (integrand x) x) ↔
    ∃ P, (∀ x, HasDerivAt P (leftReduced x) x) ∧
      ∃ Q, (∀ x, HasDerivAt Q (rightReduced x) x) ∧
        ∀ x, F x = (1 / 4 : ℝ) * P x + (1 / 4 : ℝ) * Q x
  constructor
  · intro hF
    refine ⟨fun y => 4 * F y - rightPrimitive y, ?_,
      rightPrimitive, rightPrimitive_hasDerivAt, ?_⟩
    · intro x
      have hd : HasDerivAt (fun y => 4 * F y - rightPrimitive y)
          (4 * integrand x - rightReduced x) x :=
        ((hF x).const_mul 4).sub (rightPrimitive_hasDerivAt x)
      convert hd using 1
      rw [(trig_reductions x).2]
      ring
    · intro x
      ring
  · rintro ⟨P, hP, Q, hQ, hF⟩
    have hfun : F = fun y =>
        (1 / 4 : ℝ) * P y + (1 / 4 : ℝ) * Q y := funext hF
    intro x
    rw [hfun]
    have hd : HasDerivAt
        (fun y => (1 / 4 : ℝ) * P y + (1 / 4 : ℝ) * Q y)
        ((1 / 4 : ℝ) * leftReduced x + (1 / 4 : ℝ) * rightReduced x) x :=
      ((hP x).const_mul (1 / 4 : ℝ)).add
        ((hQ x).const_mul (1 / 4 : ℝ))
    simpa only [(trig_reductions x).2] using hd
theorem gap3 : Family integrand = Translates primitive := by
  ext F
  change (∀ x, HasDerivAt F (integrand x) x) ↔
    ∃ C, ∀ x, F x = primitive x + C
  constructor
  · intro hF
    let D : ℝ → ℝ := fun y => F y - primitive y
    have hD : ∀ x, HasDerivAt D 0 x := by
      intro x
      dsimp [D]
      convert (hF x).sub (primitive_hasDerivAt x) using 1 <;> ring
    have hdiff : Differentiable ℝ D := fun x => (hD x).differentiableAt
    have hderiv : ∀ x, deriv D x = 0 := fun x => (hD x).deriv
    refine ⟨D 0, ?_⟩
    intro x
    have hc : D x = D 0 :=
      is_const_of_deriv_eq_zero hdiff hderiv x 0
    calc
      F x = primitive x + D x := by dsimp [D]; ring
      _ = primitive x + D 0 := by rw [hc]
  · rintro ⟨C, hF⟩
    have hfun : F = fun y => primitive y + C := funext hF
    intro x
    rw [hfun]
    exact (primitive_hasDerivAt x).add_const C

end
end ProofGap.Exercise2014
