import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

namespace ProofGap.Exercise1937

noncomputable section

def q (x : ℝ) := x ^ 2 + x + 1
def integrand (x : ℝ) := x ^ 2 / Real.sqrt (q x)
def Antiderivatives (f : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∀ x, HasDerivAt F (f x) x}
def PrimitiveFamily (p : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x, F x = p x + C}
def DecompositionFamily₁ : Set (ℝ → ℝ) :=
  {F | ∃ A ∈ Antiderivatives (fun x => q x / Real.sqrt (q x)),
    ∃ B ∈ Antiderivatives (fun x => (2 * x + 1) / Real.sqrt (q x)),
    ∃ D ∈ Antiderivatives (fun x => 1 / Real.sqrt (q x)),
    ∀ x, F x = A x - 1 / 2 * B x - 1 / 2 * D x}
def DecompositionFamily₂ : Set (ℝ → ℝ) :=
  {F | ∃ A ∈ Antiderivatives
      (fun x => Real.sqrt ((x + 1 / 2) ^ 2 + 3 / 4)),
    ∃ B ∈ Antiderivatives (fun x => deriv q x / Real.sqrt (q x)),
    ∃ D ∈ Antiderivatives
      (fun x => 1 / Real.sqrt ((x + 1 / 2) ^ 2 + 3 / 4)),
    ∀ x, F x = A x - 1 / 2 * B x - 1 / 2 * D x}
def primitiveLong (x : ℝ) :=
  (2 * x + 1) / 4 * Real.sqrt (q x) +
    3 / 8 * Real.log (x + 1 / 2 + Real.sqrt (q x)) -
    Real.sqrt (q x) -
    1 / 2 * Real.log (x + 1 / 2 + Real.sqrt (q x))
def primitive (x : ℝ) :=
  (2 * x - 3) / 4 * Real.sqrt (q x) -
    1 / 8 * Real.log (x + 1 / 2 + Real.sqrt (q x))

private theorem antiderivatives_eq_primitive (f p : ℝ → ℝ)
    (hp : ∀ x, HasDerivAt p (f x) x) :
    Antiderivatives f = PrimitiveFamily p := by
  unfold Antiderivatives PrimitiveFamily
  ext F
  simp only [Set.mem_setOf_eq]
  constructor
  · intro hF
    have hz : ∀ x, HasDerivAt (fun y => F y - p y) 0 x := by
      intro x
      convert (hF x).sub (hp x) using 1 <;> ring
    have hd : Differentiable ℝ (fun y => F y - p y) :=
      fun x => (hz x).differentiableAt
    refine ⟨F 0 - p 0, ?_⟩
    intro x
    have heq : F x - p x = F 0 - p 0 :=
      is_const_of_deriv_eq_zero hd (fun y => (hz y).deriv) x 0
    linarith
  · rintro ⟨C, hC⟩
    rw [show F = fun x => p x + C from funext hC]
    intro x
    exact (hp x).add_const C

theorem gap1 :
    Antiderivatives integrand = DecompositionFamily₁ := by
  unfold Antiderivatives DecompositionFamily₁
  ext F
  simp only [Set.mem_setOf_eq]
  have hqpos : ∀ x : ℝ, 0 < q x := by
    intro x
    dsimp [q]
    nlinarith [sq_nonneg (x + 1 / 2)]
  have hqderiv : ∀ x : ℝ, HasDerivAt q (2 * x + 1) x := by
    intro x
    convert ((((hasDerivAt_id x).pow 2).add (hasDerivAt_id x)).add_const 1) using 1 <;>
      simp [q] <;> ring
  have hs : ∀ x : ℝ, HasDerivAt (fun y => Real.sqrt (q y))
      ((2 * x + 1) / (2 * Real.sqrt (q x))) x := by
    intro x
    have hs0 := (Real.hasDerivAt_sqrt (ne_of_gt (hqpos x))).comp x (hqderiv x)
    convert hs0 using 1
    field_simp [ne_of_gt (Real.sqrt_pos.2 (hqpos x))]
    <;> ring
  have hB : ∀ x : ℝ, HasDerivAt (fun y => 2 * Real.sqrt (q y))
      ((2 * x + 1) / Real.sqrt (q x)) x := by
    intro x
    convert (hs x).const_mul 2 using 1 <;> ring
  have hD : ∀ x : ℝ,
      HasDerivAt (fun y => Real.log (y + 1 / 2 + Real.sqrt (q y)))
        (1 / Real.sqrt (q x)) x := by
    intro x
    have hspos : 0 < Real.sqrt (q x) := Real.sqrt_pos.2 (hqpos x)
    have hs_sq : Real.sqrt (q x) ^ 2 = q x := Real.sq_sqrt (le_of_lt (hqpos x))
    have hs_sq' : Real.sqrt (q x) ^ 2 = (x + 1 / 2) ^ 2 + 3 / 4 := by
      rw [hs_sq]
      dsimp [q]
      ring
    have hu : 0 < x + 1 / 2 + Real.sqrt (q x) := by
      nlinarith [sq_nonneg (x + 1 / 2), Real.sqrt_nonneg (q x), hs_sq']
    have hi : HasDerivAt (fun y => y + 1 / 2 + Real.sqrt (q y))
        (1 + (2 * x + 1) / (2 * Real.sqrt (q x))) x := by
      convert (((hasDerivAt_id x).add_const (1 / 2)).add (hs x)) using 1 <;> ring
    have hfactor : 1 + (2 * x + 1) / (2 * Real.sqrt (q x)) =
        (x + 1 / 2 + Real.sqrt (q x)) / Real.sqrt (q x) := by
      field_simp [ne_of_gt hspos]
      <;> ring
    have hu2 : 0 < x * 2 + 1 + Real.sqrt (q x) * 2 := by
      nlinarith [hu]
    have hl := (Real.hasDerivAt_log (ne_of_gt hu)).comp x hi
    convert hl using 1
    rw [hfactor]
    field_simp [ne_of_gt hu, ne_of_gt hspos, ne_of_gt hu2]
  have hdecomp : ∀ x : ℝ, integrand x =
      q x / Real.sqrt (q x) -
        1 / 2 * ((2 * x + 1) / Real.sqrt (q x)) -
        1 / 2 * (1 / Real.sqrt (q x)) := by
    intro x
    have hspos : 0 < Real.sqrt (q x) := Real.sqrt_pos.2 (hqpos x)
    rw [integrand]
    field_simp [ne_of_gt hspos]
    dsimp [q]
    ring
  constructor
  · intro hF
    refine ⟨fun y => F y + 1 / 2 * (2 * Real.sqrt (q y)) +
        1 / 2 * Real.log (y + 1 / 2 + Real.sqrt (q y)), ?_,
      fun y => 2 * Real.sqrt (q y), hB,
      fun y => Real.log (y + 1 / 2 + Real.sqrt (q y)), hD, ?_⟩
    · intro x
      convert (((hF x).add ((hB x).const_mul (1 / 2))).add
        ((hD x).const_mul (1 / 2))) using 1
      rw [hdecomp x]
      ring
    · intro x
      ring
  · rintro ⟨A, hA, B, hB', D, hD', hF⟩
    rw [show F = fun x => A x - 1 / 2 * B x - 1 / 2 * D x from funext hF]
    intro x
    convert ((hA x).sub ((hB' x).const_mul (1 / 2))).sub
      ((hD' x).const_mul (1 / 2)) using 1
    exact hdecomp x
theorem gap2 :
    Antiderivatives integrand = DecompositionFamily₂ := by
  rw [gap1]
  have hqpos : ∀ x : ℝ, 0 < q x := by
    intro x
    dsimp [q]
    nlinarith [sq_nonneg (x + 1 / 2)]
  have hA : (fun x : ℝ => Real.sqrt ((x + 1 / 2) ^ 2 + 3 / 4)) =
      (fun x => q x / Real.sqrt (q x)) := by
    funext x
    have hc : (x + 1 / 2) ^ 2 + 3 / 4 = q x := by
      dsimp [q]
      ring
    rw [hc]
    have hspos : 0 < Real.sqrt (q x) := Real.sqrt_pos.2 (hqpos x)
    apply (eq_div_iff (ne_of_gt hspos)).2
    nlinarith [Real.sq_sqrt (le_of_lt (hqpos x))]
  have hB : (fun x : ℝ => deriv q x / Real.sqrt (q x)) =
      (fun x => (2 * x + 1) / Real.sqrt (q x)) := by
    funext x
    have hqd : HasDerivAt q (2 * x + 1) x := by
      convert ((((hasDerivAt_id x).pow 2).add (hasDerivAt_id x)).add_const 1) using 1 <;>
        simp [q] <;> ring
    rw [hqd.deriv]
  have hD : (fun x : ℝ => 1 / Real.sqrt ((x + 1 / 2) ^ 2 + 3 / 4)) =
      (fun x => 1 / Real.sqrt (q x)) := by
    funext x
    congr 2
    dsimp [q]
    ring
  unfold DecompositionFamily₂ DecompositionFamily₁
  rw [hA, hB, hD]
theorem gap3 :
    Antiderivatives integrand = PrimitiveFamily primitiveLong := by
  have hqpos : ∀ x : ℝ, 0 < q x := by
    intro x
    dsimp [q]
    nlinarith [sq_nonneg (x + 1 / 2)]
  have hqderiv : ∀ x : ℝ, HasDerivAt q (2 * x + 1) x := by
    intro x
    convert ((((hasDerivAt_id x).pow 2).add (hasDerivAt_id x)).add_const 1) using 1 <;>
      simp [q] <;> ring
  have hs : ∀ x : ℝ, HasDerivAt (fun y => Real.sqrt (q y))
      ((2 * x + 1) / (2 * Real.sqrt (q x))) x := by
    intro x
    have hs0 := (Real.hasDerivAt_sqrt (ne_of_gt (hqpos x))).comp x (hqderiv x)
    convert hs0 using 1
    field_simp [ne_of_gt (Real.sqrt_pos.2 (hqpos x))]
    <;> ring
  have hlog : ∀ x : ℝ,
      HasDerivAt (fun y => Real.log (y + 1 / 2 + Real.sqrt (q y)))
        (1 / Real.sqrt (q x)) x := by
    intro x
    have hspos : 0 < Real.sqrt (q x) := Real.sqrt_pos.2 (hqpos x)
    have hs_sq : Real.sqrt (q x) ^ 2 = q x := Real.sq_sqrt (le_of_lt (hqpos x))
    have hs_sq' : Real.sqrt (q x) ^ 2 = (x + 1 / 2) ^ 2 + 3 / 4 := by
      rw [hs_sq]
      dsimp [q]
      ring
    have hu : 0 < x + 1 / 2 + Real.sqrt (q x) := by
      nlinarith [sq_nonneg (x + 1 / 2), Real.sqrt_nonneg (q x), hs_sq']
    have hi : HasDerivAt (fun y => y + 1 / 2 + Real.sqrt (q y))
        (1 + (2 * x + 1) / (2 * Real.sqrt (q x))) x := by
      convert (((hasDerivAt_id x).add_const (1 / 2)).add (hs x)) using 1 <;> ring
    have hfactor : 1 + (2 * x + 1) / (2 * Real.sqrt (q x)) =
        (x + 1 / 2 + Real.sqrt (q x)) / Real.sqrt (q x) := by
      field_simp [ne_of_gt hspos]
      <;> ring
    have hu2 : 0 < x * 2 + 1 + Real.sqrt (q x) * 2 := by
      nlinarith [hu]
    have hl := (Real.hasDerivAt_log (ne_of_gt hu)).comp x hi
    convert hl using 1
    rw [hfactor]
    field_simp [ne_of_gt hu, ne_of_gt hspos, ne_of_gt hu2]
  have hp : ∀ x : ℝ, HasDerivAt primitive (integrand x) x := by
    intro x
    have ha : HasDerivAt (fun y : ℝ => (2 * y - 3) / 4) (1 / 2) x := by
      have ha0 := ((hasDerivAt_id x).const_mul (1 / 2)).sub_const (3 / 4)
      convert ha0 using 1
      · funext y
        dsimp
        ring
      · ring
    have hspos : 0 < Real.sqrt (q x) := Real.sqrt_pos.2 (hqpos x)
    have hs_sq : Real.sqrt (q x) ^ 2 = q x := Real.sq_sqrt (le_of_lt (hqpos x))
    have hs_sq' : Real.sqrt (q x) ^ 2 = x ^ 2 + x + 1 := by
      simpa [q] using hs_sq
    have hcalc : 1 / 2 * Real.sqrt (q x) +
          (2 * x - 3) / 4 * ((2 * x + 1) / (2 * Real.sqrt (q x))) -
          1 / 8 * (1 / Real.sqrt (q x)) = integrand x := by
      rw [integrand]
      field_simp [ne_of_gt hspos] <;> nlinarith [hs_sq']
    have hp0 := (ha.mul (hs x)).sub ((hlog x).const_mul (1 / 8))
    change HasDerivAt primitive
      (1 / 2 * Real.sqrt (q x) +
        (2 * x - 3) / 4 * ((2 * x + 1) / (2 * Real.sqrt (q x))) -
        1 / 8 * (1 / Real.sqrt (q x))) x at hp0
    rw [hcalc] at hp0
    exact hp0
  have hlong : primitiveLong = primitive := by
    funext x
    dsimp [primitiveLong, primitive]
    ring
  rw [hlong]
  exact antiderivatives_eq_primitive integrand primitive hp
theorem gap4 :
    Antiderivatives integrand = PrimitiveFamily primitive := by
  have hlong : primitiveLong = primitive := by
    funext x
    dsimp [primitiveLong, primitive]
    ring
  simpa only [hlong] using gap3

end
end ProofGap.Exercise1937
