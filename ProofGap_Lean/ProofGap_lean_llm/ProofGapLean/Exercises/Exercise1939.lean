import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise1939

noncomputable section

def xOf (t : ℝ) := (1 - t ^ 2) / (1 + t ^ 2)
def parameterBranch : Set ℝ := {t | 0 < t}
def xBranch : Set ℝ := {x | -1 < x ∧ x < 1}
def AntiderivativesOn (s : Set ℝ) (f : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∀ x ∈ s, HasDerivAt F (f x) x}
def PrimitiveFamilyOn (s : Set ℝ) (p : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x ∈ s, F x = p x + C}
def sourceParamIntegrand (t : ℝ) :=
  1 / ((1 - xOf t) ^ 2 * Real.sqrt (1 - xOf t ^ 2)) * deriv xOf t
def rationalParamIntegrand (t : ℝ) := (1 + t ^ 2) / t ^ 4
def NegativeHalfFamily : Set (ℝ → ℝ) :=
  {F | ∃ G ∈ AntiderivativesOn parameterBranch rationalParamIntegrand,
    ∀ t ∈ parameterBranch, F t = -1 / 2 * G t}
def parameterPrimitive (t : ℝ) := 1 / (6 * t ^ 3) + 1 / (2 * t)
def xPrimitiveAtParam (t : ℝ) :=
  (2 - xOf t) / (3 * (1 - xOf t) ^ 2) *
    Real.sqrt (1 - xOf t ^ 2)
def sourceXIntegrand (x : ℝ) :=
  1 / ((1 - x) ^ 2 * Real.sqrt (1 - x ^ 2))
def xPrimitive (x : ℝ) :=
  (2 - x) / (3 * (1 - x) ^ 2) * Real.sqrt (1 - x ^ 2)

private theorem pairwise_eq_of_hasDerivAt_zero_on_Ioo
    (a b : ℝ) (h : ℝ → ℝ)
    (hd : ∀ x ∈ Set.Ioo a b, HasDerivAt h 0 x) :
    Set.Pairwise (Set.Ioo a b) fun x y => h x = h y := by
  have hdiff : DifferentiableOn ℝ h (Set.Ioo a b) := by
    intro x hx
    exact (hd x hx).differentiableAt.differentiableWithinAt
  have hz : ∀ x ∈ Set.Ioo a b, deriv h x = 0 := by
    intro x hx
    exact (hd x hx).deriv
  have hopen : IsOpen (Set.Ioo a b) := isOpen_Ioo
  have hconv : Convex ℝ (Set.Ioo a b) := convex_Ioo a b
  intro x hx y hy _
  exact hopen.is_const_of_deriv_eq_zero hconv.isPreconnected hdiff hz hx hy

private theorem antiderivativesOn_eq_primitiveFamilyOn_of_open_const
    (s : Set ℝ) (hsopen : IsOpen s)
    (x₀ : ℝ) (hx₀ : x₀ ∈ s) (f p : ℝ → ℝ)
    (hp : ∀ x ∈ s, HasDerivAt p (f x) x)
    (hzero_const : ∀ h : ℝ → ℝ,
      (∀ x ∈ s, HasDerivAt h 0 x) →
        Set.Pairwise s fun x y => h x = h y) :
    AntiderivativesOn s f = PrimitiveFamilyOn s p := by
  ext F
  change
    (∀ x ∈ s, HasDerivAt F (f x) x) ↔
      ∃ C : ℝ, ∀ x ∈ s, F x = p x + C
  constructor
  · intro hF
    let h : ℝ → ℝ := fun x => F x - p x
    have hd : ∀ x ∈ s, HasDerivAt h 0 x := by
      intro x hx
      simpa [h] using (hF x hx).sub (hp x hx)
    have hconst := hzero_const h hd
    refine ⟨F x₀ - p x₀, ?_⟩
    intro x hx
    have heq : h x = h x₀ := by
      by_cases hxx : x = x₀
      · simpa [hxx]
      · exact hconst hx hx₀ hxx
    dsimp [h] at heq
    linarith
  · rintro ⟨C, hF⟩
    intro x hx
    have heq : F =ᶠ[nhds x] fun y => p y + C := by
      filter_upwards [hsopen.mem_nhds hx] with y hy
      exact hF y hy
    exact (heq.hasDerivAt_iff).2 ((hp x hx).add_const C)

theorem gap1 (t : ℝ) :
    xOf t = (1 - t ^ 2) / (1 + t ^ 2) := by
  rfl
theorem gap2 (t : ℝ) :
    HasDerivAt xOf (-4 * t / (1 + t ^ 2) ^ 2) t := by
  unfold xOf
  have hden : 1 + t ^ 2 ≠ 0 := by
    nlinarith [sq_nonneg t]
  convert
    (((hasDerivAt_const (x := t) (1 : ℝ)).sub ((hasDerivAt_id t).pow 2)).div
      ((hasDerivAt_const (x := t) (1 : ℝ)).add ((hasDerivAt_id t).pow 2))
      (by simpa [id] using hden)) using 1 <;>
    simp [id] <;> ring
theorem gap3 (t : ℝ) :
    1 - xOf t = 2 * t ^ 2 / (1 + t ^ 2) := by
  unfold xOf
  have hd : 1 + t ^ 2 ≠ 0 := by positivity
  field_simp [hd]
  ring
theorem gap4 (t : ℝ) (ht : t ∈ parameterBranch) :
    Real.sqrt (1 - xOf t ^ 2) = 2 * t / (1 + t ^ 2) := by
  change 0 < t at ht
  have hd : 0 < 1 + t ^ 2 := by positivity
  have hsquare :
      1 - xOf t ^ 2 = (2 * t / (1 + t ^ 2)) ^ 2 := by
    rw [gap1]
    field_simp [ne_of_gt hd]
    ring
  have hrhs : 0 < 2 * t / (1 + t ^ 2) := by
    exact div_pos (mul_pos (by norm_num) ht) hd
  rw [hsquare, Real.sqrt_sq_eq_abs, abs_of_pos hrhs]
theorem gap5 :
    AntiderivativesOn parameterBranch sourceParamIntegrand =
      NegativeHalfFamily := by
  have hs (t : ℝ) (ht : t ∈ parameterBranch) :
      sourceParamIntegrand t = -1 / 2 * rationalParamIntegrand t := by
    change 0 < t at ht
    have ht0 : t ≠ 0 := ne_of_gt ht
    unfold sourceParamIntegrand rationalParamIntegrand
    rw [gap3 t, gap4 t ht, (gap2 t).deriv]
    field_simp [ht0]
    ring
  ext F
  change
    (∀ t ∈ parameterBranch, HasDerivAt F (sourceParamIntegrand t) t) ↔
      ∃ G, (∀ t ∈ parameterBranch,
        HasDerivAt G (rationalParamIntegrand t) t) ∧
        ∀ t ∈ parameterBranch, F t = -1 / 2 * G t
  constructor
  · intro hF
    refine ⟨fun t => -2 * F t, ?_, ?_⟩
    · intro t ht
      have hd := (hF t ht).const_mul (-2)
      convert hd using 1
      rw [hs t ht]
      ring
    · intro t ht
      ring
  · rintro ⟨G, hG, hFG⟩
    intro t ht
    have hscaled : HasDerivAt (fun x => -1 / 2 * G x)
        (-1 / 2 * rationalParamIntegrand t) t :=
      (hG t ht).const_mul (-1 / 2)
    have hscaled' : HasDerivAt (fun x => -1 / 2 * G x)
        (sourceParamIntegrand t) t := by
      convert hscaled using 1
      exact hs t ht
    have heq : F =ᶠ[nhds t] fun x => -1 / 2 * G x := by
      have hopen : parameterBranch ∈ nhds t := by
        apply (isOpen_Ioi : IsOpen (Set.Ioi (0 : ℝ))).mem_nhds
        exact ht
      filter_upwards [hopen] with x hx
      exact hFG x hx
    exact (heq.hasDerivAt_iff).2 hscaled'
theorem gap6 :
    NegativeHalfFamily =
      PrimitiveFamilyOn parameterBranch parameterPrimitive := by
  rw [← gap5]
  apply antiderivativesOn_eq_primitiveFamilyOn_of_open_const
    (x₀ := (1 : ℝ))
  · simpa [parameterBranch] using
      (isOpen_Ioi : IsOpen (Set.Ioi (0 : ℝ)))
  · norm_num [parameterBranch]
  · intro t ht
    change 0 < t at ht
    have ht0 : t ≠ 0 := ne_of_gt ht
    have hs :
        sourceParamIntegrand t = -1 / 2 * rationalParamIntegrand t := by
      unfold sourceParamIntegrand rationalParamIntegrand
      rw [gap3 t, gap4 t ht, (gap2 t).deriv]
      field_simp [ht0]
      ring
    have hden3 : 6 * t ^ 3 ≠ 0 :=
      mul_ne_zero (by norm_num) (pow_ne_zero 3 ht0)
    have hfirst : HasDerivAt (fun y : ℝ => 1 / (6 * y ^ 3))
        (-1 / (2 * t ^ 4)) t := by
      convert
        ((hasDerivAt_const (x := t) (1 : ℝ)).div
          ((hasDerivAt_const (x := t) (6 : ℝ)).mul
            ((hasDerivAt_id t).pow 3))
          (by simpa [id] using hden3)) using 1 <;>
        simp [id] <;> field_simp [ht0] <;> ring
    have hden1 : 2 * t ≠ 0 :=
      mul_ne_zero (by norm_num) ht0
    have hsecond : HasDerivAt (fun y : ℝ => 1 / (2 * y))
        (-1 / (2 * t ^ 2)) t := by
      convert
        ((hasDerivAt_const (x := t) (1 : ℝ)).div
          ((hasDerivAt_const (x := t) (2 : ℝ)).mul
            (hasDerivAt_id t))
          (by simpa [id] using hden1)) using 1 <;>
        simp [id] <;> field_simp [ht0] <;> ring
    unfold parameterPrimitive
    convert hfirst.add hsecond using 1
    rw [hs]
    unfold rationalParamIntegrand
    field_simp [ht0]
    ring
  · intro h hd
    intro x hx y hy hxy
    change 0 < x at hx
    change 0 < y at hy
    let b : ℝ := max x y + 1
    have hxb : x < b := by
      dsimp [b]
      linarith [le_max_left x y]
    have hyb : y < b := by
      dsimp [b]
      linarith [le_max_right x y]
    have hlocal : ∀ z ∈ Set.Ioo (0 : ℝ) b, HasDerivAt h 0 z := by
      intro z hz
      apply hd z
      change 0 < z
      exact hz.1
    have hc := pairwise_eq_of_hasDerivAt_zero_on_Ioo
      (a := (0 : ℝ)) (b := b) h hlocal
    exact hc ⟨hx, hxb⟩ ⟨hy, hyb⟩ hxy
theorem gap7 :
    PrimitiveFamilyOn parameterBranch parameterPrimitive =
      PrimitiveFamilyOn parameterBranch xPrimitiveAtParam := by
  have hp (t : ℝ) (ht : t ∈ parameterBranch) :
      xPrimitiveAtParam t = parameterPrimitive t := by
    change 0 < t at ht
    have ht0 : t ≠ 0 := ne_of_gt ht
    unfold xPrimitiveAtParam parameterPrimitive
    rw [gap3 t, gap4 t ht, gap1 t]
    field_simp [ht0]
    ring
  ext F
  change
    (∃ C : ℝ, ∀ t ∈ parameterBranch,
      F t = parameterPrimitive t + C) ↔
    ∃ C : ℝ, ∀ t ∈ parameterBranch,
      F t = xPrimitiveAtParam t + C
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨C, ?_⟩
    intro t ht
    rw [hC t ht, hp t ht]
  · rintro ⟨C, hC⟩
    refine ⟨C, ?_⟩
    intro t ht
    rw [hC t ht, hp t ht]
theorem gap8 :
    AntiderivativesOn xBranch sourceXIntegrand =
      PrimitiveFamilyOn xBranch xPrimitive := by
  apply antiderivativesOn_eq_primitiveFamilyOn_of_open_const
    (x₀ := (0 : ℝ))
  · simpa [xBranch] using
      (isOpen_Ioo : IsOpen (Set.Ioo (-1 : ℝ) 1))
  · norm_num [xBranch]
  · intro x hx
    rcases hx with ⟨hxlow, hxhigh⟩
    have h1mx : 0 < 1 - x := sub_pos.mpr hxhigh
    have h1px : 0 < 1 + x := by linarith
    have hinside : 0 < 1 - x ^ 2 := by
      nlinarith [mul_pos h1mx h1px]
    have hroot : 0 < Real.sqrt (1 - x ^ 2) :=
      Real.sqrt_pos.2 hinside
    have hsquare : Real.sqrt (1 - x ^ 2) ^ 2 = 1 - x ^ 2 :=
      Real.sq_sqrt (le_of_lt hinside)
    have hinner : HasDerivAt (fun y : ℝ => 1 - y ^ 2) (-2 * x) x := by
      convert
        (hasDerivAt_const (x := x) (1 : ℝ)).sub
          ((hasDerivAt_id x).pow 2) using 1 <;>
        simp [id] <;> ring
    have hs : HasDerivAt (fun y : ℝ => Real.sqrt (1 - y ^ 2))
        (-x / Real.sqrt (1 - x ^ 2)) x := by
      convert
        (Real.hasDerivAt_sqrt (ne_of_gt hinside)).comp x hinner using 1 <;>
        field_simp [ne_of_gt hroot] <;> ring
    have hqden : 3 * (1 - x) ^ 2 ≠ 0 :=
      mul_ne_zero (by norm_num) (pow_ne_zero 2 (ne_of_gt h1mx))
    have hqraw :=
      ((hasDerivAt_const (x := x) (2 : ℝ)).sub (hasDerivAt_id x)).div
        ((hasDerivAt_const (x := x) (3 : ℝ)).mul
          (((hasDerivAt_const (x := x) (1 : ℝ)).sub
            (hasDerivAt_id x)).pow 2))
        (by simpa [id] using hqden)
    have hq : HasDerivAt
        (fun y : ℝ => (2 - y) / (3 * (1 - y) ^ 2))
        ((3 - x) / (3 * (1 - x) ^ 3)) x := by
      convert hqraw using 1 <;>
        simp [id] <;> field_simp [ne_of_gt h1mx] <;> ring
    unfold xPrimitive sourceXIntegrand
    convert hq.mul hs using 1
    field_simp [ne_of_gt h1mx, ne_of_gt hroot]
    nlinarith [hsquare]
  · intro h hd
    apply pairwise_eq_of_hasDerivAt_zero_on_Ioo
    intro z hz
    apply hd z
    simpa [xBranch] using hz

end
end ProofGap.Exercise1939
