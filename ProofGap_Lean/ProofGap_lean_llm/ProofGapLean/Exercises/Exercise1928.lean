import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Order.IntermediateValue

namespace ProofGap.Exercise1928

noncomputable section

def cubeRoot (x : ℝ) := Real.sign x * Real.rpow |x| (1 / 3 : ℝ)
def xOf (t : ℝ) := t ^ 3 - 2
def regularBranch : Set ℝ := {t | t ≠ 1}
def AntiderivativesOn (s : Set ℝ) (f : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∀ t ∈ s, HasDerivAt F (f t) t}
def BranchwisePrimitiveFamilyOn (s : Set ℝ) (p : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∀ u : Set ℝ, IsOpen u → IsPreconnected u → u ⊆ s →
    ∃ C : ℝ, ∀ t ∈ u, F t = p t + C}
def sourceIntegrand (t : ℝ) :=
  xOf t * cubeRoot (2 + xOf t) /
    (xOf t + cubeRoot (2 + xOf t)) * deriv xOf t
def transformed₁ (t : ℝ) :=
  (t ^ 6 - 2 * t ^ 3) / (t ^ 3 + t - 2)
def transformed₂ (t : ℝ) :=
  t ^ 3 - t + (t ^ 2 - 2 * t) / (t ^ 3 + t - 2)
def ScaledFamily (p : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ G ∈ AntiderivativesOn regularBranch p,
    ∀ t ∈ regularBranch, F t = 3 * G t}
def partialFraction (t : ℝ) :=
  -1 / (4 * (t - 1)) + ((5 / 4 : ℝ) * t - 1 / 2) / (t ^ 2 + t + 2)
def PartialFractionFamily : Set (ℝ → ℝ) :=
  {F | ∃ G ∈ AntiderivativesOn regularBranch partialFraction,
    ∀ t ∈ regularBranch,
      F t = 3 / 4 * t ^ 4 - 3 / 2 * t ^ 2 + 3 * G t}
def AuxiliaryFamily : Set (ℝ → ℝ) :=
  {F | ∃ A ∈ AntiderivativesOn regularBranch
      (fun t => (2 * t + 1) / (t ^ 2 + t + 2)),
    ∃ B ∈ AntiderivativesOn regularBranch
      (fun t => 1 / ((t + 1 / 2) ^ 2 + 7 / 4)),
    ∀ t ∈ regularBranch,
      F t = 3 / 4 * t ^ 4 - 3 / 2 * t ^ 2 -
        3 / 4 * Real.log |t - 1| + 15 / 8 * A t - 27 / 8 * B t}
def primitive (t : ℝ) :=
  3 / 4 * t ^ 4 - 3 / 2 * t ^ 2 -
    3 / 4 * Real.log |t - 1| +
    15 / 8 * Real.log (t ^ 2 + t + 2) -
    27 / (4 * Real.sqrt 7) *
      Real.arctan ((2 * t + 1) / Real.sqrt 7)

private theorem regularBranch_isOpen : IsOpen regularBranch := by
  change IsOpen {t : ℝ | t ≠ 1}
  have hset : {t : ℝ | t ≠ 1} = ({(1 : ℝ)} : Set ℝ)ᶜ := by
    ext t
    simp only [Set.mem_setOf_eq, Set.mem_compl_iff, Set.mem_singleton_iff]
  rw [hset]
  exact isOpen_compl_singleton

private theorem denominator_ne_zero (t : ℝ) (ht : t ∈ regularBranch) :
    t ^ 3 + t - 2 ≠ 0 := by
  change t ≠ 1 at ht
  have hq : 0 < t ^ 2 + t + 2 := by
    nlinarith [sq_nonneg (t + 1 / 2)]
  have hfac : t ^ 3 + t - 2 = (t - 1) * (t ^ 2 + t + 2) := by
    ring
  rw [hfac]
  exact mul_ne_zero (sub_ne_zero.mpr ht) (ne_of_gt hq)

private theorem cubeRoot_add_xOf (t : ℝ) : cubeRoot (2 + xOf t) = t := by
  have hsimp : 2 + xOf t = t ^ 3 := by
    simp [xOf]
  rw [hsimp]
  by_cases hz : t = 0
  · simp [hz, cubeRoot]
  rcases lt_or_gt_of_ne hz with hneg | hpos
  · have hcube : t ^ 3 < 0 := by
      calc
        t ^ 3 = (t * t) * t := by ring
        _ < 0 := mul_neg_of_pos_of_neg (mul_pos_of_neg_of_neg hneg hneg) hneg
    have hnt : 0 < -t := neg_pos.mpr hneg
    have habs : |t ^ 3| = (-t) ^ 3 := by
      rw [abs_of_neg hcube]
      ring
    have hr : ((-t) ^ 3 : ℝ) ^ (3 : ℝ)⁻¹ = -t := by
      simpa using Real.pow_rpow_inv_natCast (le_of_lt hnt)
        (by norm_num : (3 : ℕ) ≠ 0)
    have hexp : (1 / 3 : ℝ) = (3 : ℝ)⁻¹ := by norm_num
    unfold cubeRoot
    rw [Real.sign_of_neg hcube, habs, hexp]
    change -1 * Real.rpow ((-t) ^ 3) ((3 : ℝ)⁻¹) = t
    calc
      _ = -1 * (-t) := by
        congr 1
      _ = t := by ring
  · have hcube : 0 < t ^ 3 := by
      calc
        t ^ 3 = (t * t) * t := by ring
        _ > 0 := mul_pos (mul_pos hpos hpos) hpos
    have hr : (t ^ 3 : ℝ) ^ (3 : ℝ)⁻¹ = t := by
      simpa using Real.pow_rpow_inv_natCast (le_of_lt hpos)
        (by norm_num : (3 : ℕ) ≠ 0)
    have hexp : (1 / 3 : ℝ) = (3 : ℝ)⁻¹ := by norm_num
    unfold cubeRoot
    rw [Real.sign_of_pos hcube, abs_of_pos hcube, hexp]
    change 1 * Real.rpow (t ^ 3) ((3 : ℝ)⁻¹) = t
    calc
      _ = 1 * t := by
        congr 1
      _ = t := by ring

private theorem hasDerivAt_xOf (t : ℝ) :
    HasDerivAt xOf (3 * t ^ 2) t := by
  simpa [xOf, id] using
    (((hasDerivAt_id t).pow 3).sub (hasDerivAt_const t (2 : ℝ)))

private theorem sourceIntegrand_eq_three_transformed₁
    (t : ℝ) (ht : t ∈ regularBranch) :
    sourceIntegrand t = 3 * transformed₁ t := by
  have hden := denominator_ne_zero t ht
  have hcube := cubeRoot_add_xOf t
  have hderiv : deriv xOf t = 3 * t ^ 2 := (hasDerivAt_xOf t).deriv
  unfold sourceIntegrand transformed₁
  rw [hcube, hderiv]
  unfold xOf
  have hdenform : t ^ 3 - 2 + t = t ^ 3 + t - 2 := by
    ring
  rw [hdenform]
  field_simp [hden] <;> ring

private theorem hasDerivAt_congr_on_open
    {s : Set ℝ} {f g : ℝ → ℝ} {f' x : ℝ}
    (hs : IsOpen s) (hx : x ∈ s) (hfg : ∀ y ∈ s, f y = g y)
    (hg : HasDerivAt g f' x) : HasDerivAt f f' x := by
  apply hg.congr_of_eventuallyEq
  filter_upwards [hs.mem_nhds hx] with y hy
  exact hfg y hy

private theorem transformed_eq (t : ℝ) (ht : t ∈ regularBranch) :
    transformed₁ t = transformed₂ t := by
  have hden := denominator_ne_zero t ht
  unfold transformed₁ transformed₂
  apply (div_eq_iff hden).2
  rw [add_mul, div_mul_cancel₀ _ hden]
  ring

private def polynomialPart (t : ℝ) :=
  3 / 4 * t ^ 4 - 3 / 2 * t ^ 2

private theorem hasDerivAt_polynomialPart (t : ℝ) :
    HasDerivAt polynomialPart (3 * t ^ 3 - 3 * t) t := by
  convert ((((hasDerivAt_id t).pow 4).const_mul (3 / 4)).sub
    (((hasDerivAt_id t).pow 2).const_mul (3 / 2))) using 1 <;>
    simp [polynomialPart, id] <;> ring

private theorem partial_denominator_pos (t : ℝ) :
    0 < t ^ 2 + t + 2 := by
  nlinarith [sq_nonneg (t + 1 / 2)]

private theorem three_transformed₂_eq_polynomial_add_partial
    (t : ℝ) (ht : t ∈ regularBranch) :
    3 * transformed₂ t = (3 * t ^ 3 - 3 * t) + 3 * partialFraction t := by
  have hq : t ^ 2 + t + 2 ≠ 0 := ne_of_gt (partial_denominator_pos t)
  change t ≠ 1 at ht
  have hsub : t - 1 ≠ 0 := sub_ne_zero.mpr ht
  have hprod : (t - 1) * (t ^ 2 + t + 2) ≠ 0 := mul_ne_zero hsub hq
  have hfourSub : (4 * (t - 1) : ℝ) ≠ 0 :=
    mul_ne_zero (by norm_num) hsub
  have hfac : t ^ 3 + t - 2 = (t - 1) * (t ^ 2 + t + 2) := by
    ring
  have hr :
      (t ^ 2 - 2 * t) / (t ^ 3 + t - 2) = partialFraction t := by
    rw [hfac]
    unfold partialFraction
    have hleft :
        (-1 : ℝ) / (4 * (t - 1)) =
          (-(t ^ 2 + t + 2) / 4) /
            ((t - 1) * (t ^ 2 + t + 2)) := by
      apply (div_eq_div_iff hfourSub hprod).2
      ring
    have hright :
        ((5 / 4 : ℝ) * t - 1 / 2) / (t ^ 2 + t + 2) =
          (((5 / 4 : ℝ) * t - 1 / 2) * (t - 1)) /
            ((t - 1) * (t ^ 2 + t + 2)) := by
      apply (div_eq_div_iff hq hprod).2
      ring
    rw [hleft, hright, ← add_div]
    congr 1
    ring
  unfold transformed₂
  rw [hr]
  ring

private theorem hasDerivAt_logAbsSubOne (t : ℝ) (ht : t ∈ regularBranch) :
    HasDerivAt (fun x : ℝ => Real.log |x - 1|) (1 / (t - 1)) t := by
  change t ≠ 1 at ht
  have hsub : t - 1 ≠ 0 := sub_ne_zero.mpr ht
  rcases lt_or_gt_of_ne ht with hlt | hgt
  · have hrev : 1 - t ≠ 0 := sub_ne_zero.mpr ht.symm
    have hd0 :=
      ((hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t)).log hrev
    have hd0' : HasDerivAt (fun x : ℝ => Real.log (1 - x))
        ((0 - 1 : ℝ) / (1 - t)) t := by
      simpa [id] using hd0
    have hder : (0 - 1 : ℝ) / (1 - t) = 1 / (t - 1) := by
      field_simp [hsub, hrev]
      ring
    rw [hder] at hd0'
    apply hasDerivAt_congr_on_open isOpen_Iio hlt _ hd0'
    intro y hy
    rw [abs_of_neg (sub_neg.mpr hy)]
    congr 1
    ring
  · have hd0 :=
      ((hasDerivAt_id t).sub (hasDerivAt_const t (1 : ℝ))).log hsub
    have hd : HasDerivAt (fun x : ℝ => Real.log (x - 1))
        (1 / (t - 1)) t := by
      simpa [id] using hd0
    apply hasDerivAt_congr_on_open isOpen_Ioi hgt _ hd
    intro y hy
    rw [abs_of_pos (sub_pos.mpr hy)]

private def canonicalB (t : ℝ) :=
  2 / Real.sqrt 7 * Real.arctan ((2 * t + 1) / Real.sqrt 7)

private theorem hasDerivAt_canonicalB (t : ℝ) :
    HasDerivAt canonicalB (1 / ((t + 1 / 2) ^ 2 + 7 / 4)) t := by
  have hspos : 0 < Real.sqrt 7 := Real.sqrt_pos.2 (by norm_num)
  have hsne : Real.sqrt 7 ≠ 0 := ne_of_gt hspos
  have hsquare : (Real.sqrt 7) ^ 2 = 7 := Real.sq_sqrt (by norm_num)
  have hinner : HasDerivAt (fun x : ℝ => (2 * x + 1) / Real.sqrt 7)
      (2 / Real.sqrt 7) t := by
    simpa [id] using
      ((((hasDerivAt_id t).const_mul 2).add
        (hasDerivAt_const t (1 : ℝ))).div_const (Real.sqrt 7))
  have hd := (Real.hasDerivAt_arctan
    (x := (2 * t + 1) / Real.sqrt 7)).comp t hinner
  unfold canonicalB
  convert hd.const_mul (2 / Real.sqrt 7) using 1
  field_simp [hsne]
  nlinarith

private theorem partialFraction_decomposition
    (t : ℝ) (ht : t ∈ regularBranch) :
    partialFraction t =
      -(1 / 4 : ℝ) * (1 / (t - 1)) +
        (5 / 8 : ℝ) * ((2 * t + 1) / (t ^ 2 + t + 2)) -
        (9 / 8 : ℝ) * (1 / ((t + 1 / 2) ^ 2 + 7 / 4)) := by
  change t ≠ 1 at ht
  have hsub : t - 1 ≠ 0 := sub_ne_zero.mpr ht
  have hq : t ^ 2 + t + 2 ≠ 0 := ne_of_gt (partial_denominator_pos t)
  have hcomplete : (t + 1 / 2) ^ 2 + 7 / 4 = t ^ 2 + t + 2 := by
    ring
  rw [hcomplete]
  unfold partialFraction
  field_simp [hsub, hq]
  ring

private theorem hasDerivAt_logQuadratic (t : ℝ) :
    HasDerivAt (fun x : ℝ => Real.log (x ^ 2 + x + 2))
      ((2 * t + 1) / (t ^ 2 + t + 2)) t := by
  have hq : t ^ 2 + t + 2 ≠ 0 := ne_of_gt (partial_denominator_pos t)
  have hdq0 :=
    (((hasDerivAt_id t).pow 2).add (hasDerivAt_id t)).add_const (2 : ℝ)
  have hdq : HasDerivAt (fun x : ℝ => x ^ 2 + x + 2) (2 * t + 1) t := by
    convert hdq0 using 1 <;> simp [id] <;> ring
  exact hdq.log hq

private theorem hasDerivAt_primitive
    (t : ℝ) (ht : t ∈ regularBranch) :
    HasDerivAt primitive (sourceIntegrand t) t := by
  have hP := hasDerivAt_polynomialPart t
  have hL := hasDerivAt_logAbsSubOne t ht
  have hA := hasDerivAt_logQuadratic t
  have hB := hasDerivAt_canonicalB t
  have hdecomp := partialFraction_decomposition t ht
  have hsource₁ := sourceIntegrand_eq_three_transformed₁ t ht
  have htrans := transformed_eq t ht
  have hsource₂ := three_transformed₂_eq_polynomial_add_partial t ht
  have hd := ((hP.sub (hL.const_mul (3 / 4))).add
    (hA.const_mul (15 / 8))).sub (hB.const_mul (27 / 8))
  convert hd using 1
  · funext x
    dsimp [primitive, polynomialPart, canonicalB]
    ring
  · rw [hsource₁, htrans, hsource₂, hdecomp]
    ring

theorem gap1 (t : ℝ) :
    xOf t = t ^ 3 - 2 := by
  rfl
theorem gap2 (t : ℝ) :
    HasDerivAt xOf (3 * t ^ 2) t := by
  simpa [xOf, id] using
    (((hasDerivAt_id t).pow 3).sub (hasDerivAt_const t (2 : ℝ)))
theorem gap3 :
    AntiderivativesOn regularBranch sourceIntegrand =
      ScaledFamily transformed₁ := by
  ext F
  constructor
  · intro hF
    change (∀ t ∈ regularBranch, HasDerivAt F (sourceIntegrand t) t) at hF
    change ∃ G ∈ AntiderivativesOn regularBranch transformed₁,
      ∀ t ∈ regularBranch, F t = 3 * G t
    refine ⟨fun t => F t / 3, ?_, ?_⟩
    · intro t ht
      have hd := (hF t ht).div_const 3
      rw [sourceIntegrand_eq_three_transformed₁ t ht] at hd
      simpa using hd
    · intro t ht
      ring
  · rintro ⟨G, hG, hFG⟩
    change ∀ t ∈ regularBranch, HasDerivAt F (sourceIntegrand t) t
    intro t ht
    have hd : HasDerivAt (fun x => 3 * G x) (sourceIntegrand t) t := by
      rw [sourceIntegrand_eq_three_transformed₁ t ht]
      simpa using (hG t ht).const_mul 3
    exact hasDerivAt_congr_on_open regularBranch_isOpen ht hFG hd
theorem gap4 :
    ScaledFamily transformed₁ = ScaledFamily transformed₂ := by
  ext F
  constructor
  · rintro ⟨G, hG, hFG⟩
    refine ⟨G, ?_, hFG⟩
    intro t ht
    rw [← transformed_eq t ht]
    exact hG t ht
  · rintro ⟨G, hG, hFG⟩
    refine ⟨G, ?_, hFG⟩
    intro t ht
    rw [transformed_eq t ht]
    exact hG t ht
theorem gap5 :
    AntiderivativesOn regularBranch sourceIntegrand =
      ScaledFamily transformed₂ := by
  rw [gap3, gap4]
theorem gap6 :
    AntiderivativesOn regularBranch sourceIntegrand =
      PartialFractionFamily := by
  rw [gap5]
  ext F
  constructor
  · rintro ⟨G, hG, hFG⟩
    let H : ℝ → ℝ := fun t => G t - polynomialPart t / 3
    refine ⟨H, ?_, ?_⟩
    · intro t ht
      have hd := (hG t ht).sub ((hasDerivAt_polynomialPart t).div_const 3)
      have hi := three_transformed₂_eq_polynomial_add_partial t ht
      have heq :
          transformed₂ t - (3 * t ^ 3 - 3 * t) / 3 = partialFraction t := by
        linarith
      rw [heq] at hd
      simpa only [H] using hd
    · intro t ht
      rw [hFG t ht]
      dsimp [H, polynomialPart]
      ring
  · rintro ⟨H, hH, hFH⟩
    let G : ℝ → ℝ := fun t => polynomialPart t / 3 + H t
    refine ⟨G, ?_, ?_⟩
    · intro t ht
      have hd := ((hasDerivAt_polynomialPart t).div_const 3).add (hH t ht)
      have hi := three_transformed₂_eq_polynomial_add_partial t ht
      have heq :
          (3 * t ^ 3 - 3 * t) / 3 + partialFraction t = transformed₂ t := by
        linarith
      rw [heq] at hd
      simpa only [G] using hd
    · intro t ht
      rw [hFH t ht]
      dsimp [G, polynomialPart]
      ring
theorem gap7 :
    AntiderivativesOn regularBranch sourceIntegrand = AuxiliaryFamily := by
  rw [gap6]
  ext F
  constructor
  · rintro ⟨H, hH, hFH⟩
    let B : ℝ → ℝ := canonicalB
    let A : ℝ → ℝ := fun t =>
      (8 / 5 : ℝ) * (H t + (1 / 4 : ℝ) * Real.log |t - 1| +
        (9 / 8 : ℝ) * B t)
    refine ⟨A, ?_, B, ?_, ?_⟩
    · intro t ht
      have hdL := hasDerivAt_logAbsSubOne t ht
      have hdB := hasDerivAt_canonicalB t
      have hd := ((hH t ht).add (hdL.const_mul (1 / 4))).add
        (hdB.const_mul (9 / 8))
      have ha := partialFraction_decomposition t ht
      have hcomplete :
          (t + 1 / 2) ^ 2 + 7 / 4 = t ^ 2 + t + 2 := by
        ring
      have hcoef :
          (8 / 5 : ℝ) *
              (partialFraction t + (1 / 4) * (1 / (t - 1)) +
                (9 / 8) * (1 / ((t + 1 / 2) ^ 2 + 7 / 4))) =
            (2 * t + 1) / (t ^ 2 + t + 2) := by
        rw [ha, hcomplete]
        ring
      have hd' := hd.const_mul (8 / 5)
      rw [hcoef] at hd'
      simpa only [A, B] using hd'
    · intro t _
      simpa [B] using hasDerivAt_canonicalB t
    · intro t ht
      rw [hFH t ht]
      simp only [A, B]
      ring
  · rintro ⟨A, hA, B, hB, hFAB⟩
    let H : ℝ → ℝ := fun t =>
      (5 / 8 : ℝ) * A t - (9 / 8 : ℝ) * B t -
        (1 / 4 : ℝ) * Real.log |t - 1|
    refine ⟨H, ?_, ?_⟩
    · intro t ht
      have hd := (((hA t ht).const_mul (5 / 8)).sub
        ((hB t ht).const_mul (9 / 8))).sub
        ((hasDerivAt_logAbsSubOne t ht).const_mul (1 / 4))
      have hcoef :
          (5 / 8 : ℝ) * ((2 * t + 1) / (t ^ 2 + t + 2)) -
              (9 / 8 : ℝ) * (1 / ((t + 1 / 2) ^ 2 + 7 / 4)) -
              (1 / 4 : ℝ) * (1 / (t - 1)) = partialFraction t := by
        rw [partialFraction_decomposition t ht]
        ring
      rw [hcoef] at hd
      simpa only [H, Pi.sub_apply] using hd
    · intro t ht
      rw [hFAB t ht]
      simp only [H]
      ring
theorem gap8 :
    AntiderivativesOn regularBranch sourceIntegrand =
      BranchwisePrimitiveFamilyOn regularBranch primitive := by
  ext F
  constructor
  · intro hF
    change ∀ u : Set ℝ, IsOpen u → IsPreconnected u → u ⊆ regularBranch →
      ∃ C : ℝ, ∀ t ∈ u, F t = primitive t + C
    intro u huOpen huConn hus
    by_cases hu : u.Nonempty
    · rcases hu with ⟨t₀, ht₀⟩
      let D : ℝ → ℝ := fun t => F t - primitive t
      have hD : ∀ t ∈ u, HasDerivAt D 0 t := by
        intro t ht
        have htreg := hus ht
        have hd := (hF t htreg).sub (hasDerivAt_primitive t htreg)
        simpa [D] using hd
      have hDdiff : DifferentiableOn ℝ D u := by
        intro t ht
        exact (hD t ht).differentiableAt.differentiableWithinAt
      have hDderiv : ∀ t ∈ u, deriv D t = 0 := by
        intro t ht
        exact (hD t ht).deriv
      refine ⟨D t₀, ?_⟩
      intro t ht
      have hEq : D t = D t₀ :=
        huOpen.is_const_of_deriv_eq_zero huConn hDdiff hDderiv ht ht₀
      dsimp [D] at hEq ⊢
      linarith
    · refine ⟨0, ?_⟩
      intro t ht
      exact False.elim (hu ⟨t, ht⟩)
  · intro hF
    change ∀ t ∈ regularBranch, HasDerivAt F (sourceIntegrand t) t
    intro t ht
    change t ≠ 1 at ht
    rcases lt_or_gt_of_ne ht with hlt | hgt
    · have hsub : Set.Iio (1 : ℝ) ⊆ regularBranch := by
        intro x hx
        change x ≠ 1
        exact ne_of_lt hx
      rcases hF (Set.Iio (1 : ℝ)) isOpen_Iio isPreconnected_Iio hsub with ⟨C, hC⟩
      have hd : HasDerivAt (fun x => primitive x + C) (sourceIntegrand t) t :=
        (hasDerivAt_primitive t (hsub hlt)).add_const C
      exact hasDerivAt_congr_on_open isOpen_Iio hlt hC hd
    · have hsub : Set.Ioi (1 : ℝ) ⊆ regularBranch := by
        intro x hx
        change x ≠ 1
        exact ne_of_gt hx
      rcases hF (Set.Ioi (1 : ℝ)) isOpen_Ioi isPreconnected_Ioi hsub with ⟨C, hC⟩
      have hd : HasDerivAt (fun x => primitive x + C) (sourceIntegrand t) t :=
        (hasDerivAt_primitive t (hsub hgt)).add_const C
      exact hasDerivAt_congr_on_open isOpen_Ioi hgt hC hd
theorem gap9 (t : ℝ) :
    t = cubeRoot (2 + xOf t) := by
  exact (cubeRoot_add_xOf t).symm

end
end ProofGap.Exercise1928
