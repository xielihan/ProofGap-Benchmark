import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Topology.Defs.Filter
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise2114
noncomputable section

def domain : Set ℝ := Set.Ioo (-1) 1
def logRatio (x : ℝ) := Real.log ((1 + x) / (1 - x))
def integrand (x : ℝ) := x * logRatio x
def squareDifferential (x : ℝ) :=
  logRatio x * deriv (fun y : ℝ => y ^ 2) x
def rational (x : ℝ) := x ^ 2 / (1 - x ^ 2)
def splitRational (x : ℝ) := 1 - 1 / (1 - x ^ 2)
def primitive (x : ℝ) := (x ^ 2 - 1) / 2 * logRatio x + x

def Family (f : ℝ → ℝ) :=
  {F : ℝ → ℝ | ∀ x ∈ domain, HasDerivAt F (f x) x}
def HalfFamily (f : ℝ → ℝ) :=
  {F : ℝ → ℝ | ∃ A ∈ Family f, ∀ x ∈ domain, F x = (1 / 2 : ℝ) * A x}
def ByPartsFamily (f : ℝ → ℝ) :=
  {F : ℝ → ℝ | ∃ A ∈ Family f, ∀ x ∈ domain,
    F x = (1 / 2 : ℝ) * x ^ 2 * logRatio x - A x}
def SplitFamily :=
  {F : ℝ → ℝ | ∃ A ∈ Family splitRational, ∀ x ∈ domain,
    F x = (1 / 2 : ℝ) * x ^ 2 * logRatio x + A x}
def Translates (p : ℝ → ℝ) :=
  {F : ℝ → ℝ | ∃ C : ℝ, ∀ x ∈ domain, F x = p x + C}

private theorem hasDerivAt_congr_on_domain
    {f g : ℝ → ℝ} {f' x : ℝ} (hx : x ∈ domain)
    (hfg : ∀ y ∈ domain, f y = g y) (hg : HasDerivAt g f' x) :
    HasDerivAt f f' x := by
  apply hg.congr_of_eventuallyEq
  filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
  exact hfg y hy

private theorem domain_den_pos (x : ℝ) (hx : x ∈ domain) :
    0 < 1 - x ^ 2 := by
  change -1 < x ∧ x < 1 at hx
  have hp : 0 < 1 + x := by linarith
  have hm : 0 < 1 - x := by linarith
  have hmul : 0 < (1 + x) * (1 - x) := mul_pos hp hm
  nlinarith

private theorem hasDerivAt_logRatio (x : ℝ) (hx : x ∈ domain) :
    HasDerivAt logRatio (2 / (1 - x ^ 2)) x := by
  have hp : 0 < 1 + x := by
    change -1 < x ∧ x < 1 at hx
    linarith
  have hm : 0 < 1 - x := by
    change -1 < x ∧ x < 1 at hx
    linarith
  have hq : 0 < (1 + x) / (1 - x) := div_pos hp hm
  have hnum : HasDerivAt (fun y : ℝ => 1 + y) 1 x := by
    simpa using (hasDerivAt_const x (1 : ℝ)).add (hasDerivAt_id x)
  have hden : HasDerivAt (fun y : ℝ => 1 - y) (-1) x := by
    simpa using (hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id x)
  have hratio := hnum.div hden (ne_of_gt hm)
  have hquad : 1 - x ^ 2 ≠ 0 := ne_of_gt (domain_den_pos x hx)
  unfold logRatio
  convert (Real.hasDerivAt_log (ne_of_gt hq)).comp x hratio using 1
  · field_simp [ne_of_gt hp, ne_of_gt hm, hquad]
    <;> ring

private theorem squareDifferential_eq (x : ℝ) :
    squareDifferential x = 2 * integrand x := by
  have hs : HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by
    convert (hasDerivAt_id x).pow 2 using 1 <;> simp [id] <;> ring
  have hd : deriv (fun y : ℝ => y ^ 2) x = 2 * x := hs.deriv
  unfold squareDifferential integrand
  rw [hd]
  ring

private theorem hasDerivAt_partsTerm (x : ℝ) (hx : x ∈ domain) :
    HasDerivAt (fun y : ℝ => (1 / 2 : ℝ) * y ^ 2 * logRatio y)
      (integrand x + rational x) x := by
  have hs : HasDerivAt (fun y : ℝ => (1 / 2 : ℝ) * y ^ 2) x x := by
    convert ((hasDerivAt_id x).pow 2).const_mul (1 / 2 : ℝ) using 1
      <;> simp [id] <;> ring
  have hden : 1 - x ^ 2 ≠ 0 := ne_of_gt (domain_den_pos x hx)
  convert hs.mul (hasDerivAt_logRatio x hx) using 1
  · unfold integrand rational
    field_simp [hden]
    <;> ring

private theorem family_eq_byParts :
    Family integrand = ByPartsFamily rational := by
  ext F
  simp only [Family, ByPartsFamily, Set.mem_setOf_eq]
  constructor
  · intro hF
    refine ⟨fun y => (1 / 2 : ℝ) * y ^ 2 * logRatio y - F y, ?_, ?_⟩
    · intro x hx
      convert (hasDerivAt_partsTerm x hx).sub (hF x hx) using 1 <;> ring
    · intro x hx
      ring
  · rintro ⟨A, hA, hFA⟩
    intro x hx
    have hpart :
        HasDerivAt
          (fun y => (1 / 2 : ℝ) * y ^ 2 * logRatio y - A y)
          (integrand x) x := by
      convert (hasDerivAt_partsTerm x hx).sub (hA x hx) using 1 <;> ring
    exact hasDerivAt_congr_on_domain hx hFA hpart

private theorem splitRational_eq_neg (x : ℝ) (hx : x ∈ domain) :
    splitRational x = -rational x := by
  have hden : 1 - x ^ 2 ≠ 0 := ne_of_gt (domain_den_pos x hx)
  unfold splitRational rational
  field_simp [hden]
  <;> ring

private theorem byParts_eq_split :
    ByPartsFamily rational = SplitFamily := by
  ext F
  simp only [ByPartsFamily, SplitFamily, Family, Set.mem_setOf_eq]
  constructor
  · rintro ⟨A, hA, hFA⟩
    refine ⟨fun y => -A y, ?_, ?_⟩
    · intro x hx
      simpa only [splitRational_eq_neg x hx] using (hA x hx).neg
    · intro x hx
      simpa only [sub_eq_add_neg] using hFA x hx
  · rintro ⟨A, hA, hFA⟩
    refine ⟨fun y => -A y, ?_, ?_⟩
    · intro x hx
      simpa only [splitRational_eq_neg x hx, neg_neg] using (hA x hx).neg
    · intro x hx
      simpa only [sub_neg_eq_add] using hFA x hx

private theorem hasDerivAt_primitive (x : ℝ) (hx : x ∈ domain) :
    HasDerivAt primitive (integrand x) x := by
  have hc : HasDerivAt (fun y : ℝ => (y ^ 2 - 1) / 2) x x := by
    convert (((hasDerivAt_id x).pow 2).sub
      (hasDerivAt_const x (1 : ℝ))).const_mul (1 / 2 : ℝ) using 1
    · funext y
      simp [id] <;> ring
    · simp [id]
  have hden : 1 - x ^ 2 ≠ 0 := ne_of_gt (domain_den_pos x hx)
  unfold primitive
  convert (hc.mul (hasDerivAt_logRatio x hx)).add (hasDerivAt_id x) using 1
  · unfold integrand
    field_simp [hden]
    <;> ring

private theorem family_eq_translates :
    Family integrand = Translates primitive := by
  ext F
  simp only [Family, Translates, Set.mem_setOf_eq]
  constructor
  · intro hF
    let g : ℝ → ℝ := fun y => F y - primitive y
    have hg : ∀ x ∈ domain, HasDerivAt g 0 x := by
      intro x hx
      dsimp [g]
      convert (hF x hx).sub (hasDerivAt_primitive x hx) using 1 <;> ring
    have hdiff : DifferentiableOn ℝ g domain := by
      intro x hx
      exact (hg x hx).differentiableAt.differentiableWithinAt
    have hzero : ∀ x ∈ domain, deriv g x = 0 := by
      intro x hx
      exact (hg x hx).deriv
    have h0 : (0 : ℝ) ∈ domain := by
      change -1 < (0 : ℝ) ∧ (0 : ℝ) < 1
      constructor <;> linarith
    refine ⟨g 0, ?_⟩
    intro x hx
    have hconst : g x = g 0 :=
      isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo
        hdiff hzero hx h0
    dsimp [g] at hconst ⊢
    linarith
  · rintro ⟨C, hFC⟩
    intro x hx
    have hsum := (hasDerivAt_primitive x hx).add (hasDerivAt_const x C)
    have heq : F =ᶠ[nhds x] (primitive + fun _ => C) := by
      filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
      exact hFC y hy
    simpa only [add_zero] using hsum.congr_of_eventuallyEq heq

theorem gap1 : Family integrand = HalfFamily squareDifferential := by
  ext F
  simp only [Family, HalfFamily, Set.mem_setOf_eq]
  constructor
  · intro hF
    refine ⟨fun y => 2 * F y, ?_, ?_⟩
    · intro x hx
      simpa only [squareDifferential_eq] using (hF x hx).const_mul 2
    · intro x hx
      ring
  · rintro ⟨A, hA, hFA⟩
    intro x hx
    have heq : (1 / 2 : ℝ) * squareDifferential x = integrand x := by
      rw [squareDifferential_eq]
      ring
    have hhalf :
        HasDerivAt (fun y => (1 / 2 : ℝ) * A y) (integrand x) x := by
      simpa only [heq] using (hA x hx).const_mul (1 / 2 : ℝ)
    exact hasDerivAt_congr_on_domain hx hFA hhalf
theorem gap2 : HalfFamily squareDifferential = ByPartsFamily rational := by
  exact gap1.symm.trans family_eq_byParts
theorem gap3 : Family integrand = ByPartsFamily rational := by
  exact gap1.trans gap2
theorem gap4 : Family integrand = SplitFamily := by
  exact gap3.trans byParts_eq_split
theorem gap5 : SplitFamily = Translates primitive := by
  exact gap4.symm.trans family_eq_translates
theorem gap6 : Family integrand = Translates primitive := by
  exact gap4.trans gap5

end
end ProofGap.Exercise2114
