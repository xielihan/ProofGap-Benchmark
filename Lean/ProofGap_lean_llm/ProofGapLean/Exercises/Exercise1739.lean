import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Topology.Neighborhoods
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise1739

noncomputable section

def domain (a b : ℝ) : Set ℝ := Set.Ioi (max (-a) (-b))
def original (a b x : ℝ) : ℝ := 1 / ((x + a) ^ 2 * (x + b) ^ 2)
def squareForm (a b x : ℝ) : ℝ :=
  (1 / (a - b) ^ 2) * (1 / (x + a) - 1 / (x + b)) ^ 2
def expanded (a b x : ℝ) : ℝ :=
  (1 / (a - b) ^ 2) *
    (1 / (x + a) ^ 2 + 1 / (x + b) ^ 2 -
      2 / ((x + a) * (x + b)))
def basePrimitive (a b x : ℝ) : ℝ :=
  -(1 / (a - b)) * Real.log |(x + a) / (x + b)|
def mixedPrimitive (a b x : ℝ) : ℝ :=
  -(1 / (a - b) ^ 2) * (1 / (x + a) + 1 / (x + b)) -
    (2 / (a - b) ^ 2) * basePrimitive a b x
def primitive (a b x : ℝ) : ℝ :=
  -(2 * x + a + b) / ((a - b) ^ 2 * (x + a) * (x + b)) +
    (2 / (a - b) ^ 3) * Real.log |(x + a) / (x + b)|
def AntiderivativesOn (a b : ℝ) (g : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | DifferentiableOn ℝ F (domain a b) ∧
    ∀ x ∈ domain a b, deriv F x = g x}
def PrimitiveFamily (a b : ℝ) (p : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x ∈ domain a b, F x = p x + C}

private lemma domain_positive (a b x : ℝ) (hx : x ∈ domain a b) :
    0 < x + a ∧ 0 < x + b := by
  change max (-a) (-b) < x at hx
  constructor
  · have h := le_max_left (-a) (-b)
    linarith
  · have h := le_max_right (-a) (-b)
    linarith

private lemma integrand_square_identity (a b : ℝ) (hab : a ≠ b)
    (x : ℝ) (hx : x ∈ domain a b) :
    original a b x = squareForm a b x := by
  obtain ⟨hxa, hxb⟩ := domain_positive a b x hx
  have ha : x + a ≠ 0 := ne_of_gt hxa
  have hb : x + b ≠ 0 := ne_of_gt hxb
  have hd : a - b ≠ 0 := sub_ne_zero.mpr hab
  unfold original squareForm
  field_simp [ha, hb, hd]
  ring

private lemma integrand_expanded_identity (a b : ℝ) (hab : a ≠ b)
    (x : ℝ) (hx : x ∈ domain a b) :
    original a b x = expanded a b x := by
  obtain ⟨hxa, hxb⟩ := domain_positive a b x hx
  have ha : x + a ≠ 0 := ne_of_gt hxa
  have hb : x + b ≠ 0 := ne_of_gt hxb
  have hd : a - b ≠ 0 := sub_ne_zero.mpr hab
  unfold original expanded
  field_simp [ha, hb, hd]
  ring

private lemma hasDerivAt_log_abs_ratio (a b x : ℝ)
    (hxa : 0 < x + a) (hxb : 0 < x + b) :
    HasDerivAt (fun t : ℝ => Real.log |(t + a) / (t + b)|)
      (1 / (x + a) - 1 / (x + b)) x := by
  have ha : x + a ≠ 0 := ne_of_gt hxa
  have hb : x + b ≠ 0 := ne_of_gt hxb
  have hA : HasDerivAt (fun t : ℝ => t + a) 1 x :=
    (hasDerivAt_id x).add_const a
  have hB : HasDerivAt (fun t : ℝ => t + b) 1 x :=
    (hasDerivAt_id x).add_const b
  have hratio : HasDerivAt (fun t : ℝ => (t + a) / (t + b))
      ((1 * (x + b) - (x + a) * 1) / (x + b) ^ 2) x :=
    hA.div hB hb
  have hlog :=
    (Real.hasDerivAt_log (div_ne_zero ha hb)).comp x hratio
  convert hlog using 1
  · funext t
    simp only [Real.log_abs, Function.comp_apply]
  · field_simp [ha, hb]

private lemma hasDerivAt_mixedPrimitive (a b : ℝ) (hab : a ≠ b)
    (x : ℝ) (hx : x ∈ domain a b) :
    HasDerivAt (mixedPrimitive a b) (original a b x) x := by
  obtain ⟨hxa, hxb⟩ := domain_positive a b x hx
  have ha : x + a ≠ 0 := ne_of_gt hxa
  have hb : x + b ≠ 0 := ne_of_gt hxb
  have hd : a - b ≠ 0 := sub_ne_zero.mpr hab
  have hA : HasDerivAt (fun t : ℝ => t + a) 1 x :=
    (hasDerivAt_id x).add_const a
  have hB : HasDerivAt (fun t : ℝ => t + b) 1 x :=
    (hasDerivAt_id x).add_const b
  have hrecA : HasDerivAt (fun t : ℝ => 1 / (t + a))
      (-1 / (x + a) ^ 2) x := by
    simpa [one_div, add_comm] using hA.inv ha
  have hrecB : HasDerivAt (fun t : ℝ => 1 / (t + b))
      (-1 / (x + b) ^ 2) x := by
    simpa [one_div, add_comm] using hB.inv hb
  have hlog := hasDerivAt_log_abs_ratio a b x hxa hxb
  have hbase : HasDerivAt (basePrimitive a b)
      (1 / ((x + a) * (x + b))) x := by
    unfold basePrimitive
    convert hlog.const_mul (-(1 / (a - b))) using 1
    field_simp [hd, ha, hb]
    ring
  unfold mixedPrimitive original
  convert ((hrecA.add hrecB).const_mul (-(1 / (a - b) ^ 2))).sub
      (hbase.const_mul (2 / (a - b) ^ 2)) using 1 <;>
    field_simp [hd, ha, hb] <;> ring

private theorem antiderivatives_eq_family_of_hasDerivAt
    (a b : ℝ) (g p : ℝ → ℝ)
    (hp : ∀ x ∈ domain a b, HasDerivAt p (g x) x) :
    AntiderivativesOn a b g = PrimitiveFamily a b p := by
  ext F
  simp only [AntiderivativesOn, PrimitiveFamily, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hF, hder⟩
    let q : ℝ → ℝ := fun x => F x - p x
    have hopen : IsOpen (domain a b) := isOpen_Ioi
    have hconvex : Convex ℝ (domain a b) := convex_Ioi _
    have hpreconnected : IsPreconnected (domain a b) :=
      hconvex.isPreconnected
    have hqdiff : DifferentiableOn ℝ q (domain a b) := by
      intro x hx
      exact (hF x hx).sub (hp x hx).differentiableAt.differentiableWithinAt
    have hqderiv : ∀ x ∈ domain a b, deriv q x = 0 := by
      intro x hx
      have hFa : DifferentiableAt ℝ F x :=
        (hF x hx).differentiableAt (hopen.mem_nhds hx)
      have hqhas : HasDerivAt q (deriv F x - g x) x := by
        exact hFa.hasDerivAt.sub (hp x hx)
      calc
        deriv q x = deriv F x - g x := hqhas.deriv
        _ = 0 := by rw [hder x hx]; ring
    have hpair : ∀ u ∈ domain a b, ∀ v ∈ domain a b, q u = q v := by
      intro u hu v hv
      exact hopen.is_const_of_deriv_eq_zero hpreconnected hqdiff hqderiv hu hv
    let x₀ : ℝ := max (-a) (-b) + 1
    have hx₀ : x₀ ∈ domain a b := by
      change max (-a) (-b) < x₀
      dsimp [x₀]
      linarith
    refine ⟨F x₀ - p x₀, fun x hx => ?_⟩
    have heq := hpair x hx x₀ hx₀
    dsimp [q] at heq
    linarith
  · rintro ⟨C, hC⟩
    have hopen : IsOpen (domain a b) := isOpen_Ioi
    have hlocal : ∀ x ∈ domain a b, HasDerivAt F (g x) x := by
      intro x hx
      have hev : F =ᶠ[nhds x] (fun y => p y + C) := by
        filter_upwards [hopen.mem_nhds hx] with y hy
        exact hC y hy
      exact ((hp x hx).add_const C).congr_of_eventuallyEq hev
    refine ⟨?_, ?_⟩
    · intro x hx
      exact (hlocal x hx).differentiableAt.differentiableWithinAt
    · intro x hx
      exact (hlocal x hx).deriv

private lemma mixed_primitive_identity (a b : ℝ) (hab : a ≠ b)
    (x : ℝ) (hx : x ∈ domain a b) :
    mixedPrimitive a b x = primitive a b x := by
  obtain ⟨hxa, hxb⟩ := domain_positive a b x hx
  have ha : x + a ≠ 0 := ne_of_gt hxa
  have hb : x + b ≠ 0 := ne_of_gt hxb
  have hd : a - b ≠ 0 := sub_ne_zero.mpr hab
  unfold mixedPrimitive primitive basePrimitive
  field_simp [ha, hb, hd]
  ring

theorem gap1 (a b : ℝ) (hab : a ≠ b) :
    AntiderivativesOn a b (original a b) =
      AntiderivativesOn a b (squareForm a b) := by
  ext F
  simp only [AntiderivativesOn, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hF, hder⟩
    refine ⟨hF, fun x hx => ?_⟩
    calc
      deriv F x = original a b x := hder x hx
      _ = squareForm a b x := integrand_square_identity a b hab x hx
  · rintro ⟨hF, hder⟩
    refine ⟨hF, fun x hx => ?_⟩
    calc
      deriv F x = squareForm a b x := hder x hx
      _ = original a b x := (integrand_square_identity a b hab x hx).symm

theorem gap2 (a b : ℝ) (hab : a ≠ b) :
    AntiderivativesOn a b (original a b) =
      AntiderivativesOn a b (expanded a b) := by
  ext F
  simp only [AntiderivativesOn, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hF, hder⟩
    refine ⟨hF, fun x hx => ?_⟩
    calc
      deriv F x = original a b x := hder x hx
      _ = expanded a b x := integrand_expanded_identity a b hab x hx
  · rintro ⟨hF, hder⟩
    refine ⟨hF, fun x hx => ?_⟩
    calc
      deriv F x = expanded a b x := hder x hx
      _ = original a b x := (integrand_expanded_identity a b hab x hx).symm

theorem gap3 (a b : ℝ) (hab : a ≠ b) :
    AntiderivativesOn a b (original a b) =
      PrimitiveFamily a b (mixedPrimitive a b) := by
  apply antiderivatives_eq_family_of_hasDerivAt
  intro x hx
  exact hasDerivAt_mixedPrimitive a b hab x hx

theorem gap4 (a b : ℝ) (hab : a ≠ b) :
    AntiderivativesOn a b (original a b) =
      PrimitiveFamily a b (primitive a b) := by
  rw [gap3 a b hab]
  ext F
  simp only [PrimitiveFamily, Set.mem_setOf_eq]
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨C, fun x hx => ?_⟩
    calc
      F x = mixedPrimitive a b x + C := hC x hx
      _ = primitive a b x + C := by
        rw [mixed_primitive_identity a b hab x hx]
  · rintro ⟨C, hC⟩
    refine ⟨C, fun x hx => ?_⟩
    calc
      F x = primitive a b x + C := hC x hx
      _ = mixedPrimitive a b x + C := by
        rw [mixed_primitive_identity a b hab x hx]

end
end ProofGap.Exercise1739
