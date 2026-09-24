import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Neighborhoods
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise1635

noncomputable section

def domain : Set ℝ := Set.Ioi 0
def original (x : ℝ) : ℝ := (1 - x) ^ 3 / (x * Real.cbrt x)
def powers (x : ℝ) : ℝ :=
  Real.rpow x (-(4 / 3)) - 3 * Real.rpow x (-(1 / 3)) +
    3 * Real.rpow x (2 / 3) - Real.rpow x (5 / 3)
def primitive (x : ℝ) : ℝ :=
  -(3 / Real.cbrt x) *
    (1 + (3 / 2) * x - (3 / 5) * x ^ 2 + (1 / 8) * x ^ 3)
def AntiderivativesOn (g : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | DifferentiableOn ℝ F domain ∧ ∀ x ∈ domain, deriv F x = g x}
def PrimitiveFamily (p : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x ∈ domain, F x = p x + C}

private lemma original_eq_powers (x : ℝ) (hx : x ∈ domain) :
    original x = powers x := by
  change 0 < x at hx
  let r : ℝ := Real.rpow x (1 / 3)
  have hrpos : 0 < r := Real.rpow_pos_of_pos hx (1 / 3)
  have hr0 : r ≠ 0 := ne_of_gt hrpos
  have hroot : Real.cbrt x = r := by
    dsimp [r]
    simp [Real.cbrt]
  have hone : Real.rpow x 1 = x := by
    simp
  have hneg13 : Real.rpow x (-(1 / 3)) = r⁻¹ := by
    dsimp [r]
    change x ^ (-(1 / 3 : ℝ)) = (x ^ (1 / 3 : ℝ))⁻¹
    exact Real.rpow_neg hx.le (1 / 3)
  have h23 : Real.rpow x (2 / 3) = r * r := by
    calc
      Real.rpow x (2 / 3) = Real.rpow x (1 / 3 + 1 / 3) := by
        congr 1 <;> ring
      _ = Real.rpow x (1 / 3) * Real.rpow x (1 / 3) := by
        change x ^ ((1 / 3 : ℝ) + 1 / 3) =
          x ^ (1 / 3 : ℝ) * x ^ (1 / 3 : ℝ)
        exact Real.rpow_add hx (1 / 3) (1 / 3)
      _ = r * r := by rfl
  have hr3 : r ^ 3 = x := by
    calc
      r ^ 3 = r * (r * r) := by ring
      _ = Real.rpow x (1 / 3) * Real.rpow x (2 / 3) := by rw [h23]
      _ = Real.rpow x (1 / 3 + 2 / 3) := by
        symm
        change x ^ ((1 / 3 : ℝ) + 2 / 3) =
          x ^ (1 / 3 : ℝ) * x ^ (2 / 3 : ℝ)
        exact Real.rpow_add hx (1 / 3) (2 / 3)
      _ = Real.rpow x 1 := by congr 1 <;> ring
      _ = x := hone
  have h53 : Real.rpow x (5 / 3) = x * (r * r) := by
    calc
      Real.rpow x (5 / 3) = Real.rpow x (1 + 2 / 3) := by
        congr 1 <;> ring
      _ = Real.rpow x 1 * Real.rpow x (2 / 3) := by
        change x ^ ((1 : ℝ) + 2 / 3) = x ^ (1 : ℝ) * x ^ (2 / 3 : ℝ)
        exact Real.rpow_add hx 1 (2 / 3)
      _ = x * (r * r) := by rw [hone, h23]
  have h43 : Real.rpow x (4 / 3) = x * r := by
    calc
      Real.rpow x (4 / 3) = Real.rpow x (1 + 1 / 3) := by
        congr 1 <;> ring
      _ = Real.rpow x 1 * Real.rpow x (1 / 3) := by
        change x ^ ((1 : ℝ) + 1 / 3) = x ^ (1 : ℝ) * x ^ (1 / 3 : ℝ)
        exact Real.rpow_add hx 1 (1 / 3)
      _ = x * r := by rw [hone]
  have hneg43 : Real.rpow x (-(4 / 3)) = (x * r)⁻¹ := by
    change x ^ (-(4 / 3 : ℝ)) = (x * r)⁻¹
    rw [Real.rpow_neg hx.le (4 / 3)]
    exact congrArg Inv.inv h43
  unfold original powers
  rw [hroot, hneg43, hneg13, h23, h53]
  rw [← hr3]
  field_simp [hr0]
  ring

private def expandedPrimitive (x : ℝ) : ℝ :=
  -3 * Real.rpow x (-(1 / 3)) -
    (9 / 2) * Real.rpow x (2 / 3) +
    (9 / 5) * Real.rpow x (5 / 3) -
    (3 / 8) * Real.rpow x (8 / 3)

private lemma primitive_eq_expanded (x : ℝ) (hx : x ∈ domain) :
    primitive x = expandedPrimitive x := by
  change 0 < x at hx
  let r : ℝ := Real.rpow x (1 / 3)
  have hrpos : 0 < r := Real.rpow_pos_of_pos hx (1 / 3)
  have hr0 : r ≠ 0 := ne_of_gt hrpos
  have hroot : Real.cbrt x = r := by
    dsimp [r]
    simp [Real.cbrt]
  have hone : Real.rpow x 1 = x := by
    simp
  have hneg13 : Real.rpow x (-(1 / 3)) = r⁻¹ := by
    dsimp [r]
    change x ^ (-(1 / 3 : ℝ)) = (x ^ (1 / 3 : ℝ))⁻¹
    exact Real.rpow_neg hx.le (1 / 3)
  have h23 : Real.rpow x (2 / 3) = r * r := by
    calc
      Real.rpow x (2 / 3) = Real.rpow x (1 / 3 + 1 / 3) := by
        congr 1 <;> ring
      _ = Real.rpow x (1 / 3) * Real.rpow x (1 / 3) := by
        change x ^ ((1 / 3 : ℝ) + 1 / 3) =
          x ^ (1 / 3 : ℝ) * x ^ (1 / 3 : ℝ)
        exact Real.rpow_add hx (1 / 3) (1 / 3)
      _ = r * r := by rfl
  have hr3 : r ^ 3 = x := by
    calc
      r ^ 3 = r * (r * r) := by ring
      _ = Real.rpow x (1 / 3) * Real.rpow x (2 / 3) := by rw [h23]
      _ = Real.rpow x (1 / 3 + 2 / 3) := by
        symm
        change x ^ ((1 / 3 : ℝ) + 2 / 3) =
          x ^ (1 / 3 : ℝ) * x ^ (2 / 3 : ℝ)
        exact Real.rpow_add hx (1 / 3) (2 / 3)
      _ = Real.rpow x 1 := by congr 1 <;> ring
      _ = x := hone
  have h53 : Real.rpow x (5 / 3) = x * (r * r) := by
    calc
      Real.rpow x (5 / 3) = Real.rpow x (1 + 2 / 3) := by
        congr 1 <;> ring
      _ = Real.rpow x 1 * Real.rpow x (2 / 3) := by
        change x ^ ((1 : ℝ) + 2 / 3) = x ^ (1 : ℝ) * x ^ (2 / 3 : ℝ)
        exact Real.rpow_add hx 1 (2 / 3)
      _ = x * (r * r) := by rw [hone, h23]
  have h83 : Real.rpow x (8 / 3) = x * (x * (r * r)) := by
    calc
      Real.rpow x (8 / 3) = Real.rpow x (1 + 5 / 3) := by
        congr 1 <;> ring
      _ = Real.rpow x 1 * Real.rpow x (5 / 3) := by
        change x ^ ((1 : ℝ) + 5 / 3) = x ^ (1 : ℝ) * x ^ (5 / 3 : ℝ)
        exact Real.rpow_add hx 1 (5 / 3)
      _ = x * (x * (r * r)) := by rw [hone, h53]
  change -(3 / Real.cbrt x) *
      (1 + (3 / 2) * x - (3 / 5) * x ^ 2 + (1 / 8) * x ^ 3) =
    -3 * Real.rpow x (-(1 / 3)) -
      (9 / 2) * Real.rpow x (2 / 3) +
      (9 / 5) * Real.rpow x (5 / 3) -
      (3 / 8) * Real.rpow x (8 / 3)
  rw [hroot, hneg13, h23, h53, h83]
  rw [← hr3]
  field_simp [hr0]
  ring

private lemma primitive_hasDerivAt_original (x : ℝ) (hx : x ∈ domain) :
    HasDerivAt primitive (original x) x := by
  change 0 < x at hx
  have hx0 : x ≠ 0 := ne_of_gt hx
  have h1 : HasDerivAt (fun y : ℝ => Real.rpow y (-(1 / 3)))
      ((-(1 / 3)) * Real.rpow x (-(4 / 3))) x := by
    have he : (-(1 / 3) : ℝ) - 1 = -(4 / 3) := by ring
    simpa only [he] using
      (Real.hasDerivAt_rpow_const (p := (-(1 / 3) : ℝ)) (Or.inl hx0))
  have h2 : HasDerivAt (fun y : ℝ => Real.rpow y (2 / 3))
      ((2 / 3) * Real.rpow x (-(1 / 3))) x := by
    have he : (2 / 3 : ℝ) - 1 = -(1 / 3) := by ring
    simpa only [he] using
      (Real.hasDerivAt_rpow_const (p := (2 / 3 : ℝ)) (Or.inl hx0))
  have h3 : HasDerivAt (fun y : ℝ => Real.rpow y (5 / 3))
      ((5 / 3) * Real.rpow x (2 / 3)) x := by
    have he : (5 / 3 : ℝ) - 1 = 2 / 3 := by ring
    simpa only [he] using
      (Real.hasDerivAt_rpow_const (p := (5 / 3 : ℝ)) (Or.inl hx0))
  have h4 : HasDerivAt (fun y : ℝ => Real.rpow y (8 / 3))
      ((8 / 3) * Real.rpow x (5 / 3)) x := by
    have he : (8 / 3 : ℝ) - 1 = 5 / 3 := by ring
    simpa only [he] using
      (Real.hasDerivAt_rpow_const (p := (8 / 3 : ℝ)) (Or.inl hx0))
  have hraw :=
    (((((hasDerivAt_const x (-3 : ℝ)).mul h1).sub
      ((hasDerivAt_const x (9 / 2 : ℝ)).mul h2)).add
      ((hasDerivAt_const x (9 / 5 : ℝ)).mul h3)).sub
      ((hasDerivAt_const x (3 / 8 : ℝ)).mul h4))
  have hexp : HasDerivAt expandedPrimitive (powers x) x := by
    convert hraw using 1 <;> dsimp [expandedPrimitive, powers] <;> ring
  rw [← original_eq_powers x hx] at hexp
  have heq : Filter.EventuallyEq (nhds x) primitive expandedPrimitive := by
    filter_upwards [show domain ∈ nhds x by
      simpa [domain] using (isOpen_Ioi.mem_nhds hx)] with y hy
    exact primitive_eq_expanded y hy
  exact hexp.congr_of_eventuallyEq heq

theorem gap1 : AntiderivativesOn original = AntiderivativesOn powers := by
  ext F
  constructor
  · rintro ⟨hF, hder⟩
    exact ⟨hF, fun x hx => (hder x hx).trans (original_eq_powers x hx)⟩
  · rintro ⟨hF, hder⟩
    exact ⟨hF, fun x hx => (hder x hx).trans (original_eq_powers x hx).symm⟩

theorem gap2 : AntiderivativesOn powers = PrimitiveFamily primitive := by
  ext F
  constructor
  · intro hF
    have hForig : F ∈ AntiderivativesOn original := by
      rw [gap1]
      exact hF
    have hdiff : DifferentiableOn ℝ (fun y => F y - primitive y) domain := by
      intro x hx
      exact (hForig.1 x hx).sub
        ((primitive_hasDerivAt_original x hx).differentiableAt.differentiableWithinAt)
    have hzero : ∀ x ∈ domain, deriv (fun y => F y - primitive y) x = 0 := by
      intro x hx
      have hnhds : domain ∈ nhds x := by
        simpa [domain] using (isOpen_Ioi.mem_nhds hx)
      have hFat : DifferentiableAt ℝ F x :=
        (hForig.1 x hx).differentiableAt hnhds
      have hFd : HasDerivAt F (original x) x := by
        simpa only [hForig.2 x hx] using hFat.hasDerivAt
      have hsub : HasDerivAt (fun y => F y - primitive y) 0 x := by
        simpa only [sub_self] using
          hFd.sub (primitive_hasDerivAt_original x hx)
      exact hsub.deriv
    have hopen : IsOpen domain := by
      simpa [domain] using isOpen_Ioi
    have hconv : Convex ℝ domain := by
      simpa [domain] using convex_Ioi (0 : ℝ)
    have hpre : IsPreconnected domain := hconv.isPreconnected
    refine ⟨F 1 - primitive 1, ?_⟩
    intro x hx
    have hone : (1 : ℝ) ∈ domain := by
      change (0 : ℝ) < 1
      exact zero_lt_one
    have hc : F x - primitive x = F 1 - primitive 1 :=
      hopen.is_const_of_deriv_eq_zero hpre hdiff hzero hx hone
    linarith
  · rintro ⟨C, hFC⟩
    have hantiOrig : F ∈ AntiderivativesOn original := by
      constructor
      · intro x hx
        have hp : HasDerivAt (fun y => primitive y + C) (original x) x := by
          simpa only [Pi.add_apply, add_zero] using
            (primitive_hasDerivAt_original x hx).add (hasDerivAt_const x C)
        have heq : Filter.EventuallyEq (nhds x) F
            (fun y => primitive y + C) := by
          filter_upwards [show domain ∈ nhds x by
            simpa [domain] using (isOpen_Ioi.mem_nhds hx)] with y hy
          exact hFC y hy
        exact (hp.congr_of_eventuallyEq heq).differentiableAt.differentiableWithinAt
      · intro x hx
        have hp : HasDerivAt (fun y => primitive y + C) (original x) x := by
          simpa only [Pi.add_apply, add_zero] using
            (primitive_hasDerivAt_original x hx).add (hasDerivAt_const x C)
        have heq : Filter.EventuallyEq (nhds x) F
            (fun y => primitive y + C) := by
          filter_upwards [show domain ∈ nhds x by
            simpa [domain] using (isOpen_Ioi.mem_nhds hx)] with y hy
          exact hFC y hy
        exact (hp.congr_of_eventuallyEq heq).deriv
    rw [← gap1]
    exact hantiOrig

theorem gap3 : AntiderivativesOn original = PrimitiveFamily primitive := by
  exact gap1.trans gap2

end
end ProofGap.Exercise1635
