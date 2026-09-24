import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Neighborhoods
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1634

noncomputable section

def domain : Set ℝ := Set.Ioi 0
def original (x : ℝ) : ℝ :=
  (Real.sqrt x - 2 * Real.cbrt (x ^ 2) + 1) / Real.rpow x (1 / 4)
def powers (x : ℝ) : ℝ :=
  Real.rpow x (1 / 4) - 2 * Real.rpow x (5 / 12) +
    Real.rpow x (-(1 / 4))
def primitive (x : ℝ) : ℝ :=
  (4 / 5) * x * Real.rpow x (1 / 4) -
    (24 / 17) * x * Real.rpow x (5 / 12) +
    (4 / 3) * Real.rpow x (3 / 4)
def AntiderivativesOn (g : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | DifferentiableOn ℝ F domain ∧ ∀ x ∈ domain, deriv F x = g x}
def PrimitiveFamily (p : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x ∈ domain, F x = p x + C}

private theorem domain_isOpen : IsOpen domain := by
  simpa [domain] using (isOpen_Ioi : IsOpen (Set.Ioi (0 : ℝ)))

private theorem original_eq_powers {x : ℝ} (hx : x ∈ domain) :
    original x = powers x := by
  have hxpos : 0 < x := hx
  have hsqrt : Real.sqrt x = Real.rpow x (1 / 2) := by
    change Real.sqrt x = x ^ (1 / 2 : ℝ)
    exact Real.sqrt_eq_rpow x
  have hcbrt : Real.cbrt (x ^ 2) = Real.rpow x (2 / 3) := by
    unfold Real.cbrt
    calc
      Real.rpow (x ^ 2) (1 / 3) =
          Real.rpow x ((2 : ℝ) * (1 / 3)) :=
        (Real.rpow_natCast_mul hxpos.le 2 (1 / 3)).symm
      _ = Real.rpow x (2 / 3) := by congr 1 <;> ring
  have hq1 :
      Real.rpow x (1 / 2) / Real.rpow x (1 / 4) =
        Real.rpow x (1 / 4) := by
    change x ^ (1 / 2 : ℝ) / x ^ (1 / 4 : ℝ) = x ^ (1 / 4 : ℝ)
    rw [← Real.rpow_sub hxpos]
    congr 1
    ring
  have hq2 :
      Real.rpow x (2 / 3) / Real.rpow x (1 / 4) =
        Real.rpow x (5 / 12) := by
    change x ^ (2 / 3 : ℝ) / x ^ (1 / 4 : ℝ) = x ^ (5 / 12 : ℝ)
    rw [← Real.rpow_sub hxpos]
    congr 1
    ring
  have hq3 :
      1 / Real.rpow x (1 / 4) = Real.rpow x (-(1 / 4)) := by
    change 1 / x ^ (1 / 4 : ℝ) = x ^ (-(1 / 4 : ℝ))
    simpa using (Real.rpow_sub hxpos (0 : ℝ) (1 / 4)).symm
  unfold original powers
  rw [hsqrt, hcbrt]
  calc
    (Real.rpow x (1 / 2) - 2 * Real.rpow x (2 / 3) + 1) /
          Real.rpow x (1 / 4) =
        Real.rpow x (1 / 2) / Real.rpow x (1 / 4) -
          2 * (Real.rpow x (2 / 3) / Real.rpow x (1 / 4)) +
          1 / Real.rpow x (1 / 4) := by ring
    _ = Real.rpow x (1 / 4) - 2 * Real.rpow x (5 / 12) +
          Real.rpow x (-(1 / 4)) := by rw [hq1, hq2, hq3]

private def expandedPrimitive (x : ℝ) : ℝ :=
  (4 / 5) * Real.rpow x (5 / 4) -
    (24 / 17) * Real.rpow x (17 / 12) +
    (4 / 3) * Real.rpow x (3 / 4)

private theorem primitive_eq_expanded {x : ℝ} (hx : x ∈ domain) :
    primitive x = expandedPrimitive x := by
  have hxpos : 0 < x := hx
  have h1 :
      x * Real.rpow x (1 / 4) = Real.rpow x (5 / 4) := by
    calc
      x * Real.rpow x (1 / 4) =
          Real.rpow x 1 * Real.rpow x (1 / 4) := by simp
      _ = Real.rpow x (1 + 1 / 4) :=
        (Real.rpow_add hxpos 1 (1 / 4)).symm
      _ = Real.rpow x (5 / 4) := by congr 1 <;> ring
  have h2 :
      x * Real.rpow x (5 / 12) = Real.rpow x (17 / 12) := by
    calc
      x * Real.rpow x (5 / 12) =
          Real.rpow x 1 * Real.rpow x (5 / 12) := by simp
      _ = Real.rpow x (1 + 5 / 12) :=
        (Real.rpow_add hxpos 1 (5 / 12)).symm
      _ = Real.rpow x (17 / 12) := by congr 1 <;> ring
  unfold primitive expandedPrimitive
  calc
    4 / 5 * x * Real.rpow x (1 / 4) -
          24 / 17 * x * Real.rpow x (5 / 12) +
          4 / 3 * Real.rpow x (3 / 4) =
        (4 / 5) * (x * Real.rpow x (1 / 4)) -
          (24 / 17) * (x * Real.rpow x (5 / 12)) +
          (4 / 3) * Real.rpow x (3 / 4) := by ring
    _ = 4 / 5 * Real.rpow x (5 / 4) -
          24 / 17 * Real.rpow x (17 / 12) +
          4 / 3 * Real.rpow x (3 / 4) := by rw [h1, h2]

private theorem primitive_hasDerivAt {x : ℝ} (hx : x ∈ domain) :
    HasDerivAt primitive (powers x) x := by
  have hxpos : 0 < x := hx
  have hx0 : x ≠ 0 := ne_of_gt hxpos
  have h1 : HasDerivAt (fun y : ℝ => Real.rpow y (5 / 4))
      ((5 / 4) * Real.rpow x (1 / 4)) x := by
    have he : (5 / 4 : ℝ) - 1 = 1 / 4 := by ring
    simpa only [he] using
      (Real.hasDerivAt_rpow_const (p := (5 / 4 : ℝ)) (Or.inl hx0))
  have h2 : HasDerivAt (fun y : ℝ => Real.rpow y (17 / 12))
      ((17 / 12) * Real.rpow x (5 / 12)) x := by
    have he : (17 / 12 : ℝ) - 1 = 5 / 12 := by ring
    simpa only [he] using
      (Real.hasDerivAt_rpow_const (p := (17 / 12 : ℝ)) (Or.inl hx0))
  have h3 : HasDerivAt (fun y : ℝ => Real.rpow y (3 / 4))
      ((3 / 4) * Real.rpow x (-(1 / 4))) x := by
    have he : (3 / 4 : ℝ) - 1 = -(1 / 4) := by ring
    simpa only [he] using
      (Real.hasDerivAt_rpow_const (p := (3 / 4 : ℝ)) (Or.inl hx0))
  have hraw :=
    ((((hasDerivAt_const x (4 / 5 : ℝ)).mul h1).sub
      ((hasDerivAt_const x (24 / 17 : ℝ)).mul h2)).add
      ((hasDerivAt_const x (4 / 3 : ℝ)).mul h3))
  have hexp : HasDerivAt expandedPrimitive (powers x) x := by
    convert hraw using 1 <;> dsimp [expandedPrimitive, powers] <;> ring
  have heq : primitive =ᶠ[nhds x] expandedPrimitive := by
    filter_upwards [domain_isOpen.mem_nhds hx] with y hy
    exact primitive_eq_expanded hy
  exact hexp.congr_of_eventuallyEq heq

theorem gap1 : AntiderivativesOn original = AntiderivativesOn powers := by
  ext F
  simp only [AntiderivativesOn, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hF, hderiv⟩
    exact ⟨hF, fun x hx => (hderiv x hx).trans (original_eq_powers hx)⟩
  · rintro ⟨hF, hderiv⟩
    exact ⟨hF, fun x hx => (hderiv x hx).trans (original_eq_powers hx).symm⟩

theorem gap2 : AntiderivativesOn powers = PrimitiveFamily primitive := by
  ext F
  simp only [AntiderivativesOn, PrimitiveFamily, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hFdiff, hFderiv⟩
    let H : ℝ → ℝ := fun x => F x - primitive x
    have hHdiff : DifferentiableOn ℝ H domain := by
      intro x hx
      have hFat : DifferentiableAt ℝ F x :=
        (hFdiff x hx).differentiableAt (domain_isOpen.mem_nhds hx)
      exact (hFat.sub (primitive_hasDerivAt hx).differentiableAt).differentiableWithinAt
    have hHzero : ∀ x ∈ domain, deriv H x = 0 := by
      intro x hx
      have hFat : DifferentiableAt ℝ F x :=
        (hFdiff x hx).differentiableAt (domain_isOpen.mem_nhds hx)
      have hd : HasDerivAt H (deriv F x - powers x) x := by
        simpa [H] using hFat.hasDerivAt.sub (primitive_hasDerivAt hx)
      rw [hFderiv x hx] at hd
      simpa using hd.deriv
    have hpre : IsPreconnected domain := by
      exact (convex_Ioi (0 : ℝ)).isPreconnected
    refine ⟨F 1 - primitive 1, ?_⟩
    intro x hx
    have hone : (1 : ℝ) ∈ domain := by norm_num [domain]
    have hc : H x = H 1 :=
      domain_isOpen.is_const_of_deriv_eq_zero hpre hHdiff hHzero hx hone
    dsimp [H] at hc
    linarith
  · rintro ⟨C, hFC⟩
    have hpDiff : DifferentiableOn ℝ (fun x => primitive x + C) domain := by
      intro x hx
      exact ((primitive_hasDerivAt hx).add_const C).differentiableAt.differentiableWithinAt
    refine ⟨hpDiff.congr (fun x hx => hFC x hx), ?_⟩
    intro x hx
    have hevent : F =ᶠ[nhds x] fun y => primitive y + C := by
      filter_upwards [domain_isOpen.mem_nhds hx] with y hy
      exact hFC y hy
    rw [hevent.deriv_eq]
    exact ((primitive_hasDerivAt hx).add_const C).deriv

theorem gap3 : AntiderivativesOn original = PrimitiveFamily primitive := by
  exact gap1.trans gap2

end
end ProofGap.Exercise1634
