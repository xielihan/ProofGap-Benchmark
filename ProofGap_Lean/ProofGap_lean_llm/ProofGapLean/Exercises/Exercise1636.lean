import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.Neighborhoods
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace ProofGap.Exercise1636

noncomputable section

def domain : Set ℝ := Set.Ioi 0
def original (x : ℝ) : ℝ :=
  (1 - 1 / x ^ 2) * Real.sqrt (x * Real.sqrt x)
def powers (x : ℝ) : ℝ :=
  Real.rpow x (3 / 4) - Real.rpow x (-(5 / 4))
def primitive₁ (x : ℝ) : ℝ :=
  (4 / 7) * Real.rpow x (7 / 4) + 4 * Real.rpow x (-(1 / 4))
def primitive₂ (x : ℝ) : ℝ :=
  4 * (x ^ 2 + 7) / (7 * Real.rpow x (1 / 4))
def AntiderivativesOn (g : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | DifferentiableOn ℝ F domain ∧ ∀ x ∈ domain, deriv F x = g x}
def PrimitiveFamily (p : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x ∈ domain, F x = p x + C}

private theorem positive_sqrt_eq_rpow_half (x : ℝ) (hx : 0 < x) :
    Real.sqrt x = Real.rpow x (1 / 2) := by
  have hsnonneg : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
  have hrnonneg : 0 ≤ Real.rpow x (1 / 2) :=
    (Real.rpow_pos_of_pos hx (1 / 2)).le
  have hsquare : (Real.sqrt x) ^ 2 = x := Real.sq_sqrt hx.le
  have hrpow_one : Real.rpow x (1 : ℝ) = x := by
    simpa using (Real.rpow_natCast x 1)
  have hrsquare : (Real.rpow x (1 / 2)) ^ 2 = x := by
    calc
      (Real.rpow x (1 / 2)) ^ 2 =
          Real.rpow x (1 / 2) * Real.rpow x (1 / 2) := by ring
      _ = Real.rpow x (1 / 2 + 1 / 2) :=
        (Real.rpow_add hx (1 / 2) (1 / 2)).symm
      _ = Real.rpow x 1 := by norm_num
      _ = x := hrpow_one
  nlinarith

private theorem positive_nested_sqrt (x : ℝ) (hx : 0 < x) :
    Real.sqrt (x * Real.sqrt x) = Real.rpow x (3 / 4) := by
  have hhalf := positive_sqrt_eq_rpow_half x hx
  have hprodnonneg : 0 ≤ x * Real.sqrt x :=
    mul_nonneg hx.le (Real.sqrt_nonneg x)
  have hsnonneg : 0 ≤ Real.sqrt (x * Real.sqrt x) :=
    Real.sqrt_nonneg _
  have hrnonneg : 0 ≤ Real.rpow x (3 / 4) :=
    (Real.rpow_pos_of_pos hx (3 / 4)).le
  have hsquare : (Real.sqrt (x * Real.sqrt x)) ^ 2 = x * Real.sqrt x :=
    Real.sq_sqrt hprodnonneg
  have hrpow_one : Real.rpow x (1 : ℝ) = x := by
    simpa using (Real.rpow_natCast x 1)
  have hrsquare : (Real.rpow x (3 / 4)) ^ 2 = x * Real.sqrt x := by
    calc
      (Real.rpow x (3 / 4)) ^ 2 =
          Real.rpow x (3 / 4) * Real.rpow x (3 / 4) := by ring
      _ = Real.rpow x (3 / 4 + 3 / 4) :=
        (Real.rpow_add hx (3 / 4) (3 / 4)).symm
      _ = Real.rpow x (1 + 1 / 2) := by norm_num
      _ = Real.rpow x 1 * Real.rpow x (1 / 2) :=
        Real.rpow_add hx 1 (1 / 2)
      _ = x * Real.sqrt x := by rw [hrpow_one, ← hhalf]
  nlinarith

private theorem primitive₁_hasDerivAt (x : ℝ) (hx : x ∈ domain) :
    HasDerivAt primitive₁ (powers x) x := by
  have hxpos : 0 < x := hx
  have hxne : x ≠ 0 := hxpos.ne'
  have h₁ :
      HasDerivAt (fun y : ℝ => Real.rpow y (7 / 4))
        ((7 / 4) * Real.rpow x (7 / 4 - 1)) x :=
    Real.hasDerivAt_rpow_const (p := 7 / 4) (Or.inl hxne)
  have h₂ :
      HasDerivAt (fun y : ℝ => Real.rpow y (-(1 / 4)))
        (-(1 / 4) * Real.rpow x (-(1 / 4) - 1)) x :=
    Real.hasDerivAt_rpow_const (p := -(1 / 4)) (Or.inl hxne)
  unfold primitive₁ powers
  convert (h₁.const_mul (4 / 7)).add (h₂.const_mul 4) using 1 <;>
    norm_num <;> ring

private theorem primitives_agree (x : ℝ) (hx : x ∈ domain) :
    primitive₁ x = primitive₂ x := by
  have hxpos : 0 < x := hx
  have hqpos : 0 < Real.rpow x (1 / 4) := Real.rpow_pos_of_pos hxpos _
  have hqne : Real.rpow x (1 / 4) ≠ 0 := hqpos.ne'
  have hrpow_two : Real.rpow x (2 : ℝ) = x ^ (2 : ℕ) := by
    simpa using (Real.rpow_natCast x 2)
  have hA :
      Real.rpow x (7 / 4) = x ^ 2 / Real.rpow x (1 / 4) := by
    apply (eq_div_iff hqne).2
    calc
      Real.rpow x (7 / 4) * Real.rpow x (1 / 4) =
          Real.rpow x (7 / 4 + 1 / 4) :=
        (Real.rpow_add hxpos (7 / 4) (1 / 4)).symm
      _ = Real.rpow x 2 := by norm_num
      _ = x ^ 2 := hrpow_two
  have hB :
      Real.rpow x (-(1 / 4)) = 1 / Real.rpow x (1 / 4) := by
    apply (eq_div_iff hqne).2
    calc
      Real.rpow x (-(1 / 4)) * Real.rpow x (1 / 4) =
          Real.rpow x (-(1 / 4) + 1 / 4) :=
        (Real.rpow_add hxpos (-(1 / 4)) (1 / 4)).symm
      _ = 1 := by norm_num
  rw [primitive₁, primitive₂, hA, hB]
  field_simp [hqne]

theorem gap1 (x : ℝ) (hx : x ∈ domain) : original x = powers x := by
  have hxpos : 0 < x := hx
  have hxne : x ≠ 0 := hxpos.ne'
  have hrpow_two : Real.rpow x (2 : ℝ) = x ^ (2 : ℕ) := by
    simpa using (Real.rpow_natCast x 2)
  have hBA :
      Real.rpow x (-(5 / 4)) * x ^ 2 = Real.rpow x (3 / 4) := by
    calc
      Real.rpow x (-(5 / 4)) * x ^ 2 =
          Real.rpow x (-(5 / 4)) * Real.rpow x 2 :=
        congrArg (fun z : ℝ => Real.rpow x (-(5 / 4)) * z) hrpow_two.symm
      _ = Real.rpow x (-(5 / 4) + 2) :=
        (Real.rpow_add hxpos (-(5 / 4)) 2).symm
      _ = Real.rpow x (3 / 4) := by norm_num
  have hdiv :
      Real.rpow x (3 / 4) / x ^ 2 = Real.rpow x (-(5 / 4)) := by
    apply (div_eq_iff (pow_ne_zero 2 hxne)).2
    exact hBA.symm
  rw [original, powers, positive_nested_sqrt x hxpos]
  calc
    (1 - 1 / x ^ 2) * Real.rpow x (3 / 4) =
        Real.rpow x (3 / 4) - Real.rpow x (3 / 4) / x ^ 2 := by ring
    _ = Real.rpow x (3 / 4) - Real.rpow x (-(5 / 4)) := by rw [hdiv]

theorem gap2 : AntiderivativesOn original = AntiderivativesOn powers := by
  ext F
  constructor
  · rintro ⟨hF, hder⟩
    refine ⟨hF, ?_⟩
    intro x hx
    rw [← gap1 x hx]
    exact hder x hx
  · rintro ⟨hF, hder⟩
    refine ⟨hF, ?_⟩
    intro x hx
    rw [gap1 x hx]
    exact hder x hx

theorem gap3 : AntiderivativesOn powers = PrimitiveFamily primitive₁ := by
  ext F
  constructor
  · rintro ⟨hFdiff, hFder⟩
    have hpDiff : DifferentiableOn ℝ primitive₁ domain := by
      intro x hx
      exact (primitive₁_hasDerivAt x hx).differentiableAt.differentiableWithinAt
    have hsubDiff :
        DifferentiableOn ℝ (fun y => F y - primitive₁ y) domain :=
      hFdiff.sub hpDiff
    have hzero :
        ∀ x ∈ domain, deriv (fun y => F y - primitive₁ y) x = 0 := by
      intro x hx
      have hFx : DifferentiableAt ℝ F x :=
        (hFdiff x hx).differentiableAt (isOpen_Ioi.mem_nhds hx)
      have hpx := primitive₁_hasDerivAt x hx
      have hsubderiv :
          HasDerivAt (fun y => F y - primitive₁ y)
            (deriv F x - powers x) x :=
        hFx.hasDerivAt.sub hpx
      calc
        deriv (fun y => F y - primitive₁ y) x = deriv F x - powers x :=
          hsubderiv.deriv
        _ = 0 := by rw [hFder x hx]; ring
    have hpre : IsPreconnected domain := by
      simpa only [domain] using
        (isPreconnected_Ioi : IsPreconnected (Set.Ioi (0 : ℝ)))
    have hopen : IsOpen domain := by
      simpa only [domain] using (isOpen_Ioi : IsOpen (Set.Ioi (0 : ℝ)))
    refine ⟨F 1 - primitive₁ 1, ?_⟩
    intro x hx
    have hone : (1 : ℝ) ∈ domain := by norm_num [domain]
    have heq : F x - primitive₁ x = F 1 - primitive₁ 1 :=
      hopen.is_const_of_deriv_eq_zero hpre hsubDiff hzero hx hone
    linarith
  · rintro ⟨C, hFC⟩
    have hpCDiff :
        DifferentiableOn ℝ (fun y => primitive₁ y + C) domain := by
      intro x hx
      exact ((primitive₁_hasDerivAt x hx).add_const C).differentiableAt.differentiableWithinAt
    have hFdiff : DifferentiableOn ℝ F domain := by
      apply hpCDiff.congr
      intro x hx
      exact hFC x hx
    refine ⟨hFdiff, ?_⟩
    intro x hx
    have heq : F =ᶠ[nhds x] (fun y => primitive₁ y + C) :=
      Filter.mem_of_superset (isOpen_Ioi.mem_nhds hx) (fun y hy => hFC y hy)
    calc
      deriv F x = deriv (fun y => primitive₁ y + C) x := heq.deriv_eq
      _ = powers x := ((primitive₁_hasDerivAt x hx).add_const C).deriv

theorem gap4 : PrimitiveFamily primitive₁ = PrimitiveFamily primitive₂ := by
  ext F
  constructor
  · rintro ⟨C, hF⟩
    refine ⟨C, ?_⟩
    intro x hx
    rw [← primitives_agree x hx]
    exact hF x hx
  · rintro ⟨C, hF⟩
    refine ⟨C, ?_⟩
    intro x hx
    rw [primitives_agree x hx]
    exact hF x hx

theorem gap5 : AntiderivativesOn original = PrimitiveFamily primitive₂ := by
  calc
    AntiderivativesOn original = AntiderivativesOn powers := gap2
    _ = PrimitiveFamily primitive₁ := gap3
    _ = PrimitiveFamily primitive₂ := gap4

end
end ProofGap.Exercise1636
