import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Neighborhoods
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise1633

noncomputable section

def domain : Set ℝ := Set.Ioi 0
def original (x : ℝ) : ℝ := (x + 1) / Real.sqrt x
def powers (x : ℝ) : ℝ :=
  Real.rpow x (1 / 2) + Real.rpow x (-(1 / 2))
def primitive (x : ℝ) : ℝ :=
  (2 / 3) * x * Real.sqrt x + 2 * Real.sqrt x
def AntiderivativesOn (g : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | DifferentiableOn ℝ F domain ∧ ∀ x ∈ domain, deriv F x = g x}
def PrimitiveFamily (p : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x ∈ domain, F x = p x + C}

private theorem domain_isOpen : IsOpen domain := by
  simpa [domain] using (isOpen_Ioi : IsOpen (Set.Ioi (0 : ℝ)))

private theorem powers_eq_sqrt_add_inv {x : ℝ} (hx : 0 < x) :
    powers x = Real.sqrt x + (Real.sqrt x)⁻¹ := by
  have hpos : Real.rpow x (1 / 2 : ℝ) =
      Real.exp (Real.log x * (1 / 2 : ℝ)) := by
    change x ^ (1 / 2 : ℝ) = Real.exp (Real.log x * (1 / 2 : ℝ))
    exact Real.rpow_def_of_pos hx (1 / 2 : ℝ)
  have hnegpow : Real.rpow x (-(1 / 2 : ℝ)) =
      Real.exp (Real.log x * (-(1 / 2 : ℝ))) := by
    change x ^ (-(1 / 2 : ℝ)) = Real.exp (Real.log x * (-(1 / 2 : ℝ)))
    exact Real.rpow_def_of_pos hx (-(1 / 2 : ℝ))
  have hinv : Real.rpow x (-(1 / 2 : ℝ)) =
      (Real.rpow x (1 / 2 : ℝ))⁻¹ := by
    calc
      Real.rpow x (-(1 / 2 : ℝ)) =
          Real.exp (Real.log x * (-(1 / 2 : ℝ))) := hnegpow
      _ = Real.exp (-(Real.log x * (1 / 2 : ℝ))) := by
        congr 1
        ring
      _ = (Real.exp (Real.log x * (1 / 2 : ℝ)))⁻¹ := Real.exp_neg _
      _ = (Real.rpow x (1 / 2 : ℝ))⁻¹ :=
        congrArg (fun z : ℝ => z⁻¹) hpos.symm
  have hsqrt : Real.rpow x (1 / 2 : ℝ) = Real.sqrt x := by
    exact (Real.sqrt_eq_rpow (x := x)).symm
  unfold powers
  calc
    Real.rpow x (1 / 2) + Real.rpow x (-(1 / 2)) =
        Real.rpow x (1 / 2) + (Real.rpow x (1 / 2))⁻¹ :=
      congrArg (fun z : ℝ => Real.rpow x (1 / 2) + z) hinv
    _ = Real.sqrt x + (Real.sqrt x)⁻¹ :=
      congrArg (fun z : ℝ => z + z⁻¹) hsqrt

private theorem original_eq_powers {x : ℝ} (hx : x ∈ domain) :
    original x = powers x := by
  have hxpos : 0 < x := hx
  have hsne : Real.sqrt x ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hxpos)
  rw [powers_eq_sqrt_add_inv hxpos]
  unfold original
  field_simp [hsne]
  nlinarith [Real.sq_sqrt hxpos.le]

private theorem primitive_hasDerivAt {x : ℝ} (hx : x ∈ domain) :
    HasDerivAt primitive (powers x) x := by
  have hxpos : 0 < x := hx
  have hsne : Real.sqrt x ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hxpos)
  have hs : HasDerivAt Real.sqrt (1 / (2 * Real.sqrt x)) x :=
    Real.hasDerivAt_sqrt (ne_of_gt hxpos)
  have hraw : HasDerivAt primitive
      ((2 / 3) * (Real.sqrt x + x * (1 / (2 * Real.sqrt x))) +
        2 * (1 / (2 * Real.sqrt x))) x := by
    convert (((hasDerivAt_id x).mul hs).const_mul (2 / 3)).add (hs.const_mul 2) using 1
    · ext y
      simp [primitive, mul_assoc]
    · simp
  convert hraw using 1
  rw [powers_eq_sqrt_add_inv hxpos]
  field_simp [hsne]
  nlinarith [Real.sq_sqrt hxpos.le]

theorem gap1 : AntiderivativesOn original = AntiderivativesOn powers := by
  ext F
  simp only [AntiderivativesOn, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hF, hderiv⟩
    refine ⟨hF, ?_⟩
    intro x hx
    rw [← original_eq_powers hx]
    exact hderiv x hx
  · rintro ⟨hF, hderiv⟩
    refine ⟨hF, ?_⟩
    intro x hx
    rw [original_eq_powers hx]
    exact hderiv x hx

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
    have hconst : ∀ x ∈ domain, ∀ y ∈ domain, H x = H y := by
      intro x hx y hy
      let b : ℝ := max x y + 1
      have hb : max x y < b := by
        dsimp [b]
        linarith
      have hxI : x ∈ Set.Ioo (0 : ℝ) b :=
        ⟨hx, lt_of_le_of_lt (le_max_left x y) hb⟩
      have hyI : y ∈ Set.Ioo (0 : ℝ) b :=
        ⟨hy, lt_of_le_of_lt (le_max_right x y) hb⟩
      have hsub : Set.Ioo (0 : ℝ) b ⊆ domain := by
        intro z hz
        exact hz.1
      have hdiffI : DifferentiableOn ℝ H (Set.Ioo (0 : ℝ) b) :=
        hHdiff.mono hsub
      have hzeroI : ∀ z ∈ Set.Ioo (0 : ℝ) b, deriv H z = 0 := by
        intro z hz
        exact hHzero z (hsub hz)
      exact isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo
        hdiffI hzeroI hxI hyI
    refine ⟨F 1 - primitive 1, ?_⟩
    intro x hx
    have hc := hconst x hx 1 (by norm_num [domain])
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
  rw [gap1, gap2]

end
end ProofGap.Exercise1633
