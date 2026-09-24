import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Topology.Neighborhoods
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise1730

noncomputable section

def domain : Set ℝ := Set.Iio (2 / 5)
def original (x : ℝ) : ℝ := x * Real.sqrt (2 - 5 * x)
def substituted (x : ℝ) : ℝ :=
  (-(1 / 5) * (2 - 5 * x) + 2 / 5) * Real.rpow (2 - 5 * x) (1 / 2)
def expanded (x : ℝ) : ℝ :=
  -(1 / 5) * Real.rpow (2 - 5 * x) (3 / 2) +
    (2 / 5) * Real.rpow (2 - 5 * x) (1 / 2)
def primitive₁ (x : ℝ) : ℝ :=
  (2 / 125) * Real.rpow (2 - 5 * x) (5 / 2) -
    (4 / 75) * Real.rpow (2 - 5 * x) (3 / 2)
def primitive₂ (x : ℝ) : ℝ :=
  -((8 + 30 * x) / 375) * Real.rpow (2 - 5 * x) (3 / 2)
def AntiderivativesOn (g : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | DifferentiableOn ℝ F domain ∧ ∀ x ∈ domain, deriv F x = g x}
def PrimitiveFamily (p : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x ∈ domain, F x = p x + C}

private lemma sqrt_eq_explicit_rpow (x : ℝ) :
    Real.sqrt x = Real.rpow x (1 / 2) := by
  change Real.sqrt x = x ^ (1 / 2 : ℝ)
  exact Real.sqrt_eq_rpow x

private lemma explicit_rpow_add (x a b : ℝ) (hx : 0 < x) :
    Real.rpow x (a + b) = Real.rpow x a * Real.rpow x b := by
  change x ^ (a + b) = x ^ a * x ^ b
  exact Real.rpow_add hx a b

private lemma explicit_rpow_one (x : ℝ) : Real.rpow x 1 = x := by
  change x ^ (1 : ℝ) = x
  simp

private lemma primitive_one_hasDerivAt (x : ℝ) (hx : x ∈ domain) :
    HasDerivAt primitive₁ (original x) x := by
  have hpos : 0 < 2 - 5 * x := by
    simp only [domain, Set.mem_Iio] at hx
    linarith
  have hlinear : HasDerivAt (fun y : ℝ => 2 - 5 * y) (-5) x := by
    convert (hasDerivAt_const x (2 : ℝ)).sub
      ((hasDerivAt_id x).const_mul 5) using 1 <;> ring
  have hfive :
      HasDerivAt (fun y : ℝ => Real.rpow (2 - 5 * y) (5 / 2))
        ((5 / 2) * Real.rpow (2 - 5 * x) (3 / 2) * (-5)) x := by
    convert
      (Real.hasDerivAt_rpow_const (p := (5 / 2 : ℝ))
        (Or.inl (ne_of_gt hpos))).comp x hlinear using 1 <;>
      norm_num
  have hthree :
      HasDerivAt (fun y : ℝ => Real.rpow (2 - 5 * y) (3 / 2))
        ((3 / 2) * Real.rpow (2 - 5 * x) (1 / 2) * (-5)) x := by
    convert
      (Real.hasDerivAt_rpow_const (p := (3 / 2 : ℝ))
        (Or.inl (ne_of_gt hpos))).comp x hlinear using 1 <;>
      norm_num
  have hp :
      HasDerivAt primitive₁
        ((2 / 125) * ((5 / 2) * Real.rpow (2 - 5 * x) (3 / 2) * (-5)) -
          (4 / 75) * ((3 / 2) * Real.rpow (2 - 5 * x) (1 / 2) * (-5))) x := by
    simpa only [primitive₁] using
      (hfive.const_mul (2 / 125)).sub (hthree.const_mul (4 / 75))
  have hpow :
      Real.rpow (2 - 5 * x) (3 / 2) =
        (2 - 5 * x) * Real.rpow (2 - 5 * x) (1 / 2) := by
    calc
      Real.rpow (2 - 5 * x) (3 / 2) =
          Real.rpow (2 - 5 * x) (1 + 1 / 2) := by norm_num
      _ = Real.rpow (2 - 5 * x) 1 *
            Real.rpow (2 - 5 * x) (1 / 2) :=
        explicit_rpow_add (2 - 5 * x) 1 (1 / 2) hpos
      _ = (2 - 5 * x) * Real.rpow (2 - 5 * x) (1 / 2) := by
        rw [explicit_rpow_one]
  convert hp using 1
  rw [hpow]
  unfold original
  rw [sqrt_eq_explicit_rpow]
  ring

private theorem antiderivatives_eq_primitive_family :
    AntiderivativesOn original = PrimitiveFamily primitive₁ := by
  ext F
  simp only [AntiderivativesOn, PrimitiveFamily, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hF, hder⟩
    refine ⟨F 0 - primitive₁ 0, ?_⟩
    have hdiff : DifferentiableOn ℝ (fun y => F y - primitive₁ y) domain := by
      intro y hy
      exact (hF y hy).sub
        ((primitive_one_hasDerivAt y hy).differentiableAt.differentiableWithinAt)
    have hzero : ∀ y ∈ domain, deriv (fun z => F z - primitive₁ z) y = 0 := by
      intro y hy
      have hFat : DifferentiableAt ℝ F y :=
        (hF y hy).differentiableAt (isOpen_Iio.mem_nhds hy)
      have hFhas : HasDerivAt F (original y) y := by
        convert hFat.hasDerivAt using 1
        exact (hder y hy).symm
      simpa using (hFhas.sub (primitive_one_hasDerivAt y hy)).deriv
    have hopen : IsOpen domain := by
      simpa only [domain] using isOpen_Iio
    have hpre : IsPreconnected domain := by
      unfold domain
      exact isPreconnected_Iio
    intro x hx
    have hzero_mem : (0 : ℝ) ∈ domain := by
      simp [domain]
    have heq : F x - primitive₁ x = F 0 - primitive₁ 0 :=
      hopen.is_const_of_deriv_eq_zero hpre hdiff hzero hx hzero_mem
    linarith
  · rintro ⟨C, hFC⟩
    have hhas : ∀ x ∈ domain, HasDerivAt F (original x) x := by
      intro x hx
      have hevent : F =ᶠ[nhds x] (fun y => primitive₁ y + C) := by
        filter_upwards [isOpen_Iio.mem_nhds hx] with y hy
        exact hFC y hy
      exact ((primitive_one_hasDerivAt x hx).add_const C).congr_of_eventuallyEq hevent
    refine ⟨?_, ?_⟩
    · intro x hx
      exact (hhas x hx).differentiableAt.differentiableWithinAt
    · intro x hx
      exact (hhas x hx).deriv

theorem gap1 (x : ℝ) : x = -(1 / 5) * (2 - 5 * x) + 2 / 5 := by
  ring

theorem gap2 : AntiderivativesOn original = AntiderivativesOn substituted := by
  have heq : ∀ x : ℝ, original x = substituted x := by
    intro x
    unfold original substituted
    calc
      x * Real.sqrt (2 - 5 * x) =
          x * Real.rpow (2 - 5 * x) (1 / 2) :=
        congrArg (fun z : ℝ => x * z)
          (sqrt_eq_explicit_rpow (2 - 5 * x))
      _ = (-(1 / 5) * (2 - 5 * x) + 2 / 5) *
          Real.rpow (2 - 5 * x) (1 / 2) :=
        congrArg (fun z : ℝ => z * Real.rpow (2 - 5 * x) (1 / 2)) (gap1 x)
  ext F
  simp only [AntiderivativesOn, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hF, hder⟩
    exact ⟨hF, fun x hx => (hder x hx).trans (heq x)⟩
  · rintro ⟨hF, hder⟩
    exact ⟨hF, fun x hx => (hder x hx).trans (heq x).symm⟩

theorem gap3 : AntiderivativesOn substituted = AntiderivativesOn expanded := by
  have heq : ∀ x ∈ domain, substituted x = expanded x := by
    intro x hx
    have hpos : 0 < 2 - 5 * x := by
      simp only [domain, Set.mem_Iio] at hx
      linarith
    have hpow :
        Real.rpow (2 - 5 * x) (3 / 2) =
          (2 - 5 * x) * Real.rpow (2 - 5 * x) (1 / 2) := by
      calc
        Real.rpow (2 - 5 * x) (3 / 2) =
            Real.rpow (2 - 5 * x) (1 + 1 / 2) := by norm_num
        _ = Real.rpow (2 - 5 * x) 1 *
              Real.rpow (2 - 5 * x) (1 / 2) :=
          explicit_rpow_add (2 - 5 * x) 1 (1 / 2) hpos
        _ = (2 - 5 * x) * Real.rpow (2 - 5 * x) (1 / 2) := by
          rw [explicit_rpow_one]
    unfold substituted expanded
    rw [hpow]
    ring
  ext F
  simp only [AntiderivativesOn, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hF, hder⟩
    exact ⟨hF, fun x hx => (hder x hx).trans (heq x hx)⟩
  · rintro ⟨hF, hder⟩
    exact ⟨hF, fun x hx => (hder x hx).trans (heq x hx).symm⟩

theorem gap4 : AntiderivativesOn original = AntiderivativesOn expanded := by
  exact gap2.trans gap3

theorem gap5 : AntiderivativesOn original = PrimitiveFamily primitive₁ := by
  exact antiderivatives_eq_primitive_family

theorem gap6 : PrimitiveFamily primitive₁ = PrimitiveFamily primitive₂ := by
  have heq : ∀ x ∈ domain, primitive₁ x = primitive₂ x := by
    intro x hx
    have hpos : 0 < 2 - 5 * x := by
      simp only [domain, Set.mem_Iio] at hx
      linarith
    have hpow :
        Real.rpow (2 - 5 * x) (5 / 2) =
          (2 - 5 * x) * Real.rpow (2 - 5 * x) (3 / 2) := by
      calc
        Real.rpow (2 - 5 * x) (5 / 2) =
            Real.rpow (2 - 5 * x) (1 + 3 / 2) := by norm_num
        _ = Real.rpow (2 - 5 * x) 1 *
              Real.rpow (2 - 5 * x) (3 / 2) :=
          explicit_rpow_add (2 - 5 * x) 1 (3 / 2) hpos
        _ = (2 - 5 * x) * Real.rpow (2 - 5 * x) (3 / 2) := by
          rw [explicit_rpow_one]
    unfold primitive₁ primitive₂
    rw [hpow]
    ring
  ext F
  simp only [PrimitiveFamily, Set.mem_setOf_eq]
  constructor
  · rintro ⟨C, hF⟩
    exact ⟨C, fun x hx =>
      (hF x hx).trans (congrArg (fun y : ℝ => y + C) (heq x hx))⟩
  · rintro ⟨C, hF⟩
    exact ⟨C, fun x hx =>
      (hF x hx).trans (congrArg (fun y : ℝ => y + C) (heq x hx).symm)⟩

theorem gap7 : AntiderivativesOn original = PrimitiveFamily primitive₂ := by
  exact gap5.trans gap6

end
end ProofGap.Exercise1730
